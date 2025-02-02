`timescale 1ns / 1ps

module top2(input         clk, reset, 
           output  [31:0] WriteDataM, DataAdrM, 
           output         MemWriteM);

  wire [31:0] PCF, InstrF, ReadDataM;
  
  
  riscv riscv(clk, reset, PCF, InstrF, MemWriteM, DataAdrM, 
              WriteDataM, ReadDataM);
  imem imem(PCF, InstrF);
  dmem dmem(clk, MemWriteM, DataAdrM, WriteDataM, ReadDataM);
endmodule

module riscv(input          clk, reset,
             output  [31:0] PCF,
             input   [31:0] InstrF,
             output         MemWriteM,
             output  [31:0] ALUResultM, WriteDataM,
             input   [31:0] ReadDataM);

  wire [6:0]  opD;
  wire [2:0]  funct3D,funct3E;
  wire        funct7b5D,funct7b0D;
  wire [2:0]  ImmSrcD;
  wire        ZeroE;
  wire        PCSrcE;
  wire [3:0]  ALUControlE;
  wire        ALUSrcE;
  wire 	   ResultSrcEb0;
  wire        RegWriteM;
  wire [1:0]  ResultSrcW;
  wire        RegWriteW;
  wire		  PCTargetSrcE;
  wire [1:0]  ForwardAE, ForwardBE;
  wire        StallF, StallD, FlushD, FlushE;

  wire [4:0] Rs1D, Rs2D, Rs1E, Rs2E, RdE, RdM, RdW;
  
  controller c(clk, reset,
               opD, funct3D, funct7b5D,funct7b0D, ImmSrcD,
               FlushE, ZeroE, PCSrcE, ALUControlE, ALUSrcE, ResultSrcEb0,
               MemWriteM, RegWriteM, 
			   RegWriteW, ResultSrcW,PCTargetSrcE);

  datapath dp(clk, reset,
              StallF, PCF, InstrF,
			  opD, funct3D, funct7b5D,funct7b0D, StallD, FlushD, ImmSrcD,
			  PCTargetSrcE, FlushE, ForwardAE, ForwardBE, PCSrcE, ALUControlE, ALUSrcE, ZeroE,funct3E,
              MemWriteM, WriteDataM, ALUResultM, ReadDataM,
              RegWriteW, ResultSrcW,
              Rs1D, Rs2D, Rs1E, Rs2E, RdE, RdM, RdW);

  hazard  hu(Rs1D, Rs2D, Rs1E, Rs2E, RdE, RdM, RdW,
             PCSrcE, ResultSrcEb0, RegWriteM, RegWriteW,
             ForwardAE, ForwardBE, StallF, StallD, FlushD, FlushE);			 
endmodule


module controller(input  		  clk, reset,
                  
                  input  [6:0]  opD,
                  input  [2:0]  funct3D,
                  input  	     funct7b5D,
                  input			 funct7b0D,
                  output  [2:0] ImmSrcD,
                  
                  input  	     FlushE, 
                  input  	     ZeroE, 
                  output        PCSrcE,
                  output  [3:0] ALUControlE, 
                  output  	     ALUSrcE,
                  output        ResultSrcEb0,
                  output  	     MemWriteM,
                  output        RegWriteM,   				  
                  output  	     RegWriteW,
                  output  [1:0] ResultSrcW,
						output PCTargetSrcE);

  wire 	  RegWriteD, RegWriteE;
  wire [1:0] ResultSrcD, ResultSrcE, ResultSrcM;
  wire       MemWriteD, MemWriteE;
  wire		  JumpD, JumpE;
  wire		  BranchD, BranchE;
  wire	[1:0] ALUOpD;
  wire [3:0] ALUControlD;
  wire 	  ALUSrcD;
  wire PCTargetSrcD;	
  
  maindec md(opD, ResultSrcD, MemWriteD, BranchD,
             ALUSrcD, RegWriteD, JumpD, ImmSrcD, ALUOpD,PCTargetSrcD);
  aludec  ad(opD[5], funct3D, funct7b5D,funct7b0D, ALUOpD, ALUControlD);
  
  floprc #(12) controlregE(clk, reset, FlushE,
                           {RegWriteD, ResultSrcD, MemWriteD, JumpD, BranchD, ALUControlD, ALUSrcD, PCTargetSrcD},
                           {RegWriteE, ResultSrcE, MemWriteE, JumpE, BranchE, ALUControlE, ALUSrcE, PCTargetSrcE});

  assign PCSrcE = (BranchE & ZeroE) | JumpE;
  assign ResultSrcEb0 = ResultSrcE[0];
  
  
  flopr #(4) controlregM(clk, reset,
                         {RegWriteE, ResultSrcE, MemWriteE},
                         {RegWriteM, ResultSrcM, MemWriteM});
  
  
  flopr #(3) controlregW(clk, reset,
                         {RegWriteM, ResultSrcM},
                         {RegWriteW, ResultSrcW});     
endmodule

module maindec(input   [6:0] op,
               output  [1:0] ResultSrc,
               output        MemWrite,
               output        Branch, ALUSrc,
               output        RegWrite, Jump,
               output  [2:0] ImmSrc,
               output  [1:0] ALUOp,
					output PCTargetSrc /*JALR işlemi yapılıyorsa rs1+imm sonucunu PCMux'a yollamak için eklendi*/ );

  reg [12:0] controls;

  assign {RegWrite, ImmSrc, ALUSrc, MemWrite,
          ResultSrc, Branch, ALUOp, Jump, PCTargetSrc} = controls;
  always @*
    case(op)
    // RegWrite_ImmSrc_ALUSrc_MemWrite_ResultSrc_Branch_ALUOp_Jump_PCTargetSrc
      7'b0000011: controls = 13'b1_000_1_0_01_0_00_0_0; // lw
      7'b0100011: controls = 13'b0_001_1_1_00_0_00_0_0; // sw
      7'b0110011: controls = 13'b1_xxx_0_0_00_0_10_0_0; // R-type 
      7'b1100011: controls = 13'b0_010_0_0_00_1_01_0_0; // B-type
      7'b0010011: controls = 13'b1_000_1_0_00_0_10_0_0; // I-type ALU
      7'b1101111: controls = 13'b1_011_0_0_10_0_00_1_0; // jal
		7'b1100111: controls = 13'b1_000_1_0_10_0_00_1_1; // jalr-NEW
		7'b0010111: controls = 13'b1_100_x_0_11_0_xx_0_0; // auipc-NEW
      7'b0000000: controls = 13'b0_000_0_0_00_0_00_0_0; // need valid values at reset
      default:    controls = 13'bx_xxx_x_x_xx_x_xx_x_x; // non-implemented instruction
    endcase
endmodule

module aludec(input         opb5,
              input   [2:0] funct3,
              input         funct7b5,
              input			funct7b0,
              input   [1:0] ALUOp,
              output  reg [3:0] ALUControl);

  wire  RtypeSub,RtypeExt;
  assign RtypeSub = funct7b5 & opb5;  // TRUE for R-type subtract instruction
  assign RtypeExt = funct7b0 & opb5; //TRUE for R-type extended instructions

  always @(*) begin
    case(ALUOp)
      2'b00:                ALUControl = 4'b0000; // addition
      2'b01:                ALUControl = 4'b0001; // subtraction
      default: case(funct3) // R-type or I-type ALU
                 3'b000:  if (RtypeSub) 
                            ALUControl = 4'b0001; // sub
        				  else if(RtypeExt)
                            ALUControl = 4'b1000; // mul-NEW
                          else          
                            ALUControl = 4'b0000; // add, addi
                 3'b010:    ALUControl = 4'b0101; // slt, slti
					  3'b100:	 if(RtypeExt)
										ALUControl = 4'b1001; //div-NEW
									 else
										ALUControl = 4'b1011; //xor-NEW
        		     3'b110:  if(RtypeExt)
                   			 ALUControl = 4'b1010; //rem-NEW
								  else                   			
               			 	 ALUControl = 4'b0011; // or, ori
                 3'b111:    ALUControl = 4'b0010; // and, andi
                 default:   ALUControl = 4'bxxxx; // ???
               endcase
    endcase
  end
endmodule

module datapath(input  clk, reset,
                // Fetch stage signals
                input          StallF,
                output  [31:0] PCF,
                input   [31:0] InstrF,
                // Decode stage signals
                output  [6:0]  opD,
                output  [2:0]	 funct3D, 
                output         funct7b5D,
					 output			 funct7b0D,
                input          StallD, FlushD,
                input   [2:0]  ImmSrcD,
                // Execute stage signals
					 input PCTargetSrcE,
                input          FlushE,
                input   [1:0]  ForwardAE, ForwardBE,
                input          PCSrcE,
                input   [3:0]  ALUControlE,
                input          ALUSrcE,
                output         ZeroE,
					 output [2:0] funct3E,
                // Memory stage signals
                input          MemWriteM, 
                output  [31:0] WriteDataM, ALUResultM,
                input   [31:0] ReadDataM,
                // Writeback stage signals
                input          RegWriteW, 
                input   [1:0]  ResultSrcW,
                // Hazard Unit signals 
                output  [4:0]  Rs1D, Rs2D, Rs1E, Rs2E,
                output  [4:0]  RdE, RdM, RdW);

  // Fetch stage signals
  wire [31:0] PCNextF, PCPlus4F;
  // Decode stage signals
  wire [31:0] InstrD;
  wire [31:0] PCD, PCPlus4D;
  wire [31:0] RD1D, RD2D;
  wire [31:0] ImmExtD;
  wire [4:0]  RdD;
  // Execute stage signals
  wire [31:0] RD1E, RD2E;
  wire [31:0] PCE, ImmExtE;
  wire [31:0] SrcAE, SrcBE;
  wire [31:0] ALUResultE;
  wire [31:0] WriteDataE;
  wire [31:0] PCPlus4E;
  wire [31:0] PCTargetE;
  wire [31:0] PCFinalTargetE; // JALR'ye özel; eğer jalr işlemi yapılıyorsa rs1 + imm, öbür işlemlerde PCTargetE(PC+imm)
  // Memory stage signals
  wire [31:0] PCPlus4M;
  wire [31:0] PCTargetM;
  // Writeback stage signals
  wire [31:0] ALUResultW;
  wire [31:0] ReadDataW;
  wire [31:0] PCPlus4W;
  wire [31:0] ResultW;
  wire [31:0] PCTargetW;

  // Fetch stage pipeline register and logic
  mux2    #(32) pcmux(PCPlus4F, PCFinalTargetE, PCSrcE, PCNextF);
  flopenr #(32) pcreg(clk, reset, ~StallF, PCNextF, PCF);
  adder         pcadd(PCF, 32'h4, PCPlus4F);
  
  // Decode stage pipeline register and logic
  flopenrc #(96) regD(clk, reset, FlushD, ~StallD, 
                      {InstrF, PCF, PCPlus4F},
                      {InstrD, PCD, PCPlus4D});
  assign opD       = InstrD[6:0];
  assign funct3D   = InstrD[14:12];
  assign funct7b5D = InstrD[30];
  assign funct7b0D = InstrD[25];
  assign Rs1D      = InstrD[19:15];
  assign Rs2D      = InstrD[24:20];
  assign RdD       = InstrD[11:7];
	
  regfile        rf(clk, RegWriteW, Rs1D, Rs2D, RdW, ResultW, RD1D, RD2D);
  extend         ext(InstrD[31:7], ImmSrcD, ImmExtD);
 
  floprc #(178) regE(clk, reset, FlushE, 
                     {RD1D, RD2D, PCD, Rs1D, Rs2D, RdD, ImmExtD, PCPlus4D,funct3D}, 
                     {RD1E, RD2E, PCE, Rs1E, Rs2E, RdE, ImmExtE, PCPlus4E,funct3E});
	
  mux3   #(32)  faemux(RD1E, ResultW, ALUResultM, ForwardAE, SrcAE);
  mux3   #(32)  fbemux(RD2E, ResultW, ALUResultM, ForwardBE, WriteDataE);
  mux2   #(32)  pctargetmux(PCTargetE, ALUResultE, PCTargetSrcE,PCFinalTargetE); 
  mux2   #(32)  srcbmux(WriteDataE, ImmExtE, ALUSrcE, SrcBE);
  alu           alu(SrcAE, SrcBE, ALUControlE,funct3E, ALUResultE, ZeroE);
  adder         branchadd(ImmExtE, PCE, PCTargetE);

  flopr  #(133) regM(clk, reset, 
                     {ALUResultE, WriteDataE, RdE,PCTargetE, PCPlus4E},
                     {ALUResultM, WriteDataM, RdM,PCTargetM, PCPlus4M});
	
  flopr  #(133) regW(clk, reset, 
                     {ALUResultM, ReadDataM, RdM,PCTargetM, PCPlus4M},
                     {ALUResultW, ReadDataW, RdW,PCTargetW, PCPlus4W});
  mux4   #(32)  resultmux(ALUResultW, ReadDataW, PCPlus4W, PCTargetW, ResultSrcW, ResultW);	
endmodule

module hazard(input   [4:0] Rs1D, Rs2D, Rs1E, Rs2E, RdE, RdM, RdW,
              input         PCSrcE, ResultSrcEb0, 
              input         RegWriteM, RegWriteW,
              output  reg [1:0] ForwardAE, ForwardBE,
              output        StallF, StallD, FlushD, FlushE);

  wire lwStallD;
  
  // forwarding logic
  always @* begin
    ForwardAE = 2'b00;
    ForwardBE = 2'b00;
    if (Rs1E != 5'b0)
      if      ((Rs1E == RdM) & RegWriteM) ForwardAE = 2'b10;
      else if ((Rs1E == RdW) & RegWriteW) ForwardAE = 2'b01;
 
    if (Rs2E != 5'b0)
      if      ((Rs2E == RdM) & RegWriteM) ForwardBE = 2'b10;
      else if ((Rs2E == RdW) & RegWriteW) ForwardBE = 2'b01;
  end
  
  // stalls and flushes
  assign lwStallD = ResultSrcEb0 & ((Rs1D == RdE) | (Rs2D == RdE));  
  assign StallD = lwStallD;
  assign StallF = lwStallD;
  assign FlushD = PCSrcE;
  assign FlushE = lwStallD | PCSrcE;
endmodule

module regfile(input          clk, 
               input          we3, 
               input   [4:0] a1, a2, a3, 
               input   [31:0] wd3, 
               output  [31:0] rd1, rd2);

  reg [31:0] rf[31:0];



  always @(negedge clk)
    if (we3) rf[a3] <= wd3;	

  assign rd1 = (a1 != 0) ? rf[a1] : 0;
  assign rd2 = (a2 != 0) ? rf[a2] : 0;
endmodule

module adder(input  [31:0] a, b,
             output [31:0] y);

  assign y = a + b;
endmodule

module extend(input   [31:7] instr,
              input   [2:0]  immsrc,
              output  reg [31:0] immext);
 
  always @*
    case(immsrc) 
               // I-type 
      3'b000:   immext = {{20{instr[31]}}, instr[31:20]};  
               // S-type (stores)
      3'b001:   immext = {{20{instr[31]}}, instr[31:25], instr[11:7]}; 
               // B-type (branches)
      3'b010:   immext = {{20{instr[31]}}, instr[7], instr[30:25], instr[11:8], 1'b0}; 
               // J-type (jal)
      3'b011:   immext = {{12{instr[31]}}, instr[19:12], instr[20], instr[30:21], 1'b0}; 
					// U-type (auipc)-NEW
		3'b100:	 immext = {instr[31:12],{12{1'b0}}};
		default: immext = 32'bx; // undefined
    endcase             
endmodule

module flopr #(parameter WIDTH = 8)
              (input               clk, reset,
               input   [WIDTH-1:0] d, 
               output  reg [WIDTH-1:0] q);

  always @(posedge clk, posedge reset)
    if (reset) q <= 0;
    else       q <= d;
endmodule

module flopenr #(parameter WIDTH = 8)
                (input               clk, reset, en,
                 input   [WIDTH-1:0] d, 
                 output  reg [WIDTH-1:0] q);

  always @(posedge clk, posedge reset)
    if (reset)   q <= 0;
    else if (en) q <= d;
endmodule

module flopenrc #(parameter WIDTH = 8)
                (input               clk, reset, clear, en,
                 input   [WIDTH-1:0] d, 
                 output  reg [WIDTH-1:0] q);

  always @(posedge clk, posedge reset)
    if (reset)   q <= 0;
    else if (en) 
      if (clear) q <= 0;
      else       q <= d;
endmodule

module floprc #(parameter WIDTH = 8)
              (input   clk,
               input   reset,
               input   clear,
               input   [WIDTH-1:0] d, 
               output  reg [WIDTH-1:0] q);

  always @(posedge clk, posedge reset)
    if (reset) q <= 0;
    else       
      if (clear) q <= 0;
      else       q <= d;
endmodule

module mux2 #(parameter WIDTH = 8)
             (input   [WIDTH-1:0] d0, d1, 
              input               s, 
              output  [WIDTH-1:0] y);

  assign y = s ? d1 : d0; 
endmodule
module mux3 #(parameter WIDTH = 8)
             (input   [WIDTH-1:0] d0, d1, d2,
              input   [1:0]       s, 
              output  [WIDTH-1:0] y);

  assign y = s[1] ? d2 : (s[0] ? d1 : d0); 
endmodule
module mux4 #(parameter WIDTH = 8)
             (input   [WIDTH-1:0] d0, d1, d2,d3,
              input   [1:0]       s, 
              output  [WIDTH-1:0] y);

  assign y = s[1] ? (s[0] ? d3 : d2) : (s[0] ? d1 : d0); 
endmodule

module imem(input   [31:0] a,
            output  [31:0] rd);

  reg [31:0] RAM[63:0];

  initial begin
	 RAM[0]  = 32'h20000113;  // main: 0: addi sp, x0, 512// addi x2, x0, 512
    RAM[1]  = 32'hfe010113;  //       4: addi sp, sp, -32// addi x2, x2, -32
    RAM[2]  = 32'h00112e23;  //       8: sw ra, 28(sp)   // sw x1, 28(x2)
    RAM[3]  = 32'h00812c23;  //      12: sw s0, 24(sp)   // sw x8, 24(x2)
    RAM[4]  = 32'h02010413;  //      16: addi s0, sp, 32 // addi x8, x2, 32
    RAM[5]  = 32'h06200793;  //      20: li a5, 98       // addi x15, x0, 98
    RAM[6]  = 32'hfef42623;  //      24: sw a5, -20(s0)  // sw x15, -20(x8)
    RAM[7]  = 32'h03800793;  //      28: li a5, 56       // addi x15, x0, 56
    RAM[8]  = 32'hfef42423;  //      32: sw a5, -24(s0)  // sw x15, -24(x8)
    RAM[9]  = 32'hfe842583;  //      36: lw a1, -24(s0)  // lw x11, -24(x8)
    RAM[10] = 32'hfec42503;  //      40: lw a0, -20(s0)  // lw x10, -20(x8)
    RAM[11] = 32'h020000ef;  //      44: call gcd        // jal x1, 32
    RAM[12] = 32'h00050793;  //      48: mv a5, a0       // addi x15, x10, 0
    RAM[13] = 32'h00000013;  //      52: nop             // addi x0, x0, 0 
    RAM[14] = 32'h00078513;  //      56: mv a0, a5       // addi x10, x15, 0
    RAM[15] = 32'h01c12083;  //      60: lw ra, 28(sp)   // lw x1, 28(x2)
    RAM[16] = 32'h01812403;  //      64: lw s0, 24(sp)   // lw x8, 24(x2)
    RAM[17] = 32'h02010113;  //      68: addi sp, sp, 32 // addi x2, x2, 32
    RAM[18] = 32'h00008067;  //      72: jr ra           // jalr x0, 0(x1)
    RAM[19] = 32'hfd010113;  // gcd: 76: addi sp, sp, -48// addi x2, x2, -48
    RAM[20] = 32'h02112623;  //      80: sw ra, 44(sp)   // sw x1, 44(x2)
    RAM[21] = 32'h02812423;  //      84: sw s0, 40(sp)   // sw x8, 40(x2)
    RAM[22] = 32'h03010413;  //      88: addi s0, sp, 48 // addi x8, x2, 48
    RAM[23] = 32'hfca42e23;  //      92: sw a0, -36(s0)  // sw x10, -36(x8)
    RAM[24] = 32'hfcb42c23;  //      96: sw a1, -40(s0)  // sw x11, -40(x8)
    RAM[25] = 32'hfdc42703;  //     100: lw a4, -36(s0)  // lw x14, -36(x8)
    RAM[26] = 32'hfd842783;  //     104: lw a5, -40(s0)  // lw x15, -40(x8)
    RAM[27] = 32'h00f75863;  //     108: bge a4, a5, L4  // bge x14, x15, 16
    RAM[28] = 32'hfdc42783;  //     112: lw a5, -36(s0)  // lw x15, -36(x8)
    RAM[29] = 32'hfef42623;  //     116: sw a5, -20(s0)  // sw x15, -20(x8)
    RAM[30] = 32'h03c0006f;  //     120: j L6            // jal x0, 60
    RAM[31] = 32'hfd842783;  // L4: 124: lw a5, -40(s0)  // lw x15, -40(x8)
    RAM[32] = 32'hfef42623;  //     128: sw a5, -20(s0)  // sw x15, -20(x8)
    RAM[33] = 32'h0300006f;  //     132: j L6            // jal x0, 48
    RAM[34] = 32'hfdc42703;  // L9: 136: lw a4, -36(s0)  // lw x14, -36(x8)
    RAM[35] = 32'hfec42783;  //     140: lw a5, -20(s0)  // lw x15, -20(x8)
    RAM[36] = 32'hfcf42e23;  //		144: sw a5, -36(s0)  // sw x15, -36(x8)
    RAM[37] = 32'h02f767b3;  //     148: rem a5, a4, a5  // rem x15, x14, x15
    RAM[38] = 32'hfef42623;  //     152: sw a5, -20(s0)  // sw x15, -20(x8)
    RAM[39] = 32'h00079a63;  //     156: bne a5, zero, L7// bne x15, x0, 20
    RAM[40] = 32'hfd842703;  //     160: lw a4, -40(s0)  // lw x14, -40(x8)
    RAM[41] = 32'hfec42783;  //     164: lw a5, -20(s0)  // lw x15, -20(x8)
    RAM[42] = 32'h02f767b3;  //     168: rem a5, a4, a5  // rem x15, x14, x15
    RAM[43] = 32'h00078e63;  //     172: beq a5, zero,L11// beq x15, x0, 28
    RAM[44] = 32'hfec42783;  // L7: 176: lw a5, -20(s0)  // lw x15, -20(x8)
    RAM[45] = 32'hfec42783;  // L6: 180: lw a5, -20(s0)  // lw x15, -20(x8)
    RAM[46] = 32'hfcf048e3;  //     184: bgt a5, zero, L9// blt x0, x15, -48
    RAM[47] = 32'h0080006f;  //     188: j L8            // jal x0, 8
    RAM[48] = 32'h00000013;  // L11:192: nop             // addi x0, x0, 0
    RAM[49] = 32'hfdc42783;  // L8: 196: lw a5, -36(s0)  // lw x15, -20(x8)
    RAM[50] = 32'h00078513;  //     200: mv a0, a5       // addi x10, x15, 0
    RAM[51] = 32'h02c12083;  //     204: lw ra, 44(sp)   // lw x1, 44(x2)
    RAM[52] = 32'h02812403;  //     208: lw s0, 40(sp)   // lw x8, 40(x2)
    RAM[53] = 32'h03010113;  //     212: addi sp, sp, 48 // addi x2, x2, 48
    RAM[54] = 32'h00008067;  //     216: jr ra           // jalr x0, 0(x1)
end

  assign rd = RAM[a[31:2]]; // word aligned
endmodule

module dmem(input          clk, we,
            input   [31:0] a, wd,
            output  [31:0] rd);

  reg [31:0] RAM[1024:0];

  assign rd = RAM[a[31:2]]; // word aligned

  always @(posedge clk)
    if (we) RAM[a[31:2]] <= wd;
endmodule

module alu(input   [31:0] a, b,
           input   [3:0]  alucontrol,
			  input [2:0] funct3,
           output  reg [31:0] result,
           output         zero);

  wire [31:0] condinvb, sum;
  wire        v;              // overflow
  wire        isAddSub;       // true when is add or subtract operation

  assign condinvb = alucontrol[0] ? ~b : b;
  assign sum = a + condinvb + alucontrol[0];
  assign isAddSub = ~alucontrol[2] & ~alucontrol[1] |
                    ~alucontrol[1] &  alucontrol[0];

  always @*
    case (alucontrol)
      4'b0000:  result = sum;         // add
      4'b0001:  result = sum;         // subtract
      4'b0010:  result = a & b;       // and
      4'b0011:  result = a | b;       // or
      4'b0100:  result = a ^ b;       // xor
      4'b0101:  result = sum[31] ^ v; // slt
      4'b0110:  result = a << b[4:0]; // sll
      4'b0111:  result = a >> b[4:0]; // srl
	   4'b1000: result = a * b;		  //mul-NEW
      4'b1001: result = a / b;		  //div-NEW
      4'b1010: result = b == 0 ? a : a % b; //rem-NEW
		4'b1011: result = a ^ b;		  //xor-NEW
      default: result = 32'bx;
    endcase

  assign zero = funct3[0] == 0 ? funct3[2] == 0 ? (result == 32'b0) : (result[31] == 1'b1 && !v) : funct3[2] == 0 ? (result != 32'b0) : (result[31]  != 1'b1 && result >= 32'b0 && !v) ;
  assign v = (~(alucontrol[0] ^ a[31] ^ b[31]) & (a[31] ^ sum[31]) & isAddSub);// | (alucontrol[0] ^ alucontrol[1] ^ alucontrol[2] ^ a[31] ^ b[31]) & (a[31] ^ sum; // Overflow logic added for: Mul,Div,Rem
  
endmodule

