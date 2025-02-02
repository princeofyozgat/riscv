`timescale 1ns / 1ps

module top(input         clk, reset, 
           output [31:0] WriteData, DataAdr, 
           output        MemWrite);

  wire [31:0] ReadData;
  
  // instantiate processor and memories
  riscvmulti rvmulti(clk, reset, MemWrite, DataAdr, 
                     WriteData, ReadData);
  mem mem(clk, MemWrite, DataAdr, WriteData, ReadData);
endmodule

module riscvmulti(input          clk, reset,
                  output         MemWrite,
                  output  [31:0] Adr, WriteData,
                  input   [31:0] ReadData);

  wire        RegWrite, jump;
  wire [1:0]  ResultSrc; 
  wire [2:0]  ImmSrc;
  wire [3:0]  ALUControl;
  wire 	     PCWrite;
  wire 	     IRWrite;
  wire [1:0]  ALUSrcA;
  wire [1:0]  ALUSrcB;
  wire	     AdrSrc;
  wire        Zero;
  wire [6:0]  op;
  wire [2:0]  funct3;
  wire        funct7b5,funct7b0;

  controller c(clk, reset, op, funct3, funct7b5,funct7b0, Zero, 
               ImmSrc, ALUSrcA, ALUSrcB,
               ResultSrc, AdrSrc, ALUControl,
               IRWrite, PCWrite, RegWrite, MemWrite);
               
  datapath   dp(clk, reset, 
                ImmSrc, ALUSrcA, ALUSrcB,
                ResultSrc, AdrSrc, IRWrite, PCWrite, 
                RegWrite, MemWrite, ALUControl, op, funct3, 
                funct7b5,funct7b0, Zero, Adr, ReadData, WriteData);
endmodule

module controller(input         clk,
                  input         reset,  
                  input   [6:0] op,
                  input   [2:0] funct3,
                  input         funct7b5, funct7b0,
                  input         Zero,
                  output  [2:0] ImmSrc,
                  output  [1:0] ALUSrcA, 
						output  [1:0] ALUSrcB,
                  output  [1:0] ResultSrc, 
                  output        AdrSrc,
                  output  [3:0] ALUControl,
                  output        IRWrite, PCWrite, 
                  output        RegWrite, MemWrite);

  wire [1:0] ALUOp;
  wire       Branch, PCUpdate;

  // Main FSM
  mainfsm fsm(clk, reset, op,
              ALUSrcA, ALUSrcB, ResultSrc, AdrSrc, 
              IRWrite, PCUpdate, RegWrite, MemWrite, 
              ALUOp, Branch);

  // ALU Decoder
  aludec  ad(op[5], funct3, funct7b5,funct7b0, ALUOp, ALUControl);
  
  // Instruction Decoder
  instrdec id(op, ImmSrc);
  
  // Branch logic
  assign PCWrite = (Branch & Zero) | PCUpdate; 
  
endmodule

module mainfsm(input          clk,
               input          reset,
               input  [6:0]   op,
               output [1:0]   ALUSrcA, ALUSrcB,
               output [1:0]   ResultSrc,
               output         AdrSrc,  
               output         IRWrite, PCUpdate,
               output         RegWrite, MemWrite,
               output [1:0]   ALUOp,
               output         Branch);  
              
  //typedef enum reg [3:0] {FETCH, DECODE, MEMADR, MEMREAD, MEMWB, MEMWRITE,
  //                          EXECUTER,EXECUTEI,AUIPC, ALUWB, 
  //                          BRA,JAL,JALR, UNKNOWN} statetype;
  // 0: FETCH, 1: DECODE, 2: MEMADR, 3: MEMREAD, 4: MEMWB, 5: MEMWRITE,
  // 6: EXECUTER, 7: EXECUTEI, 8: AUIPC, 9: ALUWB, 
  // 10: BRA, 11: JAL, 12: JALR, 13: UNKNOWN
  reg [3:0] state, nextstate;
  reg [14:0] controls;
  
  // state register
  always @(posedge clk or posedge reset)
    if (reset) state <= 4'd0;
    else state <= nextstate;
  
  // next state logic
  always @(*) begin
    casex(state)
      4'd0/*FETCH*/:         nextstate = 4'd1;  // DECODE
      4'd1/*DECODE*/: 
		   casex(op)
            7'b0?00011:      nextstate = 4'd2;  // MEMADR: lw or sw
            7'b0110011:      nextstate = 4'd6;  // EXECUTER: R-type
        		7'b0010011:      nextstate = 4'd7;  // EXECUTEI: I-type(G NCELLENDI)
        		7'b0010111:		  nextstate = 4'd8;  // AUIPC:(YENI)
            7'b1100011:      nextstate = 4'd10; // BRA: B-type
            7'b1101111:      nextstate = 4'd11; // JAL:
        		7'b1100111:		  nextstate = 4'd12; // JALR:
            default:         nextstate = 4'd13;
         endcase
      4'd2/*MEMADR*/: 
        if (op[5])           nextstate = 4'd5;  // MEMWRITE: sw
        else                 nextstate = 4'd3;  // MEMREAD:  lw
      4'd3/*MEMREAD*/:       nextstate = 4'd4;  // MEMWB:
      4'd6/*EXECUTER*/:      nextstate = 4'd9;  // ALUWB:
      4'd7/*EXECUTEI*/:      nextstate = 4'd9;	// ALUWB:
      4'd11/*JAL*/:          nextstate = 4'd9;  // ALUWB:
      default:               nextstate = 4'd0;  // FETCH:
    endcase
  end 
  // state-dependent output logic
  always @(*) begin
    casex(state)
      4'd0/*FETCH*/: 	 controls = 15'b00_10_10_0_1100_00_0; 
      4'd1/*DECODE*/: if(op == 7'b1100111)
        		             controls = 15'b10_01_00_0_0010_00_0;
        		          else	
        			          controls = 15'b01_01_00_0_0000_00_0;      
      4'd2/*MEMADR*/:    controls = 15'b10_01_00_0_0000_00_0;
      4'd3/*MEMREAD*/:   controls = 15'b00_00_00_1_0000_00_0;
      4'd5/*MEMWRITE*/:  controls = 15'b00_00_00_1_0001_00_0;
      4'd4/*MEMWB*/:     controls = 15'b00_00_01_0_0010_00_0;
      4'd6/*EXECUTER*/:  controls = 15'b10_00_00_0_0000_10_0;
      4'd7/*EXECUTEI*/:  controls = 15'b10_01_00_0_0000_10_0;
      4'd8/*AUIPC*/:	    controls = 15'b01_01_00_0_0010_00_0;
      4'd9/*ALUWB*/:     controls = 15'b00_00_00_0_0010_00_0;
      4'd10/*BRA*/:      controls = 15'b10_00_00_0_0000_01_1; //(EKLEME YAPILDI)
      4'd11/*JAL*/:      controls = 15'b01_10_00_x_0100_00_0;
      4'd12/*JALR*/:		 controls = 15'b10_01_10_0_0100_00_0;//(YENI)
      default:           controls = 15'bxx_xx_xx_x_xxxx_xx_x;
    endcase
  end
  assign {ALUSrcA, ALUSrcB, ResultSrc, AdrSrc, IRWrite, PCUpdate, 
  RegWrite, MemWrite, ALUOp, Branch} = controls;
          
endmodule  

module aludec(input        opb5,
              input  [2:0] funct3,
              input        funct7b5,funct7b0, 
              input  [1:0] ALUOp,
              output reg [3:0] ALUControl);

  wire RtypeSub,RtypeExt;
  assign RtypeSub = funct7b5 & opb5;  // TRUE for R-type subtract instruction
  assign RtypeExt = funct7b0 & opb5; //TRUE for R-type Extended instructions(MUL,DIV etc.)
  always @(*) begin
    case(ALUOp)
      2'b00: ALUControl = 4'b0000; // addition
      2'b01: ALUControl = 4'b0001; // subtraction
      default: case(funct3) // R-type or I-type ALU
                 3'b000:  
					     if (RtypeSub) 
                       ALUControl = 4'b0001; // sub
        				  else if(RtypeExt)
          				  ALUControl = 4'b1000; // MUL(NEW)
                    else          
                       ALUControl = 4'b0000; // add, addi
                 3'b010:    
					     ALUControl = 4'b0101; // slt, slti
        		     3'b100:
                    if(RtypeExt)
                       ALUControl = 4'b1001; // DIV(NEW)
        				  else
                       ALUControl = 4'b1011; // XOR,XORI(NEW)
        		 3'b110:  
				        if(RtypeExt)
          			 	  ALUControl = 4'b1010; //REM(NEW)
          		     else
                    	  ALUControl = 4'b0011; // or, ori
                 3'b111:    
					     ALUControl = 4'b0010; // and, andi
                 default:   
					     ALUControl = 4'bxxxx; // ???
               endcase
    endcase
  end
endmodule

module instrdec (input  [6:0] op, 
                 output reg [2:0] ImmSrc);
  always @(*) begin
    case(op)
      7'b0110011: ImmSrc = 3'bxxx; // R-type
      7'b0010011: ImmSrc = 3'b000; // I-type ALU
      7'b0000011: ImmSrc = 3'b000; // lw
      7'b0100011: ImmSrc = 3'b001; // sw
      7'b1100011: ImmSrc = 3'b010; // B-type
      7'b1101111: ImmSrc = 3'b011; // jal
      7'b1100111: ImmSrc = 3'b000; // jalr
      7'b0010111: ImmSrc = 3'b100; // auipc(YENI)
      default:    ImmSrc = 3'bxxx; // ???
    endcase
  end
endmodule

module datapath(input         clk, reset,
                input  [2:0]  ImmSrc,
					 input  [1:0]  ALUSrcA, ALUSrcB, 
                input  [1:0]  ResultSrc, 
					 input         AdrSrc,
                input         IRWrite, PCWrite,
                input         RegWrite, MemWrite,
                input  [3:0]  alucontrol,
                output [6:0]  op,
                output [2:0]  funct3,
                output        funct7b5,funct7b0,
                output        Zero,
                output [31:0] Adr,
                input  [31:0] ReadData,
                output [31:0] WriteData);

  wire [31:0] PC, OldPC, Instr, immext, ALUResult;
  wire [31:0] SrcA, SrcB, RD1, RD2, A;
  wire [31:0] Result, Data, ALUOut;


  // next PC logic
  flopenr #(32) pcreg(clk, reset, PCWrite, Result, PC);
  flopenr #(32) oldpcreg(clk, reset, IRWrite, PC, OldPC);
  
  // memory logic
  mux2    #(32) adrmux(PC, Result, AdrSrc, Adr);
  flopenr #(32) ir(clk, reset, IRWrite, ReadData, Instr);
  flopr   #(32) datareg(clk, reset, ReadData, Data);
 
  // F logic
  regfile       rf(clk, RegWrite, Instr[19:15], Instr[24:20], 
                   Instr[11:7], Result, RD1, RD2);
  extend        ext(Instr[31:7], ImmSrc, immext);
  flopr  #(32)  srcareg(clk, reset, RD1, A);
  flopr  #(32)  wdreg(clk, reset, RD2, WriteData);

  // ALU logic
  mux3   #(32)  srcamux(PC, OldPC, A, ALUSrcA, SrcA);
  mux3   #(32)  srcbmux(WriteData, immext, 32'd4, ALUSrcB, SrcB);
  alu           alu(SrcA, SrcB, alucontrol,funct3, ALUResult, Zero);
  flopr  #(32)  aluoutreg(clk, reset, ALUResult, ALUOut);
  mux3   #(32)  resmux(ALUOut, Data, ALUResult, ResultSrc, Result);
  
  // outputs to control unit
  assign op       = Instr[6:0];
  assign funct3   = Instr[14:12];
  assign funct7b5 = Instr[30];
  assign funct7b0 = Instr[25];
  
endmodule


module regfile(input         clk, 
               input         we3, 
               input  [ 4:0] a1, a2, a3, 
               input  [31:0] wd3, 
               output [31:0] rd1, rd2);

  reg [31:0] rf[31:0];

  // three ported register file
  // read two ports combinationally (A1/RD1, A2/RD2)
  // write third port on rising edge of clock (A3/WD3/WE3)
  // register 0 hardwired to 0

  always @(posedge clk)
    if (we3) rf[a3] <= wd3;	

  assign rd1 = (a1 != 0) ? rf[a1] : 0;
  assign rd2 = (a2 != 0) ? rf[a2] : 0;
endmodule

module adder(input  [31:0] a, b,
             output [31:0] y);

  assign y = a + b;
endmodule

module extend(input  [31:7] instr,
              input  [2:0]  immsrc,
              output reg [31:0] immext);
 
  always @(*) begin
    case(immsrc) 
               // I-type 
      3'b000:   immext = {{20{instr[31]}}, instr[31:20]};  
               // S-type (stores)
      3'b001:   immext = {{20{instr[31]}}, instr[31:25], instr[11:7]}; 
               // B-type (branches)
      3'b010:   immext = {{20{instr[31]}}, instr[7], instr[30:25], instr[11:8], 1'b0}; 
               // J-type (jal)
      3'b011:   immext = {{12{instr[31]}}, instr[19:12], instr[20], instr[30:21], 1'b0};
      		   // AUIPC,LUI
      3'b100: 	immext = {instr[31:12],12'b0};
      default: immext = 32'bx; // undefined
    endcase 
  end
endmodule

module flopr #(parameter WIDTH = 8)
              (input              clk, reset,
               input  [WIDTH-1:0] d, 
               output reg [WIDTH-1:0] q);

  always @(posedge clk, posedge reset)
    if (reset) q <= 0;
    else       q <= d;
endmodule

module flopenr #(parameter WIDTH = 8)
                (input              clk, reset, en,
                 input  [WIDTH-1:0] d, 
                 output reg [WIDTH-1:0] q);

  always @(posedge clk, posedge reset)
    if (reset)   q <= 0;
    else if (en) q <= d;
endmodule

module mux2 #(parameter WIDTH = 8)
             (input  [WIDTH-1:0] d0, d1, 
              input              s, 
              output [WIDTH-1:0] y);

  assign y = s ? d1 : d0; 
endmodule

module mux3 #(parameter WIDTH = 8)
             (input  [WIDTH-1:0] d0, d1, d2,
              input  [1:0]       s, 
              output [WIDTH-1:0] y);

  assign y = s[1] ? d2 : (s[0] ? d1 : d0); 
endmodule

module mux4 #(parameter WIDTH = 8)
             (input  [WIDTH-1:0] d0, d1, d2, d3,
              input  [1:0]       s, 
              output [WIDTH-1:0] y);

  assign y = s[1] ? (s[0] ? d3: d2) : (s[0] ? d1 : d0); 
endmodule

module mem(input         clk, we,
           input  [31:0] a, wd,
           output [31:0] rd);

  reg [31:0] RAM[1024:0];
      
  initial begin
    //RAM[0] = 32'h1f400113;----|
    //RAM[1] = 32'h014100e7;------->JALR testi
    //RAM[130] = 32'h00000013;--|
    RAM[0]  = 32'h10000113;
    RAM[1]  = 32'hfe010113;
    RAM[2]  = 32'h00112e23;
    RAM[3]  = 32'h00812c23;
    RAM[4]  = 32'h02010413;
    RAM[5]  = 32'h06200793;
    RAM[6]  = 32'hfef42623;
    RAM[7]  = 32'h03800793;
    RAM[8]  = 32'hfef42423;
    RAM[9]  = 32'hfe842583;
    RAM[10] = 32'hfec42503;
    RAM[11] = 32'h020000ef;
    RAM[12] = 32'h00050793;
    RAM[13] = 32'h00000013;
    RAM[14] = 32'h00078513;
    RAM[15] = 32'h01c12083;
    RAM[16] = 32'h01812403;
    RAM[17] = 32'h02010113;
    RAM[18] = 32'h00008067;
    RAM[19] = 32'hfd010113;
    RAM[20] = 32'h02112623;
    RAM[21] = 32'h02812423;
    RAM[22] = 32'h03010413;
    RAM[23] = 32'hfca42e23;
    RAM[24] = 32'hfcb42c23;
    RAM[25] = 32'hfdc42703;
    RAM[26] = 32'hfd842783;
    RAM[27] = 32'h00f75863;
    RAM[28] = 32'hfdc42783;
    RAM[29] = 32'hfef42623;
    RAM[30] = 32'h03c0006f;
    RAM[31] = 32'hfd842783;
    RAM[32] = 32'hfef42623;
    RAM[33] = 32'h0300006f;
    RAM[34] = 32'hfdc42703;
    RAM[35] = 32'hfec42783;
    RAM[36] = 32'h02f767b3;
    RAM[37] = 32'h00079a63;
    RAM[38] = 32'hfd842703;
    RAM[39] = 32'hfec42783;
    RAM[40] = 32'h02f767b3;
    RAM[41] = 32'h00078e63;
    RAM[42] = 32'hfec42783;
    RAM[43] = 32'hfff78793;
    RAM[44] = 32'hfef42623;
    RAM[45] = 32'hfec42783;
    RAM[46] = 32'hfcf048e3;
    RAM[47] = 32'h0080006f;
    RAM[48] = 32'h00000013;
    RAM[49] = 32'hfec42783;
    RAM[50] = 32'h00078513;
    RAM[51] = 32'h02c12083;
    RAM[52] = 32'h02812403;
    RAM[53] = 32'h03010113;
    RAM[54] = 32'h00008067;
  end 
  assign rd = RAM[a[31:2]]; // word aligned

  always @(posedge clk)
    if (we) RAM[a[31:2]] <= wd;
endmodule

module alu(input  [31:0] a, b,
           input  [3:0]  alucontrol,
           input [2:0] funct3,
           output reg [31:0] result,
           output        zero);

  wire [31:0] condinvb, sum;
  wire        v;              // overflow
  wire        isAddSub;       // true when is add or subtract operation

  assign condinvb = alucontrol[0] ? ~b : b;
  assign sum = a + condinvb + alucontrol[0];
  assign isAddSub = ~alucontrol[2] & ~alucontrol[1] |
                    ~alucontrol[1] &  alucontrol[0];

  always @(*) begin
    case (alucontrol)
      4'b0000:  result = sum;         // add
      4'b0001:  result = sum;         // subtract
      4'b0010:  result = a & b;       // and
      4'b0011:  result = a | b;       // or
      4'b0100:  result = a ^ b;       // xor
      4'b0101:  result = sum[31] ^ v; // slt
      4'b0110:  result = a << b[4:0]; // sll
      4'b0111:  result = a >> b[4:0]; // srl
      4'b1000: result = a * b; //mul(NEW)
      4'b1001: result = a / b;  //div(NEW)
      4'b1010: result = a % b; //rem(NEW)
      4'b1011: result = a ^ b; // xor(NEW)
      default: result = 32'bx;
    endcase
  end
  assign zero = funct3[0] == 0 ? funct3[2] == 0 ? (result == 32'b0) : (result[31] == 1'b1 && !v) : funct3[2] == 0 ? (result != 32'b0) : (result[31]  != 1'b1 && result >= 32'b0 && !v) ;
  assign v = ~(alucontrol[0] ^ a[31] ^ b[31]) & (a[31] ^ sum[31]) & isAddSub;
endmodule
