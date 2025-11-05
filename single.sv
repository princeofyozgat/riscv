module top(input clk, reset, 
           output [31:0] WriteData, DataAdr, 
           output MemWrite);

  wire [31:0] PC, Instr, ReadData;
  
  
  RISCVsingle RISCVsingle(clk, reset, PC, Instr, MemWrite, DataAdr, 
                          WriteData, ReadData);
  imem imem(PC, Instr);
  dmem dmem(clk, MemWrite, DataAdr, WriteData, ReadData);
endmodule

module dmem(input clk, WE,
            input [31:0] A, WD,
            output wire [31:0] RD);

  reg [31:0] RAM[1024:0];

  assign RD = RAM[A[31:2]]; // word aligned

  always @(posedge clk)
    if (WE) RAM[A[31:2]] <= WD;
endmodule

module imem(
    input [31:0] A,
    output wire [31:0] RD
);
  reg [31:0] RAM[63:0]; 

  // Initial block to load instructions into the RAM
  initial begin
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


  assign RD = RAM[A[31:2]];
endmodule



module RISCVsingle(input clk, reset,
                   output wire [31:0] PC,
                   input [31:0] Instr,
                   output wire MemWrite,
                   output wire [31:0] ALUResult, WriteData,
                   input [31:0] ReadData);
 
  wire ALUSrc, RegWrite, Jump, Zero, PCSrc; //bak
  wire [1:0] ResultSrc, ImmSrc;//bak
  wire [2:0] ALUControl;//bak

  controller c(Instr[30],Instr[25], Instr[14:12], Instr[6:0], Zero,
               ResultSrc, MemWrite, PCSrc,
               ALUSrc, RegWrite, Jump,
               ImmSrc, ALUControl);
  datapath dp(clk, reset, ResultSrc, PCSrc,
              ALUSrc, RegWrite,
              ImmSrc, ALUControl,
              Zero, PC, Instr,
              ALUResult, WriteData, ReadData);
endmodule

module controller(input funct7b5, funct7b0,
                  input [2:0] funct3,
                  input [6:0] op,
                  input Zero,
                  output wire [1:0] ResultSrc,
                  output wire MemWrite,
                  output wire PCSrc, ALUSrc,
                  output wire RegWrite, Jump,
                  output wire[1:0] ImmSrc,
                  output wire [2:0] ALUControl);

  wire [1:0] ALUOp;
  wire Branch;

  MainDec md(op, funct3, ResultSrc, MemWrite, Branch,
             ALUSrc, RegWrite, Jump, ImmSrc, ALUOp);
  ALUDec  ad(funct7b5,funct7b0, op[5], funct3, ALUOp, ALUControl);
    
  assign PCSrc = (Branch &  Zero) | Jump;
endmodule

module MainDec(input [6:0] op, input [2:0] funct3,
               output wire [1:0] ResultSrc,
               output wire MemWrite,
               output wire Branch, ALUSrc,
               output wire       RegWrite, Jump,
               output wire [1:0] ImmSrc,
               output wire [1:0] ALUOp);

  reg [10:0] controls;

  assign {RegWrite, ImmSrc, ALUSrc, MemWrite,
          ResultSrc, Branch, ALUOp, Jump} = controls;

  always@(*) begin
		 casez(op)
		 // RegWrite_ImmSrc_ALUSrc_MemWrite_ResultSrc_Branch_ALUOp_Jump
			7'b0000011: controls = 11'b1_00_1_0_01_0_00_0; // lw
			7'b0100011: controls = 11'b0_01_1_1_00_0_00_0; // sw
			7'b0110011: controls = 11'b1_xx_0_0_00_0_10_0; // R-type 
			7'b1100011: controls = 11'b0_10_0_0_00_1_01_0; // BB-typee
			7'b0010011: controls = 11'b1_00_1_0_00_0_10_0; // I-type ALU
			7'b1101111: controls = 11'b1_11_0_0_10_0_00_1; // jal
			7'b1100111: controls = 11'b1_00_1_0_10_0_00_1; // jalr
			7'b0010111: controls = 11'b1_00_1_0_10_0_11_0; // auipc
			default:    controls = 11'bx_xx_x_x_xx_x_xx_x; // non-implemented instruction
		 endcase
  end
endmodule

module ALUDec(input funct7b5, funct7b0, opb5,
              input [2:0] funct3, 
              input [1:0] ALUOp,
              output reg [2:0] ALUControl);

  wire RtypeSub, RtypeMul;
  assign RtypeSub = funct7b5 & opb5;  // true for R-type subtract instruction
  assign RtypeMul = funct7b0 & opb5;
  always@(*) begin
	 case(ALUOp)
      2'b00: ALUControl = 3'b010;         // addition
      2'b01:
        case(funct3)                 
          3'b000: ALUControl = 3'b110; // beq
          3'b100: ALUControl = 3'b110; // blt
          3'b101: ALUControl = 3'b111; // bge
          3'b001: ALUControl = 3'b110;
          default: ALUControl = 3'bxxx; // ???
        endcase
      2'b10: case(funct3)                 // R-type or I-type ALU
               3'b000:  
                 if (RtypeSub) 
                   ALUControl = 3'b110;   // sub
                 else if (RtypeMul)
                   ALUControl = 3'b100;   // mul
                 else 
                   ALUControl = 3'b010;   // add
               3'b110: 
                 if(RtypeMul)
          		   ALUControl = 3'b011; //Yeni-rem
                 else
                   ALUControl = 3'b001; // ort
               3'b111: ALUControl = 3'b000; // and
               default: ALUControl = 3'bxxx; // ???
             endcase
      2'b11: ALUControl = 3'b011;         // auipc
      default: ALUControl = 3'bxxx;       // ???
    endcase
  end
endmodule


module datapath(input clk, reset,
                input [1:0] ResultSrc, 
                input PCSrc, ALUSrc,
                input RegWrite,
                input [1:0] ImmSrc,
                input [2:0] ALUControl,
                output wire Zero,
                output [31:0] PC,
                input [31:0] Instr,
                output wire [31:0] ALUResult, WriteData,
                input [31:0] ReadData);

  reg [31:0] PCNext;
  wire [31:0] PCPlus4, PCTarget, PCJump;
  wire [31:0] ImmExt;
  wire [31:0] SrcA, SrcB;
  wire [31:0] Result;
  wire [2:0] funct3;
  assign funct3 = Instr[14:12];
  // next PC logic
  flopr #(32) pcreg(clk, reset, PCNext, PC);
  adder       pcadd4(PC, 32'd4, PCPlus4);
  adder       pcaddbranch(PC, ImmExt, PCTarget);

  always@(*) begin
    if (Instr[6:0] == 7'b1100111)
      PCNext = (SrcA + ImmExt) & ~32'b1;
    else if (Instr[6:0] == 7'b0010111) // auipc
      PCNext = PC + (ImmExt << 12);
    else
      PCNext = PCSrc ? PCTarget : PCPlus4;
  end

  // register file logic
  RegFile     RF(clk, RegWrite, Instr[19:15], Instr[24:20], 
                 Instr[11:7], Result, SrcA, WriteData);
  Extend      Ext(Instr[31:7], ImmSrc, ImmExt);

  // ALU logic
  mux2 #(32)  SrcBmux(WriteData, ImmExt, ALUSrc, SrcB);
  ALU         ALU(SrcA, SrcB, ALUControl, funct3,ALUResult, Zero);
  mux3 #(32)  Resultmux(ALUResult, ReadData, PCPlus4, ResultSrc, Result);
endmodule


module Extend(input [31:7] Instr,
              input [1:0]  ImmSrc,
              output reg [31:0] ImmExt);
 
  always@(*) begin
    case(ImmSrc) 
               // I-type 
      2'b00:   ImmExt = {{20{Instr[31]}}, Instr[31:20]};  
               // S-type (Stores)
      2'b01:   ImmExt = {{20{Instr[31]}}, Instr[31:25], Instr[11:7]}; 
               // B-type (Branches)
      2'b10:   ImmExt = {{20{Instr[31]}}, Instr[7], Instr[30:25], Instr[11:8], 1'b0}; 
               // J-type (Jumps)
      2'b11:   ImmExt = {{12{Instr[31]}}, Instr[19:12], Instr[20], Instr[30:21], 1'b0}; 
      default: ImmExt = 32'bx; // undefined
    endcase
  end
endmodule

module RegFile(input clk, 
               input WE3, 
               input [ 4:0] A1, A2, A3, 
               input [31:0] WD3, 
               output wire [31:0] RD1, RD2);

  reg [31:0] rf[31:0];



  always @(posedge clk)
    if (WE3) rf[A3] <= WD3;	

  assign RD1 = (A1 != 0) ? rf[A1] : 0;
  assign RD2 = (A2 != 0) ? rf[A2] : 0;
endmodule

module adder(input  [31:0] a, b,
             output [31:0] y);

  assign y = a + b;
endmodule

module flopr #(parameter WIDTH = 8)
              (input clk, reset,
               input [WIDTH-1:0] d, 
               output reg [WIDTH-1:0] q);

  always@(posedge clk, posedge reset)
    if (reset) q <= 0;
    else       q <= d;
endmodule

module mux2 #(parameter WIDTH = 8)
             (input [WIDTH-1:0] d0, d1, 
              input s, 
              output wire [WIDTH-1:0] y);

  assign y = s ? d1 : d0; 
endmodule

module mux3 #(parameter WIDTH = 8)
             (input [WIDTH-1:0] d0, d1, d2,
              input [1:0] s, 
              output wire [WIDTH-1:0] y);

  assign y = s[1] ? d2 : (s[0] ? d1 : d0); 
endmodule

module ALU (input [31:0] A, B,
            input [2:0]  ALUControl,
				input [2:0] funct3,
            output reg [31:0] Result,
            output wire Zero
            );

  wire [31:0] condinvB, sum, product; 
  wire isAddSub;
  assign condinvB = ALUControl[2] ? ~B : B;
  assign sum = A + condinvB + ALUControl[2];
  assign product = A*B;
  assign isAddSub = ~ALUControl[2] & ~ALUControl[1] | ~ALUControl[1] & ALUControl[0];
  always@(*) begin
    case (ALUControl)
      3'b000: Result = A & B;
      3'b001: Result = A | B;
      3'b010: Result = sum;
      3'b110: Result = sum;
      3'b011: Result = A % B;
      3'b100: Result = product;
      3'b111: Result = sum[31];
    endcase
  end
  assign Zero = funct3[0] == 0 ? funct3[2] == 0 ? (Result == 32'b0) : (Result[31] == 1'b1 && !v) : funct3[2] == 0 ? (Result != 32'b0) : (Result[31]  != 1'b1 && Result >= 32'b0 && !v) ;
  assign v = (~(ALUControl[0] ^ A[31] ^ B[31]) & (A[31] ^ sum[31]) & isAddSub);// | (alucontrol[0] ^ alucontrol[1] ^ alucontrol[2] ^ a[31] ^ b[31]) & (a[31] ^ sum; // Overflow logic added for: Mul,Div,Rem

endmodule

