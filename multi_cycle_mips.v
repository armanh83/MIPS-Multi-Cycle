
`timescale 1ns/100ps

   `define ADD  4'h0
   `define SUB  4'h1
   `define SLT  4'h2
   `define SLTU 4'h3
   `define AND  4'h4
   `define OR   4'h5
   `define NOR  4'h6
   `define XOR  4'h7
   `define LUI  4'h8
   `define JUMP    4'h9
   `define JR      4'ha
module multi_cycle_mips(

   input clk,
   input reset,

   // Memory Ports
   output  [31:0] mem_addr,
   input   [31:0] mem_read_data,
   output  [31:0] mem_write_data,
   output         mem_read,
   output         mem_write
);

   // Data Path Registers
   reg MRE, MWE;
   reg [31:0] A, B, PC, IR, MDR, MAR,regw,hi,lo;
   wire [31:0] hi1,lo1;

   // Data Path Control Lines, don't forget, regs are not always register !!
   reg setMRE, clrMRE, setMWE, clrMWE;
   reg Awrt, Bwrt, RFwrt, PCwrt, IRwrt, MDRwrt, MARwrt;

   // Memory Ports Bindings
   assign mem_addr = MAR;
   assign mem_read = MRE;
   assign mem_write = MWE;
   assign mem_write_data = B;

   // Mux & ALU Control Line
   reg [3:0] AluOP;
   reg [1:0] aluSelB,SgnExt;
   reg  aluSelA,  RegDst, IorD;
   reg [1:0] MemtoReg;
   reg link; // for jal setting wr to reg 31
   // Wiring
   wire aluZero;
   wire [31:0] aluResult, rfRD1, rfRD2;

   // Clocked Registers
   always @( posedge clk ) begin
      if( reset )
         PC <= #0.1 32'h00000000;
      else if( PCwrt )
         PC <= #0.1 aluResult;

      if( Awrt ) A <= #0.1 rfRD1;
      if( Bwrt ) B <= #0.1 rfRD2;

      if( MARwrt ) MAR <= #0.1 IorD ? aluResult : PC;

      if( IRwrt ) IR <= #0.1 mem_read_data;
      if( MDRwrt ) MDR <= #0.1 mem_read_data;

      if( reset | clrMRE ) MRE <= #0.1 1'b0;
          else if( setMRE) MRE <= #0.1 1'b1;

      if( reset | clrMWE ) MWE <= #0.1 1'b0;
          else if( setMWE) MWE <= #0.1 1'b1;
   end

   // Register File
   reg_file rf(
      .clk( clk ),
      .write( RFwrt ),

      .RR1( IR[25:21] ),
      .RR2( IR[20:16] ),
      .RD1( rfRD1 ),
      .RD2( rfRD2 ),

      .WR(link ? 5'b11111 : RegDst ? IR[15:11] : IR[20:16] ),
      .WD( regw )
   );


   // Sign/Zero Extension
   //wire [31:0] SZout = SgnExt ? {{16{IR[15]}}, IR[15:0]} : {16'h0000, IR[15:0]};
   reg [31:0] SZout;
   always @(*)
   case (SgnExt)
      2'b00: SZout= {16'h0000, IR[15:0]};
      2'b01: SZout = {{16{IR[15]}}, IR[15:0]};
      2'b10: SZout ={PC[31:28],IR[25:0],2'b00} ;
   endcase

   always @(*)
   case (MemtoReg)
      2'b00: regw= aluResult;
      2'b01: regw = MDR;
      2'b10: regw = hi1 ;
      2'b11: regw =lo1;
   endcase
   // ALU-A Mux
   wire [31:0] aluA = aluSelA ? A : PC;

   // ALU-B Mux
   reg [31:0] aluB;
   always @(*)
   case (aluSelB)
      2'b00: aluB = B;
      2'b01: aluB = 32'h4;
      2'b10: aluB = SZout;
      2'b11: aluB = SZout << 2;
   endcase

   my_alu alu(
      .A( aluA ),
      .B( aluB ),
      .Op( AluOP ),

      .X( aluResult ),
      .Z( aluZero )
   );
  
   wire ready1,mult_start1;
   wire [63:0] output_mult; 
reg ready,mult_start;

assign mult_start1=mult_start;
assign hi1=output_mult[63:32];
assign lo1=output_mult[31:0];
   multiplier1 mult(
 .A(aluA),
 .B( aluB ),
 .Product(output_mult),
 .ready(ready1),
 .clk(clk),
 .start(mult_start1)
   );

   // Controller Starts Here

   // Controller State Registers
   reg [4:0] state, nxt_state;
   
   // State Names & Numbers
   localparam
      RESET = 0, FETCH1 = 1, FETCH2 = 2, FETCH3 = 3, DECODE = 4,
      EX_ALU_R = 7, EX_ALU_I = 8,EX_MULT3=9,
      EX_LW_1 = 11, EX_LW_2 = 12, EX_LW_3 = 13, EX_LW_4 = 14, EX_LW_5 = 15,
      EX_SW_1 = 21, EX_SW_2 = 22, EX_SW_3 = 23,
      EX_BRA_1 = 25, EX_BRA_2 = 26, EX_J = 27,EX_JR=28,EX_MULT1=29,EX_MULT2=30,EX_MOVE=31;

   // State Clocked Register 
   always @(posedge clk)
      if(reset)
         state <= #0.1 RESET;
      else
         state <= #0.1 nxt_state;

   task PrepareFetch;
      begin
         IorD = 0;
         setMRE = 1;
         MARwrt = 1;
         nxt_state = FETCH1;
      end
   endtask

   // State Machine Body Starts Here
   always @( * ) begin

      nxt_state = 'bx;

      SgnExt = 'bx; IorD = 'bx;
      MemtoReg = 'bx; RegDst = 'bx;
      aluSelA = 'bx; aluSelB = 'bx; AluOP = 'bx;
      link=0;
      mult_start=1'b0;
      PCwrt = 0;
      Awrt = 0; Bwrt = 0;
      RFwrt = 0; IRwrt = 0;
      MDRwrt = 0; MARwrt = 0;
      setMRE = 0; clrMRE = 0;
      setMWE = 0; clrMWE = 0;

      case(state)

         RESET:
            PrepareFetch;

         FETCH1:
         
            nxt_state = FETCH2;

         FETCH2:
            nxt_state = FETCH3;

         FETCH3: begin
            IRwrt = 1;
            PCwrt = 1;
            clrMRE = 1;
            aluSelA = 0;
            aluSelB = 2'b01; // pc+4
            AluOP = `ADD;
            nxt_state = DECODE;
         end

         DECODE: begin
            Awrt = 1;
            Bwrt = 1;
            case( IR[31:26] )
               6'b000_000:    
         // R-format
                  case( IR[5:3] )
                     3'b000: ;
                     3'b001:begin
                        case (IR[0])
                        1'b1:
                        begin
                     aluSelA=1'b0;
                     
                     AluOP=`JR;
                     RFwrt = 1'b1;
                     MemtoReg = 1'b0;
                     link = 1'b1;
                      nxt_state=EX_JR;
                        end
                        1'b0: nxt_state=EX_JR;
                        endcase
                     end
                      
                     3'b010: nxt_state=EX_MOVE; 

                     3'b011: begin
                       
                     
                     nxt_state=EX_MULT1;
                      
                     end
                     3'b100: nxt_state = EX_ALU_R;
                     3'b101: nxt_state = EX_ALU_R;
                     3'b110: ;
                     3'b111: ;
                  endcase

               6'b001_000,             // addi
               6'b001_001,             // addiu
               6'b001_010,             // slti
               6'b001_011,             // sltiu
               6'b001_100,             // andi
               6'b001_101,             // ori
               6'b001_110,            // xori
               6'b001_111:             //lui
                  nxt_state = EX_ALU_I;

               6'b100_011:
                  nxt_state = EX_LW_1;

               6'b101_011:
                  nxt_state = EX_SW_1;

               6'b000_100,
               6'b000_101:
                  nxt_state = EX_BRA_1;
               6'b000_010 :
                   nxt_state = EX_J;
               6'b000_011 :
                  begin
                     aluSelA=1'b0;
                     AluOP=`JR;
                     RFwrt = 1'b1;
                     MemtoReg = 1'b0;
                     link = 1'b1;
                     nxt_state = EX_J;
                  end
                  

               // rest of instructiones should be decoded here

            endcase
         end
   

         EX_ALU_R: begin
         MARwrt=1'b0;
         MDRwrt=1'b0;
         IRwrt=1'b0;
         aluSelA=1'b1;
         aluSelB=2'b0;
         
         SgnExt = 1'bx;
         RegDst = 1'b1;
         MemtoReg = 1'b0;
         RFwrt = 1'b1;
            case(IR[3:0]) 
         4'b0000:     AluOP=`ADD;  //add
         4'b0001:     AluOP=`ADD;  //addu
         4'b0010:     AluOP=`SUB;  //sub
         4'b0011:     AluOP=`SUB;  //subu
         4'b0100:     AluOP=`AND;  //and
         4'b0101:     AluOP=`OR;   //or
         4'b0110:     AluOP=`XOR;  //xor
         4'b0111:     AluOP=`NOR;  //nor
         4'b1010:     AluOP=`SLT;  //slt
         4'b1011:     AluOP=`SLTU; //sltu

         endcase
         PrepareFetch;
         end

         EX_ALU_I: begin
         MARwrt=1'b0;
         MDRwrt=1'b0;
         IRwrt=1'b0;
         link=1'b0;
         aluSelA = 1'b1;
         aluSelB = 2'b10;
         RegDst = 1'b0;
         MemtoReg = 1'b0;
         RFwrt = 1'b1;
         case (IR[31:26])
               6'b001_000:             // addi
               begin
               SgnExt=1'b1;
               AluOP=`ADD;
               end
               6'b001_001:             // addiu
               begin
               SgnExt=1'b0;
               AluOP=`ADD;
               end
               6'b001_010:             // slti
               begin
               SgnExt=1'b1;
               AluOP=`SLT;
               end
               6'b001_011:             // sltiu
               begin
               SgnExt=1'b0;
               AluOP=`SLT;   
               end
               6'b001_100:             // andi
               begin
               SgnExt=1'b0;
               AluOP=`AND;   
               end
               6'b001_101:             // ori
               begin
               SgnExt=1'b0;
               AluOP=`OR;   
               end
               6'b001_110:             // xori
               begin
               SgnExt=1'b0;
               AluOP=`XOR;   
               end
               6'b001_111:             //lui
               begin
                  SgnExt=1'b0;
                 AluOP =`LUI; 
               end
         endcase
         
           PrepareFetch;
         end

         EX_LW_1: begin
         MARwrt=1'b1;
         aluSelA = 1'b1;
         aluSelB = 2'b10;
         SgnExt=1'b1;
         setMRE=1'b1;
         AluOP=`ADD;
         IorD=1'b1;
          nxt_state=EX_LW_2;
         end
         EX_LW_2: begin
            nxt_state=EX_LW_3;
         end
         EX_LW_3: begin
            nxt_state=EX_LW_4;
         end
         EX_LW_4: begin
            clrMRE=1'b1; 
            MDRwrt=1'b1;
           nxt_state=EX_LW_5;
         end
         EX_LW_5: begin
            MemtoReg=1'b1;
            RegDst = 1'b0;
            RFwrt = 1'b1;
           PrepareFetch;
         end


         EX_SW_1: begin
         IRwrt=1'b0;
         aluSelA = 1'b1;
         aluSelB = 2'b10;
         MARwrt=1'b1;
         IorD=1'b1;
         SgnExt=1'b1;
         setMWE=1'b1;
         AluOP=`ADD;
         nxt_state= EX_SW_2;
         end
         EX_SW_2: begin
           clrMWE=1'b1;
          nxt_state= EX_SW_3;
         end
         EX_SW_3: begin
           PrepareFetch;
         end


         EX_BRA_1: begin
            aluSelA = 1'b1;
            aluSelB = 2'b0;
            AluOP=`SUB;
            if(IR[26]==1'b0)begin
            if(aluZero)begin
               nxt_state=EX_BRA_2;
            end
            else
            begin
               PrepareFetch;
            end
            end
            else
            begin
            if(!aluZero)begin
               nxt_state=EX_BRA_2;
            end
            else
            begin
               PrepareFetch;
            end
            end
            
         end
         EX_BRA_2: begin
            SgnExt=1'b1;
            aluSelA = 1'b0;
            aluSelB = 2'b11;
            AluOP=`ADD;
            MARwrt=1'b1;
            IorD=1'b1;
            PCwrt=1'b1;
            setMRE=1'b1;
           nxt_state=FETCH1;
         end
          EX_J: begin
            SgnExt=2'b10;
            aluSelB = 2'b10;
            AluOP=`JUMP;
            MARwrt=1'b1;
            IorD=1'b1;
            PCwrt=1'b1;
            setMRE=1'b1;
            link = 0;
           nxt_state=FETCH1;

         end
         EX_JR:
         begin
            link = 0;
            aluSelA = 1'b1;
            AluOP=`JR;
            MARwrt=1'b1;
            IorD=1'b1;
            PCwrt=1'b1;
            setMRE=1'b1;
            link = 0;
           nxt_state=FETCH1;
         end
EX_MOVE: begin
         RegDst = 1'b1;
         RFwrt = 1'b1;
         if(IR[1])
         MemtoReg=2'b11;
         else 
         MemtoReg=2'b10;

         PrepareFetch;
end
EX_MULT1: begin

                     aluSelA = 1'b1;
                      aluSelB=1'b0;
                     mult_start = 1'b1; 

   nxt_state=EX_MULT2;
   
end
EX_MULT2: begin
   nxt_state = EX_MULT2;
   if(ready1)
   nxt_state=EX_MULT3;
end
EX_MULT3: begin
   hi=hi1;
   lo=lo1;
   PrepareFetch;
end

      endcase

   end

endmodule

//==============================================================================

module my_alu(
   input  [3:0] Op,
   input  [31:0] A,
   input  [31:0] B,
   output [31:0] X,
   output        Z
   );

   wire sub = Op != `ADD;
   wire [31:0] bb = sub ? ~B : B;
   wire [32:0] sum = A + bb + sub;
   wire sltu = ! sum[32];

   wire v = sub ?
            ( A[31] != B[31] && A[31] != sum[31] )
          : ( A[31] == B[31] && A[31] != sum[31] );

   wire slt = v ^ sum[31];

   reg [31:0] x;

   always @( * )
      case( Op )
         `ADD : x = sum;
         `SUB : x = sum;
         `SLT : x = slt;
         `SLTU: x = sltu;
         `AND : x = A & B;
         `OR  : x = A | B;
         `NOR : x = ~(A | B);
         `XOR : x = A ^ B;
         `LUI : x = {B[15:0], 16'h0};
         `JUMP : x=B;
         `JR : x=A;
         default : x = 32'hxxxxxxxx;
      endcase

   assign X = x;
   assign Z = x == 32'h00000000;

endmodule

//==============================================================================

module reg_file(
   input clk,
   input write,
   input [4:0] WR,
   input [31:0] WD,
   input [4:0] RR1,
   input [4:0] RR2,
   output [31:0] RD1,
   output [31:0] RD2
);

   reg [31:0] rf_data [0:31];

   assign #2 RD1 = rf_data[ RR1 ];
   assign #2 RD2 = rf_data[ RR2 ];   

   always @( posedge clk ) begin
      if ( write )
         rf_data[ WR ] <= WD;

      rf_data[0] <= 32'h00000000;
   end

endmodule



module multiplier1(
//---------------------Port directions and deceleration
   input clk,  
   input start,
   input [31:0] A, 
   input [31:0] B, 
   output reg [63:0] Product,
   output ready
    );



//----------------------------------------------------

//--------------------------------- register deceleration
reg [63:0] Multiplicand ;
reg [31:0]  Multiplier;
reg [5:0]  counter;
//-----------------------------------------------------

//----------------------------------- wire deceleration
wire product_write_enable;
wire [63:0] adder_output;
//-------------------------------------------------------

//------------------------------------ combinational logic
assign adder_output = Multiplicand + Product;
assign product_write_enable = Multiplier[0];
assign ready = counter[5];
//-------------------------------------------------------

//------------------------------------- sequential Logic
always @ (posedge clk)

   if(start) begin
      counter <= 6'h0 ;
      Multiplier <= B;
      Product <= 64'h0000;
      Multiplicand <= {32'h00, A} ;
   end

   else if(! ready) begin
         counter <= counter + 1;
         Multiplier <= Multiplier >> 1;
         Multiplicand <= Multiplicand << 1;

      if(product_write_enable)
         Product <= adder_output;
   end   

endmodule

//==============================================================================
