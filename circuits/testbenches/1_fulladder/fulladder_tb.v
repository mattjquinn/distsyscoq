// Verilog test bench for FullAdder
`timescale 1ns/100ps
`include "xlated_verilog.v"

module fulladder_tb;

   wire i1, i2, ic, sum, carry;
   integer k=0;

   assign {i1,i2,ic} = k;
   FullAdder dut(i1, i2, ic, sum, carry);

   initial begin

      $dumpfile("fulladder_tb.vcd");
      $dumpvars(0, fulladder_tb);

      for (k=0; k<8; k=k+1)
        #10 $display("done testing case %d", k);

      $finish;

   end

endmodule
