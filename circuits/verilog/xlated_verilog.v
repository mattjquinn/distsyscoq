/**************************************************
 * COQ-TO-VERILOG DESCRIPTION FILE
 * GENERATED 2018-03-08 16:47:01
 **************************************************/
module FullAdder
  (
    input i1, i2, ic, 
    output sum, carry
  );

  assign sum = i1 ^ i2 ^ ic;
  assign carry = ((i1 ^ i2) & ic) | (i1 & i2);

endmodule