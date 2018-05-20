rm *.vcd *.vvp ;
iverilog -o fulladder_tb.vvp fulladder_tb.v ;
vvp fulladder_tb.vvp ;
gtkwave fulladder_tb.vcd
