rm *.class ; javac -Xlint:deprecation *.java ; java ToVerilog "../Initial.v" "xlated_verilog.v"
