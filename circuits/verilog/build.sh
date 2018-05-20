rm -rf antlrgallinaparser ; java -jar /opt/antlr/antlr-4.7.1-complete.jar -o antlrgallinaparser -Dlanguage=Java -package antlrgallinaparser -visitor Gallina.g4 ; javac antlrgallinaparser/*.java
