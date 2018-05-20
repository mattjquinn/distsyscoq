grammar Gallina ;

sentences : sentence+ EOF ;

sentence : requireImport
         | notation
         | record
         | definition
         ;

requireImport : 'Require' 'Import' ID '.';

notation : 'Notation' STRING_LITERAL ':='
           '(' term ')'
           '(' 'at' 'level' NUMBER ',' ('left'|'right') 'associativity' ')' '.' ;

record : 'Record' ID binders? ':=' '{' fields? '}' '.' ;
fields : (field ';')+ ;
field  : name binders? ':' term ;
fieldAssgmt : ID ':=' term ;

definition : 'Definition' ID binders? (':' ty=term)? ':=' body=term '.' ;

binders : binder+ ;
binder  : ID
        | '(' ID+ ':' term ')' ;

name : ID | WILDCARD ;

arg : term
    | '(' ID ':=' term ')' ;

term : '{|' (fieldAssgmt ';')* '|}'             # termRecordInstance
     | lhs=term op=('|'|'&'|'XOR') rhs=term     # termInfixFuncCall
     | term arg+                                # termPrefixFuncCall
     | '(' term ')'                             # termParenthesized
     | ID                                       # termId
     | ID '.' ID                                # termQualifiedId
     ;


/*** LEXER RULES ***********************************************************/

ID : [a-zA-Z_] [0-9a-zA-Z_]* ;
WS : [ \t\r\n]+ -> skip ;
WILDCARD : '_' ;
STRING_LITERAL : '"' .*? '"' ;
NUMBER : [1-9]+ [0-9]* ;
COMMENT : '(*' .*? '*)' -> skip ;

/*sentences : sentence* EOF ;

sentence : inductive
         | definition
         ;

inductive : 'Inductive' ind_body '.' ;

definition : 'Definition' ID binders? (':' term)? ':=' term '.' ;

ind_body  : ID ':=' ind_rule+ ;
ind_rule  : '|' constructor=ID ':' ty=ID ;


ID : [a-zA-Z_] [0-9a-zA-Z_]* ;
WS : [ \t\r\n]+ -> skip ;
COMMENT : '(*' .*? '*)' -> skip ;
*/
