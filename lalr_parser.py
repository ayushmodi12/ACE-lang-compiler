from lark import Lark,tree,ast_utils,LarkError
from lark.lexer import Lexer, Token
import sys

grammar = '''
program: function_decl_list 
function_decl_list: function_decl 
function_decl: "func" datatype IDENTIFIER "(" params ")" "{" stmts "}" function_decl | main_function 
main_function: "func" "num" "main" "(" ")" "{" stmts "}" 
params: (param ("," param)*)? 
param: datatype IDENTIFIER  | datatype "(" ")" IDENTIFIER  | datatype "[" "]" IDENTIFIER  | datatype "{" "}" IDENTIFIER 
datatype: "num" | "flag" | "str" | "void" | "char"
stmts: (stmt ";" | function_decl | floop  |  wloop  |  if_cond  |  try  |  catch | iter";" )*
stmt: "continue" | "break" | "return" | "return" IDENTIFIER | "return" CONST |(IDENTIFIER "[" IDENTIFIER "]" "=" exp ) | l1 | "return" IDENTIFIER "[" (VAL2)? ":" (VAL2)? "]"

try : "try"  "{"  stmts  "}" 
catch :  "catch"  "{"  stmts  "}" 
throw : "throw"  "("  VAL1  ")" 
floop : "floop"  "("  assign  ";"  cond  ";"  iter  ")"  "{"  stmts  "}" 
wloop : "wloop"  "("  cond  ")"  "{"  stmts  "}" 
assign : "cook" datatype IDENTIFIER "=" exp | IDENTIFIER "=" exp | IDENTIFIER "++" | IDENTIFIER "--"
cond : "!" c | c

c : "(" c ")" | (exp | "len" "(" IDENTIFIER ")" | "headof" "(" IDENTIFIER ")" | "tailof" "(" IDENTIFIER ")" | VAL2 | VAL1) comp (exp | "len" "(" IDENTIFIER ")" | "headof" "(" IDENTIFIER ")" | "tailof" "(" IDENTIFIER ")" | VAL2 | VAL1) | "true" | "false" | c "||" c | c "&&" c | exp 
comp : ">=" | "<=" | "!=" | ">" | "<" | "=="  
exp : (IDENTIFIER | IDENTIFIER "[" (VAL2 | IDENTIFIER) "]" | "(" exp ")" | (exp | int_exp) op (exp| int_exp))? | exp1
exp1: "(" exp1 ")" | CONST 
e1: ((datatype IDENTIFIER  | datatype "(" ")" IDENTIFIER  | datatype "[" "]" IDENTIFIER  | datatype "{" "}" IDENTIFIER ) e2*)*
e2: ("," e1)
op: "+" | "-" | "*" | "/" | "#" | "&" | "|" | "^" | "%"

binary_exp: binary_exp binary_op binary_exp
          | "(" binary_exp ")" | "!"binary_exp
          | "true"
          |"false"
          | exp

binary_op: "||" | "&&" | "==" | "!=" 


if_cond : "if" "(" cond ")" "{" stmts "}" (else_if_cond | else_cond)?
else_if_cond : "else_if" "(" cond ")" "{" stmts "}" (else_if_cond | else_cond)?
else_cond : "else" "{" stmts "}"
int_exp : VAL2 | "len" "(" IDENTIFIER ")" | "headof" "(" IDENTIFIER ")" | "tailof" "(" IDENTIFIER ")" | "(" int_exp ")"
iter: stmt | IDENTIFIER "++" | IDENTIFIER "--"
print : ((IDENTIFIER | CONST) ("," print)?  |  ("," print)? | (IDENTIFIER | CONST) "[" (exp | VAL2) "]" ("," print)? )? 

l1:  "cook" datatype IDENTIFIER "=" VAL2 ":" ":" IDENTIFIER
    | IDENTIFIER "=" VAL2 ":" ":" IDENTIFIER
    | l

l:"cook" datatype IDENTIFIER "=" "{" val11 "}" 
    | "cook" IDENTIFIER "=" "[" val7 "]"
    | "cook" IDENTIFIER "=" "(" val7 ")"
    | "cook" datatype IDENTIFIER
    | "cook" datatype IDENTIFIER "[" IDENTIFIER "]"
    | "cook" datatype IDENTIFIER "[" int_exp "]"
    | IDENTIFIER "=" "[" val7 "]"
    | IDENTIFIER "=" ( binary_exp)
    | IDENTIFIER "=" IDENTIFIER "[" int_exp "]"
    | IDENTIFIER "=" IDENTIFIER "(" val7 ")"
    | "cook" datatype IDENTIFIER "=" ( binary_exp | VAL1 | VAL9 )
    | "cook" datatype IDENTIFIER "=" "[" val7 "]"
    | "cook" datatype IDENTIFIER "=" IDENTIFIER "[" int_exp "]"
    | "cook" datatype IDENTIFIER "=" IDENTIFIER "(" val7 ")"
    | "cook" datatype IDENTIFIER "=" IDENTIFIER "("  ")"
    | "cook" datatype IDENTIFIER "=" IDENTIFIER "[" exp? ":" exp? "]"
    | "cook" datatype IDENTIFIER "=" VAL1 "[" exp? ":" exp? "]"
    | "echo" "(" print ")"
    | throw 

slicing: IDENTIFIER "[" exp? ":" exp? "]"
       | VAL1 "[" exp? ":" exp? "]"

CONST : VAL2 | VAL1 | VAL9

VAL1: /"[^"]*"/
NUM1 : /[1-9]/
NUM2 : /[0-9]*/
VAL2T: /[1-9][0-9]*/ 
VAL2 : ("-")?VAL2T |"0"

VAL3 : "true" | "false"

val4 : ((VAL2 ) ( "," (VAL2) )*)?
val11: ((VAL1 | VAL3 | VAL2 | VAL9) ( "," (VAL1 | VAL3 | VAL2 | VAL9) )*)?
val5 : (VAL1 ( "," VAL1 )*)?

val6 : (VAL3 ( "," VAL3 )*)?

val7 : ((VAL1 | VAL2 | VAL3 |  IDENTIFIER | VAL9 |  IDENTIFIER "[" exp "]" | "len" "(" IDENTIFIER ")" | "headof" "(" IDENTIFIER ")" | "tailof" "(" IDENTIFIER ")" | slicing ) ( "," (VAL1 | VAL2 | VAL3 | IDENTIFIER | VAL9 |  IDENTIFIER "[" exp "]" | "len" "(" IDENTIFIER ")" | "headof" "(" IDENTIFIER ")" | "tailof" "(" IDENTIFIER ")" | slicing) )*)?
VAL9 : /'([A-Za-z])'/
val10 : (VAL9 ( "," VAL9 )*)?
IDENTIFIER: /[a-zA-Z_][a-zA-Z0-9_]*/
%import common.WS
%ignore WS
%import common.WS_INLINE
%ignore WS_INLINE
'''


if __name__ == '__main__':
    
    if len(sys.argv) != 2:
        print("Usage: python parser.py <input_file>")
        sys.exit(1)

    file = sys.argv[1]

    try:
        with open(file, 'r', encoding="utf8") as f:
            sentence = f.read()
        parser = Lark(grammar, start='program', parser='lalr',debug=True)
        tree = parser.parse(sentence)
        print("Parsing succesfull. The input is syntactically correct. \n\nFollowing is the parse tree: \n")
        print(tree.pretty())
        
    except FileNotFoundError:
        print(f"Error: File '{file}' not found.")
        
    except LarkError as e:
        if hasattr(e, 'line') and hasattr(e, 'column'):
            error_line = e.line
            error_column = e.column
            print(f"Syntax error at line {error_line}, column {error_column}: \n\n{e}")
        else:
            print(f"Syntax error: {e}")
            
    except Exception as e:
        print(f"Error: {e}")