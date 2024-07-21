import sys
from typing import List, Optional
from dataclasses import dataclass
import lark
from lark.lexer import Token, Lexer
import lark.tree as tree
from lark import Lark, LarkError, ast_utils, Transformer, v_args
from lark.tree import Meta
import networkx as nx
import matplotlib.pyplot as plt
from graphviz import Digraph
import re
this_module = sys.modules[__name__]

#
#   Define AST
#

grammar = '''
start: program
program: function_decl_list 
function_decl_list:  main_function |  ( function_decl )* 
main_function: "func" "num" "main" "(" ")" "{" stmts "}"
function_decl:  "func" dt_identifier "(" params ")" "{" stmts "}" 



params: (param ("," param)*)? 
param: dt_identifier  | datatype "(" ")" IDENTIFIER  | datatype "[" "]" IDENTIFIER  | datatype "{" "}" IDENTIFIER 
datatype: NUM | STR | VOID | CHAR | FLAG
stmts: (stmt ";" | function_decl | floop  |  wloop  |  if_else_block  |  trycatchblock | iter ";" )*
trycatchblock: try_ catch?
stmt: CONTINUE | BREAK | RETURN | RETURN IDENTIFIER | RETURN CONST |(IDENTIFIER "[" IDENTIFIER "]" "=" exp ) | l1 | RETURN IDENTIFIER "[" (VAL2)? ":" (VAL2)? "]"
if_else_block: if_cond else_if_cond* else_cond?
try_ : "try"  "{"  stmts  "}" 
catch :  "catch"  "{"  stmts  "}" 
throw : "throw"  "("  VAL1  ")" 
floop : "floop"  "("  assign  ";"  cond  ";"  iter  ")"  "{"  stmts  "}"
wloop : "wloop"  "("  cond  ")"  "{"  stmts  "}" 
assign : "cook" dt_identifier "=" exp 
        | IDENTIFIER "=" exp -> a2
        | IDENTIFIER INC -> a3
        | IDENTIFIER DEC
cond : UNARY_NOT c | c


c : "(" c ")" | (exp | LEN "(" IDENTIFIER ")" | HEADOF "(" IDENTIFIER ")" | TAILOF "(" IDENTIFIER ")" | VAL2 | VAL1) comp (exp | LEN "(" IDENTIFIER ")" | HEADOF "(" IDENTIFIER ")" | TAILOF "(" IDENTIFIER ")" | VAL2 | VAL1) | TRUE | FALSE | c "||" c | c "&&" c | exp 
comp : GTE | LTE | NEQL | LT | GT | EQL  
exp : ( IDENTIFIER | IDENTIFIER "[" (IDENTIFIER) "]" | "(" exp ")" | (exp | int_exp) op (exp| int_exp))? | exp1
exp1: "(" exp1 ")" | CONST 
e1: ((dt_identifier  | datatype "(" ")" IDENTIFIER  | datatype "[" "]" IDENTIFIER  | datatype "{" "}" IDENTIFIER ) e2*)*
e2: ("," e1)
op: PLUS | MINUS | MUL | DIV | POW | BWAND | BWOR | XOR | MODULO

binary_exp: binary_exp (OR | AND | EQL | NEQL) binary_exp
          | "(" binary_exp ")" | UNARY_NOT binary_exp
          | TRUE
          |FALSE
          | exp
          


if_cond : "if" "(" cond ")" "{" stmts "}" 
else_if_cond : "else_if" "(" cond ")" "{" stmts "}" 
else_cond : "else" "{" stmts "}"
int_exp : VAL2 | LEN "(" IDENTIFIER ")" | HEADOF "(" IDENTIFIER ")" | TAILOF "(" IDENTIFIER ")" | "(" int_exp ")"
iter: stmt | IDENTIFIER INC | IDENTIFIER DEC
print : ((IDENTIFIER | CONST) ("," print)?  |  ("," print)? | (IDENTIFIER | CONST) "[" (exp | VAL2) "]" ("," print)? )? 

to_print: "echo" "(" print ")"

l1:  "cook" dt_identifier "=" VAL2 ":" ":" IDENTIFIER
    | IDENTIFIER "=" VAL2 ":" ":" IDENTIFIER
    | l

l:"cook" dt_identifier "=" "{" val11 "}" 
    | "cook" dt_identifier
    | "cook" dt_identifier "[" IDENTIFIER "]"
    | "cook" dt_identifier "[" int_exp "]"
    | IDENTIFIER "=" ( binary_exp)
    | IDENTIFIER "=" IDENTIFIER "[" int_exp "]"
    | IDENTIFIER "=" IDENTIFIER "(" val7 ")"
    | "cook" dt_identifier "=" IDENTIFIER "[" int_exp "]"
    | "cook" dt_identifier "=" IDENTIFIER "(" val7 ")"
    | "cook" dt_identifier "=" IDENTIFIER "("  ")"
    | IDENTIFIER "[" VAL2 | IDENTIFIER "]" "=" ( binary_exp | VAL1 | VAL9 )
    | slicing
    | to_print
    | throw 
    | l2

l2: "cook" dt_identifier "=" ( binary_exp | VAL1 | VAL9 )

LIST_TUPLE_ID: /(?<!(main)\b)[a-zA-Z_][a-zA-Z0-9_]*/
FUNC_IDENTIFIER: /(?<!(main)\b)[a-zA-Z_][a-zA-Z0-9_]*/
FUNC_DECL_IDENTIFIER : /(?<!(main)\b)[a-zA-Z_][a-zA-Z0-9_]*/

dt_identifier : datatype IDENTIFIER

slicing: IDENTIFIER "[" exp? ":" exp? "]"
       | VAL1 "[" VAL2 ":" VAL2 "]"

CONST : VAL2 | VAL1 | VAL9

VAL1: /"[^"]*"/
NUM1 : /[1-9]/
NUM2 : /[0-9]*/
VAL2T: /[1-9][0-9]*/ 
VAL2 : ("-")?VAL2T |"0"

VAL3 : TRUE | FALSE

val4 : ((VAL2 ) ( "," (VAL2) )*)?
val11: ((VAL1 | VAL3 | VAL2 | VAL9 | IDENTIFIER) ( "," (VAL1 | VAL3 | VAL2 | VAL9 | IDENTIFIER) )*)?
val5 : (VAL1 ( "," VAL1 )*)?

val6 : (VAL3 ( "," VAL3 )*)?

val7 : ((VAL1 | VAL2 | VAL3 |  IDENTIFIER | VAL9 |  IDENTIFIER "[" exp "]" | LEN "(" IDENTIFIER ")" | HEADOF "(" IDENTIFIER ")" | TAILOF "(" IDENTIFIER ")" | slicing ) ( "," (VAL1 | VAL2 | VAL3 | IDENTIFIER | VAL9 |  IDENTIFIER "[" exp "]" | LEN "(" IDENTIFIER ")" | HEADOF "(" IDENTIFIER ")" | TAILOF "(" IDENTIFIER ")" | slicing) )*)?
VAL9 : /'([A-Za-z])'/
val10 : (VAL9 ( "," VAL9 )*)?
NUM : "num"
FLAG : "flag"
STR : "str"
VOID : "void" 
CHAR : "char"
TRY : "try"
CATCH : "catch"
THROW : "throw"
MAIN : "main"
RETURN : "return"
CONTINUE : "continue"
BREAK : "break"
INC : "++"
DEC : "--"
UNARY_NOT : "!"
LEN : "len"
HEADOF : "headof"
TAILOF : "tailof"
TRUE : "true"
FALSE : "false"
PLUS : "+"
MINUS : "-"
MUL : "*"
DIV : "/"
POW : "^"
BWAND : "&"
BWOR : "|"
XOR : "^"
OR : "||"
AND : "&&"
EQL : "=="
NEQL : "!="
GTE : ">="
LTE : "<="
LT : "<"
GT : ">"
MODULO : "%"



IDENTIFIER: /(?<!(main)\b)[a-zA-Z_][a-zA-Z0-9_]*/
%import common.WS
%ignore WS
%import common.WS_INLINE
%ignore WS_INLINE
'''




class ASTNodeMeta(type):
    def __new__(cls, name, bases, dct):
        if name != 'ASTNode':
            def repr_func(self):
                return name
            dct['__repr__'] = repr_func
        return super().__new__(cls, name, bases, dct)
    

class ASTNode(metaclass=ASTNodeMeta):
    """Abstract b"""
    pass

class Start(ASTNode):
    def __init__(self, values):
        for i, value in enumerate(values):
            setattr(self, f'{i}', value)

class Program(ASTNode):
    def __init__(self, values):
        for i, value in enumerate(values):
            setattr(self, f'{i}', value)
            
class FunctionDeclList(ASTNode):
    def __init__(self, values):
        for i, value in enumerate(values):
            setattr(self, f'{i}', value)
            

class Statement(ASTNode):
    def __init__(self, values):
        for i, value in enumerate(values):
            setattr(self, f'{i}', value)
            
class FunctionDeclaration(ASTNode):
    def __init__(self, values):
        for i, value in enumerate(values):
            setattr(self, f'{i}', value)
            
class Param(ASTNode):
    def __init__(self, values):
        for i, value in enumerate(values):
            setattr(self, f'{i}', value)
            
class Params(ASTNode):
    def __init__(self, values):
        for i, value in enumerate(values):
            setattr(self, f'{i}', value)
            
class MainFunction(ASTNode):
    def __init__(self, values):
        for i, value in enumerate(values):
            setattr(self, f'{i}', value)
            
class DataType(ASTNode):
    def __init__(self, values):
        for i, value in enumerate(values):
            setattr(self, f'{i}', value)
            
class Assign(ASTNode):
    def __init__(self, values):

        for i, value in enumerate(values):
            # print(value,type(value))
            if(type(value)==str):     
                new_val=IDENTIFIER(value)
                setattr(self, f'{i}', new_val)
            else:
                setattr(self, f'{i}', value)

class   IfElseBlock(ASTNode):
    def __init__(self, values):
        for i, value in enumerate(values):
            setattr(self, f'{i}', value)

class IfCond(ASTNode):
    def __init__(self, values):
        for i, value in enumerate(values):
            setattr(self, f'{i}', value)
            
class ElseIfCond(ASTNode):
    def __init__(self, values):
        for i, value in enumerate(values):
            setattr(self, f'{i}', value)
            
class ElseCond(ASTNode):
    def __init__(self, values):
        for i, value in enumerate(values):
            setattr(self, f'{i}', value)
            
class Expression(ASTNode):
    def __init__(self, values):
        for i, value in enumerate(values):
            setattr(self, f'{i}', value)
            

class Try(ASTNode):
    def __init__(self, values):
        for i, value in enumerate(values):
            setattr(self, f'{i}', value)
            
class Catch(ASTNode):
    def __init__(self, values):
        for i, value in enumerate(values):
            setattr(self, f'{i}', value)
            
class Throw(ASTNode):
    def __init__(self, values):
        for i, value in enumerate(values):
            setattr(self, f'{i}', value)

class Floop(ASTNode):
    def __init__(self, values):
        for i, value in enumerate(values):
            setattr(self, f'{i}', value)
            
class Wloop(ASTNode):
    def __init__(self, values):
        for i, value in enumerate(values):
            setattr(self, f'{i}', value)

class Print(ASTNode):
    def __init__(self, values):
        for i, value in enumerate(values):
            setattr(self, f'{i}', value)

class TryCatchBlock(ASTNode):
    def __init__(self, values):
        for i, value in enumerate(values):
            setattr(self, f'{i}', value)

class LoopAssign(ASTNode):
    def __init__(self, values):
        for i, value in enumerate(values):
            setattr(self, f'{i}', value)
            
class ConditionalStatement(ASTNode):
    def __init__(self, values):
        for i, value in enumerate(values):
            setattr(self, f'{i}', value)
            
class PrintParams(ASTNode):
    def __init__(self, values):
        for i, value in enumerate(values):
            setattr(self, f'{i}', value)
            
class Slice(ASTNode):
    def __init__(self, values):
        for i, value in enumerate(values):
            setattr(self, f'{i}', value)
            
class IntTerminal(ASTNode):
    def __init__(self, value):
        str=""
        for i in value:
            str+=i
        self.value = str
        
class StringTerminal(ASTNode):
    def __init__(self, value):
        str=""
        for i in value:
            str+=i
        self.value = str
class BoolTerminal(ASTNode):
    def __init__(self, value):
        self.value = value
        
class CharTerminal(ASTNode):
    def __init__(self, value):
        self.value = value
        
class ListItems(ASTNode):
    def __init__(self, values):
        for i, value in enumerate(values):
            # print(value)
            # pattern = r'^[+-]?\d+$'
            # f = bool(re.match(pattern, value))

            if(type(value)==str):
                pattern = r'^[+-]?\d+$'
                f = bool(re.match(pattern, value))
                if(f):
                    # print(value)
                    new_val=IntTerminal(value)
                    setattr(self, f'{i}', new_val)
            
                elif( len(value)==1):   
                    new_val=IDENTIFIER(value)
                    setattr(self, f'{i}', new_val)
            else:
                setattr(self, f'{i}', value)
            # print(type(value))
            
class DT_IDENTIFIER(ASTNode):
    def __init__(self, values):
        for i, value in enumerate(values):
            if(type(value)!=str):
                setattr(self, f'{i}', value)
            else:
                setattr(self, f'{i}', IDENTIFIER(value))

class ListTupleIdentifier(ASTNode):
    def __init__(self, value):
        str=""
        for i in value:
            str+=i
        self.value = str
                     
class IDENTIFIER(ASTNode):
    def __init__(self, value):
        str=""
        for i in value:
            str+=i
        self.value = str
                        
class FUNC_IDENTIFIER(ASTNode):
    def __init__(self, value):
        str=""
        for i in value:
            str+=i
        self.value = str
            
class FUNC_DECL_IDENTIFIER(ASTNode):
    def __init__(self, value):
        str=""
        for i in value:
            str+=i
        self.value = str

class UnaryNot(ASTNode):
    def __init__(self, value):
        self.value=value

def single_list(_list):
    combined_list = []
    for entry in _list:
        if isinstance(entry, list):
            combined_list.extend(single_list(entry))
        else:
            combined_list.append(entry)
    return combined_list


def to_list(our_tree):

    ls=[]
    if isinstance(our_tree, lark.tree.Tree):
        for child in our_tree.children:
            ls1= to_list(child)
            ls += ls1
            
    elif(isinstance(our_tree, lark.lexer.Token)):
        ls.append(our_tree.value)
    
    elif(isinstance(our_tree, list)):
        for child in our_tree:
            ls1= to_list(child)
            ls+=ls1
    else:
        ls= [our_tree]
    return ls
         


class ToAst(Transformer):
    
    def create_node(self, items, node_class):
        items = single_list(items)
        if len(items) == 1:
            return items
        return node_class(items)
    
    def start(self, items):
        lst=[]
        for i in items:
            lst+=to_list(i)
        items=lst
        return Start(items)
    
    def program(self, items):
        lst=[]
        for i in items:
            lst+=to_list(i)
        items=lst
        return Program(items)
    
    def function_decl_list(self, items):
        lst=[]
        for i in items:
            lst+=to_list(i)
        items=lst
        
        return FunctionDeclList(items)
    
    def function_decl(self, items):
        lst=[]
        for i in items:
            lst+=to_list(i)
        items=lst
        
        return FunctionDeclaration(items)
    
    def main_function(self, items):
        lst=[]
        for i in items:
            lst+=to_list(i)
        items=lst
        return MainFunction(items)
    
    def params(self, items):
        items = single_list(items)
        return Params(items)
    
    def param(self, items):
        items = single_list(items)
        return Param(items)
    
    def datatype(self, items):
        lst=[]
        for i in items:
            lst+=to_list(i)
        items=lst
        return DataType(items)
    
    def stmts(self, items):
        lst=[]
        for i in items:
            lst+=to_list(i)
        items=lst
        return Statement(items)
    
    def stmt(self, items):
        lst=[]
        for i in items:
            lst+=to_list(i)
        items=lst
        return Statement(items)
    
    def assign(self, items):
        lst=[]
        for i in items:
            lst+=to_list(i)
        items=lst
        return LoopAssign(items)
    
    def try_(self, items):
        lst=[]
        for i in items:
            lst+=to_list(i)
        items=lst
        return Try(items)
    
    def catch(self, items):
        lst=[]
        for i in items:
            lst+=to_list(i)
        items=lst 
        return Catch(items)
        
    def throw(self, items):
        lst=[]
        for i in items:
            lst+=to_list(i)
        items=lst
        return Throw(items)
    
    def floop(self, items):
        lst=[]
        for i in items:
            lst+=to_list(i)
        items=lst
        return Floop(items)
    
    def wloop(self, items):
        lst=[]
        for i in items:
            lst+=to_list(i)
        items=lst
        return Wloop(items)
    
    def if_cond(self, items):
        lst=[]
        for i in items:
            lst+=to_list(i)
        items=lst
        return IfCond(items)
    
    def else_if_cond(self, items):
        lst=[]
        for i in items:
            lst+=to_list(i)
        items=lst
        return ElseIfCond(items)
    
    def else_cond(self, items):
        lst=[]
        for i in items:
            lst+=to_list(i)
        items=lst
        return ElseCond(items)
    
    def cond(self, items):
        lst=[]
        for i in items:
            lst+=to_list(i)
        items=lst
        return ConditionalStatement(items)
    
    def c(self, items):
        lst=[]
        for i in items:
            lst+=to_list(i)
        items=lst
        return ConditionalStatement(items)
    
    def exp(self, items):
        lst=[]
        for i in items:
            lst+=to_list(i)
        items=lst
        return Expression(items)
    
    def ex1(self, items):
        lst=[]
        for i in items:
            lst+=to_list(i)
        items=lst
        return Expression(items)
    
    def e1(self, items):
        lst=[]
        for i in items:
            lst+=to_list(i)
        items=lst
        return Expression(items)
    
    def e2(self, items):
        lst=[]
        for i in items:
            lst+=to_list(i)
        items=lst
        return Expression(items)
    
    def exp1(self, items):
        lst=[]
        for i in items:
            lst+=to_list(i)
        items=lst
        return Expression(items)
    
    def binary_exp(self, items):
        lst=[]
        for i in items:
            lst+=to_list(i)
        items=lst
        # print(items)
        return Expression(items)
    
    def int_exp(self, items):
        lst=[]
        for i in items:
            lst+=to_list(i)
        items=lst
        # print(items)
        return Expression(items)
    
    def iter(self, items):
        lst=[]
        for i in items:
            lst+=to_list(i)
        items=lst
        return Statement(items)
    
    def print(self, items):
        lst=[]
        for i in items:
            lst+=to_list(i)
        items=lst
        return PrintParams(items)
    
    def to_print(self, items):
        lst=[]
        for i in items:
            lst+=to_list(i)
        items=lst
        return Print(items)
    
    def l1(self, items):
        lst=[]
        for i in items:
            lst+=to_list(i)
        items=lst
        return Assign(items)
    
    def comp(self, items):
        lst=[]
        for i in items:
            lst+=to_list(i)
        items=lst
        return Expression(items)
    
    def l(self, items):
        lst=[]
        for i in items:
            lst+=to_list(i)
        items=lst
        # print(items)
        return Assign(items)
    
    def l2(self, items):
        lst=[]
        for i in items:
            lst+=to_list(i)
        items=lst
        # print(items)
        return Assign(items)

    
    def dt_identifier(self, items):
        lst=[]
        for i in items:
            lst+=to_list(i)
        items=lst
        # print("dt___ID", items)
        return DT_IDENTIFIER(items)
    
    def slicing(self, items):
        lst=[]
        for i in items:
            lst+=to_list(i)
        items=lst
        return Slice(items)
    
    # def VAL1(self,items):
    #     return self.create_node(items, StringTerminal)
    
    def NUM1(self,items):
        return self.create_node(items, IntTerminal)
    
    def NUM2(self,items):
        return self.create_node(items, IntTerminal)
    
    def VAL2T(self,items):
        return self.create_node(items, IntTerminal)
    
    def VAL2(self,items):
        # print(items)
        return self.create_node(items, IntTerminal)
    
    def VAL3(self,items):
        return self.create_node(items, BoolTerminal)
    
    def val11(self,items):
        return self.create_node(items, ListItems)
    
    def val4(self,items):
        return self.create_node(items, ListItems)
    
    def val5(self,items):
        return self.create_node(items, ListItems)
    
    def val6(self,items):
        return self.create_node(items, ListItems)
    
    def val7(self,items):
        return self.create_node(items, ListItems)
    
    def val10(self,items):
        return self.create_node(items, ListItems)
    
    def val9(self,items):
        return self.create_node(items, CharTerminal)
    
    def num(self,items):
        return self.create_node(items, DataType)
    
    def flag(self,items):
        return self.create_node(items, DataType)
    
    def str(self,items):
        return self.create_node(items, DataType)
    
    def void(self,items):
        return self.create_node(items, DataType)
    
    def char(self,items):
        return self.create_node(items, DataType)
    
    def binary_op(self,items):
        return self.create_node(items, Expression)
    
    def op(self,items):
        return self.create_node(items, Expression)
    
    def if_else_block(self,items):
        lst=[]
        for i in items:
            lst+=to_list(i)
        items=lst
        return IfElseBlock(items)
    
    def IDENTIFIER(self,items):
        # print("ID", items)
        return self.create_node(items, IDENTIFIER)
    
    def trycatchblock(self,items):
        lst=[]
        for i in items:
            lst+=to_list(i)
        items=lst
        return TryCatchBlock(items)
    def LIST_TUPLE_ID(self,items):
        return self.create_node(items, ListTupleIdentifier)
    def FUNC_IDENTIFIER(self,items):
        return self.create_node(items, FUNC_IDENTIFIER)
    def FUNC_DECL_IDENTIFIER(self,items):
        return self.create_node(items, FUNC_DECL_IDENTIFIER)
    def UNARY_NOT(self,items):
        return UnaryNot(items)
    
    
transformer = ast_utils.create_transformer(this_module, ToAst())

def parse(text):
    parser = Lark(grammar, parser="lalr")
    tree = parser.parse(text)
    p = transformer.transform(tree)
    return p



def create_ast(tree, edge_list,graph=None,parent=None):
    if isinstance(tree, ASTNode)==False:
        graph.node(str(id(tree)), label=str(tree), shape='box', filled='true')
        if str(id(parent)) in edge_list.keys():
            edge_list[str(id(parent))].append((str(id(tree)),str(tree)))
        else:
            edge_list[str(id(parent))]=[]
            edge_list[str(id(parent))].append((str(id(tree)),str(tree)))
        graph.edge(str(id(parent)), str(id(tree)))
    else:
        children = vars(tree).items()
        child_count = sum(isinstance(child, ASTNode) for _, child in children)
        if graph is None:
            graph = Digraph()
        if parent is None:
            parent = tree
            graph.node(str(id(parent)), label=str(parent), filled='true')
            for _, child in children:
                create_ast(child,edge_list,graph,tree)
        else:
            if (type(tree)==ListItems or type(tree)== Params or type(tree)==ElseCond or type(tree)==FunctionDeclaration or type(tree)==MainFunction or type(tree)==Try or type(tree)==Catch or type(tree)==Throw or type(tree)==ListTupleIdentifier):
                graph.node(str(id(tree)), label=str(tree), filled='true')
                graph.edge(str(id(parent)), str(id(tree)))
                if str(id(parent)) in edge_list.keys():
                    edge_list[str(id(parent))].append((str(id(tree)),str(tree)))
                else:
                    edge_list[str(id(parent))]=[]
                    edge_list[str(id(parent))].append((str(id(tree)),str(tree)))
                for _, child in children:
                    create_ast(child,edge_list,graph,tree)
                    
            elif child_count==1:
                for _, child in children:
                    if isinstance(child, ASTNode):
                        create_ast(child,edge_list,graph,parent)
            else:
                graph.node(str(id(tree)), label=str(tree), filled='true')
                graph.edge(str(id(parent)), str(id(tree)))
                if str(id(parent)) in edge_list.keys():
                    edge_list[str(id(parent))].append((str(id(tree)),str(tree)))
                else:
                    edge_list[str(id(parent))]=[]
                    edge_list[str(id(parent))].append((str(id(tree)),str(tree)))
                for _, child in children:
                    create_ast(child,edge_list,graph,tree)
                
    return graph

keywords={"num":"num", "str":"str", "void":"void", "char":"char", "flag":"flag", "true":"flag", "false":"flag", "try":"try", "catch":"catch", "throw":"throw", "main":"main", "return":"return", "continue":"continue", "break":"break", "len":"len", "headof":"headof", "tailof":"tailof", "cook":"cook", "floop":"floop", "wloop":"wloop", "if":"if", "else_if":"else_if", "else":"else", "echo":"echo"}
class scopecheck:
    def __init__(self,tree):
        self.tree=tree
        self.scopes = []
        self.func_list = []
    
    def enter_scope(self):
        self.scope = {}
        self.scopes.append(self.scope)
    
    def exit_scope(self):
        self.scopes.pop()
        if self.scopes:
            self.scope = self.scopes[-1]
    
    def add_symbol(self, symbol):
        self.scope[symbol] = True
    
    def check_symbol(self, symbol):
        if symbol in keywords:
            return keywords[symbol]
        for scope in reversed(self.scopes):
            if symbol in scope:
                return True
        return False
    
    def check_scope(self, symbol):
        return symbol in self.scope
    
    def dfs_traverse(self,edge_list,node, visited=None,node_type=None, curr_func=None):
        if visited is None:
            visited = set()
        if node in visited:
            return
        if node not in edge_list.keys():
            return
        children = edge_list[node]
        if(node_type=='FunctionDeclaration'):
            dt_id=children[0]
            identifier=edge_list[dt_id[0]][1][0]
            idd=edge_list[identifier]
            self.func_list.append(idd[0][1])
        if(node_type=='Param'):
            child=edge_list[node]
            idd = edge_list[child[1][0]][0]
            self.add_symbol(idd[1])
            return
        if(node_type=='Params'):
            child1=edge_list[node]
            for child in child1:
                child=edge_list[child[0]]
                idd = edge_list[child[1][0]][0]
                self.add_symbol(idd[1])

        for child in children:
            # print(child[1])
            if(node_type=='Params') and child[1]!='Param':
                continue

            if (child[1]=="FunctionDeclaration" or child[1]=="MainFunction" or child[1]=="Floop" or child[1]=="Wloop" or child[1]=="IfCond"or child[1]=="ElseIfCond"or child[1]=="ElseCond"):
                self.enter_scope()
                self.dfs_traverse(edge_list,child[0], visited,child[1], curr_func)
                self.exit_scope()
                                                        
            elif(child[1]=="DT_IDENTIFIER"):
                identifier=edge_list[child[0]][1]
                identifier_id=identifier[0]
                idd=edge_list[identifier_id][0][1]
                check=self.check_scope(idd)
                if not check:
                    self.add_symbol(idd)
                else:
                    raise Exception(f"{idd} already declared in the same scope")
            elif(child[1]=="IDENTIFIER"):
                check=self.check_symbol(edge_list[child[0]][0][1])
                idd = edge_list[child[0]][0][1]
                if not check:
                    if idd not in self.func_list:
                        raise Exception(f"{idd} not declared in the scope")
                
            elif(child[1]=="ListTupleIdentifier"):
                identifier=edge_list[child[0]][0]
                identifier_id=identifier[1]
                check=self.check_scope(identifier_id)
                if not check:
                    self.add_symbol(identifier_id)
                else:
                    raise Exception(f"{identifier_id} already declared in the same scope")
            else:
                self.dfs_traverse(edge_list, child[0], visited,child[1])

class TypeCheck:
    def __init__(self,tree):
        self.tree=tree
        self.scopes = []
        self.func_list = {}
    
    def enter_scope(self):
        self.scope = {}
        self.scopes.append(self.scope)
    
    def exit_scope(self):
        self.scopes.pop()
        if self.scopes:
            self.scope = self.scopes[-1]
    
    def add_symbol_type(self, symbol, type):
        self.scope[symbol] = type
    
    def check_symbol_type(self, symbol):
        if symbol in keywords:
            return keywords[symbol]
        for scope in reversed(self.scopes):
            if symbol in scope:
                return scope[symbol]
        return None
    
    def check_scope(self, symbol):
        return symbol in self.scope
    
    def check_type(self, exp):
        pattern = r'^[+-]?\d+$'
        f = bool(re.match(pattern, exp))
        if (exp[0]=="\'"):
            return "char"
        elif (exp[0]=="\""):
            return "str"
        elif (f):
            return "num"
        elif (exp=="true" or exp=="false"):
            return "flag"
        elif exp in self.func_list.keys():
            return self.func_list[exp][0]
        else:
            return "other"
        
    def check_exp_type2(self,exp,edge_list,isArray=False, var_id=None):
        if(isArray==True):
            
            datatype_array=var_id
            
            for tup in exp[0:]:
                if(tup[1]=="IDENTIFIER"):
                     if(self.check_symbol_type(edge_list[tup[0]][0][1])!=datatype_array):
                        raise Exception(f"Invalid Array Declaration. Array datatype: {datatype_array} does not match with element's datatype: {self.check_symbol_type(edge_list[tup[0]][0][1])}")
        
                elif(tup[1]!="IntTerminal"):
                    if(self.check_type(tup[1])!=datatype_array):
                        raise Exception(f"Invalid Array Declaration. Array datatype: {datatype_array} does not match with element's datatype: {self.check_type(tup[1])}")
                        
                else:
                    
                    list_id=tup[0]
                    int_list=edge_list[list_id]
                    first_ele_dt=int_list[0][1]
                    
                    if(self.check_type(first_ele_dt)!=datatype_array):
                        raise Exception(f"Invalid Array Declaration. Array datatype: {datatype_array} does not match with element's datatype: {self.check_type(first_ele_dt)}")
                        
                        # raise Exception("Invalid Array Declaration")
                    
            
            return datatype_array
        
        if(len(exp)==1):
            if (self.check_symbol_type(exp[0][1]) is not None):
                return self.check_symbol_type(exp[0][1])
            else:
                return self.check_type(exp[0][1])
        
        if(len(exp)==2):
            if (self.check_exp_type2(edge_list[exp[1][0]], edge_list)=="flag" and exp[0][1]=="UnaryNot"):
                return "flag"
            else:
                raise Exception("Invalid Unary Operation")
        
        if(len(exp)==3):
                    
            if(self.check_exp_type2(edge_list[exp[0][0]], edge_list) == self.check_exp_type2(edge_list[exp[2][0]], edge_list)):
                
                
                if (self.check_exp_type2(edge_list[exp[0][0]], edge_list)=="str" and exp[1][1]!="+"):
                    raise Exception("Invalid String Concatenation")

                else:
                    return self.check_exp_type2(edge_list[exp[0][0]], edge_list)
            elif(self.check_exp_type2(edge_list[exp[1][0]], edge_list) == self.check_exp_type2(edge_list[exp[2][0]], edge_list) and self.check_exp_type2(edge_list[exp[1][0]], edge_list)=="num" and self.check_exp_type2(edge_list[exp[0][0]], edge_list)=="str"):
                return "str"
             
            else:
                
                raise Exception("Unequal DataTypes")
        
    def check_exp_type(self,exp,edge_list):
        if(len(exp)==1):
            if (self.check_symbol_type(exp[0][1]) is not None):
                return self.check_symbol_type(exp[0][1])
            else:
                return self.check_type(exp[0][1])
        
        if(len(exp)==2 and exp[0][1]=="UnaryNot"):
            if (self.check_exp_type(edge_list[exp[1][0]], edge_list)=="flag" and exp[0][1]=="UnaryNot"):
                return "flag"
            else:
                raise Exception("Invalid Unary Operation")
        
        if(len(exp)==3):
            if(self.check_exp_type(edge_list[exp[0][0]], edge_list) == self.check_exp_type(edge_list[exp[2][0]], edge_list)):
                if (self.check_exp_type(edge_list[exp[0][0]], edge_list)=="str" and exp[1][1]!="+"):
                    raise Exception("Invalid String Concatenation")

                else:
                    return self.check_exp_type(edge_list[exp[0][0]], edge_list)
            else:
                raise Exception("Unequal DataTypes")
        
    
    def dfs_traverse(self,edge_list,node, visited=None,node_type=None, curr_func=None):
        if visited is None:
            visited = set()
        if node in visited:
            return
        if node not in edge_list.keys():
            return
        children = edge_list[node]

        if(node_type=='FunctionDeclaration'):
            dt_id=children[0]
            identifier=edge_list[dt_id[0]][1][0]
            idd=edge_list[identifier]
            rttype=edge_list[dt_id[0]][0][0]
            rt=edge_list[rttype]
            self.func_list[idd[0][1]]=[]
            self.func_list[idd[0][1]].append(rt[0][1])
            curr_func = idd[0][1]
        if(node_type=='Param'):
            child=edge_list[node]
            idd = edge_list[child[1][0]][0]
            dt= edge_list[child[0][0]][0]
            self.add_symbol_type(idd[1],dt[1])
            self.func_list[curr_func].append(dt[1])
            return
        if(node_type=='Params'):
            child1=edge_list[node]
            for child in child1:
                child=edge_list[child[0]]
                idd = edge_list[child[1][0]][0]
                dt= edge_list[child[0][0]][0]
                self.func_list[curr_func].append(dt[1])
                self.add_symbol_type(idd[1],dt[1])
        for child in children:
            
                    if(node_type=='Params') and child[1]!='Param':
                        continue
                    # print(child[1])
                    if (child[1]=="FunctionDeclaration" or child[1]=="MainFunction" or child[1]=="Floop" or child[1]=="Wloop" or child[1]=="IfCond"or child[1]=="ElseIfCond"or child[1]=="ElseCond"):
                        self.enter_scope()
                        self.dfs_traverse(edge_list,child[0], visited, child[1])
                        self.exit_scope()
                        
                    elif (child[1]=="Statement" and len(edge_list[child[0]])==2 and (edge_list[child[0]][1][1]=="++" or edge_list[child[0]][1][1]=="--") ):    
                        # and (edge_list[child[0]][1][1]=="++" or edge_list[child[0]][1][1]=="--")
                        # print()
                        if (self.check_symbol_type(edge_list[child[0]][0][1])!="num"):
                            raise Exception(f"Only datatype num can be incremented/decremented.")

                        
                    elif (child[1]=="Assign"):
                        identifier=edge_list[child[0]][0]
                        child_name = identifier[1]
                        child2=edge_list[child[0]][1][1]
                        
                        exp = edge_list[child[0]][1]
                        
                        exp_id=exp[0]
                        length_exp= len(edge_list[exp_id])
                        exp_val=edge_list[exp_id][0][1]
                        
                        c1=edge_list[child[0]][0]
                        c2 =edge_list[child[0]][1]
                        
                        if(child2=="Slice"):
                            dt = edge_list[child[0]][0]
                            dt_id=dt[0]
                            type2=edge_list[dt_id][0][0]
                            type=edge_list[type2][0][1]
                            # print(type)
                            
                            if(type=="num" or type=="flag" or type=="char"):
                                raise Exception("Slicing not allowed on num or flag or char type")
                            
                            id1 = edge_list[child[0]][0]
                            id1_id = id1[0]
                            var_id2 =edge_list[id1_id][1][0]
                            var_id=edge_list[var_id2][0][1]
                            
                            
                            slice_list=edge_list[edge_list[child[0]][1][0]]
                            start=edge_list[slice_list[1][0]][0][1]
                            end=edge_list[slice_list[2][0]][0][1]
                            var=edge_list[slice_list[0][0]][0][1]
                            
                            type_slicing_var=self.check_symbol_type(var)
                            # print(type)
                            # print(type_slicing_var)
                           
                            if(type_slicing_var!=type):
                                raise Exception("Slicing variable type is different from the type of the list")
                            
                            
                            type_start=self.check_exp_type2([edge_list[slice_list[1][0]][0]],edge_list)
                            
                            type_end=self.check_exp_type2([edge_list[slice_list[2][0]][0]],edge_list)
                            
                            
                            if(type_start!="num" or type_end!="num"):
                                raise Exception("Slicing indexes should be of type num")
                        
                        elif (child2 == "ListItems" and child_name=="DT_IDENTIFIER"):
                            # print(1)
                            # if(isinstance(edge_list[exp_id],list)==False):
                            #     continue
                            # type_exp=self.check_exp_type(edge_list[exp_id],edge_list)
                            identifier=edge_list[child[0]][1]
                            identifier_id=identifier[0]
                            idd=edge_list[identifier_id][0][1]
                            
                            dt = edge_list[child[0]][0]
                            dt_id=dt[0]
                            type2=edge_list[dt_id][0][0]
                            type=edge_list[type2][0][1]
                            
                            id1 = edge_list[child[0]][0]
                            id1_id = id1[0]
                            var_id2 =edge_list[id1_id][1][0]
                            var_id=edge_list[var_id2][0][1]
                            check=self.check_scope(var_id)
                            
                            type_exp=self.check_exp_type2(edge_list[exp_id],edge_list,isArray=True, var_id=type)
                            
                            if not check:
                                self.add_symbol_type(var_id, type)
                            else:
                                raise Exception(f"Error: {var_id} already declared in the same scope")
                                
                            for c in edge_list[edge_list[child[0]][1][0]]:
                                if (self.check_type(c[0][1])!=type):
                                    raise Exception(f"Error: Type of {var_id}: {type} is different from type of {c[0][1]}: {self.check_type(c[0][1])}")                        
                            
                        elif (edge_list[c2[0]][0][1] in self.func_list.keys()):
                            c3 = edge_list[child[0]][2]
                            if (c3[1]=="IDENTIFIER"):
                                func_called = edge_list[c2[0]][0][1]
                                if (len(self.func_list[func_called])-1!=1):
                                    raise Exception(f"Number of paramaters passed: {len(edge_list[c3[0]])} is uneqal to number of parameters required in function definition: {len(self.func_list[func_called])-1} of Function: {func_called}")
                                
                                p1 = edge_list[c3[0]][0][1]
                                if (self.check_symbol_type(p1)!=self.func_list[func_called][1]):
                                    raise Exception(f"Type of parameter {p1}: {self.check_symbol_type(p1)} is different from that defined at function declaration of {curr_func}: {self.func_list[func_called][1]}")
                            else:
                                func_called = edge_list[c2[0]][0][1]
                            
                                if (len(edge_list[c3[0]])!=len(self.func_list[func_called])-1):
                                    raise Exception(f"Number of paramaters passed: {len(edge_list[c3[0]])} is uneqal to number of parameters required in function definition: {len(self.func_list[func_called])-1} of Function: {func_called}")
                                ind = 1
                                for child in edge_list[c3[0]]:
                                    # print(child)
                                    
                                    if (child[1]=="IDENTIFIER"):
                                        p1 = edge_list[child[0]][0][1]
                                        # print(p1)
                                        
                                        if (self.check_symbol_type(p1)!=self.func_list[func_called][ind]):
                                            raise Exception(f"Type of parameter {p1}: {self.check_symbol_type(p1)} is different from that defined at function declaration of {func_called}: {self.func_list[func_called][ind]}")
                                    elif (child[1]=="StringTerminal"):
                                        if ("str"!=self.func_list[func_called][ind]):
                                            raise Exception(f"Type of parameter {p1}: {self.check_type(p1)} is different from that defined at function declaration of {func_called}: {self.func_list[func_called][ind]}")
                                    else:
                                        if (self.check_type(child[1])!=self.func_list[func_called][ind]):
                                            raise Exception(f"Type of parameter {child[1]}: {self.check_type(child[1])} is different from that defined at function declaration of {func_called}: {self.func_list[func_called][ind]}")
                                    ind=ind+1
                        
                        # elif (child[1]=="Statement" ):
                        #     print("PPPPPPPPPPPPPPPPPPPPPPPPPPPPPPPPPPPPPPPPPPPPPPPPPP")
                        #     # if (edge_list[child[0]][1][1]=="++" or edge_list[child[0]][1][1]=="--"):
                        #     #     if (self.check_symbol_type(edge_list[child[0]][0][1])!="num"):
                        #     #         raise Exception(f"Only datatype num can be incremented/decremented.")
            
                        
                        elif (child_name=="IDENTIFIER"):
                            
                            type_exp=self.check_exp_type(edge_list[exp_id],edge_list)
                           
                            identifier_id=identifier[0]
                            idd=edge_list[identifier_id][0][1]

                            type_idd = self.check_symbol_type(idd)
                            
                            check=self.check_symbol_type(edge_list[edge_list[child[0]][0][0]][0][1])
                            idd = edge_list[edge_list[child[0]][0][0]][0][1]
                            if not check:
                                raise Exception(f"Error: {idd} not declared in the scope")

                            if (type_idd != type_exp):
                                raise Exception(f"Error: Type of {idd}: {type_idd} is different from type of {exp_val}: {type_exp}")
                           
                        elif (child_name=="DT_IDENTIFIER"):
                            
                            type_exp=self.check_exp_type(edge_list[exp_id],edge_list)
                            identifier=edge_list[child[0]][1]
                            
                            identifier_id=identifier[0]
                            idd=edge_list[identifier_id][0][1]

                            
                            dt = edge_list[child[0]][0]

                            dt_id=dt[0]
                            type2=edge_list[dt_id][0][0]
                            type=edge_list[type2][0][1]

                            
                            id1 = edge_list[child[0]][0]

                            id1_id = id1[0]
                            
                            var_id2 =edge_list[id1_id][1][0]
                            var_id=edge_list[var_id2][0][1]
                            check=self.check_scope(var_id)
                            if not check:
                                self.add_symbol_type(var_id, type)
                            else:
                                raise Exception(f"Error: {var_id} already declared in the same scope")                           
                            if (exp_val=="IDENTIFIER" and len(edge_list[edge_list[child[0]][1][0]])==2):                                
                                exp_val = edge_list[edge_list[edge_list[child[0]][1][0]][0][0]]                                                                                                
                                exp_val2 = edge_list[edge_list[edge_list[child[0]][1][0]][1][0]][0][1]
                                if (self.check_symbol_type(exp_val2)!="num"):
                                    raise Exception(f"{exp_val2} should be of type num")                                                                
                                type_exp= self.check_symbol_type(exp_val[0][1])
                                                            
                            if (type_exp != type):

                                raise Exception(f"Error: Type of {var_id}: {type} is different from type of {exp_val}: {type_exp}")                        
                            
                    elif(child[1]=="DT_IDENTIFIER"):
                        identifier=edge_list[child[0]][1]
                        identifier_id=identifier[0]
                        idd=edge_list[identifier_id][0][1]
                        
                        dt = edge_list[child[0]][0]
                        dt_id=dt[0]
                        type=edge_list[dt_id][0][1]
                        
                        check=self.check_scope(idd)
                        if not check:
                            self.add_symbol_type(idd, type)
                        else:
                            raise Exception(f"Error: {idd} already declared in the same scope")

                    elif(child[1]=="IDENTIFIER"):

                        check=self.check_symbol_type(edge_list[child[0]][0][1])
                        idd = edge_list[child[0]][0][1]
                        if not check:
                            raise Exception(f"Error: {idd} not declared in the scope")
                        
                    else:
                        self.dfs_traverse(edge_list, child[0], visited, child[1], curr_func)

class WATGenerator:
    def __init__(self, edge_list, node, startId):
        self.edge_list = edge_list
        self.wat_code = ""
        self.node = node
        self.startId=startId

    def generate_wat(self):
        self.traverse(self.node)
        return self.wat_code

    def traverse(self, node):
        # node = edge_list[node]
        # print(node)
        if (self.startId==node):
        # if node[0][1]=="Start":
            self.traverse_program(node)
        elif node[1]=="MainFunction":
            self.traverse_main_function(node)
        elif node[1]=="FunctionDeclList":
            for function_decl in node.children:
                self.traverse(function_decl)
        elif node[1]=="FunctionDeclaration":
            self.traverse_function_declaration(node)
        elif node[1]=="Statement":
            print("stms")
            print(edge_list[node[0]])
            for child in edge_list[node[0]]:
                print(child)
                self.traverse(child)
            print(self.wat_code)
        elif node[1]=="Assign":
            print("HELLLO")
            # self.traverse_assign(node)
            self.assign_codegen(node)
            
        # Add more cases for other node types

    def traverse_program(self, node):
        print(node)
        children = edge_list[node]
        print(children)
        for child in children:
            print(child)    
            self.traverse(child)
    
    def traverse_main_function(self, node):
        print("HII")
        print(node)
        # children = edge_list[node[0]]
        # print(children)
        # for child in children:
        #     self.traverse(child)
            
        # Generate WAT code for function declaration
        self.wat_code += f'module(\n\t(func $main \n'
        # Process parameters
        # for param in parameters:
        #     self.wat_code += f'(param ${param}) '
        # Process function body
        # self.traverse(node.function_body)
        # self.wat_code += 'call $Statement\n'
        # End of function declaration
        children = edge_list[node[0]]
        self.traverse(children[0])
        # print('ooooooooooooooooooooooooooooooooooooooooooo')
        # print(self.wat_code)
        self.wat_code += f'))\n'
        # self.wat_code += f"tt"
        # print(self.wat_code)
        
        # print('ooooooooooooooooooooooooooooooooooooooooooo')
        
        # children = edge_list[node[0]]
        # print(children)
        # self.traverse(children[0])
        # for child in children:
        #     print("ok")
        #     print(child)
        #     self.traverse(child)
        # traverse()
        


    def traverse_function_declaration(self, node):
        function_name = node.function_name
        parameters = node.parameters
        # Generate WAT code for function declaration
        self.wat_code += f'(func ${function_name} '
        # Process parameters
        for param in parameters:
            self.wat_code += f'(param ${param}) '
        self.wat_code += ')\n'
        # Process function body
        self.traverse(node.function_body)
        # End of function declaration
        self.wat_code += ')\n'

    def traverse_assign(self, node):
        # variable = node.variable
        # value = node.value
        # Generate WAT code for assignment
        print(self.wat_code)
        DT_IDENTIFIER = edge_list[node[0]][0]
        print(DT_IDENTIFIER)
        dt = edge_list[edge_list[DT_IDENTIFIER[0]][0][0]][0][1]
        print(dt)
        id = edge_list[edge_list[DT_IDENTIFIER[0]][1][0]][0][1]
        print(id)
        
        Exp = edge_list[node[0]][1]
        dt = edge_list[edge_list[DT_IDENTIFIER[0]][0][0]][0][1]

        # DT_IDENTIFIER = 
        
        self.wat_code += f'(local.set $ '
        # self.traverse(value)
        self.wat_code += ')\n'
        
    def assign_codegen(self,node):
        print(111111111111111111111111111111111)
        # print(self.wat_code)'
        if node[0] not in self.edge_list:
            return
        if node[1]=='DT_IDENTIFIER':
            child2_id=self.edge_list[node[0]][1][0]
            var_name=self.edge_list[child2_id][0][1]
            self.wat_code+=f"\t\tlocal ${var_name} i32\n"
        elif node[1]=='Expression':
            if len(self.edge_list[node[0]])==1:
                num=self.edge_list[node[0]][0]
                self.wat_code+=f"\t\ti32.const {num[1]}\n"
                return 
            else:
                self.assign_codegen(self.edge_list[node[0]][0])
                self.assign_codegen(self.edge_list[node[0]][2])
                op=self.edge_list[node[0]][1][1]
                if op=="+":
                    self.wat_code+="\t\ti32.add\n"
                elif op=="-":
                    self.wat_code+="\t\ti32.sub\n"
                elif op=="*":
                    self.wat_code+="\t\ti32.mul\n"
                elif op=="/":
                    self.wat_code+="\t\ti32.div_s\n"
                elif op=="%":
                    self.wat_code+="\t\ti32.rem_s\n"
                elif op=="==":
                    self.wat_code+="\t\ti32.eq\n"
                elif op=="!=":
                    self.wat_code+="\t\ti32.ne\n"
                elif op==">":
                    self.wat_code+="\t\ti32.gt_s\n"
                elif op=="<":
                    self.wat_code+="\t\ti32.lt_s\n"
                elif op==">=":
                    self.wat_code+="\t\ti32.ge_s\n"
                elif op=="<=":
                    self.wat_code+="\t\ti32.le_s\n"
                elif op=="&&":
                    self.wat_code+="\t\ti32.and\n"
                elif op=="||":
                    self.wat_code+="\t\ti32.or\n"
                elif op=="!":
                    self.wat_code+="\t\ti32.eqz\n"
                
        elif node[1]=='Assign':
            child2_id=self.edge_list[node[0]][0][0]
            var_name=self.edge_list[child2_id][1][0]
            var_name=self.edge_list[var_name][0][1]
            for child in self.edge_list[node[0]]:
                self.assign_codegen(child)
            self.wat_code+=f"\t\tlocal.set ${var_name}\n"
        else:
            for child in self.edge_list[node[0]]:
                self.assign_codegen(child)


class codeGenerator:
    def __init__(self, tree):
        self.tree = tree
        
    def dfs_traverse(self, edge_list, node):
        if node not in edge_list.keys():
            return
        
        children = edge_list[node]
        
        for child in children:
            child_type = child[1]
            
            add_op = 'module((func $add (param $lhs i32) (param $rhs i32) (result i32)local.get $lhslocal.get $rhsi32.add)(export "add" (func $add)))'

            # if True:
                
            if child_type == 'FunctionDeclaration':
                # Handle function declaration
                # function_id = children[0]
                # function_name = edge_list[edge_list[function_id][1][0]][0][1]
                
                DT_IDENTIFIER = edge_list[child[0]][0]
                dt = edge_list[edge_list[DT_IDENTIFIER[0]][0][0]][0][1]
                id = edge_list[edge_list[DT_IDENTIFIER[0]][1][0]][0][1]
                
                
                
                
                # self.emit(f'(func ${function_name} (param $param1 i32) (result i32)')
                self.enter_scope()  # Enter function scope

                # Traverse function body
                function_body = edge_list[node][2]
                self.dfs_traverse(edge_list, function_body)

                # self.exit_scope()  # Exit function scope
                self.emit(')')  # End of function

            elif child_type == 'Assignment':
                # Handle assignment
                variable_name = edge_list[edge_list[node][0]][0][1]
                value_node = edge_list[node][2]
                self.dfs_traverse(edge_list, value_node)
                self.emit(f'(local.set ${variable_name})')

            elif child_type == 'BinaryExpression':
                # Handle binary expression
                left_operand = edge_list[node][0]
                right_operand = edge_list[node][2]
                operator = edge_list[node][1][1]  # Assuming operator is part of the node
                self.dfs_traverse(edge_list, left_operand)
                self.dfs_traverse(edge_list, right_operand)
                self.emit(f'(i32.{operator})')

            # Add handling for other node types (conditions, loops, etc.)


if __name__ == '__main__':
    
    if len(sys.argv) != 2:
        print("Usage: python parser.py <input_file>")
        sys.exit(1)

    file = sys.argv[1]

    try:
        with open(file, 'r', encoding="utf8") as f:
            sentence = f.read()
            test_program = sentence
        parser = Lark(grammar, start='program', parser='lalr')
        tree = parser.parse(sentence)
        # print(tree.pretty())
        edge_list={}
        print("Parsing succesfull. The input is syntactically correct. AST Generation Succesfull. The AST file has been created.\n")
        graph =create_ast(parse(test_program),edge_list)
        graph.render('AST.gv', view=True)
        scopecheck1=scopecheck(edge_list)
        startId=list(edge_list.keys())[0]
        print("-------------Scope Checking Started----------------")
        scopecheck1.dfs_traverse(edge_list,startId)
        print("-------------Scope Checking Done----------------")
        typeCheck1 = TypeCheck(edge_list)
        print("-------------Type Checking Started----------------")
        typeCheck1.dfs_traverse(edge_list, startId)
        print("-------------Type Checking Done----------------")
        # print("-------------Code Generation Started----------------")
        # codeGen = WATGenerator(edge_list, startId, startId)
        # codeGen.generate_wat()
        # print(codeGen.wat_code)
        
        # # generate_wat() returns a string, write that to a file of type .wat:
        # with open("output.wat", "w") as f:
        #     f.write(codeGen.wat_code)
        
        # print("-------------Code Generation Done----------------")

        
        
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