## Group 7 

To run the CodeGenerator.py file type

```
python CodeGenerator.py codegen_testcases/arthmetic_testcase.ace
```
in shell.

This will generate the output.wat file for the given testcase.

To convert the generated wat file type

```
wat2wasm output.wat -o <wasm_filename>.wasm
```
in shell.


To run the SemanticAnalyzer.py file type

```
python SemanticAnalyzer.py test_cases/test1.ace
```
in shell.

To run the AST_Generator.py file type

```
python AST_Generator.py test_cases/test1.ace
```
in shell.


To run the lalr_parser.py file type

```
python lalr_parser.py test_cases/test1.ace
```
in shell.
