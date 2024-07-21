### Let Expressions and Assignment Operator  
cook is used as a let expression, and the "=" operator is used as an assignment operator.  

```cook <datatype> <variable name> = <value>;``` 
#### for example:  
``` shell
 cook num n=25;
```
### List of basic datatypes supported in ACE language  
* integer  
* char
* boolean

In ACE, the user can declare and initialise variables of the above datatypes in separate steps or combine both processes into a single statement.  

### Integer datatype  
The ```num``` keyword is used to declare an integer. 

#### for example:  
```shell
cook num n1;
n1=23;
cook num n2=25;
```
### Char datatype  
The ```char``` keyword is used to declare a char.   

#### for example:  
```shell
cook char c1;
c1='a';
cook char c2='b';
```

### boolean datatype  
The ```flag``` keyword is used to declare a bool. 

#### for example:  
```shell
cook flag b1;
b1=true;
cook flag b2=false;
```

### Syntax for binary operations   

* (+) - Addition
* (-) - Subtraction
* (*) - Multiplication
* (/) - Division
* (#) - Power
* (&) -BITWISE AND
* ( | ) - BITWISE OR
* (&&) - AND 
* ( || ) -  OR 
* (^)- XOR
* (%) - MODULO

* ```(&&)``` and ```(||)``` are Short-circuiting (lazy) boolean operators

### Syntax for unary operations  
* (++) - ADDING ONE
* (--) -  DECREMENTING ONE
* (!) - NOT
* (~) - BITWISE NOT  

### syntax for strings 

```cook str <string name>= “some_string”;```

For strings, users can declare and initialise variables in separate steps or combine both processes into a single statement.  

#### for example:  
```shell
cook str s1;
s1="abc";
cook str s2="def";
```

### Syntax for Arrays 
* Arrays are used to store elements 
* They cannot have different datatype elements
* Declaration of Array:  ```cook < datatype > < arrayname >[length of array];```
* Declaration + Initialization :```cook < datatype > < arrayname > = {values comma separated };```  

```shell
cook num arr1[5];
cook num arr2={ 1 , 2 , 3 , 4 , 5};
```  
* To calculate length: ```len(< arrayname >)```
* For head: ```headof(< arrayname >)```  
* For tail: ```tailof(< arrayname >)```  
* For Cons: ```< array name > = < element > :: < array name >```  
* For accessing  element at ith index : ```< arrayname >[i]```
* For modifying element at ith index : ```< arrayname >[i]=< some value >;```  

```shell
cook num length=len(arr);
cook num head=headof(arr);
cook num tail=tailof(arr);
cook num new_arr= 6 :: arr1;
cook num second_element=arr1[2];
arr1[2]=7;
```

## Syntax to Print 
* Print to the terminal: ```echo( expression to be printed ) ;```
```shell
cook num a=5;
echo(a);
echo(" This prints Hello !");
echo(" This prints a" + a);
```  

## Branches and Loops
* ***Branches*** :
* if/else if ( boolean expression or integer ->{false if 0 else true}) {...}
* else {...}
```shell
cook num a=2;
if(a>2){
    echo("The number is greater than 2");
}
else_if(a<2){
    echo("The number is less than 2");
}
else{
    echo("The number is 2");
}
```  

* ***Loops*** :
* floop is used as an iteration statement(similar to for loop).
* ```break``` exits from loops, and ```continue``` exits the current iteration and continues with the next.
* floop does not support multiple expressions in iteration. 
* Used as : ```floop(declaration + initialization ; stopping condition ; iteration ){.....}```  

```shell
floop(cook num a=1; a < 5; a++){
    continue;
    echo(a);
}
```  

* wloop is used as an iteration statement(similar to while loop). 
* Used as : ```wloop(stopping condition){.....}```  

```shell
cook num iter=5;
wloop(iter>0){
    echo(iter);
    iter--;
    break;
}
```

## Using Functions 
* The functions are entities used to give an output based on certain inputs( not necessary to always have an input and output).
* The language also supports void return type.
* Defining Functions : ```func <data type/void> <function name> ( parameters with data type comma separated ){...... return something  }```
  ```shell
  func num increment_by_one(num a){
  return a+1;
  }
  
  cook num a=5;
  cook num b=increment_by_one(a);
  echo(b);
  ```

## Closures
* A closure is the combination of a function bundled together (enclosed) with references to its surrounding state (the lexical environment). In other words, a closure gives you access to an outer function's scope from an inner function.
* An example of closure in ACE Lang.  

```shell
func func makeFunc(){
    cook str name="Pratham Sagar";
    func display_name(){
        echo(name);
    }
    return display_name;
}

const myFunc = makeFunc();
myFunc();
```  

* As ACE supports closures, the name variable is still accessible by inner function although it's declared in the outer function.  

## Handling Errors
* ```try``` Encloses code that may potentially throw an exception.
* ```catch``` Handles exceptions thrown within a try block, allowing for graceful error handling.
* ```throw``` Explicitly raises an exception within a program, allowing for custom error propagation and handling. Our throw takes a string and shows it on console. 

```shell
func void main(){
try{
cook num result=10/0;
echo(result);
}
catch{
echo("Divide by zero error !");
}
}

func num divide(num divident,num divisor){
if(divisor==0){
throw("Cannot divide by zero!");
}
return dividend / divisor;
}
```



