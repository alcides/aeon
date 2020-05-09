# Æon Programming Language


**Æon** is a programming language with polymorphism and non-restricted-refined types. This language is used as the basis for Refinement Typed Genetic Programming due to its support of static verification of polymorphism.
It is important to make notice that while the **Æon** language does not make any distiction, there are two classes of refinements: **restricted refinements** and **non-restricted refinements**.

**Restricted refinements** are those whose satisfiability is statically verified using a SMT Solver.

**Non-Restricted refinements** are those that SMT solvers are not able to reason about, thus being checked at runtime.


## Requirements

**Æon** basic requirements for running are  Python3.7 and a ll dependencies that can be found in [**requirements.pip**](/requirements.pip)
```
pip install -r requirements.pip
```
or
```
python3.7 -m pip install -r requirements.pip
```

I am currently using [**Visual Studio Code**](https://code.visualstudio.com/) and the **Æon** syntax highlighter. I find it very useful to use the [**Todo+**](https://marketplace.visualstudio.com/items?itemName=fabiospampinato.vscode-todo-plus) to keep track of the Todo list. Give it a try :)


## Modules

**Æon** is composed by different modules to essential for the parsing, typechecking and synthesis of the language. A brief description may help you to understand the role of each package.
 - [**frontend**](aeon/frontend): responsible for parsing the *.ae* file into **Æon** abstract syntax tree and convert it to **Æoncore** tree representation.
 - [**typechecker**](aeon/typechecker): in charge of checking the program and annotating the nodes. If any hole is found during typechecking, its type and contexts are saved for synthesis.
  - [**synthesis.py**](aeon/synthesis.py): contains the non-deterministic synthesizer responsible for generating  random expressions from a given type. 
 - [**automatic**](aeon/automatic): in control of the evolutionary approach for generating a valid and correct solution. It also contains the rules for conversion of refinements into fitness functions.
  - [**interpreter.py**](aeon/interpreter.py): executes an **Æon** program. 

 
## Libraries

To more easily allow the interaction of the user with the language, **Æon** provides different kinds of implemented [**libraries**](aeon/libraries). The specification of each function for each library can be found in the [**proper markdown**](aeon/libraries/Documentation.md).


## Examples

**Æon** acts like syntactic sugar from its core, providing a user friendly syntax, making it easy and intuitive for a new user to engage into program synthesis. The following examples present the basics of the language, many more can be found in the [**examples**](examples/aeon3/) folder.

We start by defining a new **Nat** type by refining the **Integer** type with the condition *x >= 0*. The program computes the fibonacci from a given value with type **Nat**.  The output of the functions is restrictively refined to ensure that we never compute a value smaller or equal than the input. The body of the function is implemented using the inline **if then else** expression.
```haskell
type Nat as {x:Integer | x >= 0};

fibonacci(x:Nat) -> {y:Nat | y >= x} {
    if (x <= 1) then x else (n - 1) + fibonacci(n - 2);
}
```

Similarly to the previous example, we create a type alias **RestrictedValue** by refining the **Integer** type. **Æon** allows low-level details to be implemented in another language by using the **native** construct. The *buildKey* and *getKey* functions are natively implemented in the language.
The **decipher** function takes an integer and deciphers the value with the key. The output function ensures that our implementation is bug free! In this case a type exception would raise since the *i* variable can take any value even smaller than ```k.key```. One could easily fix this by refining key value to ensure that it is smaller than *i*, ```{k:Key | k.key < < i}```. 
In the **cipher** function by providing the hole operator, ```??```, we are able to delegate the implementation of the function to the compiler. We present our intention of the function behaviour with the **where** specification, in a way to help the synthesis of the program.
```haskell
type RestrictedValue as {x:Integer | x >= 0 && x <= 1024};

type Key {
    {key : RestrictedValue};
}

buildKey(i:RestrictedValue) -> {k:Key | k.key == i} = native;
getKey(key:Key) -> key:RestrictedValue = native;

decipher(i:Integer, k:Key) -> {j:Integer | j > 0} {
    i - getKey(k); 
}

cipher(i:Integer, k:Key) -> j:Integer where {j >= 0 and i == decipher(j, getKey(k))} {
    ??;
}
```

