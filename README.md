Description
===========

This is an XOR parser to compile first-order logic language with function symbols into propositional CNF with an intermediate step of converting FOL functions into relations.   
For example: given input in the form "((F(x) ~= Adam) --> (M(x) == Beth))", the parser first converts function symbols into corresponding relations as in "(F(x,Adam) --> M(x,Beth))", and then converts the latter into propositional CNF as in "(p --> q)", where p and q stand for F(x,Adam) and M(x,Beth), respectively.  
  
Major steps include:  
-parse(expression): contains the main logic. Reads in the knowledge base from the FunKB.txt file specified in parser.sh and if correct passes for encoding.  
-RGND(expression): grounds the expressions wrt domain with k arbitrary constants. Returns relational KB and its propositional model in CNF.  
-XOR_TD(expression): retrieves primitive terms from the expression, and applies exclusive-or. Returns propositional theory of XOR(t,D).  
-XOR(expression): returns a conjunction of RGND and XOR_TD in propositional CNF.  
  
An example showing how these routines work in practice is shown in Notes.pdf attached.  

Usage
=====

To run the project one should run the "parser.sh" executable.

	$ ./parser.sh

It is assumed that python3 is installed at /usr/bin/python3.

Input format
============
The input to the parser should be saved in a separate file with .txt extension. The input file must be saved in /models directory. The name of the file can be specified arbitrarily, however this must be reflected in parser.sh.   
  
An example input file with acceptable format would look as follows:  
  
S(Adam) & (S(x) --> (E(y) ~= x))  
QUERY: E(Bob) == Adam  
  
The first row in the file must be the model, the second row must be a query: query must be identified with QUERY: keyword.  
  
Note:   
-predicates are upper-case letters: F, M, S, E...  
-constants are words with an upper-case first letter: Adam, Beth...  
-variables are lower-case single letters:x, y,...  
  
Important
=========
It is important to put parentheses correctly. Remeber to always parenthesize function symbols. 

Output format
=============
The XOR parser outputs resulting propositional model theory in CNF to the file named "propKB.txt" in the /output directory. It can be viewed but it is advised not to change the name and the contents of the file once it has been generated since it is going to be processed by the WFOMC inference.

WFOMC inference
===============

Once the XOR parser produces output in propositional form and saves it into the "propKB.txt" file in the correct format, the custom-code written in scala and saved as part of WFOMC project, invokes this file and processes it.   
Be careful not to change the "propKB.txt" contents, because the scala code looks for specific keywords. The code written for inference step is assembled using sbt into "forclift.jar". If one needs to modify inference steps, he should unpack this .jar file, and compile/assembly again using sbt.  

External Dependencies
=====================
  
[c2d compiler](http://reasoning.cs.ucla.edu/c2d/): Adnan Darwiche's c2d compiler.  
The c2d compiler used for propositional inference and verification must be stored in the /external directory.  
  
References
==========
  
For detailed information on Python Expressions, please refer to   
<https://docs.python.org/3/reference/expressions.html#expressions>
  
Contact
=======
  
For further clarification and thesis related questions please contact   
Nazgul Tazhigaliyeva, MSc in Artificial Intelligence  
<s1667865@sms.ed.ac.uk>  
alternatively on  
<nazgul.tazhigaliyeva@gmail.com>  
