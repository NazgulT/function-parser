#!/bin/bash
clear
echo "Parsing FOL sentence with Function Symbols!"
/usr/bin/python3 src/fparser.py -k FunKB.txt
java -jar forclift.jar
