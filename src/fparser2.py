from logic import *
from utils import *
import itertools
import random
import sys, getopt
from argparse import *
from itertools import permutations

constant_names = {Expr('Adam'),Expr('Beth'),Expr('Bob'),Expr('Carol'), Expr('Lisa'), Expr('Amy'), Expr('Ellis'), Expr('Lorde')}

def main(argv):
    parser = ArgumentParser()
    parser.add_argument('-k', '--kbfile', help = 'Enter the filename where funcion KB is stored.')
    #parser.add_argument('-h', '--help', help = '/usr/bin/python3 fparser.py -k FunKB.txt')
    args = parser.parse_args()
    if args.kbfile:
        #kb_filename = args.kbfile
        print("Processing file {}".format(args.kbfile))
        processKB(args.kbfile)
    else:
        print("parser_func.py -k <filename>")

def processKB(filename):
    q=''
    with open('models/'+filename) as fp:     #process the file <filename>
        for line in fp.readlines():
            line = line.strip()                 #remove \n from each line
            if line[0:6] == 'QUERY:':           #everything after the QUERY: is treated as query
                q = line[7:]
                break
            expression = process(line)          #otherwise it is a expression KB
    query = process(q)
    print('Parsing expression with function symbols: {}'.format(expression))
    global domain
    domain = get_domain(expression)       #retrieve constans from the expression to form domain D
    #print("Domain D = {}".format(domain))
    global var_s
    var_s = variables(expression)               #retrieve variables from the expression
    #print("Variables = {}".format(var_s))
    #print(eliminate_functions_from(expression))
    print("Domain = {}".format(domain))
    parse(expression)
    #fo, kb_prop = parse(expression)             #parse KB with functions into KB with relations
    #q_prop = parseQ(query)                      #parse query with functions into query with relations
    #output_to_file(kb_prop, q_prop)             #output the result to the file to be further processed by scala code and fed to WFOMC for inference
    #print("Successfully parsed an expression. \nThe output is written to propKB.txt")
    #print("Query = {}".format(query))

def process(line):
    #helper function. Converts a line from the input models file into Expr.
    return expr(line)

def increase_domain(domain):
    """Increases the existing global domain by an arbitrary constant randomly chosen from the list of constants defined for the universe.
    Returns this arbitrary constant that is not already in the domain"""
    arbitrary_constant = random.choice(list(constant_names - set(domain)))  #get the difference between the constant names in the universe and the current domain
    domain.append(arbitrary_constant)                                       #add randomly chosen one to the current domain
    return domain

def get_domain(s):
    domain = constant_symbols(s)
    var_s = variables(s)
    if len(var_s) > len(domain):
        return increase_domain(domain)
    return domain

def eliminate_functions_from(expression):
    """Given a functional expression, returns an equivalent expression in relational form
    e.g. given expression: (F(x) ~= Adam) | (M(x) = Beth)
    returns: -F(x,Adam) | M(x,Beth)"""
    s = expr(expression)                                    #Make sure to convert an argument to type-expression
    if not s.args or is_symbol(s.op):                       #If a literal is received just return it
        return s
    args = list(map(eliminate_functions_from, s.args))
    if s.op == '==' or s.op == '~=':                        #recognise function related operators
        #rel = increase_arity(list(s.args), oper=s.op)       #convert the function into relation
        #return Expr(rel.op, *tuple(rel.args))
        return s.toRelation()
    else:
        assert s.op in ('&', '|', '~', '-->', '<--', '<->') #otherwise, ensure that the operators listed stay unchanged
        return Expr(s.op, *args)

def gnd(expression):
    """Grounds a given expression by substituting variables var by constants in the domain domain"""
    domain = get_domain(expression)
    var_s = variables(expression)
    substitutions = {}
    for p in permutations(domain,len(domain)):
        print("p={}".format(p))
        z = zip(var_s,p)
        substitutions = dict(z)
        print("substitutions={}".format(substitutions))
        sub = subst(substitutions, expression)
        print("expression = {}".format(sub))

def terms(s):
    s = expr(s)
    for subexprs in subexpressions(s):
        if is_symbol(subexprs.op) and subexprs.args:
            yield subexprs

def parse(s):
    filename = "output/mln.mln"
    identifier = "person"                      #the name of the file to save the output. Name is fixed.
    weight =  "1"
    f = open_file(filename)
    header(f, identifier)
    for t in terms_to_mln(terms_generic(s), identifier):
        to_mln_file(f,t)
    #to_mln_file(f,subst_mln(to_cnf(s)))
    #print(subst_mln(to_cnf(s)))
    #print("s={}".format(s))
    s1 = subst_mln(to_cnf(s))
    #print("s1={}".format(s1))
    for xt in s1.split('\n'):
        f.write(weight+" "+balance_brackets(xt)+"\n")
    xortd(f,s,weight)


def xortd(f,s,w):
    x = []
    for t in terms(s):
        for d in domain:
            if len(t.args) == 1:
                expression = Expr(t.op, t.args[0], d)
                x.append(expression)
        #xr = xor(x)
        #print("xr = {}".format(xr))
        #xrc = to_cnf(xr)
        #print("xrc = {}\n".format(xrc))
        #xs = str(xrc).replace("&","\n").replace("|","v").replace("~","!")
        #print("str = {}".format(xs))
        #xs = subst_mln(to_cnf(xor(x)))
        xs = subst_mln(xor(x))
        #print("xs = {}".format(xs))
        for xt in xs.split('\n'):
            #print("xt = {}".format(xt))
            #print("balanced = {}".format(balance_brackets(xt)))
            f.write(w+" "+balance_brackets(xt)+"\n")
        del x[:]

def terms_generic(s):
    ts = []
    for t in terms(s):
        print("terms={}".format(t))
        for d in domain:
            if len(t.args) == 1:
                expression = Expr(t.op, t.args[0], d)
        ts.append(expression)
    return ts

def xor(iterable):
    x = Expr('^', *iter(iterable))
    return x

def removeUnbalanced(s):
    def remove_char(stri, n):
        #print("n={}".format(n))
        if n!=-1:
            first_part = stri[:n]
            last_part = stri[n+1:]
            whole = first_part + last_part
            #print("n = {}".format(n))
            #print("first_part = {}".format(first_part))
            #print("last_part = {}".format(last_part))
            #print("whole = {}".format(whole))
            return whole
        return stri
    opening=set('([{')
    new=set(')]}{[(')
    match=set([ ('(',')'), ('[',']'), ('{','}') ])
    stack=[]
    stackcount=[]
    elem=0
    for i,char in enumerate(s,1):
        if char not in new:
            continue
        elif char in opening:
            stack.append(char)
            stackcount.append(i)
        else:
            if len(stack)==0:
                #print("i:",i)
                return remove_char(s,i-1)
            lastOpen=stack.pop()
            lastindex=stackcount.pop()
            if (lastOpen, char) not in match:
                #print ("do not match:",i)
                return remove_char(s,i-1)
    length=len(stack)
    if length!=0:
      elem=stackcount[0]
      #print ("elem:",elem)
    return remove_char(s,elem-1)

def header(f, identifier):
    f.write(identifier+"={")
    for d in domain:
        f.write(str(d))
        if domain.index(d) != len(domain) - 1: f.write(",")
    f.write("}\n")

def terms_to_mln(terms_list, identifier):
    test=set()
    for t in terms_list:
        test.add(Expr(t.op, *[identifier]*len(t.args)))
    return test

def subst_mln(x):
    return str(x).replace('& ','\n').replace('|','v').replace('~','!')

def balance_brackets(x):
        b = removeUnbalanced(x)
        #print("removeUnbalanced = {}".format(b))
        #return removeUnbalanced(x)
        return b

def deleteContent(pfile):
    pfile.seek(0)
    pfile.truncate()

def open_file(filename):
    #filename = "output/"+input+"_mln.txt"                         #the name of the file to save the output. Name is fixed.
    try:
        f = open(filename,"w")
        deleteContent(f)
    except OSError as err:
        print("OS error: {0}".format(err))
    except ValueError:
        print("Could not convert data to an integer.")
    except:
        print("Unexpected error:", sys.exc_info()[0])
        raise
        f.close
    return f

def close_file(f):
    try:
        f.close
    except OSError as err:
        print("OS error: {0}".format(err))
    except ValueError:
        print("Could not convert data to an integer.")
    except:
        print("Unexpected error:", sys.exc_info()[0])
        raise
        f.close
        return False
    return True

def to_mln_file(f,s):
    f.write(str(s)+"\n")
    #return filename

if __name__=="__main__":
    main(sys.argv[1:])
