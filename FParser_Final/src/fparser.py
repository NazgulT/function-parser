#!/usr/bin/python3

from logic import *
from utils import *
from bidict import *
import itertools
import random
import sys, getopt

"""List of constants in the universe"""
constant_names = {Expr('Adam'),Expr('Beth'),Expr('Bob'),Expr('Carol'), Expr('Naz'), Expr('Amy'), Expr('Vaishak'), Expr('Stefanie')}
PROPOSITIONS = list("0123456789ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz")
domain = list()
var_s = list()
terms = set()
BJ = bidict({})

def eliminate_functions_from(expression):
    """Given a functional expression, returns an equivalent expression in relational form
    e.g. given expression: F(x) ~= Adam v M(x) = Beth
    returns: -F(x,Adam) v M(x,Beth)"""
    s = expr(expression)
    if not s.args or is_symbol(s.op):
        return s
    args = list(map(eliminate_functions_from, s.args))
    if s.op == '==' or s.op == '~=':
        rel = increase_arity(list(s.args), oper=s.op)
        return Expr(rel.op, *tuple(rel.args))
    else:
        assert s.op in ('&', '|', '~', '-->', '<--', '<->')
        return Expr(s.op, *args)


def increase_arity(atom, oper=None, dom=None):
    """Returns relation given a clause. Helper function for the 'eliminate_functions_from()' function above."""
    if isinstance(atom, Expr):
        prop = atom
        prop_args = atom.args
        constant = dom
    else:
        prop = atom[0]
        prop_args = prop.args
        constant = atom[1]

    if oper == '~=':
        negation = '~'
    else:
        negation = ''

    s = ''.join([negation, str(prop.op),'('])
    p=''
    for a in list(prop_args):
        p = ''.join([p,str(a),','])
    q = ''.join([str(constant),')'])
    new_expr = expr(''.join([s,p,q]))
    return new_expr

def gnd(expression, domain, var):
    """Grounds a given expression by substituting variables var by constants in the domain"""
    for d in domain:
            for x in var:
                yield subst({x:d}, expression)
'''
def retrieve_domain(x):
    """Given an expression x, returns domain of x that does not include propositions.
    e.g. given F(Adam) = x ==> CEO = x
    returns: {Adam}"""
    constants = constant_symbols(x)
    propositions = prop_symbols(x)
    print("constants = {}, propositions {}".format(constants,propositions))
    return list(set(p for p in propositions if p in constants))
'''

def increase_domain(domain):
    """Returns an arbitrary constant that is not already in the domain"""
    arbitrary_constant = random.choice(list(constant_names - set(domain)))
    domain.append(arbitrary_constant)
    return arbitrary_constant

def is_empty(x):
    """Returns TRUE if x is empty"""
    return len(x) == 0

def get_terms(expression):
    """Returns a list of terms of the ground expression.
    e.g. given  F(Adam) = Bob ==> CEO = Bob
    returns {F(Adam), CEO}"""
    s = expr(expression)
    args = list(map(get_terms, s.args))
    if s not in domain and s not in var_s and is_symbol(s.op):
        terms.add(s)


def RGND(expression):
    dnf_KB = to_cnf(expression)
    base_KB_fo = []
    base_KB_prop = []
    for i in gnd(dnf_KB, domain, variables(dnf_KB)):
        base_KB_prop.append(bijection(i))
        base_KB_fo.append(i)
    rgnd_fo = associate('&',base_KB_fo)
    rgnd_prop = associate('&',base_KB_prop)
    return rgnd_fo, rgnd_prop

def xor_t_D(terms_list):
    """Performs XOR(t,D): t \in T where T = terms_list.
    Terms in XOR(t,D) are converted into relational form"""
    for term in terms_list:
        if not isinstance(term,Expr):
            xor_t_D(term)
        else:
            atoms_list = []
            for d in domain:
                rel = increase_arity(term, dom=d)
                atoms_list.append(Expr(rel.op, *rel.args))
            yield atoms_list



def parse(expression):
    #-----------Parsing Functional KB-----------#
    if is_empty(domain):
        for i in range(len(var_s)):
            increase_domain(domain)
        print("Increased domain to the size of variables. D = {}".format(domain))
    relational_KB = eliminate_functions_from(expression)
    print("Relational KB x = {}".format(relational_KB))

    print("Adding an arbitrary constant = {}".format(increase_domain(domain)))
    rgnd_fo, rgnd_prop = RGND(relational_KB)

    print("Adding another arbitrary constant = {}".format(increase_domain(domain)))
    cnf_fo = []; cnf_prop = []
    for fo, prop in XOR(expression):
        cnf_fo.append(to_cnf(fo))
        cnf_prop.append(to_cnf(prop))

    xor_fo = associate('&', [rgnd_fo, associate('&',cnf_fo)])
    xor_prop = associate('&', [rgnd_prop, associate('&',cnf_prop)])


    #print("########Relational KB########")
    #print("RGND(x) = {}".format(rgnd_fo))
    #print("##############################")
    #print("XOR(t,D): t in T, where T = {} = {}".format(terms,cnf_fo))
    #print("##############################")
    #print("XOR(x) = {}".format(xor_fo))


    #print("########Propositional KB########")
    #print("RGND(x) = {}".format(rgnd_prop))
    #print("##############################")
    #print("XOR(t,D): t in T, where T = {} = {}".format(terms,cnf_prop))
    #print("##############################")
    #print("XOR(x) = {}".format(xor_prop))

    return xor_fo, xor_prop


def XOR(expression):
    for g in gnd(expression, domain, var_s):
        get_terms(g)
    print("Terms = ", terms)
    dnf = []
    for x in xor_t_D(list(terms)):
        yield concatenate("^", x), concatenate("^",list(map(bijection,x)))


def concatenate(op,li):
    s = ""
    le = len(li)
    for i in range(le - 1):
        s+=str(li[i])+op
    s+=str(li[le-1])
    return s


def bijection(x):
    args = list(map(bijection,x.args))
    if is_symbol(x.op) and x not in domain:
        if x not in BJ.keys():
            prop = PROPOSITIONS.pop()
            BJ.update({x:prop})
            return prop
        else:
            return BJ.get(x)
    else:
        return Expr(x.op, *args)


def parseQ(query):
    q = eliminate_functions_from(query)
    return bijection(standardize_query(q))


def toString(self,x):
    return str(x)

def replace(x, old_c, new_c):
    assert isinstance(x, Expr)
    return expr(str(x).replace(str(old_c),str(new_c)))


def standardize_query(q):
    if is_symbol(q.op):
        query = q
        for c in constant_symbols(q):
            if c not in domain:
                query = replace(q, c, domain[-1])
        return query
    elif isinstance(q, Expr):
        return Expr(q.op, *[standardize_query(arg) for arg in q.args])

def output_to_file(xor_prop, q_prop):
    filename = "propKB.txt"
    try:
        f = open(filename,"w")
        for value in BJ.values():
            f.write("predicate "+value+" 1 1\n")
        f.write("\n")
        s_xor_prop = str(xor_prop).replace("&", "\n").replace("(","").replace(")","").replace(" ","").replace("~","!").replace("|"," v ")
        f.write(s_xor_prop)
        f.write("\n")
        s_q_prop = str(q_prop).replace("&", "\n").replace("(","").replace(")","").replace(" ","").replace("~","!").replace("|"," v ")
        clauses = s_q_prop.split('\n')
        for clause in clauses:
            f.write("query "+ clause+"\n")
    except OSError as err:
        print("OS error: {0}".format(err))
    except ValueError:
        print("Could not convert data to an integer.")
    except:
        print("Unexpected error:", sys.exc_info()[0])
        raise
        f.close
    return filename

def process(line):
    return expr(line)
    #associate('&', expr(lines))


def main(argv):
    kb_filename = ''
    query = ''
    try:
        #opts, args = getopt.getopt(argv,"hk:q:",["kb=","query="])
        opts, args = getopt.getopt(argv,"hk:",["kb="])
    except getopt.GetoptError:
        #print('parser_func.py -k <filename> -q <query>')
        print('parser_func.py -k <filename>')
        sys.exit(2)
    for opt,arg in opts:
        if opt == '-h':
            print('parser_func.py -k <filename> -q <query> \n The expression must be put in the models folder and must be of the form (F(Sally) == Fred) --> (R == x). \n Acceptable logical operators:')
            sys.exit()
        elif opt in ("-k", "--kb"):
            kb_filename = arg
        #elif opt in ("-q", "-query"):
            #query = arg


    print("%%%%%%%%%%%%%%%%%%%MAIN%%%%%%%%%%%%%%%%")
    #expression = expr("((F(Sally) == Frank) | (F(Sally) == Fred)) & ((F(Sally) ~= x) --> (R == x))")
    #expression = expr("(F(x) == Adam) --> (M(x) ~= Beth)")
    #query = expr("((F(Henry) == Bob) | (F(Sally) == Bob))")
    #expression = expr("((F(Adam) == Dave) & (F(x) ~= x))")
    #query = expr("(F(John) == Dave)")
    #expression = expr(sentence)
    #expression = expr(open("models/"+filename,"r").read())
    lines = []
    q=''
    with open('models/'+kb_filename) as fp:
        for line in fp.readlines():
            line = line.strip()
            if line[0:6] == 'QUERY:':
                q = line[7:]
                break
            expression = process(line)
    query = expr(q)
    print('Parsing expression with function symbols: {}'.format(expression))
    global domain
    domain = constant_symbols(expression)
    print("Domain D = {}".format(domain))
    global var_s
    var_s = variables(expression)
    print("Variables = {}".format(var_s))
    fo, kb_prop = parse(expression)
    q_prop = parseQ(query)
    output_to_file(kb_prop, q_prop)
    print("Successfully parsed an expression. \nThe output is written to propKB.txt")
    print("Query = {}".format(query))
    #print("Bijection Dictionary (FOL <==> PROP):",BJ)

if __name__=="__main__":
    main(sys.argv[1:])
