#!/usr/bin/python3

from logic import *
from utils import *
from bidict import *
import itertools
import random
import sys, getopt
from argparse import *
import time

"""List of constants in the universe"""
constant_names = {Expr('Adam'),Expr('Beth'),Expr('Bob'),Expr('Carol'), Expr('Lisa'), Expr('Amy'), Expr('Ellis'), Expr('Lorde')}
PROPOSITIONS = list("abcdefghijklmnopqrstuvwxyzabcdefghijklmnopqrstuvwxyzabcdefghijklmnopqrstuvwxyzabcdefghijklmnopqrstuvwxyzabcdefghijklmnopqrstuvwxyz")
NUMBERS = list("123456789012345678901234567890123456789012345678901234567890")
domain = list()
var_s = list()
terms = set()
mapping = bidict({})

def eliminate_functions_from(expression):
    """Given a functional expression, returns an equivalent expression in relational form
    e.g. given expression: (F(x) ~= Adam) | (M(x) = Beth)
    returns: -F(x,Adam) | M(x,Beth)"""
    s = expr(expression)                                    #Make sure to convert an argument to type-expression
    if not s.args or is_symbol(s.op):                       #If a literal is received just return it
        return s
    args = list(map(eliminate_functions_from, s.args))
    if s.op == '==' or s.op == '~=':                        #recognise function related operators
        rel = increase_arity(list(s.args), oper=s.op)       #convert the function into relation
        return Expr(rel.op, *tuple(rel.args))
    else:
        assert s.op in ('&', '|', '~', '-->', '<--', '<->') #otherwise, ensure that the operators listed stay unchanged
        return Expr(s.op, *args)


def increase_arity(atom, oper=None, dom=None):
    """Helper function. Returns a relation given a function formula.
    Increases the arity of the atom in the function by the constant/variable in the assignment.
    e.g.: given F(x) ~= Adam
    return ~F(x, Adam)"""
    if isinstance(atom, Expr):  #the atom argument can be of two types. If it is an Expression then
        prop = atom             #get the functor
        prop_args = atom.args   #get its arguments
        constant = dom          #get the assignment
    else:                       #if it is list or tuple
        prop = atom[0]          #get the first argument which the functor
        prop_args = prop.args   #get is arguments
        constant = atom[1]      #get the assignment

    if oper == '~=':
        negation = '~'
    else:
        negation = ''

    s = ''.join([negation, str(prop.op),'('])   #the rest is manipulating the string to join functor, arguments and assignment into one relation
    p=''
    for a in list(prop_args):
        p = ''.join([p,str(a),','])
    q = ''.join([str(constant),')'])
    new_expr = expr(''.join([s,p,q]))
    return new_expr

def gnd(expression, domain, var):
    """Grounds a given expression by substituting variables var by constants in the domain domain"""
    for d in domain:
            for x in var:
                yield subst({x:d}, expression)  #Substitute each occurrence of the variable in the expression by the constant from the domain

def increase_domain(domain):
    """Increases the existing global domain by an arbitrary constant randomly chosen from the list of constants defined for the universe.
    Returns this arbitrary constant that is not already in the domain"""
    arbitrary_constant = random.choice(list(constant_names - set(domain)))  #get the difference between the constant names in the universe and the current domain
    domain.append(arbitrary_constant)                                       #add randomly chosen one to the current domain
    return arbitrary_constant                                               #return this arbitrary constant

def is_empty(x):
    """Returns TRUE if x is empty"""
    return len(x) == 0

def get_terms(expression):
    """Retrieves a list of terms from the ground expression.
    e.g. given  F(Adam) == Bob ==> CEO == Bob
    appends {F(Adam), CEO} to the global 'terms' list. """
    s = expr(expression)
    args = list(map(get_terms, s.args))
    if s not in domain and s not in var_s and is_symbol(s.op):
        terms.add(s)

def RGND(expression):
    """Performs RGND(expression) = GND(expression,k) where k is the rank of expression i.e. grounds the expression w.r.t. domain + an arbitrary constant.
    Returns both ground first-order formula and its propositional bijection.

        arg: expression to be ground
        return: ground expression and its propositional bijection."""
    dnf_KB = to_cnf(expression)                         #Convert given expression to CNF
    base_KB_fo = []
    base_KB_prop = []
    for i in gnd(dnf_KB, domain, variables(dnf_KB)):    #ground the CNF KB w.r.t. domain
        base_KB_prop.append(bijection(i))               #map each literal in CNF KB to a proposition, append to PROP KB
        base_KB_fo.append(i)                            #append ground CNF KB to FO KB list
    rgnd_fo = associate('&',base_KB_fo)                 #convert lists of FO and PROP KBs to CNF
    rgnd_prop = associate('&',base_KB_prop)
    return rgnd_fo, rgnd_prop

def xor_t_D(terms_list):
    """Helper function for XORTD. Converts functional terms into relational form"""
    for term in terms_list:                                 #for each term in the get_terms()
        if not isinstance(term,Expr):                       #if it is a nested list of terms
            xor_t_D(term)                                   #recurse the function only terms of type Expr left
        else:
            atoms_list = []
            for d in domain:
                rel = increase_arity(term, dom=d)
                atoms_list.append(Expr(rel.op, *rel.args))  #append the relational terms to the terms_list
            yield atoms_list


def XORTD(expression):
    """Performs XOR(t,D): t \in T where T = get_terms.
    Terms in XOR(t,D) are converted into relational form."""
    for g in gnd(expression, domain, var_s):                                #ground the expression first
        get_terms(g)                                                        #get terms T in functional form
    print("Terms = ", terms)
    dnf = []
    for x in xor_t_D(list(terms)):                                          #convert them into relational form
        yield concatenate("^", x), concatenate("^",list(map(bijection,x)))  #and return the concatenated terms associated with the logical xor operator in both FO and PROP forms.


def concatenate(op,li):
    """Helper function to concatenate the members of the list li using an operator op.
    The 'associate' routine does the same, however, it tends to flatten the formula.
    Flat xor formulas cannot be correctly converted into CNF, therefore, parentheses are needed to
    imitate the precendence from left to right.
    e.g. 'p xor q' is converted to CNF just fine,
    but 'p xor q xor s' will not work, therefore, we are doing ((p xor q) xor s) instead"""
    s = ""
    le = len(li)
    for i in range(le - 1):
        s+=str(li[i])+op
    s+=str(li[le-1])
    return s


def bijection(x):
    """Returns an equivalent expression to x, in propositional form.
    Performs bijectional mapping from atoms to propositions.
    The 'mapping' dictionary is global.
    The alpha-numerical list of PROPOSITIONS is also defined as global."""
    args = list(map(bijection,x.args))
    if is_symbol(x.op) and x not in domain:                                            #if we are dealing with atoms and not constants
        if x not in mapping.keys():                                                    #if the atom is not already in the dictionary
            prop = str(PROPOSITIONS.pop())
            if prop in mapping.values():
                prop = str(prop) + str(NUMBERS.pop())
            mapping.update({x:prop})                                                   #enter the proposition as the value and the atom as the key of the mapping
            return prop
        else:
            return mapping.get(x)                                                      #if the atom was seen before, then get its prop representation
    else:
        return Expr(x.op, *args)


def standardize_query(q):
    """Given query q, return a query whose unknown constant symbols are mapped to those arbitrary constants that account for open universe.
    e.g. if q = F(Sally) == John and John is not in the domain.
    return F(Sally) == Bob where Bob is one of those arbitrary constants added during RGND and XORTD.
    In other words, Bob accounts for some unknown that can become anything."""
    if is_symbol(q.op):
        query = q
        for c in constant_symbols(q):
            if c not in domain:                                         #if constants in the query are not in the domain
                query = replace(q, c, domain[-1])                       #replace the unknown constant with an arbitrary constant, which is usually the last members of the domain.
        return query
    elif isinstance(q, Expr):
        return Expr(q.op, *[standardize_query(arg) for arg in q.args])  #do it in recursion of query is complex and nested

def parseQ(query):
    """Parses the query. Returns the propositional form of the query."""
    q = eliminate_functions_from(query)     #convert any functions in the query into relations
    return bijection(standardize_query(q))  #return prop bijection


def replace(x, old_c, new_c):
    """Helper function. Replaces the old_c by new_c in expression x. """
    assert isinstance(x, Expr)
    return expr(str(x).replace(str(old_c),str(new_c)))

def deleteContent(pfile):
    pfile.seek(0)
    pfile.truncate()

def output_to_file(xor_prop, q_prop):
    """A routine to encode the XOR output so that it is compatible with format received by WFOMC.
    The encoding is put into a file. WFOMC accepts input in MLN, FactorGraph and Weighted CNF format.
    We will be feeding the Weighted CNf input file. The format is as follows:

    predicate r 1 1
    predicate p 0.5 0.5

    r
    r v q


    """
    filename = "output/propKB.txt"                         #the name of the file to save the output. Name is fixed.
    try:
        f = open(filename,"w")
        deleteContent(f)
        for value in mapping.values():
            f.write("predicate "+value+" 1 1\n")    #enter each predicate from the mapping into file with the predicate prefix and append weights. For now the weights are 1 for simplicity.
        f.write("\n")
        #replace occurence of operators incompatible with WFOMC by those accepted by WFOMC
        s_xor_prop = str(xor_prop).replace("&", "\n").replace("(","").replace(")","").replace(" ","").replace("~","!").replace("|"," v ")
        f.write(s_xor_prop)
        f.write("\n")
        #do the same for processed queries
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


def parse(expression):
    #-----------Parsing Functional KB-----------#
    """This is the main parsing routine.

        arg: KB read from the filename
        return: logical xor of the propositional form of this KB"""
    start_time = time.time()

    if is_empty(domain):                                                                #if somehow expression contains only variables
        for i in range(len(var_s)):                                                     #iterate over the rank of the expression
            increase_domain(domain)                                                     #increase the domain by at least one constant defined in the universe
        print("Increased domain to the size of variables. D = {}".format(domain))
    relational_KB = eliminate_functions_from(expression)                                #convert function symbols to corresponding relations
    print("Relational KB x = {}".format(relational_KB))

    print("CNF = {}".format(to_cnf(relational_KB)))
    print("Adding an arbitrary constant = {}".format(increase_domain(domain)))          #add an arbitrary constant to the domain before RGND
    rgnd_fo, rgnd_prop = RGND(relational_KB)                                            #perform RGND(expression) w.r.t. domain

    print("Adding another arbitrary constant = {}".format(increase_domain(domain)))     #increase the domain by another arbitrary constant befor performing XOR
    cnf_fo = []; cnf_prop = []
    for fo, prop in XORTD(expression):                                                    #perform XOR(t,D): t \in T, where T = terms_list
        cnf_fo.append(to_cnf(fo))
        cnf_prop.append(to_cnf(prop))

    xor_fo = associate('&', [rgnd_fo, associate('&',cnf_fo)])                           #perform XOR = RGND(expression) & XOR(t,D): t \in T, where T = terms_list using FO symbols
    xor_prop = associate('&', [rgnd_prop, associate('&',cnf_prop)])                     #perform XOR = RGND(expression) & XOR(t,D): t \in T, where T = terms_list using PROP symbols

    elapsed_time = time.time() - start_time
    print("Parsing time = {}".format(elapsed_time))
    #Uncomment these to visualise every step of the parser
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

def process(line):
    #helper function. Converts a line from the input models file into Expr.
    return expr(line)
    #associate('&', expr(lines))

def main(argv):
    """Performs the main logic. Reads the the KB from the /models/<filename> and converts it into type suitable for parsing."""

    kb_filename = ''
    parser = ArgumentParser()
    parser.add_argument('-k', '--kbfile', help = 'Enter the filename where funcion KB is stored.')
    #parser.add_argument('-h', '--help', help = '/usr/bin/python3 fparser.py -k FunKB.txt')
    args = parser.parse_args()
    if args.kbfile:
        kb_filename = args.kbfile
        print("Processing file {}".format(args.kbfile))
        processKB(kb_filename)
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
    domain = constant_symbols(expression)       #retrieve constans from the expression to form domain D
    print("Domain D = {}".format(domain))
    global var_s
    var_s = variables(expression)               #retrieve variables from the expression
    print("Variables = {}".format(var_s))
    fo, kb_prop = parse(expression)             #parse KB with functions into KB with relations
    q_prop = parseQ(query)                      #parse query with functions into query with relations
    output_to_file(kb_prop, q_prop)             #output the result to the file to be further processed by scala code and fed to WFOMC for inference
    print("Successfully parsed an expression. \nThe output is written to propKB.txt")
    print("Query = {}".format(query))
    #print("Bijection Dictionary (FOL <==> PROP):",mapping)


    '''
    formula = expr(expression & (query))
    print("formula:",formula)
    domain = constant_symbols(formula)       #retrieve constans from the expression to form domain D
    print("Domain D = {}".format(domain))
    var_s = variables(formula)               #retrieve variables from the expression
    print("Variables = {}".format(var_s))
    fo, kb_prop = parse(formula)
    q_prop = parseQ(query)                      #parse query with functions into query with relations
    output_to_file(kb_prop, q_prop)             #output the result to the file to be further processed by scala code and fed to WFOMC for inference
    '''

if __name__=="__main__":
    main(sys.argv[1:])



#expression = expr("((F(Sally) == Frank) | (F(Sally) == Fred)) & ((F(Sally) ~= x) --> (R == x))")
#expression = expr("(F(x) == Adam) --> (M(x) ~= Beth)")
#query = expr("((F(Henry) == Bob) | (F(Sally) == Bob))")
#expression = expr("((F(Adam) == Dave) & (F(x) ~= x))")
#query = expr("(F(John) == Dave)")
#expression = expr(sentence)
#expression = expr(open("models/"+filename,"r").read())
