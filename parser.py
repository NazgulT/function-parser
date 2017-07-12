from logic import *
from utils import *
import random

def parseExpr(expression, negation):
    """ A function to a clause with functions to return relations
    e.g.: P(x) = Beth becomes P(x,Beth)"""
    """
    if(is_definite_clause(expression)):
        for clause in parse_definite_clause(expression):
            relations.append(add_arity(get_args_as_list(clause)))
    """
    return add_arity(get_args_as_list(expression), negation)

def get_args_as_list(expression):
    return list(expression.args)


def add_arity(clause, dom, negation):
    #prop = clause[0]
    prop = list(clause)[0]
    #variable = str(list(variables(prop))[0])
    prop_args = list(prop.args)
    if len(clause) == 1:
        constant = dom
    else:
        constant = clause[1]
    print(constant)
    #new_expr = expr(negation+prop.op+'('+variable+','+str(constant)+')')
    s = ''.join([negation,prop.op,'('])
    p=''
    for a in prop_args:
        p = ''.join([p,str(a),','])
    q = ''.join([str(constant),')'])
    new_expr = expr(''.join([s,p,q]))
    return new_expr

def retrieve_domain(expression):
    domain = []
    for clause in parse_definite_clause(expression):
        domain.append(list(clause.args)[1])
    return domain

def eliminate_functions(expression):
    props = []
    operators=[]
    #print(expression)
    #print(expression.op)
    operators.append(expression.op)
    for subexpr in expression.args:
        props.append(parseFunc(subexpr))
    #print(len(props))
    #print(props)
    #print(operators)
    string=""
    while len(operators) != 0:
        string = str(operators.pop()) + str(props.pop()) + string
    string = str(props.pop()) + string
    return expr(string)

def parseFunc(subexpression):
    negation=""
    if subexpression.op == 'eq' or subexpression.op == '!=':
        #print("Parsing functional expression...")
        if subexpression.op == '!=':
            negation="~"
        return parseExpr(subexpression, negation)

#constant_names = [Expr'Adam'), Expr('Beth'),Expr('Carol'),Expr('Bob'), Expr('Alice'), Expr('J'),Expr('K'),Expr('L'),Expr('Naz')]
constant_names = {Expr('Adam'),Expr('Beth'),Expr('Bob'),Expr('Carol')}

def gnd(expression, rank):
    if rank == 0:
        return list(map(lambda x: list(map(lambda d: subst({x: d},expression),domain)),var))
    if rank == 1:
        domain_new = increase_domain(domain)
        return list(map(lambda x: list(map(lambda d: subst({x: d},expression),domain_new )),var))

def increase_domain(domain):
    not_in_domain_set = constant_names - set(domain)
    arbitrary_cons = random.choice(list(not_in_domain_set))
    domain.append(arbitrary_cons)
    return domain

def get_terms(expression):
    for exp in list(expression.args):
        if exp not in domain and exp not in var and is_symbol(exp.op):
            terms.append(exp)
        else:
            get_terms(exp)

def xor_t_D(expression):
    for pair in expression:
        print(pair)
        if not isinstance(pair,Expr):
            xor_t_D(pair)
        else:
            for d in domain:
                add_arity(pair,d,"") #Change the type of first argument in add_arity and test using difference cases





#-----------------------------------Main----------------------------------#
expression = expr("(F(x) != Adam) ==> (M(x) != Beth)")
expression_1 = expr("P(x,y) & A(x,z)")
expression_2 = expr("F(x) & A(x) | M(x) & B & C ==> A ")
domain = constant_symbols(expression)
gnd_exps=[]
terms = []
print(type(domain), type(domain[0]), domain[0])
print("Domain D = {}".format(domain))
var = variables(expression)
print("Variables = {}".format(var))
#expr_wt_impl = move_not_inwards(eliminate_implications(eliminate_functions(expression)))
#gnd_exps = gnd(expr_wt_impl,0)
#gnd_exps = gnd(expr_wt_impl,1)
#while is_symbol(get_terms(expression).op) == False:
#    print("Saw an operator", get_terms(expression).op)
#get_terms(expr("F(x) & A(x) | M(x) & B & C ==> A "))
#get_terms(expression)
get_terms(expression)
gnd_terms = list(map(lambda t: list(map(lambda d: subst({t:d},terms),domain)),var))
print(xor_t_D(gnd_terms))
#print(add_arity([expr('F(x,y)')], expr('Beth'), ""))
