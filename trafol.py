"""
trafol.py -- added tokenizer and parser.
Formalization of Programs in First-Order Logic with Discrete Linear Order.

version: 0.0.2
author: legendlee(legendlee1314@gmail.com)
"""

import ply.lex as lex

# Tokenizer

"""
Tokenizing Process:
- Input String: 'if x > 1 then x = 0'
- Tokenizers:
  -- IF V(x) MORE N(1) THEN V(x) ASSIGN N(0)
  -- V for VARIABLE, N for NUMBER
"""

# List of reserved words.
reserved = {
    'if' : 'IF',
    'then' : 'THEN',
    'else' : 'ELSE',
    'while' : 'WHILE',
    'do' : 'DO',
}

# List of token names.
tokens = [
    'ASSIGN',
    'PLUS',
    'MINUS',
    'LEQ',
    'LESS',
    'MEQ',
    'MORE',
    'EQUALS',
    'NUMBER',
    'VARIABLE',
    'LBRACKET',
    'RBRACKET',
] + list(reserved.values())

# A string containing ignored characters.
t_ignore  = ' \t\n'

# Regular expression rules for simple tokens.
t_ASSIGN     = r'\='
t_PLUS       = r'\+'
t_MINUS      = r'\-'
t_LEQ        = r'<\='
t_LESS       = r'<'
t_MEQ        = r'>\='
t_MORE       = r'>'
t_EQUALS     = r'\=\='
t_LBRACKET   = r'{'
t_RBRACKET   = r'}'

# A regular expression rules for actions.
def t_NUMBER(t):
    r'\d+'
    return t

def t_VARIABLE(t):
    r'[a-zA-z][a-zA-Z0-9]*'
    t.type = reserved.get(t.value, 'VARIABLE')
    return t

# Error handling rule.
def t_error(t):
    print "Illegal character '%s'" % t.value[0]
    t.lexer.skip(1)

# Build the lexer.
lexer = lex.lex()

# Parser

import ply.yacc as yacc

from structures import AtomicExpression
from structures import AtomicBoolean
from structures import ExprNode
from structures import ProgNode

# All variables occuring whole program.
variables = {}

# AST extra map(string, node) of node.
anodes, bnodes, enodes, pnodes = {}, {}, {}, {}

"""
Grammar rules:

S'   : P
P    : E
     | P P
     | if B then { P } else { P }
     | while B do { P }
E    : A
     | E E
A    : R = R
     | R = R + R
     | R = R - R
B    : R <= R
     | R < R
     | R == R
     | R > R
     | R >= R
R    : V
     | N
"""

def p_pro_expr(p):
    'pro : expr'
    p[0] = p[1]
    pnodes[p[0]] = ProgNode('unary', {'E': enodes[p[1]]})
    enodes[p[1]].set_pre_node(pnodes[p[0]])

def p_pro_2pro(p):
    'pro : pro pro'
    p[0] = p[1] + p[2]
    pnodes[p[0]] = ProgNode('binary', {'P1': pnodes[p[1]], 'P2': pnodes[p[2]]})
    pnodes[p[1]].set_pre_node(pnodes[p[0]])
    pnodes[p[2]].set_pre_node(pnodes[p[0]])

def p_pro_judge(p):
    'pro : IF bool THEN LBRACKET pro RBRACKET ELSE LBRACKET pro RBRACKET'
    p[0] = 'if(' + p[2] + ')then{' + p[5] + '}else{' + p[9] + '}'
    next_node = {'B': bnodes[p[2]], 'P1': pnodes[p[5]], 'P2': pnodes[p[9]]}
    pnodes[p[0]] = ProgNode('judge', next_node)
    pnodes[p[5]].set_pre_node(pnodes[p[0]])
    pnodes[p[9]].set_pre_node(pnodes[p[0]])

def p_pro_loop(p):
    'pro : WHILE bool DO LBRACKET pro RBRACKET'
    p[0] = 'while(' + p[2] + '){' + p[5] + '}'
    pnodes[p[0]] = ProgNode('loop', {'B': bnodes[p[2]], 'P': pnodes[p[5]]})
    pnodes[p[5]].set_pre_node(pnodes[p[0]])

def p_expr_axi(p):
    'expr : axi'
    p[0] = p[1] + ';'
    enodes[p[0]] = ExprNode('unary', {'A': anodes[p[1]]})

def p_expr_2expr(p):
    'expr : expr expr'
    p[0] = p[1] + p[2]
    enodes[p[0]] = ExprNode('binary', {'E1': enodes[p[1]], 'E2': enodes[p[2]]})
     
def p_axi_assign1(p):
    'axi : rep ASSIGN rep'
    p[0] = p[1] + '=' + p[3]
    anodes[p[0]] = AtomicExpression(p[1], p[3], None, None)

def p_axi_assign2(p):
    '''axi : rep ASSIGN rep PLUS rep
           | rep ASSIGN rep MINUS rep'''
    if p[4] == '+':
        p[0] = p[1] + '=' + p[3] + '+' + p[5]
    elif p[4] == '-':
        p[0] = p[1] + '=' + p[3] + '-' + p[5]
    anodes[p[0]] = AtomicExpression(p[1], p[3], p[4], p[5])

def p_bool(p):
    '''bool : rep LEQ rep
            | rep LESS rep
            | rep EQUALS rep
            | rep MORE rep
            | rep MEQ rep'''
    if p[2] == '<=':
        p[0] = p[1] + '<=' + p[3]
    elif p[2] == '<':
        p[0] = p[1] + '<' + p[3]
    elif p[2] == '==':
        p[0] = p[1] + '==' + p[3]
    elif p[2] == '>':
        p[0] = p[1] + '>' + p[3]
    elif p[2] == '>=':
        p[0] = p[1] + '>=' + p[3]
    bnodes[p[0]] = AtomicBoolean(p[1], p[2], p[3])

def p_rep_v(p):
    'rep : VARIABLE'
    p[0] = p[1]
    # Note: store variables map.
    variables[p[1]] = p[1]

def p_rep_n(p):
    'rep : NUMBER'
    p[0] = p[1]

# Error rule for syntax errors.
def p_error(p):
    print "Syntax error in input!"

# Build the parser.
parser = yacc.yacc()

# Translation Process

from structures import MidExprList
from structures import MidJudgeNode
from structures import MidLoopNode
from structures import AxiomUnarySet
from structures import Smallest

# Scan atomic expressions.
def scan_for_exprs(node, mid_exprs_list):
    if node.form == 'unary':
        mid_exprs_list.add_expr(node.next_node['A'])
    else:
        scan_for_exprs(node.next_node['E1'], mid_exprs_list)
        scan_for_exprs(node.next_node['E2'], mid_exprs_list)

# Scan all nodes of AST and build the middle layer.
def scan_nodes(node):
    if node.form == 'unary':
        mid_node = MidExprList()
        scan_for_exprs(node.next_node['E'], mid_node)
        return mid_node
    elif node.form == 'judge':
        mid_node = MidJudgeNode()
        mid_node.add_condition(node.next_node['B'].atomic)
        mid_node.set_childs(scan_nodes(node.next_node['P1']), scan_nodes(node.next_node['P2']))
        return mid_node
    elif node.form == 'loop':
        mid_node = MidLoopNode()
        mid_node.add_condition(node.next_node['B'].atomic)
        mid_node.set_child(scan_nodes(node.next_node['P']))
        return mid_node
    elif node.form == 'binary':
        mid_node = scan_nodes(node.next_node['P1'])
        mid_node.set_next_node(scan_nodes(node.next_node['P2']))
        return mid_node

# Show all mid structures.
def show_mid(mid):
    if mid is not None:
        mid.show()
    if isinstance(mid, MidExprList):
        print "->"
        show_mid(mid.next_node)
    elif isinstance(mid, MidJudgeNode):
        print "1>"
        show_mid(mid.first_child)
        print "2>"
        show_mid(mid.second_child)
        print "->"
        show_mid(mid.next_node)
    elif isinstance(mid, MidLoopNode):
        print "|>"
        show_mid(mid.child)
        print "->"
        show_mid(mid.next_node)

# Parse all mid expression list.
def parse_mid_expr_list(mid_exprs_list):
    axiom_set = []
    for expr in mid_exprs_list:
        axiom_set.append(AxiomUnarySet(variables, expr))
    return axiom_set

# Parse mid judge node.
def parse_mid_judge(axiom_set, condition, flag):
    for i in xrange(0, len(axiom_set)):
        if isinstance(axiom_set[i], Smallest):
            continue
        axiom_set[i].set_condition(condition, flag)

# Parse mid loop node.
def parse_mid_loop(axiom_set):
    for i in xrange(0, len(axiom_set)):
        if isinstance(axiom_set[i], Smallest):
            continue
        axiom_set[i].to_loop(variables)

# Parse mid nodes in middle layer.
def transalte_mid(mid):
    if mid is None:
        return []
    if isinstance(mid, MidExprList):
        axiom_set = parse_mid_expr_list(mid.exprs)
        return axiom_set + transalte_mid(mid.next_node)
    elif isinstance(mid, MidJudgeNode):
        axiom_set_1 = transalte_mid(mid.first_child)
        parse_mid_judge(axiom_set_1, mid.condition, True)
        axiom_set_2 = transalte_mid(mid.second_child)
        parse_mid_judge(axiom_set_2, mid.condition, False)
        return axiom_set_1 + axiom_set_2 + transalte_mid(mid.next_node)
    elif isinstance(mid, MidLoopNode):
        axiom_set = transalte_mid(mid.child)
        parse_mid_loop(axiom_set)
        axiom_set.append(Smallest(mid.condition))
        return axiom_set + transalte_mid(mid.next_node)

# Translation with scanning the AST.
def translate(root):
    mid_start = scan_nodes(root)
    axiom_set = transalte_mid(mid_start)
    for a in axiom_set:
        a.show()

# Test the lexer.
def test_lexer(lexer, num, data):
    lexer.input(data)
    print "-------------------------------"
    print "Test%d: %s" % (num, data)
    while True:
        tok = lexer.token()
        if not tok: break
        print tok

def test_lex(lexer):
    print "********Test Lexer********"
    test_lexer(lexer=lexer, num=1, data="x = x + y y = x + 4")
    test_lexer(lexer=lexer, num=2, data="z <= y x > z")
    test_lexer(lexer=lexer, num=3, data="if x == y then { x = y } else { y = x }")
    test_lexer(lexer=lexer, num=4, data="while x >= 100 do { x = x - 1 }")
    print "********Test Lexer********"

def test_yacc(parser):
    print "********Test Parser********"
    test_parser(parser=parser, num=1, data="x = x + 4")
    test_parser(parser=parser, num=2, data="x = x + y y = x + 4 z = 2 y = 3")
    test_parser(parser=parser, num=3, data="if x == y then { x = y } else { y = x z = 0}")
    test_parser(parser=parser, num=4, data="while x >= 100 do { x = x - 1 }")
    test_parser(parser=parser, num=5, data="x = 0 y = 0 while x < 4 do { if x == 2 then { y = 1 x = x + 1 } else { y = 0 } y = y + 1} x = y")
    print "********Test Parser********"

# Test the parser.
def test_parser(parser, num, data):
    print "-------------------------------"
    print "Test%d: %s" % (num, data)
    result = parser.parse(data)
    print "Result: %s" % result
    pnodes[result].show()

def test(data):
    result = parser.parse(data)
    translate(pnodes[result])

if __name__ == '__main__':
#test_lex(lexer)
#test_yacc(parser)
#test("x = 1 y = x + 1")
#test("y = y x = 1 x = x + 1")
#test("if x == y then { x = 1 } else { y = x + 1 }")
#test("x = 1 y = 2 while x < 4 do { x = x + 1 }")
#test("while x < 5 do { if 5 > 1 then { x = x + 1 } else { x = x - 1}}")
    test("while x < 4 do { while x > 1 do { x = x + 1 } }")
#test("x = 0 y = 0 while x < 4 do { if x == 2 then { y = 1 x = x + 1 } else { y = 0 } y = y + 1} x = y")
#test("i = 0 j = 9 while i < 10 do { i = i + 1 j = j - 1}")
