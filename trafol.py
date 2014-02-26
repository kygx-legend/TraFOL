"""
trafol.py--tokenizer and parser.
Formalization of Programs in First-Order Logic with Discrete Linear Order.

version: 0.0.1
author: legendlee(legendlee1314@gmail.com)
"""

import ply.lex as lex
import ply.yacc as yacc

from structures import ABNode
from structures import AENode
from structures import PNode

# Tokenizer

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
"""
Grammar rules:

S'   : P
P    : A
     | P P
     | if B then P else P
     | while B do P
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

# added structures.
abnodes, aenodes, pnodes = {}, {}, {}
variables, output = {}, ''

def p_pro_axi(p):
    'pro : axi'
    p[0] = p[1] + ';'
    pnodes[p[0]] = PNode('unary', {'A': aenodes[p[1]]})

def p_pro_2pro(p):
    'pro : pro pro'
    p[0] = p[1] + p[2]
    pnodes[p[0]] = PNode('binary', {'P1': pnodes[p[1]], 'P2': pnodes[p[2]]})

def p_pro_judge(p):
    'pro : IF bool THEN pro ELSE pro'
    p[0] = 'if(' + p[2] + ')then{' + p[4] + '}else{' + p[6] + '}'
    child = {'B': abnodes[p[2]], 'P1': pnodes[p[4]], 'P2': pnodes[p[6]]}
    pnodes[p[0]] = PNode('judge', child)

def p_pro_loop(p):
    'pro : WHILE bool DO pro'
    p[0] = 'while(' + p[2] + '){' + p[4] + '}'
    pnodes[p[0]] = PNode('loop', {'B': abnodes[p[2]], 'P': pnodes[p[4]]})

def p_axi_assign1(p):
    'axi : rep ASSIGN rep'
    p[0] = p[1] + '=' + p[3]
    aenodes[p[0]] = AENode(p[1], p[3], None, None)

def p_axi_assign2(p):
    '''axi : rep ASSIGN rep PLUS rep
           | rep ASSIGN rep MINUS rep'''
    if p[4] == '+':
        p[0] = p[1] + '=' + p[3] + '+' + p[5]
    elif p[4] == '-':
        p[0] = p[1] + '=' + p[3] + '-' + p[5]
    aenodes[p[0]] = AENode(p[1], p[3], p[4], p[5])

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
    abnodes[p[0]] = ABNode(p[1], p[2], p[3])

def p_rep_v(p):
    'rep : VARIABLE'
    p[0] = p[1]
    variables[p[1]] = p[1]

def p_rep_n(p):
    'rep : NUMBER'
    p[0] = p[1]

# Error rule for syntax errors.
def p_error(p):
    print "Syntax error in input!"

# Build the parser.
parser = yacc.yacc()

# Main recursion logic of translation.
def translate(node, v):
    global output
    if isinstance(node, PNode):
        if node.form == 'unary':
            translate(node.child['A'], v)
        elif node.form == 'binary':
            translate(node.child['P1'], v)
            translate(node.child['P2'], v)
        elif node.form == 'judge':
            node.child['B'].show()
            output += '%s %s %s :\n' % node.child['B'].axiom
            translate(node.child['P1'], v)
            output += '^ %s %s %s :\n' % node.child['B'].axiom
            translate(node.child['P2'], v)
        elif node.form == 'loop':
            node.child['B'].show()
            translate(node.child['P'], v)
    elif isinstance(node, AENode):
        data = ''
        for key in v:
            if key == node.axiom[0]:
                if node.op:
                    data += "%s* = %s %s %s;\n" % node.axiom
                else:
                    data += "%s* = %s;\n" % node.axiom
            else:
                data += "%s* = %s;\n" % (key, key)
        output += data

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
    test_lexer(lexer=lexer, num=3, data="if x == y then x = y else y = x")
    test_lexer(lexer=lexer, num=4, data="while x >= 100 do x = x - 1")
    print "********Test Lexer********"

# Test the parser.
def test_parser(parser, num, data):
    print "-------------------------------"
    print "Test%d: %s" % (num, data)
    result = parser.parse(data)
    print "Result: %s" % result
    pnodes[result].show()

def test_yacc(parser):
    print "********Test Parser********"
    test_parser(parser=parser, num=1, data="x = x + 4")
    test_parser(parser=parser, num=2, data="x = y - 4")
    test_parser(parser=parser, num=3, data="x = y")
    test_parser(parser=parser, num=4, data="x = x + y y = x + 4 z = 2 y = 3")
    test_parser(parser=parser, num=5, data="if x == y then x = y else y = x")
    test_parser(parser=parser, num=6, data="while x >= 100 do x = x - 1")
    print "********Test Parser********"

def test(data):
    result = parser.parse(data)
    translate(pnodes[result], variables)

if __name__ == '__main__':
#test_lex(lexer)
#test_yacc(parser)
#test("x = y + 4")
#test("x = 4 y = 2 z = x + y")
#test("if x == y then x = y else y = x")
#test("while x < 4 do x = x + 1")
    test("while x < 4 do if x == 2 then y = 1 x = x + 1 else y = 0 x = x - 1")
    print output
