"""
structures.py -- AST and neccesary structures.
Formalization of Programs in First-Order Logic with Discrete Linear Order.

version: 0.0.2
author: legendlee(legendlee1314@gmail.com)
"""

# Strutures for AST(abstract syntax tree).
"""
Generating Rules(Double Sides):
P <-> E                           unary
P <-> P | P                       binary
P <-> if(B) ^ then(P1) else(P2)   judge
P <-> while(B) ^ do(P)            loop
"""

# Atomic Expression.
class AtomicExpression:
    """ 
        p1 = p3
        p1 = p3 p4(+/)- p5
    """
    def __init__(self, p1, p3, p4=None, p5=None):
        self.atomic = (p1, p3, p4, p5)
        if p4 is None or p5 is None:
            self.op = False
        else:
            self.op = True

    def show(self):
        if self.op is True:
            print "AE: %s = %s %s %s" % self.atomic
        else:
            print "AE: %s = %s" % self.atomic[0:2]

# Atomic Boolean.
class AtomicBoolean:
    """ 
        p1 p2(<,<=,==,>=,>) p3
    """
    def __init__(self, p1, p2, p3):
        self.atomic = (p1, p2, p3)

    def show(self):
        print "AB: %s %s %s" % self.atomic

# Expressions Node.
class ExprNode:
    def __init__(self, form, next_node):
        self.form = form
        self.next_node = next_node 
        self.pre_node = None

    def set_pre_node(self, pre_node):
        self.pre_node = pre_node

    def show(self):
        print "ExprNode:" + self.form
        if self.form == 'unary':
            self.next_node['A'].show()
        elif self.form == 'binary':
            self.next_node['E1'].show()
            self.next_node['E2'].show()

# Program Node.
class ProgNode:
    def __init__(self, form, next_node):
        self.form = form
        self.next_node = next_node
        self.pre_node = None

    def set_pre_node(self, pre_node):
        self.pre_node = pre_node

    def show(self):
        print "ProgNode:" + self.form
        if self.form == 'unary':
            self.next_node['E'].show()
        elif self.form == 'binary':
            self.next_node['P1'].show()
            self.next_node['P2'].show()
        elif self.form == 'judge':
            self.next_node['B'].show()
            self.next_node['P1'].show()
            self.next_node['P2'].show()
        elif self.form == 'loop':
            self.next_node['B'].show()
            self.next_node['P'].show()

# Strutures for Intermediate Layer.
class MidNode:
    def __init__(self):
        self.next_node = None

    def set_next_node(self, node):
        self.next_node = node

class MidExprList(MidNode):
    def __init__(self):
        MidNode.__init__(self)
        self.exprs = []

    def add_expr(self, expr):
        self.exprs.append(expr)

    def show(self):
        print "MidExprList"

class MidJudgeNode(MidNode):
    def __init__(self):
        MidNode.__init__(self)
        self.condition = None
        self.first_child = None
        self.second_child = None

    def add_condition(self, condition):
        self.condition = condition

    def set_childs(self, child1, child2):
        self.first_child = child1
        self.second_child = child2

    def show(self):
        print "MidJudgeNode"

class MidLoopNode(MidNode):
    def __init__(self):
        MidNode.__init__(self)
        self.condition = None
        self.child = None

    def add_condition(self, condition):
        self.condition = condition

    def set_child(self, child):
        self.child = child

    def show(self):
        print "MidLoopNode"

# Axiom in First-Order Logic.
class Axiom:
    def __init__(self, variable, expr, condition=None):
        self.variable = variable
        self.expr = expr
        self.condition = condition

    def set_condition(self, condition):
        self.condition = condition

    def phi_n(self, variables, natural):
        self.variable = self.variable + "(%s+1)" % natural
        for key in variables:
            self.expr = self.expr.replace(key, "%s(%s)" % (key, natural))

    def show(self):
        if self.condition is not None:
            print "%s -> %s = %s" % (self.condition, self.variable, self.expr)
        else:
            print "%s = %s" % (self.variable, self.expr)

class AxiomUnarySet:
    def __init__(self, variables, expr):
        self.axiom_set = []
        for key in variables:
            if key == expr.atomic[0]:
                if expr.op:
                    self.axiom_set.append(Axiom(key, "%s %s %s" % (expr.atomic[1:4])))
                else:
                    self.axiom_set.append(Axiom(key, expr.atomic[1]))
            else:
                self.axiom_set.append(Axiom(key, key))
        self.condition = None

    def set_condition(self, condition, flag):
        if flag:
            self.condition = "%s %s %s" % condition
        else:
            self.condition = "not (%s %s %s)" % condition
        for i in xrange(0, len(self.axiom_set)):
            self.axiom_set[i].set_condition(self.condition)

    def phi_n(self, variables, natural):
        for i in xrange(0, len(self.axiom_set)):
            self.axiom_set[i].phi_n(variables, natural)

    def to_loop(self, variables):
        self.phi_n(variables, 'n')
        for key in variables:
            self.axiom_set.append(Axiom("%s(0)" % key, key, self.condition))
            self.axiom_set.append(Axiom(key, "%s(N)" % key, self.condition))

    def show(self):
        print "axioms:"
        for a in self.axiom_set:
            a.show()

# Smallest expression.
class Smallest:
    def __init__(self, condition):
        self.e = 'N'
        self.n = 'n'
        self.condition = "%s %s %s" % condition

    def show(self):
        print "Smallest(%s, %s, not %s)" % (self.e, self.n, self.condition)

def testAST():
    print "********Test AST********"
    aenode1 = AtomicExprNode('x', 'y', '+', 'z')
    aenode1.show()
    aenode2 = AtomicExprNode('x', '4')
    aenode2.show()
    abnode = AtomicBoolNode('x', '==', 'y')
    abnode.show()
    pnode1 = ProgNode('unary', {'A': aenode1})
    pnode1.show()
    pnode2 = ProgNode('binary', {'P1': pnode1, 'P2': pnode1})
    pnode2.show()
    pnode3 = ProgNode('judge', {'B': abnode, 'P1': pnode1, 'P2': pnode2})
    pnode3.show()
    pnode4 = ProgNode('loop', {'B': abnode, 'P': pnode3})
    pnode4.show()
    print "********Test AST********"

if __name__ == '__main__':
    testAST()
