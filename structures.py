"""
structures.py--AST and needed structures.
Formalization of Programs in First-Order Logic with Discrete Linear Order.

version: 0.0.1
author: legendlee(legendlee1314@gmail.com)
"""

# AST(abstract syntax tree).
"""
P -> A                           unary
P -> P | P                       binary
P -> B(if) ^ P(then) | P(then)   judge
P -> B(while) ^ P(do)            loop
"""

# Axiom Exp Node.
class AENode:
    """ 
        p1 = p3
        p1 = p3 +/- p5
    """
    def __init__(self, p1, p3, p4=None, p5=None):
        if p4 is None:
            self.axiom = (p1, p3)
            self.op = False
        else:
            self.axiom = (p1, p3, p4, p5)
            self.op = True

    def show(self):
        if self.op is True:
            print "AENode: %s = %s %s %s" % self.axiom
        else:
            print "AENode: %s = %s" % self.axiom

# Axiom Bool Node.
class ABNode:
    """ 
        p1 <,<=,==,>=,> p3
    """
    def __init__(self, p1, p2, p3):
        self.axiom = (p1, p2, p3)

    def show(self):
        print "ABNode: %s %s %s" % self.axiom

# Program Node.
class PNode:
    def __init__(self, form, child):
        self.form = form
        self.child = child

    def show(self):
        print "PNode:"
        if self.form == 'unary':
            self.child['A'].show()
        elif self.form == 'binary':
            self.child['P1'].show()
            self.child['P2'].show()
        elif self.form == 'judge':
            self.child['B'].show()
            self.child['P1'].show()
            self.child['P2'].show()
        elif self.form == 'loop':
            self.child['B'].show()
            self.child['P'].show()

def testAST():
    print "********Test AST********"
    aenode1 = AENode('x', 'y', '+', 'z')
    aenode1.show()
    aenode2 = AENode('x', '4')
    aenode2.show()
    abnode = ABNode('x', '==', 'y')
    abnode.show()
    pnode1 = PNode('unary', {'A': aenode1})
    pnode1.show()
    pnode2 = PNode('binary', {'P1': pnode1, 'P2': pnode1})
    pnode2.show()
    pnode3 = PNode('judge', {'B': abnode, 'P1': pnode1, 'P2': pnode2})
    pnode3.show()
    pnode4 = PNode('loop', {'B': abnode, 'P': pnode3})
    pnode4.show()
    print "********Test AST********"

if __name__ == '__main__':
    testAST()
