#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Created on Fri Mar 19 12:08:25 2021

@author: clara
"""
import modular_operations 

constFactor = 0



# Checks if a linear expression is constant (if after simplification it only constains the constant factor)
def isConstant (lin_exp, p) :
    simplifyLin(lin_exp, p)    
    for x in lin_exp :
        if x != constFactor: return False
    return True


# Given two linear expression l and r, it computes l + r mod p 
def addLin(l, r, p) :
    "return r + l"
    lr = r

    for (x,e) in l.items() :
        if x in lr :
            lr[x] = modular_operations.addP(e,lr[x], p)
        else:
            lr[x] = e % p
    return lr

# Given a linear expression l and value e, it computes e * l mod p 
def multiplyLin(l, e, p) :
    "return e * l"
    lr = {}

    for (x,v) in l.items() :
        lr[x] = modular_operations.multiplyP(e, v, p)
    return lr


# Given two linear expression l and r, it computes r-l mod p 
def addLinInv(l, r, p) :
    "return r-l"
    lr = r
    il = dict(map(lambda x: (x[0],modular_operations.negateP(x[1], p)),l.items()))
    for (x,e) in il.items() :
        if x in lr :
            lr[x] = modular_operations.addP(e,lr[x], p)
        else:
            lr[x] = e % p
    return lr


# Removes the labels with coefficient 0 of a linear expression l
def simplifyLin (l, p) :
    "assume normalized"
    laux={}
    if l != []:
        for (x,e) in l.items() :
            if e % p != 0:
                laux[x] = e % p
    return laux

# Applies the mapping map_labels (from labels to labels) to the linear expression l
def substituteSimplification(l, map_substitution, p):
    laux = {}
    if l != []:
        for (x, e) in l.items():
            # If the label is not the constant factor check its new value
            if x in map_substitution.keys():
                new_expr = multiplyLin(map_substitution[x], e, p)
            else:
                new_expr = dict({x : e})
            laux = addLin(laux, new_expr, p)
    return laux, laux != l
    
# Applies the mapping map_substitution (from labels to linear expressions) to the linear expression l
def substituteLabels(l, map_substitution, p):
    laux = {}
    if l != []:
        for (x, e) in l.items():
            # If the label is not the constant factor check its new value
            if x != 0:
                new_label = map_substitution[x]                    
            else:
                new_label = 0
            # add its value to the new linear expression (if it does not appear add the label, if it appears add the coefficient)
            if new_label in laux:
                laux[new_label] = modular_operations.addP(e, laux[new_label], p)
            else:
                laux[new_label] = e
    return laux

def get_linear_coefficents_AB(linA, linB, p):
    linear_coefficients_AB = {}
    if 0 in linA.keys():
        linear_coefficients_AB = multiplyLin(linB, linA[0], p)
        linA.pop(0)
    if 0 in linB.keys():
        linear_coefficients_AB = addLin(linear_coefficients_AB, multiplyLin(linA, linB[0], p), p)
        linB.pop(0)
    return list(linA.items()), list(linB.items()), linear_coefficients_AB

def sort_linear_expressions(l1, l2):
    labels_l1 = list(map(lambda x: x[0], l1))
    labels_l2 = list(map(lambda x: x[0], l2))


    if labels_l1 < labels_l2:
        return l1, l2
    elif labels_l1 > labels_l2:
        return l2, l1
    else:
        # VER QUE HACER EN ESTE CASO
        return l1, l2

def get_hash_linear_expr(l):
    "assume normalized"
     
    hash_expr = ""
    for (x, e) in l.items():
        hash_expr = hash_expr + str(x) + '*' + str(e) + '.'
    return hash_expr


def get_sum_order(l, signal_to_order):
    sum_order = 0
    for x in l:
        sum_order += signal_to_order[x]
    return sum_order

def get_sum_order(l, signal_to_order):
    sum_order = 0
    for x in l:
        sum_order += signal_to_order[x]
    return sum_order
    
def update_order(l, value, signal_to_order, order_to_signal):
    changed = False
    for x in l:
        order_signal = signal_to_order[x]
        if value - order_signal + 1 < order_signal:
            order_to_signal[order_signal].remove(x)
            if value - order_signal + 1 in order_to_signal:
                order_to_signal[value - order_signal + 1].add(x)
            else:
                 order_to_signal[value - order_signal + 1] = {x}
            signal_to_order[x] = value - order_signal + 1
            changed = True
    return changed
            

def translation_expression(A, translation, p):
    h = {}
    translation[0] = 1
    for (a,b) in list(A.items()) :
        h[translation[a]] = b
    return h
    
class Constraint :

    def __init__(self, p):
        self.A = {}
        self.B = {}
        self.C = {}
        self.p = p
    
    def __init__(self, A, B, C, p):
        self.A = A
        self.B = B
        self.C = C
        self.p = p
        
        
    def print_constraint(self, out):
        print("Linear expression A:", self.A, file = out)
        print("Linear expression B:", self.B, file = out)
        print("Linear expression C:", self.C, file = out)
        
    def print_constraint_terminal(self):
        print("Linear expression A:", self.A)
        print("Linear expression B:", self.B)
        print("Linear expression C:", self.C)
     

        
    def print_constraint_translation(self, translation):
        print("--- Linear expression A:", translation_expression(self.A, translation, self.p))
        print("--- Linear expression B:", translation_expression(self.B, translation, self.p))
        print("--- Linear expression C:", translation_expression(self.C, translation, self.p))

        
    # Normalizes a constraint: makes it linear if it is possible. If not it reverses A and B if A < B
    # If it is linear it normalizes the coefficients making the factor of the first signal 1
    # If it is not linear it normalizes the coefficients

    def normalize(self):
        auxA = sorted(list(simplifyLin(self.A, self.p).items()))
        auxB = sorted(list(simplifyLin(self.B, self.p).items()))
        auxC = sorted(list(simplifyLin(self.C, self.p).items()))
        if auxA == [] or auxB == []:
            self.A = {}
            self.B = {}
            if len(auxC) > 0:
                self.C = dict(map(lambda x: (x[0],modular_operations.divideP(x[1], auxC[0][1], self.p)),auxC))
            else:
                self.C = {}
        elif isConstant(dict(auxA), self.p):
            n = auxA[0][1] #can have only one element
            auxB = list(map(lambda x: (x[0], modular_operations.multiplyP(n, x[1], self.p)), auxB))
            self.A = {}
            self.B = {}
            auxC = sorted(simplifyLin(addLinInv(dict(auxB),dict(auxC), self.p), self.p).items())
            if len(auxC) > 0: 
                self.C = dict(map(lambda x: (x[0],modular_operations.divideP(x[1], auxC[0][1], self.p)),auxC))
            else:
                self.C = {}
            
        elif isConstant(dict(auxB), self.p):
            n = auxB[0][1] #can have only one element
            auxA = list(map(lambda x: (x[0], modular_operations.multiplyP(n,x[1], self.p)),auxA))
            self.A = {}
            self.B = {}
            auxC = sorted(simplifyLin(addLinInv(dict(auxA),dict(auxC), self.p), self.p).items())
            if len(auxC) > 0:
                self.C = dict(map(lambda x: (x[0],modular_operations.divideP(x[1], auxC[0][1], self.p)),auxC))
            else:
                self.C = {}
            
        else:
            auxA, auxB, add_C = get_linear_coefficents_AB(dict(auxA), dict(auxB), self.p)
            auxC = sorted(simplifyLin(addLinInv(dict(add_C),dict(auxC), self.p), self.p).items())
            
            auxA, auxB = sort_linear_expressions(auxA, auxB)
            self.A = dict(auxA)
           
            # We normalize dividing A and C by the first factor of A 
            self.A = dict(map(lambda x: (x[0],modular_operations.divideP(x[1], auxA[0][1], self.p)),auxA))
            auxC_div = list(map(lambda x: (x[0],modular_operations.divideP(x[1], auxA[0][1], self.p)),auxC))
            
            # We normalize dividing A and C by the first factor of B
            self.B = dict(map(lambda x: (x[0],modular_operations.divideP(x[1], auxB[0][1], self.p)),auxB))
            self.C = dict(map(lambda x: (x[0],modular_operations.divideP(x[1], auxB[0][1], self.p)),auxC_div))
            
            
            
                    
            
            
        
    def substitute_simplification(self, map_labels):
        self.A = substituteSimplification(self.A, map_labels, self.p)[0]
        self.B = substituteSimplification(self.B, map_labels, self.p)[0]
        self.C = substituteSimplification(self.C, map_labels, self.p)[0]
    
    def substituteLabels(self, map_labels):
        self.A = substituteLabels(self.A, map_labels, self.p)
        self.B = substituteLabels(self.B, map_labels, self.p)
        self.C = substituteLabels(self.C, map_labels, self.p)
      
    
    def isEmpty(self):
        "assume normalized"
        return self.A == {} and self.B == {} and (self.C == {} or self.C == {0:0})
    
    def isLinear(self):
        "assume normalized"
        return self.A == {} and self.B == {}
    
    def isEqual(self, c):
        "assume normalized"
        return self.A == c.A and self.B == c.B and self.C == c.C
    
    
    def get_hash(self):
        "assume normalized"
        hash_expr = ""
        for (x, e) in self.A.items():
            hash_expr = hash_expr + str(x) + '*' + str(e) + '.'
        hash_expr = hash_expr + '||'
        for (x, e) in self.B.items():
            hash_expr = hash_expr + str(x) + '*' + str(e) + '.'
            hash_expr = hash_expr + '||'
        for (x, e) in self.C.items():
            hash_expr = hash_expr + str(x) + '*' + str(e) + '.'
        hash_expr = hash_expr + '||'
        return hash_expr
    
    def get_sum_order(self, signal_to_order):
        sum_order = get_sum_order(self.A, signal_to_order)
        sum_order += get_sum_order(self.B, signal_to_order)
        sum_order += get_sum_order(self.C, signal_to_order)
        return sum_order
    

    def update_order(self, signal_to_order, order_to_signal):
        sum_order = self.get_sum_order(signal_to_order)
        changed = update_order(self.A, sum_order, signal_to_order, order_to_signal)     
        changed |= update_order(self.B, sum_order, signal_to_order, order_to_signal)  
        changed |=  update_order(self.C, sum_order, signal_to_order, order_to_signal)  
        return changed
    
    def get_signals(self):
        alldict = [self.A, self.B, self.C]
        return set().union(*alldict)
                         
                    