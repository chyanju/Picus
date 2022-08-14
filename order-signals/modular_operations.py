#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Created on Fri Mar 19 12:18:58 2021

@author: clara
"""


# Computes n + m mod p
def addP(n, m, p):
    return ( n + m ) % p

# Computes n * m mod p
def multiplyP(n, m, p):
    return ( n * m ) % p



# Computes - n mod p
def negateP(n, p):
    return ( p - n ) % p 


def isNegativeP(n, p):
    return n > p // 2



#    
## ONLY WORK IF P IS PRIME
#    
## Computes the inverse of n mod p
def inverseP(n, p): 
    return pow(n, -1, p)
#  
#  
# =============================================================================
# Computes n/m modulo m (if it exists)
def divideP(n, m, p): 
    n = n % p
    inv = inverseP(m, p) 
    if(inv == -1): 
        print("Division not defined") 
    else: 
        return ((inv * n) % p) 
# =============================================================================

     