#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Created on Fri May  6 18:00:01 2022

@author: clara
"""

#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Created on Mon Apr 12 11:02:58 2021

@author: clara
"""

#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Created on Mon Mar 22 17:59:00 2021

@author: clara
"""

import read_r1cs
import circuit_representation
import argparse
import json
parser = argparse.ArgumentParser()

parser.add_argument("file1", help=".sym file of the circuit",
                    type=str)
parser.add_argument("file2", help=".r1cs file of the circuit",
                    type=str)
parser.add_argument("out1", help=".json file with the order",
                    type=str)
parser.add_argument("out2", help=".json file with the dependencies",
                    type=str)

args=parser.parse_args()



# Compute the circuit produced by original circom
original_circuit = circuit_representation.Circuit()
read_r1cs.parse_sym(args.file1, original_circuit)
read_r1cs.parse_r1cs(args.file2, original_circuit)
#original_circuit.normalize_constraints()

f_out1 = open(args.out1, 'w', encoding="utf-8")
f_out2 = open(args.out2, 'w', encoding="utf-8")



def initialize_order(circuit):
    signal_to_order = {}
    order_to_signal = {}
    
    aux_known = set()
    aux_unknown = set()
    limit_unknown = circuit.nPubOut + 1
    limit_known = circuit.nPubOut + circuit.nPubIn + circuit.nPrvIn + 1
    aux_known.add(0)
    signal_to_order[0] = 0
    for s in range(1, limit_unknown):
        aux_unknown.add(s)
        signal_to_order[s] = 10000000000
    for s in range(limit_unknown, limit_known):
        aux_known.add(s)
        signal_to_order[s] = 0
    for s in range(limit_known, circuit.nWires):
        aux_unknown.add(s)
        signal_to_order[s] = 10000000000
    order_to_signal[0] = aux_known
    order_to_signal[10000000000] = aux_unknown
    return (signal_to_order, order_to_signal)
    
(signal_to_order, order_to_signal) =  initialize_order(original_circuit)

original_circuit.update_order(signal_to_order, order_to_signal)
print(signal_to_order)
def generate_list_order(order_to_signal):
    orders = list(order_to_signal.keys())
    orders.sort()
    new_order = list()
    for order in orders:
        if order != 0:
            for s in order_to_signal[order]:
                new_order.append(s)
    return new_order

order_signals = generate_list_order(order_to_signal)

for s in order_signals:
    print(s)
    
clusters_cons = original_circuit.get_dependencies(signal_to_order)

for (s, cons) in clusters_cons.items():
    print("Signal ", s, "Constraints: ", cons)
    
json.dump(order_signals, f_out1)
json.dump(clusters_cons, f_out2)