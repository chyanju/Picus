#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Created on Thu Mar 18 10:21:14 2021

@author: clara
"""
import struct
from circuit_representation import Circuit
from constraint import Constraint
        
    

def parse_header(content, info):
    field_size = struct.unpack('<i', content[0:4])[0]
    prime_number = 0
    init_pos = 4
    for i in range(field_size // 4):
        aux = struct.unpack('<I', content[init_pos:init_pos + 4])[0]
        prime_number = prime_number + aux * 16 ** (8 * i)
        init_pos = init_pos + 4
    
    nWires = struct.unpack('<i', content[4+field_size:8+field_size])[0]
    nPubOut = struct.unpack('<i', content[8+field_size:12+field_size])[0]
    nPubIn = struct.unpack('<i', content[12+field_size:16+field_size])[0]
    nPrvIn = struct.unpack('<i', content[16+field_size:20+field_size])[0]
    nLabels = struct.unpack('<q', content[20+field_size:28+field_size])[0]
    nConstraints = struct.unpack('<i', content[28+field_size:32+field_size])[0]
    info.update_header(field_size, prime_number, nWires, nPubOut, nPubIn, nPrvIn, nLabels, nConstraints)
    return info


def parse_linear_expression(content, info, init_pos):
    n_vals = struct.unpack('<i', content[init_pos: init_pos + 4])[0]
    init_pos += 4
    lin_expr = {}
    for i in range(n_vals):
        label = struct.unpack('<i', content[init_pos: init_pos + 4])[0]
        init_pos += 4
        coef = 0
        for i in range(info.field_size // 4):
            aux = struct.unpack('<I', content[init_pos:init_pos + 4])[0]
            coef = coef + aux * 16 ** (8 * i)
            init_pos = init_pos + 4       
        lin_expr[label] = coef
    return lin_expr, init_pos

def parse_constraint(content, info, init_pos):
    const_a, init_pos = parse_linear_expression(content, info, init_pos)
    const_b, init_pos = parse_linear_expression(content, info, init_pos)
    const_c, init_pos = parse_linear_expression(content, info, init_pos)
    
    info.add_constraint(Constraint(const_a, const_b, const_c, info.prime_number))
    return init_pos

    
def parse_constraints(content, info):
    init_pos = 0
    for i in range(info.nConstraints):
        init_pos = parse_constraint(content, info, init_pos)
        
        

def parse_sections(f, n_sections, circuit):
    
    for i in range(n_sections):
        
        section_type = struct.unpack('<i', f.read(4))[0]
        section_size = struct.unpack('<q',f.read(8))[0]
        section_content = f.read(section_size)
        if section_type == 1:
            header_content = section_content
        elif section_type == 2:
            constraint_section = section_content
        elif section_type == 3:
            map_section = section_content
            
    
    parse_header(header_content, circuit)
    parse_constraints(constraint_section, circuit)



def parse_r1cs(file, circuit):
    with open(file, "rb") as f:
        magic_constant = f.read(4)
        version = struct.unpack('<i',f.read(4))[0]
        n_sections = struct.unpack('<i',f.read(4))[0]
        parse_sections(f, n_sections, circuit)
        


def parse_sym(file, circuit):
    
    with open(file, "r") as read1:
        Lines = read1.readlines()
        circuit.signal2label = {line.split(',')[3].strip():int(line.split(',')[1]) for line in Lines}
        circuit.label2signal = {int(line.split(',')[1]):line.split(',')[3].strip() for line in Lines}
        read1.close()
        
def parse_inverse_sym(file):
    
    with open(file, "r") as read1:
        Lines = read1.readlines()
        label2signal = {int(line.split(',')[1]):line.split(',')[3].strip() for line in Lines}
        read1.close()
    return label2signal
        