#!/usr/bin/env python3

# CBMC-GCv5.7 from
# http://forsyte.at/software/cbmc-gc/
# http://forsyte.at/wp-content/uploads/cbmc-gc-v0.9.3_upd1.pdf

CONSTANTS = 'output.constants.txt'
INPUTS = 'output.inputs.txt'
MAPPING = 'output.mapping.txt'
GATES = 'output.gate.txt'

LAZYINPUT = True # only grab bits of input that are used
#LAZYINPUT = False
LAZYOUTPUT = True # skip setting "if false" output bits
#LAZYOUTPUT = False

class Op:
    """
    Parent class for operators
    creates a unique var name for each gate
    defines __str__ for the binary operators (DRY)
    """
    opstr = NotImplemented

    def __init__(self):
        self.inputs = []
        self.outputs = []

    def getvarname(self):
        return "Op" + str(id(self))

    def __str__(self):
        if type(self.inputs[0]) is str:
            left = self.inputs[0]
        else:
            left = self.inputs[0].getvarname()
        if type(self.inputs[1]) is str:
            right = self.inputs[1]
        else:
            right = self.inputs[1].getvarname()
        return "{} = {} {} {}".format(self.getvarname(),
                                        left,
                                        self.opstr,
                                        right)

class Not(Op):
    def __str__(self):
        """ Not must overwrite as default is binary operators """
        if type(self.inputs[0]) is str:
            opnd = self.inputs[0]
        else:
            opnd = self.inputs[0].getvarname()
        return "{} = not {}".format(self.getvarname(), opnd)

class And(Op):
    opstr = "and"
    
class Xor(Op):
    opstr = "^"

class Or(Op):
    opstr = "or"

# saves a big if/elif/.../else later
GATE_MAP = {'NOT': Not, 'AND': And, 'XOR': Xor, 'OR': Or}

def parse_constants(gates):
    """ which gates have an initial ONE flowing in """
    with open(CONSTANTS, 'r') as f:
        lines = f.readlines()
    constgates = []
    if len(lines) > 0:
        line = lines[0].split(' ')[1:]
        for i in range(len(line)):
            gatenum, pin = line[i].split(':')[1:]
            gate = gates[int(gatenum)-1]
            gate.inputs.insert(int(pin), "True")
            if type(gate) is Not or len(gate.inputs) == 2:
                # take gates which only take input from consts
                # these will be the start of the topo sort
                constgates.append(gate)
    return constgates

def parse_inputs(gates):
    """
    set up gates which take function input
    assumes the names that input_mapping has created exist
    """
    with open(INPUTS, 'r') as f:
        lines = f.readlines()
    ingates = []
    print("# NOTE the below is just to unpack input bits from an int")
    print("input = # FIXME")
    for i in range(len(lines)):
        targets = lines[i].split(' ')[1:]
        for gate_info in targets:
            gatenum, pin = gate_info.split(':')[1:]
            gate = gates[int(gatenum)-1]
            if LAZYINPUT:
                print("input{} = bool(input & (1 << {}))".format(i, i))
            gate.inputs.insert(int(pin), "input" + str(i))
            if type(gate) is Not or len(gate.inputs) == 2:
                # take gates which only take input from consts and input vars
                # these will be the start of the topo sort
                ingates.append(gate)
    return ingates

def input_mapping():
    """ split 'input' into 'input0..n' for use by parse_inputs """
    if not LAZYINPUT:
        with open(INPUTS, 'r') as f:
            numbits = len(f.readlines())
        for i in range(numbits):
            print("input{} = bool(input & (1 << {}))".format(i, i))

def output_mapping(outputs):
    """
    aggregate output bits into an int
    gets variable names from parse_mapping
    """
    print("# NOTE the below is just to re-pack output bits into an int")
    print("result = 0")
    for (var,og) in outputs:
        if LAZYOUTPUT and (type(var) is Not and var.inputs[0] == 'True'):
            # if this came directly from a "not True" gate just skip it
            continue
        print("if {}:".format(var.getvarname()))
        print("    result |= 1 << {}".format(og))

def print_gates_topo(ingates):
    seen = set()
    nextgates = list(ingates)
    while nextgates:
        nxt = nextgates.pop(0)
        if nxt in seen:
            raise Exception("Cyclic gate dependency")
        print(str(nxt))
        seen.add(nxt)
        for out in nxt.outputs:
            if all(map(lambda i: i in seen, out.inputs)):
                nextgates.append(out)

def parse_gate():
    with open(GATES, 'r') as f:
        lines = f.readlines()
    gates = []
    for i in range(len(lines)):
        # create a gate for each operator
        op = lines[i].split(' ')[0]
        gate = GATE_MAP.get(op.upper())() # 'NoneType not callable' if OP unsupported
        gates.append(gate)
    constgates = parse_constants(gates)
    input_mapping()
    ingates = parse_inputs(gates)
    outputs = []
    for i in range(len(lines)):
        # wire gates to their inputs
        targets = lines[i].split(' ')[2:]
        for target in targets:
            # for each output of this gate
            target_gate, target_pin = target.split(':')[1:]
            if '-' in target_gate:
                target_gate = target_gate.replace('-', '')
                outputs.insert(int(target_gate)-1,
                               (gates[i], int(target_gate)-1))
            else:
                # add this gate to the output gate's inputs
                gates[int(target_gate)-1].inputs.insert(int(target_pin),
                                                    gates[i])
                # add the output gate to this gate's outputs
                gates[i].outputs.append(gates[int(target_gate)-1])
    print("# NOTE the program starts here")
    print_gates_topo(constgates + ingates)
    print("# NOTE the program ends here")
    output_mapping(outputs)

if __name__ == '__main__':
    parse_gate()
