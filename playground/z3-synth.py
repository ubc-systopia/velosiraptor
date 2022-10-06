
from z3 import *


WORD_SIZE = 64

class StateFieldPte() :
    def __init__(self):

        self.val = BitVec('state-field-pte', WORD_SIZE)

    def with_val(val) :
        iface = StateFieldPte()
        iface.val = val
        return iface

    def extract_present(self) :
        return (self.val >> 0) & BitVecVal(1, WORD_SIZE)

    def insert_present(self, val) :
        self.val = (self.val & ~(BitVecVal(1, WORD_SIZE) << 0)) | ((BitVecVal(1, WORD_SIZE) & val) << 0)

    def extract_writable(self) :
        return (self.val >> 1) & BitVecVal(1, WORD_SIZE)

    def insert_writable(self, val) :
        self.val = (self.val & ~(BitVecVal(1, WORD_SIZE) << 1)) | ((BitVecVal(1, WORD_SIZE) & val) << 1)


class State():
    def __init__(self) :
        self.pte = StateFieldPte()

    def with_val(val) :
        st = State()
        st.pte = StateFieldPte.with_val(val)
        return st

    def get_pte(self):
        return self.pte

    def set_pte(self, pte: StateFieldPte) :
        self.pte = pte


class IFaceFieldPte() :
    def __init__(self):
        self.val = BitVec('iface-field-pte', WORD_SIZE)

    def with_val(val) :
        iface = IFaceFieldPte()
        iface.val = val
        return iface

    def extract_present(self) :
        return (self.val >> 0) & BitVecVal(1, WORD_SIZE)

    def insert_present(self, val) :
        # self.val ==  (self.val & ~BitVecVal(1, WORD_SIZE) ) | (BitVecVal(1, WORD_SIZE) &  BitVecVal(val, WORD_SIZE))
        self.val = (self.val & ~BitVecVal(1, WORD_SIZE)) |  (BitVecVal(1, WORD_SIZE) & val)

    def extract_writable(self) :
        return (self.val >> 1) & BitVecVal(1, WORD_SIZE)

    def insert_writable(self, val) :
        self.val = (self.val & ~(BitVecVal(1, WORD_SIZE) << 1)) | ((BitVecVal(1, WORD_SIZE) & val) << 1)


class IFace():
    def __init__(self):
        self.pte = IFaceFieldPte()

    def with_val(val) :
        st = IFace()
        st.pte = IFaceFieldPte.with_val(val)
        return st

    def get_pte(self):
        return self.pte

    def set_pte(self, pte: IFaceFieldPte):
        self.pte = pte


class Model():
    def __init__(self, iface, state):
        self.state = State.with_val(state)
        self.iface = IFace.with_val(iface)

    def iface_pte_write(self) :
        self.state.set_pte(StateFieldPte.with_val(self.iface.get_pte().val))

    def iface_pte_read(self) :
        self.iface.set_pte(IFaceFieldPte.with_val(self.state.get_pte().val))




class Op() :
    def interp(self, model):
        pass
    def __str__(self) -> str:
        return "unknown op"
    def pretty_print(self, model) -> str:
        return "unknown op"

class IFacePtePresentInsert(Op):
    def __init__(self, val):
        self.val = val
    def interp(self, model):
        model.iface.get_pte().insert_present(self.val)
    def __str__(self) -> str:
        return f"iface_pte_present_insert({self.val})"
    def pretty_print(self, model) -> str:
        v = model[self.val]
        if v is None:
            v = "??"
        return f"iface_pte_present_insert({v})"

class IFacePteWritableInsert(Op):
    def __init__(self, val):
        self.val = val
    def interp(self, model):
        model.iface.get_pte().insert_writable(self.val)
    def __str__(self) -> str:
        return f"iface_pte_writable_insert({self.val})"
    def pretty_print(self, model) -> str:
        v = model[self.val]
        if v is None:
            v = "??"
        return f"iface_pte_writable_insert({v})"

class IFacePteWriteAction(Op):
    def interp(self, model):
        model.iface_pte_write()
    def __str__(self) -> str:
        return "iface_pte_write()"
    def pretty_print(self, model) -> str:
        return str(self)

class IFacePteReadAction(Op):
    def interp(self, model):
        model.iface_pte_read()
    def __str__(self) -> str:
        return "iface_pte_read()"
    def pretty_print(self, model) -> str:
        return str(self)



ops = [
    IFacePtePresentInsert(0),
    IFacePteWriteAction()
]


counter = 0
def new_bitvec():
    global counter
    bv = BitVec(f'arg{counter}', WORD_SIZE)
    counter += 1
    return bv


possible_ops = [
    IFacePtePresentInsert(new_bitvec()),
    IFacePteWriteAction(),
    IFacePteReadAction()
]

def get_ops() :
    return [
    IFacePtePresentInsert(new_bitvec()),
    IFacePteWritableInsert(new_bitvec()),
    IFacePteWriteAction(),
    IFacePteReadAction()
    ]

def interp(st, ops):
    for o in ops:
        o.interp(st)

def check_sat(ops) :
    s = Solver()

    iface = Const('iface', BitVecSort(WORD_SIZE))
    state = Const('state', BitVecSort(WORD_SIZE))
    st = Model(iface, state)
    interp(st, ops)
    s.add(ForAll([iface, state], Not(st.state.get_pte().extract_present() == 1)))
    s.add(ForAll([iface, state], Not(st.state.get_pte().extract_writable() == 1)))

    if s.check() == z3.sat :
        print(f"SOLVED:     ", end=' ')
        m = s.model()
        print([ o.pretty_print(m) for o in ops])
        return True
    else :
        print(f"NOT SOLVED: ", end=' ')
        print([ str(o) for o in ops])
        return False

from itertools import product

def eval_ops():
    ops = [[o] for o in get_ops()]
    for n in range(1, 5):
        print(f"\n\nLENGTH {n}")
        for o in ops :
            if check_sat(o):
                return True
        new_ops = get_ops()

        expanded = [new_ops, ops]
        ops = [ [e[0]] + e[1] for e in product(*expanded) ]

eval_ops()


# for op in possible_ops:
#     for op2 in possible_ops:
#         s = Solver()

#         ops = [op, op2]

#         iface = Const('iface', BitVecSort(WORD_SIZE))
#         state = Const('state', BitVecSort(WORD_SIZE))
#         st = Model(iface, state)
#         interp(st, ops)
#         s.add(ForAll([iface, state], Not(st.state.get_pte().extract_present() == 1)))


#         if s.check() == z3.sat :
#             print(f"SOLVED:     ", end=' ')
#             m = s.model()
#             print([ o.pretty_print(m) for o in ops])
#         else :
#             print(f"NOT SOLVED: ", end=' ')
#             print([ str(o) for o in ops])

