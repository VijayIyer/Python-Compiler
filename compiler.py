import ast
import types
from ast import *
from functools import reduce
import sys

import x86_ast

sys.setrecursionlimit(2000)
from utils import *
from x86_ast import *
import os
from typing import List, Tuple, Set, Dict
from graph import UndirectedAdjList, DirectedAdjList, UEdge, topological_sort, transpose
from priority_queue import PriorityQueue, Heap
import itertools
from collections import OrderedDict, deque

Binding = Tuple[Name, expr]
Temporaries = List[Binding]
caller_saved_regs = {Reg('rax'): -1, Reg('rcx'): 3, Reg('rdx'): 2, Reg('rsi'): 1, Reg('rdi'): 0, Reg('r8'): 4,
                     Reg('r9'): 5, Reg('r10'): 6, Reg('r11'): -4}
callee_saved_regs = {Reg('rsp'): -2, Reg('rbp'): -3, Reg('rbx'): 7, Reg('r12'): 8, Reg('r13'): 9, Reg('r14'): 10,
                     Reg('r15'): -3}

Exprs = {}


# region rco helpers
def get_let_exp(temporaries2):
    if len(temporaries2) == 1:
        return temporaries2[0][1]
    i = 0
    let_exp = Let(temporaries2[i][0], temporaries2[i][1], get_let_exp(temporaries2[i + 1:]))
    return let_exp


# endregion

# region assign homes helpers
# region commented out
# def choose_color(restricted_colors, move_related_vertices, interfering_vertices, already_colored_vertices):
#     i = 0  # start with minimum color
#     while i in restricted_colors:
#         i += 1
#     return i
#
# def pick_Reg(reg_set1, reg_set2):
#     if len(reg_set1) != 0:
#         picked_reg = reg_set1.pop()
#     else:
#         picked_reg = reg_set2.pop()
#     return picked_reg
# def get_candidate_variables(pq, vars_map):
#     out = []
#     sat_length = vars_map[pq.heap.maximum().key]
#     while vars_map[pq.heap.maximum().key] == sat_length and not pq.empty():
#         var = pq.pop()
#         out.append(var)
#         # pq.push(var)
#     for var in out:
#         pq.push(var)
#     return out
# endregion
def choose_reg(byte_Reg):
    match byte_Reg:
        case 'al':
            return Reg('rax')
        case 'ah':
            return Reg('rax')
        case 'bl':
            return Reg('rbx')
        case 'bh':
            return Reg('rbx')
        case 'cl':
            return Reg('rcx')
        case 'ch':
            return Reg('rcx')
        case 'dl':
            return Reg('rdx')
        case 'dh':
            return Reg('rdx')


def get_color(var, colored_set, color_map, inf_graph):
    # if len(candidate_vars) == 1:
    #     return candidate_vars[0]
    #
    color = 0
    rest_nodes = set(inf_graph.adjacent(var)).intersection(colored_set)
    adj_colors = [color_map[node].color for node in rest_nodes]
    while color in adj_colors:
        color += 1
    return color


def get_color_with_move_biasing(var, move_graph, colored_set, restricted_colors, inf_graph):
    candidate_vars = (set(move_graph.out[var])).intersection(colored_set)
    allowed_colors = []
    for related_var in candidate_vars:
        allowed_colors.extend(list(restricted_colors[related_var].color))
    allowed_colors = set(allowed_colors).difference(restricted_colors[var].color)
    if len(allowed_colors) == 0:
        i = 0  # start with minimum color
        while i in restricted_colors[var]:
            i += 1
        return i
    else:
        return list(allowed_colors)[0]


def create_cfg(basic_blocks, name):
    cfg = DirectedAdjList()
    for block in basic_blocks.keys():
        if len(basic_blocks[block]) > 0:
            cfg.add_vertex(block)
    for block in basic_blocks.keys():
        for instr in basic_blocks[block]:
            match instr:
                case Jump(block_label) if not block_label.endswith('conclusion'):
                    cfg.add_edge(block_label, block)
                case JumpIf(cc, block_label) if not block_label.endswith('conclusion'):
                    cfg.add_edge(block_label, block)
    if cfg.num_vertices() == 0:
        cfg.add_vertex(name + 'start')
    return cfg


# endregion

# region explicate control helpers
def get_jmp_instr_label(jmp_instr):
    match jmp_instr:
        case Jump(label):
            return label
        case JumpIf(cc, label):
            return label
        case _:
            return ''


def force(promise):
    # return lambda promise: promise() if isinstance(promise, types.FunctionType) else promise
    if isinstance(promise, types.FunctionType):
        return promise()
    else:
        return promise


def promise(func):
    yield func()


def merge_trivial_blocks(prev_label, basic_blocks):
    prev_block_stmts = basic_blocks[prev_label]
    if len(prev_block_stmts) == 1:
        match prev_block_stmts:
            case Goto(prev_label1):
                return merge_trivial_blocks(prev_label1, basic_blocks)
    return Goto(prev_label)


def create_block(stmts, basic_blocks):
    stmts = force(stmts)
    match stmts:
        case [Goto(prev_label)]:
            return merge_trivial_blocks(prev_label, basic_blocks)
        case _:
            label = label_name(generate_name('block'))
            basic_blocks[label] = stmts
            return Goto(label)


# endregion

class Node:
    def __init__(self, name):
        self.colored = False
        self.color = None
        self.satur_set = set()
        self.satur_set_length = 0
        self.name = name

    def add(self, color):
        if color not in self.satur_set:
            self.satur_set.add(color)
            self.satur_set_length += 1

    def color_node(self, color):
        self.colored = True
        self.color = color


class Compiler:
    def parse_stmt(self, stmt):
        match stmt:
            case AnnAssign(lhs, typ, value, simple):
                if self.pass_name == 'convert_to_closures':
                    return Assign([lhs], self.parse_expr(value))
                if self.pass_name == 'convert_assignments':
                    match lhs:
                        case Name(var):
                            if var in self.assign_vars:
                                return AnnAssign(Subscript(Name(var), Constant(0), Store()), typ,
                                                 self.parse_expr(value), simple)
                            else:
                                return AnnAssign(Name(var), typ, self.parse_expr(value), simple)
                        case _:
                            return AnnAssign(lhs, typ, self.parse_expr(value), simple)

                return AnnAssign(lhs, typ, self.parse_expr(value), simple)
            case FunctionDef(name, params, bod, dl, returns, comment):
                if self.pass_name == 'limit_functions':
                    if len(params) < 6:
                        return FunctionDef(name, params, [self.parse_stmt(s) for s in bod], dl,
                                           returns,
                                           comment)
                    else:
                        new_params = params[0:5]
                        tup_name = generate_name('tup_0')
                        tup_types = [t for v, t in params[5:]]
                        self.tup_mapping = {v: Subscript(Name(tup_name), Constant(i), Load()) for i, (v, t) in
                                            enumerate(params[5:])}
                        return FunctionDef(name, new_params + [(tup_name, TupleType(tup_types))],
                                           [self.parse_stmt(s) for s in bod], dl, returns, comment)

                if self.pass_name == 'convert_to_closures':
                    return FunctionDef(name,
                                       [(generate_name('fvs'), Bottom())] + [(v, self.convert_types(t)) for v, t in
                                                                             params] if len(params) > 0 else [],
                                       [self.parse_stmt(s) for s in bod], dl,
                                       self.convert_types(returns), comment)
                if self.pass_name == 'convert_assignments':
                    param_names = list(zip(*params))
                    if len(param_names) > 0:
                        self.assign_vars = self.assigned_vars_stmt(bod).difference(set(param_names[0]))
                    else:
                        self.assign_vars = self.assigned_vars_stmt(bod)
                    self.assign_vars = self.assign_vars.intersection(self.free_variables_lambda(bod))
                    return FunctionDef(name, params,
                                       self.initializing_args(self.assign_vars) + [
                                           self.parse_stmt(s)
                                           for s in bod], dl, returns, comment)

                elif self.pass_name == 'uniquify':
                    self.enclosing_vars = {v: generate_name(v + '_0') for v, t in params}
                    return FunctionDef(name,
                                       [(self.enclosing_vars[v], t) if v in self.enclosing_vars.keys() else (v, t) for
                                        v, t in
                                        params], [self.parse_stmt(s) for s in bod], dl, returns,
                                       comment)
                else:
                    return FunctionDef(name, params, [self.parse_stmt(s) for s in bod], dl, returns, comment)
            case Expr(Call(Name('print'), [exp])):
                return Expr(Call(Name('print'), [self.parse_expr(exp)]))
            case Expr(exp):
                return Expr(self.parse_expr(exp))
            case Assign([Name(var)], exp):
                if self.pass_name == 'convert_assignments':
                    if var in self.assign_vars:
                        return Assign([Subscript(Name(var), Constant(0), Store())],
                                      self.parse_expr(exp))
                    else:
                        return Assign([Name(var)], self.parse_expr(exp))
                if self.pass_name == 'uniquify':
                    if var not in self.enclosing_vars.keys():
                        self.enclosing_vars[var] = generate_name(var + '_0')
                    return Assign([Name(self.enclosing_vars[var])], self.parse_expr(exp))
                else:
                    return Assign([Name(var)], self.parse_expr(exp))
            case If(test, ifstmts, orelsestmts):
                return If(self.parse_expr(test), [self.parse_stmt(s) for s in ifstmts],
                          [self.parse_stmt(s) for s in orelsestmts])
            case Return(e):
                return Return(self.parse_expr(e))
            case While(test, body, []):
                return While(self.parse_expr(test), [self.parse_stmt(s) for s in body], [])
            case Assign([Subscript(lhs, slice, Store())], exp):
                return Assign([Subscript(lhs, slice, Store())], self.parse_expr(exp))
            case _:
                return stmt

    def parse_expr(self, exp):
        match exp:
            case Let(var, rhs, body):
                return Let(var, self.parse_expr(rhs), self.parse_expr(body))
            case Lambda(params, body):
                if self.pass_name == 'convert_to_closures':
                    fn_name = generate_name('lambda_0')
                    free_vars_lambda = self.free_variables(body).difference(set(params))
                    clos = generate_name('clos_0')
                    self.top_lvl_funcs.append(FunctionDef(fn_name,
                                                          [(clos, TupleType([Bottom()] +
                                                                            [self.get_type(body, p) for p in
                                                                             free_vars_lambda]))] +
                                                          list(zip(params, exp.has_type.param_types)),
                                                          [Assign([Name(v)],
                                                                  Subscript(Name(clos), Constant(i + 1), Load())) for
                                                           i, v
                                                           in
                                                           enumerate(free_vars_lambda)]
                                                          + [Return(self.parse_expr(body))], None,
                                                          exp.has_type.ret_type,
                                                          None))
                    return ast.Tuple([FunRef(fn_name)] + [Name(v) for v in list(free_vars_lambda)], Load())
                if self.pass_name == 'uniquify':
                    self.enclosing_vars = self.enclosing_vars | {v: generate_name(v + '_0') for v in params}
                    return Lambda([self.enclosing_vars[v] if v in self.enclosing_vars.keys() else v for v in params],
                                  self.parse_expr(body))
                return Lambda(params, self.parse_expr(body))

            case BoolOp(boolop, e):
                match boolop:
                    case And():
                        if self.pass_name == 'shrink':
                            return IfExp(self.parse_expr(e[0]), self.parse_expr(e[1]), Constant(False))
                        else:
                            return exp
                    case Or():
                        if self.pass_name == 'shrink':
                            return IfExp(self.parse_expr(e[0]), Constant(True), self.parse_expr(e[1]))
                        else:
                            return exp
                    case _:
                        return exp

            case UnaryOp(uniop, e1):
                if self.pass_name == 'partial_evaluation':
                    match uniop:
                        case USub():
                            return self.pe_neg(self.parse_expr(e1))
                        case _:
                            return exp
                return UnaryOp(uniop, self.parse_expr(e1))

            case Compare(e1, cmpop, [e2]):
                return Compare(self.parse_expr(e1), cmpop, [self.parse_expr(e2)])
            case BinOp(e1, binop, e2):
                if self.pass_name == 'partial_evaluation':
                    match binop:
                        case Add():
                            return self.pe_add(self.parse_expr(e1), self.parse_expr(e2))
                        case Sub():
                            e2 = UnaryOp(USub(), e2)
                            return self.pe_add(self.parse_expr(e1), self.parse_expr(e2))
                        case _:
                            return exp
                return BinOp(self.parse_expr(e1), binop, self.parse_expr(e2))

            case IfExp(e1, e2, e3):
                return IfExp(self.parse_expr(e1), self.parse_expr(e2), self.parse_expr(e3))

            case Subscript(e1, e2, Load()):
                return Subscript(self.parse_expr(e1), self.parse_expr(e2), Load())
            case ast.Tuple(e, Load()):
                if self.pass_name == 'expose_allocation':
                    body = []
                    tmp_e = []
                    for es in e:
                        tmp_e.append(Name(generate_name('tmp_0')))
                        body.append(Assign([tmp_e[-1]], self.parse_expr(es)))
                    len_exp = len(e)
                    bytes = len_exp * 8 + 8
                    body.append(If(Compare(BinOp(GlobalValue(Name('free_ptr')), Add(), Constant(bytes)), [Lt()],
                                           [GlobalValue(Name('fromspace_end'))]), [Expr(Constant(0))],
                                   [Collect(bytes)]))
                    v = Name(generate_name('alloc_0'))
                    body.append(Assign([v], Allocate(len_exp, exp.has_type)))
                    for i, x in enumerate(tmp_e):
                        body.append(Assign([Subscript(v, Constant(i), Store())], x))
                    result = v
                    return Begin(body, result)
                return ast.Tuple([self.parse_expr(e_) for e_ in e], Load())
            case Call(Name('input_int'), []):
                return exp
            case Call(Name('len'), [exp]):
                return Call(Name('len'), [self.parse_expr(exp)])
            case Call(e1, e2):
                if self.pass_name == 'limit_functions':
                    if len(e2) <= 6:
                        return Call(self.parse_expr(e1),
                                    [self.parse_expr(arg) for arg in e2])
                    else:
                        new_args = [self.parse_expr(arg) for arg in e2[0:5]]
                        tup_arg = ast.Tuple([self.parse_expr(arg) for arg in e2[5:]], Load())
                        return Call(self.parse_expr(e1), new_args + [tup_arg])

                if self.pass_name == 'convert_to_closures':
                    tmp = generate_name('tmp_0')
                    return Let(Name(tmp), self.parse_expr(e1),
                               Call(Subscript(Name(tmp), Constant(0), Load()),
                                    [Name(tmp)] + [self.parse_expr(arg) for arg in e2]))

                return Call(self.parse_expr(e1), [self.parse_expr(e) for e in e2])
            case FunRef(var):
                if self.pass_name == 'convert_to_closures':
                    return ast.Tuple([FunRef(var)], Load())
                else:
                    return FunRef(var)
            case Name(var):
                if self.pass_name == 'limit_functions':
                    if var in self.tup_mapping.keys():
                        return self.tup_mapping[var]
                    else:
                        return exp
                if self.pass_name == 'uniquify':
                    if var in self.enclosing_vars.keys():
                        return Name(self.enclosing_vars[var])
                    else:
                        return exp
                elif self.pass_name == 'reveal':
                    if var in self.func_map:
                        return FunRef(var)
                    else:
                        return exp
                elif self.pass_name == 'convert_assignments':
                    if var in self.assign_vars:
                        return Subscript(Name(var), Constant(0), Load())
                    else:
                        return exp
                else:
                    return exp
            case _:
                return exp

    # region shrink
    def classify_main(self, body):
        if len(body) == 0:
            return [([], [])]
        return [([body[0]], []) if isinstance(body[0], FunctionDef) else ([], [body[0]])] + self.classify_main(body[1:])

    def apply_main(self, body):
        normal_func, main_func = unzip(self.classify_main(body))
        return sum(normal_func, []) + [
            FunctionDef('main', [], sum(main_func, []) + [Return(Constant(0))], None, int, None)]

    def shrink(self, p):
        self.pass_name = 'shrink'
        match p:
            case Module(body):
                return Module(self.apply_main([self.parse_stmt(s) for s in body]))

    # endregion
    # region uniquify
    def uniquify(self, p: Module):
        self.enclosing_vars = {}
        self.pass_name = 'uniquify'
        return Module([self.parse_stmt(s) for s in p.body])

    # endregion
    # region reveal functions
    def reveal_functions(self, p):
        self.pass_name = 'reveal'
        self.func_map = reduce(set.union, [{s.name} if isinstance(s, FunctionDef) else set() for s in p.body])
        match p:
            case Module(body):
                return Module([self.parse_stmt(stmt) for stmt in body])
        return p

    # endregion
    # region convert_assignments
    def assigned_vars_stmt(self, bod):
        assigned_vars = set()
        for s in bod:
            match s:
                case Assign([Name(var)], exp):
                    assigned_vars.add(var)
        return assigned_vars

    def initializing_args(self, assigned_vars):
        return [Assign([Name(var)], ast.Tuple([Constant(0)], Load())) for var in assigned_vars]

    def free_variables_lambda(self, bod):

        free_vars = reduce(set.union, [self.free_vars_stmt(s) for s in bod])
        return free_vars

    def free_vars_stmt(self, stmt):
        match stmt:
            case AnnAssign(lhs, typ, value, simple):
                return self.free_vars_exp(value)
            # case FunctionDef(name, params, bod, dl, returns, comment):
            #     return FunctionDef(name, params, [self.reveal_func_stmts(s, func_map) for s in bod], dl, returns,
            #                        comment)
            case Expr(Call(Name('print'), [exp])):
                return self.free_vars_exp(exp)
            case Expr(exp):
                return self.free_vars_exp(exp)
            case Assign([Name(var)], exp):
                return self.free_vars_exp(exp)
            case If(test, ifstmts, orelsestmts):
                return reduce(set.union, [self.free_vars_stmt(s) for s in ifstmts + orelsestmts]
                              + [self.free_vars_exp(test)])
            case Return(e):
                return self.free_vars_exp(e)
            case While(test, body, []):
                return self.free_vars_exp(test).union(reduce(set.union, [self.free_vars_stmt(s) for s in body]))

    def free_variables(self, exp):
        match exp:
            case Lambda(params, body):
                free_vars = self.free_variables(body)
                return free_vars.difference(set(params))

            case BoolOp(boolop, e):
                return self.free_variables(e[0]).union(self.free_variables(e[1]))

            case UnaryOp(uniop, e1):
                return self.free_variables(e1)

            case Compare(e1, cmpop, [e2]):
                return self.free_variables(e1).union(self.free_variables(e2))
            case BinOp(e1, binop, e2):
                return self.free_variables(e1).union(self.free_variables(e2))

            case IfExp(e1, e2, e3):
                return reduce(set.union, [self.free_variables(e_) for e_ in [e1] + [e2] + [e3]])

            case Subscript(e1, e2, Load()):
                return self.free_variables(e1).union(self.free_variables(e2))
            case ast.Tuple(e, Load()):
                return reduce(set.union, [self.free_variables(e_) for e_ in e])
            case Call(Name('input_int'), args):
                return set()
            case Call(e1, e2):
                return reduce(set.union, [self.free_variables(e_) for e_ in [e1] + e2])
            case Name(var):
                return {var}
            case _:
                return set()

    def free_vars_exp(self, exp):
        match exp:
            case Lambda(params, body):
                free_vars = self.free_variables(body)
                return free_vars.difference(set(params))

            case BoolOp(boolop, e):
                return [self.free_vars_exp(e1) for e1 in e]

            case UnaryOp(uniop, e1):
                return self.free_vars_exp(e1)

            case Compare(e1, cmpop, [e2]):
                return self.free_vars_exp(e1).union(self.free_vars_exp(e2))
            case BinOp(e1, binop, e2):
                return self.free_vars_exp(e1).union(self.free_vars_exp(e2))

            case IfExp(e1, e2, e3):
                return reduce(set.union, [self.free_vars_exp(e_) for e_ in [e1] + [e2] + [e3]])

            case Subscript(e1, e2, Load()):
                return self.free_vars_exp(e1).union(
                    self.free_vars_exp(e2))
            case ast.Tuple(e, Load()):
                return reduce(set.union, [self.free_vars_exp(e_) for e_ in e])
            case Call(e1, e2):
                return reduce(set.union, [self.free_vars_exp(e_) for e_ in [e1] + e2])
            case _:
                return set()

    def convert_assignments(self, p: Module):
        self.pass_name = 'convert_assignments'
        self.assign_vars = set()
        return Module([self.parse_stmt(s) for s in p.body])

    # endregion
    # region convert_closures
    def get_type(self, exp, p):
        match exp:
            case Lambda(params, body):
                return self.get_type(body, p)

            case BoolOp(boolop, e):
                t1 = self.get_type(e[0], p)
                t2 = self.get_type(e[1], p)
                return t2 if t1 is None else t1

            case UnaryOp(uniop, e1):
                return self.get_type(e1, p)

            case Compare(e1, cmpop, [e2]):
                t1 = self.get_type(e1, p)
                t2 = self.get_type(e2, p)
                return t2 if t1 is None else t1
            case BinOp(e1, binop, e2):
                t1 = self.get_type(e1, p)
                t2 = self.get_type(e2, p)
                return t2 if t1 is None else t1

            case IfExp(e1, e2, e3):
                t1 = self.get_type(e1, p)
                t2 = self.get_type(e2, p)
                return t2 if t1 is None else t1

            case Subscript(e1, e2, Load()):
                t1 = self.get_type(e1, p)
                t2 = self.get_type(e2, p)
                return t2 if t1 is None else t1
            case ast.Tuple(e, Load()):
                return self.get_type(e, p)
            case Call(Name('input_int'), args):
                return int
            case Call(e1, e2):
                t1 = self.get_type(e1, p)
                if t1 is None:
                    for e2_ in e2:
                        t2 = self.get_type(e2_, p)
                        if t2 is not None:
                            return t2
            case Name(var):
                return exp.has_type if var == p else None
            case _:
                return None

    def convert_types(self, t):
        match t:
            case FunctionType(ps, rt):
                return TupleType(
                    [FunctionType([TupleType([])] + [self.convert_types(p) for p in ps], self.convert_types(rt))])
            case _:
                return t

    def convert_to_closures(self, p: Module):
        self.top_lvl_funcs = []
        self.pass_name = 'convert_to_closures'

        return Module([self.parse_stmt(s) for s in p.body] + self.top_lvl_funcs)

    # endregion
    # region limit functions

    def limit_functions(self, p):
        match p:
            case Module(body):
                self.tup_mapping = {}
                self.pass_name = 'limit_functions'
                return Module([self.parse_stmt(s) for s in body])

    # endregion
    # region expose allocation

    def expose_allocation(self, p):
        match p:
            case Module(body):
                self.pass_name = 'expose_allocation'
                return Module([self.parse_stmt(stmt) for stmt in body])
            case _:
                Exception('program not valid at Expose Allocation pass')  # pass name should be parameterized

    # endregion
    ###########################################################################
    # Remove Complex Operands
    ###########################################################################
    # region remove complex operands

    def rco_exp(self, e: expr, need_atomic: bool) -> Tuple[expr, Temporaries]:
        # YOUR CODE HERE

        match e:
            case Let(var, rhs, body):
                tmp1, temporaries1 = self.rco_exp(rhs, True)
                if len(temporaries1) > 0:
                    tmp1 = get_let_exp(temporaries1)
                tmp2, temporaries2 = self.rco_exp(body, True)
                if len(temporaries2) > 0:
                    tmp2 = get_let_exp(temporaries2)
                if need_atomic:
                    atm = Name(generate_name('tmp_0'))
                    return atm, [(atm, Let(var, tmp1, tmp2))]
                else:
                    return Let(var, tmp1, tmp2), []
            case Call(Name('input_int'), []):
                if need_atomic:
                    tmp1 = Name(generate_name('tmp_0'))
                    return tmp1, [(tmp1, e)]
                else:
                    return e, []
            case Call(Name('len'), [exp]):
                atm, tmp = self.rco_exp(exp, False)
                if need_atomic:
                    tmp3 = (Name(generate_name('tmp_0')))
                    return tmp3, tmp + [(tmp3, Call(Name('len'), [atm]))]
                else:
                    return Call(Name('len'), [atm]), tmp
            case Call(e1, args):
                tmp1, temporaries1 = self.rco_exp(e1, True)
                arg_atm = {}
                arg_temps = {}
                for arg in args:
                    arg_atm[arg], arg_temps[arg] = self.rco_exp(arg, True)
                if need_atomic:
                    tmp3 = (Name(generate_name('tmp_0')))
                    return tmp3, temporaries1 + sum(arg_temps.values(), []) + [
                        (tmp3, Call(tmp1, [arg_atm[arg] for arg in args]))]
                else:
                    return Call(tmp1, [arg_atm[arg] for arg in args]), temporaries1 + sum(arg_temps.values(), [])
            case FunRef(var):
                if need_atomic:
                    tmp = Name(generate_name('fun_0'))
                    return tmp, [(tmp, e)]
                return e, []
            case Begin(ss, e):
                ss_rco = []
                [ss_rco.extend(self.rco_stmt(s)) for s in ss]
                exp_rco, temp = self.rco_exp(e, False)
                if need_atomic:
                    tmp = Name(generate_name('tmp_0'))
                    return tmp, temp + [(tmp, Begin(ss_rco, exp_rco))]
                return Begin(ss_rco, exp_rco), temp
            case IfExp(e1, e2, e3):
                tmp1, temporaries1 = self.rco_exp(e1, False)
                tmp2, temporaries2 = self.rco_exp(e2, True)
                if len(temporaries2) > 0:
                    tmp2 = get_let_exp(temporaries2)
                tmp3, temporaries3 = self.rco_exp(e3, True)
                if len(temporaries3) > 0:
                    tmp3 = get_let_exp(temporaries3)
                if need_atomic:
                    atm = Name(generate_name('tmp_0'))
                    return atm, temporaries1 + [(atm, IfExp(tmp1, tmp2, tmp3))]
                else:
                    return IfExp(tmp1, tmp2, tmp3), temporaries1

            case UnaryOp(uniop, e1):
                tmp1, temporaries1 = self.rco_exp(e1, True)
                if need_atomic:
                    tmp3 = (Name(generate_name('tmp_0')))
                    return tmp3, temporaries1 + [(tmp3, UnaryOp(uniop, tmp1))]
                else:
                    return UnaryOp(uniop, tmp1), temporaries1

            case BinOp(e1, binop, e2):
                tmp1, temporaries1 = self.rco_exp(e1, True)
                tmp2, temporaries2 = self.rco_exp(e2, True)
                if need_atomic:
                    tmp3 = (Name(generate_name('tmp_0')))
                    return tmp3, temporaries1 + temporaries2 + [(tmp3, BinOp(tmp1, binop, tmp2))]
                else:
                    return BinOp(tmp1, binop, tmp2), temporaries1 + temporaries2
            case BoolOp(boolop, [e1, e2]):
                tmp1, temporaries1 = self.rco_exp(self.shrink_exp(e1), True)
                tmp2, temporaries2 = self.rco_exp(self.shrink_exp(e2), True)
                if need_atomic:
                    tmp3 = (Name(generate_name('tmp_0')))
                    return tmp3, temporaries1 + temporaries2 + [(tmp3, BoolOp(boolop, [tmp1, tmp2]))]
                else:
                    return BoolOp(boolop, [tmp1, tmp2]), temporaries1 + temporaries2
            case Compare(e1, cmpop, [e2]):
                tmp1, temporaries1 = self.rco_exp(e1, True)
                tmp2, temporaries2 = self.rco_exp(e2, True)
                if need_atomic:
                    tmp3 = (Name(generate_name('tmp_0')))
                    return tmp3, temporaries1 + temporaries2 + [(tmp3, Compare(tmp1, cmpop, [tmp2]))]
                else:
                    return Compare(tmp1, cmpop, [tmp2]), temporaries1 + temporaries2
            case Name(var):
                return e, []
            case Constant(int_or_bool):
                return e, []

            case Subscript(tup_name, slice, Load()):
                atm1, tmp1 = self.rco_exp(tup_name, True)
                atm2, tmp2 = self.rco_exp(slice, True)
                if need_atomic:
                    tmp = Name(generate_name('tmp_0'))
                    return tmp, tmp1 + tmp2 + [(tmp, Subscript(atm1, atm2, Load()))]
                return Subscript(atm1, atm2, Load()), tmp1 + tmp2
            case GlobalValue(var):
                if need_atomic:
                    tmp = Name(generate_name('tmp_0'))
                    return tmp, [(tmp, e)]
                return e, []
            case _:
                return e, []

    def rco_stmt(self, s: stmt) -> List[stmt]:
        # YOUR CODE HERE
        match s:
            case FunctionDef(name, params, bod, dl, returns, comment):
                new_bod = sum([self.rco_stmt(stmt) for stmt in bod], [])
                return [FunctionDef(name, params, new_bod, dl, returns, comment)]
            case Return(e):
                atm, tmp = self.rco_exp(e, False)
                return [Assign([stmt[0]], stmt[1]) for stmt in tmp] + [Return(atm)]
            case Collect(size):
                return [s]
            case Expr(Call(Name('print'), [exp])):
                atm, tmp = self.rco_exp(exp, True)
                return [Assign([stmt[0]], stmt[1]) for stmt in tmp] \
                       + [Expr(Call(Name('print'), [atm]))] if len(tmp) > 0 \
                    else [Expr(Call(Name('print'), [atm]))]
            case Expr(exp):
                atm, tmp = self.rco_exp(exp, False)
                return [Expr(stmt[1]) if stmt == tmp[-1] else Assign([stmt[0]], stmt[1]) for stmt in tmp] if len(
                    tmp) > 0 \
                    else [s]

            case Assign([Subscript(tup_name, slice, Store())], exp):
                atm1, tmp1 = self.rco_exp(tup_name, True)
                atm2, tmp2 = self.rco_exp(slice, True)
                atm3, tmp3 = self.rco_exp(exp, False)
                return_list = [Assign([stmt[0]], stmt[1]) for stmt in tmp1]
                return_list.extend([Assign([stmt[0]], stmt[1]) for stmt in tmp2])
                return_list.extend([Assign([stmt[0]], stmt[1]) for stmt in tmp3])
                return_list.extend([Assign([Subscript(atm1, atm2, Store())], atm3)])
                return return_list

            case Assign([Name(var)], exp):

                atm, tmp = self.rco_exp(exp, False)
                return [Assign([stmt[0]], stmt[1]) for stmt in tmp] + [Assign([Name(var)], atm)] \
                    if len(tmp) > 0 \
                    else [Assign([Name(var)], atm)]

            case While(test, stmts, []):
                test, tmp = self.rco_exp(test, True)
                if len(tmp) > 0:
                    test = get_let_exp(tmp)
                return [While(test, sum([self.rco_stmt(stmt) for stmt in stmts], []), [])]

            case If(test, ifstmts, orelsestmts):
                if_rco = sum([self.rco_stmt(stmt) for stmt in ifstmts], [])
                orelse_rco = sum([self.rco_stmt(stmt) for stmt in orelsestmts], [])
                test, tmp = self.rco_exp(test, False)
                return [Assign([stmt[0]], stmt[1]) for stmt in tmp] + [If(test, if_rco, orelse_rco)] \
                    if len(tmp) > 0 \
                    else [If(test, if_rco, orelse_rco)]
            case _:
                Exception('statement invalid in rco_stmt')

    def remove_complex_operands(self, p: Module) -> Module:
        # YOUR CODE HERE

        # partial evaluation
        match p:
            case Module(body):
                self.pass_name = 'partial_evaluation'
                p = Module([self.parse_stmt(s) for s in body])
        match p:
            case Module(body):
                return Module(sum([self.rco_stmt(stmt) for stmt in body], []))
            case _:
                Exception('program not valid')

    # endregion
    # region explicate control:
    def explicate_control(self, p):
        match p:
            case Module(defs):
                program_defs = []
                for defn in defs:
                    basic_blocks = {}
                    match defn:
                        case FunctionDef(name, params, bod, dl, returns, comment):
                            new_body = []
                            for s in reversed(bod):
                                new_body = self.explicate_stmt(s, new_body, basic_blocks)
                            basic_blocks[name + label_name('start')] = new_body
                            program_defs.append(FunctionDef(name, params, basic_blocks, dl, returns, comment))
                return CProgramDefs(program_defs)

    def explicate_tail(self, e, basic_blocks):
        match e:
            case Call(Name('input_int'), []):
                return [Return(e)]
            case Call(Name('len'), [tup]):
                return [Return(e)]
            case Call(fn, args):
                return [TailCall(fn, args)]
            case IfExp(test, body, orelse):
                return_body = self.explicate_tail(body, basic_blocks)
                return_orelse = self.explicate_tail(orelse, basic_blocks)
                return self.explicate_pred(test, return_body, return_orelse, basic_blocks)
            case Let(var, rhs, body):
                new_body = self.explicate_tail(body, basic_blocks)
                return self.explicate_assign(rhs, var, new_body, basic_blocks)
            case Begin(body, result):
                new_body = self.explicate_tail(result, basic_blocks)
                for s in reversed(body):
                    new_body = self.explicate_stmt(s, new_body, basic_blocks)
                return new_body
                # new_body = []
                # for s in reversed(body):
                #     new_body = self.explicate_stmt(s, new_body, basic_blocks)
                #
                # return new_body + self.explicate_tail(result, basic_blocks)
            case _:
                return [Return(e)]

    def explicate_stmt(self, s, cont, basic_blocks):
        match s:
            case Return(e):
                return self.explicate_tail(e, basic_blocks)
            case Assign([Subscript(tup, ind, Store())], rhs):
                tmp = Name(generate_name('tmp_0'))
                new_body = self.explicate_assign(tmp, Subscript(tup, ind, Store()), cont, basic_blocks)
                return self.explicate_assign(rhs, tmp, new_body, basic_blocks)
            case Assign([lhs], rhs):
                return self.explicate_assign(rhs, lhs, cont, basic_blocks)
            case Expr(value):
                return self.explicate_effect(value, cont, basic_blocks)
            case If(cond, thn, els):
                cont = [create_block(cont, basic_blocks)]
                thn_body = cont
                for s in reversed(thn):
                    thn_body = self.explicate_stmt(s, thn_body, basic_blocks)

                els_body = cont
                for s in reversed(els):
                    els_body = self.explicate_stmt(s, els_body, basic_blocks)
                return self.explicate_pred(cond, thn_body, els_body, basic_blocks)
            case While(test, body, []):
                loop_block = [create_block([], basic_blocks)]
                thn_body = loop_block
                for s in reversed(body):
                    thn_body = self.explicate_stmt(s, thn_body, basic_blocks)
                # thn_body = create_block(thn_body, basic_blocks)
                goto_if = self.explicate_pred(test, thn_body
                                              , cont, basic_blocks)
                match loop_block:
                    case [Goto(label1)]:
                        basic_blocks[label1].extend(goto_if)
                return loop_block
            case Collect(size):
                return [s] + cont

    def explicate_pred(self, cnd, thn, els, basic_blocks):
        match cnd:
            case Compare(left, [op], [right]):
                goto_thn = create_block(thn, basic_blocks)
                goto_els = create_block(els, basic_blocks)
                return [If(cnd, [goto_thn], [goto_els])]
            case Constant(True):
                return thn
            case Constant(False):
                return els
            case Name(var):
                goto_thn = create_block(thn, basic_blocks)
                goto_els = create_block(els, basic_blocks)
                return [If(Compare(cnd, [Eq()], [Constant(True)]), [goto_thn], [goto_els])]
            case UnaryOp(Not(), operand):
                return self.explicate_pred(operand, els, thn, basic_blocks)
            case IfExp(test, body, orelse):
                thn_block = [create_block(thn, basic_blocks)]
                orelse_block = [create_block(els, basic_blocks)]
                body = self.explicate_pred(body, thn_block, orelse_block, basic_blocks)
                orelse = self.explicate_pred(orelse, thn_block, orelse_block, basic_blocks)
                return self.explicate_pred(test, body, orelse, basic_blocks)
            case Let(var, rhs, body):
                return [Assign([var], rhs)] + self.explicate_pred(body, thn, els, basic_blocks)
            case Subscript(tup_name, slice, Load()):
                tmp = Name(generate_name('tmp'))
                return [Assign([tmp], cnd)] + self.explicate_pred(tmp, thn, els, basic_blocks)
            case Call(fn, args):
                tmp = Name(generate_name('tmp'))
                return [Assign([tmp], cnd)] + self.explicate_pred(tmp, thn, els, basic_blocks)
            case _:
                return [If(Compare(cnd, [Eq()], [Constant(False)]),
                           [create_block(els, basic_blocks)],
                           [create_block(thn, basic_blocks)])]

    def explicate_assign(self, rhs, lhs, cont, basic_blocks):
        match rhs:

            case IfExp(test, body, orelse):

                body = self.explicate_assign(body, lhs, cont, basic_blocks)
                orelse = self.explicate_assign(orelse, lhs, cont, basic_blocks)
                return self.explicate_pred(test, body, orelse, basic_blocks)
            case Let(var, rhs, body):
                new_body = self.explicate_assign(body, lhs, cont, basic_blocks)
                return self.explicate_assign(rhs, var, new_body, basic_blocks)
            case Begin(body, result):
                new_body = [create_block(self.explicate_assign(result, lhs, cont, basic_blocks), basic_blocks)]
                for s in reversed(body):
                    new_body = self.explicate_stmt(s, new_body, basic_blocks)
                return new_body

            case _:
                return [Assign([lhs], rhs)] + cont

    def explicate_effect(self, e, cont, basic_blocks):
        match e:
            case IfExp(test, body, orelse):
                return self.explicate_pred(test, body + cont, orelse + cont, basic_blocks)
            case Call(func, args):
                return [Expr(e)] + cont
            case Let(var, rhs, body):
                ...
            case _:
                return [Expr(e)] + cont

    # endregion
    ############################################################################
    # Select Instructions
    ############################################################################
    # region instruction selection
    def select_op(self, op):
        match op:
            case Add():
                return 'addq'
            case Sub():
                return 'subq'
            case USub():
                return 'negq'
            case Not():
                return 'xorq'
            case Is():
                return 'eq'

    def select_suffix(self, cmpop):
        '''
        :param cmpop:
        :return: a condition code string
        '''
        match cmpop:
            case Eq():
                return 'e'
            case NotEq():
                return 'ne'
            case Lt():
                return 'l'
            case LtE():
                return 'le'
            case Gt():
                return 'g'
            case GtE():
                return 'ge'
            case Is():
                return 'e'

    def select_arg(self, e: expr) -> arg:
        # YOUR CODE HERE
        match e:
            case Constant(True):
                return Immediate(1)
            case Constant(False):
                return Immediate(0)
            case Constant(num):
                return Immediate(num)
            case Name(var):
                return Variable(var)
            case GlobalValue(var):
                return x86_ast.Global(var)

    def select_exp(self, e: expr, dest: arg = Reg('rax')) -> List:
        match e:
            case BinOp(atm1, binop, atm2):
                return [Instr('movq', [self.select_arg(atm1), Reg('rax')]),
                        Instr(self.select_op(binop), [self.select_arg(atm2), dest])]
            case UnaryOp(uniop, atm1):
                op = self.select_op(uniop)
                if op == 'xorq':
                    instr2 = Instr('xorq', [Immediate(1), dest])
                else:
                    instr2 = Instr(op, [dest])
                return [Instr('movq', [self.select_arg(atm1), dest]),
                        instr2]
            case Compare(atm1, [cmpop], [atm2]):
                return [Instr('cmpq', [self.select_arg(atm2), self.select_arg(atm1)]),
                        Instr('set' + self.select_suffix(cmpop), [ByteReg('al')]),
                        Instr('movzbq', [ByteReg('al'), dest])]
            case Call(Name('input_int'), []):
                return [Callq('read_int', 0), Instr('movq', [Reg('rax'), dest])]
            case Subscript(tup, Constant(index), Load()):
                return [Instr('movq', [self.select_arg(tup), Reg('r11')]),
                        Instr('movq', [Deref('r11', 8 * (index + 1)), dest])]
            case Allocate(len_tup, TupleType(types)):
                ptr_mask = (lambda types: ''.join(['1' if isinstance(typ, Tuple) else '0' for typ in types])) \
                    (types)
                ptr_mask = (50 - len(ptr_mask)) * '0' + ptr_mask
                fwrd_ptr = '1'
                length_mask = f'{len_tup:06b}'
                tag = Immediate(int(ptr_mask + length_mask + fwrd_ptr, base=2))
                return [Instr('movq', [Deref('rip', 'free_ptr'), Reg('r11')]),
                        Instr('addq', [Immediate(8 * (len_tup + 1)), Deref('rip', 'free_ptr')]),
                        Instr('movq', [tag, Deref('r11', 0)]),
                        Instr('movq', [Reg('r11'), dest])]
            case GlobalValue(var):
                return [Instr('movq', [self.select_arg(e), dest])]
            case Call(Name('len'), [e1]):
                return [Instr('movq', [self.select_arg(e1), Reg('rax')]),
                        Instr('movq', [Deref('rax', 0), Reg('rax')]),
                        Instr('andq', [Immediate(126), Reg('rax')]),
                        Instr('sarq', [Immediate(1), Reg('rax')]),
                        Instr('movq', [Reg('rax'), dest])]
            case Call(fun, args):
                arg_mapping = {v: k for k, v in caller_saved_regs.items()}
                return sum(
                    [[Instr('movq', [self.select_arg(arg), arg_mapping[i]]) for i, arg in enumerate(args)],
                     [IndirectCallq(self.select_arg(fun), len(args)), Instr('movq', [Reg('rax'), dest])]], [])
            case FunRef(label):
                return [Instr('leaq', [x86_ast.Global(label), dest])]
            case _:
                return [Instr('movq', [self.select_arg(e), dest])]

    def select_fn(self, fn: FunctionDef) -> FunctionDef:
        match fn:
            case FunctionDef(name, params, basic_blocks, dl, returns, comment):
                self.fn_name = name
                arg_mapping = {v: k for k, v in caller_saved_regs.items()}
                defn = FunctionDef(name, [],
                                   {k: sum([self.select_stmt(stmt) for stmt in basic_blocks[k]], [])
                                   if k == name + 'start' else [Instr('movq', [arg_mapping[i], Variable(arg)]) for
                                                                i, (arg, type) in enumerate(params)] + sum(
                                       [self.select_stmt(stmt) for stmt in basic_blocks[k]], [])
                                    for k in basic_blocks.keys()}, dl, returns, comment)
                defn.var_types = fn.var_types
                return defn

    def select_stmt(self, s: stmt) -> List[instr]:
        # YOUR CODE HERE
        match s:
            case TailCall(fn, args):
                arg_mapping = {v: k for k, v in caller_saved_regs.items()}
                return sum([[Instr('movq', [self.select_arg(arg), arg_mapping[i]]) for i, arg in enumerate(args)],
                            [TailJump(fn, len(args))]], [])
            case If(Compare(atm1, [cmpop], [atm2]), [Goto(label1)], [Goto(label2)]):
                return [Instr('cmpq', [self.select_arg(atm2), self.select_arg(atm1)]),
                        JumpIf(self.select_suffix(cmpop), label1),
                        Jump(label2)]
            case Goto(label):
                return [Jump(label)]
            case Return(exp):
                return self.select_exp(exp) + [Jump(self.fn_name + 'conclusion')]
            # case UnaryOp(uniop, atm1):
            #     op = self.select_op(uniop)
            #     if op == 'xorq':
            #         instr2 = Instr('xorq', [Immediate(1), self.select_arg(atm1)])
            #     else:
            #         instr2 = Instr(op, [self.select_arg(atm1)])
            #     return [Instr('movq', [self.select_arg(atm1), var_arg]),
            #             instr2,
            #             Jump(name + 'conclusion')]
            # case Compare(atm1, [cmpop], [atm2]):
            #     return [Instr('cmpq', [self.select_arg(atm2), self.select_arg(atm1)]),
            #             Instr('set' + self.select_suffix(cmpop), [ByteReg('al')]),
            #             Instr('movzbq', [ByteReg('al'), var_arg])]
            # case Constant(num):
            #     return [Instr('movq', [self.select_arg(e), var_arg])]
            # case Name(var):
            #     return [Instr('movq', [self.select_arg(e), var_arg])]
            # case GlobalValue(var):
            #     return [Instr('movq', [self.select_arg(e), var_arg])]
            # case Call(Name('input_int'), []):
            #     return [Callq('read_int', 0),
            #             Instr('movq', [Reg('rax'), var_arg])]
            # case Call(Name('len'), [e1]):
            #     return [Instr('movq', [self.select_arg(e1), Reg('rax')]),
            #             Instr('movq', [Deref('rax', 0), Reg('rax')]),
            #             Instr('andq', [Immediate(126), Reg('rax')]),
            #             Instr('sarq', [Immediate(1), Reg('rax')]),
            #             Instr('movq', [Reg('rax'), var_arg])]
            case Expr(Call(Name('print'), [atm])):
                return [Instr('movq', [self.select_arg(atm), Reg('rdi')]),
                        Callq('print_int', 0)]
            case Assign([Subscript(tup_name, Constant(n), Store())], rhs):
                return [Instr('movq', [self.select_arg(tup_name), Reg('r11')]),
                        Instr('movq', [self.select_arg(rhs), Deref('r11', 8 * (n + 1))])]
            case Collect(bytes):
                return [Instr('movq', [Reg('r15'), Reg('rdi')]),
                        Instr('movq', [Immediate(bytes), Reg('rsi')]),
                        Callq('collect', 2)]
            case Assign([var_name], e):
                var_arg = self.select_arg(var_name)
                return self.select_exp(e, dest=var_arg)
            case Expr(e):
                return self.select_exp(e)
            case _:
                return []

    def select_instructions(self, p: Module) -> X86ProgramDefs:
        # YOUR CODE HERE
        match p:
            case CProgramDefs(defs):
                return X86ProgramDefs([self.select_fn(defn) for defn in defs])
            case _:
                Exception('invalid program in select instructions pass')

    # endregion
    # region Assign homes
    ############################################################################
    # Assign Homes
    ############################################################################

    def initialize_live_blocks(self, basic_blocks, name):
        self.live_before_block = {k: set() for k, v in basic_blocks.items()}
        self.live_before_block[name + 'conclusion'] = {Reg('rsp'), Reg('rax')}
        self.basic_blocks = basic_blocks
        self.L_after = {block: [set() for _ in range(len(basic_blocks[block]))] for block in
                        basic_blocks.keys()}
        self.L_before = {block: [set() for _ in range(len(basic_blocks[block]))] for block in
                         basic_blocks.keys()}
        self.W_set = {block: [set() for _ in range(len(basic_blocks[block]))] for block in basic_blocks.keys()}
        self.R_set = {block: [set() for _ in range(len(basic_blocks[block]))] for block in basic_blocks.keys()}

    def remove_jumps(self, dependent_block, block, basic_blocks):
        for i, instr in enumerate(basic_blocks[dependent_block]):
            match basic_blocks[dependent_block][i]:
                case Jump(label_name):
                    if label_name == block:
                        instr_to_append = basic_blocks[block]
                        basic_blocks[dependent_block] = basic_blocks[dependent_block][:i] + instr_to_append + \
                                                        basic_blocks[dependent_block][i:]
                        basic_blocks.pop(block, None)

    def allocate_registers(self, var_color_map, reg_color_map, var_types):
        used_callee = set()
        used_Stack_space = 0
        used_root_space = 0
        k = 0
        if len(var_color_map.values()) > 0:
            k = max(reg_color_map.keys())
        homes = {}
        for var, color in var_color_map.items():
            if var in var_types.keys() and isinstance(var_types[var], TupleType):
                used_root_space += 8
                homes[var] = Deref('r15', -used_root_space)
                continue
            if color > k:
                used_Stack_space += 8  # for spill
                homes[var] = Deref('rbp', -used_Stack_space)

            else:
                homes[var] = reg_color_map[color]
                if reg_color_map[color] in callee_saved_regs:
                    used_callee.add(reg_color_map[color])
        return homes, used_callee, used_Stack_space, used_root_space

    def assign_homes_arg(self, a: arg, home: Dict[Variable, arg]) -> arg:
        # YOUR CODE HERE
        #
        match a:
            case x86_ast.Global(var):
                if var in home.keys():
                    return x86_ast.Global(home[var])
                return a
            case Deref(reg, offset):
                return a
            case _:
                if a in home.keys():
                    return home[a]
                return a

    def assign_homes_instr(self, i: instr,
                           home: Dict[location, arg]) -> instr:
        # YOUR CODE HERE

        match i:
            case TailJump(fn, num_args):
                return TailJump(self.assign_homes_arg(fn, home), num_args)
            case IndirectCallq(fn, num_args):
                return IndirectCallq(self.assign_homes_arg(fn, home), num_args)
                # new_instr = self.assign_homes_instr(instrn, home)
                # match new_instr:
                #     case Instr(instr_name, [new_arg1, new_arg2]):
                #         if type(arg1) == Variable(location):
                #             if arg1 not in home.keys():
                #                 home[arg1] = new_arg1
                #         if type(arg2) == Variable(location):
                #             if arg2 not in home.keys():
                #                 home[arg2] = new_arg2
                # new_instructions.append(new_instr)
            case Instr(instr_name, args):
                return Instr(instr_name, [self.assign_homes_arg(arg, home) for arg in args])
            case _:
                return i

    def assign_homes_instrs(self, ss: List[instr],
                            home: Dict[location, arg]) -> List[instr]:
        # YOUR CODE HERE
        return [self.assign_homes_instr(instr, home) for instr in ss]

    def assign_homes(self, p: X86Program) -> X86ProgramDefs:
        # YOUR CODE HERE
        match p:
            case X86ProgramDefs(defs):
                xprogram_defs = []
                for d in defs:
                    match d:
                        case FunctionDef(name, params, basic_blocks, dl, returns, comment):
                            cfg = create_cfg(basic_blocks, name)
                            self.initialize_live_blocks(basic_blocks, name)
                            self.analyze_dataflow(cfg, transfer=self.transfer, bottom=set(), join=set().union)
                            inf_graph = self.build_interference_graph(basic_blocks, self.L_after, self.W_set)
                            move_graph = self.build_move_graph(basic_blocks, inf_graph.vertices())
                            reg_color_map = {color: reg for reg, color in itertools.chain(callee_saved_regs.items(),
                                                                                          caller_saved_regs.items())}
                            var_color_map = self.color_graph(inf_graph, move_graph, move_biasing=False)
                            homes, used_callee, stack_space, root_space = self.allocate_registers(var_color_map,
                                                                                                  reg_color_map,
                                                                                                  d.var_types)
                            for block in basic_blocks.keys():
                                basic_blocks[block] = self.assign_homes_instrs(basic_blocks[block], homes)
                            for block in cfg.ins.keys():
                                if len(cfg.ins[block]) == 1:
                                    self.remove_jumps(cfg.ins[block][0], block, basic_blocks)
                            d_ = FunctionDef(name, params, basic_blocks, dl, returns, comment)
                            d_.var_types = d.var_types
                            d_.stack_space = stack_space
                            d_.used_callee = used_callee
                            d_.root_space = root_space
                            xprogram_defs.append(d_)
                return X86ProgramDefs(xprogram_defs)
            case _:
                Exception('program is invalid in assign homes pass')

    # endregion
    # region Patch instructions
    ############################################################################
    # Patch Instructions
    ############################################################################

    def patch_instr(self, i: instr) -> List[instr]:
        # YOUR CODE HERE
        match i:
            case Instr('leaq', [FunRef(label), Variable(id)]):
                return [Instr('leaq', [FunRef(label), Reg('rax')]), Instr('movq', [Reg('rax'), Variable(id)])]
            case TailJump(jmp_loc, num_args):
                return [Instr('movq', [jmp_loc, Reg('rax')]),
                        TailJump(Reg('rax'), num_args)]
            case Instr('cmpq', [Immediate(int1), Immediate(int2)]):
                instr1 = Instr('movq', [Immediate(int2), Reg('rax')])
                instr2 = Instr('cmpq', [Immediate(int1), Reg('rax')])
                return [instr1, instr2]
            case Instr(instr_name, [Deref(reg_name1, offset1), Deref(reg_name2, offset2)]):
                if reg_name1 == reg_name2 and offset1 == offset2:
                    return []
                else:
                    instr1 = Instr('movq', [Deref(reg_name1, offset1), Reg('rax')])
                    instr2 = Instr(instr_name, [Reg('rax'), Deref(reg_name2, offset2)])
                    return [instr1, instr2]
            case Instr('movq', [loc1, loc2]):
                if loc1 == loc2:
                    return []
                else:
                    return [i]
            case _:
                return [i]

    def patch_instrs(self, ss: List[instr]) -> List[instr]:
        # YOUR CODE HERE
        return sum([self.patch_instr(instrn) for instrn in ss], [])

    def patch_instructions(self, p: X86Program) -> X86Program:
        # YOUR CODE HERE

        match p:
            case X86ProgramDefs(defs):
                xprogram_defs = []
                for d in defs:
                    match d:
                        case FunctionDef(name, params, basic_blocks, dl, returns, comment):
                            d_ = FunctionDef(name, params, {k: self.patch_instrs(v) for k, v in basic_blocks.items()},
                                             dl, returns, comment)
                            d_.stack_space = d.stack_space
                            d_.used_callee = d.used_callee
                            d_.root_space = d.root_space
                            xprogram_defs.append(d_)
                return X86Program(xprogram_defs)

    # endregion
    # region Prelude and Conclusions
    ############################################################################
    # Prelude & Conclusion
    ############################################################################

    def prelude_and_conclusion(self, p: X86Program) -> X86Program:
        # YOUR CODE HERE
        match p:
            case X86Program(defs):
                basic_blocks = {}
                for d in defs:

                    match d:
                        case FunctionDef(name, [], basic_blocks, dl, returns, comment):
                            # while rsp_space <= stack_space:
                            #     rsp_space += 16

                            prelude = [Instr('pushq', [Reg('rbp')]), Instr('movq', [Reg('rsp'), Reg('rbp')])]
                            used_callee = list(d.used_callee)  # preserving the order of callees for pop instructions
                            for callee in used_callee:
                                prelude.extend([Instr('pushq', [callee])])
                                # stack_space += 8
                            if len(used_callee) > 0:
                                d.stack_space = align(d.stack_space + 8 * len(used_callee),
                                                      8 * len(used_callee))  # - (stack_space%(8*len(used_callee))))
                            prelude.extend([Instr('subq', [Immediate(d.stack_space), Reg('rsp')])])

                            if name == 'main':
                                prelude.extend([Instr('movq', [Immediate(65536), Reg('rdi')]),
                                                Instr('movq', [Immediate(65536), Reg('rsi')]),
                                                Callq('initialize', 2),
                                                Instr('movq', [Global('rootstack_begin'), Reg('r15')]),
                                                Instr('addq', [Immediate(d.root_space), Reg('r15')]),
                                                Instr('movq', [Immediate(0), Reg('r15')]),
                                                Jump(name + 'start')])
                            basic_blocks[name] = prelude
                            conclusion = [Instr('subq', [Immediate(d.root_space), Reg('r15')])
                                , Instr('addq', [Immediate(d.stack_space), Reg('rsp')])]
                            for callee in reversed(used_callee):
                                conclusion.extend([Instr('popq', [callee])])
                            conclusion.extend([Instr('popq', [Reg('rbp')]),
                                               Instr('retq', [])])
                            basic_blocks[name + 'conclusion'] = conclusion
                            for block_name, block in basic_blocks.items():
                                for instr_no, instr in enumerate(block):
                                    match instr:
                                        case TailJump(arg, num_args):
                                            block_update = block[:instr_no]
                                            block_update = block_update + conclusion[:-1] + [IndirectJump(arg)] + block[
                                                                                                                  instr_no:]
                                            basic_blocks[block_name] = block_update
                return X86Program(basic_blocks)

                # homes = set()
                # for instrn in p.body:
                #     match instrn:
                #         case Instr(instr_name, [Deref('rbp', offset1),Deref('rbp', offset2)]):
                #             homes.add(offset1)
                #             homes.add(offset2)
                #         case Instr(instr_name, [Deref('rbp', offset1),arg]):
                #             homes.add(offset1)
                #         case Instr(instr_name, [arg, Deref('rbp', offset1)]):
                #             homes.add(offset1)
                #         case Instr(instr_name, [Deref('rbp', offset1)]):
                #             homes.add(offset1)
                # if homes:
                #     stack_space = abs(min(homes))
                #

                # prelude.extend(p.body)
                # prelude.extend(conclusion)
                #
                # return X86Program(prelude)

    # endregion
    ## region partial evaluation :
    def pe_neg(self, r):
        match r:
            case Constant(n):
                return Constant(-n)
            case _:
                return UnaryOp(USub(), r)

    def pe_add(self, r1, r2):
        match (r1, r2):
            case (Constant(n1), Constant(n2)):
                return Constant(n1 + n2)
            case (BinOp(any_type, binop, Constant(int1)), Constant(int2)):
                left = Constant(int1 + int2)
                return BinOp(any_type, binop, left)
            case (Constant(int2), BinOp(any_type, binop, Constant(int1))):
                left = Constant(int1 + int2)
                return BinOp(left, binop, any_type)
            case (BinOp(Constant(int1), binop, any_type), Constant(int2)):
                left = Constant(int1 + int2)
                return BinOp(any_type, binop, left)
            case (Constant(int2), BinOp(Constant(int1), binop, any_type)):
                left = Constant(int1 + int2)
                return BinOp(left, binop, any_type)
            case _:

                return BinOp(r1, Add(), r2)

    def pe_sub(self, r1, r2):
        match (r1, r2):
            case (Constant(n1), Constant(n2)):
                return Constant(n1 - n2)
            case (BinOp(any_type, binop, Constant(int1)), Constant(int2)):
                left = Constant(int1 - int2)
                return BinOp(any_type, binop, left)
            case (Constant(int2), BinOp(any_type, binop, Constant(int1))):
                left = Constant(int1 - int2)
                return BinOp(left, binop, any_type)
            case (BinOp(Constant(int1), binop, any_type), Constant(int2)):
                left = Constant(int1 - int2)
                return BinOp(left, binop, any_type)
            case (Constant(int2), BinOp(Constant(int1), binop, any_type)):
                left = Constant(int1 - int2)
                return BinOp(left, binop, any_type)
            case _:

                return BinOp(r1, Sub(), r2)

    # def pe_exp(self, e):
    #     match e:
    #         case Call(func_exp, args):
    #             return Call(self.pe_exp(func_exp), [self.pe_exp(arg) for arg in args])
    #         case BinOp(left, Add(), right):
    #             return self.pe_add(self.pe_exp(left), self.pe_exp(right))
    #         case BinOp(left, Sub(), right):
    #             right = UnaryOp(USub(), right)
    #             return self.pe_add(self.pe_exp(left), self.pe_exp(right))
    #         case UnaryOp(USub(), v):
    #             return self.pe_neg(self.pe_exp(v))
    #         case IfExp(e1, e2, e3):
    #             return IfExp(self.pe_exp(e1), self.pe_exp(e2), self.pe_exp(e3))
    #         case Compare(e1, [cmpop], [e2]):
    #             return Compare(self.pe_exp(e1), [cmpop], [self.pe_exp(e2)])
    #         case Call(Name('len'), [exp]):
    #             return Call(Name('len'), [self.pe_exp(exp)])
    #         case Subscript(e1, e2, Load()):
    #             return Subscript(self.pe_exp(e1), self.pe_exp(e2), Load())
    #         case ast.Tuple(e1, Load()):
    #             return ast.Tuple([self.pe_exp(e_) for e_ in e1], Load())
    #         case _:
    #             return e
    #
    # def pe_stmt(self, s):
    #     match s:
    #         case FunctionDef(name, params, bod, dl, returns, comment):
    #             return FunctionDef(name, params, [self.pe_stmt(s) for s in bod], dl, returns, comment)
    #         case Return(e):
    #             return Return(self.pe_exp(e))
    #         case Expr(Call(Name('print'), [arg])):
    #             return Expr(Call(Name('print'), [self.pe_exp(arg)]))
    #         case Expr(value):
    #             return Expr(self.pe_exp(value))
    #         case Assign([Name(var)], e):
    #             return Assign([Name(var)], self.pe_exp(e))
    #         case If(test, body, orelse):
    #             body_pe = []
    #             body_pe.extend([self.pe_stmt(stmt) for stmt in body])
    #             orelse_pe = []
    #             orelse_pe.extend([self.pe_stmt(stmt) for stmt in orelse])
    #             return If(self.pe_exp(test), body_pe, orelse_pe)
    #         case While(test, body, []):
    #             body_pe = []
    #             body_pe.extend([self.pe_stmt(stmt) for stmt in body])
    #             return While(self.pe_exp(test), body_pe, [])
    #         case _:
    #             return s

    ## endregion
    # region liveness analysis
    # def uncover_live(self, cfg, basic_blocks):
    #
    #     ordering = topological_sort(transpose(cfg))
    #     if ordering.num_vertices() == 0:
    #         ordering = list(basic_blocks.keys())
    #     live_before_block = {}
    #     #  initialize live_befores of block having no dependency
    #     dependencies = 0
    #     i = 0
    #     while dependencies == 0:
    #         live_before_block[ordering[i]] = {}
    #         i += 1
    #         if i < len(ordering):
    #             dependencies = len(cfg.out[ordering[i]])
    #         else:
    #             break
    #
    #     L_after = {block: [set() for _ in range(len(basic_blocks[block]))] for block in basic_blocks.keys()}
    #     L_before = {block: [set() for _ in range(len(basic_blocks[block]))] for block in basic_blocks.keys()}
    #     W_set = {block: [set() for _ in range(len(basic_blocks[block]))] for block in basic_blocks.keys()}
    #     R_set = {block: [set() for _ in range(len(basic_blocks[block]))] for block in basic_blocks.keys()}
    #     for block_num in ordering:
    #         ss = basic_blocks[block_num]
    #         num_instr = len(basic_blocks[block_num])
    #         # L_after[block_num] = [set() for _ in range(num_instr)]
    #         # L_before[block_num] = [set() for _ in range(num_instr)]
    #         # # L_before[-1] = live_before_block[block]
    #         # W_set[block_num] = [set() for _ in range(num_instr)]
    #         # R_set[block_num] = [set() for _ in range(num_instr)]
    #         for instr in range(num_instr - 1, -1, -1):
    #             match ss[instr]:
    #                 case Jump('conclusion'):
    #                     L_before[block_num][instr] = set()
    #                 case Jump(label):
    #                     L_before[block_num][instr] = live_before_block[label]
    #                 case JumpIf(cc, label):
    #                     prev_jmpinstr_label = get_jmp_instr_label(ss[instr + 1])
    #                     if prev_jmpinstr_label != '':
    #                         prev_set = live_before_block[prev_jmpinstr_label]
    #                     else:
    #                         prev_set = set()
    #                     L_before[block_num][instr] = live_before_block[label].union(prev_set)
    #                 case _:
    #                     W_set[block_num][instr] = self.W(ss[instr])
    #                     R_set[block_num][instr] = self.R(ss[instr])
    #                     L_before[block_num][instr] = (
    #                         L_after[block_num][instr].difference(W_set[block_num][instr]).union(
    #                             R_set[block_num][instr]))
    #             if instr == 0:
    #                 live_before_block[block_num] = L_before[block_num][0]
    #             else:
    #                 L_after[block_num][instr - 1] = L_before[block_num][instr]
    #         if block_num == ordering[-1]:
    #             return L_after, W_set
    def transfer(self, node, input):
        ss = self.basic_blocks[node]
        num_instr = len(self.basic_blocks[node])
        self.L_after[node][num_instr - 1] = input
        for instr in range(num_instr - 1, -1, -1):
            match ss[instr]:
                case Jump('conclusion'):
                    self.L_before[node][instr] = set()
                case Jump(label):
                    self.L_before[node][instr] = self.live_before_block[label]
                case JumpIf(cc, label):  # assumption that conditional jump will never go to conclusion
                    prev_jmpinstr_label = get_jmp_instr_label(ss[instr + 1])
                    prev_set = set() \
                        if prev_jmpinstr_label == '' \
                        else self.live_before_block[prev_jmpinstr_label]
                    self.L_before[node][instr] = self.live_before_block[label].union(prev_set)
                case _:
                    self.W_set[node][instr] = self.W(ss[instr])
                    self.R_set[node][instr] = self.R(ss[instr])
                    self.L_before[node][instr] = (
                        self.L_after[node][instr].difference(self.W_set[node][instr]).union(self.R_set[node][instr]))
            if instr == 0:
                self.live_before_block[node] = self.L_before[node][0]
            else:
                self.L_after[node][instr - 1] = self.L_before[node][instr]
        return self.live_before_block[node]

    def analyze_dataflow(self, G, transfer, bottom, join):
        trans_G = transpose(G)
        mapping = {}
        for v in G.vertices():
            mapping[v] = bottom
        worklist = deque()
        for v in G.vertices():
            worklist.append(v)
        while worklist:
            node = worklist.pop()
            input = reduce(join, [mapping[v] for v in trans_G.adjacent(node)], bottom)
            output = transfer(node, input)
            if output != mapping[node]:
                mapping[node] = output
                for v in G.adjacent(node):
                    worklist.append(v)

    def W(self, instr):
        match instr:
            case Instr('cmpq', args):
                return {}
            case Instr(instr_name, args):
                match args[-1]:
                    case Variable(id):
                        return {args[-1]}
                    case Reg(reg_name):
                        return {args[-1]}
                    case ByteReg(arg):
                        return {choose_reg(arg)}
                    case _:
                        return {}

            case Callq(any_instr, any_type):
                return set(caller_saved_regs.keys())
            case IndirectCallq(fn, num_args):
                return set(caller_saved_regs.keys())
            case _:
                return {}

    def R(self, instr):
        match instr:
            case Instr('movq', args):

                match args[0]:
                    case Variable(id):
                        return {args[0]}
                    case Reg(name):
                        return {args[0]}

                    case ByteReg(byte_Reg):
                        return {choose_reg(byte_Reg)}
                    case _:
                        return {}
            case Instr('movzbq', args):
                match args[0]:
                    case Variable(id):
                        return {args[0]}
                    case Reg(name):
                        return {args[0]}
                    case ByteReg(byte_Reg):
                        return {choose_reg(byte_Reg)}
                    case _:
                        return {}

            case Instr(instr, args):
                read_set = set()
                for arg in args:
                    match arg:
                        case Variable(id):
                            read_set.add(arg)
                        case Reg(reg_name):
                            read_set.add(arg)
                return read_set

            # case Instr('negq', args):
            #     read_set = set()
            #     for arg in args:
            #         match arg:
            #             case Variable(id):
            #                 read_set.add(arg)
            #             case Reg(reg_name):
            #                 read_set.add(arg)
            #     return read_set

            case Callq('print_int', num_args):
                return {Reg('rdi')}

            case Callq('read_int', []):
                return {}
            case IndirectCallq(fn, num_args) | TailCall(fn, num_args) | Callq(fn, num_args):
                arg_mapping = {v: k for k, v in caller_saved_regs.items()}
                return {arg_mapping[i] for i in range(num_args)}.union({fn})
            case _:
                return {}

    # endregion
    # region build graphs
    def build_interference_graph(self, basic_blocks, L_after, W_Set):
        interference_graph = UndirectedAdjList()
        for block in basic_blocks.keys():
            for instr in basic_blocks[block]:
                match instr:
                    case Callq(func_name, args):
                        for reg in caller_saved_regs.keys():
                            if caller_saved_regs[reg] >= 0:
                                interference_graph.add_vertex(reg)
                    case Instr(instr_name, args):
                        for arg in args:
                            match arg:
                                case Variable(var1):
                                    interference_graph.add_vertex(arg)
                                case Reg(reg_name):
                                    if Reg(reg_name) in caller_saved_regs.keys():
                                        if caller_saved_regs[Reg(reg_name)] > 0:
                                            interference_graph.add_vertex(arg)
                                    elif Reg(reg_name) in callee_saved_regs.keys():
                                        if callee_saved_regs[Reg(reg_name)] > 0:
                                            interference_graph.add_vertex(arg)
                                case ByteReg(bytereg):
                                    interference_graph.add_vertex(choose_reg(bytereg))
                                # case Deref(reg_name, offset):
                                #     interference_graph.add_vertex(Reg(reg_name))

        for block in basic_blocks.keys():
            vertices = interference_graph.vertices()
            for k in range(len(basic_blocks[block])):  # need k to use L_after indexing
                match basic_blocks[block][k]:
                    case Instr('movq', [s, d]):
                        for v in L_after[block][k]:
                            if v != d and v != s:
                                if d in vertices and v in vertices:
                                    interference_graph.add_edge(d, v)
                    case _:
                        for d in W_Set[block][k]:
                            for v in L_after[block][k]:
                                if v != d:
                                    if d in vertices and v in vertices:
                                        interference_graph.add_edge(d, v)
        return interference_graph

    def build_move_graph(self, basic_blocks, vertices):
        move_graph = UndirectedAdjList()
        for vertex in vertices:
            move_graph.add_vertex(vertex)
        for block_num, block in enumerate(basic_blocks.keys()):
            for instr in basic_blocks[block]:
                match instr:
                    case Instr('movq', [Variable(id1), Variable(id2)]):
                        move_graph.add_edge(Variable(id1), Variable(id2))
        return move_graph

    # endregion
    # region graph coloring
    def color_graph(self, inf_graph, move_graph, move_biasing=False):

        vars_map_satur = {v: Node(v) for v in inf_graph.vertices()}

        # region pre-coloring
        for vertex in vars_map_satur.keys():
            match vertex:
                case Deref(reg_name, offset):
                    vars_map_satur[vertex].color_node(vertex)
                    for node in inf_graph.adjacent(vertex):
                        vars_map_satur[node].add(vertex)
                        # vars_map_satur_length[node] = len(vars_map_satur[node])
                    # rem_set.remove(vertex)
                    # colored_set.add(vertex)
                case Reg(reg_name):
                    if vertex in caller_saved_regs.keys():
                        vars_map_satur[vertex].color_node(caller_saved_regs[vertex])
                        for node in inf_graph.adjacent(vertex):
                            vars_map_satur[node].add(caller_saved_regs[vertex])
                    else:
                        vars_map_satur[vertex].color_node(callee_saved_regs[vertex])
                        for node in inf_graph.adjacent(vertex):
                            vars_map_satur[node].add(callee_saved_regs[vertex])

        # endregion
        # region build priority queue
        pq = self.build_priority_queue(
            vars_map_satur, lambda a, b: a.key.satur_set_length < b.key.satur_set_length)
        # endregion
        # region assigning colors
        while not pq.empty():
            var_to_color = pq.pop().name  # pop the maximally saturated node
            if not vars_map_satur[var_to_color].colored:
                colored_set = set([v for v in vars_map_satur.keys() if vars_map_satur[v].colored])
                vars_map_satur[var_to_color].color_node(get_color_with_move_biasing(var=var_to_color,
                                                                                    move_graph=move_graph,
                                                                                    colored_set=colored_set,
                                                                                    restricted_colors=vars_map_satur,
                                                                                    inf_graph=inf_graph) \
                                                            if move_biasing \
                                                            else \
                                                            get_color(var=var_to_color,
                                                                      colored_set=colored_set,
                                                                      color_map=vars_map_satur,
                                                                      inf_graph=inf_graph))

                for node in set(inf_graph.adjacent(var_to_color)):  # wrapped in set() because of possibility of
                    # duplicates
                    vars_map_satur[node].add(vars_map_satur[var_to_color].color)
                    pq.increase_key(vars_map_satur[node])

        # endregion
        return {k: v.color for k, v in vars_map_satur.items() if v.color >= 0}

    def build_priority_queue(self, vars_map, func=lambda a, b: a.position < b.position):
        pq = PriorityQueue(func)
        for var in vars_map.keys():
            pq.push(vars_map[var])
        return pq

    # endregion
