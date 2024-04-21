from lark import Lark, Tree, Token
from grammar import GRAMMAR
import operator
import z3
from z3 import ArithRef, BitVecRef, BoolRef

class LanguageError(Exception):
    def __init__(self, message: str):
        self.message = message

    def __str__(self) -> str:
        return f"[error] {self.message}"

class Interpretor:

    def __init__(self):
        self.holes = {}
        self.variables = {}
        self.functions = {
            "print": print, 
            "max": self.z3_max, 
            "min": min, 
            "length": len,
            "array": self.make_array,
        }
        self.parser = Lark(
            GRAMMAR,
            start="program",
            parser="lalr", 
            propagate_positions=True,
        )

    # Create an array of length n with default value val
    def make_array(self, n: int, val: int | bool | float):
        return z3.K(z3.IntSort(), val)
    
    def z3_max(self, vs: list[z3.ArithRef | z3.BitVecRef] | list[int | float]):
        #if isinstance(vs[0], int | float):
        #    return max(vs)
        #else:
        m = vs[0]
        for v in vs[1:]:
            m = z3.If(v > m, v, m)
        return m
    
    def eval_var(self, node: Tree):
        name = node.children[0]
        try:
            if name in self.functions:
                return self.functions[name]
            return self.variables[name]
        except KeyError:
            raise Exception(f"No array with name: {name}")
        
    def eval_hole(self, node: Tree):
        name = node.children[0]
        if name not in self.holes:
            self.holes[name] = z3.Int(name)                
        return self.holes[name]
    
    def eval_arguments(self, node: Tree):
        args = []
        for child in node.children:
            args.append(self.eval_expression(child))
        return args
    
    def eval_atom(self, node: Tree | Token):
        atom_data = node.children[0].data 
        if atom_data == "var":
            return self.eval_var(node.children[0])
        elif atom_data == "hole":
            return self.eval_hole(node.children[0])
        elif atom_data == "expression":
            return self.eval_expression(node.children[0])
        raise Exception("Atom Error")
            
    def eval_call(self, node: Tree | Token):
        if len(node.children) == 1:
            child = node.children[0]
            if child.data == "atom":
                return self.eval_atom(node.children[0])
            elif child.data == "true":
                return True
            elif child.data == "false":
                return False
            elif child.data == "nil":
                return None
            elif child.data == "number":
                return int(node.children[0].children[0].value)
            elif child.data == "string":
                return str(node.children[0].children[0].value[1:-1])
            elif child.data == "array_access":
                name = node.children[0].children[0].children[0].value
                index = self.eval_expression(node.children[0].children[1])
                try:
                    arr = self.variables[name]
                    try:
                        if isinstance(index, ArithRef | BitVecRef):
                            return arr[index]
                        index = int(index)
                        return arr[index]
                    except IndexError:
                        raise Exception(f"Index out of range: {index}")
                except KeyError:
                    raise Exception(f"No array with name: {name}")
            elif child.data == "array":
                vals = []
                for gchild in child.children:
                    vals.append(self.eval_expression(gchild))
                return vals
        else:
            fun = self.eval_atom(node.children[0])
            args = self.eval_arguments(node.children[1])
            if fun == self.z3_max:
                return fun(args)
            return fun(*args)
    
    def eval_unary(self, node: Tree | Token):
        if len(node.children) == 1:
            return self.eval_call(node.children[0])
        raise Exception(f"Unary Error")
    
    def eval_factor(self, node: Tree | Token):
        if len(node.children) == 1:
            child = node.children[0]
            if child.data == "neg":
                val = self.eval_unary(child.children[0])
                if isinstance(val, int | float):
                    return -val
                raise LanguageError("Arithmetic negation can only be applied on ints or floats")
            elif child.data == "not":
                val = self.eval_unary(child.children[0])
                if isinstance(val, bool):
                    return not val 
                raise LanguageError("Logical negation can only be applied on booleans")
            elif child.data == "unary":
                return self.eval_unary(child)
        raise Exception(f"Factor Error")
    
    def eval_term(self, node: Tree | Token):
        if len(node.children) == 1:
            child = node.children[0]
            if child.data in {"mul", "div"}:
                factor1 = self.eval_factor(child.children[0])
                factor2 = self.eval_factor(child.children[1])
                op = {
                    "mul": operator.mul, 
                    "div": operator.truediv
                }[child.data]
                if isinstance(factor1, int | float | ArithRef) and isinstance(factor2, int | float | ArithRef):
                    try:
                        return op(factor1, factor2)
                    except ZeroDivisionError:
                        raise LanguageError("Cannot divide by 0")
                raise LanguageError("Only floats and ints can be multiplied")
            elif child.data == "factor":
                return self.eval_factor(child)
        raise Exception(f"Term Error")
    
    def eval_comparison(self, node: Tree | Token):
        if len(node.children) == 1:
            child = node.children[0]
            if child.data in {"add", "sub"}:
                term1 = self.eval_term(child.children[0])
                term2 = self.eval_term(child.children[1])
                op = {
                        "add": operator.add, 
                        "sub": operator.sub
                    }[child.data]
                if isinstance(term1, int | float | ArithRef | BitVecRef) and isinstance(term2, int | float | ArithRef | BitVecRef):
                    return op(term1, term2)
                raise LanguageError("Only floats and ints can be added/subtraced")
            elif child.data == "term":
                return self.eval_term(child)
        raise Exception(f"Comparison Error")
    
    def eval_equality(self, node: Tree | Token):
        if len(node.children) == 1:
            child = node.children[0]
            if child.data in {"ge", "le", "geq", "leq"}:
                comp1 = self.eval_comparison(child.children[0])
                comp2 = self.eval_comparison(child.children[1])
                if isinstance(comp1, int | float | ArithRef | BitVecRef) and isinstance(comp2, int | float | ArithRef | BitVecRef):
                    op = {
                        "ge": operator.gt, 
                        "le": operator.lt, 
                        "geq": operator.ge, 
                        "leq": operator.le
                    }[child.data]
                    return op(comp1, comp2)
                raise LanguageError("Only float and ints can be compared")
            elif child.data == "comparison":
                return self.eval_comparison(child)
        raise Exception(f"Equlaity Error")

    def eval_logic_and(self, node: Tree | Token):
        if len(node.children) == 1:
            child = node.children[0]
            if child.data in {"eeq", "neq"}:
                eq1 = self.eval_equality(child.children[0])
                eq2 = self.eval_equality(child.children[1])
                op = {
                    "eeq": operator.eq, 
                    "neq": operator.ne
                }[child.data]
                return op(eq1, eq2)
            elif child.data == "equality":
                return self.eval_equality(child)
        raise Exception(f"Logic And Error")

    def eval_logic_or(self, node: Tree | Token):
        if len(node.children) == 1:
            child = node.children[0]
            if child.data == "and":
                p1 = self.eval_logic_and(child.children[0])
                p2 = self.eval_logic_and(child.children[1])
                if isinstance(p1, bool | BoolRef) and isinstance(p2, bool | BoolRef):
                    return p1 and p2
                raise LanguageError("Can only take an and of boolean expressions")
            elif child.data == "logic_and":
                return self.eval_logic_and(child)
        raise Exception(f"Logic Or Error")
    
    def eval_var_assign(self, node: Tree | Token):
        if len(node.children) == 2:
            var = node.children[0].children[0].value
            val = self.eval_expression(node.children[1])
            self.variables[var] = val
            return None
        raise Exception(f"Variable Assignment Error")
    
    def eval_arr_assign(self, node: Tree | Token):
        if len(node.children) == 3:
            name = node.children[0].children[0].value
            index = self.eval_expression(node.children[1])
            val = self.eval_expression(node.children[2])
            try:
                arr = self.variables[name]
                try:
                    if isinstance(arr, z3.ArrayRef):
                        self.variables[name] = z3.Store(arr, index, val)
                    else:
                        index = int(index)
                        arr[index] = val
                except IndexError:
                    raise Exception(f"Index out of range: {index}")
            except KeyError:
                raise Exception(f"No array with name: {name}")
            return None
        raise Exception(f"Array Assignment Error")
    
    def eval_assignment(self, node: Tree | Token):
        if len(node.children) == 1:
            child = node.children[0]
            if child.data == "var_assignment":
                self.eval_var_assign(child)
            elif child.data == "array_assignment":
                self.eval_arr_assign(child)
            return None
        raise Exception(f"Assignment Error")

    def eval_expression(self, node: Tree | Token):
        if len(node.children) == 1:
            child = node.children[0]
            if child.data == "or":
                p1 = self.eval_logic_or(child.children[0])
                p2 = self.eval_logic_or(child.children[1])
                if isinstance(p1, bool) and isinstance(p2, bool):
                    return p1 or p2
                raise LanguageError("Can only take an or of boolean expressions")
            elif child.data == "logic_or":
                return self.eval_logic_or(child)
            elif child.data == "assignment":
                return self.eval_assignment(child)
        raise Exception(f"Expression Error")
    
    def eval_return_stmt(self, node: Tree | Token):
        if len(node.children) == 1:
            child = node.children[0]
            if child.data == "expression":
                return self.eval_expression(child)
        raise Exception(f"Return Stmt Error")
    
    def eval_if_stmt(self, node: Tree | Token):
        if len(node.children) == 2:
            cond = node.children[0]
            check = self.eval_expression(cond)
            if isinstance(check, bool):
                if check:
                    stmt_list = node.children[1]
                    return self.eval_stmt_list(stmt_list)
                else:
                    return None
        raise Exception(f"If Stmt Error")

    def eval_for_stmt(self, node: Tree | Token):
        if len(node.children) == 4:
            init = node.children[0]
            limit = node.children[1]
            incr = node.children[2]
            action = node.children[3]
            self.eval_expression(init)

            last = None
            while True:
                limit_check = self.eval_expression(limit)
                if isinstance(limit_check, bool):
                    if limit_check:
                        last = self.eval_stmt_list(action)
                    else:
                        return last
                    self.eval_expression(incr)
                else:
                    raise LanguageError("Limit Check must be a boolean expression")
        raise Exception("For Stmt Error")

    def eval_statement(self, node: Tree | Token):
        if len(node.children) == 1:
            child = node.children[0]
            if child.data == "expression":
                return self.eval_expression(child)
            elif child.data == "return_statement":
                return self.eval_return_stmt(child)
            elif child.data == "if_statement":
                return self.eval_if_stmt(child)
            elif child.data == "for_statement":
                return self.eval_for_stmt(child)
        raise Exception(f"Statement Error")
    
    def eval_stmt_list(self, node: Tree | Token):
        for child in node.children:
            if child.data == "statement":
                val = self.eval_statement(child)
                if child.children[0].data == "return_statement":
                    return val
            else: 
                raise Exception("Stmt List Error")
        return None
    
    def eval_program(self, node: Tree | Token):
        if len(node.children) == 1:
            child = node.children[0]
            if child.data == "stmt_lst":
                return self.eval_stmt_list(child)
        raise Exception(f"Program Error")

    def interpret(self, prog, lookup = dict()):
        tree = self.parser.parse(prog)
        self.variables = lookup
        #print(tree.pretty())
        return self.eval_program(tree)
    
    def synthesis(self, prog, lookup, s, debug = False):
        if debug:
            try:
                print(s.model())
            except z3.Z3Exception:
                pass

        tree = self.parser.parse(prog)
        self.variables = lookup

        bounds_flag = False
        if len(self.holes) == 0:
            bounds_flag = True

        out = self.eval_program(tree)

        if bounds_flag:
            for hole in self.holes:
                if hole.startswith('x'):
                    s.add(self.holes[hole] >= 0)
                    s.add(self.holes[hole] <= self.variables['n']-1)
                else:
                    s.add(self.holes[hole] >= -1)
                    s.add(self.holes[hole] <= 1)

        s.push()
        return out