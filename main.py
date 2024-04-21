from interp import Interpretor
import z3
import pandas as pd
from pathlib import Path  
from ast import literal_eval
import argparse
import time

def fill_holes(m, j=1):
    decs = m.decls()
    val_x = []
    val_a = []
    val_b = []
    for dec in decs:
        match dec.name()[0]:
            case 'x':
                val_x.append(dec)
            case 'a':
                val_a.append(dec)
            case 'b':
                val_b.append(dec)

    val_x.sort(key=lambda x: int(x.name().split('x')[1]))
    val_x = [m[x] for x in val_x]
    print(val_x)
    val_a.sort(key=lambda x: int(x.name().split('a')[1]))
    val_a = [m[x] for x in val_a]
    val_b.sort(key=lambda x: int(x.name().split('b')[1]))
    val_b = [m[x] for x in val_b]

    holes = []
    for i in range(len(val_x)):
        hole = ""
        match val_a[i]:
            case 1:
                hole += f"dp{i%j+1}[i" 
                #if val_x[i] > 0:    
                hole += f"-{val_x[i]}"
                hole += f"]"
            case 0:
                hole += f""
            case _:
                hole += f"{val_a[i]}dp{i%j+1}[i"
                #if val_x[i] > 0:    
                hole += f"-{val_x[i]}"
                hole += f"]"
        match val_b[i]:
            case 1:
                hole += f" + val"
            case 0:
                hole += f""
            case _:
                hole += f" + {val_b[i]}val"
        holes.append(hole)
    return holes

if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("-s", "--sketch", type=str, help="Path to the sketch file", default=None, required=True)
    parser.add_argument("-e", "--examples", type=str, help="Path to the examples file", default=None, required=True)
    parser.add_argument("-t", "--timeout", type=int, help="z3 Solver Timeout (default: %(default)d s)", default=150)
    parser.add_argument("-r", "--runs", type=int, help="Number of times to repeat (default: %(default)d)", default=1)
    args = parser.parse_args()

    sketch_path = Path(args.sketch)
    with open(sketch_path, 'r') as f:
        prog = f.read()

    examples = Path(args.examples)  
    df = pd.read_csv(examples)
    df['Input'] = df['Input'].apply(lambda x: literal_eval(x))
    n = len(df['Input'][0])
    print("Finished reading inputs")

    ts = time.perf_counter()
    print_time = 0
    init_time = 0
    for i in range(args.runs):
        print(f"Run {i+1}/{args.runs}")

        i_ts = time.perf_counter()
        interp = Interpretor()
        s = z3.Solver()
        s.set("timeout", args.timeout*1000)
        i_te = time.perf_counter()
        init_time += i_te - i_ts

        lst = []
        #A = z3.IntVector('A', n)
        for index, row in df.iterrows():
            arr = row['Input']
            opt = row['Opt']
            #test = z3.Implies(z3.And([A[i] == arr[i] for i in range(len(arr))]), interp.synthesis(prog, {'A': arr}, s, debug=False) == opt)
            test = interp.synthesis(prog, {'A': arr}, s, debug=False) == opt
            lst.append(test)
        tests = z3.And(lst)
        #s.add(z3.ForAll(A, tests))
        s.add(tests)
       # print(s.sexpr())

        res = s.check()
        if res == z3.sat:
            p_ts = time.perf_counter()
            m = s.model()
            #print(m)
            holes = fill_holes(m, j=2)
            #print(f"Synthesized recurrence: max({holes[0]}, {holes[1]})")
            print(f"Synthesized recurrences:")
            print(f"dp1[i] = max({holes[0]}, {holes[1]})")
            print(f"dp2[i] = max({holes[2]}, {holes[3]})\n")
            p_te = time.perf_counter()
            print_time += p_te - p_ts
        else:
            raise Exception("No solution found (Did not find sat solutions).")
    te = time.perf_counter()

    print(f"Average Time of {args.runs} runs: {(te - ts - print_time - init_time)/args.runs:0.4f} seconds")