from interp import Interpretor
import z3
import pandas as pd
from pathlib import Path  
from ast import literal_eval

s = z3.Solver()
interp = Interpretor()

prob = "mis"
sketch_path = Path(f'sketches/{prob}.txt')
with open(sketch_path, 'r') as f:
    prog = f.read()

k = 1
#examples = Path(f'examples/{prob}/examples.csv')  
examples = Path(f'examples/{prob}/k{k}.csv')  
df = pd.read_csv(examples)
df['Input'] = df['Input'].apply(lambda x: literal_eval(x))
n = len(df['Input'][0])

lst = []
arrs = []
A = z3.IntVector('A', n)
expr = interp.synthesis(prog, {'A': A}, s, debug=False) 
#for i in range(n):
#    s.add(A[i] <= 5)
#    s.add(A[i] >= -5)
val = z3.Int('val')
#s.add(expr == val)

for index, row in df.iterrows():
    arr = row['Input']
    opt = row['Opt']

    arrs.append(arr)
    stmt = [A[i] == arr[i] for i in range(len(arr))]
    stmt.append(val == opt)
    test = z3.And(stmt)
    #test = z3.Implies(z3.And(stmt), expr == opt)
    #test = interp.synthesis(prog, {'A': arr}, s, debug=False) == opt
    lst.append(test)
tests = z3.Or(lst)

#print(lst)
#print(arrs)

s.add(
    z3.ForAll([*A, val], z3.Implies(tests, expr == val))
)
print(s.sexpr())

if s.check() == z3.sat:
    m = s.model()
    print(m)
    #print(s.sexpr())

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
    val_a.sort(key=lambda x: int(x.name().split('a')[1]))
    val_a = [m[x] for x in val_a]
    val_b.sort(key=lambda x: int(x.name().split('b')[1]))
    val_b = [m[x] for x in val_b]

    holes = []
    for i in range(len(val_x)):
        hole = ""
        match val_a[i]:
            case 1:
                hole += f"dp{i%2+1}[i-{val_x[i]}]"
            case 0:
                hole += f""
            case _:
                hole += f"{val_a[i]}dp{i%2+1}[i-{val_x[i]}]"
        match val_b[i]:
            case 1:
                hole += f" + val"
            case 0:
                hole += f""
            case _:
                hole += f" + {val_b[i]}val"
        holes.append(hole)

    print(f"Synthesized recurrences:")
    print(f"dp1[i] = max({holes[0]}, {holes[1]})")
    #print(f"dp2[i] = max({holes[2]}, {holes[3]})")
else:
    print("Failed to synthesize recurrence")