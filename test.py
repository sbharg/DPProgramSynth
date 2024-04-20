from interp import Interpretor
import z3

interp = Interpretor()
prog = """
n = length(A)
dp = array(n+1, 0)
dp[1] = A[0]

for(i = 2; i <= n; i = i + 1)
    dp[i] = max(?a1*dp[i-?x1] + ?b1*A[i-1], ?a2*dp[i-?x2] + ?b2*A[i-1])
end
return dp[n]
"""

x = z3.Int('x')
#print(type(x))

ret = interp.interpret(prog, {'A': [1, 2, 3, 4, 5], 'x': x})
print(ret)
print(type(ret))

#print(interp.variables)