GRAMMAR = r"""
    %import common.LETTER
    %import common.DIGIT
    %import common.INT
    %import common.NUMBER
    %import common.WORD
    %import common.CNAME
    %import common.ESCAPED_STRING

    %import common.WS
    %ignore WS
    %import common.SH_COMMENT
    %ignore SH_COMMENT

    program         : stmt_lst
    stmt_lst        : statement+

    statement       : expression | return_stmt | if_stmt | for_stmt 
    return_stmt     : "return" expression ~ 1 -> return_statement
    if_stmt         : "if" "(" expression ")" stmt_lst "end" -> if_statement
    for_stmt        : "for" "(" expression ";" expression ";" expression ")" stmt_lst "end" -> for_statement

    expression      : assignment | logic_or
    assignment      : var_assign | arr_assign
    var_assign      : var "=" expression -> var_assignment
    arr_assign      : var "[" expression "]" "=" expression -> array_assignment
    logic_or        : logic_and 
                    | logic_or "or" logic_or -> or
    logic_and       : equality 
                    | logic_and "and" logic_and -> and
    equality        : comparison 
                    | equality "!=" equality -> neq
                    | equality "==" equality -> eeq
    comparison      : term 
                    | comparison ">" comparison -> ge
                    | comparison "<" comparison -> le
                    | comparison ">=" comparison -> geq
                    | comparison "<=" comparison -> leq
    term            : factor 
                    | term "+" term -> add
                    | term "-" term -> sub
    factor          : unary 
                    | factor "*" factor -> mul
                    | factor "/" factor -> div
    unary           : call
                    | "!" unary -> not
                    | "-" unary -> neg
    call            : atom 
                    | atom ( "(" arguments ")" )* 
    atom            : "true" -> true 
                    | "false" -> false 
                    | NUMBER -> number
                    | ESCAPED_STRING -> string
                    | var
                    | hole
                    | var "[" expression "]" -> array_access
                    | "[" expression ( "," expression )* "]" -> array
                    | "(" expression ")"
    var             : CNAME
    hole            : "??" | "?" CNAME
    arguments       : expression ( "," expression )*
"""