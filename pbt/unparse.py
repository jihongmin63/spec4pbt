"""Render the example proposition's addition as executable Python source."""

import ast


def render_program(input_value: int) -> str:
    """Render an AST that prints the observed side of ``input + 0 = input``."""
    if type(input_value) is not int or input_value < 0:
        raise ValueError(f"program input must be a natural number; received {input_value!r}")
    expression: ast.BinOp = ast.BinOp(
        left=ast.Constant(value=input_value), op=ast.Add(), right=ast.Constant(value=0)
    )
    program: ast.Module = ast.Module(
        body=[
            ast.Expr(
                value=ast.Call(
                    func=ast.Name(id="print", ctx=ast.Load()), args=[expression], keywords=[]
                )
            )
        ],
        type_ignores=[],
    )
    return ast.unparse(ast.fix_missing_locations(program)) + "\n"
