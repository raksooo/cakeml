open preamble;

val _ = new_theory"javascriptMockAst";

val js_lit_def = Hol_datatype `
  js_lit =
      Js_boolean of bool`;

val js_unary_op_def = Hol_datatype `
  js_unary_op =
      Js_not`;

val js_binary_op_def = Hol_datatype `
  js_binary_op =
      Js_and
    | Js_or
    | Js_eq`;

val js_expr_def = Hol_datatype `
  js_expr =
      Js_lit of js_lit
    | Js_unary of js_unary_op => js_expr
    | Js_binary of js_binary_op => js_expr => js_expr`;

val _ = export_theory()

