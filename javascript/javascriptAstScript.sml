open preamble;

val _ = new_theory"javascriptAst";

val js_lit_def = Hol_datatype `
  js_lit =
      JSIntLit of int
    | JSStrLit of string
    | JSWord8 of word8
    | JSWord64 of word64`;

val js_opn_def = Hol_datatype `
  js_opn = JSPlus | JSMinus | JSTimes | JSDivide | JSModulo`;

val js_opb_def = Hol_datatype `
  js_opb = JSLt | JSGt | JSLeq | JSGeq`;

val js_opw_def = Hol_datatype `
  js_opw = JSAndw | JSOrw | JSXor | JSAdd | JSSub`;

val js_shift_def = Hol_datatype `
  js_shift = JSLsl | JSLsr | JSAsr | JSRor`;

val js_word_size_def = Hol_datatype `
  js_word_size = JSW8 | JSW64`;

val js_op_def = Hol_datatype `
  js_op =
      JSOpn of js_opn
    | JSOpb of js_opb
    | JSOpw of js_word_size => js_opw
    | JSShift of js_word_size => js_shift => int
    | JSEquality
    | JSOpapp`;

val js_lop_def = Hol_datatype `
  js_lop =
      JSAnd
    | JSOr`;

val js_exp_def = Hol_datatype `
  js_exp =
      JSLit of js_lit
    | JSApp of js_op => js_exp list
    | JSLog of js_lop => js_exp => js_exp
    | JSIf of js_exp => js_exp => js_exp`;

val _ = export_theory()

