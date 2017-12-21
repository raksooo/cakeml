open preamble;

val _ = new_theory"javascriptAst";

val js_lit_def = Hol_datatype `
  js_lit =
      JSIntLit of int
    | JSStrLit of string
		| JSBool of bool`;

val js_opn_def = Hol_datatype `
  js_opn = JSPlus | JSMinus | JSTimes | JSDivide | JSModulo`;

val js_opb_def = Hol_datatype `
  js_opc = JSLt | JSGt | JSLeq | JSGeq`;

val js_lop_def = Hol_datatype `
  js_opb = JSAnd | JSOr`;

val js_op_def = Hol_datatype `
  js_op =
      JSOpb of js_opb
    | JSOpn of js_opn
    | JSOpc of js_opc
    | JSOpapp`;

val js_exp_def = Hol_datatype `
  js_exp =
      JSLit of js_lit
    | JSApp of js_op => js_exp list`;

val js_stm_def = Hol_datatype `
	js_stm =
			JSLet of string => js_exp
		| JSExp of js_exp`;

val js_top_def = Hol_datatype `
	js_top =
			JSStm of js_stm`;

val _ = type_abbrev( "js_prog" , ``: js_top list``);

val _ = export_theory()

