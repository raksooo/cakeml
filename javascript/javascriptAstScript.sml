open preamble;

val _ = new_theory"javascriptAst";

val js_varN_def = type_abbrev("js_varN", ``:string``);

val js_lit_def = Hol_datatype `
  js_lit =
    | JSIntLit of int
    | JSStrLit of string
		| JSBool of bool
		| JSNull`;

val js_opn_def = Hol_datatype `
  js_opn = JSPlus | JSMinus | JSTimes | JSDivide | JSModulo`;

val js_opc_def = Hol_datatype `
  js_opc = JSLt | JSGt | JSLeq | JSGeq`;

val js_opb_def = Hol_datatype `
  js_opb = JSAnd | JSOr`;

val js_op_def = Hol_datatype `
  js_op =
      JSOpb of js_opb
    | JSOpn of js_opn
    | JSOpc of js_opc`;

val js_exp_def = Hol_datatype `
  js_exp =
      JSLit of js_lit
    | JSOp of js_op => js_exp => js_exp
		| JSVar of js_varN
		| JSFun of js_varN => js_exp
		| JSApp of js_exp => js_exp`;

val js_stm_def = Hol_datatype `
	js_stm =
			JSLet of js_varN => js_exp
		| JSExp of js_exp`;

val js_top_def = Hol_datatype `
	js_top =
			JSStm of js_stm`;

val _ = type_abbrev( "js_prog" , ``: js_top list``);

val _ = export_theory()

