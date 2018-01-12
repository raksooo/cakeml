open preamble;

val _ = new_theory"javascriptAst";

val js_varN_def = type_abbrev("js_varN", ``:string``);

val js_lit_def = Hol_datatype `
  js_lit =
    | JSInteger of int
    | JSString of string
		| JSBool of bool
		| JSNull`;

val js_binary_op_def = Hol_datatype `
  js_binary_op =
		| JSPlus | JSMinus | JSTimes | JSDivide | JSModulo
		| JSLt | JSGt | JSLeq | JSGeq
		| JSAnd | JSOr`;

val js_exp_def = Hol_datatype `
  js_exp =
    | JSLit of js_lit
    | JSBop of js_binary_op => js_exp => js_exp
		| JSVar of js_varN
		| JSAFun of js_varN list => js_exp
		| JSApp of js_exp => js_exp list`;

val js_stm_def = Hol_datatype `
	js_stm =
		| JSLet of js_varN => js_exp
		| JSExp of js_exp`;

val js_top_def = Hol_datatype `
	js_top =
		| JSStm of js_stm`;

val _ = type_abbrev( "js_prog" , ``: js_top list``);

val _ = export_theory()

