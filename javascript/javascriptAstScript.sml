open preamble;

val _ = new_theory"javascriptAst";

val js_varN_def = type_abbrev("js_varN", ``:string``);

val js_lit_def = Datatype `
  js_lit =
    | JSInteger int
    | JSString string
		| JSBool bool
		| JSNull`;

val js_binary_op_def = Datatype `
  js_binary_op =
		| JSPlus | JSMinus | JSTimes | JSDivide | JSModulo
		| JSLt | JSGt | JSLeq | JSGeq
		| JSAnd | JSOr`;

val js_exp_def = Datatype `
  js_exp =
    | JSLit js_lit
    | JSBop js_binary_op js_exp js_exp
		| JSVar js_varN
		| JSAFun (js_varN list) js_exp
		| JSApp js_exp (js_exp list)`;

val js_stm_def = Datatype `
	js_stm =
		| JSLet js_varN js_exp
		| JSExp js_exp`;

val _ = type_abbrev( "js_prog" , ``: js_stm list``);

val _ = export_theory()

