open preamble;

val _ = new_theory"javascriptAst";

val js_varN_def = type_abbrev("js_varN", ``:string``);

val js_lit_def = Datatype `
  js_lit =
    | JSBigInt int
    | JSString string
		| JSBool bool
		| JSNull`;

val js_binary_op_def = Datatype `
  js_binary_op =
		| JSPlus | JSMinus | JSTimes | JSDivide | JSModulo
		| JSLt | JSGt | JSLeq | JSGeq | JSEq | JSNeq
		| JSAnd | JSOr`;

val js_exp_def = Datatype `
  js_exp =
    | JSLit js_lit
		| JSArray (js_exp list)
		| JSObjectCreate ((js_varN, js_exp) alist)
		| JSObjectAssign js_exp js_varN js_exp
		| JSObjectRetrieve js_exp js_varN
    | JSBop js_binary_op js_exp js_exp
		| JSVar js_varN
		| JSAFun (js_varN list) (js_exp list)
		| JSFun js_varN (js_varN list) (js_exp list)
		| JSApp js_exp (js_exp list)
		| JSTernary js_exp js_exp js_exp`;

val js_stm_def = Datatype `
	js_stm =
		| JSLet js_varN js_exp
		| JSVarDecl js_varN js_exp
		| JSExp js_exp`;

val _ = type_abbrev( "js_prog" , ``: js_stm list``);

val _ = export_theory()

