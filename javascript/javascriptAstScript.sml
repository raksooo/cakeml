open preamble;

val _ = new_theory"javascriptAst";

val js_varN_def = type_abbrev("js_varN", ``:string``);

val js_lit_def = Datatype `
  js_lit =
    | JSBigInt int
    | JSString string
		| JSBool bool
		| JSNull`;

val js_unary_op_def = Datatype `
	js_unary_op =
		| JSNeg`;

val js_binary_op_def = Datatype `
  js_binary_op =
		| JSPlus | JSMinus | JSTimes | JSDivide | JSModulo
		| JSLt | JSGt | JSLeq | JSGeq | JSEq | JSNeq
		| JSAnd | JSOr`;

val js_bind_element_def = Datatype `
	js_bind_element =
		| JSBVar js_varN
		| JSBObject ((js_varN, js_bind_element option) alist)
		| JSBArray (js_bind_element list)
		| JSBRest js_bind_element
		| JSBDiscard`;

val js_exp_def = Datatype `
  js_exp =
		| JSComma (js_exp list)
    | JSLit js_lit
		| JSArray (js_exp list)
		| JSRest js_exp
		| JSObjectCreate ((js_varN, js_exp option) alist)
		| JSObjectAssign js_exp js_varN js_exp
		| JSObjectRetrieve js_exp js_varN
    | JSUop js_unary_op js_exp
    | JSBop js_binary_op js_exp js_exp
		| JSVar js_varN
		| JSAFun (js_bind_element list) (js_stm list)
		| JSFun js_varN (js_bind_element list) (js_stm list)
		| JSApp js_exp (js_exp list)
		| JSConditional js_exp js_exp js_exp
		| JSClass (js_varN option) (js_varN option) ((js_varN # (js_varN list) # js_exp) list)
		| JSNew js_exp (js_exp list);

	js_stm =
		| JSBlock (js_stm list)
		| JSLet js_bind_element js_exp
		| JSConst js_bind_element js_exp
		| JSVarDecl js_bind_element js_exp
		| JSExp js_exp
		| JSIf js_exp js_stm js_stm
		| JSReturn js_exp
		| JSThrow js_exp
		| JSTryCatch (js_stm list) js_bind_element (js_stm list)`;

val _ = type_abbrev("js_prog", ``: js_stm list``);

val _ = export_theory()

