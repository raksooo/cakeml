open preamble javascriptAstTheory;

val _ = new_theory"prettyPrint";

val join_def = Define `
	(join _ [] = "") /\
	(join _ (s::[]) = s) /\
	(join c (s::ss) = s ++ c ++ join c ss)`;

val lit_toString_def = Define `
	(lit_toString (JSBigInt n) = "bigInt(" ++ toString n ++ ")") /\
	(lit_toString (JSString s) = "'" ++ s ++ "'" ) /\
	(lit_toString (JSBool T) = "true") /\
	(lit_toString (JSBool F) = "false") /\
	(lit_toString (JSNull) = "null")`;

val bop_toString_def = Define `
	(bop_toString JSPlus a b = a ++ ".add(" ++ b ++ ")") /\
	(bop_toString JSMinus a b = a ++ ".subtract(" ++ b ++ ")") /\
	(bop_toString JSTimes a b = a ++ ".multiply(" ++ b ++ ")") /\
	(bop_toString JSDivide a b = a ++ ".divide(" ++ b ++ ")") /\
	(bop_toString JSLt a b = a ++ ".lesser(" ++ b ++ ")") /\
	(bop_toString JSLeq a b = a ++ ".lesserOrEquals(" ++ b ++ ")") /\
	(bop_toString JSGt a b = a ++ ".greater(" ++ b ++ ")") /\
	(bop_toString JSGeq a b = a ++ ".greaterOrEquals(" ++ b ++ ")") /\
	(bop_toString JSAnd a b = a ++ " && " ++ b) /\
	(bop_toString JSOr a b = a ++ " || " ++ b)`;

val bindElement_toString_def = tDefine "bindElement_toString" `
	(bindElement_toString (JSBDiscard) = "cmlg__") /\
	(bindElement_toString (JSBVar name) = name) /\
	(bindElement_toString (JSBObject props) = "{" ++ join "," (MAP
			(\(p, be). p ++ if IS_SOME be then ": " ++ bindElement_toString (THE be) else "")
		props) ++ "}") /\
	(bindElement_toString (JSBArray l) = let
      bets = (\e. if e = JSBDiscard then "" else bindElement_toString e)
    in "[" ++ join "," (MAP bets l) ++ "]") /\
	(bindElement_toString (JSBRest b) = "..." ++ bindElement_toString b)`
	cheat;

val exp_toString_def = tDefine "exp_toString" `
	(exp_toString (JSLit lit) = lit_toString lit) /\
	(exp_toString (JSComma exps) = "(" ++ join "," (MAP exp_toString exps) ++ ")") /\
	(exp_toString (JSArray exps) = "[" ++ join "," (MAP exp_toString exps) ++ "]") /\
	(exp_toString (JSRest exp) = "..." ++ exp_toString exp) /\
	(exp_toString (JSAFun pars exp) = "(function(" ++
			join "," (MAP bindElement_toString pars) ++ ") { return " ++ exp_toString exp ++ " })") /\
	(exp_toString (JSFun name pars exp) = "(function " ++ name ++ "(" ++
			join "," (MAP bindElement_toString pars) ++ ") { return " ++ exp_toString exp ++ " })") /\
	(exp_toString (JSVar name) = name) /\
	(exp_toString (JSConditional condition ifexp elseexp) = "(" ++ exp_toString condition ++
			" ? " ++ exp_toString ifexp ++ " : " ++ exp_toString elseexp ++ ")") /\
	(exp_toString (JSApp exp args) = let
				exp' = exp_toString exp;
				args' = MAP exp_toString args
			in exp' ++ "(" ++ join "," args' ++ ")") /\
	(exp_toString (JSObjectCreate decls) = "({" ++ join "," (MAP
				(\(p, exp). p ++ if IS_SOME exp then ": " ++ exp_toString (THE exp) else "")
			decls) ++ "})") /\
	(exp_toString (JSObjectRetrieve exp prop) = exp_toString exp ++ "." ++ prop) /\
	(exp_toString (JSObjectAssign exp1 prop exp2) =
			exp_toString exp1 ++ "." ++ prop ++ " = " ++ exp_toString exp2) /\
	(exp_toString (JSBop op exp1 exp2) = "(" ++ bop_toString op
				(exp_toString exp1) (exp_toString exp2) ++ ")") /\
	(exp_toString (JSClass name extends methods) = let
			name' = if IS_SOME name then " " ++ THE name else "";
			extends' = if IS_SOME extends then " extends " ++ THE extends else "";
			methods' = MAP
				(\m. FST m ++ "(" ++ join "," (FST (SND m)) ++ ") { " ++ exp_toString (SND (SND m)) ++ " }")
				methods
		in "class" ++ name' ++ extends' ++ " {" ++ join " " methods' ++ "}") /\
	(exp_toString (JSNew class fields) = "(new " ++ exp_toString class ++ "(" ++ join "," (MAP exp_toString fields) ++ "))")`
	cheat;

val stm_toString_def = Define `
	(stm_toString (JSExp exp) = exp_toString exp ++ ";") /\
	(stm_toString (JSLet name exp) =
		"let " ++ bindElement_toString name ++ " = " ++ exp_toString exp ++ ";") /\
	(stm_toString (JSConst name exp) =
		"const " ++ bindElement_toString name ++ " = " ++ exp_toString exp ++ ";") /\
	(stm_toString (JSVarDecl name exp) =
		"var " ++ bindElement_toString name ++ " = " ++ exp_toString exp ++ ";") /\
	(stm_toString (JSIf condition stm1 stm2) = "if (" ++ exp_toString condition ++ ") " ++
		stm_toString stm1 ++ " else " ++ stm_toString stm2) /\
	(stm_toString (JSThrow exp) = "throw " ++ exp_toString exp ++ ";")`;

val stms_toString = Define `
	(stms_toString [] = "") /\
	(stms_toString (stm::stms) = stm_toString stm ++ stms_toString stms)`;

val prog_toString = Define `
	prog_toString prog = stms_toString prog`;

val _ = export_theory();

