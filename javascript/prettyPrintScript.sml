open preamble javascriptAstTheory;

val _ = new_theory"prettyPrint";

val join_def = Define `
	(join [] = "") /\
	(join (s::[]) = s) /\
	(join (s::ss) = s ++ "," ++ join ss)`;

val lit_toString_def = tDefine "lit_to_string" `
	(lit_toString (JSBigInt n) = "bigInt(" ++ toString n ++ ")") /\
	(lit_toString (JSString s) = s) /\
	(lit_toString (JSBool T) = "true") /\
	(lit_toString (JSBool F) = "false") /\
	(lit_toString (JSNull) = "null") /\
	(lit_toString (JSArray lits) = "[" ++ join (MAP lit_toString lits) ++ "]")`
	cheat;

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

val exp_toString_def = tDefine "exp_toString" `
	(exp_toString (JSLit lit) = lit_toString lit) /\
	(exp_toString (JSAFun pars exp) =
      "(function(" ++ join pars ++ ") { return " ++ exp_toString exp ++ " })") /\
	(exp_toString (JSFun name pars exp) =
      "(function " ++ name ++ "(" ++ join pars ++ ") { return " ++ exp_toString exp ++ " })") /\
	(exp_toString (JSVar name) = name) /\
	(exp_toString (JSApp exp args) = let
				exp' = exp_toString exp;
				args' = MAP exp_toString args
			in exp' ++ "(" ++ join args' ++ ")") /\
	(exp_toString (JSBop op exp1 exp2) = "(" ++ bop_toString op
				(exp_toString exp1) (exp_toString exp2) ++ ")")`
	(cheat);

val stm_toString_def = Define `
	(stm_toString (JSExp exp) = exp_toString exp ++ ";") /\
	(stm_toString (JSLet name exp) = "let " ++ name ++ " = " ++ exp_toString exp ++ ";") /\
	(stm_toString (JSVarDecl name exp) = "var " ++ name ++ " = " ++ exp_toString exp ++ ";")`;

val stms_toString = Define `
	(stms_toString [] = "") /\
	(stms_toString (stm::stms) = stm_toString stm ++ stms_toString stms)`;

val prog_toString = Define `
	prog_toString prog = "const bigInt = require('./BigInteger.min.js');" ++ stms_toString prog`;

val _ = export_theory();

