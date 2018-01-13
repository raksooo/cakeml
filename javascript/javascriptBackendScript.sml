open preamble javascriptAstTheory javascriptSemanticsTheory astTheory stringTheory;

val _ = new_theory"javascriptBackend";

val apply_if_some_def = Define `
	(apply_if_some _ NONE = NONE) /\
	(apply_if_some f (SOME v) = SOME (f v))`;

val apply_if_some_list_def = Define `
	(apply_if_some_list _ NONE = NONE) /\
	(apply_if_some_list f (SOME v) = SOME [f v])`;

val ata_op_def = Define `
	ata_op op [a; b] =
		(JSApp (JSAFun ["a"; "b"] (JSBop op (JSVar "a") (JSVar "b"))) [a; b])`;

val ata_exp_def = tDefine "ata_exp" `
	(ata_exp [] = SOME []) /\
	(ata_exp (exp1::exp2::exps) = case ata_exp [exp1] of
		| SOME [jsexp] => (case ata_exp (exp2 :: exps) of
				| SOME jsexps => SOME (jsexp :: jsexps)
				| NONE => NONE)
		| NONE => NONE) /\
	(ata_exp [Lannot exp _] = ata_exp [exp]) /\
	(ata_exp [Var (Short name)] = SOME [JSVar name]) /\
	(ata_exp [Con (SOME (Short b)) _] = case b of
		| "true" => SOME [JSLit (JSBool T)]
		| "false" => SOME [JSLit (JSBool F)]) /\
	(ata_exp [App Opapp exps] =
		apply_if_some_list (\jsexps. JSApp (HD jsexps) (TL jsexps)) (ata_exp exps)) /\
	(ata_exp [Fun par exp] = apply_if_some_list ((JSAFun [par]) o HD) (ata_exp [exp])) /\
	(ata_exp [Let (SOME name) exp1 exp2] =
		apply_if_some_list (\es. JSApp (JSAFun ["a"] ((HD o TL) es)) [HD es]) (ata_exp [exp1; exp2])) /\
	(ata_exp [Log And exp1 exp2] = let exps = ata_exp [exp1; exp2]
		in apply_if_some_list (ata_op JSAnd) exps) /\
	(ata_exp [Log Or exp1 exp2] = let exps = ata_exp [exp1; exp2]
		in apply_if_some_list (ata_op JSOr) exps) /\
	(ata_exp _ = NONE)`
	(cheat);

val ata_dec_def = Define `
	(ata_dec (Dlet _ Pany exp) = apply_if_some_list (JSExp o HD) (ata_exp [exp])) /\
	(ata_dec (Dlet _ (Pvar name) exp) = apply_if_some_list ((JSLet name) o HD) (ata_exp [exp])) /\
	(ata_dec (Dletrec _ defs) = let
			exps = MAP (\(_, _, exp). exp) defs;
			zipped = apply_if_some (\jsexps. ZIP (defs, jsexps)) (ata_exp exps);
			replaced = apply_if_some (MAP (\((name, par, _), exp). (name, par, exp))) zipped;
			in apply_if_some (MAP (\(name, par, exp). JSLet name (JSAFun [par] exp))) replaced) /\
	(ata_dec _ = NONE)`;

val ata_top_def = Define `
	(ata_top (Tdec dec) = apply_if_some (MAP JSStm) (ata_dec dec)) /\
	(ata_top _ = NONE)`;

val ast_to_ast_def = Define `
	(ast_to_ast [] = SOME []) /\
	(ast_to_ast (top::tops) = case ata_top top of
		| SOME top' => (case ast_to_ast tops of
				| SOME tops' => SOME (top' ++ tops')
				| NONE => NONE)
		| NONE => NONE)`;

val _ = export_theory();

