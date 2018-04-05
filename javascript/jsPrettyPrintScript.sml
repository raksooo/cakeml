open preamble jsAstTheory miscTheory;

val _ = new_theory"jsPrettyPrint";

val appendList_def = Define `
	appendList = FOLDL SmartAppend Nil`;

val join_def = Define `
	(join _ [] = Nil) /\
	(join _ (s::[]) = s) /\
	(join c (s::ss) = appendList [s; List c; join c ss])`;

val appendStringList_def = Define `
	appendStringList = appendList o MAP List`;

val lit_toString_def = Define `
	(lit_toString (JSBigInt n) = appendStringList ["bigInt('"; toString n; "')"]) /\
	(lit_toString (JSString s) = appendStringList ["'"; s; "'"]) /\
	(lit_toString (JSBool T) = List "true") /\
	(lit_toString (JSBool F) = List "false") /\
	(lit_toString (JSNull) = List "null")`;

val uop_toString_def = Define `
  (uop_toString JSNew a = appendList [List "new "; a]) /\
  (uop_toString JSNeg a = appendList [List "!"; a]) /\
  (uop_toString JSSpread a = appendList [List "..."; a])`;

val bop_toString_def = Define `
  (bop_toString JSPlus a b = appendList [a; List "+"; b]) /\
  (bop_toString JSMinus a b = appendList [a; List "-"; b]) /\
  (bop_toString JSTimes a b = appendList [a; List "*"; b]) /\
  (bop_toString JSDivide a b = appendList [a; List "/"; b]) /\
  (bop_toString JSModulo a b = appendList [a; List "%"; b]) /\
  (bop_toString JSLt a b = appendList [a; List "<"; b]) /\
  (bop_toString JSLeq a b = appendList [a; List "<="; b]) /\
  (bop_toString JSGt a b = appendList [a; List ">"; b]) /\
  (bop_toString JSGeq a b = appendList [a; List ">="; b]) /\
	(bop_toString JSAnd a b = appendList [a; List " && "; b]) /\
	(bop_toString JSOr a b = appendList [a; List " || "; b]) /\
	(bop_toString JSEq a b = appendList [List "cmljs_eq("; a; List ", "; b; List ")"]) /\
	(bop_toString JSNeq a b = appendList [List "!cmljs_eq("; a; List ", "; b; List ")"]) /\
  (bop_toString JSComma a b = appendList [a; List ","; b]) /\
	(bop_toString JSIntPlus a b = appendList [a; List ".add("; b; List ")"]) /\
	(bop_toString JSIntMinus a b = appendList [a; List ".subtract("; b; List ")"]) /\
	(bop_toString JSIntTimes a b = appendList [a; List ".multiply("; b; List ")"]) /\
	(bop_toString JSIntDivide a b = appendList [a; List ".divide("; b; List ")"]) /\
	(bop_toString JSIntModulo a b = appendList [a; List ".mod("; b; List ")"]) /\
	(bop_toString JSIntLt a b = appendList [a; List ".lesser("; b; List ")"]) /\
	(bop_toString JSIntLeq a b = appendList [a; List ".lesserOrEquals("; b; List ")"]) /\
	(bop_toString JSIntGt a b = appendList [a; List ".greater("; b; List ")"]) /\
	(bop_toString JSIntGeq a b = appendList [a; List ".greaterOrEquals("; b; List ")"])`;

val bindElement_toString_def = tDefine "bindElement_toString" `
	(bindElement_toString (JSBVar name) = List name) /\
	(bindElement_toString (JSBObject props) = let
			props' = MAP
				(\(p, be). appendList
					[List p; if IS_SOME be then appendList [List ": "; bindElement_toString (THE be)] else Nil])
				props
		in appendList [List "{"; join "," props'; List "}"]) /\
	(bindElement_toString (JSBArray l) = let
      bets = MAP bindElement_toString l
    in appendList [List "["; join "," bets; List "]"]) /\
	(bindElement_toString (JSBRest b) = appendList [List "..."; bindElement_toString b])`
	cheat;

val toString_defn = Defn.Hol_multi_defns `
	(exp_toString (JSLit lit) = lit_toString lit) /\
	(exp_toString (JSArray exps) = appendList [List "["; join "," (MAP exp_toString exps); List "]"]) /\
	(exp_toString (JSIndex exp n) =
		appendList [exp_toString exp; List "["; exp_toString n; List "]"]) /\
	(exp_toString (JSAFun pars body) = appendList [List "(function(";
			join "," (MAP bindElement_toString pars); List ") { "; stms_toString body; List " })"]) /\
	(exp_toString (JSFun name pars body) = appendList [List "(function "; List name; List "(";
			join "," (MAP bindElement_toString pars); List ") { "; stms_toString body; List " })"]) /\
	(exp_toString (JSVar name) = List name) /\
	(exp_toString (JSConditional condition ifexp elseexp) = appendList [List "("; exp_toString condition;
			List " ? "; exp_toString ifexp; List " : "; exp_toString elseexp; List ")"]) /\
	(exp_toString (JSApp exp args) = let
				exp' = exp_toString exp;
				args' = MAP exp_toString args
			in appendList [exp'; List "("; join "," args'; List ")"]) /\
	(exp_toString (JSObject decls) = let 
				props = MAP
					(\(p, exp). Append (List p)
						(if IS_SOME exp then Append (List ": ") (exp_toString (THE exp)) else Nil))
					decls
			in appendList [List "({"; join "," props; List "})"]) /\
	(exp_toString (JSObjectProp exp prop) = appendList [exp_toString exp; List "."; List prop]) /\
	(exp_toString (JSAssign exp1 exp2) = appendList [
			exp_toString exp1; List " = "; exp_toString exp2]) /\
	(exp_toString (JSUop op exp) = uop_toString op (exp_toString exp)) /\
	(exp_toString (JSBop op exp1 exp2) = appendList [List "(";
			bop_toString op (exp_toString exp1) (exp_toString exp2); List ")"]) /\
	(exp_toString (JSClass name extends methods) = let
			name' = if IS_SOME name then appendStringList [" "; THE name] else Nil;
			extends' = if IS_SOME extends then appendStringList [" extends "; THE extends] else Nil;
			methods' = MAP
				(\m. appendList [List (FST m); List "("; join "," (MAP List (FST (SND m))); List ") { ";
					stm_toString (SND (SND m)); List " }"])
				methods
		in appendList [List "class"; name'; extends'; List " {"; join " " methods'; List "}"]) /\
	(exp_toString (Exp_not_compiled _) = List "Expression not supported by compiler") /\

  (stm_toString (JSBlock stms) = appendList [List "{ "; stms_toString stms; List " }"]) /\
	(stm_toString (JSExp exp) = appendList [exp_toString exp; List ";"]) /\
	(stm_toString (JSLet name exp) = appendList [
		List "let "; bindElement_toString name; List " = "; exp_toString exp; List ";"]) /\
	(stm_toString (JSConst name exp) = appendList [
		List "const "; bindElement_toString name; List " = "; exp_toString exp; List ";"]) /\
	(stm_toString (JSVarDecl name exp) = appendList [
		List "var "; bindElement_toString name; List " = "; exp_toString exp; List ";"]) /\
	(stm_toString (JSIf condition stm1 stm2) = appendList [List "if ("; exp_toString condition;
		List ") "; stm_toString stm1; List " else "; stm_toString stm2]) /\
	(stm_toString (JSThrow exp) = appendList [List "throw "; exp_toString exp; List ";"]) /\
  (stm_toString (JSReturn exp) = appendList [List "return "; exp_toString exp; List ";"]) /\
  (stm_toString (JSTryCatch try bind catch) = appendList [List "try { "; stms_toString try;
    List " } catch("; bindElement_toString bind; List ") { "; stms_toString catch; List " }"]) /\
  (stm_toString JSEmpty = List ";") /\
	(stm_toString (Dec_not_compiled _) = List "Declaration not supported by compiler") /\
	(stm_toString (Top_not_compiled _) = List "Top not supported by compiler") /\

	(stms_toString [] = Nil) /\
	(stms_toString (stm::stms) = Append (stm_toString stm) (stms_toString stms))`;

val _ = Lib.with_flag (computeLib.auto_import_definitions, false) (List.map Defn.save_defn) toString_defn;
val exp_toString_def = fetch "-" "exp_toString_def";

val prog_toString = Define `
	prog_toString prog = append_aux (stms_toString prog) ""`;

val _ = export_theory();

