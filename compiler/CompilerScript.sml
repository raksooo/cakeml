(*Generated by Lem from compiler.lem.*)
open bossLib Theory Parse res_quanTheory
open fixedPointTheory finite_mapTheory listTheory pairTheory pred_setTheory
open integerTheory set_relationTheory sortingTheory stringTheory wordsTheory

val _ = numLib.prefer_num();



open ToBytecodeTheory ToIntLangTheory IntLangTheory CompilerPrimitivesTheory BytecodeTheory PrinterTheory CompilerLibTheory SemanticPrimitivesTheory AstTheory LibTheory

val _ = new_theory "Compiler"

(*open SemanticPrimitives*)
(*open Ast*)
(*open CompilerLib*)
(*open IntLang*)
(*open ToIntLang*)
(*open ToBytecode*)
(*open Bytecode*)

val _ = type_abbrev( "contab" , ``: (( ( conN id)option), num)fmap # (num # ( conN id) option) list # num``);
(*val cmap : contab -> Pmap.map (option (id conN)) num*)
 val cmap_def = Define `
 (cmap (m,_,_) = m)`;


val _ = Hol_datatype `
 compiler_state =
  <| contab : contab
   ; renv : (string # num) list
   ; rmenv : (string, ( (string # num)list))fmap
   ; rsz : num
   ; rnext_label : num
   |>`;


(*val cpam : compiler_state -> list (num * option (id conN))*)
 val cpam_def = Define `
 (cpam s = ((case s.contab of (_,w,_) => w )))`;


val _ = Define `
 init_compiler_state =  
(<| contab := ( FUPDATE FEMPTY ( NONE, tuple_cn)
              ,[(tuple_cn,NONE)]
              ,1)
   ; renv := []
   ; rmenv := FEMPTY
   ; rsz := 0
   ; rnext_label := 0
   |>)`;


 val number_constructors_defn = Hol_defn "number_constructors" `

(number_constructors _ [] ct = ct)
/\
(number_constructors mn ((c,_)::cs) (m,w,n) =  
(number_constructors mn cs ( FUPDATE  m ( (SOME (mk_id mn c)), n), ((n,SOME (mk_id mn c)) ::w), (n +1))))`;

val _ = Lib.with_flag (computeLib.auto_import_definitions, false) Defn.save_defn number_constructors_defn;

 val dec_to_contab_def = Define `

(dec_to_contab mn ct (Dtype ts) = ( FOLDL (\ct p . 
  (case (ct ,p ) of ( ct , (_,_,cs) ) => number_constructors mn cs ct )) ct ts))
/\
(dec_to_contab _ ct _ = ct)`;


 val decs_to_contab_defn = Hol_defn "decs_to_contab" `

(decs_to_contab _ ct [] = ct)
/\
(decs_to_contab mn ct (d::ds) = (decs_to_contab mn (dec_to_contab mn ct d) ds))`;

val _ = Lib.with_flag (computeLib.auto_import_definitions, false) Defn.save_defn decs_to_contab_defn;

 val compile_news_defn = Hol_defn "compile_news" `

(compile_news cs _ [] = ( emit cs [Stack Pop]))
/\
(compile_news cs i (_::vs) =  
(let cs = ( emit cs ( MAP Stack [Load 0; Load 0; El i])) in
  let cs = ( emit cs [Stack (Store 1)]) in
  compile_news cs (i +1) vs))`;

val _ = Lib.with_flag (computeLib.auto_import_definitions, false) Defn.save_defn compile_news_defn;

val _ = Define `
 (compile_Cexp menv env rsz cs Ce =  
(let (Ce,nl) = ( label_closures ( LENGTH env) cs.next_label Ce) in
  let cs = ( compile_code_env menv ( cs with<| next_label := nl |>) Ce) in
  compile menv env TCNonTail rsz cs Ce))`;


val _ = Define `
 (compile_fake_exp menv m env rsz cs vs e =  
(let Ce = ( exp_to_Cexp m (e (Con NONE ( MAP (\ v . Var (Short v)) ( REVERSE vs))))) in
  compile_Cexp menv env rsz cs Ce))`;


 val compile_dec_def = Define `

(compile_dec _ _ _ _ cs (Dtype _) = (NONE, emit cs [Stack (Cons (block_tag +tuple_cn) 0)]))
/\
(compile_dec menv m env rsz cs (Dletrec defs) =  
(let vs = ( MAP (\p . 
  (case (p ) of ( (n,_,_) ) => n )) defs) in
  (SOME vs, compile_fake_exp menv m env rsz cs vs (\ b . Letrec defs b))))
/\
(compile_dec menv m env rsz cs (Dlet p e) =  
(let vs = ( pat_bindings p []) in
  (SOME vs, compile_fake_exp menv m env rsz cs vs (\ b . Mat e [(p,b)]))))`;


 val compile_decs_defn = Hol_defn "compile_decs" `

(compile_decs _ _ ct m _ rsz cs [] = (ct,m,rsz,cs))
/\
(compile_decs mn menv ct m env rsz cs (dec::decs) =  
(let (vso,cs) = ( compile_dec menv m env rsz cs dec) in
  let ct = ( dec_to_contab mn ct dec) in
  let vs = ((case vso of NONE => [] | SOME vs => vs )) in
  let n = ( LENGTH vs) in
  let m = (( m with<| cnmap := cmap ct; bvars := vs ++m.bvars |>)) in
  let env = (( GENLIST(\ i . CTDec (rsz +n - 1 - i))n) ++env) in
  let rsz = (rsz +n) in
  let cs = ( compile_news cs 0 vs) in
  compile_decs mn menv ct m env rsz cs decs))`;

val _ = Lib.with_flag (computeLib.auto_import_definitions, false) Defn.save_defn compile_decs_defn;

val _ = Define `
 (compile_decs_wrap mn rs decs =  
(let cs = (<| out := []; next_label := rs.rnext_label |>) in
  let cs = ( emit cs [PushPtr (Addr 0); PushExc]) in
  let menv = ( (o_f) ( MAP SND) rs.rmenv) in
  let m = (<| bvars := ( MAP FST rs.renv)
           ; mvars := ( (o_f) ( MAP FST) rs.rmenv)
           ; cnmap := ( cmap rs.contab)
           |>) in
  let env = ( MAP ((o) CTDec SND) rs.renv) in
  let (ct,m,rsz,cs) = ( compile_decs mn menv rs.contab m env (rs.rsz +2) cs decs) in
  let n = (rsz - 2 - rs.rsz) in
  let news = ( TAKE n m.bvars) in
  let cs = ( emit cs [Stack (Cons tuple_cn n)]) in
  let cs = ( emit cs [PopExc; Stack(Pops 1)]) in
  let cs = ( compile_news cs 0 news) in
  let env = ( ZIP ( news, ( GENLIST (\ i . rs.rsz +n - 1 - i) n))) in
  (ct,env,cs)))`;


 val compile_print_vals_defn = Hol_defn "compile_print_vals" `

(compile_print_vals _ [] s = s)
/\
(compile_print_vals n (v::vs) s =  
(let s = ( emit s ( MAP PrintC (EXPLODE (CONCAT ["val ";v;" = "])))) in
  let s = ( emit s [Stack(Load n); Print]) in
  compile_print_vals (n +1) vs s))`;

val _ = Lib.with_flag (computeLib.auto_import_definitions, false) Defn.save_defn compile_print_vals_defn;

 val compile_print_ctors_defn = Hol_defn "compile_print_ctors" `

(compile_print_ctors [] s = s)
/\
(compile_print_ctors ((c,_)::cs) s =  
(compile_print_ctors cs
    (emit s ( MAP PrintC (EXPLODE (CONCAT [c;" = <constructor>"]))))))`;

val _ = Lib.with_flag (computeLib.auto_import_definitions, false) Defn.save_defn compile_print_ctors_defn;

 val compile_print_types_defn = Hol_defn "compile_print_types" `

(compile_print_types [] s = s)
/\
(compile_print_types ((_,_,cs)::ts) s =  
(compile_print_types ts (compile_print_ctors cs s)))`;

val _ = Lib.with_flag (computeLib.auto_import_definitions, false) Defn.save_defn compile_print_types_defn;

 val compile_print_dec_def = Define `

(compile_print_dec (Dtype ts) s = ( compile_print_types ts s))
/\
(compile_print_dec (Dlet p e) s =  
(
  compile_print_vals 0 (pat_bindings p []) s))
/\
(compile_print_dec (Dletrec defs) s =  
(
  compile_print_vals 0 ( MAP (\p . 
  (case (p ) of ( (n,_,_) ) => n )) defs) s))`;


 val compile_top_def = Define `

(compile_top rs (Tmod mn _ decs) =  
(let (ct,env,cs) = ( compile_decs_wrap (SOME mn) rs decs) in
  let str = ( CONCAT["structure ";mn;" = <structure>"]) in
  (( rs with<|
      contab := ct
    ; rnext_label := cs.next_label
    ; rmenv := FUPDATE  rs.rmenv ( mn, env)
    ; rsz := rs.rsz + LENGTH env |>)
  ,( rs with<|
      contab := ct
    ; rnext_label := cs.next_label
    |>)
  ,(emit cs ( MAP PrintC (EXPLODE str))).out)))
/\
(compile_top rs (Tdec dec) =  
(let (ct,env,cs) = ( compile_decs_wrap NONE rs [dec]) in
  (( rs with<|
      contab := ct
    ; rnext_label := cs.next_label
    ; renv := env ++rs.renv
    ; rsz := rs.rsz + LENGTH env |>)
  ,( rs with<|
      contab := ct
    ; rnext_label := cs.next_label |>)
  ,(compile_print_dec dec cs).out)))`;

val _ = export_theory()

