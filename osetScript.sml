open HolKernel boolLib bossLib BasicProvers Parse;
open optionTheory pairTheory stringTheory;
open arithmeticTheory pred_setTheory listTheory finite_mapTheory alistTheory sortingTheory;
open balanced_mapTheory comparisonTheory;
open lcsymtacs;

val _ = new_theory "oset";

val _ = temp_tight_equality ();

(* oset for ordered set *)
val _ = type_abbrev ("oset", ``:('a,unit) balanced_map``);

(* Basic definitions, that correspond directly to balanced tree operations *)
val good_oset_def = Define `
good_oset cmp (s:'a oset) ⇔ good_cmp cmp ∧ invariant cmp s`;

val oempty_def = Define `
oempty = empty:'a oset`;

val osingleton_def = Define `
osingleton v = singleton v ()`;

val oin_def = Define `
oin cmp (v:'a) (s:'a oset) ⇔  member cmp v s`;

val oinsert_def = Define `
oinsert cmp v s = insert cmp v () s`;

val odelete_def = Define `
odelete cmp (s:'a oset) (v:'a) = delete cmp v s`;

val ounion_def = Define `
ounion cmp (s1:'a oset) s2 = union cmp s1 s2`;

val oimage_def = Define `
oimage cmp f (s:'a oset) = map_keys cmp f s`;

val osubset_def = Define `
osubset cmp (s1:'a oset) (s2:'a oset) ⇔ isSubmapOf cmp s1 s2`;

val ocompare_def = Define `
ocompare cmp (s1:'a oset) (s2:'a oset) = compare (\(x,y) (x',y'). cmp x x') s1 s2`;

val oevery_def = Define `
oevery f (s:'a oset) ⇔  every (\x y. f x) s`;

val oexists_def = Define `
oexists f (s:'a oset) ⇔  exists (\x y. f x) s`;

(* operations preserve good_set *)

val good_oset_oempty = Q.store_thm ("good_oset_oempty",
`!cmp. good_cmp cmp ⇒ good_oset cmp oempty`,
 rw [empty_thm, good_oset_def, oempty_def]);

val good_oset_singleton = Q.store_thm ("good_oset_singleton",
`!cmp x. good_cmp cmp ⇒ good_oset cmp (osingleton x)`,
 rw [singleton_thm, good_oset_def, osingleton_def]);

val good_oset_oinsert = Q.store_thm ("good_oset_oinsert",
`!cmp s x. good_oset cmp s ⇒ good_oset cmp (oinsert cmp x s)`,
 rw [oinsert_def, good_oset_def] >>
 metis_tac [insert_thm]);

val good_oset_odelete = Q.store_thm ("good_oset_odelete",
`!cmp s x. good_oset cmp s ⇒ good_oset cmp (odelete cmp s x)`,
 rw [good_oset_def, odelete_def] >>
 metis_tac [delete_thm]);

val good_oset_ounion = Q.store_thm ("good_oset_ounion",
`!cmp s1 s2. good_oset cmp s1 ∧ good_oset cmp s2 ⇒ good_oset cmp (ounion cmp s1 s2)`,
 rw [good_oset_def, ounion_def] >>
 metis_tac [union_thm]);

val good_oset_oimage = Q.store_thm ("good_oset_oimage",
`!cmp f s. good_cmp cmp ⇒ good_oset cmp (oimage cmp f s)`,
 cheat);

val good_cmp_ocompare = Q.store_thm ("good_cmp_ocompare",
`!cmp f s. good_cmp cmp ⇒ good_cmp (ocompare cmp)`,
 rw [] >>
 `good_cmp (\(x,y:unit) (x',y':unit). cmp x x')` 
            by (rw [good_cmp_def, LAMBDA_PROD, FORALL_PROD] >>
                metis_tac [good_cmp_def]) >>
 imp_res_tac compare_thm >>
 pop_assum mp_tac >>
 pop_assum (fn _ => all_tac) >>
 pop_assum (fn _ => all_tac) >>
 rw [] >>
 rw [ocompare_def, good_cmp_def] >>
 metis_tac [good_cmp_def]);

(* How oin interacts with other operations *)

val oin_oempty = Q.store_thm ("oin_oinsert",
`!cmp x. oin cmp x oempty = F`,
 rw [oin_def, oempty_def, empty_def, member_def]); 

val oin_singleton = Q.store_thm ("oin_singleton",
`∀cmp x y. oin cmp x (osingleton y) ⇔ cmp x y = Equal`,
 rw [oin_def, osingleton_def, member_def, singleton_def] >>
 EVERY_CASE_TAC);

val oin_oinsert = Q.store_thm ("oin_oinsert",
`∀cmp x y s. good_oset cmp s ⇒ (oin cmp x (oinsert cmp y s) ⇔ cmp x y = Equal ∨ oin cmp x s)`,
 rw [good_oset_def, oin_def, oinsert_def] >>
 imp_res_tac insert_thm >>
 last_x_assum (qspecl_then [`()`, `y`] assume_tac) >>
 imp_res_tac member_thm >>
 rw [FLOOKUP_UPDATE] >>
 rfs [key_set_eq] >>
 metis_tac [good_cmp_def]);

val oin_odelete = Q.store_thm ("oin_odelete",
`!cmp s x y. good_oset cmp s ⇒ (oin cmp x (odelete cmp s y) ⇔ oin cmp x s ∧ cmp x y ≠ Equal)`,
 rw [oin_def, odelete_def] >>
 imp_res_tac good_oset_odelete >>
 pop_assum (qspecl_then [`y`] assume_tac) >>
 fs [good_oset_def, odelete_def] >>
 imp_res_tac delete_thm >>
 imp_res_tac member_thm >>
 rw [FDOM_DRESTRICT, key_set_eq] >>
 eq_tac >>
 rw []);

val oin_ounion = Q.store_thm ("oin_ounion",
`!cmp x s1 s2. good_oset cmp s1 ∧ good_oset cmp s2 ⇒ (oin cmp x (ounion cmp s1 s2) ⇔ oin cmp x s1 ∨ oin cmp x s2)`,
 rw [oin_def] >>
 `good_oset cmp (ounion cmp s1 s2)` by metis_tac [good_oset_ounion] >>
 fs [good_oset_def, ounion_def] >>
 imp_res_tac member_thm >>
 rw [] >>
 `to_fmap cmp (union cmp s1 s2) = to_fmap cmp s1 ⊌ to_fmap cmp s2` by metis_tac [union_thm] >>
 rw []);

val oin_oimage = Q.store_thm ("oin_oimage",
`!cmp y s f. good_cmp cmp ⇒ (oin cmp y (oimage cmp f s) ⇔ ?x. cmp y (f x) = Equal ∧ oin cmp x s)`,
 cheat);

val osubset_thm = Q.store_thm ("osubset_thm",
`!cmp s1 s2. good_oset cmp s1 ∧ good_oset cmp s2 ⇒ (osubset cmp s1 s2 ⇔ (!x. oin cmp x s1 ⇒ oin cmp x s2))`,
 cheat);

val oextension = Q.store_thm ("oextension",
`!cmp s1 s2. good_oset cmp s1 ∧ good_oset cmp s2 ⇒ (ocompare cmp s1 s2 = Equal ⇔ (!x. oin cmp x s1 ⇔ oin cmp x s2))`,
 cheat);

val oevery_oin = Q.store_thm ("oevery_oin",
`!cmp f s. 
  good_oset cmp s ∧
  (∀k1 k2. cmp k1 k2 = Equal ⇒ (f k1 ⇔ f k2))
  ⇒ 
  (oevery f s ⇔ (!x. oin cmp x s ⇒ f x))`,
 rw [good_oset_def, oevery_def, oin_def] >>
 `∀k1 (v:unit) k2 (v:unit). cmp k1 k2 = Equal ⇒ ((\x y. f x) k1 v ⇔ (\x y. f x) k2 v)` by metis_tac [] >>
 imp_res_tac every_thm >>
 rw [lookup_thm, flookup_thm, member_thm]);

val oexists_oin = Q.store_thm ("oexists_oin",
`!cmp f s. 
  good_oset cmp s ∧
  (∀k1 k2. cmp k1 k2 = Equal ⇒ (f k1 ⇔ f k2))
  ⇒ 
  (oexists f s ⇔ (?x. oin cmp x s ∧ f x))`,
 rw [good_oset_def, oexists_def, oin_def] >>
 `∀k1 (v:unit) k2 (v:unit). cmp k1 k2 = Equal ⇒ ((\x y. f x) k1 v ⇔ (\x y. f x) k2 v)` by metis_tac [] >>
 imp_res_tac exists_thm >>
 rw [lookup_thm, flookup_thm, member_thm]);

val _ = export_theory ();
