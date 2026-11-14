(** * Soundness (paper: Typing Rules as Programs, "Soundness by typing", "Soundness by values").

    Sound abstractors and sound declarations ([abstractor_sound_by_typing],
    [ontology_sound]), and evaluation preserves typing
    ([evaluation_preserves_typing]).  The wrapper lemmas used by the
    soundness of the IsNamed family ([is_named_value_typing], [declared_wrapper],
    ...) are here too, although the paper explains them with Type-Directed Conditionals.

    Build order: this file precedes booleans.v, because the boolean
    abstractor is proved sound with the framework defined
    here ([plain_clause_sound_for], [extend_intro_sound_by_typing]). *)


(** Preservation is proved by strong induction on the height of the
    evaluation of type application; the height-indexed evaluation [evaln]
    and the height-aware inversions of the recursive clauses come first. *)
From Stdlib Require Import Arith Lia.
From TreeTyping Require Import tree.
From TreeTyping Require Import typing.
From TreeTyping Require Import typing.
From Stdlib Require Import String.
Open Scope string_scope.
Local Abbreviation app := typing.type_app.
Local Abbreviation inf := typing.infer.
Set Default Proof Using "Type".

(* ================================================================== *)
(** * Declarations

    A family at a nametag [N] is an abstractor [AI @ N ==> D] (typing.v):
    a program mapping each carrier type [C] of the family to its
    eliminator, [D @ C ==> Sm E], and refusing other carriers,
    [D @ C ==> Lf].  Type application applies the abstractor to the
    carrier type.  Eliminators are typically built as ['wait[E,X]] from an
    eliminator program [E] and parameters [X], so ['wait[E,X] @ U] behaves
    as [E @ X @r U].
    A nametag without a family is refused: the declarations answer
    [refusal = 'K1 Lf], which refuses every carrier type.  Parameters with
    several components use the default tupling, the Church pair [A '* B]. *)
(* ================================================================== *)

(** The eliminator ['wait[E,X]] passes its argument to [E] after [X]. *)
Lemma wait_elim : forall E X U V,
  E @ X @r U ==> V -> 'wait[E,X] @ U ==> V.
Proof. intros; apply wait_eval; assumption. Qed.

Lemma wait_elim_inv : forall E X U V,
  'wait[E,X] @ U ==> V -> E @ X @r U ==> V.
Proof. intros; apply wait_eval_inv; assumption. Qed.


(** ** Accessors

    Paths to the components of ['wait[E,X]].  The general machinery ([dir], [path_prog],
    [path_fn], [path_arg], [path_pB], [acc_arg], [acc_pB], [ceqb],
    [equal1_bt_case]) is in typing.v, where the function family uses it. *)


(** ** The refusal *)

(** The refusal refuses every carrier type. *)

Lemma refusal_eval : forall a C, refusal @ a @r C ==> Lf.
Proof. intros; unfold refusal; evaluate. Qed.


(** ** The default tupling *)


(** The default tupling: the parameters [A] and [B] form the Church pair
    [A '* B].  Its components are read by the accessors [acc_arg] and
    [acc_pB]. *)

Ltac fam_atom :=
  match goal with
  | |- eval ?e _ =>
      tryif has_evar e then fail else
      first [ eassumption | apply equal_eval | apply equal1_bt
            | apply acc_arg_eval | apply acc_pB_eval ]
  end.
Ltac fam_eval :=
  first [ fam_atom | evaluate_expr_core fam_eval fam_head | idtac ]
with fam_head :=
  first [ fam_atom | evaluate_head_core fam_eval | idtac ].


(** * Height-indexed evaluation

    [evaln n e v] has the rules of [eval]; each rule concludes at height
    [S n] from premises of height [n]. *)
Inductive evaln : nat -> Application -> Combination -> Prop :=
| evaln_appl : forall n d u w v,
    evaln n d w -> evaln n (w @ u) v -> evaln (S n) (d @r u) v
| evaln_to_stem : forall n u,
    evaln (S n) (Lf @ u) (Sm u)
| evaln_to_fork : forall n a u,
    evaln (S n) (Sm a @ u) (Fk a u)
| evaln_k : forall n a u,
    evaln (S n) (Fk Lf a @ u) a
| evaln_s : forall n g f u a b v,
    evaln n (g @ u) a -> evaln n (f @ u) b -> evaln n (a @ b) v ->
    evaln (S n) (Fk (Sm g) f @ u) v
| evaln_leaf : forall n f0 f1 f2,
    evaln (S n) ('triage [f0, f1, f2] @ Lf) f0
| evaln_stem : forall n f0 f1 f2 u v,
    evaln n (f1 @ u) v ->
    evaln (S n) ('triage [f0, f1, f2] @ Sm u) v
| evaln_fork : forall n f0 f1 f2 x y v,
    evaln n (f2 @ x @r y) v ->
    evaln (S n) ('triage [f0, f1, f2] @ Fk x y) v.

Lemma evaln_mono : forall n e v, evaln n e v ->
  forall m, n <= m -> evaln m e v.
Proof.
  intros n e v H; induction H; intros m Hm;
    (destruct m as [|m]; [lia|]);
    econstructor; try apply IHevaln; try apply IHevaln1; try apply IHevaln2;
    try apply IHevaln3; lia.
Qed.

Lemma evaln_eval : forall n e v, evaln n e v -> e ==> v.
Proof. intros n e v H; induction H; econstructor; eauto. Qed.

Lemma eval_evaln : forall e v, e ==> v -> exists n, evaln n e v.
Proof.
  intros e v H; induction H;
    repeat match goal with H : exists _, _ |- _ => destruct H end;
    try (exists 1; constructor; fail).
  all: first
    [ match goal with H1 : evaln ?a _ _, H2 : evaln ?b _ _, H3 : evaln ?c _ _ |- _ =>
        exists (S (a + b + c)); econstructor; eapply evaln_mono; eauto; lia end
    | match goal with H1 : evaln ?a _ _, H2 : evaln ?b _ _ |- _ =>
        exists (S (a + b)); econstructor; eapply evaln_mono; eauto; lia end
    | match goal with H1 : evaln ?a _ _ |- _ => exists (S a); constructor; exact H1 end ].
Qed.

(** Invert height-indexed evaluations whose application shape determines
    the rule, as [invert_eval] does for [eval]. *)
Ltac invert_evaln :=
  repeat match goal with
  | H : evaln _ (_ @r _) _ |- _ => inv_out H
  | H : evaln _ (Lf @ _) _ |- _ => inv_out H
  | H : evaln _ (Sm _ @ _) _ |- _ => inv_out H
  | H : evaln _ (Fk Lf _ @ _) _ |- _ => inv_out H
  | H : evaln _ (Fk (Sm _) _ @ _) _ |- _ => inv_out H
  | H : evaln _ (Fk (Fk _ _) _ @ _) _ |- _ => inv_out H
  end.

Lemma evaln_lt : forall a k e v, evaln a e v -> a <= k -> evaln k e v.
Proof. intros; eapply evaln_mono; eauto. Qed.

Lemma evaln_appl_pred : forall k d u w v,
  0 < k -> evaln (pred k) d w -> evaln (pred k) (w @ u) v ->
  evaln k (d @r u) v.
Proof. intros; destruct k; [lia|]; apply evaln_appl with (w := w); assumption. Qed.

(** Close a goal [evaln k e v] from height-indexed premises in context:
    either a premise for [e] itself, or a reassembly of an application
    whose second premise determines the intermediate value. *)
Ltac evaln_close :=
  first
  [ match goal with H : evaln ?a ?e ?v |- evaln ?k ?e ?v =>
      apply (evaln_lt a k e v H); lia end
  | match goal with
    | |- evaln ?k (?d @r ?u) ?v =>
        match goal with H2 : evaln ?b (?w @ u) ?v' |- _ =>
          unify v v';
          apply (evaln_appl_pred k d u w v);
          [lia|evaln_close|apply (evaln_lt b _ _ _ H2); lia] end
    end
  | eapply evaln_lt; [eassumption|lia] ].

(** Choose the predecessor height for a goal [exists m, m < n /\ ...]. *)
Ltac exists_pred :=
  match goal with
  | |- exists m, m < ?n /\ _ => exists (pred n); split; [lia|]
  | |- exists m w, m < ?n /\ _ => exists (pred n); eexists; split; [lia|]
  end.

(** Convert all height-indexed hypotheses into ordinary evaluations. *)
Ltac evaln_forget :=
  repeat match goal with H : evaln _ _ _ |- _ =>
    apply evaln_eval in H end.

Local Opaque app inf equal equal1 get_tagname.
Local Opaque abstract_case default_body type_app_stem type_app_S
  triage_case get_name_test.

Lemma abstract_case_none : forall T,
 (forall E N, T <> 'tagged[E,N]) -> abstract_case @ T ==> Lf.
Proof.
  Local Transparent abstract_case.
  intros T Hplain; unfold abstract_case.
  destruct T as [|T|X Y]; try (cbv; evaluate; fail).
  destruct X as [|X|X1 X2]; try (cbv; evaluate; fail).
  exact (type_app_abstract_case_S_none X Y Hplain).
  Local Opaque abstract_case.
Qed.

(** * Height-aware inversion of type application *)

(** Fixpoint unfolding and fallback selection, keeping heights. *)
Lemma Z_evaln_inv : forall n f x v,
  evaln n (Z f @ x) v ->
  exists m w, m < n /\ evaln m (f @ Z f) w /\ evaln m (w @ x) v.
Proof.
  intros n f x v H; unfold Z in H; invert_evaln.
  match goal with
  | H : evaln _ (dup_z @ _) _ |- _ =>
      unfold dup_z at 1 in H
  end; invert_evaln.
  match goal with
  | H : evaln _ (bz @ _) _ |- _ =>
      unfold bz in H
  end; invert_evaln.
  exists_pred; split; [|evaln_close]; unfold Z; evaln_close.
Qed.


Lemma extend_program_evaln_inv : forall n p f x r,
  evaln n (extend_program @ p @r f @r x) r ->
  (exists v, p @ x ==> Sm v /\ r = v) \/
  (p @ x ==> Lf /\ exists m, m < n /\ evaln m (f @ x) r) \/
  (exists l q, p @ x ==> Fk l q /\ r = Lf).
Proof.
  Local Transparent extend_program.
  intros n p f x r H; unfold extend_program in H; cbn in H.
  invert_evaln.
  all: try solve [left; eexists; split; [evaln_forget; eassumption|reflexivity]].
  all: try solve [right; right; do 2 eexists; split; [evaln_forget; eassumption|reflexivity]].
  right; left; split; [evaln_forget; eassumption|].
  exists_pred; evaln_close.
  Local Opaque extend_program.
Qed.

Local Transparent app.
Lemma app_partial_evaln : forall AI n F w,
  (forall E N, F <> 'tagged[E,N]) ->
  evaln n (app AI @ F) w ->
  exists m, m < n /\ evaln m (default_body AI @ app AI @r F) w.
Proof.
  intros AI n F w Hplain H.
  unfold type_app in H.
  destruct (Z_evaln_inv _ _ _ _ H) as [m [b [Hm [Hb Hw]]]]; clear H.
  change (Z (body AI)) with (type_app AI) in Hb, Hw.
  remember (type_app AI) as A eqn:HA.
  rewrite body_components in Hb; cbn in Hb.
  invert_evaln.
  (* a leaf or a stem: the ordinary clauses at once *)
  all: try solve [exists (pred n); split; [lia|evaln_close]].
  (* a fork: the F-level clause, then the ordinary clauses *)
  match goal with Hp : forall E N, ?F0 <> 'tagged[E,N] |- _ => set (F := F0) in * end.
  match goal with
  | H10 : evaln _ (extend_program @ ?p) ?v0,
    H9 : evaln _ (?v0 @ ?d) ?v1,
    H8 : evaln _ (?v1 @ F) w |- _ =>
    assert (HE : evaln (pred n)
      (extend_program @ p @r d @r F) w)
      by evaln_close
  end.
  destruct (extend_program_evaln_inv _ _ _ _ _ HE) as [[v [HS _]]|[[_ [k [Hk Hk']]]|[l [q [HS _]]]]].
  1,3: pose proof (eval_deterministic _ _ HS _ (wait_abstract_wait_plain _ F Hplain)); discriminate.
  exists (pred n); split; [lia|evaln_close].
Qed.
Local Opaque app.

(** Off tagged function types, type application is the application of
    the default clauses, at smaller height. *)
Lemma app_evaln_head : forall AI n F U R,
  (forall E N, F <> 'tagged[E,N]) ->
  evaln n (app AI @ F @r U) R ->
  exists m w, m < n /\ evaln m (default_body AI @ app AI @r F) w /\ evaln m (w @ U) R.
Proof.
  intros AI n F U R Hplain H.
  inv_out H.
  match goal with
  | H1 : evaln _ (app AI @ F) ?w,
    H2 : evaln ?k (?w @ U) R |- _ =>
    destruct (app_partial_evaln AI _ F w Hplain H1) as [m [Hm HD]]
  end.
  exists n0; eexists; split; [lia|split; [evaln_close|eassumption]].
Qed.


Local Opaque equal index_check.


(** Function introduction from a direct carrier. *)
Lemma function_abstractor_direct_eval : forall type_app0 F U V,
  type_app0 @ F @r U ==> Sm V ->
  function_abstractor_core @ 'decorate[F,U] @r type_app0 ==>
    Sm (funty_eliminator U V).
Proof.
  Local Transparent function_abstractor_core.
  intros type_app0 F U V Htype; inv_out Htype; split_all.
  eapply eval_appl.
  - unfold function_abstractor_core; eapply extend_some.
    unfold check_function_direct; cbn.
    repeat first [apply get_decorate_some | progress evaluate].
  - repeat first [progress evaluate | eassumption].
  Local Opaque function_abstractor_core.
Qed.


(** * Components of types

    A component of a type is reached through stems, untagged forks and the
    parameters of tagged types (one rule for every family: the arrow
    domains and codomains and the query result types are instances). *)
Inductive type_component : Combination -> Combination -> Prop :=
| component_refl : forall T, type_component T T
| component_stem : forall S X, type_component S X -> type_component S (Sm X)
| component_fork_left : forall S X Y,
    (forall E N, Fk X Y <> 'tagged[E,N]) ->
    type_component S X -> type_component S (Fk X Y)
| component_fork_right : forall S X Y,
    (forall E N, Fk X Y <> 'tagged[E,N]) ->
    type_component S Y -> type_component S (Fk X Y)
| component_param : forall S E X N,
    type_component S X -> type_component S ('tagged['wait[E,X],N]).


Lemma component_pair_left : forall S A B,
  type_component S A -> type_component S (A '* B).
Proof.
  intros S A B H.
  apply component_fork_left; [intros ? ? ?; discriminate|].
  apply component_stem, component_fork_right; [intros ? ? ?; discriminate|].
  apply component_fork_right; [intros ? ? ?; discriminate|exact H].
Qed.

Lemma component_pair_right : forall S A B,
  type_component S B -> type_component S (A '* B).
Proof.
  intros S A B H.
  apply component_fork_right; [intros ? ? ?; discriminate|].
  apply component_fork_right; [intros ? ? ?; discriminate|exact H].
Qed.

Lemma component_domain : forall S U V,
  type_component S U -> type_component S ('tagged[funty_eliminator U V,fun_nm]).
Proof. intros; apply component_param, component_pair_left; assumption. Qed.

Lemma component_codomain : forall S U V,
  type_component S V -> type_component S ('tagged[funty_eliminator U V,fun_nm]).
Proof. intros; apply component_param, component_pair_right; assumption. Qed.

Lemma component_query : forall S B,
  type_component S B -> type_component S ('tagged[query_eliminator B,query_nm]).
Proof. intros; apply component_param; assumption. Qed.

(** Find a component path; untagged side conditions are discharged by
    computation. *)
Ltac component_tac :=
  first
  [ apply component_refl
  | apply component_stem; component_tac
  | apply component_query; component_tac
  | apply component_domain; component_tac
  | apply component_codomain; component_tac
  | apply component_fork_left; [intros ? ? ?; discriminate|component_tac]
  | apply component_fork_right; [intros ? ? ?; discriminate|component_tac] ].


Unset Default Proof Using.
Transparent app inf equal equal1 get_tagname abstract_case extend_program default_body type_app_S type_app_stem function_abstractor_core.

(** Evaluation preserves typing, relative to a sound declarations.

    typing.v supplies the auxiliary programs and their recognition facts,
    application and inversion lemmas, inference and its inversions.

    The proof has three ingredients before the main evaluation induction:
    name tests agree on typed values and their types; child reconstruction
    preserves each node's inferred type; and the core direct and recursive
    function constructors are sound.  Wrapper lookup refuses fun_nm, which
    is always dispatched to the core function handler.  The declarations
    have one obligation ([ontology_sound]): at an index, every eliminator
    it makes is sound for values (a carrier applied to a value of the
    argument type yields a value of the result type).

    The final section makes abstract-introduction soundness
    compositional. *)
From TreeTyping Require Import tree.
From TreeTyping Require Import typing.
From TreeTyping Require Import typing.
From Stdlib Require Import String.
Open Scope string_scope.
Set Default Proof Using "Type".
Local Opaque app inf equal equal1 get_tagname.
Definition inhabited (AI U : Combination) : Prop :=
 exists u, inf AI @ u ==> Sm U.

(** Name-test preservation: recover the runtime name and relate its test
    to the test performed on the inferred argument type. *)
Lemma infer_name_test_inv : forall AI m N,
 inf AI @ m ==> Sm (name_test N) ->
 exists n, m = name_test n /\ inf AI @ n ==> Sm N.
Proof.
 intros AI m N H; unfold name_test in H.
 destruct (infer_S2_inv AI m ('K1 ('wait[equal,Sm N])) get_tagname ltac:(intros;discriminate) H)
   as [g [f [-> [Hg Hf]]]].
 pose proof (infer_tag_free_inv AI f get_tagname Hf ltac:(tag_free_tac)) as ->.
 destruct (infer_K1_inv AI g _ Hg) as [w [-> Hw]].
 destruct (infer_S2_inv AI w ('S2['K1 equal,'K1 (Sm N)]) ('I) ltac:(intros;discriminate) Hw)
   as [a [i [-> [Ha Hi]]]].
 pose proof (infer_tag_free_inv AI i ('I) Hi ltac:(tag_free_tac)) as ->.
 destruct (infer_S2_inv AI a ('K1 equal) ('K1 (Sm N)) ltac:(intros;discriminate) Ha)
   as [e [sn [-> [He Hsn]]]].
 pose proof (infer_tag_free_inv AI e ('K1 equal) He ltac:(tag_free_tac)) as ->.
 destruct (infer_K1_inv AI sn _ Hsn) as [s [-> Hs]].
 destruct (infer_stem_result_inv AI s N Hs) as [n [-> Hn]].
 exists n; split; [reflexivity|exact Hn].
Qed.

(** The equal1 presentation is used only to reason about the same name test. *)
Definition tag_matches N := equal1 (Sm N) 'C get_tagname.

Lemma tag_matches_hit : forall N C,
 tag_matches N @ ('tagged[C,N]) ==> 'K.
Proof.
 intros; pose proof (get_tagname_some C N).
 unfold tag_matches; repeat first [eassumption|apply equal1_eq|progress evaluate].
Qed.

Lemma tag_matches_miss : forall N u,
 (forall C, u <> 'tagged[C,N]) -> tag_matches N @ u ==> 'KI.
Proof.
 intros N u H.
 destruct (tagged_decide u) as [[C [M ->]]|Hplain].
 - pose proof (get_tagname_some C M).
   assert (Sm N <> Sm M) by (intro HE; inversion HE; subst; eapply H; reflexivity).
   unfold tag_matches; repeat first [eassumption|apply equal1_neq; assumption|progress evaluate].
 - pose proof (get_tagname_none u Hplain).
   unfold tag_matches; repeat first [eassumption|apply equal1_neq; discriminate|progress evaluate].
Qed.

(** [name_test_tag_hit] and [name_test_tag_miss] live in typing.v. *)
Lemma name_test_equivalent : forall N u b,
 name_test N @ u ==> b <-> tag_matches N @ u ==> b.
Proof.
 intros N u b.
 destruct (tagged_decide u) as [[C [M ->]]|Hplain].
 - destruct (combination_eq_dec N M) as [->|Hneq].
   + split; intro H.
     * pose proof (eval_deterministic _ _ H _ (name_test_tag_hit M C)) as ->; apply tag_matches_hit.
     * pose proof (eval_deterministic _ _ H _ (tag_matches_hit M C)) as ->; apply name_test_tag_hit.
   + assert (HM : forall D, 'tagged[C,M] <> 'tagged[D,N]) by (intros D HE; inversion HE; congruence).
     split; intro H.
     * pose proof (eval_deterministic _ _ H _ (name_test_tag_miss N _ HM)) as ->; apply tag_matches_miss; exact HM.
     * pose proof (eval_deterministic _ _ H _ (tag_matches_miss N _ HM)) as ->; apply name_test_tag_miss; exact HM.
 - assert (HM : forall C, u <> 'tagged[C,N]) by eauto.
   split; intro H.
   + pose proof (eval_deterministic _ _ H _ (name_test_tag_miss N _ HM)) as ->; apply tag_matches_miss; exact HM.
   + pose proof (eval_deterministic _ _ H _ (tag_matches_miss N _ HM)) as ->; apply name_test_tag_miss; exact HM.
Qed.

Lemma tag_free_tag_iff : forall AI u U N,
 tag_free N = true -> infer AI @ u ==> Sm U ->
 ((exists f, u = 'tagged[f,N]) <-> (exists E, U = 'tagged[E,N])).
Proof.
 intros AI u U N HN HU; split.
 - intros [f ->].
   destruct (infer_tagged_source_inv AI f N U HU)
     as [C [M [E [-> [HC [HM HE]]]]]].
   pose proof (infer_tag_free AI N HN) as Hself.
   pose proof (eval_deterministic _ _ HM _ Hself) as HH.
   inversion HH; subst M; eauto.
 - intros [E ->].
   destruct (infer_tagged_result_inv AI u E N HU)
     as [f [n [C [-> [HC [Hn HE]]]]]].
   pose proof (infer_tag_free_inv AI n N Hn HN) as ->; eauto.
Qed.

Lemma tag_test_preservation : forall AI N u U b,
 tag_free N = true -> infer AI @ u ==> Sm U ->
 tag_matches N @ U ==> b -> tag_matches N @ u ==> b.
Proof.
 intros AI N u U b HN HU HB.
 destruct (tagged_decide U) as [[E [M ->]]|Hplain].
 - destruct (combination_eq_dec N M) as [->|Hneq].
   + pose proof (eval_deterministic _ _ HB _ (tag_matches_hit M E)) as ->.
     destruct (proj2 (tag_free_tag_iff AI u ('tagged[E,M]) M HN HU)
       ltac:(eauto)) as [f ->]; apply tag_matches_hit.
   + assert (HM : forall C, 'tagged[E,M] <> 'tagged[C,N]) by (intros C HE; inversion HE; congruence).
     pose proof (eval_deterministic _ _ HB _ (tag_matches_miss N _ HM)) as ->.
     apply tag_matches_miss; intros C HC.
     destruct (proj1 (tag_free_tag_iff AI u ('tagged[E,M]) N HN HU)
       ltac:(eauto)) as [D HD]; inversion HD; congruence.
 - assert (HM : forall C, U <> 'tagged[C,N]) by eauto.
   pose proof (eval_deterministic _ _ HB _ (tag_matches_miss N U HM)) as ->.
   apply tag_matches_miss; intros C HC.
   destruct (proj1 (tag_free_tag_iff AI u U N HN HU) ltac:(eauto))
     as [E HE]; eapply Hplain; exact HE.
Qed.

(** The name test fires only at concrete names, so only the concrete case
    of name-test preservation is needed. *)
Lemma inferred_name_test_preservation : forall AI n N u U B,
 tag_free N = true -> inf AI @ n ==> Sm N ->
 inf AI @ u ==> Sm U -> name_test N @ U ==> B -> name_test n @ u ==> B.
Proof.
 intros AI n N u U B HN Hn Hu HB.
 pose proof (infer_tag_free_inv AI n N Hn HN) as ->.
 apply name_test_equivalent; eapply tag_test_preservation;
   [exact HN|exact Hu|apply name_test_equivalent;exact HB].
Qed.

Lemma tag_matches_boolean : forall N u b,
 tag_matches N @ u ==> b -> b = 'K \/ b = 'KI.
Proof.
 intros N u b H.
 destruct (tagged_decide u) as [[C [M ->]]|Hplain].
 - destruct (combination_eq_dec N M) as [->|Hneq].
   + left; eapply eval_deterministic; [exact H|apply tag_matches_hit].
   + right; eapply eval_deterministic; [exact H|apply tag_matches_miss].
     intros D HE; inversion HE; congruence.
 - right; eapply eval_deterministic; [exact H|apply tag_matches_miss].
   intros C HE; eapply Hplain; exact HE.
Qed.

(* ================================================================== *)
(** * Wrappers *)
(* ================================================================== *)

(** A wrapper family is given by a concrete payload program [p] with
    [p @ Lf ==> Sm T]; the abstract payload type [T] need not be stored in
    the declarations.  Its abstractor maps the carrier [swap T] to the
    eliminator [wrap_eliminator T], which applies the type of an action to
    [T] by type application. *)

Local Opaque equal equal1 get_wait.
Local Ltac run_hw := first [eassumption|apply equal1_neq;discriminate|apply equal1_eq|apply equal_eval|apply get_wait_some|
 evaluate_expr_core run_hw run_head_hw|idtac]
with run_head_hw := first [eassumption|apply equal1_neq;discriminate|apply equal1_eq|apply equal_eval|
 evaluate_head_core run_hw|idtac].


Lemma fixed_payload_eval : forall T, fixed_payload T @ Lf ==> Sm T.
Proof. intros; unfold fixed_payload; evaluate. Qed.

Lemma computed_wrap_abstractor_some : forall p T,
 p @ Lf ==> Sm T -> computed_wrap_abstractor p @ swap T ==> Sm (wrap_eliminator T).
Proof.
 intros; unfold computed_wrap_abstractor, wrap_abstractor_body, wrap_eliminator;
 apply wait_eval; run_hw.
Qed.


Lemma computed_wrap_abstractor_inv : forall p C E,
 computed_wrap_abstractor p @ C ==> Sm E ->
 exists T, p @ Lf ==> Sm T /\ C = swap T /\ E = wrap_eliminator T.
Proof.
 intros p C E H; unfold computed_wrap_abstractor in H; apply wait_eval_inv in H.
 unfold wrap_abstractor_body in H; invert_eval; repeat progress recognizer_eqtac.
 all: eexists; repeat split; eassumption.
Qed.

Lemma wrap_abstractor_inv : forall T C E,
  wrap_abstractor T @ C ==> Sm E ->
  C = ('S2['I,'K1 T]) /\ E = wrap_eliminator T.
Proof.
  intros T C E H; destruct (computed_wrap_abstractor_inv _ _ _ H) as [T' [HT [-> ->]]].
  pose proof (eval_deterministic _ _ HT _ (fixed_payload_eval T)) as HE; inversion HE.
  split; reflexivity.
Qed.


(** Applying [swap T] to [T --> V] gives [V]. *)
Lemma type_app_swap : forall AI T V,
  type_app AI @ swap T @r (T --> V) ==> Sm V.
Proof.
  intros; unfold swap; eapply app_S;
  [intros;discriminate|apply get_name_test_S_right;discriminate|apply app_I|apply app_K|].
  apply app_abstract; apply funty_eliminator_eval.
Qed.


(** ** Wrapper lookup

    The lookup reads the payload program [p] from the abstractor
    (path [path_payload]), rebuilds the abstractor
    [computed_wrap_abstractor p] and compares it with the answer of the declarations;
    on a match it runs [p]. *)


Lemma get_payload_program_eval : forall p,
  get_payload_program @ ('K1 (computed_wrap_abstractor p)) ==> p.
Proof.
  intros; unfold get_payload_program.
  exact (path_eval path_payload ('K1 (computed_wrap_abstractor p))).
Qed.


Lemma computed_wrap_builder_eval : forall p,
  computed_wrap_builder @ p ==> ('K1 (computed_wrap_abstractor p)).
Proof.
  intros; unfold computed_wrap_builder, computed_wrap_abstractor; evaluate.
Qed.

Local Opaque computed_wrap_builder get_payload_program.
Local Lemma equal1_eq' : forall p q, p = q -> equal1 p @ q ==> 'K.
Proof. intros p q <-; apply equal1_eq. Qed.

Lemma get_computed_payload_some : forall p T,
 p @ Lf ==> Sm T -> get_computed_payload @ ('K1 (computed_wrap_abstractor p)) ==> Sm T.
Proof.
 intros; pose proof (get_payload_program_eval p).
 pose proof (computed_wrap_builder_eval p).
 unfold get_computed_payload; run_hw.
Qed.

Lemma get_computed_payload_inv : forall C T,
 get_computed_payload @ C ==> Sm T ->
 exists p, C = ('K1 (computed_wrap_abstractor p)) /\ p @ Lf ==> Sm T.
Proof.
 intros C T H; unfold get_computed_payload in H; invert_eval.
 pose proof (path_eval path_payload C) as HP.
 change (get_payload_program @ C ==> path_fn path_payload C) in HP.
 repeat match goal with
 | H1 : get_payload_program @ C ==> ?x |- _ =>
     pose proof (eval_deterministic _ _ H1 _ HP); subst x; clear H1
 end.
 pose proof (computed_wrap_builder_eval (path_fn path_payload C)) as HB.
 repeat match goal with
 | H1 : computed_wrap_builder @ path_fn path_payload C ==> ?x |- _ =>
     pose proof (eval_deterministic _ _ H1 _ HB); subst x; clear H1
 end.
 match goal with H1 : equal @ C ==> ?e |- _ =>
   pose proof (eval_deterministic _ _ H1 _ (equal_eval C)); subst e; clear H1 end.
 match goal with H1 : equal1 C @ ?R ==> ?b |- _ =>
   destruct (combination_eq_dec C R) as [Heq|Hneq];
   [ pose proof (eval_deterministic _ _ H1 _ (equal1_eq' C R Heq))
   | pose proof (eval_deterministic _ _ H1 _ (equal1_neq C R Hneq)) ];
   subst b; clear H1; invert_eval
 end.
 all: eexists; split; [exact Heq|eassumption].
Qed.

Local Opaque get_computed_payload.
(** declarations entry for a wrapper at N: a fixed or a computed payload. *)
Definition wrapper_entry AI N T :=
 AI @ N ==> ('K1 (wrap_abstractor T)) \/
 exists p, AI @ N ==> ('K1 (computed_wrap_abstractor p)) /\ p @ Lf ==> Sm T.
Definition declared_wrapper AI N T := wrapper_entry AI N T.
Lemma wrapper_lookup_some : forall AI N T,
 wrapper_entry AI N T -> wrapper_lookup AI @ N ==> Sm T.
Proof.
 intros AI N T [HO|[p [HI HP]]]; unfold wrapper_lookup.
 - pose proof (get_computed_payload_some _ T (fixed_payload_eval T)); evaluate.
 - pose proof (get_computed_payload_some p T HP); evaluate.
Qed.
Lemma wrapper_lookup_inv : forall AI N T,
 wrapper_lookup AI @ N ==> Sm T -> wrapper_entry AI N T.
Proof.
 intros AI N T H; unfold wrapper_lookup in H; invert_eval.
 match goal with H : get_computed_payload @ _ ==> Sm _ |- _ =>
   apply get_computed_payload_inv in H; destruct H as [p [-> HP]] end.
 right; exists p; split; assumption.
Qed.
Local Opaque wrapper_lookup equal1.
Lemma get_wrap_payload_type_some : forall AI N T,
 declared_wrapper AI N T -> get_wrap_payload_type AI @ N ==> Sm T.
Proof. intros AI N T H; apply wrapper_lookup_some; exact H. Qed.
Lemma get_wrap_payload_type_inv : forall AI N T,
 get_wrap_payload_type AI @ N ==> Sm T -> declared_wrapper AI N T.
Proof. intros AI N T H; apply wrapper_lookup_inv; exact H. Qed.
Local Transparent get_wait computed_wrap_builder get_payload_program get_computed_payload wrapper_lookup index_check.


(** One-level reconstruction preserves the inferred child types. *)
Lemma inf_children_inv : forall AI f0 f1 f2,
 inf AI @ 'triage[f0,f1,f2] ==> Sm (update_one_level ('Update)) ->
 inf AI @ f0 ==> Sm Lf /\ inf AI @ f1 ==> Sm (Lf 'C ('Update)) /\
 inf AI @ f2 ==> Sm (update_fork ('Update)).
Proof.
 intros AI f0 f1 f2 H; unfold update_one_level in H.
 destruct (typing.infer_plain_fork_inv AI _ (Fk Lf (Lf 'C ('Update)))
  (update_fork ('Update)) ltac:(intros;discriminate) H)
 as [l [r [HE [Hl Hr]]]].
 inversion HE; subst l r.
 destruct (typing.infer_plain_fork_inv AI _ Lf (Lf 'C ('Update)) ltac:(intros;discriminate) Hl)
 as [a [b [HE' [Ha Hb]]]].
 inversion HE'; subst a b; repeat split; assumption.
Qed.

(** The typing of the reduct of [triage[f0,f1,f2] @ x]. *)
Definition reduct_typed AI f0 f1 f2 x T : Prop :=
  match x with
  | Lf => inf AI @ f0 ==> Sm T
  | Sm y => has_type AI (f1 @ y) T
  | Fk y z => has_type AI (f2 @ y @r z) T
  end.

Lemma children_reduct_typing : forall AI f0 f1 f2 x X,
 inf AI @ 'triage[f0,f1,f2] ==> Sm (update_one_level ('Update)) ->
 inf AI @ x ==> Sm X -> reduct_typed AI f0 f1 f2 x X.
Proof.
 intros AI f0 f1 f2 x X Htriage Hx.
 destruct (inf_children_inv AI f0 f1 f2 Htriage) as [H0 [H1 H2]].
 destruct x as [|y|y z].
 - pose proof (eval_deterministic _ _ Hx _ (typing.inf_leaf AI)) as HE;
   inversion HE; subst; exact H0.
 - destruct (typing.infer_stem_inv AI _ _ Hx) as [Y [-> Hy]].
   eapply has_type_ap; [exact H1|exact Hy|apply app_update_stem].
 - destruct (typing.infer_fork_inv AI _ _ _ Hx) as [Y [Z [Hy [Hz HP]]]].
   eapply has_type_apr; [|exact Hz|apply app_update_fork_second; exact HP].
   eapply has_type_ap; [exact H2|exact Hy|apply app_update_fork_first].
Qed.

(** The two function-introduction cases handled by the core. *)
Section FunctionSoundnessFacts.
Variable AI : Decl.
Local Abbreviation type_app := (app AI).
Local Abbreviation type_app_stem := (type_app_stem AI).
Local Notation "F # U" := (type_app @ F @r U) (at level 45, left associativity).
Lemma type_app_stem_recursive_function : forall app U V,
  type_app_stem @ app
    @r (Sm ('K1 (Z (((U --> V) --> (U --> V)) 'C tagged_fun))))
    @r ('S2['K,'K1 fun_nm]) ==> Sm (U --> V).
Proof using AI.
  intros; apply type_app_stem_tagged; apply function_declared.
  apply function_abstractor_recursive_eval.
Qed.

Lemma type_app_tagged_fun_recursive : forall A B,
  tagged_fun # Z (((A --> B) --> (A --> B)) 'C tagged_fun) ==>
    Sm (A --> B).
Proof using AI.
  intros A B; unfold tagged_fun.
  repeat first
    [ new_S; [discriminate | | |]
    | eapply type_app_K_ev
    | eapply type_app_stem_ev; apply type_app_stem_recursive_function
    | eapply type_app_stem_ev; eapply type_app_stem_structural; intros; discriminate
    | eapply type_app_leaf_ev ].
Qed.

Lemma recursive_function_carrier_type_app : forall A B,
  Z (((A --> B) --> (A --> B)) 'C tagged_fun) # A ==> Sm B.
Proof using AI.
  intros A B; eapply type_app_Z.
  - eapply typing.app_compose;[solve [reject_name]| | |].
    + intros; discriminate.
    + apply type_app_tagged_fun_recursive.
    + apply type_app_abstract; apply funty_eliminator_eval.
  - apply type_app_abstract; apply funty_eliminator_eval.
Qed.

Lemma function_abstractor_core_sound : forall C E U V,
  function_abstractor_core @ C @r type_app ==> Sm E ->
  E @ type_app @r U ==> Sm V -> C # U ==> Sm V.
Proof using AI.
  intros C E U V HC HE.
  destruct (function_abstractor_success_inv _ _ _ HC)
    as [[F [A [B [-> [HF ->]]]]] | [A [B [-> ->]]]].
  - apply funty_eliminator_inv in HE; destruct HE as [-> ->].
    eapply type_app_wait; [apply type_app_K_ev|exact HF].
  - apply funty_eliminator_inv in HE; destruct HE as [-> ->].
    apply recursive_function_carrier_type_app.
Qed.

(** Function type introduction is sound by typing, in declarations with the row. *)
Theorem function_abstractor_sound : forall C E U V,
  function_abstractor @ type_app @r C ==> Sm E ->
  E @ type_app @r U ==> Sm V -> C # U ==> Sm V.
Proof using AI.
  intros C E U V HC HE.
  exact (function_abstractor_core_sound C E U V (function_abstractor_eval_inv _ _ _ HC) HE).
Qed.

End FunctionSoundnessFacts.

Local Opaque equal1.

Section Soundness.
Variable AI : Combination.
Local Abbreviation type_app := (app AI).
Local Abbreviation type_app_stem := (type_app_stem AI).
Local Abbreviation infer := (inf AI).
Local Notation "F # U" := (type_app @ F @r U) (at level 45, left associativity).

(** ** The rules without a premise *)

Lemma leaf_app_typing : forall u F U T,
  infer @ Lf ==> Sm F -> infer @ u ==> Sm U -> F # U ==> Sm T ->
  infer @ Sm u ==> Sm T.
Proof.
  intros u F U T Hf Hu HT.
  pose proof (eval_deterministic _ _ Hf _ (typing.inf_leaf AI)) as HF; inv_out HF.
  pose proof (eval_deterministic _ _ HT _ (typing.app_leaf AI U)) as HE; inv_out HE.
  apply typing.inf_stem; exact Hu.
Qed.

Lemma stem_app_typing : forall a u F U T,
  infer @ Sm a ==> Sm F -> infer @ u ==> Sm U -> F # U ==> Sm T ->
  infer @ Fk a u ==> Sm T.
Proof.
  intros a u F U T Hf Hu HT.
  destruct (typing.infer_stem_inv AI _ _ Hf) as [A [-> Ha]].
  exact (typing.inf_fork AI _ _ _ _ _ Ha Hu HT).
Qed.

(** ** The rules with premises

    Each typed application is inverted into the typings of the
    applications of its reduct. *)

(** The second component of a tagged value passes its argument through. *)
Lemma tagged_part_type : forall N U, 'S2['K,'K1 N] # U ==> Sm U.
Proof.
  intros N U; new_S. discriminate.
  eapply typing.app_stem.
  eapply type_app_stem_structural; intros; discriminate.
  eapply typing.app_K.
  eapply typing.app_K.
Qed.

(** An application of [S2[g,f]] is typed as its reduct, unless the value
    is tagged: then [g = K1 c] for its carrier [c], and the type is given
    by the abstractor declared at its tag. *)
Lemma S_app_typing_inv : forall g f u F U T,
  infer @ 'S2[g,f] ==> Sm F -> infer @ u ==> Sm U -> F # U ==> Sm T ->
  (exists G H VG VH, infer @ g ==> Sm G /\ infer @ f ==> Sm H /\
     G # U ==> Sm VG /\ H # U ==> Sm VH /\ VG # VH ==> Sm T) \/
  (exists c C N E, g = 'K1 c /\ infer @ c ==> Sm C /\
     infer @ f ==> Sm ('S2['K,'K1 N]) /\
     AI @ N @r type_app @r C ==> Sm E /\ E @ type_app @r U ==> Sm T).
Proof.
  intros g f u FT U T Hfunction Hu Happ.
  destruct (typing.infer_fork_inv AI _ _ _ Hfunction) as [GT [F [Hleft [Hf Hc]]]].
  destruct (typing.infer_stem_inv AI _ _ Hleft) as [G [-> Hg]].
  apply typing.app_stem_inv in Hc.
  destruct (tagged_decide ('S2[G,F])) as [[C [N Htag]]|Hplain].
  - right; inversion Htag; subst G F.
    destruct (type_app_stem_tagged_success_inv AI type_app C N FT Hc)
      as [E [Hintro ->]].
    apply app_abstract_inv in Happ.
    destruct (infer_K1_inv AI g C Hg) as [c [-> Hc']].
    exists c, C, N, E; repeat split; assumption.
  - left.
    pose proof (type_app_stem_structural_inv AI type_app _ _ _ Hplain Hc) as ->.
    pose proof (app_plain_inv AI _ _ _ (abstract_case_none _ Hplain) Happ) as HD.
    destruct (default_S_inv _ _ _ _ _ _ HD) as [VG [VF [HG [HF HR]]]].
    exists G, F, VG, VF; repeat split; assumption.
Qed.

(** Query application may be used compositionally inside the stem and fork
    reducts of triage. *)
Lemma query_app_type : forall B U, ('Query[B]) # U ==> Sm B.
Proof. intros; eapply typing.app_abstract; apply query_eliminator_eval. Qed.

Lemma query_triage_reduct_typing : forall f0 f1 f2 x T X,
  infer @ ('triage[f0,f1,f2]) ==> Sm (query_one_level T) ->
  infer @ x ==> Sm X ->
  reduct_typed AI f0 f1 f2 x T.
Proof.
  intros f0 f1 f2 x T X Htriage Hx.
  destruct (typing.infer_triage_inv AI f0 f1 f2 T Htriage) as [Hf0 [Hf1 Hf2]].
  destruct x as [|y|y z].
  - exact Hf0.
  - destruct (typing.infer_stem_inv AI _ _ Hx) as [Y [HX Hy]].
    eapply has_type_ap; [exact Hf1|exact Hy|apply query_app_type].
  - destruct (typing.infer_fork_inv AI _ _ _ Hx) as [Y [Z [Hy [Hz Hpair]]]].
    eapply has_type_apr; [|exact Hz|apply query_app_type].
    eapply has_type_ap; [exact Hf2|exact Hy|apply query_app_type].
Qed.

Lemma triage_application_typing : forall f0 f1 f2 x Q X T,
  infer @ 'triage[f0,f1,f2] ==> Sm Q -> infer @ x ==> Sm X -> Q # X ==> Sm T ->
  reduct_typed AI f0 f1 f2 x T.
Proof.
  intros f0 f1 f2 x Q X T Htriage Hx Happ.
  destruct (typing.infer_triage_shape AI _ _ _ _ Htriage) as [F0 [F1 [F2 ->]]].
  pose proof (app_plain_inv AI _ _ _ (abstract_case_triage_none F0 F1 F2) Happ) as HD.
  pose proof (structural_triage_inv _ _ _ _ _ _
    (triage_case_inv _ _ _ _ _ _ (default_triage_inv _ _ _ _ _ _ _ HD))) as HC.
  destruct (typing.infer_plain_fork_inv AI _ (Fk F0 F1) F2
    ltac:(intros; discriminate) Htriage) as [p [q [HE [Hp Hq]]]].
  inversion HE; subst p q; clear HE.
  destruct HC as [[Hplain HC]|[L [R [G [-> [HP [HL HR]]]]]]].
  - destruct (typing.infer_plain_fork_inv AI _ F0 F1 Hplain Hp)
      as [a [b [HE [Ha Hb]]]].
    inversion HE; subst a b; clear HE.
    destruct HC as [[-> ->]|[N [-> Hstep]]].
    + pose proof (typing.infer_tag_free_inv AI x Lf Hx eq_refl) as ->; exact Ha.
    + destruct (infer_stem_result_inv AI x N Hx) as [y [-> Hy]].
      eapply has_type_ap; [exact Hb|exact Hy|exact Hstep].
  - destruct (typing.infer_plain_fork_inv AI x L R HP Hx) as [y [z [-> [Hy Hz]]]].
    eapply has_type_apr; [|exact Hz|exact HR].
    eapply has_type_ap; [exact Hq|exact Hy|exact HL].
Qed.


(** * Plain soundness

    declarations needs agreement on every argument type. *)
Definition plain_intro_sound : Prop :=
  forall C N E U V,
    AI @ N @r type_app @r C ==> Sm E -> E @ type_app @r U ==> Sm V ->
    type_app @ C @r U ==> Sm V.

Lemma plain_evaluation_preserves_typing : forall e v,
  plain_intro_sound ->
  e ==> v -> forall T,
  has_type AI e T -> infer @ v ==> Sm T.
Proof.
  intros e v plain Heval; induction Heval; intros T HT.
  - destruct (has_type_apr_inv _ _ _ _ HT) as [D [U [Hd [Hu HA]]]].
    apply IHHeval2; eapply has_type_ap; [exact (IHHeval1 D Hd)|exact Hu|exact HA].
  - destruct (has_type_ap_inv _ _ _ _ HT) as [F [U [Hf [Hu HA]]]].
    eapply leaf_app_typing; eassumption.
  - destruct (has_type_ap_inv _ _ _ _ HT) as [F [U [Hf [Hu HA]]]].
    eapply stem_app_typing; eassumption.
  - destruct (has_type_ap_inv _ _ _ _ HT) as [F [U [Hf [Hu HA]]]].
    eapply K_typing; eassumption.
  - destruct (has_type_ap_inv _ _ _ _ HT) as [F [U [Hf [Hu HA]]]].
    destruct (S_app_typing_inv g f u F U T Hf Hu HA) as
      [[G [H [VG [VH [Hg [Hh [HG [HH HR]]]]]]]]
      |[c [C [N [E [-> [Hc [Hh [HI HE]]]]]]]]].
    + apply IHHeval3; eapply has_type_ap;
        [apply IHHeval1; eapply has_type_ap; eassumption
        |apply IHHeval2; eapply has_type_ap; eassumption|exact HR].
    + pose proof (eval_deterministic _ _ Heval1 _ (eval_k c u)) as ->.
      apply IHHeval3; eapply has_type_ap;
        [exact Hc
        |apply IHHeval2; eapply has_type_ap; [exact Hh|exact Hu|apply tagged_part_type]
        |exact (plain C N E U T HI HE)].
  - destruct (has_type_ap_inv _ _ _ _ HT) as [F [U [Hf [Hu HA]]]].
    exact (triage_application_typing f0 f1 f2 Lf F U T Hf Hu HA).
  - destruct (has_type_ap_inv _ _ _ _ HT) as [F [U [Hf [Hu HA]]]].
    exact (IHHeval T (triage_application_typing f0 f1 f2 (Sm u) F U T Hf Hu HA)).
  - destruct (has_type_ap_inv _ _ _ _ HT) as [F [U [Hf [Hu HA]]]].
    exact (IHHeval T (triage_application_typing f0 f1 f2 (Fk x y) F U T Hf Hu HA)).
Qed.

End Soundness.


(* Print Assumptions closed_evaluation_preserves_typing. (* clean: no axioms *) *)


Definition empty_ontology := 'K1 refusal.

(** The function row. *)
Definition function_case := to_tree (tcase (Val fun_nm) (Val function_abstractor)).
Lemma function_case_some : function_case @ fun_nm ==> Sm function_abstractor.
Proof. apply tcase_eq. Qed.
Lemma function_case_none : forall N, N <> fun_nm -> function_case @ N ==> Lf.
Proof. intros; apply tcase_neq; congruence. Qed.
(** Declarations with the function row and nothing else. *)
Definition function_ontology := extend function_case empty_ontology.
Lemma function_ontology_row : function_ontology @ fun_nm ==> function_abstractor.
Proof. apply extend_some; apply function_case_some. Qed.
Canonical Structure function_decl := mkDecl function_ontology function_ontology_row.


(** * One-round soundness

    An abstractor is sound when every eliminator it makes agrees with the
    carrier type it was made from, on every argument. declarations is
    sound when, at every index, it answers the refusal or a sound
    declaration. No program identifying the types is needed. *)
(** A declaration is a single program [D] from carrier types to
    eliminators.  It is sound when every eliminator it makes agrees with
    the carrier type it was made from, at every argument. *)
Definition abstractor_sound_by_typing (AI D : Combination) : Prop :=
  forall C E U V, D @ C ==> Sm E -> E @ app AI @r U ==> Sm V -> app AI @ C @r U ==> Sm V.

(** The declarations are sound when every abstractor they answer is
    sound.  The refusal is an abstractor too, and trivially sound. *)
Definition ontology_sound_by_typing (AI : Combination) : Prop :=
  forall N R D, AI @ N ==> R -> R @ app AI ==> D ->
    abstractor_sound_by_typing AI D.

(** The function row is sound by typing. *)
Lemma function_abstractor_row_sound : forall (AI : Decl) D,
  function_abstractor @ app AI ==> D -> abstractor_sound_by_typing AI D.
Proof.
  intros AI D HD C E U V HC HE.
  apply (function_abstractor_sound AI C E U V); [|exact HE].
  eapply eval_appl; eassumption.
Qed.

Lemma refusal_sound : forall AI, abstractor_sound_by_typing AI ('K1 Lf).
Proof.
  intros AI C E U V H.
  assert (H0 : ('K1 Lf) @ C ==> Lf) by evaluate.
  pose proof (eval_deterministic _ _ H _ H0); discriminate.
Qed.

(** The abstractors of a refusal, and what it answers at type application. *)
Lemma refusal_head : forall a, refusal @ a ==> ('K1 Lf).
Proof. intros; unfold refusal; evaluate. Qed.

Lemma ontology_sound_by_typing_plain : forall AI, ontology_sound_by_typing AI -> plain_intro_sound AI.
Proof.
  intros AI Hs C N E U V HI HE.
  destruct (declaration_apply_inv _ _ _ _ _ HI) as [R [D [HR [HD HDC]]]].
  exact (Hs N R D HR HD C E U V HDC HE).
Qed.

(** ** Bounded evaluation

    [eval_bounded n e] evaluates the application [e] with recursion depth
    at most [n]; every premise has a smaller bound.  It agrees with
    [eval] ([eval_bounded_sound], [eval_bounded_complete]). *)
(** One level of evaluation, with [rec] evaluating the premises. *)
Definition eval_step (rec : Application -> option Combination) (e : Application)
  : option Combination :=
  match e with
  | d @r u =>
    match rec d with
    | Some w => rec (w @ u)
    | None => None
    end
  | f @ u =>
    match f with
    | Lf => Some (Sm u)
    | Sm a => Some (Fk a u)
    | Fk Lf a => Some a
    | Fk (Sm g) h =>
      match rec (g @ u) with
      | Some a =>
        match rec (h @ u) with
        | Some b => rec (a @ b)
        | None => None
        end
      | None => None
      end
    | Fk (Fk f0 f1) f2 =>
      match u with
      | Lf => Some f0
      | Sm x => rec (f1 @ x)
      | Fk x y => rec (f2 @ x @r y)
      end
    end
  end.

Fixpoint eval_bounded (n : nat) (e : Application) : option Combination :=
  match n with
  | O => None
  | S n => eval_step (eval_bounded n) e
  end.

Lemma eval_bounded_sound : forall n e v, eval_bounded n e = Some v -> e ==> v.
Proof.
  induction n as [|n IH]; intros e v H; [discriminate|].
  destruct e as [f u|d u]; cbn [eval_bounded eval_step] in H.
  - destruct f as [|a|[|g|f0 f1] h].
    + inversion H; constructor.
    + inversion H; constructor.
    + inversion H; constructor.
    + destruct (eval_bounded n (g @ u)) as [a|] eqn:E1; [|discriminate].
      destruct (eval_bounded n (h @ u)) as [b|] eqn:E2; [|discriminate].
      eapply eval_s; apply IH; eassumption.
    + destruct u as [|x|x y].
      * inversion H; constructor.
      * apply eval_stem, IH, H.
      * apply eval_fork, IH, H.
  - destruct (eval_bounded n d) as [w|] eqn:E; [|discriminate].
    eapply eval_appl; apply IH; eassumption.
Qed.

Lemma eval_bounded_S : forall n e v, eval_bounded n e = Some v -> eval_bounded (S n) e = Some v.
Proof.
  induction n as [|n IH]; intros e v H; [discriminate|].
  change (eval_bounded (S (S n)) e) with (eval_step (eval_bounded (S n)) e).
  change (eval_bounded (S n) e) with (eval_step (eval_bounded n) e) in H.
  destruct e as [f u|d u]; cbn [eval_step] in H |- *.
  - destruct f as [|a|[|g|f0 f1] h]; try exact H.
    + destruct (eval_bounded n (g @ u)) as [a|] eqn:E1; [|discriminate].
      destruct (eval_bounded n (h @ u)) as [b|] eqn:E2; [|discriminate].
      rewrite (IH _ _ E1), (IH _ _ E2); apply IH, H.
    + destruct u as [|x|x y]; [exact H|apply IH, H|apply IH, H].
  - destruct (eval_bounded n d) as [w|] eqn:E; [|discriminate].
    rewrite (IH _ _ E); apply IH, H.
Qed.

Lemma eval_bounded_le : forall n e v, eval_bounded n e = Some v ->
  forall m, n <= m -> eval_bounded m e = Some v.
Proof.
  intros n e v H m Hle; induction Hle; [exact H|apply eval_bounded_S, IHHle].
Qed.

Lemma eval_bounded_complete : forall e v, e ==> v -> exists n, eval_bounded n e = Some v.
Proof.
  intros e v H; induction H;
    repeat match goal with H : exists _, _ |- _ => destruct H as [? H] end;
    try (exists 1; reflexivity).
  - exists (S (x + x0)); cbn [eval_bounded eval_step].
    rewrite (eval_bounded_le _ _ _ IHeval1 (x + x0) ltac:(lia)).
    exact (eval_bounded_le _ _ _ IHeval2 (x + x0) ltac:(lia)).
  - exists (S (x + x0 + x1)); cbn [eval_bounded eval_step].
    rewrite (eval_bounded_le _ _ _ IHeval1 (x + x0 + x1) ltac:(lia)),
      (eval_bounded_le _ _ _ IHeval2 (x + x0 + x1) ltac:(lia)).
    exact (eval_bounded_le _ _ _ IHeval3 (x + x0 + x1) ltac:(lia)).
  - match goal with IH : eval_bounded ?k _ = _ |- _ => exists (S k); exact IH end.
  - match goal with IH : eval_bounded ?k _ = _ |- _ => exists (S k); exact IH end.
Qed.

(** Evaluation is bounded evaluation at some depth. *)
Theorem eval_iff_bounded : forall e v,
  e ==> v <-> exists n, eval_bounded n e = Some v.
Proof.
  intros e v; split.
  - apply eval_bounded_complete.
  - intros [n H]; exact (eval_bounded_sound n e v H).
Qed.

(** [app_type_bounded AI n f u] computes the type of [f @ u] within
    bound [n]: [Some Lf] when inference or type application fails, [None]
    when the bound runs out. *)
Definition app_type_bounded (AI : Combination) (n : nat) (f u : Combination) :=
  match eval_bounded n (inf AI @ f) with
  | Some (Sm F) =>
    match eval_bounded n (inf AI @ u) with
    | Some (Sm U) => eval_bounded n (app AI @ F @r U)
    | Some _ => Some Lf
    | None => None
    end
  | Some _ => Some Lf
  | None => None
  end.

Lemma app_type_bounded_untyped : forall AI n f u T,
  app_type_bounded AI n f u = Some Lf -> ~ has_type AI (f @ u) T.
Proof.
  intros AI n f u T Hc HT.
  destruct (has_type_ap_inv _ _ _ _ HT) as [F [U [Hf [Hu HA]]]]; unfold app_type_bounded in Hc.
  destruct (eval_bounded n (inf AI @ f)) as [x|] eqn:E1; [|discriminate].
  pose proof (eval_deterministic _ _ Hf _ (eval_bounded_sound _ _ _ E1)) as <-.
  destruct (eval_bounded n (inf AI @ u)) as [y|] eqn:E2; [|discriminate].
  pose proof (eval_deterministic _ _ Hu _ (eval_bounded_sound _ _ _ E2)) as <-.
  pose proof (eval_deterministic _ _ HA _ (eval_bounded_sound _ _ _ Hc)); discriminate.
Qed.

(** ** Soundness for values

    An eliminator [E] of an abstract type with carrier [c] is sound for
    values when [E @ U ==> Sm V], [v : U] and [c @ v ==> w] imply
    [w : V].  The proof that evaluation preserves typing uses it at
    evaluations inside the evaluation being typed, so it may assume that
    evaluation preserves typing ([ept]) at every evaluation of bound at
    most that of [c @ v] ([ept_within]): the induction on evaluation is
    an induction on the bound. *)
Definition ept (AI : Combination) : Application -> Combination -> Prop :=
  fun e w => forall T, has_type AI e T -> inf AI @ w ==> Sm T.

Definition ept_within (AI : Combination) (n : nat) : Prop :=
  forall m e w, m <= n -> eval_bounded m e = Some w -> ept AI e w.

Definition sound_abstractor (AI D : Combination) : Prop :=
  forall n C E U V c v w,
    D @ C ==> Sm E -> E @ app AI @r U ==> Sm V ->
    inf AI @ c ==> Sm C -> inf AI @ v ==> Sm U ->
    ept_within AI n -> eval_bounded n (c @ v) = Some w -> inf AI @ w ==> Sm V.

(** The declarations are sound when every abstractor they answer is
    sound for values. *)
Definition ontology_sound (AI : Combination) : Prop :=
  forall N R D, AI @ N ==> R -> R @ app AI ==> D -> sound_abstractor AI D.

Lemma carrier_value_typing : forall AI n C U V c v w,
  app AI @ C @r U ==> Sm V -> inf AI @ c ==> Sm C -> inf AI @ v ==> Sm U ->
  ept_within AI n -> eval_bounded n (c @ v) = Some w -> inf AI @ w ==> Sm V.
Proof.
  intros AI n C U V c v w HC Hc Hv He Ht.
  exact (He n _ _ (le_n n) Ht V (has_type_ap _ _ _ _ _ _ Hc Hv HC)).
Qed.

Lemma sound_by_typing_implies_sound : forall AI D,
  abstractor_sound_by_typing AI D -> sound_abstractor AI D.
Proof.
  intros AI D HD n C E U V c v w HDC HE Hc Hv He Ht.
  eapply carrier_value_typing; [eapply HD; eassumption|eassumption|eassumption|exact He|exact Ht].
Qed.

Lemma refusal_value_sound : forall AI, sound_abstractor AI ('K1 Lf).
Proof. intros; apply sound_by_typing_implies_sound, refusal_sound. Qed.

Lemma ontology_sound_by_typing_value : forall AI, ontology_sound_by_typing AI -> ontology_sound AI.
Proof.
  intros AI Hs N R D HR HD; apply sound_by_typing_implies_sound; exact (Hs N R D HR HD).
Qed.

Section ValueSoundness.
Variable AI : Combination.
Local Abbreviation type_app := (app AI).
Local Abbreviation type_app_stem := (type_app_stem AI).
Local Abbreviation infer := (inf AI).
Local Notation "F # U" := (type_app @ F @r U) (at level 45, left associativity).

(** Evaluation within bound [n] preserves typing, by induction on [n]. *)
Lemma bounded_evaluation_preserves_typing :
  ontology_sound AI -> forall n, ept_within AI n.
Proof.
  intros HSv n; induction n as [|n IH].
  { intros m e w Hm H; inversion Hm; subst; discriminate. }
  intros m e w Hm H T HT.
  destruct (Nat.le_succ_r m n) as [HL _]; destruct (HL Hm) as [Hle| ->];
    [exact (IH m e w Hle H T HT)|]; clear HL Hm.
  destruct e as [f u|d u]; cbn [eval_bounded eval_step] in H.
  - destruct (has_type_ap_inv _ _ _ _ HT) as [F [U [Hf [Hu HA]]]]; clear HT.
    destruct f as [|a|[|g|f0 f1] h].
    + inv_out H; eapply leaf_app_typing; eassumption.
    + inv_out H; eapply stem_app_typing; eassumption.
    + inv_out H; eapply K_typing; eassumption.
    + destruct (eval_bounded n (g @ u)) as [a|] eqn:E1; [|discriminate].
      destruct (eval_bounded n (h @ u)) as [b|] eqn:E2; [|discriminate].
      destruct (S_app_typing_inv AI g h u F U T Hf Hu HA) as
        [[G [H' [VG [VH [Hg [Hh [HG [HH HR]]]]]]]]
        |[c [C [N [E [-> [Hc [Hh [HI HE]]]]]]]]].
      * (* untagged: the reduct (g u)(h u) *)
        apply (IH n _ _ (le_n n) H); eapply has_type_ap;
          [apply (IH n _ _ (le_n n) E1); eapply has_type_ap; eassumption
          |apply (IH n _ _ (le_n n) E2); eapply has_type_ap; eassumption|exact HR].
      * (* tagged: soundness for values at the carrier c *)
        assert (a = c) as ->.
        { destruct n; [discriminate|]; cbn in E1; congruence. }
        destruct (declaration_apply_inv _ _ _ _ _ HI) as [R0 [D0 [HR0 [HD0 HC0]]]].
        exact (HSv N R0 D0 HR0 HD0 n C E U T c b w HC0 HE Hc
          (IH n _ _ (le_n n) E2 U (has_type_ap _ _ _ _ _ _ Hh Hu (tagged_part_type AI N U)))
          IH H).
    + pose proof (triage_application_typing AI f0 f1 h u F U T Hf Hu HA) as HR.
      destruct u as [|x|x y].
      * inv_out H; exact HR.
      * exact (IH n _ _ (le_n n) H T HR).
      * exact (IH n _ _ (le_n n) H T HR).
  - destruct (eval_bounded n d) as [v|] eqn:E; [|discriminate].
    destruct (has_type_apr_inv _ _ _ _ HT) as [D [U [Hd [Hu HA]]]].
    apply (IH n _ _ (le_n n) H); eapply has_type_ap;
      [exact (IH n _ _ (le_n n) E D Hd)|exact Hu|exact HA].
Qed.

End ValueSoundness.

Theorem evaluation_preserves_typing : forall AI e v T,
  ontology_sound AI -> e ==> v ->
  has_type AI e T -> inf AI @ v ==> Sm T.
Proof.
  intros AI e v T HS He HT.
  destruct (eval_bounded_complete _ _ He) as [n Hn].
  exact (bounded_evaluation_preserves_typing AI HS n n e v (le_n n) Hn T HT).
Qed.

(** The first form of the central theorem, by induction on the evaluation
    ([plain_evaluation_preserves_typing]), with no bound. *)
Theorem ept_by_typing : forall AI e v T,
  ontology_sound_by_typing AI -> e ==> v ->
  has_type AI e T -> inf AI @ v ==> Sm T.
Proof.
  intros AI e v T HS He HT.
  exact (plain_evaluation_preserves_typing AI e v
           (ontology_sound_by_typing_plain AI HS) He T HT).
Qed.

(** The children carrier [update_one_level r] of the Update family is
    sound for values: every child of the argument is updated by an
    update [r], which preserves its type.  The carrier type
    [update_one_level Update] has no clause of type application, so the
    carrier is not sound by typing. *)
Lemma children_value_typing : forall AI n c v U w,
  inf AI @ c ==> Sm (update_one_level ('Update)) -> inf AI @ v ==> Sm U ->
  ept_within AI n -> eval_bounded n (c @ v) = Some w -> inf AI @ w ==> Sm U.
Proof.
  intros AI n c v U w Hc Hv He Ht.
  pose proof Hc as Hc'; unfold update_one_level in Hc'.
  destruct (typing.infer_plain_fork_inv AI _ (Fk Lf (Lf 'C ('Update)))
    (update_fork ('Update)) ltac:(intros;discriminate) Hc')
    as [l [f2 [-> [Hl _]]]].
  destruct (typing.infer_plain_fork_inv AI _ Lf (Lf 'C ('Update)) ltac:(intros;discriminate) Hl)
    as [f0 [f1 [-> _]]].
  pose proof (children_reduct_typing AI f0 f1 f2 v U Hc Hv) as HR.
  destruct n as [|n]; [discriminate|].
  destruct v as [|x|x y]; cbn [eval_bounded eval_step] in Ht.
  - inversion Ht; subst w; exact HR.
  - exact (He n _ _ ltac:(lia) Ht U HR).
  - exact (He n _ _ ltac:(lia) Ht U HR).
Qed.

(** The carrier [name_test n] of the IsNamed family is sound for values: a
    runtime name n of type N is N itself, and a value of type U is tagged
    at N exactly when U is ([inferred_name_test_preservation]), so the
    name test on the value gives the name test on its type. *)
Lemma is_named_value_typing : forall AI n c v N U V w,
  concrete N -> inf AI @ c ==> Sm (name_test N) -> inf AI @ v ==> Sm U ->
  name_test N @ U ==> V -> eval_bounded n (c @ v) = Some w -> inf AI @ w ==> Sm V.
Proof.
  intros AI n c v N U V w HN Hc Hv HB Ht.
  assert (HF : tag_free N = true) by (apply concrete_tag_free; exact HN).
  destruct (infer_name_test_inv AI c N Hc) as [m [-> Hn]].
  pose proof (inferred_name_test_preservation AI m N v U V HF Hn Hv HB) as HT.
  pose proof (eval_deterministic _ _ (eval_bounded_sound _ _ _ Ht) _ HT) as ->.
  apply name_test_equivalent in HB.
  destruct (tag_matches_boolean N U V HB) as [-> | ->]; apply infer_tag_free; reflexivity.
Qed.

Lemma is_named_abstractor_inv : forall C E,
  is_named_abstractor @ C ==> Sm E ->
  exists N, C = name_test N /\ concrete N /\ E = tagged_by N.
Proof.
  intros C E H; unfold is_named_abstractor in H; cbn in H; invert_eval.
  match goal with H4 : get_name_test @ C ==> Sm ?n |- _ => apply get_name_test_inv in H4; subst C end.
  match goal with H5 : is_concrete @ ?n ==> ?b |- _ =>
    pose proof (is_concrete_spec n) as HC;
    pose proof (eval_deterministic _ _ H5 _ HC) as HB;
    destruct (concreteb n) eqn:HN; cbn in HB; subst b end.
  all: invert_eval; try (eexists; split; [reflexivity|split; [apply concreteb_sound; exact HN|reflexivity]]).
Qed.

(** The IsNamed family is sound for values: its abstractor accepts only
    name tests [name_test N] at concrete [N] ([is_named_value_typing]). *)
Lemma is_named_abstractor_value_sound : forall AI, sound_abstractor AI is_named_abstractor.
Proof.
  intros AI n C E U V c v w HC HE Hc Hv He Ht.
  destruct (is_named_abstractor_inv _ _ HC) as [X [-> [HXc ->]]].
  apply tagged_by_inv in HE.
  eapply is_named_value_typing; eassumption.
Qed.

(** The one-level query carrier is sound for values. *)
Lemma query_one_level_value_typing : forall AI n c v B U w,
  inf AI @ c ==> Sm (query_one_level B) -> inf AI @ v ==> Sm U ->
  ept_within AI n -> eval_bounded n (c @ v) = Some w -> inf AI @ w ==> Sm B.
Proof.
  intros AI n c v B U w Hc Hv He Ht.
  pose proof Hc as Hc'; unfold query_one_level in Hc'.
  destruct (typing.infer_plain_fork_inv AI _ (Fk B ('Query[B]))
    ('Query['Query[B]]) ltac:(intros;discriminate) Hc')
    as [l [f2 [-> [Hl _]]]].
  destruct (typing.infer_plain_fork_inv AI _ B ('Query[B]) ltac:(intros;discriminate) Hl)
    as [f0 [f1 [-> _]]].
  pose proof (query_triage_reduct_typing AI f0 f1 f2 v B U Hc Hv) as HR.
  destruct n as [|n]; [discriminate|].
  destruct v as [|x|x y]; cbn [eval_bounded eval_step] in Ht.
  - inversion Ht; subst w; exact HR.
  - exact (He n _ _ ltac:(lia) Ht B HR).
  - exact (He n _ _ ltac:(lia) Ht B HR).
Qed.

(** Soundness of declarations built by [extend], one clause at a time. *)
Definition plain_clause_sound_for (clause target : Combination) : Prop :=
  forall C N constructor D E U V,
    clause @ N ==> Sm constructor ->
    constructor @ app target ==> D ->
    D @ C ==> Sm E ->
    E @ app target @r U ==> Sm V ->
    typing.type_app target @ C @r U ==> Sm V.

Definition plain_intro_sound_for (source target : Combination) : Prop :=
  forall C N E U V,
    source @ N @r app target @r C ==> Sm E ->
    E @ app target @r U ==> Sm V -> typing.type_app target @ C @r U ==> Sm V.

Lemma plain_extend_intro_sound_for : forall clause default target,
  (forall N left right, clause @ N ==> Fk left right -> False) ->
  plain_clause_sound_for clause target ->
  plain_intro_sound_for default target ->
  plain_intro_sound_for (extend clause default) target.
Proof.
  intros clause default target Hnofork Hclause Hdefault.
  intros C N E U V Hintro HE.
  destruct (declaration_apply_inv _ _ _ _ _ Hintro) as [selected [D [Hchoose [HD Hconstruct]]]].
  clear Hintro.
  destruct (extend_inv _ _ _ _ Hchoose)
    as [[chosen [Hsome Heq]] |
        [[Hnone Hfallback] | [left [right [Hfork Heq]]]]].
  + subst selected; exact (Hclause C N chosen D E U V Hsome HD Hconstruct HE).
  + assert (Hconstructed : default @ N @r app target @r C ==> Sm E)
      by (eapply eval_appl; [eapply eval_appl; eassumption|exact Hconstruct]).
    exact (Hdefault C N E U V Hconstructed HE).
  + exfalso; eapply Hnofork; exact Hfork.
Qed.

(** soundness by typing of declarations built by [extend]. *)
Lemma extend_intro_sound_by_typing : forall clause default,
  (forall N left right, clause @ N ==> Fk left right -> False) ->
  plain_clause_sound_for clause (extend clause default) ->
  plain_intro_sound_for default (extend clause default) ->
  plain_intro_sound (extend clause default).
Proof.
  intros clause default Hnofork Hclause Hdefault.
  exact (plain_extend_intro_sound_for _ _ _ Hnofork Hclause Hdefault).
Qed.

(** Soundness for values of declarations built by [extend]: if every
    abstractor that [clause] answers and every abstractor that [default]
    answers is sound for values in the extended declarations, then the
    extended declarations are sound. *)
Lemma extend_intro_sound : forall AI clause default,
  (forall N r, AI @ N ==> r <-> extend clause default @ N ==> r) ->
  (forall N left right, clause @ N ==> Fk left right -> False) ->
  (forall N R D, clause @ N ==> Sm R -> R @ app AI ==> D ->
     sound_abstractor AI D) ->
  (forall N R D, clause @ N ==> Lf -> default @ N ==> R ->
     R @ app AI ==> D -> sound_abstractor AI D) ->
  ontology_sound AI.
Proof.
  intros AI clause default Hext Hnofork Hclause Hdefault N R D HR HD.
  apply Hext in HR.
  destruct (extend_inv _ _ _ _ HR)
    as [[chosen [Hsome ->]] | [[Hnone Hfallback] | [left [right [Hfork _]]]]].
  - exact (Hclause N chosen D Hsome HD).
  - exact (Hdefault N R D Hnone Hfallback HD).
  - exfalso; eapply Hnofork; exact Hfork.
Qed.

(** soundness by typing of the declarations follows from the soundness for
    types of their abstract introduction. *)
Lemma plain_ontology_sound_by_typing : forall AI, plain_intro_sound AI -> ontology_sound_by_typing AI.
Proof.
  intros AI Hp N R D HR HD C E U V HC HE.
  apply (Hp C N E U V); [|exact HE].
  eapply eval_appl; [eapply eval_appl; eassumption|exact HC].
Qed.
