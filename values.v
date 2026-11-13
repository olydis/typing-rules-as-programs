(** * Values and application (Support: the core without expressions).

    Evaluation in tree.v relates expressions, trees read as pending
    applications, to values.  This file rebuilds the core on values alone:
    the application of a value to a value.

    - [applies f u v]: applying the value [f] to the value [u] yields [v].
      It is deterministic ([applies_deterministic]).
    - Applying values preserves typing, relative to sound declarations, by
      induction on applications ([application_preserves_typing],
      [application_preserves_typing_by_typing]).
    - Expressions are derived: their evaluation is a fold of [applies]
      ([eval_iff_run]) and their type is a fold of type application, so
      the theorems on expressions follow
      ([expression_typing_by_applications]).

    Typing judgements are themselves applications of the values [inf AI]
    and [type_app AI]; [==>] on an application of values is [applies]
    ([applies_iff_eval]). *)

From Stdlib Require Import Arith Wf_nat Lia.
From TreeTyping Require Import tree typing soundness.
From TreeTyping Require paper_ontology.

Local Opaque app inf equal equal1 get_tagname.


(** * Application of values *)

Inductive applies : Combination -> Combination -> Combination -> Prop :=
| applies_leaf : forall u, applies Lf u (Sm u)
| applies_stem : forall a u, applies (Sm a) u (Fk a u)
| applies_k : forall a u, applies ('K1 a) u a
| applies_s : forall g f u a b v,
    applies g u a -> applies f u b -> applies a b v -> applies ('S2[g,f]) u v
| applies_triage_leaf : forall f0 f1 f2, applies ('triage[f0,f1,f2]) Lf f0
| applies_triage_stem : forall f0 f1 f2 x v,
    applies f1 x v -> applies ('triage[f0,f1,f2]) (Sm x) v
| applies_triage_fork : forall f0 f1 f2 x y a v,
    applies f2 x a -> applies a y v -> applies ('triage[f0,f1,f2]) (Fk x y) v.

Theorem applies_deterministic :
  forall f u v, applies f u v -> forall v', applies f u v' -> v = v'.
Proof.
  intros f u v H; induction H; intros v' H'; inv_out H';
    repeat match goal with
      | IH : forall w, applies ?f ?u w -> _ = w, H : applies ?f ?u _ |- _ =>
          apply IH in H; inv_out H
      end; auto.
Qed.

(** ** Bounded application

    The bound counts depth as [eval_bounded] does on [f @ u]
    ([apply_bounded_eval]): an S-step builds its reduct (g u)(f u) in two
    further levels, a triage step on a fork its reduct (f2 x) y in one.
    This makes the soundness conditions below interchangeable with those
    of soundness.v ([ontology_sound_iff]). *)
Fixpoint apply_bounded (n : nat) (f u : Combination) : option Combination :=
  match n with
  | O => None
  | S n1 =>
    match f with
    | Lf => Some (Sm u)
    | Sm a => Some (Fk a u)
    | Fk Lf a => Some a
    | Fk (Sm g) h =>
      match n1 with
      | S (S n3 as n2) =>
        match apply_bounded n2 g u with
        | Some a =>
          match apply_bounded n3 h u with
          | Some b => apply_bounded n3 a b
          | None => None
          end
        | None => None
        end
      | _ => None
      end
    | Fk (Fk f0 f1) f2 =>
      match u with
      | Lf => Some f0
      | Sm x => apply_bounded n1 f1 x
      | Fk x y =>
        match n1 with
        | S n2 =>
          match apply_bounded n2 f2 x with
          | Some a => apply_bounded n2 a y
          | None => None
          end
        | O => None
        end
      end
    end
  end.

Lemma apply_bounded_s : forall n g f u,
  apply_bounded (S (S (S n))) ('S2[g,f]) u =
  match apply_bounded (S n) g u with
  | Some a =>
    match apply_bounded n f u with
    | Some b => apply_bounded n a b
    | None => None
    end
  | None => None
  end.
Proof. reflexivity. Qed.

Lemma apply_bounded_triage_stem : forall n f0 f1 f2 x,
  apply_bounded (S n) ('triage[f0,f1,f2]) (Sm x) = apply_bounded n f1 x.
Proof. reflexivity. Qed.

Lemma apply_bounded_triage_fork : forall n f0 f1 f2 x y,
  apply_bounded (S (S n)) ('triage[f0,f1,f2]) (Fk x y) =
  match apply_bounded n f2 x with
  | Some a => apply_bounded n a y
  | None => None
  end.
Proof. reflexivity. Qed.

Lemma apply_bounded_S : forall n f u v,
  apply_bounded n f u = Some v -> apply_bounded (S n) f u = Some v.
Proof.
  induction n as [n IH] using lt_wf_ind; intros f u v H.
  destruct n as [|n]; [discriminate|].
  destruct f as [|a|[|g|f0 f1] f2]; try exact H.
  - destruct n as [|[|n]]; try discriminate.
    rewrite apply_bounded_s in H; rewrite apply_bounded_s.
    destruct (apply_bounded (S n) g u) as [a|] eqn:Hg; [|discriminate].
    destruct (apply_bounded n f2 u) as [b|] eqn:Hf; [|discriminate].
    rewrite (IH (S n) ltac:(lia) _ _ _ Hg), (IH n ltac:(lia) _ _ _ Hf).
    exact (IH n ltac:(lia) _ _ _ H).
  - destruct u as [|x|x y]; [exact H| |].
    + rewrite apply_bounded_triage_stem in H; rewrite apply_bounded_triage_stem.
      exact (IH n ltac:(lia) _ _ _ H).
    + destruct n as [|n]; [discriminate|].
      rewrite apply_bounded_triage_fork in H; rewrite apply_bounded_triage_fork.
      destruct (apply_bounded n f2 x) as [a|] eqn:Ha; [|discriminate].
      rewrite (IH n ltac:(lia) _ _ _ Ha); exact (IH n ltac:(lia) _ _ _ H).
Qed.

Lemma apply_bounded_le : forall n m f u v,
  n <= m -> apply_bounded n f u = Some v -> apply_bounded m f u = Some v.
Proof.
  intros n m f u v Hle; induction Hle; [tauto|intro H; apply apply_bounded_S, IHHle, H].
Qed.

Lemma apply_bounded_sound : forall n f u v,
  apply_bounded n f u = Some v -> applies f u v.
Proof.
  induction n as [n IH] using lt_wf_ind; intros f u v H.
  destruct n as [|n]; [discriminate|].
  destruct f as [|a|[|g|f0 f1] f2].
  - cbn in H; inv_out H; constructor.
  - cbn in H; inv_out H; constructor.
  - cbn in H; inv_out H; constructor.
  - destruct n as [|[|n]]; try discriminate.
    rewrite apply_bounded_s in H.
    destruct (apply_bounded (S n) g u) as [a|] eqn:Hg; [|discriminate].
    destruct (apply_bounded n f2 u) as [b|] eqn:Hf; [|discriminate].
    eapply applies_s; eapply IH; [|exact Hg| |exact Hf| |exact H]; lia.
  - destruct u as [|x|x y].
    + cbn in H; inv_out H; constructor.
    + rewrite apply_bounded_triage_stem in H.
      apply applies_triage_stem; eapply IH; [|exact H]; lia.
    + destruct n as [|n]; [discriminate|].
      rewrite apply_bounded_triage_fork in H.
      destruct (apply_bounded n f2 x) as [a|] eqn:Ha; [|discriminate].
      eapply applies_triage_fork; eapply IH; [|exact Ha| |exact H]; lia.
Qed.

Lemma apply_bounded_complete : forall f u v,
  applies f u v -> exists n, apply_bounded n f u = Some v.
Proof.
  intros f u v H; induction H; try (exists 1; reflexivity).
  - destruct IHapplies1 as [n1 E1], IHapplies2 as [n2 E2], IHapplies3 as [n3 E3].
    exists (S (S (S (n1 + n2 + n3)))); rewrite apply_bounded_s.
    rewrite (apply_bounded_le n1 (S (n1 + n2 + n3)) _ _ _ ltac:(lia) E1),
      (apply_bounded_le n2 (n1 + n2 + n3) _ _ _ ltac:(lia) E2).
    exact (apply_bounded_le n3 (n1 + n2 + n3) _ _ _ ltac:(lia) E3).
  - destruct IHapplies as [n E1]; exists (S n).
    rewrite apply_bounded_triage_stem; exact E1.
  - destruct IHapplies1 as [n1 E1], IHapplies2 as [n2 E2].
    exists (S (S (n1 + n2))); rewrite apply_bounded_triage_fork.
    rewrite (apply_bounded_le n1 (n1 + n2) _ _ _ ltac:(lia) E1).
    exact (apply_bounded_le n2 (n1 + n2) _ _ _ ltac:(lia) E2).
Qed.


(** * Typing applications of values *)

Section ApplicationTyping.
Variable AI : Combination.
Local Abbreviation type_app := (app AI).
Local Abbreviation infer := (inf AI).
Local Notation "F # U" := (type_app @ F @r U) (at level 45, left associativity).

(** The application of [f] to [u] with value [v] preserves typing. *)
Definition typed_app (f u v : Combination) : Prop :=
  forall F U T, infer @ f ==> Sm F -> infer @ u ==> Sm U -> F # U ==> Sm T ->
    infer @ v ==> Sm T.

Definition typed_within (n : nat) : Prop :=
  forall m f u v, m <= n -> apply_bounded m f u = Some v -> typed_app f u v.

(** An abstractor is sound for values when every carrier [c] it accepts,
    applied to a value of the argument type, yields a value of the result
    type, given preservation at every application of smaller bound. *)
Definition sound_abstractor_app (D : Combination) : Prop :=
  forall n C E U V c v w,
    D @ C ==> Sm E -> E @ type_app @r U ==> Sm V ->
    infer @ c ==> Sm C -> infer @ v ==> Sm U ->
    typed_within n -> apply_bounded n c v = Some w -> infer @ w ==> Sm V.

Definition ontology_sound_app : Prop :=
  forall N R D, AI @ N ==> R -> R @ type_app ==> D -> sound_abstractor_app D.

(** ** The rules without a premise *)

Lemma leaf_app_typed : forall u, typed_app Lf u (Sm u).
Proof.
  intros u F U T Hf Hu HT.
  pose proof (eval_deterministic _ _ Hf _ (inf_leaf AI)) as HF; inv_out HF.
  pose proof (eval_deterministic _ _ HT _ (app_leaf AI U)) as HE; inv_out HE.
  apply inf_stem; exact Hu.
Qed.

Lemma stem_app_typed : forall a u, typed_app (Sm a) u (Fk a u).
Proof.
  intros a u F U T Hf Hu HT.
  destruct (infer_stem_inv AI _ _ Hf) as [A [-> Ha]].
  exact (inf_fork AI _ _ _ _ _ Ha Hu HT).
Qed.

Lemma K_app_typed : forall a u, typed_app ('K1 a) u a.
Proof.
  intros a u F U T Hf Hu HT.
  destruct (infer_fork_inv AI _ _ _ Hf) as [L [A [Hleaf [Ha Hc]]]].
  pose proof (eval_deterministic _ _ Hleaf _ (inf_leaf AI)) as HL; inv_out HL.
  apply app_stem_inv in Hc.
  pose proof (type_app_stem_structural_inv AI type_app Lf A _
    ltac:(intros; discriminate) Hc) as ->.
  pose proof (eval_deterministic _ _ HT _ (app_K AI A U)) as HA; inv_out HA.
  exact Ha.
Qed.

(** ** The rules with premises

    Each typed application is inverted into the typed applications of its
    reduct. *)

(** A tagged [S2[g,f]] has [g = K1 c] for its carrier [c], and its type is
    given by the abstractor declared at its tag; its second component
    passes the argument through. *)
Lemma tagged_part_type : forall N U, 'S2['K,'K1 N] # U ==> Sm U.
Proof.
  intros N U; new_S. discriminate.
  eapply app_stem.
  eapply type_app_stem_structural; intros; discriminate.
  eapply app_K.
  eapply app_K.
Qed.

Lemma S_app_typing_inv : forall g f u F U T,
  infer @ 'S2[g,f] ==> Sm F -> infer @ u ==> Sm U -> F # U ==> Sm T ->
  (exists G H VG VH, infer @ g ==> Sm G /\ infer @ f ==> Sm H /\
     G # U ==> Sm VG /\ H # U ==> Sm VH /\ VG # VH ==> Sm T) \/
  (exists c C N E, g = 'K1 c /\ infer @ c ==> Sm C /\
     infer @ f ==> Sm ('S2['K,'K1 N]) /\
     AI @ N @r type_app @r C ==> Sm E /\ E @ type_app @r U ==> Sm T).
Proof.
  intros g f u FT U T Hfunction Hu Happ.
  destruct (infer_fork_inv AI _ _ _ Hfunction) as [GT [F [Hleft [Hf Hc]]]].
  destruct (infer_stem_inv AI _ _ Hleft) as [G [-> Hg]].
  apply app_stem_inv in Hc.
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

Definition triage_reduct_typed (f0 f1 f2 x T : Combination) : Prop :=
  match x with
  | Lf => infer @ f0 ==> Sm T
  | Sm y => exists F1 Y,
      infer @ f1 ==> Sm F1 /\ infer @ y ==> Sm Y /\ F1 # Y ==> Sm T
  | Fk y z => exists F2 Y Z G,
      infer @ f2 ==> Sm F2 /\ infer @ y ==> Sm Y /\ infer @ z ==> Sm Z /\
      F2 # Y ==> Sm G /\ G # Z ==> Sm T
  end.

Lemma triage_app_typing_inv : forall f0 f1 f2 x Q X T,
  infer @ 'triage[f0,f1,f2] ==> Sm Q -> infer @ x ==> Sm X -> Q # X ==> Sm T ->
  triage_reduct_typed f0 f1 f2 x T.
Proof.
  intros f0 f1 f2 x Q X T Htriage Hx Happ.
  destruct (infer_triage_shape AI _ _ _ _ Htriage) as [F0 [F1 [F2 ->]]].
  pose proof (app_plain_inv AI _ _ _ (abstract_case_triage_none F0 F1 F2) Happ) as HD.
  pose proof (structural_triage_inv _ _ _ _ _ _
    (triage_case_inv _ _ _ _ _ _ (default_triage_inv _ _ _ _ _ _ _ HD))) as HC.
  destruct (infer_plain_fork_inv AI _ (Fk F0 F1) F2
    ltac:(intros; discriminate) Htriage) as [p [q [HE [Hp Hq]]]].
  inversion HE; subst p q; clear HE.
  destruct HC as [[Hplain HC]|[L [R [G [-> [HP [HL HR]]]]]]].
  - destruct (infer_plain_fork_inv AI _ F0 F1 Hplain Hp) as [a [b [HE [Ha Hb]]]].
    inversion HE; subst a b; clear HE.
    destruct HC as [[-> ->]|[N [-> Hstep]]].
    + pose proof (infer_tag_free_inv AI x Lf Hx eq_refl) as ->; exact Ha.
    + destruct (infer_stem_result_inv AI x N Hx) as [y [-> Hy]].
      hnf; exists F1, N; repeat split; assumption.
  - destruct (infer_plain_fork_inv AI x L R HP Hx) as [y [z [-> [Hy Hz]]]].
    hnf; exists F2, L, R, G; repeat split; assumption.
Qed.

(** ** Preservation *)

Lemma bounded_application_preserves_typing :
  ontology_sound_app -> forall n, typed_within n.
Proof.
  intros HS n; induction n as [|n IH].
  { intros m f u v Hm H; inversion Hm; subst; discriminate. }
  intros m f u v Hm H F U T Hf Hu Happ.
  destruct (Nat.le_succ_r m n) as [HL _]; destruct (HL Hm) as [Hle| ->];
    [exact (IH m f u v Hle H F U T Hf Hu Happ)|]; clear HL Hm.
  destruct f as [|a|[|g|f0 f1] f2].
  - cbn in H; inv_out H; eapply leaf_app_typed; eassumption.
  - cbn in H; inv_out H; eapply stem_app_typed; eassumption.
  - cbn in H; inv_out H; eapply K_app_typed; eassumption.
  - destruct n as [|[|n]]; try discriminate.
    rewrite apply_bounded_s in H.
    destruct (apply_bounded (S n) g u) as [a|] eqn:Hg; [|discriminate].
    destruct (apply_bounded n f2 u) as [b|] eqn:Hf2; [|discriminate].
    destruct (S_app_typing_inv g f2 u F U T Hf Hu Happ) as
      [[G [H2 [VG [V2 [HgT [Hf2T [HG [H2U HR]]]]]]]]
      |[c [C [N [E [-> [Hc [Hf2T [HI HE]]]]]]]]].
    + (* untagged: the reduct (g u)(f u) *)
      exact (IH n a b v ltac:(lia) H VG V2 T
        (IH (S n) g u a ltac:(lia) Hg G U VG HgT Hu HG)
        (IH n f2 u b ltac:(lia) Hf2 H2 U V2 Hf2T Hu H2U) HR).
    + (* tagged: the carrier c applied to the argument *)
      assert (a = c) as -> by (cbn in Hg; congruence).
      destruct (declaration_apply_inv _ _ _ _ _ HI) as [R0 [D0 [HR0 [HD0 HC0]]]].
      exact (HS N R0 D0 HR0 HD0 n C E U T c b v HC0 HE Hc
        (IH n f2 u b ltac:(lia) Hf2 _ U U Hf2T Hu (tagged_part_type N U))
        (fun m f u w Hm => IH m f u w ltac:(lia)) H).
  - pose proof (triage_app_typing_inv f0 f1 f2 u F U T Hf Hu Happ) as HR.
    destruct u as [|x|x y].
    + cbn in H; inv_out H; exact HR.
    + rewrite apply_bounded_triage_stem in H.
      destruct HR as [F1 [X [H1 [Hx HT]]]].
      exact (IH n f1 x v (le_n n) H F1 X T H1 Hx HT).
    + destruct n as [|n]; [discriminate|].
      rewrite apply_bounded_triage_fork in H.
      destruct (apply_bounded n f2 x) as [a|] eqn:Ha; [|discriminate].
      destruct HR as [F2 [X [Y [G [H2 [Hx [Hy [HG HT]]]]]]]].
      exact (IH n a y v ltac:(lia) H G Y T
        (IH n f2 x a ltac:(lia) Ha F2 X G H2 Hx HG) Hy HT).
Qed.

Theorem application_preserves_typing :
  ontology_sound_app -> forall f u v, applies f u v -> typed_app f u v.
Proof.
  intros HS f u v H; destruct (apply_bounded_complete _ _ _ H) as [n Hn].
  exact (bounded_application_preserves_typing HS n n f u v (le_n n) Hn).
Qed.

Lemma sound_by_typing_implies_sound_app : forall D,
  abstractor_sound_by_typing AI D -> sound_abstractor_app D.
Proof.
  intros D HD n C E U V c v w HC HE Hc Hv Ht Hw.
  exact (Ht n c v w (le_n n) Hw C U V Hc Hv (HD C E U V HC HE)).
Qed.

Theorem application_preserves_typing_by_typing :
  ontology_sound_by_typing AI -> forall f u v, applies f u v -> typed_app f u v.
Proof.
  intro HS; apply application_preserves_typing.
  intros N R D HR HD; apply sound_by_typing_implies_sound_app; exact (HS N R D HR HD).
Qed.

End ApplicationTyping.


(** * Expressions, derived from applications *)

Inductive run : Combination -> Combination -> Prop :=
| run_val : forall v, run (Sm v) v
| run_app : forall e1 e2 v1 v2 v,
    run e1 v1 -> run e2 v2 -> applies v1 v2 v -> run (Fk e1 e2) v.

Lemma run_fork_inv : forall e1 e2 v,
  run (Fk e1 e2) v -> exists v1 v2, run e1 v1 /\ run e2 v2 /\ applies v1 v2 v.
Proof. intros e1 e2 v H; inv_out H; eauto. Qed.

Lemma run_applies : forall f u v, run (f @ u) v <-> applies f u v.
Proof.
  split.
  - intro H; destruct (run_fork_inv _ _ _ H) as [v1 [v2 [H1 [H2 H3]]]].
    inv_out H1; inv_out H2; exact H3.
  - intro H; eapply run_app; [constructor|constructor|exact H].
Qed.

Lemma applies_eval : forall f u v, applies f u v -> f @ u ==> v.
Proof.
  intros f u v H; induction H; try (constructor; fail).
  - apply eval_s; eapply eval_pair; eassumption.
  - apply eval_stem; exact IHapplies.
  - apply eval_fork; eapply eval_pair; [exact IHapplies1|apply eval_val|exact IHapplies2].
Qed.

Theorem eval_iff_run : forall e v, e ==> v <-> run e v.
Proof.
  split.
  - intro H; induction H;
      try (apply run_applies; constructor; fail).
    + constructor.
    + destruct (run_fork_inv _ _ _ IHeval2) as [w1 [w2 [R1 [R2 A]]]].
      inv_out R1; eapply run_app; eassumption.
    + eapply run_app; [constructor|exact IHeval1|apply run_applies, IHeval2].
    + destruct (run_fork_inv _ _ _ IHeval) as [a [b [Ra [Rb A]]]].
      apply run_applies in Ra, Rb; apply run_applies; econstructor; eassumption.
    + apply run_applies; constructor; apply run_applies, IHeval.
    + destruct (run_fork_inv _ _ _ IHeval) as [a [y [Ra [Ry A]]]].
      apply run_applies in Ra; inv_out Ry; apply run_applies; econstructor; eassumption.
  - intro H; induction H; [constructor|].
    eapply eval_pair; [exact IHrun1|exact IHrun2|apply applies_eval, H1].
Qed.

Corollary applies_iff_eval : forall f u v, applies f u v <-> f @ u ==> v.
Proof.
  split; [apply applies_eval|intro H; apply run_applies, eval_iff_run, H].
Qed.

(** The type of an expression is built from the types of the values it
    applies, so preservation at applications gives preservation at
    expressions. *)
Theorem expression_typing_by_applications : forall AI,
  (forall f u v, applies f u v -> typed_app AI f u v) ->
  forall e v T, e ==> v -> infer_expression AI @ e ==> Sm T -> inf AI @ v ==> Sm T.
Proof.
  intros AI Ha e v T He; apply eval_iff_run in He; revert T.
  induction He as [v|e1 e2 v1 v2 v H1 IH1 H2 IH2 H3]; intros T HT.
  - exact (infer_expression_stem_inv AI _ _ HT).
  - destruct (infer_expression_fork_inv AI _ _ _ HT) as [T1 [T2 [HT1 [HT2 Happ]]]].
    exact (Ha _ _ _ H3 T1 T2 T (IH1 T1 HT1) (IH2 T2 HT2) Happ).
Qed.

(** ** The soundness conditions agree *)

Lemma apply_bounded_eval : forall n f u, apply_bounded n f u = eval_bounded n (f @ u).
Proof.
  induction n as [n IH] using lt_wf_ind; intros f u.
  destruct n as [|n]; [reflexivity|].
  destruct f as [|a|[|g|f0 f1] f2]; try reflexivity.
  - destruct n as [|[|n]]; [reflexivity|reflexivity|].
    rewrite apply_bounded_s.
    change (eval_bounded (S (S (S n))) ('S2[g,f2] @ u)) with
      (match eval_bounded (S n) (g @ u) with
       | Some a =>
         match eval_bounded n (f2 @ u) with
         | Some b => eval_bounded n (a @ b)
         | None => None
         end
       | None => None
       end).
    rewrite (IH (S n) ltac:(lia) g u), (IH n ltac:(lia) f2 u).
    destruct (eval_bounded (S n) (g @ u)) as [a|]; [|reflexivity].
    destruct (eval_bounded n (f2 @ u)) as [b|]; [|reflexivity].
    apply IH; lia.
  - destruct u as [|x|x y]; [reflexivity| |].
    + rewrite apply_bounded_triage_stem.
      change (eval_bounded (S n) ('triage[f0,f1,f2] @ Sm x))
        with (eval_bounded n (f1 @ x)).
      apply IH; lia.
    + destruct n as [|n]; [reflexivity|].
      rewrite apply_bounded_triage_fork.
      change (eval_bounded (S (S n)) ('triage[f0,f1,f2] @ Fk x y)) with
        (match eval_bounded n (f2 @ x) with
         | Some a => eval_bounded n (a @ y)
         | None => None
         end).
      rewrite (IH n ltac:(lia) f2 x).
      destruct (eval_bounded n (f2 @ x)) as [a|]; [|reflexivity].
      apply IH; lia.
Qed.

Lemma eval_bounded_fork_inv : forall m e1 e2 w,
  eval_bounded m (Fk e1 e2) = Some w ->
  exists v1 v2, eval_bounded m e1 = Some v1 /\ eval_bounded m e2 = Some v2 /\
    eval_bounded m (v1 @ v2) = Some w.
Proof.
  intros m e1 e2 w H; destruct m as [|m]; [discriminate|].
  destruct e1 as [|v1|a b]; [discriminate| |].
  - destruct e2 as [|v2|c d]; [discriminate|exists v1, v2; repeat split; auto|].
    destruct (eval_bounded_appr_inv _ _ _ _ _ H) as [v2 [H2 H3]].
    exists v1, v2; repeat split; apply eval_bounded_S; assumption.
  - destruct (eval_bounded_appl_inv _ _ _ _ _ H) as [v1 [H1 H2]].
    destruct e2 as [|v2|c d].
    + destruct m; discriminate.
    + exists v1, v2; repeat split; apply eval_bounded_S; assumption.
    + destruct m as [|m]; [discriminate|].
      destruct (eval_bounded_appr_inv _ _ _ _ _ H2) as [v2 [H3 H4]].
      exists v1, v2; repeat split;
        [apply eval_bounded_S; exact H1|..];
        apply (eval_bounded_le m); [lia|exact H3|lia|exact H4].
Qed.

Lemma typed_within_iff : forall AI n, typed_within AI n <-> ept_within AI n.
Proof.
  intros AI n; split.
  - intros Ht m e; revert m.
    induction e as [|v|e1 IH1 e2 IH2]; intros m w Hm He T HT.
    + destruct m; discriminate.
    + destruct m as [|m]; [discriminate|]; inv_out He.
      exact (infer_expression_stem_inv AI _ _ HT).
    + destruct (eval_bounded_fork_inv _ _ _ _ He) as [v1 [v2 [H1 [H2 H3]]]].
      destruct (infer_expression_fork_inv AI _ _ _ HT) as [T1 [T2 [HT1 [HT2 Happ]]]].
      rewrite <- apply_bounded_eval in H3.
      exact (Ht m v1 v2 w Hm H3 T1 T2 T (IH1 m v1 Hm H1 T1 HT1) (IH2 m v2 Hm H2 T2 HT2) Happ).
  - intros He m f u v Hm H F U T Hf Hu Happ.
    rewrite apply_bounded_eval in H.
    apply (He m (f @ u) v Hm H T).
    eapply infer_expression_fork;
      [apply infer_expression_stem; exact Hf|apply infer_expression_stem; exact Hu|exact Happ].
Qed.

Theorem ontology_sound_iff : forall AI, ontology_sound AI <-> ontology_sound_app AI.
Proof.
  intros AI; split; intros HS N R D HR HD n C E U V c v w HC HE Hc Hv Ht Hw;
    apply (HS N R D HR HD n C E U V c v w HC HE Hc Hv);
    first [apply typed_within_iff; exact Ht|rewrite apply_bounded_eval in *; exact Hw].
Qed.

(** The two forms of the central theorem, from the application form. *)
Corollary evaluation_preserves_typing_by_applications : forall AI e v T,
  ontology_sound AI -> e ==> v ->
  infer_expression AI @ e ==> Sm T -> inf AI @ v ==> Sm T.
Proof.
  intros AI e v T HS; apply expression_typing_by_applications.
  apply application_preserves_typing, ontology_sound_iff, HS.
Qed.

Corollary ept_by_typing_by_applications : forall AI e v T,
  ontology_sound_by_typing AI -> e ==> v ->
  infer_expression AI @ e ==> Sm T -> inf AI @ v ==> Sm T.
Proof.
  intros AI e v T HS; apply expression_typing_by_applications.
  apply application_preserves_typing_by_typing, HS.
Qed.

(** The declarations of the paper's ontology figure: application of
    values preserves typing. *)
Theorem paper_application_preserves_typing : forall f u v,
  applies f u v -> typed_app paper_ontology.paper_ontology f u v.
Proof.
  apply application_preserves_typing, ontology_sound_iff.
  exact paper_ontology.paper_ontology_sound.
Qed.
