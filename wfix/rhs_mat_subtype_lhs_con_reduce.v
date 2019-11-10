Require Export List.
Require Export Bool.
Require Export Arith.
Require Export Peano_dec.
Require Export Coq.Arith.PeanoNat.
Require Import CpdtTactics.
Require Export Coq.Program.Wf.
Require Export Coq.Program.Tactics.
Require Export Coq.Logic.FunctionalExtensionality.
Require Export Recdef.
Require Import wyv_common.
Require Import rhs_mat_tree.
Set Implicit Arguments.

Import WfExtensionality.

Lemma subtype_con_con_reduce :
  forall T1 T1' Ts1, T1 = t_con T1' Ts1 ->
                forall T2 T2' Ts2, T2 = t_con T2' Ts2 ->
                              subtype T1 T2 = (subtype T1' T2') && (subtype Ts1 Ts2).
Proof.
  intros.

  remember (subtype T1 T2) as sub_fn; subst T1 T2.
  
  unfold subtype, subtype_func in Heqsub_fn;
    simpl in Heqsub_fn;
    rewrite fix_sub_eq_ext in Heqsub_fn;
    simpl in Heqsub_fn;
    fold subtype_func in Heqsub_fn;
    auto.
Qed.

Lemma subtype_con_nil_reduce :
  forall T1 T1' Ts1, T1 = t_con T1' Ts1 ->
                subtype T1 t_nil = true.
Proof.
  intros.

  remember (subtype T1 t_nil) as sub_fn; subst T1.
  
  unfold subtype, subtype_func in Heqsub_fn;
    simpl in Heqsub_fn;
    rewrite fix_sub_eq_ext in Heqsub_fn;
    simpl in Heqsub_fn;
    fold subtype_func in Heqsub_fn;
    auto.
Qed.

Lemma subtype_con_other_reduce :
  forall T1 T1' Ts1, T1 = t_con T1' Ts1 ->
                forall T2, (T2 <> t_nil)  ->
                      (forall T2' Ts2, T2 <> t_con T2' Ts2) ->
                      subtype T1 T2 = false.
Proof.
  intros.

  remember (subtype T1 T2) as sub_fn; subst T1.
  
  unfold subtype, subtype_func in Heqsub_fn;
    simpl in Heqsub_fn;
    rewrite fix_sub_eq_ext in Heqsub_fn;
    simpl in Heqsub_fn;
    fold subtype_func in Heqsub_fn;
    auto.

  destruct T2; auto.
  contradiction H0; auto.
  contradiction (H1 T2_1 T2_2); auto.
Qed.

Lemma subtype_con_reduce :
  forall T1 T1' Ts1, T1 = t_con T1' Ts1 ->
                forall T2, subtype T1 T2 = match T2 with
                                      | t_nil => true
                                      | t_con T2' Ts2 => (subtype T1' T2') && (subtype Ts1 Ts2)
                                      | _ => false
                                      end.
Proof.
  intros; subst; destruct T2;
    try solve [eapply subtype_con_other_reduce; crush].

  eapply subtype_con_nil_reduce; auto.
  eapply subtype_con_con_reduce; auto.
Qed.