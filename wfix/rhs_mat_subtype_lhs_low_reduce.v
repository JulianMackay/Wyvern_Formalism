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

Lemma subtype_low_low_reduce : 
  forall T1 L1 T1', T1 = (t_low L1 T1') ->
               forall T2 L2 T2', T2 = (t_low L2 T2') ->
                            subtype T1 T2 = (eq_label L1 L2) && subtype T2' T1'.
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

Lemma subtype_low_other_reduce : 
  forall T1 L T1', T1 = (t_low L T1') ->
              forall T2, (forall T2', T2 <> (t_low L T2')) ->
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

  destruct (eq_label_dec L l) as [Heq|Heq];
    rewrite Heq in Heqsub_fn;
    [rewrite andb_true_l in Heqsub_fn
    |rewrite andb_false_l in Heqsub_fn; auto].

  apply beq_label_eq in Heq; subst L;
    contradiction (H0 T2); auto.
Qed.

Lemma subtype_low_reduce :
  forall T1 L1 T1', T1 = t_low L1 T1' ->
               forall T2, subtype T1 T2 = match T2 with
                                     | t_low L2 T2' => andb (eq_label L1 L2)
                                                           (subtype T2' T1')
                                     | _ => false
                                     end.
Proof.
  intros; subst; destruct T2;
    try solve [eapply subtype_low_other_reduce; crush].
  apply subtype_low_low_reduce; auto.
Qed.
