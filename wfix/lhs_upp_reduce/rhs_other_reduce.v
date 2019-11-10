Require Export List.
Require Export Bool.
Require Export Arith.
Require Export Peano_dec.
Require Export Coq.Arith.PeanoNat.
Require Export Coq.Program.Wf.
Require Export Coq.Program.Tactics.
Require Export Coq.Logic.FunctionalExtensionality.
Require Export Recdef.

Require Import common.CpdtTactics.
Require Import common.wyv_common.
Require Import common.rhs_mat_tree.

Set Implicit Arguments.

Import WfExtensionality.

Lemma subtype_upp_other_reduce : 
  forall T1 L T1', T1 = (t_upp L T1') ->
              forall T2, (forall T2', T2 <> (t_upp L T2')) ->
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