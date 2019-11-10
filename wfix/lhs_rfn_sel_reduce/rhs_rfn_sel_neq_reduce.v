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

Lemma subtype_rfn_sel_rfn_sel_neq_reduce : 
  forall T1 x1 L1 Ts1 T1', T1 = (t_rfn_sel x1 L1 Ts1 T1') ->
                      forall T2 x2 L2 Ts2 T2', T2 = (t_rfn_sel x2 L2 Ts2 T2') ->
                                          (x1 <> x2 \/ L1 <> L2) ->
                                          subtype T1 T2 = subtype T1' T2.
Proof.
  intros.

  remember (subtype T1 T2) as sub_fn; subst T1 T2.
  
  unfold subtype, subtype_func in Heqsub_fn;
    simpl in Heqsub_fn;
    rewrite fix_sub_eq_ext in Heqsub_fn;
    simpl in Heqsub_fn;
    fold subtype_func in Heqsub_fn;
    auto.

  destruct H1 as [Heq|Heq].

  apply eq_var_neq in Heq;
    rewrite Heq in Heqsub_fn.

  rewrite andb_false_l, orb_false_l in Heqsub_fn.
  auto.
  
  apply eq_label_neq in Heq;
    rewrite Heq in Heqsub_fn.
  rewrite andb_false_r, andb_false_l, orb_false_l in Heqsub_fn.
  auto.
Qed.