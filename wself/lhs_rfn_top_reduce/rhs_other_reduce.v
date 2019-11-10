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


Lemma subtype_rfn_top_other_reduce :
  forall T1 Ts1, T1 = (t_rfn_top Ts1) ->
             forall T2, (T2 <> t_top) ->
                   (forall Ts2, T2 <> (t_rfn_top Ts2)) ->
                   (forall x L T, T2 <> (t_sel_low x L T)) ->
                   (forall x L T, T2 <> (t_sel_equ x L T)) ->
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

  destruct T2; auto;
    [contradiction H0; auto
    |contradiction (H2 v l T2); auto
    |contradiction (H3 v l T2); auto
    |contradiction (H1 T2); auto].
  
Qed.