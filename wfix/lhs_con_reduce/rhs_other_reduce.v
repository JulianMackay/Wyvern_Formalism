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