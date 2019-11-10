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

Lemma subtype_sel_low_all_reduce : 
  forall T1 x1 L1 T1', T1 = (t_sel_low x1 L1 T1') ->
                  forall T2 T T', T2 = (t_all T T') ->
                             subtype T1 T2 = false.
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