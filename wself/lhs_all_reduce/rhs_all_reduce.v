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

Lemma subtype_all_all_reduce : 
  forall T T1 T2, T = (t_all T1 T2) ->
             forall T' T1' T2', T' = (t_all T1' T2') ->
                           subtype T T' = andb (eq_tree T1' T1)
                                               (subtype T2 T2').
Proof.
  intros.

  remember (subtype T T') as sub_fn; subst T T'.
  
  unfold subtype, subtype_func in Heqsub_fn;
    simpl in Heqsub_fn;
    rewrite fix_sub_eq_ext in Heqsub_fn;
    simpl in Heqsub_fn;
    fold subtype_func in Heqsub_fn;
    auto.
Qed.