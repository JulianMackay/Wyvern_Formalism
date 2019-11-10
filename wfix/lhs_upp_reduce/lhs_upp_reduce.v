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

Require Export common.lhs_upp_reduce.rhs_upp_reduce.
Require Export common.lhs_upp_reduce.rhs_other_reduce.


Set Implicit Arguments.

Import WfExtensionality.

Lemma subtype_upp_reduce :
  forall T1 L1 T1', T1 = t_upp L1 T1' ->
               forall T2, subtype T1 T2 = match T2 with
                                     | t_upp L2 T2' => andb (eq_label L1 L2)
                                                           (subtype T1' T2')
                                     | _ => false
                                     end.
Proof.
  intros; subst; destruct T2;
    try solve [eapply subtype_upp_other_reduce; crush].
  apply subtype_upp_upp_reduce; auto.
Qed.
