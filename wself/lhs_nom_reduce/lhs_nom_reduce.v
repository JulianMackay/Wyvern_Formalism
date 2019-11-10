Require Export List.
Require Export Bool.
Require Export Arith.
Require Export Peano_dec.
Require Export Coq.Arith.PeanoNat.
Require Export Coq.Program.Wf.
Require Export Coq.Program.Tactics.
Require Export Coq.Logic.FunctionalExtensionality.
Require Export Recdef.

Require Export common.lhs_nom_reduce.rhs_nom_reduce.
Require Export common.lhs_nom_reduce.rhs_upp_reduce.
Require Export common.lhs_nom_reduce.rhs_other_reduce.

Require Import common.CpdtTactics.
Require Import common.wyv_common.
Require Import common.rhs_mat_tree.

Import WfExtensionality.

Lemma subtype_nom_reduce :
  forall T1 L1 T1', T1 = t_nom L1 T1' ->
               forall T2, subtype T1 T2 = match T2 with
                                     | t_upp L2 T2' => andb (eq_label L1 L2)
                                                           (subtype T1' T2')
                                     | t_nom L2 T2' => (eq_label L1 L2) && (eq_tree T1' T2')
                                     | _ => false
                                     end.
Proof.
  intros; subst; destruct T2;
    try solve [eapply subtype_nom_other_reduce; crush].
  apply subtype_nom_upp_reduce; auto.
  apply subtype_nom_nom_reduce; auto.
Qed.
