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

Require Export common.lhs_nil_reduce.rhs_nil_reduce.
Require Export common.lhs_nil_reduce.rhs_other_reduce.

Set Implicit Arguments.

Import WfExtensionality.

Lemma subtype_nil_reduce :
  forall T, subtype t_nil T = match T with
                         | t_nil => true
                         | _ => false
                         end.
Proof.
  intros; subst; destruct T;
    try solve [eapply subtype_nil_other_reduce; crush].
  apply subtype_nil_nil_reduce; auto.
Qed.
