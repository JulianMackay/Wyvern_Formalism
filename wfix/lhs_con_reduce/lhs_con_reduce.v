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

Require Export common.lhs_con_reduce.rhs_con_reduce.
Require Export common.lhs_con_reduce.rhs_nil_reduce.
Require Export common.lhs_con_reduce.rhs_other_reduce.
Set Implicit Arguments.

Import WfExtensionality.

Lemma subtype_con_reduce :
  forall T1 T1' Ts1, T1 = t_con T1' Ts1 ->
                forall T2, subtype T1 T2 = match T2 with
                                      | t_nil => true
                                      | t_con T2' Ts2 => (subtype T1' T2') && (subtype Ts1 Ts2)
                                      | _ => false
                                      end.
Proof.
  intros; subst; destruct T2;
    try solve [eapply subtype_con_other_reduce; crush].

  eapply subtype_con_nil_reduce; auto.
  eapply subtype_con_con_reduce; auto.
Qed.