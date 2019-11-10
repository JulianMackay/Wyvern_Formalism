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

Require Export common.lhs_sha_top_reduce.rhs_sel_equ_reduce.
Require Export common.lhs_sha_top_reduce.rhs_sel_low_reduce.
Require Export common.lhs_sha_top_reduce.rhs_other_reduce.

Set Implicit Arguments.

Import WfExtensionality.

Lemma subtype_sha_top_reduce :
  forall T1 x1 L1 ss1, T1 = t_sha_top x1 L1 ss1 ->
                  forall T2, subtype T1 T2 = match T2 with
                                        | t_top => true
                                        | t_sel_low x L T => subtype T1 T
                                        | t_sel_equ x L T => subtype T1 T
                                        | _ => false
                                        end.
Proof.
  intros; subst; destruct T2;
    try solve [eapply subtype_sha_top_other_reduce; crush].

  apply subtype_top; crush.

  eapply subtype_sha_top_sel_low_reduce; crush.

  eapply subtype_sha_top_sel_equ_reduce; crush.  
Qed.
