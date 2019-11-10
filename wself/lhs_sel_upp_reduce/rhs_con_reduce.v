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

Import WfExtensionality.

Lemma subtype_sel_upp_con_reduce :
  forall T1 x1 L1 T1', T1 = (t_sel_upp x1 L1 T1') ->
                  forall T2 T2' Ts, T2 = t_con T2' Ts ->
                               subtype T1 T2 = false.
Proof.
  intros; subst.
  
  unfold subtype, subtype_func;
    simpl;
    rewrite fix_sub_eq_ext;
    simpl;
    fold subtype_func.

  auto.

Qed.