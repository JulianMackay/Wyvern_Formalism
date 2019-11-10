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

Lemma subtype_sel_bnd_con_reduce :
  forall T1 x1 L1, T1 = (t_sel_bnd x1 L1) ->
                  forall T2 T Ts, T2 = t_con T Ts ->
                             subtype T1 T2 = false.
Proof.
  intros; subst.
  
  unfold subtype, subtype_func;
    simpl;
    rewrite fix_sub_eq_ext;
    simpl;
    fold subtype_func;
    auto.  
Qed.