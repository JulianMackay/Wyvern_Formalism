Require Import List.
Require Import Bool.
Require Import Arith.
Require Import Peano_dec.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Program.Wf.
Require Import Coq.Program.Tactics.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Recdef.

Require Export common.CpdtTactics.
Require Export common.wyv_common.
Require Export common.rhs_mat_tree.

Import WfExtensionality.

Lemma subtype_sel_equ_nil_reduce : 
  forall T1 x1 L1 T1', T1 = (t_sel_equ x1 L1 T1') ->
                  subtype T1 t_nil = false.
Proof.
  intros; subst.
  
  unfold subtype, subtype_func;
    simpl;
    rewrite fix_sub_eq_ext;
    simpl;
    fold subtype_func;
    auto.

Qed.