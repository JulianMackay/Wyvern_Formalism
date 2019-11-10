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

Lemma subtype_nil_nil_reduce : 
  subtype t_nil t_nil = true.
Proof.
  intros.
  
  unfold subtype, subtype_func;
    simpl;
    rewrite fix_sub_eq_ext;
    simpl;
    fold subtype_func;
    auto.
Qed.