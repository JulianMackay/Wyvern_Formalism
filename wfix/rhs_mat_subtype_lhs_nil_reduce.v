Require Export List.
Require Export Bool.
Require Export Arith.
Require Export Peano_dec.
Require Export Coq.Arith.PeanoNat.
Require Import CpdtTactics.
Require Export Coq.Program.Wf.
Require Export Coq.Program.Tactics.
Require Export Coq.Logic.FunctionalExtensionality.
Require Export Recdef.
Require Import wyv_common.
Require Import rhs_mat_tree.
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

Lemma subtype_nil_other_reduce : 
  forall T, T <> t_nil  ->
       subtype t_nil T = false.

Proof.
  intros.
  
  unfold subtype, subtype_func;
    simpl;
    rewrite fix_sub_eq_ext;
    simpl;
    fold subtype_func;
    auto.

  destruct T; auto.
  contradiction H; auto.
Qed.

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
