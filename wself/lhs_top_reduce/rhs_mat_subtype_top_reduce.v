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

Lemma subtype_lhs_top_reduce :
  forall T, subtype t_top T = match T with
                         | t_top => true
                         | t_sel_low x L T2' => subtype t_top T2'
                         | t_sel_equ x L T2' => subtype t_top T2'
                         | _ => false
                         end.
Proof.
  intros.

  remember (subtype t_top T) as sub_fn.
  
  unfold subtype, subtype_func in Heqsub_fn;
    simpl in Heqsub_fn;
    rewrite fix_sub_eq_ext in Heqsub_fn;
    simpl in Heqsub_fn;
    fold subtype_func in Heqsub_fn;
    auto.

  destruct T; auto.
Qed.