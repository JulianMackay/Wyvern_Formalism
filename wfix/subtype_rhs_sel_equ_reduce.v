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
Require Import rhs_mat_subtype_lhs_sel_low_reduce.
Require Import rhs_mat_subtype_lhs_sel_upp_reduce.
Require Import rhs_mat_subtype_lhs_sel_equ_reduce.
Require Import rhs_mat_subtype_lhs_sel_nom_reduce.
Require Import rhs_mat_subtype_lhs_all_reduce.
Require Import rhs_mat_subtype_lhs_rfn_top_reduce.
Require Import rhs_mat_subtype_lhs_rfn_sel_reduce.
Require Import rhs_mat_subtype_lhs_sha_top_reduce.
Require Import rhs_mat_subtype_lhs_sha_sel_reduce.
Require Import rhs_mat_subtype_lhs_upp_reduce.
Require Import rhs_mat_subtype_lhs_low_reduce.
Require Import rhs_mat_subtype_lhs_equ_reduce.
Require Import rhs_mat_subtype_lhs_nom_reduce.
Require Import rhs_mat_subtype_lhs_nil_reduce.
Require Import rhs_mat_subtype_lhs_con_reduce.
Set Implicit Arguments.

Import WfExtensionality.

Lemma subtype_rhs_sel_equ_reduce :
  forall T2 x L T2', T2 = t_sel_equ x L T2' ->
                forall T1, subtype T1 T2' = true ->
                      (T1 <> t_nil) ->
                      (forall T1' Ts1, T1 <> t_con T1' Ts1) ->
                      (forall L1 T1', T1 <> t_upp L1 T1') ->
                      (forall L1 T1', T1 <> t_low L1 T1') ->
                      (forall L1 T1', T1 <> t_equ L1 T1') ->
                      (forall L1 T1', T1 <> t_nom L1 T1') ->
                      subtype T1 T2 = true.
Proof.
  intros.

  subst T2.

  destruct T1.

  unfold subtype, subtype_func;
    simpl;
    rewrite fix_sub_eq_ext;
    simpl;
    fold subtype_func;
    auto.

  rewrite subtype_bot; auto;
    try solve [intros; intros Hcontra; inversion Hcontra].

  erewrite subtype_sel_upp_sel_equ_reduce; eauto;
    rewrite H0;
    repeat rewrite orb_true_r;
    auto.

  erewrite subtype_sel_low_sel_equ_reduce; eauto;
    rewrite H0;
    repeat rewrite orb_true_r;
    auto.

  erewrite subtype_sel_equ_sel_equ_reduce; eauto;
    rewrite H0;
    repeat rewrite orb_true_r;
    auto.

  erewrite subtype_sel_nom_sel_equ_reduce; eauto;
    rewrite H0;
    repeat rewrite orb_true_r;
    auto.

  erewrite subtype_rfn_top_sel_equ_reduce; eauto.

  erewrite subtype_rfn_sel_sel_equ_reduce; eauto;
    rewrite H0;
    repeat rewrite orb_true_r;
    auto.

  erewrite subtype_sha_top_sel_equ_reduce; eauto.

  erewrite subtype_sha_sel_sel_equ_reduce; eauto;
    rewrite H0;
    repeat rewrite orb_true_r;
    auto.

  erewrite subtype_all_sel_equ_reduce; eauto.

  contradiction (H3 l T1); auto.
  contradiction (H4 l T1); auto.
  contradiction (H5 l T1); auto.
  contradiction (H6 l T1); auto.
  contradiction (H1); auto.
  contradiction (H2 T1_1 T1_2); auto.
Qed.
