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
Require Import common.lhs_sel_low_reduce.lhs_sel_low_reduce.
Require Import common.lhs_sel_upp_reduce.lhs_sel_upp_reduce.
Require Import common.lhs_sel_equ_reduce.lhs_sel_equ_reduce.
Require Import common.lhs_sel_nom_reduce.lhs_sel_nom_reduce.
Require Import common.lhs_all_reduce.lhs_all_reduce.
Require Import common.lhs_rfn_top_reduce.lhs_rfn_top_reduce.
Require Import common.lhs_rfn_sel_reduce.lhs_rfn_sel_reduce.
Require Import common.lhs_sha_top_reduce.lhs_sha_top_reduce.
Require Import common.lhs_sha_sel_reduce.lhs_sha_sel_reduce.
Require Import common.lhs_upp_reduce.lhs_upp_reduce.
Require Import common.lhs_low_reduce.lhs_low_reduce.
Require Import common.lhs_equ_reduce.lhs_equ_reduce.
Require Import common.lhs_nom_reduce.lhs_nom_reduce.
Require Import common.lhs_nil_reduce.lhs_nil_reduce.
Require Import common.lhs_con_reduce.lhs_con_reduce.
Set Implicit Arguments.

Import WfExtensionality.

Lemma subtype_lhs_sel_nom_reduce :
  forall T1 x1 L1 T1', T1 = t_sel_nom x1 L1 T1' ->
                  forall T2, subtype T1' T2 = true ->
                        (T2 <> t_nil) ->
                        (forall T2' Ts2, T2 <> t_con T2' Ts2) ->
                        (forall L2 T2', T2 <> t_upp L2 T2') ->
                        (forall L2 T2', T2 <> t_low L2 T2') ->
                        (forall L2 T2', T2 <> t_equ L2 T2') ->
                        (forall L2 t2 T2', T2 <> t_nom L2 t2 T2') ->
                        subtype T1 T2 = true.
Proof.
  intros.

  subst T1.
  rewrite subtype_sel_nom_reduce with (x1:=x1)(L1:=L1)(T1':=T1');
    [|auto].

  destruct T2; simpl; auto.

  rewrite H0, orb_true_r; auto.

  rewrite H0, orb_true_r; auto.

  rewrite H0, orb_true_r; auto.

  rewrite H0, orb_true_r; auto.

  contradiction (H3 l T2); auto.
  contradiction (H4 l T2); auto.
  contradiction (H5 l T2); auto.
  contradiction (H6 l t T2); auto.
  contradiction (H2 T2_1 T2_2); auto.
Qed.
