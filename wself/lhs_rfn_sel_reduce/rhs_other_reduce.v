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

Lemma subtype_rfn_sel_other_reduce :
  forall T1 x1 L1 Ts1 T', T1 = (t_rfn_sel x1 L1 Ts1 T') ->
                     forall T2, (T2 <> t_top) ->
                           (forall Ts2, T2 <> (t_rfn_top Ts2)) ->
                           (forall x2 L2 Ts2 T'', T2 <> (t_rfn_sel x2 L2 Ts2 T'')) ->
                           (forall x L T, T2 <> (t_sel_low x L T)) ->
                           (forall x L T, T2 <> (t_sel_equ x L T)) ->
                           (forall L2 T2', T2 <> (t_upp L2 T2')) ->
                           (forall L2 T2', T2 <> (t_equ L2 T2')) ->
                           (forall L2 T2', T2 <> (t_low L2 T2')) ->
                           (forall L2 T2', T2 <> (t_nom L2 T2')) ->
                           (T2 <> t_nil) ->
                           (forall T2' Ts2, T2 <> (t_con T2' Ts2)) ->
                           subtype T1 T2 = subtype T' T2.
Proof.
  intros.

  remember (subtype T1 T2) as sub_fn; subst T1.
  
  unfold subtype, subtype_func in Heqsub_fn;
    simpl in Heqsub_fn;
    rewrite fix_sub_eq_ext in Heqsub_fn;
    simpl in Heqsub_fn;
    fold subtype_func in Heqsub_fn;
    auto.

  destruct T2; auto.
  
  contradiction H0; auto.
  contradiction (H3 v l T2); auto.
  contradiction (H4 v l T2); auto.
  contradiction (H2 v l T2_1 T2_2); auto.
  contradiction (H5 l T2); auto.
  contradiction (H7 l T2); auto.
  contradiction (H6 l T2); auto.
  contradiction (H8 l T2); auto.
  contradiction H9; auto.
  contradiction (H10 T2_1 T2_2); auto.

Qed.