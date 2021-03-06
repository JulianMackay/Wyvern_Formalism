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

Lemma subtype_rfn_top_rfn_top_reduce : 
  forall T1 Ts1, T1 = (t_rfn_top Ts1) ->
            forall T2 Ts2, T2 = (t_rfn_top Ts2) ->
                      subtype T1 T2 = subtype Ts1 Ts2.
Proof.
  intros.

  remember (subtype T1 T2) as sub_fn; subst T1 T2.
  
  unfold subtype, subtype_func in Heqsub_fn;
    simpl in Heqsub_fn;
    rewrite fix_sub_eq_ext in Heqsub_fn;
    simpl in Heqsub_fn;
    fold subtype_func in Heqsub_fn;
    auto.
Qed.

Lemma subtype_rfn_top_sel_low_reduce : 
  forall T1 Ts, T1 = (t_rfn_top Ts) ->
           forall T2 x L T, T2 = (t_sel_low x L T) ->
                       subtype T1 T2 = subtype T1 T.
Proof.
  intros.

  remember (subtype T1 T2) as sub_fn; subst T1 T2.
  
  unfold subtype, subtype_func in Heqsub_fn;
    simpl in Heqsub_fn;
    rewrite fix_sub_eq_ext in Heqsub_fn;
    simpl in Heqsub_fn;
    fold subtype_func in Heqsub_fn;
    auto.
Qed.

Lemma subtype_rfn_top_sel_equ_reduce : 
  forall T1 Ts, T1 = (t_rfn_top Ts) ->
             forall T2 x L T, T2 = (t_sel_equ x L T) ->
                         subtype T1 T2 = subtype T1 T.
Proof.
  intros.

  remember (subtype T1 T2) as sub_fn; subst T1 T2.
  
  unfold subtype, subtype_func in Heqsub_fn;
    simpl in Heqsub_fn;
    rewrite fix_sub_eq_ext in Heqsub_fn;
    simpl in Heqsub_fn;
    fold subtype_func in Heqsub_fn;
    auto.
Qed.


Lemma subtype_rfn_top_other_reduce :
  forall T1 Ts1, T1 = (t_rfn_top Ts1) ->
             forall T2, (T2 <> t_top) ->
                   (forall Ts2, T2 <> (t_rfn_top Ts2)) ->
                   (forall x L T, T2 <> (t_sel_low x L T)) ->
                   (forall x L T, T2 <> (t_sel_equ x L T)) ->
                   subtype T1 T2 = false.
Proof.
  intros.

  remember (subtype T1 T2) as sub_fn; subst T1.
  
  unfold subtype, subtype_func in Heqsub_fn;
    simpl in Heqsub_fn;
    rewrite fix_sub_eq_ext in Heqsub_fn;
    simpl in Heqsub_fn;
    fold subtype_func in Heqsub_fn;
    auto.

  destruct T2; auto;
    [contradiction H0; auto
    |contradiction (H2 v l T2); auto
    |contradiction (H3 v l T2); auto
    |contradiction (H1 T2); auto].
  
Qed.

Lemma subtype_rfn_top_reduce :
  forall T1 Ts1, T1 = (t_rfn_top Ts1) ->
            forall T2, subtype T1 T2 = match T2 with
                                  | t_top => true
                                  | t_sel_low x L T => subtype T1 T
                                  | t_sel_equ x L T => subtype T1 T
                                  | t_rfn_top Ts2 => subtype Ts1 Ts2
                                  | _ => false
                                  end.
Proof.
  intros; subst; destruct T2;
    try solve [eapply subtype_rfn_top_other_reduce; crush].

  apply subtype_top; crush.

  eapply subtype_rfn_top_sel_low_reduce; crush.

  eapply subtype_rfn_top_sel_equ_reduce; crush.

  eapply subtype_rfn_top_rfn_top_reduce; crush.
Qed.