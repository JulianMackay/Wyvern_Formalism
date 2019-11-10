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

Lemma subtype_all_all_reduce : 
  forall T T1 T2, T = (t_all T1 T2) ->
             forall T' T1' T2', T' = (t_all T1' T2') ->
                           subtype T T' = andb (subtype T1' T1)
                                               (subtype T2 T2').
Proof.
  intros.

  remember (subtype T T') as sub_fn; subst T T'.
  
  unfold subtype, subtype_func in Heqsub_fn;
    simpl in Heqsub_fn;
    rewrite fix_sub_eq_ext in Heqsub_fn;
    simpl in Heqsub_fn;
    fold subtype_func in Heqsub_fn;
    auto.
Qed.

Lemma subtype_all_sel_low_reduce : 
  forall T T1 T2, T = (t_all T1 T2) ->
             forall T' x L T'', T' = (t_sel_low x L T'') ->
                           subtype T T' = subtype T T''.
Proof.
  intros.

  remember (subtype T T') as sub_fn; subst T T'.
  
  unfold subtype, subtype_func in Heqsub_fn;
    simpl in Heqsub_fn;
    rewrite fix_sub_eq_ext in Heqsub_fn;
    simpl in Heqsub_fn;
    fold subtype_func in Heqsub_fn;
    auto.
Qed.

Lemma subtype_all_sel_equ_reduce : 
  forall T T1 T2, T = (t_all T1 T2) ->
             forall T' x L T'', T' = (t_sel_equ x L T'') ->
                           subtype T T' = subtype T T''.
Proof.
  intros.

  remember (subtype T T') as sub_fn; subst T T'.
  
  unfold subtype, subtype_func in Heqsub_fn;
    simpl in Heqsub_fn;
    rewrite fix_sub_eq_ext in Heqsub_fn;
    simpl in Heqsub_fn;
    fold subtype_func in Heqsub_fn;
    auto.
Qed.

Lemma subtype_all_other_reduce :
  forall T T1 T2, T = (t_all T1 T2) ->
             forall T', (T' <> t_top) ->
                   (forall T1' T2', T' <> (t_all T1' T2')) ->
                   (forall x L T'', T' <> (t_sel_low x L T'')) ->
                   (forall x L T'', T' <> (t_sel_equ x L T'')) ->
                   subtype T T' = false.
Proof.
  intros.

  remember (subtype T T') as sub_fn; subst T.
  
  unfold subtype, subtype_func in Heqsub_fn;
    simpl in Heqsub_fn;
    rewrite fix_sub_eq_ext in Heqsub_fn;
    simpl in Heqsub_fn;
    fold subtype_func in Heqsub_fn;
    auto.

  destruct T'; auto;
    [contradiction H0; auto
    |contradiction (H2 v l T'); auto
    |contradiction (H3 v l T'); auto
    |contradiction (H1 T'1 T'2); auto].
  
Qed.

Lemma subtype_all_reduce :
  forall T1 Ta1 Tb1, T1 = (t_all Ta1 Tb1) ->
                forall T2, subtype T1 T2 = match T2 with
                                      | t_top => true
                                      | t_sel_low x L T => subtype T1 T
                                      | t_sel_equ x L T => subtype T1 T
                                      | t_all Ta2 Tb2 => andb (subtype Ta2 Ta1) (subtype Tb1 Tb2)
                                      | _ => false
                                      end.
Proof.
  intros; subst; destruct T2;
    try solve [eapply subtype_all_other_reduce; crush].

  apply subtype_top; crush.

  eapply subtype_all_sel_low_reduce; crush.

  eapply subtype_all_sel_equ_reduce; crush.

  eapply subtype_all_all_reduce; crush.
Qed.