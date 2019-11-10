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

Lemma subtype_rfn_sel_rfn_sel_eq_reduce : 
  forall T1 x L Ts1 T1', T1 = (t_rfn_sel x L Ts1 T1') ->
            forall T2 Ts2 T2', T2 = (t_rfn_sel x L Ts2 T2') ->
                          subtype T1 T2 = subtype Ts1 Ts2 || subtype T1' T2.
Proof.
  intros.

  remember (subtype T1 T2) as sub_fn; subst T1 T2.
  
  unfold subtype, subtype_func in Heqsub_fn;
    simpl in Heqsub_fn;
    rewrite fix_sub_eq_ext in Heqsub_fn;
    simpl in Heqsub_fn;
    fold subtype_func in Heqsub_fn;
    auto.

  rewrite eq_var_refl, eq_label_refl in Heqsub_fn.
  repeat rewrite andb_true_l in Heqsub_fn.
  auto.
Qed.

Lemma subtype_rfn_sel_rfn_top_reduce : 
  forall T1 x L Ts1 T1', T1 = (t_rfn_sel x L Ts1 T1') ->
                    forall T2 Ts2, T2 = (t_rfn_top Ts2) ->
                              subtype T1 T2 = subtype T1' T2.
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

Lemma subtype_rfn_sel_sel_low_reduce : 
  forall T1 x L Ts T, T1 = (t_rfn_sel x L Ts T) ->
                 forall T2 x L T', T2 = (t_sel_low x L T') ->
                              subtype T1 T2 = orb (subtype T1 T')
                                                  (subtype T T2).
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

Lemma subtype_rfn_sel_sel_equ_reduce : 
  forall T1 x L Ts T, T1 = (t_rfn_sel x L Ts T) ->
                 forall T2 x L T', T2 = (t_sel_equ x L T') ->
                              subtype T1 T2 = orb (subtype T1 T')
                                                  (subtype T T2).
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

Lemma subtype_rfn_sel_rfn_sel_neq_reduce : 
  forall T1 x1 L1 Ts1 T1', T1 = (t_rfn_sel x1 L1 Ts1 T1') ->
                      forall T2 x2 L2 Ts2 T2', T2 = (t_rfn_sel x2 L2 Ts2 T2') ->
                                          (x1 <> x2 \/ L1 <> L2) ->
                                          subtype T1 T2 = subtype T1' T2.
Proof.
  intros.

  remember (subtype T1 T2) as sub_fn; subst T1 T2.
  
  unfold subtype, subtype_func in Heqsub_fn;
    simpl in Heqsub_fn;
    rewrite fix_sub_eq_ext in Heqsub_fn;
    simpl in Heqsub_fn;
    fold subtype_func in Heqsub_fn;
    auto.

  destruct H1 as [Heq|Heq].

  apply eq_var_neq in Heq;
    rewrite Heq in Heqsub_fn.

  rewrite andb_false_l, orb_false_l in Heqsub_fn.
  auto.
  
  apply eq_label_neq in Heq;
    rewrite Heq in Heqsub_fn.
  rewrite andb_false_r, andb_false_l, orb_false_l in Heqsub_fn.
  auto.
Qed.

Lemma subtype_rfn_sel_upp_reduce :
  forall T1 x1 L1 Ts1 T', T1 = (t_rfn_sel x1 L1 Ts1 T') ->
                     forall T2 L2 T2', T2 = t_upp L2 T2' ->
                                  subtype T1 T2 = false.
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

Lemma subtype_rfn_sel_low_reduce :
  forall T1 x1 L1 Ts1 T', T1 = (t_rfn_sel x1 L1 Ts1 T') ->
                     forall T2 L2 T2', T2 = t_low L2 T2' ->
                                  subtype T1 T2 = false.
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

Lemma subtype_rfn_sel_equ_reduce :
  forall T1 x1 L1 Ts1 T', T1 = (t_rfn_sel x1 L1 Ts1 T') ->
                     forall T2 L2 T2', T2 = t_equ L2 T2' ->
                                  subtype T1 T2 = false.
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

Lemma subtype_rfn_sel_nom_reduce :
  forall T1 x1 L1 Ts1 T', T1 = (t_rfn_sel x1 L1 Ts1 T') ->
                     forall T2 L2 T2', T2 = t_nom L2 T2' ->
                                  subtype T1 T2 = false.
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

Lemma subtype_rfn_sel_nil_reduce :
  forall T1 x1 L1 Ts1 T', T1 = (t_rfn_sel x1 L1 Ts1 T') ->
                     forall T2, T2 = t_nil ->
                           subtype T1 T2 = false.
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

Lemma subtype_rfn_sel_con_reduce :
  forall T1 x1 L1 Ts1 T', T1 = (t_rfn_sel x1 L1 Ts1 T') ->
                     forall T2 T2' Ts2, T2 = t_con T2' Ts2 ->
                                   subtype T1 T2 = false.
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

Lemma subtype_rfn_sel_reduce :
  forall T1 x1 L1 Ts1 T', T1 = t_rfn_sel x1 L1 Ts1 T' ->
                     forall T2, subtype T1 T2 = match T2 with
                                           | t_top => true
                                           | t_sel_low x L T => orb (subtype T1 T)
                                                                   (subtype T' T2)
                                           | t_sel_equ x L T => orb (subtype T1 T)
                                                                   (subtype T' T2)
                                           | t_rfn_top _ => subtype T' T2
                                           | t_rfn_sel x2 L2 Ts2 _ => orb (andb ((andb (eq_var x1 x2) (eq_label L1 L2)))
                                                                               (subtype Ts1 Ts2))
                                                                         (subtype T' T2)
                                           | t_upp _ _ => false
                                           | t_low _ _ => false
                                           | t_equ _ _ => false
                                           | t_nom _ _ => false
                                           | t_nil => false
                                           | t_con _ _ => false
                                                           
                                           | _ => subtype T' T2
                                           end.
Proof.
  intros; subst; destruct T2.
  
  apply subtype_top; crush.

  apply subtype_rfn_sel_other_reduce
    with
      (x1:=x1)(L1:=L1)(Ts1:=Ts1);
    crush.

  apply subtype_rfn_sel_other_reduce
    with
      (x1:=x1)(L1:=L1)(Ts1:=Ts1);
    crush.
  
  eapply subtype_rfn_sel_sel_low_reduce; crush.

  eapply subtype_rfn_sel_sel_equ_reduce; crush.

  apply subtype_rfn_sel_other_reduce
    with
      (x1:=x1)(L1:=L1)(Ts1:=Ts1);
    crush.

  eapply subtype_rfn_sel_rfn_top_reduce; crush.
  destruct (eq_var_dec x1 v) as [Heq|Heq];
    rewrite Heq;
    [rewrite andb_true_l
    |rewrite andb_false_l, orb_false_l].
  destruct (eq_label_dec L1 l) as [Heq'|Heq'];
    rewrite Heq';
    [rewrite andb_true_l
    |rewrite andb_false_l, orb_false_l].
  apply beq_var_eq in Heq; subst v.
  apply beq_label_eq in Heq'; subst l.
  eapply subtype_rfn_sel_rfn_sel_eq_reduce; eauto.

  eapply subtype_rfn_sel_rfn_sel_neq_reduce; eauto.
  right; apply neqb_label_neq in Heq'; auto.

  eapply subtype_rfn_sel_rfn_sel_neq_reduce; eauto.
  left; apply neqb_var_neq in Heq; auto.
  
  apply subtype_rfn_sel_other_reduce
    with
      (x1:=x1)(L1:=L1)(Ts1:=Ts1);
    crush.

  apply subtype_rfn_sel_other_reduce
    with
      (x1:=x1)(L1:=L1)(Ts1:=Ts1);
    crush.

  apply subtype_rfn_sel_other_reduce
    with
      (x1:=x1)(L1:=L1)(Ts1:=Ts1);
    crush.
  
  apply subtype_rfn_sel_upp_reduce
    with
      (x1:=x1)(L1:=L1)(Ts1:=Ts1)
      (T':=T')(L2:=l)(T2':=T2);
    crush.

  apply subtype_rfn_sel_low_reduce
    with
      (x1:=x1)(L1:=L1)(Ts1:=Ts1)
      (T':=T')(L2:=l)(T2':=T2);
    crush.

  apply subtype_rfn_sel_equ_reduce
    with
      (x1:=x1)(L1:=L1)(Ts1:=Ts1)
      (T':=T')(L2:=l)(T2':=T2);
    crush.

  apply subtype_rfn_sel_nom_reduce
    with
      (x1:=x1)(L1:=L1)(Ts1:=Ts1)
      (T':=T')(L2:=l)(T2':=T2);
    crush.

  apply subtype_rfn_sel_nil_reduce
    with
      (x1:=x1)(L1:=L1)(Ts1:=Ts1)
      (T':=T');
    crush.

  apply subtype_rfn_sel_con_reduce
    with
      (x1:=x1)(L1:=L1)(Ts1:=Ts1)
      (T':=T')(T2':=T2_1)(Ts2:=T2_2);
    crush.

Qed.