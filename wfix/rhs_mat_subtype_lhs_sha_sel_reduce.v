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

Lemma subtype_sha_sel_sel_low_reduce : 
  forall T1 x1 L1 ss1 T1', T1 = (t_sha_sel x1 L1 ss1 T1') ->
                      forall T2 x2 L2 T2', T2 = (t_sel_low x2 L2 T2') ->
                                      subtype T1 T2 = orb (subtype T1 T2')
                                                          (subtype T1' T2).
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

Lemma subtype_sha_sel_sel_equ_reduce : 
  forall T1 x1 L1 ss1 T1', T1 = (t_sha_sel x1 L1 ss1 T1') ->
                      forall T2 x2 L2 T2', T2 = (t_sel_equ x2 L2 T2') ->
                                      subtype T1 T2 = orb (subtype T1 T2')
                                                          (subtype T1' T2).
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

Lemma subtype_sha_sel_low_reduce :
  forall T1 x1 L1 ss1 T1', T1 = (t_sha_sel x1 L1 ss1 T1') ->
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

Lemma subtype_sha_sel_upp_reduce :
  forall T1 x1 L1 ss1 T1', T1 = (t_sha_sel x1 L1 ss1 T1') ->
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

Lemma subtype_sha_sel_equ_reduce :
  forall T1 x1 L1 ss1 T1', T1 = (t_sha_sel x1 L1 ss1 T1') ->
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

Lemma subtype_sha_sel_nom_reduce :
  forall T1 x1 L1 ss1 T1', T1 = (t_sha_sel x1 L1 ss1 T1') ->
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

Lemma subtype_sha_sel_nil_reduce :
  forall T1 x1 L1 ss1 T1', T1 = (t_sha_sel x1 L1 ss1 T1') ->
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

Lemma subtype_sha_sel_con_reduce :
  forall T1 x1 L1 ss1 T1', T1 = (t_sha_sel x1 L1 ss1 T1') ->
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

Lemma subtype_sha_sel_other_reduce :
  forall T1 x L ss1 T1', T1 = (t_sha_sel x L ss1 T1') ->
                    forall T2, (T2 <> t_top) ->
                          (forall x L T2', T2 <> (t_sel_low x L T2')) ->
                          (forall x L T2', T2 <> (t_sel_equ x L T2')) ->
                          (forall L2 T2', T2 <> (t_upp L2 T2')) ->
                          (forall L2 T2', T2 <> (t_equ L2 T2')) ->
                          (forall L2 T2', T2 <> (t_low L2 T2')) ->
                          (forall L2 T2', T2 <> (t_nom L2 T2')) ->
                          (T2 <> t_nil) ->
                          (forall T2' Ts2, T2 <> (t_con T2' Ts2)) ->
                          subtype T1 T2 = subtype T1' T2.
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
  contradiction (H1 v l T2); auto.
  contradiction (H2 v l T2); auto.
  contradiction (H3 l T2); auto.
  contradiction (H5 l T2); auto.
  contradiction (H4 l T2); auto.
  contradiction (H6 l T2); auto.
  contradiction H7; auto.
  contradiction (H8 T2_1 T2_2); auto.
Qed.

Lemma subtype_sha_sel_reduce :
  forall T1 x1 L1 ss1 T1', T1 = t_sha_sel x1 L1 ss1 T1' ->
                      forall T2, subtype T1 T2 = match T2 with
                                            | t_top => true
                                            | t_sel_low x2 L2 T2' => orb (subtype T1 T2')
                                                                        (subtype T1' T2)
                                            | t_sel_equ x2 L2 T2' => orb (subtype T1 T2')
                                                                        (subtype T1' T2)
                                            | t_upp _ _ => false
                                            | t_low _ _ => false
                                            | t_equ _ _ => false
                                            | t_nom _ _ => false
                                            | t_nil => false
                                            | t_con _ _ => false
                                                            
                                            | _ => subtype T1' T2
                                            end.
Proof.
  intros; subst; destruct T2.
  
  apply subtype_top; crush.

  apply subtype_sha_sel_other_reduce with (x:=x1)(L:=L1)(ss1:=ss1); crush.

  apply subtype_sha_sel_other_reduce with (x:=x1)(L:=L1)(ss1:=ss1); crush.
  
  eapply subtype_sha_sel_sel_low_reduce; crush.

  eapply subtype_sha_sel_sel_equ_reduce; crush.

  apply subtype_sha_sel_other_reduce with (x:=x1)(L:=L1)(ss1:=ss1); crush.

  apply subtype_sha_sel_other_reduce with (x:=x1)(L:=L1)(ss1:=ss1); crush.

  apply subtype_sha_sel_other_reduce with (x:=x1)(L:=L1)(ss1:=ss1); crush.

  apply subtype_sha_sel_other_reduce with (x:=x1)(L:=L1)(ss1:=ss1); crush.

  apply subtype_sha_sel_other_reduce with (x:=x1)(L:=L1)(ss1:=ss1); crush.

  apply subtype_sha_sel_other_reduce with (x:=x1)(L:=L1)(ss1:=ss1); crush.

  apply subtype_sha_sel_upp_reduce
    with
      (x1:=x1)(L1:=L1)(ss1:=ss1)
      (T1':=T1')(L2:=l)(T2':=T2);
    crush.

  apply subtype_sha_sel_low_reduce
    with
      (x1:=x1)(L1:=L1)(ss1:=ss1)
      (T1':=T1')(L2:=l)(T2':=T2);
    crush.

  apply subtype_sha_sel_equ_reduce
    with
      (x1:=x1)(L1:=L1)(ss1:=ss1)
      (T1':=T1')(L2:=l)(T2':=T2);
    crush.

  apply subtype_sha_sel_nom_reduce
    with
      (x1:=x1)(L1:=L1)(ss1:=ss1)
      (T1':=T1')(L2:=l)(T2':=T2);
    crush.

  apply subtype_sha_sel_nil_reduce
    with
      (x1:=x1)(L1:=L1)
      (T1':=T1')(ss1:=ss1);
    crush.

  apply subtype_sha_sel_con_reduce
    with
      (x1:=x1)(L1:=L1)(ss1:=ss1)
      (T1':=T1')(T2':=T2_1)(Ts2:=T2_2);
    crush.
Qed.