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

Lemma subtype_sel_upp_sel_upp_reduce : 
  forall T1 x1 L1 T1', T1 = (t_sel_upp x1 L1 T1') ->
                  forall T2 x2 L2 T2', T2 = (t_sel_upp x2 L2 T2') ->
                                  subtype T1 T2 = orb (andb (eq_var x1 x2)
                                                            (eq_label L1 L2))
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

Lemma subtype_sel_upp_sel_low_reduce : 
  forall T1 x1 L1 T1', T1 = (t_sel_upp x1 L1 T1') ->
                  forall T2 x2 L2 T2', T2 = (t_sel_low x2 L2 T2') ->
                                  subtype T1 T2 = orb (andb (eq_var x1 x2)
                                                            (eq_label L1 L2))
                                                      (orb (subtype T1' T2)
                                                           (subtype T1 T2')).
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

Lemma subtype_sel_upp_sel_equ_reduce : 
  forall T1 x1 L1 T1', T1 = (t_sel_upp x1 L1 T1') ->
                  forall T2 x2 L2 T2', T2 = (t_sel_equ x2 L2 T2') ->
                                  subtype T1 T2 = orb (andb (eq_var x1 x2)
                                                            (eq_label L1 L2))
                                                      (orb (subtype T1' T2)
                                                           (subtype T1 T2')).
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

Lemma subtype_sel_upp_sel_nom_reduce : 
  forall T1 x1 L1 T1', T1 = (t_sel_upp x1 L1 T1') ->
                  forall T2 x2 L2 T2', T2 = (t_sel_nom x2 L2 T2') ->
                                  subtype T1 T2 = orb (andb (eq_var x1 x2)
                                                            (eq_label L1 L2))
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

Lemma subtype_sel_upp_upp_reduce : 
  forall T1 x1 L1 T1', T1 = (t_sel_upp x1 L1 T1') ->
                  forall T2 L2 T2', T2 = (t_upp L2 T2') ->
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

Lemma subtype_sel_upp_low_reduce : 
  forall T1 x1 L1 T1', T1 = (t_sel_upp x1 L1 T1') ->
                  forall T2 L2 T2', T2 = (t_low L2 T2') ->
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


Lemma subtype_sel_upp_equ_reduce : 
  forall T1 x1 L1 T1', T1 = (t_sel_upp x1 L1 T1') ->
                  forall T2 L2 T2', T2 = (t_equ L2 T2') ->
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


Lemma subtype_sel_upp_nom_reduce : 
  forall T1 x1 L1 T1', T1 = (t_sel_upp x1 L1 T1') ->
                  forall T2 L2 t T2', T2 = (t_nom L2 t T2') ->
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

Lemma subtype_sel_upp_rfn_top_reduce : 
  forall T1 x1 L1 T1', T1 = (t_sel_upp x1 L1 T1') ->
                  forall T2 Ts, T2 = (t_rfn_top Ts) ->
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

Lemma subtype_sel_upp_rfn_sel_reduce : 
  forall T1 x1 L1 T1', T1 = (t_sel_upp x1 L1 T1') ->
                  forall x2 L2 T2 Ts T', T2 = (t_rfn_sel x2 L2 Ts T') ->
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

Lemma subtype_sel_upp_sha_top_reduce : 
  forall T1 x1 L1 T1', T1 = (t_sel_upp x1 L1 T1') ->
                  forall T2 x2 L2 ss2, T2 = (t_sha_top x2 L2 ss2) ->
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

Lemma subtype_sel_upp_sha_sel_reduce : 
  forall T1 x1 L1 T1', T1 = (t_sel_upp x1 L1 T1') ->
                  forall T2 x2 L2 ss2 T', T2 = (t_sha_sel x2 L2 ss2 T') ->
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

Lemma subtype_sel_upp_all_reduce : 
  forall T1 x1 L1 T1', T1 = (t_sel_upp x1 L1 T1') ->
                  forall T2 T T', T2 = (t_all T T') ->
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

Lemma subtype_sel_upp_bot_reduce : 
  forall T1 x1 L1 T1', T1 = (t_sel_upp x1 L1 T1') ->
                  subtype T1 t_bot = subtype T1' t_bot.
Proof.
  intros.

  remember (subtype T1 t_bot) as sub_fn; subst T1.
  
  unfold subtype, subtype_func in Heqsub_fn;
    simpl in Heqsub_fn;
    rewrite fix_sub_eq_ext in Heqsub_fn;
    simpl in Heqsub_fn;
    fold subtype_func in Heqsub_fn;
    auto.  
Qed.

Lemma subtype_sel_upp_nil_reduce :
  forall T1 x1 L1 T1', T1 = (t_sel_upp x1 L1 T1') ->
                  subtype T1 t_nil = false.
Proof.
  intros; subst.
  
  unfold subtype, subtype_func;
    simpl;
    rewrite fix_sub_eq_ext;
    simpl;
    fold subtype_func.

  auto.

Qed.

Lemma subtype_sel_upp_con_reduce :
  forall T1 x1 L1 T1', T1 = (t_sel_upp x1 L1 T1') ->
                  forall T2 T2' Ts, T2 = t_con T2' Ts ->
                               subtype T1 T2 = false.
Proof.
  intros; subst.
  
  unfold subtype, subtype_func;
    simpl;
    rewrite fix_sub_eq_ext;
    simpl;
    fold subtype_func.

  auto.

Qed.

Lemma subtype_sel_upp_reduce :
  forall T1 x1 L1 T1',
    T1 = (t_sel_upp x1 L1 T1') ->
    forall T2, subtype T1 T2 = match T2 with
                          | t_top => true
                          | t_sel_low x2 L2 T2' => orb (andb (eq_var x1 x2) (eq_label L1 L2)) (orb (subtype T1' T2) (subtype T1 T2'))
                          | t_sel_equ x2 L2 T2' => orb (andb (eq_var x1 x2) (eq_label L1 L2)) (orb (subtype T1' T2) (subtype T1 T2'))
                          | t_sel_upp x2 L2 _ => orb (andb (eq_var x1 x2) (eq_label L1 L2)) (subtype T1' T2)
                          | t_sel_nom x2 L2 _ => orb (andb (eq_var x1 x2) (eq_label L1 L2)) (subtype T1' T2)
                          | t_upp L2 T2' => false
                          | t_low L2 T2' => false
                          | t_equ L2 T2' => false
                          | t_nom L2 _ T2' => false

                          | t_nil => false
                          | t_con _ _ => false
                                          
                          | _ => subtype T1' T2
                          end.
Proof.
  intros.

  destruct T2.

  apply subtype_top;
    subst;
    intros;
    intro Hcontra;
    inversion Hcontra.

  subst;
    apply subtype_sel_upp_bot_reduce
      with (x1:=x1)(L1:=L1);
    auto.

  subst;
    apply subtype_sel_upp_sel_upp_reduce
      with (x1:=x1)(L1:=L1)(T2':=T2);
    auto.

  subst;
    apply subtype_sel_upp_sel_low_reduce
      with (x1:=x1)(L1:=L1)(T2':=T2);
    auto.

  subst;
    apply subtype_sel_upp_sel_equ_reduce
      with (x1:=x1)(L1:=L1)(T2':=T2);
    auto.

  subst;
    apply subtype_sel_upp_sel_nom_reduce
      with (x1:=x1)(L1:=L1)(T2':=T2);
    auto.

  subst;
    apply subtype_sel_upp_rfn_top_reduce
      with (x1:=x1)(L1:=L1)(Ts:=T2);
    auto.

  subst;
    apply subtype_sel_upp_rfn_sel_reduce
      with (x1:=x1)(L1:=L1)(x2:=v)(L2:=l)(Ts:=T2_1)(T':=T2_2);
    auto.

  subst;
    apply subtype_sel_upp_sha_top_reduce
      with (x1:=x1)(L1:=L1)(x2:=v)(L2:=l)(ss2:=d);
    auto.

  subst;
    apply subtype_sel_upp_sha_sel_reduce
      with (x1:=x1)(L1:=L1)(x2:=v)(L2:=l)(T':=T2)(ss2:=d);
    auto.

  subst;
    apply subtype_sel_upp_all_reduce
      with (x1:=x1)(L1:=L1)(T:=T2_1)(T':=T2_2);
    auto.

  subst;
    apply subtype_sel_upp_upp_reduce
      with (x1:=x1)(L1:=L1)(T1':=T1')(L2:=l)(T2':=T2);
    auto.

  subst;
    apply subtype_sel_upp_low_reduce
      with (x1:=x1)(L1:=L1)(T1':=T1')(L2:=l)(T2':=T2);
    auto.

  subst;
    apply subtype_sel_upp_equ_reduce
      with (x1:=x1)(L1:=L1)(T1':=T1')(L2:=l)(T2':=T2);
    auto.

  subst;
    eapply subtype_sel_upp_nom_reduce
      with (x1:=x1)(L1:=L1)(T1':=T1')(L2:=l)(T2':=T2);
    eauto.

  subst T1; erewrite subtype_sel_upp_nil_reduce; eauto.

  subst T1; erewrite subtype_sel_upp_con_reduce; eauto.
  
Qed.