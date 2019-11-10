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

Require Export common.lhs_rfn_sel_reduce.rhs_con_reduce.
Require Export common.lhs_rfn_sel_reduce.rhs_nil_reduce.

Require Export common.lhs_rfn_sel_reduce.rhs_equ_reduce.
Require Export common.lhs_rfn_sel_reduce.rhs_low_reduce.
Require Export common.lhs_rfn_sel_reduce.rhs_upp_reduce.
Require Export common.lhs_rfn_sel_reduce.rhs_nom_reduce.

Require Export common.lhs_rfn_sel_reduce.rhs_rfn_sel_eq_reduce.
Require Export common.lhs_rfn_sel_reduce.rhs_rfn_sel_neq_reduce.
Require Export common.lhs_rfn_sel_reduce.rhs_rfn_top_reduce.

Require Export common.lhs_rfn_sel_reduce.rhs_sel_equ_reduce.
Require Export common.lhs_rfn_sel_reduce.rhs_sel_low_reduce.

Require Export common.lhs_rfn_sel_reduce.rhs_other_reduce.

Set Implicit Arguments.

Import WfExtensionality.

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