Require Import List.
Require Import Bool.
Require Import Arith.
Require Import Peano_dec.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Program.Wf.
Require Import Coq.Program.Tactics.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Recdef.

Require Export common.CpdtTactics.
Require Import common.wyv_common.
Require Import common.rhs_mat_tree.


Require Export common.lhs_sel_equ_reduce.rhs_nil_reduce.
Require Export common.lhs_sel_equ_reduce.rhs_con_reduce.

Require Export common.lhs_sel_equ_reduce.rhs_sel_equ_reduce.
Require Export common.lhs_sel_equ_reduce.rhs_sel_upp_reduce.
Require Export common.lhs_sel_equ_reduce.rhs_sel_low_reduce.
Require Export common.lhs_sel_equ_reduce.rhs_sel_nom_reduce.
Require Export common.lhs_sel_equ_reduce.rhs_sel_bnd_reduce.

Require Export common.lhs_sel_equ_reduce.rhs_bot_reduce.

Require Export common.lhs_sel_equ_reduce.rhs_all_reduce.

Require Export common.lhs_sel_equ_reduce.rhs_rfn_sel_reduce.
Require Export common.lhs_sel_equ_reduce.rhs_rfn_top_reduce.
Require Export common.lhs_sel_equ_reduce.rhs_sha_sel_reduce.
Require Export common.lhs_sel_equ_reduce.rhs_sha_top_reduce.

Require Export common.lhs_sel_equ_reduce.rhs_upp_reduce.
Require Export common.lhs_sel_equ_reduce.rhs_nom_reduce.
Require Export common.lhs_sel_equ_reduce.rhs_equ_reduce.
Require Export common.lhs_sel_equ_reduce.rhs_low_reduce.

Set Implicit Arguments.

Import WfExtensionality.

Lemma subtype_sel_equ_reduce :
  forall T1 x1 L1 T1',
    T1 = (t_sel_equ x1 L1 T1') ->
    forall T2, subtype T1 T2 = match T2 with
                          | t_top => true
                          | t_sel_low x2 L2 T2' => orb (andb (eq_var x1 x2) (eq_label L1 L2)) (orb (subtype T1' T2) (subtype T1 T2'))
                          | t_sel_equ x2 L2 T2' => orb (andb (eq_var x1 x2) (eq_label L1 L2)) (orb (subtype T1' T2) (subtype T1 T2'))
                          | t_sel_upp x2 L2 _ => orb (andb (eq_var x1 x2) (eq_label L1 L2)) (subtype T1' T2)
                          | t_sel_nom x2 L2 _ => orb (andb (eq_var x1 x2) (eq_label L1 L2)) (subtype T1' T2)
                          | t_sel_bnd x2 L2 => orb (andb (eq_var x1 x2) (eq_label L1 L2)) (subtype T1' T2)
                          | t_upp L2 T2' => false
                          | t_low L2 T2' => false
                          | t_equ L2 T2' => false
                          | t_nom L2 T2' => false

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
    apply subtype_sel_equ_bot_reduce
      with (x1:=x1)(L1:=L1);
    auto.

  subst;
    apply subtype_sel_equ_sel_upp_reduce
      with (x1:=x1)(L1:=L1)(T2':=T2);
    auto.

  subst;
    apply subtype_sel_equ_sel_low_reduce
      with (x1:=x1)(L1:=L1)(T2':=T2);
    auto.

  subst;
    apply subtype_sel_equ_sel_equ_reduce
      with (x1:=x1)(L1:=L1)(T2':=T2);
    auto.

  subst;
    apply subtype_sel_equ_sel_nom_reduce
      with (x1:=x1)(L1:=L1)(T2':=T2);
    auto.

  subst;
    apply subtype_sel_equ_sel_bnd_reduce
      with (x1:=x1)(L1:=L1);
    auto.

  subst;
    apply subtype_sel_equ_rfn_top_reduce
      with (x1:=x1)(L1:=L1)(Ts:=T2);
    auto.

  subst;
    apply subtype_sel_equ_rfn_sel_reduce
      with (x1:=x1)(L1:=L1)(x2:=v)(L2:=l)(Ts:=T2_1)(T':=T2_2);
    auto.

  subst;
    apply subtype_sel_equ_sha_top_reduce
      with (x1:=x1)(L1:=L1)(x2:=v)(L2:=l)(ss2:=d);
    auto.

  subst;
    apply subtype_sel_equ_sha_sel_reduce
      with (x1:=x1)(L1:=L1)(x2:=v)(L2:=l)(T':=T2)(ss2:=d);
    auto.

  subst;
    apply subtype_sel_equ_all_reduce
      with (x1:=x1)(L1:=L1)(T:=T2_1)(T':=T2_2);
    auto.

  subst;
    apply subtype_sel_equ_upp_reduce
      with (x1:=x1)(L1:=L1)(T1':=T1')(L2:=l)(T2':=T2);
    auto.

  subst;
    apply subtype_sel_equ_low_reduce
      with (x1:=x1)(L1:=L1)(T1':=T1')(L2:=l)(T2':=T2);
    auto.

  subst;
    apply subtype_sel_equ_equ_reduce
      with (x1:=x1)(L1:=L1)(T1':=T1')(L2:=l)(T2':=T2);
    auto.

  subst;
    apply subtype_sel_equ_nom_reduce
      with (x1:=x1)(L1:=L1)(T1':=T1')(L2:=l)(T2':=T2);
    auto.

  subst;
    eapply subtype_sel_equ_nil_reduce; eauto.

  subst;
    eapply subtype_sel_equ_con_reduce; eauto.
Qed.