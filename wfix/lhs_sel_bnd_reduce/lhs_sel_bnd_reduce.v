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

Require Export common.lhs_sel_bnd_reduce.rhs_nil_reduce.
Require Export common.lhs_sel_bnd_reduce.rhs_con_reduce.

Require Export common.lhs_sel_bnd_reduce.rhs_sel_equ_reduce.
Require Export common.lhs_sel_bnd_reduce.rhs_sel_upp_reduce.
Require Export common.lhs_sel_bnd_reduce.rhs_sel_low_reduce.
Require Export common.lhs_sel_bnd_reduce.rhs_sel_nom_reduce.
Require Export common.lhs_sel_bnd_reduce.rhs_sel_bnd_reduce.

Require Export common.lhs_sel_bnd_reduce.rhs_bot_reduce.

Require Export common.lhs_sel_bnd_reduce.rhs_all_reduce.

Require Export common.lhs_sel_bnd_reduce.rhs_rfn_sel_reduce.
Require Export common.lhs_sel_bnd_reduce.rhs_rfn_top_reduce.
Require Export common.lhs_sel_bnd_reduce.rhs_sha_sel_reduce.
Require Export common.lhs_sel_bnd_reduce.rhs_sha_top_reduce.

Require Export common.lhs_sel_bnd_reduce.rhs_upp_reduce.
Require Export common.lhs_sel_bnd_reduce.rhs_nom_reduce.
Require Export common.lhs_sel_bnd_reduce.rhs_equ_reduce.
Require Export common.lhs_sel_bnd_reduce.rhs_low_reduce.

Set Implicit Arguments.

Import WfExtensionality.

Lemma subtype_sel_bnd_reduce :
  forall T1 x1 L1,
    T1 = (t_sel_bnd x1 L1) ->
    forall T2, subtype T1 T2 = match T2 with
                          | t_top => true
                          | t_sel_low x2 L2 T2' => orb (andb (eq_var x1 x2) (eq_label L1 L2)) (subtype T1 T2')
                          | t_sel_equ x2 L2 T2' => orb (andb (eq_var x1 x2) (eq_label L1 L2)) (subtype T1 T2')
                          | t_sel_bnd x2 L2 => andb (eq_var x1 x2) (eq_label L1 L2)
                          | t_sel_upp x2 L2 _ => andb (eq_var x1 x2) (eq_label L1 L2)
                          | t_sel_nom x2 L2 _ => andb (eq_var x1 x2) (eq_label L1 L2)
                          | _ => false
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
    apply subtype_sel_bnd_bot_reduce
      with (x1:=x1)(L1:=L1);
    auto.

  subst;
    apply subtype_sel_bnd_sel_upp_reduce
      with (x1:=x1)(L1:=L1)(T2':=T2);
    auto.

  subst;
    apply subtype_sel_bnd_sel_low_reduce
      with (x1:=x1)(L1:=L1)(T2':=T2);
    auto.

  subst;
    apply subtype_sel_bnd_sel_equ_reduce
      with (x1:=x1)(L1:=L1)(T2':=T2);
    auto.

  subst;
    apply subtype_sel_bnd_sel_nom_reduce
      with (x1:=x1)(L1:=L1)(T2':=T2);
    auto.

  subst;
    apply subtype_sel_bnd_sel_bnd_reduce
      with (x1:=x1)(L1:=L1);
    auto.

  subst;
    apply subtype_sel_bnd_rfn_top_reduce
      with (x1:=x1)(L1:=L1)(Ts:=T2);
    auto.

  subst;
    apply subtype_sel_bnd_rfn_sel_reduce
      with (x1:=x1)(L1:=L1)(x2:=v)(L2:=l)(Ts:=T2_1)(T':=T2_2);
    auto.

  subst;
    apply subtype_sel_bnd_sha_top_reduce
      with (x1:=x1)(L1:=L1)(x2:=v)(L2:=l)(ss2:=d);
    auto.

  subst;
    apply subtype_sel_bnd_sha_sel_reduce
      with (x1:=x1)(L1:=L1)(x2:=v)(L2:=l)(T':=T2)(ss2:=d);
    auto.

  subst;
    apply subtype_sel_bnd_all_reduce
      with (x1:=x1)(L1:=L1)(T:=T2_1)(T':=T2_2);
    auto.

  subst;
    apply subtype_sel_bnd_upp_reduce
      with (x1:=x1)(L1:=L1)(L2:=l)(T2':=T2);
    auto.

  subst;
    apply subtype_sel_bnd_low_reduce
      with (x1:=x1)(L1:=L1)(L2:=l)(T2':=T2);
    auto.

  subst;
    apply subtype_sel_bnd_equ_reduce
      with (x1:=x1)(L1:=L1)(L2:=l)(T2':=T2);
    auto.

  subst;
    apply subtype_sel_bnd_nom_reduce
      with (x1:=x1)(L1:=L1)(L2:=l)(T2':=T2);
    auto.

  subst; eapply subtype_sel_bnd_nil_reduce; eauto.

  subst; eapply subtype_sel_bnd_con_reduce; eauto.
Qed.