Require Export List.
Require Export Bool.
Require Export Arith.
Require Export Peano_dec.
Require Export Coq.Arith.PeanoNat.
Require Export Coq.Program.Wf.
Require Export Coq.Program.Tactics.
Require Export Coq.Logic.FunctionalExtensionality.
Require Export Recdef.

Add LoadPath "..".
Require Import CpdtTactics.
Require Import wyv_common.
Require Import rhs_mat_tree.
Set Implicit Arguments.

Import WfExtensionality.

Lemma subtype_sel_low_reduce :
  forall T1 x1 L1 T1',
    T1 = (t_sel_low x1 L1 T1') ->
    forall T2, subtype T1 T2 = match T2 with
                          | t_top => true
                          | t_sel_low x2 L2 T2' => orb (andb (eq_var x1 x2) (eq_label L1 L2)) (subtype T1 T2')
                          | t_sel_equ x2 L2 T2' => orb (andb (eq_var x1 x2) (eq_label L1 L2)) (subtype T1 T2')
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
    apply subtype_sel_low_bot_reduce
      with (x1:=x1)(L1:=L1)(T1':=T1');
    auto.

  subst;
    apply subtype_sel_low_sel_upp_reduce
      with (x1:=x1)(L1:=L1)(T2':=T2)(T1':=T1');
    auto.

  subst;
    apply subtype_sel_low_sel_low_reduce
      with (x1:=x1)(L1:=L1)(T2':=T2)(T1':=T1');
    auto.

  subst;
    apply subtype_sel_low_sel_equ_reduce
      with (x1:=x1)(L1:=L1)(T2':=T2)(T1':=T1');
    auto.

  subst;
    apply subtype_sel_low_sel_nom_reduce
      with (x1:=x1)(L1:=L1)(T2':=T2)(T1':=T1');
    auto.

  subst;
    apply subtype_sel_low_rfn_top_reduce
      with (x1:=x1)(L1:=L1)(Ts:=T2)(T1':=T1');
    auto.

  subst;
    apply subtype_sel_low_rfn_sel_reduce
      with (x1:=x1)(L1:=L1)(x2:=v)(L2:=l)(Ts:=T2_1)(T':=T2_2)(T1':=T1');
    auto.

  subst;
    apply subtype_sel_low_sha_top_reduce
      with (x1:=x1)(L1:=L1)(x2:=v)(L2:=l)(T1':=T1')(ss2:=d);
    auto.

  subst;
    apply subtype_sel_low_sha_sel_reduce
      with (x1:=x1)(L1:=L1)(x2:=v)(L2:=l)(T':=T2)(T1':=T1')(ss2:=d);
    auto.

  subst;
    apply subtype_sel_low_all_reduce
      with (x1:=x1)(L1:=L1)(T:=T2_1)(T':=T2_2)(T1':=T1');
    auto.

  subst;
    apply subtype_sel_low_upp_reduce
      with (x1:=x1)(L1:=L1)(T1':=T1')(L2:=l)(T2':=T2);
    auto.

  subst;
    apply subtype_sel_low_low_reduce
      with (x1:=x1)(L1:=L1)(T1':=T1')(L2:=l)(T2':=T2);
    auto.

  subst;
    apply subtype_sel_low_equ_reduce
      with (x1:=x1)(L1:=L1)(T1':=T1')(L2:=l)(T2':=T2);
    auto.

  subst;
    apply subtype_sel_low_nom_reduce
      with (x1:=x1)(L1:=L1)(T1':=T1')(L2:=l)(T2':=T2);
    auto.

  subst; eapply subtype_sel_low_nil_reduce; eauto.

  subst; eapply subtype_sel_low_con_reduce; eauto.
Qed.