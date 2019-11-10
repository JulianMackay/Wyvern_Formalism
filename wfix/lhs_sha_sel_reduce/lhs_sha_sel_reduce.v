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

Require Export common.lhs_sha_sel_reduce.rhs_con_reduce.
Require Export common.lhs_sha_sel_reduce.rhs_nil_reduce.

Require Export common.lhs_sha_sel_reduce.rhs_sel_low_reduce.
Require Export common.lhs_sha_sel_reduce.rhs_sel_equ_reduce.

Require Export common.lhs_sha_sel_reduce.rhs_low_reduce.
Require Export common.lhs_sha_sel_reduce.rhs_equ_reduce.
Require Export common.lhs_sha_sel_reduce.rhs_upp_reduce.
Require Export common.lhs_sha_sel_reduce.rhs_nom_reduce.

Require Export common.lhs_sha_sel_reduce.rhs_other_reduce.

Set Implicit Arguments.

Import WfExtensionality.

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
                                            | t_nom _ _ _ => false
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
      (T1':=T1')(L2:=l)(t2:=t)(T2':=T2);
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