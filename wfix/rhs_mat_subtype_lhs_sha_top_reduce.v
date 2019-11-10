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

Lemma subtype_sha_top_sel_low_reduce : 
  forall T1 x1 L1 ss1, T1 = (t_sha_top x1 L1 ss1) ->
                  forall T2 x2 L2 T2', T2 = (t_sel_low x2 L2 T2') ->
                                  subtype T1 T2 = subtype T1 T2'.
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

Lemma subtype_sha_top_sel_equ_reduce : 
  forall T1 x1 L1 ss1, T1 = (t_sha_top x1 L1 ss1) ->
                  forall T2 x2 L2 T', T2 = (t_sel_equ x2 L2 T') ->
                                 subtype T1 T2 = subtype T1 T'.
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

Lemma subtype_sha_top_other_reduce :
  forall T x L ss1, T = (t_sha_top x L ss1) ->
               forall T', (T' <> t_top) ->
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
    |contradiction (H1 v l T'); auto
    |contradiction (H2 v l T'); auto].
Qed.

Lemma subtype_sha_top_reduce :
  forall T1 x1 L1 ss1, T1 = t_sha_top x1 L1 ss1 ->
                  forall T2, subtype T1 T2 = match T2 with
                                        | t_top => true
                                        | t_sel_low x L T => subtype T1 T
                                        | t_sel_equ x L T => subtype T1 T
                                        | _ => false
                                        end.
Proof.
  intros; subst; destruct T2;
    try solve [eapply subtype_sha_top_other_reduce; crush].

  apply subtype_top; crush.

  eapply subtype_sha_top_sel_low_reduce; crush.

  eapply subtype_sha_top_sel_equ_reduce; crush.  
Qed.
