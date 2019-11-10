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

Import WfExtensionality.

Lemma subtype_sel_nom_sel_bnd_reduce : 
  forall T1 x1 L1 T1', T1 = (t_sel_nom x1 L1 T1') ->
                  forall T2 x2 L2, T2 = (t_sel_bnd x2 L2) ->
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