Require Export List.
Require Export Bool.
Require Export Arith.
Require Export Peano_dec.
Require Export Coq.Arith.PeanoNat.
Require Export Coq.Program.Wf.
Require Export Coq.Program.Tactics.
Require Export Coq.Logic.FunctionalExtensionality.
Require Export Recdef.
Set Implicit Arguments.

Import WfExtensionality.

Require Export common.CpdtTactics.
Require Export common.wyv_common.
Require Export common.rhs_mat_tree.

Lemma subtype_nom_nom_reduce : 
  forall T1 L1 T1', T1 = (t_nom L1 T1') ->
               forall T2 L2 T2', T2 = (t_nom L2 T2') ->
                            subtype T1 T2 = (eq_label L1 L2) && (eq_tree T1' T2').
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