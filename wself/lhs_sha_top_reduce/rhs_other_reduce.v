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
Set Implicit Arguments.

Import WfExtensionality.

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