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

Require Import common.lhs_sel_nom_reduce.lhs_sel_nom_reduce.
Require Import common.lhs_sel_upp_reduce.lhs_sel_upp_reduce.
Require Import common.lhs_sel_equ_reduce.lhs_sel_equ_reduce.
Require Import common.lhs_sel_low_reduce.lhs_sel_low_reduce.

Require Import common.lhs_all_reduce.lhs_all_reduce.
Require Import common.lhs_con_reduce.lhs_con_reduce.
Require Import common.lhs_nil_reduce.lhs_nil_reduce.
Require Import common.lhs_top_reduce.lhs_top_reduce.

Require Import common.lhs_upp_reduce.lhs_upp_reduce.
Require Import common.lhs_low_reduce.lhs_low_reduce.
Require Import common.lhs_nom_reduce.lhs_nom_reduce.
Require Import common.lhs_equ_reduce.lhs_equ_reduce.

Require Import common.lhs_rfn_top_reduce.lhs_rfn_top_reduce.
Require Import common.lhs_sha_top_reduce.lhs_sha_top_reduce.
Require Import common.lhs_rfn_sel_reduce.lhs_rfn_sel_reduce.
Require Import common.lhs_sha_sel_reduce.lhs_sha_sel_reduce.

Require Import common.subtype_by_bound.subtype_lhs_sel_upp_reduce.
Require Import common.subtype_by_bound.subtype_lhs_sel_equ_reduce.
Require Import common.subtype_by_bound.subtype_lhs_sel_nom_reduce.
Require Import common.subtype_by_bound.subtype_lhs_rfn_sel_reduce.
Require Import common.subtype_by_bound.subtype_lhs_sha_sel_reduce.
Require Import common.subtype_by_bound.subtype_rhs_sel_equ_reduce.
Require Import common.subtype_by_bound.subtype_rhs_sel_low_reduce.
Require Import common.wfix.
Set Implicit Arguments.

Ltac var_auto :=
  match goal with
  | [ |- context[if ?x =? ?y then _ else _] ] =>
    destruct (eq_nat_dec x y) as [|];
    [subst y;
     rewrite <- beq_nat_refl
    |try match goal with
         | [Hneq : x <> y |- _ ] => assert (Hneqb := Hneq);
                                 apply Nat.eqb_neq in Hneqb;
                                 try rewrite Hneqb in *;
                                 clear Hneqb
         end]
  | [H : context[if ?x =? ?y then _ else _] |- _] =>
    destruct (eq_nat_dec x y) as [|];
    [subst y;
     rewrite <- beq_nat_refl in H
    |try match goal with
         | [Hneq : x <> y |- _ ] => assert (Hneqb := Hneq);
                                 apply Nat.eqb_neq in Hneqb;
                                 try rewrite Hneqb in *;
                                 clear Hneqb
         end]
  end.

Ltac subtype_reduce :=
  match goal with
  | [Hsub : subtype (t_sel_upp ?x ?L ?T) _ = true |- _] =>
    rewrite subtype_sel_upp_reduce
      with
        (x1:=x)(L1:=L)(T1':=T)
      in Hsub; [|auto]
  | [Hsub : subtype (t_sel_low ?x ?L ?T) _ = true |- _] =>
    rewrite subtype_sel_low_reduce
      with
        (x1:=x)(L1:=L)(T1':=T)
      in Hsub; [|auto]
  | [Hsub : subtype (t_sel_equ ?x ?L ?T) _ = true |- _] =>
    rewrite subtype_sel_equ_reduce
      with
        (x1:=x)(L1:=L)(T1':=T)
      in Hsub; [|auto]
  | [Hsub : subtype (t_sel_nom ?x ?L ?T) _ = true |- _] =>
    rewrite subtype_sel_nom_reduce
      with
        (x1:=x)(L1:=L)(T1':=T)
      in Hsub; [|auto]
                 
  | [ |- context [subtype (t_sel_upp ?x ?L ?T)]] =>
    rewrite subtype_lhs_sel_upp_reduce
      with
        (x1:=x)(L1:=L)(T1':=T)
  | [ |- context [subtype (t_sel_low ?x ?L ?T)]] =>
    rewrite subtype_sel_low_reduce
      with
        (x1:=x)(L1:=L)(T1':=T)
  | [ |- context [subtype (t_sel_equ ?x ?L ?T)]] =>
    rewrite subtype_lhs_sel_equ_reduce
      with
        (x1:=x)(L1:=L)(T1':=T)
  | [ |- context [subtype (t_sel_nom ?x ?L ?T)]] =>
    rewrite subtype_lhs_sel_nom_reduce
      with
        (x1:=x)(L1:=L)(T1':=T)

  (*upp, low, nom, equ*)
  | [Hsub : subtype (t_upp ?L ?T) _ = true |- _] =>
    rewrite subtype_upp_reduce
      with
        (L1:=L)(T1':=T)
      in Hsub; [|auto]
  | [Hsub : subtype (t_low ?L ?T) _ = true |- _] =>
    rewrite subtype_low_reduce
      with
        (L1:=L)(T1':=T)
      in Hsub; [|auto]
  | [Hsub : subtype (t_nom?L ?T) _ = true |- _] =>
    rewrite subtype_nom_reduce
      with
        (L1:=L)(T1':=T)
      in Hsub; [|auto]
  | [Hsub : subtype (t_equ ?L ?T) _ = true |- _] =>
    rewrite subtype_equ_reduce
      with
        (L1:=L)(T1':=T)
      in Hsub; [|auto]
                 
  | [ |- context [subtype (t_upp ?L ?T)]] =>
    rewrite subtype_upp_reduce
      with
        (L1:=L)(T1':=T)

  (*rfn*)
  | [Hsub : context [subtype (t_rfn_top _) _] |- _] =>
    erewrite subtype_rfn_top_reduce in Hsub; eauto
  | [Hsub : context [subtype (t_rfn_sel _ _ _ _) _] |- _] =>
    erewrite subtype_rfn_sel_reduce in Hsub; eauto
  | [Hsub : context [subtype (t_sha_top _ _ _) _] |- _] =>
    erewrite subtype_sha_top_reduce in Hsub; eauto
  | [Hsub : context [subtype (t_sha_sel _ _ _ _) _] |- _] =>
    erewrite subtype_sha_sel_reduce in Hsub; eauto

  (*top*)
  | [Hsub : context [subtype t_top _] |- _] => erewrite subtype_lhs_top_reduce in Hsub; eauto

  (*all*)
  | [Hsub : context [subtype (t_all _ _) _] |- _] =>  erewrite subtype_all_reduce in Hsub; eauto

  (*decls*)
  | [Hsub : context [subtype t_nil _] |- _] =>  erewrite subtype_nil_reduce in Hsub; eauto
  | [Hsub : context [subtype (t_con _ _) _] |- _] =>  erewrite subtype_con_reduce in Hsub; eauto
  end.

Ltac contra_auto :=
  match goal with
  | [H : ?P, Hnot : ~ ?P |- _] => contradiction Hnot; auto
  end.

Ltac bool_auto :=
  repeat match goal with
         | [H : _ && _ = true |- _] => apply andb_prop in H; destruct H
         | [H : _ || _ = true |- _] => apply orb_prop in H; destruct H
         | [H : false = true |- _] => inversion H
         end.

Ltac eq_auto :=
  repeat match goal with
         | [H : eq_var ?x ?y = true |- _] => apply beq_var_eq in H;
                                           subst y
         | [H : eq_label ?l1 ?l2 = true |- _] => apply beq_label_eq in H;
                                               subst l2
         end.

Ltac sub_auto :=
  match goal with
  | [|- ?G1 ⊢ (sel ?x ?L) ≤ (sel ?x ?L) ⊣ ?G2] => apply s_refl
  end.

Ltac s_upper :=
  match goal with
  | [H : _ ⊢ ?x ∋ (type ?L ⩽ _) |- _ ⊢ sel ?x ?L ≤ _ ⊣ _] => try solve [eapply s_upper_1; eauto]
  | [H : _ ⊢ ?x ∋ (type ?L ≝ _) |- _ ⊢ sel ?x ?L ≤ _ ⊣ _] => try solve [eapply s_upper_2; eauto]
  | [H : _ ⊢ ?x ∋ (type ?L ⪯ _) |- _ ⊢ sel ?x ?L ≤ _ ⊣ _] => try solve [eapply s_upper_3; eauto]
  end.

Ltac s_lower :=
  match goal with
  | [H : _ ⊢ ?x ∋ (type ?L ⩾ ?t) |- _ ⊢ _ ≤ sel ?x ?L ⊣ _] => try solve [eapply s_lower_1 with (t2:=t); eauto]
  | [H : _ ⊢ ?x ∋ (type ?L ≝ ?t) |- _ ⊢ _ ≤ sel ?x ?L ⊣ _] => try solve [eapply s_lower_2 with (t2:=t); eauto]
  end.

Ltac s_ext :=
  match goal with
  | [H : _ ⊢ ?t ≤⦂⦂ ?t' |- _ ⊢ ?t ≤ _ ⊣ _] => try solve [eapply s_extend; eauto]
  end.
    
Lemma material_is_not_shape :
  forall t, is_material t ->
       ~is_shape t.
Proof.
  intros t H;
    induction H;
    subst;
    intros Hcontra;
    inversion Hcontra;
    subst;
    auto.
Qed.

Lemma shape_is_not_material :
  forall t, is_shape t ->
       ~is_material t.
Proof.
  intros t H;
    induction H;
    subst;
    intros Hcontra;
    inversion Hcontra;
    subst;
    auto.
Qed.

Ltac shape_auto :=
  match goal with
  | [Hsha : is_shape ?t, Hmat : is_material ?t |- _] =>
    apply shape_is_not_material in Hsha; bool_auto
  end.

Lemma subst_closed_mutind :
  (forall t n, closed t n ->
          forall x, ([x /t n] t) = t) /\

  (forall s n, closed_s s n ->
          forall x, ([x /s n] s) = s) /\

  (forall ss n, closed_ss ss n ->
           forall x, ([x /ss n] ss) = ss).
Proof.
  apply closed_mutind;
    intros;
    simpl;
    crush.

  destruct x as [m|m]; simpl;
    [auto
    |var_auto; crush].  
Qed.

Lemma subst_closed :
  (forall t n, closed t n ->
          forall x, ([x /t n] t) = t).
Proof.
  destruct subst_closed_mutind; crush.
Qed.

Lemma subst_closed_s :
  (forall s n, closed_s s n ->
          forall x, ([x /s n] s) = s).
Proof.
  destruct subst_closed_mutind; crush.
Qed.

Lemma subst_closed_ss :
  (forall ss n, closed_ss ss n ->
           forall x, ([x /ss n] ss) = ss).
Proof.
  destruct subst_closed_mutind; crush.
Qed.

  
Lemma closed_subst_mutind :
  (forall t n, closed t n ->
          forall x m, closed ([c_ x/t m] t) n) /\

  (forall s n, closed_s s n ->
          forall x m, closed_s ([c_ x/s m] s) n) /\
  
  (forall ss n, closed_ss ss n ->
           forall x m, closed_ss ([c_ x/ss m] ss) n).
Proof.
  apply closed_mutind;
    intros;
    simpl;
    auto.

  destruct x as [x|x];
    simpl;
    auto.
  var_auto.
  apply cl_sel; crush.
  apply cl_sel; auto.
Qed.

Lemma closed_subst :
  (forall t n, closed t n ->
          forall x m, closed ([c_ x/t m] t) n).
Proof.
  destruct closed_subst_mutind; crush.
Qed.

Lemma closed_s_subst :
  (forall s n, closed_s s n ->
          forall x m, closed_s ([c_ x/s m] s) n).
Proof.
  destruct closed_subst_mutind; crush.
Qed.

Lemma closed_ss_subst :  
  (forall ss n, closed_ss ss n ->
           forall x m, closed_ss ([c_ x/ss m] ss) n).
Proof.
  destruct closed_subst_mutind; crush.
Qed.

Lemma is_material_subst_mutind :
  (forall t, is_material t ->
        forall x n, is_material ([c_ x /t n] t)) /\

  (forall s, is_material_s s ->
        forall x n, is_material_s ([c_ x /s n] s)) /\

  (forall ss, is_material_ss ss ->
         forall x n, is_material_ss ([c_ x /ss n] ss)).
Proof.
  apply is_material_mutind;
    intros;
    auto;
    match goal with
    | [ |- is_material ([_ /t _] (sel _ _)) ] => simpl; apply m_sel; eauto
    | [ |- is_material ([_ /t _] (_ str _ rts)) ] => simpl; apply m_rfn; eauto
    | [ |- is_material ([_ /t _] (all _ ∙ _)) ] => simpl; apply m_all; eauto
    | [ |- is_material_s ([_ /s _] (type _ ⩽ _)) ] => simpl; apply m_upp; eauto
    | [ |- is_material_s ([_ /s _] (type _ ⩾ _)) ] => simpl; apply m_low; eauto
    | [ |- is_material_s ([_ /s _] (type _ ≝ _)) ] => simpl; apply m_equ; eauto
    | [ |- is_material_s ([_ /s _] (type _ ⪯ _)) ] => simpl; apply m_nom; eauto
    | [ |- is_material_ss ([_ /ss _] (d_nil)) ] => simpl; apply m_nil; eauto
    | [ |- is_material_ss ([_ /ss _] (d_con _ _)) ] => simpl; apply m_con; eauto
    end.
  apply closed_ss_subst;
    auto.
Qed.

Lemma is_material_subst :
  (forall t, is_material t ->
        forall x n, is_material ([c_ x /t n] t)).
Proof.
  destruct is_material_subst_mutind; crush.
Qed.

Lemma is_material_s_subst :
  (forall s, is_material_s s ->
        forall x n, is_material_s ([c_ x /s n] s)).
Proof.
  destruct is_material_subst_mutind; crush.
Qed.

Lemma is_material_ss_subst :
  (forall ss, is_material_ss ss ->
         forall x n, is_material_ss ([c_ x /ss n] ss)).
Proof.
  destruct is_material_subst_mutind; crush.
Qed.



Ltac mat_auto :=
  try match goal with
      | [H : is_material (?t str ?ss rts) |- _] =>
        match (match goal with
            | [H1 : is_material t, H2 : is_material_ss ss |- _] => true
            | _ => false
            end) with
        | true => fail
        | false => inversion H; subst
        end
      | [H : is_material (all ?t ∙ ?t') |- _] =>
        match (match goal with
            | [H1 : is_material t, H2 : is_material t' |- _] => true
            | _ => false
            end) with
        | true => fail
        | false => inversion H; subst
        end
                                                                           
      | [ H : is_material_s (type _ ⩽ ?t) |- _] => 
        match (match goal with
            | [H' : is_material t |- _] => true
            | _ => false
            end) with
        | true => fail
        | false => inversion H; subst
        end
      | [ H : is_material_s (type _ ⩾ ?t) |- _] => 
        match (match goal with
            | [H' : is_material t |- _] => true
            | _ => false
            end) with
        | true => fail
        | false => inversion H; subst
        end
      | [ H : is_material_s (type _ ≝ ?t) |- _] => 
        match (match goal with
            | [H' : is_material t |- _] => true
            | _ => false
            end) with
        | true => fail
        | false => inversion H; subst
        end
      | [ H : is_material_s (type _ ⪯ ?t) |- _] => 
        match (match goal with
            | [H' : is_material t |- _] => true
            | _ => false
            end) with
        | true => fail
        | false => inversion H; subst
        end
      | [ H : is_material_ss (d_con ?s ?ss) |- _ ] => 
        match (match goal with
            | [H1 : is_material_s s, H2 : is_material_ss ss |- _] => true
            | _ => false
            end) with
        | true => fail
        | false => inversion H; subst
        end
          
      | [ |- is_material ([_ /t _] (sel _ _)) ] => simpl; apply m_sel; eauto
      | [ |- is_material ([_ /t _] (_ str _ rts)) ] => simpl; apply m_rfn; eauto
      | [ |- is_material ([_ /t _] (all _ ∙ _)) ] => simpl; apply m_all; eauto
      | [ |- is_material_s ([_ /s _] (type _ ⩽ _)) ] => simpl; apply m_upp; eauto
      | [ |- is_material_s ([_ /s _] (type _ ⩾ _)) ] => simpl; apply m_low; eauto
      | [ |- is_material_s ([_ /s _] (type _ ≝ _)) ] => simpl; apply m_equ; eauto
      | [ |- is_material_s ([_ /s _] (type _ ⪯ _)) ] => simpl; apply m_nom; eauto
      | [ |- is_material_ss ([_ /ss _] (d_nil)) ] => simpl; apply m_nil; eauto
      | [ |- is_material_ss ([_ /ss _] (d_con _ _)) ] => simpl; apply m_con; eauto

      | [_ : is_material ?t |- is_material ([_ /t _] ?t)] => apply is_material_subst; eauto
      | [_ : is_material_s ?s |- is_material_s ([_ /s _] ?s)] => apply is_material_s_subst; eauto
      | [_ : is_material_ss ?ss |- is_material_ss ([_ /ss _] ?ss)] => apply is_material_ss_subst; eauto
      end.

Inductive ord : env -> Prop :=
| ord_nil : ord nil
| ord_con : forall t G, (forall n, n >= length G ->
                         n notin_t t) ->
                   ord G ->
                   ord (t::G).

Definition closed_env (G : env) := forall n t, In t G -> closed t n.

Lemma get_lt :
  forall A (G : list A) n t, get n G = Some t ->
                        n < (length G).
Proof.
  intros A G;
    induction G as [|a G'];
    intros;
    [destruct n; simpl in H; inversion H|].

  destruct n as [|n'];
    [crush|simpl in H].
  apply IHG' in H. crush.
Qed.

Lemma mapping_lt :
  forall A (G : list A) n t, n ↦ t elem G ->
                        n < length G.
Proof.
  intros; unfold mapping in H; rewrite <- rev_length; eapply get_lt; eauto.
Qed.

Lemma ord_typing1 :
  forall G x t, G ⊢ x ⦂ t ->
           forall n, n >= length G ->
                n notin_v x.
Proof.
  intros;
    inversion H;
    subst;
    apply mapping_lt in H1;
    crush.
Qed.

Lemma ord_in :
  forall G, ord G ->
       forall t, In t G ->
            forall n, n >= length G ->
                 n notin_t t.
Proof.
  intros H Hord;
    induction Hord;
    intros;
    [crush|].
  inversion H0; [subst t0|].
  apply H; crush.
  apply IHHord; crush.
Qed.

Lemma in_get :
  forall A (G : list A) n t, get n G = Some t ->
                        In t G.
Proof.
  intros A G;
    induction G as [|a G'];
    intros;
    [destruct n; crush|].
  destruct n as [|n'];
    simpl in H;
    inversion H;
    subst;
    crush.
  right; eauto.
Qed.

Lemma in_mapping :
  forall A n t (G : list A), n ↦ t elem G ->
                        In t G.
Proof.
  intros.
  unfold mapping in H;
    apply in_get in H;
    apply in_rev in H;
    auto.
Qed.

Lemma ord_typing2 :
  forall G x t, G ⊢ x ⦂ t ->
           ord G ->
           forall n, n >= length G ->
                n notin_t t.
Proof.
  intros;
    inversion H;
    subst.
  apply in_mapping in H2.
  eapply ord_in; eauto.
Qed.

Lemma notin_subst_mutind :
  (forall n t, n notin_t t ->
          forall x, n notin_v x ->
               forall m, n notin_t ([x /t m] t)) /\
  
  (forall n s, n notin_s s ->
          forall x, n notin_v x ->
               forall m, n notin_s ([x /s m] s)) /\
  
  (forall n ss, n notin_ss ss ->
           forall x, n notin_v x ->
                forall m, n notin_ss ([x /ss m] ss)).
Proof.
  apply notin_mutind;
    intros;
    crush.

  simpl.
  destruct p; simpl; auto;
    var_auto; auto.
Qed.

Lemma notin_subst :
  (forall n t, n notin_t t ->
          forall x, n notin_v x ->
               forall m, n notin_t ([x /t m] t)).
Proof.
  destruct notin_subst_mutind; crush.
Qed.

Lemma notin_s_subst :  
  (forall n s, n notin_s s ->
          forall x, n notin_v x ->
               forall m, n notin_s ([x /s m] s)).
Proof.
  destruct notin_subst_mutind; crush.
Qed.

Lemma notin_ss_subst :  
  (forall n ss, n notin_ss ss ->
           forall x, n notin_v x ->
                forall m, n notin_ss ([x /ss m] ss)).
Proof.
  destruct notin_subst_mutind; crush.
Qed.

Lemma notin_in_ss :
  forall s ss, in_ss s ss ->
          forall n, n notin_ss ss ->
               n notin_s s.
Proof.
  intros s ss Hin;
    induction Hin;
    intros;
    inversion H; auto.
Qed.

Lemma subst_notin_mutind :
  (forall n t, n notin_t t ->
          forall x m t', t = ([x /t m] t') ->
                    n notin_t t') /\

  (forall n s, n notin_s s ->
          forall x m s', s = ([x /s m] s') ->
                    n notin_s s') /\

  (forall n ss, n notin_ss ss ->
           forall x m ss', ss = ([x /ss m] ss') ->
                      n notin_ss ss').
Proof.
  apply notin_mutind;
    intros;
    try match goal with
        | [H : _ = ([_ /t _] ?t) |- _] => destruct t; simpl in *; inversion H; subst; eauto
        | [H : _ = ([_ /s _] ?s) |- _] => destruct s; simpl in *; inversion H; subst; eauto
        | [H : _ = ([_ /ss _] ?ss) |- _] => destruct ss; simpl in *; inversion H; subst; eauto
        end;
    destruct v; auto.
Qed.

Lemma subst_notin :
  (forall n t, n notin_t t ->
          forall x m t', t = ([x /t m] t') ->
                    n notin_t t').
Proof.
  destruct subst_notin_mutind; crush.
Qed.

Lemma subst_notin_s :
  (forall n s, n notin_s s ->
          forall x m s', s = ([x /s m] s') ->
                    n notin_s s').
Proof.
  destruct subst_notin_mutind; crush.
Qed.

Lemma subst_notin_ss :
  (forall n ss, n notin_ss ss ->
           forall x m ss', ss = ([x /ss m] ss') ->
                      n notin_ss ss').
Proof.
  destruct subst_notin_mutind; crush.
Qed.

Lemma ord_has_contains :
  (forall G x s, G ⊢ x ∋ s ->
            ord G ->
            forall n, n >= length G ->
                 n notin_s s) /\
  
  (forall G t s, G ⊢ s ∈ t ->
            ord G ->
            forall n, n >= length G ->
                 n notin_t t ->
                 n notin_s s).
Proof.
  apply has_contains_mutind;
    intros.
  
  (*has*)
  inversion t0; subst.
  apply notin_s_subst;
    [apply H; auto;
     eapply ord_typing2;
     eauto
    |eapply ord_typing1;
     eauto].

  (*rfn1*)
  inversion H1;
    eapply notin_in_ss;
    eauto.

  (*rfn2*)
  inversion H2;
    apply H;
    eauto.

  (*sel upp*)
  apply H0; auto;
    eapply H in H1; [|eauto];
    inversion H1;
    eauto.

  (*sel equ*)
  apply H0; auto;
    eapply H in H1; [|eauto];
    inversion H1;
    eauto.

  (*sel nom*)
  apply H0; auto;
    eapply H in H1; [|eauto];
    inversion H1;
    eauto.
Qed.

Lemma ord_contains :
  (forall G t s, G ⊢ s ∈ t ->
            ord G ->
            forall n, n >= length G ->
                 n notin_t t ->
                 n notin_s s).
Proof.
  destruct ord_has_contains; crush.
Qed.

Lemma ord_has :
  (forall G x s, G ⊢ x ∋ s ->
            ord G ->
            forall n, n >= length G ->
                 n notin_s s).
Proof.
  destruct ord_has_contains; crush.
Qed.

Lemma ord_has' :
  (forall G x t, G ⊢ x ∋ t ->
            forall n, n >= length G ->
                 n notin_v x).
Proof.
  intros;
    destruct H;
    eapply ord_typing1; eauto.
Qed.

Lemma ord_merge :
  forall ss1 ss2 m, (forall n, n >= m ->
                     n notin_ss ss1) ->
               (forall n, n >= m ->
                     n notin_ss ss2) ->
               (forall n, n >= m ->
                     n notin_ss merge ss1 ss2).
Proof.
  intros ss1;
    induction ss1 as [|s ss];
    intros;
    auto.

  simpl.
  destruct (in_ds (id s) ss2).
  apply IHss with (m:=m); intros; eauto.
  apply H in H2;
    inversion H2;
    auto.

  apply ni_con.
  apply H in H1;
    inversion H1;
    auto.

  eapply IHss;
    eauto;
    intros.

  apply H in H2;
    inversion H2;
    auto.
  
Qed.

Lemma ord_flat :
  forall t ss m, (forall n, n >= m ->
                  n notin_t t) ->
            (forall n, n >= m ->
                  n notin_ss ss) ->
            forall t', flat t ss = Some t' ->
                  (forall n, n >= m ->
                        n notin_t t').
Proof.
  intros.
  destruct t;
    simpl in *;
    inversion H1;
    subst t';
    auto.

  apply ni_rfn;
    [apply H in H2;
     inversion H2;
     auto
    |eapply ord_merge;
     eauto;
     intros].
  apply H in H3;
    inversion H3;
    auto.
Qed.
            

Lemma ord_extends :
  (forall G t t', G ⊢ t ≤⦂⦂ t' ->
             ord G ->
             (forall n, n >= length G ->
                   n notin_t t) ->
             (forall n, n >= length G ->
                   n notin_t t')).
Proof.
  intros G t t' Hext;
    induction Hext;
    intros;
    try solve [eapply ord_has in H;
               eauto;
               inversion H;
               crush].

  eapply ord_flat with (ss:=ss)(t:=t');
    eauto;
    [intros;
     apply IHHext|];
    auto;
    intros.
  apply H1 in H4;
    inversion H4;
    auto.
  apply H1 in H3;
    inversion H3;
    auto.
Qed.

Lemma ord_extends' :
  (forall G x L t', G ⊢ (sel x L) ≤⦂⦂ t' ->
               (forall n, n >= length G ->
                     n notin_v x)).
Proof.
  intros.
  inversion H; subst;
    try solve [eapply ord_has'; eauto].
Qed.


Reserved Notation "x '⊢' G1 'equiv_v' G2" (at level 80).
Reserved Notation "t '⊢' G1 'equiv_t' G2" (at level 80).
Reserved Notation "s '⊢' G1 'equiv_s' G2" (at level 80).
Reserved Notation "ss '⊢' G1 'equiv_ss' G2" (at level 80).

Inductive equiv_ctx_var : env -> var -> env -> Prop :=
| ec_conc1 : forall G G' x t, G ⊢ x ⦂ t ->
                         G' ⊢ x ⦂ t ->
                         t ⊢ G equiv_t G' ->
                         x ⊢ G equiv_v G'
                           
| ec_conc2 : forall G G' n, n >= length G ->
                       n >= length G' ->
                       (c_ n) ⊢ G equiv_v G'

| ec_abst : forall G G' n, equiv_ctx_var G (a_ n) G'
where "x '⊢' G1 'equiv_v' G2" := (equiv_ctx_var G1 x G2)

with
equiv_ctx : env -> ty -> env -> Prop :=
| ec_top     : forall G1 G2, top ⊢ G1 equiv_t G2
| ec_bot     : forall G1 G2, bot ⊢ G1 equiv_t G2
| ec_sel : forall G1 G2 x L, x ⊢ G1 equiv_v G2 ->
                        (sel x L) ⊢ G1 equiv_t G2
                              
| ec_all     : forall G1 G2 t t', t ⊢ G1 equiv_t G2 ->
                             t' ⊢ G1 equiv_t G2 ->
                             (all t ∙ t') ⊢ G1 equiv_t G2
                                       
| ec_rfn     : forall G1 G2 t ss, t ⊢ G1 equiv_t G2 ->
                             ss ⊢ G1 equiv_ss G2 ->
                             (t str ss rts) ⊢ G1 equiv_t G2
where "t '⊢' G1 'equiv_t' G2" := (equiv_ctx G1 t G2)

with
equiv_ctx_s : env -> decl -> env -> Prop :=
| ec_upp : forall G1 G2 L t, t ⊢ G1 equiv_t G2 ->
                        (type L ⩽ t) ⊢ G1 equiv_s G2

| ec_low : forall G1 G2 L t, t ⊢ G1 equiv_t G2 ->
                        (type L ⩾ t) ⊢ G1 equiv_s G2
                                     
| ec_equ : forall G1 G2 L t, t ⊢ G1 equiv_t G2 ->
                        (type L ≝ t) ⊢ G1 equiv_s G2
                                     
| ec_nom : forall G1 G2 L t, t ⊢ G1 equiv_t G2 ->
                        (type L ⪯ t) ⊢ G1 equiv_s G2
where "s '⊢' G1 'equiv_s' G2" := (equiv_ctx_s G1 s G2)

with
equiv_ctx_ss : env -> decls -> env -> Prop :=
| ec_nil : forall G1 G2, d_nil ⊢ G1 equiv_ss G2
| ec_con : forall G1 G2 s ss, s ⊢ G1 equiv_s G2 ->
                         ss ⊢ G1 equiv_ss G2 ->
                         (d_con s ss) ⊢ G1 equiv_ss G2
where "ss '⊢' G1 'equiv_ss' G2" := (equiv_ctx_ss G1 ss G2).

Hint Constructors equiv_ctx_var equiv_ctx equiv_ctx_s equiv_ctx_ss.

Scheme equiv_ctx_var_mut_ind := Induction for equiv_ctx_var Sort Prop
  with equiv_ctx_mut_ind := Induction for equiv_ctx Sort Prop
  with equiv_ctx_s_mut_ind := Induction for equiv_ctx_s Sort Prop
  with equiv_ctx_ss_mut_ind := Induction for equiv_ctx_ss Sort Prop.

Combined Scheme equiv_ctx_mutind from equiv_ctx_var_mut_ind, equiv_ctx_mut_ind, equiv_ctx_s_mut_ind, equiv_ctx_ss_mut_ind.

Scheme equiv_ctx_var_mut_ind' := Induction for equiv_ctx_var Sort Prop
  with equiv_ctx_mut_ind' := Induction for equiv_ctx Sort Prop.

Combined Scheme equiv_ctx_mutind' from equiv_ctx_var_mut_ind', equiv_ctx_mut_ind'.

Lemma equiv_ctx_sym_mutind :
  (forall G x G', x ⊢ G equiv_v G' ->
             x ⊢ G' equiv_v G) /\

  (forall G t G', t ⊢ G equiv_t G' ->
             t ⊢ G' equiv_t G) /\

  (forall G s G', s ⊢ G equiv_s G' ->
             s ⊢ G' equiv_s G) /\
  
  (forall G ss G', ss ⊢ G equiv_ss G' ->
              ss ⊢ G' equiv_ss G).
Proof.
  apply equiv_ctx_mutind;
    intros;
    auto;
    destruct x; eauto.
Qed.

Lemma equiv_ctx_x_sym :
  (forall G x G', x ⊢ G equiv_v G' ->
             x ⊢ G' equiv_v G).
Proof.
  destruct equiv_ctx_sym_mutind; crush.
Qed.

Lemma equiv_ctx_t_sym :
  (forall G t G', t ⊢ G equiv_t G' ->
             t ⊢ G' equiv_t G).
Proof.
  destruct equiv_ctx_sym_mutind; crush.
Qed.

Lemma equiv_ctx_s_sym :
  (forall G s G', s ⊢ G equiv_s G' ->
             s ⊢ G' equiv_s G).
Proof.
  destruct equiv_ctx_sym_mutind; crush.
Qed.

Lemma equiv_ctx_ss_sym :  
  (forall G ss G', ss ⊢ G equiv_ss G' ->
              ss ⊢ G' equiv_ss G).
Proof.
  destruct equiv_ctx_sym_mutind; crush.
Qed.

Lemma typing_unique :
  forall G x t, G ⊢ x ⦂ t ->
           forall t', G ⊢ x ⦂ t' ->
                 t' = t.
Proof.
  intros.
  inversion H; inversion H0; subst.
  inversion H7; subst; auto.
  unfold mapping in H1, H5;
    rewrite H5 in H1.
  inversion H1; auto.
Qed.

Lemma subst_equiv_ctx_mutind :
  (forall G x G', x ⊢ G equiv_v G' ->
             forall y, y ⊢ G equiv_v G' ->
                  forall n, ([y /v n] x) ⊢ G equiv_v G') /\

  (forall G t G', t ⊢ G equiv_t G' ->
             forall y, y ⊢ G equiv_v G' ->
                  forall n, ([y /t n] t) ⊢ G equiv_t G') /\

  (forall G s G', s ⊢ G equiv_s G' ->
             forall y, y ⊢ G equiv_v G' ->
                  forall n, ([y /s n] s) ⊢ G equiv_s G') /\

  (forall G ss G', ss ⊢ G equiv_ss G' ->
              forall y, y ⊢ G equiv_v G' ->
                   forall n, ([y /ss n] ss) ⊢ G equiv_ss G').
Proof.
  apply equiv_ctx_mutind;
    intros;
    auto;
    simpl in *;
    try solve [try destruct x;
               simpl in *;
               try var_auto;
               eauto].
Qed.

Lemma subst_equiv_ctx_var :
  (forall G x G', equiv_ctx_var G x G' ->
             forall y, equiv_ctx_var G y G' ->
                  forall n, equiv_ctx_var G ([y /v n] x) G').
Proof.
  destruct subst_equiv_ctx_mutind; crush.
Qed.

Lemma subst_equiv_ctx :
  (forall G t G', equiv_ctx G t G' ->
             forall y, equiv_ctx_var G y G' ->
                  forall n, equiv_ctx G ([y /t n] t) G').
Proof.
  destruct subst_equiv_ctx_mutind; crush.
Qed.

Lemma subst_equiv_ctx_s :
  (forall G s G', equiv_ctx_s G s G' ->
             forall y, equiv_ctx_var G y G' ->
                  forall n, equiv_ctx_s G ([y /s n] s) G').
Proof.
  destruct subst_equiv_ctx_mutind; crush.
Qed.

Lemma subst_equiv_ctx_ss :
  (forall G ss G', equiv_ctx_ss G ss G' ->
              forall y, equiv_ctx_var G y G' ->
                   forall n, equiv_ctx_ss G ([y /ss n] ss) G').
Proof.
  destruct subst_equiv_ctx_mutind; crush.
Qed.

Lemma equiv_ctx_in_ss :
  forall s ss, in_ss s ss ->
          forall G G', ss ⊢ G equiv_ss G' ->
                  s ⊢ G equiv_s G'.
Proof.
  intros s ss Hin;
    induction Hin;
    intros;
    auto;
    inversion H; subst; eauto.
Qed.

Lemma has_contains_equiv_ctx_mutind :
  (forall G x s, G ⊢ x ∋ s ->
            forall G', equiv_ctx_var G x G' ->
                  equiv_ctx_s G s G') /\
  
  (forall G t s, G ⊢ s ∈ t ->
            forall G', equiv_ctx G t G' ->
                  equiv_ctx_s G s G').
Proof.
  apply has_contains_mutind;
    intros;
    auto.

  apply subst_equiv_ctx_s; auto.
  apply H; inversion H0; subst; eauto.
  apply typing_unique
    with
      (t:=t1)
    in t0; subst; eauto.
  inversion t0; subst.
  apply mapping_lt in H5.
  crush.
  inversion t0.
  eapply equiv_ctx_in_ss; inversion H; eauto.

  apply H; inversion H0; auto.

  apply H0.
  inversion H1; subst.
  apply H in H6; inversion H6; auto.

  apply H0.
  inversion H1; subst.
  apply H in H6; inversion H6; auto.

  apply H0.
  inversion H1; subst.
  apply H in H6; inversion H6; auto.
Qed.

Lemma has_equiv_ctx :
  (forall G x s, G ⊢ x ∋ s ->
            forall G', x ⊢ G equiv_v G' ->
                  s ⊢ G equiv_s G').
Proof.
  destruct has_contains_equiv_ctx_mutind; crush.
Qed.

Lemma contains_equiv_ctx :  
  (forall G t s, G ⊢ s ∈ t ->
            forall G', t ⊢ G equiv_t G' ->
                  s ⊢ G equiv_s G').
Proof.
  destruct has_contains_equiv_ctx_mutind; crush.
Qed.

Lemma equiv_ctx_has_contains_mutind :
  (forall G x s, G ⊢ x ∋ s ->
            forall G', equiv_ctx_var G x G' ->
                  G' ⊢ x ∋ s) /\
  
  (forall G t s, G ⊢ s ∈ t ->
            forall G', equiv_ctx G t G' ->
                  G' ⊢ s ∈ t).
Proof.
  apply has_contains_mutind;
    intros;
    eauto.

  eapply h_path with (t:=t); [|apply H];
    try solve [inversion H0; subst;
               [| |inversion t0];
               [apply typing_unique
                  with (t:=t1)
                 in t0;
                [subst t1; auto|auto]
               |inversion t0; subst;
                apply mapping_lt in H5;
                crush]].        

  apply c_rfn2; eauto.
  apply H; inversion H0; auto.

  apply c_upp with (t:=t);
    [apply H; inversion H1; auto
    |apply H0; auto].
  apply has_equiv_ctx with (G':=G') in h;
    [inversion h; auto|inversion H1; eauto].

  apply c_equ with (t:=t);
    [apply H; inversion H1; auto
    |apply H0; auto].
  apply has_equiv_ctx with (G':=G') in h;
    [inversion h; auto|inversion H1; eauto].

  apply c_nom with (t:=t);
    [apply H; inversion H1; auto
    |apply H0; auto].
  apply has_equiv_ctx with (G':=G') in h;
    [inversion h; auto|inversion H1; eauto].
  
Qed.

Lemma equiv_ctx_has :
  (forall G x s, G ⊢ x ∋ s ->
            forall G', equiv_ctx_var G x G' ->
                  G' ⊢ x ∋ s).
Proof.
  destruct equiv_ctx_has_contains_mutind; crush.
Qed.

Lemma equiv_ctx_contains :
  (forall G t s, G ⊢ s ∈ t ->
            forall G', equiv_ctx G t G' ->
                  G' ⊢ s ∈ t).
Proof.
  destruct equiv_ctx_has_contains_mutind; crush.
Qed.

Lemma get_some_app :
  forall A G n (t : A), get n G = Some t ->
                   forall G', get n (G ++ G') = Some t.
Proof.
  intros A G;
    induction G as [|a G'];
    intros;
    destruct n as [|n']; simpl in H;
      try solve [inversion H; eauto].

  simpl.
  apply IHG'; auto.
Qed.

Lemma mapping_weakening :
  forall A G n (t : A), n ↦ t elem G ->
                   forall t', n ↦ t elem (t'::G).
Proof.
  intros.
  unfold mapping in *; simpl.
  apply get_some_app; auto.
Qed.

Lemma typing_weakening :
  forall G x t, G ⊢ x ⦂ t ->
           forall t', (t'::G) ⊢ x ⦂ t.
Proof.
  intros.
  inversion H; subst.

  apply t_var, mapping_weakening; auto.
Qed.

Ltac equiv_ctx_auto :=
  repeat match goal with
         | [H : (sel _ _) ⊢ _ equiv_t _ |- _] => inversion H; subst; clear H
         | [H : (_ str _ rts) ⊢ _ equiv_t _ |- _] => inversion H; subst; clear H
         | [H : (all _ ∙ _) ⊢ _ equiv_t _ |- _] => inversion H; subst; clear H
                                                                   
         | [ |- (sel _ _) ⊢ _ equiv_t _] => apply ec_sel; eauto
         | [ |- (_ str _ rts) ⊢ _ equiv_t _] => apply ec_rfn; eauto
         | [ |- (all _ ∙ _) ⊢ _ equiv_t _] => apply ec_all; eauto
                                                                   
         | [H : (type _ ⩽ _) ⊢ _ equiv_s _ |- _] => inversion H; subst; clear H
         | [H : (type _ ⩾ _) ⊢ _ equiv_s _ |- _] => inversion H; subst; clear H
         | [H : (type _ ≝ _) ⊢ _ equiv_s _ |- _] => inversion H; subst; clear H
         | [H : (type _ ⪯ _) ⊢ _ equiv_s _ |- _] => inversion H; subst; clear H
                                                                   
         | [|- (type _ ⩽ _) ⊢ _ equiv_s _ ] => apply ec_upp; eauto
         | [|- (type _ ⩾ _) ⊢ _ equiv_s _ ] => apply ec_low; eauto
         | [|- (type _ ≝ _) ⊢ _ equiv_s _ ] => apply ec_equ; eauto
         | [|- (type _ ⪯ _) ⊢ _ equiv_s _ ] => apply ec_nom; eauto
                                                                      
         | [H : (d_con _ _) ⊢ _ equiv_ss _ |- _] => inversion H; subst; clear H
                                                                      
         | [|- (d_con _ _) ⊢ _ equiv_ss _ ] => apply ec_con; eauto
         end.

Ltac equiv_ctx_solve :=
  match goal with
  | [Hhas : ?G ⊢ ?x ∋ ?s, Hequiv : ?x ⊢ ?G equiv_v ?G'  |- ?G' ⊢ ?x ∋ ?s] =>
    eapply equiv_ctx_has; eauto
  | [Hhas : ?G ⊢ ?x ∋ ?s, Hequiv : ?x ⊢ ?G' equiv_v ?G  |- ?G' ⊢ ?x ∋ ?s] =>
    apply equiv_ctx_t_sym in Hequiv;
    eapply equiv_ctx_has; eauto
     
  | [Hhas : ?G ⊢ ?x ∋ ?s, Heq : ?x ⊢ ?G equiv_v ?G' |- _] =>
    match goal with
    | [_ : ?s ⊢ ?G equiv_s ?G' |- _] => idtac
    | _ => let Hfresh := fresh in assert (Hfresh : s ⊢ G equiv_s G');
                                 [apply has_equiv_ctx with (x:=x); auto|]
    end
  end.

Ltac notin_auto :=
  repeat match goal with
         | [H : _ notin_t (sel _ _) |- _] => inversion H; subst; clear H
         | [H : _ notin_t (_ str _ rts) |- _] => inversion H; subst; clear H
         | [H : _ notin_t (all _ ∙ _) |- _] => inversion H; subst; clear H

         | [H : _ notin_s (type _ ⩽ _) |- _] => inversion H; subst; clear H
         | [H : _ notin_s (type _ ⩾ _) |- _] => inversion H; subst; clear H
         | [H : _ notin_s (type _ ≝ _) |- _] => inversion H; subst; clear H
         | [H : _ notin_s (type _ ⪯ _) |- _] => inversion H; subst; clear H
                                                                  
         | [H : _ notin_ss (d_con _ _) |- _] => inversion H; subst; clear H
         end.

Ltac notin_solve :=
  match goal with
  | [H : forall n, n >= length ?G -> n >= length ?G' -> n notin_t ?t ,
       Hleng1 : ?m >= length ?G,
       Hleng2 : ?m >= length ?G' |- _] =>
    let Hfresh:= fresh in assert (Hfresh : m notin_t t);
                          [apply H; auto|clear H]

  | [H : forall n, n >= length ?G -> n >= length ?G' -> n notin_s ?s ,
       Hleng1 : ?m >= length ?G,
       Hleng2 : ?m >= length ?G' |- _] =>
    let Hfresh:= fresh in assert (Hfresh : m notin_s s);
                          [apply H; auto|clear H]

  | [H : forall n, n >= length ?G -> n >= length ?G' -> n notin_ss ?ss ,
       Hleng1 : ?m >= length ?G,
       Hleng2 : ?m >= length ?G' |- _] =>
    let Hfresh:= fresh in assert (Hfresh : m notin_ss ss);
                          [apply H; auto|clear H]
                                         
  | [H : ?G ⊢ ?x ∋ ?s,
         Hleng : ?n >= length ?G,
                 Hord : ord ?G |- _] =>
    match goal with
    | [Hni : ?n notin_s ?s |- _] => idtac
    | _ => let Hfresh := fresh in assert (Hfresh : n notin_s s);
                                 [eapply ord_has with (x:=x);
                                  eauto|]
    end
                                         
  | [H : ?G ⊢ ?t ≤⦂⦂ ?t',
         Hleng : ?n >= length ?G,
                 Hord : ord ?G |- _] =>
    match goal with
    | [Hni : ?n notin_t ?t' |- _] => idtac
    | _ => let Hfresh := fresh in assert (Hfresh : n notin_t t');
                                 [eapply ord_extends with (t:=t);
                                  eauto|]
    end
  end.

Lemma equiv_ctx_weakening_mutind :
  (forall G x G', x ⊢ G equiv_v G' ->
             ord G ->
             ord G' ->
             (forall n, n >= length G ->
                   n >= length G' ->
                   n notin_v x) ->
             forall t1 t2, x ⊢ (t1::G) equiv_v (t2::G')) /\

  (forall G t G', t ⊢ G equiv_t G' ->
             ord G ->
             ord G' ->
             (forall n, n >= length G ->
                   n >= length G' ->
                   n notin_t t) ->
             forall t1 t2, t ⊢ (t1::G) equiv_t (t2::G')) /\

  (forall G s G', s ⊢ G equiv_s G' ->
             ord G ->
             ord G' ->
             (forall n, n >= length G ->
                   n >= length G' ->
                   n notin_s s) ->
             forall t1 t2, s ⊢ (t1::G) equiv_s (t2::G')) /\

  (forall G ss G', ss ⊢ G equiv_ss G' ->
              ord G ->
              ord G' ->
              (forall n, n >= length G ->
                    n >= length G' ->
                    n notin_ss ss) ->
              forall t1 t2, ss ⊢ (t1::G) equiv_ss (t2::G')).
Proof.
  apply equiv_ctx_mutind;
    intros;
    auto;
    equiv_ctx_auto;
    notin_auto;
    repeat match goal with
           | [H : _ -> _ -> _ -> forall t1 t2, ?x ⊢ t1::?G1 equiv_v t2::?G2 |- ?x ⊢ _::?G1 equiv_v _::?G2] => eapply H; eauto; intros; eauto
           | [H : _ -> _ -> _ -> forall t1 t2, ?t ⊢ t1::?G1 equiv_t t2::?G2 |- ?t ⊢ _::?G1 equiv_t _::?G2] => eapply H; eauto; intros; eauto
           | [H : _ -> _ -> _ -> forall t1 t2, ?s ⊢ t1::?G1 equiv_s t2::?G2 |- ?s ⊢ _::?G1 equiv_s _::?G2] => eapply H; eauto; intros; eauto
           | [H : _ -> _ -> _ -> forall t1 t2, ?ss ⊢ t1::?G1 equiv_ss t2::?G2 |- ?ss ⊢ _::?G1 equiv_ss _::?G2] => eapply H; eauto; intros; eauto
                                                                                                                  
           | [H : forall n, n >= length ?G ->
                       _ ->
                       n notin_t ?t , Hleng : ?m >= length ?G |- _] =>
             apply H in Hleng;
               eauto;
               inversion Hleng;
               subst;
               eauto
           | [H : forall n, n >= length ?G ->
                       _ ->
                       n notin_s ?s , Hleng : ?m >= length ?G |- _] =>
             apply H in Hleng;
               eauto;
               inversion Hleng;
               subst;
               eauto
           | [H : forall n, n >= length ?G ->
                       _ ->
                       n notin_ss ?ss , Hleng : ?m >= length ?G |- _] =>
             apply H in Hleng;
               eauto;
               inversion Hleng;
               subst;
               eauto
           end.

  apply ec_conc1 with (t:=t);
    eauto;
    [apply typing_weakening; auto
    |apply typing_weakening; auto
    |apply H;
     auto;
     intros;
     eapply ord_typing2;
     eauto].

  apply H1 in g;
    auto;
    inversion g;
    crush.

Qed.

Lemma equiv_ctx_v_weakening :
  (forall G x G', x ⊢ G equiv_v G' ->
             ord G ->
             ord G' ->
             (forall n, n >= length G ->
                   n >= length G' ->
                   n notin_v x) ->
             forall t1 t2, x ⊢ (t1::G) equiv_v (t2::G')).
Proof.
  destruct equiv_ctx_weakening_mutind; crush.
Qed.

Lemma equiv_ctx_t_weakening :
  (forall G t G', t ⊢ G equiv_t G' ->
             ord G ->
             ord G' ->
             (forall n, n >= length G ->
                   n >= length G' ->
                   n notin_t t) ->
             forall t1 t2, t ⊢ (t1::G) equiv_t (t2::G')).
Proof.
  destruct equiv_ctx_weakening_mutind; crush.
Qed.

Lemma equiv_ctx_s_weakening :
  (forall G s G', s ⊢ G equiv_s G' ->
             ord G ->
             ord G' ->
             (forall n, n >= length G ->
                   n >= length G' ->
                   n notin_s s) ->
             forall t1 t2, s ⊢ (t1::G) equiv_s (t2::G')).
Proof.
  destruct equiv_ctx_weakening_mutind; crush.
Qed.

Lemma equiv_ctx_ss_weakening :
  (forall G ss G', ss ⊢ G equiv_ss G' ->
              ord G ->
              ord G' ->
              (forall n, n >= length G ->
                    n >= length G' ->
                    n notin_ss ss) ->
              forall t1 t2, ss ⊢ (t1::G) equiv_ss (t2::G')).
Proof.
  destruct equiv_ctx_weakening_mutind; crush.
Qed.

Lemma get_append :
  forall A G (t : A), get (length G) (G ++ (t::nil)) = Some t.
Proof.
  intros A G;
    induction G as [|a G'];
    intros;
    simpl in *;
    auto.
Qed.

Lemma mapping_cons :
  forall A G (t : A), (length G) ↦ t elem (t::G).
Proof.
  intros;
    unfold mapping in *;
    simpl in *.
  rewrite <- rev_length; apply get_append.
Qed.

Lemma typing_cons :
  forall G t, (t::G) ⊢ (c_ (length G)) ⦂ t.
Proof.
  intros.
  apply t_var.
  apply mapping_cons.
Qed.

Lemma equiv_ctx_merge :
  forall ss1 ss2 G G', ss1 ⊢ G equiv_ss G' ->
                  ss2 ⊢ G equiv_ss G' ->
                  (merge ss1 ss2) ⊢ G equiv_ss G'.
Proof.
  intros ss1;
    induction ss1;
    intros;
    simpl in *;
    auto.

  destruct (in_ds (id d) ss2);
    [apply IHss1;
     inversion H;
     eauto
    |apply ec_con;
     inversion H;
     eauto].
Qed.

Lemma equiv_ctx_flat :
  forall t ss t', flat t ss = Some t' ->
             forall G G', t ⊢ G equiv_t G' ->
                     ss ⊢ G equiv_ss G' ->
                     t' ⊢ G equiv_t G'.
Proof.
  intros t;
    destruct t;
    intros;
    simpl in H;
    auto;
    try solve [inversion H];
    try solve [inversion H;
               subst t';
               apply ec_rfn;
               auto].

  inversion H; subst t'.
  apply ec_rfn;
    inversion H0;
    [inversion H0
    |apply equiv_ctx_merge];
    auto.
Qed.

Lemma extend_equiv_ctx :
  forall G t t', G ⊢ t ≤⦂⦂ t' ->
            forall G', t ⊢ G equiv_t G' ->
                  t' ⊢ G equiv_t G'.
Proof.
  intros G t t' Hext;
    induction Hext;
    intros;
    auto;

    try solve [apply has_equiv_ctx
                 with
                   (G':=G')
                in H;
               [inversion H; subst
               |inversion H1; subst]; eauto].

  eapply equiv_ctx_flat
    with
      (G:=Γ)(G':=G')
    in H; eauto.
  apply IHHext;
    inversion H0;
    auto.
  inversion H0;
    auto.
Qed.

Lemma equiv_ctx_extend :
  forall G t t', G ⊢ t ≤⦂⦂ t' ->
            forall G', t ⊢ G equiv_t G' ->
                  G' ⊢ t ≤⦂⦂ t'.
Proof.
  intros G t t' Hext;
    induction Hext;
    intros;
    auto;

    try solve [apply equiv_ctx_has
                 with (G':=G')
                in H;
               [auto
               |inversion H1; subst; eauto]];
    try solve [inversion H0; eauto].
Qed.

(*Lemma subtype_equiv_ctx_mutind :
  (forall G1 t1 t2, G ⊢ t1 ≤ t2 ->
               forall G', t1 ⊢ G equiv_t G' ->
                     t2 ⊢ G equiv_t G' ->
                     ord G ->
                     ord G' ->
                     (forall n, n >= length G ->
                           n >= length G' ->
                           n notin_t t1) ->
                     (forall n, n >= length G ->
                           n >= length G' ->
                           n notin_t t2) ->
                     length G' = length G ->
                     G' ⊢ t1 ≤ t2 ⊣ G2) /\

  (forall G s1 s2, G ⊢ s1 ≤; s2 ->
              forall G', s1 ⊢ G equiv_s G' ->
                    s2 ⊢ G equiv_s G' ->
                    ord G ->
                    ord G' ->
                    (forall n, n >= length G ->
                          n >= length G' ->
                          n notin_s s1) ->
                    (forall n, n >= length G ->
                          n >= length G' ->
                          n notin_s s2) ->
                    length G' = length G ->
                    G' ⊢ s1 ≤; s2) /\
  
  (forall G ss1 ss2, G ⊢ ss1 ≤;; ss2 ->
                forall G', ss1 ⊢ G equiv_ss G' ->
                      ss2 ⊢ G equiv_ss G' ->
                      ord G ->
                      ord G' ->
                      (forall n, n >= length G ->
                            n >= length G' ->
                            n notin_ss ss1) ->
                      (forall n, n >= length G ->
                            n >= length G' ->
                            n notin_ss ss2) ->
                      length G' = length G ->
                      G' ⊢ ss1 ≤;; ss2).
Proof.
  apply subtype_mutind;
    intros;
    auto;
    try solve [try match goal with
                   | [H : _ ⊢ _ ∋ (type _ ⩽ _) |- _] => eapply s_upper_1 with (t1:=t1);
                                                      eauto
                   | [H : _ ⊢ _ ∋ (type _ ⩾ _) |- _] => eapply s_lower_1 with (t2:=t2);
                                                      eauto
                   | [H : _ ⊢ ?x ∋ (type ?L ≝ _) |- _ ⊢ _ ≤ sel ?x ?L ] => eapply s_lower_2 with (t2:=t2);
                                                                         eauto
                   | [H : _ ⊢ ?x ∋ (type ?L ≝ _) |- _ ⊢ sel ?x ?L ≤ _ ] => eapply s_upper_2 with (t1:=t1);
                                                                         eauto
                   | [H : _ ⊢ _ ∋ (type _ ⪯ _) |- _] => eapply s_upper_3 with (t1:=t1);
                                                      eauto
                   end;
               equiv_ctx_auto;
               equiv_ctx_solve;
               apply H;
               auto;
               intros;
               repeat notin_solve;
               notin_auto;
               equiv_ctx_auto;
               auto;
               notin_auto].

  apply s_all;
    rewrite H6;
    apply H;
    simpl;
    auto;
    intros;
    repeat notin_solve;
    notin_auto;
    equiv_ctx_auto;
    try equiv_ctx_solve;
    try solve [apply subst_equiv_ctx;
               [apply equiv_ctx_t_weakening;
                intros;
                auto;
                repeat notin_solve;
                notin_auto;
                auto
               |eapply ec_conc1;
                [apply typing_cons
                |rewrite <- H6;
                 apply typing_cons
                |apply equiv_ctx_t_weakening;
                 intros;
                 auto;
                 repeat notin_solve;
                 notin_auto;
                 auto]]];
    try solve [apply ord_con;
               intros;
               auto;
               match goal with
               | [H : ?m >= length ?G, Hleng : length ?G' = length ?G |- _] =>
                 let Htmp := fresh in assert (Htmp := H); auto;
                                      rewrite <- Hleng in Htmp
               | [H : ?m >= length ?G, Hleng : length ?G = length ?G' |- _] =>
                 let Htmp := fresh in assert (Htmp := H); auto;
                                      rewrite Hleng in Htmp
               end;
               try notin_solve;
               notin_auto;
               auto].
  
  apply notin_subst;
    crush.
  assert (Hge : n >= length Γ);
    [crush|
     apply H4 in Hge;
     [notin_auto; auto|crush]].
  
  apply notin_subst;
    crush.
  assert (Hge : n >= length Γ);
    [crush|
     apply H5 in Hge;
     [notin_auto; auto|crush]].

  apply s_refine;
    rewrite H6;
    apply H;
    simpl;
    auto;
    intros;
    repeat notin_solve;
    notin_auto;
    equiv_ctx_auto;
    try equiv_ctx_solve;
    try solve [apply subst_equiv_ctx_ss;
               [apply equiv_ctx_ss_weakening;
                intros;
                auto;
                repeat notin_solve;
                notin_auto;
                auto
               |eapply ec_conc1;
                [apply typing_cons
                |rewrite <- H6;
                 apply typing_cons
                |apply equiv_ctx_t_weakening;
                 intros;
                 auto;
                 repeat notin_solve;
                 notin_auto;
                 auto]]];
    try solve [apply ord_con;
               intros;
               auto;
               match goal with
               | [H : ?m >= length ?G, Hleng : length ?G' = length ?G |- _] =>
                 let Htmp := fresh in assert (Htmp := H); auto;
                                      rewrite <- Hleng in Htmp
               | [H : ?m >= length ?G, Hleng : length ?G = length ?G' |- _] =>
                 let Htmp := fresh in assert (Htmp := H); auto;
                                      rewrite Hleng in Htmp
               end;
               try notin_solve;
               notin_auto;
               auto].
  
  apply notin_ss_subst;
    crush.
  assert (Hge : n >= length Γ);
    [crush|
     apply H4 in Hge;
     [notin_auto; auto|crush]].
  
  apply notin_ss_subst;
    crush.
  assert (Hge : n >= length Γ);
    [crush|
     apply H5 in Hge;
     [notin_auto; auto|crush]].
  
  apply s_extend with (t:=t);
    [eapply equiv_ctx_extend; eauto
    |].
  apply H;
    intros;
    auto.
  eapply extend_equiv_ctx; eauto.
  apply ord_extends with (n:=n) in e;
    intros;
    auto.
  apply H4;
    auto;
    crush.

  apply s_lower_d;
    apply H;
    auto;
    equiv_ctx_auto;
    try equiv_ctx_solve;
    intros;
    auto;
    repeat notin_solve;
    notin_auto;
    auto.

  apply s_upper_d;
    apply H;
    auto;
    equiv_ctx_auto;
    try equiv_ctx_solve;
    intros;
    auto;
    repeat notin_solve;
    notin_auto;
    auto.

  apply s_lo_eq_d;
    apply H;
    auto;
    equiv_ctx_auto;
    try equiv_ctx_solve;
    intros;
    auto;
    repeat notin_solve;
    notin_auto;
    auto.

  apply s_up_eq_d;
    apply H;
    auto;
    equiv_ctx_auto;
    try equiv_ctx_solve;
    intros;
    auto;
    repeat notin_solve;
    notin_auto;
    auto.

  apply s_equal_d;
    [apply H|apply H0];
    auto;
    equiv_ctx_auto;
    try equiv_ctx_solve;
    intros;
    auto;
    repeat notin_solve;
    notin_auto;
    auto.

  apply s_up_no_d;
    apply H;
    auto;
    equiv_ctx_auto;
    try equiv_ctx_solve;
    intros;
    auto;
    repeat notin_solve;
    notin_auto;
    auto.

  apply s_con;
    [apply H|apply H0];
    auto;
    equiv_ctx_auto;
    try equiv_ctx_solve;
    intros;
    auto;
    repeat notin_solve;
    notin_auto;
    auto.
  
Qed.*)

Lemma get_strengthening :
  forall A G1 G2 n (t : A), get n (G1 ++ G2) = Some t ->
                       n < length G1 ->
                       get n G1 = Some t.
Proof.
  intros A G1;
    induction G1;
    intros;
    eauto;
    [inversion H0|].

  destruct n;
    simpl in *;
     eauto.

  simpl; erewrite IHG1;
    crush.
Qed.

Lemma mapping_strengthening :
  forall A n (t : A) G1 G2, n ↦ t elem (G1 ++ G2) ->
                       n < length G2 ->
                       n ↦ t elem G2.
Proof.
  intros; unfold mapping in *;
    rewrite rev_app_distr in *;
    eapply get_strengthening;
    try rewrite rev_length;
    eauto.
Qed.

Lemma get_length :
  forall A (G : list A) n, n < length G ->
                      exists t, get n G = Some t.
Proof.
  intros A G;
    induction G;
    intros;
    eauto;
    [destruct n; crush|].

  destruct n; simpl; crush.
  exists a; crush.
Qed.

Lemma mapping_length :
  forall A n (G : list A), n < length G ->
           exists t, n ↦ t elem G.
Proof.
  intros;
    unfold mapping in *;
    rewrite <- rev_length in *;
    eapply get_length in H;
    eauto.
Qed.

Lemma typing_strengthening :
  forall G x t, G ⊢ x ⦂ t ->
           forall t' G', G = t'::G' ->
                    length G' notin_v x ->
                    G' ⊢ x ⦂ t.
Proof.
  intros.
  inversion H; subst.
  apply t_var.
  apply mapping_strengthening with (G1:=t'::nil);
    inversion H1;
    subst;
    eauto.
  eapply mapping_lt in H2.
  simpl in H2.
  destruct (lt_eq_lt_dec n (length G'));
    crush.
Qed.

Lemma equiv_ctx_strengthening_mutind :
  (forall G1 x G2, x ⊢ G1 equiv_v G2 ->
              ord G1 ->
              forall t1 G1' t2 G2', G1 = t1 :: G1' ->
                               G2 = t2 :: G2' ->
                               length G1' = length G2' ->
                               (length G1') notin_v x ->
                               x ⊢ G1' equiv_v G2') /\

  (forall G1 t G2, t ⊢ G1 equiv_t G2 ->
              ord G1 ->
              forall t1 G1' t2 G2', G1 = t1 :: G1' ->
                               G2 = t2 :: G2' ->
                               length G1' = length G2' ->
                               (length G1') notin_t t ->
                               t ⊢ G1' equiv_t G2') /\

  (forall G1 s G2, s ⊢ G1 equiv_s G2 ->
              ord G1 ->
              forall t1 G1' t2 G2', G1 = t1 :: G1' ->
                               G2 = t2 :: G2' ->
                               length G1' = length G2' ->
                               (length G1') notin_s s ->
                               s ⊢ G1' equiv_s G2') /\

  (forall G1 ss G2, ss ⊢ G1 equiv_ss G2 ->
               ord G1 ->
               forall t1 G1' t2 G2', G1 = t1 :: G1' ->
                                G2 = t2 :: G2' ->
                                length G1' = length G2' ->
                                (length G1') notin_ss ss ->
                                ss ⊢ G1' equiv_ss G2').
Proof.
  apply equiv_ctx_mutind;
    intros;
    subst;
    notin_auto;
    eauto.
  
  destruct x; eauto. 
  apply ec_conc1 with (t:=t);
    eauto;
    [apply typing_strengthening with (G:=t2::G1')(t':=t2); eauto
    |apply typing_strengthening with (G:=t3::G2')(t':=t3); eauto;
     rewrite <- H3; auto
    |eapply H; eauto].
  apply ord_typing2 with (G:=G1')(x:=c_ n); eauto;
    [apply typing_strengthening with (G:=t2::G1')(t':=t2); eauto
    |inversion H0; auto].

  apply ec_conc2;
    crush.
Qed.

Lemma equiv_ctx_v_strengthening :
  (forall G1 x G2, x ⊢ G1 equiv_v G2 ->
              ord G1 ->
              forall t1 G1' t2 G2', G1 = t1 :: G1' ->
                               G2 = t2 :: G2' ->
                               length G1' = length G2' ->
                               (length G1') notin_v x ->
                               x ⊢ G1' equiv_v G2').
Proof.
  destruct equiv_ctx_strengthening_mutind; crush.
Qed.

Lemma equiv_ctx_t_strengthening :
  (forall G1 t G2, t ⊢ G1 equiv_t G2 ->
              ord G1 ->
              forall t1 G1' t2 G2', G1 = t1 :: G1' ->
                               G2 = t2 :: G2' ->
                               length G1' = length G2' ->
                               (length G1') notin_t t ->
                               t ⊢ G1' equiv_t G2').
Proof.
  destruct equiv_ctx_strengthening_mutind; crush.
Qed.

Lemma equiv_ctx_s_strengthening :
  (forall G1 s G2, s ⊢ G1 equiv_s G2 ->
              ord G1 ->
              forall t1 G1' t2 G2', G1 = t1 :: G1' ->
                               G2 = t2 :: G2' ->
                               length G1' = length G2' ->
                               (length G1') notin_s s ->
                               s ⊢ G1' equiv_s G2').
Proof.
  destruct equiv_ctx_strengthening_mutind; crush.
Qed.

Lemma equiv_ctx_ss_strengthening :
  (forall G1 ss G2, ss ⊢ G1 equiv_ss G2 ->
               ord G1 ->
               forall t1 G1' t2 G2', G1 = t1 :: G1' ->
                                G2 = t2 :: G2' ->
                                length G1' = length G2' ->
                                (length G1') notin_ss ss ->
                                ss ⊢ G1' equiv_ss G2').
Proof.
  destruct equiv_ctx_strengthening_mutind; crush.
Qed.


Inductive conforms : env -> ty -> tytree -> Prop :=
| conf_top     : forall G, conforms G top t_top
| conf_bot     : forall G, conforms G bot t_bot
| conf_sel_upp : forall G x L t T, G ⊢ x ∋ (type L ⩽ t) ->
                              conforms G t T ->
                              is_material (sel x L) -> 
                              conforms G (sel x L) (t_sel_upp x L T)

| conf_sel_low : forall G x L t T, G ⊢ x ∋ (type L ⩾ t) ->
                              conforms G t T ->
                              is_material (sel x L) -> 
                              is_material t ->
                              conforms G (sel x L) (t_sel_low x L T)

| conf_sel_equ : forall G x L t T, G ⊢ x ∋ (type L ≝ t) ->
                              conforms G t T ->
                              is_material (sel x L) ->
                              is_material t ->
                              conforms G (sel x L) (t_sel_equ x L T)

| conf_sel_nom : forall G x L t T, G ⊢ x ∋ (type L ⪯ t) ->
                              conforms G t T ->
                              is_material (sel x L) -> 
                              conforms G (sel x L) (t_sel_nom x L T)

| conf_rfn_top : forall G ss Ts, conforms_ss ((top str ss rts)::G) ([c_ (length G) /ss 0]ss) Ts ->
                            (*(forall n, n >= length G ->
                                  n notin_ss ss) ->*)
                            conforms G (top str ss rts) (t_rfn_top Ts)
                                     
| conf_rfn_sel : forall G x L ss t Ts T, G ⊢ ((sel x L) str ss rts) ≤⦂⦂ t ->
                                    is_material (sel x L) ->
                                    conforms_ss ((sel x L str ss rts)::G) ([c_ (length G) /ss 0]ss) Ts ->
                                   (* (forall n, n >= length G ->
                                          n notin_ss ss) ->*)
                                    conforms G t T ->
                                    conforms G ((sel x L) str ss rts) (t_rfn_sel x L Ts T)

| conf_sha_top_1 : forall G x L ss t, G ⊢ x ∋ (type L ⩽ t) ->
                                 is_struct t ->
                                 is_shape (sel x L) ->
                                 (*(forall n, n >= length G ->
                                       n notin_ss ss) ->*)
                                 conforms G ((sel x L) str ss rts) (t_sha_top x L ss)

| conf_sha_top_2 : forall G x L ss t, G ⊢ x ∋ (type L ≝ t) ->
                                 is_struct t ->
                                 is_shape (sel x L) ->
                                 (*(forall n, n >= length G ->
                                       n notin_ss ss) ->*)
                                 conforms G ((sel x L) str ss rts) (t_sha_top x L ss)

| conf_sha_top_3 : forall G x L ss t, G ⊢ x ∋ (type L ⪯ t) ->
                                 is_struct t ->
                                 is_shape (sel x L) ->
                                 (*(forall n, n >= length G ->
                                       n notin_ss ss) ->*)
                                 conforms G ((sel x L) str ss rts) (t_sha_top x L ss)

| conf_sha_sel : forall G x L ss t T, G ⊢ (sel x L str ss rts) ≤⦂⦂ t ->
                                 is_shape t ->
                                 is_shape (sel x L) ->
                                 conforms G t T ->
                                 (*(forall n, n >= length G ->
                                       n notin_ss ss) ->*)
                                 conforms G ((sel x L) str ss rts) (t_sha_sel x L ss T)

| conf_all : forall G t t' T T', conforms G t T ->
                            conforms (t::G) ([c_ (length G) /t 0]t') T' ->
                            (*(forall n, n >= length G ->
                                  n notin_t t') ->*)
                            is_material t ->
                            conforms G (all t ∙ t') (t_all T T')
                                    

with
conforms_s : env -> decl -> tytree -> Prop :=
| conf_upp : forall G L t T, conforms G t T ->
                        conforms_s G (type L ⩽ t) (t_upp L T)

| conf_low : forall G L t T, conforms G t T ->
                        is_material t ->
                        conforms_s G (type L ⩾ t) (t_low L T)

| conf_equ : forall G L t T, conforms G t T ->
                        is_material t ->
                        conforms_s G (type L ≝ t) (t_equ L T)

| conf_nom : forall G L t T, conforms G t T ->
                        conforms_s G (type L ⪯ t) (t_nom L t T)

with
conforms_ss : env -> decls -> tytree -> Prop :=
| conf_nil : forall G, conforms_ss G d_nil t_nil

| conf_con : forall G s ss T Ts, conforms_s G s T ->
                            conforms_ss G ss Ts ->
                            conforms_ss G (d_con s ss) (t_con T Ts).

Hint Constructors conforms conforms_s conforms_ss.

Scheme conf_mut_ind := Induction for conforms Sort Prop
  with conf_s_mut_ind := Induction for conforms_s Sort Prop
  with conf_ss_mut_ind := Induction for conforms_ss Sort Prop.

Combined Scheme conforms_mutind from conf_mut_ind, conf_s_mut_ind, conf_ss_mut_ind.
(*
Lemma conforms_notin_mutind :
  (forall G t T, conforms G t T ->
            forall n, n >= length G ->
                 n notin_t t) /\

  (forall G s T, conforms_s G s T ->
            forall n, n >= length G ->
                 n notin_s s) /\

  (forall G ss Ts, conforms_ss G ss Ts ->
              forall n, n >= length G ->
                   n notin_ss ss).
Proof.
  apply conforms_mutind;
    intros;
    auto;
    try solve [eapply ni_sel, ord_has'; eauto].

  apply ni_rfn; auto.
  inversion e; subst; auto.
  eapply ni_sel, ord_extends'; eauto.

  apply ni_rfn; auto.
  apply ni_sel.
  eapply ord_has'; eauto.

  apply ni_rfn; auto.
  eapply ni_sel, ord_has'; eauto.

  apply ni_rfn; auto.
  eapply ni_sel, ord_has'; eauto.

  apply ni_rfn; auto.
  inversion e; subst.
  eapply ni_sel, ord_extends'; eauto.
Qed.

Lemma conforms_notin :
  (forall G t T, conforms G t T ->
            forall n, n >= length G ->
                 n notin_t t).
Proof.
  destruct conforms_notin_mutind; crush.
Qed.

Lemma conforms_s_notin :
  (forall G s T, conforms_s G s T ->
            forall n, n >= length G ->
                 n notin_s s).
Proof.
  destruct conforms_notin_mutind; crush.
Qed.

Lemma conforms_ss_notin:
  (forall G ss Ts, conforms_ss G ss Ts ->
              forall n, n >= length G ->
                   n notin_ss ss).
Proof.
  destruct conforms_notin_mutind; crush.
Qed.
 *)
(*
Lemma conforms_equiv_ctx_mutind :
  (forall G t T, conforms G t T ->
            ord G ->
            forall G', t ⊢ G equiv_t G' ->
                  ord G' ->
                  length G' = length G ->
                  conforms G' t T) /\
  
  (forall G s T, conforms_s G s T ->
            ord G ->
            forall G', s ⊢ G equiv_s G' ->
                  ord G' ->
                  length G' = length G ->
                  conforms_s G' s T) /\
  
  (forall G ss Ts, conforms_ss G ss Ts ->
              ord G ->
              forall G', ss ⊢ G equiv_ss G' ->
                    ord G' ->
                    length G' = length G ->
                    conforms_ss G' ss Ts).
Proof.
  apply conforms_mutind;
    intros;
    auto;
    try solve [inversion H1; eauto];
    try solve [inversion H3; eauto].

  inversion H1; subst.
  eapply conf_sel_upp with (t:=t); eauto.
  apply equiv_ctx_has
    with (G':=G')
    in h; eauto.
  eapply has_equiv_ctx
    with (G':=G')
    in h; eauto.
  apply H; inversion h; auto.

  inversion H1; subst.
  eapply conf_sel_low with (t:=t); eauto.
  apply equiv_ctx_has
    with (G':=G')
    in h; eauto.
  eapply has_equiv_ctx
    with (G':=G')
    in h; eauto.
  apply H; inversion h; auto.

  inversion H1; subst.
  eapply conf_sel_equ with (t:=t); eauto.
  apply equiv_ctx_has
    with (G':=G')
    in h; eauto.
  eapply has_equiv_ctx
    with (G':=G')
    in h; eauto.
  apply H; inversion h; auto.

  inversion H1; subst.
  eapply conf_sel_nom with (t:=t); eauto.
  apply equiv_ctx_has
    with (G':=G')
    in h; eauto.
  eapply has_equiv_ctx
    with (G':=G')
    in h; eauto.
  apply H; inversion h; auto.

  inversion H1; subst; eauto.
  apply conf_rfn_top; eauto;
    [|rewrite H3; auto].
  rewrite H3; apply H; simpl; eauto.
  apply ord_con;
    eauto.
  apply subst_equiv_ctx_ss;
    [apply equiv_ctx_ss_weakening
    |apply ec_conc1 with (t:=top str ss rts);
     [
     |rewrite <- H3
     |apply equiv_ctx_t_weakening]]; 
    try solve [apply typing_cons];
    auto.
  apply ord_con;
    try (rewrite H3);
    eauto.

  inversion H2; subst; eauto.
  apply conf_rfn_sel with (t:=t); eauto;
    [| |rewrite H4; auto|].
  eapply equiv_ctx_extend; eauto.
  rewrite H4; apply H; simpl; eauto.
  apply ord_con; intros; auto.
  apply ni_rfn;
    [|apply n; crush];
    inversion e; subst;
    apply ni_sel, ord_extends' with (G:=G)(L:=L)(t':=t');
    crush.
  apply subst_equiv_ctx_ss;
    [apply equiv_ctx_ss_weakening
    |apply ec_conc1 with (t:=sel x L str ss rts);
     [
     |rewrite <- H4
     |apply equiv_ctx_t_weakening]]; 
    try solve [apply typing_cons];
    auto.
  intros;
    apply ni_rfn;
    [|apply n; auto];
    inversion e; subst;
    apply ni_sel, ord_extends' with (G:=G)(L:=L)(t':=t');
    auto.
  apply ord_con; intros; auto.
  apply ni_rfn;
    [|apply n; crush];
    inversion e; subst;
    apply ni_sel, ord_extends' with (G:=G)(L:=L)(t':=t');
    crush.
  apply H0; auto.
  eapply extend_equiv_ctx; eauto.

  inversion H0; subst.
  apply conf_sha_top_1 with (t:=t);
    auto;
    [|rewrite H2; auto].
  eapply equiv_ctx_has; eauto.
  inversion H6; subst; auto.

  inversion H0; subst.
  apply conf_sha_top_2 with (t:=t);
    auto;
    [|rewrite H2; auto].
  eapply equiv_ctx_has; eauto.
  inversion H6; subst; auto.

  inversion H0; subst.
  apply conf_sha_top_3 with (t:=t);
    auto;
    [|rewrite H2; auto].
  eapply equiv_ctx_has; eauto.
  inversion H6; subst; auto.

  inversion H1; subst.
  apply conf_sha_sel with (t:=t);
    auto;
    [| |rewrite H3; auto].
  eapply equiv_ctx_extend; eauto.
  apply H; auto.
  eapply extend_equiv_ctx; eauto.

  inversion H2; subst.
  apply conf_all; auto;
    [|rewrite H4; auto].
  rewrite H4.
  apply H0; simpl; auto.
  apply ord_con; intros; auto.
  eapply conforms_notin; eauto.
  apply subst_equiv_ctx.
  apply equiv_ctx_t_weakening; auto.
  apply ec_conc1 with (t:=t);
    [apply typing_cons
    |rewrite <- H4; apply typing_cons
    |apply equiv_ctx_t_weakening; auto].
  intros;
    eapply conforms_notin;
    eauto.
  apply ord_con; intros; auto.
  eapply conforms_notin;
    try rewrite <- H4;
    eauto.

  apply conf_con;
    [apply H;
     auto
    |apply H0;
     auto];
    equiv_ctx_auto;
    auto.
Qed.

Lemma conforms_equiv_ctx :
  (forall G t T, conforms G t T ->
            ord G ->
            forall G', t ⊢ G equiv_t G' ->
                  ord G' ->
                  length G' = length G ->
                  conforms G' t T).
Proof.
  destruct conforms_equiv_ctx_mutind; crush.
Qed.

Lemma conforms_equiv_ctx_s :  
  (forall G s T, conforms_s G s T ->
            ord G ->
            forall G', s ⊢ G equiv_s G' ->
                  ord G' ->
                  length G' = length G ->
                  conforms_s G' s T).
Proof.
  destruct conforms_equiv_ctx_mutind; crush.
Qed.

Lemma conforms_equiv_ctx_ss :  
  (forall G ss Ts, conforms_ss G ss Ts ->
              ord G ->
              forall G', ss ⊢ G equiv_ss G' ->
                    ord G' ->
                    length G' = length G ->
                    conforms_ss G' ss Ts).
Proof.
  destruct conforms_equiv_ctx_mutind; crush.
Qed.
*)
Scheme type_mut_ind := Induction for ty Sort Prop
  with decl_mut_ind := Induction for decl Sort Prop
  with decls_mut_ind := Induction for decls Sort Prop.

Combined Scheme type_mutind from type_mut_ind, decl_mut_ind, decls_mut_ind.

Lemma notin_equiv_refl_mutind' :
  (forall t G, (forall t', In t' G -> t' ⊢ G equiv_t G) ->
          t ⊢ G equiv_t G) /\

  (forall s G, (forall t', In t' G -> t' ⊢ G equiv_t G) ->
          s ⊢ G equiv_s G) /\

  (forall ss G, (forall t', In t' G -> t' ⊢ G equiv_t G) ->
           ss ⊢ G equiv_ss G).
Proof.
  apply type_mutind;  
    intros;
    auto;
    equiv_ctx_auto;
    repeat match goal with
           | [H : forall G, _ -> _ -> ?t ⊢ G equiv_t G |- ?t ⊢ ?G' equiv_t ?G'] => eapply H; eauto; intros; eauto
           | [H : forall G, _ -> _ -> ?s ⊢ G equiv_s G |- ?s ⊢ ?G' equiv_s ?G'] => eapply H; eauto; intros; eauto
           | [H : forall G, _ -> _ -> ?ss ⊢ G equiv_ss G |- ?ss ⊢ ?G' equiv_ss ?G'] => eapply H; eauto; intros; eauto
           | [H : forall n, n >= length ?G -> n notin_t ?t , Hleng : ?m >= length ?G |- _] =>
             apply H in Hleng;
               inversion Hleng;
               subst;
               eauto
           | [H : forall n, n >= length ?G -> n notin_s ?s , Hleng : ?m >= length ?G |- _] =>
             apply H in Hleng;
               inversion Hleng;
               subst;
               eauto
           | [H : forall n, n >= length ?G -> n notin_ss ?ss , Hleng : ?m >= length ?G |- _] =>
             apply H in Hleng;
               inversion Hleng;
               subst;
               eauto
           end.
  
  destruct v; auto.
  destruct (le_lt_dec (length G) n) as [Hle|Hlt].
  apply ec_conc2; auto.
  apply mapping_length in Hlt;
    destruct Hlt as [t];
    apply ec_conc1 with (t:=t);
    eauto.
  eapply H, in_mapping; eauto.
Qed.

Lemma notin_equiv_refl' :
  (forall t G, (forall t', In t' G -> t' ⊢ G equiv_t G) ->
          t ⊢ G equiv_t G).
Proof.
  destruct notin_equiv_refl_mutind'; crush.
Qed.

Lemma ord_equiv_ctx :
  forall G, ord G ->
       forall t, In t G ->
            t ⊢ G equiv_t G.
Proof.
  intros G Hord;
    induction Hord;
    intros;
    [crush|].

  inversion H0; subst.

  apply equiv_ctx_t_weakening;
    intros;
    eauto.
  apply notin_equiv_refl';
    auto.

  apply equiv_ctx_t_weakening;
    intros;
    eauto.
  eapply ord_in; eauto.
Qed.

Lemma ord_equiv_refl :
  (forall t G, ord G ->
          t ⊢ G equiv_t G).
Proof.
  intros.
  apply notin_equiv_refl';
    intros.
  apply ord_equiv_ctx;
    auto.
Qed.

Lemma ord_equiv_s_refl :
  (forall s G, ord G ->
          s ⊢ G equiv_s G).
Proof.
  intros.
  destruct notin_equiv_refl_mutind' as [Ha Hb];
    destruct Hb as [Hb Hc];
    apply Hb;
    intros.
  apply ord_equiv_ctx;
    auto.
Qed.

Lemma ord_equiv_ss_refl :
  (forall ss G, ord G ->
          ss ⊢ G equiv_ss G).
Proof.
  intros.
  destruct notin_equiv_refl_mutind' as [Ha Hb];
    destruct Hb as [Hb Hc];
    apply Hc;
    intros.
  apply ord_equiv_ctx;
    auto.
Qed.

Lemma beq_ty_eq_mutind :
  (forall t1 t2, eq_ty t1 t2 = true ->
            t1 = t2) /\

  (forall s1 s2, eq_decl s1 s2 = true ->
            s1 = s2) /\

  (forall ss1 ss2, eq_decls ss1 ss2 = true ->
              ss1 = ss2).
Proof.
  apply type_mutind;
    intros;
    try match goal with
        | [H : eq_ty _ ?t2 = true |- _] => destruct t2
        | [H : eq_decl _ ?s2 = true |- _] => destruct s2
        | [H : eq_decls _ ?ss2 = true |- _] => destruct ss2
        end;
    auto;
    try match goal with 
        | [H : eq_ty _ _ = true |- _] => simpl in H; try solve [inversion H]
        | [H : eq_decl _ _ = true |- _] => simpl in H; try solve [inversion H]
        | [H : eq_decls _ _ = true |- _] => simpl in H; try solve [inversion H]
        end;
    repeat match goal with
           | [H : _ && _ = true |- _] => apply andb_prop in H; destruct H
           end.
  erewrite H0, H; eauto.
  apply beq_var_eq in H;
    apply beq_label_eq in H0;
    subst;
    auto.
  erewrite H0, H; eauto.
  erewrite H; eauto;
    apply beq_label_eq in H0;
    subst;
    auto.
  erewrite H; eauto;
    apply beq_label_eq in H0;
    subst;
    auto.
  erewrite H; eauto;
    apply beq_label_eq in H0;
    subst;
    auto.
  erewrite H; eauto;
    apply beq_label_eq in H0;
    subst;
    auto.
  erewrite H0, H; eauto.
Qed.

Lemma beq_ty_eq :
  (forall t1 t2, eq_ty t1 t2 = true ->
            t1 = t2).
Proof.
  destruct beq_ty_eq_mutind; crush.
Qed.

Lemma beq_decl_eq :
  (forall s1 s2, eq_decl s1 s2 = true ->
            s1 = s2).
Proof.
  destruct beq_ty_eq_mutind; crush.
Qed.

Lemma beq_decls_eq :
  (forall ss1 ss2, eq_decls ss1 ss2 = true ->
              ss1 = ss2).
Proof.
  destruct beq_ty_eq_mutind; crush.
Qed.

(*Lemma beq_tree_eq :
  forall T1 T2, eq_tree T1 T2 = true ->
           T1 = T2.
Proof.
  intros T1;
    induction T1;
    intros;
    destruct T2;
    try match goal with
        | [H : eq_tree _ _ = true |- _] => simpl in H; try solve [inversion H]
        end;
    auto;
    repeat match goal with
           | [H : _ && _ = true |- _] => apply andb_prop in H; destruct H
           | [H : eq_var ?x _ = true |- _] => apply beq_var_eq in H; subst x
           | [H : eq_label ?l _ = true |- _] => apply beq_label_eq in H; subst l
           | [H : eq_ty ?t _ = true |- _] => apply beq_ty_eq in H; subst t
           | [H : eq_decl ?s _ = true |- _] => apply beq_decl_eq in H; subst s
           | [H : eq_decls ?ss _ = true |- _] => apply beq_decls_eq in H; subst ss
           end;
    try solve [erewrite IHT1; eauto];
    auto.

  erewrite IHT1_1, IHT1_2; eauto.

  erewrite IHT1_1, IHT1_2; eauto.

  erewrite IHT1_1, IHT1_2; eauto.
Qed.*)

Lemma subst_equality_mutind :
  (forall x t1, x notin_t t1 ->
           forall t2, x notin_t t2 ->
                 forall n, ([c_ x /t n] t1) = ([c_ x /t n] t2) ->
                      t1 = t2) /\

  (forall x s1, x notin_s s1 ->
           forall s2, x notin_s s2 ->
                 forall n, ([c_ x /s n] s1) = ([c_ x /s n] s2) ->
                      s1 = s2) /\

  (forall x ss1, x notin_ss ss1 ->
           forall ss2, x notin_ss ss2 ->
                 forall n, ([c_ x /ss n] ss1) = ([c_ x /ss n] ss2) ->
                      ss1 = ss2).
Proof.
  apply notin_mutind;
    intros;
    repeat match goal with
        | [H : ([_ /t _] _) = ([_ /t _] _) |- _] => simpl in H
        | [H : ([_ /s _] _) = ([_ /s _] _) |- _] => simpl in H
        | [H : ([_ /ss _] _) = ([_ /ss _] _) |- _] => simpl in H
        | [H : top = ([_ /t _] ?t) |- _] => destruct t; simpl in H; inversion H; auto
        | [H : bot = ([_ /t _] ?t) |- _] => destruct t; simpl in H; inversion H; auto
        | [H : d_nil = ([_ /ss _] ?ss) |- _] => destruct ss; simpl in H; inversion H; auto
        | [H : _ notin_t (_ str _ rts) |- _] => inversion H; subst; clear H
        | [H : (sel _ _) = ([_ /t _] ?t2) |- _] => destruct t2; simpl in H; inversion H; subst; eauto
        | [H : (_ str _ rts) = ([_ /t _] ?t2) |- _] => destruct t2; simpl in H; inversion H; subst; eauto
        | [H : (all _ ∙ _ ) = ([_ /t _] ?t) |- _] => destruct t; simpl in H; inversion H; auto
        | [H : (type _ ⩽ _) = ([_ /s _] ?s) |- _] => destruct s; simpl in H; inversion H; subst; eauto
        | [H : (type _ ⩾ _) = ([_ /s _] ?s) |- _] => destruct s; simpl in H; inversion H; subst; eauto
        | [H : (type _ ≝ _) = ([_ /s _] ?s) |- _] => destruct s; simpl in H; inversion H; subst; eauto
        | [H : (type _ ⪯ _) = ([_ /s _] ?s) |- _] => destruct s; simpl in H; inversion H; subst; eauto
        | [H : (d_con _ _) = ([_ /ss _] ?ss) |- _] => destruct ss; simpl in H; inversion H; subst; eauto
        end.

  destruct p, v; simpl; auto;
    simpl in H2.
  destruct (n1 =? n3); inversion H2; subst.
  inversion n0; crush.
  destruct (n1 =? n2); inversion H2; subst.
  inversion H; subst.
  inversion H4; crush.
  var_auto;
    try var_auto;
    auto;
    inversion H2;
    subst;
    auto.

  inversion H1; subst.
  erewrite H, H0; eauto.

  inversion H1; subst.
  erewrite H, H0; eauto.

  inversion H0; subst.
  erewrite H; eauto.

  inversion H0; subst.
  erewrite H; eauto.

  inversion H0; subst.
  erewrite H; eauto.

  inversion H0; subst.
  erewrite H; eauto.

  inversion H1; subst.
  erewrite H, H0; eauto.
Qed.

Lemma subst_equality :
  (forall x t1, x notin_t t1 ->
           forall t2, x notin_t t2 ->
                 forall n, ([c_ x /t n] t1) = ([c_ x /t n] t2) ->
                      t1 = t2).
Proof.
  destruct subst_equality_mutind; crush.
Qed.

Lemma subst_equality_s :
  (forall x s1, x notin_s s1 ->
           forall s2, x notin_s s2 ->
                 forall n, ([c_ x /s n] s1) = ([c_ x /s n] s2) ->
                      s1 = s2).
Proof.
  destruct subst_equality_mutind; crush.
Qed.

Lemma subst_equality_ss :
  (forall x ss1, x notin_ss ss1 ->
           forall ss2, x notin_ss ss2 ->
                 forall n, ([c_ x /ss n] ss1) = ([c_ x /ss n] ss2) ->
                      ss1 = ss2).
Proof.
  destruct subst_equality_mutind; crush.
Qed.

(*
Lemma conforms_uniqueness_mutind :
  (forall G1 t1 T, conforms G1 t1 T ->
              forall G2 t2, conforms G2 t2 T ->
                       length G1 = length G2 ->
                       t1 = t2) /\

  (forall G1 s1 T, conforms_s G1 s1 T ->
              forall G2 s2, conforms_s G2 s2 T ->
                       length G1 = length G2 ->
                       s1 = s2) /\

  (forall G1 ss1 T, conforms_ss G1 ss1 T ->
               forall G2 ss2, conforms_ss G2 ss2 T ->
                         length G1 = length G2 ->
                         ss1 = ss2).
Proof.
  apply conforms_mutind;
    intros;
    auto;
    try match goal with
        | [H : conforms _ ?t _ |- _ = ?t] => inversion H; subst
        | [H : conforms_s _ ?s _ |- _ = ?s] => inversion H; subst
        | [H : conforms_ss _ ?ss _ |- _ = ?ss] => inversion H; subst
        end;
    eauto;
    match goal with 
    | [H : length _ = length _ |- _] => rewrite H in *
    end;
    try solve [apply H in H6;
               subst;
               eauto];
    try solve [apply H in H5;
               subst;
               eauto].

  apply H in H3;
    simpl;
    auto.
  apply subst_equality_ss in H3;
    subst; auto.

  apply H in H11;
    simpl;
    auto.
  apply subst_equality_ss in H11;
    subst; auto.

  apply H0 in H6;
    simpl;
    auto.
  apply subst_equality in H6;
    subst; auto.
  apply H in H5;
    simpl;
    subst;
    auto.

  apply H in H7;
    simpl;
    subst;
    auto.
  apply H0 in H8;
    simpl;
    subst;
    auto.
Qed.
 *)

(*
Lemma conforms_uniqueness :
  (forall G1 t1 T, conforms G1 t1 T ->
              forall G2 t2, conforms G2 t2 T ->
                       length G1 = length G2 ->
                       t1 = t2).
Proof.
  destruct conforms_uniqueness_mutind; crush.
Qed.

Lemma conforms_uniqueness_s :
  (forall G1 s1 T, conforms_s G1 s1 T ->
              forall G2 s2, conforms_s G2 s2 T ->
                       length G1 = length G2 ->
                       s1 = s2).
Proof.
  destruct conforms_uniqueness_mutind; crush.
Qed.

Lemma conforms_uniqueness_ss :
  (forall G1 ss1 T, conforms_ss G1 ss1 T ->
               forall G2 ss2, conforms_ss G2 ss2 T ->
                         length G1 = length G2 ->
                         ss1 = ss2).
Proof.
  destruct conforms_uniqueness_mutind; crush.
Qed.
*)
Import WfExtensionality.

Lemma subtype_refl_sel :
  forall G1 G2 x L T1 T2, conforms G1 (sel x L) T1 ->
                     conforms G2 (sel x L) T2 ->
                     subtype T1 T2 = true.
Proof.
  intros.

  inversion H; inversion H0; subst.

  (*sel_upp*)  

  rewrite subtype_sel_upp_sel_upp_reduce
    with
      (x1:=x)(L1:=L)(T1':=T)
      (x2:=x)(L2:=L)(T2':=T0);
    auto;
    rewrite eq_var_refl, eq_label_refl;
    auto.

  rewrite subtype_sel_upp_sel_low_reduce
    with
      (x1:=x)(L1:=L)(T1':=T)
      (x2:=x)(L2:=L)(T2':=T0);
    auto;
    rewrite eq_var_refl, eq_label_refl;
    auto.

  rewrite subtype_sel_upp_sel_equ_reduce
    with
      (x1:=x)(L1:=L)(T1':=T)
      (x2:=x)(L2:=L)(T2':=T0);
    auto;
    rewrite eq_var_refl, eq_label_refl;
    auto.

  rewrite subtype_sel_upp_sel_nom_reduce
    with
      (x1:=x)(L1:=L)(T1':=T)
      (x2:=x)(L2:=L)(T2':=T0);
    auto;
    rewrite eq_var_refl, eq_label_refl;
    auto.

  (*sel_low*)

  rewrite subtype_sel_low_sel_upp_reduce
    with
      (x1:=x)(L1:=L)(T1':=T)
      (x2:=x)(L2:=L)(T2':=T0);
    auto;
    rewrite eq_var_refl, eq_label_refl;
    auto.

  rewrite subtype_sel_low_sel_low_reduce
    with
      (x1:=x)(L1:=L)(T1':=T)
      (x2:=x)(L2:=L)(T2':=T0);
    auto;
    rewrite eq_var_refl, eq_label_refl;
    auto.

  rewrite subtype_sel_low_sel_equ_reduce
    with
      (x1:=x)(L1:=L)(T1':=T)
      (x2:=x)(L2:=L)(T2':=T0);
    auto;
    rewrite eq_var_refl, eq_label_refl;
    auto.

  rewrite subtype_sel_low_sel_nom_reduce
    with
      (x1:=x)(L1:=L)(T1':=T)
      (x2:=x)(L2:=L)(T2':=T0);
    auto;
    rewrite eq_var_refl, eq_label_refl;
    auto.

  (*sel_equ*)

  rewrite subtype_sel_equ_sel_upp_reduce
    with
      (x1:=x)(L1:=L)(T1':=T)
      (x2:=x)(L2:=L)(T2':=T0);
    auto;
    rewrite eq_var_refl, eq_label_refl;
    auto.

  rewrite subtype_sel_equ_sel_low_reduce
    with
      (x1:=x)(L1:=L)(T1':=T)
      (x2:=x)(L2:=L)(T2':=T0);
    auto;
    rewrite eq_var_refl, eq_label_refl;
    auto.

  rewrite subtype_sel_equ_sel_equ_reduce
    with
      (x1:=x)(L1:=L)(T1':=T)
      (x2:=x)(L2:=L)(T2':=T0);
    auto;
    rewrite eq_var_refl, eq_label_refl;
    auto.

  rewrite subtype_sel_equ_sel_nom_reduce
    with
      (x1:=x)(L1:=L)(T1':=T)
      (x2:=x)(L2:=L)(T2':=T0);
    auto;
    rewrite eq_var_refl, eq_label_refl;
    auto.

  (*sel_nom*)

  rewrite subtype_sel_nom_sel_upp_reduce
    with
      (x1:=x)(L1:=L)(T1':=T)
      (x2:=x)(L2:=L)(T2':=T0);
    auto;
    rewrite eq_var_refl, eq_label_refl;
    auto.

  rewrite subtype_sel_nom_sel_low_reduce
    with
      (x1:=x)(L1:=L)(T1':=T)
      (x2:=x)(L2:=L)(T2':=T0);
    auto;
    rewrite eq_var_refl, eq_label_refl;
    auto.

  rewrite subtype_sel_nom_sel_equ_reduce
    with
      (x1:=x)(L1:=L)(T1':=T)
      (x2:=x)(L2:=L)(T2':=T0);
    auto;
    rewrite eq_var_refl, eq_label_refl;
    auto.

  rewrite subtype_sel_nom_sel_nom_reduce
    with
      (x1:=x)(L1:=L)(T1':=T)
      (x2:=x)(L2:=L)(T2':=T0);
    auto;
    rewrite eq_var_refl, eq_label_refl;
    auto.
Qed.

Parameter extends_uniqueness:
  forall G t t1, G ⊢ t ≤⦂⦂ t1 ->
            forall t2, G ⊢ t ≤⦂⦂ t2 ->
                  t1 = t2.

(*
Lemma conforms_tree_uniqueness_mutind :
  (forall G t T1, conforms G t T1 ->
             forall T2, conforms G t T2 ->
                   T1 = T2) /\

  (forall G s T1, conforms_s G s T1 ->
             forall T2, conforms_s G s T2 ->
                   T1 = T2) /\

  (forall G ss T1, conforms_ss G ss T1 ->
              forall T2, conforms_ss G ss T2 ->
                    T1 = T2).
Proof.
  apply conforms_mutind; intros.

  inversion H; auto.

  inversion H; auto.

  inversion H0; subst;
    try (apply member_uniqueness
           with
             (s1:=type L ⩽ t)
          in H3;
         auto;
         inversion H3;
         subst).
  rewrite (H T0 H5); auto.

  inversion H0; subst;
    try (apply member_uniqueness
           with
             (s1:=type L ⩾ t)
          in H3;
         auto;
         inversion H3;
         subst).
  rewrite (H T0 H4); auto.

  inversion H0; subst;
    try (apply member_uniqueness
           with
             (s1:=type L ≝ t)
          in H3;
         auto;
         inversion H3;
         subst).
  rewrite (H T0 H4); auto.

  inversion H0; subst;
    try (apply member_uniqueness
           with
             (s1:=type L ⪯ t)
          in H3;
         auto;
         inversion H3;
         subst).
  rewrite (H T0 H5); auto.

  inversion H0; subst.
  rewrite (H Ts0 H2); auto.
  
  inversion H1; subst;
    try solve [inversion i; subst;
               shape_auto; crush].
  apply extends_uniqueness
    with
      (t1:=t)
    in H5;
    auto;
    subst t0.
  rewrite (H Ts0), (H0 T0);
    auto.

  inversion H; subst;
    try solve [inversion i; subst;
               shape_auto; crush].
  crush.

  apply member_uniqueness with (s1:=type L ⩽ t) in H3;
    [|auto|auto]; inversion H3; subst.
  apply member_uniqueness with (s1:=type L ⩽ t) in H3;
    [|auto|auto]; inversion H3; subst.

  inversion H3; subst.
  inversion H5; subst.
  apply member_uniqueness with (s1:=type L ⩽ t) in H7;
    [|auto|auto]; inversion H7; subst.
  apply struct_is_not_shape in i; crush.
  apply member_uniqueness with (s1:=type L ⩽ t) in H7;
    [|auto|auto]; inversion H7; subst.
  apply member_uniqueness with (s1:=type L ⩽ t) in H7;
    [|auto|auto]; inversion H7; subst.

  inversion H; subst;
    try solve [inversion i; subst;
               shape_auto; crush].
  crush.

  apply member_uniqueness with (s1:=type L ≝ t) in H3;
    [|auto|auto]; inversion H3; subst.
  apply struct_is_not_shape in i; crush.
  apply member_uniqueness with (s1:=type L ≝ t) in H3;
    [|auto|auto]; inversion H3; subst.

  inversion H3; subst.
  inversion H5; subst.
  apply member_uniqueness with (s1:=type L ≝ t) in H7;
    [|auto|auto]; inversion H7; subst.
  apply member_uniqueness with (s1:=type L ≝ t) in H7;
    [|auto|auto]; inversion H7; subst.
  apply struct_is_not_shape in i; crush.
  apply member_uniqueness with (s1:=type L ≝ t) in H7;
    [|auto|auto]; inversion H7; subst.

  inversion H; subst;
    try solve [inversion i; subst;
               shape_auto; crush].
  crush.

  apply member_uniqueness with (s1:=type L ⪯ t) in H3;
    [|auto|auto]; inversion H3; subst.
  apply member_uniqueness with (s1:=type L ⪯ t) in H3;
    [|auto|auto]; inversion H3; subst.
  apply struct_is_not_shape in i; crush.

  inversion H3; subst.
  inversion H5; subst.
  apply member_uniqueness with (s1:=type L ⪯ t) in H7;
    [|auto|auto]; inversion H7; subst.
  apply member_uniqueness with (s1:=type L ⪯ t) in H7;
    [|auto|auto]; inversion H7; subst.
  apply member_uniqueness with (s1:=type L ⪯ t) in H7;
    [|auto|auto]; inversion H7; subst.
  apply struct_is_not_shape in i; crush.

  (*t_sha_sel*)
  inversion H0; subst.
  apply shape_is_not_material in i0; inversion H5; crush.
  inversion e; subst.
  inversion H5; subst.
  apply member_uniqueness with (s1:=type L ⩽ t0) in H7;
    [|auto|auto]; inversion H7; subst.
  apply H12 in i0.
  apply shape_is_not_struct in i0; crush.
  apply member_uniqueness with (s1:=type L ⩽ t0) in H7;
    [|auto|auto]; inversion H7; subst.
  apply member_uniqueness with (s1:=type L ⩽ t0) in H7;
    [|auto|auto]; inversion H7; subst.

  inversion e; subst.
  inversion H5; subst.
  apply member_uniqueness with (s1:=type L ≝ t0) in H7;
    [|auto|auto]; inversion H7; subst.
  apply member_uniqueness with (s1:=type L ≝ t0) in H7;
    [|auto|auto]; inversion H7; subst.
  apply H12 in i0.
  apply shape_is_not_struct in i0; crush.
  apply member_uniqueness with (s1:=type L ≝ t0) in H7;
    [|auto|auto]; inversion H7; subst.

  inversion e; subst.
  inversion H5; subst.
  apply member_uniqueness with (s1:=type L ⪯ t0) in H7;
    [|auto|auto]; inversion H7; subst.
  apply member_uniqueness with (s1:=type L ⪯ t0) in H7;
    [|auto|auto]; inversion H7; subst.
  apply member_uniqueness with (s1:=type L ⪯ t0) in H7;
    [|auto|auto]; inversion H7; subst.
  apply H12 in i0.
  apply shape_is_not_struct in i0; crush.

  apply extends_uniqueness with (t1:=t) in H4; subst; auto.
  rewrite (H T0); auto.

  inversion H1; subst.
  rewrite (H T0), (H0 T'0); auto.

  inversion H0; subst.
  rewrite (H T0); auto.

  inversion H0; subst.
  rewrite (H T0); auto.

  inversion H0; subst.
  rewrite (H T0); auto.

  inversion H0; subst.
  rewrite (H T0); auto.

  inversion H; auto.

  inversion H1; subst.
  rewrite (H T0); auto.
  rewrite (H0 Ts0); auto.
Qed.
*)

(*
Lemma conforms_tree_uniqueness :
  (forall G t T1, conforms G t T1 ->
             forall T2, conforms G t T2 ->
                   T1 = T2).
Proof.
  destruct conforms_tree_uniqueness_mutind; crush.
Qed.

Lemma conforms_tree_uniqueness_s :
  (forall G s T1, conforms_s G s T1 ->
             forall T2, conforms_s G s T2 ->
                   T1 = T2).
Proof.
  destruct conforms_tree_uniqueness_mutind; crush.
Qed.

Lemma conforms_tree_uniqueness_ss :
  (forall G t Ts1, conforms_ss G t Ts1 ->
              forall Ts2, conforms_ss G t Ts2 ->
                     Ts1 = Ts2).
Proof.
  destruct conforms_tree_uniqueness_mutind; crush.
Qed.
 *)

Lemma eq_ty_refl_mutind :
  (forall t, eq_ty t t = true) /\
  (forall σ, eq_decl σ σ= true) /\
  (forall σs, eq_decls σs σs = true).
Proof.
  apply type_mutind;
    intros;
    simpl;
    auto;
    try solve [rewrite H, H0;
               auto];
    try solve [rewrite H, eq_label_refl;
               auto].
  rewrite eq_var_refl, eq_label_refl;
    auto.
Qed.

Lemma eq_ty_refl :
  (forall t, eq_ty t t = true).
Proof.
  destruct eq_ty_refl_mutind; crush.
Qed.

Theorem subtype_equivalence1 :
  (forall G1 t1 t2 G2, G1 ⊢ t1 ≤ t2 ⊣ G2 ->
                  is_material t2 ->
                  forall T1 T2, conforms G1 t1 T1 ->
                           conforms G2 t2 T2 ->
                           subtype T1 T2 = true) /\
  
  (forall G1 s1 s2 G2, G1 ⊢ s1 ≤; s2 ⊣ G2 ->
                  is_material_s s2 ->
                  forall T1 T2, conforms_s G1 s1 T1 ->
                           conforms_s G2 s2 T2 ->
                           subtype T1 T2 = true) /\
  
  (forall G1 ss1 ss2 G2, G1 ⊢ ss1 ≤;; ss2 ⊣ G2 ->
                    is_material_ss ss2 ->
                    forall T1 T2, conforms_ss G1 ss1 T1 ->
                             conforms_ss G2 ss2 T2 ->
                             subtype T1 T2 = true).
Proof.
  apply subtype_mutind; intros.

  (*s-top*)
  inversion H1; subst;
  apply subtype_top;
    inversion H0;
    subst;
    intros;
    intro Hcontra;
    inversion Hcontra.

  (*s-bot*)
  inversion H0; subst.
  apply subtype_bot;
    inversion H1;
    subst;
    intros;
    intro Hcontra;
    inversion Hcontra.

  (*s-refl*)
  apply subtype_refl_sel
    with (G1:=Γ1)(G2:=Γ2)(x:=x)(L:=l);
    auto.

  (*s-lower-1*)
  inversion H2; subst;
    try (apply member_uniqueness
           with
             (s1:=type l ⩾ t2)
          in H5;
         auto;
         inversion H5;
         subst).
  apply subtype_rhs_sel_low_reduce
    with
      (x:=x)(L:=l)(T2':=T); auto;
    intros;
    intro Hcontra;
    subst T1; inversion H1.

  
  (*s-lower-2*)
  inversion H2; subst;
    try (apply member_uniqueness
           with
             (s1:=type l ≝ t2)
          in H5;
         auto;
         inversion H5;
         subst).
  apply subtype_rhs_sel_equ_reduce
    with
      (x:=x)(L:=l)(T2':=T); auto;
    intros;
    try solve [intro Hcontra;
               subst T1; inversion H1].
  
  (*s-upper-1*)
  inversion H1; subst;
    try (apply member_uniqueness
           with
             (s1:=type l ⩽ t1)
          in H5;
         auto;
         inversion H5;
         subst).
  rewrite subtype_sel_upp_reduce
    with (x1:=x)(L1:=l)(T1':=T);
    auto.
  destruct T2; auto;
    try solve [rewrite H; crush];
    try solve [inversion H2].
  
  (*s-upper-2*)
  inversion H1; subst;
    try (apply member_uniqueness
           with
             (s1:=type l ≝ t1)
          in H5;
         auto;
         inversion H5;
         subst).
  rewrite subtype_sel_equ_reduce
    with (x1:=x)(L1:=l)(T1':=T);
    auto.
  destruct T2; auto;
    try solve [rewrite H; crush];
    try solve [inversion H2].
  
  (*s-upper-3*)
  inversion H1; subst;
    try (apply member_uniqueness
           with
             (s1:=type l ⪯ t1)
          in H5;
         auto;
         inversion H5;
         subst).
  rewrite subtype_sel_nom_reduce
    with (x1:=x)(L1:=l)(T1':=T);
    auto.
  destruct T2; auto;
    try solve [rewrite H; crush];
    try solve [inversion H2].

  (*s-all*)
  inversion H2; inversion H3; subst.
  rewrite subtype_all_all_reduce
    with (T1:=T)(T2:=T')(T1':=T0)(T2':=T'0);
    auto.
  rewrite H, H0; auto.
  apply is_material_subst; auto.
  mat_auto; auto.

  (*s-refn*)
  inversion H1; inversion H2; subst;
    try solve [inversion H8];
    try solve [inversion H10];
    try solve [inversion H11];
    try match goal with
          [H : sel ?x1 ?l1 = sel ?x2 ?l2 |-_] => inversion H; subst x1 l1
        end;
    try solve [shape_auto; auto];
    try solve [inversion H0;
               subst;
               shape_auto;
               auto].

  rewrite subtype_rfn_top_rfn_top_reduce with (Ts1:=Ts)(Ts2:=Ts0);
    auto.
  rewrite H;
    auto.
  apply is_material_ss_subst;
    inversion H0;
    subst;
    auto.

  rewrite subtype_rfn_sel_rfn_sel_eq_reduce
    with
      (x:=x)(L:=L)
      (Ts1:=Ts)(T1':=T)
      (Ts2:=Ts0)(T2':=T0);
    auto.
  rewrite H; auto.
  apply is_material_ss_subst;
    inversion H0;
    subst;
    auto.
  
  (*s-extend*)
  inversion e; subst.

  inversion H1;
    subst;
    auto.
  
  apply member_uniqueness with (s1:=type L ⩽ t0) in H3; auto;
    inversion H3; subst.
  subtype_reduce;
    auto;
    try solve [intros; intro Hcontra; subst;
               inversion H2].
  
  apply member_uniqueness with (s1:=type L ⩽ t) in H7; auto;
    inversion H7; subst.
  
  apply member_uniqueness with (s1:=type L ⩽ t) in H7; auto;
    inversion H7; subst.
  
  apply member_uniqueness with (s1:=type L ⩽ t) in H7; auto;
    inversion H7; subst.

  inversion H1; subst.
  
  apply member_uniqueness with (s1:=type L ≝ t) in H7; auto;
    inversion H7; subst.
  
  apply member_uniqueness with (s1:=type L ≝ t) in H7; auto;
    inversion H7; subst.
  
  apply member_uniqueness with (s1:=type L ≝ t) in H7; auto;
    inversion H7; subst.
  
  subtype_reduce; auto;
    try solve [intros; intro Hcontra; subst;
               inversion H2].
  
  apply member_uniqueness with (s1:=type L ≝ t) in H7; auto;
    inversion H7; subst.

  inversion H1; subst.
  
  apply member_uniqueness with (s1:=type L ⪯ t) in H7; auto;
    inversion H7; subst.

  apply member_uniqueness with (s1:=type L ⪯ t) in H7; auto;
    inversion H7; subst.
  
  apply member_uniqueness with (s1:=type L ⪯ t) in H7; auto;
    inversion H7; subst.
  
  apply member_uniqueness with (s1:=type L ⪯ t) in H7; auto;
    inversion H7; subst.
  subtype_reduce; auto;
    try solve [intros; intro Hcontra; subst;
               inversion H2].

  inversion H1; subst.

  inversion H3.

  apply extends_uniqueness with (t1:=t) in H7; auto; subst t1.
  apply subtype_lhs_rfn_sel_reduce
    with
      (x1:=x)(L1:=L)(Ts1:=Ts)(T1':=T); auto;
    try solve [intros;
               intros Hcontra;
               subst T2;
               inversion H2].

  inversion H3; subst.
  apply member_uniqueness with (s1:=type L ⩽ t1) in H10; auto;
    inversion H10; subst t1.
  apply H13 in H11. 
  apply struct_is_not_shape in H11; auto.
  apply member_uniqueness with (s1:=type L ⩽ t1) in H10; auto;
    inversion H10; subst t1.
  apply member_uniqueness with (s1:=type L ⩽ t1) in H10; auto;
    inversion H10; subst t1.

  inversion H3; subst.
  apply member_uniqueness with (s1:=type L ≝ t1) in H10; auto;
    inversion H10; subst t1.
  apply member_uniqueness with (s1:=type L ≝ t1) in H10; auto;
    inversion H10; subst t1.
  apply H13 in H11.
  apply struct_is_not_shape in H11; auto.
  apply member_uniqueness with (s1:=type L ≝ t1) in H10; auto;
    inversion H10; subst t1.

  inversion H3; subst.
  apply member_uniqueness with (s1:=type L ⪯ t1) in H10; auto;
    inversion H10; subst t1.
  apply member_uniqueness with (s1:=type L ⪯ t1) in H10; auto;
    inversion H10; subst t1.
  apply member_uniqueness with (s1:=type L ⪯ t1) in H10; auto;
    inversion H10; subst t1.
  apply H13 in H11.
  apply struct_is_not_shape in H11; auto.

  apply subtype_lhs_sha_sel_reduce
    with
      (x1:=x)(L1:=L)(T1':=T)(ss:=ss);
    auto;
    try solve [intros;
               intro Hcontra;
               subst T2;
               inversion H2];
    apply extends_uniqueness with (t1:=t) in H7;
    auto;
    subst t1;
    apply H; auto.

  (*s-low*)
  inversion H1; inversion H2; subst.
  erewrite subtype_low_low_reduce; eauto.
  rewrite H; auto.
  rewrite eq_label_refl; auto.

  (*s-upp*)
  inversion H1; inversion H2; subst.
  erewrite subtype_upp_upp_reduce; eauto.
  rewrite H; auto.
  rewrite eq_label_refl; auto.
  inversion H0; auto.

  (*s-eq-lo*)
  inversion H1; inversion H2; subst.
  erewrite subtype_equ_low_reduce; eauto.
  rewrite H; auto.
  rewrite eq_label_refl; auto.

  (*s-eq-up*)
  inversion H1; inversion H2; subst.
  erewrite subtype_equ_upp_reduce; eauto.
  rewrite H; auto.
  rewrite eq_label_refl; auto.
  inversion H0; auto.

  (*s-equ-equ*)
  inversion H2; inversion H3; subst.
  erewrite subtype_equ_equ_reduce; eauto.
  rewrite H, H0; auto.
  rewrite eq_label_refl; auto.

  (*s-nom-up*)
  inversion H1; inversion H2; subst.
  erewrite subtype_nom_upp_reduce; eauto.
  rewrite H; auto.
  rewrite eq_label_refl; auto.
  inversion H0; auto.

  (*s-nom-nom*)
  inversion H0; inversion H1; subst.
  erewrite subtype_nom_nom_reduce; eauto.
  rewrite eq_label_refl, eq_ty_refl; auto.
  

  (*s-nil*)
  inversion H1; subst.
  inversion H0; subst.
  apply subtype_nil_nil_reduce; auto.
  eapply subtype_con_nil_reduce; eauto.

  (*s-con*)
  inversion H2; inversion H3; subst.
  erewrite subtype_con_con_reduce; eauto.
  rewrite H, H0; auto.
  inversion H1; auto.
  inversion H1; auto.
Qed.

Lemma subtype_equivalence_top_lhs :
  forall G2 t T, conforms G2 t T ->
            subtype t_top T = true ->
            forall G1, G1 ⊢ top ≤ t ⊣ G2.
Proof.
  intros G2 t T Hconf;
    induction Hconf;
    intros;
    auto;
    try solve [match goal with
               | [H : (subtype t_top t_bot = true) |- _] =>
                 rewrite subtype_lhs_top_reduce in H; inversion H
               | [H : (subtype t_top (t_sel_upp _ _ _) = true) |- _] =>
                 rewrite subtype_lhs_top_reduce in H; inversion H
               | [H : (subtype t_top (t_sel_nom _ _ _) = true) |- _] =>
                 rewrite subtype_lhs_top_reduce in H; inversion H
               | [H : (subtype t_top (t_rfn_top _) = true) |- _] =>
                 rewrite subtype_lhs_top_reduce in H; inversion H
               | [H : (subtype t_top (t_rfn_sel _ _ _ _) = true) |- _] =>
                 rewrite subtype_lhs_top_reduce in H; inversion H
               | [H : (subtype t_top (t_sha_top _ _ _) = true) |- _] =>
                 rewrite subtype_lhs_top_reduce in H; inversion H
               | [H : (subtype t_top (t_sha_sel _ _ _ _) = true) |- _] =>
                 rewrite subtype_lhs_top_reduce in H; inversion H
               | [H : (subtype t_top (t_all _ _) = true) |- _] =>
                 rewrite subtype_lhs_top_reduce in H; inversion H
               end].

  rewrite subtype_lhs_top_reduce in H2.
  apply s_lower_1 with (t2:=t), IHHconf; auto.
  
  rewrite subtype_lhs_top_reduce in H2.
  apply s_lower_2 with (t2:=t), IHHconf; auto.
Qed.

Lemma subtype_equiv_lhs_top :
  forall G2 t T, conforms G2 t T ->
            subtype t_top T = true ->
            forall G1, G1 ⊢ top ≤ t ⊣ G2.
Proof.
  intros G2 t T Hconf;
    induction Hconf;
    intros;
    auto;
    try solve [subtype_reduce; crush].
Qed.

Lemma subtype_equiv_lhs_bot :
  forall G1 t T, conforms G1 t T ->
            subtype T t_bot = true ->
            forall G2, G1 ⊢ t ≤ bot ⊣ G2.
Proof.
  intros G1 t T Hconf;
    induction Hconf;
    intros;
    auto;
    try solve [subtype_reduce; eauto; crush].
Qed.

Lemma subtype_equivalence_sel_upp_lhs :
  forall G2 t2 T2, conforms G2 t2 T2 ->
              is_material t2 ->
              forall G1 x L t1 T1, G1 ⊢ x ∋ (type L ⩽ t1) ->
                              (forall t2' T2', conforms G2 t2' T2' ->
                                          is_material t2' ->
                                          subtype T1 T2' = true ->
                                          G1 ⊢ t1 ≤ t2' ⊣ G2) ->
                              subtype (t_sel_upp x L T1) T2 = true ->
                              G1 ⊢ (sel x L) ≤ t2 ⊣ G2.
Proof.
  intros G2 t2 T2 Hconf;
    induction Hconf;
    intros;
    subtype_reduce;
    bool_auto;
    eq_auto;
    eauto.
Qed.

Lemma subtype_equivalence_sel_equ_lhs :
  forall G2 t2 T2, conforms G2 t2 T2 ->
              is_material t2 ->
              forall G1 x L t1 T1, G1 ⊢ x ∋ (type L ≝ t1) ->
                              (forall t2' T2', conforms G2 t2' T2' ->
                                          is_material t2' ->
                                          subtype T1 T2' = true ->
                                          G1 ⊢ t1 ≤ t2' ⊣ G2) ->
                              subtype (t_sel_equ x L T1) T2 = true ->
                              G1 ⊢ (sel x L) ≤ t2 ⊣ G2.
Proof.
  intros G2 t2 T2 Hconf;
    induction Hconf;
    intros;
    subtype_reduce;
    bool_auto;
    eq_auto;
    eauto.
Qed.

Lemma subtype_equivalence_sel_low_lhs :
  forall G2 t2 T2, conforms G2 t2 T2 ->
              forall G1 x L t1, G1 ⊢ x ∋ (type L ⩾ t1) ->
                           forall T1, conforms G1 (sel x L) (t_sel_low x L T1) ->
                                 subtype (t_sel_low x L T1) T2 = true ->
                                 G1 ⊢ (sel x L) ≤ t2 ⊣ G2.
Proof.
  intros G t2 T2 Hconf;
    induction Hconf;
    intros;
    auto;
    try solve [subtype_reduce;
               bool_auto;
               eq_auto;
               eauto].
Qed.

Lemma subtype_equivalence_sel_nom_lhs :
  forall G2 t2 T2, conforms G2 t2 T2 ->
              is_material t2 ->
              forall G1 x L t1 T1, G1 ⊢ x ∋ (type L ⪯ t1) ->
                              (forall t2' T2', conforms G2 t2' T2' ->
                                          is_material t2' ->
                                          subtype T1 T2' = true ->
                                          G1 ⊢ t1 ≤ t2' ⊣ G2) ->
                              subtype (t_sel_nom x L T1) T2 = true ->
                              G1 ⊢ (sel x L) ≤ t2 ⊣ G2.
Proof.
  intros G2 t2 T2 Hconf;
    induction Hconf;
    intros;
    subtype_reduce;
    bool_auto;
    eq_auto;
    eauto.
Qed.

Lemma subtype_equivalence_sel_equ_rhs :
  forall G1 t1 T1, conforms G1 t1 T1 ->
              forall G2 x L t2 T2, G2 ⊢ x ∋ (type L ≝ t2) ->
                              (forall t1' T1', conforms G1 t1' T1' ->
                                          subtype T1' T2 = true ->
                                          G1 ⊢ t1' ≤ t2 ⊣ G2) ->
                              subtype T1 (t_sel_equ x L T2) = true ->
                              G1 ⊢ t1 ≤ (sel x L) ⊣ G2.
Proof.
  intros G1 t1 T1 Hconf;
    induction Hconf;
    intros;
    try subtype_reduce;
    bool_auto;
    eq_auto;
    eauto.
Qed.

Lemma subtype_equivalence_sel_low_rhs :
  forall G1 t1 T1, conforms G1 t1 T1 ->
              forall G2 x L t2 T2, G2 ⊢ x ∋ (type L ⩾ t2) ->
                              (forall t1' T1', conforms G1 t1' T1' ->
                                          subtype T1' T2 = true ->
                                          G1 ⊢ t1' ≤ t2 ⊣ G2) ->
                              subtype T1 (t_sel_low x L T2) = true ->
                              G1 ⊢ t1 ≤ (sel x L) ⊣ G2.
Proof.
  intros G1 t1 T1 Hconf;
    induction Hconf;
    intros;
    try subtype_reduce;
    bool_auto;
    eq_auto;
    eauto.
Qed.

Lemma subtype_equivalence_sel_upp_rhs :
  forall G1 t T, conforms G1 t T ->
            forall x L T', subtype T (t_sel_upp x L T') = true ->
                      forall G2, G1 ⊢ t ≤ (sel x L) ⊣ G2.
Proof.
  intros G t T Hconf;
    induction Hconf;
    intros;
    try solve [subtype_reduce;
               bool_auto;
               eq_auto;
               crush;
               eauto];
    auto.
Qed.

Lemma subtype_equivalence_sel_nom_rhs :
  forall G1 t T, conforms G1 t T ->
            forall x L T', subtype T (t_sel_nom x L T') = true ->
                      forall G2, G1 ⊢ t ≤ (sel x L) ⊣ G2.
Proof.
  intros G t T Hconf;
    induction Hconf;
    intros;
    try solve [subtype_reduce;
               bool_auto;
               eq_auto;
               crush;
               eauto];
    auto.
Qed.

Lemma subtype_equivalence_rfn_top_lhs :
  forall G2 t2 T2, conforms G2 t2 T2 ->
              is_material t2 ->
              forall G1 ss1 Ts1,
                conforms G1 (top str ss1 rts) (t_rfn_top Ts1) ->
                (forall ss2 Ts2,
                    conforms G2 (top str ss2 rts) (t_rfn_top Ts2) ->
                    is_material (top str ss2 rts) ->
                    subtype Ts1 Ts2 = true ->
                    (top str ss1 rts ::G1) ⊢ ([c_ (length G1) /ss 0] ss1) ≤;; ([c_ (length G2) /ss 0] ss2) ⊣ (top str ss2 rts ::G2)) ->
                subtype (t_rfn_top Ts1) T2 = true ->
                G1 ⊢ (top str ss1 rts) ≤ t2 ⊣ G2.
Proof.
  intros G t T Hconf;
    induction Hconf;
    intros;
    auto;
    subtype_reduce;
    bool_auto;
    eauto.
Qed.

Lemma subtype_equivalence_rfn_top_rhs :
  forall G1 t1 T1, conforms G1 t1 T1 ->
              forall G2 ss2 Ts2,
                conforms G2 (top str ss2 rts) (t_rfn_top Ts2) ->
                is_material (top str ss2 rts) ->
                (forall ss1 Ts1,
                    conforms G1 (top str ss1 rts) (t_rfn_top Ts1) ->
                    subtype Ts1 Ts2 = true ->
                    (top str ss1 rts ::G1) ⊢ ([c_ (length G1) /ss 0] ss1) ≤;; ([c_ (length G2) /ss 0] ss2) ⊣ (top str ss2 rts::G2)) ->
                subtype T1 (t_rfn_top Ts2) = true ->
                G1 ⊢ t1 ≤ (top str ss2 rts) ⊣ G2.
Proof.
  intros G1 t1 T1 Hconf;
    induction Hconf;
    intros;
    auto;
    subtype_reduce;
    bool_auto;
    eauto.
Qed.

Lemma subtype_equivalence_rfn_sel_lhs :
  forall G2 t2 T2, conforms G2 t2 T2 ->
              is_material t2 ->
              forall G1 x L ss1 t1 Ts1 T1, conforms G1 (sel x L str ss1 rts) (t_rfn_sel x L Ts1 T1) ->
                                      G1 ⊢ (sel x L str ss1 rts) ≤⦂⦂ t1 ->
                                           (forall ss2 Ts2 T2', conforms G2 (sel x L str ss2 rts) (t_rfn_sel x L Ts2 T2') ->
                                                           is_material (sel x L str ss2 rts) ->
                                                           subtype Ts1 Ts2 = true ->
                                                           (sel x L str ss1 rts ::G1) ⊢ ([c_ (length G1) /ss 0] ss1) ≤;; ([c_ (length G2) /ss 0] ss2) ⊣ (sel x L str ss2 rts :: G2)) ->
                                           (forall t2' T2', conforms G2 t2' T2' ->
                                                       is_material t2' ->
                                                       subtype T1 T2' = true ->
                                                       G1 ⊢ t1 ≤ t2' ⊣ G2) ->
                                           subtype (t_rfn_sel x L Ts1 T1) T2 = true ->
                                           G1 ⊢ (sel x L str ss1 rts) ≤ t2 ⊣ G2.
Proof.
  intros G t T Hconf;
    induction Hconf;
    intros;
    auto;
    subtype_reduce;
    bool_auto;
    eq_auto;
    try solve [apply s_extend with (t:=t1);
               eauto].

  apply s_lower_1 with (t2:=t);
    eauto.

  apply s_lower_2 with (t2:=t);
    eauto.

  apply s_refine; eauto.
Qed.

Lemma subtype_equivalence_rfn_sel_rhs :
  forall G1 t1 T1, conforms G1 t1 T1 ->
              forall G2 x L ss2 Ts2 T2, conforms G2 (sel x L str ss2 rts) (t_rfn_sel x L Ts2 T2) ->
                                   is_material (sel x L str ss2 rts) ->
                                           (forall ss1 Ts1 T1', conforms G1 (sel x L str ss1 rts) (t_rfn_sel x L Ts1 T1') ->
                                                           subtype Ts1 Ts2 = true ->
                                                           (sel x L str ss1 rts ::G1) ⊢ ([c_ (length G1) /ss 0] ss1) ≤;; ([c_ (length G2) /ss 0] ss2) ⊣ (sel x L str ss2 rts :: G2)) ->
                                           subtype T1 (t_rfn_sel x L Ts2 T2) = true ->
                                           G1 ⊢ t1 ≤ (sel x L str ss2 rts) ⊣ G2.
Proof.
   intros G1 t1 T1 Hconf;
     induction Hconf;
     intros;
     auto;
     subtype_reduce;
     bool_auto;
     eq_auto.

   apply s_upper_1 with (t1:=t);
     eauto.

   apply s_upper_2 with (t1:=t);
     eauto.

   apply s_upper_3 with (t1:=t);
     eauto.

   apply s_refine; eauto.
   
   apply s_extend with (t:=t);
     eauto.
 Qed.


Lemma subtype_equivalence_sha_top_lhs :
  forall G2 t2 T2, conforms G2 t2 T2 ->
              is_material t2 ->
              forall G1 x L ss, conforms G1 (sel x L str ss rts) (t_sha_top x L ss) ->
                           subtype (t_sha_top x L ss) T2 = true ->
                           G1 ⊢ (sel x L str ss rts) ≤ t2 ⊣ G2.
Proof.
  intros G t2 T2 Hconf;
    induction Hconf;
    intros;
    auto;
    try solve [subtype_reduce;
               bool_auto;
               eq_auto;
               eauto].
Qed.

Lemma subtype_equivalence_sha_sel_lhs :
  forall G2 t2 T2, conforms G2 t2 T2 ->
              is_material t2 ->
              forall G1 x L ss t1, G1 ⊢ (sel x L str ss rts) ≤⦂⦂ t1 ->
                              forall T1, conforms G1 t1 T1 ->
                                    (forall t2' T2', conforms G2 t2' T2' ->
                                                is_material t2' ->
                                                subtype T1 T2' = true ->
                                                G1 ⊢ t1 ≤ t2' ⊣ G2) ->
                                    subtype (t_sha_sel x L ss T1) T2 = true ->
                                    G1 ⊢ (sel x L str ss rts) ≤ t2 ⊣ G2.

Proof.
  intros G t2 T2 Hconf;
    induction Hconf;
    intros;
    auto;
    subtype_reduce;
    bool_auto;
    eq_auto;
    try solve [apply s_extend with (t:=t1);
               eauto];
    eauto.
Qed.

Lemma subtype_equivalence_all_lhs :
  forall G2 t2 T2, conforms G2 t2 T2 ->
              is_material t2 ->
              forall G1 ta1 tb1 Ta1 Tb1,
                conforms G1 (all ta1 ∙ tb1) (t_all Ta1 Tb1) ->
                (forall ta2 tb2 Ta2 Tb2,
                    conforms G2 (all ta2 ∙ tb2) (t_all Ta2 Tb2)  ->
                    is_material (all ta2 ∙ tb2) ->
                    (subtype Ta2 Ta1 = true ->
                     G2 ⊢ ta2 ≤ ta1 ⊣ G1) /\
                    (subtype Tb1 Tb2 = true ->
                     (ta1::G1) ⊢ ([c_ (length G1) /t 0] tb1) ≤ ([c_ (length G2) /t 0] tb2) ⊣ (ta2::G2))) ->
                subtype (t_all Ta1 Tb1) T2 = true ->
                G1 ⊢ (all ta1 ∙ tb1) ≤ t2 ⊣ G2.
Proof.
  intros G t T Hconf;
    induction Hconf;
    intros;
    auto;
    subtype_reduce;
    bool_auto.

  destruct H2
    with
      (ta2:=t)(tb2:=t')
      (Ta2:=T)(Tb2:=T');
    auto.
Qed.

Lemma subtype_equivalence_all_rhs :
  forall G1 t1 T1, conforms G1 t1 T1 ->
              forall G2 ta2 tb2 Ta2 Tb2,
                conforms G2 (all ta2 ∙ tb2) (t_all Ta2 Tb2) ->
                is_material (all ta2 ∙ tb2) ->
                (forall ta1 tb1 Ta1 Tb1,
                    conforms G1 (all ta1 ∙ tb1) (t_all Ta1 Tb1)  ->
                    (subtype Ta2 Ta1 = true ->
                     G2 ⊢ ta2 ≤ ta1 ⊣ G1) /\
                    (subtype Tb1 Tb2 = true ->
                     (ta1::G1) ⊢ ([c_ (length G1) /t 0] tb1) ≤ ([c_ (length G2) /t 0] tb2) ⊣ (ta2::G2))) ->
                subtype T1 (t_all Ta2 Tb2) = true ->
                G1 ⊢ t1 ≤ (all ta2 ∙ tb2) ⊣ G2.
Proof.
  intros G t T Hconf;
    induction Hconf;
    intros;
    auto;
    subtype_reduce;
    bool_auto.

  apply s_upper_1 with (t1:=t); eauto.
  
  apply s_upper_2 with (t1:=t); eauto.
  
  apply s_upper_3 with (t1:=t); eauto.

  destruct H2
    with
      (ta1:=t)(tb1:=t')
      (Ta1:=T)(Tb1:=T');
    eauto.
Qed.

Ltac subtype_equiv :=
  match goal with
  | [Hsub : subtype (t_sel_upp ?x ?l ?T),
            Hconf : conforms ?G2 ?t2 ?T2  |- ?G1 ⊢ (sel ?x ?l) ≤ ?t2 ⊣ ?G2]
    => eapply subtype_equivalence_sel_upp_lhs; eauto
  end.

Lemma subtype_equivalence2 :
  (forall G1 t1 T1, conforms G1 t1 T1 ->
               forall G2 t2 T2, conforms G2 t2 T2 ->
                           (is_material t2 ->
                            subtype T1 T2 = true ->
                            G1 ⊢ t1 ≤ t2 ⊣ G2) /\
                           (is_material t1 ->
                            subtype T2 T1 = true ->
                            G2 ⊢ t2 ≤ t1 ⊣ G1)) /\

  (forall G1 s1 T1, conforms_s G1 s1 T1 ->
               forall G2 s2 T2, conforms_s G2 s2 T2 ->
                           (is_material_s s2 ->
                            subtype T1 T2 = true ->
                            G1 ⊢ s1 ≤; s2 ⊣ G2) /\
                           (is_material_s s1 ->
                            subtype T2 T1 = true ->
                            G2 ⊢ s2 ≤; s1 ⊣ G1)) /\

  (forall G1 ss1 T1, conforms_ss G1 ss1 T1 ->
                forall G2 ss2 T2, conforms_ss G2 ss2 T2 ->
                             (is_material_ss ss2 ->
                              subtype T1 T2 = true ->
                              G1 ⊢ ss1 ≤;; ss2 ⊣ G2) /\
                             (is_material_ss ss1 ->
                              subtype T2 T1 = true ->
                              G2 ⊢ ss2 ≤;; ss1 ⊣ G1)).
Proof.
  apply conforms_mutind;
    intros;
    split;
    intros;
    auto;
    try solve [subtype_equiv];
    try solve [mat_auto; shape_auto; crush];
    try solve [eapply subtype_equivalence_sha_top_lhs;
               eauto].

  (* top *)
  (* <: *)
  eapply subtype_equiv_lhs_top;
    eauto.

  (* bot *)
  (* >: *)
  eapply subtype_equiv_lhs_bot;
    eauto.

  (* sel upp *)
  (* <: *)
  eapply subtype_equivalence_sel_upp_lhs;
    eauto;
    intros;
    edestruct H as [Ha Hb];
    eauto;
    eapply Ha;
    eauto.

  (* >: *)
  eapply subtype_equivalence_sel_upp_rhs;
    eauto.

  (* sel low  *)
  (* <: *)
  eapply subtype_equivalence_sel_low_lhs;
    eauto.

  (* >: *)
  eapply subtype_equivalence_sel_low_rhs;
    eauto;
    intros;
    edestruct H as [Ha Hb];
    eauto;
    eapply Ha;
    eauto.

  (* sel equ *)
  (* <: *)
  eapply subtype_equivalence_sel_equ_lhs;
    eauto;
    intros;
    edestruct H as [Ha Hb];
    eauto;
    eapply Ha;
    eauto.
  
  (* >: *)
  eapply subtype_equivalence_sel_equ_rhs;
    eauto;
    intros;
    edestruct H as [Ha Hb];
    eauto;
    eapply Ha;
    eauto.

  (* sel nom *)
  (* <: *)
  eapply subtype_equivalence_sel_nom_lhs;
    eauto;
    intros;
    edestruct H as [Ha Hb];
    eauto;
    eapply Ha;
    eauto.

  (* >: *)
  eapply subtype_equivalence_sel_nom_rhs;
    eauto.

  (* top rfn *)
  (* <: *)
  apply subtype_equivalence_rfn_top_lhs
    with (T2:=T2)(Ts1:=Ts);
    auto;
    intros.
  edestruct H
    with
      (G2:=(top str ss2 rts)::G2)
      (ss2:=[c_ (length G2) /ss 0]ss2)
      (T2:=Ts2)
    as [Ha Hb];
    eauto.
  inversion H3;
    subst;
    auto.
  eapply Ha;
    auto.
  apply is_material_ss_subst;
    inversion H4;
    auto.

  (* >: *)
  eapply subtype_equivalence_rfn_top_rhs;
    eauto;
    intros.
  edestruct H
    with
      (G2:=(top str ss1 rts)::G2)
      (ss2:=[c_ (length G2) /ss 0]ss1)
      (T2:=Ts1)
    as [Ha Hb];
    eauto.
  inversion H3;
    auto.
  apply Hb;
    eauto.
  repeat mat_auto.

  (* sel rfn *)
  (* <: *)
  eapply subtype_equivalence_rfn_sel_lhs;
    intros;
    eauto.
  edestruct H
    with
      (G2:=(sel x L str ss2 rts)::G2)
      (ss2:=[c_ (length G2) /ss 0]ss2)
      (T2:=Ts2)
    as [Ha Hb];
    eauto.
  inversion H4;
    subst;
    auto.
  eapply Ha;
    auto.
  apply is_material_ss_subst;
    repeat mat_auto;
    auto.
  edestruct H0
    with
      (G2:=G2)
      (t2:=t2')
      (T2:=T2')
    as [Ha Hb];
    eauto.

  (* >: *)
  eapply subtype_equivalence_rfn_sel_rhs;
    intros;
    eauto.
  edestruct H
    with
      (G2:=(sel x L str ss1 rts)::G2)
      (ss2:=[c_ (length G2) /ss 0]ss1)
      (T2:=Ts1)
    as [Ha Hb];
    eauto.
  inversion H4;
    subst;
    auto.
  eapply Hb;
    auto.
  repeat mat_auto.

  (* sha sel 1 *)
  (* <: *)
  eapply subtype_equivalence_sha_sel_lhs;
    eauto;
    intros.
  edestruct H;
    eauto.

  (* all *)
  (* <: *)
  eapply subtype_equivalence_all_lhs;
    eauto;
    intros;
    split;
    eauto;
    intros.
  edestruct H
    with
      (G2:=G2)
      (t2:=ta2)
      (T2:=Ta2)
    as [Ha Hb];
    eauto;
    inversion H4;
    auto.
  edestruct H0
    with
      (G2:=ta2::G2)
      (t2:=[c_ (length G2) /t 0]tb2)
      (T2:=Tb2)
    as [Ha Hb];
    eauto;
    [inversion H4; subst; auto|].
  apply Ha;
    repeat mat_auto;
    auto.

  (* >: *)
  eapply subtype_equivalence_all_rhs;
    eauto;
    intros;
    split;
    eauto;
    intros.
  edestruct H
    with
      (G2:=G2)
      (t2:=ta1)
      (T2:=Ta1)
    as [Ha Hb];
    eauto;
    inversion H4;
    auto.
  edestruct H0
    with
      (G2:=ta1::G2)
      (t2:=[c_ (length G2) /t 0]tb1)
      (T2:=Tb1)
    as [Ha Hb];
    eauto;
    [inversion H4; subst; auto|].
  apply Hb;
    repeat mat_auto;
    auto.

  (* upp *)
  (* <: *)
  subtype_reduce;
    destruct T2;
    try solve [inversion H2];
    inversion H0;
    subst.

  bool_auto; eq_auto; mat_auto.
  apply s_upper_d; eapply H; eauto.

  (* >: *)
  destruct T2;
    try solve [subtype_reduce; inversion H2];
    inversion H0;
    subst.
  
  subtype_reduce;
    bool_auto;
    eq_auto;
    mat_auto.
  apply s_upper_d; eapply H; eauto.
  
  subtype_reduce;
    bool_auto;
    eq_auto;
    mat_auto.
  apply s_up_eq_d; eapply H; eauto.

  erewrite subtype_nom_reduce in H2;
    eauto;
    bool_auto;
    eq_auto;
    mat_auto.
  apply s_up_no_d; eapply H; eauto.

  (* low *)
  (* <: *)
  subtype_reduce;
    destruct T2;
    try solve [inversion H2];
    inversion H0;
    subst.

  bool_auto; eq_auto; mat_auto.
  apply s_lower_d; eapply H; eauto.

  (* >: *)
  destruct T2;
    try solve [subtype_reduce; inversion H2];
    inversion H0;
    subst.
  
  subtype_reduce;
    bool_auto;
    eq_auto;
    mat_auto.
  apply s_lower_d; eapply H; eauto.
  
  subtype_reduce;
    bool_auto;
    eq_auto;
    mat_auto.
  apply s_lo_eq_d; eapply H; eauto.

  erewrite subtype_nom_reduce in H2;
    eauto;
    bool_auto.

  (* equ *)
  (* <: *)
  subtype_reduce;
    destruct T2;
    try solve [inversion H2];
    inversion H0;
    subst.

  bool_auto; eq_auto; mat_auto.
  apply s_up_eq_d; eapply H; eauto.

  bool_auto; eq_auto; mat_auto.
  apply s_lo_eq_d; eapply H; eauto.

  bool_auto; eq_auto; mat_auto.
  apply s_equal_d; eapply H; eauto.

  (* >: *)
  destruct T2;
    try solve [subtype_reduce; inversion H2];
    inversion H0;
    subst.
  
  subtype_reduce;
    bool_auto;
    eq_auto;
    mat_auto.
  apply s_equal_d; eapply H; eauto.

  erewrite subtype_nom_reduce in H2;
    eauto;
    bool_auto.

  (* upp *)
  (* <: *)
  erewrite subtype_nom_reduce in H2;
    eauto;
    destruct T2;
    try solve [inversion H2];
    inversion H0;
    subst.

  bool_auto; eq_auto; mat_auto.
  apply s_up_no_d; eapply H; eauto.

  bool_auto; eq_auto; mat_auto.
  apply beq_ty_eq in H3; subst;
    apply s_nomin_d; eapply H; eauto.

  (* >: *)
  destruct T2;
    try solve [subtype_reduce; inversion H2];
    inversion H0;
    subst.
  
  erewrite subtype_nom_reduce in H2;
    eauto;
    bool_auto;
    eq_auto;
    mat_auto.
  apply beq_ty_eq in H3; subst;
    apply s_nomin_d; eapply H; eauto.

  (* nil *)
  subtype_reduce;
    destruct T2;
    bool_auto.
  inversion H;
    auto.

  (* con *)
  (* <: *)
  subtype_reduce;
    inversion H1;
    subst;
    auto;
    bool_auto;
    mat_auto.
  apply s_con.
  destruct H
      with
        (G2:=G2)
        (s2:=s0)
        (T2:=T0);
    eauto.
  destruct H0
      with
        (G2:=G2)
        (ss2:=ss0)
        (T2:=Ts0);
    eauto.
  
  (* >: *)
  inversion H1;
    subst;
    auto;
    subtype_reduce;
    bool_auto;
    mat_auto.
  apply s_con.
  destruct H
      with
        (G2:=G2)
        (s2:=s0)
        (T2:=T0);
    eauto.
  destruct H0
      with
        (G2:=G2)
        (ss2:=ss0)
        (T2:=Ts0);
    eauto.
Qed.
