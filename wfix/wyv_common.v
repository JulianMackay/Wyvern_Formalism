Require Export List.
Require Export Bool.
Require Export Arith.
Require Export Peano_dec.
Require Export Coq.Arith.PeanoNat.
Require Export Coq.Arith.EqNat.
Require Export Coq.Program.Wf.
Require Export Coq.Program.Tactics.
Require Export Coq.Logic.FunctionalExtensionality.
Require Export Recdef.

Require Import common.CpdtTactics.

Set Implicit Arguments.

Inductive var : Type :=
| c_  : nat -> var  (*concrete variables*)
| a_ : nat -> var. (*abstract variables*)

Inductive label :=
| Material : nat -> label
| Shape : nat -> label.

Inductive ty : Type := (*types*)
| refn : ty -> decls -> ty
| sel  : var -> label -> ty
| all : ty -> ty -> ty
| top    : ty
| bot    : ty
           
with
decl : Type := (*declarations*)
| d_upper : label -> ty -> decl
| d_lower : label -> ty -> decl
| d_equal : label -> ty -> decl
| d_nominal : label -> ty -> decl

with
decls : Type := (*list of declarations*)
| d_nil : decls
| d_con : decl -> decls -> decls.

Notation "t 'str' ss 'rts'" := (refn t ss) (at level 80).
Notation "'all' t1 '∙' t2" := (all t1 t2) (at level 80). 
Notation "'type' l '⩾' t" := (d_lower l t) (at level 80).
Notation "'type' l '⩽' t" := (d_upper l t) (at level 80). 
Notation "'type' l '≝' t" := (d_equal l t) (at level 80).
Notation "'type' l '⪯' t" := (d_nominal l t) (at level 80).

Scheme type_mut_ind := Induction for ty Sort Prop
  with decl_mut_ind := Induction for decl Sort Prop.

Combined Scheme type_mutind from type_mut_ind, decl_mut_ind(*, path_mut_ind*).
  

Definition id (d : decl) : label :=
  match d with
  | type l ⩾ _ => l
  | type l ⩽ _ => l
  | type l ⪯ _ => l
  | type l ≝ _ => l
  end.

Definition env := list ty.

Definition eq_label (l1 l2 : label) : bool :=
  match l1, l2 with
  | Material n, Material m => n =? m
  | Shape n, Shape m => n =? m
  | _, _ => false
  end.

Definition eq_var (x y : var) : bool :=
  match x, y with
  | c_ n, c_ m => n =? m
  | a_ n, a_ m => n =? m
  | _, _ => false
  end.

Reserved Notation "'[' p '/t' n ']' t" (at level 80).
Reserved Notation "'[' p '/s' n ']' d" (at level 80).
Reserved Notation "'[' p '/ss' n ']' d" (at level 80).
Reserved Notation "'[' p '/v' n ']' v" (at level 80).
(*  Reserved Notation "'[' p1 '/p' n ']' p2" (at level 80).*)

(*subst*)

Fixpoint subst_v (v1 : var)(n : nat)(v2 : var) : var :=
  match v1 with
  | a_ m => if n =? m
            then v2
            else v1
  | _ => v1
  end.

Notation "'[' v1 '/v' n ']' v2" := (subst_v v2 n v1).

Fixpoint subst (n : nat) (x : var) (t : ty) : ty :=
  match t with
  | top => top
  | bot => bot
  | sel y l => sel ([ x /v n ] y) l
  | t str ss rts  => ([x /t n]t) str ([ x /ss S n ] ss) rts
  | all t1 ∙ t2 => all ([x /t n] t1) ∙ ([x /t S n] t2)
  end

where "'[' x '/t' n ']' t" := (subst n x t)

with
subst_s (n : nat) (x : var) (s : decl) : decl :=
  match s with
  | type l ⩾ t => type l ⩾ ([x /t n] t)
  | type l ⩽ t => type l ⩽ ([x /t n] t)
  | type l ≝ t => type l ≝ ([x /t n] t)
  | type l ⪯ t => type l ⪯ ([x /t n] t)
  end
    
where "'[' x '/s' n ']' d" := (subst_s n x d)

with
subst_ss (n : nat) (x : var) (s : decls) : decls :=
  match s with
  | d_nil => d_nil
  | d_con s ss => d_con ([x /s n]s) ([x /ss n]ss)
  end
    
where "'[' x '/ss' n ']' d" := (subst_ss n x d).


Fixpoint get {A : Type} (n : nat) (l : list A) : option A :=
  match n with
  | O => match l with
        | nil => None
        | h::t => Some h
        end
  | S m => match l with
          | nil => None
          | h::t => get m t
          end
  end.

Definition mapping {A : Type}(n : nat)(l : list A) : option A :=
  get n (rev l).

Notation "n '↦' t 'elem' Γ" := (mapping n Γ = Some t)(at level 80).

Reserved Notation "Γ '⊢' p '⦂' t" (at level 80).

Inductive typing : env -> var -> ty -> Prop :=
| t_var : forall Γ n t, n ↦ t elem Γ ->
                   Γ ⊢ (c_ n) ⦂ t

where "Γ '⊢' p '⦂' t" := (typing Γ p t).

Reserved Notation "G '⊢' p '∋' d" (at level 80).
Reserved Notation "G '⊢' d '∈' t" (at level 80).

Hint Constructors typing.

Inductive in_ss : decl -> decls -> Prop :=
| in_head_ss : forall s ss, in_ss s (d_con s ss)
| in_tail_ss : forall s s' ss, in_ss s ss ->
                          in_ss s (d_con s' ss).

Hint Constructors in_ss.

Inductive has : env -> var -> decl -> Prop :=
| h_path : forall Γ p s t, Γ ⊢ p ⦂ t ->
                      Γ ⊢ s ∈ t ->
                      Γ ⊢ p ∋ ([ p /s 0] s)
where "Γ '⊢' p '∋' s" := (has Γ p s)

with
contains : env -> ty -> decl -> Prop :=
| c_rfn1 : forall Γ t s ss, in_ss s ss ->
                       Γ ⊢ s ∈ (t str ss rts)
                         
| c_rfn2 : forall Γ t s ss, Γ ⊢ s ∈ t ->
                       (forall s', in_ss s ss ->
                              id s <> id s') ->
                       Γ ⊢ s ∈ (t str ss rts)
                         
| c_upp : forall Γ x L t d, Γ ⊢ x ∋ (type L ⩽ t) ->
                       Γ ⊢ d ∈ t ->
                       Γ ⊢ d ∈ (sel x L)
                         
| c_equ : forall Γ x L t s, Γ ⊢ x ∋ (type L ≝ t) ->
                       Γ ⊢ s ∈ t ->
                       Γ ⊢ s ∈ (sel x L)
                         
| c_nom : forall Γ x L t s, Γ ⊢ x ∋ (type L ⪯ t) ->
                       Γ ⊢ s ∈ t ->
                       Γ ⊢ s ∈ (sel x L)
                           
(*| c_refined : forall Γ x L y L' ss s, Γ ⊢ x ∋ (type L refines y dot L' br ss rb) ->
                                 Γ ⊢ s ∈ ((sel y L')str ss rts) ->
                                 Γ ⊢ s ∈(sel x L)*)
                                                
where "Γ '⊢' d '∈' t" := (contains Γ t d). 

Hint Constructors has contains.

Scheme has_mut_ind := Induction for has Sort Prop
  with contains_mut_ind := Induction for contains Sort Prop.

Combined Scheme has_contains_mutind from has_mut_ind, contains_mut_ind.

Fixpoint in_ds (l : label)(ss : decls) : bool :=
  match ss with 
  | d_nil => false
  | d_con s ss' => orb (eq_label l (id s)) (in_ds l ss')
  end.

Fixpoint merge (ss1 ss2 : decls) : decls :=
  match ss1 with
  | d_nil => ss2
  | d_con s ss => if (in_ds (id s) (ss2))
                 then merge ss ss2
                 else d_con s (merge ss ss2)
  end.

Fixpoint flat (t : ty)(ss : decls) : option ty :=
  match t with
  | top => Some (top str ss rts)
  | bot => None
  | sel x L => Some ((sel x L) str ss rts)
  | t' str ss' rts => Some (t' str merge ss ss' rts)
  | all _ ∙ _ => None
  end.

Reserved Notation "G '⊢' d 'ext' t" (at level 80).


Reserved Notation "n 'notin_t' t" (at level 80).
Reserved Notation "n 'notin_s' s" (at level 80).
Reserved Notation "n 'notin_ss' ss" (at level 80).
Reserved Notation "n 'notin_v' p" (at level 80).
(*  Reserved Notation "n 'notin_p' p" (at level 80).*)

Inductive notin_var : nat -> var -> Prop :=
| ni_abstract : forall n m, n notin_v (a_ m)
| ni_concrete : forall n m, n <> m ->
                       n notin_v (c_ m)

where "n 'notin_v' v" := (notin_var n v).

Inductive notin_ty : nat -> ty -> Prop :=
| ni_top : forall n, n notin_t top
| ni_bot : forall n, n notin_t bot
| ni_sel : forall n p l, n notin_v p ->
                    n notin_t (sel p l)
| ni_rfn : forall n t ss, n notin_t t ->
                     n notin_ss ss ->
                     n notin_t (t str ss rts)
| ni_all : forall n t t', n notin_t t ->
                     n notin_t t' ->
                     n notin_t (all t ∙ t')
where "n 'notin_t' t" := (notin_ty n t)

with
notin_decl : nat -> decl -> Prop :=
| ni_lower : forall n l t, n notin_t t ->
                      n notin_s (type l ⩾ t)
                        
| ni_upper : forall n l t, n notin_t t ->
                      n notin_s (type l ⩽ t)
                        
| ni_equal : forall n l t, n notin_t t ->
                      n notin_s (type l ≝ t)
                        
| ni_nom : forall n l t, n notin_t t ->
                    n notin_s (type l ⪯ t)
                        
(*| ni_refine : forall n L y L' ss, n notin_v y ->
                             n notin_ss ss ->
                             n notin_s (type L refines y dot L' br ss rb)*)
where "n 'notin_s' s" := (notin_decl n s)

with
notin_decls : nat -> decls -> Prop :=
| ni_nil : forall n, n notin_ss d_nil
| ni_con : forall n s ss, n notin_s s ->
                     n notin_ss ss ->
                     n notin_ss (d_con s ss)
where "n 'notin_ss' ss" := (notin_decls n ss).

Hint Constructors notin_ty notin_decl notin_decls notin_var.

Scheme notin_ty_mutind := Induction for notin_ty Sort Prop
  with notin_decl_mutind := Induction for notin_decl Sort Prop
  with notin_decls_mutind := Induction for notin_decls Sort Prop.

Combined Scheme notin_mutind from notin_ty_mutind, notin_decl_mutind, notin_decls_mutind.

Reserved Notation "n 'notin_env' G" (at level 80).

Inductive notin_environment : nat -> env -> Prop :=
| nie_nil : forall n, n notin_env nil
| nie_cons : forall n Γ t, n notin_t t ->
                     n notin_env Γ ->
                     n notin_env (t::Γ)
where "n 'notin_env' Γ" := (notin_environment n Γ).

Reserved Notation "Γ '⊢' t 'wf_t'" (at level 80).
Reserved Notation "Γ '⊢' s 'wf_s'" (at level 80).
Reserved Notation "Γ '⊢' ss 'wf_ss'" (at level 80).
Reserved Notation "Γ '⊢' p 'wf_v'" (at level 80).

Inductive wf_var : env -> var -> Prop :=
| wf_concrete : forall Γ r, r < length Γ ->
                       Γ ⊢ c_ r wf_v

where "Γ '⊢' v 'wf_v'" := (wf_var Γ v).

Inductive wf_ty : env -> ty -> Prop := 
| wf_top : forall Γ, Γ ⊢ top wf_t
| wf_bot : forall Γ, Γ ⊢ bot wf_t
| wf_sel_lower : forall Γ p l t, Γ ⊢ p ∋ (type l ⩾ t) ->
                            Γ ⊢ p wf_v ->
                            Γ ⊢ (sel p l) wf_t
| wf_sel_upper : forall Γ p l t, Γ ⊢ p ∋ (type l ⩽ t) ->
                            Γ ⊢ p wf_v ->
                            Γ ⊢ (sel p l) wf_t
| wf_refn : forall Γ t ss, Γ ⊢ t wf_t ->
                      (t str ss rts)::Γ ⊢ ([ c_ (length Γ) /ss 0] ss) wf_ss ->
                      (length Γ) notin_ss ss ->
                      Γ ⊢ (t str ss rts) wf_t

where "Γ '⊢' t 'wf_t'" := (wf_ty Γ t)

with
wf_decl : env -> decl -> Prop :=
| wf_lower : forall Γ l t, Γ ⊢ t wf_t ->
                      Γ ⊢ (type l ⩾ t) wf_s
| wf_upper : forall Γ l t, Γ ⊢ t wf_t ->
                      Γ ⊢ (type l ⩽ t) wf_s
| wf_equal : forall Γ l t, Γ ⊢ t wf_t ->
                      Γ ⊢ (type l ≝ t) wf_s
(*| wf_refine : forall Γ l y l' ss, Γ ⊢ (sel y l') str ss rts wf_t ->
                             Γ ⊢ (type l refines y dot l' br ss rb) wf_s*)

where "Γ '⊢' d 'wf_s'" := (wf_decl Γ d)

with
wf_decls : env -> decls -> Prop :=
| wf_nil : forall Γ, Γ ⊢ d_nil wf_ss
| wf_con : forall Γ s ss, Γ ⊢ s wf_s ->
                     Γ ⊢ ss wf_ss ->
                     (forall s', in_ss s' ss ->
                            id s' <> id s) ->
                     Γ ⊢ (d_con s ss) wf_ss
                        
where "Γ '⊢' s 'wf_ss'" := (wf_decls Γ s).

Hint Constructors wf_ty wf_decl wf_decls wf_var.

Reserved Notation "G 'wf_e'" (at level 80).

Inductive wf_env : env -> Prop :=
| wfe_nil : nil wf_e
| wfe_cons : forall Γ t ss, Γ wf_e ->
                       Γ ⊢ (t str ss rts) wf_t ->
                       (t str ss rts)::Γ wf_e

where "G 'wf_e'" := (wf_env G).

Scheme wf_ty_mutind := Induction for wf_ty Sort Prop
  with wf_decl_mutind := Induction for wf_decl Sort Prop
  with wf_decls_mutind := Induction for wf_decls Sort Prop.

Combined Scheme wf_mutind from wf_ty_mutind, wf_decl_mutind, wf_decls_mutind.

Lemma eq_label_refl :
  forall l, eq_label l l = true.
Proof.
  intros;
    destruct l;
    simpl;
    rewrite <- beq_nat_refl;
    auto.
Qed.

Lemma eq_dec_label :
  forall l1 l2 : label, {l1 = l2} + {l1 <> l2}.
Proof.
  intros;
    destruct l1 as [m1|s1], l2 as [m2|s2].

  destruct (Nat.eq_dec m1 m2) as [Heq|Heq];
    [subst;
     left;
     auto
    |right;
     intro Hcontra;
     inversion Hcontra;
     crush].

  right;
    intros Hcontra;
    inversion Hcontra.

  right;
    intros Hcontra;
    inversion Hcontra.

  destruct (Nat.eq_dec s1 s2) as [Heq|Heq];
    [subst;
     left;
     auto
    |right;
     intro Hcontra;
     inversion Hcontra;
     crush].
Qed.

Lemma eq_label_neq :
  forall l1 l2, l1 <> l2 -> eq_label l1 l2 = false.
Proof.
  intros.

  destruct l1 as [m1|s1], l2 as [m2|s2];
    simpl;
    auto.
  
  destruct (Nat.eq_dec m1 m2) as [|Hneq];
    [subst;
     contradiction H;
     auto
    |rewrite Nat.eqb_neq;
     auto].
  
  destruct (Nat.eq_dec s1 s2) as [|Hneq];
    [subst;
     contradiction H;
     auto
    |rewrite Nat.eqb_neq;
     auto].
  
Qed.

Lemma neqb_label_neq :
  forall l1 l2, eq_label l1 l2 = false -> l1 <> l2.
Proof.
  intros.

  intro Hcontra;
    subst;
    rewrite eq_label_refl in H.
  inversion H.
Qed.

Lemma beq_label_eq :
  forall l1 l2, eq_label l1 l2 = true -> l1 = l2.
Proof.
  intros l1;
    destruct l1 as [|l1'];
    intros;
    destruct l2;
    simpl in H;
    try solve [inversion H];
    try solve [apply Nat.eqb_eq in H;
               subst;
               auto].
Qed.

Lemma eq_var_refl :
  forall x, eq_var x x = true.
Proof.
  intros;
    destruct x;
    simpl;
    rewrite <- beq_nat_refl;
    auto.
Qed.

Lemma eq_dec_var :
  forall x y : var, {x = y} + {x <> y}.
Proof.
  intros;
    destruct x as [n|n], y as [m|m].

  destruct (Nat.eq_dec n m) as [Heq|Heq];
    [subst;
     left;
     auto
    |right;
     intro Hcontra;
     inversion Hcontra;
     crush].

  right;
    intros Hcontra;
    inversion Hcontra.

  right;
    intros Hcontra;
    inversion Hcontra.

  destruct (Nat.eq_dec n m) as [Heq|Heq];
    [subst;
     left;
     auto
    |right;
     intro Hcontra;
     inversion Hcontra;
     crush].
Qed.

Lemma eq_var_neq :
  forall x y, x <> y -> eq_var x y = false.
Proof.
  intros.

  destruct x as [n|n], y as [m|m];
    simpl;
    auto.
  
  destruct (Nat.eq_dec n m) as [|Hneq];
    [subst;
     contradiction H;
     auto
    |rewrite Nat.eqb_neq;
     auto].
  
  destruct (Nat.eq_dec n m) as [|Hneq];
    [subst;
     contradiction H;
     auto
    |rewrite Nat.eqb_neq;
     auto].
  
Qed.

Lemma neqb_var_neq :
  forall x y, eq_var x y = false -> x <> y.
Proof.
  intros.

  intro Hcontra;
    subst;
    rewrite eq_var_refl in H.
  inversion H.
Qed.

Lemma beq_var_eq :
  forall x y, eq_var x y = true -> x = y.
Proof.
  intros x;
    destruct x as [n|n];
    intros;
    destruct y;
    simpl in H;
    try solve [inversion H];
    try solve [apply Nat.eqb_eq in H;
               subst;
               auto].
Qed.

Lemma eq_var_dec :
  forall x y, {eq_var x y = true} + {eq_var x y = false}.
Proof.
  intros.

  destruct x as [c1|a1], y as [c2|a2]; auto.

  destruct (eq_nat_dec c1 c2) as [Heq|Hneq];
    [subst; left; rewrite eq_var_refl; auto
    |rewrite eq_var_neq; crush].

  destruct (eq_nat_dec a1 a2) as [Heq|Hneq];
    [subst; left; rewrite eq_var_refl; auto
    |rewrite eq_var_neq; crush].
  
Qed.

Lemma eq_label_dec :
  forall l1 l2, {eq_label l1 l2 = true} + {eq_label l1 l2 = false}.
Proof.
  intros.

  destruct l1 as [m1|s1], l2 as [m2|s2]; auto.

  destruct (eq_nat_dec m1 m2) as [Heq|Hneq];
    [subst; left; rewrite eq_label_refl; auto
    |rewrite eq_label_neq; crush].

  destruct (eq_nat_dec s1 s2) as [Heq|Hneq];
    [subst; left; rewrite eq_label_refl; auto
    |rewrite eq_label_neq; crush].
  
Qed.

Parameter member_uniqueness :
  forall Γ x s1 s2, Γ ⊢ x ∋ s1 ->
               Γ ⊢ x ∋ s2 ->
               id s1 = id s2 ->
               s1 = s2.