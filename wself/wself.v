Require Export List.
Require Export Bool.
Require Export Arith.
Require Export Peano_dec.
Require Export Coq.Arith.PeanoNat.
Require Export Coq.Arith.EqNat.
Require Import CpdtTactics.
Require Export Coq.Program.Wf.
Require Export Coq.Program.Tactics.
Require Export Coq.Logic.FunctionalExtensionality.
Require Export Recdef.
Require Import wyv_common.
Set Implicit Arguments.

Inductive closed : ty -> nat -> Prop :=
| cl_top : forall n, closed top n
| cl_bot : forall n, closed bot n
                       
| cl_sel : forall x L n, x <> (a_ n) ->
                    closed (sel x L) n
                       
| cl_all : forall t1 t2 n, closed t1 n ->
                      closed t2 (S n) ->
                      closed (all t1 ∙ t2) n
                       
| cl_rfn : forall t ss n, closed t n ->
                     closed_ss ss (S n) ->
                     closed (t str ss rts) n

with
closed_s : decl -> nat -> Prop :=
| cl_low : forall L t n, closed t n ->
                    closed_s (type L ⩾ t) n
                       
| cl_upp : forall L t n, closed t n ->
                    closed_s (type L ⩽ t) n
                             
| cl_equ : forall L t n, closed t n ->
                    closed_s (type L ≝ t) n
                       
| cl_nom  :forall L t n, closed t n ->
                    closed_s (type L ⪯ t) n

with
closed_ss : decls -> nat -> Prop :=
| cl_nil : forall n, closed_ss d_nil n

| cl_con : forall s ss n, closed_s s n ->
                     closed_ss ss n ->
                     closed_ss (d_con s ss) n.

Hint Constructors closed closed_s closed_ss.

Scheme cl_mut_ind := Induction for closed Sort Prop
  with cl_s_mut_ind := Induction for closed_s Sort Prop
  with cl_ss_mut_ind := Induction for closed_ss Sort Prop.

Combined Scheme closed_mutind from cl_mut_ind, cl_s_mut_ind, cl_ss_mut_ind.

Reserved Notation "G '⊢' t1 '<;' t2" (at level 80).
Reserved Notation "G '⊢' d1 '<;;' d2" (at level 80).
Reserved Notation "G '⊢' d1 '<;;;' d2" (at level 80).
(*Reserved Notation "G1 '⊢' t1 '>;' t2 'dashv' G2" (at level 80).
Reserved Notation "G1 '⊢' d1 '>;;' d2 'dashv' G2" (at level 80).*)

Inductive is_material : ty -> Prop :=
| m_top : is_material top
| m_bot : is_material bot
| m_rfn_top : forall ss,is_material_ss ss ->
                   closed_ss ss 0 ->
                   is_material (top str ss rts)
| m_rfn_sel : forall x l ss, is_material (sel x l) ->
                        is_material_ss ss ->
                        closed_ss ss 0 ->
                        is_material ((sel x l) str ss rts)
                              
| m_sel : forall p M, is_material (sel p (Material M))
| m_all : forall t1 t2, is_material t1 ->
                   is_material t2 ->
                   is_material (all t1 ∙ t2)

with
is_material_s : decl -> Prop :=
| m_upp : forall L t, is_material t ->
                 is_material_s (type L ⩽ t)
| m_low : forall L t, is_material t ->
                 is_material_s (type L ⩾ t)
| m_equ : forall L t, is_material t ->
                 is_material_s (type L ≝ t)
| m_nom : forall L t, is_material t ->
                 is_material_s (type L ⪯ t)

with
is_material_ss : decls -> Prop :=
| m_nil : is_material_ss d_nil
| m_con : forall s ss, is_material_s s ->
                  is_material_ss ss ->
                  is_material_ss (d_con s ss).

Hint Constructors is_material is_material_s is_material_ss.

Scheme mat_mut_ind := Induction for is_material Sort Prop
  with mat_s_mut_ind := Induction for is_material_s Sort Prop
  with mat_ss_mut_ind := Induction for is_material_ss Sort Prop.

Combined Scheme is_material_mutind from mat_mut_ind, mat_s_mut_ind, mat_ss_mut_ind.

Inductive is_shape : ty -> Prop :=
| sh_sel : forall x S, is_shape (sel x (Shape S))

| sh_rfn : forall x l ss, is_shape (sel x l) ->
                     is_shape ((sel x l) str ss rts).

Inductive is_struct : ty -> Prop :=
| str_top : is_struct top
| str_rfn : forall t ss, is_struct t ->
                    is_struct (t str ss rts).

Reserved Notation "Γ '⊢' t1 '≤⦂⦂' t2" (at level 80).

Inductive extends : env -> ty -> ty -> Prop :=
| e_upper : forall Γ x L t, Γ ⊢ x ∋ (type L ⩽ t) ->
                       (is_shape (sel x L) -> is_shape t) ->
                       Γ ⊢ (sel x L) ≤⦂⦂ t
                         
| e_equal : forall Γ x L t, Γ ⊢ x ∋ (type L ≝ t) ->
                       (is_shape (sel x L) -> is_shape t) ->
                       Γ ⊢ (sel x L) ≤⦂⦂ t
                         
| e_nomin : forall Γ x L t, Γ ⊢ x ∋ (type L ⪯ t) ->
                       (is_shape (sel x L) -> is_shape t) ->
                       Γ ⊢ (sel x L) ≤⦂⦂ t
                         
| e_refn : forall Γ t t' ss t'', Γ ⊢ t ≤⦂⦂ t' ->
                            flat t' ss = Some t'' ->
                            Γ ⊢ t str ss rts ≤⦂⦂ t''
                                                
where "Γ '⊢' t1 '≤⦂⦂' t2" := (extends Γ t1 t2).

Hint Constructors extends.


Inductive sub_t : env -> ty -> ty -> Prop :=
| s_top : forall Γ t, Γ ⊢ t <; top
| s_bot : forall Γ t, Γ ⊢ bot <; t
| s_refl : forall Γ x l, Γ ⊢ (sel x l) <; (sel x l)
                           
| s_lower_1 : forall Γ x l t1 t2, Γ ⊢ x ∋ (type l ⩾ t2) ->
                             Γ ⊢ t1 <; t2 ->
                             Γ ⊢ t1 <; (sel x l)
                               
| s_lower_2 : forall Γ x l t1 t2, Γ ⊢ x ∋ (type l ≝ t2) ->
                             Γ ⊢ t1 <; t2 ->
                             Γ ⊢ t1 <; (sel x l)
                               
| s_upper_1 : forall Γ x l t1 t2, Γ ⊢ x ∋ (type l ⩽ t1) ->
                             Γ ⊢ t1 <; t2 ->
                             Γ ⊢ (sel x l) <; t2
                               
| s_upper_2 : forall Γ x l t1 t2, Γ ⊢ x ∋ (type l ≝ t1) ->
                             Γ ⊢ t1 <; t2 ->
                             Γ ⊢ (sel x l) <; t2
                               
| s_upper_3 : forall Γ x l t1 t2, Γ ⊢ x ∋ (type l ⪯ t1) ->
                             Γ ⊢ t1 <; t2 ->
                             Γ ⊢ (sel x l) <; t2

| s_all : forall Γ t t1 t2, (t::Γ) ⊢ ([c_ (length Γ) /t 0]t1) <; ([c_ (length Γ) /t 0]t2) ->
                       Γ ⊢ all t ∙ t1 <; all t ∙ t2

| s_refine : forall Γ t ss1 ss2, ((t str ss1 rts)::Γ) ⊢ ([c_ (length Γ) /ss 0]ss1) <;;; ([c_ (length Γ) /ss 0]ss2) ->
                            Γ ⊢ (t str ss1 rts) <; (t str ss2 rts)

| s_extend : forall Γ t1 t t2, Γ ⊢ t1 ≤⦂⦂ t ->
                          Γ ⊢ t <; t2 ->
                          Γ ⊢ t1 <; t2
       
where "Γ '⊢' t1 '<;' t2" := (sub_t Γ t1 t2)

with
sub_s : env -> decl -> decl -> Prop :=
| s_lower_d : forall Γ l t1 t2, Γ ⊢ t2 <; t1 ->
                           Γ ⊢ (type l ⩾ t1) <;; (type l ⩾ t2) 
                                  
| s_upper_d : forall Γ l t1 t2, Γ ⊢ t1 <; t2 ->
                           Γ ⊢ (type l ⩽ t1) <;; (type l ⩽ t2) 
                                  
| s_lo_eq_d : forall Γ l t1 t2, Γ ⊢ t2 <; t1 ->
                           Γ ⊢ (type l ≝ t1) <;; (type l ⩾ t2) 
                                  
| s_up_eq_d : forall Γ l t1 t2, Γ ⊢ t1 <; t2 ->
                           Γ ⊢ (type l ≝ t1) <;; (type l ⩽ t2)
                                   
| s_equal_d : forall Γ l t1 t2, Γ ⊢ t1 <; t2 ->
                           Γ ⊢ t2 <; t1 ->
                           Γ ⊢ (type l ≝ t1) <;; (type l ≝ t2)
                                   
| s_up_no_d : forall Γ l t1 t2, Γ ⊢ t1 <; t2 ->
                           Γ ⊢ (type l ⪯ t1) <;; (type l ⩽ t2)
                                   
| s_nomin_d : forall Γ l t, Γ ⊢ (type l ⪯ t) <;; (type l ⪯ t)

where "Γ '⊢' s1 '<;;' s2" := (sub_s Γ s1 s2)

with
sub_ss : env -> decls -> decls -> Prop :=
| s_nil : forall Γ ss, Γ ⊢ ss <;;; d_nil 
| s_con : forall Γ s1 ss1 s2 ss2, Γ ⊢ s1 <;; s2 ->
                             Γ ⊢ ss1 <;;; ss2 ->
                             Γ ⊢ (d_con s1 ss1) <;;; (d_con s2 ss2)

where "Γ '⊢' s1 '<;;;' s2" := (sub_ss Γ s1 s2).

Hint Constructors sub_t sub_s sub_ss.

Scheme sub_mut_ind := Induction for sub_t Sort Prop
  with sub_s_mut_ind := Induction for sub_s Sort Prop
  with sub_ss_mut_ind := Induction for sub_ss Sort Prop.

Combined Scheme subtype_mutind from sub_mut_ind, sub_s_mut_ind, sub_ss_mut_ind.

Lemma struct_is_not_shape :
  forall t, is_struct t ->
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

Lemma shape_is_not_struct :
  forall t, is_shape t ->
       ~is_struct t.
Proof.
  intros t H;
    induction H;
    subst;
    intros Hcontra;
    inversion Hcontra;
    subst;
    auto.
Qed.