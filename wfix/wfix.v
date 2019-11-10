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

Inductive is_material : ty -> Prop :=
| m_top : is_material top
| m_bot : is_material bot
| m_rfn : forall t ss, is_material t ->
                  is_material_ss ss ->
                  closed_ss ss 0 ->
                  is_material (refn t ss)
                              
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

| sh_rfn : forall t ss, is_shape t ->
                   is_shape (t str ss rts).

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


Reserved Notation "Γ1 '⊢' t1 '≤' t2 ⊣ Γ2" (at level 80).
Reserved Notation "Γ1 '⊢' d1 '≤;' d2 ⊣ Γ2" (at level 80).
Reserved Notation "Γ1 '⊢' d1 '≤;;' d2 ⊣ Γ2" (at level 80).
(*Reserved Notation "G1 '⊢' t1 '>;' t2 'dashv' G2" (at level 80).
Reserved Notation "G1 '⊢' d1 '>;;' d2 'dashv' G2" (at level 80).*)

Inductive sub_t : env -> ty -> ty -> env -> Prop :=
| s_top : forall Γ1 t Γ2, Γ1 ⊢ t ≤ top ⊣ Γ2
| s_bot : forall Γ1 t Γ2, Γ1 ⊢ bot ≤ t ⊣ Γ2
| s_refl : forall Γ1 Γ2 x l, Γ1 ⊢ (sel x l) ≤ (sel x l) ⊣ Γ2
                           
| s_lower_1 : forall Γ1 Γ2 x l t1 t2, Γ2 ⊢ x ∋ (type l ⩾ t2) ->
                                 Γ1 ⊢ t1 ≤ t2 ⊣ Γ2 ->
                                 Γ1 ⊢ t1 ≤ (sel x l) ⊣ Γ2
                                    
| s_lower_2 : forall Γ1 Γ2 x l t1 t2, Γ2 ⊢ x ∋ (type l ≝ t2) ->
                                 Γ1 ⊢ t1 ≤ t2 ⊣ Γ2 ->
                                 Γ1 ⊢ t1 ≤ (sel x l) ⊣ Γ2
                                    
| s_upper_1 : forall Γ1 Γ2 x l t1 t2, Γ1 ⊢ x ∋ (type l ⩽ t1) ->
                                 Γ1 ⊢ t1 ≤ t2 ⊣ Γ2 ->
                                 Γ1 ⊢ (sel x l) ≤ t2 ⊣ Γ2
                                    
| s_upper_2 : forall Γ1 Γ2 x l t1 t2, Γ1 ⊢ x ∋ (type l ≝ t1) ->
                                 Γ1 ⊢ t1 ≤ t2 ⊣ Γ2 ->
                                 Γ1 ⊢ (sel x l) ≤ t2 ⊣ Γ2
                                    
| s_upper_3 : forall Γ1 Γ2 x l t1 t2, Γ1 ⊢ x ∋ (type l ⪯ t1) ->
                                 Γ1 ⊢ t1 ≤ t2 ⊣ Γ2 ->
                                 Γ1 ⊢ (sel x l) ≤ t2 ⊣ Γ2

| s_all : forall Γ1 Γ2 t1 t2 t1' t2', Γ2 ⊢ t2 ≤ t1 ⊣ Γ1 ->
                                 (t1::Γ1) ⊢ ([c_ (length Γ1) /t 0]t1') ≤ ([c_ (length Γ2) /t 0]t2') ⊣ (t2::Γ2) ->
                                 Γ1 ⊢ all t1 ∙ t1' ≤ all t2 ∙ t2' ⊣ Γ2

| s_refine : forall Γ1 Γ2 t ss1 ss2, ((t str ss1 rts)::Γ1) ⊢ ([c_ (length Γ1) /ss 0]ss1) ≤;; ([c_ (length Γ2) /ss 0]ss2) ⊣ ((t str ss2 rts)::Γ2) ->
                                Γ1 ⊢ (t str ss1 rts) ≤ (t str ss2 rts) ⊣ Γ2

| s_extend : forall Γ1 Γ2 t1 t t2, Γ1 ⊢ t1 ≤⦂⦂ t ->
                              Γ1 ⊢ t ≤ t2 ⊣ Γ2 ->
                              Γ1 ⊢ t1 ≤ t2 ⊣ Γ2
                                 
where "Γ1 '⊢' t1 '≤' t2 ⊣ Γ2" := (sub_t Γ1 t1 t2 Γ2)

with
sub_s : env -> decl -> decl -> env -> Prop :=
| s_lower_d : forall Γ1 Γ2 l t1 t2, Γ2 ⊢ t2 ≤ t1 ⊣ Γ1 ->
                               Γ1 ⊢ (type l ⩾ t1) ≤; (type l ⩾ t2) ⊣ Γ2
                                  
| s_upper_d : forall Γ1 Γ2 l t1 t2, Γ1 ⊢ t1 ≤ t2 ⊣ Γ2 ->
                               Γ1 ⊢ (type l ⩽ t1) ≤; (type l ⩽ t2) ⊣ Γ2
                                  
| s_lo_eq_d : forall Γ1 Γ2 l t1 t2, Γ2 ⊢ t2 ≤ t1 ⊣ Γ1 ->
                               Γ1 ⊢ (type l ≝ t1) ≤; (type l ⩾ t2) ⊣ Γ2 
                                  
| s_up_eq_d : forall Γ1 Γ2 l t1 t2, Γ1 ⊢ t1 ≤ t2 ⊣ Γ2 ->
                               Γ1 ⊢ (type l ≝ t1) ≤; (type l ⩽ t2) ⊣ Γ2
                                  
| s_equal_d : forall Γ1 Γ2 l t1 t2, Γ1 ⊢ t1 ≤ t2 ⊣ Γ2 ->
                               Γ2 ⊢ t2 ≤ t1 ⊣ Γ1 ->
                               Γ1 ⊢ (type l ≝ t1) ≤; (type l ≝ t2) ⊣ Γ2
                                  
| s_up_no_d : forall Γ1 Γ2 l t1 t2, Γ1 ⊢ t1 ≤ t2 ⊣ Γ2 ->
                               Γ1 ⊢ (type l ⪯ t1) ≤; (type l ⩽ t2) ⊣ Γ2
                                  
| s_nomin_d : forall Γ1 Γ2 l t, Γ1 ⊢ (type l ⪯ t) ≤; (type l ⪯ t) ⊣ Γ2

where "Γ1 '⊢' s1 '≤;' s2 '⊣' Γ2" := (sub_s Γ1 s1 s2 Γ2)

with
sub_ss : env -> decls -> decls -> env -> Prop :=
| s_nil : forall Γ1 Γ2 ss, Γ1 ⊢ ss ≤;; d_nil ⊣ Γ2
| s_con : forall Γ1 Γ2 s1 ss1 s2 ss2, Γ1 ⊢ s1 ≤; s2 ⊣ Γ2 ->
                                 Γ1 ⊢ ss1 ≤;; ss2 ⊣ Γ2 ->
                                 Γ1 ⊢ (d_con s1 ss1) ≤;; (d_con s2 ss2) ⊣ Γ2

where "Γ1 '⊢' s1 '≤;;' s2 '⊣' Γ2" := (sub_ss Γ1 s1 s2 Γ2).

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