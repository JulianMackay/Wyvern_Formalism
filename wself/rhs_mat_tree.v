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
Set Implicit Arguments.

(*
Here we model the case where an unseparated type on the left hand side, and
a pure material is on the the right hand side.

Here we know that following the syntax and the subtype semantics of Decidable 
Wyvern, every subsequent subtype check will feature a Material on the right 
hand side. We also know that if the left hand side is a shape, the only way 
to proceed 
would require a shape refinement on the right hand side. As we have already 
noted, this is not possible. Thus we can easily demonstrate termination as
without shapes, cycles are not possible on the right hand side, and the 
algorithm is thus bound by the finiteness of specified types.
 *)

Inductive tytree : Type :=
| t_top : tytree
| t_bot : tytree

| t_sel_upp : var -> label -> tytree -> tytree
| t_sel_low : var -> label -> tytree -> tytree
| t_sel_equ : var -> label -> tytree -> tytree
| t_sel_nom : var -> label -> tytree -> tytree
| t_sel_bnd : var -> label -> tytree

| t_rfn_top : tytree -> tytree                         (*first tytree is actually a list of trees constructed by t_nil and t_con*)
| t_rfn_sel : var -> label -> tytree -> tytree -> tytree  (*first tytree is actually a list of trees constructed by t_nil and t_con*)
| t_sha_top : var -> label -> decls -> tytree
| t_sha_sel : var -> label -> decls -> tytree -> tytree
| t_all : tytree -> tytree -> tytree

| t_upp : label -> tytree -> tytree
| t_low : label -> tytree -> tytree
| t_equ : label -> tytree -> tytree
| t_nom : label -> tytree -> tytree

| t_nil : tytree
| t_con : tytree -> tytree -> tytree.

Inductive Tree (A: Set): Set :=
| Leaf: A -> Tree A
| Node: list (Tree A) -> Tree A.

Fixpoint bind' {A B:Set} (k:A -> Tree B) (m:Tree A) : Tree B :=
  match m with
  | Leaf a => k a
  | Node ts => Node (map (bind' k) ts)
  end.

Definition bind (A B:Set) m (k:A -> Tree B) := bind' k m.

Fixpoint shape_depth (T : tytree) : nat :=
  match T with
  | t_sel_upp x L T' => 1 + shape_depth T'
  | t_sel_low x L T' => 1 + shape_depth T'
  | t_sel_equ x L T' => 1 + shape_depth T'
  | t_sel_nom x L T' => 1 + shape_depth T'
  | t_rfn_top Ts => 1 + shape_depth Ts
  | t_rfn_sel _ _ Ts T' => 1 + shape_depth Ts + shape_depth T'
  | t_sha_sel _ _ _ T' => 1 + shape_depth T'
  | t_all T1 T2 => 1 + shape_depth T1 + shape_depth T2
                                                   
  | t_upp _ T' => 1 + shape_depth T'
  | t_low _ T' => 1 + shape_depth T'
  | t_equ _ T' => 1 + shape_depth T'
  | t_nom _ T' => 1 + shape_depth T'

  | t_con T Ts => 1 + shape_depth T + shape_depth Ts
                                 
  | _ => 1
  end.

Definition shape_depth_p (P : tytree * tytree) := let (T1, T2) := P in shape_depth T1 + shape_depth T2.

Function zip (Ts1 Ts2 : list tytree) : option (list (tytree * tytree)) :=
  match Ts1, Ts2 with
  | _, nil => Some nil
  | T1::Ts1', T2::Ts2' => match zip Ts1' Ts2' with
                         | None => None
                         | Some Ps => Some ((T1, T2)::Ps)
                         end
  | nil, _::_ => None
  end.

Check fold_right andb true (map negb nil).
Compute fold_right andb true (map negb nil).

Fixpoint fold_mapb {A B : Type} (f : A * B -> bool) (Ps : list (A * B)) : bool :=
  match Ps with
  | nil => true
  | P::Ps' => andb (f P) (fold_mapb f Ps')
  end.

Definition zip_mapb {A B : Type} (f : A * B -> bool) (o : option (list (A * B))) : bool :=
  match o with 
  | None => false
  | Some Ps => fold_mapb f Ps
  end.

(*Definition map {A B} (xs : list A) (f : forall (x:A), In x xs -> B) : list B.
Proof.
  induction xs.
  exact nil.
  refine (f a _ :: IHxs _).
    - left. reflexivity.
    - intros. eapply f. right. eassumption.
Defined.*)

(*Fixpoint map {A B} (xs : list A) : forall (f : forall (x:A), In x xs -> B), list B :=
  match xs with
   | nil => fun _ => nil
   | x :: xs => fun f => f x (or_introl eq_refl) :: map xs (fun y h => f y (or_intror h))
  end.*)

(*forall P0 : tytree * tytree, shape_depth P0 < shape_depth P -> bool*)

Check in_cons.

Definition map_tree (P1 :  tytree * tytree)
           (f : forall P2 : tytree * tytree, shape_depth_p P2 < shape_depth_p P1 -> bool)
           (Ps : list (tytree * tytree))
           (lt : forall P2 : tytree * tytree, In P2 Ps -> shape_depth_p P2 < shape_depth_p P1) : list bool.
Proof.
  induction Ps.
  exact nil.
  assert (HIna : In a (a :: Ps));
    [apply in_eq|apply lt in HIna].
  refine (f a HIna :: IHPs _).
  intros. apply lt, in_cons; auto.
Defined.

(*Fixpoint map  (P1 :  tytree * tytree)
         (f : forall P2 : tytree * tytree, shape_depth P2 < shape_depth P1 -> bool)
         (Ps : list (tytree * tytree))
         (lt : forall P2 : tytree * tytree, In P2 Ps -> shape_depth P2 < shape_depth P1) : list bool :=
  match Ps with
  | nil => nil
  | P::Ps' => (f P lt)::(map P1 f Ps' lt)
  end.*)

Fixpoint eq_ty (t1 t2 : ty): bool :=
  match t1, t2 with
  | top, top => true
  | bot, bot => true
  | sel x1 L1 , sel x2 L2 => eq_var x1 x2 && eq_label L1 L2
  | t1 str ss1 rts, t2 str ss2 rts => eq_ty t1 t2 && eq_decls ss1 ss2
  | all t1 ∙ t1', all t2 ∙ t2' => eq_ty t1 t2 && eq_ty t1' t2'
  | _, _ => false
  end

with
eq_decl (s1 s2 : decl) : bool :=
  match s1, s2 with 
  | type L1 ⩽ t1, type L2 ⩽ t2 => eq_label L1 L2 && eq_ty t1 t2
  | type L1 ⩾ t1, type L2 ⩾ t2 => eq_label L1 L2 && eq_ty t1 t2
  | type L1 ≝ t1, type L2 ≝ t2 => eq_label L1 L2 && eq_ty t1 t2
  | type L1 ⪯ t1, type L2 ⪯ t2 => eq_label L1 L2 && eq_ty t1 t2
  | _, _ => false
  end

with
eq_decls (ss1 ss2 : decls) : bool :=
  match ss1, ss2 with
  | d_nil, d_nil => true
  | d_con s1 ss1, d_con s2 ss2 => eq_decl s1 s2 && eq_decls ss1 ss2
  | _, _ => false
  end.

Fixpoint eq_tree (T1 T2 : tytree) : bool :=
  match T1, T2 with
  | t_top, t_top => true
              
  | t_bot, t_bot => true
              
  | t_sel_upp x1 L1 T1', t_sel_upp x2 L2 T2' => (eq_var x1 x2) && (eq_label L1 L2) && (eq_tree T1' T2')
              
  | t_sel_low x1 L1 T1', t_sel_low x2 L2 T2' => (eq_var x1 x2) && (eq_label L1 L2) && (eq_tree T1' T2')
              
  | t_sel_equ x1 L1 T1', t_sel_equ x2 L2 T2' => (eq_var x1 x2) && (eq_label L1 L2) && (eq_tree T1' T2')
              
  | t_sel_nom x1 L1 T1', t_sel_nom x2 L2 T2' => (eq_var x1 x2) && (eq_label L1 L2) && (eq_tree T1' T2')
      
  | t_all Ta1 Tb1, t_all Ta2 Tb2 => (eq_tree Ta1 Ta2) && (eq_tree Tb1 Tb2)

  | t_rfn_top Ts1, t_rfn_top Ts2 => (eq_tree Ts1 Ts2)

  | t_rfn_sel x1 L1 Ts1 T1', t_rfn_sel x2 L2 Ts2 T2' => (eq_var x1 x2) && (eq_label L1 L2) && (eq_tree Ts1 Ts2) && (eq_tree T1' T2')

  | t_sha_top x1 L1 ss1, t_sha_top x2 L2 ss2 => (eq_var x1 x2) && (eq_label L1 L2) && (eq_decls ss1 ss2)

  | t_sha_sel x1 L1 ss1 T1', t_sha_sel x2 L2 ss2 T2' => (eq_var x1 x2) && (eq_label L1 L2) && (eq_decls ss1 ss2) && (eq_tree T1' T2')
      
  | t_upp L1 T1', t_upp L2 T2' => (eq_label L1 L2) && (eq_tree T1' T2')
      
  | t_low L1 T1', t_low L2 T2' => (eq_label L1 L2) && (eq_tree T1' T2')
      
  | t_equ L1 T1', t_equ L2 T2' => (eq_label L1 L2) && (eq_tree T1' T2')
      
  | t_nom L1 T1', t_nom L2 T2' => (eq_label L1 L2) && (eq_tree T1' T2')
              
  | t_nil, t_nil => true
              
  | t_con T1' Ts1, t_con T2' Ts2 => (eq_tree T1' T2') && (eq_tree Ts1 Ts2)
  | _, _ => false
  end.

Parameter eq_tree_refl :
  forall T, eq_tree T T = true.

Parameter eqb_tree_eq :
  forall T1 T2, eq_tree T1 T2 = true ->
           T1 = T2.

Parameter neqb_tree_neq :
  forall T1 T2, eq_tree T1 T2 = false ->
           T1 <> T2.

Parameter eq_tree_dec :
  forall T1 T2, {eq_tree T1 T2 = true} + {eq_tree T1 T2 = false}.
    

Program Fixpoint subtype (T1 T2 : tytree) {measure (shape_depth T1 + shape_depth T2)} : bool :=  
  match T1 with
  | t_top => match T2 with
            | t_top => true
            | t_sel_low x L T2' => subtype T1 T2'
            | t_sel_equ x L T2' => subtype T1 T2'
            | _ => false
            end
              
  | t_bot => match T2 with
            | t_upp _ _ => false
            | t_low _ _ => false
            | t_equ _ _ => false
            | t_nom _ _ => false
            | t_nil     => false
            | t_con _ _ => false
            | _ => true
            end
                          
  | t_sel_upp x1 L1 T1' => match T2 with
                          | t_top => true
                          | t_sel_low x2 L2 T2' => orb (andb (eq_var x1 x2) (eq_label L1 L2)) (orb (subtype T1' T2) (subtype T1 T2'))
                          | t_sel_equ x2 L2 T2' => orb (andb (eq_var x1 x2) (eq_label L1 L2)) (orb (subtype T1' T2) (subtype T1 T2'))
                          | t_sel_upp x2 L2 _ => orb (andb (eq_var x1 x2) (eq_label L1 L2)) (subtype T1' T2)
                          | t_sel_nom x2 L2 _ => orb (andb (eq_var x1 x2) (eq_label L1 L2)) (subtype T1' T2)
                          | t_sel_bnd x2 L2 => orb (andb (eq_var x1 x2) (eq_label L1 L2)) (subtype T1' T2)
                          | t_upp L2 T2' => false
                          | t_low L2 T2' => false
                          | t_equ L2 T2' => false
                          | t_nom L2 T2' => false
                          | t_nil     => false
                          | t_con _ _ => false
                          | _ => subtype T1' T2
                          end
                          
  | t_sel_equ x1 L1 T1' => match T2 with
                          | t_top => true
                          | t_sel_low x2 L2 T2' => orb (andb (eq_var x1 x2) (eq_label L1 L2)) (orb (subtype T1' T2) (subtype T1 T2'))
                          | t_sel_equ x2 L2 T2' => orb (andb (eq_var x1 x2) (eq_label L1 L2)) (orb (subtype T1' T2) (subtype T1 T2'))
                          | t_sel_upp x2 L2 _ => orb (andb (eq_var x1 x2) (eq_label L1 L2)) (subtype T1' T2)
                          | t_sel_nom x2 L2 _ => orb (andb (eq_var x1 x2) (eq_label L1 L2)) (subtype T1' T2)
                          | t_sel_bnd x2 L2 => orb (andb (eq_var x1 x2) (eq_label L1 L2)) (subtype T1' T2)
                          | t_upp L2 T2' => false
                          | t_low L2 T2' => false
                          | t_equ L2 T2' => false
                          | t_nom L2 T2' => false
                          | t_nil     => false
                          | t_con _ _ => false
                          | _ => subtype T1' T2
                          end
                          
  | t_sel_nom x1 L1 T1' => match T2 with
                          | t_top => true
                          | t_sel_low x2 L2 T2' => orb (andb (eq_var x1 x2) (eq_label L1 L2)) (orb (subtype T1' T2) (subtype T1 T2'))
                          | t_sel_equ x2 L2 T2' => orb (andb (eq_var x1 x2) (eq_label L1 L2)) (orb (subtype T1' T2) (subtype T1 T2'))
                          | t_sel_upp x2 L2 _ => orb (andb (eq_var x1 x2) (eq_label L1 L2)) (subtype T1' T2)
                          | t_sel_nom x2 L2 _ => orb (andb (eq_var x1 x2) (eq_label L1 L2)) (subtype T1' T2)
                          | t_sel_bnd x2 L2 => orb (andb (eq_var x1 x2) (eq_label L1 L2)) (subtype T1' T2)
                          | t_upp L2 T2' => false
                          | t_low L2 T2' => false
                          | t_equ L2 T2' => false
                          | t_nom L2 T2' => false
                          | t_nil     => false
                          | t_con _ _ => false
                          | _ => subtype T1' T2
                          end
                          
  | t_sel_low x1 L1 T1' => match T2 with
                          | t_top => true
                          | t_sel_low x2 L2 T2' => orb (andb (eq_var x1 x2) (eq_label L1 L2)) (subtype T1 T2')
                          | t_sel_equ x2 L2 T2' => orb (andb (eq_var x1 x2) (eq_label L1 L2)) (subtype T1 T2')
                          | t_sel_upp x2 L2 _ => andb (eq_var x1 x2) (eq_label L1 L2)
                          | t_sel_nom x2 L2 _ => andb (eq_var x1 x2) (eq_label L1 L2)
                          | t_sel_bnd x2 L2 => andb (eq_var x1 x2) (eq_label L1 L2)
                          | _ => false
                          end

  | t_sel_bnd x1 L1 => match T2 with
                      | t_top => true
                      | t_sel_low x2 L2 T2' => orb (andb (eq_var x1 x2) (eq_label L1 L2)) (subtype T1 T2')
                      | t_sel_equ x2 L2 T2' => orb (andb (eq_var x1 x2) (eq_label L1 L2)) (subtype T1 T2')
                      | t_sel_upp x2 L2 _ => andb (eq_var x1 x2) (eq_label L1 L2)
                      | t_sel_nom x2 L2 _ => andb (eq_var x1 x2) (eq_label L1 L2)
                      | t_sel_bnd x2 L2 => andb (eq_var x1 x2) (eq_label L1 L2)
                      | _ => false
                      end

  | t_rfn_top Ts1 => match T2 with
                    | t_top => true
                    | t_sel_low x L T => subtype T1 T
                    | t_sel_equ x L T => subtype T1 T
                    | t_rfn_top Ts2 => subtype Ts1 Ts2
                    | _ => false
                    end

  | t_rfn_sel x1 L1 Ts1 T' => match T2 with
                             | t_top => true
                             | t_sel_low x L T => orb (subtype T1 T)
                                                     (subtype T' T2)
                             | t_sel_equ x L T => orb (subtype T1 T)
                                                     (subtype T' T2)
                             | t_rfn_top _ => subtype T' T2
                             | t_rfn_sel x2 L2 Ts2 _ => orb (andb ((andb (eq_var x1 x2) (eq_label L1 L2)))
                                                                 (subtype Ts1 Ts2))
                                                           (subtype T' T2)
                             | t_upp _ _ => false
                             | t_low _ _ => false
                             | t_equ _ _ => false
                             | t_nom _ _ => false
                             | t_nil => false
                             | t_con _ _ => false
                                             
                             | _ => subtype T' T2
                             end

  | t_sha_top _ _ _ => match T2 with
                      | t_top => true
                      | t_sel_low x L T => subtype T1 T
                      | t_sel_equ x L T => subtype T1 T
                      | _ => false
                      end

  | t_sha_sel _ _ _ T' => match T2 with
                         | t_top => true
                         | t_sel_low x L T => orb (subtype T1 T)
                                                 (subtype T' T2)
                         | t_sel_equ x L T => orb (subtype T1 T)
                                                 (subtype T' T2)
                         | t_upp _ _ => false
                         | t_low _ _ => false
                         | t_equ _ _ => false
                         | t_nom _ _ => false
                         | t_nil => false
                         | t_con _ _ => false
                                         
                         | _ => subtype T' T2
                         end

  | t_all Ta1 Tb1 => match T2 with
                    | t_top => true
                    | t_sel_low x L T => subtype T1 T
                    | t_sel_equ x L T => subtype T1 T
                    | t_all Ta2 Tb2 => andb (eq_tree Ta2 Ta1) (subtype Tb1 Tb2)
                    | _ => false
                    end

  | t_upp L1 T1' => match T2 with
                   | t_upp L2 T2' => andb (eq_label L1 L2)
                                         (subtype T1' T2')
                   | _ => false
                   end

  | t_low L1 T1' => match T2 with
                   | t_low L2 T2' => andb (eq_label L1 L2)
                                         (subtype T2' T1')
                   | _ => false
                   end

  | t_equ L1 T1' => match T2 with
                   | t_upp L2 T2' => andb (eq_label L1 L2)
                                         (subtype T1' T2')
                   | t_low L2 T2' => andb (eq_label L1 L2)
                                         (subtype T2' T1')
                   | t_equ L2 T2' => andb (eq_label L1 L2)
                                         (andb (subtype T1' T2')
                                               (subtype T2' T1'))
                   | _ => false
                   end

  | t_nom L1 T1' => match T2 with
                   | t_upp L2 T2' => andb (eq_label L1 L2)
                                         (subtype T1' T2')
                   | t_nom L2 T2' => (eq_label L1 L2) && eq_tree T1' T2'
                   | _ => false
                   end

  | t_nil => match T2 with
            | t_nil => true
            | _ => false
            end

  | t_con T1' Ts1 => match T2 with
                   | t_nil => true
                   | t_con T2' Ts2 => andb (subtype T1' T2') (subtype Ts1 Ts2)
                   | _ => false
                   end
                     
  end.
Next Obligation.
  crush.
Defined.
Next Obligation.
  crush.
Defined.
Next Obligation.
  crush.
Defined.
Next Obligation.
  crush.
Defined.
Next Obligation.
  crush.
Defined.
Next Obligation.
  crush.
Defined.
Next Obligation.
  crush.
Defined.
Next Obligation.
  crush.
Defined.
Next Obligation.
  crush.
Defined.
Next Obligation.
  crush.
Defined.
Next Obligation.
  crush.
Defined.
Next Obligation.
  crush.
Defined.
Next Obligation.
  crush.
Defined.
Next Obligation.
  crush.
Defined.
Next Obligation.
  crush.
Defined.
Next Obligation.
  crush.
Defined.
Next Obligation.
  crush.
Defined.
Next Obligation.
  crush.
Defined.
Next Obligation.
  crush.
Defined.
Next Obligation.
  crush.
Defined.
Next Obligation.
  crush.
Defined.
Next Obligation.
  crush.
Defined.
Next Obligation.
  crush.
Defined.
Next Obligation.
  crush.
Defined.
Next Obligation.
  crush.
Defined.
Next Obligation.
  crush.
Defined.
Next Obligation.
  crush.
Defined.
Next Obligation.
  crush.
Defined.
Next Obligation.
  crush.
Defined.
Next Obligation.
  crush.
Defined.
Next Obligation.
  crush.
Defined.
Next Obligation.
  crush.
Defined.
Next Obligation.
  crush.
Defined.
Next Obligation.
  crush.
Defined.
Next Obligation.
  crush.
Defined.
Next Obligation.
  crush.
Defined.
Next Obligation.
  crush.
Defined.
Next Obligation.
  crush.
Defined.
Next Obligation.
  crush.
Defined.
Next Obligation.
  crush.
Defined.
Next Obligation.
  crush.
Defined.
Next Obligation.
  crush.
Defined.
Next Obligation.
  crush.
Defined.
Next Obligation.
  crush.
Defined.
Next Obligation.
  crush.
Defined.
Next Obligation.
  crush.
Defined.
Next Obligation.
  crush.
Defined.
Next Obligation.
  crush.
Defined.
Next Obligation.
  crush.
Defined.
Next Obligation.
  crush.
Defined.
Next Obligation.
  crush.
Defined.
Next Obligation.
  crush.
Defined.
Next Obligation.
  crush.
Defined.
Next Obligation.
  crush.
Defined.
Next Obligation.
  crush.
Defined.
Next Obligation.
  crush.
Defined.
Next Obligation.
  crush.
Defined.
Next Obligation.
  crush.
Defined.
Next Obligation.
  simpl.
  destruct T1'; crush.
Defined.
Next Obligation.
  crush.
Defined.
Next Obligation.
  crush.
Defined.
Next Obligation.
  crush.
Defined.
Next Obligation.
  destruct T1'; crush.
Defined.
Next Obligation.
  crush.
Defined.
Next Obligation.
  crush.
Defined.
Next Obligation.
  crush.
Defined.
Next Obligation.
  crush.
Defined.
Next Obligation.
  crush.
Defined.
Next Obligation.
  crush.
Defined.
Next Obligation.
  crush.
Defined.
Next Obligation.
  crush.
Defined.
Next Obligation.
  crush.
Defined.
Next Obligation.
  crush.
Defined.
Next Obligation.
  crush.
Defined.
Next Obligation.
  crush.
Defined.
Next Obligation.
  crush.
Defined.
Next Obligation.
  crush.
Defined.
Next Obligation.
  crush.
Defined.
Next Obligation.
  crush.
Defined.
Next Obligation.
  crush.
Defined.
Next Obligation.
  crush.
Defined.
Next Obligation.
  crush.
Defined.
Next Obligation.
  crush.
Defined.
Next Obligation.
  crush.
Defined.
Next Obligation.
  crush.
Defined.
Next Obligation.
  crush.
Defined.
Next Obligation.
  crush.
Defined.
Next Obligation.
  crush.
Defined.
Next Obligation.
  crush.
Defined.
Next Obligation.
  crush.
Defined.
Next Obligation.
  crush.
Defined.
Next Obligation.
  crush.
Defined.
Next Obligation.
  crush.
Defined.
Next Obligation.
  crush.
Defined.
Next Obligation.
  crush.
Defined.
Next Obligation.
  crush.
Defined.
Next Obligation.
  crush.
Defined.
Next Obligation.
  crush.
Defined.
Next Obligation.
  crush.
Defined.
Next Obligation.
  crush.
Defined.
Next Obligation.
  crush.
Defined.
Next Obligation.
  crush.
Defined.
Next Obligation.
  crush.
Defined.
Next Obligation.
  crush.
Defined.
Next Obligation.
  crush.
Defined.
Next Obligation.
  crush.
Defined.
Next Obligation.
  destruct T'; crush.
Defined.
Next Obligation.
  crush.
Defined.
Next Obligation.
  crush.
Defined.
Next Obligation.
  crush.
Defined.
Next Obligation.
  crush.
Defined.
Next Obligation.
  crush.
Defined.
Next Obligation.
  crush.
Defined.
Next Obligation.
  crush.
Defined.
Next Obligation.
  crush.
Defined.
Next Obligation.
  crush.
Defined.
Next Obligation.
  crush.
Defined.
Next Obligation.
  crush.
Defined.
Next Obligation.
  crush.
Defined.
Next Obligation.
  crush.
Defined.
Next Obligation.
  crush.
Defined.
Next Obligation.
  crush.
Defined.
Next Obligation.
  crush.
Defined.
Next Obligation.
  crush.
Defined.
Next Obligation.
  crush.
Defined.
Next Obligation.
  crush.
Defined.
Next Obligation.
  crush.
Defined.
Next Obligation.
  crush.
Defined.
Next Obligation.
  crush.
Defined.
Next Obligation.
  crush.
Defined.
Next Obligation.
  crush.
Defined.
Next Obligation.
  crush.
Defined.
Next Obligation.
  crush.
Defined.
Next Obligation.
  crush.
Defined.
Next Obligation.
  crush.
Defined.
Next Obligation.
  crush.
Defined.
Next Obligation.
  crush.
Defined.
Next Obligation.
  crush.
Defined.
Next Obligation.
  crush.
Defined.
Next Obligation.
  crush.
Defined.
Next Obligation.
  crush.
Defined.
Next Obligation.
  crush.
Defined.
Next Obligation.
  crush.
Defined.
Next Obligation.
  crush.
Defined.
Next Obligation.
  crush.
Defined.
Next Obligation.
  crush.
Defined.
Next Obligation.
  crush.
Defined.
Next Obligation.
  crush.
Defined.
Next Obligation.
  crush.
Defined.
Next Obligation.
  crush.
Defined.
Next Obligation.
  crush.
Defined.
Next Obligation.
  crush.
Defined.
Next Obligation.
  crush.
Defined.
Next Obligation.
  crush.
Defined.
Next Obligation.
  crush.
Defined.
Next Obligation.
  crush.
Defined.
Next Obligation.
  crush.
Defined.
Next Obligation.
  crush.
Defined.
Next Obligation.
  crush.
Defined.
Next Obligation.
  crush.
Defined.
Next Obligation.
  crush.
Defined.
Next Obligation.
  crush.
Defined.
Next Obligation.
  crush.
Defined.
Next Obligation.
  crush.
Defined.
Next Obligation.
  crush.
Defined.
Next Obligation.
  crush.
Defined.
Next Obligation.
  crush.
Defined.
Next Obligation.
  crush.
Defined.
Next Obligation.
  crush.
Defined.
Next Obligation.
  crush.
Defined.
Next Obligation.
  crush.
Defined.
Next Obligation.
  crush.
Defined.
Next Obligation.
  crush.
Defined.
Next Obligation.
  crush.
Defined.
Next Obligation.
  crush.
Defined.
Next Obligation.
  crush.
Defined.
Next Obligation.
  crush.
Defined.
Next Obligation.
  crush.
Defined.
Next Obligation.
  crush.
Defined.
Next Obligation.
  crush.
Defined.
Next Obligation.
  crush.
Defined.
Next Obligation.
  crush.
Defined.
Next Obligation.
  crush.
Defined.
Next Obligation.
  crush.
Defined.
Next Obligation.
  crush.
Defined.
Next Obligation.
  crush.
Defined.
Next Obligation.
  crush.
Defined.
Next Obligation.
  crush.
Defined.
Next Obligation.
  crush.
Defined.
Next Obligation.
  crush.
Defined.
Next Obligation.
  crush.
Defined.
Next Obligation.
  crush.
Defined.
Next Obligation.
  crush.
Defined.
Next Obligation.
  crush.
Defined.
Next Obligation.
  crush.
Defined.
Next Obligation.
  crush.
Defined.
Next Obligation.
  crush.
Defined.
Next Obligation.
  crush.
Defined.
Next Obligation.
  crush.
Defined.
Next Obligation.
  crush.
Defined.
Next Obligation.
  crush.
Defined.
Next Obligation.
  crush.
Defined.
Next Obligation.
  crush.
Defined.
Next Obligation.
  crush.
Defined.
Next Obligation.
  crush.
Defined.
Next Obligation.
  crush.
Defined.
Next Obligation.
  crush.
Defined.
Next Obligation.
  crush.
Defined.

Import WfExtensionality.

Lemma subtype_top :
  forall T, (forall L T', T <> t_upp L T') ->
       (forall L T', T <> t_low L T') ->
       (forall L T', T <> t_equ L T') ->
       (forall L T', T <> t_nom L T') ->
       (T <> t_nil) ->
       (forall T' Ts, T <> t_con T' Ts) ->
       subtype T t_top = true.
Proof.
  intros.

  unfold subtype, subtype_func;
    simpl;
    rewrite fix_sub_eq_ext;
    simpl;
    fold subtype_func;
    auto.

  destruct T; simpl; auto.
  
  contradiction (H l T); auto.
  contradiction (H0 l T); auto.
  contradiction (H1 l T); auto.
  contradiction (H2 l T); auto.
  contradiction (H3); auto.
  contradiction (H4 T1 T2); auto.
Qed.

Lemma subtype_bot :
  forall T, (forall L T', T <> t_upp L T') ->
       (forall L T', T <> t_low L T') ->
       (forall L T', T <> t_equ L T') ->
       (forall L T', T <> t_nom L T') ->
       (T <> t_nil) ->
       (forall T' Ts, T <> t_con T' Ts) ->
       subtype t_bot T = true.
Proof.
  intros.

  unfold subtype, subtype_func;
    simpl;
    rewrite fix_sub_eq_ext;
    simpl;
    fold subtype_func;
    auto.

  destruct T; simpl; auto.
  
  contradiction (H l T); auto.
  contradiction (H0 l T); auto.
  contradiction (H1 l T); auto.
  contradiction (H2 l T); auto.
  contradiction (H3); auto.
  contradiction (H4 T1 T2); auto.
Qed.