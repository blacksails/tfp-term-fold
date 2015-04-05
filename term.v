(*

Project about fold_right and fold_left
Given the two specifications

*)

Require Import Bool List Arith.
Ltac unfold_tactic name := intros; unfold name; reflexivity.

(* We will use the following function to construct a function which compares two nat lists *)
Fixpoint beq_list (T : Type) (l1 l2 : list T) (comp : T -> T -> bool) := 
  match l1 with
  | nil =>
      match l2 with
      | nil => true
      | _ => false
      end
  | e :: l =>
      match l2 with
      | nil => false
      | e' :: l' =>
          match comp e e' with
          | false => false
          | true => beq_list T l l' comp
          end
      end
  end.

Definition beq_nat_list (l1 l2 : list nat) :=
  beq_list nat l1 l2 beq_nat.

Definition unit_tests_for_fold_right (candidate : forall T1 T2, T2 -> (T1 -> T2 -> T2) -> list T1 -> T2) :=
  (* Nil list always returns nil case. Cons case doesn't any influence *)
  (beq_nat (candidate nat nat 42 plus nil)
           42) &&
  (beq_nat (candidate nat nat 42 mult nil)
           42) &&
  (* Simple cons cases *)
  (beq_nat (candidate nat nat 21 plus (21 :: nil))
           (21 + 21)) &&
  (beq_nat (candidate nat nat 21 mult (2 :: nil))
           (2 * 21)) &&
  (* Sum function for list of nat *)
  (beq_nat (candidate nat nat 0 plus (1 :: 2 :: 3 :: 4 :: 5 :: nil))
           (1 + (2 + (3 + (4 + (5 + 0)))))) &&
  (* Factorial function for list of nat *)
  (beq_nat (candidate nat nat 1 mult (1 :: 2 :: 3 :: 4 :: 5 :: nil))
           (1 * (2 * (3 * (4 * (5 * 1)))))) &&
  (* Identity of list *)
  (beq_nat_list (candidate nat (list nat) nil (fun n ns => n :: ns) (1 :: 2 :: 3 :: nil))
                (1 :: (2 :: (3 :: nil)))).

Definition specification_of_fold_right (fold_right : forall T1 T2, T2 -> (T1 -> T2 -> T2) -> list T1 -> T2) :=
  (forall (T1 T2 : Type)
          (nil_case : T2)
          (cons_case : T1 -> T2 -> T2),
     fold_right T1 T2 nil_case cons_case nil =
     nil_case)
  /\
  (forall (T1 T2 : Type)
          (nil_case : T2)
          (cons_case : T1 -> T2 -> T2)
          (v : T1)
          (vs' : list T1),
     fold_right T1 T2 nil_case cons_case (v :: vs') =
     cons_case v (fold_right T1 T2 nil_case cons_case vs')).

Theorem there_is_only_one_fold_right :
  forall f g : (forall T1 T2, T2 -> (T1 -> T2 -> T2) -> list T1 -> T2),
    specification_of_fold_right f ->
    specification_of_fold_right g ->
    forall (T1 T2 : Type)
           (nil_case : T2)
           (cons_case : T1 -> T2 -> T2)
           (vs : list T1),
      f T1 T2 nil_case cons_case vs = g T1 T2 nil_case cons_case vs.
Proof.
  unfold specification_of_fold_right.
  intros f g [H_f_nil H_f_cons] [H_g_nil H_g_cons].
  intros T1 T2 nil_case cons_case vs.
  
  induction vs as [ | v vs' IHvs'].
    rewrite H_g_nil.
    apply H_f_nil.
  rewrite H_f_cons.
  rewrite IHvs'.
  rewrite H_g_cons.
  reflexivity.
Qed.

Fixpoint fold_right_v0 (T1 T2 : Type)
                       (nil_case : T2)
                       (cons_case : T1 -> T2 -> T2)
                       (vs : list T1) :=
  match vs with
  | nil => nil_case
  | v :: vs' => cons_case v (fold_right_v0 T1 T2 nil_case cons_case vs')
  end.

Compute unit_tests_for_fold_right fold_right_v0.

Lemma unfold_fold_right_v0_nil :
  forall (T1 T2 : Type)
         (nil_case : T2)
         (cons_case : T1 -> T2 -> T2),
    fold_right_v0 T1 T2 nil_case cons_case nil = nil_case.
Proof.
  unfold_tactic fold_right_v0.
Qed.

Lemma unfold_fold_right_v0_cons :
  forall (T1 T2 : Type)
         (nil_case : T2)
         (cons_case : T1 -> T2 -> T2)
         (v : T1)
         (vs' : list T1),
    fold_right_v0 T1 T2 nil_case cons_case (v :: vs') =
    cons_case v (fold_right_v0 T1 T2 nil_case cons_case vs').
Proof.
  unfold_tactic fold_right_v0.
Qed.

Proposition fold_right_v0_fits_the_specification_of_fold_right :
  specification_of_fold_right fold_right_v0.
Proof.
  unfold specification_of_fold_right; split.
    exact unfold_fold_right_v0_nil.
  exact unfold_fold_right_v0_cons.
Qed.

Definition unit_tests_for_fold_left (candidate : forall T1 T2, T2 -> (T1 -> T2 -> T2) -> list T1 -> T2) :=
  (* Nil list always returns nil case. Cons case doesn't any influence *)
  (beq_nat (candidate nat nat 42 plus nil)
           42) &&
  (beq_nat (candidate nat nat 42 mult nil)
           42) &&
  (* Simple cons cases *)
  (beq_nat (candidate nat nat 21 plus (21 :: nil))
           (21 + 21)) &&
  (beq_nat (candidate nat nat 21 mult (2 :: nil))
           (2 * 21)) &&
  (* Sum function for list of nat *)
  (beq_nat (candidate nat nat 0 plus (1 :: 2 :: 3 :: 4 :: 5 :: nil))
           (5 + (4 + (3 + (2 + (1 + 0)))))) &&
  (* Factorial function for list of nat *)
  (beq_nat (candidate nat nat 1 mult (1 :: 2 :: 3 :: 4 :: 5 :: nil))
           (5 * (4 * (3 * (2 * (1 * 1)))))) &&
  (* Reverse of list *)
  (beq_nat_list (candidate nat (list nat) nil (fun n ns => n :: ns) (1 :: 2 :: 3 :: nil))
           (3 :: (2 :: (1 :: nil)))).

Definition specification_of_fold_left (fold_left : forall T1 T2, T2 -> (T1 -> T2 -> T2) -> list T1 -> T2) :=
  (forall (T1 T2 : Type)
          (nil_case : T2)
          (cons_case : T1 -> T2 -> T2),
     fold_left T1 T2 nil_case cons_case nil =
     nil_case)
  /\
  (forall (T1 T2 : Type)
          (nil_case : T2)
          (cons_case : T1 -> T2 -> T2)
          (v : T1)
          (vs' : list T1),
     fold_left T1 T2 nil_case cons_case (v :: vs') =
     fold_left T1 T2 (cons_case v nil_case) cons_case vs').

Theorem there_is_only_one_fold_left :
  forall f g : (forall T1 T2, T2 -> (T1 -> T2 -> T2) -> list T1 -> T2),
    specification_of_fold_left f ->
    specification_of_fold_left g ->
    forall (T1 T2 : Type)
           (nil_case : T2)
           (cons_case : T1 -> T2 -> T2)
           (vs : list T1),
      f T1 T2 nil_case cons_case vs = g T1 T2 nil_case cons_case vs.
Proof.
  unfold specification_of_fold_left.
  intros f g [H_f_nil H_f_cons] [H_g_nil H_g_cons].
  intros T1 T2 nil_case cons_case vs.
  
  (* Strengthen IH *)
  revert nil_case.
  
  induction vs as [ | v vs' IHvs'].
    intro nil_case.
    rewrite H_g_nil.
    apply H_f_nil.
  intro nil_case.
  rewrite H_f_cons.
  rewrite IHvs'.
  rewrite H_g_cons.
  reflexivity.
Qed.

Fixpoint fold_left_v0 (T1 T2 : Type)
                      (nil_case : T2)
                      (cons_case : T1 -> T2 -> T2)
                      (vs : list T1) :=
  match vs with
  | nil => nil_case
  | v :: vs' => fold_left_v0 T1 T2 (cons_case v nil_case) cons_case vs'
  end.

Compute unit_tests_for_fold_left fold_left_v0.

Lemma unfold_fold_left_v0_nil :
  forall (T1 T2 : Type)
         (nil_case : T2)
         (cons_case : T1 -> T2 -> T2),
    fold_left_v0 T1 T2 nil_case cons_case nil = nil_case.
Proof.
  unfold_tactic fold_left_v0.
Qed.

Lemma unfold_fold_left_v0_cons :
  forall (T1 T2 : Type)
         (nil_case : T2)
         (cons_case : T1 -> T2 -> T2)
         (v : T1)
         (vs' : list T1),
    fold_left_v0 T1 T2 nil_case cons_case (v :: vs') =
    fold_left_v0 T1 T2 (cons_case v nil_case) cons_case vs'.
Proof.
  unfold_tactic fold_left_v0.
Qed.

Proposition fold_left_v0_fits_the_specification_of_fold_left :
  specification_of_fold_left fold_left_v0.
Proof.
  unfold specification_of_fold_left; split.
    exact unfold_fold_left_v0_nil.
  exact unfold_fold_left_v0_cons.
Qed.

(* propose an implementation of fold_right (resp. of fold_left)
that satisfies the specification of fold_right (resp. of fold_left). *)

(* Moved further down the file *)
  
(* show that applying [your implementation of] fold_right
  to nil and cons gives the identity function over lists

  Example:
    Compute
      fold_right nat
                 (list nat)
                 nil
                 (fun n ns => n :: ns)
                 (1 :: 2 :: 3 :: nil).
  yields
    (1 :: 2 :: 3 :: nil) *)

Definition unit_tests_for_list_nat_identiy (identity : forall T, list T -> list T) :=
  (beq_nat_list (identity nat nil) nil)
  &&
  (beq_nat_list (identity nat (1 :: 2 :: 3 :: nil)) (1 :: 2 :: 3 :: nil))
  &&
  (beq_nat_list (identity nat (42 :: nil)) (42 :: nil)).

Definition specification_of_list_identity (identity : forall T, list T -> list T) :=
  forall (T : Type) (xs : list T),
    identity T xs = xs.

Theorem there_is_only_one_list_identity :
  forall (f g : forall T, list T -> list T),
    specification_of_list_identity f ->
    specification_of_list_identity g ->
    forall (T : Type) (xs : list T),
      f T xs = g T xs.
Proof.
  unfold specification_of_list_identity.
  intros f g S_i_f S_i_g T xs.
  rewrite S_i_g.
  apply S_i_f.
Qed.

Definition list_identity_v0 (T : Type) (xs : list T) :=
  fold_right_v0 T (list T) nil (fun n ns => n :: ns) xs.

Compute unit_tests_for_list_nat_identiy list_identity_v0.

Proposition list_identity_v0_fits_the_specification_of_list_identity :
  specification_of_list_identity list_identity_v0.
Proof.
  unfold specification_of_list_identity.
  unfold list_identity_v0.
  intros T xs.

  induction xs as [ | x xs' IHxs' ].
    (* NIL CASE *)
    apply unfold_fold_right_v0_nil.
  (* CONS CASE *)
  rewrite unfold_fold_right_v0_cons.
  rewrite IHxs'.
  reflexivity.
Qed.

(* show that applying [your implementation of] fold_left
  to nil and cons gives the reverse function over lists

  Example:
    Compute
      fold_left nat
                (list nat)
                nil
                (fun n ns => n :: ns)
                (1 :: 2 :: 3 :: nil).
  yields
    (3 :: 2 :: 1 :: nil)
 *)

Definition unit_tests_for_append_nat (append : forall T, list T -> list T -> list T) :=
  (beq_nat_list (append nat nil nil)
                  nil)
  &&
  (beq_nat_list (append nat (1 :: nil) nil)
                (1 :: nil))
  &&
  (beq_nat_list (append nat nil (4 :: nil))
                (4 :: nil))
  &&
  (beq_nat_list (append nat (1 :: 2 :: nil) (3 :: 4 :: nil))
                  (1 :: 2 :: 3 :: 4 :: nil)).

Definition specification_of_append (append : forall T, list T -> list T -> list T) :=
  (forall (T : Type) (ys : list T),
     append T nil ys = ys)
  /\
  (forall (T : Type) (x : T) (xs' ys : list T),
     append T (x :: xs') ys = x :: (append T xs' ys)).

Theorem there_is_only_one_append :
  forall (f g : forall T, list T -> list T -> list T),
    specification_of_append f ->
    specification_of_append g ->
    forall (T : Type) (xs ys : list T),
      f T xs ys = g T xs ys.
Proof.
  intros f g [Sf_bc Sf_ic] [Sg_bc Sg_ic].
  intros T xs.

  induction xs as [ | x xs' IHxs' ]; intro ys.

  rewrite -> Sg_bc.
  apply Sf_bc.

  rewrite -> Sf_ic.
  rewrite -> IHxs'.
  rewrite -> Sg_ic.
  reflexivity.
Qed.

Definition append_v0 (T : Type) (xs ys : list T) :=
  fold_right_v0 T (list T) ys (fun n ns => n :: ns) xs.

Compute unit_tests_for_append_nat append_v0.

Proposition append_v0_fits_the_specification_of_append :
  specification_of_append append_v0.
Proof.
  unfold specification_of_append, append_v0.
  split.

  intros T ys.
  apply unfold_fold_right_v0_nil.

  intros T x xs' ys.
  rewrite -> unfold_fold_right_v0_cons.
  reflexivity.
Qed.

Theorem append_is_associative :
  forall (append : forall T, list T -> list T -> list T),
    specification_of_append append ->
    forall (T : Type) (x y z : list T),
    append T x (append T y z) = append T (append T x y) z.
Proof.
  intros append [H_append_bc H_append_ic].
  intros T xs ys zs.
  induction xs as [ | x xs' IHxs'].
    rewrite ->2 H_append_bc.
    reflexivity.
  rewrite H_append_ic.
  rewrite IHxs'.
  rewrite H_append_ic.
  rewrite H_append_ic.
  reflexivity.
Qed.

Definition unit_tests_for_reverse_nat (reverse : forall T, list T -> list T) :=
  (beq_nat_list (reverse nat nil)
                  nil)
  &&
  (beq_nat_list (reverse nat (1 :: nil))
                  (1 :: nil))
  &&
  (beq_nat_list (reverse nat (1 :: 2 :: nil))
                  (2 :: 1 :: nil))
  &&
  (beq_nat_list (reverse nat (1 :: 2 :: 3 :: nil))
                  (3 :: 2 :: 1 :: nil)).
  
Definition specification_of_reverse (reverse : forall T, list T -> list T) :=
  (forall (T : Type),
     reverse T nil = nil)
  /\
  (forall (T : Type) (x : T) (xs' : list T)
          (append : forall T, list T -> list T -> list T),
     specification_of_append append ->
     reverse T (x :: xs') = append T (reverse T xs') (x :: nil)).

Theorem there_is_only_one_reverse :
  forall (f g : forall T, list T -> list T)
         (append : forall T : Type, list T -> list T -> list T),
    specification_of_reverse f ->
    specification_of_reverse g ->
    specification_of_append append ->
    forall (T : Type) (xs : list T),
      f T xs = g T xs.
Proof.
  intros f g append [Sf_bc Sf_ic] [Sg_bc Sg_ic].
  intros S_append.
  assert (S_append_tmp := S_append).
  destruct S_append_tmp as [S_append_bc S_append_ic].    
  intros T xs.

  induction xs as [ | x xs' IHxs' ].

  rewrite -> Sg_bc.
  apply Sf_bc.

  rewrite -> (Sf_ic T x xs' append S_append).
  rewrite -> IHxs'.
  rewrite -> (Sg_ic T x xs' append S_append).
  reflexivity.
Qed.

Definition reverse_v0 (T : Type) (xs : list T) :=
  fold_left_v0 T (list T) nil (fun n ns => n :: ns) xs.

Compute unit_tests_for_reverse_nat reverse_v0.

Proposition about_fold_left_and_append :
  forall (fold_left : forall (T1 T2 : Type), T2 -> (T1 -> T2 -> T2) -> list T1 -> T2),
    specification_of_fold_left fold_left ->
      forall (T1 : Type)
             (vs : list T1)
             (x : T1)
             (xs : list T1)
             (append : forall T, list T -> list T -> list T),
        specification_of_append append ->
        fold_left T1
                  (list T1)
                  (x :: xs)
                  (fun (n : T1) (ns : list T1) => n :: ns)
                  vs =
        append T1
               (fold_left T1
                          (list T1)
                          nil
                          (fun (n : T1) (ns : list T1) => n :: ns)
                          vs)
               (x :: xs).
Proof.
  intros fold_left [H_fold_left_nil H_fold_left_cons].
  intros T1 vs x xs.
  intros append S_append;
  assert (S_append_tmp := S_append);
  destruct S_append_tmp as [H_append_bc H_append_ic].
  revert x xs.

  induction vs as [ | v vs' IHvs' ]; intros x xs.
    (* NIL CASE *)
    rewrite ->2 H_fold_left_nil.
    rewrite -> H_append_bc.
    reflexivity.
  (* CONS CASE *)
  (* left hand side *)
  rewrite H_fold_left_cons.
  rewrite IHvs'.
  (* right hand side *)
  rewrite H_fold_left_cons.
  rewrite IHvs'.  
  rewrite <- (append_is_associative append S_append).
  rewrite H_append_ic.
  rewrite H_append_bc.
  reflexivity.
Qed.

Proposition reverse_v0_fits_the_specification_of_reverse :
  specification_of_reverse reverse_v0.
Proof.
  unfold specification_of_reverse, reverse_v0; split.  
  (* NIL CASE *)
    intros T.
    apply unfold_fold_left_v0_nil.
  (* CONS CASE *)
  intros T x xs' append S_append.    
  assert (S_append_tmp := S_append);
  destruct S_append_tmp as [H_append_bc H_append_ic].    
  rewrite unfold_fold_left_v0_cons.
  rewrite (about_fold_left_and_append
             fold_left_v0
             fold_left_v0_fits_the_specification_of_fold_left
             T
             xs'
             x
             nil
             append
             S_append).
  reflexivity.
Qed.

(* define fold_left in term of fold_right, and prove that your definition
  satisfies the specification of fold_left; *)

Definition fold_left_v1 (T1 T2 : Type)
                        (nil_case : T2)
                        (cons_case : T1 -> T2 -> T2)
                        (vs : list T1) : T2 :=
  fold_right_v0 T1
                (T2 -> T2)
                (fun a => a)
                (fun x h a => h (cons_case x a))
                vs
                nil_case.

Proposition fold_left_v1_fits_the_specification_of_fold_left :
    specification_of_fold_left fold_left_v1.
Proof.
  unfold specification_of_fold_left, fold_left_v1.
  split.
    (* NIL CASE *)
    apply unfold_fold_right_v0_nil.
  (* CONS CASE *)
  intros T1 T2 nil_case cons_case v vs'.
  rewrite unfold_fold_right_v0_cons.
  reflexivity.
Qed.

(* define fold_right in term of fold_left, and prove that your definition
  satisfies the specification of fold_right; *)

Proposition fold_right_from_fold_left_aux :
  forall (fold_left : forall (T1 T2 : Type), T2 -> (T1 -> T2 -> T2) -> list T1 -> T2),
    specification_of_fold_left fold_left ->
    forall (T1 T2 : Type)
           (nil_case : T2)
           (cons_case : T1 -> T2 -> T2)
           (vs : list T1)
           (k : T2 -> T2),
      fold_left T1
                (T2 -> T2)
                k
                (fun x h a => h (cons_case x a))
                vs
                nil_case =
      k (fold_left T1
                   (T2 -> T2)
                   (fun a => a)
                   (fun x h a => h (cons_case x a))
                   vs
                   nil_case).
Proof.
  intros fold_left [H_fold_left_nil H_fold_left_cons].
  intros T1 T2 nil_case cons_case vs.

  induction vs as [ | v vs' IHvs' ]; intro k.
    (* NIL CASE *)
    rewrite ->2 H_fold_left_nil.
    reflexivity.
  (* CONS CASE *)
  (* left hand side *)
  rewrite H_fold_left_cons.
  rewrite IHvs'.
  (* right hand side *)
  rewrite H_fold_left_cons.
  rewrite (IHvs' (fun a : T2 => cons_case v a)).
  reflexivity.    
Qed.

Proposition fold_right_from_fold_left :
  forall (fold_left : forall (T1 T2 : Type), T2 -> (T1 -> T2 -> T2) -> list T1 -> T2),
    specification_of_fold_left fold_left ->
    specification_of_fold_right (fun T1 T2 nil_case cons_case vs =>
                                   fold_left T1
                                             (T2 -> T2)
                                             (fun a => a)
                                             (fun x h a => h (cons_case x a))
                                             vs
                                             nil_case).
Proof.
  intros fold_left S_fold_left_tmp.
  assert (S_fold_left := S_fold_left_tmp).
  destruct S_fold_left_tmp as [H_fold_left_nil H_fold_left_cons].

  unfold specification_of_fold_right; split.
    (* NIL CASE *)
    intros T1 T2 nil_case cons_case.
    rewrite H_fold_left_nil.
    reflexivity.
  (* CONS CASE *)
  intros T1 T2 nil_case cons_case v vs'.
  rewrite H_fold_left_cons.
  rewrite -> (fold_right_from_fold_left_aux
                fold_left
                S_fold_left
                T1 T2
                nil_case cons_case vs'
                (fun a : T2 => cons_case v a)).
  reflexivity.
Qed.

Definition fold_right_v1 (T1 T2 : Type)
                         (nil_case : T2)
                         (cons_case : T1 -> T2 -> T2)
                         (vs : list T1) : T2 :=
  fold_left_v0 T1
               (T2 -> T2)
               (fun a => a)
               (fun x h a => h (cons_case x a))
               vs
               nil_case.

Proposition fold_right_v1_fits_the_specification_of_fold_right :
    specification_of_fold_right fold_right_v1.
Proof.
  unfold fold_right_v1.
  (* 
    We have already shown that the goal holds if the implementation of fold_left
    that we use fits the specification of fold_left. Let's use that knowledge!
  *)
  apply fold_right_from_fold_left.
  (* 
    Now we just have to prove that fold_left_v0 fits the specification which
    we have already proven. 
  *)
  apply fold_left_v0_fits_the_specification_of_fold_left.
Qed.

(* 
  show that if the cons case is a function that is associative and
  commutative, applying fold_left and applying fold_right to a nil case,
  this cons case, and a list give the same result.  Example
  (remembering that + is the infix notation for the function plus):
*)

Definition specification_of_addition (add : nat -> nat -> nat) :=
  (forall j : nat,
    add O j = j)
  /\
  (forall i' j : nat,
    add (S i') j = S (add i' j)).

Theorem there_is_only_one_addition :
  forall (p1 p2 : nat -> nat -> nat),
    specification_of_addition p1 ->
    specification_of_addition p2 ->
    forall (x y : nat),
      p1 x y = p2 x y.
Proof.
  intros p1 p2 [H_p1_bc H_p1_ic] [H_p2_bc H_p2_ic].
  intros x y.
  induction x as [ | x' IHx'].
    rewrite H_p2_bc.
    apply H_p1_bc.
  rewrite H_p1_ic.
  rewrite IHx'.
  rewrite H_p2_ic.
  reflexivity.
Qed.

Theorem plus_fits_the_specification_of_addition :
  specification_of_addition plus.
Proof.
  unfold specification_of_addition; split.
    apply plus_0_l.
  apply plus_Sn_m.
Qed.

Proposition about_addition_and_fold_left :
  forall (fold_left : forall (T1 T2 : Type), T2 -> (T1 -> T2 -> T2) -> list T1 -> T2)
         (add : nat -> nat -> nat),
    specification_of_fold_left fold_left ->
    specification_of_addition add ->
    forall (n : nat)
           (ns : list nat),
      add n (fold_left nat nat 0 add ns) = fold_left nat nat n add ns.
Proof.
  intros fold_left add 
         [H_fold_left_nil H_fold_left_cons] S_add.
  intros n ns.
 
  revert n. 
  induction ns as [ | n' ns' IHns']; intro n.
    rewrite ->2 H_fold_left_nil.
    (* Rewrite add to plus so that we can use the coq lib's lemmas about plus *)
    rewrite (there_is_only_one_addition 
               add
               plus
               S_add
               plus_fits_the_specification_of_addition).
    ring.
  rewrite H_fold_left_cons.
  rewrite <- IHns'.
  rewrite H_fold_left_cons.
  rewrite <- (IHns' (add n' n)).
  (* Rewrite add to plus so that we can use the coq lib's lemmas about plus *)
  rewrite ->5 (there_is_only_one_addition 
                 add
                 plus
                 S_add
                 plus_fits_the_specification_of_addition).
  ring.
Qed.

Proposition same_old_same_old :
  (forall n m p : nat,
     n + (m + p) = n + m + p) ->
  (forall n m : nat,
     n + m = m + n) ->
  forall ns : list nat,
    fold_right_v0 nat nat 0 plus ns = fold_left_v0 nat nat 0 plus ns.
Proof.
  intros H_plus_assoc.
  intros H_plus_comm.
  intro ns.  
  
  induction ns as [ | n ns' IHns'].
    (* NIL CASE *)
    rewrite unfold_fold_right_v0_nil.
    rewrite unfold_fold_left_v0_nil.
    reflexivity.
  (* CONS CASE *)
  (* left hand side *)
  rewrite unfold_fold_right_v0_cons.
  rewrite IHns'.
  (* right hand side *)
  rewrite unfold_fold_left_v0_cons.
  rewrite plus_0_r.

  apply (about_addition_and_fold_left
           fold_left_v0
           plus
           fold_left_v0_fits_the_specification_of_fold_left
           plus_fits_the_specification_of_addition
           n
           ns').
Qed.

(* Wrote this too many times :o) *)
Definition fold_type :=
  forall (T1 T2 : Type), T2 -> (T1 -> T2 -> T2) -> list T1 -> T2.

Proposition fold_right_and_left_on_assoc_and_comm_cons_same_result_aux :
  forall (fold_left : fold_type),
    specification_of_fold_left fold_left ->
    forall (T : Type)
           (func : T -> T -> T),
      (forall n m p : T, func n (func m p) = func (func n m) p) ->
      (forall n m : T, func n m = func m n) ->
        forall (n : T)
               (n' : T)
               (ns' : list T),
        func n' (fold_left T T n func ns') = fold_left T T (func n' n) func ns'.
Proof.
  intros fold_left [H_fold_left_nil H_fold_left_cons].
  intros T func H_func_assoc H_func_comm.
  intros n n' ns'.
  revert n.

  induction ns' as [ | n'' ns'' IHns'']; intro n.
    rewrite ->2 H_fold_left_nil.
    reflexivity.
  rewrite H_fold_left_cons.
  rewrite IHns''.
  rewrite H_fold_left_cons.

  rewrite ->2 H_func_assoc.
  rewrite (H_func_comm n' n'').
  reflexivity.
Qed.

Proposition fold_right_and_left_on_assoc_and_comm_cons_same_result :
  forall (T : Type) (func : T -> T -> T),
    (forall n m p : T, func n (func m p) = func (func n m) p) ->
    (forall n m : T, func n m = func m n) ->
    forall (n : T) (ns : list T),
      fold_right_v0 T T n func ns = fold_left_v0 T T n func ns.
Proof.
  intros T func func_assoc func_comm n ns.
  induction ns as [ | n' ns' IHns'].
    rewrite unfold_fold_right_v0_nil.
    rewrite unfold_fold_left_v0_nil.
    reflexivity.
  rewrite unfold_fold_right_v0_cons.
  rewrite IHns'.
  rewrite unfold_fold_left_v0_cons.

  apply (fold_right_and_left_on_assoc_and_comm_cons_same_result_aux
           fold_left_v0
           fold_left_v0_fits_the_specification_of_fold_left
           T
           func
           func_assoc
           func_comm
           n
           n'
           ns').
Qed.

Proposition same_old_same_old_alternative :
  (forall n m p : nat,
     n + (m + p) = n + m + p) ->
  (forall n m : nat,
     n + m = m + n) ->
  forall ns : list nat,
    fold_right_v0 nat nat 0 plus ns = fold_left_v0 nat nat 0 plus ns.
Proof.
  intros H_plus_assoc H_plus_comm ns.
  apply (fold_right_and_left_on_assoc_and_comm_cons_same_result
           nat
           plus
           H_plus_assoc
           H_plus_comm).
Qed.

(* (Olivier, from blackboard)
   Exercise 11 might suggest things to you for your present project.

Revisit the following procedures from last week and define them using fold-right_proper-list.
  * map1 in the section on Mapping procedures over proper lists;
*)

Fixpoint odd (n : nat) :=
  match n with
    | O => false
    | 1 => true
    | S (S n) => odd n
  end.

Definition even (n : nat) :=
  negb (odd n).

Definition beq_bool (b1 b2 : bool) :=
  match b1 with
  | true => b2
  | false => negb b2
  end.

Definition beq_bool_list (l1 l2 : list bool) :=
  beq_list bool l1 l2 beq_bool.

Definition beq_list_nat_list (l1 l2 : list (list nat)) :=
  beq_list (list nat) l1 l2 beq_nat_list.

Definition unit_tests_for_map (candidate : forall T1 T2, (T1 -> T2) -> list T1 -> list T2) :=
  (beq_nat_list (candidate nat nat (fun x => x * 10) (1 :: 2 :: 3 :: nil))
                (10 :: 20 :: 30 :: nil))
  &&
  (beq_bool_list (candidate nat bool even (1 :: 2 :: 3 :: nil))
                 (false :: true :: false :: nil))
  &&
  (beq_bool_list (candidate nat bool odd (1 :: 2 :: 3 :: nil))
                 (true :: false :: true :: nil))
  &&
  (beq_bool_list (candidate bool bool negb (true :: false :: nil))
                 (false :: true :: nil))
  &&
  (beq_list_nat_list (candidate nat (list nat) (fun x => (x :: nil)) (1 :: 2 :: 3 :: nil))
                     ((1 :: nil) :: (2 :: nil) :: (3 :: nil) :: nil)).

Definition specification_of_map (map : forall T1 T2, (T1 -> T2) -> list T1 -> list T2) :=
  (forall (T1 T2 : Type) 
          (func : T1 -> T2),
     map T1 T2 func nil = nil)
  /\
  (forall (T1 T2 : Type) 
          (func : T1 -> T2)
          (v : T1)
          (vs' : list T1),
     map T1 T2 func (v :: vs') = func v :: map T1 T2 func vs').

Theorem there_is_only_one_map :
  forall (m1 m2 : forall T1 T2, (T1 -> T2) -> list T1 -> list T2),
    specification_of_map m1 ->
    specification_of_map m2 ->
    forall (T1 T2 : Type)
           (func : T1 -> T2)
           (vs : list T1),
      m1 T1 T2 func vs = m2 T1 T2 func vs.
Proof.  
  intros m1 m2 [H_m1_bc H_m1_ic] [H_m2_bc H_m2_ic].
  intros T1 T2 func vs.
  induction vs as [ | v vs' IHvs'].
    rewrite H_m2_bc.
    apply H_m1_bc.
  rewrite H_m1_ic.
  rewrite IHvs'.
  rewrite H_m2_ic.
  reflexivity.
Qed.

Definition map_v0 (T1 T2 : Type) (func : T1 -> T2)(vs : list T1) :=
  fold_right_v0 T1 (list T2) nil (fun x xs => func x :: xs) vs.

Compute unit_tests_for_map map_v0.

Proposition map_v0_fits_specification_of_map :
  specification_of_map map_v0.
Proof.
  unfold specification_of_map, map_v0; split.

  intros T1 T2 func.
  apply unfold_fold_right_v0_nil.
  
  intros T1 T2 func v vs'.
  rewrite -> unfold_fold_right_v0_cons.
  reflexivity.
Qed.

(*  map1-append in the section on Mapping procedures over proper lists, continued; *)

Definition unit_tests_for_map_append (candidate : forall T1 T2, (T1 -> (list T2)) -> list T1 -> list T2) :=
  (beq_nat_list (candidate nat nat (fun x => (x :: nil)) (1 :: 2 :: 3 :: nil))
                (1 :: 2 :: 3 :: nil))
  &&
  (beq_nat_list (candidate nat nat (fun x => (x :: x :: nil)) (1 :: 2 :: 3 :: nil))
                (1 :: 1 :: 2 :: 2 :: 3 :: 3 :: nil))
  &&
  (beq_nat_list (candidate nat nat (fun x => nil) (1 :: 2 :: 3 :: nil))
                (nil))
  &&
  (beq_nat_list (candidate nat nat (fun x => (x :: nil)) nil)
                (nil)).

Definition specification_of_map_append (map : forall T1 T2, (T1 -> (list T2)) -> list T1 -> list T2) :=
  (forall (T1 T2 : Type)
          (func : T1 -> list T2),
          map T1 T2 func nil = nil)
  /\
  (forall (T1 T2 : Type)
          (func : T1 -> list T2)
          (v : T1)
          (vs' : list T1)
          (append : forall T : Type, list T -> list T -> list T),
     specification_of_append append ->
     map T1 T2 func (v :: vs') = append T2 (func v) (map T1 T2 func vs')).

Theorem there_is_only_one_map_append :
  forall (m1 m2 : forall T1 T2, (T1 -> (list T2)) -> list T1 -> list T2)
         (append : forall T : Type, list T -> list T -> list T),
    specification_of_map_append m1 ->
    specification_of_map_append m2 ->
    specification_of_append append ->
    forall (T1 T2 : Type)
           (func : T1 -> (list T2))
           (vs : list T1),
      m1 T1 T2 func vs = m2 T1 T2 func vs.
Proof.  
  intros m1 m2 append
         [H_m1_bc H_m1_ic] [H_m2_bc H_m2_ic].
  intros S_append.
  assert (S_append_tmp := S_append).
  destruct S_append_tmp as [H_append_bc H_append_ic].
  intros T1 T2 func vs.
  
  induction vs as [ | v vs' IHvs'].
    rewrite H_m2_bc.
    apply H_m1_bc.
  rewrite -> (H_m1_ic T1 T2 func v vs' append S_append).
  rewrite -> IHvs'.
  rewrite -> (H_m2_ic T1 T2 func v vs' append S_append).
  reflexivity.
Qed.

Definition map_append_v0 (T1 T2 : Type) (func : T1 -> list T2)(vs : list T1) :=
  fold_right_v0 T1 (list T2) nil (fun x xs => append_v0 T2 (func x) xs) vs.

Compute unit_tests_for_map_append map_append_v0.

Proposition map_append_v0_fits_specification_of_map_append :
  specification_of_map_append map_append_v0.
Proof.
  unfold specification_of_map_append, map_append_v0; split.

  intros T1 T2 func.
  apply unfold_fold_right_v0_nil.
  
  intros T1 T2 func v vs' append S_append.
  rewrite -> unfold_fold_right_v0_cons.

  rewrite -> (there_is_only_one_append append append_v0).
  reflexivity.
  apply S_append.
  apply append_v0_fits_the_specification_of_append.
Qed.

(* compare fold_right and fold_left with primitive iteration and primitive
  recursion over lists *)

Definition unit_tests_for_p_i_over_lists 
  (candidate : forall T : Type, list T -> (list T -> list T) -> nat -> list T) :=
(beq_nat_list (candidate nat nil (fun ns => 1 :: ns) 0)
              nil)
&&
(beq_nat_list (candidate nat nil (fun ns => 1 :: ns) 3)
(1 :: 1 :: 1 :: nil))
&&
(* applying reverse repeatedly: *)
(beq_nat_list (candidate nat (1 :: 2 :: nil) (reverse_v0 nat) 1)
              (2 :: 1 :: nil)) 
&&
(beq_nat_list (candidate nat (1 :: 2 :: nil) (reverse_v0 nat) 2)
              (1 :: 2 :: nil))
&&
(beq_nat_list (candidate nat (1 :: 2 :: nil) (reverse_v0 nat) 3)
              (2 :: 1 :: nil))
&&
(* add to each element: *)
(beq_nat_list (candidate nat (1 :: 2 :: 3 :: nil) (fun ns => map_v0 nat nat S ns) 1)
              (2 :: 3 :: 4 :: nil))
&&
(beq_nat_list (candidate nat (1 :: 2 :: 3 :: nil) (fun ns => map_v0 nat nat S ns) 3)
              (4 :: 5 :: 6 :: nil)).

Definition specification_of_p_i_over_lists 
  (p_i_over_lists : forall T : Type, list T -> (list T -> list T) -> nat -> list T) :=
  (forall (T : Type)
          (z : list T)
          (s : list T -> list T),
     p_i_over_lists T z s 0 = z)
  /\
  (forall (T : Type)
          (z : list T)
          (s : list T -> list T)
          (n' : nat),
     p_i_over_lists T z s (S n') = s (p_i_over_lists T z s n')).

Theorem there_is_only_one_p_i_over_lists :
  forall (f g : forall T : Type, list T -> (list T -> list T) -> nat -> list T),
    specification_of_p_i_over_lists f ->
    specification_of_p_i_over_lists g ->
    forall (T : Type)
           (z : list T)
           (s : list T -> list T)
           (n : nat),
      f T z s n = g T z s n.
Proof.
  intros f g [H_f_bc H_f_ic] [H_g_bc H_g_ic].
  intros T z s n.
  induction n as [ | n' IHn'].
    rewrite H_g_bc.
    apply H_f_bc.
  rewrite H_f_ic.
  rewrite IHn'.
  rewrite H_g_ic.
  reflexivity.
Qed.

Definition p_i_over_lists_v0 (T : Type)
                             (z : list T)
                             (s : (list T -> list T))
                             (n : nat) :=
  let fix visit (n : nat) :=
    match n with
    | 0 => z
    | S n' => s (visit n')
    end
  in visit n.

Compute unit_tests_for_p_i_over_lists p_i_over_lists_v0.

Lemma unfold_p_i_over_lists_v0_bc :
  forall (T : Type)
         (z : list T)
         (s : (list T -> list T)),
    p_i_over_lists_v0 T z s 0 = z.
Proof.
  unfold_tactic p_i_over_lists_v0.
Qed.

Lemma unfold_p_i_over_lists_v0_ic :
  forall (T : Type)
         (z : list T)
         (s : (list T -> list T))
         (n' : nat),
    p_i_over_lists_v0 T z s (S n') = s (p_i_over_lists_v0 T z s n').
Proof.
  unfold_tactic p_i_over_lists_v0.
Qed.

Proposition p_i_over_lists_v0_fits_the_specification_of_p_i_over_lists :
  specification_of_p_i_over_lists p_i_over_lists_v0.
Proof.
  unfold specification_of_p_i_over_lists; split.
    exact unfold_p_i_over_lists_v0_bc.
  exact unfold_p_i_over_lists_v0_ic.
Qed.
