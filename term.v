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

Definition specification_of_append (append : forall T, list T -> list T -> list T) :=
  (forall (T : Type) (ys : list T),
     append T nil ys = ys)
  /\
  (forall (T : Type) (x : T) (xs' ys : list T),
     append T (x :: xs') ys = x :: (append T xs' ys)).

Definition specification_of_reverse (reverse : forall T, list T -> list T) :=
  forall (T : Type) (append : forall T, list T -> list T -> list T),
    specification_of_append append ->
    (reverse T nil = nil)
    /\
    (forall (x : T) (xs' : list T),
       reverse T (x :: xs') = append T (reverse T xs') (x :: nil)).

Definition reverse_v0 (T : Type) (xs : list T) :=
  fold_left_v0 T (list T) nil (fun n ns => n :: ns) xs.

Compute unit_tests_for_reverse_nat reverse_v0.

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
  unfold specification_of_reverse.
  intros T append S_append;
  assert (S_append_tmp := S_append);
  destruct S_append_tmp as [H_append_bc H_append_ic].
  
  unfold reverse_v0; split.
    (* NIL CASE *)
    apply unfold_fold_left_v0_nil.
  (* CONS CASE *)
  intros x xs'.
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

Proposition fold_right_and_left_on_assoc_and_comm_cons_same_result :
  forall (T : Type) (func : T -> T -> T),
    (forall n m p : T,
       func n (func m p) = func (func n m) p) ->
    (forall n m : T,
       func n m = func m n) ->
    forall (n : T) (ns : list T),
      fold_right_v0 T T n func ns = fold_left_v0 T T n func ns.
Proof.
Abort.

(* compare fold_right and fold_left with primitive iteration and primitive
  recursion over lists *)

(* (Olivier, from blackboard)
   Exercise 11 might suggest things to you for your present project.

Revisit the following procedures from last week and define them using fold-right_proper-list.
  * map1 in the section on Mapping procedures over proper lists;
  * map1-append in the section on Mapping procedures over proper lists, continued;
  * all-possible-environments in the section on Recursive programming: enumerating Boolean environments; and
  * powerset in the section on Recursive programming: computing the powerset of a set.
  * Make your definition go through the unit test of each of these procedures. *)
