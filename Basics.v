Inductive day : Type :=
| monday : day
| tuesday : day
| wednesday : day
| thursday : day
| friday : day
| saturday : day
| sunday : day.

Definition next_weekday (d:day) : day :=
match d with
| monday => tuesday
| tuesday => wednesday
| wednesday => thursday
| thursday => friday
| friday => monday
| saturday => monday
| sunday => monday
end.


Example test_next_weekday:
(next_weekday (next_weekday saturday)) = tuesday.
Proof. simpl. reflexivity. Qed. 

Inductive bool : Type :=
| true : bool
| false : bool.

Definition negb (b:bool) : bool :=
match b with
| true => false
| false => true
end.
Definition andb (b1 :bool) (b2 :bool) : bool :=
match b1 with
| true => b2
| false => false
end.
Definition orb (b1 :bool) (b2 :bool) : bool :=
match b1 with
| true => true
| false => b2
end.

Example test_orb1 : (orb true false) = true.
Proof. simpl. reflexivity. Qed.
Example test_orb2 : (orb false false) = false.
Proof. simpl. reflexivity. Qed.
Example test_orb3 : (orb false true) = true.
Proof. simpl. reflexivity. Qed.
Example test_orb4 : (orb true true) = true.
Proof. simpl. reflexivity. Qed.


Infix "&&" := andb.
Infix "||" := orb.

Example test_orb5 : false || false || true = true.
Proof. simpl. reflexivity. Qed.


Definition nandb (b1 :bool) (b2 :bool) : bool :=
orb (negb b1) (negb b2).
Example test_nandb1 : (nandb true false) = true.
Proof. simpl. reflexivity. Qed.
Example test_nandb2 : (nandb false false) = true.
Proof. simpl. reflexivity. Qed.
Example test_nandb3 : (nandb false true) = true.
Proof. simpl. reflexivity. Qed.
Example test_nandb4 : (nandb true true) = false.
Proof. simpl. reflexivity. Qed.

Definition andb3 (b1 :bool) (b2 :bool) (b3 :bool) : bool :=
(andb b1 (andb b2 b3)).
Example test_andb31 : (andb3 true true true) = true.
Proof. simpl. reflexivity. Qed.
Example test_andb32 : (andb3 false true true) = false.
Proof. simpl. reflexivity. Qed.
Example test_andb33 : (andb3 true false true) = false.
Proof. simpl. reflexivity. Qed.
Example test_andb34 : (andb3 true true false) = false.
Proof. simpl. reflexivity. Qed.

Check true.
Check (negb true).

Check negb.

Module Playground1.

Inductive nat : Type :=
| O : nat
| S : nat -> nat.

Definition pred (n : nat) : nat :=
match n with
| O => O
| S n' => n'
end.

End Playground1.

Definition minustwo (n : nat) : nat :=
match n with
| O => O
| S O => O
| S (S n') => n'
end.

Fixpoint even (n:nat) : bool :=
match n with
| O => true
| S O => false
| S (S n') => even n'
end.

(*涉及到递归定义需要使用Fixpoint*)
Check (S (S (S (S O)))).
Compute (minustwo 4).

Check S.
Check pred.
Check minustwo.
(*
These are all things that can be applied to a number to yield a number. However, there
is a fundamental difference between the first one and the other two: functions like pred and
minustwo come with computation rules – e.g., the definition of pred says that pred 2 can be
simplified to 1 – while the definition of S has no such behavior attached. Although it is like
a function in the sense that it can be applied to an argument, it does not do anything at all!
*)

Definition odd (n:nat) : bool := negb (even n).
Example test_odd1 : odd 1 = true.
Proof. simpl. reflexivity. Qed.

Example test_odd2 : odd 4 = false.
Proof. simpl. reflexivity. Qed.

Module Playground2.

Fixpoint plus (n : nat) (m : nat) : nat :=
match n with
| O => m
| S n' => S (plus n' m)
end.

Compute (plus 3 2).

Fixpoint mult (n m : nat) : nat :=
match n with
| O => O
| S n' => plus m (mult n' m)
end.
Example test_mult1 : (mult 3 3) = 9.
Proof. simpl. reflexivity. Qed.

Fixpoint minus (n m:nat) : nat := 
    match n, m with
    | O , _ => O
    | S _, O => n
    | S n', S m' => minus n' m'
    end.

End Playground2.

Fixpoint exp (base power : nat) : nat := 
    match power with
    | S power' => mult base (exp base power')
    | O => S O
end.

Fixpoint factorial (n:nat) : nat := 
match n with 
| S n' => mult n (factorial n')
| O => 1
end.
Example test_factorial1 : (factorial 3) = 6.
Proof. simpl. reflexivity. Qed.
Example test_factorial2 : (factorial 5) = (mult 10 12).
Proof. simpl. reflexivity. Qed.

Notation "x + y" := (plus x y)
(at level 50, left associativity)
: nat_scope.
Notation "x - y" := (minus x y)
(at level 50, left associativity)
: nat_scope.
Notation "x * y" := (mult x y)
(at level 40, left associativity)
: nat_scope.


Fixpoint beq_nat (n m : nat) : bool :=
match n with
| O => match m with
        | O => true
        | S m' => false
    end
| S n' => match m with
        | O => false
        | S m' => beq_nat n' m'
    end
end.


Fixpoint leb (n m : nat) : bool :=
match n with
    | O => true
    | S n' => match m with
        | O => false
        | S m' => leb n' m'
        end
end.
Example test_leb1 : (leb 2 2) = true.
Proof. simpl. reflexivity. Qed.
Example test_leb2 : (leb 2 4) = true.
Proof. simpl. reflexivity. Qed.
Example test_leb3 : (leb 4 2) = false.
Proof. simpl. reflexivity. Qed.

Definition blt_nat (n m : nat) : bool :=
((leb n m) && (negb (beq_nat n m))).
Example test_blt_nat1 : (blt_nat 2 2) = false.
Proof. simpl. reflexivity. Qed.
Example test_blt_nat2 : (blt_nat 2 4) = true.
Proof. simpl. reflexivity. Qed.
Example test_blt_nat3 : (blt_nat 4 2) = false.
Proof. simpl. reflexivity. Qed.


Theorem plus_O_n : forall n : nat, 0 + n = n.
Proof. 
    intros n.
    simpl.
    reflexivity.
Qed.


Theorem plus_1_l : forall n:nat, 1 + n = S n.
Proof.
    intros n.
    simpl.
    reflexivity.
Qed.

Theorem plus_id_example : forall n m:nat,
n = m -> n + n = m + m.
Proof.
    intros n m.
    intros H.
    rewrite -> H.
    reflexivity.
Qed.

Theorem plus_id_exercise : forall n m o : nat,
n = m -> m = o -> n + m = m + o.
Proof.
    intros n m o.
    intros H1 H2.
    rewrite -> H1.
    rewrite <- H2.
    reflexivity.
Qed.


Theorem mult_0_plus : forall n m : nat,
(0 + n) * m = n * m.
Proof.
    intros n m.
    rewrite -> plus_O_n.
    reflexivity. 
Qed.

Theorem plus_1_neq_0_firsttry : forall n : nat,
beq_nat (n + 1) 0 = false.
Proof.
    intros n.
    destruct n as [ | n'].
    - reflexivity.
    - reflexivity.
Qed.


Theorem negb_involutive : forall b : bool,
negb (negb b) = b.
Proof.
    intros b.
    destruct b.
    - simpl. reflexivity.
    - reflexivity.
Qed.

Theorem andb_commutative : forall b c, andb b c = andb c b.

Proof.
    intros b c.
    destruct b.
    - destruct c.
        -- reflexivity.
        -- reflexivity.
    - destruct c.
        -- reflexivity.
        -- reflexivity.
Qed.

Theorem andb_commutative' :forall b c, andb b c = andb c b.
Proof.
intros b c. destruct b.
{ destruct c.
{ reflexivity. }
{ reflexivity. } }
{ destruct c.
{ reflexivity. }
{ reflexivity. } }
Qed.

Theorem andb_true_elim2 : forall b c : bool, andb b c = true -> c = true.
Proof.
    intros b c.
    intros H.
    destruct b.
    - destruct c.
        -- reflexivity.   
        -- rewrite <- H. reflexivity.
    - destruct c.
        -- reflexivity.
        -- rewrite <- H. reflexivity.
Qed.

Theorem zero_nbeq_plus_1 : forall n : nat,
beq_nat 0 (n + 1) = false.
Proof.
    intros n.
    destruct n as [|n'].
    - reflexivity.
    - simpl. reflexivity.
Qed.

Theorem identity_fn_applied_twice :
forall (f : bool -> bool),
(forall (x : bool), f x = x ) ->
forall (b : bool), f (f b) = b.
Proof.
    intros f.
    intros H1.
    intros b.
    rewrite -> H1.
    rewrite -> H1.
    reflexivity.
Qed.

Theorem andb_eq_orb : forall (b c: bool), (andb b c = orb b c) -> b = c.
Proof.
    intros b c.
    destruct b.
    - destruct c.
        -- reflexivity.
        -- simpl. intros H. rewrite <- H. reflexivity.
    - destruct c.
        -- simpl. intros H. rewrite <- H. reflexivity.
        -- reflexivity.
Qed.


Inductive bin : Type :=
| BO : bin
| BD : bin -> bin
| BS : bin -> bin
.

Fixpoint incr (b0: bin) : bin :=
match b0 with
| BO => BS BO
| BD b1 => BS b1
| BS b1 => BD (incr b1)
end
.

Fixpoint bin_to_nat (b0: bin) : nat :=
match b0 with
| BO => O
| BD b1 => 2 * (bin_to_nat b1)
| BS b1 => 1 + 2 * (bin_to_nat b1)
end
.










