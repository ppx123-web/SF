Require Export Lists.

Inductive boollist : Type :=
    | bool_nil : boollist
    | bool_cons : bool -> boollist -> boollist.

Inductive list (X:Type) : Type :=
    | nil : list X
    | cons : X -> list X -> list X.

Check nil.
Check nil nat.
Check cons.
Check (cons nat 2 (cons nat 1 (nil nat))).

Fixpoint repeat (X:Type) (x: X) (count : nat) : list X := match count with
    | 0 => nil X
    | S count' => cons X x (repeat X x count' )
end.

Example test_repeat1 :
repeat nat 4 2 = cons nat 4 (cons nat 4 (nil nat)).
Proof. reflexivity. Qed.

Example test_repeat2 :
repeat bool false 1 = cons bool false (nil bool ).
Proof. reflexivity. Qed.


Module MumbleGrumble.

Inductive mumble : Type :=
  | a : mumble
  | b : mumble -> nat -> mumble
  | c : mumble.
Inductive grumble (X:Type) : Type :=
  | d : mumble -> grumble X
  | e : X -> grumble X.

(** Which of the following are well-typed elements of [grumble X] for
    some type [X]?
        - [d (b a 5)]
        - [d mumble (b a 5)]
        - [d bool (b a 5)]
        - [e bool true]
        - [e mumble (b c 0)]
        - [e bool (b c 0)]
        - [c] 
    - [d mumble (b a 5)]
    - [d bool (b a 5)]
    - [e bool true]
    - [e mumble (b c 0)]
*)

End MumbleGrumble.


Fixpoint repeat' X x count : list X :=
match count with
| 0 => nil X
| S count' => cons X x (repeat' X x count' )
end.

Check repeat'.
Check repeat.


Fixpoint repeat'' X x count : list X :=
match count with
| 0 => nil _
| S count' => cons _ x (repeat'' _ x count' )
end.

Arguments nil {X}.
Arguments cons {X} _ _ .
Arguments repeat {X} x count.


Definition list123'' := cons 1 (cons 2 (cons 3 nil )).

Fixpoint repeat''' {X : Type} (x : X ) (count : nat) : list X :=
match count with
| 0 => nil
| S count' => cons x (repeat''' x count' )
end.

Inductive list' {X :Type} : Type :=
| nil' : list'
| cons' : X -> list' -> list'.


Fixpoint app {X : Type} (l1 l2 : list X )
: (list X ) :=
match l1 with
| nil => l2
| cons h t => cons h (app t l2 )
end.
Fixpoint rev {X :Type} (l :list X ) : list X :=
match l with
| nil => nil
| cons h t => app (rev t) (cons h nil )
end.
Fixpoint length {X : Type} (l : list X ) : nat :=
match l with
| nil => 0
| cons _ l' => S (length l' )
end.
Example test_rev1 :
rev (cons 1 (cons 2 nil )) = (cons 2 (cons 1 nil )).
Proof. reflexivity. Qed.
Example test_rev2 :
rev (cons true nil ) = cons true nil.
Proof. reflexivity. Qed.
Example test_length1 : length (cons 1 (cons 2 (cons 3 nil ))) = 3.
Proof. reflexivity. Qed.

Fail Definition mynil := nil.
Definition mynil : list nat := nil.

Check @nil.
Definition mynil' := @nil nat.

Notation "x :: y" := (cons x y)
(at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y []) ..).
Notation "x ++ y" := (app x y)
(at level 60, right associativity).

Theorem app_nil_r : forall (X :Type), forall l :list X,
l ++ [] = l.
Proof.
    intros X l.
    induction l as [|h t IHl' ].
    - reflexivity.
    - simpl. rewrite IHl'. reflexivity.
Qed.

Theorem app_assoc : forall A (l m n:list A),
l ++ m ++ n = (l ++ m) ++ n.
Proof.
    intros A l m n. 
    induction l as [|h t IHl'].
    - reflexivity.
    - simpl. rewrite -> IHl'. reflexivity.
Qed.


Lemma app_length : forall (X :Type) (l1 l2 : list X ),
length (l1 ++ l2 ) = length l1 + length l2.
Proof.
    intros X l1 l2.
    induction l1 as [|n l1' IHl1'].
    - reflexivity.
    - simpl. rewrite -> IHl1'. reflexivity.
Qed.

Theorem rev_app_distr : forall X (l1 l2 : list X ),
rev (l1 ++ l2 ) = rev l2 ++ rev l1.
Proof.
    intros X l1 l2.
    induction l1 as [|h1 t1 IHl1'].
    - simpl. rewrite app_nil_r. reflexivity.
    - simpl. rewrite IHl1'. rewrite app_assoc. reflexivity.
Qed.

Theorem rev_involutive : forall X : Type, forall l : list X,
rev (rev l ) = l.
Proof.
    intros X l.
    induction l as [|h t IHL'].
    - reflexivity.
    - simpl. rewrite rev_app_distr. rewrite IHL'. simpl. reflexivity.
Qed.