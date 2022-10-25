Add LoadPath "tmp" as src.

Require Export Basics.

Theorem plus_n_O: forall n:nat, n = n + 0.
Proof.
    intros n.
    induction n as [|n' IHn'].
    - reflexivity.
    - simpl. rewrite <- IHn'. reflexivity.
Qed.

Theorem minus_diag: forall n, minus n n = 0.
Proof.
    intros n.
    induction n as [|n' IHn'].
    - reflexivity.
    - simpl. rewrite -> IHn'. reflexivity.
Qed.

Theorem mult_0_r : forall n:nat,
n * 0 = 0.
Proof.
    intros n.
    induction n as [|n' IHn'].
    - reflexivity.
    - simpl. rewrite -> IHn'. reflexivity.
Qed.

Theorem plus_n_Sm : forall n m : nat,
S (n + m) = n + (S m).
Proof.
    intros n m.
    induction n as [|n' IHn'].
    - reflexivity.
    - simpl. rewrite <- IHn'. reflexivity.
Qed.

Theorem plus_comm : forall n m : nat,
n + m = m + n.
Proof.
    intros n m.
    induction n as [|n' IHn'].
    - rewrite <- plus_n_O. rewrite -> plus_O_n. reflexivity.
    - simpl. rewrite -> IHn'. rewrite -> plus_n_Sm.  reflexivity.
Qed.

Theorem plus_assoc : forall n m p : nat,
n + (m + p) = (n + m) + p.
Proof.
    intros n m p.
    induction n as [|n' IHn'].
    - reflexivity.
    - simpl. rewrite -> IHn'. reflexivity.
Qed.

Theorem evenb_S : forall n : nat,
evenb (S n) = negb (evenb n).
Proof.
    intros n.
    induction n as [|n' IHn'].
    - reflexivity.
    - rewrite -> IHn'. rewrite -> negb_involutive. reflexivity.
Qed.

Theorem mult_0_plus' : forall n m : nat,
(0 + n) * m = n * m.
Proof.
    intros n m.
    assert (H : 0 + n = n). { 
        reflexivity. 
    }
    rewrite -> H.
    reflexivity. 
Qed.


Theorem plus_rearrange : forall n m p q : nat,
(n + m) + (p + q) = (m + n) + (p + q).
Proof.
    intros n m p q.
    assert (H : n + m = m + n). { 
        rewrite -> plus_comm. reflexivity. 
    }
    rewrite -> H. reflexivity. 
Qed.

Theorem plus_swap : forall n m p : nat,
    n + (m + p) = m + (n + p).
Proof.
    intros n m p.
    rewrite -> plus_comm.
    rewrite <- plus_assoc.
    assert(H: p + n = n + p). {
        rewrite -> plus_comm.
        reflexivity.
    }
    rewrite -> H.
    reflexivity.
Qed.

Theorem mult_n_Sm : forall n m : nat,
  n * S m = n + n * m.
Proof.
    intros n m.
    induction n as [|n' IHn'].
    - reflexivity.
    - simpl. rewrite -> IHn'. rewrite <- plus_swap. reflexivity.
Qed.


Theorem mult_comm : forall m n : nat,
m * n = n * m.
Proof.
    intros n m.
    induction n as [|n' IHn'].
    - simpl. assert(H: m * 0 = 0). {
            induction m as [|m' IHm'].
            - reflexivity.
            - simpl. rewrite -> IHm'. reflexivity.
        }
        rewrite -> H. reflexivity.
    - simpl. rewrite -> IHn'. rewrite <- mult_n_Sm. reflexivity.
Qed.




