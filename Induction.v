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


Theorem leb_refl : forall n:nat,
true = leb n n.
Proof.
    intros n.
    induction n as [|n' IHn'].
    - reflexivity.
    - simpl. rewrite <- IHn'. reflexivity.
Qed.




Theorem zero_nbeq_S : forall n:nat,
beq_nat 0 (S n) = false.
Proof.
    intros n.
    induction n as [|IHn'].
    - reflexivity.
    - reflexivity.
Qed.




Theorem andb_false_r : forall b : bool,
andb b false = false.
Proof.
    intros b.
    destruct b as [|].
    - reflexivity.
    - reflexivity.
Qed.

Theorem plus_ble_compat_l : forall n m p : nat,
leb n m = true -> leb (p + n) (p + m) = true.
Proof.
    intros n m p.
    intros H.
    induction p as [|p' IHp'].
    - simpl. rewrite -> H. reflexivity.
    - simpl. rewrite -> IHp'. reflexivity.
Qed.


Theorem S_nbeq_0 : forall n:nat,
beq_nat (S n) 0 = false.
Proof.
    intros n.
    reflexivity.
Qed.


Theorem mult_1_l : forall n:nat, 1 * n = n.
Proof.
    intros n.
    simpl.
    rewrite <- plus_n_O.
    reflexivity.
Qed.

Theorem all3_spec : forall b c : bool,
orb
(andb b c)
(orb (negb b)
(negb c))
= true.
Proof.
    intros b c.
    destruct b as [|].
    -  destruct c as [|].
        -- reflexivity.
        -- reflexivity.
    -  destruct c as [|].
        -- reflexivity.
        -- reflexivity.
Qed.


Theorem mult_plus_distr_r : forall n m p : nat,
(n + m) * p = (n * p) + (m * p).
Proof.
    intros n m p.
    induction n as [|n' IHn'].
    - reflexivity.
    - simpl. rewrite IHn'. rewrite -> plus_assoc. reflexivity.
Qed.



(* Proof.
    intros n m p.
    induction p as [|p' IHp'].
    - rewrite -> mult_0_r. rewrite -> mult_0_r. rewrite -> mult_0_r. rewrite <-  plus_n_O. reflexivity.
    - rewrite -> mult_n_Sm. rewrite -> mult_n_Sm. rewrite -> mult_n_Sm. rewrite -> IHp'. 
    assert (H1:n + n * p' + (m + m * p') = n + (n * p'+ (m + m * p'))). {
        rewrite <- plus_assoc.
        reflexivity.
        }
    rewrite H1.
    assert (H2 :n * p' + (m + m * p') = m + n * p' + m * p'). {
        rewrite plus_comm.
        assert(H3: m + n * p' + m * p' = m + (n * p' + m * p')). {
                rewrite plus_assoc.
                reflexivity.
            }
        rewrite H3.
        assert(H4: n * p' + m * p' = m * p' + n * p'). {
            rewrite plus_comm. 
            reflexivity.
            }
        rewrite H4.
        rewrite plus_assoc.
        reflexivity.
        }

    rewrite H2.
    rewrite <- plus_assoc.
    rewrite <- plus_assoc.
    reflexivity.
Qed. *)

Theorem mult_assoc : forall n m p : nat,
n * (m * p) = (n * m) * p.
Proof.
    intros n m p.
    induction n as [|n' IHn'].
    - reflexivity.
    - simpl. rewrite mult_plus_distr_r. rewrite -> IHn'. reflexivity.
Qed.


Theorem beq_nat_refl : forall n : nat,
true = beq_nat n n.
Proof.
    intros n.
    induction n as [|n' IHn'].
    - reflexivity.
    - simpl. rewrite IHn'. reflexivity.
Qed.

Theorem plus_swap' : forall n m p : nat,
n + (m + p) = m + (n + p).
Proof.
    intros n m p.
    rewrite plus_assoc. rewrite plus_assoc.
    replace (n + m) with (m + n).
    - reflexivity.
    - rewrite plus_comm.
    reflexivity.
Qed.

Theorem bin_to_nat_pres_incr : forall b,
bin_to_nat (incr b) = S (bin_to_nat b).
Proof.
    intros b.
    induction b as [|BD' IHD'| BS' IDS'].
    - reflexivity.
    - simpl. reflexivity.
    - simpl. rewrite <- plus_n_O. rewrite <- plus_n_O. rewrite IDS'. rewrite -> plus_n_Sm. simpl. reflexivity.
Qed.










