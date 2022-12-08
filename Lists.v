From LF Require Export Induction.

Module NatList.

Inductive natprod : Type := 
| pair : nat -> nat -> natprod.


Check (pair 3 5).

Definition fst (p : natprod) : nat := 
    match p with 
    | pair x y => x
end.

Definition snd (p : natprod) : nat := 
    match p with 
    | pair x y => y
end.

Compute (fst (pair 3 5)).

Notation "( x , y )" := (pair x y).

Compute (fst (4,5)).


Definition fst' (p : natprod ) : nat :=
match p with
| (x,y) => x
end.
Definition snd' (p : natprod ) : nat :=
match p with
| (x,y) => y
end.
Definition swap_pair (p : natprod ) : natprod :=
match p with
| (x,y) => (y,x )
end.

Theorem surjective_pairing' : forall (n m : nat),
(n,m) = (fst (n,m), snd (n,m)).
Proof.
reflexivity. Qed.

Theorem surjective_pairing : forall (p : natprod ),
p = (fst p, snd p).
Proof.
    intros p.
    destruct p as [n m]. simpl. reflexivity.
Qed.


Theorem snd_fst_is_swap : forall (p : natprod ),
(snd p, fst p) = swap_pair p.
Proof.
    intros p.
    destruct p as [n m].
    simpl.
    reflexivity.
Qed.



Theorem fst_swap_is_snd : forall (p : natprod ),
fst (swap_pair p) = snd p.
Proof.
    intros p.
    destruct p as [n m].
    simpl.
    reflexivity.
Qed.

Inductive natlist: Type := 
| nil : natlist
| cons : nat -> natlist -> natlist.

Notation " x :: l " := (cons x l).

Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil)..).

Notation "[ ]" := nil.

Fixpoint repeat (n count : nat) : natlist := 
match count with 
    | O => nil
    | S count' => n :: (repeat n count')
end.

Fixpoint length (l:natlist) : nat := 
match l with 
    | nil => O
    | h :: t => S (length t)
end.

Fixpoint app (l1 l2 : natlist) : natlist :=
match l1 with
    | nil => l2
    | h :: t => h :: (app t l2 )
end.

Notation "x ++ y" := (app x y).

Example test_app1 : [1;2;3] ++ [4;5] = [1;2;3;4;5].
Proof. reflexivity. Qed.
Example test_app2 : nil ++ [4;5] = [4;5].
Proof. reflexivity. Qed.
Example test_app3 : [1;2;3] ++ nil = [1;2;3].
Proof. reflexivity. Qed.

Definition hd (default:nat) (l :natlist) : nat :=
match l with
    | nil => default
    | h :: t => h
end.
Definition tl (l :natlist) : natlist :=
match l with
    | nil => nil
    | h :: t => t
end.
Example test_hd1 : hd 0 [1;2;3] = 1.
Proof. reflexivity. Qed.
Example test_hd2 : hd 0 nil = 0.
Proof. reflexivity. Qed.
Example test_tl : tl [1;2;3] = [2;3].
Proof. reflexivity. Qed.

Fixpoint nonzeros (l :natlist) : natlist := 
match l with 
    | nil => nil
    | h :: t => match h with
                | O => nonzeros t
                | S h' => h :: (nonzeros t)
                end
end.
Example test_nonzeros: nonzeros [0;1;0;2;3;0;0] = [1;2;3].
Proof. simpl. reflexivity. Qed.

Fixpoint oddmembers (l :natlist) : natlist :=
match l with 
    | nil => nil
    | h :: t => match (odd h) with
                | false => oddmembers t
                | true => h :: (oddmembers t)
                end
end.


Example test_oddmembers:
oddmembers [0;1;0;2;3;0;0] = [1;3].
Proof. simpl. reflexivity. Qed.


Fixpoint countoddmembers (l :natlist) : nat :=
match l with 
    | nil => O
    | h :: t => match (odd h) with
                | false => countoddmembers t
                | true => S (countoddmembers t)
                end
end.

Example test_countoddmembers1 :
countoddmembers [1;0;3;1;4;5] = 4.
Proof. simpl. reflexivity. Qed.

Example test_countoddmembers2 :
countoddmembers [0;2;4] = 0.
Proof. simpl. reflexivity. Qed.

Example test_countoddmembers3 :
countoddmembers nil = 0.
Proof. simpl. reflexivity. Qed.

Fixpoint alternate (l1 l2 : natlist) : natlist :=
match l1 with
    | nil => l2
    | h1 :: t1 => match l2 with 
                    | nil => h1 :: t1
                    | h2 :: t2 => h1 :: h2 :: alternate t1 t2
                end
end. 

Example test_alternate1 :
alternate [1;2;3] [4;5;6] = [1;4;2;5;3;6].
Proof. simpl. reflexivity. Qed.

Example test_alternate2 :
alternate [1] [4;5;6] = [1;4;5;6].
Proof. simpl. reflexivity. Qed.

Example test_alternate3 :
alternate [1;2;3] [4] = [1;4;2;3].
Proof. simpl. reflexivity. Qed.

Example test_alternate4 :
alternate [] [20;30] = [20;30].
Proof. simpl. reflexivity. Qed.


Definition bag := natlist.

Fixpoint count (v :nat) (s:bag) : nat :=
match s with 
    | nil => O
    | h :: t => match beq_nat v h with
                | true => S (count v t)
                | false => count v t
                end
end.


Example test_count1 : count 1 [1;2;3;1;4;1] = 3.
Proof. simpl. reflexivity. Qed.

Example test_count2 : count 6 [1;2;3;1;4;1] = 0.
Proof. simpl. reflexivity. Qed.


Definition sum : bag -> bag -> bag :=
app.

Example test_sum1 : count 1 (sum [1;2;3] [1;4;1]) = 3.
Proof. simpl. reflexivity. Qed.

Definition add (v :nat) (s:bag) : bag :=
v :: s.

Example test_add1 : count 1 (add 1 [1;4;1]) = 3.
Proof. simpl. reflexivity. Qed.

Example test_add2 : count 5 (add 1 [1;4;1]) = 0.
Proof. simpl. reflexivity. Qed.

Definition member (v :nat) (s:bag) : bool :=
blt_nat 0 (count v s).

Example test_member1 : member 1 [1;4;1] = true.
Proof. simpl. reflexivity. Qed.

Example test_member2 : member 2 [1;4;1] = false.
Proof. simpl. reflexivity. Qed.


Fixpoint remove_one (v :nat) (s:bag) : bag :=
match s with
    | nil => nil
    | h :: t => match beq_nat h v with 
                | true => t
                | false => h :: remove_one v t
                end
end.


Example test_remove_one1 :
count 5 (remove_one 5 [2;1;5;4;1]) = 0.
Proof. simpl. reflexivity. Qed.

Example test_remove_one2 :
count 5 (remove_one 5 [2;1;4;1]) = 0.
Proof. simpl. reflexivity. Qed.

Example test_remove_one3 :
count 4 (remove_one 5 [2;1;4;5;1;4]) = 2.
Proof. simpl. reflexivity. Qed.

Example test_remove_one4 :
count 5 (remove_one 5 [2;1;5;4;5;1;4]) = 1.
Proof. simpl. reflexivity. Qed.

Fixpoint remove_all (v :nat) (s:bag) : bag :=
    match s with
    | nil => nil
    | h :: t => match beq_nat h v with 
                | true => remove_all v t
                | false => h :: remove_all v t
                end
end.


Example test_remove_all1 : count 5 (remove_all 5 [2;1;5;4;1]) = 0.
Proof. simpl. reflexivity. Qed.

Example test_remove_all2 : count 5 (remove_all 5 [2;1;4;1]) = 0.
Proof. simpl. reflexivity. Qed.

Example test_remove_all3 : count 4 (remove_all 5 [2;1;4;5;1;4]) = 2.
Proof. simpl. reflexivity. Qed.

Example test_remove_all4 : count 5 (remove_all 5 [2;1;5;4;5;1;4;5;1;4]) = 0.
Proof. simpl. reflexivity. Qed.

Fixpoint subset (s1 :bag) (s2 :bag) : bool :=
match s1 with 
    | nil => true
    | h :: t => match leb (count h s1)  (count h s2) with 
                | true => subset t s2
                | false => false
                end
end.


Example test_subset1 : subset [1;2] [2;1;4;1] = true.
Proof. simpl. reflexivity. Qed.

Example test_subset2 : subset [1;2;2] [2;1;4;1] = false.
Proof. simpl. reflexivity. Qed.

Theorem bag_sum_nil: forall (b : bag), sum b [] = b .
Proof.
    induction b as [|h' t' IHb'].
    - reflexivity.
    - simpl. rewrite IHb'. reflexivity.
Qed.

Theorem leb_n_Sn: forall n : nat, leb n (S n) = true.
Proof.
    induction n as [|n' IHn'].
    - reflexivity.
    - simpl. rewrite IHn'. reflexivity.
Qed.


Theorem bag_theorem1 : forall v1 v2 : nat, forall b: bag, leb (count v1 b) (count v1 (add v2 b)) = true. 
Proof.
    intros v1 v2 b.
    induction b as [|h t IHb'].
    - reflexivity.
    - simpl. destruct (beq_nat v1 h) as [|].
        -- destruct (beq_nat v1 v2) as [|].
            --- simpl. rewrite -> leb_n_Sn. reflexivity.
            --- simpl. rewrite <- leb_refl. reflexivity.
        -- destruct (beq_nat v1 v2) as [|].
            --- simpl. rewrite -> leb_n_Sn. reflexivity.
            --- simpl. rewrite <- leb_refl. reflexivity.
Qed.

Theorem bag_theorem2 : forall v : nat, forall b1 b2 : bag, leb (count v b1) (count v (sum b1 b2)) = true. 
Proof.
    intros v b1 b2.
    induction b1 as [|h1 b1 IHb1].
    - simpl. reflexivity.
    - simpl. destruct (beq_nat v h1) as [|].
        -- simpl. rewrite IHb1. reflexivity.
        -- rewrite IHb1. reflexivity.
Qed.

(* Theorem bag_theorem3 : forall v : nat, forall b1 b2, (member v b1) && (member v b2) = true -> subset b1 b2 = true .
Proof.
    intros v.
    intros b1 b2.
    destruct (member v b1) as [|].
    - destruct (member v b2) as [|].
        -- simpl. induction b1 as [|h1 t1 IHb1].
            --- reflexivity.
            --- assert(H1 : member v b2 = true). {
                reflexivity.
                }
Qed. *)

(* 
Theorem bag_theorem3 : forall v : nat, forall b , subset b (v :: b) = true.
Proof.
    intros v b.
    induction b

Theorem bag_theorem3 : forall b , subset b b = true.
Proof.
    intros b.
    induction b as [|h t IHb].
    - reflexivity.
    - simpl. rewrite <- beq_nat_refl. simpl. rewrite <- leb_refl. simpl.



Theorem bag_theorem3 : forall b1 b2 : bag, subset b1 (sum b1 b2) = true.
Proof.
    induction b1 as [|h1 t1 IHb].
    - simpl. reflexivity.
    - simpl. rewrite <- beq_nat_refl. simpl. intros b2. rewrite bag_theorem2.
        assert(H1 : leb (count h1 t1) (count h1 (sum t1 b2)) = true). { 
            rewrite bag_theorem2. reflexivity
        }
        
        rewrite -> bag_theorem2.  destruct (beq_nat h1 v) as [|].
        -- simpl. rewrite leb_n_Sn.


Theorem bag_theorem3 : forall v : nat, forall b1 b2 , subset b1 (v :: sum b1 b2) = subset b1 (sum b1 b2).
Proof.
    intros v b1 b2.
    induction b2 as [|h2 t2 IHb2].
    - rewrite bag_sum_nil. rewrite reflexivity.
    - simpl. rewrite <- beq_nat_refl. simpl. destruct (beq_nat h1 v) as [|].
        -- rewrite -> bag_theorem2. rewrite <- leb_n_Sn.

Theorem bag_theorem : forall b1 b2 : bag, subset b1 (sum b1 b2) = true.
Proof.
    intros b1 b2.
    induction b1 as [|h1 t1 IHb1].
    -- simpl. reflexivity.
    -- simpl. rewrite <- beq_nat_refl. simpl. rewrite bag_theorem2. simpl. *)

Theorem nil_app: forall l : natlist, [] ++ l = l.
Proof.
    reflexivity.
Qed.

Theorem tl_length_pred : forall l :natlist,
pred (length l ) = length (tl l ).
Proof.
    intros l. destruct l as [| n l' ].
    - reflexivity.
    - reflexivity. 
Qed.

Theorem app_assoc : forall l1 l2 l3 : natlist,
(l1 ++ l2 ) ++ l3 = l1 ++ (l2 ++ l3 ).
Proof.
    intros l1 l2 l3. 
    induction l1 as [| n l1' IHl1' ].
    - reflexivity.
    - simpl. rewrite ! IHl1'. reflexivity.
Qed.

Fixpoint rev (l :natlist) : natlist :=
match l with
    | nil => nil
    | h :: t => rev t ++ [h]
end.

Example test_rev1 : rev [1;2;3] = [3;2;1].
Proof. reflexivity. Qed.
Example test_rev2 : rev nil = nil.
Proof. reflexivity. Qed.


Theorem app_length : forall l1 l2 : natlist,
length (l1 ++ l2 ) = (length l1 ) + (length l2 ).
Proof.
    intros l1 l2.
    induction l1 as [|n l1' IHl1'].
    - reflexivity.
    - simpl. rewrite -> IHl1'. reflexivity.
Qed.


Theorem rev_length_firsttry : forall l : natlist,
length (rev l ) = length l.
Proof.
    intros l.
    induction l as [|n l' IHl'].
    - reflexivity.
    - simpl. rewrite -> app_length. rewrite -> plus_comm. rewrite -> IHl'. reflexivity.
Qed.

Theorem app_nil_r : forall l : natlist,
l ++ [] = l.
Proof.
    induction l as [|n l' IHl'].
    - reflexivity.
    - simpl. rewrite IHl'. reflexivity.
Qed.

Theorem rev_add_n: forall l : natlist, forall n : nat, rev(l ++ [n]) = [n] ++ rev l.
Proof.
    intros l n.
    induction l as [|h l' IHl'].
    - reflexivity.
    - simpl. rewrite IHl'. reflexivity.
Qed.



Theorem rev_involutive : forall l : natlist,
rev (rev l ) = l.
Proof.
    intros l.
    induction l as [|n l' IHl'].
    - reflexivity.
    - simpl. rewrite rev_add_n. rewrite IHl'. reflexivity.
Qed.

Theorem app_assoc4 : forall l1 l2 l3 l4 : natlist,
l1 ++ (l2 ++ (l3 ++ l4 )) = ((l1 ++ l2 ) ++ l3 ) ++ l4.
Proof.
    intros l1 l2 l3 l4.
    rewrite app_assoc.
    rewrite app_assoc.
    reflexivity.
Qed.

Lemma nonzeros_app : forall l1 l2 : natlist,
nonzeros (l1 ++ l2 ) = (nonzeros l1 ) ++ (nonzeros l2 ).
Proof.
    intros l1 l2.
    induction l1 as [|n l1' IHl1'].
    - reflexivity.
    - simpl. destruct n as [|n'].
        -- rewrite IHl1'. reflexivity.
        -- rewrite IHl1'. simpl. reflexivity.
Qed.


Fixpoint beq_natlist (l1 l2 : natlist) : bool :=
match l1 with
| nil => match l2 with 
            | nil => true
            | n2::l2' => false
        end
| n1::l1' => match l2 with 
            | nil => false
            | n2::l2' => match beq_nat n1 n2 with
                    | true => beq_natlist l1' l2'
                    | false => false
                    end
            end
end.

Example test_beq_natlist1 :
(beq_natlist nil nil = true).
Proof. reflexivity. Qed.

Example test_beq_natlist2 :
beq_natlist [1;2;3] [1;2;3] = true.
Proof. reflexivity. Qed.

Example test_beq_natlist3 :
beq_natlist [1;2;3] [1;2;4] = false.
Proof. reflexivity. Qed.

Theorem beq_natlist_refl : forall l :natlist,
true = beq_natlist l l.
Proof.
    intros l.
    induction l as [|n l' IHl'].
    - reflexivity.
    - simpl. rewrite <- beq_nat_refl. rewrite IHl'. reflexivity.
Qed.


Theorem count_member_nonzero : forall (s : bag),
leb 1 (count 1 (1 :: s)) = true.
Proof.
    intros s.
    induction s as [|h t IHs'].
    - reflexivity.
    - simpl. reflexivity.
Qed.

Theorem ble_n_Sn : forall n,
leb n (S n) = true.
Proof.
    intros n. induction n as [| n' IHn' ].
    - simpl. reflexivity.
    - simpl. rewrite IHn'. reflexivity. 
Qed.

Theorem remove_decreases_count: forall (s : bag),
leb (count 0 (remove_one 0 s)) (count 0 s) = true.
Proof.
    induction s as [| h t IHs'].
    - reflexivity.
    - simpl. destruct h as [| h'].
        -- simpl. rewrite ble_n_Sn. reflexivity.
        -- simpl. rewrite IHs'. reflexivity.
Qed.

Theorem rev_injective: forall (l1 l2 : natlist), rev l1 = rev l2 -> l1 = l2.
Proof.
    intros l1 l2 H.
    replace l1 with (rev (rev l1)).
    replace l2 with (rev (rev l2)).
    - rewrite H. reflexivity.
    - rewrite rev_involutive. reflexivity.
    - rewrite rev_involutive. reflexivity.
Qed.


Inductive natoption : Type :=
| Some : nat -> natoption
| None : natoption.

Fixpoint nth_error (l :natlist) (n:nat) : natoption :=
match l with
| nil => None
| a :: l' => match beq_nat n O with
        | true => Some a
        | false => nth_error l' (pred n)
        end
end.
Example test_nth_error1 : nth_error [4;5;6;7] 0 = Some 4.
Proof. reflexivity. Qed.
Example test_nth_error2 : nth_error [4;5;6;7] 3 = Some 7.
Proof. reflexivity. Qed.
Example test_nth_error3 : nth_error [4;5;6;7] 9 = None.
Proof. reflexivity. Qed.

Definition option_elim (d : nat) (o : natoption) : nat :=
match o with
| Some n' => n'
| None => d
end.

Definition hd_error (l : natlist) : natoption :=
match l with 
| nil => None
| n :: t => Some n
end.

Example test_hd_error1 : hd_error [] = None.
Proof. reflexivity. Qed.
Example test_hd_error2 : hd_error [1] = Some 1.
Proof. reflexivity. Qed.
Example test_hd_error3 : hd_error [5;6] = Some 5.
Proof. reflexivity. Qed.


Theorem option_elim_hd : forall (l :natlist) (default:nat),
hd default l = option_elim default (hd_error l ).
Proof.
    intros l default.
    destruct l as [|h t].
    - reflexivity.
    - simpl. reflexivity.
Qed.

Inductive id : Type :=
| Id : nat -> id.

Definition beq_id x1 x2 :=
match x1, x2 with
| Id n1, Id n2 => beq_nat n1 n2
end.

Theorem beq_id_refl : forall x, true = beq_id x x.
Proof.
    intros x.
    destruct x as [].
    simpl. rewrite <- beq_nat_refl. reflexivity.
Qed.

End NatList.

Module PartialMap.
Import NatList.

Inductive partial_map : Type :=
| empty : partial_map
| record : id -> nat -> partial_map -> partial_map.

Definition update (d : partial_map) (key : id) (value : nat) : partial_map :=
record key value d.


Fixpoint find (key : id ) (d : partial_map) : natoption :=
match d with
| empty => None
| record k v d' => if beq_id key k
                    then Some v
                    else find key d'
end.

Theorem update_eq :
forall (d : partial_map) (k : id ) (v : nat),
find k (update d k v ) = Some v.
Proof.
    intros d k v.
    destruct d as [|id' n' d'].
    - simpl. rewrite <- beq_id_refl. reflexivity.
    - simpl. rewrite <- beq_id_refl. reflexivity.
Qed.

Theorem update_neq :
forall (d : partial_map) (m n : id ) (o: nat),
beq_id m n = false -> find m (update d n o) = find m d.
Proof.
    intros d m n o H.
    simpl. rewrite H. reflexivity.
Qed.

(* Inductive baz : Type :=
| Baz1 : baz -> baz
| Baz2 : baz -> bool -> baz.
How many elements does the type baz have? zero *)

Definition injective : forall {t1 t2}, (t1 -> t2) -> Prop := fun t1 t2 f1 => forall x1 x2, f1 x1 = f1 x2 -> x1 = x2.

Definition surjective : forall {t1 t2}, (t1 -> t2) -> Prop := fun t1 t2 f1 => forall x1, exists x2, f1 x2 = x1.

Definition bijective : forall {t1 t2}, (t1 -> t2) -> Prop := fun t1 t2 f1 => injective f1 /\ surjective f1.

Inductive baz : Type :=
    | x : baz -> baz
    | y : baz -> bool -> baz.

Theorem baz_False : baz -> False. 
Proof. 
    induction 1; 
    firstorder. 
Qed.

Goal exists f1 : baz -> False, bijective f1.
Proof.
exists baz_False. unfold bijective, injective, surjective. firstorder.
assert (H2 := baz_False x1). firstorder.
assert (H2 := x1). firstorder.
Qed.

End PartialMap.