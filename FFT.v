From VerifiedCalculus Require Export PolynomialModels.
From VerifiedCalculus Require Export PolynomialModelAdd.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Arith.
Require Export Reals.
Require Import Lia.
Require Import Lra.
Require Import Ring.
From Coquelicot Require Import Complex.
Context `{F : Type} `{FltF : Float F}.
Open Scope R_scope.
Definition i := sqrt(-1).
Definition nth_unit_root(n:nat): C :=
  cos((2*PI)/n) + i * sin ((2*PI)/n).
Definition Even:= Nat.Even.
Definition Odd:= Nat.Odd.
(*Fixpoint even (n:nat) : bool :=
  match n with
  | O => true
  | S O => false
  | S (S n') => even n'
  end.

Fixpoint odd(n:nat) : bool :=
 match n with
 | O => false
 | S O => true
 | S(S n') => odd n'
end.*)

Lemma even_or_odd: forall n, Even n \/ Odd n.
Proof. 
  intros n. unfold Even, Odd. induction n. 
  - unfold Nat.Even, Nat.Odd. 
    left. 
    exists 0%nat. 
    reflexivity.
  - rewrite -> Nat.Even_succ, 
    Nat.Odd_succ. 
    tauto. Qed.

Fixpoint even_poly(p:list(nat*F)): list(nat*F) :=
 match p with
  | nil => nil
  | a1::p' => if Nat.even(fst(a1)) then a1::even_poly(p') else even_poly(p')
  end.

Fixpoint even_poly_R(p:list(nat*R)): list(nat*R) :=
 match p with
  | nil => nil
  | a1::p' => if Nat.even(fst(a1)) then a1::even_poly_R(p') else even_poly_R(p')
  end.


Fixpoint odd_poly(p:list(nat*F)): list(nat*F) :=
  match p with
  | nil => nil
  | a1::p' => if Nat.odd(fst(a1)) then a1::odd_poly(p') else odd_poly(p')
end.

Fixpoint odd_poly_R(p:list(nat*R)): list(nat*R) :=
  match p with
  | nil => nil
  | a1::p' => if Nat.odd(fst(a1)) then a1::odd_poly_R(p') else odd_poly_R(p')
end.


Lemma add_recombination: forall p1 p2 x,
Pax_eval p1 x + Pax_eval p2 x = Pax_eval (p1++p2) x.
Proof. 
  intros. induction p1.
 - simpl. lra.
 - simpl. lra.
Qed.

(*Lemma even_odd_recomb: forall p x,
Pax_eval (even_poly p) x + Pax_eval(odd_poly p) x = Pax_eval(even_poly p ++ odd_poly p) x.
Proof. intros. apply add_recombination. Qed.*)

Lemma even_plus_odd: forall p x,
Pax_eval (even_poly p) x + Pax_eval (odd_poly p) x = Pax_eval p x.
Proof. 
  intros. 
  rewrite -> add_recombination. 
  induction p.
- simpl. lra. 
- simpl. destruct (Nat.even (fst a)) eqn:Heven. 
  + rewrite <- Nat.negb_even. 
    rewrite -> Heven. 
    simpl; lra.
  + rewrite <- Nat.negb_even.
    rewrite -> Heven. 
    simpl. 
    assert(even_poly p = even_poly(a::p)). 
      simpl. 
      rewrite -> Heven. 
      tauto. 
    rewrite <- add_recombination. 
    rewrite -> Pax_eval_cons. rewrite <- IHp. 
    rewrite <- add_recombination. lra. 
Qed.



Fixpoint max_degree (p : list (nat * F)) : nat :=
  match p with
  | nil => 0
  | (n, _) :: t => Nat.max n (max_degree t)
  end.

Lemma max_degree_decreasing : forall p a,
Nat.le (max_degree(p)) (max_degree(a::p)).
Proof.
  intros. 
  destruct (a). simpl.
  induction p. 
  - simpl.  
    rewrite -> Nat.max_0_r. 
    apply Nat.le_0_l. 
  - apply Nat.le_max_r.
Qed.

Fixpoint find_coeff (n : nat) (p : list (nat * F)): F :=
  match p with
  | nil => Fnull
  | (m, c) :: t => if Nat.eqb m n then c else find_coeff n t
  end.

Fixpoint find_coeff_R (n : nat) (p : list (nat * R)): R :=
  match p with
  | nil => 0
  | (m, c) :: t => if Nat.eqb m n then c else find_coeff_R n t
  end.


Fixpoint PinjR(p:list(nat*F)) : list (nat*R) :=
  match p with
  | nil => nil
  | a1::p' => (fst(a1),FinjR(snd a1)) :: PinjR p'
end.

Fixpoint PaxR_eval (p:list (nat*R)) (x:R) : R :=
    match p with
    | nil => 0
    | fn :: p0 =>  ((snd fn) * (pow x (fst fn))) + PaxR_eval p0 x
    end.

Definition el_sparse(x:R)(d:nat)(c: R): R :=
  c * (pow x d).

Definition sum_R(p:list R):R :=
  fold_right Rplus 0 p.

Definition sum_fun(p:list(nat*R))(f: (nat*R) -> R): R :=
  sum_R (map (fun a => f a) p).

Lemma PaxR_correct: forall p x,
 Pax_eval p x = PaxR_eval (PinjR p) x.
Proof. 
  intros; unfold PinjR; induction p.
  - simpl; auto.
  - rewrite -> Pax_eval_cons.
      simpl; lra. 
Qed.
Lemma sum_fun2: forall (p:list(nat*R))(f:(nat*R) -> (nat*R))(g: (nat*R) -> R),
  sum_fun (map f p) g = sum_R (map(fun x => g (f x)) p).
Proof.
intros.
unfold sum_fun.
rewrite -> map_map.
auto.
Qed.
Definition eval_sum_fun(p:list(nat*R)) x: R :=
sum_fun p (fun a => el_sparse x (fst a)(snd a)).
Lemma sum_eq_eval: forall p x,
  eval_sum_fun p x= PaxR_eval p x.
Proof.
intros.
induction p.
  - simpl.
    unfold sum_fun. simpl. auto.
  - simpl.
    unfold sum_fun. simpl. rewrite <- IHp.
    unfold sum_fun. unfold el_sparse. auto.
Qed.


Lemma addR_recombination: forall p1 p2 x,
PaxR_eval p1 x + PaxR_eval p2 x = PaxR_eval (p1++p2) x.
Proof.
  intros; induction p1.
   - simpl. lra.
   - simpl. lra.
Qed.

Fixpoint max_degree_R (p : list (nat * R)) : nat :=
  match p with
  | nil => 0
  | (n, _) :: t => Nat.max n (max_degree_R t)
  end.

Lemma max_degree_R_decreasing : forall p a,
Nat.le (max_degree(p)) (max_degree(a::p)).
Proof.
  intros; destruct (a). simpl.
  induction p. 
  - simpl.  rewrite -> Nat.max_0_r. apply Nat.le_0_l. 
  - apply Nat.le_max_r.
Qed.

Lemma PaxR_eval_cons: forall (p1 : list (nat * R)) (a0:nat*R) (y : R),
  PaxR_eval (a0 :: p1) y =
  snd a0 * y ^ fst a0 + PaxR_eval p1 y.
Proof.
  intros; simpl; reflexivity.
Qed.

Lemma even_plus_odd_R: forall p x,
PaxR_eval (odd_poly_R p) x + PaxR_eval (even_poly_R p) x = PaxR_eval p x.
Proof. 
  intros; induction p.
  - simpl. lra.
  - simpl.
    destruct (Nat.even (fst a)) eqn:Heven. 
    + rewrite <- Nat.negb_even.
      rewrite -> Heven. 
      simpl; lra. 
    + rewrite <- Nat.negb_even.
      rewrite -> Heven.
      simpl; lra.
Qed.



Definition dense_poly := list R.


Fixpoint dense_to_sparse' (d:nat)(p:dense_poly) : list(nat*R) :=
    match p with
    | nil => nil
    | fn :: p0 => (d,fn) :: dense_to_sparse' (S d) p0
    end.

Fixpoint Pdense_eval'(d:nat) (p: dense_poly) (x:R) : R :=
  match p with
  | nil => 0
  | fn :: p0 => fn * (pow x d) + Pdense_eval' (S d) p0 x
  end.

Definition Pdense_eval(p:dense_poly) (x:R) : R :=
  Pdense_eval' 0 p x.
Definition dense_to_sparse(p:dense_poly):list(nat*R) :=
  dense_to_sparse' 0 p.

Definition dense_head (p:dense_poly) : R :=
  match p with
  | nil => 0
  | a::p' => a
  end.

Lemma Peval_dts': forall p d x,
PaxR_eval (dense_to_sparse' d p) x = Pdense_eval' d p x.
Proof.
  intros p. 
  induction p as [|fn p].
  - auto.
  - simpl; intros.
    rewrite -> IHp.
    lra.
Qed.
Lemma Peval_dts: forall p x,
PaxR_eval (dense_to_sparse p) x = Pdense_eval p x.
Proof.
  intros. 
  unfold dense_to_sparse,Pdense_eval. 
  apply Peval_dts'.
 Qed.
Lemma Pdense_inductive_step: forall p x n,
  x * Pdense_eval' n p x = Pdense_eval' (S n) p x.
Proof.
  intros p x; induction p.
    - unfold Pdense_eval'.
      intros n; lra.
    - simpl; intros n. 
      assert (x*(a*x^n + Pdense_eval' (S n) p x) = 
              a*(x*x^n) + x*Pdense_eval'(S n) p x) by lra.
      rewrite -> H.
      f_equal; apply IHp.
 Qed.

 
Fixpoint degree_poly' (n:nat)(p:dense_poly) : nat :=
match p with
  | nil => n
  | c::p' => degree_poly'(S n)(p')
end.

Definition degree_poly (p:dense_poly) : nat :=
 degree_poly' O p.


Lemma degree_succ: forall p n,
  S (degree_poly' n p) = degree_poly' (S n) p.
Proof.
  induction p.
  - simpl; auto.
  - intros; simpl. 
    apply IHp. 
Qed.

Lemma degree_length: forall p,
length p = degree_poly p.
Proof.
unfold degree_poly.
induction p.
  - simpl. auto.
  - simpl. 
    rewrite -> IHp.
    apply degree_succ.
Qed.
Lemma degree_add: forall a p,
  degree_poly (a::p) = S(degree_poly p).
Proof.
  intros; unfold degree_poly; induction p.
    - simpl; auto.
    - simpl; symmetry; apply degree_succ. 
Qed. 

Lemma degree_nil: forall p,
  p = nil <-> degree_poly p = O.
Proof.
  split. 
    - intros. unfold degree_poly. destruct p.
      + simpl; reflexivity.
      + discriminate H.
    - unfold degree_poly. intros. induction p.
      + simpl; auto.
      + rewrite -> degree_add in H. 
        discriminate H.
Qed.

Lemma degree_one_eval: forall x p,
 degree_poly p = 1%nat -> Pdense_eval p x = dense_head p.
Proof. 
  intros; destruct p.
    - discriminate H.
    - rewrite -> degree_add in H.
      injection H as H0.
      assert(p = nil) by (apply degree_nil; exact H0).
      rewrite -> H.
      unfold Pdense_eval; simpl. 
      lra.
Qed.

Fixpoint even_poly_D'(d:nat)(p:dense_poly): dense_poly :=
 match p with
  | nil => nil
  | a1::p' => if Nat.even(d) then a1::even_poly_D' (S d) p' else even_poly_D'(S d) p'
  end.

Fixpoint odd_poly_D'(d:nat)(p:dense_poly): dense_poly :=
  match p with
  | nil => nil
  | a1::p' => if Nat.odd(d) then a1::odd_poly_D'(S d) p' else odd_poly_D'(S d) p'
end.

Definition even_poly_D(p:dense_poly): dense_poly :=
  even_poly_D' 0 p.
Definition odd_poly_D(p:dense_poly): dense_poly :=
  odd_poly_D' 0 p.

Lemma even_succ_odd:  forall p n,
even_poly_D' n p = odd_poly_D' (S n) p.
Proof. 
  intros p; induction p. 
     - auto. 
     - simpl; intros n. 
       rewrite -> Nat.odd_succ.
       destruct (Nat.even n) eqn: E.
        + f_equal; apply IHp.
        + apply IHp.
Qed.

Lemma odd_succ_even:  forall p n,
odd_poly_D' n p = even_poly_D' (S n) p.
Proof.
  intros p; induction p. 
     - auto. 
     - intros n; induction n.
        + simpl. apply IHp.
        + simpl.
          rewrite -> Nat.odd_succ. 
          destruct(Nat.even n) eqn: E.
            * f_equal; apply IHp.
            * apply IHp. 
Qed.

Lemma pdense_eval_scale : forall (p : list R) (x : R) (d:nat),
  Pdense_eval' (S d) p x = x * Pdense_eval' d p x.
Proof.
  intros p x.
  induction p as [| fn p IHp].
  - simpl. intros. 
    ring.
  - simpl. intros. 
    rewrite IHp.
    ring_simplify. 
    reflexivity.
Qed.

Lemma pdense_eval_add : forall a p x, Pdense_eval(a::p)x = a + x*Pdense_eval(p)x.
Proof.
  intros; unfold Pdense_eval; simpl.
  f_equal.
    - lra.
    - apply pdense_eval_scale.
Qed.

Lemma even_and_odd_D': forall p x,
 Pdense_eval (even_poly_D' 0 p) (x^2) + x*Pdense_eval(odd_poly_D' 0 p) (x^2) = Pdense_eval p x.
Proof. 
  intros. induction p.
   - unfold Pdense_eval. simpl. 
     lra.
   - simpl. 
     rewrite <- even_succ_odd. 
     rewrite <- odd_succ_even. 
     repeat rewrite -> pdense_eval_add. 
     rewrite <- IHp. 
     simpl. 
     lra. 
Qed.

Lemma even_and_odd_D: forall p x,
 Pdense_eval (even_poly_D p) (x^2) + x*Pdense_eval(odd_poly_D p) (x^2) = 
 Pdense_eval p x.
Proof. 
  apply even_and_odd_D'. 
Qed. 
  

     
      
          

Lemma inductive_even : forall a p,
even_poly_D (a::p) = a :: odd_poly_D p.
Proof.
  intros; unfold even_poly_D, odd_poly_D; simpl.
  rewrite <- odd_succ_even. 
  auto. 
Qed.

Lemma inductive_odd : forall a p,
odd_poly_D (a::p) = even_poly_D p.
Proof. 
  intros; unfold even_poly_D, odd_poly_D; simpl. 
  rewrite <- even_succ_odd. 
  auto. 
Qed.
Search(repeat).
Fixpoint sparse_to_dense' (d:nat) (p:list(nat*R)) : dense_poly :=
  match p with
  |nil => nil
  |a::p' => (repeat 0 ((fst a)-d)) ++ snd(a) :: sparse_to_dense' (S(fst a))p'
end.

Definition sparse_to_dense (p : list(nat*R)) : dense_poly :=
  sparse_to_dense' 0 p.

Lemma std_add: forall p n a,
sparse_to_dense' n (a::p) = repeat 0 (fst a - n) ++ snd(a) :: sparse_to_dense' (S(fst a))p.
Proof.
intros. simpl. auto.
Qed.
Lemma std_step: forall p n a,
is_sorted_fst p -> Nat.lt n (fst a) -> 
sparse_to_dense' n (a::p) = 0::sparse_to_dense'(S n) (a::p).
Proof.
intros.
destruct (fst a) eqn: fa.
   - exfalso; lia.
   - simpl. replace(repeat 0 (fst a - 0)) with (0:: repeat 0 (fst a - 1)).
     rewrite -> fa.
     assert(repeat 0 (S n0 - n) = 0:: repeat 0 (S n0 - S n)).
     rewrite -> repeat_cons.
     replace(0::nil) with (repeat 0 1).
     rewrite <- repeat_app.
     f_equal. lia.
     auto.
     rewrite -> H1.
     simpl. auto.
     rewrite -> repeat_cons.
     replace(0::nil) with (repeat 0 1) by auto.
     rewrite <- repeat_app.
     f_equal; lia.  
Qed.
Lemma std_succ: forall p n,
p<> nil -> is_sorted_fst p -> Nat.lt n (fst (hd (O,0) p)) -> 
sparse_to_dense' n (p) = 0::sparse_to_dense'(S n) (p).
Proof.
intros.
destruct (fst(hd (O,0) p)) eqn: fa.
   - exfalso; lia.
   - simpl. 
     induction p.
     + exfalso; auto.
     + apply std_step. 
       apply is_sorted_fst_cons_inv in H0.
       auto.
       simpl in fa.
       rewrite -> fa.
       auto.
Qed.

Lemma sorted_impl_nonzero:   forall a p,
  p<>nil -> is_sorted_fst(a::p) -> Nat.lt(fst a)(fst (hd (1%nat, 0) p)).
Proof.
intros.
destruct p.
  - exfalso; auto.
  - Search(is_sorted_fst).
    apply is_sorted_fst_cons_lt in H0.
    simpl.
    lia.
Qed.

Lemma peval_std_succ: forall p n x,
is_sorted_fst p -> Nat.lt n (fst (hd (1%nat,0) p)) -> 
Pdense_eval(sparse_to_dense' n (p))x = x*Pdense_eval(sparse_to_dense'(S n) (p))x.
Proof.
intros.
destruct (fst(hd (1%nat,0) p)) eqn: fa.
   - exfalso; lia.
   - simpl. 
     induction p.
     + simpl. unfold Pdense_eval. simpl. lra.
     + replace(Pdense_eval (sparse_to_dense' n (a::p))) with (Pdense_eval (0::sparse_to_dense'(S n) (a::p))).
       rewrite -> pdense_eval_add. lra.
       f_equal.
       symmetry; apply std_step.
       apply is_sorted_fst_cons_inv in H. auto.
       simpl in fa.
       lia.
Qed.

Lemma pdense_eval_zeroes: forall n x,
Pdense_eval (repeat 0 n) x = 0.
Proof.
induction n.
  - intros. unfold Pdense_eval. auto. 
  - intros. unfold Pdense_eval. simpl.
    rewrite -> pdense_eval_scale.
    rewrite -> IHn.
    lra.
Qed.

Lemma eval_zeroes_appended: forall n p x,
Pdense_eval (repeat 0 n ++ p) x =
x^n * Pdense_eval p x.
Proof.
unfold Pdense_eval.
induction n.
  - intros.
    simpl.
    lra.
  - intros.
    simpl.
    rewrite -> pdense_eval_scale.
    rewrite -> IHn.
    lra.
Qed.
Lemma peval_scale: forall a p x,
is_sorted_fst (a::p) -> 
x ^ (fst a) * Pdense_eval' 0 (sparse_to_dense' (fst a) p) x =
Pdense_eval' 0 (sparse_to_dense' 0 p) x.
Proof.
destruct p.
- intros.
  simpl.
  lra.
- intros.
  simpl.
  repeat rewrite -> eval_zeroes_appended.
  ring_simplify.
  rewrite <- pow_add.
  rewrite -> Rmult_comm.
  f_equal; f_equal.
  Search((_+(_-_))%nat).
  replace ((fst p - 0)%nat) with (fst p) by lia.
  apply Arith_prebase.le_plus_minus_r_stt.
  Search(is_sorted_fst).
  apply is_sorted_fst_cons_lt in H.
  lia.
Qed.
  

       
Lemma Peval_std': forall p x,
is_sorted_fst p -> Pdense_eval (sparse_to_dense p) x = PaxR_eval p x.
Proof.
induction p as [|a p]. 
- simpl. auto. 
- intros.
  
  destruct p.
  + unfold Pdense_eval, sparse_to_dense; simpl.
    rewrite -> eval_zeroes_appended.
    unfold Pdense_eval; simpl.
    replace((fst a - 0)%nat) with (fst a) by lia.
    ring.
  + rewrite -> PaxR_eval_cons.
    rewrite <- IHp by (apply is_sorted_fst_cons_inv in H; auto).
    unfold sparse_to_dense, Pdense_eval.
    rewrite -> std_add.
    rewrite -> eval_zeroes_appended.
    rewrite -> pdense_eval_add.
    rewrite <- peval_std_succ.
    ring_simplify.
    replace(fst a - 0)%nat with (fst a) by lia.
    rewrite -> peval_scale by auto.
    lra.
    (apply is_sorted_fst_cons_inv in H; auto).
    apply sorted_impl_nonzero in H.
    auto.
    discriminate.
Qed.


Lemma eo_plus_deg: forall p,
degree_poly p = (degree_poly(even_poly_D p) + degree_poly(odd_poly_D p))%nat.
Proof.
  unfold even_poly_D, odd_poly_D.
  induction p.
  - simpl. auto.
  - rewrite -> degree_add.
    simpl.
    rewrite <- even_succ_odd.
    rewrite <- odd_succ_even.
    rewrite -> degree_add.
    rewrite -> IHp.
    simpl.
    lia.
Qed.

Lemma eo_eq_succ: forall a p,
degree_poly(even_poly_D p) = degree_poly(odd_poly_D p) ->
degree_poly(even_poly_D (a::p)) = S(degree_poly(odd_poly_D (a::p))).
Proof.
intros. unfold even_poly_D, odd_poly_D in *. 
destruct p.
- simpl. reflexivity.
- simpl in *.
  repeat (rewrite <- even_succ_odd in *; rewrite <- odd_succ_even in *).
  repeat rewrite -> degree_add in *.
  f_equal.
  symmetry.
  apply H.
Qed.

Lemma eo_ne_succ: forall a p,
degree_poly(even_poly_D p) = S(degree_poly(odd_poly_D p)) ->
degree_poly(even_poly_D (a::p)) = degree_poly(odd_poly_D (a::p)).
Proof.
intros. unfold even_poly_D, odd_poly_D in *. 
destruct p.
  - simpl in H. discriminate H.
  - simpl in *.
    repeat (rewrite <- even_succ_odd in *; rewrite <- odd_succ_even in *).
    repeat rewrite -> degree_add in *.
    symmetry.
    apply H.
Qed.

Lemma eo_equal_or_succ: forall p,
degree_poly(even_poly_D (p)) = S(degree_poly(odd_poly_D (p)))
  \/
degree_poly(even_poly_D (p)) = degree_poly(odd_poly_D (p)).
Proof.
induction p.
  - right; reflexivity.
  - destruct IHp.
    + right. 
      apply eo_ne_succ.
      exact H.
    + left.
      apply eo_eq_succ.
      exact H.
Qed.

Lemma even_eq_odd: forall p n,
Nat.le 1 (n)%nat -> degree_poly p = (2*n)%nat -> 
degree_poly(even_poly_D p) = degree_poly(odd_poly_D p).
Proof.
intros; unfold even_poly_D, odd_poly_D. 
pose proof eo_equal_or_succ p as [H1 | H2].
  - rewrite -> eo_plus_deg in H0.
    rewrite -> H1 in H0.
    exfalso.
    replace((S (degree_poly (odd_poly_D p)) + degree_poly (odd_poly_D p))%nat)
     with 
           (( 2* degree_poly (odd_poly_D p) + 1)%nat) in H0 by lia.
    replace((2 * degree_poly (odd_poly_D p) + 1)%nat) with
            ( S (2 * degree_poly (odd_poly_D p))%nat) in H0 by lia.
    lia.
  - unfold even_poly_D, odd_poly_D. 
    exact H2.
Qed.
    
Lemma even_half_deg: forall p n,
Nat.le 1 (n)%nat -> degree_poly p = (2*n)%nat -> 
degree_poly(even_poly_D p) = n.
Proof.
  intros.
  assert(degree_poly (even_poly_D p) = degree_poly (odd_poly_D p)).
  apply even_eq_odd with (n:= n); auto.
  rewrite -> eo_plus_deg in H0.
  rewrite <- H1 in H0.
  replace ( (degree_poly (even_poly_D p) + degree_poly (even_poly_D p))%nat) with
           ( (2*degree_poly(even_poly_D p))%nat) in H0 by lia.
  rewrite -> Nat.mul_cancel_l in H0.
  lia.
  lia.
Qed.

Lemma odd_half_deg: forall p n,
Nat.le 1 (n)%nat -> degree_poly p = (2*n)%nat ->
 degree_poly(odd_poly_D p) = n.
Proof.
  intros.
  assert(degree_poly (even_poly_D p) = degree_poly (odd_poly_D p)).
  apply even_eq_odd with (n:= n); auto.
  rewrite <- H1.
  apply even_half_deg.
  auto.
  auto.
Qed.

Fixpoint evals (w:R)(n:nat)(p:dense_poly) :=
  match n with
  | O => Pdense_eval p (w ^ O) :: nil
  | S(n') => evals w n' p ++ Pdense_eval p (w^n) :: nil 
  end.

Lemma evals_succ: forall n w p,
evals w (S n) p = evals w n p ++ Pdense_eval p (w^(S n))::nil.
Proof.
intros. simpl. reflexivity. Qed.



Lemma evals_nil: forall n w,
evals w n nil = 0::repeat 0 n.
Proof.
induction n.
  - intros. simpl. unfold Pdense_eval. simpl. auto.
  - intros. rewrite -> evals_succ.
    rewrite -> IHn.
    simpl.
    unfold Pdense_eval.
    simpl.
    rewrite -> repeat_cons.
    auto. 
Qed.


Lemma evals_length_le_1: forall w n p,
Nat.le 1 (length(evals w n p)).
Proof.
intros.
induction n.
  - simpl. lia.
  - simpl. rewrite -> last_length.
    apply le_trans with (length (evals w n p)).
    apply IHn.
    auto.
Qed.

Lemma evals_length_eq_n: forall w n p,
length(evals w n p) = S(n).
Proof.
induction n.
  - intros. simpl. auto.
  - intros. simpl. rewrite -> last_length.
    f_equal. apply IHn.
Qed.

Lemma evals_step: forall n j w a p,
Nat.le j n -> 
nth j (evals w n (a::p)) 0 = (a + w^j * Pdense_eval p (w^j))%R.
Proof.
intros.
induction n.
  - simpl. assert(j = O) by lia. rewrite -> H0.
    rewrite -> pdense_eval_add. simpl. lra.
  - apply  Nat.lt_eq_cases in H.
    destruct H.
    ++ simpl. rewrite -> app_nth1.
       apply IHn. lia. rewrite -> evals_length_eq_n. auto.
    ++ simpl. assert(length(evals w n (a :: p)) = j).
       rewrite -> H. apply evals_length_eq_n.
       replace (nth j (evals w n (a :: p) ++ Pdense_eval (a :: p) (w * w ^ n) :: nil) 0) with
       (nth (length(evals w n (a :: p))) (evals w n (a :: p) ++ Pdense_eval (a :: p) (w * w ^ n) :: nil) 0).
       rewrite -> nth_middle.
       rewrite -> pdense_eval_add.
      rewrite -> H.
      auto.
      rewrite -> H0. auto.
Qed.

Lemma pdense_eval_split: forall p w,
hd 0 p + Pdense_eval' 1 (tl p) w = Pdense_eval p w.
Proof.
intros. unfold Pdense_eval. induction p.
  - simpl. lra.
  - simpl. rewrite -> pdense_eval_scale.
    lra.
Qed. 
    
       
Lemma evals_end: forall p,
nth (length p - 1) p 0 = last p 0.
Proof.
intros.
induction p.
  - simpl. lra.
  - simpl.
      destruct (length p) eqn: E.
      apply length_zero_iff_nil in E.
      rewrite -> E. auto.
      replace ((S n - 0)%nat) with (S n) by lia.
      rewrite <- IHp.
      replace ((S n - 1)%nat) with (n).
      assert(length p <> O).
      lia.
      rewrite -> length_zero_iff_nil in H.
      destruct p.
      exfalso; auto.
      auto.
      lia.
Qed.

Lemma evals_correct: forall w n a p,
Nat.le a n -> nth a (evals w n p) O = Pdense_eval p (w^a).
Proof.
induction p.
 - simpl. unfold Pdense_eval. rewrite -> evals_nil. 
   rewrite -> repeat_cons. simpl. replace (repeat 0 n ++ 0 :: nil) with (repeat 0 (S n)).
   rewrite -> nth_repeat. auto.
   simpl. rewrite <- repeat_cons. auto.
 - intros. rewrite -> pdense_eval_add.
   (*destruct a.*)
   simpl. rewrite -> evals_step. simpl. auto. lia.
Qed.

Definition make_two_element(e o: R)(w:R)(j:nat): (R*R) :=
  ((e + w^j * o),(e - w ^ j * o)).


Fixpoint evals_inv (w:R)(n:nat)(p:dense_poly) :=
 match n with
 | O => nil
 | S(n') => Pdense_eval p (w^n) :: evals_inv w n' p
end.

(* Lemma element_correct: forall p n j,
Pdense_eval p (nth_unit_root(2*n)^j) = 
make_two_element(nth (2*n - j) even_poly_D p O)(nth (2*n - j) odd_poly_D p O)
nth_unit_root(2*n) j. *)

Lemma degree_concat: forall a p,
S(degree_poly(p)) = degree_poly(p++a::nil).
intros.
induction p.
  - simpl.
    rewrite -> degree_add.
    reflexivity.
  - 
    rewrite -> degree_add.
    rewrite -> IHp.
    simpl.
    rewrite -> degree_add.
    reflexivity.
Qed.

Lemma evals_add_degree: forall p n w,
S(degree_poly(evals w n p)) = degree_poly(evals w (S n) p).
Proof.
  intros.
  simpl.
  unfold Pdense_eval. simpl.
  rewrite <- degree_concat.
  reflexivity.
Qed.

  

Lemma eval_deg: forall p w n,
degree_poly (evals w n p) = S n.
Proof.
induction n.
  - simpl.
    auto.
  - simpl.
    rewrite <- degree_concat.
    auto.
Qed.

Local Open Scope C_scope.
Lemma unit_root_k_squares: forall n k,
((nth_unit_root (2*n))^k)^2 = (nth_unit_root n)^k.
Proof.
Admitted.

Lemma unit_root_symmetry: forall n k,
nth_unit_root (2*n)^(k+n) = - (nth_unit_root (2*n))^k.
Proof.
Admitted.  

Lemma c_proj_eq: forall  c1 c2: C,
fst c1 = fst c2 -> snd c1 = snd c2 -> c1 = c2.
Proof.
intros.
destruct c1, c2.
simpl in *.
subst.
reflexivity.
Qed.



Lemma nth_unit_root_pow_n: forall n,
  (nth_unit_root (2*n)) ^ (2*n) = 1.
Proof.
intros.
replace (nth_unit_root (2 * n) ^ (2 * n)) with 
(nth_unit_root (2 * n) ^ (n+n)).
rewrite -> unit_root_symmetry.
replace (- nth_unit_root (2 * n) ^ n) with (- nth_unit_root (2 * n) ^ (0+n)).
rewrite -> unit_root_symmetry.
eapply c_proj_eq.
simpl; lra.
simpl; lra.
f_equal.
f_equal.
lia.
Qed.



Lemma unit_root_squares: forall n,
nth_unit_root(2*n)^2 = nth_unit_root(n).
Proof.
intros.
replace (nth_unit_root (2 * n)) with (nth_unit_root (2 * n)^1).
replace (nth_unit_root n) with (nth_unit_root n ^1).
apply unit_root_k_squares.
eapply c_proj_eq.
f_equal. ring.
f_equal; ring.
ring.
Qed.

Definition dense_cpoly:= list C.
Fixpoint poly_RtoC(p:dense_poly): dense_cpoly:=
  match p with
  | nil => nil
  | fn::p' => RtoC(fn)::poly_RtoC(p')
  end.


Fixpoint complex_eval' (d:nat)(p: dense_cpoly)(c:C): C :=
  match p with
  | nil => 0
  | fn::p0 => fn * (c^d) + complex_eval' (S d) p0 c
  end.

Definition complex_eval (p:dense_cpoly)(c:C) : C :=
  complex_eval' 0 p c.

Lemma complex_scale: forall (p: dense_cpoly)(c: C)(d:nat),
  complex_eval' (S d) p c = c * complex_eval'  d p c.
Proof.
  induction p.
  - intros.
    simpl. 
    rewrite -> Cmult_0_r.
    auto.
  - intros; simpl.
    repeat rewrite IHp.
    ring.
Qed.

Lemma poly_RtoC_correct: forall p x,
RtoC(Pdense_eval p x) = complex_eval(poly_RtoC p) x.
Proof.
intros.
unfold Pdense_eval, complex_eval.
induction p.
  - auto.
  - simpl.
    rewrite -> pdense_eval_scale.
    rewrite -> complex_scale.
    rewrite <- IHp.
    apply c_proj_eq.
    + simpl. lra.
    + simpl. lra.
Qed.
      
Lemma complex_eval_add: forall a p x, complex_eval(a::p)x = a+x*complex_eval p x.
Proof.
intros; unfold complex_eval; simpl.
f_equal.
eapply c_proj_eq.
  - simpl; lra.
  - simpl; lra.
  - apply complex_scale.
Qed.


Fixpoint even_poly_C'(d:nat)(p:dense_cpoly): dense_cpoly :=
 match p with
  | nil => nil
  | a1::p' => if Nat.even(d) then a1::even_poly_C' (S d) p' else even_poly_C'(S d) p'
  end.

Fixpoint odd_poly_C'(d:nat)(p:dense_cpoly): dense_cpoly :=
  match p with
  | nil => nil
  | a1::p' => if Nat.odd(d) then a1::odd_poly_C'(S d) p' else odd_poly_C'(S d) p'
end.

Definition even_poly_C(p:dense_cpoly): dense_cpoly :=
  even_poly_C' 0 p.
Definition odd_poly_C(p:dense_cpoly): dense_cpoly :=
  odd_poly_C' 0 p.

Lemma ceven_succ_odd:  forall p n,
even_poly_C' n p = odd_poly_C' (S n) p.
Proof. 
  intros p; induction p. 
     - auto. 
     - simpl; intros n. 
       rewrite -> Nat.odd_succ.
       destruct (Nat.even n) eqn: E.
        + f_equal; apply IHp.
        + apply IHp.
Qed.

Lemma codd_succ_even:  forall p n,
odd_poly_C' n p = even_poly_C' (S n) p.
Proof.
  intros p; induction p. 
     - auto. 
     - intros n; induction n.
        + simpl. apply IHp.
        + simpl.
          rewrite -> Nat.odd_succ. 
          destruct(Nat.even n) eqn: E.
            * f_equal; apply IHp.
            * apply IHp. 
Qed.
Lemma even_and_odd_C: forall p x,
  complex_eval (even_poly_C' 0 p) (x^2) + x*complex_eval(odd_poly_C' 0 p) (x^2) = complex_eval p x.
Proof.
intros. induction p.
  - unfold complex_eval.
    simpl.
    apply c_proj_eq.
    simpl; lra.
    simpl; lra.
  - simpl.
    rewrite <- ceven_succ_odd.
    rewrite <- codd_succ_even.
    repeat rewrite -> complex_eval_add.
    rewrite <- IHp.
    apply c_proj_eq.
    + simpl. lra.
    + simpl; lra.
Qed.



Lemma ceo_plus_deg: forall p,
length p = (length(even_poly_C p) + length(odd_poly_C p))%nat.
Proof.
  unfold even_poly_C, odd_poly_C.
  induction p.
  - simpl. auto.
  - simpl.
    f_equal.
    rewrite <- ceven_succ_odd.
    rewrite <- codd_succ_even.
    rewrite -> IHp.
    lia.
Qed.

Lemma ceo_eq_succ: forall a p,
length (even_poly_C p) = length (odd_poly_C p) ->
length (even_poly_C (a::p)) = S(length(odd_poly_C (a::p))).
Proof.
intros. unfold even_poly_C, odd_poly_C in *.
destruct p.
- simpl. reflexivity.
- simpl in *.
  repeat (rewrite <- ceven_succ_odd in *; rewrite <- codd_succ_even in *).
  f_equal.
  symmetry.
  apply H.
Qed.

Lemma ceo_ne_succ: forall a p,
length (even_poly_C p) = S(length (odd_poly_C p)) ->
length (even_poly_C (a::p)) = length (odd_poly_C (a::p)).
Proof.
intros. unfold even_poly_C, odd_poly_C in *. 
destruct p.
  - simpl in H. discriminate H.
  - simpl in *.
    repeat (rewrite <- ceven_succ_odd in *; rewrite <- codd_succ_even in *).
    auto.
Qed.

Lemma ceo_equal_or_succ: forall p,
length(even_poly_C (p)) = S(length(odd_poly_C (p)))
  \/
length(even_poly_C (p)) = length(odd_poly_C (p)).
Proof.
induction p.
  - right; reflexivity.
  - destruct IHp.
    + right. 
      apply ceo_ne_succ.
      exact H.
    + left.
      apply ceo_eq_succ.
      exact H.
Qed.
Lemma ceven_eq_odd: forall p n,
Nat.le 1 (n)%nat -> length p = (2*n)%nat -> 
length(even_poly_C p) = length(odd_poly_C p).
Proof.
intros; unfold even_poly_D, odd_poly_D. 
pose proof ceo_equal_or_succ p as [H1 | H2].
  - rewrite -> ceo_plus_deg in H0.
    rewrite -> H1 in H0.
    exfalso.
    replace((S (length (odd_poly_C p)) + length (odd_poly_C p))%nat)
     with 
           (( 2* length (odd_poly_C p) + 1)%nat) in H0 by lia.
    replace((2 * length (odd_poly_C p) + 1)%nat) with
            ( S (2 * length (odd_poly_C p))%nat) in H0 by lia.
    lia.
  - unfold even_poly_C, odd_poly_C. 
    exact H2.
Qed.
    
Lemma ceven_half_deg: forall p n,
Nat.le 1 (n)%nat -> length p = (2*n)%nat -> 
length(even_poly_C p) = n.
Proof.
  intros.
  assert(length (even_poly_C p) = length (odd_poly_C p)).
  apply ceven_eq_odd with (n:= n); auto.
  rewrite -> ceo_plus_deg in H0.
  rewrite <- H1 in H0.
  replace ( (length (even_poly_C p) + length (even_poly_C p))%nat) with
           ( (2*length(even_poly_C p))%nat) in H0 by lia.
  rewrite -> Nat.mul_cancel_l in H0.
  all: lia.
Qed.

Lemma codd_half_deg: forall p n,
Nat.le 1 (n)%nat -> length p = (2*n)%nat ->
 length(odd_poly_C p) = n.
Proof.
  intros.
  assert(length (even_poly_C p) = length (odd_poly_C p)).
  apply ceven_eq_odd with (n:= n); auto.
  rewrite <- H1.
  apply ceven_half_deg.
  all:auto.
Qed.

Fixpoint cevals (w:C)(n:nat)(p:dense_cpoly): dense_cpoly :=
  match n with
  | O => complex_eval p (w^0)::nil
  | S(n') => cevals w n' p ++ complex_eval p (w^n) :: nil
  end.

Lemma cevals_succ: forall n w p,
cevals w (S n) p = cevals w n p ++ complex_eval p (w^(S n))::nil.
Proof.
auto. 
Qed.

Search(repeat).
Lemma cevals_nil: forall n w,
cevals w n nil = RtoC(0)::repeat (RtoC 0) n.
Proof.
induction n.
  - intros. simpl.
    auto.
  - intros. simpl. 
    rewrite -> IHn.
    unfold complex_eval.
    simpl.
    Search(repeat).
     rewrite -> repeat_cons.
    auto.
Qed.

Lemma complex_add: forall a p x, 
complex_eval(a::p)x = a + x*complex_eval p x.
Proof.
intros; unfold complex_eval; simpl.
f_equal.
apply c_proj_eq. 
simpl. lra.
simpl. lra.
rewrite -> complex_scale.
apply c_proj_eq.
all: simpl.
all: lra.
Qed.

Lemma cevals_length_eq_n: forall w n p,
length(cevals w n p) = S n.
Proof.
induction n.
  - auto.
  - intros; simpl.
    rewrite -> last_length.
    f_equal.
    apply IHn.
Qed.
Lemma cevals_step: forall n j w a p,
Nat.le j n ->
nth j (cevals w n (a::p)) 0 = a + w^j * complex_eval p (w^ j).
Proof.
intros.
induction n.
  - simpl.
    replace j with O by lia.
    simpl.
    rewrite -> complex_add.
    auto.
  - apply Nat.lt_eq_cases in H.
    destruct H.
    + simpl. rewrite -> app_nth1 by (rewrite -> cevals_length_eq_n; auto).
      apply IHn; lia.
    + simpl.
      assert(length(cevals w n (a::p)) = j) 
      by (rewrite -> H; apply cevals_length_eq_n).
      replace(nth j (cevals w n (a :: p) ++ complex_eval (a :: p) (w * w ^ n) :: nil) 0) with
      (nth(length(cevals w n (a::p))) (cevals w n (a::p) ++ complex_eval(a::p)(w*w^n)::nil)0).
      rewrite -> nth_middle.
      rewrite -> complex_add.
      rewrite -> H.
      auto.
     (* proof of rewrite *)
     rewrite -> H0; auto.
Qed.

      
    
    
    
    
Lemma cevals_correct: forall w n a p,
Nat.le a n -> nth a (cevals w n p) O = complex_eval p (w^a).
Proof.
induction p.
  - intros; simpl.
    unfold complex_eval.
    simpl.
    rewrite -> cevals_nil.
    rewrite -> repeat_cons.
    simpl.
    intros.
    replace(repeat (RtoC 0) n ++ RtoC(0)::nil) with 
    (repeat (RtoC 0) (S n)) by (rewrite <- repeat_cons; auto).
    rewrite -> nth_repeat. 
    auto.
  - intros. 
    unfold complex_eval. simpl.
    rewrite -> complex_scale.
    rewrite -> cevals_step by apply H.
    unfold complex_eval.
    apply c_proj_eq.
    all:simpl.
    all:lra.
Qed.
    
Lemma FFT_inductive_step_even: forall p j n,
Nat.le 1 n ->
complex_eval p ((nth_unit_root (2*n)^j)) = 
complex_eval (even_poly_C p)(nth_unit_root n^j) + 
nth_unit_root (2*n)^j * complex_eval(odd_poly_C p)(nth_unit_root n ^j).
Proof. 
  unfold Nat.le.
  destruct n.
  (* case n = 0 *)
   - intros. 
     exfalso. 
     lia.
  (* case n >= 1*)
  - intros. 
    assert(nth_unit_root(S n) ^ j = (nth_unit_root(2* S n)^j)^2). 
       rewrite -> unit_root_k_squares. reflexivity. 
    rewrite -> H0.
    symmetry. 
    apply even_and_odd_C. 
Qed.


Lemma FFT_inductive_step_odd: forall p j n,
Nat.le 1 n -> 
complex_eval p (nth_unit_root (2*n)^(j+ n)) = 
complex_eval(even_poly_C p)(nth_unit_root n ^j) - 
(nth_unit_root (2*n) ^j) * complex_eval(odd_poly_C p)(nth_unit_root n^j).
Proof.
  unfold Nat.le. 
  destruct n.
  (* case n = 0 *)
   - intros. 
     exfalso. 
     lia.
  (* induction starts at n = 1*)
   - intros.
       assert(forall n x p, x - n*p = x+(-n*p)).
       (*assertion*)
        {intros. apply c_proj_eq.
        all: simpl.
        all: lra. }
       rewrite -> H0.
       rewrite <- unit_root_symmetry.
       assert(forall n j, nth_unit_root (2*n) ^(2*j+2*n) = 
              nth_unit_root (2*n) ^ (j*2)).
              intros. 
              assert(nth_unit_root (2*n0) ^ (2*j0 + 2 * n0) =
                     nth_unit_root (2*n0) ^ (2*j0 + n0 + n0)) by (f_equal; lia). 
              rewrite -> H1.
             repeat rewrite -> unit_root_symmetry.
             apply c_proj_eq.
             simpl. rewrite -> Ropp_involutive.
             f_equal.
             f_equal.
             lia.
             simpl. rewrite -> Ropp_involutive.
             f_equal; f_equal.
             lia. 
       assert(nth_unit_root(S n) ^ j = (nth_unit_root(2* S n)^j)^2) by
          (rewrite -> unit_root_k_squares; reflexivity). 
       rewrite -> H2.
       Search(_^_).
       rewrite <- Cpow_mult_r.
       rewrite <- H1.
       assert(nth_unit_root (2 * S n) ^ (2 * j + 2 * S n) = 
              (nth_unit_root (2 * S n) ^ (j+S n)) ^ 2) by
           (rewrite <- Cpow_mult_r; f_equal; lia).
       rewrite -> H3.
       symmetry.
       apply even_and_odd_C.
Qed.

Lemma length_one_ceval: forall x p,
 length p = 1%nat -> complex_eval p x = hd (RtoC 0) p.
Proof.
intros.
induction p.
  - simpl in H.
    exfalso; lia.
  - rewrite -> complex_eval_add.
    simpl.
    simpl in H.
    assert(length p = O) by lia.
    apply length_zero_iff_nil in H0.
    rewrite -> H0.
    unfold complex_eval; simpl.
    apply c_proj_eq.
    all:simpl.
    all: lra.
Qed.

Fixpoint make_left (y_e y_o: list C) (n:nat)(w: C): list C :=
  match n with
  |O => (nth n y_e O) + w^n * (nth n y_o O) :: nil
  |S(n') => make_left y_e y_o n' w  ++ (((nth n y_e O) + w^n * (nth n y_o O)) :: nil)
end.

Lemma make_left_length: forall n w y_e y_o,
length(make_left y_e y_o n w) = S n.
Proof.
intros. induction n.
  - simpl. lia.
  - simpl. rewrite -> last_length.
    rewrite -> IHn. auto.
Qed.

Lemma make_left_cons: forall a n w y_e y_o,
Nat.le a n ->
nth a (make_left y_e y_o (S n) (w)) 0 = 
nth a (make_left y_e y_o (n) w ++ (((nth n y_e O) + w^n * (nth n y_o O)))::nil) 0.
Proof.
    intros.
    simpl. rewrite -> app_nth1.
    rewrite -> app_nth1.
    reflexivity.
    all: rewrite -> make_left_length.
    all: lia.
Qed.

Lemma make_left_zero: forall n w e o,
nth 0 (make_left e o n w) 0 = (nth 0 e O) + w^0 * (nth 0 o O).
Proof.
intros. simpl. induction n.
  - simpl. auto.
  - simpl. rewrite -> app_nth1.
    rewrite -> IHn.
    auto.
    rewrite -> make_left_length.
    lia.
Qed.

Lemma make_left_nth: forall a n w e o,
Nat.le a n ->
nth a (make_left e o n w) 0 = (nth a e O) + w^a * (nth a o O).
Proof.
intros. induction n.
  - simpl. destruct a.
    auto. exfalso; lia.
  - simpl. 
    apply le_lt_or_eq in H.
    destruct H.
    + rewrite -> app_nth1.
      apply IHn. lia. rewrite -> make_left_length. lia.
    + rewrite -> app_nth2 by (rewrite -> make_left_length; lia).
      rewrite -> make_left_length.
      rewrite -> H.
      simpl.
      replace ((n-n)%nat) with O by lia.
      auto.   
Qed.

    
(* Nat.le a n -> nth a (evals w n p) O = Pdense_eval p (w^a). *)
Lemma make_left_correct: forall n a y_e y_o p,
Nat.le 1 n -> Nat.lt a n -> length p = (2*n)%nat ->
y_e = cevals (nth_unit_root (n)) (n-1) (even_poly_C p) ->
y_o = cevals (nth_unit_root (n)) (n-1) (odd_poly_C p) ->
nth a (make_left y_e y_o (n-1) (nth_unit_root(2*n))) O  =
nth a (cevals (nth_unit_root (2*n)) (2*n-1) p) O.
Proof.
intros.
destruct n.
  - simpl. exfalso. lia.
  - rewrite -> make_left_nth by lia.
    rewrite -> H2, H3.
    repeat rewrite -> cevals_correct by lia.
    rewrite -> FFT_inductive_step_even by auto. 
    auto.
Qed.

Fixpoint make_right (y_e y_o: list C) (n:nat)(w: C): list C :=
  match n with
  |O => (nth n y_e O) - w^n * (nth n y_o O) :: nil
  |S(n') => make_right y_e y_o n' w  ++ (((nth n y_e O) - w^n * (nth n y_o O)) :: nil)
end.

Lemma make_right_length: forall n w y_e y_o,
length(make_right y_e y_o n w) = S n.
Proof.
intros. induction n.
  - simpl. lia.
  - simpl. rewrite -> last_length.
    rewrite -> IHn. auto.
Qed.

Lemma make_right_cons: forall a n w y_e y_o,
Nat.le a n ->
nth a (make_right y_e y_o (S n) (w)) 0 = 
nth a (make_right y_e y_o (n) w ++ (((nth n y_e O) + w^n * (nth n y_o O)))::nil) 0.
Proof.
    intros.
    simpl. rewrite -> app_nth1.
    rewrite -> app_nth1.
    reflexivity.
    all: rewrite -> make_right_length.
    all: lia.
Qed.

Lemma make_right_zero: forall n w e o,
nth 0 (make_right e o n w) 0 = (nth 0 e O) - w^0 * (nth 0 o O).
Proof.
intros. simpl. induction n.
  - simpl. auto.
  - simpl. rewrite -> app_nth1.
    rewrite -> IHn.
    auto.
    rewrite -> make_right_length.
    lia.
Qed.

Lemma make_right_nth: forall a n e o w,
Nat.le a n ->
nth a (make_right e o n w) 0 = (nth a e O) - w^a * (nth a o O).
Proof.
intros. induction n.
  - simpl. destruct a.
    auto. exfalso; lia.
  - simpl. 
    apply le_lt_or_eq in H.
    destruct H.
    + rewrite -> app_nth1.
      apply IHn. lia. rewrite -> make_right_length. lia.
    + rewrite -> app_nth2 by (rewrite -> make_right_length; lia).
      rewrite -> make_right_length.
      rewrite -> H.
      simpl.
      replace ((n-n)%nat) with O by lia.
      auto.   
Qed.

Lemma make_right_correct: forall n a y_e y_o p,
Nat.le 1 n -> Nat.lt a n -> length p = (2*n)%nat ->
y_e = cevals (nth_unit_root (n)) (n-1) (even_poly_C p) ->
y_o = cevals (nth_unit_root (n)) (n-1) (odd_poly_C p) ->
nth a (make_right y_e y_o (n-1) (nth_unit_root(2*n))) O  =
nth (a+n) (cevals (nth_unit_root (2*n)) (2*n-1) p) O.
Proof.
intros.
destruct n.
  - simpl. exfalso. lia.
  - rewrite -> make_right_nth by lia.
    rewrite -> H2, H3.
    repeat rewrite -> cevals_correct by lia.
    rewrite -> FFT_inductive_step_odd by auto.
    auto.
Qed.

Definition m2_l (y_e y_o: list C)(w: C): list C :=
 let n      := length(y_e) in
 let l1     := make_left y_e y_o (n-1) w in
 let l2     := make_right y_e y_o (n-1) w in
      l1 ++ l2.

Fixpoint fft(n:nat)(p:list C)(w:C):list C :=
  match n with
  | O => p
  | S(n')     => let y_e := fft(n')(even_poly_C p)(w^2%nat) in
                 let y_o := fft(n')(odd_poly_C p)(w^2%nat) in 
                 m2_l y_e y_o w
  end.

Lemma m2_l_nth_correct: forall n a y_e y_o p,
Nat.le 1 n -> length p = (2*n)%nat -> Nat.lt a (2*n) ->
y_e = cevals (nth_unit_root (n)) (n-1) (even_poly_C p) ->
y_o = cevals (nth_unit_root (n)) (n-1) (odd_poly_C p) ->
nth a (m2_l y_e y_o (nth_unit_root(2*n))) 0= 
nth a (cevals (nth_unit_root (2*n)) (2*n-1) p) 0.
Proof.
    intros.
    unfold m2_l.
    replace(length y_e) with (n)  by (rewrite -> H2; rewrite -> cevals_length_eq_n; lia).
    destruct(Nat.lt_ge_cases a n).
    - rewrite -> app_nth1.
      rewrite -> make_left_correct with (p:= p).
      all:auto.
      rewrite -> make_left_length. lia.
   -  rewrite -> app_nth2 by (rewrite -> make_left_length; lia).
      rewrite -> make_left_length.
      rewrite -> make_right_correct with (p:= p).
      repeat rewrite -> cevals_correct by lia.
      repeat f_equal.
      all: auto.
      all: lia.
Qed.


Lemma nth_succ: forall (l1 l2: list C) a0 a r,
nth (S a0) (a :: l1) 0 = nth (S a0) (r :: l2) 0 ->
nth a0 l1 0 = nth a0 l2 0.
Proof.
intros. simpl in H. auto.
Qed.

Lemma lt_to_all_nth: forall l1 l2: list C,
length l1 = length l2 ->
(forall (a:nat), Nat.lt a (length l1) -> nth a l1 0 = nth a l2 0)
-> (forall (a : nat), nth a l1 0 = nth a l2 0).
Proof.
intros.
destruct (Nat.lt_ge_cases a (length l1)) as [Hlt | Hge].
 - apply H0. auto.
 - Search(nth).
   rewrite -> nth_overflow by auto.
   rewrite -> H in Hge.
   rewrite -> nth_overflow by auto.
   auto.
Qed.
   
    
          
Lemma nth_eq: forall l1 l2: list C,
length l1 = length l2 ->
  (forall (a : nat), nth a l1 0 = nth a l2 0) ->
  l1 = l2.
Proof.
induction l1.
  - intros.
    simpl in H.
    symmetry in H; apply length_zero_iff_nil in H.
    auto.
  - intros.
    destruct l2.
    simpl in H.
    exfalso; lia.
    
    simpl in H.
    f_equal.
    specialize (H0 O).
    simpl in H0. auto.
    
    apply IHl1.
    lia.
    intros.
    assert(nth (S a0) (a :: l1) 0 = nth (S a0) (c :: l2) 0).
    apply H0.
    apply nth_succ in H1. auto.
Qed.

Lemma m2_l_correct: forall n y_e y_o p,
Nat.le 1 n -> length p = (2*n)%nat ->
y_e = cevals (nth_unit_root (n)) (n-1) (even_poly_C p) ->
y_o = cevals (nth_unit_root (n)) (n-1) (odd_poly_C p) ->
m2_l y_e y_o (nth_unit_root(2*n)) = cevals (nth_unit_root (2*n)) (2*n-1) p.
Proof.
intros.

assert(forall a, Nat.lt a (2*n) -> 
nth a (m2_l y_e y_o (nth_unit_root(2*n))) 0= 
nth a (cevals (nth_unit_root (2*n)) (2*n-1) p) 0).
intros. apply m2_l_nth_correct. all: auto.

assert(length (m2_l y_e y_o (nth_unit_root (2 * n))) = (2*n)%nat).
unfold m2_l.
rewrite -> app_length.
rewrite -> make_left_length.
rewrite -> make_right_length.
rewrite -> H1.
rewrite -> cevals_length_eq_n.
lia.

assert(forall a:nat,
nth a (m2_l y_e y_o (nth_unit_root(2*n))) 0= 
nth a (cevals (nth_unit_root (2*n)) (2*n-1) p) 0).
apply lt_to_all_nth.
rewrite -> H4.
rewrite -> cevals_length_eq_n.
lia.

rewrite -> H4.
apply H3.

apply nth_eq in H5.
auto.
rewrite -> H4.
rewrite -> cevals_length_eq_n.
lia.
Qed.



Lemma pow_le_1: forall n,
Nat.le 1 (2^n)%nat.
Proof.
intros. induction n.
- simpl. lia.
- apply Nat.le_trans with ((2^n)%nat).
  auto.
  simpl.
  lia.
Qed.
    

Lemma fft_correct: forall n p,
length p = (2^n)%nat -> 
fft n p (nth_unit_root(2^n%nat)) = cevals(nth_unit_root (2^n)%nat) (2^n-1)%nat p.
Proof.
induction n.
  - intros.
    simpl in *.
    unfold complex_eval.
    rewrite -> length_one_ceval.
    destruct p.
    (* case p = nil *) 
    discriminate H.
    (* case p = degree 1 *)
    simpl in *.
      assert(length p = O) by lia.
      rewrite -> length_zero_iff_nil in H0.
      rewrite -> H0.
      auto.
    apply H.
  - intros.
    simpl.
(* even poly degree *)
    assert(length (even_poly_C p) = (2^n)%nat).
      apply ceven_half_deg in H.
      apply H.
      apply pow_le_1.
(* odd poly degree *)
    assert(length (odd_poly_C p) = (2^n)%nat).
      apply codd_half_deg.
      apply pow_le_1.
      apply H.

    assert(nth_unit_root (2 ^ n + (2 ^ n + 0)) *
      (nth_unit_root (2 ^ n + (2 ^ n + 0)) * 1)= nth_unit_root (2 ^ n)).
    apply unit_root_squares.
    rewrite -> H2.
    apply m2_l_correct. 
    
    (* Nat.le 2^n*)
    apply pow_le_1.
    (* degree p*)
    auto.
    
    all: rewrite -> IHn.
    all: auto.
Qed.

Definition ifft(n:nat)(p:list C):list C :=
  let w:= (1/n) * 1/nth_unit_root (2^n) in 
  fft n p w. 
    
Lemma icorrect : forall n p x,
length p = (2^n)%nat -> 
complex_eval (ifft n (fft n p (nth_unit_root(2^n)))) x = complex_eval p x.
Proof.

  induction n.
  - simpl. reflexivity.
  - intros. simpl.
    
     Admitted.

Fixpoint add_dense_poly (p1 p2: dense_poly): dense_poly :=
  match p1, p2 with
  | nil, _ => p2
  | _  , nil => p1
  | a::p1', b::p2' => (a+b) :: add_dense_poly p1' p2'
  end.

Fixpoint scalar_mult (a : R) (p : dense_poly) : dense_poly :=
  match p with
  | nil => nil
  | h :: t => (a * h) :: scalar_mult a t
  end.

Fixpoint naive_mult (p1 p2 : dense_poly) : dense_poly :=
  match p1 with
  | nil => nil
  | h1 :: t1 => add_dense_poly (scalar_mult h1 p2) (0 :: naive_mult t1  p2)
  end.

Lemma add_cons: forall p1 p2 a,
add_dense_poly (a::p1)(p2) = (a+ hd 0 p2) :: add_dense_poly p1 (tl p2).
Proof.
destruct p1.
  - intros. destruct p2.
    + simpl. 
      f_equal.
      lra.
    + simpl.
      auto.
  - intros. 
    destruct p2.
    + simpl.
      f_equal; lra.
    + simpl. reflexivity.
Qed.

Lemma add_correct: forall p1 p2 x,
Pdense_eval(add_dense_poly p1 p2) x = Pdense_eval(p1)x + Pdense_eval(p2) x.
Proof.
unfold Pdense_eval.
induction p1.
  - intros. simpl.
    lra.
  - intros. rewrite -> add_cons.
    repeat rewrite -> pdense_eval_add.
    unfold Pdense_eval.
    rewrite -> IHp1.
    replace (x * (Pdense_eval' 0 p1 x + Pdense_eval' 0 (tl p2) x)) with
             (x * Pdense_eval' 0 p1 x + x * Pdense_eval' 0 (tl p2) x) by lra.
    rewrite <- Rplus_assoc.
    Search(Pdense_eval).
    replace (a + hd 0 p2 + x * Pdense_eval' 0 p1 x +
    x * Pdense_eval' 0 (tl p2) x) with (a+ x * Pdense_eval' 0 p1 x +
    (hd 0 p2 + x * Pdense_eval' 0 (tl p2) x)) by lra.
    rewrite <- pdense_eval_add.
    rewrite <- pdense_eval_add.
    unfold Pdense_eval.
    f_equal. 
    destruct p2. 
    all: simpl. 
    all: lra.
Qed.
    
    

Lemma scalar_mult_cons: forall n a p,
scalar_mult n (a::p) = a*n :: scalar_mult n p.
Proof.
intros. simpl. f_equal. lra.
Qed.

Lemma scalar_correct: forall n p x,
Pdense_eval(scalar_mult n p) x = n*Pdense_eval p x.
Proof.
intros. unfold Pdense_eval.
induction p.
  - simpl. lra.
  - rewrite -> scalar_mult_cons.
    repeat rewrite -> pdense_eval_add.
    replace (Pdense_eval (scalar_mult n p) x) with ( n * Pdense_eval p x).
    lra.
Qed.
Lemma mul_cons: forall a p1 p2,
naive_mult (a::p1) p2 = add_dense_poly (scalar_mult a p2) (0::naive_mult p1 p2).
Proof.
intros.
simpl. reflexivity. Qed.


Lemma pmul_correct: forall p1 p2 x,
Pdense_eval p1 x * Pdense_eval p2 x = Pdense_eval(naive_mult p1 p2) x.
Proof.
unfold Pdense_eval.
induction p1.
  - intros.
    simpl in *. ring.
  - intros.
    rewrite -> pdense_eval_add.
    rewrite -> mul_cons. 
    rewrite -> add_correct. 
    rewrite -> scalar_correct.
    ring_simplify.
    unfold Pdense_eval.
    rewrite -> pdense_eval_add.
    rewrite <- IHp1.
    ring_simplify.
    auto.
Qed.
    

Fixpoint pointwise_mul(p1 p2:list R)(n:nat):=
  match n with
  | O      => (nth n p1 0)*(nth n p2 0)::nil
  | S (n') => pointwise_mul p1 p2 n' ++ ((nth n p1 0)*(nth n p2 0)::nil)
end.

Lemma pointwise_mul_add: forall p1 p2 n a b,
Nat.lt n (length p1) -> length p1 = length p2 ->
pointwise_mul(p1++a::nil)(p2++b::nil)(n) = pointwise_mul(p1)(p2)(n).
Proof.
intros. induction n.
  - simpl.
    repeat rewrite -> app_nth1 by lia.
    auto.
  - simpl. 
      destruct(Nat.lt_ge_cases n (length p1)).
    + rewrite -> IHn.
      f_equal. f_equal.
      rewrite -> app_nth1.
      rewrite -> app_nth1.
      auto.
      all: lia.
    + exfalso. lia.
Qed.

Lemma pointwise_mul_length: forall p1 p2 n,
length(pointwise_mul p1 p2 n) = S n.
Proof.
intros.
induction n.
  - simpl. lia.
  - simpl. 
    rewrite -> last_length.
    f_equal.
    apply IHn.
Qed.

Lemma nth_mul_evals: forall a p1 p2 n w,
Nat.le a n -> 
nth a (pointwise_mul(evals w n p1) (evals w n p2) n) 0 = 
nth a (evals w n (naive_mult p1 p2)) 0.
Proof.
intros.
induction n.
  - replace a with O by lia.
    simpl.
    rewrite -> pmul_correct.
    auto.
  - simpl.
    apply le_lt_or_eq in H.
    destruct H.
    (*case a < S n *)
    +     rewrite -> pointwise_mul_add.
          repeat rewrite -> app_nth1.
          apply IHn. lia.
          all: try rewrite -> evals_length_eq_n. 
          all: try rewrite -> pointwise_mul_length.
          all: auto.
          rewrite -> evals_length_eq_n; auto.
    (* case a = S n *)
    +     assert(a = length((pointwise_mul
         (evals w n p1 ++ Pdense_eval p1 (w * w ^ n) :: nil)
         (evals w n p2 ++ Pdense_eval p2 (w * w ^ n) :: nil) n))).
          rewrite -> pointwise_mul_length; auto.
          rewrite -> H0. rewrite -> nth_middle.
          rewrite <- H0.
          replace a with (length(evals w n (naive_mult p1 p2))) by
          (rewrite -> evals_length_eq_n; auto).
          rewrite -> nth_middle.
          replace(S n) with (length (evals w n p1)).
          rewrite -> nth_middle.
          replace (length (evals w n p1)) with (length (evals w n p2)).
          rewrite -> nth_middle.
          rewrite -> pmul_correct. auto.
          all: repeat rewrite -> evals_length_eq_n.
          all: auto.
Qed.

Lemma mul_evals: forall p1 p2 w n,
pointwise_mul(evals w n p1)(evals w n p2) n =
evals w n (naive_mult p1 p2).
Proof.
intros.
assert(length (pointwise_mul (evals w n p1) (evals w n p2) n) = length(evals w n (naive_mult p1 p2))) by
(rewrite -> pointwise_mul_length;
 rewrite -> degree_length; rewrite -> eval_deg;
 auto).
apply nth_eq.
auto.
apply lt_to_all_nth.
auto.
intros.
rewrite -> pointwise_mul_length in H0.
apply nth_mul_evals; lia.
Qed.


(* 
Fixpoint evals (w:R)(n:nat)(p:dense_poly) :=
  match n with
  | O => Pdense_eval p (w ^ O) :: nil
  | S(n') => evals w n' p ++ Pdense_eval p (w^n) :: nil 
  end. *)

Definition degree_div(n:nat)(x:R) :=
  (/n) * x.

Definition ievals(w:R)(n:nat)(p:dense_poly) :=
match n with
| O => nil
| n => map (degree_div n) (evals (/w) n p)
end.

Lemma degdiv_zero: forall n,
degree_div n O = O.
Proof.
intros. simpl.
unfold degree_div. lra.
Qed.
(*Lemma evals_correct: forall w n a p,
Nat.le a n -> nth a (evals w n p) O = Pdense_eval p (w^a).*)
Lemma ievals_ev: forall (w:R) n p a,
0<w -> Nat.lt O n -> 
Nat.le a n -> nth a (ievals w n p) O = (/n) * Pdense_eval p ((/w^a)).
intros.
unfold ievals.
destruct n.
  - exfalso; lia.
  - rewrite <- degdiv_zero with(n:= S n).
    Search(nth _ (map _ _) _).
    rewrite -> map_nth.
    unfold degree_div.
    rewrite -> evals_correct by auto.
    repeat f_equal.
    rewrite -> pow_inv by lra.
    auto.
Qed.

Search(Pdense_eval).
(*
  pdense_eval_add:
  forall (a : R) (p : list R) (x : R),
  Pdense_eval (a :: p) x = a + x * Pdense_eval p x
*)

 (*
  evals_correct:
  forall (w : R) (n a : nat) (p : dense_poly),
  Nat.le a n -> nth a (evals w n p) 0%nat = Pdense_eval p (w ^ a) 
*)


Lemma nth_evals_cons: forall w n p a f,
Nat.le a n ->
nth a (evals w n (f::p)) O = f + w^a * nth a (evals w n p) O.
Proof.
intros.
repeat rewrite -> evals_correct by auto.
rewrite -> pdense_eval_add.
auto.
Qed.
(*
Lemma evals_inverse: forall a p n,
degree_poly p = n ->
nth a (ievals (nth_unit_root n) n (evals (nth_unit_root n) n p)) O  = 
nth a p O.
Proof.
unfold Pdense_eval.
induction a.
  - induction p.
    + intros. 
      simpl.
      rewrite <- degree_length in H.
      assert(n = O) by auto.
      rewrite -> H0.
      simpl.
      lra.
    + intros.
      unfold ievals.
      destruct n.
        * rewrite <- degree_length in H. exfalso.
          simpl in H. lia.
        * Search(nth _ (map _ _) _).
          rewrite <- degdiv_zero with (n:= S n).
          rewrite -> map_nth.
          simpl.
          Search(nth).
          rewrite -> app_nth1.
          rewrite -> evals_correct.
          simpl; rewrite <- evals_succ.
          unfold Pdense_eval, degree_div. *)



Lemma eval_zeroes_end: forall p n x,
Pdense_eval p x = Pdense_eval (p ++ repeat 0 n) x.
Proof. 
induction p.
  - intros. simpl.
    induction n.
    + simpl. auto.
    + simpl. rewrite -> pdense_eval_add.
      rewrite <- IHn.
      unfold Pdense_eval; simpl; lra.
  - intros.
    simpl.
    repeat rewrite -> pdense_eval_add.
    rewrite <- IHp.
    auto.
Qed.
    
Lemma naive_mult_padded: forall p1 p2 n x,
Pdense_eval (naive_mult(p1 ++ repeat 0 n)(p2 ++ repeat 0 n)) x= 
Pdense_eval (naive_mult p1 p2) x.
Proof.
intros.
rewrite <- pmul_correct.
unfold Pdense_eval.
induction n.
  - simpl.
    repeat rewrite -> app_nil_r.
    apply pmul_correct.
  - intros. 
    rewrite <- IHn.
    repeat rewrite <- eval_zeroes_end.
    lra.
Qed.

Lemma scalar_mult_length: forall a p,
length p = length(scalar_mult a p).
Proof.
intros.
induction p.
  - simpl. auto.
  - simpl. rewrite -> IHp. auto.
Qed.
Lemma add_poly_length: forall p1 p2,
length p1 = length p2 ->
length(add_dense_poly p1 p2) = length p1.
Proof.
induction p1.
  - simpl. auto.
  - intros.
    rewrite -> add_cons.
    simpl.
    f_equal.
    simpl in H.
    Search(hd).
    destruct p2.
    + simpl in *. exfalso; lia.
    + simpl in *. rewrite -> IHp1. auto. auto.
Qed.

Lemma add_poly_upper: forall p1 p2,
Nat.le (length(add_dense_poly p1 p2)) (max(length p1)(length p2)).
Proof.
induction p1.
  - intros.
    simpl.
    auto.
  - intros.
    induction p2.
    + simpl. auto.
    + simpl.
      Search((S _<=S _)%nat).
      rewrite <- Nat.succ_le_mono.
      apply IHp1.
Qed.

Lemma add_poly_lower: forall p1 p2,
Nat.le (max(length p1)(length p2)) (length(add_dense_poly p1 p2)) .
Proof.
induction p1.
  - intros.
    simpl.
    auto.
  - intros.
    induction p2.
    + simpl. auto.
    + simpl.
      Search((S _<=S _)%nat).
      rewrite <- Nat.succ_le_mono.
      apply IHp1.
Qed.
      
Lemma add_poly_length_max: forall p1 p2,
length(add_dense_poly p1 p2) = max (length p1) (length p2).
Proof.
intros.
apply Nat.le_antisymm.
  -  apply add_poly_upper.
  - apply add_poly_lower.
Qed.

Lemma add_poly_comm: forall p1 p2,
add_dense_poly p1 p2 = add_dense_poly p2 p1.
Proof.
induction p1.
  - simpl. destruct p2.
    + simpl. auto.
    + simpl. auto.
  - simpl.
    destruct p2.
    + simpl. auto.
    + simpl. rewrite -> IHp1. f_equal; lra.
Qed. 

Lemma naive_mult_length_gt_left: forall p1 p2,
Nat.le 1 (length p2) ->
Nat.le (length p1) (length(naive_mult p1 p2)).
Proof.
induction p1.
  - intros. simpl in *. auto. 
  - intros. simpl in *.
    rewrite -> add_poly_length_max.
    rewrite <- scalar_mult_length.
    apply IHp1 in H.
    simpl.
    lia.
Qed.

Lemma naive_mult_length_gt_right: forall p1 p2,
Nat.le 1 (length p1) ->
Nat.le (length p2) (length(naive_mult p1 p2)).
Proof.
destruct p1.
  - intros. exfalso; simpl in H; lia.
  - intros. simpl in *.
    rewrite -> add_poly_length_max.
    rewrite <- scalar_mult_length.
    lia.
Qed.

Lemma naive_mult_length: forall p1 p2,
Nat.le 1 (length p1) ->
Nat.le 1 (length p2) -> 
length(naive_mult p1 p2) = (length p2 + length p1 - 1)%nat.
Proof.
intros.
induction p1.
  - simpl in H; exfalso; lia.
  - destruct p1.
    + simpl.
      rewrite -> add_poly_length_max.
      rewrite <- scalar_mult_length.
      simpl. 
      lia.
    + simpl in *.
      rewrite -> add_poly_length_max.
      rewrite <- scalar_mult_length.
      simpl.
      rewrite -> IHp1 by lia.
      lia. 
Qed.
      
      
Lemma evals_padded: forall p a n j,
evals n j p  = evals n j (p++repeat 0 a).
Proof.
induction a.
  - intros. simpl. rewrite -> app_nil_r; auto.
  - intros.
    induction j.
    + simpl. replace(0:: repeat 0 a) with (repeat 0 (S a)) by auto.
      rewrite <- eval_zeroes_end.
      auto.  
    + simpl. 
      replace(0:: repeat 0 a) with (repeat 0 (S a)) by auto.
      repeat rewrite <- eval_zeroes_end.
      f_equal.
      apply IHj.
Qed.

Lemma eval_mul_padded: forall a p1 p2 x,
Pdense_eval(naive_mult(p1++repeat 0 a)(p2++repeat 0 a)) x = 
Pdense_eval(naive_mult p1 p2) x.
Proof.
intros.
rewrite <- pmul_correct.
repeat rewrite <- eval_zeroes_end.
apply pmul_correct.
Qed.

Lemma evals_mul_padded: forall n j p1 p2 a b,
evals n j (naive_mult(p1++repeat 0 a)(p2++repeat 0 a))
=
evals n j (naive_mult p1 p2 ++ (repeat 0 b)).
Proof.
induction j.
  - intros. simpl.
    repeat rewrite -> eval_mul_padded. rewrite <- eval_zeroes_end. auto.
  - intros. 
    simpl.
    rewrite -> IHj with (b:= b).
    f_equal.
    rewrite -> eval_mul_padded.
    rewrite <- eval_zeroes_end.
    auto.
Qed.

Lemma one_le_2pow: forall n,
  (1 <= 2 ^ n)%nat.
Proof.
induction n.
  - simpl. auto.
  - simpl. apply le_trans with (m:= (2^n)%nat).
    apply IHn.
    lia.
Qed.
Definition dense_fast_mul(p1 p2: dense_poly)(n:nat):=
let p1_pad := p1++(repeat 0 (2^n)%nat) in
let p2_pad := p2++(repeat 0 (2^n)%nat) in
ifft (S n) (pointwise_mul (fft (S n) p1_pad (nth_unit_root(2^(S n))%nat))
                          (fft (S n) p2_pad (nth_unit_root(2^(S n))%nat)) 
                          (2^(S n)-1)%nat).

Lemma dense_fast_mul_correct: forall p1 p2 n x,
  degree_poly p1 = (2^n)%nat -> degree_poly p1 = degree_poly p2 ->
  Pdense_eval (dense_fast_mul p1 p2 n) x = 
  Pdense_eval (naive_mult p1 p2)       x.
Proof.
intros.
unfold dense_fast_mul.
repeat rewrite <-degree_length in *.
rewrite -> H in H0.
assert(length (p1 ++ repeat 0 (2^n)%nat) = (2^(S n))%nat).
  rewrite -> app_length. 
  rewrite -> repeat_length.
  simpl. lia.
rewrite -> fft_correct by (rewrite -> degree_length in H1; auto).
rewrite -> fft_correct.
rewrite -> mul_evals.
rewrite -> evals_mul_padded with (b:= 1%nat).
rewrite <- fft_correct.
rewrite -> icorrect.
rewrite <- eval_zeroes_end.
auto.
(* degree of naive mult *)
all: rewrite <- degree_length.
all: simpl.
rewrite -> last_length.
rewrite -> naive_mult_length.
rewrite -> H; rewrite <- H0.
ring_simplify.
rewrite -> Nat.sub_add.
lia.
apply Nat.le_trans with (m:= (2^n)%nat).
apply one_le_2pow.
lia.
Search(Nat.le 1 _).
rewrite -> H; apply pow_le_1.
rewrite <- H0; apply pow_le_1.

rewrite -> last_length.
rewrite -> naive_mult_length.
    
rewrite -> H.
rewrite <- H0.
ring_simplify.
rewrite -> Nat.sub_add.
lia.
apply Nat.le_trans with (m:= (2^n)%nat).
apply one_le_2pow.
lia.
rewrite -> H.
apply one_le_2pow.
rewrite <- H0.
apply one_le_2pow.
rewrite -> app_length.
rewrite <- H0.
Search(length( repeat _ _)).
rewrite -> repeat_length.
lia.
Qed.
    
Lemma evals_zeroes: forall a w n p,
evals w n (p::repeat 0 a) = evals w n (p::nil).
Proof.
intros.
induction n.
  - simpl.
    rewrite -> pdense_eval_add.
    rewrite -> pdense_eval_zeroes.
    rewrite -> pdense_eval_add.
    unfold Pdense_eval; auto.
  - repeat rewrite -> evals_succ.
    repeat rewrite -> pdense_eval_add.
    rewrite -> pdense_eval_zeroes.
    rewrite -> IHn.
    unfold Pdense_eval; auto.
Qed.

Lemma eval_zero: forall a w n,
evals w n (repeat 0 a) = evals w n nil.
Proof.
intros.
induction n.
  - simpl. rewrite -> pdense_eval_zeroes.
    unfold Pdense_eval; auto.
  - repeat rewrite -> evals_succ.
    rewrite <- IHn.
    rewrite -> pdense_eval_zeroes.
    unfold Pdense_eval; auto.
Qed.
    

Lemma first_unit_root:
nth_unit_root 1 = 1.
Proof.
Admitted.

(*
Fixpoint Pdense_eval'(d:nat) (p: dense_poly) (x:R) : R :=
  match p with
  | nil => 0
  | fn :: p0 => fn * (pow x d) + Pdense_eval' (S d) p0 x
  end.

Definition Pdense_eval(p:dense_poly) (x:R) : R :=
  Pdense_eval' 0 p x.
Definition dense_to_sparse(p:dense_poly):list(nat*R) :=
  dense_to_sparse' 0 p.
*) 
Search(sum).
Fixpoint pdense_ieval' (d:nat) (p: dense_poly) (x:R) : R :=
  match p with
  | nil => 0
  | fn:: p0 => fn * (/ pow x d) + pdense_ieval' (S d) p0 x
  end.

Definition pdense_ieval (p:dense_poly) (x:R): R :=
 match p with
  | nil => 0
  | p   => let n := length p in 1/n * pdense_ieval' 0 p x
  end.

Lemma eval_ieval: forall a p n,
Nat.le 1 n -> Nat.le a n -> Pdense_eval (evals (nth_unit_root n) n p) ((/nth_unit_root n)^a) =
(nth a (evals (/nth_unit_root n) n (evals(nth_unit_root n) n p)) 0).
Proof.
intros.
rewrite -> evals_correct by auto.
auto.
Qed.

Search(ifft).
(*
Definition fun_poly(n:nat) := Fin.t n -> R.
Check(fun_poly).

Definition fun_from_dense(p: dense_poly): nat -> R :=
  let l := length p in
  fun n => match ((length p) - n)%nat with
           |O => 0*n
           |_ => nth n p 0
           end.




Fixpoint summation' (n: nat) (p:dense_poly) (f: nat -> R -> R) :=
  match n with
  | 0 => f n (hd 0 p)
  | S n' => f n (hd 0 p) + summation' (n') (tl p) f
  end.

Definition summation (p:dense_poly) (f:nat -> R -> R) :=
  let n := (length p) in 
  summation' n (rev p) f.

Lemma summation_step: forall p a f,
  summation(a::p) f = f (S(length p)) a + summation p f.
Proof.
unfold summation.
intros.
simpl.
destruct p.
  - simpl. lra.
  - replace(hd 0 (rev (r::p) ++ a :: nil)) with (last (r::p) 0).
    simpl.
    
Lemma DFT_summation: forall p x,
  summation p (fun n a => a*x^n) = Pdense_eval p x.
Proof.
intros.
induction p.
  - unfold summation, Pdense_eval.
    simpl; lra.
  - unfold summation, Pdense_eval.
    simpl. *)

Check(eval_sum_fun).
Lemma snd_dts_step: forall p a j,
snd (nth a (dense_to_sparse' j p) (O,0)) = snd (nth a (dense_to_sparse' (S j) p) (O,0)).
Proof.
induction p.
  - intros. simpl. auto.
  - intros. simpl.
    destruct a0.
    + auto.
    + repeat rewrite <- IHp.
      auto.
Qed.

Lemma fst_dts_step: forall p a j,
Nat.lt a (length p) -> 
S(fst (nth a (dense_to_sparse' j p) (O,0))) = fst (nth a (dense_to_sparse' (S j) p) (O,0)).
Proof.
induction p.
  - intros. simpl in *.
    exfalso; lia.
  - intros; simpl.
    destruct a0.
    + auto.
    +  simpl in H. 
       repeat rewrite <- IHp by lia.
       auto.
Qed.

Lemma nth_dts_snd: forall p a,
Nat.lt a (length p) ->
nth a p 0 = snd (nth a (dense_to_sparse p) (O,0)).
Proof.
induction p.
  - simpl. destruct a.
    all: auto.
  - intros. simpl.
    destruct a0.
    auto.
    rewrite -> IHp.
    unfold dense_to_sparse.
    destruct p.
    auto.
    rewrite <- snd_dts_step.
    auto.
    simpl in *; lia.
Qed. 

Lemma nth_dts_fst: forall p a,
Nat.lt a (length p) ->
fst(nth a (dense_to_sparse p) (O,0)) = a.
Proof.
induction p.
  - intros; simpl in *.
     exfalso; lia.
  - intros.
    simpl.
    destruct a0.
    auto.
    simpl in H.
    rewrite <- fst_dts_step by lia.
    f_equal.
    apply IHp; lia.
Qed.

Definition map_evals_sparse(p:list (nat*R))(w:R) :=
map(fun a => PaxR_eval p (w^fst a)) p.

Search(seq).
Definition map_evals_dense(p: list R)(w:R) :=
map(fun a => Pdense_eval p (w^a)) (seq 0 (length(p))).

Lemma map_nth2: forall e a s f,
Nat.lt a (e) -> nth a (map(fun r => f r)(seq s e)) 0 = f(s+a)%nat.
Proof.
induction e.
  - intros.
    exfalso; lia.
  - intros. 
    simpl.
    destruct a.
    + auto.
    + replace (s + S a)%nat with (S s + a)%nat by lia.
      apply IHe.
      lia.
Qed.

Lemma mevals_dense_correct: forall a p w,
Nat.lt a (length p) ->
nth a (map_evals_dense p w) 0 = Pdense_eval p (w^a).
Proof.
intros.
unfold map_evals_dense.
Search(seq).
apply map_nth2; auto.
Qed.



Lemma map_evals_length: forall p w,
length(map_evals_dense p w) = length p.
Proof.
intros.
unfold map_evals_dense.
rewrite -> map_length.
Search(seq).
rewrite -> seq_length.
auto.
Qed.

Lemma map_evals_nth: forall a p w n,
S n = length p ->
nth a (map_evals_dense p w) 0 = nth a (evals w n p) 0.
Proof.
intros.
rewrite <- evals_length_eq_n with (w:= w)(p:=p)in H.
symmetry in H; rewrite <- map_evals_length with (w:= w) in H.
apply lt_to_all_nth with (a:= a) in H .
auto.
intros.
rewrite -> mevals_dense_correct.
rewrite -> evals_correct.
auto.
all: rewrite -> map_evals_length in H0, H.
all: rewrite -> evals_length_eq_n in H.
all: lia.
Qed.

Lemma map_evals_eq: forall p w n,
S n = length p -> map_evals_dense p w = evals w n p.
Proof.
  intros.
  rewrite <- evals_length_eq_n with (w:= w)(p:=p) in H.
  symmetry in H; rewrite <- map_evals_length with (w:=w) in H.
  apply nth_eq in H.
  auto.
  rewrite -> map_evals_length in H; rewrite -> evals_length_eq_n in H.
  symmetry in H.
  intros.
  apply map_evals_nth with (a:= a)(w:= w) in H.
  auto.
Qed.

Lemma dense_to_sparse_spec: forall (p:dense_poly) a,
dense_to_sparse' a p = combine(seq a (length p)) p.
Proof.
unfold dense_to_sparse.
induction p.
  - auto.
  - intros. 
    simpl.
    rewrite -> IHp.
    auto.
Qed.
    
Lemma sd_map_evals: forall p w,
map_evals_dense p w = map_evals_sparse (dense_to_sparse p) w.
Proof.
intros.
unfold map_evals_dense.
unfold map_evals_sparse.
assert(map(fun a : nat * R => PaxR_eval (dense_to_sparse p) (w ^ fst a))(dense_to_sparse p) =
       map(fun a : nat * R => Pdense_eval p (w^fst a)) (dense_to_sparse p)).
   f_equal.
   apply functional_extensionality.
   intros.
   rewrite -> Peval_dts. auto.
rewrite -> H.
unfold dense_to_sparse; rewrite -> dense_to_sparse_spec.
simpl.
 assert (H1: forall l b, map (fun a : nat * R => Pdense_eval p (w ^ fst a)) (combine (seq b (length l)) l) = map (fun a : nat => Pdense_eval p (w ^ a)) (seq b (length l))).
  {
    (* Prove by induction on l *)
     induction l as [| x xs IHxs].
     - simpl in *. auto.
     - intros. simpl.
       f_equal.
       apply IHxs.
    }
rewrite -> H1. auto.
Qed.

Definition term (d : nat) (x : R) (coeff : R) : R :=
  coeff * (pow x d).

(* Generate the list of terms *)
Fixpoint generate_terms (d : nat) (p : list R) (x : R) : list R :=
  match p with
  | nil => nil
  | fn :: p0 => term d x fn :: generate_terms (S d) p0 x
  end.

(* Sum the list of terms *)
Fixpoint sum_list (l : list R) : R :=
  match l with
  | nil => 0
  | x :: xs => x + sum_list xs
  end.

Lemma gen_terms_scale_nth: forall p b a x,
nth a (generate_terms b p x) 0 * x = nth a (generate_terms (S b) p x) 0.
Proof.
induction p.
  - intros.
    simpl. destruct a. all: lra.
  - intros. simpl. destruct a0.
    + unfold term. rewrite <- tech_pow_Rmult. lra.
    + rewrite -> IHp. auto.
Qed.  
Lemma sum_terms_scale: forall x p b, 
x * sum_list (generate_terms b p x) = sum_list(generate_terms (S b) p x ).
Proof.
induction p.
  - intros. simpl. lra.
  - intros. simpl. 
    rewrite -> Rmult_plus_distr_l.
    f_equal.
    + unfold term. 
      ring_simplify.
      rewrite <- tech_pow_Rmult.
      lra.
    + apply IHp.
Qed.

Lemma eval_terms_eq: forall p x,
Pdense_eval p x = sum_list (generate_terms 0 p x).
Proof.
intros.
unfold Pdense_eval.
induction p.
  - simpl. auto.
  - simpl. rewrite -> pdense_eval_scale.
    rewrite -> IHp.
    unfold term.
    f_equal.
    apply sum_terms_scale.
Qed. 

Definition DFT(n: nat)(p: dense_poly): list R:= 
evals(nth_unit_root (2^n)%nat) (2^n-1)%nat p.

Lemma fft_dft: forall n p,
degree_poly p = (2^n)%nat ->
fft n p (nth_unit_root(2^n%nat)) = DFT n p.
Proof.
intros.
apply fft_correct in H.
auto.
Qed.

Definition iDFT(n:nat)(p: dense_poly): list R :=
evals((1/(2^n-1)) * 1/nth_unit_root(2^n))(2^n-1)%nat p.

Lemma ievals_evals: forall n p,
length p = (2^n)%nat -> iDFT (2^n)%nat (DFT(2^n)%nat p) = p.
Proof.
intros.
unfold iDFT, DFT.
induction n.
  - simpl in *.
    repeat rewrite -> pdense_eval_add.
    rewrite -> degree_one_eval.
    rewrite -> degree_one_eval.
    unfold Pdense_eval; simpl.
Admitted.


Lemma evals_inversed: forall a n p,
(2*n)%nat = length p -> Nat.lt a (2*n)%nat ->
nth a (evals (/nth_unit_root (2*n)%nat) (2*n-1)%nat (evals(nth_unit_root (2*n)%nat) (2*n-1)%nat p)) 0=
n * nth a p 0.
Proof.
intros.
rewrite -> evals_correct.
rewrite -> eval_terms_eq.
induction p.
  - simpl in H.
    exfalso; lia.
  - simpl.

  
  




    
     

    
   
         

    
    
    
(* type words here to prevent weird thing happening *)
      
    
         
       
        

       

       
    
    
    
    
    
    

    
      
    

    
    
   
    

    
    
    
    

    
     

      
      
    
    
    
      
    
    
    


