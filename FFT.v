From VerifiedCalculus Require Export PolynomialModels.
From VerifiedCalculus Require Export PolynomialModelAdd.
Require Import Arith.
Require Export Reals.
Require Import Lia.
Require Import Lra.
Require Import Ring.
Context `{F : Type} `{FltF : Float F}.
Open Scope R_scope.
Definition i := sqrt(-1).

Definition nth_unit_root(n:nat): R :=
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

Lemma PaxR_correct: forall p x,
 Pax_eval p x = PaxR_eval (PinjR p) x.
Proof. 
  intros; unfold PinjR; induction p.
  - simpl; auto.
  - rewrite -> Pax_eval_cons.
      simpl; lra. 
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

(* Definition sparse_to_dense (p : list (nat * R)) : dense_poly :=
  let d := max_degree_R p in
  let
    fix create (deg : nat) (p : list (nat * R)) : list R :=
      match deg with
      | 0 => nil
      | S n' =>
        let coeff := fold_left 
        (fun acc '(d, c) => if Nat.eqb d deg then c + acc else acc) p 0 in
        coeff :: create n' p
      end
  in
  create d p. *)

Fixpoint sparse_to_dense' (d:nat) (p:list(nat*R)) : dense_poly :=
  match d, p with
  | _,nil => nil
  | _,a::p' => if Nat.eqb (fst a) d then snd a :: sparse_to_dense' (S d) p' else
              0 :: sparse_to_dense' (S d) p'
end.

Definition sparse_to_dense (p : list(nat*R)) : dense_poly :=
  sparse_to_dense' 0 p.

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
(* Lemma Peval_step1: forall p fn d x,
Pdense_eval' d (fn::p) x = fn *(pow x d) + Pdense_eval' (S d) (p) x.
intros. simpl. lra. Qed.
 
Lemma Peval_step: forall p d x,
Pdense_eval' d p x = hd 0 p *(pow x d) + Pdense_eval' (S d) (tail p) x.
intros. induction p. simpl. lra. simpl. lra. Qed.

(*Lemma Peval_div: forall p d x,
Pdense_eval d p x = Pdense_eval (S d) p x / x.
intros. induction p. simpl. lra. simpl. rewrite -> Peval_step. symmetry.
rewrite -> Peval_step. *) *)

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

Lemma sparse_to_dense_step: forall p a n, 
is_sorted_fst(a::p) ->
fst a =? n = true -> sparse_to_dense' (S n) (a::p) = 0::sparse_to_dense' n p.
Proof. 
  intros p0 a0. induction p0.
  -  simpl. intros. assert (fst a0 =? (S n) = false). Search(_=?_). rewrite Nat.eqb_eq in H0.
    rewrite Nat.eqb_neq. rewrite -> H0. lia. rewrite -> H1. auto. 
  - intros. simpl. 
    destruct (fst a =? (S (S n))) eqn: ea.
      + rewrite -> Nat.eqb_eq in ea. assert(fst a =? n = false). rewrite -> Nat.eqb_neq. 
        rewrite -> ea. lia. rewrite -> H1. assert (fst a0 =? (S n) = false). Search(_=?_). rewrite Nat.eqb_eq in H0.
    rewrite Nat.eqb_neq. rewrite -> H0. lia. rewrite -> H2. unfold sparse_to_dense'. simpl. Abort.
      



Lemma Peval_dts: forall p x,
PaxR_eval (dense_to_sparse p) x = Pdense_eval p x.
Proof.
  intros. 
  unfold dense_to_sparse,Pdense_eval. 
  apply Peval_dts'.
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

(* Lemma degree_even_odd: forall p n,
 degree_poly p = (2*n)%nat -> 
  degree_poly(even_poly_D p) + degree_poly(odd_poly_D p) = (2*n)%nat.
Proof.
induction p.
  - intros. simpl. 
    destruct n.
    + simpl. lra.
    + discriminate H.
  - intros.
    unfold even_poly_D; unfold odd_poly_D.
    simpl.
    unfold degree_poly in *.
    simpl in *. *)
    
    
    
       

    
    

(* Lemma sparse_to_dense_step: forall p x (n: nat) a ,
is_sorted_fst (a::p) -> fst a =? n = true -> x*Pdense_eval' (S n) (sparse_to_dense' (S n) (a::p)) x = Pdense_eval' n (sparse_to_dense' n (a::p)) x - snd a * x^n.
Proof.
  intros p x n. induction n.
    - induction p.
        + simpl. intros. rewrite -> H0. simpl. assert (fst a =? 1 = false). Search( _=?_).
          rewrite -> Nat.eqb_eq in H0. rewrite -> Nat.eqb_neq. rewrite -> H0. auto. 
          rewrite -> H1. simpl. lra.
        + intros. simpl. rewrite -> Nat.eqb_eq in H0. rewrite -> H0. simpl. 
          destruct(fst a =? 1) eqn: E. 
            (* case fast a = 1*)
             rewrite -> Nat.eqb_eq in E. rewrite -> E. simpl. 
             repeat rewrite -> pdense_eval_scale. rewrite <- pdense_eval_scale. assert (0*(x*1) = 0) by lra.
             rewrite -> H1. assert(0*(x*(x*1)) = 0) by lra. rewrite -> H2. 
             ring_simplify. Abort.
  


Lemma Peval_std': forall p x,
  is_sorted_fst p -> Pdense_eval (sparse_to_dense p) x = PaxR_eval p x.
  induction p.
   - auto.
   - intros. unfold dense_to_sparse,sparse_to_dense. simpl. 
      destruct (fst a =? 0) eqn:E.
        + rewrite -> Nat.eqb_eq in E. rewrite -> E. unfold Pdense_eval. simpl. 
          rewrite -> pdense_eval_scale.
          rewrite <- IHp. simpl. unfold Pdense_eval, sparse_to_dense. 
          assert(x*Pdense_eval' 0 (sparse_to_dense' 1 p) x = 
                  Pdense_eval' 0 (sparse_to_dense' 0 p) x - snd a * 1). 
                  unfold sparse_to_dense'. Abort.  *)
          

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

         
      
(* FRESH START *)
(* unit root: cos((2*PI)/n) + i * sin ((2*PI)/n) = e^((2*PI*I)/n).*)  
(* unit root properties: *)
(* Lemma even_and_odd_D: forall p x,
 Pdense_eval (even_poly_D p) (x^2) + x*Pdense_eval(odd_poly_D p) (x^2) =
 Pdense_eval p x.
 Qed. *)
Lemma unit_root_k_squares: forall n k,
((nth_unit_root (2*n))^k)^2 = (nth_unit_root n)^k.
Proof.
Admitted.

Lemma unit_root_symmetry: forall n k,
nth_unit_root (2*n)^(k+n) = - (nth_unit_root (2*n))^k.
Proof.
intros. unfold nth_unit_root. Admitted.  

Fixpoint w_powers (w:R)(n:nat): list R:=
match n with
  |O     => 1::nil
  |S(n') => w_powers w n' ++ (w^n)::nil
end.

Lemma sum_mod_O: forall k j n,
Nat.le j (n-1) -> n mod k = O -> 
fold_right Rplus 0 (w_powers((nth_unit_root n^k))(j)) = n.
Proof.
Admitted.

Lemma sum_mod_else: forall k j n,
Nat.le j (n-1) -> n mod k <> O ->
fold_right Rplus 0 (w_powers((nth_unit_root n^k))(j)) = O.
Proof.
Admitted.
(*Lemma unit_root_sums: forall n k j,
k mod n <> 0 -> Nat.le j (n-1) -> 
*)
Lemma unit_root_squares: forall n,
nth_unit_root(2*n)^2 = nth_unit_root(n).
Proof.
intros.
replace (nth_unit_root (2 * n)) with (nth_unit_root (2 * n)^1) by lra.
replace (nth_unit_root n) with (nth_unit_root n ^1) by lra.
apply unit_root_k_squares.
Qed.




Lemma FFT_inductive_step_even: forall p j n,
Nat.le 1 n ->
Pdense_eval p ((nth_unit_root (2*n)^j)) = 
Pdense_eval(even_poly_D p)(nth_unit_root n^j) + 
nth_unit_root (2*n)^j * Pdense_eval(odd_poly_D p)(nth_unit_root n ^j).
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
    apply even_and_odd_D. 
Qed.


Lemma FFT_inductive_step_odd: forall p j n,
Nat.le 1 n -> 
Pdense_eval p (nth_unit_root (2*n)^(j+ n)) = 
Pdense_eval(even_poly_D p)(nth_unit_root n ^j) - 
(nth_unit_root (2*n) ^j) * Pdense_eval(odd_poly_D p)(nth_unit_root n^j).
Proof.
  unfold Nat.le. 
  destruct n.
  (* case n = 0 *)
   - intros. 
     exfalso. 
     lia.
  (* induction starts at n = 1*)
   - intros.
       assert(forall n x p, x - n*p = x+(-n*p)) by (intros; lra).
       rewrite -> H0.
       rewrite <- unit_root_symmetry.
       assert(forall n j, nth_unit_root (2*n) ^(2*j+2*n) = 
              nth_unit_root (2*n) ^ (j*2)).
              intros. 
              assert(nth_unit_root (2*n0) ^ (2*j0 + 2 * n0) =
                     nth_unit_root (2*n0) ^ (2*j0 + n0 + n0)) by (f_equal; lia). 
              rewrite -> H1.
             repeat rewrite -> unit_root_symmetry.
             rewrite -> Ropp_involutive.
             f_equal.
             lia. 
       assert(nth_unit_root(S n) ^ j = (nth_unit_root(2* S n)^j)^2) by
          (rewrite -> unit_root_k_squares; reflexivity). 
       rewrite -> H2.
       rewrite <- pow_mult.
       rewrite <- H1. 
       assert(nth_unit_root (2 * S n) ^ (2 * j + 2 * S n) = 
              (nth_unit_root (2 * S n) ^ (j+S n)) ^ 2) by
           (rewrite <- pow_mult; f_equal; lia).
       rewrite -> H3.
       symmetry.
       apply even_and_odd_D.
Qed.

Lemma FFT_base_case: forall p,
degree_poly p = 1%nat -> Pdense_eval p (nth_unit_root 1%nat) = hd 0 p.
Proof.
  intros; unfold nth_unit_root. 
  apply degree_one_eval. 
  apply H.
Qed.

Fixpoint powers2(n:nat):list nat :=
  match n with
  | O    => 1%nat::nil
  | S n' => (2^n)%nat :: powers2(n')
  end.


Lemma powers2_succ_head: forall n,
 (2 * hd O (powers2 n))%nat = hd O (powers2 (S n)).
Proof.
intros. destruct n.
 - simpl. 
   reflexivity.
 - simpl.
   lia.
Qed. 

Lemma powers2_succ: forall n,
(2 * hd O (powers2 n))%nat::(powers2 n) = powers2 (S n).
Proof.
intros. destruct n.
  - simpl.
    reflexivity.
  - simpl. auto.
Qed.
    

Lemma powers2_half : forall n a p,
  Nat.le 1 n -> powers2 n = a::p -> a = (2*hd O p)%nat.
Proof.
intros. destruct n.
- lia.
- rewrite <- powers2_succ in H0.
    inversion H0. simpl. lia.
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
  | O => nil
  | S(n') => evals w n' p ++ Pdense_eval p (w^n) :: nil 
  end.

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

Fixpoint make_two (y_e y_o: list R) (n:nat)(w: R) (j: nat): (list R * list R) :=
  match n with
  |O => (nil, nil)
  |S(n') => let (list_pos, list_neg) := make_two y_e y_o n' w (S j) in
            (list_pos ++ ((nth n y_e O) + w^j * (nth n y_o O)) :: nil , 
            list_neg ++ ((nth n y_e O) - w^j * (nth n y_o O)) :: nil)
end.

Definition m2_l (y_e y_o: list R)(w: R): list R :=
 let n      := degree_poly y_e in
 let(l1,l2) := make_two y_e y_o n w O in
                      l1 ++ l2.

Fixpoint fft(n:nat)(p:list R)(w:R):list R :=
  match n with
  | O => p
  | S(n')     => let y_e := fft(n')(even_poly_D p)(w^2%nat) in
                 let y_o := fft(n')(odd_poly_D p)(w^2%nat) in 
                 m2_l y_e y_o w
  end.

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
degree_poly (evals w n p) = n.
Proof.
induction n.
  - simpl.
    auto.
  - simpl.
    rewrite <- degree_concat.
    auto.
Qed.

Lemma m2_l_even_base: forall n p y_e y_o,
Nat.le 1 n -> degree_poly p = (2*n)%nat ->
y_e = evals (nth_unit_root (n)) (n) (even_poly_D p) ->
y_o = evals (nth_unit_root (n)) (n) (odd_poly_D p) ->
hd 0 (fst(make_two y_e y_o n (nth_unit_root(2*n)) O)) = 
hd 0 (evals (nth_unit_root (2*n)) (n) p).
Proof.
intros.
induction n.
  - exfalso; lia.
  - Admitted. 

    
    


Lemma m2_l_correct: forall n y_e y_o p,
Nat.le 1 n -> degree_poly p = (2*n)%nat ->
y_e = evals (nth_unit_root (n)) (n) (even_poly_D p) ->
y_o = evals (nth_unit_root (n)) (n) (odd_poly_D p) ->
m2_l y_e y_o (nth_unit_root(2*n)) = evals (nth_unit_root (2*n)) (2*n) p.
Proof.
Admitted.
(*
    replace(y_e) with (m2_l (evals (nth_unit_root (2 ^ (n - 1))) 
        (2 ^ (n - 1)) (even_poly_D y_e)) (evals (nth_unit_root (2 ^ (n - 1))) 
        (2 ^ (n - 1)) (odd_poly_D y_e)) (nth_unit_root (2 ^ n))).
   
    replace(y_o) with (m2_l (evals (nth_unit_root (2 ^ (n - 1))) 
        (2 ^ (n - 1)) (even_poly_D y_o)) (evals (nth_unit_root (2 ^ (n - 1))) 
        (2 ^ (n - 1)) (odd_poly_D y_o)) (nth_unit_root (2 ^ n))).
    apply IHn. *)


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

(*Lemma listops : forall p e o w n,
Nat.le 1 (2^n) -> degree_poly p = (2*(2^n))%nat ->
e = evals (nth_unit_root (2^n)) (2^n) (even_poly_D p) ->
o = evals (nth_unit_root (2^n)) (2^n) (odd_poly_D p) ->
w = w_powers(nth_unit_root (2^n)) (2^n) ->
map3(fun x w y => x + w*y) e o w = evals (nth_unit_root (2*(2^n))) (2^n) p.
Proof.
induction n.
  - intros. simpl in *.
    unfold Pdense_eval in *.
    unfold map3.
    Search(map).
    
    
  - intros.
    Search(map).
    destruct p.
    + assert(degree_poly nil= O) by (apply degree_nil; auto).
      exfalso; lia.

    + *)
    
    
    
    
    



Lemma fft_correct: forall n p,
degree_poly p = (2^n)%nat -> 
fft n p (nth_unit_root(2^n%nat)) = evals(nth_unit_root (2^n)%nat) (2^n)%nat p.
Proof.
induction n.
  - intros.
    simpl in *.
    assert(Pdense_eval p (nth_unit_root 1) = hd 0 p) by (apply FFT_base_case in H; auto).
    replace (nth_unit_root 1 * 1) with (nth_unit_root 1) by lra.
    rewrite -> H0.
    destruct p.
    + discriminate H.
    + simpl in *.
      assert(p = nil).
      rewrite -> degree_add in H.
      assert(degree_poly p = O) by lia.
      apply degree_nil; auto.
      rewrite -> H1; auto.
  - intros.
    simpl.
(* even poly degree *)
    assert(degree_poly (even_poly_D p) = (2^n)%nat).
      apply even_half_deg in H.
      apply H.
      apply pow_le_1.
(* odd poly degree *)
    assert(degree_poly (odd_poly_D p) = (2^n)%nat).
      apply odd_half_deg.
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




(*Lemma inversion: forall p n,
degree_poly p = (2^n)%nat -> 
fft n (fft n p (nth_unit_root(2^n))) (1/n*1/nth_unit_root(2^n%nat)) =  p.
Proof.
intros.
*)

Definition ifft(n:nat)(p:list R):list R :=
  let w:= 1/nth_unit_root (2^n) in 
  fft n p w. 

Definition div_n (n:nat)(r:R) := r/n.
Definition div_n_list (r:list R)(n:nat):=
map (div_n  n) r.


Lemma ievals: forall n p,
degree_poly p = (2^n)%nat -> 
ifft n (evals(nth_unit_root (2^n)%nat) (2^n)%nat p) = div_n_list p (2^n).

induction n.
  - intros. unfold ifft. simpl. simpl.
    
    simpl in H.
    destruct p.
    + assert(degree_poly nil = O) by (apply degree_nil; auto).
      exfalso. lia.
    + rewrite -> degree_add in H.
      apply eq_add_S in H.
      apply degree_nil in H.
      rewrite -> H.
      rewrite -> pdense_eval_add.
      unfold Pdense_eval.
      simpl.
      f_equal.
      unfold div_n.
      simpl.
      lra.
  - intros.
    unfold ifft in *.
    Search(fft).
    rewrite <- fft_correct.
    Search(nth_unit_root).
    replace(div_n_list p (2 ^ S n)) with (map(fun n => 2*n) (div_n_list p (2 ^ n))).
    simpl.
    replace (nth_unit_root (2 ^ n + (2 ^ n + 0)) *
         (nth_unit_root (2 ^ n + (2 ^ n + 0)) * 1)) with (nth_unit_root(2^n)).
    replace (nth_unit_root (2 ^ n + (2 ^ n + 0))) with (nth_unit_root(2*2^n)).
    rewrite -> fft_correct. rewrite -> fft_correct.
    Search(m2_l). 
    assert(m2_l
           (evals (nth_unit_root (2 ^ n)) 
              (2 ^ n) (even_poly_D p))
           (evals (nth_unit_root (2 ^ n)) 
              (2 ^ n) (odd_poly_D p))
           (nth_unit_root (2 * 2 ^ n)) = evals (nth_unit_root (2 * 2^n)) (2 * 2^n) p).
    apply m2_l_correct.
      apply pow_le_1.
      all: auto.
    rewrite -> H0.
    
Abort.
 

Lemma icorrect : forall n p x,
degree_poly p = (2^n)%nat -> 
Pdense_eval (ifft n (fft n p (nth_unit_root(2^n)))) x = Pdense_eval p x.
Proof.

  induction n.
  - simpl. reflexivity.
  - intros. simpl.

    replace (nth_unit_root (2 ^ n + (2 ^ n + 0)) *
         (nth_unit_root (2 ^ n + (2 ^ n + 0)) * 1)) with (nth_unit_root(2^n)).
    rewrite -> fft_correct.
    rewrite -> fft_correct.
    simpl in H. ring_simplify in H.
    Search(m2_l).
    replace ((m2_l
     (evals (nth_unit_root (2 ^ n)) (2 ^ n)
        (even_poly_D p))
     (evals (nth_unit_root (2 ^ n)) (2 ^ n)
        (odd_poly_D p))
     (nth_unit_root (2 ^ n + (2 ^ n + 0))))) with (evals (nth_unit_root (2 * n)) (2 * n) p).
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
  | nil => 0::nil
  | h1 :: t1 => add_dense_poly (scalar_mult h1 p2) (naive_mult t1  p2)
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
    + simpl. lra.
    + simpl. lra. 
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
naive_mult (a::p1) p2 = add_dense_poly (scalar_mult a p2) (naive_mult p1 p2).
Proof.
intros.
simpl. reflexivity. Qed.

Lemma mul_nil: forall p1,
naive_mult p1 nil = 0::nil.
Proof.
intros.
induction p1.
  - simpl. auto.
  - simpl. apply IHp1.
Qed.

Fixpoint new_eval(p:dense_poly)(x:R) :R :=
match p with
  | nil => 0
  | a :: p' => a + x * (new_eval p' x)
  end.

Lemma new_eval_same: forall p x,
Pdense_eval p x = new_eval p x.
Proof.
intros. induction p.
  - unfold Pdense_eval; simpl; auto.
  - simpl. rewrite -> pdense_eval_add. f_equal. f_equal. apply IHp.
Qed.

Lemma pmul_correct: forall p1 p2 x,
Pdense_eval p1 x * Pdense_eval p2 x = Pdense_eval(naive_mult p1 p2) x.
Proof.
unfold Pdense_eval.
induction p1.
  - intros.
    simpl in *.
    lra.
  - intros.
    rewrite -> mul_cons.
    rewrite -> add_correct.
    rewrite -> scalar_correct.
    ring_simplify.
    rewrite <- IHp1.
    simpl.
    
    f_equal.
    simpl.
    
    
    
   
    

    
    
    
    

    
     

      
      
    
    
    
      
    
    
    


