From VerifiedCalculus Require Export PolynomialModels.
From VerifiedCalculus Require Export PolynomialModelAdd.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Arith.
Require Export Reals.
Require Import Lia.
Require Import Lra.
Require Import Ring.
Require Import Reals.Rtrigo.

From Coquelicot Require Import Complex.
From Coquelicot Require Import Hierarchy.


Section PMtoR.
(* Defining sparse polynomials over reals and their relation to 
   sparse polynomials over floats*)
Context `{F : Type} `{FltF : Float F}.
Open Scope R_scope.

(* From float polynomial to real polynomial *)
Fixpoint PinjR(p:list(nat*F)) : list (nat*R) :=
  match p with
  | nil => nil
  | a1::p' => (fst(a1),FinjR(snd a1)) :: PinjR p'
end.

(* evaluation real polynomial*)
Fixpoint PaxR_eval (p:list (nat*R)) (x:R) : R :=
    match p with
    | nil => 0
    | fn :: p0 =>  ((snd fn) * (pow x (fst fn))) + PaxR_eval p0 x
    end.

(* evaluating a float polynomial has the same result as evaluating a real
   polynomial after casting it from float *)
Lemma PaxR_correct: forall p x,
 Pax_eval p x = PaxR_eval (PinjR p) x.
Proof. 
  intros; unfold PinjR; induction p.
  - simpl; auto.
  - rewrite -> Pax_eval_cons.
      simpl; lra. 
Qed.

(* cons function to help with induction *)
Lemma PaxR_eval_cons: forall (p1 : list (nat * R)) (a0:nat*R) (y : R),
  PaxR_eval (a0 :: p1) y =
  snd a0 * y ^ fst a0 + PaxR_eval p1 y.
Proof.
  intros; simpl; reflexivity.
Qed.

End PMtoR.

Section dense_poly_r.
(* Defining dense polynomials over reals and functions to move between
   dense and sparse representation *)
Open Scope R_scope.
(* dense polynomials as a single list of reals *)
Definition dense_poly := list R.

(* casts dense poly to a sparse one *)
Fixpoint dense_to_sparse' (d:nat)(p:dense_poly) : list(nat*R) :=
    match p with
    | nil => nil
    | fn :: p0 => (d,fn) :: dense_to_sparse' (S d) p0
    end.
(* recursive helper function for evaluation *)
Fixpoint Pdense_eval'(d:nat) (p: dense_poly) (x:R) : R :=
  match p with
  | nil => 0
  | fn :: p0 => fn * (pow x d) + Pdense_eval' (S d) p0 x
  end.
(* evaluation function for dense polynomial *)
Definition Pdense_eval(p:dense_poly) (x:R) : R :=
  Pdense_eval' 0 p x.

(* scaling the helper function at higher degree input
  back to the original eval function *)
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
(* property to help inductive arguments over p*)
Lemma pdense_eval_add : forall a p x, Pdense_eval(a::p)x = a + x*Pdense_eval(p)x.
Proof.
  intros; unfold Pdense_eval; simpl.
  f_equal.
    - lra.
    - apply pdense_eval_scale.
Qed.
(* casting dense to sparse polynomials *)
Definition dense_to_sparse(p:dense_poly):list(nat*R) :=
  dense_to_sparse' 0 p.

(* correctness of dense to sparse helper function *)
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
(* correctness of dense to sparse *)
Lemma Peval_dts: forall p x,
PaxR_eval (dense_to_sparse p) x = Pdense_eval p x.
Proof.
  intros. 
  unfold dense_to_sparse,Pdense_eval. 
  apply Peval_dts'.
 Qed.
(* helper function for sparse to dense casting function *)
Fixpoint sparse_to_dense' (d:nat) (p:list(nat*R)) : dense_poly :=
  match p with
  |nil => nil
  |a::p' => (repeat 0 ((fst a)-d)) ++ snd(a) :: sparse_to_dense' (S(fst a))p'
end.

(* sparse to dense casting function *)
Definition sparse_to_dense (p : list(nat*R)) : dense_poly :=
  sparse_to_dense' 0 p.

(* auxiliary lemma for the sparse to dense proof of correctness *)
Lemma std_add: forall p n a,
sparse_to_dense' n (a::p) = repeat 0 (fst a - n) ++ snd(a) :: sparse_to_dense' (S(fst a))p.
Proof.
intros. simpl. auto.
Qed.

(* auxiliary lemma for the sparse to dense proof of correctness *)
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
(* auxiliary lemma for the sparse to dense proof of correctness *)
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

(* auxiliary lemma for the sparse to dense proof of correctness *)
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

(* auxiliary lemma for the sparse to dense proof of correctness *)
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

(* evaluation on a list filled with zeroes is always 0 *)
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

(* evaluation of a padded polynomial is the same result as without padding *)
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

(* auxiliary lemma to prove sparse to dense correctness *)
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
  

(* correctness of sparse to dense *)       
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
End dense_poly_r.

Section complex_polys.
Open Scope C_scope.


(* Split a complex equality into two real equalities *)
Lemma c_proj_eq: forall  c1 c2: C,
fst c1 = fst c2 -> snd c1 = snd c2 -> c1 = c2.
Proof.
intros.
destruct c1, c2.
simpl in *.
subst.
reflexivity.
Qed.

Definition dense_cpoly:= list C.

(* casting a real polynomial into a complex one *)
Fixpoint p_RtoC(p:dense_poly): dense_cpoly:=
  match p with
  | nil => nil
  | fn::p' => RtoC(fn)::p_RtoC(p')
  end.

(* evaluation helper function *)
Fixpoint complex_eval' (d:nat)(p: dense_cpoly)(c:C): C :=
  match p with
  | nil => 0
  | fn::p0 => fn * (c^d) + complex_eval' (S d) p0 c
  end.
(* function for evaluating complex polynomials at complex numbers *)
Definition complex_eval (p:dense_cpoly)(c:C) : C :=
  complex_eval' 0 p c.

(* scaling function for the evaluation helper function *)
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

Notation "p [ x ]" := (complex_eval p x) (at level 10, no associativity).


(* This lemma helps for inductive arguments over p involving evaluation *)
Lemma complex_add: forall a p x, 
(a::p)[x] = a + x * p[x].
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

Definition poly_eq(p1:dense_poly)(p2: dense_cpoly) :=
 forall x:R, RtoC(Pdense_eval p1 x) = p2[RtoC x].

Search(RtoC _ = _%R).
Lemma poly_RtoC_eq: forall p,
poly_eq(p)(p_RtoC p).
Proof.
intros.
unfold poly_eq.
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
(* This function returns the complex nth unit root *)
Definition nth_unit_root(n:nat): C :=
  cos((2*PI)/n) + Ci * sin ((2*PI)/n).

Lemma unit_root_incr: forall x y : R,
(cos(x)+Ci*(sin x))*((cos y) + Ci * sin y) =
cos(x+y) + Ci * (sin (x+y)).
Proof.
  intros.
  rewrite -> cos_plus.
  rewrite -> sin_plus.
  apply c_proj_eq.
  simpl.
  ring_simplify. auto.
  simpl; ring_simplify.
  auto.
Qed.

Lemma unit_root_k_squares: forall n k,
n<> O -> ((nth_unit_root (2*n))^k)^2 = (nth_unit_root n)^k.
Proof.
 intros.
 unfold nth_unit_root.
 replace(2 * PI / n)%R with ((2 * PI / (2 * n)%nat)+(2 * PI / (2 * n)%nat))%R.
 rewrite <- unit_root_incr.
 replace(((cos (2 * PI / (2 * n)%nat) + Ci * sin (2 * PI / (2 * n)%nat)) *
 (cos (2 * PI / (2 * n)%nat) + Ci * sin (2 * PI / (2 * n)%nat)))) 
  with((cos (2 * PI / (2 * n)%nat) + Ci * sin (2 * PI / (2 * n)%nat))^2) by ring.
 repeat rewrite <- Cpow_mult_r.
 f_equal.
 ring.
 symmetry.
 Search(_/(_*_)%nat)%nat.
 rewrite <- Rdiv_Rmult_simplify with (z:=2%nat).
 ring_simplify.
 rewrite -> mult_INR.
 ring_simplify.
 replace(INR 2%nat) with 2%R by (simpl; auto).
 field.
 apply not_0_INR; auto.
 simpl.
 lra.
 apply not_0_INR; auto.
Qed.

Lemma pow_n_to_1: forall n,
nth_unit_root(2^n)^(2^n) = 1.
Proof.
intros.
  induction n.
  - simpl. 
    unfold nth_unit_root.
    simpl.
    ring_simplify.
    replace(2*PI/1)%R with (2*PI)%R by lra.
    rewrite -> cos_2PI, sin_2PI.
    ring.
  - simpl.
    replace(2 ^ n + (2 ^ n + 0))%nat with (2*(2^n))%nat by lia.
    replace(nth_unit_root (2 * 2 ^ n) ^ (2 * 2 ^ n)) with
            ((nth_unit_root (2 * 2 ^ n)%nat ^ (2 ^ n)) ^2).
    rewrite -> unit_root_k_squares with (n:= (2^n)%nat).
    apply IHn.
    pose proof pow_le_1. 
    specialize H with (n:=n).
    lia.
    rewrite <- Cpow_mult_r.
    f_equal; lia.
Qed.

Lemma unit_root_symmetry: forall n k,
nth_unit_root (2^S n)^(k+(2^n)) = - (nth_unit_root (2^ S n))^k.
Proof.
 induction n.
  - simpl.
    unfold nth_unit_root.
    simpl.
    replace(2 * PI / (1+1))%R with (PI) by lra.
    rewrite -> cos_PI, sin_PI.
    replace((-1 + Ci * 0)) with (-(RtoC 1)) by ring.
    induction k.
    + simpl. ring.
    + simpl. rewrite -> IHk.
      ring.
  - intros.
    replace(2^S(S n))%nat with (2*(2^S n))%nat by (simpl; lia).
    replace(k+2^S n)%nat with (k+2^n*2)%nat by (simpl; lia).
    rewrite -> Cpow_add_r.
    rewrite -> Cpow_mult_r.
    rewrite -> unit_root_k_squares.
    ring_simplify.
    rewrite -> Cmult_comm.
    f_equal.
    replace(RtoC (- 1)) with (-(RtoC 1)) by ring.
    rewrite <- pow_n_to_1 with(n:= (S n)%nat).
    rewrite <- IHn.
    rewrite -> Cpow_add_r.
    rewrite -> pow_n_to_1.
    ring.
    pose proof pow_le_1.
    specialize H with (n:= S n).
    lia.
Qed.

Notation "\w_ n " := (nth_unit_root n) (at level 10, no associativity).

Lemma unit_root_squares: forall n,
\w_(2^S n)^2 = \w_(2^ n).
Proof.
intros.
replace (nth_unit_root (2 ^ S n)) with (nth_unit_root (2 ^ S n)^1).
replace (nth_unit_root (2^n)) with (nth_unit_root (2^n) ^1).
replace(2^S n)%nat with (2*(2^n))%nat by (simpl; lia).
rewrite -> unit_root_k_squares.
auto.
pose proof pow_le_1.
specialize H with (n:= n).
lia.
apply c_proj_eq.
f_equal. ring.
f_equal; ring.
ring.
Qed.
Lemma unit_root_nonzero: forall n,
(nth_unit_root(2^n)) <> 0.
Proof.
intros.
  pose proof pow_n_to_1.
  induction n.
  - simpl. 
    unfold nth_unit_root.
    simpl. 
    replace(2*PI/1)%R with (2*PI)%R by lra.
    rewrite -> cos_2PI, sin_2PI.
    intros Hf.
    apply C1_nz.
    replace(1+ Ci * 0) with (RtoC 1) in Hf by ring.
    auto.
  - intros Hf.
    specialize H with (n:= S n).
    apply IHn.
    pose proof unit_root_squares.
    specialize H0 with (n:= n).
    rewrite <- H0.
    rewrite -> Hf.
    ring.
Qed.

Lemma inverse_to_1: forall n1 n2,
n1<> RtoC 0 -> n2 <> RtoC 0 -> n1 * n2 = 1 -> n2 = /n1.
Proof.
intros.
  Search(_*_ = RtoC 1).
  simpl.
  field_simplify.
  Search(_*_ = _).
  rewrite <- Cinv_l with (r:= n1) in H1.
  ring_simplify in H1.
  Search(_*_ = _*_).
  assert (Hinv: / n1 * (n1 * n2) = / n1 * (n1 * / n1)).
  rewrite H1. reflexivity.
  repeat rewrite -> Cmult_assoc in Hinv.
  rewrite -> Cinv_l  in Hinv.
  replace(n2) with (1*n2) by ring.
  apply Hinv.
  all:auto.
Qed.
  
Lemma inverse_unit_root: forall n,
\w_ (2 ^ n) ^ (2 ^ n - 1) = / \w_ (2 ^ n).
Proof.
  intros.
  pose proof pow_n_to_1.
  specialize H with (n:= n).
  assert(\w_ (2^n)^(2^n - 1) * \w_(2^n) = 1).
  replace(\w_ (2 ^ n) ^ (2 ^ n - 1) *\w_(2^n)) with (\w_ (2 ^ n) ^ (2 ^ n - 1) *\w_(2^n)^1) by ring.
  rewrite <- Cpow_add_r.
  pose proof pow_le_1.
  specialize H0 with (n:=n).
  rewrite <- H.
  f_equal.
  lia.
  apply inverse_to_1.
  apply unit_root_nonzero.
  intros Hf.
  rewrite -> Hf in H0.
  ring_simplify in H0.
  apply C1_nz.
  symmetry; auto.
  rewrite <- H0.
  ring.
Qed.
  
Lemma even_powered_n_symmetry: forall n a e,
- \w_ (2^S n) ^ (a * S (2 * e)) =
- \w_ (2^S n) ^ (a * S (2 * e) + 2 * e * (2^n)).
Proof.
intros.
induction e.
  - f_equal; f_equal. lia.
  - replace(a * S (2 * S e))%nat with(a * (S (2 * e)+2))%nat by lia.
    replace(a * (S (2 * e) + 2))%nat with (2*a + a*(S (2*e)))%nat by lia.
    Search(_ ^(_+_)).
    rewrite -> Cpow_add_r.
    ring_simplify.
    replace(-1 * \w_ (2^S n) ^ (2 * a) * \w_ (2^S n) ^ (a * S (2 * e))) with 
    ( - \w_ (2^S n) ^ (a * S (2 * e))* \w_ (2^S n) ^ (2 * a)) by ring.
    rewrite -> IHe.
    ring_simplify.
    replace(-1 * \w_ (2 ^S n) ^ (2 * a + a * S (2 * e) + 2 * S e * (2^ n))) with
     (-1 * \w_ (2 ^ S n) ^ (a * S (2 * e) + 2 * S e *(2^n))*\w_ (2 ^ S n) ^ (2 * a)).
    f_equal. f_equal.
    replace(a * S (2 * e) + 2 * S e * 2^ n)%nat with (((a * S (2 * e) + 2 * e * 2^n) + (2^n)) + (2^n))%nat by lia.
    repeat rewrite -> unit_root_symmetry.
    ring_simplify.
    auto.
    Search(_(_^_)).
    replace(-1 * \w_ (2 ^ S n) ^ (a * S (2 * e) + 2 * S e * 2 ^ n) *
    \w_ (2 ^ S n) ^ (2 * a)) with (-1 * (\w_ (2 ^ S n) ^ (a * S (2 * e) + 2 * S e * 2^n) *
      \w_ (2 ^ S n) ^ (2 * a))) by ring.
    rewrite <- Cpow_add_r.
    f_equal; f_equal.
    lia.
Qed.



(* returns the even decomposition of a polynomial *)
Fixpoint even_poly'(d:nat)(p:dense_cpoly): dense_cpoly :=
 match p with
  | nil => nil
  | a1::p' => if Nat.even(d) then a1::even_poly' (S d) p' else even_poly'(S d) p'
  end.

(* returns the odd decomposition of a polynomial *)
Fixpoint odd_poly'(d:nat)(p:dense_cpoly): dense_cpoly :=
  match p with
  | nil => nil
  | a1::p' => if Nat.odd(d) then a1::odd_poly'(S d) p' else odd_poly'(S d) p'
end.


Notation "\even_ p " := (even_poly' 0 p)(at level 10).
Notation "\odd_ p " := (odd_poly' 0 p)(at level 10).

(* helper lemma to prove correctness of the decomposition*)
Lemma even_succ_odd:  forall p n,
even_poly' n p = odd_poly' (S n) p.
Proof. 
  intros p; induction p. 
     - auto. 
     - simpl; intros n. 
       rewrite -> Nat.odd_succ.
       destruct (Nat.even n) eqn: E.
        + f_equal; apply IHp.
        + apply IHp.
Qed.
(* helper lemma to prove correctness of the decomposition*)
Lemma odd_succ_even:  forall p n,
odd_poly' n p = even_poly' (S n) p.
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

(* justification of decomposition *)
Lemma even_and_odd: forall p x,
\even_p[x^2] + x * \odd_p[x^2] = p[x].
Proof.
intros. induction p.
  - unfold complex_eval.
    simpl.
    apply c_proj_eq.
    simpl; lra.
    simpl; lra.
  - simpl.
    rewrite <- even_succ_odd.
    rewrite <- odd_succ_even.
    repeat rewrite -> complex_add.
    rewrite <- IHp.
    ring_simplify.
    f_equal.
Qed.

(* auxiliary proof on the length of the decompositions *)
Lemma eo_plus_len: forall p,
length p = (length(\even_p) + length(\odd_p))%nat.
Proof.
  induction p.
  - simpl. auto.
  - simpl.
    f_equal.
    rewrite <- even_succ_odd.
    rewrite <- odd_succ_even.
    rewrite -> IHp.
    lia.
Qed.
(* auxiliary proof on the length of the decompositions *)
Lemma eo_eq_succ: forall a p,
length (\even_p) = length (\odd_p) ->
length (\even_(a::p)) = S(length(\odd_(a::p))).
Proof.
intros.
destruct p.
- simpl in *. reflexivity.
- simpl in *.
  repeat (rewrite <- even_succ_odd in *; rewrite <- odd_succ_even in *).
  f_equal.
  symmetry.
  apply H.
Qed.

(* auxiliary proof on the length of the decompositions *)
Lemma eo_ne_succ: forall a p,
length (\even_p) = S(length (\odd_p)) ->
length (\even_(a::p)) = length (\odd_(a::p)).
Proof.
intros. 
destruct p.
  - simpl in H. discriminate H.
  - simpl in *.
    repeat (rewrite <- even_succ_odd in *; rewrite <- odd_succ_even in *).
    auto.
Qed.

(* auxiliary proof on the length of the decompositions *)
Lemma eo_equal_or_succ: forall p,
length(\even_p) = S(length(\odd_p))
  \/
length(\even_p) = length(\odd_p).
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

(* auxiliary proof on the length of the decompositions *)
Lemma even_eq_odd: forall p n,
Nat.le 1 (n)%nat -> length p = (2*n)%nat -> 
length(\even_p) = length(\odd_p).
Proof.
intros.
pose proof eo_equal_or_succ p as [H1 | H2].
  - rewrite -> eo_plus_len in H0.
    rewrite -> H1 in H0.
    exfalso.
    replace((S (length (\odd_p)) + length (\odd_p))%nat)
     with 
           (( 2* length (\odd_p) + 1)%nat) in H0 by lia.
    replace((2 * length (\odd_p) + 1)%nat) with
            ( S (2 * length (\odd_p))%nat) in H0 by lia.
    lia.
  - 
    exact H2.
Qed.

(* length of even is half that of the original polynomial *)
Lemma even_half_len: forall p n,
Nat.le 1 (n)%nat -> length p = (2*n)%nat -> 
length(\even_p) = n.
Proof.
  intros.
  assert(length (\even_p) = length (\odd_p)).
  apply even_eq_odd with (n:= n); auto.
  rewrite -> eo_plus_len in H0.
  rewrite <- H1 in H0.
  replace ( (length (\even_p) + length (\even_p))%nat) with
           ( (2*length(\even_p))%nat) in H0 by lia.
  rewrite -> Nat.mul_cancel_l in H0.
  all: lia.
Qed.
(* length of odd is half that of the original polynomial *)
Lemma odd_half_len: forall p n,
Nat.le 1 (n)%nat -> length p = (2*n)%nat ->
 length(\odd_p) = n.
Proof.
  intros.
  assert(length (\even_p) = length (\odd_p)).
  apply even_eq_odd with (n:= n); auto.
  rewrite <- H1.
  apply even_half_len.
  all:auto.
Qed.

(* evaluation on a power list *)
Fixpoint evals (w:C)(n:nat)(p:dense_cpoly): dense_cpoly :=
  match n with
  | O => p[w^0]::nil
  | S(n') => evals w n' p ++ p[w^n] :: nil
  end.

Lemma cevals_succ: forall n w p,
evals w (S n) p = evals w n p ++ p[w^(S n)]::nil.
Proof.
auto. 
Qed.

Lemma evals_nil: forall n w,
evals w n nil = RtoC(0)::repeat (RtoC 0) n.
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



Lemma evals_length_eq_n: forall w n p,
length(evals w n p) = S n.
Proof.
induction n.
  - auto.
  - intros; simpl.
    rewrite -> last_length.
    f_equal.
    apply IHn.
Qed.

Notation "p `_ j" := (nth j p 0)(at level 10). 
Lemma evals_step: forall n j w a p,
Nat.le j n ->
(evals w n (a::p))`_j = a + w^j * p[w^ j].
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
    + simpl. rewrite -> app_nth1 by (rewrite -> evals_length_eq_n; auto).
      apply IHn; lia.
    + simpl.
      assert(length(evals w n (a::p)) = j) 
      by (rewrite -> H; apply evals_length_eq_n).
      replace(nth j (evals w n (a :: p) ++ (a :: p) [w * w ^ n] :: nil) 0%R) with
      (nth(length(evals w n (a::p))) (evals w n (a::p) ++ (a::p)[w*w^n]::nil)0).
      rewrite -> nth_middle.
      rewrite -> complex_add.
      rewrite -> H.
      auto.
     (* proof of rewrite *)
     rewrite -> H0; auto.
Qed.

Lemma evals_correct: forall x n a p,
Nat.le a n -> (evals x n p)`_a = p[x^a].
Proof.
induction p.
  - intros; simpl.
    simpl.
    rewrite -> evals_nil.
    rewrite -> repeat_cons.
    simpl.
    intros.
    replace(repeat (RtoC 0) n ++ RtoC(0)::nil) with 
    (repeat (RtoC 0) (S n)) by (rewrite <- repeat_cons; auto).
    rewrite -> nth_repeat. 
    auto.
  - intros. 
    simpl.
    unfold complex_eval.
    rewrite -> complex_add.
    rewrite -> evals_step by apply H.
    auto.
Qed.

Definition DFT(p: dense_cpoly): list C:=
let n := length p in
evals(\w_n) (n-1) p.

Lemma FFT_inductive_step_even: forall p j n,
Nat.le 1 n ->
p[(\w_(2*n)^j)] = 
\even_p [(\w_n^j)] + 
\w_(2*n)^j * \odd_p [nth_unit_root n ^j].
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
    lia. 
    rewrite -> H0.
    symmetry. 
    apply even_and_odd. 
Qed.

Lemma FFT_inductive_step_odd: forall p j n,
p [\w_(2^ S n)^(j+ (2^n))] = 
\even_p [\w_(2^n)^j] - 
(\w_(2^ S n) ^j) * (\odd_p)[\w_(2^n)^j].
Proof.
  intros.
  rewrite <- even_and_odd.
  ring_simplify.
  replace(-1*\w_ (2 ^ S n) ^ j) with (\w_ (2 ^ S n) ^ (j+2^n)).
  replace(2^S n)%nat with (2*2^n)%nat by (simpl; lia).
  rewrite -> unit_root_k_squares.
  replace(\w_ (2 ^ n) ^ (j + 2 ^ n)) with (\w_ (2 ^ n) ^ j).
  auto.
  rewrite -> Cpow_add_r.
  rewrite -> pow_n_to_1.
  ring.
  pose proof pow_le_1. 
  specialize H with (n:= n); lia.
  rewrite -> unit_root_symmetry.
  ring.
Qed.

Lemma FFT_inductive_step_odd_pow_k: forall  k p j n, 
p [\w_(2^S n)^((j*k)+2^n)] = 
\even_p [\w_(2^n)^(j*k)] - 
(\w_(2^S n) ^(j*k)) * (\odd_p)[\w_(2^n)^(j*k)].
Proof.
  unfold Nat.le. 
  intros.
  rewrite <- even_and_odd.
  ring_simplify.
  replace(-1*\w_ (2 ^ S n) ^ (j*k)) with (\w_ (2 ^ S n) ^ ((j*k)+2^n)).
  replace(2^S n)%nat with (2*2^n)%nat by (simpl; lia).
  rewrite -> unit_root_k_squares.
  replace(\w_ (2 ^ n) ^ (j*k + 2 ^ n)) with (\w_ (2 ^ n) ^ (j*k)).
  auto.
  rewrite -> Cpow_add_r.
  rewrite -> pow_n_to_1.
  ring.
  pose proof pow_le_1. 
  specialize H with (n:= n); lia.
  rewrite -> unit_root_symmetry.
  ring.
Qed.

Lemma length_one_eval: forall x p,
 length p = 1%nat -> p[x] = hd (RtoC 0) p.
Proof.
intros.
induction p.
  - simpl in H.
    exfalso; lia.
  - rewrite -> complex_add.
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


Fixpoint make_left (e o: list C) (n:nat)(w: C): list C :=
  match n with
  |O => e`_n + w^n * o`_n :: nil
  |S(n') => make_left e o n' w  ++ ((e`_n + w^n * o`_n) :: nil)
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


Lemma make_left_nth: forall a n w e o,
Nat.le a n ->
make_left e o n w `_a = e`_a + w^a * o`_a.
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
Lemma make_left_correct: forall n a y_e y_o p,
Nat.le 1 n -> Nat.lt a n -> length p = (2*n)%nat ->
y_e = DFT (\even_p) ->
y_o = DFT (\odd_p) ->
(make_left y_e y_o (n-1) (\w_(2*n)))`_a  =
(DFT p)`_a.
Proof.
intros.
destruct n.
  - simpl. exfalso. lia.
  - rewrite -> make_left_nth by lia.
    rewrite -> H2, H3.
    unfold DFT.
    Search(length(_)).
    replace(length(\even_p)) with (S n).
    replace(length(\odd_p)) with (S n). 
    repeat rewrite -> evals_correct by lia.
    Search(nth_unit_root).
    rewrite -> H1.
    rewrite -> FFT_inductive_step_even by auto. 
    auto.
    apply odd_half_len in H1.
    auto.
    lia.
    apply even_half_len in H1.
    auto.
    lia.
Qed.
Lemma make_left_correct_any_pow: forall k n a y_e y_o p,
Nat.le 1 n -> Nat.lt a n -> length p = (2*n)%nat ->
y_e = evals(\w_n^k)(n-1)%nat (\even_p) ->
y_o = evals(\w_n^k)(n-1)%nat (\odd_p) ->
(make_left y_e y_o (n-1) (\w_(2*n)^k))`_a  =
evals(\w_(2*n)^k) (n-1)%nat(p)`_a.
Proof.
intros.
destruct n.
  - simpl. exfalso. lia.
  - rewrite -> make_left_nth by lia.
    rewrite -> H2, H3.
    unfold DFT.
    Search(length(_)).
    replace(length(\even_p)) with (S n).
    replace(length(\odd_p)) with (S n). 
    repeat rewrite -> evals_correct by lia.
    replace((\w_ (S n) ^ k) ^ a) with ((\w_ (S n) ^ (a*k))) by 
    (rewrite <- Cpow_mult_r;
    f_equal; lia).
    replace((\w_ (2 * S n) ^ k) ^ a) with ((\w_ (2 * S n) ^ (a*k))) by 
    (rewrite <- Cpow_mult_r;
    f_equal; lia).
    rewrite -> FFT_inductive_step_even by auto.
    auto.
    apply odd_half_len in H1.
    auto.
    lia.
    apply even_half_len in H1.
    auto.
    lia.
Qed.
Fixpoint make_right (y_e y_o: list C) (n:nat)(w: C): list C :=
  match n with
  |O => y_e`_n - w^n * y_o`_n :: nil
  |S(n') => make_right y_e y_o n' w  ++ (((y_e`_n - w^n * y_o`_n)) :: nil)
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
Nat.lt a (2^n) -> length p = (2^S n)%nat ->
y_e = DFT(\even_p) ->
y_o = DFT(\odd_p) ->
(make_right y_e y_o (2^n-1)%nat (\w_(2^S n)))`_a  =
(DFT p)`_(a+(2^n)).
Proof.
intros.

  - rewrite -> make_right_nth by lia.
    rewrite -> H1, H2.
    unfold DFT.
    replace(length(\even_p)) with (2^n)%nat.
    replace(length(\odd_p)) with (2^n)%nat.   
    repeat rewrite -> evals_correct by lia.
    rewrite -> H0.
    rewrite -> evals_correct.
    rewrite -> FFT_inductive_step_odd.
    all:auto.
    { destruct(Nat.lt_ge_cases(2^n - 1)(a)).
       
       assert(a = (2^n -1)%nat) by lia.
       rewrite -> H4.
       simpl. lia.
       
       apply Nat.le_trans with (m:= (2*2^n - 1)%nat).
       lia.
       simpl. lia.
    }
    rewrite -> odd_half_len with (n:= (2^n)%nat); auto; lia.
    rewrite -> even_half_len with (n:= (2^n)%nat); auto; lia.     
Qed.
Lemma make_right_correct_odd_pow: forall e k n a y_e y_o p,
Nat.lt a (2^n) -> length p = (2^S n)%nat ->
y_e = evals(\w_(2^n)^(k))((2^n)-1)%nat(\even_p) ->
y_o = evals(\w_(2^n)^(k))((2^n)-1)%nat(\odd_p) ->  k = S(2*e) ->
(make_right y_e y_o ((2^n)-1) (\w_(2^S n)^(k)))`_a  =
evals(\w_(2^S n)^(k))(2^S n-1)%nat p`_(a+(2^n)).
Proof.
intros.
    rewrite -> make_right_nth.
    rewrite -> H1, H2.
    replace(length(\even_p)) with (2^ n)%nat.
    replace(length(\odd_p)) with (2^ n)%nat.   
    repeat rewrite -> evals_correct by lia.
    rewrite -> evals_correct.
    replace((\w_ (2^S n) ^ k) ^ a) with ((\w_ (2^S n) ^ (a*k))) by 
    (rewrite <- Cpow_mult_r;
    f_equal; lia).
    replace((\w_ (2 ^ n) ^ k) ^ a) with (\w_ (2 ^ n) ^ (a * k)) by 
    (rewrite <- Cpow_mult_r;
        f_equal; lia).
    replace((\w_ (2 ^ S n) ^ (k)) ^ (a+2 ^n)) with ((\w_ (2 ^ S n) ^ (k*(a + 2^ n)))) by
    (rewrite <- Cpow_mult_r; auto).
    replace(k * (a + 2 ^ n))%nat with (a*k + k*(2 ^ n))%nat by lia.
    rewrite <-  FFT_inductive_step_odd_pow_k by lia.
    f_equal.
    rewrite -> H3.
    replace(a * S (2 * e) + S (2 * e) * 2^n)%nat with((a * S (2 * e) + (2 * e) * 2^n + 2^n))%nat by lia.
    repeat rewrite -> unit_root_symmetry.
    rewrite <- even_powered_n_symmetry.
    auto.
    { destruct(Nat.lt_ge_cases(2^ n - 1)(a)).
  
       assert(a = (2^ n -1)%nat) by lia.
       rewrite -> H5.
       simpl. lia.
       
       apply Nat.le_trans with (m:= (2*2^ n - 1)%nat).
       lia.
       simpl. lia.  }
    rewrite -> odd_half_len with (n:= (2^ n)%nat); auto; lia.
    rewrite -> even_half_len with (n:= (2^ n)%nat); auto; lia.
    lia. 
Qed.


Definition butterfly (y_e y_o: list C)(w: C): list C :=
 let n      := length(y_e) in
 let l1     := make_left y_e y_o (n-1) w in
 let l2     := make_right y_e y_o (n-1) w in
      l1 ++ l2.

Fixpoint fft(n:nat)(p:list C)(w:C):list C :=
  match n with
  | O => p
  | S(n')     => let y_e := fft(n')(\even_p)(w^2%nat) in
                 let y_o := fft(n')(\odd_p)(w^2%nat) in 
                 butterfly y_e y_o w
  end.

Lemma butterfly_nth_correct: forall n a y_e y_o p,
length p = (2^S n)%nat -> Nat.lt a (2^S n) ->
y_e = DFT(\even_p) ->
y_o = DFT(\odd_p) ->
butterfly y_e y_o (\w_(2^S n))`_a= 
DFT (p)`_a.
Proof.
    intros.
    unfold butterfly.
    unfold DFT in *.
    assert(length y_e = (2^n)%nat).
    { simpl in H. apply even_half_len in H.
      rewrite -> H1.
      rewrite -> evals_length_eq_n.
      rewrite -> H.
      pose proof pow_le_1.
      specialize H3 with (n:= n).
      lia.
      apply pow_le_1.
     }
    rewrite -> H3.
    destruct(Nat.lt_ge_cases a (2^n)).
    - rewrite -> app_nth1.
      rewrite -> make_left_correct with (p:= p).
      unfold DFT.
      all:auto.
      all: try lia.
      rewrite -> make_left_length. lia.
   -  rewrite -> app_nth2. 
      rewrite -> make_left_length.
      rewrite -> make_right_correct with (p:= p).
      unfold DFT.
      repeat rewrite -> evals_correct by lia.
      repeat f_equal.
      pose proof pow_le_1; specialize H5 with (n:= n).
      lia.
      all: auto.
      simpl in *. lia.
      rewrite -> make_left_length.
      simpl in *; lia.
Qed.


Lemma butterfly_nth_correct_odd_pows: forall e k n y_e y_o p a,
length p = (2^S n)%nat -> Nat.lt a (2^S n) ->
y_e = evals(\w_(2^n)^(k))(2^n-1)%nat(\even_p) ->
y_o =  evals(\w_(2^n)^(k))(2^n-1)%nat(\odd_p) -> k = S(2*e) ->
butterfly y_e y_o (\w_(2^S n)^k)`_a= 
evals(\w_(2^S n)^(k))(2^S n-1)%nat p`_(a).
Proof.
 intros.
    unfold butterfly.
    assert(length y_e = (2^n)%nat).
    { simpl in H0. apply even_half_len in H.
      rewrite -> H1.
      rewrite -> evals_length_eq_n.
      pose proof pow_le_1.
      specialize H4 with (n:= n).
      lia.
      apply pow_le_1.
     }
    rewrite -> H4.
    destruct(Nat.lt_ge_cases a (2^n)).
    - rewrite -> app_nth1.
      rewrite -> make_left_correct_any_pow with (p:= p). 
      repeat rewrite -> evals_correct by lia.
      simpl in *.
      all:try lia.
      all: auto.
      rewrite -> make_left_length.
      lia.
   -  rewrite -> app_nth2. 
      all: rewrite -> make_left_length.
      rewrite -> make_right_correct_odd_pow with (e:= e)(p:= p).
      repeat rewrite -> evals_correct by lia.
      f_equal. f_equal. 
      all: auto.
      pose proof pow_le_1; specialize H6 with (n:=n).
      all: try lia.
      pose proof pow_le_1. specialize H6 with (n:=n).
      replace(S (2 ^ n - 1)) with (2^n)%nat by lia. 
      { 
        destruct(Nat.lt_ge_cases(2^S n - 1)(a)).
  
       assert(a = (2^S n -1)%nat) by lia.
       rewrite -> H8.
       simpl. lia.
       
       simpl in *. lia.
    }
      pose proof pow_le_1. specialize H6 with (n:=n).
      replace(S (2 ^ n - 1)) with (2^n)%nat by lia.
      lia.    
Qed.
Lemma nth_succ: forall (l1 l2: list C) a0 a r,
(a :: l1)`_(S a0) = (r :: l2)`_(S a0) ->
l1`_a0 = l2`_a0.
Proof.
intros. simpl in H. auto.
Qed.

Lemma lt_to_all_nth: forall l1 l2: list C,
length l1 = length l2 ->
(forall (a:nat), Nat.lt a (length l1) -> l1`_a = l2`_a)
-> (forall (a : nat), l1`_a = l2`_a).
Proof.
intros.
destruct (Nat.lt_ge_cases a (length l1)) as [Hlt | Hge].
 - apply H0. auto.
 - rewrite -> nth_overflow by auto.
   rewrite -> H in Hge.
   rewrite -> nth_overflow by auto.
   auto.
Qed.

Lemma nth_eq: forall l1 l2: list C,
length l1 = length l2 ->
  (forall (a : nat), l1`_a = l2`_a) ->
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

Lemma butterfly_correct: forall n y_e y_o p,
length p = (2^S n)%nat ->
y_e = DFT(\even_p) ->
y_o = DFT(\odd_p) ->
butterfly y_e y_o (\w_(2^S n)) = DFT p.
Proof.
intros.

assert(forall a, Nat.lt a (2^S n) -> 
(butterfly y_e y_o (\w_(2^S n)))`_a= 
DFT p `_ a).
intros. apply butterfly_nth_correct. all: auto.

assert(length (butterfly y_e y_o (\w_(2 ^S n))) = (2^ S n)%nat).
unfold butterfly.
rewrite -> app_length.
rewrite -> make_left_length.
rewrite -> make_right_length.
rewrite -> H0.
unfold DFT.
rewrite -> evals_length_eq_n.
simpl in H; apply even_half_len in H.
rewrite -> H.
pose proof pow_le_1; specialize H3 with (n:=n).
simpl.
lia.
apply pow_le_1.

assert(forall a:nat,
butterfly y_e y_o (\w_(2 ^ S n)) `_ a= 
DFT p `_ a).
apply lt_to_all_nth.
rewrite -> H3.
unfold DFT.
rewrite -> evals_length_eq_n.
rewrite -> H. 
pose proof pow_le_1; specialize H4 with (n:=n).
simpl; lia.
rewrite -> H3.
apply H2.

apply nth_eq in H4.
auto.
rewrite -> H3.
unfold DFT.
rewrite -> evals_length_eq_n.
pose proof pow_le_1; specialize H5 with (n:=S n).
rewrite -> H. lia.
Qed.

Lemma butterfly_odd_pows_correct: forall e k n y_e y_o p,
length p = (2^S n)%nat ->
y_e = evals(\w_(2^n)^(k))(2^n-1)%nat(\even_p) ->
y_o =  evals(\w_(2^n)^(k))(2^n-1)%nat(\odd_p) -> k = S(2*e) ->
butterfly y_e y_o (\w_(2^S n)^k)= 
evals(\w_(2^S n)^(k))(2^S n-1)%nat p.
Proof.
intros.
assert(forall a, Nat.lt a (2^S n) -> 
(butterfly y_e y_o (\w_(2^S n)^k))`_a= 
evals(\w_(2^S n)^(k))(2^S n-1)%nat p`_a).
intros. apply butterfly_nth_correct_odd_pows with (e:= e). all: auto.
assert(length (butterfly y_e y_o (\w_(2 ^ S n)^k)) = (2^S n)%nat).
unfold butterfly.
rewrite -> app_length.
rewrite -> make_left_length.
rewrite -> make_right_length.
rewrite -> H0.
rewrite -> evals_length_eq_n.
simpl.
pose proof pow_le_1. specialize H4 with (n:= n).
lia.


assert(forall a:nat,
butterfly y_e y_o (\w_(2^S n)^k) `_ a= 
evals(\w_(2^S n)^(k))(2^S n-1)%nat p`_a).
apply lt_to_all_nth.
rewrite -> H4.
rewrite -> evals_length_eq_n.
pose proof pow_le_1. specialize H5 with (n:= S n).
lia.

rewrite -> H4.
apply H3.

apply nth_eq in H5.
auto.
rewrite -> H4.
rewrite -> evals_length_eq_n.
pose proof pow_le_1. specialize H6 with (n:= S n).
lia.
Qed.



    
Lemma DFT_constant: forall p,
length p = 1%nat -> DFT p = p.
Proof.
induction p.
  - intros.
    simpl in *.
    exfalso; lia.
  - intros.
    unfold DFT.
    simpl in *.
    assert(length p = O) by lia.
    apply length_zero_iff_nil in H0.
    rewrite -> H0.
    simpl.
    rewrite -> length_one_eval.
    all:auto.
Qed.
Lemma fft_correct: forall n p,
length p = (2^n)%nat -> 
fft n p (nth_unit_root(2^n%nat)) = DFT p.
Proof.
induction n.
  - intros.
    rewrite -> DFT_constant.
    simpl in *.
    auto.
    simpl in H.
    auto.
  - intros.
    simpl.
(* even poly degree *)
    assert(length (\even_p) = (2^n)%nat).
      apply even_half_len in H.
      apply H.
      apply pow_le_1.
(* odd poly degree *)
    assert(length (\odd_p) = (2^n)%nat).
      apply odd_half_len.
      apply pow_le_1.
      apply H.

    assert(nth_unit_root (2 ^ n + (2 ^ n + 0)) *
      (nth_unit_root (2 ^ n + (2 ^ n + 0)) * 1%R)= nth_unit_root (2 ^ n)).
    apply unit_root_squares.
    rewrite -> H2.
    repeat rewrite -> IHn by auto.
    replace(\w_ (2 ^ n + (2 ^ n + 0))) with (\w_(2^S n)).
    rewrite -> butterfly_correct with (p:= p).
    all:auto. 
Qed.

Lemma fft_correct_odd_pows: forall n p k e,
length p = (2^n)%nat -> k = S(2*e) ->
fft n p (nth_unit_root(2^n%nat)^k) = evals(\w_(2^n)^(k))(2^n-1)%nat p.
Proof.
induction n.
  - intros.
    simpl in *.
    rewrite -> length_one_eval by auto.
    destruct p.
    + simpl in H; exfalso; lia.
    + simpl in *.
      assert(length p = O) by lia.
      apply length_zero_iff_nil in H1.
      rewrite -> H1; auto.
  - intros.
    simpl.
(* even poly degree *)
    assert(length (\even_p) = (2^n)%nat).
      apply even_half_len in H.
      apply H.
      apply pow_le_1.
(* odd poly degree *)
    assert(length (\odd_p) = (2^n)%nat).
      apply odd_half_len.
      apply pow_le_1.
      apply H.
    replace(2 ^ n + (2 ^ n + 0))%nat with (2*(2^n))%nat by lia.
    replace(\w_ (2*(2^n)) ^ k *
           (\w_ (2*(2^n)) ^ k * 1)) with ((\w_ (2*(2^n))^k)^2) by ring.
    rewrite -> unit_root_k_squares.
    repeat rewrite -> IHn with (e:= e) by auto.
    replace(2*2^n)%nat with (2^S n)%nat by (simpl; lia).
    rewrite -> butterfly_odd_pows_correct with (e:=e)(p:= p).
    f_equal.
    all:try auto.
    (* Nat.le 2^n*)
    pose proof pow_le_1.
    specialize H3 with (n:= n).
    lia.
Qed.



Print nth.
Definition sum_eval'(x:C)(p:dense_cpoly) :=
sum_n(fun c => p`_c*x^c)(length p).

Definition sum_eval (x:C)(p:dense_cpoly) :=
sum_n(fun c => p`_c*x^c)(length p-1).

Lemma sum_n_eq_m_n: forall (f: nat -> C) n,
sum_n f n = sum_n_m f 0 n.
Proof.
induction n.
  - rewrite -> sum_n_n.
    rewrite -> sum_O.
    auto.
  - rewrite -> sum_Sn.
    rewrite -> sum_n_Sm by lia.
    rewrite -> IHn.
    auto.
Qed.

Lemma sum_n_mult_r_C : forall (a : C) (u : nat -> C) (m : nat),
    sum_n (fun k => Cmult (u k) a) m = Cmult (sum_n u m) a.
Proof.
intros.
induction m.
    repeat rewrite -> sum_O.
    auto.
    { rewrite -> sum_Sn by lia.
      rewrite -> IHm.
      rewrite -> sum_Sn by lia.
      apply c_proj_eq.
      simpl. lra.
      simpl. lra.
    }
Qed.

Lemma sum_ev_add: forall p a x,
  sum_eval' x (a :: p) = a + x * sum_eval' x p.
Proof.
 intros.
 unfold sum_eval'.
 repeat rewrite -> sum_n_eq_m_n.
 replace(length(a::p)) with (S(length p)) by auto.
 replace(a) with ((a::p)`_(O)*x^O).
 rewrite -> sum_Sn_m.
 simpl.
 rewrite <- sum_n_m_S.
 repeat rewrite <- sum_n_eq_m_n.
 assert(x * sum_n (fun c : nat => nth c p 0 * x ^ c) (length p) =
        sum_n(fun c: nat => nth c p 0 * x^c * x) (length p)).
 rewrite -> sum_n_mult_r_C.
 ring.
 rewrite -> H.
 rewrite -> sum_n_ext with (b:= (fun c : nat => nth c p 0 * x ^ c * x)).
 apply c_proj_eq.
 simpl. lra.
 simpl. lra.
 { intros. simpl. ring. }
  lia.
  simpl. ring.
Qed.

Lemma sum_evalc_ev: forall x p,
sum_eval' x p = sum_eval x p.
Proof.
unfold sum_eval, sum_eval'.
intros.
induction (length p) eqn: e.
  - simpl. auto.
  - rewrite -> sum_Sn.
    rewrite -> nth_overflow by lia.
    replace(0 * x^S n) with (RtoC 0) by ring.
    simpl.
    replace(n-0)%nat with n by lia.
    apply c_proj_eq.
    all: simpl.
    all: try lra.
Qed.
    

Lemma sum_ev_eq: forall x p,
sum_eval x p = p[x].
Proof.
intros.
rewrite <- sum_evalc_ev.
induction p.
  - unfold sum_eval'. 
    simpl.
    rewrite -> sum_O.
    unfold complex_eval.
    simpl. ring.
  - rewrite -> complex_add.
    rewrite <- IHp.
    simpl.
    rewrite -> sum_ev_add.
    auto.
Qed.

Lemma DFT_correct: forall p a,
Nat.lt a (length p) ->
DFT p`_a = p[\w_(length p)^a].

Proof.
intros.
unfold DFT.
rewrite -> evals_correct by lia.
auto.
Qed.


Lemma sum_eval_scalar: forall p m x a,
sum_n(fun c => p`_c*x^c) m * a = sum_n(fun c => p`_c*x^c*a) m.
Proof.
intros.
rewrite <- sum_n_mult_r_C.
auto.
Qed. 



  
Lemma transform_roots: forall k c j n, 
(\w_ (2^n) ^ c) ^ k * ((/ \w_ (2^n)) ^ j) ^ c =
       ((\w_(2^n))^(c*k))/((\w_(2^n))^(c*j)).
Proof.
intros.
repeat rewrite <- Cpow_mult_r.
rewrite -> Cpow_inv.
replace(j*c)%nat with (c*j)%nat by lia.
Search(_*/_)%R.
apply c_proj_eq.
simpl. lra.
simpl. lra.
apply unit_root_nonzero.
Qed.

(*
Lemma DFT_correct: forall p a,
Nat.lt a (length p) ->
DFT p`_a = p[\w_(length p)^a]. *)


Lemma sum_term_out_funs: forall n m (f: nat -> C)(u: nat -> nat -> C),
sum_n(fun j0 : nat => sum_n (fun i : nat =>(f j0) * (u i j0)) (m)) (n) 
=
sum_n(fun j0: nat => (f j0) * (sum_n (fun i : nat => (u i j0)) m)) n.
Proof.
induction n.
  - intros.
    repeat rewrite -> sum_O.
    rewrite -> Cmult_comm.
    rewrite <- sum_n_mult_r_C.
    f_equal.
    apply functional_extensionality.
    intros. ring.
  - intros.
    repeat rewrite -> sum_Sn.
    rewrite <- IHn.
    f_equal.
    rewrite -> Cmult_comm.
    rewrite <- sum_n_mult_r_C.
    f_equal.
    apply functional_extensionality; intros; ring.
Qed.

Lemma nonzeroes_pow: forall (n:C) m,
n <> 0 -> n^m <> 0.
Proof.
intros.
induction m.
  - simpl. apply C1_nz.
  - simpl.
    Search(_*_<>_).
    apply Cmult_neq_0.
    all: auto.
Qed.

Lemma sum_n_const_C: forall n (a: C),
sum_n(fun _ => a)n = (S n)* a.
Proof.
intros.
induction n.
  rewrite -> sum_O. 
  simpl. ring.
  
  rewrite -> sum_Sn.
  rewrite -> IHn.
  apply c_proj_eq.
  all:simpl.
  all:lra.
Qed.


  
    

Lemma inner_sum_1: forall n j j0,
j = j0 ->
sum_n (fun i : nat =>(\w_ (2^n) ^ i) ^ j0 * ((/ \w_ (2^n)) ^ j) ^ i)((2^n)-1)=
RtoC (2^n).
Proof.
intros.
rewrite -> H.
rewrite -> sum_n_ext with (b:= fun i => ((\w_(2^n))^(i*j0)%nat */ ((\w_(2^n))^(i*j0)%nat))).
rewrite -> sum_n_ext with (b:= fun i => RtoC 1).
destruct (2^n)%nat eqn:E .
  - pose proof pow_le_1.
    specialize H0 with (n:= n).
    exfalso; lia.
  - simpl.
    replace(n0-0)%nat with n0 by lia.
    rewrite -> sum_n_const_C.
    rewrite <- E.
    ring_simplify.
    rewrite -> pow_INR.
    simpl.
    f_equal.

    { intros.
      apply Cinv_r.
       
      apply nonzeroes_pow.
      apply unit_root_nonzero. }

    intros.
    apply transform_roots.
Qed.

Lemma unit_roots_sum_to_zero: forall n k,
sum_n (fun i : nat => \w_ (2 ^ n) ^ (k * i)) (2 ^ n - 1) = RtoC 0.
Proof.
Admitted.
    
Lemma inner_sum_zero: forall j j0 n,
Nat.lt j (2^n) -> Nat.lt j0 (2^n) ->
j <> j0 ->
sum_n (fun i : nat =>(\w_ (2^n) ^ i) ^ j0 * ((/ \w_ (2^n)) ^ j) ^ i)(2^n-1)
= RtoC 0.
Proof.
intros.
  rewrite -> sum_n_ext with (b:= fun i => \w_ (2 ^ n) ^ (i* j0)*  (/ ((\w_ (2 ^ n))) ^ (i*j))).
  rewrite -> sum_n_ext with (b:= fun i => \w_(2^n)^(i*j0) * (\w_(2^n)^(2^n-1))^(i*j)).
  rewrite -> sum_n_ext with (b:= fun i => \w_(2^n)^(i*j0) * \w_(2^n)^((2^n-1)*j*i)) .
  rewrite -> sum_n_ext with (b:= fun i => \w_(2^n)^((i*j0)+(2^n-1)*j*i)) by (intros;
    rewrite -> Cpow_add_r;
    auto). 
  rewrite -> sum_n_ext with (b:= fun i => \w_(2^n)^((j0+(2^n-1)*j)*i)) by (intros;
    f_equal;
    lia).
  rewrite -> unit_roots_sum_to_zero.
  auto.
  { intros.
    rewrite <- Cpow_mult_r.
    f_equal. f_equal.
    lia.  }
  { intros.
    f_equal.
    rewrite -> inverse_unit_root.
    rewrite -> Cpow_inv by apply unit_root_nonzero.
    auto. }
  { intros.
    repeat rewrite <- Cpow_mult_r.
    f_equal.
    rewrite -> Cpow_inv by apply unit_root_nonzero.
    f_equal. f_equal.
    lia. }
Qed.

Definition delta(n m : nat) : C :=
if Nat.eqb n m then 1 else 0.

Lemma delta_1: forall a,
delta a a = 1.
Proof.
intros.
unfold delta.
assert(a =? a = true).
rewrite -> Nat.eqb_eq. lia.
rewrite -> H.
auto.
Qed.

Lemma delta_0: forall a b,
a <> b -> delta a b = 0.
Proof.
intros.
unfold delta.
assert(a =? b = false).
rewrite -> Nat.eqb_neq.
lia.
rewrite -> H0.
auto.
Qed.

Lemma inner_sum_diroc: forall n j0 j,
Nat.lt j (2^n) -> Nat.lt j0 (2^n) -> 
sum_n (fun i : nat => (\w_ (2^n) ^ i) ^ j0 * ((/ \w_ (2^n)) ^ j) ^ i) (2^n-1)
= 
delta j0 j * (2^n)
.
Proof.
intros.
destruct (Nat.eq_dec j j0).
 { (* equal *)
   rewrite -> inner_sum_1 by auto.
   symmetry in e.
   apply Nat.eqb_eq in e.
   unfold delta.
   rewrite -> e.
   ring_simplify.
   rewrite -> RtoC_pow.
   auto. }
  apply inner_sum_zero with (n:= (n)%nat) in n0 as H2.
  rewrite -> H2.
  apply Nat.eqb_neq in n0.
  unfold delta.
  rewrite -> Nat.eqb_sym in n0.
  rewrite -> n0.
  ring_simplify.
  auto.
  all: lia.
Qed.

Lemma delta_zero_sum: forall a,
sum_n(fun j : nat => delta j 0) a = RtoC 1.
Proof.
intros.
induction a.
  - rewrite -> sum_O.
    rewrite -> delta_1 by lia.
    auto.
  - rewrite -> sum_Sn.
    rewrite -> IHa.
    rewrite -> delta_0 by lia.
    unfold plus; simpl; ring.
Qed.

Lemma sum_delta_out_range: forall a b,
Nat.lt a b ->
sum_n (fun j : nat => delta b j) (a) = RtoC 0.
Proof.
intros.
rewrite -> sum_n_ext_loc with (b:= fun _ => RtoC 0).
rewrite -> sum_n_const_C.
ring_simplify.
auto.
intros.
assert(n <> b) by lia.
rewrite -> delta_0 by lia.
auto.
Qed.

Lemma sum_delta_in_range: forall a b,
Nat.lt a b ->
sum_n (fun j : nat => delta a j) b = RtoC 1.
Proof.
intros.
induction b.
  - exfalso; lia.
  - rewrite -> sum_Sn.
    destruct (Nat.lt_ge_cases a (b)).
    { rewrite -> IHb by lia.
      rewrite -> delta_0 by lia.
      unfold plus; simpl.
      ring. }
    { assert(a = b) by lia.
      rewrite -> delta_0 by lia.
      destruct b.
      rewrite -> sum_O.
      rewrite -> H1.
      rewrite -> delta_1 by lia.
      unfold plus; simpl; ring.
      
      rewrite -> sum_Sn.
      rewrite -> sum_delta_out_range by lia.
      rewrite <- H1.
      rewrite -> delta_1 by lia.
      unfold plus; simpl; ring. }
Qed.

Lemma sum_split: forall n a (f:nat -> C),
Nat.lt a n ->
sum_n(fun i: nat => f i) n = sum_n_m(fun i: nat => f i) 0 a +
                             sum_n_m(fun i: nat => f i)(S a) n.
Proof.
induction n.
  - intros.
    exfalso; lia. 
  - intros.
    destruct(Nat.lt_ge_cases a n).
    + rewrite -> sum_Sn.
      rewrite -> IHn with (a:=a) by lia .
      rewrite -> sum_n_Sm.
      unfold plus; simpl.
      ring. lia.
    + assert(a = n) by lia.
      rewrite -> H1.
      rewrite -> sum_n_n.
      rewrite -> sum_Sn.
      unfold plus; simpl.
      rewrite -> sum_n_eq_m_n.
      ring.
Qed.

    
Lemma sum_of_delta: forall (p:dense_cpoly) j,
Nat.lt j (length p) ->
sum_n (fun j0 : nat => nth j0 p 0 * delta j0 j) (length p-1)%nat =
      nth j p 0.
Proof.
intros.
destruct j.
  - rewrite -> sum_n_eq_m_n.
    rewrite -> sum_Sn_m by lia.
    rewrite -> sum_n_m_ext_loc with (b:= fun _ => zero).
    rewrite -> delta_1 by lia.
    rewrite -> sum_n_m_const_zero.
    unfold plus, zero; simpl.
    ring.
    { intros.
      unfold zero; simpl.
      assert(k <> O) by lia.
      rewrite -> delta_0 by lia.
      ring. }
  
  -   destruct(Nat.lt_ge_cases (S j) (length p-1)).
      rewrite -> sum_split with (a:= (S j)).
      rewrite <- sum_n_eq_m_n.
      rewrite -> sum_split with (a:= (j)%nat).
      rewrite -> sum_n_n.
      rewrite -> delta_1 by lia.
      rewrite <- sum_n_eq_m_n.
      rewrite -> sum_n_ext_loc with (b:= fun _ => RtoC(0)).
      rewrite -> sum_n_m_ext_loc with (b:= fun _ => zero).
      rewrite -> sum_n_const_C.
      rewrite -> sum_n_m_const_zero.
      unfold zero; simpl.
      ring_simplify.
      auto.
       { intros.
         assert(k <> j) by lia.
         rewrite -> delta_0 by lia.
         unfold zero; simpl.
         ring. }
       { intros.
         assert(n <> S j) by lia.
         rewrite -> delta_0 by lia.
         ring_simplify.
         auto. }
      lia. apply H0.

    assert(S j = (length p - 1)%nat) by lia.
    rewrite <- H1.
    rewrite -> sum_Sn.
    rewrite -> sum_n_ext_loc with (b:= fun _ => RtoC 0).
    rewrite -> sum_n_const_C.
    rewrite -> delta_1 by lia.
    unfold plus; simpl.
    ring.
    { intros.
      assert(n <> S j) by lia.
      rewrite -> delta_0 by lia.
      ring_simplify.
      reflexivity. }
Qed.
  
Lemma evals_inversed: forall j n p,
(2^n)%nat = length p ->Nat.lt j (2^n)%nat ->
nth j (evals (/nth_unit_root (2^n)%nat) (2^n-1)%nat (DFT p)) 0=
2^n * nth j p 0.
Proof.
intros.
rewrite -> evals_correct by lia.
rewrite <- sum_ev_eq.
unfold sum_eval.
unfold DFT.
rewrite <- H.
rewrite -> sum_n_ext_loc with (b:= fun c : nat =>
                             p[\w_(2^n)^c] * (((/ \w_ (2^n)) ^ j) ^ c)).
rewrite -> sum_n_ext with (b:=  fun c : nat =>
                              sum_eval(\w_(2^n)^c) p * ((/ \w_ (2^n)) ^ j) ^ c).
unfold sum_eval.
rewrite <- H.
rewrite -> evals_length_eq_n.
replace(S (2^n-1)-1)%nat with (2^n-1)%nat by lia.
rewrite -> sum_n_ext with (b:=(fun c : nat => 
                         sum_n (fun c0 : nat => nth c0 p 0 * ((\w_ (2^n) ^ c) ^ c0 *
                          (( / \w_ (2^n)) ^ j) ^ c)) (2^n-1))).
rewrite -> sum_n_switch.
rewrite -> sum_term_out_funs.
rewrite -> sum_n_ext_loc with (b:= fun j0 : nat =>
                           nth j0 p 0 * delta j0 j * 2^n).
rewrite -> sum_n_mult_r_C.
rewrite -> Cmult_comm.
f_equal.

    rewrite <- sum_of_delta.
    rewrite <- H. 
    auto.
    rewrite <- H.
    lia.

{ intros.
  replace (nth n0 p 0 * delta n0 j * 2^n) with (nth n0 p 0 * (delta n0 j * 2^n)) by ring.
  f_equal.
  rewrite -> inner_sum_diroc.
  auto. all: lia. }
  
{ intros.
  rewrite <- sum_n_mult_r_C.
  f_equal.
  apply functional_extensionality.
  intros.
  ring. }
{ intros.
  rewrite -> sum_ev_eq.
  auto. }
{ intros.
  rewrite -> evals_length_eq_n in H1.
  rewrite -> evals_correct by lia.
  auto.
}
Qed.

Lemma nonzero_nat_to_C: forall n,
n <> O -> RtoC n <> RtoC 0.
Proof.
intros.
unfold RtoC.
intros Hf.
apply pair_equal_spec in Hf.
destruct Hf.
apply Nat.neq_0_lt_0 in H.
apply lt_INR in H.
rewrite -> H0 in H.
unfold INR in *.
lra.
Qed.


Lemma nth_mul: forall j n (p: list C),
n * nth j p 0 = map(fun x => n * x)p `_j.
Proof.
induction j.
  - intros.
    destruct p.
    + simpl. ring.
    + simpl. ring.
  - intros.
    destruct p.
    + simpl. ring.
    + simpl. apply IHj.
Qed.

Lemma nth_mul_to_div: forall j n (p: list C),
n<>O -> map(fun x => /n * x)(map(fun x => n * x)p)`_j= p`_j.
Proof.
induction j.
  - intros.
    destruct p.
    + simpl. ring.
    + simpl. ring_simplify. rewrite -> Cinv_l.
      ring.
      apply nonzero_nat_to_C in H.
      auto.
  - intros.
    destruct p.
   + simpl; ring.
   + simpl.
     rewrite -> IHj by auto.
     auto.
Qed.
     
Lemma evals_map_inversed: forall n p,
(2^n)%nat = length p ->
evals (/nth_unit_root (2^n)%nat) (2^n-1)%nat (DFT p) = map(fun x => 2^n * x)p.
Proof.
intros.
  pose proof evals_inversed.
  assert(forall j, nth j (evals (/ \w_ (2^n)) (2^n - 1) (DFT p)) 0 =
    nth j (map (fun x : C => 2^n * x) p) 0).
  { intros.
    destruct (Nat.lt_ge_cases j (2^n)).
    - rewrite -> evals_inversed.
      apply nth_mul.
      auto.
      lia.
    - repeat rewrite -> nth_overflow. 
      auto. 
      rewrite -> map_length. lia. 
      rewrite -> evals_length_eq_n.
      pose proof pow_le_1.
      specialize H2 with (n:= (n)%nat). 
      lia. } 
  apply nth_eq in H1.
  auto.
  rewrite -> evals_length_eq_n; rewrite -> map_length.
  pose proof pow_le_1.
  specialize H2 with (n:= n). 
  lia.
Qed.

Lemma full_fun_correct: forall n p,
(2^n)%nat = length p ->
map(fun x => /(2^n)%nat * x)(evals (/nth_unit_root (2^n)%nat) (2^n-1)%nat (DFT p)) = p.
Proof.
intros.
  replace (evals (/nth_unit_root (2^n)%nat) (2^n-1)%nat (DFT p)) with (map(fun x => (2^n)%nat * x)p).
  assert(forall a, map (fun x : C => / (2^n)%nat * x) (map (fun x : C => (2^n)%nat * x) p)`_a = p`_a).
   { 
    intros.
    apply nth_mul_to_div with (n:= (2^n)%nat).
    pose proof pow_le_1.
    specialize H0 with (n:= n).
    lia. }
  apply nth_eq in H0; auto.
  repeat rewrite -> map_length. auto.
  rewrite -> evals_map_inversed.
  f_equal.
  apply functional_extensionality.
  intros.
  rewrite -> pow_INR.
  f_equal.
  rewrite -> RtoC_pow.
  f_equal.
  auto.
Qed.
 
Definition iDFT(p: dense_cpoly) :=
 let n := length p in
  map(fun x => /n * x)((evals(/ \w_n)) (n-1)%nat p).

Lemma iDFT_correct: forall p n,
length p = (2^n)%nat -> 
iDFT (DFT p) = p.
Proof.
intros.
unfold iDFT.
assert(length(DFT p) = length p).
  { unfold DFT.
    rewrite -> evals_length_eq_n.
    pose proof pow_le_1.
    specialize H0 with (n:= n).
    lia. }
rewrite -> H0.
rewrite -> H. 
apply full_fun_correct.
auto.
Qed.


Definition ifft(n:nat)(p:list C):list C :=
  let w:= /(\w_(2^n)) in 
  map(fun x => /(2^n)%nat * x) (fft n p w).

Lemma ifft_iDFT: forall p n,
length p = (2^n)%nat ->
ifft n p = iDFT p.
Proof.
  intros.
  unfold ifft, iDFT.
  destruct n.
  - rewrite -> H.
    simpl in *.
    destruct p.
    + simpl in H.
      exfalso; lia.
    + simpl in *.
      assert ((length p) = O) by lia.
      apply length_zero_iff_nil in H0.
      rewrite -> H0.
      simpl.
      rewrite -> complex_add.
      f_equal.
      unfold complex_eval.
      simpl.
      ring.
  - rewrite -> H.
    replace(/ \w_ (2 ^ (S n))) with (\w_(2^(S n))^(2^(S n)-1)%nat).
    Search(fft).
    rewrite -> fft_correct_odd_pows with (e:= ((2^(S n)-2)/2)%nat).
    f_equal.
    auto.
    rewrite <- Nat.div2_div.
    rewrite <- Nat.double_twice.
    rewrite <- Nat.Even_double.
    assert(forall n0, Nat.le 2 (2^ S n0)) as H1.
    { induction n0.
       - simpl. auto.
       - apply Nat.le_trans with (2 ^ S n0)%nat.
         apply IHn0.
         simpl.
         lia.
    }
    rewrite <-  Nat.sub_succ_l by apply H1.
    lia.
    apply Nat.even_spec.
    rewrite -> Nat.even_sub.
    replace (Nat.even (2 ^ S n)) with true by
      (simpl;
      replace(2 ^ n + (2 ^ n + 0))%nat with (2*(2^n))%nat by lia;
      rewrite -> Nat.even_mul; auto).
    auto.
    (* (2 <= 2 ^ S n)%nat *)
    { destruct n.
      - simpl. auto.
      - simpl. assert(Nat.le 1 (2^n)) by apply pow_le_1. lia.
    }
    apply inverse_unit_root.
Qed.
    
Lemma icorrect : forall n p x,
length p = (2^n)%nat -> 
(ifft n (fft n p (\w_(2^n))))[x] = p[x].
Proof.
  intros.
  assert(Nat.le 1 (length p)) as H1 by
    (rewrite -> H; apply pow_le_1).
  rewrite -> ifft_iDFT.
  rewrite -> fft_correct by auto.
  rewrite -> iDFT_correct with (n:= n).
  auto.
  auto.
  (* length of fft*)
  rewrite -> fft_correct by auto.
  unfold DFT.
  rewrite -> evals_length_eq_n.
  rewrite -> H.
  ring_simplify.
  lia.
Qed.

Fixpoint add_dense_poly (p1 p2: dense_cpoly): dense_cpoly :=
  match p1, p2 with
  | nil, _ => p2
  | _  , nil => p1
  | a::p1', b::p2' => (a+b) :: add_dense_poly p1' p2'
  end.

Fixpoint scalar_mult (a : C) (p : dense_cpoly) : dense_cpoly :=
  match p with
  | nil => nil
  | h :: t => (a * h) :: scalar_mult a t
  end.

Fixpoint pmul (p1 p2 : dense_cpoly) : dense_cpoly :=
  match p1 with
  | nil => nil
  | h1 :: t1 => add_dense_poly (scalar_mult h1 p2) (RtoC 0 :: pmul t1  p2)
  end.

Lemma add_cons: forall p1 p2 a,
add_dense_poly (a::p1)(p2) = (a+ hd (RtoC 0) p2) :: add_dense_poly p1 (tl p2).
Proof.
destruct p1.
  - intros. destruct p2.
    + simpl. 
      f_equal.
      { apply c_proj_eq.
        all:simpl.
        all:lra. }
    + simpl.
      auto.
  - intros. 
    destruct p2.
    + simpl.
      f_equal. {
      apply c_proj_eq.
      all:simpl.
      all: lra. }
    + simpl. reflexivity.
Qed.

Lemma add_correct: forall p1 p2 x,
complex_eval(add_dense_poly p1 p2) x = complex_eval(p1)x + complex_eval(p2) x.
Proof.
unfold complex_eval.
induction p1.
  - intros. simpl.
    apply c_proj_eq. 
    simpl; lra.
    simpl; lra.
  - intros. rewrite -> add_cons.
    repeat rewrite -> complex_add.
    unfold complex_eval.
    rewrite -> IHp1.
    replace (x * (complex_eval' 0 p1 x + complex_eval' 0 (tl p2) x)) with
             (x * complex_eval' 0 p1 x + x * complex_eval' 0 (tl p2) x) by (apply c_proj_eq; simpl; lra; simpl ;lra).
    rewrite <- Cplus_assoc.
    replace (a + hd (RtoC 0) p2 + x * complex_eval' 0 p1 x +
    x * complex_eval' 0 (tl p2) x) with (a+ x * complex_eval' 0 p1 x +
    (hd (RtoC 0) p2 + x * complex_eval' 0 (tl p2) x)) by (apply c_proj_eq; simpl; lra; simpl; lra).
    rewrite <- complex_add.
    rewrite <- complex_add.
    unfold complex_eval.
    simpl.
    replace(a*1) with a by (apply c_proj_eq; simpl; lra; simpl; lra).
    repeat rewrite -> complex_scale.
    induction p2.
    + simpl. apply c_proj_eq.
      simpl; lra.
      simpl; lra.
    + simpl.
      rewrite -> complex_scale.
      ring_simplify.
      ring. 
Qed.
    
    

Lemma scalar_mult_cons: forall n a p,
scalar_mult n (a::p) = a*n :: scalar_mult n p.
Proof.
intros. simpl. f_equal. ring. 
Qed.

Lemma scalar_correct: forall n p x,
complex_eval(scalar_mult n p) x = n*complex_eval p x.
Proof.
intros. unfold complex_eval.
induction p.
  - simpl. ring. 
  - rewrite -> scalar_mult_cons.
    repeat rewrite -> pdense_eval_add.
    replace (complex_eval (scalar_mult n p) x) with ( n * complex_eval p x).
    simpl.
    rewrite -> complex_scale.
    rewrite -> IHp.
    ring_simplify.
    rewrite -> complex_scale.
    ring.
Qed.
Lemma mul_cons: forall a p1 p2,
pmul(a::p1) p2 = add_dense_poly (scalar_mult a p2) (RtoC 0::pmul p1 p2).
Proof.
intros.
simpl. reflexivity. Qed.


Lemma pmul_correct: forall p1 p2 x,
p1[x] * p2[x] = (pmul p1 p2)[x].
Proof.
unfold complex_eval.
induction p1.
  - intros.
    simpl in *. ring.
  - intros.
    rewrite -> complex_add.
    rewrite -> mul_cons. 
    rewrite -> add_correct. 
    rewrite -> scalar_correct.
    ring_simplify.
    unfold complex_eval.
    rewrite -> complex_add.
    rewrite <- IHp1.
    ring_simplify.
    auto.
Qed.
    

Fixpoint pointwise_mul'(p1 p2:list C)(n:nat):=
  match n with
  | O      => (nth n p1 0)*(nth n p2 0)::nil
  | S (n') => pointwise_mul' p1 p2 n' ++ ((nth n p1 0)*(nth n p2 0)::nil)
end.

Definition pv_mul(p1 p2: list C) :=
  pointwise_mul' p1 p2 (length p1).

Lemma pointwise_mul_add: forall p1 p2 n a b,
Nat.lt n (length p1) -> length p1 = length p2 ->
pointwise_mul'(p1++a::nil)(p2++b::nil)(n) = pointwise_mul'(p1)(p2)(n).
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
Qed.


Lemma pointwise_mul_length: forall p1 p2 n,
length(pointwise_mul' p1 p2 n) = S n.
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
nth a (pointwise_mul'(evals w n p1) (evals w n p2) n) 0 = 
nth a (evals w n (pmul p1 p2)) 0.
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
    +     assert(a = length((pointwise_mul'
         (evals w n p1 ++ complex_eval p1 (w * w ^ n) :: nil)
         (evals w n p2 ++ complex_eval p2 (w * w ^ n) :: nil) n))).
          rewrite -> pointwise_mul_length; auto.
          rewrite -> H0. rewrite -> nth_middle.
          rewrite <- H0.
          replace a with (length(evals w n (pmul p1 p2))) by
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
pointwise_mul'(evals w n p1)(evals w n p2) n =
evals w n (pmul p1 p2).
Proof.
intros.
assert(length (pointwise_mul' (evals w n p1) (evals w n p2) n) = length(evals w n (pmul p1 p2))) by 
(rewrite -> pointwise_mul_length;
 rewrite -> evals_length_eq_n; auto).
apply nth_eq.
auto.
apply lt_to_all_nth.
auto.
intros.
rewrite -> pointwise_mul_length in H0.
apply nth_mul_evals; lia.
Qed.

Definition pad(p:dense_cpoly) (n:nat) :=
p ++ repeat (RtoC 0) n.

Lemma eval_zeroes_end: forall p n x,
p[x] = (pad p n)[x].
Proof. 
unfold pad. 
induction p.
  - intros. simpl.
    induction n.
    + simpl. auto.
    + simpl. rewrite -> complex_add.
      rewrite <- IHn.
      unfold complex_eval; apply c_proj_eq; simpl; lra; simpl; lra.
  - intros.
    simpl.
    repeat rewrite -> complex_add.
    rewrite <- IHp.
    auto.
Qed.
    
Lemma naive_mult_padded: forall p1 p2 n x,
(pmul(pad p1 n)(pad p2 n))[x]= 
(pmul p1 p2)[x].
Proof.
intros.
rewrite <- pmul_correct.
induction n.
  - unfold pad.
    simpl.
    repeat rewrite -> app_nil_r.
    apply pmul_correct.
  - intros. 
    rewrite <- IHn.
    repeat rewrite <- eval_zeroes_end.
    apply c_proj_eq.
    all: simpl.
    all: lra.
Qed.

Lemma eval_pmul_padded: forall a p1 p2 x,
(pmul(pad p1 a)(pad p2 a))[x] = 
(pmul p1 p2)[x].
Proof.
intros.
rewrite <- pmul_correct.
repeat rewrite <- eval_zeroes_end.
apply pmul_correct.
Qed.

Lemma evals_pmul_padded: forall n j p1 p2 a b,
evals n j (pmul(pad p1 a)(pad p2 a))
=
evals n j (pad (pmul p1 p2) b). 
Proof.
induction j.
  - intros. simpl.
    repeat rewrite -> eval_pmul_padded. rewrite <- eval_zeroes_end.
    auto.
  - intros. 
    simpl.
    rewrite -> IHj with (b:= b).
    f_equal.
    rewrite -> eval_pmul_padded.
    rewrite <- eval_zeroes_end.
    auto.
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

(*Lemma add_poly_comm: forall p1 p2,
add_dense_poly p1 p2 = add_dense_poly p2 p1.
Proof.
induction p1.
  - simpl. destruct p2.
    + simpl. auto.
    + simpl. auto.
  - simpl.
    destruct p2.
    + simpl. auto.
    + simpl. rewrite -> IHp1. f_equal; ring.
Qed. *)

Lemma naive_mult_length_gt_left: forall p1 p2,
Nat.le 1 (length p2) ->
Nat.le (length p1) (length(pmul p1 p2)).
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
Nat.le (length p2) (length(pmul p1 p2)).
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
length(pmul p1 p2) = (length p2 + length p1 - 1)%nat.
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


Lemma one_le_2pow: forall n,
  (1 <= 2 ^ n)%nat.
Proof.
induction n.
  - simpl. auto.
  - simpl. apply le_trans with (m:= (2^n)%nat).
    apply IHn.
    lia.
Qed.

Definition fast_pmul(p1 p2: dense_cpoly)(n:nat):=
ifft (S n) (pointwise_mul' (fft (S n) (pad p1 (2^n)%nat) (\w_(2^(S n))%nat))
                   (fft (S n) (pad p2 (2^n)%nat) (\w_(2^(S n))%nat))(2^(S n)-1)%nat). 
                          

Lemma fast_pmul_correct: forall p1 p2 n x,
  length p1 = (2^n)%nat -> length p1 = length p2 ->
  (fast_pmul p1 p2 n)[x] = 
  (pmul p1 p2)       [x].
Proof.
intros.
unfold fast_pmul.
rewrite -> H in H0.
assert(length (p1 ++ repeat (RtoC 0) (2^n)%nat) = (2^(S n))%nat).
  rewrite -> app_length. 
  rewrite -> repeat_length.
  simpl. lia.
rewrite -> fft_correct by auto.
rewrite -> fft_correct.
unfold DFT.
replace(length (pad p1 (2 ^ n))) with (2^S n)%nat.
replace(length (pad p2 (2 ^ n))) with (2^S n)%nat.
rewrite -> mul_evals.
rewrite -> evals_pmul_padded with (b:= 1%nat).
replace (evals (\w_ (2 ^ S n)) (2 ^ S n - 1) (pad (pmul p1 p2) 1)) with (DFT((pad (pmul p1 p2) 1))).
(*
Definition DFT(p: dense_cpoly): list C:=
let n := length p in
evals(\w_n) (n-1) p.
*)
rewrite <- fft_correct with(n:= S n).
rewrite -> icorrect.
rewrite <- eval_zeroes_end.
auto.
(* degree of naive mult *)
all: unfold pad.
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
unfold DFT.
rewrite -> last_length.
Search(pmul).
rewrite -> naive_mult_length.
repeat rewrite -> H.
repeat rewrite <- H0.
f_equal. f_equal.
ring_simplify.
rewrite -> Nat.sub_add.
lia.
apply Nat.le_trans with (m:= (2^n)%nat).
apply one_le_2pow.
lia.
ring_simplify.
simpl. lia.
rewrite -> H. apply one_le_2pow.
rewrite <- H0. apply one_le_2pow.
rewrite -> app_length.
rewrite <- H0.
rewrite -> repeat_length.
lia.
rewrite -> app_length.
rewrite <- H0.
rewrite -> repeat_length.
lia.
Qed.

Check(RtoC 0).
Print C.






  
      






