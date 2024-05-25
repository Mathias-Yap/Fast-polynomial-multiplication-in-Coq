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
Proof. intros n. unfold Even, Odd. induction n. 
- unfold Nat.Even, Nat.Odd. left. exists 0%nat. reflexivity.
- rewrite -> Nat.Even_succ, Nat.Odd_succ. tauto. Qed.

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
Proof. intros. induction p1.
 - simpl. lra.
 - simpl. lra.
Qed.

(*Lemma even_odd_recomb: forall p x,
Pax_eval (even_poly p) x + Pax_eval(odd_poly p) x = Pax_eval(even_poly p ++ odd_poly p) x.
Proof. intros. apply add_recombination. Qed.*)

Lemma even_plus_odd: forall p x,
Pax_eval (even_poly p) x + Pax_eval (odd_poly p) x = Pax_eval p x.
Proof. intros. rewrite -> add_recombination. induction p. simpl. lra. simpl. 
 simpl. destruct (Nat.even (fst a)) eqn:Heven. 
- rewrite <- Nat.negb_even. rewrite -> Heven. simpl. lra.
- rewrite <- Nat.negb_even. rewrite -> Heven. simpl. 
assert(even_poly p = even_poly(a::p)). simpl. rewrite -> Heven. tauto. 
rewrite <- add_recombination. rewrite -> Pax_eval_cons. rewrite <- IHp. rewrite <- add_recombination. lra. Qed.



Fixpoint max_degree (p : list (nat * F)) : nat :=
  match p with
  | nil => 0
  | (n, _) :: t => Nat.max n (max_degree t)
  end.

Lemma max_degree_decreasing : forall p a,
Nat.le (max_degree(p)) (max_degree(a::p)). intros. induction (a). simpl.
induction p. 
- simpl.  rewrite -> Nat.max_0_r. apply Nat.le_0_l. 
 - Search(max). apply Nat.le_max_r.
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
Proof. intros. unfold PinjR. induction p.
 - simpl. auto.
 - rewrite -> Pax_eval_cons. simpl. lra. Qed. 


Lemma addR_recombination: forall p1 p2 x,
PaxR_eval p1 x + PaxR_eval p2 x = PaxR_eval (p1++p2) x.
Proof. intros. induction p1.
 - simpl. lra.
 - simpl. lra.
Qed.

Fixpoint max_degree_R (p : list (nat * R)) : nat :=
  match p with
  | nil => 0
  | (n, _) :: t => Nat.max n (max_degree_R t)
  end.

Lemma max_degree_R_decreasing : forall p a,
Nat.le (max_degree(p)) (max_degree(a::p)). intros. induction (a). simpl.
induction p. 
- simpl.  rewrite -> Nat.max_0_r. apply Nat.le_0_l. 
- apply Nat.le_max_r.
Qed.

Lemma PaxR_eval_cons: forall (p1 : list (nat * R)) (a0:nat*R) (y : R),
  PaxR_eval (a0 :: p1) y =
  snd a0 * y ^ fst a0 + PaxR_eval p1 y.
Proof. intros. simpl. tauto. Qed.

Lemma even_plus_odd_R: forall p x,
PaxR_eval (odd_poly_R p) x + PaxR_eval (even_poly_R p) x = PaxR_eval p x.
Proof. intros. induction p.
- simpl. lra.
- simpl. destruct (Nat.even (fst a)) eqn:Heven. 
rewrite <- Nat.negb_even. rewrite -> Heven. simpl. lra. 
rewrite <- Nat.negb_even. rewrite -> Heven. simpl. lra. Qed.



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
induction p as [|fn p]. auto. 
simpl. intros. rewrite -> IHp. lra. Qed.

Lemma Pdense_inductive_step: forall p x n,
  x * Pdense_eval' n p x = Pdense_eval' (S n) p x.
Proof. intros p x. induction p.
- unfold Pdense_eval'. intros n. lra.
- simpl. intros n. 
  assert (x*(a*x^n + Pdense_eval' (S n) p x) = a*(x*x^n) + x*Pdense_eval'(S n) p x).
   lra. rewrite -> H. f_equal. apply IHp. Qed.

Lemma sparse_to_dense_step: forall p a n, 
is_sorted_fst(a::p) ->
fst a =? n = true -> sparse_to_dense' (S n) (a::p) = 0::sparse_to_dense' n p.
Proof. intros p0 a0. induction p0.
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
intros. unfold dense_to_sparse,Pdense_eval. apply Peval_dts'. Qed.
 

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
Proof. intros p. induction p. 
   - auto. 
   - simpl. intros n. rewrite -> Nat.odd_succ.
     destruct (Nat.even n) eqn: E.
      + f_equal. apply IHp.
      + apply IHp.
Qed.

Lemma odd_succ_even:  forall p n,
odd_poly_D' n p = even_poly_D' (S n) p.
Proof. intros p. induction p. 
   - auto. 
   - intros n. induction n.
      + simpl. apply IHp.
      + simpl. rewrite -> Nat.odd_succ. 
        destruct(Nat.even n) eqn: E.
          * f_equal. apply IHp.
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
 intros. unfold Pdense_eval. simpl. f_equal. lra. apply pdense_eval_scale. Qed.

Lemma even_and_odd_D': forall p x,
 Pdense_eval (even_poly_D' 0 p) (x^2) + x*Pdense_eval(odd_poly_D' 0 p) (x^2) = Pdense_eval p x.
intros. induction p.
 - unfold Pdense_eval. simpl. lra.
 - simpl. rewrite <- even_succ_odd. rewrite <- odd_succ_even. 
   repeat rewrite -> pdense_eval_add. rewrite <- IHp. simpl. lra. Qed.

Lemma even_and_odd_D: forall p x,
 Pdense_eval (even_poly_D p) (x^2) + x*Pdense_eval(odd_poly_D p) (x^2) = Pdense_eval p x.
Proof. apply even_and_odd_D'. Qed.


Lemma sparse_to_dense_step: forall p x (n: nat) a ,
is_sorted_fst (a::p) -> fst a =? n = true -> x*Pdense_eval' (S n) (sparse_to_dense' (S n) (a::p)) x = Pdense_eval' n (sparse_to_dense' n (a::p)) x - snd a * x^n.
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
                unfold sparse_to_dense'. Abort.  
        
 
Definition fft(p:list(nat*R)) : list(nat*R) :=
let m:= max_degree_R p in 
let w:= nth_unit_root m in

let fix fft_rec(m:nat)(w:R)(p:list(nat*R)): list(nat*R) :=
  let n := max_degree_R p in 
    match n, m with
     |0, _ => p 
     |_,0 => nil
     |_,S(m') =>     let y_e := fft_rec m' w (even_poly_R p) in 
                     let y_o := fft_rec m' w (odd_poly_R p)  in
                     let 
                        fix inrange(j: nat)(w:R)(e o: list(nat*R)) :=
                            match j, y_e, y_o with
                            | 0,_,_ => nil
                            | _, nil,_ => nil
                            | _,_, nil => nil
                            | S(j'),e1::e',o1::o' => 
                                           (Nat.add j(Nat.div n 2),(snd e1 - w^n*(snd o1))) ::
                                           (n, (snd e1 + w^n*(snd o1))) ::
                                           inrange(j')(w) e' o'
                            end in
                     inrange n w y_e y_o  end in
    fft_rec m w p.

Fixpoint make_two (y_e y_o: list R) (w: R) (j: nat): (list R * list R) :=
  match y_e, y_o with
  | _, nil => (nil, nil)
  | nil, _ => (nil, nil)
  | e1::y_e', o1::y_o' =>
      let (list_pos, list_neg) := make_two y_e' y_o' w (S j) in
      (e1 + w^j * o1 :: list_pos, e1 - w^j * o1 :: list_neg)
  end.



Fixpoint fft_dense (n:nat)(m:nat)(p:list R) : list R :=
 match n,m with
  | _,O => nil
  | O,_ => nil
  | S(O),_ => p
  | S(S(n')),S(m') => let w := nth_unit_root n in
                      let y_e := fft_dense(n/2)(m')(even_poly_D p) in
                      let y_o := fft_dense(n/2)(m')(odd_poly_D p) in 
                      let(l1,l2) := make_two y_e y_o w O in
                      l1 ++ l2
  
  end.


(*Fixpoint fft_dense(p:list R) (w:R) (m:nat) : list R :=
  match m,p with
    | 0,_ => nil
    | _,nil => nil
    | S(m'),p => let y_e:= fft_dense(even_poly_D p) w  m'  in
                     let y_o:= fft_dense (odd_poly_D p) w m'  in
                     let (l1,l2) := make_two y_e y_o w 0 in
                     l1++l2
end.*)
Fixpoint unit_root_evals (p: list R) (w:R)(j:nat) : list R :=
  match j,p with
  | O,_ => nil
  | _, nil => nil
  | S j',a::p =>
      let prev_evals := unit_root_evals p w j' in
      prev_evals ++ (Pdense_eval p (w ^ j)::nil)
  end.

Lemma inductive_even : forall a p,
even_poly_D (a::p) = a :: odd_poly_D p.
Proof.
intros. unfold even_poly_D, odd_poly_D; simpl. rewrite <- odd_succ_even. auto. Qed.

Lemma inductive_odd : forall a p,
odd_poly_D (a::p) = even_poly_D p.
Proof. 
intros. unfold even_poly_D, odd_poly_D; simpl. rewrite <- even_succ_odd. auto. Qed.

Lemma even_leq: forall p,
  Nat.le (length(even_poly p)) (length p).
Proof. intros. induction p.
  - simpl. lia.
  - unfold even_poly. destruct (Nat.even(fst a)) eqn:E.
     + fold even_poly. assert(length(a::even_poly p) = S(length(even_poly p))).
        simpl. reflexivity. rewrite -> H. assert(length(a::p) = S(length p)).
        simpl. reflexivity. rewrite -> H0. apply le_n_S. apply IHp.
     + apply le_S. apply IHp. Qed.

Lemma even_l: forall p,
 p <> nil -> Nat.lt (length(even_poly p))  (length p).
Proof. induction p.
  - simpl. intros H. exfalso. apply H. reflexivity.
  - unfold even_poly. destruct (Nat.even(fst a)) eqn:E.
    + intros. fold even_poly. assert(length(a::even_poly p) = S(length(even_poly p))).
        simpl. reflexivity. rewrite -> H0. assert(length(a::p) = S(length p)).
        simpl. reflexivity. rewrite -> H1. rewrite <- Nat.succ_lt_mono.
        apply IHp. Abort. 
         
      
(* FRESH START *)
(* unit root: cos((2*PI)/n) + i * sin ((2*PI)/n) = e^((2*PI*I)/n).*)  
(* unit root properties: *)
(* Lemma even_and_odd_D: forall p x,
 Pdense_eval (even_poly_D p) (x^2) + x*Pdense_eval(odd_poly_D p) (x^2) =
 Pdense_eval p x.
 Qed. *)
Lemma unit_root_squares: forall n k,
((nth_unit_root n)^k)^2 = (nth_unit_root (n/2))^k.
Proof.
Admitted.

Lemma unit_root_symmetry: forall n k,
(nth_unit_root n)^(k+(n/2)) = - (nth_unit_root n)^k.
Proof.
intros. unfold nth_unit_root. Admitted.  

Lemma unit_root_squares_2: forall n,
(nth_unit_root n) ^ 2 = nth_unit_root (n/2).
Proof.
Admitted.

Lemma FFT_inductive_step_even: forall p j n,
Nat.le 1 n ->
Pdense_eval p ((nth_unit_root n)^j) = 
Pdense_eval(even_poly_D p)(nth_unit_root(n/2)^j) + 
(nth_unit_root n)^j * Pdense_eval(odd_poly_D p)(nth_unit_root (n/2)^j).
Proof. 
unfold Nat.le.
destruct n.
(* case n = 0 *)
 - intros. exfalso. lia.
(* case n >= 1*)
- rewrite <- unit_root_squares. symmetry. apply even_and_odd_D. Qed.


Lemma FFT_inductive_step_odd: forall p j n,
Nat.le 1 n -> 
Pdense_eval p (nth_unit_root n^(j+(n/2))) = 
Pdense_eval(even_poly_D p)(nth_unit_root(n/2)^j) - 
((nth_unit_root n)^j) * Pdense_eval(odd_poly_D p)(nth_unit_root (n/2)^j).
Proof.
unfold Nat.le. 
destruct n.
(* case n = 0 *)
 - intros. exfalso. lia.
(* induction starts at n = 1*)
 - intros.
     assert(forall n x p, x - n*p = x+(-n*p)). intros. lra. rewrite -> H0.
     rewrite <- unit_root_symmetry.
    
    

Lemma unit_root_square: forall n:nat,
n > 0 -> nth_unit_root(n)^(n/2) = -1.
Proof.
intros. simpl. unfold nth_unit_root. induction n.
  - simpl in H. exfalso. lra.
  - 
Fixpoint dft_poly (p:dense_poly) : list R :=



Lemma make_two_corr: forall p n w,
greater_degree p n -> nth_unit_root(2^n) = w  -> 
 fst(make_two(even_poly_D p)(odd_poly_D p) w 0) = unit_root_evals p w n.
Proof.
induction p. 
 - unfold unit_root_evals; simpl. induction n. 
  + auto.
  + auto.
 - intros. rewrite -> inductive_even. rewrite -> inductive_odd. simpl. 
  (*+ assert(nth_unit_root (2^0) = 1). unfold nth_unit_root. simpl.
    assert(2*PI/1 = 2*PI). lra. rewrite -> H1. Search(cos). rewrite -> cos_2PI.
    rewrite -> sin_2PI. lra. rewrite -> H1 in H0; symmetry in H0. simpl. rewrite -> H0.
    rewrite <- odd_succ_even. *)





