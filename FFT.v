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
    
    
    
       

    
    

Lemma sparse_to_dense_step: forall p x (n: nat) a ,
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

Lemma even_leq: forall p,
  Nat.le (length(even_poly p)) (length p).
Proof. 
  intros; induction p.
    - simpl. lia.
    - unfold even_poly. 
      destruct (Nat.even(fst a)) eqn:E.
       + fold even_poly. 
         assert(length(a::even_poly p) = S(length(even_poly p))).
            simpl. reflexivity. 
         rewrite -> H. 
         assert(length(a::p) = S(length p)).
            simpl. reflexivity. 
         rewrite -> H0. 
         apply le_n_S. 
         apply IHp.
       + apply le_S. 
         apply IHp. 
Qed.

Lemma even_l: forall p,
 p <> nil -> Nat.lt (length(even_poly p))  (length p).
Proof. 
  induction p.
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
((nth_unit_root (2*n))^k)^2 = (nth_unit_root n)^k.
Proof.
Admitted.

Lemma unit_root_symmetry: forall n k,
nth_unit_root (2*n)^(k+n) = - (nth_unit_root (2*n))^k.
Proof.
intros. unfold nth_unit_root. Admitted.  


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
       rewrite -> unit_root_squares. reflexivity. 
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
          (rewrite -> unit_root_squares; reflexivity). 
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

Lemma degree_even_plus_odd: forall p,
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

Lemma even_and_odd_equal_succ: forall a p,
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

Lemma even_and_odd_not_equal_succ: forall a p,
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
  
Lemma even_eq_odd: forall p n,
degree_poly(even_poly_D p) = (2*n)%nat -> 
degree_poly(even_poly_D p) = degree_poly(odd_poly_D p).
Proof.
intros. unfold even_poly_D, odd_poly_D in *.
induction p.
  - simpl. reflexivity.
  - destruct p.
    + simpl in H.
      rewrite -> degree_add in H.
      assert(degree_poly nil = O) by (rewrite <- degree_nil; reflexivity).
      rewrite -> H0 in H.
      exfalso.
      lia.
    +
(*
Lemma even_degree_succ: forall n  a p,
degree_poly p = (2%nat^(S n))%nat ->
degree_poly (even_poly_D p) = degree_poly (even_poly_D (a::p)).
Proof.
intros. unfold even_poly_D.
induction p.
  - simpl.
    assert(degree_poly nil = O) by (rewrite <- degree_nil; reflexivity).
    rewrite -> H0 in H.
    assert(2%nat<>0%nat) by (lia).
    assert((2^S n)%nat <> 0%nat) by (apply Nat.pow_nonzero; apply H1).
    contradict H2; symmetry.
    apply H.
  - simpl.

Lemma even_half_degree: forall n p,
degree_poly p = (2%nat^(S n))%nat -> degree_poly (even_poly_D p) = (2%nat^n)%nat.
Proof.
intros.
unfold even_poly_D; simpl.
induction p.
  - simpl.
    assert(degree_poly nil = O) by (rewrite <- degree_nil; reflexivity).
    rewrite -> H0 in H.
    assert(2%nat<>0%nat) by (lia).
    Search((_^_)%nat).
    assert((2^S n)%nat <> 0%nat).
    apply Nat.pow_nonzero. apply H1.
    contradict H2.
    symmetry.
    apply H.
  - simpl.
    rewrite -> degree_add.
    rewrite -> degree_add in H.
    
*)
    
    

  


Fixpoint evals (w:R)(n:nat)(p:dense_poly) :=
  match n, p with
  | O, _ => Pdense_eval p 1::nil
  | S(n'), _ => (evals w n' p) ++ Pdense_eval p (w^n)::nil
  end.

Lemma evals_add: forall w  n p,
w = nth_unit_root n -> 
  evals w n p ++ Pdense_eval p (w^(S n))::nil = evals w (S n) p.
Proof.
intros. simpl. auto.
Qed.

Fixpoint fft_again (n:list nat)(p:list R):list R :=
  match n with
  | nil       => nil
  | 1%nat::n' => p
  | a::n'     => let w := nth_unit_root a in
                 let y_e := fft_again(n')(even_poly_D p) in
                 let y_o := fft_again(n')(odd_poly_D p) in 
                 let (f,s) := make_two y_e y_o w O in
                 f++s
  end.

Fixpoint powvec(w:R)(n:nat) :=
  match n with
  | O => 1::nil
  | S(n') => powvec w n' ++ w^n::nil
end.
  
Lemma make_two_correct: forall y_e y_o p n,
  Nat.le 1 n -> degree_poly p = (2*n)%nat -> 
  y_e = evals(nth_unit_root n) n (even_poly_D p) ->
  y_o = evals(nth_unit_root n) n (odd_poly_D p) ->
  fst(make_two y_e y_o (nth_unit_root(2*n)) O) = evals(nth_unit_root(2*n)) (n) p.
Proof.
intros. rewrite -> H1; rewrite -> H2.
unfold make_two.

simpl.
(*intros. destruct n.
  - simpl. exfalso. lia.
  - induction n.
    + simpl.
      rewrite -> H1; rewrite -> H2.
      simpl.
      replace (Pdense_eval (even_poly_D p) 1) with 
              (Pdense_eval (even_poly_D p) (1^2)) by (f_equal; lra).
      replace (Pdense_eval (odd_poly_D p) 1) with 
              (Pdense_eval (odd_poly_D p) (1^2)) by (f_equal; lra).
      rewrite -> even_and_odd_D'.
      f_equal.
      replace (Pdense_eval (even_poly_D p) (nth_unit_root 1 * 1) +
              nth_unit_root 2 * 1 * Pdense_eval (odd_poly_D p) (nth_unit_root 1 * 1)) 
      with
              (Pdense_eval (even_poly_D p) (nth_unit_root 1^1) +
              nth_unit_root (2*1)^1 * Pdense_eval (odd_poly_D p) (nth_unit_root 1^1))
      by f_equal.
      rewrite <- FFT_inductive_step_even.
      f_equal.
      exact H.
    + *)
      
     
      
 rewrite -> H0; rewrite -> H1.
      f_equal.
      
      
        

      
      
      
      
      
      
      
  

Lemma 
fft_zero: forall p n,
degree_poly p = (2^n)%nat  -> Pdense_eval p (nth_unit_root(2^n)^0) =
                              hd 0 (fft_again (powers2 n) p).
                       
Proof.
induction n.
  - simpl. intros. 
    rewrite <- FFT_base_case.
    unfold nth_unit_root.
    simpl.
    replace (2*PI/1) with (2*PI) by lra.
    rewrite -> cos_2PI.
    rewrite -> sin_2PI.
    replace(1+i*0) with (1) by lra.
    reflexivity.
    exact H.
  - intros. 
    replace (nth_unit_root (2 ^ S n) ^ 0) with 1 by lra.
    simpl. 
    Abort.
    
    

Fixpoint fft_attempt(n: list nat)(p : list R): list R :=
  match n with
  | nil       => nil
  | 1%nat::n' => p
  | a::n'     => let w   := nth_unit_root a in
                 let y_e := fft_attempt(n')(even_poly_D p) in
                 let y_o := fft_attempt(n')(odd_poly_D p) in 
                 



