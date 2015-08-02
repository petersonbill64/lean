import data.nat.div data.nat.sub data.int tools.fake_simplifier data.int logic

open nat int eq.ops well_founded decidable fake_simplifier prod

private definition pair_nat.lt : nat × nat → nat × nat → Prop := measure pr₂
private definition pair_nat.lt.wf : well_founded pair_nat.lt :=
intro_k (measure.wf pr₂) 20 
local attribute pair_nat.lt.wf [instance]
local infixl `≺`:50 := pair_nat.lt

private definition gcd.lt.dec (x y₁ : nat) : (succ y₁, x mod succ y₁) ≺ (x, succ y₁) :=
mod_lt (succ_pos y₁)

/- extended gcd definitions and properties, and some utilities -/
definition egcd_rec_f (z : int) : int → int → int × int := 
  (λ s t, (t, s - t  * z))

definition egcdi.F (p₁ : nat × nat) : (Π p₂ : nat × nat, p₂ ≺ p₁ → (int × int)) → (int × int) :=
  prod.cases_on p₁ (λ x y, nat.cases_on y
    ( λ f,  pair 1 0 )
    ( λ y₁ (f : Π p₂, p₂ ≺ (x, succ y₁) → (int × int)),
      let bz := f (succ y₁, x mod succ y₁) !gcd.lt.dec  in
        prod.cases_on bz
          (egcd_rec_f (x div succ y₁))))

definition egcdi (x y : nat) := fix egcdi.F (pair x y)

theorem egcdi_zero_right (x : nat) : egcdi x 0 = pair 1 0 :=
  well_founded.fix_eq egcdi.F (x, 0)

theorem egcdi_zero_right_1 (x : nat) : pr₁ (egcdi x 0) = 1 := eq.subst (egcdi_zero_right x) rfl

theorem egcdi_zero_right_2 (x : nat) : pr₂ (egcdi x 0) = 0 := eq.subst (egcdi_zero_right x) rfl

theorem egcdi_succ (x y : nat) : egcdi x (succ y) = prod.cases_on (egcdi (succ y) (x mod succ y)) (egcd_rec_f (x div succ y)) :=
  well_founded.fix_eq egcdi.F (x, succ y)

theorem preq {A : Type} : (Π (p : A × A), p = (pr₁ p, pr₂ p))
 | (a, b) := have H11 : a = pr₁ (a, b), from rfl,
                have H12 : b = pr₂ (a, b), from rfl,
                have H21 : pr₁ (a, b) = pr₁ (pr₁ (a, b), pr₂ (a, b)), from rfl,
                have H22 : pr₂ (a, b) = pr₂ (pr₁ (a, b), pr₂ (a, b)), from rfl,
                have H1 : pr₁ (a, b) = pr₁ (pr₁ (a, b), pr₂ (a, b)), from eq.trans H11 H21,
                have H2 : pr₂ (a, b) = pr₂ (pr₁ (a, b), pr₂ (a, b)), from eq.trans H12 H22,
                prod.equal H1 H2

theorem pc1 (z s t : int) : prod.cases_on (s, t) (egcd_rec_f z) = (t, s - t * z) :=
  have H1 : prod.cases_on (s, t) (egcd_rec_f z) = egcd_rec_f z s t, from rfl,
  have H2 : egcd_rec_f z s t = (t, s - t * z), from rfl,
  eq.trans H1 H2

theorem pc2 (z : int) (p : int × int) : prod.cases_on p (egcd_rec_f z) = (pr₂ p, (pr₁ p) -  (pr₂ p) *  z) := 
  have H1 : prod.cases_on (pr₁ p, pr₂ p) (egcd_rec_f z) = (pr₂ p, (pr₁ p) - (pr₂ p) * z), from pc1 z (pr₁ p) (pr₂ p),
  eq.subst (preq p)⁻¹ H1               


theorem egcdi_succ2 (x y : nat) : egcdi x (succ y) =  (pr₂ (egcdi (succ y) (x mod succ y)), (pr₁ (egcdi (succ y) (x mod succ y))) - (pr₂ (egcdi (succ y) (x mod succ y))) * (x div succ y)) :=
  have H1 : egcdi x (succ y) = prod.cases_on (egcdi (succ y) (x mod succ y)) (egcd_rec_f (x div succ y)), from egcdi_succ x y,
  have H2 : prod.cases_on (egcdi (succ y) (x mod succ y)) (egcd_rec_f (x div succ y)) = 
    (pr₂ (egcdi (succ y) (x mod succ y)), int.sub (pr₁ (egcdi (succ y) (x mod succ y))) (int.mul (pr₂ (egcdi (succ y) (x mod succ y))) (x div succ y))), from pc2 (x div succ y) (egcdi (succ y) (x mod succ y)),
  eq.trans H1 H2


theorem int_rearrange (a b c : int) : a + (b - (a - c)) = b + c :=
  calc a + (b - (a - c)) = a + (b + (int.neg (a - c))) : int.sub_eq_add_neg
                            ... = a + (b + (c - a)) : int.neg_sub
                            ... = a + (b + (c + (int.neg a))) : int.sub_eq_add_neg
                            ... = a + (b + ((int.neg a) + c)) : int.add.comm
                            ... = a + (((int.neg a) + c) + b) : int.add.comm
                            ... = (a + ((int.neg a) + c)) + b : int.add.assoc
                            ... = c + b : int.add_neg_cancel_left
                            ... = b + c : int.add.comm

theorem sub_mod_eq_int_sub_mod (x y : nat) : x - (x mod (succ y)) = int.sub x (x mod (succ y)) :=
  (int.of_nat_sub_of_nat mod_le)⁻¹


theorem divmul (x y : nat) : int.mul (x div y) y = x - (x mod y) :=
  calc int.mul (x div y) y = nat.mul (nat.divide x y) y : int.of_nat_mul_of_nat
                               ... = (x div y) * y + (x mod y) - (x mod y) : (nat.add_sub_cancel ((x div y) * y) (x mod y))⁻¹
                               ... = x - (x mod y) : eq_div_mul_add_mod⁻¹


theorem egcdi_succ_first (x y : nat) : pr₁ (egcdi x (succ y)) = pr₂ (egcdi (succ y) (x mod succ y)) :=
  calc pr₁ (egcdi x (succ y)) = pr₁ (pr₂ (egcdi (succ y) (x mod succ y)), (pr₁ (egcdi (succ y) (x mod succ y))) - ((pr₂ (egcdi (succ y) (x mod succ y))) * (x div succ y))) : egcdi_succ2 x y
                                    ... = pr₂ (egcdi (succ y) (x mod succ y)) : rfl

theorem egcdi_succ_second (x y : nat) : pr₂ (egcdi x (succ y)) = (pr₁ (egcdi (succ y) (x mod succ y))) - ((pr₂ (egcdi (succ y) (x mod succ y))) * (x div succ y)) :=
  calc pr₂ (egcdi x (succ y)) = pr₂ (pr₂ (egcdi (succ y) (x mod succ y)), (pr₁ (egcdi (succ y) (x mod succ y))) - ((pr₂ (egcdi (succ y) (x mod succ y))) * (x div succ y))) : egcdi_succ2 x y
                                    ... = (pr₁ (egcdi (succ y) (x mod succ y))) - ((pr₂ (egcdi (succ y) (x mod succ y))) *  (x div succ y)) : rfl


/- Inductive step
 -/

theorem egcdi_ind (x y : nat) :
  ((pr₁ (egcdi (succ y) (x mod (succ y)))) * (succ y)) + ((pr₂ (egcdi (succ y) (x mod (succ y)))) *  (x mod (succ y))) = gcd (succ y) (x mod (succ y)) → 
  ((pr₁ (egcdi x (succ y))) *  x) + ((pr₂ (egcdi x (succ y))) * (succ y)) = gcd x (succ y) := 
    assume IH : ((pr₁ (egcdi (succ y) (x mod (succ y)))) * (succ y)) +  ((pr₂ (egcdi (succ y) (x mod (succ y)))) *  (x mod (succ y))) = gcd (succ y) (x mod (succ y)),
    calc int.add (int.mul (pr₁ (egcdi x (succ y)))  x)  (int.mul (pr₂ (egcdi x (succ y))) (succ y)) = int.add (int.mul (pr₂ (egcdi (succ y) (x mod succ y)))  x)  (int.mul (pr₂ (egcdi x (succ y))) (succ y)) : egcdi_succ_first x y
                                                                                                                                 ... = int.add (int.mul (pr₂ (egcdi (succ y) (x mod succ y)))  x) 
                                                                                                                                                    (int.mul (int.sub (pr₁ (egcdi (succ y) (x mod succ y))) (int.mul (pr₂ (egcdi (succ y) (x mod succ y))) (x div succ y))) (succ y)) : egcdi_succ_second x y
                                                                                                                                 ... = int.add (int.mul (pr₂ (egcdi (succ y) (x mod succ y)))  x) 
                                                                                                                                                    (int.sub
                                                                                                                                                      (int.mul (pr₁ (egcdi (succ y) (x mod succ y))) (succ y))
                                                                                                                                                      (int.mul (int.mul   (pr₂ (egcdi (succ y) (x mod succ y)))   (x div succ y)  ) (succ y) ) ) : int.mul_sub_right_distrib
                                                                                                                                 ... = int.add (int.mul (pr₂ (egcdi (succ y) (x mod succ y)))  x) 
                                                                                                                                                    (int.sub
                                                                                                                                                      (int.mul (pr₁ (egcdi (succ y) (x mod succ y))) (succ y))
                                                                                                                                                      (int.mul   (pr₂ (egcdi (succ y) (x mod succ y)))  
                                                                                                                                                                    (int.mul  (x div succ y)  (succ y))
                                                                                                                                                      )
                                                                                                                                                    ) : int.mul.assoc
                                                                                                                                 ... = int.add (int.mul (pr₂ (egcdi (succ y) (x mod succ y)))  x) 
                                                                                                                                                    (int.sub
                                                                                                                                                      (int.mul (pr₁ (egcdi (succ y) (x mod succ y))) (succ y))
                                                                                                                                                      (int.mul   (pr₂ (egcdi (succ y) (x mod succ y)))  
                                                                                                                                                                    (x - (x mod (succ y)))
                                                                                                                                                      )
                                                                                                                                                    ) : divmul x (succ y)
                                                                                                                                 ... = int.add (int.mul (pr₂ (egcdi (succ y) (x mod succ y)))  x) 
                                                                                                                                                    (int.sub
                                                                                                                                                      (int.mul (pr₁ (egcdi (succ y) (x mod succ y))) (succ y))
                                                                                                                                                      (int.mul   (pr₂ (egcdi (succ y) (x mod succ y)))  
                                                                                                                                                                    (int.sub x (x mod (succ y)))
                                                                                                                                                      )
                                                                                                                                                    ) : sub_mod_eq_int_sub_mod x y
                                                                                                                                 ... = int.add (int.mul (pr₂ (egcdi (succ y) (x mod succ y)))  x) 
                                                                                                                                                    (int.sub
                                                                                                                                                      (int.mul (pr₁ (egcdi (succ y) (x mod succ y))) (succ y))
                                                                                                                                                      (int.sub   (int.mul (pr₂ (egcdi (succ y) (x mod succ y))) x)
                                                                                                                                                                    (int.mul (pr₂ (egcdi (succ y) (x mod succ y))) (x mod (succ y)))
                                                                                                                                                      )
                                                                                                                                                    ) : int.mul_sub_left_distrib
                                                                                                                                 ... = int.add (int.mul (pr₁ (egcdi (succ y) (x mod succ y))) (succ y)) 
                                                                                                                                                    (int.mul (pr₂ (egcdi (succ y) (x mod succ y))) (x mod (succ y)))
                                                                                                                                                      : int_rearrange (int.mul (pr₂ (egcdi (succ y) (x mod succ y)))  x)
                                                                                                                                                                            (int.mul (pr₁ (egcdi (succ y) (x mod succ y))) (succ y))
                                                                                                                                                                            (int.mul (pr₂ (egcdi (succ y) (x mod succ y))) (x mod (succ y)))
                                                                                                                                 ... = gcd (succ y) (x mod (succ y)) : IH
                                                                                                                                 ... = gcd x (succ y) : (gcd_rec x (succ y))⁻¹

    

/- Base case
 -/

theorem egcdi_base (x : nat) : int.add (int.mul (pr₁ (egcdi x 0)) x) (int.mul (pr₂ (egcdi x 0)) 0) = gcd x 0 :=
  calc int.add (int.mul (pr₁ (egcdi x 0)) x) (int.mul (pr₂ (egcdi x 0)) 0) =  int.add (int.mul 1 x) (int.mul (pr₂ (egcdi x 0)) 0) : egcdi_zero_right_1
                                                                                                 ... =  int.add (int.mul 1 x) (int.mul 0 0) : egcdi_zero_right_2
                                                                                                 ... =  int.add (int.mul x 1) (int.mul 0 0) : int.mul.comm
                                                                                                 ... =  int.add x (int.mul 0 0) : int.mul_one
                                                                                                 ... =  int.add x 0 : int.mul_zero
                                                                                                 ... =  x + 0 : int.of_nat_add_of_nat
                                                                                                 ... =  x : nat.add_zero 
                                                                                                 ... =  gcd x 0 : gcd_zero_right




/- Conclusion
 -/

private definition P (p : nat × nat) := (pr₁ (egcdi (pr₁ p) (pr₂ p))) * (pr₁ p) + (pr₂ (egcdi (pr₁ p) (pr₂ p))) * (pr₂ p) = gcd (pr₁ p) (pr₂ p)

private theorem Pbase (x : nat) : P (x, 0) := egcdi_base x
private theorem Prec (x y : nat) : P (succ y, x mod (succ y)) → P (x, succ y) := egcdi_ind x y

private definition P.F (p₁ : nat × nat) : (Π p₂ : nat × nat, p₂ ≺ p₁ → P p₂) → P p₁ :=
  prod.cases_on p₁ (λx y, nat.cases_on y
    (λ f, Pbase x)
    (λ y₁ (f : Πp₂, p₂ ≺ (x, succ y₁) → P p₂), (Prec x y₁) (f (succ y₁, x mod succ y₁) !gcd.lt.dec)   ))

private definition Bezouts1 (x y : ℕ) : (pr₁ (egcdi x y)) * x + (pr₂ (egcdi x y)) * y = gcd x y := fix P.F (pair x y)

theorem BezoutsLemma : ∀ x y : ℕ, ∃ a b : ℤ, a * x + b * y = gcd x y :=
  take x y : ℕ,
    let a := pr₁ (egcdi x y),
         b := pr₂ (egcdi x y)
    in have H : a * x + b * y = gcd x y, from Bezouts1 x y,
        exists.intro a (exists.intro b H)

  
check BezoutsLemma






  









