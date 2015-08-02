import data.nat.div data.nat.gcd data.nat.sub data.set tools.fake_simplifier logic theories.number_theory.primes
open nat set eq.ops well_founded decidable fake_simplifier prod bool

definition eulerPhi.F (n m : ℕ) : (Π m₁ : ℕ, m₁< m → ℕ) → ℕ :=
  nat.cases_on m
    (λ f, nat.zero)
    (λ n₁(f : Π m₁, m₁ < succ n₁ → ℕ), (if coprime (succ n₁) n then 1 else 0) + (f n₁ !lt_succ_self))

definition eulerPhi (n : ℕ) : ℕ := fix (eulerPhi.F n) n

eval eulerPhi 6

eval prime

eval absurd

check gcd_dvd_right

theorem eq_one_from_prime_dvd_lt (k p : ℕ) (primep : prime p) (k_div_p : k ∣ p) (k_lt_p : k < p) : k = 1:=
  have H1 : k ≠ p, from and.elim_right ((relation.iff_ops.mp (lt_iff_le_and_ne k p)) (k_lt_p)),
  or_resolve_left (((and.elim_right primep) k) k_div_p) H1

theorem coprime_of_prime_of_pos_of_lt (i p : ℕ) (primep : prime p) (i_gt_zero : i > 0) (i_lt_p : i < p) : coprime i p := 
  have H1a : (gcd i p) ∣ p, from gcd_dvd_right i p,
  have H1b : (gcd i p) ∣ i, from gcd_dvd_left i p,
  have H2 : (gcd i p) ≤ i, from le_of_dvd i_gt_zero H1b,
  have H3 : (gcd i p) < p, from lt_of_le_of_lt H2 i_lt_p, 
  eq_one_from_prime_dvd_lt (gcd i p) p primep H1a H3
  
check coprime_of_prime_of_pos_of_lt


private definition eulerPhi_prime_minus_1.F (p : ℕ) : (Π p₂ : ℕ, p₂ < p → prime p₂ → eulerPhi p₂ = p₂ - 1) → prime p → eulerPhi p = p - 1 :=
  take primep : prime p, 
    nat.cases_on p
      (λ f, absurd primep not_prime_zero)
     (λ p₁ (f : Π p₂ : ℕ, p₂ < p → prime p₂ → eulerPhi p₂ = p₂ - 1), 
      sorry)

theorem eulerPhi_prime_minus_one (p : ℕ) : prime p → eulerPhi p = p - 1 := sorry
  

check eulerPhi_prime_minus_one







  





  









