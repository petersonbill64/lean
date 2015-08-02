import data.nat.div data.nat.gcd data.nat.sub data.set tools.fake_simplifier logic

open nat set eq.ops well_founded decidable fake_simplifier prod bool

check decidable

private definition sum_cond_map.F (P : ℕ → ℕ → Prop) (H: ∀ p q : ℕ, decidable (P p q)) (T   : ℕ → ℕ)  (n : ℕ) (m : ℕ) : (Π m₁ : ℕ, m₁ < m → ℕ) → ℕ :=
  nat.cases_on m
    (λ f, nat.zero)
    (λ n₁ (f : Π m₁, m₁ < succ n₁ → ℕ), (if P (succ n₁) n then T (succ n₁) else 0) + (f n₁ !lt_succ_self))  

definition sum_cond_map (P : ℕ → ℕ → Prop) (H: ∀ p q : ℕ, decidable (P p q)) (T   : ℕ → ℕ)  (n : ℕ) : ℕ :=
  fix (sum_cond_map.F P H T n) n

definition sum_coprime_map (T : ℕ → ℕ) (n : ℕ) : ℕ := sum_cond_map coprime _ T n

definition sum_divisor_map (T : ℕ → ℕ) (n : ℕ) : ℕ := sum_cond_map nat.dvd _ T n

definition euler_phi (n : ℕ) : ℕ := sum_coprime_map (λ x, 1) n

definition gauss_sum (n : ℕ) : ℕ  := sum_divisor_map euler_phi n

eval euler_phi 6

eval gauss_sum 7

definition coprime_i [reducible] (i m n: ℕ) : Prop :=  gcd m n = i

theorem coprime_i_dec (i : ℕ) : ∀ p q : ℕ, decidable (coprime_i i p q) := _

definition g2 (i n : ℕ) := sum_cond_map (coprime_i i) (coprime_i_dec i) (λ x : ℕ, 1) n

definition g3 (n : ℕ) := sum_divisor_map (λ i : ℕ, sum_cond_map (λ c j : ℕ , coprime c (n div i)) _ (λ x, 1) i) n


eval g3 5

eval coprime_i 1 2 2
