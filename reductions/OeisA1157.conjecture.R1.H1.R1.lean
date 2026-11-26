import OMAReductions.R_OeisA1157_conjecture_R1

/-! Prime exponents suffice for the same-support step of the divisor-sum conjecture. -/

-- Reduction OeisA1157.conjecture.R1.H1.R1 of step OeisA1157.conjecture.R1.H1
-- Credit: @JamesSlash

namespace OMA.R_OeisA1157_conjecture_R1_H1_R1

open ArithmeticFunction Finset

-- The square case for products of geometric numerators.
def H1 : Prop :=
  ∀ s : Finset ℕ, (∀ p ∈ s, p.Prime) → ∀ u v : ℕ → ℕ,
    (∀ p ∈ s, 2 ≤ u p) → (∀ p ∈ s, 2 ≤ v p) → (∃ p ∈ s, u p ≠ v p) →
    (∏ p ∈ s, (1 - 1 / (p : ℚ) ^ (2 * u p))) ≠
      ∏ p ∈ s, (1 - 1 / (p : ℚ) ^ (2 * v p))

-- The corresponding assertion at odd prime exponents.
def H2 : Prop :=
  ∀ r : ℕ, r.Prime → r ≠ 2 → ∀ s : Finset ℕ, (∀ p ∈ s, p.Prime) → ∀ u v : ℕ → ℕ,
    (∀ p ∈ s, 2 ≤ u p) → (∀ p ∈ s, 2 ≤ v p) → (∃ p ∈ s, u p ≠ v p) →
    (∏ p ∈ s, (1 - 1 / (p : ℚ) ^ (r * u p))) ≠
      ∏ p ∈ s, (1 - 1 / (p : ℚ) ^ (r * v p))

theorem geom_ratio (z : ℚ) (hz : z ≠ 0) (a : ℕ) :
    ((∑ i ∈ range (a + 1), z ^ i) / z ^ a) * (1 - 1 / z) = 1 - 1 / z ^ (a + 1) := by
  calc
    _ = (∑ i ∈ range (a + 1), z ^ i) * (z - 1) / z ^ (a + 1) := by
      rw [pow_succ]
      field_simp
    _ = _ := by
      rw [geom_sum_mul]
      field_simp

theorem geometric_numerator (k n : ℕ) (hn : n ≠ 0) :
    (sigma k n : ℚ) / (n : ℚ) ^ k * (∏ p ∈ n.primeFactors, (1 - 1 / (p : ℚ) ^ k)) =
      ∏ p ∈ n.primeFactors, (1 - 1 / (p : ℚ) ^ (k * (n.factorization p + 1))) := by
  have hpows : (n : ℚ) ^ k = ∏ p ∈ n.primeFactors, ((p : ℚ) ^ n.factorization p) ^ k := by
    rw [Finset.prod_pow]
    have hncast : (n : ℚ) = ∏ p ∈ n.primeFactors, (p : ℚ) ^ n.factorization p := by
      exact_mod_cast Nat.prod_primeFactors_pow_factorization hn
    exact congrArg (· ^ k) hncast
  rw [sigma_eq_prod_primeFactors_sum_range_factorization_pow_mul hn, Nat.cast_prod, hpows,
    ← Finset.prod_div_distrib, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro p hp
  have hpq : (p : ℚ) ≠ 0 := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).ne_zero
  have hsym (i : ℕ) : (p : ℚ) ^ (i * k) = ((p : ℚ) ^ k) ^ i := by
    rw [Nat.mul_comm i k, pow_mul]
  rw [Nat.cast_sum, ← pow_mul, hsym, pow_mul]
  simp_rw [Nat.cast_pow, hsym]
  exact geom_ratio _ (pow_ne_zero _ hpq) _

theorem main : H1 → H2 → OMA.R_OeisA1157_conjecture_R1.H1 := by
  intro squares oddPrimes k hk n m hn hm hnm _ _ _ hs heq
  have hrat : (sigma k n : ℚ) / (n : ℚ) ^ k = (sigma k m : ℚ) / (m : ℚ) ^ k := by
    apply (div_eq_div_iff (by positivity : (n : ℚ) ^ k ≠ 0)
      (by positivity : (m : ℚ) ^ k ≠ 0)).mpr
    exact_mod_cast heq
  have hprod := (geometric_numerator k n hn.ne').symm.trans
    ((congrArg (· * (∏ p ∈ n.primeFactors, (1 - 1 / (p : ℚ) ^ k))) hrat).trans
      (by rw [hs, geometric_numerator k m hm.ne']))
  have hdiff : ∃ p ∈ n.primeFactors, n.factorization p ≠ m.factorization p := by
    by_contra h
    push Not at h
    apply hnm
    suffices n = m by simp [this]
    calc
      n = ∏ p ∈ n.primeFactors, p ^ n.factorization p := Nat.prod_primeFactors_pow_factorization hn.ne'
      _ = ∏ p ∈ n.primeFactors, p ^ m.factorization p :=
        Finset.prod_congr rfl fun p hp ↦ by rw [h p hp]
      _ = m := hs.symm ▸ (Nat.prod_primeFactors_pow_factorization hm.ne').symm
  obtain ⟨r, hr, c, hkc⟩ := Nat.exists_prime_and_dvd (show k ≠ 1 by omega)
  have hc : 0 < c := Nat.pos_of_ne_zero (by rintro rfl; simp at hkc; omega)
  let u : ℕ → ℕ := fun p ↦ c * (n.factorization p + 1)
  let v : ℕ → ℕ := fun p ↦ c * (m.factorization p + 1)
  have hu : ∀ p ∈ n.primeFactors, 2 ≤ u p := by
    intro p hp
    have hpos : n.factorization p ≠ 0 := by
      rwa [← Finsupp.mem_support_iff, Nat.support_factorization]
    dsimp [u]
    simpa using Nat.mul_le_mul (show 1 ≤ c by omega) (show 2 ≤ n.factorization p + 1 by omega)
  have hv : ∀ p ∈ n.primeFactors, 2 ≤ v p := by
    intro p hp
    have hpos : m.factorization p ≠ 0 := by
      rwa [← Finsupp.mem_support_iff, Nat.support_factorization, ← hs]
    dsimp [v]
    simpa using Nat.mul_le_mul (show 1 ≤ c by omega) (show 2 ≤ m.factorization p + 1 by omega)
  have huv : ∃ p ∈ n.primeFactors, u p ≠ v p := by
    obtain ⟨p, hp, hpne⟩ := hdiff
    refine ⟨p, hp, fun huv ↦ hpne ?_⟩
    dsimp [u, v] at huv
    have hp' := Nat.mul_left_cancel (by omega : 0 < c) huv
    omega
  have hscaled : (∏ p ∈ n.primeFactors, (1 - 1 / (p : ℚ) ^ (r * u p))) =
      ∏ p ∈ n.primeFactors, (1 - 1 / (p : ℚ) ^ (r * v p)) := by
    rw [← hs] at hprod
    simpa only [u, v, ← Nat.mul_assoc, ← hkc] using hprod
  by_cases htwo : r = 2
  · subst r
    exact squares _ (fun _ hp ↦ Nat.prime_of_mem_primeFactors hp) u v hu hv huv hscaled
  · exact oddPrimes r hr htwo _ (fun _ hp ↦ Nat.prime_of_mem_primeFactors hp) u v hu hv huv hscaled

end OMA.R_OeisA1157_conjecture_R1_H1_R1
