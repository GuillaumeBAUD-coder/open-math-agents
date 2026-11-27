import FormalConjectures.ErdosProblems.«1107»

-- Credit: @marcusbuffett
-- Blomer, Uniform bounds for Fourier coefficients of theta-series with arithmetic applications,
-- Sections 3 and 5. Use a small prime coefficient coprime to the represented integer.
namespace OMA.R_Erdos1107_erdos_1107_variants_two_R1

open Finset Filter Real

private lemma two_test {q : ℕ} (hq : q % 8 = 7) (n : ℕ) : ∃ x y z : ZMod 8, (q : ZMod 8)^3 * x^2 + y^2 + z^2 = n ∧
    (x.val % 2 = 1 ∨ y.val % 2 = 1 ∨ z.val % 2 = 1) := by
  have h : ∀ a : ZMod 8, ∃ x y z : ZMod 8,
      7^3 * x^2 + y^2 + z^2 = a ∧ (x.val % 2 = 1 ∨ y.val % 2 = 1 ∨ z.val % 2 = 1) := by
    decide +kernel
  have hq' : (q : ZMod 8) = 7 := by
    calc (q : ZMod 8) = ((q % 8 : ℕ) : ZMod 8) := (ZMod.natCast_mod q 8).symm
         _ = 7 := by rw [hq]; rfl
  rw [hq']
  exact h n

private lemma odd_test {q n : ℕ} (hq : q.Prime) (hnq : ¬ q ∣ n)
    (p : ℕ) (hp : p.Prime) : ∃ x y z : ZMod p, (q : ZMod p)^3 * x^2 + y^2 + z^2 = n ∧
    ((q : ZMod p) * x ≠ 0 ∨ y ≠ 0 ∨ z ≠ 0) := by
  letI : Fact p.Prime := ⟨hp⟩
  by_cases hn : (n : ZMod p) = 0
  · have hpq : p ≠ q := by
      intro h
      exact hnq (h ▸ (ZMod.natCast_eq_zero_iff n p).mp hn)
    have hu : (q : ZMod p) ≠ 0 := by
      simpa only [ne_eq, ZMod.natCast_eq_zero_iff, Nat.prime_dvd_prime_iff_eq hp hq] using hpq
    obtain ⟨y, z, h⟩ := ZMod.sq_add_sq p (- (q : ZMod p)^3)
    refine ⟨1, y, z, ?_, Or.inl (by simpa using hu)⟩
    rw [hn]; simp only [one_pow, mul_one]; linear_combination h
  · obtain ⟨y, z, h⟩ := ZMod.sq_add_sq p (n : ZMod p)
    refine ⟨0, y, z, by simpa using h, Or.inr ?_⟩
    by_contra! hh
    simp [hh.1, hh.2] at h
    exact hn h.symm

private lemma small_prime {n : ℕ} (hn : 1 < n)
    (ht : (16 * log n) / 8 ≤ ∑ p ∈ ((Icc 1 ⌊16 * log n⌋₊).filter fun p => p.Prime ∧ p % 8 = 7), log p) :
    ∃ q : ℕ, q.Prime ∧ q % 8 = 7 ∧ (q : ℝ) ≤ 16 * log n ∧ ¬ q ∣ n := by
  let S : Finset ℕ := ((Icc 1 ⌊16 * log n⌋₊).filter fun p => p.Prime ∧ p % 8 = 7)
  by_contra! h
  have hsub : S ⊆ n.primeFactors := by
    intro p hp
    obtain ⟨hi, hprime, hseven⟩ := mem_filter.mp hp
    have hle : (p : ℝ) ≤ 16 * log n := (Nat.floor_le (by positivity)).trans' (by
      exact_mod_cast (mem_Icc.mp hi).2)
    exact Nat.mem_primeFactors.mpr ⟨hprime, h p hprime hseven hle, by omega⟩
  have hprod : (∏ p ∈ S, p) ∣ n :=
    (Finset.prod_dvd_prod_of_subset _ _ _ hsub).trans n.prod_primeFactors_dvd
  have hpos (p : ℕ) (hp : p ∈ S) : (0 : ℝ) < p := by
    exact_mod_cast (Nat.prime_of_mem_primeFactors (hsub hp)).pos
  have hprodpos : (0 : ℝ) < ∏ p ∈ S, (p : ℝ) := Finset.prod_pos hpos
  have hle : (∏ p ∈ S, (p : ℝ)) ≤ n := by
    rw [← Nat.cast_prod]
    exact_mod_cast Nat.le_of_dvd (by omega) hprod
  have hlog := Real.log_le_log hprodpos hle
  rw [Real.log_prod (fun p hp => (hpos p hp).ne')] at hlog
  have hnlog : 0 < log n := Real.log_pos (by exact_mod_cast hn)
  change (16 * log n) / 8 ≤ ∑ p ∈ S, log p at ht
  linarith

private lemma square_full (x : ℕ) : Nat.Full 2 (x^2) := by
  intro p hp
  have h := Nat.mem_primeFactors.mp hp
  exact pow_dvd_pow_of_dvd (h.1.dvd_of_dvd_pow h.2.1) 2

private lemma cube_square_full (q x : ℕ) : Nat.Full 2 (q^3 * x^2) := by
  intro p hp
  have h := Nat.mem_primeFactors.mp hp
  rcases h.1.dvd_mul.mp h.2.1 with hd | hd
  · exact dvd_mul_of_dvd_left ((pow_dvd_pow_of_dvd (h.1.dvd_of_dvd_pow hd) 2).trans
      (pow_dvd_pow q (by decide : 2 ≤ 3))) _
  · exact dvd_mul_of_dvd_right (pow_dvd_pow_of_dvd (h.1.dvd_of_dvd_pow hd) 2) _

-- A weak Chebyshev lower bound in the progression 7 modulo 8.
def H1 : Prop :=
  ∀ᶠ x : ℝ in atTop, x / 8 ≤ ∑ p ∈ ((Icc 1 ⌊x⌋₊).filter fun p => p.Prime ∧ p % 8 = 7), log p

-- Uniform ternary local-to-global estimate for the forms of logarithmic level
-- growth. This isolates the theta-series estimate from the prime selection.
def H2 : Prop :=
  ∀ᶠ n : ℕ in atTop, ∀ q : ℕ, q.Prime → q % 2 = 1 →
    (q : ℝ) ≤ 16 * log n → ¬ q ∣ n → (∃ x y z : ZMod 8, (q : ZMod 8)^3 * x^2 + y^2 + z^2 = n ∧
    (x.val % 2 = 1 ∨ y.val % 2 = 1 ∨ z.val % 2 = 1)) →
    (∀ p : ℕ, p.Prime → p ≠ 2 → (∃ x y z : ZMod p, (q : ZMod p)^3 * x^2 + y^2 + z^2 = n ∧
    ((q : ZMod p) * x ≠ 0 ∨ y ≠ 0 ∨ z ≠ 0))) →
    ∃ x y z : ℕ, q^3*x^2 + y^2 + z^2 = n

theorem main : H1 → H2 → type_of% @Erdos1107.erdos_1107.variants.two := by
  intro theta forms
  have ht : Tendsto (fun n : ℕ => 16 * log n) atTop atTop :=
    (tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).const_mul_atTop (by norm_num)
  filter_upwards [ht.eventually theta, forms, eventually_gt_atTop 1] with n htheta hf hn
  obtain ⟨q, hq, h7, hbound, hcop⟩ := small_prime hn htheta
  obtain ⟨x, y, z, heq⟩ := hf q hq (by omega) hbound hcop (two_test h7 n)
    (fun p hp _ => odd_test hq hcop p hp)
  refine ⟨[q^3*x^2, y^2, z^2], by simp, ?_, ?_⟩
  · intro t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl
    · exact cube_square_full q x
    · exact square_full y
    · exact square_full z
  · simpa [add_assoc] using heq

end OMA.R_Erdos1107_erdos_1107_variants_two_R1
