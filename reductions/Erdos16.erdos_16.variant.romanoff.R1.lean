import FormalConjectures.ErdosProblems.«16»

-- Reduction Erdos16.erdos_16.variant.romanoff.R1 of Erdős Problem 16 — romanoff
-- Credit: @senamakel
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

/-! Romanoff's theorem from a first-moment lower bound (Chebyshev) and a second-moment upper
bound (Romanoff's sieve estimate) on `r(n) = #{k ≥ 1 : n - 2^k is an odd prime}`, glued by
Cauchy–Schwarz. -/

namespace OMA.R_Erdos16_erdos_16_variant_romanoff_R1

/-- Chebyshev-type lower count: the number of representations `n = 2^k + p`
(`k ≥ 1`, `p` an odd prime) with `n ≤ x` is at least `c * x`. -/
def H1 : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∃ x₀ : ℕ, ∀ x : ℕ, x₀ ≤ x →
    c * x ≤ ∑ n ∈ Finset.range (x + 1),
      (((Finset.range n).filter (fun k => 1 ≤ k ∧ 2 ^ k < n ∧ (n - 2 ^ k).Prime ∧
        n - 2 ^ k ≠ 2)).card : ℝ)

/-- Romanoff's second-moment bound: `∑_{n ≤ x} r(n)^2 ≤ C x`, where `r(n)` counts
the representations `n = 2^k + p` with `k ≥ 1` and `p` an odd prime. -/
def H2 : Prop :=
  ∃ C : ℝ, ∀ x : ℕ, 2 ≤ x →
    ∑ n ∈ Finset.range (x + 1),
      (((Finset.range n).filter (fun k => 1 ≤ k ∧ 2 ^ k < n ∧ (n - 2 ^ k).Prime ∧
        n - 2 ^ k ≠ 2)).card : ℝ) ^ 2 ≤ C * x

theorem main : H1 → H2 → type_of% @Erdos16.erdos_16.variant.romanoff := by
  rintro ⟨c, hc, x₀, hx₀⟩ ⟨C, hC⟩
  intro S
  unfold Erdos16.positive_lower_density
  set r : ℕ → ℕ := fun n => ((Finset.range n).filter (fun k => 1 ≤ k ∧ 2 ^ k < n ∧
    (n - 2 ^ k).Prime ∧ n - 2 ^ k ≠ 2)).card with hr
  have memS : ∀ n, 0 < r n → n ∈ S := by
    intro n hn
    obtain ⟨k, hk⟩ := Finset.card_pos.1 hn
    simp only [Finset.mem_filter, Finset.mem_range] at hk
    obtain ⟨-, hk1, hlt, hp, hp2⟩ := hk
    refine ⟨?_, k, n - 2 ^ k, hp, by omega⟩
    have h1 : Odd (n - 2 ^ k) := hp.odd_of_ne_two hp2
    have h2 : Even (2 ^ k) := (Nat.even_pow.2 ⟨even_two, by omega⟩)
    have : n = 2 ^ k + (n - 2 ^ k) := by omega
    rw [this]; exact h2.add_odd h1
  classical
  set N := max x₀ 2
  have hCpos : 0 < C := by
    have h1 := hx₀ N (le_max_left _ _)
    have h2 := hC N (le_max_right _ _)
    have hN : (2 : ℝ) ≤ N := by exact_mod_cast le_max_right x₀ 2
    have hs : (∑ n ∈ Finset.range (N + 1), (r n : ℝ)) ≤
        ∑ n ∈ Finset.range (N + 1), (r n : ℝ) ^ 2 := by
      apply Finset.sum_le_sum; intro n _
      rcases Nat.eq_zero_or_pos (r n) with h | h
      · simp [h]
      · have : (1 : ℝ) ≤ r n := by exact_mod_cast h
        nlinarith
    by_contra hneg; push Not at hneg
    have : C * N ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hneg (by linarith)
    have : 0 < c * N := by positivity
    simp only [hr] at hs
    linarith
  set δ : ℝ := c ^ 2 / (2 * C) with hδ
  have hδpos : 0 < δ := by positivity
  have key : ∀ x : ℕ, N ≤ x → δ ≤ (Nat.count (· ∈ S) (x + 1) : ℝ) / ((x + 1 : ℕ) : ℝ) := by
    intro x hx
    have hx0 : x₀ ≤ x := le_trans (le_max_left _ _) hx
    have hx2 : 2 ≤ x := le_trans (le_max_right _ _) hx
    have hxr : (2 : ℝ) ≤ x := by exact_mod_cast hx2
    set A := (Finset.range (x + 1)).filter (fun n => 0 < r n)
    have hsumA : ∑ n ∈ Finset.range (x + 1), (r n : ℝ) = ∑ n ∈ A, (r n : ℝ) := by
      rw [Finset.sum_filter]; apply Finset.sum_congr rfl; intro n _
      split_ifs with h
      · rfl
      · simp [Nat.eq_zero_of_not_pos h]
    have hsqA : ∑ n ∈ A, (r n : ℝ) ^ 2 ≤ ∑ n ∈ Finset.range (x + 1), (r n : ℝ) ^ 2 :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (fun _ _ _ => by positivity)
    have hcs := sq_sum_le_card_mul_sum_sq (s := A) (f := fun n => (r n : ℝ))
    have h1 : c * x ≤ ∑ n ∈ Finset.range (x + 1), (r n : ℝ) := hx₀ x hx0
    have h2 : ∑ n ∈ Finset.range (x + 1), (r n : ℝ) ^ 2 ≤ C * x := hC x hx2
    rw [hsumA] at h1
    have hAcount : (A.card : ℝ) ≤ Nat.count (· ∈ S) (x + 1) := by
      rw [Nat.count_eq_card_filter_range]
      exact_mod_cast Finset.card_le_card (fun n hn => by
        simp only [A, Finset.mem_filter] at hn ⊢
        exact ⟨hn.1, memS n hn.2⟩)
    have hA0 : (0 : ℝ) ≤ A.card := by positivity
    have hcx : 0 ≤ c * x := by positivity
    have hsq : (c * x) ^ 2 ≤ A.card * (C * x) := by
      calc (c * x) ^ 2 ≤ (∑ n ∈ A, (r n : ℝ)) ^ 2 := pow_le_pow_left₀ hcx h1 2
        _ ≤ A.card * ∑ n ∈ A, (r n : ℝ) ^ 2 := hcs
        _ ≤ A.card * (C * x) := mul_le_mul_of_nonneg_left (hsqA.trans h2) hA0
    have hxpos : (0 : ℝ) < x := by linarith
    have hAlow : c ^ 2 * x ≤ A.card * C := by
      have : (c ^ 2 * x) * x ≤ (A.card * C) * x := by nlinarith
      exact le_of_mul_le_mul_right this hxpos
    rw [le_div_iff₀ (by positivity), hδ]
    push_cast
    rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    nlinarith
  have hev : ∀ᶠ n : ℕ in Filter.atTop,
      ((δ : ℝ) : EReal) ≤ (((Nat.count (· ∈ S) n : ℝ) : EReal) / ((n : ℝ) : EReal)) := by
    refine Filter.eventually_atTop.2 ⟨N + 1, fun n hn => ?_⟩
    obtain ⟨x, rfl⟩ : ∃ x, n = x + 1 := ⟨n - 1, by omega⟩
    rw [← EReal.coe_div]
    exact EReal.coe_le_coe_iff.2 (key x (by omega))
  calc (0 : EReal) < (δ : EReal) := EReal.coe_pos.2 hδpos
    _ ≤ _ := by convert Filter.le_liminf_of_le (by isBoundedDefault) hev

end OMA.R_Erdos16_erdos_16_variant_romanoff_R1
