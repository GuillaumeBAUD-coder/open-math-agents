import FormalConjectures.ErdosProblems.«413»

-- Credit: @kumagi
-- Uses note #65365

/-!
The negative-shift version of Lau's Proposition 5.1 isolates the
finite-window probability estimates. We use nonnegative weights on
the interval instead of a random variable, and replace the summable
bound `6 / (π² k²)` by the slightly larger `1 / k²`.
Theorem 1.3 uses the same sieve with the shifts reversed.
Source: https://arxiv.org/html/2604.15042v3
-/

namespace OMA.R_Erdos413_erdos_413_parts_ii_R1

open ArithmeticFunction Erdos413 Filter
open scoped omega Omega BigOperators

/-- The finite-window sieve estimate for backward shifts. -/
def H1 : Prop :=
  ∃ C > (0 : ℝ), ∀ᶠ X : ℕ in atTop, ∃ w : ℕ → ℝ,
    (∀ n, 0 ≤ w n) ∧ (∑ n ∈ Finset.Icc X (2 * X), w n) = 1 ∧
    ∀ k : ℕ, 1 < k → k ^ 100 ≤ X →
      (∑ n ∈ (Finset.Icc X (2 * X)).filter
        (fun n => C * Real.log (k : ℝ) < (Ω (n - k) : ℝ)), w n) ≤ 1 / (k : ℝ) ^ 2

/-- The elementary bound for shifts beyond the finite window. -/
def H2 : Prop :=
  ∃ D > (0 : ℝ), ∀ n k : ℕ, 1 < k → k < n → n ≤ 2 * k ^ 100 →
    (Ω (n - k) : ℝ) ≤ D * Real.log (k : ℝ)

section

/-- The backward-shift bound of Lau, arXiv:2604.15042v3, Theorem 1.3. -/
private def LauBackward : Prop :=
  ∃ C > (0 : ℝ), {n : ℕ | ∀ k : ℕ, 1 < k → k < n →
    (Ω (n - k) : ℝ) ≤ C * Real.log (k : ℝ)}.Infinite

private theorem barriers_from_lau (hLau : LauBackward) : type_of% @Erdos413.erdos_413.parts.ii := by
  obtain ⟨C, hC, h⟩ := hLau
  let S := {n : ℕ | ∀ k : ℕ, 1 < k → k < n →
    (Ω (n - k) : ℝ) ≤ C * Real.log (k : ℝ)} \ {0}
  have hS : S.Infinite := h.sdiff (Set.finite_singleton 0)
  refine ⟨C⁻¹, inv_pos.mpr hC, ?_⟩
  apply Set.infinite_of_injOn_mapsTo (f := fun n : ℕ => n - 1) ?_ ?_ hS
  · intro a ha b hb hab
    have ha' : a ≠ 0 := ha.2
    have hb' : b ≠ 0 := hb.2
    dsimp at hab
    omega
  · intro n hn
    change IsBarrier (fun m => C⁻¹ * ω m) (n - 1)
    intro m hm
    rcases Nat.eq_zero_or_pos m with rfl | hm₀
    · simp
    let k := n - m
    have hk₀ : 1 < k := by dsimp [k]; omega
    have hkn : k < n := by dsimp [k]; omega
    have hkm : n - k = m := by dsimp [k]; omega
    have hcast : (k : ℝ) - 1 = (↑(n - 1) : ℝ) - (m : ℝ) := by
      dsimp [k]
      rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega), Nat.cast_one]
      ring
    have hprime_count : ω m ≤ Ω m := by
      rw [cardDistinctFactors_apply, cardFactors_apply]
      exact m.primeFactorsList.dedup_sublist.length_le
    have hnat : (ω m : ℝ) ≤ (Ω m : ℝ) := by exact_mod_cast hprime_count
    have hmain := hn.1 k hk₀ hkn
    rw [hkm] at hmain
    have hlog := Real.log_le_sub_one_of_pos (show (0 : ℝ) < k by exact_mod_cast (show 0 < k by omega))
    have hscaled : (ω m : ℝ) ≤ C * ((k : ℝ) - 1) :=
      (hnat.trans hmain).trans (mul_le_mul_of_nonneg_left hlog hC.le)
    have hscaled' := mul_le_mul_of_nonneg_left hscaled (inv_nonneg.mpr hC.le)
    rw [← mul_assoc, inv_mul_cancel₀ hC.ne', one_mul, hcast] at hscaled'
    linarith


private noncomputable def gap (j : ℕ) : ℝ := 1 / ((j : ℝ) + 1) - 1 / ((j : ℝ) + 2)

private lemma gap_nonneg (j : ℕ) : 0 ≤ gap j := by
  unfold gap
  rw [sub_nonneg]
  exact one_div_le_one_div_of_le (by positivity) (by linarith)

private lemma square_reciprocal_le_gap (j : ℕ) : 1 / ((j : ℝ) + 2) ^ 2 ≤ gap j := by
  let x : ℝ := j + 2
  have hx : 1 < x := by
    have : 0 ≤ (j : ℝ) := by positivity
    dsimp [x]
    linarith
  have hx0 : 0 < x := by linarith
  have hx1 : 0 < x - 1 := by linarith
  have he : gap j = 1 / ((x - 1) * x) := by
    have h : (j : ℝ) + 1 = x - 1 := by dsimp [x]; ring
    unfold gap
    rw [h]
    change 1 / (x - 1) - 1 / x = _
    field_simp [hx0.ne', hx1.ne']
    <;> ring
  rw [he]
  change 1 / x ^ 2 ≤ _
  exact one_div_le_one_div_of_le (by positivity) (by nlinarith)

private lemma sum_gap (X : ℕ) : (∑ j ∈ Finset.range X, gap j) =
    1 - 1 / ((X : ℝ) + 1) := by
  induction X with
  | zero => norm_num
  | succ X ih =>
    rw [Finset.sum_range_succ, ih]
    unfold gap
    push_cast
    rw [show (X : ℝ) + 1 + 1 = (X : ℝ) + 2 by ring]
    ring

private lemma exists_good {C : ℝ} {X : ℕ} {w : ℕ → ℝ}
    (hnonneg : ∀ n, 0 ≤ w n) (hnorm : (∑ n ∈ Finset.Icc X (2 * X), w n) = 1)
    (hweight : ∀ k : ℕ, 1 < k → k ^ 100 ≤ X →
      (∑ n ∈ (Finset.Icc X (2 * X)).filter
        (fun n => C * Real.log (k : ℝ) < (Ω (n - k) : ℝ)), w n) ≤ 1 / (k : ℝ) ^ 2) :
    ∃ n ∈ Finset.Icc X (2 * X), ∀ k : ℕ, 1 < k → k ^ 100 ≤ X →
      (Ω (n - k) : ℝ) ≤ C * Real.log (k : ℝ) := by
  classical
  let N := Finset.Icc X (2 * X)
  let K := (Finset.range X).filter (fun j => (j + 2) ^ 100 ≤ X)
  let bad (j n : ℕ) : Prop := C * Real.log ((j + 2 : ℕ) : ℝ) < (Ω (n - (j + 2)) : ℝ)
  by_contra! h
  have hcover : ∀ n ∈ N, w n ≤ ∑ j ∈ K, if bad j n then w n else 0 := by
    intro n hn
    obtain ⟨k, hk, hkX, hb⟩ := h n hn
    have hk_le : k ≤ X := (Nat.le_self_pow (by decide : 100 ≠ 0) k).trans hkX
    let j := k - 2
    have hjk : j + 2 = k := by dsimp [j]; omega
    have hjK : j ∈ K := by
      apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_range.mpr (by dsimp [j]; omega), by simpa [hjk] using hkX⟩
    have hjb : bad j n := by unfold bad; rw [hjk]; exact hb
    have h₀ := Finset.single_le_sum
      (f := fun i => if bad i n then w n else 0)
      (fun i _ => by split <;> simp [hnonneg]) hjK
    rwa [if_pos hjb] at h₀
  have hsum := Finset.sum_le_sum hcover
  rw [show (∑ n ∈ N, w n) = 1 from hnorm, Finset.sum_comm] at hsum
  have h₁ : (∑ j ∈ K, ∑ n ∈ N, if bad j n then w n else 0) ≤ ∑ j ∈ K, gap j := by
    apply Finset.sum_le_sum
    intro j hj
    rw [← Finset.sum_filter]
    have hjpow := (Finset.mem_filter.mp hj).2
    have hb := hweight (j + 2) (by omega) hjpow
    exact hb.trans (by push_cast; exact square_reciprocal_le_gap j)
  have h₂ : (∑ j ∈ K, gap j) ≤ ∑ j ∈ Finset.range X, gap j :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun j _ _ => gap_nonneg j)
  have h₃ : (∑ j ∈ Finset.range X, gap j) < 1 := by
    rw [sum_gap]
    have : 0 < 1 / ((X : ℝ) + 1) := by positivity
    linarith
  exact (not_lt_of_ge ((hsum.trans h₁).trans h₂)) h₃

theorem main : H1 → H2 → type_of% @Erdos413.erdos_413.parts.ii := by
  rintro ⟨C, hC, hsieve⟩ ⟨D, hD, htail⟩
  apply barriers_from_lau
  refine ⟨C + D, add_pos hC hD, ?_⟩
  apply Set.infinite_of_forall_exists_gt
  intro T
  obtain ⟨N, hN⟩ := eventually_atTop.mp hsieve
  let X := max N (T + 1)
  obtain ⟨w, hnonneg, hnorm, hweights⟩ := hN X (le_max_left _ _)
  obtain ⟨n, hn, hsmall⟩ := exists_good hnonneg hnorm hweights
  have hX := Finset.mem_Icc.mp hn
  have hXT : T < X := lt_of_lt_of_le (Nat.lt_succ_self _) (le_max_right _ _)
  refine ⟨n, ?_, hXT.trans_le hX.1⟩
  intro k hk hkn
  have hlog : 0 ≤ Real.log (k : ℝ) := Real.log_nonneg (by exact_mod_cast hk.le)
  by_cases hkX : k ^ 100 ≤ X
  · exact (hsmall k hk hkX).trans
      (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hD.le) hlog)
  · have hnK : n ≤ 2 * k ^ 100 :=
      hX.2.trans (Nat.mul_le_mul_left 2 (le_of_not_ge hkX))
    exact (htail n k hk hkn hnK).trans
      (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hC.le) hlog)

end

end OMA.R_Erdos413_erdos_413_parts_ii_R1
