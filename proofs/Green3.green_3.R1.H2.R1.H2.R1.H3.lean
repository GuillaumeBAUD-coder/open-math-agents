import OMAReductions.R_Green3_green_3_R1_H2_R1_H2_R1

-- Step Green3.green_3.R1.H2.R1.H2.R1.H3: hypothesis H3 of reduction Green3.green_3.R1.H2.R1.H2.R1

/-!
Write `A n` for the number of elements of `T` below `n`. Multiply the hypothesis
`A (n - a) + A n + A (n + a) ≤ n` by `q ^ n` and sum over `n`. Since
`∑ n, [t < n] q ^ n = q ^ (t + 1) / (1 - q)`, the left side becomes
`∑ t ∈ T, (q ^ (t + a + 1) + q ^ (t + 1) + q ^ (t - a + 1)) / (1 - q)`, which is at least
`3 q / (1 - q) * ∑ t ∈ T, q ^ t` because `q ^ a + q ^ (-a) ≥ 2`; the right side is
`q / (1 - q) ^ 2`.
-/

namespace OMA

theorem hasSum_ind (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1) (m : ℕ) :
    HasSum (fun n : ℕ => if m < n then q ^ n else 0) (q ^ (m + 1) / (1 - q)) := by
  have h := (hasSum_geometric_of_lt_one hq0 hq1).mul_left (q ^ (m + 1))
  have hz : ∑ i ∈ Finset.range (m + 1), (fun n : ℕ => if m < n then q ^ n else 0) i = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    show (if m < i then q ^ i else 0) = 0
    rw [if_neg]
    have := Finset.mem_range.1 hi
    omega
  have key : HasSum (fun n : ℕ => (fun n : ℕ => if m < n then q ^ n else 0) (n + (m + 1)))
      (q ^ (m + 1) / (1 - q) -
        ∑ i ∈ Finset.range (m + 1), (fun n : ℕ => if m < n then q ^ n else 0) i) := by
    have e : (fun n : ℕ => (fun n : ℕ => if m < n then q ^ n else 0) (n + (m + 1))) =
        fun i : ℕ => q ^ (m + 1) * q ^ i := by
      funext n
      show (if m < n + (m + 1) then q ^ (n + (m + 1)) else 0) = q ^ (m + 1) * q ^ n
      rw [if_pos (by omega), pow_add, mul_comm]
    rw [hz, sub_zero, e, div_eq_mul_inv]
    exact h
  exact (hasSum_nat_add_iff' (m + 1)).1 key

end OMA

theorem OMA.solution : OMA.R_Green3_green_3_R1_H2_R1_H2_R1.H3 := by
  unfold OMA.R_Green3_green_3_R1_H2_R1_H2_R1.H3
  intro T a hT hA q hq0 hq1
  have h1q : 0 < 1 - q := by linarith
  have hs1 : ∀ t ∈ T, HasSum (fun n : ℕ => if t < n - a then q ^ n else 0)
      (q ^ (t + a + 1) / (1 - q)) := by
    intro t _
    have h := OMA.hasSum_ind q hq0.le hq1 (t + a)
    have e : (fun n : ℕ => if t < n - a then q ^ n else 0) =
        fun n : ℕ => if t + a < n then q ^ n else 0 := by
      funext n
      have hiff : (t < n - a) ↔ (t + a < n) := by omega
      simp only [hiff]
    rw [e]
    exact h
  have hs2 : ∀ t ∈ T, HasSum (fun n : ℕ => if t < n then q ^ n else 0)
      (q ^ (t + 1) / (1 - q)) := fun t _ => OMA.hasSum_ind q hq0.le hq1 t
  have hs3 : ∀ t ∈ T, HasSum (fun n : ℕ => if t < n + a then q ^ n else 0)
      (q ^ (t - a + 1) / (1 - q)) := by
    intro t ht
    have h := OMA.hasSum_ind q hq0.le hq1 (t - a)
    have hat := hT t ht
    have e : (fun n : ℕ => if t < n + a then q ^ n else 0) =
        fun n : ℕ => if t - a < n then q ^ n else 0 := by
      funext n
      have hiff : (t < n + a) ↔ (t - a < n) := by omega
      simp only [hiff]
    rw [e]
    exact h
  have hsum : HasSum (fun n : ℕ => ∑ t ∈ T, ((if t < n - a then q ^ n else 0) +
        (if t < n then q ^ n else 0) + (if t < n + a then q ^ n else 0)))
      (∑ t ∈ T, (q ^ (t + a + 1) / (1 - q) + q ^ (t + 1) / (1 - q) +
        q ^ (t - a + 1) / (1 - q))) :=
    hasSum_sum (fun t ht => ((hs1 t ht).add (hs2 t ht)).add (hs3 t ht))
  have hgeo : HasSum (fun n : ℕ => (n : ℝ) * q ^ n) (q / (1 - q) ^ 2) :=
    hasSum_coe_mul_geometric_of_norm_lt_one (by rw [Real.norm_of_nonneg hq0.le]; exact hq1)
  have hpt : ∀ n : ℕ, ∑ t ∈ T, ((if t < n - a then q ^ n else 0) +
        (if t < n then q ^ n else 0) + (if t < n + a then q ^ n else 0)) ≤ (n : ℝ) * q ^ n := by
    intro n
    have hn := hA n
    have hcast : (((T.filter (· < n - a)).card + (T.filter (· < n)).card +
        (T.filter (· < n + a)).card : ℕ) : ℝ) ≤ n := by exact_mod_cast hn
    have e : ∑ t ∈ T, ((if t < n - a then q ^ n else 0) +
        (if t < n then q ^ n else 0) + (if t < n + a then q ^ n else 0)) =
        (((T.filter (· < n - a)).card + (T.filter (· < n)).card +
          (T.filter (· < n + a)).card : ℕ) : ℝ) * q ^ n := by
      simp only [Finset.card_filter, Nat.cast_add, Nat.cast_sum, Nat.cast_ite, Nat.cast_one,
        Nat.cast_zero]
      rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, Finset.sum_mul]
      refine Finset.sum_congr rfl (fun t _ => ?_)
      split_ifs <;> ring
    rw [e]
    exact mul_le_mul_of_nonneg_right hcast (pow_nonneg hq0.le n)
  have hle := hasSum_le hpt hsum hgeo
  have h3 : ∑ t ∈ T, 3 * q ^ (t + 1) / (1 - q) ≤
      ∑ t ∈ T, (q ^ (t + a + 1) / (1 - q) + q ^ (t + 1) / (1 - q) +
        q ^ (t - a + 1) / (1 - q)) := by
    refine Finset.sum_le_sum (fun t ht => ?_)
    obtain ⟨s, rfl⟩ : ∃ s, t = a + s := ⟨t - a, by have := hT t ht; omega⟩
    rw [Nat.add_sub_cancel_left, ← add_div, ← add_div, div_le_div_iff₀ h1q h1q]
    apply mul_le_mul_of_nonneg_right _ h1q.le
    have key : 0 ≤ q ^ (s + 1) * (q ^ a - 1) ^ 2 := by positivity
    have e2 : q ^ (s + 1) * (q ^ a - 1) ^ 2 =
        q ^ (a + s + a + 1) - 2 * q ^ (a + s + 1) + q ^ (s + 1) := by ring
    linarith
  have h4 : 3 * q / (1 - q) * ∑ t ∈ T, q ^ t = ∑ t ∈ T, 3 * q ^ (t + 1) / (1 - q) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun t _ => ?_)
    rw [pow_succ]
    ring
  have h5 : 3 * q / (1 - q) * ∑ t ∈ T, q ^ t ≤ q / (1 - q) ^ 2 := by
    rw [h4]
    exact h3.trans hle
  generalize ∑ t ∈ T, q ^ t = S at h5 ⊢
  rw [div_mul_eq_mul_div, div_le_div_iff₀ h1q (pow_pos h1q 2)] at h5
  have hc : 0 < q * (1 - q) := mul_pos hq0 h1q
  have h6 : q * (1 - q) * (3 * ((1 - q) * S)) ≤ q * (1 - q) * 1 := by
    have e : q * (1 - q) * (3 * ((1 - q) * S)) = 3 * q * S * (1 - q) ^ 2 := by ring
    rw [e]
    linarith
  have h7 := le_of_mul_le_mul_left h6 hc
  linarith
