import OMAReductions.R_oeis_a284760_R1

/-!
# Proof of `oeis-a284760.R1.H1`

Proves that whenever `n % 4 = 2`, the power sum `∑ i ∈ Finset.Ico 1 n, i ^ (n - 2)` is not
divisible by `n ^ 4`.

For `n = 2`, the sum is `1` and `1 % 16 ≠ 0`. For `n = 4 * k + 2` with `k ≥ 1`, `n - 2 ≥ 4 > 0`,
so `i ^ (n - 2) ≡ i (mod 2)` for every `i`. Since `∑_{i=1}^{n-1} i = (2*k + 1) * (4*k + 1)` is
odd while `n ^ 4` is even, `n ^ 4` cannot divide the sum.
-/

theorem OMA.solution : OMA.R_oeis_a284760_R1.H1 := by
  intro n hn
  by_cases hn2 : n = 2
  · subst hn2; decide
  · have hpos : 0 < n - 2 := by omega
    have hsum_odd : Odd (∑ i ∈ Finset.Ico 1 n, i ^ (n - 2)) := by
      have hcast : ((∑ i ∈ Finset.Ico 1 n, i ^ (n - 2) : ℕ) : ZMod 2) = 1 := by
        rw [Nat.cast_sum]
        have hterm : ∀ i ∈ Finset.Ico 1 n, ((i ^ (n - 2) : ℕ) : ZMod 2) = (i : ZMod 2) := by
          intro i _
          rw [Nat.cast_pow]
          have h2 : ∀ z : ZMod 2, ∀ e : ℕ, 0 < e → z ^ e = z := by
            intro z e he
            induction e with
            | zero => omega
            | succ e ih =>
              rcases Nat.eq_zero_or_pos e with rfl | he'
              · simp
              · rw [pow_succ, ih he']
                fin_cases z <;> rfl
          exact h2 (i : ZMod 2) (n - 2) hpos
        rw [Finset.sum_congr rfl hterm]
        have hnat : ∑ i ∈ Finset.Ico 1 n, i = n * (n - 1) / 2 := by
          have h1 := Finset.sum_range_id n
          have h2 : ∑ i ∈ Finset.Ico 1 n, i = ∑ i ∈ Finset.range n, i := by
            have h0 : Finset.range n = insert 0 (Finset.Ico 1 n) := by
              ext x; simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Ico]; omega
            rw [h0, Finset.sum_insert (by simp), zero_add]
          rw [h2, h1]
        rw [← Nat.cast_sum, hnat]
        have hodd : (n * (n - 1) / 2) % 2 = 1 := by
          obtain ⟨k, rfl⟩ : ∃ k, n = 4 * k + 2 := ⟨n / 4, by omega⟩
          have heq : (4 * k + 2) * (4 * k + 2 - 1) / 2 = (2 * k + 1) * (4 * k + 1) := by
            have hsub : 4 * k + 2 - 1 = 4 * k + 1 := by omega
            have hmul : (4 * k + 2) * (4 * k + 1) = 2 * ((2 * k + 1) * (4 * k + 1)) := by ring
            rw [hsub, hmul, Nat.mul_div_right _ (by decide)]
          rw [heq, Nat.mul_mod]
          have h1 : (2 * k + 1) % 2 = 1 := by omega
          have h2 : (4 * k + 1) % 2 = 1 := by omega
          rw [h1, h2]
        rw [← ZMod.natCast_mod, hodd]
        rfl
      have hne : ((∑ i ∈ Finset.Ico 1 n, i ^ (n - 2) : ℕ) : ZMod 2) ≠ 0 := by
        rw [hcast]; decide
      have hndvd : ¬ 2 ∣ ∑ i ∈ Finset.Ico 1 n, i ^ (n - 2) := by
        intro hd
        exact hne ((ZMod.natCast_eq_zero_iff _ _).mpr hd)
      exact Nat.not_even_iff_odd.mp (fun he => hndvd (even_iff_two_dvd.mp he))
    intro hzero
    have hdvd : n ^ 4 ∣ ∑ i ∈ Finset.Ico 1 n, i ^ (n - 2) := Nat.dvd_of_mod_eq_zero hzero
    have h2n : 2 ∣ n ^ 4 := dvd_pow (Nat.dvd_of_mod_eq_zero (by omega : n % 2 = 0)) (by decide)
    have h2s : 2 ∣ ∑ i ∈ Finset.Ico 1 n, i ^ (n - 2) := h2n.trans hdvd
    exact Nat.not_even_iff_odd.mpr hsum_odd (even_iff_two_dvd.mpr h2s)
