import OMAReductions.R_Erdos683_erdos_683_variant_erdos_log_R1

-- Step Erdos683.erdos_683.variant.erdos_log.R1.H2: hypothesis H2 of reduction Erdos683.erdos_683.variant.erdos_log.R1

/-!
Erdős's argument. Every prime power dividing `choose n k` is at most `n`, so
`choose n k ≤ n ^ π(P)` with `P` the largest prime factor. Together with
`n ^ k ≤ k ^ k * choose n k` and `k ^ 3 < n ^ 2` this gives `k < 3 π(P)`. If `P` were below
`y = k log k / 20`, Chebyshev's bound `π(y) ≤ log 4 * y / log √y + √y ≤ 0.24 k` would
contradict this.
-/

namespace OMA

theorem pow_le_choose_mul : ∀ k n : ℕ, k ≤ n → n ^ k ≤ k ^ k * n.choose k := by
  intro k
  induction k with
  | zero => intro n _; simp
  | succ k ih =>
    intro n hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    have hkm : k ≤ m := by omega
    have ih1 := ih m hkm
    have hs : (m + 1) * m.choose k = (m + 1).choose (k + 1) * (k + 1) :=
      Nat.add_one_mul_choose_eq m k
    rcases Nat.eq_zero_or_pos k with rfl | hkpos
    · simp
    have h1 : ((m + 1) * k) ^ k ≤ ((k + 1) * m) ^ k := Nat.pow_le_pow_left (by nlinarith) k
    have hfin : k ^ k * (m + 1) ^ (k + 1) ≤ k ^ k * ((k + 1) ^ (k + 1) * (m + 1).choose (k + 1)) :=
      calc k ^ k * (m + 1) ^ (k + 1) = (m + 1) * ((m + 1) * k) ^ k := by
            rw [mul_pow, pow_succ]
            ring
        _ ≤ (m + 1) * ((k + 1) * m) ^ k := Nat.mul_le_mul_left _ h1
        _ = (m + 1) * (k + 1) ^ k * m ^ k := by
            rw [mul_pow]
            ring
        _ ≤ (m + 1) * (k + 1) ^ k * (k ^ k * m.choose k) := Nat.mul_le_mul_left _ ih1
        _ = k ^ k * ((k + 1) ^ k * ((m + 1) * m.choose k)) := by ring
        _ = k ^ k * ((k + 1) ^ k * ((m + 1).choose (k + 1) * (k + 1))) := by rw [hs]
        _ = k ^ k * ((k + 1) ^ (k + 1) * (m + 1).choose (k + 1)) := by ring
    exact Nat.le_of_mul_le_mul_left hfin (pow_pos hkpos k)

theorem choose_le_pow_pi (n k : ℕ) (hkn : k ≤ n) (hn : 0 < n) :
    n.choose k ≤ n ^ Nat.primeCounting ((n.choose k).primeFactors.sup id) := by
  have hC0 : n.choose k ≠ 0 := (Nat.choose_pos hkn).ne'
  have hprod : (n.choose k).factorization.prod (fun p e => p ^ e) = n.choose k :=
    Nat.prod_factorization_pow_eq_self hC0
  have h1 : n.choose k ≤ n ^ (n.choose k).primeFactors.card :=
    calc n.choose k
        = ∏ p ∈ (n.choose k).primeFactors, p ^ (n.choose k).factorization p := by
          rw [← Nat.support_factorization]
          exact hprod.symm
      _ ≤ n ^ (n.choose k).primeFactors.card :=
          Finset.prod_le_pow_card _ _ _ (fun p _ => Nat.pow_factorization_choose_le hn)
  have hsub : (n.choose k).primeFactors ⊆
      (Finset.range ((n.choose k).primeFactors.sup id + 1)).filter Nat.Prime := by
    intro p hp
    have hle : p ≤ (n.choose k).primeFactors.sup id := Finset.le_sup (f := id) hp
    exact Finset.mem_filter.2 ⟨Finset.mem_range.2 (by omega), (Nat.mem_primeFactors.1 hp).1⟩
  have hcard : ((Finset.range ((n.choose k).primeFactors.sup id + 1)).filter Nat.Prime).card =
      Nat.primeCounting ((n.choose k).primeFactors.sup id) := by
    rw [Nat.primeCounting, Nat.primeCounting', Nat.count_eq_card_filter_range]
  have h2 : (n.choose k).primeFactors.card ≤
      Nat.primeCounting ((n.choose k).primeFactors.sup id) := by
    rw [← hcard]
    exact Finset.card_le_card hsub
  exact h1.trans (Nat.pow_le_pow_right hn h2)

end OMA

theorem OMA.solution : OMA.R_Erdos683_erdos_683_variant_erdos_log_R1.H2 := by
  unfold OMA.R_Erdos683_erdos_683_variant_erdos_log_R1.H2
  intro n k hk hkn2 hk3
  have hkpos : (0 : ℝ) < k := lt_of_lt_of_le (Real.exp_pos 20) hk
  have hk0 : k ≠ 0 := by
    rintro rfl
    simp at hkpos
  have hkn : k ≤ n := by omega
  have hn2 : 2 ≤ n := by omega
  have hPdef : Erdos683.P n k = (n.choose k).primeFactors.sup id := rfl
  obtain ⟨pc, hpc⟩ : ∃ pc, pc = Nat.primeCounting (Erdos683.P n k) := ⟨_, rfl⟩
  -- the combinatorial core: `k < 3 π(P)`
  have hkey : k < 3 * pc := by
    have hA : n ^ k ≤ k ^ k * n ^ pc := by
      have h1 := OMA.pow_le_choose_mul k n hkn
      have h2 := OMA.choose_le_pow_pi n k hkn (by omega)
      rw [← hPdef, ← hpc] at h2
      exact h1.trans (Nat.mul_le_mul_left _ h2)
    have hlt : n ^ (3 * k) < n ^ (2 * k + 3 * pc) :=
      calc n ^ (3 * k) = (n ^ k) ^ 3 := by ring
        _ ≤ (k ^ k * n ^ pc) ^ 3 := Nat.pow_le_pow_left hA 3
        _ = (k ^ 3) ^ k * n ^ (3 * pc) := by ring
        _ < (n ^ 2) ^ k * n ^ (3 * pc) :=
            mul_lt_mul_of_pos_right (Nat.pow_lt_pow_left hk3 hk0) (pow_pos (by omega) _)
        _ = n ^ (2 * k + 3 * pc) := by ring
    have := (Nat.pow_lt_pow_iff_right (by omega : 1 < n)).1 hlt
    omega
  by_contra hcon
  rw [not_le] at hcon
  obtain ⟨l, hl⟩ : ∃ l, l = Real.log (k : ℝ) := ⟨_, rfl⟩
  rw [← hl] at hcon
  have hl20 : 20 ≤ l := by
    rw [hl]
    exact (Real.le_log_iff_exp_le hkpos).2 hk
  have hkexp : (k : ℝ) = Real.exp (l / 2) * Real.exp (l / 2) := by
    rw [← Real.exp_add, add_halves, hl, Real.exp_log hkpos]
  have he : l / 2 + 1 ≤ Real.exp (l / 2) := Real.add_one_le_exp _
  have hsq : (l / 2 + 1) * (l / 2 + 1) ≤ Real.exp (l / 2) * Real.exp (l / 2) :=
    mul_le_mul he he (by linarith) (Real.exp_pos _).le
  have hlk : l ≤ (k : ℝ) / 5 := by nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ l - 20) (by linarith : (0 : ℝ) ≤ l)]
  obtain ⟨y, hy⟩ : ∃ y, y = (k : ℝ) * l / 20 := ⟨_, rfl⟩
  rw [← hy] at hcon
  have hyk : (k : ℝ) ≤ y := by
    have := mul_le_mul_of_nonneg_left hl20 hkpos.le
    rw [hy]
    linarith
  have hk1 : (1 : ℝ) < k := by
    have := Real.add_one_le_exp (20 : ℝ)
    linarith
  have hy1 : 1 < y := by linarith
  have hpi := Chebyshev.pi_le_log4_mul_div hy1
  have hPfloor : Erdos683.P n k ≤ ⌊y⌋₊ := Nat.le_floor hcon.le
  have hmono : pc ≤ Nat.primeCounting ⌊y⌋₊ := by
    rw [hpc]
    exact Nat.monotone_primeCounting hPfloor
  have hlogsqrt : l / 2 ≤ Real.log (Real.sqrt y) := by
    rw [Real.log_sqrt (by linarith)]
    have := Real.log_le_log hkpos hyk
    rw [← hl] at this
    linarith
  have hlog4 : Real.log 4 ≤ 1.4 := by
    have h4 : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
      norm_num
    have := Real.log_two_lt_d9
    rw [h4]
    linarith
  have ht1 : Real.log 4 * y / Real.log (Real.sqrt y) ≤ 0.14 * (k : ℝ) := by
    rw [div_le_iff₀ (by linarith : 0 < Real.log (Real.sqrt y))]
    have a1 : Real.log 4 * y ≤ 1.4 * y := mul_le_mul_of_nonneg_right hlog4 (by linarith)
    have a2 : 0.14 * (k : ℝ) * (l / 2) ≤ 0.14 * (k : ℝ) * Real.log (Real.sqrt y) :=
      mul_le_mul_of_nonneg_left hlogsqrt (by positivity)
    have a3 : (1.4 : ℝ) * y = 0.14 * (k : ℝ) * (l / 2) := by
      rw [hy]
      ring
    linarith
  have ht2 : Real.sqrt y ≤ (k : ℝ) / 10 := by
    rw [Real.sqrt_le_iff]
    refine ⟨by positivity, ?_⟩
    have := mul_le_mul_of_nonneg_left hlk hkpos.le
    rw [hy]
    nlinarith
  have hcast1 : (k : ℝ) < 3 * (pc : ℝ) := by exact_mod_cast hkey
  have hcast2 : (pc : ℝ) ≤ (Nat.primeCounting ⌊y⌋₊ : ℝ) := by exact_mod_cast hmono
  linarith
