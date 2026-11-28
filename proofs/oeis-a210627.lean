import OMAStatements.S_oeis_a210627
import Mathlib

open OMA.S_oeis_a210627

theorem alt_vanish (n j : ℕ) (h : j < n) :
    ∑ k ∈ Finset.range (n + 1), (-1 : ℤ) ^ (n - k) * (n.choose k : ℤ) * (k : ℤ) ^ j = 0 := by
  have := congr_fun (fwdDiff_iter_pow_eq_zero_of_lt (R := ℤ) h) 0
  rw [fwdDiff_iter_eq_sum_shift] at this
  simpa [zsmul_eq_mul] using this

theorem A_eq (n : ℕ) : (A038049 n : ℤ) =
    ∑ k ∈ Finset.range (n + 1), (n.choose k : ℤ) * (k : ℤ) ^ (n - 1) := by
  unfold A038049
  push_cast
  rw [← Finset.sum_range_reflect]
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [Finset.mem_range] at hk
  rw [show n + 1 - 1 - k = n - k by omega, Nat.choose_symm (by omega),
    show n - (n - k) = k by omega]

theorem OMA.solution : type_of% @OMA.S_oeis_a210627.main := by
  refine ⟨by decide, ?_⟩
  intro n hn
  unfold r
  rw [A_eq]
  congr 1
  set g : ℕ → ℤ := fun k => (k : ℤ) ^ (n - 3) * (n.choose k : ℤ) *
    ((-1) ^ k * (9 * (k : ℤ) ^ 2 - 32 * k + 24) + (k : ℤ) ^ 2) with hg
  have hlow : ∀ k ∈ Finset.range 4, g k = 0 := by
    intro k hk
    simp only [Finset.mem_range] at hk
    interval_cases k <;> simp [hg] <;> first | omega | norm_num
  have hIcc : Finset.Icc 4 n = Finset.Ico 4 (n + 1) := by
    ext x; simp only [Finset.mem_Icc, Finset.mem_Ico]; omega
  rw [hIcc]
  have hsplit := Finset.sum_range_add_sum_Ico g (show 4 ≤ n + 1 by omega)
  rw [Finset.sum_eq_zero hlow, zero_add] at hsplit
  rw [hsplit]
  have hsign : ∀ k ∈ Finset.range (n + 1), (-1 : ℤ) ^ k =
      (-1) ^ n * (-1) ^ (n - k) := by
    intro k hk
    rw [Finset.mem_range] at hk
    rw [← pow_add]
    have : n + (n - k) = k + 2 * (n - k) := by omega
    rw [this, pow_add, pow_mul]; norm_num
  have e1 := alt_vanish n (n - 1) (by omega)
  have e2 := alt_vanish n (n - 2) (by omega)
  have e3 := alt_vanish n (n - 3) (by omega)
  have hg' : ∀ k ∈ Finset.range (n + 1), g k =
      (-1) ^ n * (9 * ((-1 : ℤ) ^ (n - k) * (n.choose k : ℤ) * (k : ℤ) ^ (n - 1))
        - 32 * ((-1 : ℤ) ^ (n - k) * (n.choose k : ℤ) * (k : ℤ) ^ (n - 2))
        + 24 * ((-1 : ℤ) ^ (n - k) * (n.choose k : ℤ) * (k : ℤ) ^ (n - 3)))
      + (n.choose k : ℤ) * (k : ℤ) ^ (n - 1) := by
    intro k hk
    have h1 : (k : ℤ) ^ (n - 1) = (k : ℤ) ^ (n - 3) * k ^ 2 := by
      rw [← pow_add]; congr 1; omega
    have h2 : (k : ℤ) ^ (n - 2) = (k : ℤ) ^ (n - 3) * k := by
      rw [← pow_succ]; congr 1; omega
    simp only [hg]
    rw [h1, h2, hsign k hk]
    ring
  rw [Finset.sum_congr rfl hg', Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_add_distrib,
    Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum, e1, e2, e3]
  simp
