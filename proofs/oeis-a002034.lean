import OMAStatements.S_oeis_a002034
import Mathlib

open OMA.S_oeis_a002034

namespace P2034

theorem geom_Icc (r : ℂ) (n : ℕ) :
    ∑ k ∈ Finset.Icc 1 n, r ^ k = r * ∑ k ∈ Finset.range n, r ^ k := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_Icc_succ_top (by omega), ih, Finset.sum_range_succ]
    ring

theorem cos_sum (n : ℕ) (hn : 0 < n) (j : ℕ) :
    ∑ k ∈ Finset.Icc 1 n, Real.cos (-2 * Real.pi * k / n * (j : ℝ)) =
      if n ∣ j then (n : ℝ) else 0 := by
  have hn0 : n ≠ 0 := by omega
  set ζ : ℂ := Complex.exp (2 * Real.pi * Complex.I / n) with hζ
  have hprim : IsPrimitiveRoot ζ n := Complex.isPrimitiveRoot_exp n hn0
  have hterm : ∀ k : ℕ, Real.cos (-2 * Real.pi * k / n * (j : ℝ)) = ((ζ ^ j) ^ k).re := by
    intro k
    rw [← pow_mul, hζ, ← Complex.exp_nat_mul]
    have : ((j * k : ℕ) : ℂ) * (2 * Real.pi * Complex.I / n) =
        ((2 * Real.pi * k / n * j : ℝ) : ℂ) * Complex.I := by
      push_cast
      ring
    rw [this, Complex.exp_ofReal_mul_I_re]
    rw [show -2 * Real.pi * k / n * (j : ℝ) = -(2 * Real.pi * k / n * j) by ring, Real.cos_neg]
  simp_rw [hterm]
  rw [← Complex.re_sum, geom_Icc]
  split_ifs with h
  · have h1 : ζ ^ j = 1 := (hprim.pow_eq_one_iff_dvd j).mpr h
    simp [h1]
  · have h1 : ζ ^ j ≠ 1 := fun h' => h ((hprim.pow_eq_one_iff_dvd j).mp h')
    have h2 : (ζ ^ j) ^ n = 1 := by
      rw [← pow_mul, mul_comm, pow_mul, hprim.pow_eq_one, one_pow]
    rw [geom_sum_eq h1, h2]
    simp

theorem filter_eq (n : ℕ) (hn : 1 ≤ n) :
    (Finset.Icc 1 n).filter (fun m => n ∣ m.factorial) = Finset.Icc (kempner n) n := by
  have hne : n ∈ {m : ℕ | 0 < m ∧ n ∣ m.factorial} := ⟨by omega, Nat.dvd_factorial hn le_rfl⟩
  have hmem := Nat.sInf_mem ⟨n, hne⟩
  ext m
  simp only [Finset.mem_filter, Finset.mem_Icc]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩
    exact ⟨Nat.sInf_le ⟨by omega, h3⟩, h2⟩
  · rintro ⟨h1, h2⟩
    have ha : 0 < kempner n := hmem.1
    refine ⟨⟨by omega, h2⟩, ?_⟩
    exact dvd_trans hmem.2 (Nat.factorial_dvd_factorial h1)

theorem solve : ∀ n : ℕ, 1 ≤ n →
    (kempner n : ℝ) = 1 + n - ∑ k ∈ Finset.Icc 1 n, ∑ m ∈ Finset.Icc 1 n,
      Real.cos (-2 * Real.pi * k / n * (m.factorial : ℝ)) / n := by
  intro n hn
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  rw [Finset.sum_comm]
  have hinner : ∀ m ∈ Finset.Icc 1 n, (∑ k ∈ Finset.Icc 1 n,
      Real.cos (-2 * Real.pi * k / n * (m.factorial : ℝ)) / n) =
      if n ∣ m.factorial then (1 : ℝ) else 0 := by
    intro m _
    rw [← Finset.sum_div, cos_sum n (by omega) m.factorial]
    split_ifs
    · field_simp
    · simp
  rw [Finset.sum_congr rfl hinner, ← Finset.sum_filter, filter_eq n hn]
  have hle : kempner n ≤ n := Nat.sInf_le ⟨by omega, Nat.dvd_factorial hn le_rfl⟩
  simp only [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul, mul_one]
  rw [Nat.cast_sub (by omega)]
  push_cast
  ring

end P2034

theorem OMA.solution : type_of% @OMA.S_oeis_a002034.main := P2034.solve
