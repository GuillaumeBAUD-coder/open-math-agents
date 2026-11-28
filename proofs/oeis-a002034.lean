import OMAStatements.S_oeis_a002034
import Mathlib

/-!
# OEIS A002034: Granvik's trigonometric formula for the Kempner function

Credit: @sntntHb (agent: Claude Code, model claude-opus-5-5)

Sketch. Let `μ = exp(2πi/n)`, a primitive `n`-th root of unity, and `ζ = μ^(m!)`.
Then `cos(-2π k m!/n) = Re(ζ^k)`, so `∑_{k=1}^n cos(-2π k m!/n)` is the real part of
`∑_{k=1}^n ζ^k`, which is `n` if `ζ = 1` (i.e. `n ∣ m!`) and `0` otherwise
(geometric sum, `ζ^n = 1`). Hence the double sum divided by `n` counts the
`m ∈ [1, n]` with `n ∣ m!`. Since `n ∣ n!` and divisibility of `m!` is monotone in `m`,
these `m` are exactly `[a(n), n]`, so the count is `n + 1 - a(n)` and the formula follows.
No computer search.
-/

open OMA.S_oeis_a002034 Complex

namespace OMA.P_oeis_a002034

lemma term (n k j : ℕ) :
    Real.cos (-2 * Real.pi * k / n * j) =
      (((Complex.exp (2 * Real.pi * I / n)) ^ j) ^ k).re := by
  rw [← pow_mul, ← Complex.exp_nat_mul]
  have h : ((j * k : ℕ) : ℂ) * (2 * Real.pi * I / n) =
      ((2 * Real.pi * k / n * j : ℝ) : ℂ) * I := by
    push_cast; ring
  rw [h, Complex.exp_ofReal_mul_I_re, ← Real.cos_neg]
  congr 1; ring

lemma inner_sum (n j : ℕ) (hn : 1 ≤ n) :
    ∑ k ∈ Finset.Icc 1 n, Real.cos (-2 * Real.pi * k / n * j) =
      if n ∣ j then (n : ℝ) else 0 := by
  have hμ : IsPrimitiveRoot (Complex.exp (2 * Real.pi * I / n)) n :=
    Complex.isPrimitiveRoot_exp n (by omega)
  simp_rw [term n _ j]
  rw [← Complex.re_sum]
  set ζ := (Complex.exp (2 * Real.pi * I / n)) ^ j with hζ
  have hshift : ∑ k ∈ Finset.Icc 1 n, ζ ^ k = ζ * ∑ k ∈ Finset.range n, ζ ^ k := by
    rw [Finset.mul_sum]
    have : Finset.Icc 1 n = Finset.image (fun i => i + 1) (Finset.range n) := by
      ext x; simp only [Finset.mem_Icc, Finset.mem_image, Finset.mem_range]
      constructor
      · intro hx; exact ⟨x - 1, by omega, by omega⟩
      · rintro ⟨i, hi, rfl⟩; omega
    rw [this, Finset.sum_image (by intro a _ b _ h; simp only at h; omega)]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [pow_succ']
  by_cases hd : n ∣ j
  · rw [if_pos hd]
    have h1 : ζ = 1 := (hμ.pow_eq_one_iff_dvd j).mpr hd
    rw [h1]; simp
  · rw [if_neg hd]
    have h1 : ζ ≠ 1 := fun h => hd ((hμ.pow_eq_one_iff_dvd j).mp h)
    have hn1 : ζ ^ n = 1 := by
      rw [hζ, ← pow_mul, mul_comm j n, pow_mul, hμ.pow_eq_one, one_pow]
    have hs : ∑ k ∈ Finset.range n, ζ ^ k = 0 := by
      have h2 := geom_sum_mul ζ n
      rw [hn1, sub_self] at h2
      exact (mul_eq_zero.mp h2).resolve_right (sub_ne_zero.mpr h1)
    rw [hshift, hs, mul_zero]; simp

lemma count (n : ℕ) (hn : 1 ≤ n) :
    (Finset.Icc 1 n).filter (fun m => n ∣ m.factorial) = Finset.Icc (a n) n := by
  have hne : n ∈ {m : ℕ | 0 < m ∧ n ∣ m.factorial} := ⟨by omega, Nat.dvd_factorial (by omega) le_rfl⟩
  have hmem : a n ∈ {m : ℕ | 0 < m ∧ n ∣ m.factorial} := Nat.sInf_mem ⟨n, hne⟩
  have hle : a n ≤ n := Nat.sInf_le hne
  ext m
  simp only [Finset.mem_filter, Finset.mem_Icc]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩
    exact ⟨Nat.sInf_le ⟨by omega, h3⟩, h2⟩
  · rintro ⟨h1, h2⟩
    refine ⟨⟨by have := hmem.1; omega, h2⟩, ?_⟩
    exact hmem.2.trans (Nat.factorial_dvd_factorial h1)

theorem main_proof : ∀ n : ℕ, 1 ≤ n →
      (a n : ℝ) = 1 + n - ∑ k ∈ Finset.Icc 1 n, ∑ m ∈ Finset.Icc 1 n,
        Real.cos (-2 * Real.pi * k / n * (m.factorial : ℝ)) / n := by
  intro n hn
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  rw [Finset.sum_comm]
  have hrow : ∀ m ∈ Finset.Icc 1 n,
      ∑ k ∈ Finset.Icc 1 n, Real.cos (-2 * Real.pi * k / n * (m.factorial : ℝ)) / n =
        if n ∣ m.factorial then 1 else 0 := by
    intro m _
    rw [← Finset.sum_div]
    have := inner_sum n m.factorial hn
    push_cast at this
    rw [this]
    split_ifs <;> simp [hnR]
  rw [Finset.sum_congr rfl hrow, Finset.sum_boole, count n hn, Nat.card_Icc]
  have hle : a n ≤ n := Nat.sInf_le ⟨by omega, Nat.dvd_factorial (by omega) le_rfl⟩
  rw [Nat.cast_sub (by omega)]
  push_cast; ring

end OMA.P_oeis_a002034

theorem OMA.solution : type_of% @OMA.S_oeis_a002034.main := OMA.P_oeis_a002034.main_proof
