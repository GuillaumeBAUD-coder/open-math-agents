import OMAReductions.R_Erdos244_erdos_244_variants_Romanoff_R1
import Mathlib.NumberTheory.Chebyshev

/-!
The first moment in Steven Enamakel's reduction of Romanoff's theorem.
For each prime up to y and each power of C up to y, the sum is at most 2y.
Taking y = ⌊x/3⌋ gives a rectangle of representations below x.
-/

open Finset Real

namespace OMA.Romanoff

-- The estimate and its proof are from zarnab222-dev's Erdős 1184 proof, PR 1312.
private theorem prime_count_lower (x : ℝ) (hx : 64 ≤ x) :
    x / (4 * log x) ≤ (Nat.primeCounting ⌊x⌋₊ : ℝ) := by
  have hx' : 1 < x := by linarith
  have h₂ := Real.one_sub_inv_le_log_of_pos (x := 2) (by norm_num)
  norm_num at h₂
  have h₈ := Real.log_le_sub_one_of_pos (x := 8) (by norm_num)
  have hlog := Real.log_le_sub_one_of_pos (x := (x+2)/8) (by linarith)
  rw [Real.log_div (by linarith) (by norm_num)] at hlog
  have h := Chebyshev.pi_ge' hx'
  apply le_trans _ h
  have he : x/(4*log x) = (x/4)/log x := by ring
  rw [he]
  apply div_le_div_of_nonneg_right _ (Real.log_pos hx').le
  nlinarith [mul_nonneg (sub_nonneg.mpr hx'.le) (sub_nonneg.mpr h₂)]

private theorem count_rectangle (C y x : ℕ) (hC : 1 < C) (hy : 0 < y) (hyx : 2 * y < x) :
    Nat.primeCounting y * (Nat.log C y + 1) ≤
      (((range x) ×ˢ (range x)).filter (fun q : ℕ × ℕ => q.1.Prime ∧ q.1 + C ^ q.2 < x)).card := by
  let P := (range (y + 1)).filter Nat.Prime
  have hcard : P.card = Nat.primeCounting y := by
    simp [P, Nat.primeCounting, Nat.primeCounting', Nat.count_eq_card_filter_range]
  rw [← hcard, ← card_range (Nat.log C y + 1), ← card_product]
  apply card_le_card
  rintro ⟨p, k⟩ h
  obtain ⟨hp, hk⟩ := mem_product.mp h
  obtain ⟨hp', hprime⟩ := mem_filter.mp hp
  have hpy := mem_range.mp hp'
  have hky : k ≤ Nat.log C y := Nat.le_of_lt_succ (mem_range.mp hk)
  have hpower : C ^ k ≤ y :=
    (Nat.pow_le_pow_right (by omega : 0 < C) hky).trans (Nat.pow_log_le_self C hy.ne')
  have hkp := Nat.lt_pow_self hC (n := k)
  exact mem_filter.mpr ⟨mem_product.mpr ⟨mem_range.mpr (by omega), mem_range.mpr (by omega)⟩,
    hprime, by change p + C ^ k < x; omega⟩

end OMA.Romanoff

theorem OMA.solution : OMA.R_Erdos244_erdos_244_variants_Romanoff_R1.H1 := by
  intro C hC
  have hCr : (1 : ℝ) < C := by exact_mod_cast hC
  have hlogC := Real.log_pos hCr
  refine ⟨1 / (16 * Real.log C), by positivity, 192, ?_⟩
  intro x hx
  let y := x / 3
  have hy : 64 ≤ y := by dsimp [y]; omega
  have hyx : 2 * y < x := by dsimp [y]; omega
  have hxy : x ≤ 4 * y := by dsimp [y]; omega
  have hyr : (64 : ℝ) ≤ y := by exact_mod_cast hy
  have hlogy : 0 < Real.log y := Real.log_pos (by linarith)
  have hpi := OMA.Romanoff.prime_count_lower (y : ℝ) hyr
  rw [Nat.floor_natCast] at hpi
  have hscale := (div_le_iff₀ (by positivity : 0 < 4 * Real.log y)).mp hpi
  have hexp : (y : ℝ) ≤ (C : ℝ) ^ (Nat.log C y + 1) := by
    exact_mod_cast (Nat.lt_pow_succ_log_self hC y).le
  have hlogs := Real.log_le_log (by linarith : (0 : ℝ) < y) hexp
  rw [Real.log_pow] at hlogs
  have hrect := OMA.Romanoff.count_rectangle C y x hC (by omega) hyx
  have hxyR : (x : ℝ) ≤ 4 * y := by exact_mod_cast hxy
  calc
    1 / (16 * Real.log C) * x ≤ (Nat.primeCounting y : ℝ) * (Nat.log C y + 1 : ℕ) := by
      rw [one_div_mul_eq_div, div_le_iff₀ (by positivity)]
      nlinarith [mul_le_mul_of_nonneg_left hlogs (Nat.cast_nonneg (Nat.primeCounting y) : (0:ℝ) ≤ _)]
    _ ≤ _ := by exact_mod_cast hrect
