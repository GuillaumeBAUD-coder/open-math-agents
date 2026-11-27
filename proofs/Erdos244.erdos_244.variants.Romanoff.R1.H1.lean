import OMAReductions.R_Erdos244_erdos_244_variants_Romanoff_R1
import Mathlib.NumberTheory.Chebyshev
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

namespace OMA.RomanoffFirstMoment

lemma prime_lower : ∃ Y : ℕ, 2 ≤ Y ∧ ∀ y : ℕ, Y ≤ y →
    Real.log 2 / 2 * y ≤ (Nat.primeCounting y : ℝ)*Real.log y := by
  have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hb := (Real.isLittleO_log_id_atTop.bound (show 0 < Real.log 2/4 by positivity))
  have he : ∀ᶠ y : ℕ in Filter.atTop,
      Real.log 2 / 2 * y ≤ (Nat.primeCounting y : ℝ)*Real.log y := by
    filter_upwards [tendsto_natCast_atTop_atTop.eventually hb,
      Filter.eventually_ge_atTop (4 : ℕ)] with y hy h4
    have hy0 : (0 : ℝ) < y := by exact_mod_cast (by omega : 0 < y)
    have hlog : 0 < Real.log (y : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < y))
    have h4r : (4 : ℝ) ≤ y := by exact_mod_cast h4
    have hl : Real.log (y : ℝ) ≤ Real.log 2/4*(y : ℝ) := by
      simpa only [id_eq, Real.norm_eq_abs, abs_of_pos hlog, abs_of_pos hy0] using hy
    have hladd : Real.log ((y : ℝ)+1) ≤ Real.log 2+Real.log y := by
      calc
        _ ≤ Real.log (2*(y : ℝ)) := Real.log_le_log (by positivity) (by linarith)
        _ = _ := Real.log_mul (by norm_num) hy0.ne'
    have hc := (div_le_iff₀ hlog).mp (Chebyshev.pi_ge y)
    have hscale := mul_le_mul_of_nonneg_right h4r h2.le
    linarith
  obtain ⟨Y, hY⟩ := Filter.eventually_atTop.mp he
  exact ⟨max Y 2, le_max_right _ _, fun y hy => hY y (by omega)⟩

end OMA.RomanoffFirstMoment

-- Step Erdos244.erdos_244.variants.Romanoff.R1.H1: hypothesis H1 of reduction Erdos244.erdos_244.variants.Romanoff.R1
-- Credit: @DeepDuke
-- H1 := ∀ C : ℕ, 1 < C → ∃ c : ℝ, 0 < c ∧ ∃ x₀ : ℕ, ∀ x : ℕ, x₀ ≤ x →     c * x ≤ (((Finset.range x ×ˢ Finset.range x).filter       (fun q : ℕ × ℕ => q.1.Prime ∧ q.1 + C ^ q.2 < x)).card : ℝ)

theorem OMA.solution : OMA.R_Erdos244_erdos_244_variants_Romanoff_R1.H1 := by
  intro C hC
  have hCr : (1 : ℝ) < C := by exact_mod_cast hC
  have hC0 : (0 : ℝ) < C := by positivity
  have hlogC : 0 < Real.log C := Real.log_pos hCr
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  let c : ℝ := Real.log 2 / (4*(C : ℝ)^2*Real.log C)
  have hc : 0 < c := by dsimp [c]; positivity
  obtain ⟨Y, hY2, hY⟩ := OMA.RomanoffFirstMoment.prime_lower
  refine ⟨c, hc, C^(Y+2), ?_⟩
  intro x hx
  have hx0 : 0 < x := lt_of_lt_of_le (by positivity) hx
  have hlog : Y+2 ≤ Nat.log C x := Nat.le_log_of_pow_le hC hx
  let t := Nat.log C x-1
  let y := C^t
  have ht : 1 ≤ t := by dsimp [t]; omega
  have hty : Y ≤ y := by
    have hT : Y ≤ t := by dsimp [t]; omega
    have htp : t < C^t := Nat.lt_pow_self hC
    omega
  have hxy : C*y ≤ x := by
    have hh := Nat.pow_log_le_self C hx0.ne'
    have he : Nat.log C x = t+1 := by dsimp [t]; omega
    simpa only [he, y, pow_succ', Nat.mul_comm] using hh
  have hypos : 0 < y := by dsimp [y]; positivity
  have hyx : y < x := by nlinarith
  have hxupper : x < C^2*y := by
    have hh := Nat.lt_pow_succ_log_self hC x
    have he : Nat.log C x+1 = 2+t := by dsimp [t]; omega
    simpa only [Nat.succ_eq_add_one, he, pow_add, y] using hh
  let B := Nat.primesLE y ×ˢ Finset.range t
  have hsub : B ⊆ (Finset.range x ×ˢ Finset.range x).filter
      (fun q : ℕ × ℕ => q.1.Prime ∧ q.1+C^q.2 < x) := by
    rintro ⟨p,k⟩ hpk
    obtain ⟨hp,hk⟩ := Finset.mem_product.mp hpk
    obtain ⟨hpy,hprime⟩ := Nat.mem_primesLE.mp hp
    have hkt := Finset.mem_range.mp hk
    have hpow : C^k < y := Nat.pow_lt_pow_right hC hkt
    have hkpow : k < C^k := Nat.lt_pow_self hC
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_product.mpr ⟨Finset.mem_range.mpr (by omega),
      Finset.mem_range.mpr (by omega)⟩, hprime, ?_⟩
    nlinarith
  have hcard := Finset.card_le_card hsub
  have hcardR : (Nat.primeCounting y : ℝ)*t ≤
      (((Finset.range x ×ˢ Finset.range x).filter
        (fun q : ℕ × ℕ => q.1.Prime ∧ q.1+C^q.2 < x)).card : ℝ) := by
    rw [Finset.card_product, Nat.primesLE_card_eq_primeCounting, Finset.card_range] at hcard
    exact_mod_cast hcard
  apply le_trans ?_ hcardR
  have hbase := hY y hty
  have hlogy : Real.log (y : ℝ) = (t : ℝ)*Real.log C := by
    simp only [y, Nat.cast_pow, Real.log_pow]
  rw [hlogy] at hbase
  have hxR : (x : ℝ) ≤ (C : ℝ)^2*y := by exact_mod_cast hxupper.le
  have hcx := mul_le_mul_of_nonneg_left hxR hc.le
  have hcancel : Real.log C*c*(C : ℝ)^2 = Real.log 2/4 := by
    dsimp [c]
    field_simp
  apply (mul_le_mul_iff_right₀ hlogC).mp
  have hh := mul_le_mul_of_nonneg_left hcx hlogC.le
  have he : Real.log C*(c*((C : ℝ)^2*(y : ℝ))) = Real.log 2/4*y := by
    calc
      _ = (Real.log C*c*(C : ℝ)^2)*y := by ring
      _ = _ := by rw [hcancel]
  rw [he] at hh
  nlinarith only [hh, hbase, mul_nonneg hlog2.le (show 0 ≤ (y : ℝ) by positivity)]

