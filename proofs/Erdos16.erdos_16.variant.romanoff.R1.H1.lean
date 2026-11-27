import OMAReductions.R_Erdos16_erdos_16_variant_romanoff_R1
import Mathlib.NumberTheory.Chebyshev
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

namespace OMA.RomanoffOddFirstMoment

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

end OMA.RomanoffOddFirstMoment

-- Step Erdos16.erdos_16.variant.romanoff.R1.H1: hypothesis H1 of reduction Erdos16.erdos_16.variant.romanoff.R1
-- Credit: @DeepDuke
-- H1 := ∃ c : ℝ, 0 < c ∧ ∃ x₀ : ℕ, ∀ x : ℕ, x₀ ≤ x →     c * x ≤ ∑ n ∈ Finset.range (x + 1),       (((Finset.range n).filter (fun k => 1 ≤ k ∧ 2 ^ k < n ∧ (n - 2 ^ k).Prime ∧         n - 2 ^ k ≠ 2)).card : ℝ)  /-- Romanoff's second-moment bound: `∑_{n ≤ x} r(n)^2 ≤ C x`, where `r(n)` counts the representations `n = 2^k + p` with `k ≥ 1` and `p` an odd prime. -/

theorem OMA.solution : OMA.R_Erdos16_erdos_16_variant_romanoff_R1.H1 := by
  obtain ⟨Y, hY2, hY⟩ := OMA.RomanoffOddFirstMoment.prime_lower
  refine ⟨1/16, by norm_num, 2^(Y+8), ?_⟩
  intro x hx
  have hx0 : 0 < x := lt_of_lt_of_le (by positivity) hx
  have hlog : Y+8 ≤ Nat.log 2 x := Nat.le_log_of_pow_le (by decide) hx
  let t := Nat.log 2 x-1
  let y := 2^t
  have ht : 7 ≤ t := by dsimp [t]; omega
  have hty : Y ≤ y := by
    have hT : Y ≤ t := by dsimp [t]; omega
    have hp : t < 2^t := Nat.lt_two_pow_self
    omega
  have hy7 : 7 ≤ y := by
    have hp : t < 2^t := Nat.lt_two_pow_self
    omega
  have hxy : 2*y ≤ x := by
    have hh := Nat.pow_log_le_self 2 hx0.ne'
    have he : Nat.log 2 x = t+1 := by dsimp [t]; omega
    simpa only [he, y, pow_succ'] using hh
  have hxupper : x < 4*y := by
    have hh := Nat.lt_pow_succ_log_self (by decide : 1 < 2) x
    have he : Nat.log 2 x+1 = 2+t := by dsimp [t]; omega
    simpa only [Nat.succ_eq_add_one, he, pow_add, y, show (2 : ℕ)^2 = 4 by decide] using hh
  have hp4 : 4 ≤ Nat.primeCounting y := by
    exact le_trans (by decide : 4 ≤ Nat.primeCounting 7) (Nat.monotone_primeCounting hy7)
  have htwo : 2 ∈ Nat.primesLE y := Nat.mem_primesLE.mpr ⟨by omega, Nat.prime_two⟩
  let B := (Nat.primesLE y).erase 2 ×ˢ Finset.Icc 1 t
  let R (n : ℕ) := (Finset.range n).filter (fun k =>
    1 ≤ k ∧ 2^k < n ∧ (n-2^k).Prime ∧ n-2^k ≠ 2)
  let T := (Finset.range (x+1)).sigma R
  let f : ℕ × ℕ → (Σ _ : ℕ, ℕ) := fun pk => ⟨pk.1+2^pk.2, pk.2⟩
  have hmaps : ∀ z ∈ B, f z ∈ T := by
    rintro ⟨p,k⟩ hpk
    obtain ⟨hp,hk⟩ := Finset.mem_product.mp hpk
    obtain ⟨hpne,hp⟩ := Finset.mem_erase.mp hp
    obtain ⟨hpy,hprime⟩ := Nat.mem_primesLE.mp hp
    obtain ⟨hk1,hkt⟩ := Finset.mem_Icc.mp hk
    have hpow : 2^k ≤ y := Nat.pow_le_pow_right (by decide) hkt
    have hkpow : k < 2^k := Nat.lt_two_pow_self
    have hp0 := hprime.pos
    apply Finset.mem_sigma.mpr
    refine ⟨Finset.mem_range.mpr (by dsimp [f]; omega), ?_⟩
    apply Finset.mem_filter.mpr
    dsimp [f]
    refine ⟨Finset.mem_range.mpr (by omega), hk1, by omega, ?_, ?_⟩
    · simpa only [Nat.add_sub_cancel_right] using hprime
    · simpa only [Nat.add_sub_cancel_right] using hpne
  have hinj : Function.Injective f := by
    rintro ⟨p,k⟩ ⟨q,l⟩ he
    have he1 := congrArg Sigma.fst he
    have he2 := congrArg (fun z : Σ _ : ℕ, ℕ => z.2) he
    dsimp [f] at he1 he2
    subst l
    exact Prod.ext (Nat.add_right_cancel he1) rfl
  have hcard := Finset.card_le_card_of_injOn f hmaps (hinj.injOn)
  rw [Finset.card_product, Finset.card_erase_of_mem htwo,
    Nat.primesLE_card_eq_primeCounting, Nat.card_Icc, Nat.add_sub_cancel,
    Finset.card_sigma] at hcard
  have hcardR : ((Nat.primeCounting y-1 : ℕ) : ℝ)*t ≤
      ∑ n ∈ Finset.range (x+1), ((R n).card : ℝ) := by
    exact_mod_cast hcard
  apply le_trans ?_ hcardR
  have hbase := hY y hty
  have hlogy : Real.log (y : ℝ) = (t : ℝ)*Real.log 2 := by
    simp only [y, Nat.cast_pow, Real.log_pow, Nat.cast_ofNat]
  rw [hlogy] at hbase
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hpi : (y : ℝ)/2 ≤ (Nat.primeCounting y : ℝ)*t := by
    apply (mul_le_mul_iff_right₀ hlog2).mp
    nlinarith only [hbase]
  have hhalf : (Nat.primeCounting y : ℝ) ≤ 2*((Nat.primeCounting y-1 : ℕ) : ℝ) := by
    exact_mod_cast (show Nat.primeCounting y ≤ 2*(Nat.primeCounting y-1) by omega)
  have hscaled := mul_le_mul_of_nonneg_right hhalf (show 0 ≤ (t : ℝ) by positivity)
  have hxR : (x : ℝ) ≤ 4*(y : ℝ) := by exact_mod_cast hxupper.le
  linarith

