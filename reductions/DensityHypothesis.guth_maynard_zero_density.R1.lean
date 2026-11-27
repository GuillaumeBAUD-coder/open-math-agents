import FormalConjectures.Wikipedia.DensityHypothesis

/-!
# A three-range reduction of the Guth–Maynard zero-density estimate

Use Ingham's estimate on the left and Huxley's on the right. In the middle
range it suffices to count zeros, with multiplicity, in one dyadic band.
The argument below sums the band bounds with a constant uniform in sigma
and compares the exponents in the other two ranges. This follows Section
13.1 of Guth and Maynard, https://arxiv.org / abs / 2405.20552.
-/

namespace OMA.R_DensityHypothesis_guth_maynard_zero_density_R1

open DensityHypothesis

private theorem finite_zero_support {S : Set ℂ} {σ T : ℝ}
    (hS : S ⊆ {z : ℂ | σ ≤ z.re ∧ z.re ≤ 1 ∧ 0 < z.im ∧ z.im ≤ T}) :
    (S ∩ Function.support (analyticOrderNatAt riemannZeta)).Finite :=
  (zetaZeroSet_finite σ T).subset fun z hz => by
    have hh := hS hz.1
    have hzero : riemannZeta z = 0 := by
      by_contra hn
      exact hz.2 (Complex.analyticOrderNatAt_eq_zero_of_ne_zero hn)
    exact ⟨hh.1, hh.2.1, hh.2.2.1, hh.2.2.2, hzero⟩

private theorem count_mono {σ τ T U : ℝ} (hσ : σ ≤ τ) (hT : T ≤ U) :
    zetaZeroCount τ T ≤ zetaZeroCount σ U := by
  let A := {z : ℂ | τ ≤ z.re ∧ z.re ≤ 1 ∧ 0 < z.im ∧ z.im ≤ T}
  let B := {z : ℂ | σ ≤ z.re ∧ z.re ≤ 1 ∧ 0 < z.im ∧ z.im ≤ U}
  have hAB : A ⊆ B := fun z hz => ⟨hσ.trans hz.1, hz.2.1, hz.2.2.1, hz.2.2.2.trans hT⟩
  have hB := finite_zero_support (σ := σ) (T := U) (S := B) Set.Subset.rfl
  have hA := finite_zero_support hAB
  change Complex.zeroCountOn riemannZeta A ≤ Complex.zeroCountOn riemannZeta B
  unfold Complex.zeroCountOn
  rw [finsum_mem_eq_sum _ hA, finsum_mem_eq_sum _ hB]
  apply Finset.sum_le_sum_of_subset
  intro z hz
  rw [Set.Finite.mem_toFinset] at hz ⊢
  exact ⟨hAB hz.1, hz.2⟩

private theorem count_split (σ T : ℝ) (hT : 0 ≤ T) :
    zetaZeroCount σ (2 * T) = zetaZeroCount σ T +
      Complex.zeroCountOn riemannZeta {z : ℂ | σ ≤ z.re ∧ z.re ≤ 1 ∧ T < z.im ∧ z.im ≤ 2 * T} := by
  let A := {z : ℂ | σ ≤ z.re ∧ z.re ≤ 1 ∧ 0 < z.im ∧ z.im ≤ T}
  let B := {z : ℂ | σ ≤ z.re ∧ z.re ≤ 1 ∧ T < z.im ∧ z.im ≤ 2 * T}
  let C := {z : ℂ | σ ≤ z.re ∧ z.re ≤ 1 ∧ 0 < z.im ∧ z.im ≤ 2 * T}
  have hAC : A ⊆ C := fun z hz => ⟨hz.1, hz.2.1, hz.2.2.1, by linarith [hz.2.2.2]⟩
  have hBC : B ⊆ C := fun z hz => ⟨hz.1, hz.2.1, hT.trans_lt hz.2.2.1, hz.2.2.2⟩
  have hC : C = A ∪ B := by
    ext z
    constructor
    · intro hz
      by_cases hzT : z.im ≤ T
      · exact Or.inl ⟨hz.1, hz.2.1, hz.2.2.1, hzT⟩
      · exact Or.inr ⟨hz.1, hz.2.1, lt_of_not_ge hzT, hz.2.2.2⟩
    · rintro (hz | hz)
      · exact hAC hz
      · exact hBC hz
  have hAB : Disjoint A B := Set.disjoint_left.mpr fun z ha hb =>
    (not_lt_of_ge ha.2.2.2) hb.2.2.1
  change Complex.zeroCountOn riemannZeta C = Complex.zeroCountOn riemannZeta A +
    Complex.zeroCountOn riemannZeta B
  unfold Complex.zeroCountOn
  rw [hC, finsum_mem_union' hAB (finite_zero_support hAC) (finite_zero_support hBC)]

private theorem power_two_bounds {T : ℝ} (hT : 2 ≤ T) :
    ∃ k : ℕ, 2 ≤ (2 : ℝ) ^ (k + 1) ∧ T ≤ (2 : ℝ) ^ (k + 1) ∧ (2 : ℝ) ^ (k + 1) ≤ 2 * T := by
  let P (k : ℕ) := T ≤ (2 : ℝ) ^ (k + 1)
  have hP : ∃ k, P k := by
    obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt T (by norm_num : (1 : ℝ) < 2)
    exact ⟨k, hk.le.trans (pow_le_pow_right₀ (by norm_num) (Nat.le_succ k))⟩
  let k := Nat.find hP
  have hk : P k := Nat.find_spec hP
  refine ⟨k, ?_, hk, ?_⟩
  · simpa using (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2)
      (show 1 ≤ k + 1 by omega))
  · by_cases hk0 : k = 0
    · rw [hk0]
      norm_num
      linarith
    · have hSmall := Nat.find_min hP (show k - 1 < Nat.find hP from Nat.sub_lt (Nat.pos_of_ne_zero hk0) (by decide))
      change ¬T ≤ (2 : ℝ) ^ ((k - 1) + 1) at hSmall
      rw [show k - 1 + 1 = k by omega] at hSmall
      rw [pow_succ, mul_comm]
      exact mul_le_mul_of_nonneg_left (lt_of_not_ge hSmall).le (by norm_num)

private theorem middle_range {ε C : ℝ} (hε : 0 < ε) (hC : 0 < C)
    (hBand : ∀ σ T : ℝ, 7 / 10 ≤ σ → σ ≤ 4 / 5 → 2 ≤ T →
      (Complex.zeroCountOn riemannZeta
        {z : ℂ | σ ≤ z.re ∧ z.re ≤ 1 ∧ T < z.im ∧ z.im ≤ 2 * T} : ℝ) ≤
        C * T ^ ((30 / 13 : ℝ) * (1 - σ) + ε)) :
    ∃ D : ℝ, 0 < D ∧ ∀ σ T : ℝ, 7 / 10 ≤ σ → σ ≤ 4 / 5 → 2 ≤ T →
      (zetaZeroCount σ T : ℝ) ≤ D * T ^ ((30 / 13 : ℝ) * (1 - σ) + ε) := by
  let base := (zetaZeroCount (1 / 2) 2 : ℝ)
  let K := base + C / ((2 : ℝ) ^ ε - 1)
  have hε2 : 1 < (2 : ℝ) ^ ε := Real.one_lt_rpow (by norm_num) hε
  have hε2' : 0 < (2 : ℝ) ^ ε - 1 := sub_pos.mpr hε2
  have hK : 0 < K := add_pos_of_nonneg_of_pos (Nat.cast_nonneg _) (div_pos hC hε2')
  refine ⟨K * (2 : ℝ) ^ ((30 / 13 : ℝ) * (1 / 2) + ε), by positivity, ?_⟩
  intro σ T hl hu hT
  let a := (30 / 13 : ℝ) * (1 - σ) + ε
  have hεa : ε ≤ a := by dsimp [a]; nlinarith
  have ha : 0 < a := hε.trans_le hεa
  have hUp : a ≤ (30 / 13 : ℝ) * (1 / 2) + ε := by dsimp [a]; nlinarith
  have hGa : (2 : ℝ) ^ ε ≤ (2 : ℝ) ^ a := Real.rpow_le_rpow_of_exponent_le (by norm_num) hεa
  have hRec : K + C ≤ K * (2 : ℝ) ^ a := by
    have hbase : 0 ≤ base := by positivity
    have hKdiff : base ≤ K := le_add_of_nonneg_right (div_pos hC hε2').le
    have hQuot : C / ((2 : ℝ) ^ ε - 1) ≤ K := le_add_of_nonneg_left hbase
    have hQ := (div_le_iff₀ hε2').mp hQuot
    have hdiff := mul_le_mul_of_nonneg_left hGa hK.le
    linarith
  have hDyadic (k : ℕ) :
      (zetaZeroCount σ ((2 : ℝ) ^ (k + 1)) : ℝ) ≤ K * ((2 : ℝ) ^ (k + 1)) ^ a := by
    induction k with
    | zero =>
      norm_num only [zero_add, pow_one]
      have hb : (zetaZeroCount σ 2 : ℝ) ≤ base := by
        change (zetaZeroCount σ 2 : ℝ) ≤ (zetaZeroCount (1 / 2) 2 : ℝ)
        exact_mod_cast count_mono (σ := 1 / 2) (τ := σ) (by linarith : 1 / 2 ≤ σ) (le_refl (2 : ℝ))
      have hbaseK : base ≤ K := le_add_of_nonneg_right (div_pos hC hε2').le
      exact hb.trans (hbaseK.trans (le_mul_of_one_le_right hK.le (Real.one_le_rpow (by norm_num) ha.le)))
    | succ k ih =>
      let s := (2 : ℝ) ^ (k + 1)
      have hs : 2 ≤ s := by
        change 2 ≤ (2 : ℝ) ^ (k + 1)
        simpa using pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (show 1 ≤ k + 1 by omega)
      have he : (2 : ℝ) ^ (k.succ + 1) = 2 * s := by
        change (2 : ℝ) ^ (k + 1 + 1) = 2 * (2 : ℝ) ^ (k + 1)
        rw [pow_succ, mul_comm]
      rw [he, count_split σ s (by linarith), Nat.cast_add]
      change (zetaZeroCount σ s : ℝ) +
        (Complex.zeroCountOn riemannZeta
          {z : ℂ | σ ≤ z.re ∧ z.re ≤ 1 ∧ s < z.im ∧ z.im ≤ 2 * s} : ℝ) ≤ K * (2 * s) ^ a
      calc
        _ ≤ K * s ^ a + C * s ^ a := add_le_add ih (hBand σ s hl hu hs)
        _ = (K + C) * s ^ a := (add_mul _ _ _).symm
        _ ≤ (K * (2 : ℝ) ^ a) * s ^ a := mul_le_mul_of_nonneg_right hRec (by positivity)
        _ = _ := by rw [Real.mul_rpow (by norm_num) (by positivity), mul_assoc]
  obtain ⟨k, _, hk, hk'⟩ := power_two_bounds hT
  have hTP : 0 ≤ T := by linarith
  have hcount : (zetaZeroCount σ T : ℝ) ≤ (zetaZeroCount σ ((2 : ℝ) ^ (k + 1)) : ℝ) :=
    by exact_mod_cast count_mono (le_refl σ) hk
  change (zetaZeroCount σ T : ℝ) ≤ K * (2 : ℝ) ^ ((30 / 13 : ℝ) * (1 / 2) + ε) * T ^ a
  calc
    _ ≤ K * ((2 : ℝ) ^ (k + 1)) ^ a := hcount.trans (hDyadic k)
    _ ≤ K * (2 * T) ^ a := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (by positivity) hk' ha.le) hK.le
    _ = K * (2 : ℝ) ^ a * T ^ a := by rw [Real.mul_rpow (by norm_num) hTP, mul_assoc]
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le (by norm_num) hUp) hK.le)
      (by positivity)

/-- Ingham's estimate on the range preceding the Guth–Maynard argument. -/
def H1 : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∀ σ T : ℝ,
    1 / 2 ≤ σ → σ ≤ 7 / 10 → 2 ≤ T →
    (zetaZeroCount σ T : ℝ) ≤ C * T ^ (3 * (1 - σ) / (2 - σ) + ε)

/-- Huxley's estimate on the range following the Guth–Maynard argument. -/
def H2 : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∀ σ T : ℝ,
    4 / 5 ≤ σ → σ ≤ 1 → 2 ≤ T →
    (zetaZeroCount σ T : ℝ) ≤ C * T ^ (3 * (1 - σ) / (3 * σ - 1) + ε)

/-- The central estimate for a single band of heights. -/
def H3 : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∀ σ T : ℝ,
    7 / 10 ≤ σ → σ ≤ 4 / 5 → 2 ≤ T →
    (Complex.zeroCountOn riemannZeta
      {z : ℂ | σ ≤ z.re ∧ z.re ≤ 1 ∧ T < z.im ∧ z.im ≤ 2 * T} : ℝ) ≤
      C * T ^ ((30 / 13 : ℝ) * (1 - σ) + ε)

theorem main : H1 → H2 → H3 → type_of% @DensityHypothesis.guth_maynard_zero_density := by
  intro hIngham hHuxley hMiddle ε hε
  obtain ⟨A, hA, hI⟩ := hIngham ε hε
  obtain ⟨B, hB, hH⟩ := hHuxley ε hε
  obtain ⟨C, hC, hBand⟩ := hMiddle ε hε
  obtain ⟨D, hD, hM⟩ := middle_range hε hC hBand
  refine ⟨A + B + D, by positivity, fun σ T hσ0 hσ1 hT => ?_⟩
  have hT1 : 1 ≤ T := by linarith
  have hT0 : 0 ≤ T := by linarith
  have hσ : 0 ≤ 1 - σ := sub_nonneg.mpr hσ1
  by_cases hLow : σ ≤ 7 / 10
  · have hz : 3 * (1 - σ) / (2 - σ) ≤ (30 / 13 : ℝ) * (1 - σ) := by
      have hRatio : 3 / (2 - σ) ≤ (30 / 13 : ℝ) :=
        (div_le_iff₀ (by linarith)).mpr (by linarith)
      calc
        _ = (3 / (2 - σ)) * (1 - σ) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_right hRatio hσ
    refine (hI σ T hσ0 hLow hT).trans ?_
    apply mul_le_mul (by linarith) (Real.rpow_le_rpow_of_exponent_le hT1 (by linarith))
      (by positivity) (by positivity)
  · by_cases hHigh : 4 / 5 ≤ σ
    · have hz : 3 * (1 - σ) / (3 * σ - 1) ≤ (30 / 13 : ℝ) * (1 - σ) := by
        have hRatio : 3 / (3 * σ - 1) ≤ (30 / 13 : ℝ) :=
          (div_le_iff₀ (by linarith)).mpr (by linarith)
        calc
          _ = (3 / (3 * σ - 1)) * (1 - σ) := by ring
          _ ≤ _ := mul_le_mul_of_nonneg_right hRatio hσ
      refine (hH σ T hHigh hσ1 hT).trans ?_
      apply mul_le_mul (by linarith) (Real.rpow_le_rpow_of_exponent_le hT1 (by linarith))
        (by positivity) (by positivity)
    · exact (hM σ T (le_of_not_ge hLow) (le_of_not_ge hHigh) hT).trans
        (mul_le_mul_of_nonneg_right (by linarith) (by positivity))

end OMA.R_DensityHypothesis_guth_maynard_zero_density_R1
