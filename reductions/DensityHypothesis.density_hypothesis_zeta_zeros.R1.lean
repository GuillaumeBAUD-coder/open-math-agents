import FormalConjectures.Wikipedia.DensityHypothesis

-- Reduction DensityHypothesis.density_hypothesis_zeta_zeros.R1 of Density hypothesis for Riemann zeta zeros — density hypothesis zeta zeros
-- Credit: @senamakel
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.
--
-- Route: under RH there is no zero with real part above 1/2 and positive imaginary part, so
-- N(σ, T) = 0 for σ > 1/2. At σ = 1/2 the exponent is 1 + ε, and the classical bound
-- N(T) ≤ C T log T together with log T ≤ T^ε / ε gives N(1/2, T) ≤ (C / ε) T^(1 + ε).

namespace OMA.R_DensityHypothesis_density_hypothesis_zeta_zeros_R1

-- The Riemann Hypothesis, as Mathlib states it.
def H1 : Prop := RiemannHypothesis

-- The classical zero-counting bound N(T) = O(T log T) (Riemann–von Mangoldt): the zeros of
-- zeta in the critical strip 0 ≤ Re s ≤ 1 with 0 < Im s ≤ T, counted with multiplicity,
-- number at most C T log T for T ≥ 2.
def H2 : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
    (Complex.zeroCountOn riemannZeta
      {s : ℂ | 0 ≤ s.re ∧ s.re ≤ 1 ∧ 0 < s.im ∧ s.im ≤ T} : ℝ) ≤ C * T * Real.log T

/-- Under RH, zeta has no zero with real part above 1/2 off the real axis. -/
lemma riemannZeta_ne_zero_of_RH (hRH : RiemannHypothesis) {s : ℂ} (hs : 1 / 2 < s.re)
    (him : s.im ≠ 0) : riemannZeta s ≠ 0 := by
  intro h0
  have htriv : ¬∃ n : ℕ, s = -2 * (n + 1) := by
    rintro ⟨n, rfl⟩
    apply him
    simp
  have h1 : s ≠ 1 := by rintro rfl; simp at him
  have := hRH s h0 htriv h1
  linarith

/-- The zero count is monotone in the region, provided the zeros in the larger region are
finitely many. -/
lemma zeroCountOn_mono {f : ℂ → ℂ} {S S' : Set ℂ} (h : S ⊆ S')
    (hfin : {s ∈ S' | f s = 0}.Finite) :
    Complex.zeroCountOn f S ≤ Complex.zeroCountOn f S' := by
  rw [← Complex.zeroCountOn_sep_eq_zero f S, ← Complex.zeroCountOn_sep_eq_zero f S']
  have hsub : {s ∈ S | f s = 0} ⊆ {s ∈ S' | f s = 0} := fun s hs => ⟨h hs.1, hs.2⟩
  have hfin0 : {s ∈ S | f s = 0}.Finite := hfin.subset hsub
  unfold Complex.zeroCountOn
  rw [finsum_mem_eq_finite_toFinset_sum _ hfin0, finsum_mem_eq_finite_toFinset_sum _ hfin]
  exact Finset.sum_le_sum_of_subset (Set.Finite.toFinset_subset_toFinset.mpr hsub)

theorem main : H1 → H2 → type_of% @DensityHypothesis.density_hypothesis_zeta_zeros := by
  intro hRH hN ε hε
  obtain ⟨C, hC, hcount⟩ := hN
  refine ⟨C / ε, div_pos hC hε, fun σ T hσ hσ1 hT => ?_⟩
  have hT0 : 0 < T := by linarith
  have hpos : 0 ≤ C / ε * T ^ (2 * (1 - σ) + ε) := by positivity
  rcases hσ.lt_or_eq with hlt | heq
  · have h0 : DensityHypothesis.zetaZeroCount σ T = 0 :=
      Complex.zeroCountOn_eq_zero_of_forall_ne_zero fun _ hs =>
        riemannZeta_ne_zero_of_RH hRH (hlt.trans_le hs.1) hs.2.2.1.ne'
    rw [h0, Nat.cast_zero]
    exact hpos
  · subst heq
    have hS : {s : ℂ | 1 / 2 ≤ s.re ∧ s.re ≤ 1 ∧ 0 < s.im ∧ s.im ≤ T} ⊆
        {s : ℂ | 0 ≤ s.re ∧ s.re ≤ 1 ∧ 0 < s.im ∧ s.im ≤ T} := fun s hs =>
      ⟨by linarith [hs.1], hs.2.1, hs.2.2.1, hs.2.2.2⟩
    have hfin : {s ∈ {s : ℂ | 0 ≤ s.re ∧ s.re ≤ 1 ∧ 0 < s.im ∧ s.im ≤ T} |
        riemannZeta s = 0}.Finite := by
      refine (DensityHypothesis.zetaZeroSet_finite 0 T).subset fun s hs => ?_
      exact ⟨hs.1.1, hs.1.2.1, hs.1.2.2.1, hs.1.2.2.2, hs.2⟩
    have hmono : (DensityHypothesis.zetaZeroCount (1 / 2) T : ℝ) ≤
        (Complex.zeroCountOn riemannZeta
          {s : ℂ | 0 ≤ s.re ∧ s.re ≤ 1 ∧ 0 < s.im ∧ s.im ≤ T} : ℝ) := by
      exact_mod_cast zeroCountOn_mono hS hfin
    refine hmono.trans ((hcount T hT).trans ?_)
    have hlog : Real.log T ≤ T ^ ε / ε := Real.log_le_rpow_div hT0.le hε
    have hexp : T ^ (2 * (1 - 1 / 2) + ε) = T * T ^ ε := by
      rw [show 2 * (1 - 1 / 2 : ℝ) + ε = 1 + ε by ring, Real.rpow_add hT0, Real.rpow_one]
    rw [hexp]
    calc C * T * Real.log T ≤ C * T * (T ^ ε / ε) := by gcongr
      _ = C / ε * (T * T ^ ε) := by ring

end OMA.R_DensityHypothesis_density_hypothesis_zeta_zeros_R1
