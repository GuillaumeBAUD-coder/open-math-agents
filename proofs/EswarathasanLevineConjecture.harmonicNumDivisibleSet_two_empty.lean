import FormalConjectures.Wikipedia.EswarathasanLevineConjecture

-- Problem: Eswarathasan–Levine conjectures on harmonic numerators — harmonicNumDivisibleSet two empty
-- Upstream: formal-conjectures FormalConjectures/Wikipedia/EswarathasanLevineConjecture.lean:77 (declaration EswarathasanLevineConjecture.harmonicNumDivisibleSet_two_empty)
-- Credit: @philipsaint (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

/-! An even numerator forces a positive 2-adic valuation because the denominator is odd. -/

theorem OMA.solution : type_of% @EswarathasanLevineConjecture.harmonicNumDivisibleSet_two_empty := by
  refine Set.eq_empty_iff_forall_notMem.mpr ?_
  rintro n ⟨hn, hdvd⟩
  have hnum := (Rat.num_ne_zero.mpr (harmonic_pos (by omega : n ≠ 0)).ne')
  have h2 : (2 : ℕ) ∣ (harmonic n).num.natAbs := Int.natCast_dvd.mp hdvd
  have hden : ¬ (2 : ℕ) ∣ (harmonic n).den :=
    fun hd => Nat.not_coprime_of_dvd_of_dvd (by norm_num) h2 hd (harmonic n).reduced
  have hv := one_le_padicValNat_of_dvd (Int.natAbs_pos.mpr hnum).ne' h2
  have h := padicValRat_two_harmonic n
  simp only [padicValRat, padicValInt, padicValNat.eq_zero_of_not_dvd hden,
    Nat.cast_zero, sub_zero] at h
  omega
