import FormalConjectures.Wikipedia.EswarathasanLevineConjecture

-- Problem: Eswarathasan–Levine conjectures on harmonic numerators — harmonicNumDivisibleSet two empty
-- Upstream: formal-conjectures FormalConjectures/Wikipedia/EswarathasanLevineConjecture.lean:77 (declaration EswarathasanLevineConjecture.harmonicNumDivisibleSet_two_empty)
-- Credit: @philipsaint (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

theorem OMA.solution : type_of% @EswarathasanLevineConjecture.harmonicNumDivisibleSet_two_empty := by
  refine Set.eq_empty_iff_forall_notMem.mpr ?_
  rintro n ⟨hn, hdvd⟩
  have hpos : 0 < harmonic n := harmonic_pos (by omega)
  have h := padicValRat_two_harmonic n
  have hnum : (harmonic n).num ≠ 0 := Rat.num_ne_zero.mpr hpos.ne'
  have h2 : (2 : ℕ) ∣ (harmonic n).num.natAbs := Int.natCast_dvd.mp hdvd
  have hden : ¬ (2 : ℕ) ∣ (harmonic n).den := by
    intro hd
    exact Nat.not_coprime_of_dvd_of_dvd (by norm_num) h2 hd (harmonic n).reduced
  have h1 : 1 ≤ padicValNat 2 (harmonic n).num.natAbs :=
    one_le_padicValNat_of_dvd (Int.natAbs_pos.mpr hnum).ne' h2
  have h0 : padicValNat 2 (harmonic n).den = 0 := padicValNat.eq_zero_of_not_dvd hden
  unfold padicValRat padicValInt at h
  rw [h0] at h
  have h3 : (0 : ℤ) ≤ (Nat.log 2 n : ℤ) := Int.natCast_nonneg _
  have h4 : (1 : ℤ) ≤ (padicValNat 2 (harmonic n).num.natAbs : ℤ) := by exact_mod_cast h1
  simp only [Nat.cast_zero, sub_zero] at h
  omega
