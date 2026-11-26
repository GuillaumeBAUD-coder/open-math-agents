import FormalConjectures.OEIS.«181082»

-- Problem: Hanna's exponential series for $\binom{n}{k}^{n+k}$ — a 1
-- Upstream: formal-conjectures FormalConjectures/OEIS/181082.lean:56 (declaration OeisA181082.a_1)
-- Credit: @philipsaint (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

open PowerSeries

theorem OMA.solution : type_of% @OeisA181082.a_1 := by
  unfold OeisA181082.a OeisA181082.hannaExp
  generalize hg : OeisA181082.hannaLog
    (fun n k => if k ≤ n then (n.choose k : ℤ) ^ (n + k) else 0) = g
  have h0 : constantCoeff g = 0 := by
    subst hg
    simp [OeisA181082.hannaLog]
  have h1 : coeff 1 g = 1 := by
    subst hg
    simp [OeisA181082.hannaLog, coeff_mk]
  have hs : HasSubst g := HasSubst.of_constantCoeff_zero' h0
  rw [coeff_subst' hs]
  rw [finsum_eq_single _ 1]
  · simp [h1]
  · intro d hd
    rcases d with _ | _ | d
    · simp
    · exact absurd rfl hd
    · have hX : (X : ℚ⟦X⟧) ∣ g := X_dvd_iff.mpr h0
      have hpow : (X : ℚ⟦X⟧) ^ (d + 2) ∣ g ^ (d + 2) := pow_dvd_pow_of_dvd hX (d + 2)
      have hc : coeff 1 (g ^ (d + 2)) = 0 := X_pow_dvd_iff.mp hpow 1 (by omega)
      simp [hc]
