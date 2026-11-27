import OMAReductions.R_Erdos604_erdos_604_variants_grid_upper_bound_R1
import Mathlib.NumberTheory.Chebyshev

-- Credit: @JaviSoto

/-! The sum of the full logarithms of prime powers up to X is O(X). -/

open Finset Chebyshev ArithmeticFunction

namespace OMA.Grid604

theorem prime_power_log_sum_linear :
    ∃ C : ℝ, 0 < C ∧ ∀ X : ℕ,
      (∑ d ∈ Ioc 0 X with IsPrimePow d, Real.log (d : ℝ)) ≤ C * X := by
  obtain ⟨B, hB⟩ := Chebyshev.psi_sub_theta_le_mul_sqrt
  have htwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨Real.log 4 + 2 * |B| / Real.log 2, by positivity, ?_⟩
  intro X
  let A := Real.log X / Real.log 2
  have hA : 0 ≤ A := div_nonneg (Real.log_natCast_nonneg _) htwo.le
  let primeLog (d : ℕ) : ℝ := if d.Prime then Real.log d else 0
  have hcmp (d : ℕ) (hd : d ∈ Ioc 0 X) :
      (if IsPrimePow d then Real.log d else 0) ≤
        primeLog d + A * (vonMangoldt d - primeLog d) := by
    by_cases hp : d.Prime
    · simp [primeLog, hp, hp.isPrimePow, vonMangoldt_apply_prime hp]
    by_cases hq : IsPrimePow d
    · simp only [hq, if_true, primeLog, hp, if_false, sub_zero, zero_add]
      have hmin : Real.log 2 ≤ vonMangoldt d := by
        rw [vonMangoldt_apply, if_pos hq]
        apply Real.log_le_log (by norm_num)
        exact_mod_cast (Nat.minFac_prime hq.ne_one).two_le
      calc Real.log d ≤ Real.log X := Real.log_le_log (by exact_mod_cast (mem_Ioc.mp hd).1)
            (by exact_mod_cast (mem_Ioc.mp hd).2)
           _ = A * Real.log 2 := by dsimp [A]; field_simp
           _ ≤ _ := mul_le_mul_of_nonneg_left hmin hA
    · simp [primeLog, hp, hq, vonMangoldt_eq_zero_iff.mpr hq]
  have htheta : (∑ d ∈ Ioc 0 X, primeLog d) = theta X := by
    simp [Chebyshev.theta, sum_filter, primeLog]
  have hpsi : (∑ d ∈ Ioc 0 X, vonMangoldt d) = psi X := by simp [Chebyshev.psi]
  have hsum : (∑ d ∈ Ioc 0 X with IsPrimePow d, Real.log (d : ℝ)) ≤
      theta X + A * (psi X - theta X) := by
    rw [sum_filter, ← htheta, ← hpsi, ← sum_sub_distrib, mul_sum, ← sum_add_distrib]
    exact sum_le_sum hcmp
  have hx : 0 ≤ (X : ℝ) := Nat.cast_nonneg _
  have hlog : Real.log X ≤ 2 * Real.sqrt X := by
    linarith [Real.log_le_self (Real.sqrt_nonneg X), Real.log_sqrt hx]
  have habs : psi X - theta X ≤ |B| * Real.sqrt X :=
    (hB X).trans (mul_le_mul_of_nonneg_right (le_abs_self _) (Real.sqrt_nonneg _))
  calc
    _ ≤ theta X + A * (psi X - theta X) := hsum
    _ ≤ Real.log 4 * X + (2 * Real.sqrt X / Real.log 2) * (|B| * Real.sqrt X) := by
      refine add_le_add (theta_le_log4_mul_x hx) ?_
      exact (mul_le_mul_of_nonneg_left habs hA).trans
        (mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hlog htwo.le) (by positivity))
    _ = _ := by
      ring_nf
      rw [Real.sq_sqrt hx]

end OMA.Grid604

/- Strip the entire prime-power component from a sum of two squares, then sum over its complement. -/

namespace OMA.Grid604Weighted

open Finset Filter

private abbrev admissible (n : ℕ) :=
  ∀ q ∈ n.primeFactors, q % 4 = 3 → Even (padicValNat q n)

private theorem admissible_ordCompl {n : ℕ} (hn : admissible n) (p : ℕ) :
    admissible (ordCompl[p] n) := by
  intro q hq hmod
  have hpq := Nat.prime_of_mem_primeFactors hq
  rw [← Nat.factorization_def _ hpq, Nat.factorization_ordCompl]
  by_cases he : q = p
  · simp [he]
  · rw [Finsupp.erase_ne he]
    have hqn : q ∈ n.primeFactors := by
      have hne : n ≠ 0 := by rintro rfl; simp at hq
      exact Nat.mem_primeFactors.mpr ⟨hpq,
        (Nat.dvd_of_mem_primeFactors hq).trans (Nat.ordCompl_dvd n p), hne⟩
    rw [Nat.factorization_def _ hpq]
    exact hn q hqn hmod

private theorem component_sum (n : ℕ) :
    Real.log n = ∑ p ∈ n.primeFactors, Real.log (ordProj[p] n : ℕ) := by
  rw [Real.log_nat_eq_sum_factorization]
  simp [Finsupp.sum, Real.log_pow]

private abbrev Index := Σ _ : ℕ, ℕ

private def strip (x : Index) : Index := ⟨ordCompl[x.2] x.1, ordProj[x.2] x.1⟩

private theorem strip_injective {S : Finset ℕ} :
    Set.InjOn strip (S.sigma Nat.primeFactors) := by
  intro ⟨m,p⟩ hmp ⟨n,q⟩ hnq he
  have hp := (mem_sigma.mp hmp).2
  have hq := (mem_sigma.mp hnq).2
  have hc : ordCompl[p] m = ordCompl[q] n := congrArg (fun z : Index => z.1) he
  have hd : ordProj[p] m = ordProj[q] n := congrArg (fun z : Index => z.2) he
  have hmn : m = n := by
    rw [← Nat.ordProj_mul_ordCompl_eq_self m p, hc, hd, Nat.ordProj_mul_ordCompl_eq_self]
  have hpow {v r : ℕ} (h : r ∈ v.primeFactors) : (ordProj[r] v).minFac = r :=
    (Nat.prime_of_mem_primeFactors h).pow_minFac (Finsupp.mem_support_iff.mp h)
  have hpq := (hpow hp).symm.trans ((congrArg Nat.minFac hd).trans (hpow hq))
  subst n q
  rfl

private noncomputable def admissibleSet (N : ℕ) := (range (N+1)).filter admissible

private theorem component_bound (N : ℕ) :
    ∑ n ∈ admissibleSet N, Real.log n ≤
      ∑ m ∈ admissibleSet N, ∑ d ∈ (Ioc 0 (N/m)).filter IsPrimePow, Real.log d := by
  classical
  let S := admissibleSet N
  let A : Finset Index := S.sigma Nat.primeFactors
  let B : Finset Index := S.sigma (fun m => (Ioc 0 (N/m)).filter IsPrimePow)
  have hsub : A.image strip ⊆ B := by
    intro z hz
    obtain ⟨⟨n,p⟩, hnp, rfl⟩ := mem_image.mp hz
    obtain ⟨hn, hp⟩ := mem_sigma.mp hnp
    obtain ⟨hN, ha⟩ := mem_filter.mp hn
    have hle : n ≤ N := by simpa using hN
    have hn0 := (Nat.mem_primeFactors.mp hp).2.2
    have hcp := Nat.ordCompl_pos p hn0
    apply mem_sigma.mpr
    refine ⟨mem_filter.mpr ⟨mem_range.mpr (Nat.lt_succ_of_le ((Nat.ordCompl_le n p).trans hle)),
      admissible_ordCompl ha p⟩, mem_filter.mpr ⟨mem_Ioc.mpr ⟨Nat.ordProj_pos n p, ?_⟩, ?_⟩⟩
    · exact (Nat.le_div_iff_mul_le hcp).mpr ((Nat.ordProj_mul_ordCompl_eq_self n p).le.trans hle)
    · exact ⟨p, n.factorization p, Nat.prime_iff.mp (Nat.prime_of_mem_primeFactors hp),
        Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hp), rfl⟩
  calc
    _ = ∑ x ∈ A, Real.log (strip x).2 := by
      rw [Finset.sum_sigma]
      exact sum_congr rfl (fun n _ => component_sum n)
    _ = ∑ y ∈ A.image strip, Real.log y.2 :=
      (sum_image (f := fun y : Index => Real.log y.2) (strip_injective (S := S))).symm
    _ ≤ ∑ y ∈ B, Real.log y.2 := sum_le_sum_of_subset_of_nonneg hsub
      (fun y _ _ => Real.log_natCast_nonneg y.2)
    _ = _ := Finset.sum_sigma ..

theorem weighted_of_primePowers
    (hprime : ∃ C : ℝ, 0 < C ∧ ∀ X : ℕ,
      (∑ d ∈ (Ioc 0 X).filter IsPrimePow, Real.log (d : ℝ)) ≤ C * X) :
    ∃ D : ℝ, 0 < D ∧ ∀ᶠ N : ℕ in atTop,
      let S := ((range (N + 1)).filter fun m =>
        ∀ q ∈ m.primeFactors, q % 4 = 3 → Even (padicValNat q m))
      (∑ m ∈ S, Real.log m) ≤ D * N * ∑ m ∈ S, (m : ℝ)⁻¹ := by
  obtain ⟨C, hC, h⟩ := hprime
  refine ⟨C, hC, Eventually.of_forall fun N => ?_⟩
  change _ ≤ _ * ∑ m ∈ admissibleSet N, (m : ℝ)⁻¹
  rw [Finset.mul_sum]
  apply (component_bound N).trans
  apply sum_le_sum
  intro m _
  calc
    _ ≤ _ := h (N/m)
    _ ≤ C * ((N:ℝ)/m) := mul_le_mul_of_nonneg_left Nat.cast_div_le hC.le
    _ = _ := by ring

end OMA.Grid604Weighted

theorem OMA.solution : OMA.R_Erdos604_erdos_604_variants_grid_upper_bound_R1.H2 :=
  OMA.Grid604Weighted.weighted_of_primePowers OMA.Grid604.prime_power_log_sum_linear
