import FormalConjectures.ErdosProblems.«1189»

-- Problem: Erdős Problem 1189 — simpson
-- Upstream: formal-conjectures FormalConjectures/ErdosProblems/1189.lean:172 (declaration Erdos1189.erdos_1189.variants.simpson)
-- Credit: @marcusbuffett (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

/-! Simpson's bound for irreducible covering sets, through the theorem of Crittenden and
Vanden Eynden: arithmetic progressions with moduli in `N` that cover `2 ^ N.card` consecutive
integers cover every integer. -/

namespace SimpsonBound

open Polynomial

/-- A sum of `s.card` exponential sequences with nonzero bases that vanishes at `s.card`
consecutive integers vanishes at every integer. -/
theorem expsum_vanish {ι : Type*} (s : Finset ι) (b ω : ι → ℂ) (hω : ∀ i ∈ s, ω i ≠ 0) (x : ℤ)
    (h : ∀ z : ℤ, x ≤ z → z < x + s.card → ∑ i ∈ s, b i * ω i ^ z = 0) :
    ∀ z : ℤ, ∑ i ∈ s, b i * ω i ^ z = 0 := by
  classical
  have hdeg : (∏ i ∈ s, (X - C (ω i))).natDegree = s.card := by
    rw [natDegree_prod_of_monic _ _ (fun i _ => monic_X_sub_C _)]
    simp
  have hmonic : (∏ i ∈ s, (X - C (ω i))).Monic := monic_prod_of_monic _ _ (fun i _ => monic_X_sub_C _)
  have hc0 : (∏ i ∈ s, (X - C (ω i))).coeff 0 ≠ 0 := by
    rw [coeff_zero_eq_eval_zero, eval_prod]
    refine Finset.prod_ne_zero_iff.mpr fun i hi => ?_
    simpa using hω i hi
  have hroot : ∀ i ∈ s, (∏ j ∈ s, (X - C (ω j))).eval (ω i) = 0 := by
    intro i hi
    rw [eval_prod]
    exact Finset.prod_eq_zero hi (by simp)
  have hlead : (∏ i ∈ s, (X - C (ω i))).coeff s.card = 1 := by
    have := hmonic.coeff_natDegree
    rwa [hdeg] at this
  have hrec : ∀ z : ℤ, ∑ t ∈ Finset.range (s.card + 1),
      (∏ i ∈ s, (X - C (ω i))).coeff t * ∑ i ∈ s, b i * ω i ^ (z + (t : ℤ)) = 0 := by
    intro z
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_eq_zero
    intro i hi
    have h1 : ∀ t ∈ Finset.range (s.card + 1),
        (∏ j ∈ s, (X - C (ω j))).coeff t * (b i * ω i ^ (z + (t : ℤ)))
          = b i * ω i ^ z * ((∏ j ∈ s, (X - C (ω j))).coeff t * ω i ^ t) := by
      intro t _
      rw [zpow_add₀ (hω i hi), zpow_natCast]
      ring
    rw [Finset.sum_congr rfl h1, ← Finset.mul_sum]
    have h2 : ∑ t ∈ Finset.range (s.card + 1), (∏ j ∈ s, (X - C (ω j))).coeff t * ω i ^ t
        = (∏ j ∈ s, (X - C (ω j))).eval (ω i) := by
      rw [eval_eq_sum_range, hdeg]
    rw [h2, hroot i hi, mul_zero]
  have hfwd : ∀ j : ℕ, ∑ i ∈ s, b i * ω i ^ (x + (j : ℤ)) = 0 := by
    intro j
    induction j using Nat.strong_induction_on with
    | _ j ih =>
      by_cases hj : j < s.card
      · exact h _ (by omega) (by omega)
      · rw [not_lt] at hj
        have hr := hrec (x + ((j - s.card : ℕ) : ℤ))
        rw [Finset.sum_range_succ] at hr
        have hz : ∑ t ∈ Finset.range s.card, (∏ i ∈ s, (X - C (ω i))).coeff t *
            ∑ i ∈ s, b i * ω i ^ (x + ((j - s.card : ℕ) : ℤ) + (t : ℤ)) = 0 := by
          apply Finset.sum_eq_zero
          intro t ht
          rw [Finset.mem_range] at ht
          have e : x + ((j - s.card : ℕ) : ℤ) + (t : ℤ) = x + ((j - s.card + t : ℕ) : ℤ) := by
            push_cast; ring
          rw [e, ih _ (by omega), mul_zero]
        rw [hz, zero_add, hlead, one_mul] at hr
        have e : x + ((j - s.card : ℕ) : ℤ) + (s.card : ℤ) = x + (j : ℤ) := by
          rw [Nat.cast_sub hj]; ring
        rwa [e] at hr
  have hall : ∀ j : ℕ, ∀ z : ℤ, x - j ≤ z → ∑ i ∈ s, b i * ω i ^ z = 0 := by
    intro j
    induction j with
    | zero =>
      intro z hz
      have e : z = x + ((z - x).toNat : ℤ) := by
        rw [Int.toNat_of_nonneg (by simpa using hz)]; ring
      rw [e]
      exact hfwd _
    | succ j ih =>
      intro z hz
      by_cases hz' : x - j ≤ z
      · exact ih z hz'
      · have hr := hrec z
        rw [Finset.sum_range_succ'] at hr
        have hz0 : ∑ t ∈ Finset.range s.card, (∏ i ∈ s, (X - C (ω i))).coeff (t + 1) *
            ∑ i ∈ s, b i * ω i ^ (z + ((t + 1 : ℕ) : ℤ)) = 0 := by
          apply Finset.sum_eq_zero
          intro t _
          rw [ih _ (by push_cast at hz ⊢; omega), mul_zero]
        rw [hz0, zero_add] at hr
        simpa [hc0] using hr
  intro z
  refine hall (x - z).toNat z ?_
  have := Int.self_le_toNat (x - z)
  omega

/-- Crittenden--Vanden Eynden: residue classes with moduli in `N` that cover `2 ^ N.card`
consecutive integers cover all the integers. -/
theorem covers_of_covers_window (N : Finset ℕ) (hpos : ∀ m ∈ N, 0 < m) (a : ℕ → ℤ) (x : ℤ)
    (hcov : ∀ z : ℤ, x ≤ z → z < x + 2 ^ N.card → ∃ m ∈ N, z ≡ a m [ZMOD m]) :
    ∀ z : ℤ, ∃ m ∈ N, z ≡ a m [ZMOD m] := by
  classical
  have hne : ∀ m : ℕ, Complex.exp (2 * Real.pi * Complex.I / m) ≠ 0 := fun m => Complex.exp_ne_zero _
  have hiff : ∀ z : ℤ, (∃ m ∈ N, z ≡ a m [ZMOD m]) ↔
      ∏ m ∈ N, (1 - Complex.exp (2 * Real.pi * Complex.I / m) ^ (z - a m)) = 0 := by
    intro z
    rw [Finset.prod_eq_zero_iff]
    refine exists_congr fun m => and_congr_right fun hm => ?_
    rw [sub_eq_zero, eq_comm,
      (Complex.isPrimitiveRoot_exp m (hpos m hm).ne').zpow_eq_one_iff_dvd, Int.modEq_iff_dvd,
      dvd_sub_comm]
  have hexp : ∀ z : ℤ, ∏ m ∈ N, (1 - Complex.exp (2 * Real.pi * Complex.I / m) ^ (z - a m))
      = ∑ t ∈ N.powerset, (∏ m ∈ t, (-(Complex.exp (2 * Real.pi * Complex.I / m) ^ (-a m)))) *
          (∏ m ∈ t, Complex.exp (2 * Real.pi * Complex.I / m)) ^ z := by
    intro z
    have h1 : ∀ m ∈ N, (1 - Complex.exp (2 * Real.pi * Complex.I / m) ^ (z - a m))
        = (-(Complex.exp (2 * Real.pi * Complex.I / m) ^ (-a m)) *
            Complex.exp (2 * Real.pi * Complex.I / m) ^ z) + 1 := by
      intro m _
      rw [sub_eq_add_neg z, zpow_add₀ (hne m)]
      ring
    rw [Finset.prod_congr rfl h1, Finset.prod_add]
    apply Finset.sum_congr rfl
    intro t _
    rw [Finset.prod_const_one, mul_one, Finset.prod_mul_distrib, Finset.prod_zpow]
  have key := expsum_vanish N.powerset
    (fun t => ∏ m ∈ t, (-(Complex.exp (2 * Real.pi * Complex.I / m) ^ (-a m))))
    (fun t => ∏ m ∈ t, Complex.exp (2 * Real.pi * Complex.I / m))
    (fun t _ => Finset.prod_ne_zero_iff.mpr fun m _ => hne m) x (by
      intro z hz1 hz2
      rw [← hexp, ← hiff]
      apply hcov z hz1
      simpa [Finset.card_powerset] using hz2)
  intro z
  rw [hiff, hexp]
  exact key z

end SimpsonBound

theorem OMA.solution : type_of% @Erdos1189.erdos_1189.variants.simpson := by
  intro M hM n hn
  obtain ⟨⟨hgt, a, ha⟩, hirr⟩ := hM
  by_contra hlt
  rw [not_le] at hlt
  apply hirr (M.erase n) (Finset.erase_ssubset hn)
  refine ⟨fun m hm => hgt m (Finset.mem_of_mem_erase hm), a, ?_⟩
  apply SimpsonBound.covers_of_covers_window (M.erase n)
    (fun m hm => by have := hgt m (Finset.mem_of_mem_erase hm); omega) a (a n + 1)
  intro z hz1 hz2
  obtain ⟨m, hm, hmz⟩ := ha z
  refine ⟨m, Finset.mem_erase.mpr ⟨?_, hm⟩, hmz⟩
  rintro rfl
  rw [Finset.card_erase_of_mem hn] at hz2
  have hd : (m : ℤ) ∣ z - a m := Int.modEq_iff_dvd.mp hmz.symm
  have h1 := Int.le_of_dvd (by omega) hd
  have h2 : ((2 : ℤ) ^ (M.card - 1)) < m := by exact_mod_cast hlt
  omega

