import FormalConjectures.OEIS.«86766»

/-!
The repeated block 104040 gives a composite candidate for every positive
repetition count. Mathlib's geometric-series identity yields the factorization.
-/

theorem OMA.disproof : ¬ (type_of% @OeisA86766.conjecture2) := by
  intro h
  refine h 104040 (by decide) ?_ ?_
  · intro m hm
    have lower : 10 ^ 5 < 10 ^ m := hm ▸ by decide
    have upper : 10 ^ m < 10 ^ 6 := hm ▸ by decide
    rw [Nat.pow_lt_pow_iff_right (by decide : 1 < 10)] at lower upper
    omega
  have hd : (Nat.digits 10 104040).length = 6 := by decide
  simp only [OeisA86766.a, show (104040 : ℕ) ≠ 0 by decide, if_false, hd]
  refine Nat.sInf_eq_zero.mpr (Or.inr (Set.eq_empty_iff_forall_notMem.mpr fun r ⟨hr, hp⟩ => ?_))
  let t := (1000 : ℕ) ^ r
  let s := ∑ i ∈ Finset.range r, (1000000 : ℕ) ^ i
  let c := (104040 * s) * 10 + 1
  have ht : 1000 ≤ t := Nat.pow_le_pow_right (by decide : 0 < 1000) hr
  have hg : 999999 * s + 1 = t * t := by
    dsimp [s, t]
    rw [mul_comm 999999, ← mul_pow]
    exact geom_sum_mul_add 999999 r
  have hfac : (1020 * t - 201) * (1020 * t + 201) = 999999 * c := by
    dsimp [c]; zify [show 201 ≤ 1020 * t by omega] at hg ⊢; nlinarith only [hg]
  change c.Prime at hp
  rcases hp.dvd_mul.mp (hfac.symm ▸ dvd_mul_left c 999999) with hd | hd <;>
    (have := Nat.le_of_dvd (by omega) hd; zify [show 201 ≤ 1020 * t by omega] at hfac this; nlinarith)
