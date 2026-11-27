import FormalConjectures.ErdosProblems.«392»

/-!
# Reduction of Erdős Problem 392 (variant with factors at most n)

Reduction `Erdos392.erdos_392.variants.lower.R1` by `@senamakel`. A known result: the least number
of factors in a factorisation of `n!` into factors at most `n` is `n - n / log n + o(n / log n)`.
The two halves of the asymptotic are split off, both stated on explicit factorisations of `n!`:
- `H1` (lower half): any factorisation of `n!` into factors at most `n` has at least
  `n - n / log n` factors, for `n ≥ 2`. This follows from `log n! ≥ n log n - n`.
- `H2` (upper half, the packing construction): for every `ε > 0` and all large `n`, there is a
  monotone factorisation of `n!` into factors at most `n` with at most
  `n - n / log n + ε n / log n` factors. This needs prime counts of PNT strength.
- `main` combines them with the minimality of `A n`.
-/

open Filter
open scoped Nat

namespace OMA.R_Erdos392_erdos_392_variants_lower_R1

-- Lower half: every factorisation of n! into factors at most n has at least n - n / log n factors.
def H1 : Prop :=
  ∀ n : ℕ, 2 ≤ n → ∀ (t : ℕ) (a : Fin (t + 1) → ℕ), (n)! = ∏ i, a i → (∀ i, a i ≤ n) →
    (n : ℝ) - n / Real.log n ≤ t + 1

-- Upper half: for all large n there is a monotone factorisation of n! into factors at most n
-- with at most n - n / log n + ε n / log n factors.
def H2 : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop, ∃ (t : ℕ) (a : Fin (t + 1) → ℕ),
    (n)! = ∏ i, a i ∧ Monotone a ∧ a (Fin.last t) ≤ n ∧
    (t + 1 : ℝ) ≤ n - n / Real.log n + ε * (n / Real.log n)

theorem main : H1 → H2 → type_of% @Erdos392.erdos_392.variants.lower := by
  intro h1 h2 A hA
  refine Asymptotics.IsLittleO.of_bound fun ε hε => ?_
  filter_upwards [h2 ε hε, eventually_ge_atTop 2] with n hn hn2
  obtain ⟨t', a', hprod', hmono', hlast', hle'⟩ := hn
  have hmem := (hA n (by omega)).1
  have hlow := (hA n (by omega)).2
  obtain ⟨t, ⟨a, hprod, hmono, hlast⟩, hAt⟩ := hmem
  have hA1 : A n ≤ t' + 1 := hlow ⟨t', ⟨a', hprod', hmono', hlast'⟩, rfl⟩
  have hbound : ∀ i, a i ≤ n := fun i => (hmono (Fin.le_last i)).trans hlast
  have hL := h1 n hn2 t a hprod hbound
  have hAt' : (A n : ℝ) = t + 1 := by rw [← hAt]; push_cast; ring
  have hA1' : (A n : ℝ) ≤ t' + 1 := by exact_mod_cast hA1
  have hpos : 0 ≤ (n : ℝ) / Real.log n :=
    div_nonneg (Nat.cast_nonneg _) (Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ n)))
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hpos,
    abs_of_nonneg (by linarith)]
  linarith

end OMA.R_Erdos392_erdos_392_variants_lower_R1
