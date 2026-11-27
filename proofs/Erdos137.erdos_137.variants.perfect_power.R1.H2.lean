import OMAReductions.R_Erdos137_erdos_137_variants_perfect_power_R1
import Mathlib.NumberTheory.Bertrand

open Finset

theorem OMA.solution : OMA.R_Erdos137_erdos_137_variants_perfect_power_R1.H2 := by
  intro k n hk hNoPrime
  have hShort : n < k - 1 := by
    by_contra! hn
    obtain ⟨q, hq, hqLower, hqUpper⟩ := Nat.bertrand (k - 1) (by omega)
    exact hNoPrime ⟨q, by omega, by omega, hq⟩
  obtain ⟨p, hp, hpHalf, hpUpper⟩ := Nat.bertrand ((n + k) / 2) (by omega)
  have hMem : p ∈ Ioc n (n + k) := mem_Ioc.mpr ⟨by omega, by omega⟩
  have hLarge : n + k < 2 * p := by omega
  have hNonzero : ∀ m ∈ Ioc n (n + k), m ≠ 0 := by
    intro m hm
    have hLower := (mem_Ioc.mp hm).1
    omega
  refine ⟨p, hp, ?_⟩
  rw [Nat.factorization_prod hNonzero, Finsupp.finsetSum_apply, Finset.sum_eq_single p]
  · exact hp.factorization_self
  · intro m hm hne
    apply Nat.factorization_eq_zero_of_not_dvd
    rintro ⟨a, ha⟩
    have hUpper := (mem_Ioc.mp hm).2
    have hSmall : a < 2 := by
      by_contra! hTwo
      have hMul := Nat.mul_le_mul_left p hTwo
      omega
    rcases (show a = 0 ∨ a = 1 by omega) with rfl | rfl
    · exact hNonzero m hm (by simpa using ha)
    · exact hne (by simpa using ha)
  · intro hMissing
    exact (hMissing hMem).elim
