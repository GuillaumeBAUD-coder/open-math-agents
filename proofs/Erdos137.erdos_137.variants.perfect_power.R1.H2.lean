import OMAReductions.R_Erdos137_erdos_137_variants_perfect_power_R1
import Mathlib.NumberTheory.Bertrand

/-! A Bertrand prime above half the upper endpoint occurs only once in the product. -/

open Finset

theorem OMA.solution : OMA.R_Erdos137_erdos_137_variants_perfect_power_R1.H2 := by
  intro k n hk hNoLargePrime
  obtain ⟨p, hp, hlo, hhi⟩ := Nat.bertrand ((n + k) / 2) (by omega)
  have hpN : p ≤ n + k := by omega
  have hpk : p < k := lt_of_not_ge fun h => hNoLargePrime ⟨p, h, hpN, hp⟩
  have hnp : n < p := by omega
  have hUnique (m : ℕ) (hm : m ∈ Ioc n (n + k)) (hmp : m ≠ p) : ¬ p ∣ m := by
    obtain ⟨hm1, hm2⟩ := Finset.mem_Ioc.mp hm
    rintro ⟨t, rfl⟩
    have ht : 2 ≤ t := by
      by_contra! h
      interval_cases t <;> simp_all
    have ht' := Nat.mul_le_mul_left p ht
    omega
  refine ⟨p, hp, ?_⟩
  calc
    _ = ∑ m ∈ Ioc n (n + k), m.factorization p :=
      Nat.factorization_prod_apply fun m hm => by
        have h := (Finset.mem_Ioc.mp hm).1
        omega
    _ = p.factorization p := Finset.sum_eq_single_of_mem p (Finset.mem_Ioc.mpr ⟨hnp, hpN⟩)
      fun m hm hne => Nat.factorization_eq_zero_of_not_dvd (hUnique m hm hne)
    _ = 1 := by simp [hp.factorization]
