import OMAReductions.R_Erdos1052_erdos_1052_R2_H1_R1
import Mathlib

/-!
Prime-power GCD factorization decomposition of the seed contribution to the repeated odd core
in Erdos problem 1052.
-/

namespace OMA.R_Erdos1052_erdos_1052_R2_H1_R1_H1_R1

/-- Uniform bound on the number of repeated odd prime factors dividing 2 ^ v2(n) + 1. -/
def H1 : Prop :=
  ∃ K : ℕ, ∀ n : ℕ, Erdos1052.IsUnitaryPerfect n →
    let S := n.primeFactors.filter (fun p => p ≠ 2 ∧ n.factorization p = 1)
    let R := n.primeFactors.filter (fun p => p ≠ 2 ∧ n.factorization p ≠ 1)
    4 ≤ S.card → (R.filter (fun p => p ∣ 2 ^ n.factorization 2 + 1)).card ≤ K

/-- Uniform bound on each prime-power factor shared by the repeated odd core and 2 ^ v2(n) + 1. -/
def H2 : Prop :=
  ∃ M : ℕ, ∀ n : ℕ, Erdos1052.IsUnitaryPerfect n →
    let S := n.primeFactors.filter (fun p => p ≠ 2 ∧ n.factorization p = 1)
    let R := n.primeFactors.filter (fun p => p ≠ 2 ∧ n.factorization p ≠ 1)
    4 ≤ S.card → ∀ p ∈ R, p ∣ 2 ^ n.factorization 2 + 1 →
      p ^ min (n.factorization p) ((2 ^ n.factorization 2 + 1).factorization p) ≤ M

/-- Deduction of the uniform gcd bound from the support-size and prime-power bounds. -/
theorem main : H1 → H2 → OMA.R_Erdos1052_erdos_1052_R2_H1_R1.H1 := by
  intro h1 h2
  obtain ⟨K, hK⟩ := h1
  obtain ⟨M, hM⟩ := h2
  refine ⟨(M + 1) ^ K, fun n hn => ?_⟩
  dsimp only
  intro hS4
  set R := n.primeFactors.filter (fun p => p ≠ 2 ∧ n.factorization p ≠ 1)
  set c := ∏ p ∈ R, p ^ n.factorization p
  set m := 2 ^ n.factorization 2 + 1
  set g := Nat.gcd c m
  set D := R.filter (fun p => p ∣ m)
  have hR : R ⊆ n.primeFactors := Finset.filter_subset _ _
  have hc0 : c ≠ 0 := OMA.R_Erdos1052_erdos_1052_R2.ppart_ne_zero hR
  have hm0 : m ≠ 0 := by positivity
  have hg0 : g ≠ 0 := Nat.gcd_ne_zero_left hc0
  have hsub : g.primeFactors ⊆ D := by
    intro p hp
    have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
    have hpg : p ∣ g := Nat.dvd_of_mem_primeFactors hp
    have hpc : p ∣ c := hpg.trans (Nat.gcd_dvd_left c m)
    have hpm : p ∣ m := hpg.trans (Nat.gcd_dvd_right c m)
    have hpR : p ∈ R := by
      rw [← OMA.R_Erdos1052_erdos_1052_R2.primeFactors_ppart hR]
      exact Nat.mem_primeFactors.mpr ⟨hpp, hpc, hc0⟩
    exact Finset.mem_filter.mpr ⟨hpR, hpm⟩
  have hfac_bound : ∀ p ∈ g.primeFactors, p ^ g.factorization p ≤ M + 1 := by
    intro p hp
    have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
    obtain ⟨hpR, hpm⟩ := Finset.mem_filter.mp (hsub hp)
    have hle_c : g.factorization p ≤ c.factorization p :=
      (Nat.factorization_le_iff_dvd hg0 hc0).mpr (Nat.gcd_dvd_left c m) p
    have hle_m : g.factorization p ≤ m.factorization p :=
      (Nat.factorization_le_iff_dvd hg0 hm0).mpr (Nat.gcd_dvd_right c m) p
    have hc_eq : c.factorization p = n.factorization p := by
      rw [OMA.R_Erdos1052_erdos_1052_R2.factorization_ppart hR p, if_pos hpR]
    have hle_min : g.factorization p ≤ min (n.factorization p) (m.factorization p) :=
      le_min (hc_eq ▸ hle_c) hle_m
    have hpow : p ^ g.factorization p ≤ p ^ min (n.factorization p) (m.factorization p) :=
      Nat.pow_le_pow_right hpp.pos hle_min
    exact (hpow.trans (hM n hn hS4 p hpR hpm)).trans (Nat.le_succ M)
  have hcard : g.primeFactors.card ≤ K :=
    (Finset.card_le_card hsub).trans (hK n hn hS4)
  calc g
      = ∏ p ∈ g.primeFactors, p ^ g.factorization p :=
        (OMA.R_Erdos1052_erdos_1052_R2.prod_primeFactors_pow_self hg0).symm
    _ ≤ ∏ _p ∈ g.primeFactors, (M + 1) :=
        Finset.prod_le_prod (fun _ _ => Nat.zero_le _) hfac_bound
    _ = (M + 1) ^ g.primeFactors.card := Finset.prod_const (M + 1)
    _ ≤ (M + 1) ^ K := Nat.pow_le_pow_right (by omega) hcard

end OMA.R_Erdos1052_erdos_1052_R2_H1_R1_H1_R1
