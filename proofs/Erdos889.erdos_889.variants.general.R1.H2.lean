import OMAReductions.R_Erdos889_erdos_889_variants_general_R1
import Mathlib

/-! A prime counted by `v (n + l) k` but not by `v n (l + k)` divides some `n + i` with
`i < l + k` and `n + l + k`, so it is at most `l + k`; it exceeds `k`, since otherwise one of
the `k` numbers `n + l + i` would be a multiple of it. At most `l` primes lie in `(k, k + l]`. -/

namespace OMA.Step_Erdos889_erdos_889_variants_general_R1_H2

open Finset

/-- Some `i < p` makes `m + i` a multiple of `p`. -/
theorem exists_dvd_add (m p : ℕ) (hp : 0 < p) : ∃ i < p, p ∣ m + i := by
  have hm := Nat.div_add_mod m p
  have hr := Nat.mod_lt m hp
  rcases Nat.eq_zero_or_pos (m % p) with h0 | hpos
  · exact ⟨0, hp, ⟨m / p, by omega⟩⟩
  · refine ⟨p - m % p, by omega, ⟨m / p + 1, ?_⟩⟩
    rw [Nat.mul_add, Nat.mul_one]
    omega

theorem shift (l n k : ℕ) : Erdos889.v (n + l) k ≤ Erdos889.v n (l + k) + l := by
  unfold Erdos889.v
  rw [show n + l + k = n + (l + k) by ring]
  set N := n + (l + k) with hN
  set A := N.primeFactors.filter (fun p => ∀ i ∈ range k, ¬ p ∣ n + l + i) with hA
  set B := N.primeFactors.filter (fun p => ∀ i ∈ range (l + k), ¬ p ∣ n + i) with hB
  have hsub : A ⊆ B ∪ Ioc k (k + l) := by
    intro p hp
    rw [hA, mem_filter] at hp
    obtain ⟨hpN, hpA⟩ := hp
    have hpp := Nat.prime_of_mem_primeFactors hpN
    have hdN := Nat.dvd_of_mem_primeFactors hpN
    by_cases hpB : p ∈ B
    · exact mem_union_left _ hpB
    · apply mem_union_right
      rw [hB, mem_filter] at hpB
      push Not at hpB
      obtain ⟨i, hi, hdi⟩ := hpB hpN
      rw [mem_range] at hi
      rw [mem_Ioc]
      constructor
      · by_contra hle
        obtain ⟨j, hj, hdj⟩ := exists_dvd_add (n + l) p hpp.pos
        exact hpA j (mem_range.mpr (by omega)) hdj
      · have hsubd : p ∣ N - (n + i) := Nat.dvd_sub hdN hdi
        have hpos : 0 < N - (n + i) := by omega
        have := Nat.le_of_dvd hpos hsubd
        omega
  calc A.card ≤ (B ∪ Ioc k (k + l)).card := card_le_card hsub
    _ ≤ B.card + (Ioc k (k + l)).card := card_union_le _ _
    _ = B.card + l := by rw [Nat.card_Ioc]; congr 1; omega

end OMA.Step_Erdos889_erdos_889_variants_general_R1_H2

theorem OMA.solution : OMA.R_Erdos889_erdos_889_variants_general_R1.H2 :=
  OMA.Step_Erdos889_erdos_889_variants_general_R1_H2.shift
