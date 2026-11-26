import FormalConjectures.OEIS.«193279»

/-!
# Subset sums of proper divisors of an even perfect number

For n = 2^k p with p = 2^(k+1)-1, write each m < n as p*q + r.
The binary expansions of r and q use disjoint blocks of proper divisors.
The three lemmas establishing Euler's factorisation below are adapted from
Mathlib's Archive/Wiedijk100Theorems/PerfectNumbers.lean, copyright 2020
Aaron Anderson, licensed under Apache 2.0.
-/

namespace OMA.PerfectSubsets

open Nat ArithmeticFunction Finset
open scoped sigma

private theorem sigma_two_pow_eq_mersenne_succ (k : ℕ) : σ 1 (2 ^ k) = mersenne (k + 1) := by
  simp_rw [sigma_one_apply, mersenne, ← one_add_one_eq_two, ← geom_sum_mul_add 1 (k + 1)]
  norm_num

private theorem eq_two_pow_mul_odd {n : ℕ} (hpos : 0 < n) : ∃ k m : ℕ, n = 2 ^ k * m ∧ ¬Even m := by
  have h := Nat.finiteMultiplicity_iff.2 ⟨Nat.prime_two.ne_one, hpos⟩
  obtain ⟨m, hm⟩ := pow_multiplicity_dvd 2 n
  use multiplicity 2 n, m
  refine ⟨hm, ?_⟩
  rw [even_iff_two_dvd]
  have hg := h.not_pow_dvd_of_multiplicity_lt (Nat.lt_succ_self _)
  contrapose hg
  rcases hg with ⟨k, rfl⟩
  apply Dvd.intro k
  rw [pow_succ, mul_assoc, ← hm]

private theorem eq_two_pow_mul_prime_mersenne_of_even_perfect {n : ℕ} (ev : Even n) (perf : Nat.Perfect n) :
    ∃ k : ℕ, Nat.Prime (mersenne (k + 1)) ∧ n = 2 ^ k * mersenne (k + 1) := by
  have hpos := perf.2
  rcases eq_two_pow_mul_odd hpos with ⟨k, m, rfl, hm⟩
  use k
  rw [even_iff_two_dvd] at hm
  rw [Nat.perfect_iff_sum_divisors_eq_two_mul hpos, ← sigma_one_apply,
    isMultiplicative_sigma.map_mul_of_coprime (Nat.prime_two.coprime_pow_of_not_dvd hm).symm,
    sigma_two_pow_eq_mersenne_succ, ← mul_assoc, ← pow_succ'] at perf
  obtain ⟨j, rfl⟩ := ((Odd.coprime_two_right (by simp)).pow_right _).dvd_of_dvd_mul_left
    (Dvd.intro _ perf)
  rw [← mul_assoc, mul_comm _ (mersenne _), mul_assoc] at perf
  have h := mul_left_cancel₀ (by positivity) perf
  rw [sigma_one_apply, Nat.sum_divisors_eq_sum_properDivisors_add_self, ← succ_mersenne, add_mul,
    one_mul, add_comm] at h
  have hj := add_left_cancel h
  cases Nat.sum_properDivisors_dvd (by rw [hj]; apply Dvd.intro_left (mersenne (k + 1)) rfl) with
  | inl h_1 =>
    have j1 : j = 1 := Eq.trans hj.symm h_1
    rw [j1, mul_one, Nat.sum_properDivisors_eq_one_iff_prime] at h_1
    simp [h_1, j1]
  | inr h_1 =>
    have jcon := Eq.trans hj.symm h_1
    rw [← one_mul j, ← mul_assoc, mul_one] at jcon
    have jcon2 := mul_right_cancel₀ ?_ jcon
    · exfalso
      match k with
      | 0 =>
        apply hm
        rw [← jcon2, pow_zero, one_mul, one_mul] at ev
        rw [← jcon2, one_mul]
        exact even_iff_two_dvd.mp ev
      | .succ k =>
        apply _root_.ne_of_lt _ jcon2
        rw [mersenne, ← Nat.pred_eq_sub_one, Nat.lt_pred_iff, ← pow_one (Nat.succ 1)]
        apply pow_lt_pow_right₀ (Nat.lt_succ_self 1) (Nat.succ_lt_succ k.succ_pos)
    contrapose hm
    simp [hm]

private lemma scaled_binary (c : ℕ) (hc : 0 < c) (k : ℕ) :
    ∀ x < 2 ^ k, ∃ s : Finset ℕ,
      (∀ a ∈ s, ∃ i < k, a = c * 2 ^ i) ∧ ∑ a ∈ s, a = c * x := by
  induction k with
  | zero =>
    intro x hx
    have : x = 0 := by simpa using hx
    subst x
    exact ⟨∅, by simp, by simp⟩
  | succ k ih =>
    intro x hx
    by_cases h : x < 2 ^ k
    · obtain ⟨s, hs, hsum⟩ := ih x h
      refine ⟨s, ?_, hsum⟩
      intro a ha
      obtain ⟨i, hi, rfl⟩ := hs a ha
      exact ⟨i, by omega, rfl⟩
    · have hrem : x - 2 ^ k < 2 ^ k := by rw [pow_succ] at hx; omega
      obtain ⟨s, hs, hsum⟩ := ih _ hrem
      have fresh : c * 2 ^ k ∉ s := by
        intro hmem
        obtain ⟨i, hi, heq⟩ := hs _ hmem
        have hlt : c * 2 ^ i < c * 2 ^ k :=
          Nat.mul_lt_mul_of_pos_left (pow_lt_pow_right₀ (by decide : 1 < (2 : ℕ)) hi) hc
        omega
      refine ⟨insert (c * 2 ^ k) s, ?_, ?_⟩
      · intro a ha
        rcases Finset.mem_insert.mp ha with rfl | ha
        · exact ⟨k, by omega, rfl⟩
        · obtain ⟨i, hi, rfl⟩ := hs a ha
          exact ⟨i, by omega, rfl⟩
      · rw [Finset.sum_insert fresh, hsum, ← Nat.mul_add]
        congr 1
        omega

private lemma covers_below (k p : ℕ) (hgap : 2 ^ k < p) (hsize : p ≤ 2 ^ (k+1))
    (m : ℕ) (hm : m < 2 ^ k * p) :
    ∃ s ⊆ (2 ^ k * p).properDivisors, ∑ a ∈ s, a = m := by
  have hp : 0 < p := (by positivity : 0 < 2 ^ k).trans hgap
  obtain ⟨s, hs, hsum⟩ := scaled_binary 1 (by decide) (k+1) (m % p)
    ((Nat.mod_lt _ hp).trans_le hsize)
  obtain ⟨t, ht, htsum⟩ := scaled_binary p hp k (m / p)
    ((Nat.div_lt_iff_lt_mul hp).mpr hm)
  have small : ∀ a ∈ s, a ∣ 2 ^ k ∧ a ≤ 2 ^ k := by
    intro a ha
    obtain ⟨i, hi, h⟩ := hs a ha
    rw [one_mul] at h
    subst a
    exact ⟨pow_dvd_pow _ (by omega), Nat.pow_le_pow_right (by decide) (by omega)⟩
  have disj : Disjoint s t := by
    apply Finset.disjoint_left.mpr
    intro a ha hb
    obtain ⟨i, _, rfl⟩ := ht a hb
    have hsmall := (small _ ha).2
    have hlarge : p ≤ p * 2 ^ i := Nat.le_mul_of_pos_right _ (by positivity)
    omega
  refine ⟨s ∪ t, ?_, ?_⟩
  · intro a ha
    apply Nat.mem_properDivisors.mpr
    rcases Finset.mem_union.mp ha with ha | ha
    · obtain ⟨hd, hle⟩ := small _ ha
      have hp_le : p ≤ 2 ^ k * p := Nat.le_mul_of_pos_left _ (by positivity)
      exact ⟨dvd_mul_of_dvd_left hd p, (hle.trans_lt hgap).trans_le hp_le⟩
    · obtain ⟨i, hi, rfl⟩ := ht a ha
      rw [Nat.mul_comm p]
      exact ⟨mul_dvd_mul_right (pow_dvd_pow 2 hi.le) p,
        Nat.mul_lt_mul_of_pos_right (pow_lt_pow_right₀ (by decide : 1 < (2 : ℕ)) hi) hp⟩
  · rw [Finset.sum_union disj, hsum, htsum, one_mul, Nat.mod_add_div]

end OMA.PerfectSubsets

open Finset OMA.PerfectSubsets in
theorem OMA.solution : type_of% @OeisA193279.a_eq_self_of_perfect_of_even := by
  intro n hperf heven
  have htotal := (Nat.perfect_iff_sum_properDivisors hperf.2).mp hperf
  have hallsums : n.properDivisors.powerset.image (fun s : Finset ℕ => ∑ a ∈ s, a) =
      range (n + 1) := by
    ext m
    simp only [mem_image, mem_powerset, mem_range]
    constructor
    · rintro ⟨s, hs, rfl⟩
      have hle := Finset.sum_le_sum_of_subset hs (f := fun i : ℕ => i)
      omega
    · intro hm
      by_cases h : m = n
      · exact ⟨n.properDivisors, Finset.Subset.rfl, htotal.trans h.symm⟩
      · obtain ⟨k, hp, rfl⟩ := eq_two_pow_mul_prime_mersenne_of_even_perfect heven hperf
        apply covers_below k (mersenne (k+1)) _ _ m (by omega)
        · have hk : k ≠ 0 := by
            rintro rfl
            norm_num [mersenne] at hp
          have hkpow : 1 < (2 : ℕ) ^ k := one_lt_pow₀ (by decide) hk
          simp only [mersenne, pow_succ]
          omega
        · simp [mersenne]
  simp [OeisA193279.a, hallsums]
