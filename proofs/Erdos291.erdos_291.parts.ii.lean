import FormalConjectures.ErdosProblems.«291»

/-! Along the subsequence indexed by twice a positive power of three, both the
unreduced harmonic numerator and its common denominator are divisible by three. -/

open Erdos291 Finset

namespace OMA.Harmonic

lemma divides_lcm {k n : ℕ} (hk : k ∈ Icc 1 n) : k ∣ L n :=
  Finset.dvd_lcm (f := fun i : ℕ ↦ i) hk

-- For n = 2q, q a power of 3, only q and 2q can contribute modulo 3.
lemma regular_term {t k : ℕ} (hk : k ∈ Icc 1 (2 * 3 ^ t))
    (h₁ : k ≠ 3 ^ t) (h₂ : k ≠ 2 * 3 ^ t) :
    3 ∣ L (2 * 3 ^ t) / k := by
  let q := 3 ^ t
  let M := L (2 * q)
  have hq : 0 < q := by positivity
  have hqM : q ∣ M := divides_lcm (Finset.mem_Icc.mpr (by omega))
  have hkM : k ∣ M := divides_lcm hk
  change 3 ∣ M / k
  by_contra h
  have hc : Nat.Coprime q (M / k) := (Nat.prime_three.coprime_iff_not_dvd.mpr h).pow_left t
  have hd : q ∣ k :=
    hc.dvd_mul_right.mp (by simpa only [Nat.mul_div_cancel' hkM] using hqM : q ∣ k * (M / k))
  obtain ⟨j, hj⟩ := hd
  obtain ⟨hkpos, hkbound⟩ := mem_Icc.mp hk
  change k ≤ 2 * q at hkbound
  have hjle : j ≤ 2 := by nlinarith
  change k ≠ q at h₁
  change k ≠ 2 * q at h₂
  interval_cases j <;> simp_all [Nat.mul_comm]

lemma common_factor (t : ℕ) (ht : 0 < t) :
    1 < Nat.gcd (a (2 * 3 ^ t)) (L (2 * 3 ^ t)) := by
  let q := 3 ^ t
  let n := 2 * q
  let M := L n
  have hq : 0 < q := by positivity
  have hn : 0 < n := by dsimp [n]; omega
  have hqn : q ≠ n := by dsimp [n]; omega
  have hns : n ∈ Icc 1 n := mem_Icc.mpr ⟨hn, le_rfl⟩
  have hqs : q ∈ (Icc 1 n).erase n :=
    mem_erase.mpr ⟨hqn, mem_Icc.mpr (by dsimp [n]; omega)⟩
  have hnM : n ∣ M := divides_lcm hns
  have h3M : 3 ∣ M := by
    apply dvd_trans _ hnM
    exact dvd_mul_of_dvd_right (dvd_pow_self 3 (by omega : t ≠ 0)) 2
  have hreg : 3 ∣ ∑ k ∈ ((Icc 1 n).erase n).erase q, M / k := by
    apply Finset.dvd_sum
    intro k hk
    obtain ⟨hkq, hk⟩ := mem_erase.mp hk
    obtain ⟨hkn, hk⟩ := mem_erase.mp hk
    exact regular_term hk hkq hkn
  have hpair : 3 ∣ M / n + M / q := by
    obtain ⟨u, hu⟩ := hnM
    rw [hu]
    have heq : n * u = q * (2 * u) := by dsimp [n]; ring
    rw [Nat.mul_div_cancel_left _ hn, heq, Nat.mul_div_cancel_left _ hq]
    exact ⟨u, by omega⟩
  have h3a : 3 ∣ a n := by
    change 3 ∣ ∑ k ∈ Icc 1 n, M / k
    rw [← Finset.add_sum_erase _ _ hns, ← Finset.add_sum_erase _ _ hqs, ← add_assoc]
    exact dvd_add hpair hreg
  have hM : M ≠ 0 := by
    apply Finset.lcm_ne_zero_iff.mpr
    intro k hk
    exact Nat.ne_of_gt (mem_Icc.mp hk).1
  have hg := Nat.gcd_pos_of_pos_right (a n) (Nat.pos_of_ne_zero hM)
  exact lt_of_lt_of_le (by decide : 1 < 3) (Nat.le_of_dvd hg (Nat.dvd_gcd h3a h3M))

end OMA.Harmonic

theorem OMA.solution : type_of% @Erdos291.erdos_291.parts.ii := by
  apply Set.infinite_of_forall_exists_gt
  intro b
  have hb : b < 3 ^ b := Nat.lt_pow_self (by decide)
  refine ⟨2 * 3 ^ (b + 1), OMA.Harmonic.common_factor _ (by omega), ?_⟩
  rw [pow_succ]
  omega
