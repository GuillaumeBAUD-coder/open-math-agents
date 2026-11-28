import OMAStatements.S_oeis_a014442
import Mathlib

theorem OMA.solution : type_of% @OMA.S_oeis_a014442.main := by
  intro p hp hp4
  have hfact : Fact p.Prime := Fact.mk hp
  have hsq : IsSquare (-1 : ZMod p) := ZMod.exists_sq_eq_neg_one_iff.mpr (by omega)
  obtain ⟨y, hy⟩ := hsq
  have hdvd : p ∣ y.val ^ 2 + 1 := by
    rw [← ZMod.natCast_eq_zero_iff]
    push_cast
    rw [ZMod.natCast_zmod_val, pow_two, ← hy]
    ring
  have hlt : y.val + 1 ≤ p := Nat.succ_le_of_lt (ZMod.val_lt y)
  have hpos : 1 ≤ y.val := by
    by_contra h0
    have h0' : y.val = 0 := by omega
    rw [h0'] at hdvd
    have h1 : p ∣ 1 := by simpa using hdvd
    have h2 := Nat.le_of_dvd Nat.one_pos h1
    have h3 := hp.two_le
    omega
  refine ⟨y.val, hpos, hdvd, ?_⟩
  intro q hq
  rw [Nat.mem_primeFactors] at hq
  obtain ⟨hqp, hqd, _⟩ := hq
  obtain ⟨m, hm⟩ := hdvd
  have hsqle : (y.val + 1) * (y.val + 1) ≤ p * p := Nat.mul_le_mul hlt hlt
  have hbound : y.val ^ 2 + 1 < p * p := by nlinarith
  have hm_lt : m < p := by
    by_contra h
    have h' : p ≤ m := by omega
    have h2 : p * p ≤ p * m := Nat.mul_le_mul_left p h'
    omega
  have hm_pos : 0 < m := by
    rcases Nat.eq_zero_or_pos m with h | h
    · rw [h, mul_zero] at hm
      omega
    · exact h
  rw [hm] at hqd
  rcases (Nat.Prime.dvd_mul hqp).mp hqd with h | h
  · exact Nat.le_of_dvd hp.pos h
  · exact (Nat.le_of_dvd hm_pos h).trans hm_lt.le
