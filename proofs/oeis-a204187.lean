import OMAStatements.S_oeis_a204187
import Mathlib

open OMA.S_oeis_a204187

theorem key_zmod (m : ℕ) (hm : 1 ≤ m) :
    (((∑ k ∈ Finset.Ico 1 (2 * m), k ^ (2 * m - 1) : ℕ)) : ZMod (2 * m)) =
      -((m : ZMod (2 * m)) ^ (2 * m - 1)) := by
  set e := 2 * m - 1 with he
  have he0 : e ≠ 0 := by omega
  have hodd : Odd e := ⟨m - 1, by omega⟩
  push_cast
  have hr : ∑ k ∈ Finset.range (2 * m), ((k : ZMod (2 * m))) ^ e =
      ∑ k ∈ Finset.Ico 1 (2 * m), ((k : ZMod (2 * m))) ^ e := by
    rw [Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot (by omega)]
    simp [he0]
  rw [← hr, two_mul, Finset.sum_range_add]
  have h2 : ∑ x ∈ Finset.range m, (((m + x : ℕ) : ZMod (m + m))) ^ e =
      -∑ j ∈ Finset.range m, (((j + 1 : ℕ) : ZMod (m + m))) ^ e := by
    rw [← Finset.sum_range_reflect, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun j hj => ?_
    have hj' : j < m := Finset.mem_range.mp hj
    have hc : (((m + (m - 1 - j) : ℕ)) : ZMod (m + m)) = -(((j + 1 : ℕ)) : ZMod (m + m)) := by
      rw [eq_neg_iff_add_eq_zero, ← Nat.cast_add, show m + (m - 1 - j) + (j + 1) = m + m by omega,
        ZMod.natCast_self]
    rw [hc, hodd.neg_pow]
  rw [h2]
  have h3 : ∑ j ∈ Finset.range m, (((j + 1 : ℕ) : ZMod (m + m))) ^ e =
      ∑ k ∈ Finset.range m, ((k : ZMod (m + m))) ^ e + (m : ZMod (m + m)) ^ e := by
    have a1 := Finset.sum_range_succ (fun k : ℕ => ((k : ZMod (m + m))) ^ e) m
    have a2 := Finset.sum_range_succ' (fun k : ℕ => ((k : ZMod (m + m))) ^ e) m
    simp only [Nat.cast_zero, zero_pow he0, add_zero] at a2
    rw [← a2, a1]
  rw [h3]
  ring

theorem OMA.solution : type_of% @OMA.S_oeis_a204187.main := by
  intro n hn
  rcases Nat.even_or_odd n with ⟨m, hm⟩ | hodd
  · have hm' : n = 2 * m := by omega
    subst hm'
    have m1 : 1 ≤ m := by omega
    have K := key_zmod m m1
    unfold a
    set S := ∑ k ∈ Finset.Ico 1 (2 * m), k ^ (2 * m - 1)
    rcases Nat.even_or_odd m with ⟨r, hr⟩ | hmo
    · -- m even: m^e ≡ 0
      obtain ⟨u, hu⟩ : ∃ u, m ^ (2 * m - 1) = 2 * m * u := by
        refine ⟨r * m ^ (2 * m - 3), ?_⟩
        have : 2 * m - 1 = (2 * m - 3) + 1 + 1 := by omega
        rw [this, pow_succ, pow_succ]
        generalize 2 * m - 3 = k
        subst hr
        ring
      have : ((S : ℕ) : ZMod (2 * m)) = ((0 : ℕ) : ZMod (2 * m)) := by
        rw [K, ← Nat.cast_pow, hu, Nat.cast_mul, ZMod.natCast_self]; simp
      rw [ZMod.natCast_eq_natCast_iff'] at this
      rw [this]; simp; omega
    · obtain ⟨t, ht⟩ := hmo.pow (n := 2 * m - 2)
      have hu : m ^ (2 * m - 1) = 2 * m * t + m := by
        have : 2 * m - 1 = (2 * m - 2) + 1 := by omega
        rw [this, pow_succ, ht]; ring
      have : ((S : ℕ) : ZMod (2 * m)) = ((m : ℕ) : ZMod (2 * m)) := by
        rw [K, ← Nat.cast_pow, hu, Nat.cast_add, Nat.cast_mul, ZMod.natCast_self, zero_mul,
          zero_add, neg_eq_iff_add_eq_zero, ← Nat.cast_add, ← two_mul, ZMod.natCast_self]
      rw [ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt (show m < 2 * m by omega)] at this
      rw [this]
      obtain ⟨q, hq⟩ := hmo
      omega
  · obtain ⟨q, hq⟩ := hodd
    constructor <;> intro h <;> omega
