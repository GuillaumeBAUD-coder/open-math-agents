import OMAReductions.R_ErdosMoser_erdos_moser_conjecture_R1
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.ZMod.Basic

/-! Reflection modulo m - 1 handles the odd-exponent case of the Erdős–Moser equation. -/

open Finset

namespace OMA.ErdosMoserOdd

lemma add_one_lt_power_three (k : ℕ) (hk : 2 ≤ k) : 1 + 2 ^ k < 3 ^ k := by
  induction k with
  | zero => omega
  | succ k ih =>
    by_cases ht : 2 ≤ k
    · specialize ih ht
      rw [pow_succ, pow_succ]
      omega
    · have he : k = 1 := by omega
      subst k
      decide

end OMA.ErdosMoserOdd

theorem OMA.solution : OMA.R_ErdosMoser_erdos_moser_conjecture_R1.H1 := by
  intro k m hk hm ho h
  have hrange : range m = insert 0 (Ico 1 m) := by
    ext i
    simp only [mem_range, mem_insert, mem_Ico]
    omega
  have hsum : (∑ i ∈ range m, i ^ k) = m ^ k := by
    rw [hrange, sum_insert (by simp), zero_pow hk.ne', zero_add]
    exact h
  let R := ZMod (m - 1)
  have hmCast : (m : R) = 1 := by
    have he : m = m - 1 + 1 := by omega
    calc
      (m : R) = ((m - 1 + 1 : ℕ) : R) := congrArg (fun n : ℕ => (n : R)) he
      _ = 1 := by
        change ((m - 1 + 1 : ℕ) : ZMod (m - 1)) = 1
        rw [Nat.cast_add, ZMod.natCast_self, zero_add, Nat.cast_one]
  have hmod : (∑ i ∈ range m, (i : R) ^ k) = 1 := by
    have he := congrArg (Nat.castRingHom R) hsum
    change Nat.castRingHom R (∑ i ∈ range m, i ^ k) = Nat.castRingHom R (m ^ k) at he
    rw [map_sum] at he
    simpa only [map_pow, Nat.coe_castRingHom, hmCast, one_pow] using he
  have hneg : (1 : R) = -1 := by
    calc
      _ = ∑ i ∈ range m, (i : R) ^ k := hmod.symm
      _ = ∑ i ∈ range m, ((m - 1 - i : ℕ) : R) ^ k :=
        (sum_range_reflect (fun i : ℕ => (i : R) ^ k) m).symm
      _ = ∑ i ∈ range m, -((i : R) ^ k) := by
        apply sum_congr rfl
        intro i hi
        have hle : i ≤ m - 1 := by have := mem_range.mp hi; omega
        change ((m - 1 - i : ℕ) : ZMod (m - 1)) ^ k =
          -((i : ZMod (m - 1)) ^ k)
        rw [Nat.cast_sub hle, ZMod.natCast_self, zero_sub, ho.neg_pow]
      _ = -1 := by rw [sum_neg_distrib, hmod]
  have htwo : (2 : R) = 0 := by
    have hc := congrArg (fun x : R => x + 1) hneg
    simpa only [one_add_one_eq_two, neg_add_cancel] using hc
  have hd : m - 1 ∣ 2 := (ZMod.natCast_eq_zero_iff 2 (m - 1)).mp (by simpa using htwo)
  have hle : m - 1 ≤ 2 := Nat.le_of_dvd (by decide) hd
  have hcases : m = 1 ∨ m = 2 ∨ m = 3 := by omega
  rcases hcases with rfl | rfl | rfl
  · simp [ErdosMoser.powerSum] at h
  · have h₁ : ErdosMoser.powerSum k 2 = 1 := by
      rw [ErdosMoser.powerSum, show Ico 1 2 = ({1} : Finset ℕ) by decide, sum_singleton, one_pow]
    have h₂ : 2 ≤ (2 : ℕ) ^ k := Nat.le_self_pow hk.ne' _
    omega
  · refine ⟨?_, rfl⟩
    have h₁ : ErdosMoser.powerSum k 3 = 1 + 2 ^ k := by
      rw [ErdosMoser.powerSum, show Ico 1 3 = ({1, 2} : Finset ℕ) by decide]
      simp
    by_contra! hn
    have h₂ := OMA.ErdosMoserOdd.add_one_lt_power_three k (by omega)
    omega
