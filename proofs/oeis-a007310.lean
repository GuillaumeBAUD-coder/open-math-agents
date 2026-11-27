import OMAStatements.S_oeis_a007310

-- Problem: A007310: Numbers congruent to 1 or 5 mod 6.
-- Upstream: formal-conjectures statements/oeis-a007310.lean:0 (declaration OMA.S_oeis_a007310.main)
-- Credit: @sntntHb (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

namespace OMA.A007310Proof

/-- `90 * ∑_{k=1}^n k^14 = n * Q(n)` (Faulhaber), with `Q` as an integer polynomial. -/
def Q (x : ℤ) : ℤ :=
  6 * x ^ 14 + 45 * x ^ 13 + 105 * x ^ 12 - 273 * x ^ 10 + 715 * x ^ 8 - 1287 * x ^ 6
    + 1365 * x ^ 4 - 691 * x ^ 2 + 105

lemma faulhaber (n : ℕ) :
    90 * ((∑ k ∈ Finset.Icc 1 n, k ^ 14 : ℕ) : ℤ) = (n : ℤ) * Q n := by
  induction n with
  | zero => simp [Q]
  | succ m ih =>
    rw [Finset.sum_Icc_succ_top (by omega), Nat.cast_add, mul_add, ih]
    push_cast
    simp only [Q]
    ring

/-- The same polynomial over `ZMod 90`. -/
def Qz (x : ZMod 90) : ZMod 90 :=
  6 * x ^ 14 + 45 * x ^ 13 + 105 * x ^ 12 - 273 * x ^ 10 + 715 * x ^ 8 - 1287 * x ^ 6
    + 1365 * x ^ 4 - 691 * x ^ 2 + 105

set_option maxRecDepth 100000 in
lemma table : ∀ x : ZMod 90, (Qz x = 0 ↔ (x.val % 6 = 1 ∨ x.val % 6 = 5)) := by decide

lemma dvd_iff (n : ℕ) : (90 : ℤ) ∣ Q n ↔ (n % 6 = 1 ∨ n % 6 = 5) := by
  have hz := ZMod.intCast_zmod_eq_zero_iff_dvd (Q n) 90
  push_cast at hz
  rw [← hz]
  have hcast : ((Q n : ℤ) : ZMod 90) = Qz (n : ZMod 90) := by
    simp only [Q, Qz]
    push_cast
    ring
  rw [hcast, table, ZMod.val_natCast, Nat.mod_mod_of_dvd n (by norm_num : 6 ∣ 90)]

end OMA.A007310Proof

open OMA.A007310Proof in
theorem OMA.solution : type_of% @OMA.S_oeis_a007310.main := by
  intro n hn
  rw [← dvd_iff n]
  have hn' : (n : ℤ) ≠ 0 := by exact_mod_cast hn.ne'
  constructor
  · intro h
    have h90 : (90 : ℤ) * n ∣ 90 * ((∑ k ∈ Finset.Icc 1 n, k ^ 14 : ℕ) : ℤ) := by
      rw [faulhaber, mul_comm (90 : ℤ)]
      exact mul_dvd_mul_left _ h
    exact_mod_cast (mul_dvd_mul_iff_left (by norm_num : (90 : ℤ) ≠ 0)).1 h90
  · intro h
    have h1 : (n : ℤ) ∣ ((∑ k ∈ Finset.Icc 1 n, k ^ 14 : ℕ) : ℤ) := by exact_mod_cast h
    have h2 : (90 : ℤ) * n ∣ (n : ℤ) * Q n := by
      rw [← faulhaber]
      exact mul_dvd_mul_left _ h1
    rw [mul_comm (90 : ℤ)] at h2
    exact (mul_dvd_mul_iff_left hn').1 h2
