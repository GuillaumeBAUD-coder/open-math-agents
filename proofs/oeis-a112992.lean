import OMAStatements.S_oeis_a112992
import Mathlib.Tactic

/-!
The Jacobsthal recurrence gives 3*J(e) = 2^e - (-1)^e.
Taking the ceiling of 2^e/3 therefore adds one exactly when e is
even. Every positive-index Jacobsthal term is odd.
-/
-- Credit: @dk8827

namespace OMA.A112992

open OMA.S_oeis_a112992

private theorem jacobsthal_formula (e : ℕ) :
    3 * (J e : ℤ) = (2 : ℤ) ^ e - (-1) ^ e := by
  induction e using Nat.twoStepInduction with
  | zero => decide
  | one => decide
  | more e h0 h1 =>
    rw [J, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, pow_succ (2 : ℤ) (e + 1),
      pow_succ (-1 : ℤ) (e + 1)]
    rw [pow_succ (2 : ℤ) e, pow_succ (-1 : ℤ) e] at h1 ⊢
    linear_combination h1 + 2 * h0

private theorem odd_jacobsthal (e : ℕ) : Odd (J (e + 1) : ℤ) := by
  induction e with
  | zero => decide
  | succ e ih =>
    rw [J, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
    obtain ⟨r, hr⟩ := ih
    exact ⟨r + J e, by omega⟩

private theorem ceiling_formula (e : ℕ) :
    ⌈(2 : ℚ) ^ e / 3⌉ = (J e : ℤ) + (if Even e then 1 else 0) := by
  have h : 3 * (J e : ℚ) = (2 : ℚ) ^ e - (-1) ^ e := by
    exact_mod_cast jacobsthal_formula e
  rcases Nat.even_or_odd e with he | ho
  · rw [if_pos he]
    rw [he.neg_one_pow] at h
    apply Int.ceil_eq_iff.mpr
    push_cast
    exact ⟨(lt_div_iff₀ (by norm_num)).mpr (by linarith),
      (div_le_iff₀ (by norm_num)).mpr (by linarith)⟩
  · rw [if_neg (Nat.not_even_iff_odd.mpr ho), add_zero]
    rw [ho.neg_one_pow] at h
    apply Int.ceil_eq_iff.mpr
    push_cast
    exact ⟨(lt_div_iff₀ (by norm_num)).mpr (by linarith),
      (div_le_iff₀ (by norm_num)).mpr (by linarith)⟩

theorem solution_aux (k : ℕ) :
    (Odd (c k) → ∃ j : ℕ, c k = (J j : ℤ)) ∧
    (Even (c k) → ∃ j : ℕ, c k = (J j : ℤ) + 1) := by
  let e := 2 ^ k % k
  have hc : c k = (J e : ℤ) + (if Even e then 1 else 0) := ceiling_formula e
  rw [hc]
  by_cases hz : e = 0
  · rw [hz, show (J 0 : ℤ) + (if Even (0 : ℕ) then 1 else 0) = 1 by decide]
    exact ⟨fun _ => ⟨1, rfl⟩, fun h => ((by decide : ¬ Even (1 : ℤ)) h).elim⟩
  · obtain ⟨j, hj⟩ := Nat.exists_eq_succ_of_ne_zero hz
    have ho : Odd (J e : ℤ) := by rw [hj]; exact odd_jacobsthal j
    by_cases he : Even e
    · rw [if_pos he]
      have heven : Even ((J e : ℤ) + 1) := ho.add_odd odd_one
      exact ⟨fun h => (Int.not_odd_iff_even.mpr heven h).elim, fun _ => ⟨e, rfl⟩⟩
    · rw [if_neg he, add_zero]
      exact ⟨fun _ => ⟨e, rfl⟩, fun h => (Int.not_even_iff_odd.mpr ho h).elim⟩

end OMA.A112992

theorem OMA.solution : type_of% @OMA.S_oeis_a112992.main :=
  fun k _ => OMA.A112992.solution_aux k
