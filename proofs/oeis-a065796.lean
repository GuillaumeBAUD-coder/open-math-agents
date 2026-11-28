import OMAStatements.S_oeis_a065796
import Mathlib

namespace A065796

open OMA.S_oeis_a065796 in
lemma alt_mod (l : List ℕ) : (11 : ℤ) ∣ ((Nat.ofDigits 10 l : ℕ) : ℤ) - alternatingSum l := by
  induction l with
  | nil => simp [alternatingSum]
  | cons d ds ih =>
    obtain ⟨c, hc⟩ := ih
    refine ⟨((Nat.ofDigits 10 ds : ℕ) : ℤ) - c, ?_⟩
    rw [Nat.ofDigits_cons, alternatingSum]
    simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
    linarith

lemma sq_mod (n : ℕ) : n ^ 2 % 11 ≠ 2 := by
  rw [Nat.pow_mod]
  have h : n % 11 < 11 := Nat.mod_lt _ (by norm_num)
  generalize n % 11 = r at h
  interval_cases r <;> norm_num

end A065796

theorem OMA.solution : type_of% @OMA.S_oeis_a065796.main := by
  apply Set.infinite_of_injective_forall_mem (f := fun t : ℕ => (11 * (t : ℤ) + 2))
  · intro s t h
    simp only at h
    omega
  · intro t n _ hz
    have h := A065796.alt_mod (Nat.digits 10 (n ^ 2))
    rw [Nat.ofDigits_digits] at h
    have ha : OMA.S_oeis_a065796.a n = 11 * (t : ℤ) + 2 := hz
    unfold OMA.S_oeis_a065796.a at ha
    rw [ha] at h
    have hs := A065796.sq_mod n
    obtain ⟨c, hc⟩ := h
    generalize n ^ 2 = N at hc hs
    omega
