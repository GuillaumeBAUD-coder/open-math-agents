import OMAStatements.S_oeis_a184894

namespace OMA.A184894Proof

open Polynomial OMA.S_oeis_a184894

noncomputable def b (m d : ℕ) : ZMod 3 :=
  ((iteratePoly m).map (Nat.castRingHom (ZMod 3))).coeff d

lemma step (m d : ℕ) : b (m+1) d = b m d + if 3 ∣ d then b m (d/3) else 0 := by
  simp only [b, iteratePoly, Polynomial.map_add, Polynomial.map_pow, coeff_add]
  rw [← ZMod.expand_card, Polynomial.coeff_expand (by decide : 0 < 3)]

lemma off_powers (m d : ℕ) (h : ∀ j : ℕ, d ≠ 3^j) : b m d = 0 := by
  induction m generalizing d with
  | zero =>
    have h1 : d ≠ 1 := by simpa using h 0
    simp [b, iteratePoly, Polynomial.coeff_X, Ne.symm h1]
  | succ m ih =>
    rw [step, ih d h, zero_add]
    split_ifs with hd
    · apply ih
      intro j hj
      apply h (j+1)
      rw [pow_succ, ← hj, Nat.div_mul_cancel hd]
    · rfl

lemma at_power (m j : ℕ) : b m (3^j) = (m.choose j : ZMod 3) := by
  induction m generalizing j with
  | zero =>
    cases j with
    | zero => simp [b, iteratePoly]
    | succ j =>
      have h : (3 : ℕ)^(j+1) ≠ 1 := by
        have hp : 0 < (3 : ℕ)^j := by positivity
        rw [pow_succ]
        omega
      simp [b, iteratePoly, Polynomial.coeff_X, Ne.symm h, Nat.choose_eq_zero_of_lt]
  | succ m ih =>
    cases j with
    | zero => simp [step, show b m 1 = 1 by simpa using ih 0]
    | succ j =>
      rw [step, if_pos (by simp [pow_succ]), pow_succ, Nat.mul_div_cancel _ (by decide : 0 < 3)]
      rw [← pow_succ, ih, ih, Nat.choose_succ_succ, Nat.cast_add, add_comm]

lemma residue (m : ℕ) : (term m : ZMod 3) = b m (2*m-1) := by simp [term,b]

end OMA.A184894Proof

open OMA.S_oeis_a184894 OMA.A184894Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a184894.main := by
  have exceptions (j : ℕ) :
      (term ((3^j+1)/2) : ZMod 3) = ((((3^j+1)/2 : ℕ).choose j) : ZMod 3) := by
    have hodd : Odd (3^j : ℕ) := (by decide : Odd (3 : ℕ)).pow
    obtain ⟨a, ha⟩ := hodd
    rw [residue, show 2*((3^j+1)/2)-1 = 3^j by omega, at_power]
  refine ⟨?_, exceptions, ?_⟩
  · intro m hm h
    by_contra! hc
    have hz := off_powers m (2*m-1) (fun j hj => hc j (by omega))
    exact h ((ZMod.natCast_eq_zero_iff _ _).mp ((residue m).trans hz))
  · apply (ZMod.natCast_eq_zero_iff _ _).mp
    have he := exceptions 6
    change (term 365 : ZMod 3) = (Nat.choose 365 6 : ZMod 3) at he
    rw [he]
    have hv := Nat.descFactorial_eq_factorial_mul_choose 365 6
    norm_num [Nat.descFactorial, Nat.factorial] at hv
    have hc : Nat.choose 365 6 = 3151277509380 := by omega
    rw [hc, ZMod.natCast_eq_zero_iff]
    decide
