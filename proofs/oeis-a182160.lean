import OMAStatements.S_oeis_a182160

open OMA.S_oeis_a182160

namespace OMA.A182160

/-- A decimal digit contributes at most 9^e to the next value. -/
lemma step_bound (e x : ℕ) :
    digitPowerSum e x ≤ (Nat.digits 10 x).length * 9 ^ e := by
  let powers := (Nat.digits 10 x).map (fun digit => digit ^ e)
  have bound : ∀ y ∈ powers, y ≤ 9 ^ e := by
    intro y hy
    obtain ⟨digit, hd, rfl⟩ := List.mem_map.mp hy
    have h := Nat.digits_lt_base (by decide : 1 < 10) hd
    exact Nat.pow_le_pow_left (by omega) e
  simpa [powers, digitPowerSum, nsmul_eq_mul] using List.sum_le_card_nsmul powers (9 ^ e) bound

end OMA.A182160

theorem OMA.solution : type_of% @OMA.S_oeis_a182160.main := by
  intro e _ start
  -- Every iterate will fit in D digits, including the starting value.
  let D := max (Nat.digits 10 start).length (9 ^ e)
  have digitBound : 9 ^ e ≤ D := le_max_right _ _
  have capacity : D * D < 10 ^ D := calc
    D * D < 2 ^ D * 2 ^ D := Nat.mul_lt_mul_of_lt_of_lt Nat.lt_two_pow_self Nat.lt_two_pow_self
    _ = (2 * 2) ^ D := (mul_pow 2 2 D).symm
    _ ≤ 10 ^ D := Nat.pow_le_pow_left (by decide) D
  have bounded : ∀ i : ℕ, (digitPowerSum e)^[i] start < 10 ^ D := by
    intro i
    induction i with
    | zero => exact (Nat.digits_length_le_iff (by decide) start).mp (le_max_left _ _)
    | succ i ih =>
      rw [Function.iterate_succ_apply']
      have lengthBound := (Nat.digits_length_le_iff (by decide : 1 < 10) _).mpr ih
      exact lt_of_le_of_lt ((OMA.A182160.step_bound e _).trans
        (Nat.mul_le_mul lengthBound digitBound)) capacity
  exact (Set.finite_Iio (10 ^ D)).exists_lt_map_eq_of_forall_mem
    (f := fun i : ℕ => (digitPowerSum e)^[i] start) bounded
