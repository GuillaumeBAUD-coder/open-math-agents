import OMAStatements.S_oeis_a245786

open OMA.S_oeis_a245786 in
theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a245786.main) := by
  have S a b : Nat.Coprime a b → sigma (a * b) = sigma a * sigma b := Nat.Coprime.sum_divisors_mul
  have hn : sigma 275890944 = 919636480 := by
    rw [show 275890944 = 256 * 3 * 7 * 19 * 37 * 73 from rfl, S, S, S, S, S] <;> decide
  have hm : sigma 142990848 = 571963392 := by
    rw [show 142990848 = 512 * 9 * 7 * 11 * 13 * 31 from rfl, S, S, S, S, S] <;> decide
  have ht : tau 275890944 = 288 := by
    rw [show 275890944 = 256 * 3 * 7 * 19 * 37 * 73 from rfl, tau, Nat.Coprime.card_divisors_mul,
      Nat.Coprime.card_divisors_mul, Nat.Coprime.card_divisors_mul, Nat.Coprime.card_divisors_mul,
      Nat.Coprime.card_divisors_mul] <;> decide
  intro H
  have := (H 275890944 ⟨by norm_num, 957958, by rw [hn, ht]; norm_num⟩).2 142990848 (by norm_num) (by norm_num)
  rw [hn, hm] at this
  norm_num at this
