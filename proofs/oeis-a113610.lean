import OMAStatements.S_oeis_a113610

open OMA.S_oeis_a113610 in
theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a113610.main) := fun h => by
  have q {n p : ℕ} (hp : p.Prime) (hc : Nat.count Nat.Prime p = n - 1) : prime n = p := by
    rw [prime, ← hc, Nat.nth_count hp]
  have b := q (n := 12) (p := 37) (by decide) (by decide +kernel)
  have c := q (n := 13) (p := 41) (by decide) (by decide +kernel)
  have d := q (n := 14) (p := 43) (by decide) (by decide +kernel)
  have e := q (n := 15) (p := 47) (by decide) (by decide +kernel)
  have := h 12 (by decide) (by rw [a, a, b, c, d]; decide +kernel) (by rw [a, a, c, d, e]; decide +kernel)
  rw [c, b] at this
  omega
