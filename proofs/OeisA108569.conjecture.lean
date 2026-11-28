import FormalConjectures.OEIS.«108569»

namespace A108569Counterexamples

-- The odd witness also appears in saientropy's earlier certificate.
lemma seed_totient : Nat.totient 5095354107 = 3393612288 := by
  rw [show (5095354107 : ℕ) = 3 * (1033 * 1644193) by decide,
    Nat.totient_mul (by decide), Nat.totient_mul (by decide)]
  norm_num [Nat.totient_prime (by norm_num : Nat.Prime 3),
    Nat.totient_prime (by norm_num : Nat.Prime 1033),
    Nat.totient_prime (by norm_num : Nat.Prime 1644193)]

lemma shifted_totient : Nat.totient 8488966395 = 3393612288 := by
  rw [show (8488966395 : ℕ) = 3 * (5 * (7 * (13 * (19 * 327317)))) by decide,
    Nat.totient_mul (by decide), Nat.totient_mul (by decide), Nat.totient_mul (by decide),
    Nat.totient_mul (by decide), Nat.totient_mul (by decide)]
  norm_num [Nat.totient_prime (by norm_num : Nat.Prime 3),
    Nat.totient_prime (by norm_num : Nat.Prime 5), Nat.totient_prime (by norm_num : Nat.Prime 7),
    Nat.totient_prime (by norm_num : Nat.Prime 13), Nat.totient_prime (by norm_num : Nat.Prime 19),
    Nat.totient_prime (by norm_num : Nat.Prime 327317)]

lemma witness : OeisA108569.A 5095354107 := by
  refine ⟨by decide, ?_⟩
  rw [seed_totient, show (5095354107 + 3393612288 : ℕ) = 8488966395 by decide,
    shifted_totient]

end A108569Counterexamples

theorem OMA.disproof : ¬ (type_of% @OeisA108569.conjecture) := by
  intro all_even
  have hpos : 0 < Nat.count OeisA108569.A 5095354107 :=
    lt_of_lt_of_le (show 0 < Nat.count OeisA108569.A 2 by decide)
      (Nat.count_monotone _ (by decide : 2 ≤ 5095354107))
  have heven := all_even _ hpos
  change Even (Nat.nth OeisA108569.A (Nat.count OeisA108569.A 5095354107)) at heven
  rw [Nat.nth_count A108569Counterexamples.witness] at heven
  exact (by decide : ¬ Even (5095354107 : ℕ)) heven
