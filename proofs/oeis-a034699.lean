import OMAStatements.S_oeis_a034699

-- Problem: OEIS A034699, the conjecture that the largest prime power factors of the
-- numbers strictly between two consecutive primes are pairwise distinct.
-- Disproof: between the consecutive primes 4177 and 4201, the numbers
-- 4180 = 2^2 * 5 * 11 * 19 and 4199 = 13 * 17 * 19 both have largest prime power factor 19
-- (M. Marcus, OEIS A034699, Jun 19 2019; see A308752).

namespace OMA.A034699Proof

open OMA.S_oeis_a034699

lemma a4180 : a 4180 = 19 := by
  decide +kernel

lemma a4199 : a 4199 = 19 := by
  decide +kernel

lemma gap : ∀ r, 4177 < r → r < 4201 → ¬ r.Prime := by
  intro r h1 h2
  interval_cases r <;> norm_num

end OMA.A034699Proof

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a034699.main) := by
  intro h
  have := h 4177 4201 (by norm_num) (by norm_num) (by norm_num) OMA.A034699Proof.gap
    4180 4199 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by rw [OMA.A034699Proof.a4180, OMA.A034699Proof.a4199])
  norm_num at this
