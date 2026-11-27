import OMAStatements.S_oeis_a102239

-- Problem: oeis-a102239
-- Credit: @anmolspace
-- Proof: s (n+1) = 5 * s n + 1 and s n % 2 = (n+1) % 2 (induction); the recurrence for
-- a n = s n + 1 - s n % 2 then follows by linear arithmetic (omega).

namespace OMA.P102239
open OMA.S_oeis_a102239

lemma hs (n : ℕ) : s (n + 1) = 5 * s n + 1 := by
  unfold s
  rw [Finset.sum_range_succ', Finset.mul_sum]
  congr 1
  all_goals first
    | (apply Finset.sum_congr rfl; intro i _; ring)
    | simp

lemma hpar (n : ℕ) : s n % 2 = (n + 1) % 2 := by
  induction n with
  | zero => simp [s]
  | succ n ih => rw [hs]; omega

end OMA.P102239

theorem OMA.solution : type_of% @OMA.S_oeis_a102239.main := by
  intro n
  have h1 := OMA.P102239.hs n
  have h2 : OMA.S_oeis_a102239.s (n + 2) = 5 * OMA.S_oeis_a102239.s (n + 1) + 1 :=
    OMA.P102239.hs (n + 1)
  have p0 := OMA.P102239.hpar n
  have p1 := OMA.P102239.hpar (n + 1)
  have p2 := OMA.P102239.hpar (n + 2)
  simp only [OMA.S_oeis_a102239.a]
  omega
