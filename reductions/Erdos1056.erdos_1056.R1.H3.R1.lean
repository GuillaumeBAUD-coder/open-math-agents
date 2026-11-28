import OMAReductions.R_Erdos1056_erdos_1056_R1

-- Reduction Erdos1056.erdos_1056.R1.H3.R1 of step Erdos1056.erdos_1056.R1.H3
-- Credit: @sntntHb

/-!
Split of the open regime k >= 4 of Erdős 1056 into a finite computational part and the rest.

The product of the integers in [a, b) (with 1 <= a <= b <= p - 1) is (b - 1)! / (a - 1)! mod p,
so k consecutive intervals with all products congruent to 1 mod p are the same as k + 1
boundaries b_0 < ... < b_k in [1, p - 1] with all (b_i - 1)! congruent mod p. A computer search
over primes (smallest prime for each k) found such boundary sets:

* p = 17:    1, 2, 6, 12, 16                      (k = 4)
* p = 23:    1, 2, 5, 9, 12, 22                   (k = 5)
* p = 71:    8, 10, 20, 52, 62, 64, 71            (k = 6)
* p = 599:   29, 51, 123, 184, 251, 290, 501, 540, 556            (k = 7, 8)
* p = 3011:  1, 2, 612, 724, 750, 806, 2206, 2262, 2288, 2400, 3010 (k = 9, 10)
* p = 52163: 1, 2, 3925, 7292, 7428, 18520, 24932, 26082, 27232, 33644, 44736, 44872, 52162
  (k = 11, 12; every prefix also works, so this one prime covers 4 <= k <= 12)

and no prime p < 600000 has 14 equal factorial residues (k = 13). So:

* H1: the cases 4 <= k <= 12, settled by the explicit witness above (a kernel computation of
  about 52000 modular multiplications; the step proof will be submitted separately).
* H2: the remaining open cases k >= 13, where no witness is known to us.
-/

namespace OMA.R_Erdos1056_erdos_1056_R1_H3_R1

open Erdos1056

/-- The finite range 4 <= k <= 12: explicit witnesses exist (p = 52163 works for all of them). -/
def H1 : Prop :=
  ∀ k : ℕ, 4 ≤ k → k ≤ 12 →
    ∃ (p : ℕ) (_ : p.Prime) (b : Fin (k + 1) → ℕ) (_ : StrictMono b), AllModProdEqualsOne p b

/-- The open range k >= 13. -/
def H2 : Prop :=
  ∀ k : ℕ, 13 ≤ k →
    ∃ (p : ℕ) (_ : p.Prime) (b : Fin (k + 1) → ℕ) (_ : StrictMono b), AllModProdEqualsOne p b

theorem main : H1 → H2 → OMA.R_Erdos1056_erdos_1056_R1.H3 := by
  intro h1 h2 k hk
  by_cases h : k ≤ 12
  · exact h1 k hk h
  · exact h2 k (by omega)

end OMA.R_Erdos1056_erdos_1056_R1_H3_R1
