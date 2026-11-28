import FormalConjectures.OEIS.«219838»
import Mathlib

-- Reduction OeisA219838.conjecture_1.R1 of "a(n) > 0 for all n > 1" (OEIS A219838).
-- Credit: @MBimrose
--
/-!
# A219838 conjecture 1: the finite part and the open tail

`a n` counts the `x` with `1 ≤ x ≤ n/2` for which `(x(n-x))^2 + x(n-x) + 1` is prime.

* `H1` (proved below, in this file): every `n` with `1 < n < 30` satisfies `a n > 0`.  Each of the
  28 cases is discharged with an explicit witness `x` and a `norm_num` primality certificate, e.g.
  `n = 29, x = 2` gives `54^2 + 54 + 1 = 2971`, prime.
* `H2` (assumed): every `n ≥ 30` has such an `x` in `Icc 1 (n/2)`.  This is the genuine open content
  of the conjecture; it was checked numerically with Miller–Rabin (bases 2..37) for every
  `n` in `31..3000`, always with a witness, and `a n` was computed exactly for `n ≤ 30`
  (the values are `1,1,1,1,2,2,2,3,2,1,2,1,2,3,1,1,3,2,2,6,4,1,3,3,4,4,4,4` for `n = 2..29`).

`main` splits on `n < 30` and converts the `H2` witness into `a n > 0` via `Finset.card_pos`.
-/

namespace OMA.R_OeisA219838_conjecture_1_R1

/-- Finite direction: every `n` with `1 < n < 30` has a valid representation. -/
def H1 : Prop := ∀ n : ℕ, 1 < n → n < 30 → OeisA219838.a n > 0

/-- Open (tail) direction: every `n ≥ 30` has a valid representation. -/
def H2 : Prop := ∀ n : ℕ, 30 ≤ n → ∃ x : ℕ, x ∈ Finset.Icc 1 (n / 2) ∧
  Nat.Prime ((x * (n - x)) ^ 2 + x * (n - x) + 1)

/-- A witness `x` with prime value certifies `a n > 0`. -/
lemma a_pos_of (n x : ℕ) (hx : x ∈ Finset.Icc 1 (n / 2))
    (hp : Nat.Prime ((x * (n - x)) ^ 2 + x * (n - x) + 1)) : OeisA219838.a n > 0 := by
  unfold OeisA219838.a
  refine Finset.card_pos.mpr ⟨x, ?_⟩
  simp only [Finset.mem_filter]
  exact ⟨hx, hp⟩

theorem H1_true : H1 := by
  intro n h1 h2
  interval_cases n
  · -- n = 2: x = 1, (x*(n-x))^2 + x*(n-x) + 1 = 3, prime
    exact a_pos_of 2 1 (by decide) (by norm_num)
  · -- n = 3: x = 1, (x*(n-x))^2 + x*(n-x) + 1 = 7, prime
    exact a_pos_of 3 1 (by decide) (by norm_num)
  · -- n = 4: x = 1, (x*(n-x))^2 + x*(n-x) + 1 = 13, prime
    exact a_pos_of 4 1 (by decide) (by norm_num)
  · -- n = 5: x = 2, (x*(n-x))^2 + x*(n-x) + 1 = 43, prime
    exact a_pos_of 5 2 (by decide) (by norm_num)
  · -- n = 6: x = 1, (x*(n-x))^2 + x*(n-x) + 1 = 31, prime
    exact a_pos_of 6 1 (by decide) (by norm_num)
  · -- n = 7: x = 1, (x*(n-x))^2 + x*(n-x) + 1 = 43, prime
    exact a_pos_of 7 1 (by decide) (by norm_num)
  · -- n = 8: x = 2, (x*(n-x))^2 + x*(n-x) + 1 = 157, prime
    exact a_pos_of 8 2 (by decide) (by norm_num)
  · -- n = 9: x = 1, (x*(n-x))^2 + x*(n-x) + 1 = 73, prime
    exact a_pos_of 9 1 (by decide) (by norm_num)
  · -- n = 10: x = 3, (x*(n-x))^2 + x*(n-x) + 1 = 463, prime
    exact a_pos_of 10 3 (by decide) (by norm_num)
  · -- n = 11: x = 3, (x*(n-x))^2 + x*(n-x) + 1 = 601, prime
    exact a_pos_of 11 3 (by decide) (by norm_num)
  · -- n = 12: x = 2, (x*(n-x))^2 + x*(n-x) + 1 = 421, prime
    exact a_pos_of 12 2 (by decide) (by norm_num)
  · -- n = 13: x = 1, (x*(n-x))^2 + x*(n-x) + 1 = 157, prime
    exact a_pos_of 13 1 (by decide) (by norm_num)
  · -- n = 14: x = 2, (x*(n-x))^2 + x*(n-x) + 1 = 601, prime
    exact a_pos_of 14 2 (by decide) (by norm_num)
  · -- n = 15: x = 1, (x*(n-x))^2 + x*(n-x) + 1 = 211, prime
    exact a_pos_of 15 1 (by decide) (by norm_num)
  · -- n = 16: x = 1, (x*(n-x))^2 + x*(n-x) + 1 = 241, prime
    exact a_pos_of 16 1 (by decide) (by norm_num)
  · -- n = 17: x = 6, (x*(n-x))^2 + x*(n-x) + 1 = 4423, prime
    exact a_pos_of 17 6 (by decide) (by norm_num)
  · -- n = 18: x = 1, (x*(n-x))^2 + x*(n-x) + 1 = 307, prime
    exact a_pos_of 18 1 (by decide) (by norm_num)
  · -- n = 19: x = 6, (x*(n-x))^2 + x*(n-x) + 1 = 6163, prime
    exact a_pos_of 19 6 (by decide) (by norm_num)
  · -- n = 20: x = 5, (x*(n-x))^2 + x*(n-x) + 1 = 5701, prime
    exact a_pos_of 20 5 (by decide) (by norm_num)
  · -- n = 21: x = 1, (x*(n-x))^2 + x*(n-x) + 1 = 421, prime
    exact a_pos_of 21 1 (by decide) (by norm_num)
  · -- n = 22: x = 1, (x*(n-x))^2 + x*(n-x) + 1 = 463, prime
    exact a_pos_of 22 1 (by decide) (by norm_num)
  · -- n = 23: x = 5, (x*(n-x))^2 + x*(n-x) + 1 = 8191, prime
    exact a_pos_of 23 5 (by decide) (by norm_num)
  · -- n = 24: x = 4, (x*(n-x))^2 + x*(n-x) + 1 = 6481, prime
    exact a_pos_of 24 4 (by decide) (by norm_num)
  · -- n = 25: x = 1, (x*(n-x))^2 + x*(n-x) + 1 = 601, prime
    exact a_pos_of 25 1 (by decide) (by norm_num)
  · -- n = 26: x = 3, (x*(n-x))^2 + x*(n-x) + 1 = 4831, prime
    exact a_pos_of 26 3 (by decide) (by norm_num)
  · -- n = 27: x = 2, (x*(n-x))^2 + x*(n-x) + 1 = 2551, prime
    exact a_pos_of 27 2 (by decide) (by norm_num)
  · -- n = 28: x = 1, (x*(n-x))^2 + x*(n-x) + 1 = 757, prime
    exact a_pos_of 28 1 (by decide) (by norm_num)
  · -- n = 29: x = 2, (x*(n-x))^2 + x*(n-x) + 1 = 2971, prime
    exact a_pos_of 29 2 (by decide) (by norm_num)

theorem main : H1 → H2 → type_of% @OeisA219838.conjecture_1 := by
  intro h1 h2 n hn
  by_cases hlt : n < 30
  · exact h1 n hn hlt
  · obtain ⟨x, hx, hp⟩ := h2 n (by omega)
    exact a_pos_of n x hx hp

end OMA.R_OeisA219838_conjecture_1_R1
