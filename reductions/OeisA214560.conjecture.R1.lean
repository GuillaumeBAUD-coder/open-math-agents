import FormalConjectures.OEIS.«214560»

-- Reduction OeisA214560.conjecture.R1 of Number of $0$'s in the binary expansion of $n^2$
-- Credit: @BetAdmin237
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.
--
-- Target: for every x there is i with x < a(n) for all n > i, where a(n) is the number of
-- zeros in the binary expansion of n^2.
--
-- Proved outright here: the even part of n is harmless. Since (2n)^2 = 4 n^2, its binary
-- expansion is that of n^2 followed by two zeros, so a(2^v m) = a(m) + 2v for m > 0
-- (a_two_pow_mul). Writing n = 2^v m with m odd, either m is large (and the odd case
-- applies) or v is large (and the 2v trailing zeros already exceed x). Hence the conjecture
-- is equivalent to its restriction to odd n, which is split by the residue of n mod 4
-- (n^2 ends in 001 in binary in both classes, but the classes have different digit
-- structure: n = 4k+1 gives n^2 = 16k^2+8k+1, n = 4k+3 gives n^2 = 16k^2+24k+9):
--  H1: for every x, x < a(n) for all sufficiently large n with n % 4 = 1;
--  H2: for every x, x < a(n) for all sufficiently large n with n % 4 = 3.

namespace OMA.R_OeisA214560_conjecture_R1

def H1 : Prop :=
  ∀ x : ℕ, ∃ i : ℕ, ∀ n > i, n % 4 = 1 → x < OeisA214560.a n

def H2 : Prop :=
  ∀ x : ℕ, ∃ i : ℕ, ∀ n > i, n % 4 = 3 → x < OeisA214560.a n

lemma count_four_mul (m : ℕ) (hm : 0 < m) :
    (Nat.digits 2 (4 * m)).count 0 = (Nat.digits 2 m).count 0 + 2 := by
  have h1 : Nat.digits 2 (4 * m) = 0 :: Nat.digits 2 (2 * m) := by
    rw [Nat.digits_def' (by norm_num) (by omega)]
    congr 1
    · omega
    · congr 1; omega
  have h2 : Nat.digits 2 (2 * m) = 0 :: Nat.digits 2 m := by
    rw [Nat.digits_def' (by norm_num) (by omega)]
    congr 1
    · omega
    · congr 1; omega
  rw [h1, h2, List.count_cons_self, List.count_cons_self]

lemma a_two_mul (n : ℕ) (hn : 0 < n) : OeisA214560.a (2 * n) = OeisA214560.a n + 2 := by
  unfold OeisA214560.a
  rw [if_neg (by omega), if_neg (by omega)]
  have : (2 * n) ^ 2 = 4 * n ^ 2 := by ring
  rw [this, count_four_mul _ (by positivity)]

lemma a_two_pow_mul (v m : ℕ) (hm : 0 < m) :
    OeisA214560.a (2 ^ v * m) = OeisA214560.a m + 2 * v := by
  induction v with
  | zero => simp
  | succ v ih =>
    have e : 2 ^ (v + 1) * m = 2 * (2 ^ v * m) := by ring
    rw [e, a_two_mul _ (by positivity), ih]
    ring

theorem main : H1 → H2 → type_of% @OeisA214560.conjecture := by
  intro h1 h2 x
  obtain ⟨i1, hi1⟩ := h1 x
  obtain ⟨i2, hi2⟩ := h2 x
  let i0 := max i1 i2
  refine ⟨(i0 + 1) * 2 ^ x, ?_⟩
  intro n hn
  have hpos : 0 < 2 ^ x := by positivity
  have hn0 : n ≠ 0 := by
    have : 0 < (i0 + 1) * 2 ^ x := by positivity
    omega
  obtain ⟨v, m, hm, rfl⟩ := Nat.exists_eq_two_pow_mul_odd hn0
  have hm0 : 0 < m := hm.pos
  rw [a_two_pow_mul v m hm0]
  by_cases hmi : i0 < m
  · have hodd : m % 4 = 1 ∨ m % 4 = 3 := by
      obtain ⟨r, rfl⟩ := hm; omega
    rcases hodd with h | h
    · have := hi1 m (lt_of_le_of_lt (le_max_left _ _) hmi) h; omega
    · have := hi2 m (lt_of_le_of_lt (le_max_right _ _) hmi) h; omega
  · have hmi : m ≤ i0 := not_lt.mp hmi
    have hv : x < v := by
      by_contra hxv
      have hxv : v ≤ x := not_lt.mp hxv
      have h3 : 2 ^ v ≤ 2 ^ x := Nat.pow_le_pow_right (by norm_num) hxv
      have h4 : 2 ^ v * m ≤ 2 ^ x * (i0 + 1) := Nat.mul_le_mul h3 (by omega)
      have : 2 ^ v * m ≤ (i0 + 1) * 2 ^ x := by rw [mul_comm (i0 + 1)]; exact h4
      omega
    omega

end OMA.R_OeisA214560_conjecture_R1
