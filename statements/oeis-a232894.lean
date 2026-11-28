import Mathlib

/-!
# A232894: Catalan(k) - k runs through all residues modulo n quickly (Sun's conjecture)

Source: https://oeis.org/A232894 (OEIS Foundation, CC BY-SA 4.0)
Credit: @trador01 (agent: Claude Code, model claude-opus-5-5)

A232894 (offset 1): least positive integer m such that {Catalan(k) - k: k = 1, ..., m} contains
a complete system of residues modulo n, or 0 if such a number m does not exist; data
1, 5, 4, 11, 16, 13, 31, 27, ... (a(2) = 5 since Catalan(k) - k is even for k = 1, ..., 4 and
Catalan(5) - 5 = 37 is odd).

The entry records (Zhi-Wei Sun):

  Conjecture: (i) Let n be any positive integer. Then 0 < a(n) <= n^2/2 + 7. Also,
  {Catalan(k) + k: k = 1, ..., [n^2/2] + 23} contains a complete system of residues modulo n,
  where [.] is the floor function.
  (ii) For any integer n > 3, neither Catalan(n) - n nor Catalan(n) + n has the form x^m with
  m > 1 and x > 1.

Both parts are stated here.

Reading of the source:
* `Catalan(k)` is Mathlib's `catalan k`; `Catalan(k) - k` is computed in `ℤ`.
* A set of integers "contains a complete system of residues modulo n" when every residue class
  modulo `n` meets it: for every `r` there is a member `≡ r (mod n)`.
* "0 < a(n) <= n^2/2 + 7" says exactly that some `m` with `1 ≤ m ≤ n^2/2 + 7` has
  `{Catalan(k) - k : 1 ≤ k ≤ m}` covering all residues modulo `n` (then the least such `m` is
  positive and at most `n^2/2 + 7`). Since `m` is an integer, `m ≤ n^2/2 + 7` is `2m ≤ n^2 + 14`.
* For n > 3, `Catalan(n) - n > 1`; "has the form x^m with m > 1 and x > 1" ranges over natural
  `x, m`, and is stated for the integers `Catalan(n) ∓ n`.
-/

namespace OMA.S_oeis_a232894

/-- `{f(1), ..., f(m)}` contains a complete system of residues modulo `n`. -/
def Covers (f : ℕ → ℤ) (n m : ℕ) : Prop :=
  ∀ r : ℤ, ∃ k, 1 ≤ k ∧ k ≤ m ∧ f k ≡ r [ZMOD (n : ℤ)]

/-- Sun's conjecture, parts (i) and (ii). -/
theorem main :
    (∀ n : ℕ, 1 ≤ n →
      (∃ m : ℕ, 1 ≤ m ∧ 2 * m ≤ n ^ 2 + 14 ∧ Covers (fun k => (catalan k : ℤ) - k) n m) ∧
        Covers (fun k => (catalan k : ℤ) + k) n (n ^ 2 / 2 + 23)) ∧
      ∀ n : ℕ, 3 < n → ∀ x m : ℕ, 1 < x → 1 < m →
        (catalan n : ℤ) - n ≠ (x : ℤ) ^ m ∧ (catalan n : ℤ) + n ≠ (x : ℤ) ^ m := by
  sorry

end OMA.S_oeis_a232894
