import Mathlib

/-!
# A033321 counts permutations sorted by a consecutive-231-avoiding stack then a 21-avoiding stack

Source: https://oeis.org/A033321
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

A033321 is the binomial transform of Fine's sequence A000957. Conjecture (Defant, 2020): `a(n)`
is the number of permutations of length `n` that are sorted to the identity by a
consecutive-231-avoiding stack followed by a classical-21-avoiding stack.

Conventions:
* Fine numbers: `F(0) = 1` and `2 F(n+1) + F(n) = C(n+1)` (Catalan), i.e.
  `F(n+1) = (C(n+1) - F(n)) / 2`. Then `a(n) = Σ_k binom(n, k) F(n-k)`.
* A stack is a list whose head is the top. A `τ`-avoiding stack machine reads the input left to
  right; it pushes the next entry unless the stack, read from top to bottom, would then contain
  `τ`, in which case it pops the top to the output; when the input is exhausted it pops
  everything. For the consecutive pattern 231 the stack always avoids it, so the push of `x` onto
  `y :: z :: _` is forbidden exactly when `z < x < y`. For the classical pattern 21 the push of
  `x` onto `y :: _` is forbidden exactly when `y < x`.
* Permutations of length `n` are `σ : Equiv.Perm (Fin n)`, read as the word `σ 0, …, σ (n-1)`.
-/

namespace OMA.S_oeis_a033321

/-- Fine's sequence A000957. -/
def fine : ℕ → ℕ
  | 0 => 1
  | n + 1 => (catalan (n + 1) - fine n) / 2

/-- A033321. -/
def a (n : ℕ) : ℕ := ∑ k ∈ Finset.range (n + 1), n.choose k * fine (n - k)

/-- Consecutive-231-avoiding stack: input, stack (head = top) ↦ output. -/
def sort231 : List ℕ → List ℕ → List ℕ
  | [], st => st
  | x :: xs, y :: z :: st =>
      if z < x ∧ x < y then y :: sort231 (x :: xs) (z :: st)
      else sort231 xs (x :: y :: z :: st)
  | x :: xs, st => sort231 xs (x :: st)
termination_by xs st => 2 * xs.length + st.length

/-- Classical-21-avoiding stack (West's stack sort): input, stack ↦ output. -/
def sort21 : List ℕ → List ℕ → List ℕ
  | [], st => st
  | x :: xs, y :: st => if y < x then y :: sort21 (x :: xs) st else sort21 xs (x :: y :: st)
  | x :: xs, [] => sort21 xs [x]
termination_by xs st => 2 * xs.length + st.length

theorem main :
    ∀ n : ℕ, (Finset.univ.filter fun σ : Equiv.Perm (Fin n) =>
        sort21 (sort231 (List.ofFn fun i => (σ i : ℕ)) []) [] = List.range n).card = a n := by
  sorry

end OMA.S_oeis_a033321
