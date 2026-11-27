import FormalConjectures.OEIS.«232616»

-- Reduction OeisA232616.conjecture_3.R1 of Complete residue systems of 2^k - k — conjecture3
-- Credit: @Andyi955
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.
--
-- The target is an iff for the equation `x ^ n + n = y ^ m`: every solution in integers `> 1` is
-- one of the two listed tuples. The forward direction is the Diophantine finiteness statement;
-- the backward direction is a finite verification on the two explicit witnesses.

namespace OMA.R_OeisA232616_conjecture_3_R1

/-- Forward direction: any solution of `x ^ n + n = y ^ m` in integers `> 1` is one of the two
exceptional tuples `(5, 2, 3, 3)` and `(5, 3, 2, 7)`. -/
def H1 : Prop :=
  ∀ (x y n m : ℕ), 1 < x → 1 < y → 1 < n → 1 < m → x ^ n + n = y ^ m →
    (x = 5 ∧ n = 2 ∧ y = 3 ∧ m = 3) ∨ (x = 5 ∧ n = 3 ∧ y = 2 ∧ m = 7)

/-- Backward direction: the two exceptional tuples do satisfy `x ^ n + n = y ^ m`. -/
def H2 : Prop :=
  ∀ (x y n m : ℕ), 1 < x → 1 < y → 1 < n → 1 < m →
    ((x = 5 ∧ n = 2 ∧ y = 3 ∧ m = 3) ∨ (x = 5 ∧ n = 3 ∧ y = 2 ∧ m = 7)) →
    x ^ n + n = y ^ m

theorem main : H1 → H2 → type_of% @OeisA232616.conjecture_3 := by
  intro h1 h2 x y n m hx hy hn hm
  exact ⟨fun h => h1 x y n m hx hy hn hm h, fun h => h2 x y n m hx hy hn hm h⟩

end OMA.R_OeisA232616_conjecture_3_R1
