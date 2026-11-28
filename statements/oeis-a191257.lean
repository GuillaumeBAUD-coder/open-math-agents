import Mathlib

/-!
Sources: OEIS A191255, A191257, A067368, and A213258.
The sequence functions below use zero-based indexing, so argument zero
denotes the first term of each OEIS sequence.
-/

namespace OMA.S_oeis_a191257

/-- The nonzero symbol in the image of a letter under the substitution
0 ↦ 01, 1 ↦ 02, 2 ↦ 03, 3 ↦ 01. -/
def advance (a : ℕ) : ℕ := if a = 3 then 1 else a + 1

/-- A191255 at the one-based position n, with position zero set to zero. -/
def symbol (n : ℕ) : ℕ :=
  @Nat.binaryRec (fun _ => ℕ) 0
    (fun b k a => if b then 0 else if k = 0 then 0 else advance a) n

/-- The original A191257, given by positions where A191255(2n) equals 1. -/
noncomputable def a191257 (j : ℕ) : ℕ := Nat.nth (fun n => symbol (2 * n) = 1) j

/-- A213258 lists the positions where A191255 equals 2. -/
noncomputable def a213258 (j : ℕ) : ℕ := Nat.nth (fun n => symbol n = 2) j

/-- The greedy rule of A067368 permits a positive even number when it is not
a product of two or three terms already admitted. Repetitions are allowed. -/
def admissible (P : ℕ → Prop) (n : ℕ) : Prop :=
  n ≠ 0 ∧ 2 ∣ n ∧
    ¬ ((∃ a b, P a ∧ P b ∧ a * b = n) ∨
       (∃ a b c, P a ∧ P b ∧ P c ∧ a * b * c = n))

open Classical in
/-- Terms of A067368 strictly below n, constructed in increasing order. -/
noncomputable def greedyPrefix : ℕ → Finset ℕ
  | 0 => ∅
  | n + 1 =>
    let A := greedyPrefix n
    if admissible (· ∈ A) n then insert n A else A

/-- A067368, the increasing sequence produced by the greedy rule. -/
noncomputable def a067368 (j : ℕ) : ℕ :=
  Nat.nth (fun n => n ∈ greedyPrefix (n + 1)) j

/-- Kimberling's identity for the original A191257, and its relation to A213258. -/
theorem main :
    (∀ n : ℕ, symbol (2 * n) = 1 ↔ 0 < n ∧ (symbol n = 0 ∨ symbol n = 3)) ∧
    (∀ j : ℕ, 2 * a191257 j = a067368 j ∧ 4 * a191257 j = a213258 j) := by
  sorry

end OMA.S_oeis_a191257
