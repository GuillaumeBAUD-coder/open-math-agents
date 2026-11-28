import Mathlib

/-!
# OEIS A269437
Source: https://oeis.org/A269437
Credit: @etaubman

R. H. Hardin counts five-letter words on 0 through n. Scan the word and
record the value of every adjacent equal pair. The recorded values
must form a weakly decreasing list. The flag proof uses the five-slot
inclusion-exclusion argument shared with the A269585 formalization. We prove the empirical polynomial and
Colin Barker's conjectured generating function and recurrence.
-/

namespace OMA.S_oeis_a269437

def repeats {q : ℕ} (a b c d e : Fin q) : List ℕ :=
  (if b=a then [a.val] else []) ++ (if c=b then [b.val] else []) ++
  (if d=c then [c.val] else []) ++ (if e=d then [d.val] else [])

def allowed : List ℕ → Bool
  | x::y::t => decide (y ≤ x) && allowed (y::t)
  | _ => true

def count (n : ℕ) : ℚ :=
  ∑ a : Fin (n+1), ∑ b : Fin (n+1), ∑ c : Fin (n+1),
    ∑ d : Fin (n+1), ∑ e : Fin (n+1),
      if allowed (repeats a b c d e) then 1 else 0

def terms : ℕ → ℚ
  | 0 => 0
  | n+1 => count (n+1)

open PowerSeries

theorem main :
    (∀ n : ℕ, count n = (n:ℚ)^5 + 5*n^4 + 17*n^3/2 + 8*n^2 + 9*n/2 + 1) ∧
    (∀ n : ℕ, terms (n+7) = 6*terms (n+6) - 15*terms (n+5) +
      20*terms (n+4) - 15*terms (n+3) + 6*terms (n+2) - terms (n+1)) ∧
    (1-X)^6 * mk terms = (X * (28 + 54*X + 52*X^2 - 19*X^3 + 6*X^4 - X^5) :
      PowerSeries ℚ) := by
  sorry

end OMA.S_oeis_a269437
