import Mathlib

/-!
# Seven-row ternary arrays, OEIS A250818

Source: https://oeis.org/A250818. Submitted by @VestigeClub.

A column is encoded in base three with the top digit least significant.
For an adjacent block with upper row (a,b) and lower row (c,d), its
conditions are b+c ≤ d+a and min(a,c) ≤ min(b,d).
The first digit of a new column is unrestricted. The remaining six
digits are selected from top to bottom by precisely these two inequalities.
Each choice of digits has a unique encoding in the range from 0 to 2186.
At every column boundary an array either repeats its column or takes one
of the distinct successors. Summing over the starting column therefore
counts all seven-by-(n+1) arrays for the sequence index n. The formal
power series starts at index one, as in the entry.
-/

namespace OMA.S_oeis_a250818

abbrev Column := Fin 2187

def tails : ℕ → ℕ → ℕ → ℕ → List ℕ
  | 0, _, _, _ => [0]
  | h+1, old, a, b =>
    (List.range 3).flatMap fun d =>
      if b + old % 3 ≤ d + a ∧ min a (old % 3) ≤ min b d then
        (tails h (old / 3) (old % 3) d).map (fun t => d + 3*t)
      else []

def changes (s : Column) : List Column :=
  ((List.range 3).flatMap (fun b =>
    (tails 6 (s.val / 3) (s.val % 3) b).map (fun t => b + 3*t))).filterMap
    (fun t => if h : t < 2187 then if t = s.val then none else some ⟨t,h⟩ else none)

def countFrom : ℕ → Column → ℕ
  | 0, _ => 1
  | n+1, s => countFrom n s + ((changes s).map (countFrom n)).sum

def a (n : ℕ) : ℕ := (List.ofFn (countFrom n)).sum

theorem main :
    (∀ n : ℕ, 1 ≤ n → a n = 136*n^4 + 1225*n^3 + 4402*n^2 + 5499*n + 2187) ∧
    (∀ n : ℕ, 5 < n → (a n : ℤ) = 5*a (n-1) - 10*a (n-2) +
      10*a (n-3) - 5*a (n-4) + a (n-5)) ∧
    (let X : PowerSeries ℤ := PowerSeries.X
     PowerSeries.mk (fun n => if n = 0 then 0 else (a n : ℤ)) * (1-X)^5 =
       X * (13449 - 24476*X + 23038*X^2 - 10934*X^3 + 2187*X^4)) := by
  sorry

end OMA.S_oeis_a250818
