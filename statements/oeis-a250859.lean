import Mathlib

/-!
# Eight-row arrays with entries from 0 through 3, OEIS A250859

Source: https://oeis.org/A250859. Submitted by @VestigeClub.

The first two rows are counted directly, a column being encoded by its
top digit plus four times its bottom digit. In an adjacent block (a,b;c,d)
the necessary and sufficient conditions are b+c ≤ d+a and
min(a,c) ≤ min(b,d). In particular c ≤ d: the bottom digit is its pair's
minimum plus max(c-a,0), and both summands are nondecreasing.

Suppose the current bottom row rises by v over its n boundaries. To add
one more row with total rise u, distribute u-v extra units in order among
the n boundaries. At each boundary the new row rises by the former bottom
row's rise plus its extra units. These are precisely the allowed
differences. Both rows are then nondecreasing, which gives the minimum
condition automatically. There are 4-u choices for the initial new digit,
and the endpoint bound guarantees all its digits lie in {0,1,2,3}.
The starting digit and the ordered list of extras reconstruct the row
uniquely. Six added rows make eight. The rational-valued sums count whole
arrays exactly, including those with repeated columns; the generating
series starts at the entry's offset one.
-/

namespace OMA.S_oeis_a250859

def stepOK (s t : ℕ) : Bool :=
  decide (t%4 + s/4 ≤ t/4 + s%4 ∧ min (s%4) (s/4) ≤ min (t%4) (t/4))

def topWays : ℕ → ℕ → ℕ → ℚ
  | 0, s, e => if s/4 = e then 1 else 0
  | n+1, s, e => ∑ t ∈ Finset.range 16, if stepOK s t then topWays n t e else 0

def extras : ℕ → ℕ → ℚ
  | 0, w => if w = 0 then 1 else 0
  | n+1, w => ∑ j ∈ Finset.range (w+1), extras n (w-j)

def layer (n : ℕ) : ℕ → ℕ → ℚ
  | 0, u => ∑ s ∈ Finset.range 16, topWays n s (s/4+u)
  | h+1, u => ((4-u : ℕ) : ℚ) * ∑ v ∈ Finset.range (u+1), layer n h v * extras n (u-v)

def a (n : ℕ) : ℚ := ∑ u ∈ Finset.range 4, layer n 6 u

theorem main :
    (∀ n : ℕ, 1 ≤ n → a n = 15887/18*(n:ℚ)^6 + 39464/3*(n:ℚ)^5 + 2674189/36*(n:ℚ)^4 + 462227/2*(n:ℚ)^3 + 12645859/36*(n:ℚ)^2 + 743119/3*(n:ℚ) + 65536) ∧
    (∀ n : ℕ, 7 < n → a n = 7*a (n-1) - 21*a (n-2) + 35*a (n-3) - 35*a (n-4) +
      21*a (n-5) - 7*a (n-6) + a (n-7)) ∧
    (let X : PowerSeries ℚ := PowerSeries.X
     PowerSeries.mk (fun n => if n = 0 then 0 else a n) * (1-X)^7 =
       X * (983950 - 1406733*X + 2363648*X^2 - 2238796*X^3 + 1326626*X^4 - 458751*X^5 + 65536*X^6)) := by
  sorry

end OMA.S_oeis_a250859
