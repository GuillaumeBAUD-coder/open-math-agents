import Mathlib

/-!
# Record indices of Leroy Quet's divisor-count greedy sequence

Source: https://oeis.org/A114111 and https://oeis.org/A111390
Credit: Leroy Quet (base sequence), Klaus Brockhaus (records), Chai Wah Wu
(conjectures, July 27, 2022), Robert Leshner (@rleshner, formalization).

Quet starts with 1 and chooses the least unused positive integer whose number
of divisors differs by one from that of the previous term. Within a divisor-count
class all numbers smaller than a selected member have already appeared: any such
unused number was eligible at the step that selected this member. Thus the last
number used in each class is an exact cursor for the ordinary greedy rule.
A114111 indexes strict records starting with record number 1 at position 1.
-/

namespace OMA.S_oeis_a114111

def tau (x : ℕ) := x.divisors.card

structure State where
  lastClass : ℕ
  lastIn : ℕ → ℕ
  largest : ℕ
  records : ℕ

def first : State := ⟨1,fun d => if d=1 then 1 else 0,1,1⟩

def admissible (s : State) (x : ℕ) : Prop :=
  s.lastIn (tau x) < x ∧ (tau x+1=s.lastClass ∨ tau x=s.lastClass+1)

noncomputable def next (s : State) : ℕ := sInf {x | admissible s x}

def accept (s : State) (d x : ℕ) : State :=
  ⟨d,Function.update s.lastIn d x,max s.largest x,s.records + if s.largest<x then 1 else 0⟩

/-- State after n+1 terms. -/
noncomputable def state : ℕ → State
  | 0 => first
  | n+1 => let s := state n; let x := next s; accept s (tau x) x

/-- Number of strict records in the first n terms. -/
noncomputable def count : ℕ → ℕ
  | 0 => 0
  | n+1 => (state n).records

/-- Index of record n; coefficient at zero is zero. -/
noncomputable def a (n : ℕ) : ℤ := (sInf {i : ℕ | n ≤ count i} : ℕ)

/-- Both conjectured descriptions of A114111. -/
theorem main :
    (∀ n : ℕ, 23<n → a n=2*a (n-1)-a (n-2)) ∧
    (let X : PowerSeries ℤ := PowerSeries.X
     (X-1)^2*PowerSeries.mk a =
       X*(-9608*X^22+9608*X^21-24*X^16+24*X^15-8*X^9+4*X^8+
         4*X^7-2*X^6+2*X^5+X^3+1)) := by
  sorry

end OMA.S_oeis_a114111
