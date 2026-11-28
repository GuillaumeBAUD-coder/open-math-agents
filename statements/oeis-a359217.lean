import Mathlib.Data.Int.Basic
import Mathlib.Data.Nat.Sqrt

/-!
# Vertical coordinate of the counterclockwise undulating spiral

Source: Hans G. Oberlack, OEIS A359217, https://oeis.org/A359217 (CC BY-SA 4.0).
The step rule is Rémy Sigrist's linked PARI generator. The conjectured T10
uses subtraction exactly as printed. The offset is 0.
Credit: @jatin6
-/

namespace OMA.S_oeis_a359217

abbrev Point := ℤ × ℤ

def move (p : Point) : Point :=
  let (x, y) := p
  if x % 2 = y % 2 then (if y ≤ 0 then x+1 else x-1, y)
  else (x, if x > 0 ∨ (x = 0 ∧ y > 0) then y+1 else y-1)

def walk : ℕ → Point
  | 0 => (0, 0)
  | n+1 => move (walk n)

/-- T3 is floor((sqrt(8*floor(n/16)+1)-1)/2). Integer square root
followed by integer division gives the same floor. -/
def ringIndex (n : ℕ) : ℕ := (Nat.sqrt (8*(n/16)+1)-1)/2

def claimed (n : ℕ) : ℤ :=
  let r : ℤ := ringIndex n
  let t := (n : ℤ) - 8*r*(r+1)
  let s := r+1
  let a := (t+12*s-1)/(16*s)
  let b := (t+8*s-1)/(16*s)
  let c := (t+4*s-1)/(16*s)
  (1-a-t/2) + (a-b)*((8*s-t+1)/2) - (b-c)*((t-8*s)/2) - c*((16*s-t+1)/2)

theorem main : ∀ n : ℕ, (walk n).2 = claimed n := by
  sorry

end OMA.S_oeis_a359217
