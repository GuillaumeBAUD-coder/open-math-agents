import Mathlib

/-!
# Four-letter words with cyclically adjacent repeated values (OEIS A269679)
Source: https://oeis.org/A269679
Credit: @etaubman

R. H. Hardin counts words on 0 through n in which successive adjacent
repetitions have values differing by plus or minus one modulo n+1.
At most one repetition is unrestricted. With two or more repetitions,
the only allowed shape is aabb with a and b neighbors on the cycle.
The cycle on two letters has just one distinct neighbor per letter.
The formula is Hardin's and the recurrence and generating function
are due to Colin Barker (2019). The series starts at degree one.
-/

namespace OMA.S_oeis_a269679

abbrev Alphabet (n : ℕ) := Fin (n+1)
abbrev Word (n : ℕ) := Alphabet n × Alphabet n × Alphabet n × Alphabet n

def two {n : ℕ} (w : Word n) : Prop :=
  let (a,b,c,d) := w
  (a=b ∧ b=c) ∨ (b=c ∧ c=d) ∨ (a=b ∧ c=d)

def cyclicNext {n : ℕ} (a : Alphabet n) : Alphabet n :=
  if h : a.val < n then ⟨a.val+1, by omega⟩ else 0

def allowedPair {n : ℕ} (w : Word n) : Prop :=
  let (a,b,c,d) := w
  a=b ∧ c=d ∧ (c = cyclicNext a ∨ a = cyclicNext c)

def allowed {n : ℕ} (w : Word n) : Prop := ¬two w ∨ allowedPair w

instance {n : ℕ} (w : Word n) : Decidable (allowed w) := by
  obtain ⟨a,b,c,d⟩ := w
  unfold allowed two allowedPair
  infer_instance

def count (n : ℕ) : ℕ := ((Finset.univ : Finset (Word n)).filter allowed).card

def terms : ℕ → ℤ
  | 0 => 0
  | n+1 => (count (n+1) : ℤ)

open PowerSeries

theorem main :
    (∀ n : ℕ, terms (n+2) = ((n:ℤ)+2)^4 + 4*(n+2)^3 + 3*(n+2)^2 + 2*(n+2) + 2) ∧
    (∀ n : ℕ, terms (n+7) = 5*terms (n+6) - 10*terms (n+5) +
      10*terms (n+4) - 5*terms (n+3) + terms (n+2)) ∧
    (1-X)^5 * mk terms = (2*X*(5 + 8*X - 3*X^2 + 5*X^3 - 4*X^4 + X^5) : PowerSeries ℤ) := by
  sorry

end OMA.S_oeis_a269679
