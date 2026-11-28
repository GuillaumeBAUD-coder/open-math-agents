import Mathlib

/-!
# A092429: Kotesovec's asymptotic a(n) ~ 4^n/4!

Source: https://oeis.org/A092429 (OEIS Foundation, CC BY-SA 4.0).
Credit: @schulzee (agent: Claude Code, model claude-fable-5-2)

Entry (Benoit Cloitre, Mar 22 2004), offset 0:
a(n) = n! * Sum_{i,j,k,l >= 0, i+j+k+l = n} 1/(i!*j!*k!*l!), with data
1, 1, 3, 10, 47, 126, 522, 1821, 8143, 26326, ...

Formula section: Conjecture: a(n) ~ 4^n/4!. - Vaclav Kotesovec, Mar 07 2014.
Status: known result. Xinjun Wang (Jun 05 2026) records that the conjecture is true:
a(n) = 4^n/24 + O(4^n/sqrt(n)).

Formalization notes.
* The sum in the name runs over the unordered quadruples, as the data and the PARI program of the
  entry show:
  `a(n)=sum(i=0,n,sum(j=0,i,sum(k=0,j,sum(l=0,k,if(i+j+k+l-n,0,n!/i!/j!/k!/l!)))))`.
  So `a n` is the sum of the multinomial coefficients n!/(i! j! k! l!) over
  n >= i >= j >= k >= l >= 0 with i + j + k + l = n. (The sum over all ordered quadruples is 4^n.)
  The definition below is this program, term for term.
* n!/(i! j! k! l!) is a multinomial coefficient, so the division of natural numbers is exact.
* `f ~ g` is asymptotic equivalence as n tends to infinity, `Asymptotics.IsEquivalent` along
  `Filter.atTop`: a(n) - 4^n/24 = o(4^n/24).
* Controls from the entry: a(0..5) = 1, 1, 3, 10, 47, 126.
-/

namespace OMA.S_oeis_a092429

open Finset Filter Asymptotics

/-- A092429(n): the sum of n!/(i! j! k! l!) over n >= i >= j >= k >= l >= 0 with
i + j + k + l = n. -/
def a (n : ℕ) : ℕ :=
  ∑ i ∈ range (n + 1), ∑ j ∈ range (i + 1), ∑ k ∈ range (j + 1), ∑ l ∈ range (k + 1),
    if i + j + k + l = n then
      n.factorial / (i.factorial * j.factorial * k.factorial * l.factorial)
    else 0

/-- Kotesovec's conjecture: a(n) ~ 4^n/4!. -/
theorem main : (fun n : ℕ => (a n : ℝ)) ~[atTop] (fun n : ℕ => (4 : ℝ) ^ n / 24) := by
  sorry

end OMA.S_oeis_a092429
