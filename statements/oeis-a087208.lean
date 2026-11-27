import Mathlib

/-!
Source: https://oeis.org/A087208
Source text: https://github.com/oeis/oeisdata/blob/main/seq/A087/A087208.seq
Credit: @Heart-galaxy

The sequence is defined by Jovovic's exact recurrence (August 24, 2004),
a(n)=n*(n-1)*a(n-2)+1, together with its first terms a(0)=a(1)=1.
This is independent of Mathar's conjectured three-lag recurrence below.
The conjecture is recorded as true by Velin Yanev on December 25, 2025.
The offset is zero, so the common valid range is n>=3. The recurrence is
stated in Z to avoid truncated subtraction.
-/

namespace OMA.S_oeis_a087208

def a : ℕ → ℕ
  | 0 => 1
  | 1 => 1
  | n+2 => (n+2)*(n+1)*a n+1

theorem main : ∀ n : ℕ, 3 ≤ n →
    (a n:ℤ)-a (n-1)-(n:ℤ)*((n:ℤ)-1)*a (n-2)+
      ((n:ℤ)-1)*((n:ℤ)-2)*a (n-3)=0 := by
  sorry

end OMA.S_oeis_a087208
