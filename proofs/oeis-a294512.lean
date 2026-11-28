import OMAStatements.S_oeis_a294512
import Mathlib

-- Disproof of the A294512 conjecture at n = 164.
-- Let V 164 = Sum_{k=0..164} 1/((k+1)(3k+1)) = N/D in lowest terms, so a 164 = D. The harmonic mean of the first
-- 165 octagonal numbers is 165/(N/D) = 165 D/N, and gcd(N, D) = 1, so its numerator is b 165 = 165 D/gcd(165, N).
-- The conjecture says gcd(n+1, N) = 1 always; here 11 divides N, so gcd(165, N) = 11 and b 165 = 15 D, not 165 D.
-- Both values are evaluated by the kernel (decide +kernel, no native code).

namespace A294512

open OMA.S_oeis_a294512

theorem a_164 : a 164 =
    1522900934001220110486931277055001102268627529692987106334059289643477906495044831840380532515782766923778283606417499970869839538732382536890476213388992000 := by
  decide +kernel

theorem b_165 : b (164 + 1) =
    22843514010018301657303969155825016534029412945394806595010889344652168597425672477605707987736741503856674254096262499563047593080985738053357143200834880000 := by
  decide +kernel

end A294512

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a294512.main) := by
  intro h
  have h1 := h 164
  rw [A294512.a_164, A294512.b_165] at h1
  norm_num at h1
