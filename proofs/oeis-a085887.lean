import OMAStatements.S_oeis_a085887
import Mathlib

/-!
# OEIS A085887: the three claims, read literally, are not all true

`a(n)` is the minimum of `τ(r) + τ(s)` over `r + s = n` with `r, s ≥ 1`.

The second claim says `a(n) = 4` whenever `n` is a sum of two primes. But `4 = 2 + 2` is a sum
of two primes, while the splitting `4 = 1 + 3` has `τ(1) + τ(3) = 1 + 2 = 3`, so `a(4) ≤ 3`.
(The claim overlooks that `n - 1` may be prime, in which case `a(n) = 3` by the first claim.)
-/

open OMA.S_oeis_a085887

namespace OMA.A085887

/-- `a(4) ≤ 3`, witnessed by `4 = 1 + 3`. -/
lemma a_four_le : a 4 ≤ 3 := by
  apply Nat.sInf_le
  refine ⟨1, 3, le_refl 1, by norm_num, by norm_num, ?_⟩
  decide

end OMA.A085887

open OMA.A085887 in
theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a085887.main) := by
  rintro ⟨-, h2, -⟩
  have h4 : a 4 = 4 := h2 4 ⟨2, 2, Nat.prime_two, Nat.prime_two, rfl⟩
  have := a_four_le
  omega
