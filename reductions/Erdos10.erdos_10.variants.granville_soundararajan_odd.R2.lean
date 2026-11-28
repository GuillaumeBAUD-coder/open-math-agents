import FormalConjectures.ErdosProblems.«10»
import Mathlib

-- Reduction Erdos10.erdos_10.variants.granville_soundararajan_odd.R2 of Erdős Problem 10
-- (Granville–Soundararajan, odd integers and three powers of two).
-- Credit: @MBimrose
--
-- The target is a conjunction, but its two halves are NOT independent. If `m` is odd and bigger
-- than one and `m = p + 2^a + 2^b + 2^c`, then `m + 1 = p + 2^0 + 2^a + 2^b + 2^c` is a prime plus
-- at most four powers of two. So the even half follows from the odd half, which is exactly the
-- "and hence" of the informal statement. H1 is the open conjecture; H2 is the parity transfer,
-- stated once and for all as "adding one costs one more power of two". Both are used by main.

namespace OMA.R_Erdos10_erdos_10_variants_granville_soundararajan_odd_R2

/-- Every odd `n > 1` is a prime plus a sum of at most three powers of two. -/
def H1 : Prop := {n : ℕ | Odd n ∧ 1 < n} ⊆ Erdos10.sumPrimeAndTwoPows 3

/-- Adding one to a number is a prime plus one more power of two: shift the exponent multiset by
`2 ^ 0 = 1`. (Monotonicity of `sumPrimeAndTwoPows` under `n ↦ n + 1` and `k ↦ k + 1`.) -/
def H2 : Prop :=
  ∀ (m k : ℕ), m ∈ Erdos10.sumPrimeAndTwoPows k → m + 1 ∈ Erdos10.sumPrimeAndTwoPows (k + 1)

theorem main : H1 → H2 →
    type_of% @Erdos10.erdos_10.variants.granville_soundararajan_odd := by
  intro h1 h2
  refine ⟨h1, ?_⟩
  rintro n ⟨hnEven, hn0⟩
  rcases eq_or_ne n 2 with rfl | hn2
  · exact ⟨2, 0, Nat.prime_two, by simp, by simp⟩
  · obtain ⟨k, hk⟩ := hnEven
    have h4 : 4 ≤ n := by omega
    have hodd : Odd (n - 1) := ⟨k - 1, by omega⟩
    have hgt : 1 < n - 1 := by omega
    have hm : n - 1 ∈ Erdos10.sumPrimeAndTwoPows 3 := h1 ⟨hodd, hgt⟩
    have hs : n - 1 + 1 ∈ Erdos10.sumPrimeAndTwoPows (3 + 1) := h2 (n - 1) 3 hm
    rwa [Nat.sub_add_cancel (by omega : 1 ≤ n)] at hs

end OMA.R_Erdos10_erdos_10_variants_granville_soundararajan_odd_R2
