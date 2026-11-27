import FormalConjectures.ErdosProblems.«406»

-- Reduction Erdos406.erdos_406.variants.one_two.R1 of Erdős Problem 406 — one two
-- Credit: @tatashbar
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.
--
-- The claim is that 2 ^ 15 is the largest power of 2 whose base-3 digits are all 1 or 2.
-- main proves that 2 ^ 15 itself has this property and that every power 2 ^ k with k <= 15 is
-- at most 2 ^ 15. What remains is that no larger power of 2 qualifies, split at k = 1000:
--   H1: the finite range 15 < k <= 1000. This is a finite check. A direct computation shows
--       that for every such k a digit 0 already occurs among the 26 lowest base-3 digits of
--       2 ^ k, so it suffices to inspect 2 ^ k mod 3 ^ 26.
--   H2: every k > 1000. This is the open part of the problem.
-- Computation: among k <= 5000, the only powers 2 ^ k with base-3 digits in {1, 2} are
-- k = 0, 1, 2, 3, 4 and 15.

namespace OMA.R_Erdos406_erdos_406_variants_one_two_R1

/-- No power `2 ^ k` with `15 < k ≤ 1000` has all base-3 digits in `{1, 2}` (a finite check). -/
def H1 : Prop :=
  ∀ k : ℕ, 15 < k → k ≤ 1000 → ¬ Nat.digits 3 (2 ^ k) ⊆ [1, 2]

/-- No power `2 ^ k` with `k > 1000` has all base-3 digits in `{1, 2}` (the open part). -/
def H2 : Prop :=
  ∀ k : ℕ, 1000 < k → ¬ Nat.digits 3 (2 ^ k) ⊆ [1, 2]

theorem main : H1 → H2 → type_of% @Erdos406.erdos_406.variants.one_two := by
  intro h1 h2
  refine ⟨⟨⟨15, rfl⟩, ?_⟩, ?_⟩
  · norm_num
  · rintro n ⟨⟨k, rfl⟩, hd⟩
    by_contra hlt
    have hk : 15 < k := by
      by_contra h
      exact hlt (Nat.pow_le_pow_right (by norm_num) (by omega))
    rcases le_or_gt k 1000 with hk' | hk'
    · exact h1 k hk hk' hd
    · exact h2 k hk' hd

end OMA.R_Erdos406_erdos_406_variants_one_two_R1
