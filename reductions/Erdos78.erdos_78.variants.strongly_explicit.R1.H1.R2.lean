import OMAReductions.R_Erdos78_erdos_78_variants_strongly_explicit_R1
namespace OMA.R_Erdos78_erdos_78_variants_strongly_explicit_R1_H1_R2
open Filter Real ComplexityTheory Erdos78

-- Reduction Erdos78.erdos_78.variants.strongly_explicit.R1.H1.R2 (range avoidance route)
-- Source of the idea: O. Korten, The Hardest Explicit Construction (FOCS 2021), Theorem 4 and
-- Corollary 1: strongly explicit O(log n)-Ramsey graphs reduce to range avoidance. A graph on
-- 2^k vertices is described by a short seed; every seed whose graph has a large clique or
-- independent set can be written down with fewer bits, so it lies in the range of a fixed
-- poly-time compression map. Any seed outside that range is a Ramsey graph.
-- H1 (OPEN core): poly-time range avoidance for UNIFORM poly-time maps: for every poly-time map
--   f and every polynomial length A = p(n) + 1 there is a poly-time g such that, for all large n,
--   g(2^n) is a string of A^3 bits that is not f(2^n, x) for any x of at most A^3 - A bits
--   (so the map stretches its input by the cube root of the output length). This is the
--   question studied by Korten-Santhanam (ECCC TR25-104, Question 1 and 2), Ren-Santhanam-Wang
--   (FOCS 2022) and Ilango-Li-Williams (STOC 2023). Only the uniform version is
--   used: range avoidance for arbitrary circuits is believed to be hard.
-- H2 (true, pure construction): there is a poly-time seeded graph family dec and a poly-time
--   compression map cmp such that every seed outside the range of cmp gives a graph on 2^k
--   vertices with no clique and no independent set of size c*k.
-- H3 (true, engineering): feeding the output of one poly-time map into another, next to the
--   original input, stays poly-time.
-- The step follows from H1, H2 and H3: the oracle first computes the seed g(2^k), then decodes.

/-- H1 (OPEN core): polynomial-time range avoidance for uniform polynomial-time maps, with
stretch from A^3 - A bits to A^3 bits, where A = p(n) + 1 for an arbitrary polynomial p. -/
def H1 : Prop := ∀ f : ℕ × ℕ → ℕ, IsPolyTime f → ∀ p : Polynomial ℕ, ∃ g : ℕ → ℕ, IsPolyTime g ∧
  ∀ᶠ n : ℕ in atTop, g (2 ^ n) < 2 ^ ((p.eval n + 1) ^ 3) ∧
    ∀ x : ℕ, x < 2 ^ ((p.eval n + 1) ^ 3 - (p.eval n + 1)) → f (2 ^ n, x) ≠ g (2 ^ n)

/-- H2 (true): a poly-time seeded family of graphs on 2^k vertices together with a poly-time
compression map whose range contains every seed with a clique or independent set of size c*k. -/
def H2 : Prop := ∃ c > (0 : ℝ), ∃ p : Polynomial ℕ, ∃ dec : ℕ × ℕ × ℕ × ℕ → Bool,
  ∃ cmp : ℕ × ℕ → ℕ, IsPolyTime dec ∧ IsPolyTime cmp ∧
  ∀ᶠ k : ℕ in atTop, ∀ s : ℕ, s < 2 ^ ((p.eval k + 1) ^ 3) →
    (∀ x : ℕ, x < 2 ^ ((p.eval k + 1) ^ 3 - (p.eval k + 1)) → cmp (2 ^ k, x) ≠ s) →
    NoHomogeneousSet
      (SimpleGraph.fromRel fun u v : Fin (2 ^ k) => dec (s, 2 ^ k, (u : ℕ), (v : ℕ))) ⌈c * k⌉₊

/-- H3 (true, engineering): pairing the output of a poly-time map with its input and feeding
the result to a poly-time map is poly-time. -/
def H3 : Prop := ∀ (g : ℕ → ℕ) (dec : ℕ × ℕ × ℕ × ℕ → Bool), IsPolyTime g → IsPolyTime dec →
  IsPolyTime (fun x : ℕ × ℕ × ℕ => dec (g x.1, x))

theorem main : H1 → H2 → H3 → OMA.R_Erdos78_erdos_78_variants_strongly_explicit_R1.H1 := by
  rintro h1 ⟨c, hc, p, dec, cmp, hdec, hcmp, hev⟩ h3
  obtain ⟨g, hg, hgev⟩ := h1 cmp hcmp p
  refine ⟨c, hc, fun x : ℕ × ℕ × ℕ => dec (g x.1, x), h3 g dec hg hdec, ?_⟩
  filter_upwards [hev, hgev] with k hk hgk
  exact hk (g (2 ^ k)) hgk.1 hgk.2

end OMA.R_Erdos78_erdos_78_variants_strongly_explicit_R1_H1_R2
