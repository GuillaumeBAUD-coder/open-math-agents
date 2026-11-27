import FormalConjectures.ErdosProblems.«94»

-- Reduction Erdos94.erdos_94.variants.regular_ngon.R1 of Erdős Problem 94 — regular ngon
-- Credit: @OrangeHeadz
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.
--
-- Write f(u) for the multiplicity of the distance u and S(P) for the sum of the f(u)^2.
-- The regular n-gon has S = n^2 (n-1) / 2 for odd n and S = n^3 / 2 - 3 n^2 / 4 for even n;
-- call this value B(n). The split isolates where the open difficulty lives:
--   H1  the regular n-gon reaches B(n) (an explicit computation, valid for every n);
--   H2  any n points in which no distance occurs more than n times have S at most B(n).
--       This is pure counting: the f(u) sum to n (n-1) / 2 and each is at most n, so for odd n
--       S <= n * (n (n-1) / 2), and for even n the sum of f (n - f) is at least n^2 / 4 because
--       g(f) = f (n - f) satisfies g(a) + g(b) >= g((a + b) mod n) and the f(u) sum to n / 2 mod n.
--       No convexity is needed; in particular every concyclic point set is covered;
--   H3  the remaining, genuinely open case: convex n-gons in which some distance occurs MORE
--       than n times (such polygons exist, e.g. the Edelsbrunner-Hajnal 2n - 7 construction).

namespace OMA.R_Erdos94_erdos_94_variants_regular_ngon_R1

open Filter EuclideanGeometry Erdos94

-- The regular n-gon attains the value B(n).
def H1 : Prop :=
  ∀ n : ℕ,
    (if n % 2 = 1 then (n : ℝ) ^ 2 * ((n : ℝ) - 1) / 2
      else (n : ℝ) ^ 3 / 2 - 3 * (n : ℝ) ^ 2 / 4) ≤
      ∑ u ∈ distanceSet (regularNGon n), (distanceMultiplicity (regularNGon n) u : ℝ) ^ 2

-- If no distance occurs more than n times, the bound B(n) holds (no convexity needed).
def H2 : Prop :=
  ∀ (n : ℕ) (P : Finset ℝ²), P.card = n →
    (∀ u ∈ distanceSet P, distanceMultiplicity P u ≤ n) →
    ∑ u ∈ distanceSet P, (distanceMultiplicity P u : ℝ) ^ 2 ≤
      (if n % 2 = 1 then (n : ℝ) ^ 2 * ((n : ℝ) - 1) / 2
        else (n : ℝ) ^ 3 / 2 - 3 * (n : ℝ) ^ 2 / 4)

-- The open core: convex n-gons in which some distance occurs more than n times.
def H3 : Prop :=
  ∀ᶠ n : ℕ in atTop, ∀ P : Finset ℝ², P.card = n → ConvexIndep (P : Set ℝ²) →
    (∃ u ∈ distanceSet P, n < distanceMultiplicity P u) →
    ∑ u ∈ distanceSet P, (distanceMultiplicity P u : ℝ) ^ 2 ≤
      (if n % 2 = 1 then (n : ℝ) ^ 2 * ((n : ℝ) - 1) / 2
        else (n : ℝ) ^ 3 / 2 - 3 * (n : ℝ) ^ 2 / 4)

theorem main : H1 → H2 → H3 → type_of% @Erdos94.erdos_94.variants.regular_ngon := by
  intro h1 h2 h3
  unfold H1 at h1
  unfold H2 at h2
  unfold H3 at h3
  refine h3.mono (fun n hn P hP hconv => le_trans ?_ (h1 n))
  by_cases hbig : ∃ u ∈ distanceSet P, n < distanceMultiplicity P u
  · exact hn P hP hconv hbig
  · exact h2 n P hP (fun u hu => not_lt.mp (fun hlt => hbig ⟨u, hu, hlt⟩))

end OMA.R_Erdos94_erdos_94_variants_regular_ngon_R1
