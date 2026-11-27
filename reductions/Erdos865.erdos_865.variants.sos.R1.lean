import FormalConjectures.ErdosProblems.«865»

/-!
Reduction R1 of `Erdos865.erdos_865.variants.sos` (the Erdős–Sós asymptotic for every k ≥ 2).

The conjectured asymptotic `f_k(N) ~ (1/2)(1 + Σ_{1 ≤ r ≤ k-2} 4^{-r}) N` is split by `k`:
* H1, `k = 2`: `f_2(N) ~ N/2`. This is the folklore case: a set with more than about `N/2` elements
  contains two elements whose sum is in the set, and the upper half `(N/2, N]` has no such pair.
* H2, `k = 3`: `f_3(N) ~ 5N/8`. This is the main Erdős problem 865, proved with `f_3(N) = 5N/8 + O(1)`
  (Cipollini, arXiv:2606.29361).
* H3, `k ≥ 4`: the open part.
The two solved cases are separated from the open core, so each can be proved on its own.
-/

namespace OMA.R_Erdos865_erdos_865_variants_sos_R1

open Filter Asymptotics Finset Erdos865

/-- The case `k = 2`. -/
def H1 : Prop :=
  (fun N ↦ (f N 2 : ℝ)) ~[atTop]
    (fun N ↦ (1 / 2 : ℝ) * (1 + ∑ r ∈ Icc 1 (2 - 2), (1 / 4 : ℝ) ^ r) * N)

/-- The case `k = 3` (Erdős problem 865 itself, in asymptotic form). -/
def H2 : Prop :=
  (fun N ↦ (f N 3 : ℝ)) ~[atTop]
    (fun N ↦ (1 / 2 : ℝ) * (1 + ∑ r ∈ Icc 1 (3 - 2), (1 / 4 : ℝ) ^ r) * N)

/-- The open part: every `k ≥ 4`. -/
def H3 : Prop :=
  ∀ k : ℕ, 4 ≤ k →
    (fun N ↦ (f N k : ℝ)) ~[atTop]
      (fun N ↦ (1 / 2 : ℝ) * (1 + ∑ r ∈ Icc 1 (k - 2), (1 / 4 : ℝ) ^ r) * N)

theorem main : H1 → H2 → H3 → type_of% @Erdos865.erdos_865.variants.sos := by
  intro h1 h2 h3 k hk
  by_cases e2 : k = 2
  · subst e2; exact h1
  by_cases e3 : k = 3
  · subst e3; exact h2
  exact h3 k (by omega)

end OMA.R_Erdos865_erdos_865_variants_sos_R1

