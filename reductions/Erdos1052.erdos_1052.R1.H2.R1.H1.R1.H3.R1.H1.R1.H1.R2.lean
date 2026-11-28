import OMAReductions.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H3_R1_H1_R1
import Mathlib

-- Reduction Erdos1052.erdos_1052.R1.H2.R1.H1.R1.H3.R1.H1.R1.H1.R2 of step Erdos1052.erdos_1052.R1.H2.R1.H1.R1.H3.R1.H1.R1.H1
-- Credit: @PetrouilFan

/-!
# Bounding the 2-adic valuation under the table-3 witness bound

The target is hypothesis H1 of the merged reduction Erdos1052.erdos_1052.R1.H2.R1.H1.R1.H3.R1.H1.R1: the family of unitary
perfect numbers with at least two repeated odd primes, 3 in the repeated-prime
set S, a non-admissible kernel, and an odd-multiple residue of e(3) in the
25-row table 3.  A uniform bound on the 2-adic valuation on this family is open.

The merged reduction PROVES (theorem table3, from its mkill3_* lemmas) that the
firing residue forces a specific repeated prime into S: every entry of every
witness list L(3,d) is at least 5 and at most 926510094425921.  Hence the target
family carries a witness c in S with 5 <= c <= 926510094425921.  That structural
witness bound is the upstream bridge.

H1 asks for the uniform bound on this family with the witness bound written as
an explicit premise.  It is a proper weakening of the target: dropping that
premise recovers the target, while the bound itself remains the open part.

H2 is the proved upstream bridge.  Under the target hypotheses it supplies the
witness bound; its proof uses only theorem table3 of the merged reduction,
whose proof uses only the parent-proved kill lemmas, with no extra trusted constants.

`main` specializes H1 at the bound it supplies and discharges H1's extra premise
with H2.  Both hypotheses are load-bearing; neither restates the target, neither
mentions an answer, and there is no bookkeeping split.
-/

namespace OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H3_R1_H1_R1_H1_R2

/-- Open core: uniform 2-adic bound with the explicit table-3 witness bound. -/
def H1 : Prop :=
  ∃ A : ℕ, ∀ n : ℕ, Erdos1052.IsUnitaryPerfect n →
    ∀ S : Finset ℕ, (∀ p, p ∈ S ↔ p.Prime ∧ p ≠ 2 ∧ p ^ 2 ∣ n) → 2 ≤ S.card →
    ¬ ((∀ z ∈ S, 128 ≤ z ∧ S.card + 3 ≤ z) ∧
      ∏ z ∈ S, (((z : ℚ) + 1) / ((z : ℚ) - 2 - (S.card : ℚ))) ≤ 2101 / 2097) →
    3 ∈ S →
    ¬ (∀ d ∈ ({6, 8, 9, 10, 12, 14, 15, 16, 17, 20, 21, 22, 23, 25, 26, 28, 29, 31, 32, 33, 34, 35, 37, 38, 39} : Finset ℕ), n.factorization 3 % (2 * d) ≠ d) →
    (∀ dL ∈ ([(6, [73, 37, 19, 5]), (8, [193, 97, 7]), (9, [37, 19]), (10, [5]),
      (12, [41, 6481, 7]), (14, [29, 5]), (15, [61, 31]), (16, [21523361, 61, 31]),
      (17, [103, 13, 307, 7]), (20, [41, 42521761, 21260881, 10630441, 139, 7]),
      (21, [7]), (22, [5501, 570461, 3067, 13, 7]),
      (23, [23535794707, 79, 74480363, 98519, 5]), (25, [151, 19, 22996651, 29, 5]),
      (26, [4795973261, 266442959, 5]), (28, [41, 430697, 3121, 7]),
      (29, [5385997, 2692999, 5]), (31, [6883, 1721, 41, 7]),
      (32, [926510094425921, 6883, 1721, 41, 7]), (33, [661, 331, 83, 7]),
      (34, [956353, 68311, 8539, 5]), (35, [547, 137, 374857981681, 2851, 23]),
      (37, [18427, 271, 17]), (38, [5301533, 126227, 157, 79, 5]), (39, [157, 79])] : List (ℕ × List ℕ)),
      n.factorization 3 % (2 * dL.1) = dL.1 → ∃ c ∈ dL.2, c ∈ S) →
    (5 ∈ S → ∀ dL ∈ ([(6, [13, 601, 7]), (10, [13, 41, 7]), (14, [234750601, 5953, 13]),
      (20, [241, 11]), (26, [13]),
      (28, [59509429687890001, 29754714843945001, 83, 7679233, 769, 7]),
      (34, [13, 1973, 7])] : List (ℕ × List ℕ)),
      n.factorization 5 % (2 * dL.1) = dL.1 → ∃ c ∈ dL.2, c ∈ S) →
    (7 ∈ S → ∀ dL ∈ ([(2, [5]), (19, [351121, 419]), (32, [7699649, 5]), (37, [149, 5])] : List (ℕ × List ℕ)),
      n.factorization 7 % (2 * dL.1) = dL.1 → ∃ c ∈ dL.2, c ∈ S) →
    (∃ c ∈ S, 5 ≤ c ∧ c ≤ 926510094425921) →
    padicValNat 2 n ≤ A

/-- Proved upstream bridge: the table-3 witness lies in S and is bounded. -/
def H2 : Prop :=
  ∀ n : ℕ, Erdos1052.IsUnitaryPerfect n →
    ∀ S : Finset ℕ, (∀ p, p ∈ S ↔ p.Prime ∧ p ≠ 2 ∧ p ^ 2 ∣ n) → 2 ≤ S.card →
    ¬ ((∀ z ∈ S, 128 ≤ z ∧ S.card + 3 ≤ z) ∧
      ∏ z ∈ S, (((z : ℚ) + 1) / ((z : ℚ) - 2 - (S.card : ℚ))) ≤ 2101 / 2097) →
    3 ∈ S →
    ¬ (∀ d ∈ ({6, 8, 9, 10, 12, 14, 15, 16, 17, 20, 21, 22, 23, 25, 26, 28, 29, 31, 32, 33, 34, 35, 37, 38, 39} : Finset ℕ), n.factorization 3 % (2 * d) ≠ d) →
    (∀ dL ∈ ([(6, [73, 37, 19, 5]), (8, [193, 97, 7]), (9, [37, 19]), (10, [5]),
      (12, [41, 6481, 7]), (14, [29, 5]), (15, [61, 31]), (16, [21523361, 61, 31]),
      (17, [103, 13, 307, 7]), (20, [41, 42521761, 21260881, 10630441, 139, 7]),
      (21, [7]), (22, [5501, 570461, 3067, 13, 7]),
      (23, [23535794707, 79, 74480363, 98519, 5]), (25, [151, 19, 22996651, 29, 5]),
      (26, [4795973261, 266442959, 5]), (28, [41, 430697, 3121, 7]),
      (29, [5385997, 2692999, 5]), (31, [6883, 1721, 41, 7]),
      (32, [926510094425921, 6883, 1721, 41, 7]), (33, [661, 331, 83, 7]),
      (34, [956353, 68311, 8539, 5]), (35, [547, 137, 374857981681, 2851, 23]),
      (37, [18427, 271, 17]), (38, [5301533, 126227, 157, 79, 5]), (39, [157, 79])] : List (ℕ × List ℕ)),
      n.factorization 3 % (2 * dL.1) = dL.1 → ∃ c ∈ dL.2, c ∈ S) →
    (5 ∈ S → ∀ dL ∈ ([(6, [13, 601, 7]), (10, [13, 41, 7]), (14, [234750601, 5953, 13]),
      (20, [241, 11]), (26, [13]),
      (28, [59509429687890001, 29754714843945001, 83, 7679233, 769, 7]),
      (34, [13, 1973, 7])] : List (ℕ × List ℕ)),
      n.factorization 5 % (2 * dL.1) = dL.1 → ∃ c ∈ dL.2, c ∈ S) →
    (7 ∈ S → ∀ dL ∈ ([(2, [5]), (19, [351121, 419]), (32, [7699649, 5]), (37, [149, 5])] : List (ℕ × List ℕ)),
      n.factorization 7 % (2 * dL.1) = dL.1 → ∃ c ∈ dL.2, c ∈ S) →
    ∃ c ∈ S, 5 ≤ c ∧ c ≤ 926510094425921

theorem main : H1 → H2 → OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H3_R1_H1_R1.H1 := by
  rintro ⟨A, hA⟩ hwit
  unfold H2 at hwit
  refine ⟨A, fun n h S hS hc hna h3S hcl htab3 htab5 htab7 => ?_⟩
  exact hA n h S hS hc hna h3S hcl htab3 htab5 htab7 (hwit n h S hS hc hna h3S hcl htab3 htab5 htab7)

end OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H3_R1_H1_R1_H1_R2
