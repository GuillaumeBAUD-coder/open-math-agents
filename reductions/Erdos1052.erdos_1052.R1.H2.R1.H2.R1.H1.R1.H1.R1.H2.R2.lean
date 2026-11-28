import OMAReductions.R_Erdos1052_erdos_1052_R1_H2_R1_H2_R1_H1_R1_H1_R1
import Mathlib

-- Reduction Erdos1052.erdos_1052.R1.H2.R1.H2.R1.H1.R1.H1.R1.H2.R2 of step Erdos1052.erdos_1052.R1.H2.R1.H2.R1.H1.R1.H1.R1.H2
-- Credit: @PetrouilFan

/-!
# Splitting the thin-kernel 607/3967 case: proved dichotomy / open bound

The target is the hypothesis H2 of the merged reduction Erdos1052.erdos_1052.R1.H2.R1.H2.R1.H1.R1.H1.R1: the
223/607/3967 family with a thin kernel.  A proved dichotomy isolates the
sub-cases 8191 | n or 7933 | n; bounding the 2-adic valuation on that remaining
family is the genuinely open part.

H1 asks for a uniform bound on the 2-adic valuation of every n in the target
family that also satisfies the (substantive) dichotomy premise.  It is a proper
weakening of the target: dropping that premise recovers the target, and the
bound is still open -- the merged sibling reduction R1 had to split it further
into the two sub-cases 8191 | n and 7933 | n.

H2 is the proved upstream bridge.  From the target's hypotheses it derives
8191 | n or 7933 | n; its proof uses only declarations already proved in the
merged parent and in the merged sibling Erdos1052.erdos_1052.R1.H2.R1.H2.R1.H1.R1.H1.R1.H2.R1 (thin_split), with #print
axioms restricted to propext, Classical.choice and Quot.sound.

`main` specializes H1 at the bound it supplies and discharges H1's extra
premise with H2.  Neither hypothesis restates the target, neither mentions an
answer, and both are load-bearing.
-/

namespace OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H2_R1_H1_R1_H1_R1_H2_R2

/-- Open core: uniform 2-adic bound on the thin-kernel family, assuming the
8191/7933 dichotomy. -/
def H1 : Prop :=
  ∃ A : ℕ, ∀ n : ℕ, Erdos1052.IsUnitaryPerfect n → ¬ Squarefree (n / 2 ^ padicValNat 2 n) →
    ∀ S : Finset ℕ, (∀ p, p ∈ S ↔ p.Prime ∧ p ≠ 2 ∧ p ^ 2 ∣ n) →
    (∀ z ∈ S, 128 ≤ z ∧ S.card + 3 ≤ z) →
    ∏ z ∈ S, (((z : ℚ) + 1) / ((z : ℚ) - 2 - (S.card : ℚ))) ≤ 2101 / 2097 →
    4 ∣ padicValNat 2 n → 3 ∣ n → 5 ∣ n → 7 ∣ n → 19 ∣ n →
    (∀ N : Finset ℕ, S ⊆ N → (∀ z ∈ N, z.Prime ∧ 128 ≤ z ∧ N.card + 3 ≤ z) →
      ∏ z ∈ N, (((z : ℚ) + 1) / ((z : ℚ) - 2 - (N.card : ℚ))) ≤ 2101 / 2097 →
      (∃ z ∈ N, z ∣ 2 ^ padicValNat 2 n + 1 ∧ z % 3 = 2) ∧
      ∀ z ∈ N, z % 3 = 2 → Even (n.factorization z)) →
    16 ∣ padicValNat 2 n → padicValNat 2 n % 64 ≠ 32 →
    31 ∣ n →
    (∀ q : ℕ, q.Prime → q ∣ n → q < 5057 →
      q = 2 ∨ q = 3 ∨ q = 5 ∨ q = 7 ∨ q = 19 ∨ q = 31 ∨ q = 223 ∨ q = 607 ∨ q = 3967) →
    223 ∣ n → 607 ∣ n → 3967 ∣ n → 48 ≤ padicValNat 2 n →
    ∏ z ∈ S, (1 + 5 / (z : ℚ)) ≤ 5001 / 5000 →
    (8191 ∣ n ∨ 7933 ∣ n) →
    padicValNat 2 n ≤ A

/-- Proved upstream bridge: the 8191/7933 dichotomy under the target's
hypotheses (merged sibling Erdos1052.erdos_1052.R1.H2.R1.H2.R1.H1.R1.H1.R1.H2.R1, theorem thin_split). -/
def H2 : Prop :=
  ∀ n : ℕ, Erdos1052.IsUnitaryPerfect n → ¬ Squarefree (n / 2 ^ padicValNat 2 n) →
    ∀ S : Finset ℕ, (∀ p, p ∈ S ↔ p.Prime ∧ p ≠ 2 ∧ p ^ 2 ∣ n) →
    (∀ z ∈ S, 128 ≤ z ∧ S.card + 3 ≤ z) →
    ∏ z ∈ S, (((z : ℚ) + 1) / ((z : ℚ) - 2 - (S.card : ℚ))) ≤ 2101 / 2097 →
    4 ∣ padicValNat 2 n → 3 ∣ n → 5 ∣ n → 7 ∣ n → 19 ∣ n →
    (∀ N : Finset ℕ, S ⊆ N → (∀ z ∈ N, z.Prime ∧ 128 ≤ z ∧ N.card + 3 ≤ z) →
      ∏ z ∈ N, (((z : ℚ) + 1) / ((z : ℚ) - 2 - (N.card : ℚ))) ≤ 2101 / 2097 →
      (∃ z ∈ N, z ∣ 2 ^ padicValNat 2 n + 1 ∧ z % 3 = 2) ∧
      ∀ z ∈ N, z % 3 = 2 → Even (n.factorization z)) →
    16 ∣ padicValNat 2 n → padicValNat 2 n % 64 ≠ 32 →
    31 ∣ n →
    (∀ q : ℕ, q.Prime → q ∣ n → q < 5057 →
      q = 2 ∨ q = 3 ∨ q = 5 ∨ q = 7 ∨ q = 19 ∨ q = 31 ∨ q = 223 ∨ q = 607 ∨ q = 3967) →
    223 ∣ n → 607 ∣ n → 3967 ∣ n → 48 ≤ padicValNat 2 n →
    ∏ z ∈ S, (1 + 5 / (z : ℚ)) ≤ 5001 / 5000 →
    8191 ∣ n ∨ 7933 ∣ n

theorem main : H1 → H2 → OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H2_R1_H1_R1_H1_R1.H2 := by
  rintro ⟨A, hA⟩ hsplit
  unfold H2 at hsplit
  refine ⟨A, fun n h hsq S hS hadm1 hadm2 h4 h3 h5 h7 h19 hres h16 h64 h31 hl
    h223 h607 h3967 h48 hk => ?_⟩
  exact hA n h hsq S hS hadm1 hadm2 h4 h3 h5 h7 h19 hres h16 h64 h31 hl
      h223 h607 h3967 h48 hk (hsplit n h hsq S hS hadm1 hadm2 h4 h3 h5 h7 h19 hres h16 h64 h31 hl
      h223 h607 h3967 h48 hk)

end OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H2_R1_H1_R1_H1_R1_H2_R2
