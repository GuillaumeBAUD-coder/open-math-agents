import FormalConjectures.ErdosProblems.«535»

/-!
Reduction of the conjectured upper bound to a uniform exponential bound for
integers with a fixed number of prime factors, an elementary arithmetic
extraction statement, and a numerical cutoff estimate.

For H2, remove the prime factors smaller than y. Their exponent vectors have
at most (L + 1)^y possibilities. The remaining part has at most K prime factors
when N < y^(K + 1). A largest fiber gives the stated extraction.

For H3, the intended cutoff is y approximately sqrt(log N), with L just above
log N / log 2 and K just above log N / log y. The logarithm of the extraction
cost is then O(log N / log log N).

The role of the stronger multiplicity-sensitive sunflower conjecture in this
problem is recorded in P. Erdős, Problems and Results on Combinatorial Number
Theory (1973), printed page 123, section 4, equations (4.1) and (4.3).
https://www.renyi.hu/~p_erdos/1973-21.pdf
-/

namespace OMA.R_Erdos535_erdos_535_R1

open Erdos535 Filter Real

/-- A uniform exponential bound for each fixed value of Ω. -/
def H1 : Prop :=
  ∀ r : ℕ, 3 ≤ r → ∃ C : ℝ, 1 ≤ C ∧
    ∀ (k : ℕ) (A : Finset ℕ),
      AllBigOmega k A → NoConstantPairwiseGcdCoprimeSubsets r A →
      (A.card : ℝ) ≤ C ^ k

/-- Extract a large layer after removing the small-prime part. -/
def H2 : Prop :=
  ∀ (N y L K : ℕ), 2 ≤ y → N < 2 ^ L → N < y ^ (K + 1) →
    ∀ A : Finset ℕ, A ⊆ Finset.Icc 1 N →
      ∃ (s k : ℕ) (B : Finset ℕ),
        0 < s ∧ k ≤ K ∧ AllBigOmega k B ∧
        A.card ≤ (L + 1) ^ y * (K + 1) * B.card ∧
        ∀ b ∈ B, s * b ∈ A

/-- Choose cutoffs whose counting cost has the required order of growth. -/
def H3 : Prop :=
  ∀ C : ℝ, 1 ≤ C → ∃ c > (0 : ℝ),
    ∀ᶠ (N : ℕ) in atTop,
      ∃ (y L K : ℕ), 2 ≤ y ∧ N < 2 ^ L ∧ N < y ^ (K + 1) ∧
        ((((L + 1) ^ y * (K + 1) : ℕ) : ℝ) * C ^ K) ≤
          (N : ℝ) ^ (c / log (log (N : ℝ)))

/-- Any common gcd among the quotient integers lifts under a common scale.
The original forbidden condition is stronger than the condition on quotients,
so this step requires no coprimality assumption on the scale. -/
lemma noConstant_of_scaled_members {r s : ℕ} {A B : Finset ℕ}
    (hs : 0 < s)
    (hA : ∀ S ⊆ A, S.card = r →
      ¬ (∃ d, (S : Set ℕ).Pairwise (fun a b => Nat.gcd a b = d)))
    (hBA : ∀ b ∈ B, s * b ∈ A) :
    NoConstantPairwiseGcdCoprimeSubsets r B := by
  classical
  intro S hSB hSr
  rintro ⟨d, _, hpair, _⟩
  let T := S.image (fun b => s * b)
  have hinj : Function.Injective (fun b : ℕ => s * b) := by
    intro b c hbc
    exact Nat.eq_of_mul_eq_mul_left hs hbc
  have hTA : T ⊆ A := by
    intro a ha
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp ha
    exact hBA b (hSB hb)
  have hTr : T.card = r := by
    rw [Finset.card_image_of_injective S hinj, hSr]
  apply hA T hTA hTr
  refine ⟨s * d, ?_⟩
  intro a ha b hb hab
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp ha
  obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hb
  have hxz : x ≠ z := fun h => hab (congrArg (fun q => s * q) h)
  rw [Nat.gcd_mul_left, hpair hx hz hxz]

/-- The arithmetic extraction and the uniform layer estimate give a finite
bound, before making any asymptotic choice of the cutoffs. -/
lemma finite_bound (hExtract : H2) {r N y L K : ℕ} {C : ℝ}
    (hC : 1 ≤ C)
    (hLayer : ∀ (k : ℕ) (B : Finset ℕ),
      AllBigOmega k B → NoConstantPairwiseGcdCoprimeSubsets r B →
      (B.card : ℝ) ≤ C ^ k)
    (hy : 2 ≤ y) (hL : N < 2 ^ L) (hK : N < y ^ (K + 1))
    (A : Finset ℕ) (hAN : A ⊆ Finset.Icc 1 N)
    (hA : ∀ S ⊆ A, S.card = r →
      ¬ (∃ d, (S : Set ℕ).Pairwise (fun a b => Nat.gcd a b = d))) :
    (A.card : ℝ) ≤ (((L + 1) ^ y * (K + 1) : ℕ) : ℝ) * C ^ K := by
  obtain ⟨s, k, B, hs, hk, hB, hsize, hBA⟩ :=
    hExtract N y L K hy hL hK A hAN
  have hfree : NoConstantPairwiseGcdCoprimeSubsets r B :=
    noConstant_of_scaled_members hs hA hBA
  have hBbound : (B.card : ℝ) ≤ C ^ K :=
    (hLayer k B hB hfree).trans (pow_le_pow_right₀ hC hk)
  have hsizeR : (A.card : ℝ) ≤
      (((L + 1) ^ y * (K + 1) : ℕ) : ℝ) * (B.card : ℝ) := by
    exact_mod_cast hsize
  exact hsizeR.trans (mul_le_mul_of_nonneg_left hBbound (by positivity))

/-- The supremum defining f is attained by a finite family. -/
lemma exists_extremal {r N : ℕ} (hr : 0 < r) :
    ∃ A : Finset ℕ, A ⊆ Finset.Icc 1 N ∧
      (∀ S ⊆ A, S.card = r →
        ¬ (∃ d, (S : Set ℕ).Pairwise (fun a b => Nat.gcd a b = d))) ∧
      A.card = f r N := by
  classical
  let D := {k : ℕ | ∃ A : Finset ℕ, A ⊆ Finset.Icc 1 N ∧
    (∀ S ⊆ A, S.card = r →
      ¬ (∃ d, (S : Set ℕ).Pairwise (fun a b => Nat.gcd a b = d))) ∧
    A.card = k}
  have hne : D.Nonempty := by
    refine ⟨0, ∅, Finset.empty_subset _, ?_, Finset.card_empty⟩
    intro S hS hSr
    have he : S = ∅ := Finset.subset_empty.mp hS
    simp only [he, Finset.card_empty] at hSr
    omega
  have hbounded : BddAbove D := by
    refine ⟨N, ?_⟩
    rintro k ⟨A, hAN, _, rfl⟩
    simpa using Finset.card_le_card hAN
  exact Nat.sSup_mem hne hbounded

theorem main : H1 → H2 → H3 → type_of% @Erdos535.erdos_535 := by
  intro hUniform hExtract hCutoffs r hr
  obtain ⟨C, hC, hLayer⟩ := hUniform r hr
  obtain ⟨c, hc, hN⟩ := hCutoffs C hC
  refine ⟨c, hc, ?_⟩
  filter_upwards [hN] with N hN
  obtain ⟨y, L, K, hy, hL, hK, hbound⟩ := hN
  obtain ⟨A, hAN, hA, hcard⟩ := exists_extremal (N := N) (by omega : 0 < r)
  rw [← hcard]
  exact (finite_bound hExtract hC hLayer hy hL hK A hAN hA).trans hbound

end OMA.R_Erdos535_erdos_535_R1
