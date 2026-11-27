import FormalConjectures.HilbertProblems.«17»
import Mathlib.FieldTheory.IsRealClosed.Basic

-- Reduction Hilbert17.hilbert_17th_problem.R1 of Hilbert17.hilbert_17th_problem
-- Credit: @green-notes

/-!
Reduces Hilbert's 17th problem (`Hilbert17.hilbert_17th_problem`) to the three pillars of
Artin's 1927 proof, while proving in-file that `MvRatFunc (Fin n) ℝ` is semireal:
1. `H1` (Artin-Schreier preordering theorem): in any semireal field `K`, any element `a` that is
   not a sum of squares is negative in some total field ordering on `K`.
2. `H2` (Existence of real closure): any ordered field embeds order-preservingly into a real
   closed ordered field.
3. `H3` (Tarski transfer principle): any multivariate real polynomial taking a negative value
   in some real closed extension of `ℝ` already takes a negative value on `ℝ`.
-/

namespace OMA.R_Hilbert17_hilbert_17th_problem_R1

open MvPolynomial

def H1 : Prop :=
  ∀ {K : Type} [Field K] [IsSemireal K] {a : K}, ¬ IsSumSq a →
    ∃ (_ : LinearOrder K) (_ : IsStrictOrderedRing K), a < 0

def H2 : Prop :=
  ∀ {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K],
    ∃ (R : Type) (_ : Field R) (_ : LinearOrder R) (_ : IsStrictOrderedRing R)
      (_ : IsRealClosed R) (ι : K →+* R), ∀ x : K, 0 ≤ x → 0 ≤ ι x

def H3 : Prop :=
  ∀ {n : ℕ} {R : Type} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R]
    (j : ℝ →+* R) (f : MvPolynomial (Fin n) ℝ),
    (∃ y : Fin n → R, MvPolynomial.eval₂ j y f < 0) →
    ∃ x : Fin n → ℝ, f.eval x < 0

section Helpers

lemma isSumSq_to_fin_sum {R : Type*} [CommRing R] {x : R} (hx : IsSumSq x) :
    ∃ (m : ℕ) (g : Fin m → R), x = ∑ i, (g i) ^ 2 := by
  induction hx with
  | zero => exact ⟨0, 0, by simp⟩
  | @sq_add a s _ ih =>
    obtain ⟨m, g, rfl⟩ := ih
    refine ⟨m + 1, Fin.cons a g, ?_⟩
    rw [Fin.sum_univ_succ]
    simp [pow_two]

lemma mvRatFunc_isSumSq_denom {n : ℕ} :
    ∀ s : MvRatFunc (Fin n) ℝ, IsSumSq s →
      ∃ D : MvPolynomial (Fin n) ℝ, D ≠ 0 ∧
        ∃ P : MvPolynomial (Fin n) ℝ, (∀ x : Fin n → ℝ, 0 ≤ P.eval x) ∧
          algebraMap (MvPolynomial (Fin n) ℝ) (MvRatFunc (Fin n) ℝ) D ^ 2 * s =
            algebraMap (MvPolynomial (Fin n) ℝ) (MvRatFunc (Fin n) ℝ) P := by
  intro s hs
  induction hs with
  | zero => exact ⟨1, one_ne_zero, 0, fun _ => le_rfl, by simp⟩
  | @sq_add a s _ ih =>
    obtain ⟨D, hD, P, hP, hEq⟩ := ih
    obtain ⟨⟨num, ⟨den, hden⟩⟩, ha_eq⟩ :=
      IsLocalization.surj (nonZeroDivisors (MvPolynomial (Fin n) ℝ)) a
    have hden0 : den ≠ 0 := nonZeroDivisors.ne_zero hden
    refine ⟨den * D, mul_ne_zero hden0 hD, (num * D) ^ 2 + den ^ 2 * P, fun x => ?_, ?_⟩
    · simp only [map_add, map_pow, map_mul]
      have hx := hP x
      positivity
    · have hcalc :
          algebraMap (MvPolynomial (Fin n) ℝ) (MvRatFunc (Fin n) ℝ) (den * D) ^ 2 * (a * a + s) =
            (a * algebraMap (MvPolynomial (Fin n) ℝ) (MvRatFunc (Fin n) ℝ) den *
              algebraMap (MvPolynomial (Fin n) ℝ) (MvRatFunc (Fin n) ℝ) D) ^ 2 +
            algebraMap (MvPolynomial (Fin n) ℝ) (MvRatFunc (Fin n) ℝ) den ^ 2 *
              (algebraMap (MvPolynomial (Fin n) ℝ) (MvRatFunc (Fin n) ℝ) D ^ 2 * s) := by
        rw [map_mul]
        ring
      rw [hcalc, ha_eq, hEq]
      simp only [map_add, map_pow, map_mul]

lemma mvRatFunc_isSemireal (n : ℕ) : IsSemireal (MvRatFunc (Fin n) ℝ) := by
  refine ⟨fun {s} hs h1s => ?_⟩
  obtain ⟨D, hD, P, hP, hEq⟩ := mvRatFunc_isSumSq_denom s hs
  have h0 : algebraMap (MvPolynomial (Fin n) ℝ) (MvRatFunc (Fin n) ℝ) (D ^ 2 + P) = 0 := by
    calc
      algebraMap (MvPolynomial (Fin n) ℝ) (MvRatFunc (Fin n) ℝ) (D ^ 2 + P) =
          algebraMap (MvPolynomial (Fin n) ℝ) (MvRatFunc (Fin n) ℝ) D ^ 2 +
            algebraMap (MvPolynomial (Fin n) ℝ) (MvRatFunc (Fin n) ℝ) P := by simp
      _ = algebraMap (MvPolynomial (Fin n) ℝ) (MvRatFunc (Fin n) ℝ) D ^ 2 * (1 + s) := by
          rw [← hEq]
          ring
      _ = 0 := by rw [h1s, mul_zero]
  have hDP : D ^ 2 + P = 0 :=
    IsFractionRing.injective (MvPolynomial (Fin n) ℝ) (MvRatFunc (Fin n) ℝ) (by simpa using h0)
  have hDeval : ∀ x : Fin n → ℝ, D.eval x = 0 := by
    intro x
    have hx := congrArg (MvPolynomial.eval x) hDP
    simp only [map_add, map_pow, map_zero] at hx
    have hsq : (D.eval x) ^ 2 = 0 := by nlinarith [sq_nonneg (D.eval x), hP x]
    exact sq_eq_zero_iff.mp hsq
  exact hD (MvPolynomial.funext fun x => by simpa using hDeval x)

end Helpers

theorem main : H1 → H2 → H3 → type_of% @Hilbert17.hilbert_17th_problem := by
  intro h1 h2 h3 n _ f hf
  by_contra hnot
  letI : IsSemireal (MvRatFunc (Fin n) ℝ) := mvRatFunc_isSemireal n
  have hnsq : ¬ IsSumSq (algebraMap (MvPolynomial (Fin n) ℝ) (MvRatFunc (Fin n) ℝ) f) :=
    fun hsq => hnot (isSumSq_to_fin_sum hsq)
  obtain ⟨ordK, hordK, hltK⟩ := h1 hnsq
  letI := ordK
  letI := hordK
  obtain ⟨R, fR, ordR, hordR, hrcR, ι, hι⟩ := h2 (K := MvRatFunc (Fin n) ℝ)
  letI := fR
  letI := ordR
  letI := hordR
  letI := hrcR
  let j : ℝ →+* R :=
    (ι.comp (algebraMap (MvPolynomial (Fin n) ℝ) (MvRatFunc (Fin n) ℝ))).comp MvPolynomial.C
  let y : Fin n → R :=
    fun i => ι (algebraMap (MvPolynomial (Fin n) ℝ) (MvRatFunc (Fin n) ℝ) (MvPolynomial.X i))
  have heval : MvPolynomial.eval₂ j y f =
      ι (algebraMap (MvPolynomial (Fin n) ℝ) (MvRatFunc (Fin n) ℝ) f) := by
    suffices ∀ p : MvPolynomial (Fin n) ℝ, MvPolynomial.eval₂ j y p =
        ι (algebraMap (MvPolynomial (Fin n) ℝ) (MvRatFunc (Fin n) ℝ) p) from this f
    intro p
    induction p using MvPolynomial.induction_on with
    | C a => simp [j]
    | add p q hp hq => simp [map_add, hp, hq]
    | mul_X p i hp => simp [y, map_mul, hp]
  have hltR : MvPolynomial.eval₂ j y f < 0 := by
    rw [heval]
    have hneg_pos : 0 < -(algebraMap (MvPolynomial (Fin n) ℝ) (MvRatFunc (Fin n) ℝ) f) :=
      neg_pos.mpr hltK
    have hle_neg : 0 ≤ ι (-(algebraMap (MvPolynomial (Fin n) ℝ) (MvRatFunc (Fin n) ℝ) f)) :=
      hι _ hneg_pos.le
    have hne_neg : ι (-(algebraMap (MvPolynomial (Fin n) ℝ) (MvRatFunc (Fin n) ℝ) f)) ≠ 0 :=
      (map_ne_zero ι).mpr hneg_pos.ne'
    rw [map_neg] at hle_neg hne_neg
    exact neg_pos.mp (lt_of_le_of_ne hle_neg hne_neg.symm)
  obtain ⟨x, hx⟩ := h3 j f ⟨y, hltR⟩
  exact not_lt_of_ge (hf x) hx

end OMA.R_Hilbert17_hilbert_17th_problem_R1
