import OMAReductions.R_Hadamard_HadamardConjecture_R1
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.NumberTheory.JacobiSum.Basic
import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic

/-! Paley's type TWO construction from finite-field quadratic characters. -/

namespace OMA.Paley

open Matrix Finset
open scoped BigOperators

section Field

variable (F : Type*) [Field F] [Fintype F] [DecidableEq F]

private theorem char_sum (hF : ringChar F ≠ 2) (y : F) :
    ∑ x : F, (quadraticChar F (x - y) : ℝ) = 0 := by
  let e : F ≃ F := Equiv.subRight y
  change (∑ x : F, (quadraticChar F (e x) : ℝ)) = 0
  rw [e.sum_comp (fun x => (quadraticChar F x : ℝ))]
  exact_mod_cast quadraticChar_sum_zero hF

/-- The column correlations of the matrix of quadratic characters. -/
private theorem char_correlation (hF : ringChar F ≠ 2) (a b : F) :
    ∑ x : F, (quadraticChar F (x - a) : ℝ) * (quadraticChar F (x - b) : ℝ)
      = if a = b then (Fintype.card F : ℝ) - 1 else -1 := by
  by_cases hab : a = b
  · subst b
    rw [if_pos rfl]
    have hterm (x : F) :
        (quadraticChar F (x-a) : ℝ) * (quadraticChar F (x-a) : ℝ) =
          if x = a then 0 else 1 := by
      by_cases h : x = a
      · simp [h, quadraticChar_zero]
      · rw [if_neg h, ← Int.cast_mul, ← sq, quadraticChar_sq_one (sub_ne_zero.mpr h)]
        norm_num
    simp_rw [hterm]
    rw [Finset.sum_ite]
    have hfilter : (univ.filter fun x : F => ¬ x = a) = univ.erase a := by
      ext x
      simp
    rw [hfilter]
    simp [Nat.cast_sub (Fintype.one_lt_card (α := F)).le]
  · rw [if_neg hab]
    let d := b - a
    have hd : d ≠ 0 := sub_ne_zero.mpr (fun h => hab h.symm)
    let e : F ≃ F := (Equiv.mulLeft₀ d hd).trans (Equiv.addLeft a)
    have h1 (t : F) : e t - a = d*t := by
      change a + d*t - a = d*t
      ring
    have h2 (t : F) : e t - b = d*(t-1) := by
      change a + d*t - b = d*(t-1)
      dsimp [d]
      ring
    have hval : ∑ x : F, quadraticChar F x * quadraticChar F (x - 1) = -1 := by
      have hinv := (quadraticChar_isQuadratic F).inv
      have hj := jacobiSum_nontrivial_inv (quadraticChar_ne_one hF)
      rw [hinv, jacobiSum] at hj
      calc
        (∑ x : F, quadraticChar F x * quadraticChar F (x - 1)) =
            ∑ x : F, (quadraticChar F x * quadraticChar F (1 - x)) *
              quadraticChar F (-1) := by
          apply sum_congr rfl
          intro x hx
          rw [show x - 1 = (1-x) * (-1) by ring, map_mul, mul_assoc]
        _ = -1 := by
          rw [← sum_mul, hj, neg_mul, ← sq, quadraticChar_sq_one (neg_ne_zero.mpr one_ne_zero)]
    rw [← e.sum_comp (fun x ↦ (quadraticChar F (x-a) : ℝ) * (quadraticChar F (x-b) : ℝ))]
    simp_rw [h1, h2, map_mul]
    have hterm (t : F) :
        ((quadraticChar F d * quadraticChar F t : ℤ) : ℝ) *
          ((quadraticChar F d * quadraticChar F (t - 1) : ℤ) : ℝ) =
            ((quadraticChar F t * quadraticChar F (t - 1) : ℤ) : ℝ) := by
      norm_cast
      calc
        _ = quadraticChar F d ^ 2 * (quadraticChar F t * quadraticChar F (t - 1)) := by ring
        _ = _ := by rw [quadraticChar_sq_one hd, one_mul]
    simp_rw [hterm]
    exact_mod_cast hval

private noncomputable def conference : Matrix (Option F) (Option F) ℝ
  | none, none => 0
  | none, some _ => 1
  | some _, none => quadraticChar F (-1)
  | some x, some y => quadraticChar F (x-y)

private theorem conference_diag (i : Option F) : conference F i i = 0 := by
  cases i <;> simp [conference, quadraticChar_zero]

private theorem conference_sign (i j : Option F) (hij : i ≠ j) :
    conference F i j ∈ ({1,-1} : Finset ℝ) := by
  simp only [mem_insert, mem_singleton]
  cases i with
  | none => cases j <;> simp_all [conference]
  | some x =>
    cases j with
    | none =>
      rcases quadraticChar_dichotomy (F := F) (neg_ne_zero.mpr one_ne_zero) with h | h
      · left; change (quadraticChar F (-1) : ℝ) = 1; exact_mod_cast h
      · right; change (quadraticChar F (-1) : ℝ) = -1; exact_mod_cast h
    | some y =>
      have hxy : x ≠ y := fun h => hij (congrArg some h)
      rcases quadraticChar_dichotomy (sub_ne_zero.mpr hxy) with h | h
      · left; change (quadraticChar F (x-y) : ℝ) = 1; exact_mod_cast h
      · right; change (quadraticChar F (x-y) : ℝ) = -1; exact_mod_cast h

private theorem conference_transpose (s : ℝ) (hs : (quadraticChar F (-1) : ℝ) = s)
    (hsq : s^2 = 1) :
    (conference F)ᵀ = s • conference F := by
  ext i j
  change conference F j i = s * conference F i j
  cases i <;> cases j <;> simp only [conference, hs, mul_zero, mul_one]
  · simpa [sq] using hsq.symm
  · rename_i x y
    rw [show y-x = (-1)*(x-y) by ring, map_mul, Int.cast_mul, hs]

private theorem conference_orthogonal (hF : ringChar F ≠ 2) :
    (conference F)ᵀ * conference F = (Fintype.card F : ℕ) := by
  ext i j
  rw [Matrix.mul_apply, Fintype.sum_option, Matrix.transpose_apply, Matrix.natCast_apply]
  cases i <;> cases j <;> simp only [conference, Matrix.transpose_apply]
  · have hx : (quadraticChar F (-1) : ℝ) ^ 2 = 1 := by
      exact_mod_cast quadraticChar_sq_one (F := F) (neg_ne_zero.mpr one_ne_zero)
    simp only [← sq, hx, sum_const, card_univ, nsmul_eq_mul, mul_one]
    norm_num
  · rw [← mul_sum, char_sum F hF]
    simp
  · rw [← sum_mul, char_sum F hF]
    simp
  · rename_i a b
    rw [char_correlation F hF]
    by_cases h : a = b <;> simp [h]


private theorem ortho_reindex {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ}
    (e : Fin n ≃ ι) (A : Matrix ι ι ℝ) (hpm : ∀ i j, A i j ∈ ({1, -1} : Finset ℝ))
    (hA : Aᵀ * A = (n : Matrix ι ι ℝ)) :
    ∃ M, Hadamard.IsHadamard' (n := n) M := by
  refine ⟨A.submatrix e e, fun i j => hpm (e i) (e j), ?_⟩
  rw [transpose_submatrix, submatrix_mul_equiv, hA]
  ext i j
  simp [Matrix.natCast_apply, Matrix.submatrix_apply]

private theorem plus_minus_signs (i j : Option F) :
    (conference F + 1) i j ∈ ({1, -1} : Finset ℝ) ∧
    (conference F - 1) i j ∈ ({1, -1} : Finset ℝ) := by
  by_cases h : i = j
  · subst j
    simp [conference_diag F, Matrix.one_apply]
  · simpa [Matrix.one_apply, h] using
      And.intro (conference_sign F i j h) (conference_sign F i j h)

private theorem neg_sign {x : ℝ} (hx : x ∈ ({1,-1} : Finset ℝ)) :
    -x ∈ ({1,-1} : Finset ℝ) := by
  simp only [mem_insert, mem_singleton] at hx ⊢
  rcases hx with rfl | rfl <;> norm_num

theorem type_two (hF : ringChar F ≠ 2) (hs : quadraticChar F (-1) = 1) :
    ∃ M, Hadamard.IsHadamard' (n := 2 * (Fintype.card F + 1)) M := by
  let C := conference F
  let P := C + 1
  let Q := C - 1
  let A := fromBlocks P Q Q (-P)
  have hsymm : Cᵀ = C := by
    simpa [C] using conference_transpose F 1 (by exact_mod_cast hs) (by norm_num)
  have hgram : C * C = (Fintype.card F : Matrix (Option F) (Option F) ℝ) := by
    simpa only [C, hsymm] using conference_orthogonal F hF
  have he : Fintype.card (Option F ⊕ Option F) = 2 * (Fintype.card F + 1) := by
    simp [two_mul]
  let e := (finCongr he.symm).trans (Fintype.equivFin (Option F ⊕ Option F)).symm
  refine ortho_reindex e A ?_ ?_
  · intro i j
    cases i <;> cases j
    · exact (plus_minus_signs F _ _).1
    · exact (plus_minus_signs F _ _).2
    · exact (plus_minus_signs F _ _).2
    · exact neg_sign (plus_minus_signs F _ _).1
  · have hd : P * P + Q * Q = (2 * (Fintype.card F + 1) : ℕ) := by
      calc
        P * P + Q * Q = C*C + C*C + 1 + 1 := by dsimp [P,Q]; noncomm_ring
        _ = _ := by rw [hgram]; push_cast; noncomm_ring
    have hcross : P * Q = Q * P := by dsimp [P,Q]; noncomm_ring
    trans fromBlocks
      (2 * (Fintype.card F + 1) : ℕ) 0 0 (2 * (Fintype.card F + 1) : ℕ)
    · dsimp [A]
      rw [fromBlocks_transpose, fromBlocks_multiply]
      have hp : Pᵀ = P := by simp [P, hsymm]
      have hq : Qᵀ = Q := by simp [Q, hsymm]
      simp only [hp, hq, transpose_neg, mul_neg, neg_mul, neg_neg, hd, ← hcross,
        add_neg_cancel, neg_add_cancel, add_comm (Q * Q)]
    · ext i j
      cases i <;> cases j <;> simp only [fromBlocks_apply₁₁, fromBlocks_apply₁₂,
        fromBlocks_apply₂₁, fromBlocks_apply₂₂, Matrix.zero_apply, Matrix.natCast_apply,
        Sum.inl.injEq, Sum.inr.injEq, Sum.inl_ne_inr, Sum.inr_ne_inl, if_false, Nat.cast_zero]


end Field

private theorem field_of_prime_power (q : ℕ) (hq : IsPrimePow q) :
    ∃ (F : Type) (_ : Field F) (_ : Fintype F), Fintype.card F = q := by
  obtain ⟨p, k, hp, hk, rfl⟩ := hq
  letI : Fact p.Prime := ⟨Nat.prime_iff.mpr hp⟩
  letI : Fintype (GaloisField p k) := Fintype.ofFinite _
  exact ⟨GaloisField p k, inferInstance, inferInstance, by
    rw [Fintype.card_eq_nat_card]
    exact GaloisField.card p k hk.ne'⟩

theorem prime_power_type_two (q : ℕ) (hq : IsPrimePow q) (hmod : q % 4 = 1) :
    ∃ M, Hadamard.IsHadamard' (n := 2*(q+1)) M := by
  classical
  obtain ⟨F, hField, hFinite, hcard⟩ := field_of_prime_power q hq
  letI : Field F := hField
  letI : Fintype F := hFinite
  have hF : ringChar F ≠ 2 := by
    intro h
    have := FiniteField.even_card_of_char_two (F := F) h
    have hc : Fintype.card F = q := hcard
    omega
  have hs : quadraticChar F (-1) = 1 := by
    rw [quadraticChar_neg_one hF, ZMod.χ₄_nat_eq_if_mod_four, hcard]
    simp [show q % 2 ≠ 0 by omega, hmod]
  rw [← hcard]
  exact type_two F hF hs

end OMA.Paley

theorem OMA.solution : OMA.R_Hadamard_HadamardConjecture_R1.H2 :=
  OMA.Paley.prime_power_type_two
