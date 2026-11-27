import OMAReductions.R_Hadamard_HadamardConjecture_R1
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.NumberTheory.JacobiSum.Basic
import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic

/-! Paley conference matrices over odd finite fields, via quadratic character correlations. -/
namespace OMA.Had
open Finset Matrix
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

theorem paley_corr_int (hF : ringChar F ≠ 2) {a b : F} (hab : a ≠ b) :
    ∑ x : F, quadraticChar F (x-a) * quadraticChar F (x-b) = -1 := by
  let χ := quadraticChar F
  have jac := jacobiSum_nontrivial_inv (quadraticChar_ne_one hF)
  rw [(quadraticChar_isQuadratic F).inv] at jac
  change (∑ t : F, χ t * χ (1-t)) = -χ (-1) at jac
  have hsq : χ (b-a)^2 = 1 := quadraticChar_sq_one (sub_ne_zero.mpr hab.symm)
  have hneg : χ (-1)^2 = 1 := quadraticChar_sq_one (neg_ne_zero.mpr one_ne_zero)
  let e := (Equiv.mulLeft₀ (b-a) (sub_ne_zero.mpr hab.symm)).trans (Equiv.addRight a)
  calc
    _ = ∑ t : F, χ (e t-a) * χ (e t-b) := (e.sum_comp _).symm
    _ = ∑ t : F, χ (-1) * (χ t * χ (1-t)) := by
      apply sum_congr rfl
      intro t _
      change χ ((b-a)*t+a-a) * χ ((b-a)*t+a-b) = _
      rw [add_sub_cancel_right, show (b-a)*t+a-b = (b-a)*((-1)*(1-t)) by ring]
      simp only [map_mul]
      linear_combination (χ (-1) * χ t * χ (1-t)) * hsq
    _ = -1 := by rw [← mul_sum, jac]; nlinarith

theorem paley_corr (hF : ringChar F ≠ 2) {a b : F} (hab : a ≠ b) :
    ∑ x : F, (quadraticChar F (x-a) : ℝ) * (quadraticChar F (x-b) : ℝ) = -1 := by
  exact_mod_cast paley_corr_int hF hab

noncomputable def conf (F : Type*) [Field F] [Fintype F] [DecidableEq F] :
    Matrix (Option F) (Option F) ℝ
  | none, none => 0
  | none, some _ => 1
  | some _, none => quadraticChar F (-1)
  | some a, some b => quadraticChar F (a-b)

theorem paley_shift (hF : ringChar F ≠ 2) (a : F) :
    ∑ x : F, (quadraticChar F (x-a) : ℝ) = 0 := by
  have h : (∑ x : F, quadraticChar F (x-a)) = 0 := by
    exact ((Equiv.subRight a).sum_comp _).trans (quadraticChar_sum_zero hF)
  exact_mod_cast h

theorem paley_gram (hF : ringChar F ≠ 2) :
    (conf F).transpose * conf F = diagonal (fun _ => (Fintype.card F : ℝ)) := by
  ext i j
  rw [mul_apply, Fintype.sum_option]
  simp only [transpose_apply]
  have hneg : (quadraticChar F (-1) : ℝ) ^ 2 = 1 := by
    exact_mod_cast quadraticChar_sq_one (neg_ne_zero.mpr (one_ne_zero' F))
  cases i with
  | none => cases j with
    | none =>
      simp only [conf, ← sq, hneg, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one, diagonal_apply_eq]
      norm_num
    | some b =>
      simp only [conf, zero_mul, zero_add, diagonal_apply_ne _ (by simp : none ≠ some b)]
      rw [← mul_sum, paley_shift hF, mul_zero]
  | some a => cases j with
    | none =>
      simp only [conf, mul_zero, zero_add, diagonal_apply_ne _ (by simp : some a ≠ none)]
      rw [← sum_mul, paley_shift hF, zero_mul]
    | some b =>
      by_cases hab : a = b
      · subst b
        simp only [conf, one_mul, diagonal_apply_eq]
        have term (x : F) : (quadraticChar F (x-a) : ℝ) * (quadraticChar F (x-a) : ℝ) =
            if x = a then 0 else 1 := by
          split_ifs with h
          · simp [h]
          · rw [← sq]; exact_mod_cast quadraticChar_sq_one (sub_ne_zero.mpr h)
        have indicator (x : F) : (if x = a then (0 : ℝ) else 1) = 1 - (if x = a then 1 else 0) := by
          split_ifs <;> norm_num
        simp_rw [term, indicator]
        rw [Finset.sum_sub_distrib]
        simp
      · simp only [conf, one_mul, diagonal_apply_ne _ (by simpa using hab : some a ≠ some b)]
        rw [paley_corr hF hab]; norm_num
theorem paley_transpose :
    (conf F).transpose = (quadraticChar F (-1) : ℝ) • conf F := by
  ext i j
  have sq : (quadraticChar F (-1) : ℝ)^2 = 1 := by
    exact_mod_cast quadraticChar_sq_one (neg_ne_zero.mpr (one_ne_zero' F))
  cases i <;> cases j
  · simp [conf]
  · simp [conf]
  · simpa [conf, ← pow_two] using sq.symm
  · rename_i a b
    change (quadraticChar F (b-a) : ℝ) = (quadraticChar F (-1) : ℝ) * (quadraticChar F (a-b) : ℝ)
    rw [show b-a = (-1)*(a-b) by ring, map_mul, Int.cast_mul]
end OMA.Had

namespace OMA.Had
open Matrix
private def PaleyHas (n : ℕ) : Prop := ∃ M : Matrix (Fin n) (Fin n) ℝ,
  (∀ i j, M i j = 1 ∨ M i j = -1) ∧ M.transpose * M = diagonal (fun _ => (n : ℝ))

private lemma movePaley {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ}
    (hc : Fintype.card ι = n) (M : Matrix ι ι ℝ)
    (he : ∀ i j, M i j = 1 ∨ M i j = -1) (hg : M.transpose * M = n) : PaleyHas n := by
  let e := (Fintype.equivFinOfCardEq hc).symm
  refine ⟨M.submatrix e e, fun i j => he _ _, ?_⟩
  change M.transpose.submatrix e e * M.submatrix e e = _
  rw [submatrix_mul_equiv, hg]
  exact submatrix_diagonal_equiv _ e
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
private theorem conf_diagonal (i : Option F) : conf F i i = 0 := by
  cases i <;> simp [conf]
private theorem conf_off {i j : Option F} (h : i ≠ j) : conf F i j = 1 ∨ conf F i j = -1 := by
  have sides {x : F} (hx : x ≠ 0) : (quadraticChar F x : ℝ) = 1 ∨ (quadraticChar F x : ℝ) = -1 := by
    rcases quadraticChar_dichotomy hx with hp | hm
    · left; simp [hp]
    · right; simp [hm]
  cases i <;> cases j
  · contradiction
  · exact Or.inl rfl
  · exact sides (neg_ne_zero.mpr one_ne_zero)
  · apply sides
    exact sub_ne_zero.mpr (fun eq => h (congrArg some eq))
private theorem confEntry (i j : Option F) :
    ((conf F + 1) i j = 1 ∨ (conf F + 1) i j = -1) ∧
    ((conf F - 1) i j = 1 ∨ (conf F - 1) i j = -1) := by
  by_cases h : i = j
  · subst j
    simp [conf_diagonal, Matrix.add_apply, Matrix.sub_apply]
  · simpa [Matrix.one_apply_ne h, Matrix.add_apply, Matrix.sub_apply] using
      (And.intro (conf_off (F := F) h) (conf_off (F := F) h))

theorem paley_one (hq : Fintype.card F % 4 = 3) : PaleyHas (Fintype.card F + 1) := by
  have hF : ringChar F ≠ 2 := fun e => by have := FiniteField.even_card_of_char_two e; omega
  have hsg : (quadraticChar F (-1) : ℝ) = -1 := by
    have := quadraticChar_neg_one_iff_not_isSquare.mpr (fun hs => (FiniteField.isSquare_neg_one_iff.mp hs) hq)
    exact_mod_cast this
  have ht : (conf F).transpose = -conf F := by rw [paley_transpose, hsg, neg_one_smul]
  apply movePaley (ι := Option F) (by simp) (conf F + 1) (fun i j => (confEntry i j).1)
  have hg : (conf F).transpose * conf F = (Fintype.card F : ℕ) := paley_gram hF
  simp only [transpose_add, transpose_one, add_mul, mul_add, one_mul, mul_one, Nat.cast_add, Nat.cast_one]
  rw [hg, ht]
  abel

theorem paley_two (hq : Fintype.card F % 4 = 1) : PaleyHas (2*(Fintype.card F + 1)) := by
  have hF : ringChar F ≠ 2 := fun e => by have := FiniteField.even_card_of_char_two e; omega
  have hsg : (quadraticChar F (-1) : ℝ) = 1 := by
    have := (quadraticChar_one_iff_isSquare (neg_ne_zero.mpr (one_ne_zero' F))).mpr
      (FiniteField.isSquare_neg_one_iff.mpr (by omega))
    exact_mod_cast this
  let C := conf F
  have ht : C.transpose = C := by
    change (conf F).transpose = conf F
    rw [paley_transpose, hsg, one_smul]
  have hg : C * C = (Fintype.card F : ℕ) := by
    have h : C.transpose * C = (Fintype.card F : ℕ) := paley_gram hF
    rwa [ht] at h
  let A := C + 1
  let B := C - 1
  apply movePaley (ι := Option F ⊕ Option F) (by simp; omega) (fromBlocks A B B (-A))
  · intro i j
    cases i <;> cases j
    · exact (confEntry _ _).1
    · exact (confEntry _ _).2
    · exact (confEntry _ _).2
    · rename_i i j
      rcases (confEntry i j).1 with h | h
      · right; change -(A i j) = -1; rw [show A i j = 1 from h]
      · left; change -(A i j) = 1; rw [show A i j = -1 from h, neg_neg]
  · have tA : A.transpose = A := by simp [A, ht]
    have tB : B.transpose = B := by simp [B, ht]
    have d : A*A + B*B = ((2*(Fintype.card F + 1) : ℕ) : Matrix (Option F) (Option F) ℝ) := by
      simp only [A,B,add_mul,mul_add,sub_mul,mul_sub,one_mul,mul_one,hg,Nat.cast_add,Nat.cast_ofNat,two_mul]
      noncomm_ring
      norm_num [two_zsmul, two_nsmul]
    have eq : A*B = B*A := by simp only [A,B,add_mul,mul_add,sub_mul,mul_sub,one_mul,mul_one]; abel
    rw [fromBlocks_transpose, transpose_neg, tA, tB, fromBlocks_multiply]
    simp only [Matrix.mul_neg, Matrix.neg_mul, neg_neg, ← eq, add_neg_cancel,
      d, show B*B+A*A = A*A+B*B by abel]
    exact (fromBlocks_diagonal _ _).trans (by congr 1; funext i; cases i <;> rfl)
end OMA.Had

open OMA.Had in
theorem OMA.solution : OMA.R_Hadamard_HadamardConjecture_R1.H1 := by
  classical
  rintro q ⟨p,e,hp,he,rfl⟩ hq
  have : Fact p.Prime := ⟨Nat.prime_iff.mpr hp⟩
  letI : Fintype (GaloisField p e) := Fintype.ofFinite _
  have hc : Fintype.card (GaloisField p e) = p^e := by
    rw [← Nat.card_eq_fintype_card, GaloisField.card p e he.ne']
  have z := paley_one (F := GaloisField p e) (by rwa [hc])
  rw [hc] at z
  obtain ⟨M, hm, hg⟩ := z
  refine ⟨M, fun i j => ?_, hg⟩
  simpa only [Finset.mem_insert, Finset.mem_singleton] using hm i j
