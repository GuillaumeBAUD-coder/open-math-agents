import OMAReductions.R_Hadamard_HadamardConjecture_R1
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic

/-!
# Paley's finite-field Hadamard constructions

R. E. A. C. Paley, *On orthogonal matrices*, Journal of Mathematics and Physics 12 (1933),
311–320, https://doi.org/10.1002/sapm1933121311.
The reduction in PR #3073 was contributed by @Dugongue.

The quadratic-character correlation is proved by reindexing the field with the
fractional linear map `x ↦ (x - a) / (x - b)`, sending `b` to `1`.
-/

namespace PaleyHadamardTypeII

open Matrix
open scoped BigOperators Matrix

noncomputable section

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- Off the diagonal, two translates of the quadratic character have correlation `-1`. -/
private theorem quadraticChar_correlation (hF : ringChar F ≠ 2) {a b : F} (hab : a ≠ b) :
    (∑ x : F, quadraticChar F (x - a) * quadraticChar F (x - b)) = -1 := by
  classical
  let f (x : F) := if x = b then 1 else (x - a) / (x - b)
  have fneq {x : F} (hx : x ≠ b) : f x ≠ 1 := by
    simp only [f, hx, if_false]
    intro h
    have h' := (div_eq_iff (sub_ne_zero.mpr hx)).mp h
    apply hab
    linear_combination -h'
  have hf : Function.Injective f := by
    intro x y h
    by_cases hx : x = b
    · by_contra hne
      have hy : y ≠ b := fun eq => hne (hx.trans eq.symm)
      exact fneq hy (h.symm.trans (by simp [f, hx]))
    by_cases hy : y = b
    · exact (fneq hx (h.trans (by simp [f, hy]))).elim
    have h' : (x - a) * (y - b) = (y - a) * (x - b) :=
      (div_eq_div_iff (sub_ne_zero.mpr hx) (sub_ne_zero.mpr hy)).mp (by simpa [f, hx, hy] using h)
    have hxy : (a - b) * (x - y) = 0 := by linear_combination h'
    exact sub_eq_zero.mp ((mul_eq_zero.mp hxy).resolve_left (sub_ne_zero.mpr hab))
  let e : F ≃ F := Equiv.ofBijective f (Finite.injective_iff_bijective.mp hf)
  have hx (x : F) : quadraticChar F (e x) =
      quadraticChar F (x - a) * quadraticChar F (x - b) + if x = b then 1 else 0 := by
    change quadraticChar F (f x) = _
    by_cases h : x = b
    · simp [f, h]
    simp only [f, h, if_false, add_zero]
    rw [← map_mul]
    have he : (x - a) * (x - b) = ((x - a) / (x - b)) * (x - b) ^ 2 := by
      field_simp [sub_ne_zero.mpr h]
    rw [he, map_mul, quadraticChar_sq_one' (sub_ne_zero.mpr h), mul_one]
  have hs := e.sum_comp (fun x => quadraticChar F x)
  simp only [hx, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true,
    quadraticChar_sum_zero hF] at hs
  linarith

private theorem sum_quadraticChar_sub (hF : ringChar F ≠ 2) (a : F) :
    (∑ x : F, quadraticChar F (x - a)) = 0 := by
  calc
    _ = ∑ x : F, quadraticChar F x := by
      simpa [sub_eq_add_neg] using
        (Equiv.sum_comp (Equiv.addRight (-a) : F ≃ F) (fun x => quadraticChar F x))
    _ = 0 := quadraticChar_sum_zero hF

private theorem sum_quadraticChar_sub_sq (a : F) :
    (∑ x : F, quadraticChar F (x - a) * quadraticChar F (x - a)) + 1 =
      (Fintype.card F : ℤ) := by
  classical
  have h (x : F) : quadraticChar F (x - a) * quadraticChar F (x - a) +
      (if x = a then 1 else 0 : ℤ) = 1 := by
    by_cases hx : x = a
    · simp [hx]
    · rw [if_neg hx, add_zero, ← pow_two, quadraticChar_sq_one (sub_ne_zero.mpr hx)]
  have hh : (∑ x : F, (quadraticChar F (x - a) * quadraticChar F (x - a) +
      (if x = a then (1 : ℤ) else 0))) = ∑ _ : F, (1 : ℤ) :=
    Finset.sum_congr rfl (fun x _ => h x)
  simpa [Finset.sum_add_distrib] using hh

/-- The Paley conference matrix with one extra row and column indexed by `none`. -/
private def conference (F : Type*) [Field F] [Fintype F] [DecidableEq F] : Matrix (Option F) (Option F) ℤ
  | none, none => 0
  | none, some _ => 1
  | some _, none => quadraticChar F (-1)
  | some a, some b => quadraticChar F (b - a)

private theorem conference_transpose :
    (conference F)ᵀ = quadraticChar F (-1) • conference F := by
  ext i j
  rcases i with _ | i <;> rcases j with _ | j
  · simp [conference, transpose_apply]
  · simp [conference, transpose_apply]
  · simpa [conference, transpose_apply, smul_eq_mul, pow_two] using
      (quadraticChar_sq_one (F := F) (a := -1) (neg_ne_zero.mpr one_ne_zero)).symm
  · simp only [conference, transpose_apply, Matrix.smul_apply, smul_eq_mul]
    rw [show i - j = (-1 : F) * (j - i) by ring, map_mul]

private theorem conference_mul_transpose (hF : ringChar F ≠ 2) :
    conference F * (conference F)ᵀ =
      (Fintype.card F : ℤ) • (1 : Matrix (Option F) (Option F) ℤ) := by
  classical
  have square : quadraticChar F (-1) * quadraticChar F (-1) = 1 := by
    rw [← pow_two, quadraticChar_sq_one (neg_ne_zero.mpr one_ne_zero)]
  ext i j
  rcases i with _ | i <;> rcases j with _ | j
  · simp [mul_apply, Fintype.sum_option, transpose_apply, conference, one_apply]
  · simp [mul_apply, Fintype.sum_option, transpose_apply, conference, one_apply]
    exact sum_quadraticChar_sub hF j
  · simp [mul_apply, Fintype.sum_option, transpose_apply, conference, one_apply]
    exact sum_quadraticChar_sub hF i
  · simp only [mul_apply, Fintype.sum_option, transpose_apply, conference, square,
      Matrix.smul_apply, smul_eq_mul, one_apply, Option.some.injEq]
    by_cases h : i = j
    · subst j
      rw [if_pos rfl, mul_one, add_comm]
      exact sum_quadraticChar_sub_sq i
    · rw [if_neg h, mul_zero, quadraticChar_correlation hF h]
      norm_num

omit [DecidableEq F] in
private theorem char_ne_two_of_mod_four {r : ℕ} (hr : r % 2 = 1)
    (hcard : Fintype.card F % 4 = r) : ringChar F ≠ 2 := by
  intro h
  have := FiniteField.even_card_of_char_two h
  omega

private theorem conference_offdiag {i j : Option F} (h : i ≠ j) :
    conference F i j = 1 ∨ conference F i j = -1 := by
  rcases i with _ | i <;> rcases j with _ | j
  · exact (h rfl).elim
  · exact Or.inl rfl
  · exact quadraticChar_dichotomy (a := (-1 : F)) (neg_ne_zero.mpr one_ne_zero)
  · exact quadraticChar_dichotomy (sub_ne_zero.mpr (fun e => h (congrArg some e.symm)))

private theorem conference_diag (i : Option F) : conference F i i = 0 := by
  cases i <;> simp [conference]

/-- Type II as an integer sign matrix on two copies of the bordered field. -/
private theorem typeII_int (hq : Fintype.card F % 4 = 1) :
    ∃ H : Matrix (Option F ⊕ Option F) (Option F ⊕ Option F) ℤ,
      (∀ i j, H i j = 1 ∨ H i j = -1) ∧
      Hᵀ * H = (2 * ((Fintype.card F : ℤ) + 1)) •
        (1 : Matrix (Option F ⊕ Option F) (Option F ⊕ Option F) ℤ) := by
  have hF : ringChar F ≠ 2 := char_ne_two_of_mod_four (by decide) hq
  have hχ : quadraticChar F (-1) = 1 :=
    (quadraticChar_one_iff_isSquare (a := (-1 : F)) (neg_ne_zero.mpr one_ne_zero)).2
      (by simp [FiniteField.isSquare_neg_one_iff, hq])
  let C := conference F
  let A := C + 1
  let B := C - 1
  let H := fromBlocks A B B (-A)
  have ht : Cᵀ = C := by
    change (conference F)ᵀ = _
    rw [conference_transpose, hχ, one_smul]
  have hC : C * C = (Fintype.card F : ℤ) • (1 : Matrix (Option F) (Option F) ℤ) := by
    have h := conference_mul_transpose hF
    change C * Cᵀ = _ at h
    rwa [ht] at h
  have hA (i j : Option F) : A i j = 1 ∨ A i j = -1 := by
    by_cases h : i = j
    · subst j
      left
      simp [A, C, conference_diag, one_apply]
    · simpa [A, C, one_apply, h] using (conference_offdiag (F := F) h)
  have hB (i j : Option F) : B i j = 1 ∨ B i j = -1 := by
    by_cases h : i = j
    · subst j
      right
      simp [B, C, conference_diag, one_apply]
    · simpa [B, C, one_apply, h] using (conference_offdiag (F := F) h)
  have hS : Hᵀ = H := by
    simp only [H, A, B, fromBlocks_transpose, transpose_add, transpose_sub, transpose_neg,
      transpose_one, ht]
  let d : ℤ := 2 * ((Fintype.card F : ℤ) + 1)
  have hD : A * A + B * B = d • (1 : Matrix (Option F) (Option F) ℤ) := by
    calc
      _ = (C * C + C * C) + (1 + 1) := by
        simp only [A, B, add_mul, mul_add, sub_mul, mul_sub, one_mul, mul_one]
        abel
      _ = _ := by
        rw [hC]
        have h : d = ((Fintype.card F : ℤ) + (Fintype.card F : ℤ)) + (1 + 1) := by dsimp [d]; ring
        rw [h]
        simp only [add_smul, one_smul]
  have hcomm : A * B = B * A := by
    simp only [A, B, add_mul, mul_add, sub_mul, mul_sub, one_mul, mul_one]
    abel
  refine ⟨H, ?_, ?_⟩
  · intro i j
    rcases i with i | i <;> rcases j with j | j
    · exact hA i j
    · exact hB i j
    · exact hB i j
    · rcases hA i j with h | h
      · right
        change -A i j = -1
        rw [h]
      · left
        change -A i j = 1
        rw [h]
        norm_num
  · have hoff₁ : A * B + B * (-A) = 0 := by rw [mul_neg, hcomm, add_neg_cancel]
    have hoff₂ : B * A + (-A) * B = 0 := by rw [neg_mul, ← hcomm, add_neg_cancel]
    have hD₂ : B * B + (-A) * (-A) = d • (1 : Matrix (Option F) (Option F) ℤ) := by
      simpa [add_comm (B * B)] using hD
    calc
      Hᵀ * H = fromBlocks (d • (1 : Matrix (Option F) (Option F) ℤ)) 0 0
          (d • (1 : Matrix (Option F) (Option F) ℤ)) := by
        rw [hS]
        change fromBlocks A B B (-A) * fromBlocks A B B (-A) = _
        rw [fromBlocks_multiply, hD, hoff₁, hoff₂, hD₂]
      _ = d • (1 : Matrix (Option F ⊕ Option F) (Option F ⊕ Option F) ℤ) := by
        have hone : fromBlocks (1 : Matrix (Option F) (Option F) ℤ) 0 0
            (1 : Matrix (Option F) (Option F) ℤ) =
            (1 : Matrix (Option F ⊕ Option F) (Option F ⊕ Option F) ℤ) := fromBlocks_one
        rw [← hone, fromBlocks_smul]
        simp only [smul_zero]

private theorem real_witness_of_integer_gram {W : Type*} [Fintype W] [DecidableEq W]
    {n : ℕ} (hn : Fintype.card W = n) (H : Matrix W W ℤ)
    (hentry : ∀ i j, H i j = 1 ∨ H i j = -1)
    (hgram : Hᵀ * H = (n : ℤ) • (1 : Matrix W W ℤ)) :
    ∃ M, Hadamard.IsHadamard' (n := n) M := by
  let e := (Fintype.equivFinOfCardEq hn).symm
  let M : Matrix (Fin n) (Fin n) ℝ := fun i j => (H (e i) (e j) : ℝ)
  refine ⟨M, ?_, ?_⟩
  · intro i j
    rcases hentry (e i) (e j) with h | h <;> simp [M, h]
  · ext i j
    calc
      _ = ∑ k : Fin n, ((H (e k) (e i) * H (e k) (e j) : ℤ) : ℝ) := by
        rw [Matrix.mul_apply]
        change (∑ k : Fin n, (H (e k) (e i) : ℝ) * (H (e k) (e j) : ℝ)) = _
        simp only [Int.cast_mul]
      _ = ((Hᵀ * H) (e i) (e j) : ℝ) := by
        simp only [mul_apply, transpose_apply]
        exact e.sum_comp (fun k : W => ((H k (e i) * H k (e j) : ℤ) : ℝ)) |>.trans
          (by push_cast; rfl)
      _ = _ := by
        rw [hgram]
        by_cases h : i = j
        · simp [h, Matrix.smul_apply, one_apply, Matrix.natCast_apply]
        · have h' : e i ≠ e j := fun eq => h (e.injective eq)
          simp [h, h', Matrix.smul_apply, one_apply, Matrix.natCast_apply]

/-- The Paley type II witness for every prime-power order parameter congruent to 1 mod 4. -/
private theorem typeII (q : ℕ) (hpow : IsPrimePow q) (hq : q % 4 = 1) :
    ∃ M, Hadamard.IsHadamard' (n := 2 * (q + 1)) M := by
  classical
  obtain ⟨p, k, hp, hk, rfl⟩ := (isPrimePow_nat_iff q).mp hpow
  let _ : Fact p.Prime := ⟨hp⟩
  let F := GaloisField p k
  let _ : Fintype F := Fintype.ofFinite F
  have hc : Fintype.card F = p ^ k := (Nat.card_eq_fintype_card).symm.trans
    (GaloisField.card p k hk.ne')
  obtain ⟨M, he, hg⟩ := typeII_int (F := F) (hc ▸ hq)
  have ho : Fintype.card (Option F ⊕ Option F) = 2 * (p ^ k + 1) := by
    simp [hc, two_mul]
  exact real_witness_of_integer_gram ho M he (by simpa [hc] using hg)

end

end PaleyHadamardTypeII

theorem OMA.solution : OMA.R_Hadamard_HadamardConjecture_R1.H2 :=
  PaleyHadamardTypeII.typeII
