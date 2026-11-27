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

namespace PaleyHadamardTypeI

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

/-- Type I as a sign matrix over the integers, with both Gram identities. -/
private theorem typeI_int (hq : Fintype.card F % 4 = 3) :
    ∃ H : Matrix (Option F) (Option F) ℤ,
      (∀ i j, H i j = 1 ∨ H i j = -1) ∧
      H * Hᵀ = ((Fintype.card F : ℤ) + 1) • (1 : Matrix (Option F) (Option F) ℤ) ∧
      Hᵀ * H = ((Fintype.card F : ℤ) + 1) • (1 : Matrix (Option F) (Option F) ℤ) := by
  have hF : ringChar F ≠ 2 := char_ne_two_of_mod_four (by decide) hq
  have hχ : quadraticChar F (-1) = -1 :=
    quadraticChar_neg_one_iff_not_isSquare.mpr (by simp [FiniteField.isSquare_neg_one_iff, hq])
  let C := conference F
  have ht : Cᵀ = -C := by
    change (conference F)ᵀ = _
    rw [conference_transpose, hχ, neg_one_smul]
  have hm : C * Cᵀ = (Fintype.card F : ℤ) • (1 : Matrix (Option F) (Option F) ℤ) :=
    conference_mul_transpose hF
  have hc : Cᵀ * C = C * Cᵀ := by rw [ht, neg_mul, mul_neg]
  refine ⟨C + 1, fun i j => ?_, ?_, ?_⟩
  · by_cases h : i = j
    · subst j
      left
      simp [C, conference_diag, one_apply]
    · simpa [C, one_apply, h] using (conference_offdiag (F := F) h)
  · simp only [transpose_add, transpose_one, add_mul, mul_add, one_mul, mul_one]
    rw [hm, ht, add_smul, one_smul]
    abel
  · simp only [transpose_add, transpose_one, add_mul, mul_add, one_mul, mul_one]
    rw [hc, hm, ht, add_smul, one_smul]
    abel


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

/-- The Paley type I witness for every prime-power order parameter congruent to 3 mod 4. -/
private theorem typeI (q : ℕ) (hpow : IsPrimePow q) (hq : q % 4 = 3) :
    ∃ M, Hadamard.IsHadamard' (n := q + 1) M := by
  classical
  obtain ⟨p, k, hp, hk, rfl⟩ := (isPrimePow_nat_iff q).mp hpow
  let _ : Fact p.Prime := ⟨hp⟩
  let F := GaloisField p k
  let _ : Fintype F := Fintype.ofFinite F
  have hc : Fintype.card F = p ^ k := (Nat.card_eq_fintype_card).symm.trans
    (GaloisField.card p k hk.ne')
  obtain ⟨M, he, _, hg⟩ := typeI_int (F := F) (hc ▸ hq)
  exact real_witness_of_integer_gram (by simp [hc]) M he (by simpa [hc] using hg)


end

end PaleyHadamardTypeI

theorem OMA.solution : OMA.R_Hadamard_HadamardConjecture_R1.H1 :=
  PaleyHadamardTypeI.typeI
