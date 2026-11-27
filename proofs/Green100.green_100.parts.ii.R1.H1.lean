import OMAReductions.R_Green100_green_100_parts_ii_R1

/-!
# Finite word models for Green 100(ii)

Given a board hyperlinear model, evaluate signed words using genuine matrix inverses.
A finite set of relators can be made arbitrarily accurate while a fixed nonidentity
word remains more than 1/8 away from the identity. The estimates also cover empty
words and dimension zero under the board's totalized division.
-/

namespace Green100.FiniteModels

open scoped Matrix.Norms.Frobenius
abbrev UnitaryAt (n : ℕ) := Matrix.unitaryGroup (Fin n) ℂ

theorem hsDist_eq_frobenius {n : ℕ} (u v : UnitaryAt n) :
    hsDist u v = ‖u.val - v.val‖ / Real.sqrt n := by
  rw [hsDist, Real.sqrt_div (by positivity), Matrix.frobenius_norm_def, Real.sqrt_eq_rpow]
  simp [Matrix.sub_apply]

theorem hsDist_symm {n : ℕ} (u v : UnitaryAt n) : hsDist u v = hsDist v u := by
  simp only [hsDist_eq_frobenius, norm_sub_rev u.val v.val]

theorem hsDist_triangle {n : ℕ} (u v w : UnitaryAt n) :
    hsDist u w ≤ hsDist u v + hsDist v w := by
  simp only [hsDist_eq_frobenius, ← add_div]
  apply div_le_div_of_nonneg_right _ (Real.sqrt_nonneg _)
  simpa only [dist_eq_norm] using dist_triangle u.val v.val w.val

private theorem sumSq_trace {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) :
    ∑ i, ∑ j, ‖M i j‖ ^ 2 = (Matrix.trace (star M * M)).re := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Complex.re_sum,
    Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply, Complex.star_def,
    ← Complex.normSq_eq_conj_mul_self, Complex.ofReal_re, Complex.normSq_eq_norm_sq]
  rw [Finset.sum_comm]

theorem hsDist_mul_left {n : ℕ} (a u v : UnitaryAt n) :
    hsDist (a * u) (a * v) = hsDist u v := by
  unfold hsDist
  congr 2
  change (∑ i, ∑ j, ‖((a.val * u.val - a.val * v.val) i j)‖ ^ 2) =
    ∑ i, ∑ j, ‖((u.val - v.val) i j)‖ ^ 2
  rw [← mul_sub, sumSq_trace, sumSq_trace, star_mul, mul_assoc,
    ← mul_assoc (star a.val), a.property.1, one_mul]

/-- Evaluate a signed word; the sign `true` denotes a generator and `false` its inverse. -/
abbrev evalWord {A H : Type*} [Group H] (v : A → H) (t : List (A × Bool)) : H :=
  FreeGroup.lift v (FreeGroup.mk t)

private theorem evalWord_nil {A H : Type*} [Group H] (v : A → H) :
    evalWord v [] = 1 := rfl

private theorem evalWord_cons {A H : Type*} [Group H] (v : A → H) (a : A) (b : Bool)
    (t : List (A × Bool)) :
    evalWord v ((a, b) :: t) = (if b then v a else (v a)⁻¹) * evalWord v t := by
  cases b <;> rfl

/-- A finite multiplication table containing the positive generators and all suffix values. -/
private def wordTable {A G : Type*} [Group G] [DecidableEq G] (s : A → G) :
    List (A × Bool) → Finset G
  | [] => {1}
  | (a, b) :: t => insert (s a) (insert (evalWord s ((a, b) :: t)) (wordTable s t))

private theorem eval_mem_wordTable {A G : Type*} [Group G] [DecidableEq G]
    (s : A → G) (t : List (A × Bool)) : evalWord s t ∈ wordTable s t := by
  cases t with
  | nil => simp [wordTable]
  | cons l t => cases l; simp [wordTable]

/-- Each signed letter costs one multiplication error. The additional term accounts
for the board's approximate normalization at the empty word. -/
private theorem eval_error {A G : Type*} [Group G] [DecidableEq G] {n : ℕ}
    (s : A → G) (θ : G → UnitaryAt n) (F : Finset G) (ε : ℝ)
    (hm : ∀ g ∈ F, ∀ h ∈ F, g * h ∈ F → hsDist (θ g * θ h) (θ (g * h)) < ε)
    (hi : 1 ∈ F → hsDist (θ 1) 1 < ε)
    (t : List (A × Bool)) (ht : wordTable s t ⊆ F) :
    hsDist (evalWord (θ ∘ s) t) (θ (evalWord s t)) < (t.length + 1 : ℝ) * ε := by
  induction t with
  | nil =>
    simpa [evalWord_nil, hsDist_symm (1 : UnitaryAt n)] using hi (ht (by simp [wordTable]))
  | cons l t ih =>
    obtain ⟨a, b⟩ := l
    have hsub : wordTable s t ⊆ F := fun _ hx => ht (by simp [wordTable, hx])
    have ha : s a ∈ F := ht (by simp [wordTable])
    have htail := hsub (eval_mem_wordTable s t)
    have hword := ht (eval_mem_wordTable s ((a, b) :: t))
    have hprev := ih hsub
    cases b with
    | true =>
      simp only [evalWord_cons, if_true, Function.comp_apply] at hword ⊢
      have hstep := hm (s a) ha (evalWord s t) htail hword
      have htri := hsDist_triangle (θ (s a) * evalWord (θ ∘ s) t)
        (θ (s a) * θ (evalWord s t)) (θ (s a * evalWord s t))
      rw [hsDist_mul_left] at htri
      simp only [List.length_cons, Nat.cast_add, Nat.cast_one]
      linarith
    | false =>
      simp only [evalWord_cons, Bool.false_eq_true, if_false, Function.comp_apply] at hword ⊢
      have hstep := hm (s a) ha ((s a)⁻¹ * evalWord s t) hword (by simpa using htail)
      simp only [mul_inv_cancel_left] at hstep
      have htri := hsDist_triangle (evalWord (θ ∘ s) t) (θ (evalWord s t))
        (θ (s a) * θ ((s a)⁻¹ * evalWord s t))
      rw [hsDist_symm (θ (evalWord s t))] at htri
      rw [← hsDist_mul_left (θ (s a)), mul_inv_cancel_left]
      simp only [List.length_cons, Nat.cast_add, Nat.cast_one]
      linarith

/-- A hyperlinear group admits finite-dimensional models of any finite list of true
relators, while any selected nonidentity word stays uniformly separated. -/
theorem finite_relator_models {A G : Type*} [Group G] (hG : IsHyperlinear G) (s : A → G)
    (R : Finset (List (A × Bool))) (w : List (A × Bool))
    (hR : ∀ r ∈ R, evalWord s r = 1) (hw : evalWord s w ≠ 1) {δ : ℝ} (hδ : 0 < δ) :
    ∃ (n : ℕ) (u : A → UnitaryAt n), (∀ r ∈ R, hsDist (evalWord u r) 1 < δ) ∧
      (1 / 8 : ℝ) < hsDist (evalWord u w) 1 := by
  classical
  let W := insert w R
  let F := insert (1 : G) (W.biUnion (wordTable s))
  let K : ℝ := (W.sup List.length : ℕ) + 2
  let η := min δ (1 / 8)
  have hK : 0 < K := by dsimp [K]; positivity
  have hη : 0 < η := lt_min hδ (by norm_num)
  let ε := η / K
  have hε : 0 < ε := div_pos hη hK
  have hKε : K * ε = η := by dsimp [ε]; field_simp
  obtain ⟨n, θ, hm, hi, hs⟩ := hG F ε hε
  have h1 : (1 : G) ∈ F := Finset.mem_insert_self ..
  have hF (t) (ht : t ∈ W) : wordTable s t ⊆ F := fun x hx =>
    Finset.mem_insert_of_mem (Finset.mem_biUnion.mpr ⟨t, ht, hx⟩)
  have hbound (t) (ht : t ∈ W) :
      hsDist (evalWord (θ ∘ s) t) (θ (evalWord s t)) + hsDist (θ 1) 1 < η := by
    have herr := eval_error s θ F ε hm hi t (hF t ht)
    have hlen : (t.length : ℝ) ≤ (W.sup List.length : ℕ) := by
      exact_mod_cast (Finset.le_sup (f := List.length) ht)
    calc
      _ < (t.length + 1 : ℝ) * ε + ε := add_lt_add herr (hi h1)
      _ = (t.length + 2 : ℝ) * ε := by ring
      _ ≤ K * ε := mul_le_mul_of_nonneg_right (by dsimp [K]; linarith) hε.le
      _ = η := hKε
  refine ⟨n, θ ∘ s, ?_, ?_⟩
  · intro r hr
    have hb := hbound r (Finset.mem_insert_of_mem hr)
    rw [hR r hr] at hb
    exact ((hsDist_triangle _ (θ 1) _).trans_lt hb).trans_le (min_le_left ..)
  · have hwW : w ∈ W := Finset.mem_insert_self ..
    have hb := hbound w hwW
    have hsep := hs _ (hF w hwW (eval_mem_wordTable s w)) 1 h1 hw
    have ht₁ := hsDist_triangle (θ (evalWord s w)) (evalWord (θ ∘ s) w) (θ 1)
    have ht₂ := hsDist_triangle (evalWord (θ ∘ s) w) 1 (θ 1)
    rw [hsDist_symm (θ (evalWord s w)) (evalWord (θ ∘ s) w)] at ht₁
    rw [hsDist_symm 1] at ht₂
    have hη8 : η ≤ 1 / 8 := min_le_right ..
    linarith

end Green100.FiniteModels

theorem OMA.solution : OMA.R_Green100_green_100_parts_ii_R1.H1 := by
  intro k R w G inst s hyperlinear relators nonidentity δ positive
  exact Green100.FiniteModels.finite_relator_models hyperlinear s R w
    relators nonidentity positive
