import OMAStatements.S_arxiv_1803_00671

/-! Counterexample: `x * y = F (lam y) x`. It moves only points of `[0, 1/2)`, and only when
`y > 1/2`. On `[0, 1/2]` the maps `F l` (`l > 0`) form a commuting one-parameter group of
Moebius maps fixing `0` and `1/2`, and `lam` is invariant under every `F l`; this gives
self-distributivity. For `x = 1/4`, `y = 1` one gets `x * y = 3/10`. -/

namespace OMA.P_arxiv_1803_00671

/-- Moebius map fixing `0` and `1/2`. -/
noncomputable def m (l t : ℝ) : ℝ := l * t / (1 + 2 * (l - 1) * t)

lemma den_pos {l t : ℝ} (hl : 0 < l) (h0 : 0 ≤ t) (h1 : t ≤ 1 / 2) :
    0 < 1 + 2 * (l - 1) * t := by
  nlinarith [mul_nonneg hl.le h0]

lemma m_nonneg {l t : ℝ} (hl : 0 < l) (h0 : 0 ≤ t) (h1 : t ≤ 1 / 2) : 0 ≤ m l t := by
  unfold m
  exact div_nonneg (mul_nonneg hl.le h0) (den_pos hl h0 h1).le

lemma m_le {l t : ℝ} (hl : 0 < l) (h0 : 0 ≤ t) (h1 : t ≤ 1 / 2) : m l t ≤ 1 / 2 := by
  unfold m
  rw [div_le_iff₀ (den_pos hl h0 h1)]
  nlinarith

lemma m_half {l : ℝ} (hl : 0 < l) : m l (1 / 2) = 1 / 2 := by
  unfold m
  have : (1 + 2 * (l - 1) * (1 / 2)) = l := by ring
  rw [this]; field_simp

lemma m_one (t : ℝ) : m 1 t = t := by
  unfold m; simp

lemma m_comp {a b t : ℝ} (ha : 0 < a) (hb : 0 < b) (h0 : 0 ≤ t) (h1 : t ≤ 1 / 2) :
    m a (m b t) = m (a * b) t := by
  have d1 := den_pos hb h0 h1
  have d3 := den_pos (mul_pos ha hb) h0 h1
  unfold m
  have e : 1 + 2 * (a - 1) * (b * t / (1 + 2 * (b - 1) * t))
      = (1 + 2 * (a * b - 1) * t) / (1 + 2 * (b - 1) * t) := by
    have h3 : 1 + 2 * (a * b - 1) * t = (1 + 2 * (b - 1) * t) + 2 * (a - 1) * (b * t) := by ring
    rw [h3, add_div, div_self d1.ne']; ring
  rw [e, mul_div_assoc', div_div_div_cancel_right₀ d1.ne']
  ring

/-- The operation on reals: `F l x = m l x` for `x ≤ 1/2`, and `x` for `x ≥ 1/2`. -/
noncomputable def F (l x : ℝ) : ℝ := m l (min x (1 / 2)) + (x - min x (1 / 2))

lemma F_of_le {l x : ℝ} (hx : x ≤ 1 / 2) : F l x = m l x := by
  unfold F; rw [min_eq_left hx]; ring

lemma F_of_ge {l x : ℝ} (hl : 0 < l) (hx : 1 / 2 ≤ x) : F l x = x := by
  unfold F; rw [min_eq_right hx, m_half hl]; ring

noncomputable def lam (y : ℝ) : ℝ := max 1 (y + 1 / 2)

lemma lam_pos (y : ℝ) : 0 < lam y := lt_of_lt_of_le one_pos (le_max_left _ _)

lemma F_mem {l x : ℝ} (hl : 0 < l) (hx : x ∈ Set.Icc (0 : ℝ) 1) : F l x ∈ Set.Icc (0 : ℝ) 1 := by
  rcases le_total x (1 / 2) with h | h
  · rw [F_of_le h]
    exact ⟨m_nonneg hl hx.1 h, by linarith [m_le hl hx.1 h]⟩
  · rw [F_of_ge hl h]; exact hx

lemma F_le_half {l x : ℝ} (hl : 0 < l) (h0 : 0 ≤ x) (h : x ≤ 1 / 2) : F l x ≤ 1 / 2 := by
  rw [F_of_le h]; exact m_le hl h0 h

lemma lam_F {l y : ℝ} (hl : 0 < l) (h0 : 0 ≤ y) : lam (F l y) = lam y := by
  rcases le_total y (1 / 2) with h | h
  · have h2 := F_le_half hl h0 h
    unfold lam
    rw [max_eq_left (by linarith), max_eq_left (by linarith)]
  · rw [F_of_ge hl h]

lemma F_comp {a b x : ℝ} (ha : 0 < a) (hb : 0 < b) (h0 : 0 ≤ x) :
    F a (F b x) = F (a * b) x := by
  rcases le_total x (1 / 2) with h | h
  · rw [F_of_le h, F_of_le (m_le hb h0 h), F_of_le h, m_comp ha hb h0 h]
  · rw [F_of_ge hb h, F_of_ge ha h, F_of_ge (mul_pos ha hb) h]

lemma F_one (x : ℝ) : F 1 x = x := by
  unfold F; rw [m_one]; ring

lemma F_self (x : ℝ) : F (lam x) x = x := by
  rcases le_total x (1 / 2) with h | h
  · have : lam x = 1 := by unfold lam; rw [max_eq_left (by linarith)]
    rw [this, F_one]
  · exact F_of_ge (lam_pos x) h

abbrev I01 := Set.Icc (0 : ℝ) 1

noncomputable def op (x y : I01) : I01 := ⟨F (lam y.1) x.1, F_mem (lam_pos _) x.2⟩

noncomputable def opInv (x y : I01) : I01 :=
  ⟨F (1 / lam y.1) x.1, F_mem (by have := lam_pos y.1; positivity) x.2⟩

lemma lam_ge (y : ℝ) : 1 ≤ lam y := le_max_left _ _

lemma contF : Continuous (fun p : I01 × I01 => F (lam p.2.1) p.1.1) := by
  unfold F m
  apply Continuous.add
  · apply Continuous.div
    · unfold lam; fun_prop
    · unfold lam; fun_prop
    · intro p
      have h1 := lam_ge p.2.1
      have h2 : 0 ≤ min p.1.1 (1 / 2) := le_min p.1.2.1 (by norm_num)
      nlinarith
  · fun_prop

lemma cont_op : Continuous (fun p : I01 × I01 => op p.1 p.2) :=
  contF.subtype_mk _

end OMA.P_arxiv_1803_00671

open OMA.P_arxiv_1803_00671 in
theorem OMA.disproof : ¬ (type_of% @OMA.S_arxiv_1803_00671.main) := by
  intro h
  have hq : OMA.S_arxiv_1803_00671.IsTopologicalQuandle op := by
    refine ⟨cont_op, ?_, ?_, ?_⟩
    · intro x
      apply Subtype.ext
      exact F_self x.1
    · intro y
      rw [isHomeomorph_iff_continuous_bijective]
      refine ⟨cont_op.comp (Continuous.prodMk_left y), ?_⟩
      rw [Function.bijective_iff_has_inverse]
      have hl := lam_pos y.1
      refine ⟨fun x => opInv x y, ?_, ?_⟩
      · intro x
        apply Subtype.ext
        change F (1 / lam y.1) (F (lam y.1) x.1) = x.1
        rw [F_comp (by positivity) hl x.2.1, one_div_mul_cancel hl.ne', F_one]
      · intro x
        apply Subtype.ext
        change F (lam y.1) (F (1 / lam y.1) x.1) = x.1
        rw [F_comp hl (by positivity) x.2.1, mul_one_div_cancel hl.ne', F_one]
    · intro x y z
      apply Subtype.ext
      change F (lam z.1) (F (lam y.1) x.1) = F (lam (F (lam z.1) y.1)) (F (lam z.1) x.1)
      rw [lam_F (lam_pos _) y.2.1, F_comp (lam_pos _) (lam_pos _) x.2.1,
        F_comp (lam_pos _) (lam_pos _) x.2.1, mul_comm]
  have e := h op hq ⟨1 / 4, by norm_num, by norm_num⟩ ⟨1, by norm_num, by norm_num⟩
  have e2 := congrArg Subtype.val e
  change F (lam 1) (1 / 4) = 1 / 4 at e2
  rw [F_of_le (by norm_num)] at e2
  unfold m lam at e2
  norm_num at e2

