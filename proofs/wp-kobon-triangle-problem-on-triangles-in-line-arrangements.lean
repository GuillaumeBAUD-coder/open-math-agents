import OMAStatements.S_wp_kobon_triangle_problem_on_triangles_in_line_arrangements
import Mathlib

/-!
# Kobon triangle problem: the maximum exists

For each `k` the set of achievable triangular-face counts is nonempty and bounded
above by `2 ^ k` (every face is a connected component of the complement, and points of
the complement with the same sign vector lie in the same component), so it has a
greatest element.
-/

namespace OMA.KobonAux

open OMA.S_wp_kobon_triangle_problem_on_triangles_in_line_arrangements
open scoped Classical

/-- Every line is the zero set of an affine functional. -/
lemma exists_fun (L : Line) (hL : Module.finrank ℝ L.direction = 1) :
    ∃ f : Plane → ℝ, (∀ x, x ∈ L ↔ f x = 0) ∧
      ∀ (a b : ℝ) (x y : Plane), a + b = 1 → f (a • x + b • y) = a * f x + b * f y := by
  have hne : (L : Set Plane).Nonempty := by
    rcases AffineSubspace.eq_bot_or_nonempty L with h | h
    · subst h
      rw [AffineSubspace.direction_bot] at hL
      simp at hL
    · exact h
  obtain ⟨p, hp⟩ := hne
  have hK : Module.finrank ℝ (L.direction)ᗮ = 1 := by
    have h1 := Submodule.finrank_add_finrank_orthogonal L.direction
    have h2 : Module.finrank ℝ Plane = 2 := by simp
    omega
  obtain ⟨n, -, hn⟩ := finrank_eq_one_iff'.mp hK
  have hmem : ∀ w : Plane, w ∈ L.direction ↔ inner ℝ (n : Plane) w = 0 := by
    intro w
    constructor
    · intro hw
      exact (Submodule.mem_orthogonal' L.direction (n : Plane)).1 n.2 w hw
    · intro hw
      rw [← Submodule.orthogonal_orthogonal L.direction, Submodule.mem_orthogonal]
      intro u hu
      obtain ⟨c, hc⟩ := hn ⟨u, hu⟩
      have hu' : u = c • (n : Plane) := by
        have := congrArg Subtype.val hc
        simpa using this.symm
      rw [hu', inner_smul_left, hw, mul_zero]
  refine ⟨fun x => inner ℝ (n : Plane) (x - p), ?_, ?_⟩
  · intro x
    rw [← hmem, ← vsub_eq_sub]
    exact (AffineSubspace.vsub_right_mem_direction_iff_mem hp x).symm
  · intro a b x y hab
    have e : a • x + b • y - p = a • (x - p) + b • (y - p) := by
      calc a • x + b • y - p = a • x + b • y - (a + b) • p := by rw [hab, one_smul]
        _ = a • (x - p) + b • (y - p) := by rw [add_smul, smul_sub, smul_sub]; abel
    simp only [e, inner_add_right, inner_smul_right]

lemma faces_le (lines : Finset Line)
    (h : ∀ L ∈ lines, Module.finrank ℝ L.direction = 1) :
    {face | IsTriangularFace lines face}.encard ≤ 2 ^ lines.card := by
  have H : ∀ L : Line, ∃ f : Plane → ℝ, Module.finrank ℝ L.direction = 1 →
      ((∀ x, x ∈ L ↔ f x = 0) ∧
      ∀ (a b : ℝ) (x y : Plane), a + b = 1 → f (a • x + b • y) = a * f x + b * f y) := by
    intro L
    by_cases hL : Module.finrank ℝ L.direction = 1
    · obtain ⟨f, hf⟩ := exists_fun L hL
      exact ⟨f, fun _ => hf⟩
    · exact ⟨fun _ => 0, fun h' => absurd h' hL⟩
  choose f hf using H
  set C : Set Plane := (⋃ L ∈ lines, (L : Set Plane))ᶜ with hC
  let σ : Plane → Finset Line := fun x => lines.filter (fun L => 0 < f L x)
  have key : ∀ x ∈ C, ∀ y ∈ C, σ x = σ y →
      connectedComponentIn C x = connectedComponentIn C y := by
    intro x hx y hy hxy
    have hseg : segment ℝ x y ⊆ C := by
      intro z hz
      obtain ⟨a, b, ha, hb, hab, rfl⟩ := hz
      simp only [hC, Set.mem_compl_iff, Set.mem_iUnion, SetLike.mem_coe, not_exists] at hx hy ⊢
      intro L hL hzL
      obtain ⟨h1, h2⟩ := hf L (h L hL)
      have hz0 := (h1 _).1 hzL
      rw [h2 a b x y hab] at hz0
      have hx0 : f L x ≠ 0 := fun e => hx L hL ((h1 x).2 e)
      have hy0 : f L y ≠ 0 := fun e => hy L hL ((h1 y).2 e)
      have hiff : 0 < f L x ↔ 0 < f L y := by
        have h3 : L ∈ σ x ↔ L ∈ σ y := by rw [hxy]
        simpa [σ, hL] using h3
      have hab0 : a * f L x = 0 ∧ b * f L y = 0 := by
        rcases lt_or_gt_of_ne hx0 with hxn | hxp
        · have hyn : f L y < 0 :=
            lt_of_le_of_ne (not_lt.1 (fun h' => absurd (hiff.2 h') (not_lt.2 hxn.le))) hy0
          have e1 : a * f L x ≤ 0 := mul_nonpos_of_nonneg_of_nonpos ha hxn.le
          have e2 : b * f L y ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hb hyn.le
          constructor <;> linarith
        · have hyp : 0 < f L y := hiff.1 hxp
          have e1 : 0 ≤ a * f L x := mul_nonneg ha hxp.le
          have e2 : 0 ≤ b * f L y := mul_nonneg hb hyp.le
          constructor <;> linarith
      have ha0 : a = 0 := (mul_eq_zero.1 hab0.1).resolve_right hx0
      have hb0 : b = 0 := (mul_eq_zero.1 hab0.2).resolve_right hy0
      linarith
    have hy' : y ∈ connectedComponentIn C x :=
      (convex_segment x y).isPreconnected.subset_connectedComponentIn
        (left_mem_segment ℝ x y) hseg (right_mem_segment ℝ x y)
    exact connectedComponentIn_eq hy'
  let pick : Finset Line → Plane := fun T =>
    if h' : ∃ x ∈ C, σ x = T then h'.choose else 0
  have sub : {face | IsTriangularFace lines face} ⊆
      (fun T => connectedComponentIn C (pick T)) '' (↑lines.powerset : Set (Finset Line)) := by
    intro face hface
    obtain ⟨x, hx, v, -, hface, -⟩ := hface
    refine ⟨σ x, ?_, ?_⟩
    · exact Finset.mem_coe.2 (Finset.mem_powerset.2 (Finset.filter_subset _ _))
    · have h' : ∃ y ∈ C, σ y = σ x := ⟨x, hx, rfl⟩
      have hs := h'.choose_spec
      simp only [pick, dif_pos h']
      rw [hface]
      exact key _ hs.1 _ hx hs.2
  calc {face | IsTriangularFace lines face}.encard
      ≤ ((fun T => connectedComponentIn C (pick T)) ''
          (↑lines.powerset : Set (Finset Line))).encard := Set.encard_le_encard sub
    _ ≤ (↑lines.powerset : Set (Finset Line)).encard := Set.encard_image_le _ _
    _ = 2 ^ lines.card := by
        rw [Set.encard_coe_eq_coe_finsetCard, Finset.card_powerset]
        push_cast
        rfl

lemma exists_lines (k : ℕ) : ∃ lines : Finset Line, lines.card = k ∧
    ∀ L ∈ lines, Module.finrank ℝ L.direction = 1 := by
  let e : Plane := EuclideanSpace.single 1 1
  have he : e ≠ 0 := by
    intro h0
    have := congrFun (congrArg (fun v : Plane => (v : Fin 2 → ℝ)) h0) 1
    simp [e] at this
  let g : Fin k → Line := fun i =>
    AffineSubspace.mk' (EuclideanSpace.single 0 ((i : ℕ) : ℝ)) (Submodule.span ℝ {e})
  have hg : Function.Injective g := by
    intro i j hij
    have h1 : (EuclideanSpace.single 0 ((i : ℕ) : ℝ) : Plane) ∈ g j := by
      rw [← hij]
      exact AffineSubspace.self_mem_mk' _ _
    rw [AffineSubspace.mem_mk', Submodule.mem_span_singleton] at h1
    obtain ⟨c, hc⟩ := h1
    have := congrFun (congrArg (fun v : Plane => (v : Fin 2 → ℝ)) hc) 0
    simp [e] at this
    have h2 : ((i : ℕ) : ℝ) = ((j : ℕ) : ℝ) := by linarith
    exact Fin.ext (by exact_mod_cast h2)
  refine ⟨Finset.univ.image g, ?_, ?_⟩
  · rw [Finset.card_image_of_injective _ hg]
    simp
  · intro L hL
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hL
    have hd : (g i).direction = Submodule.span ℝ {e} := AffineSubspace.direction_mk' _ _
    rw [hd]
    exact finrank_span_singleton he

end OMA.KobonAux

open OMA.S_wp_kobon_triangle_problem_on_triangles_in_line_arrangements in
theorem OMA.solution :
    type_of% @OMA.S_wp_kobon_triangle_problem_on_triangles_in_line_arrangements.main := by
  refine ⟨fun k => sSup {m | IsAchievableCount k m}, fun k => ?_⟩
  have hbdd : ∀ m ∈ {m | IsAchievableCount k m}, m ≤ 2 ^ k := by
    rintro m ⟨lines, hcard, hdir, hm⟩
    have h1 := OMA.KobonAux.faces_le lines hdir
    rw [hm, hcard] at h1
    exact_mod_cast h1
  have hB : BddAbove {m | IsAchievableCount k m} := ⟨2 ^ k, hbdd⟩
  have hne : {m | IsAchievableCount k m}.Nonempty := by
    obtain ⟨lines, hcard, hdir⟩ := OMA.KobonAux.exists_lines k
    have h1 := OMA.KobonAux.faces_le lines hdir
    have hfin : {face | IsTriangularFace lines face}.encard ≠ ⊤ :=
      ne_top_of_le_ne_top (by simp) h1
    exact ⟨_, lines, hcard, hdir, (ENat.natCast_toNat hfin).symm⟩
  exact ⟨Nat.sSup_mem hne hB, fun m hm => le_csSup hB hm⟩
