import FormalConjectures.ErdosProblems.«507»

/-! The probabilistic construction of Komlós, Pintz and Szemerédi, followed by the
independence bound for linear hypergraphs of Duke, Lefmann and Rödl. The geometric
lemmas use the coordinate method in the project's Erdős lower-bound proof. The deletion of
vertices in conflicting triangles and the passage to the minimum triangle area are proved below. -/

namespace OMA.R_Erdos507_erdos_507_variants_lower_kps82_R1

open Finset Asymptotics Filter Erdos507
open scoped EuclideanGeometry

open scoped Classical in
/-- A sample with few small triangles and few pairs of triangles sharing an edge.
The parameter d is an upper bound on average degree after removing at most half
the points, and its dependence on the area cutoff is recorded explicitly. -/
def H1 : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop,
    ∃ (S : Finset ℝ²) (E : Finset (Finset ℝ²)) (d : ℝ),
      (S : Set ℝ²) ⊆ Metric.closedBall 0 1 ∧
      (∀ e ∈ E, e ⊆ S ∧ e.card = 3) ∧
      (∀ p : Fin 3 → ℝ², Function.Injective p → (∀ i, p i ∈ S) →
        |EuclideanGeometry.triangle_area (p 0) (p 1) (p 2)| ≤ ε * lowerBest n →
        univ.image p ∈ E) ∧
      2 * (((E ×ˢ E).filter fun q => q.1 ≠ q.2 ∧ 2 ≤ (q.1 ∩ q.2).card).card) ≤ S.card ∧
      2 ≤ d ∧ 6 * (E.card : ℝ) ≤ d * S.card ∧
      d / Real.log d ≤ C * ε * ((S.card : ℝ) / n) ^ 2

open scoped Classical in
/-- The independence number bound of Duke, Lefmann and Rödl for a linear
three-uniform hypergraph of average degree at most d. -/
def H2 : Prop :=
  ∃ a : ℝ, 0 < a ∧ ∀ {V : Type} [DecidableEq V] (S : Finset V) (E : Finset (Finset V)) (d : ℝ),
    2 ≤ d → (∀ e ∈ E, e ⊆ S ∧ e.card = 3) →
    (∀ e ∈ E, ∀ f ∈ E, e ≠ f → (e ∩ f).card ≤ 1) →
    3 * (E.card : ℝ) ≤ d * S.card →
    ∃ I ⊆ S, (∀ e ∈ E, ¬ e ⊆ I) ∧
      a * S.card * Real.sqrt (Real.log d / d) ≤ (I.card : ℝ)

open scoped Classical in
private theorem delete_conflicts {V : Type} [DecidableEq V] (S : Finset V) (E : Finset (Finset V))
    (hE : ∀ e ∈ E, e ⊆ S ∧ e.card = 3)
    (hX : 2 * (((E ×ˢ E).filter fun q => q.1 ≠ q.2 ∧ 2 ≤ (q.1 ∩ q.2).card).card) ≤ S.card) :
    ∃ W ⊆ S, S.card ≤ 2 * W.card ∧
      ∀ e ∈ E, e ⊆ W → ∀ f ∈ E, f ⊆ W → e ≠ f → (e ∩ f).card ≤ 1 := by
  let X := (E ×ˢ E).filter fun q => q.1 ≠ q.2 ∧ 2 ≤ (q.1 ∩ q.2).card
  have choose_one (q : X) : ∃ x, x ∈ q.1.1 ∧ x ∈ q.1.2 := by
    have hq := (mem_filter.mp q.2).2.2
    exact (Finset.card_pos.mp (by omega : 0 < (q.1.1 ∩ q.1.2).card)).imp
      (fun _ hx => mem_inter.mp hx)
  choose remove hremove using choose_one
  let R : Finset V := univ.image remove
  have hR : R ⊆ S := by
    intro x hx
    obtain ⟨q, _, rfl⟩ := mem_image.mp hx
    have hq : q.1 ∈ E ×ˢ E := (mem_filter.mp q.2).1
    exact (hE q.1.1 (mem_product.mp hq).1).1 (hremove q).1
  have hRcard : R.card ≤ X.card := by
    simpa [R] using card_image_le (f := remove) (s := (univ : Finset X))
  refine ⟨S \ R, sdiff_subset, ?_, ?_⟩
  · have hcard := card_sdiff_of_subset hR
    change 2 * X.card ≤ S.card at hX
    omega
  · intro e he hWe f hf hWf hne
    by_contra! hbad
    let q : X := ⟨(e,f), mem_filter.mpr ⟨mem_product.mpr ⟨he,hf⟩, hne, by
      change 2 ≤ (e ∩ f).card
      omega⟩⟩
    have hr : remove q ∈ R := mem_image.mpr ⟨q, mem_univ _, rfl⟩
    have hw : remove q ∈ S \ R := hWe (hremove q).1
    exact (mem_sdiff.mp hw).2 hr

private theorem signed_area_formula (a b c : ℝ²) :
    EuclideanGeometry.triangle_area a b c =
      ((a 0 - c 0) * (b 1 - c 1) - (b 0 - c 0) * (a 1 - c 1)) / 2 := by
  rw [EuclideanGeometry.triangle_area_eq_det, Matrix.det_fin_three]
  simp
  ring

private theorem collinear_area {T : Set ℝ²} (hT : Collinear ℝ T)
    {a b c : ℝ²} (ha : a ∈ T) (hb : b ∈ T) (hc : c ∈ T) :
    EuclideanGeometry.triangle_area a b c = 0 := by
  obtain ⟨base, v, onLine⟩ := (collinear_iff_exists_forall_eq_smul_vadd T).mp hT
  obtain ⟨x, rfl⟩ := onLine a ha
  obtain ⟨y, rfl⟩ := onLine b hb
  obtain ⟨z, rfl⟩ := onLine c hc
  rw [signed_area_formula]
  simp only [vadd_eq_add, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
  ring

private theorem disk_area_bound {a b c : ℝ²}
    (ha : a ∈ Metric.closedBall (0 : ℝ²) 1)
    (hb : b ∈ Metric.closedBall (0 : ℝ²) 1)
    (hc : c ∈ Metric.closedBall (0 : ℝ²) 1) :
    |EuclideanGeometry.triangle_area a b c| ≤ 4 := by
  have hcoord (x : ℝ²) (hx : x ∈ Metric.closedBall (0 : ℝ²) 1) (i : Fin 2) : |x i| ≤ 1 := by
    have hnorm : ‖x‖ ≤ 1 := by simpa [Metric.mem_closedBall, dist_zero_right] using hx
    exact (Real.norm_eq_abs (x i) ▸ PiLp.norm_apply_le x i).trans hnorm
  have hdiff (x : ℝ²) (hx : x ∈ Metric.closedBall (0 : ℝ²) 1) (i : Fin 2) : |x i - c i| ≤ 2 :=
    (abs_sub _ _).trans (by linarith [hcoord x hx i, hcoord c hc i])
  rw [signed_area_formula, abs_div, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2), div_le_iff₀ (by norm_num)]
  refine (abs_sub _ _).trans ?_
  rw [abs_mul, abs_mul]
  have h₁ := mul_le_mul (hdiff a ha 0) (hdiff b hb 1) (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 2)
  have h₂ := mul_le_mul (hdiff b hb 0) (hdiff a ha 1) (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 2)
  linarith

private theorem le_alpha_of_triangles {n : ℕ} (hn : 3 ≤ n)
    (S : Finset ℝ²) (hcard : S.card = n) (hS : (S : Set ℝ²) ⊆ Metric.closedBall 0 1)
    {r : ℝ} (hr : 0 < r) (htri : ∀ p : Fin 3 → ℝ², Function.Injective p → (∀ i, p i ∈ S) →
      r ≤ |EuclideanGeometry.triangle_area (p 0) (p 1) (p 2)|) : r ≤ α n := by
  have find_triple (T : Finset ℝ²) (hT : T.card = n) :
      ∃ p : Fin 3 → ℝ², Function.Injective p ∧ ∀ i, p i ∈ T := by
    obtain ⟨g, hg⟩ := Function.Embedding.exists_of_card_le_finset
      (α := Fin 3) (s := T) (by simpa [hT] using hn)
    exact ⟨g,g.injective,fun i => hg (Set.mem_range_self i)⟩
  obtain ⟨p, hp, hmem⟩ := find_triple S hcard
  have hcol : ¬ Collinear ℝ (S : Set ℝ²) := by
    intro hc
    have he := collinear_area hc (hmem 0) (hmem 1) (hmem 2)
    have h := htri p hp hmem
    rw [he, abs_zero] at h
    exact hr.not_ge h
  have hmin : r ≤ minTriangleArea S := by
    apply le_csInf
    · exact ⟨_, p, hp, hmem, rfl⟩
    · rintro _ ⟨q, hq, hm, rfl⟩
      exact htri q hq hm
  apply hmin.trans
  unfold α
  apply le_csSup
  · refine ⟨4, ?_⟩
    rintro _ ⟨T, ⟨hT, hDisk, _⟩, rfl⟩
    obtain ⟨q, hq, hm⟩ := find_triple T hT
    have hmin' : minTriangleArea T ≤ |EuclideanGeometry.triangle_area (q 0) (q 1) (q 2)| := by
      apply csInf_le
      · refine ⟨0, ?_⟩
        rintro _ ⟨u, hu, hmu, rfl⟩
        exact abs_nonneg _
      · exact ⟨q, hq, hm, rfl⟩
    exact hmin'.trans (disk_area_bound (hDisk (hm 0)) (hDisk (hm 1)) (hDisk (hm 2)))
  · exact ⟨S, ⟨hcard,hS,hcol⟩, rfl⟩

theorem main : H1 → H2 → type_of% @Erdos507.erdos_507.variants.lower_kps82 := by
  classical
  rintro ⟨C,hC,hSample⟩ ⟨a,ha,hInd⟩
  let ε := a^2 / (4*C)
  have hε : 0 < ε := by positivity
  refine Asymptotics.IsBigO.of_bound ε⁻¹ ?_
  filter_upwards [hSample ε hε, eventually_ge_atTop (3 : ℕ)] with n hs hn
  obtain ⟨S,E,d,hDisk,hEdges,hCover,hConf,hd,hDegree,hRatio⟩ := hs
  obtain ⟨W,hWS,hSW,hLinear⟩ := delete_conflicts S E hEdges hConf
  let F := E.filter (fun e => e ⊆ W)
  have hF (e) (he : e ∈ F) : e ⊆ W ∧ e.card = 3 := by
    obtain ⟨heE, heW⟩ := mem_filter.mp he
    exact ⟨heW, (hEdges e heE).2⟩
  have hFLinear (e) (he : e ∈ F) (f) (hf : f ∈ F) (hne : e ≠ f) : (e ∩ f).card ≤ 1 :=
    hLinear e (mem_filter.mp he).1 (hF e he).1 f (mem_filter.mp hf).1 (hF f hf).1 hne
  have hFcard : (F.card : ℝ) ≤ E.card := by exact_mod_cast card_filter_le _ _
  have hSW' : (S.card : ℝ) ≤ 2 * W.card := by exact_mod_cast hSW
  have hd0 : 0 < d := by linarith
  have hn0 : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hlog : 0 < Real.log d := Real.log_pos (by linarith)
  have hFdeg : 3 * (F.card : ℝ) ≤ d * W.card := by
    have h := mul_le_mul_of_nonneg_left hSW' hd0.le
    linarith
  obtain ⟨I,hIW,hFree,hI⟩ := hInd W F d hd hF hFLinear hFdeg
  have hcancel : C*ε = a^2/4 := by dsimp [ε]; field_simp
  have hDensity : d / Real.log d ≤ a^2 * ((W.card : ℝ)/n)^2 := by
    have hdivide : (S.card : ℝ) / n ≤ (2*W.card) / n :=
      div_le_div_of_nonneg_right hSW' hn0.le
    rw [hcancel] at hRatio
    refine hRatio.trans ?_
    calc a^2 / 4 * ((S.card : ℝ) / n)^2 ≤ a^2 / 4 * ((2*W.card : ℝ) / n)^2 :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hdivide 2) (by positivity)
        _ = _ := by ring
  rw [div_pow, ← mul_div_assoc] at hDensity
  have hSquared : (n : ℝ)^2 ≤ (a*W.card*Real.sqrt (Real.log d/d))^2 := by
    calc (n : ℝ)^2 = (d / Real.log d * (n : ℝ)^2) * (Real.log d / d) := by
          field_simp
        _ ≤ a^2 * (W.card : ℝ)^2 * (Real.log d / d) :=
          mul_le_mul_of_nonneg_right ((le_div_iff₀ (sq_pos_of_pos hn0)).mp hDensity) (by positivity)
        _ = _ := by rw [mul_pow, mul_pow, Real.sq_sqrt (by positivity)]
  have hEnough : n ≤ I.card := by
    have hRange : 0 ≤ a*W.card*Real.sqrt (Real.log d/d) := by positivity
    exact_mod_cast ((sq_le_sq₀ hn0.le hRange).mp hSquared).trans hI
  obtain ⟨T,hTI,hTcard⟩ := exists_subset_card_eq hEnough
  have hTW : T ⊆ W := hTI.trans hIW
  have hTS : T ⊆ S := hTW.trans hWS
  have hLowerPos : 0 < lowerBest n := by
    unfold lowerBest
    exact div_pos (Real.log_pos (by exact_mod_cast (show 1 < n by omega))) (by positivity)
  have αlower : ε * lowerBest n ≤ α n := by
    apply le_alpha_of_triangles hn T hTcard (fun _ hm => hDisk (hTS hm)) (mul_pos hε hLowerPos)
    intro p hp hM
    by_contra! hSmall
    have hMem : univ.image p ∈ E := hCover p hp (fun i => hTS (hM i)) hSmall.le
    have hInside : univ.image p ⊆ I := by
      intro x hx
      obtain ⟨j, _, rfl⟩ := mem_image.mp hx
      exact hTI (hM j)
    exact hFree _ (mem_filter.mpr ⟨hMem, hInside.trans hIW⟩) hInside
  have hα0 : 0 ≤ α n := (mul_pos hε hLowerPos).le.trans αlower
  rw [Real.norm_of_nonneg hLowerPos.le, Real.norm_of_nonneg hα0]
  calc lowerBest n = ε⁻¹ * (ε * lowerBest n) := by field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_left αlower (inv_nonneg.mpr hε.le)

end OMA.R_Erdos507_erdos_507_variants_lower_kps82_R1
