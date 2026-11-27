import FormalConjectures.GreensOpenProblems.«69»

-- Reduction Green69.green_69.variants.elekes_szabo.R1 of the Elekes–Szabó conjecture.
-- Credit: @chris01-dev
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

/-!
The Elekes–Szabó conjecture: a set of n points with at least c n^2 triple lines has ten points
on a cubic, for n large. It is open (Green, 100 open problems, Problem 69; Elekes and Szabó,
arXiv:1302.5777, Conjecture 2.1). This file proves every degenerate case and splits what is left
along the line drawn in the literature: point sets on a curve of bounded degree, which is a
theorem of Elekes and Szabó, and point sets with no dense part on such a curve, which is open.

Proved here, inside main:
* If four points of A are collinear, ten points of A lie on three lines (two further triple
  lines avoiding the points already chosen exist by counting), hence on a cubic.
* If seven points of A lie on a conic, the conic and one further triple line carry ten points.
* If nine points of A carry two linearly independent cubics (for example a three by three grid
  of six triple lines, or any nine points that are the intersection of two cubics), then with
  any tenth point of A they lie on a cubic of the pencil.
* Cleaning: A has a subset B that keeps c n^2 / 2 triple lines and in which every point lies
  on at least c n / 2 triple lines of B (maximise the number of triple lines minus c n / 2
  times the number of points).

In the remaining case the ten points have to lie on an irreducible cubic.

H1 is the conjecture for point sets lying on an algebraic curve of degree at most d, with no
four points collinear. For an irreducible curve this is Theorem 2.2 of Elekes and Szabó; a
curve with several components should follow from their theorem on three curves (Theorem 4.1)
and the pigeonhole principle.
H2 is the conjecture for point sets in general position (no four collinear, no seven on a
conic, any nine points on a unique cubic) with every point on many triple lines, under the
further hypothesis that no subset with at least m points on a curve of degree at most d has
c' times its size squared triple lines. The solver chooses d and c' in terms of c; m is
arbitrary, and the threshold may depend on it.

The split loses nothing: the target implies both H1 and H2.
-/

namespace OMA.R_Green69_green_69_variants_elekes_szabo_R1

open scoped Finset
open Green69 MvPolynomial

/-- A nonzero polynomial of degree at most one vanishing on the line through two distinct points. -/
lemma exists_linear_form {x y : ℝ × ℝ} (hxy : x ≠ y) :
    ∃ F : MvPolynomial (Fin 2) ℝ, F ≠ 0 ∧ F.totalDegree ≤ 1 ∧
      ∀ z ∈ line[ℝ, x, y], eval ![z.1, z.2] F = 0 := by
  refine ⟨C (y.2 - x.2) * (X 0 - C x.1) - C (y.1 - x.1) * (X 1 - C x.2), ?_, ?_, ?_⟩
  · intro h
    have h1 := congrArg (eval ![x.1 + 1, x.2]) h
    have h2 := congrArg (eval ![x.1, x.2 + 1]) h
    simp at h1 h2
    apply hxy
    ext <;> linarith
  · refine (totalDegree_sub _ _).trans (max_le ?_ ?_) <;>
    · refine (totalDegree_mul _ _).trans ?_
      rw [totalDegree_C, zero_add]
      refine (totalDegree_sub _ _).trans (max_le ?_ ?_)
      · exact (totalDegree_X _).le
      · simp
  · intro z hz
    rw [← vsub_vadd z x, vadd_left_mem_affineSpan_pair] at hz
    obtain ⟨r, hr⟩ := hz
    have h1 : r * (y.1 - x.1) = z.1 - x.1 := by simpa using congrArg Prod.fst hr
    have h2 : r * (y.2 - x.2) = z.2 - x.2 := by simpa using congrArg Prod.snd hr
    simp
    linear_combination (-(y.2 - x.2)) * h1 + (y.1 - x.1) * h2

/-- The line through two distinct points of a line is that line. -/
lemma line_eq_of_mem {x y p q : ℝ × ℝ} (hp : p ∈ line[ℝ, x, y]) (hq : q ∈ line[ℝ, x, y])
    (hpq : p ≠ q) : line[ℝ, p, q] = line[ℝ, x, y] := by
  obtain ⟨s, hs⟩ : ∃ s : ℝ, s • (y - x) = p - x := by
    have := hp
    rw [← vsub_vadd p x, vadd_left_mem_affineSpan_pair] at this
    simpa using this
  obtain ⟨t, ht⟩ : ∃ t : ℝ, t • (y - x) = q - x := by
    have := hq
    rw [← vsub_vadd q x, vadd_left_mem_affineSpan_pair] at this
    simpa using this
  have hst : t - s ≠ 0 := by
    intro h
    apply hpq
    have hst' : s = t := by linarith
    subst hst'
    exact sub_left_injective (hs.symm.trans ht)
  have hqp : q - p = (t - s) • (y - x) := by
    rw [sub_smul, hs, ht]; abel
  refine le_antisymm (affineSpan_pair_le_of_mem_of_mem hp hq)
    (affineSpan_pair_le_of_mem_of_mem ?_ ?_)
  · rw [← vsub_vadd x p, vadd_left_mem_affineSpan_pair]
    refine ⟨-s / (t - s), ?_⟩
    simp only [vsub_eq_sub]
    rw [hqp, smul_smul, div_mul_cancel₀ _ hst, neg_smul, hs]; abel
  · rw [← vsub_vadd y p, vadd_left_mem_affineSpan_pair]
    refine ⟨(1 - s) / (t - s), ?_⟩
    simp only [vsub_eq_sub]
    rw [hqp, smul_smul, div_mul_cancel₀ _ hst, sub_smul, one_smul, hs]; abel

/-- The set of triple lines is finite. -/
lemma tripleLines_finite (A : Finset (ℝ × ℝ)) : (tripleLines A).Finite := by
  classical
  refine Set.Finite.subset ((A ×ˢ A).image fun p : (ℝ × ℝ) × (ℝ × ℝ) => line[ℝ, p.1, p.2]).finite_toSet ?_
  rintro L ⟨x, hx, y, hy, z, -, -, -, -, -, rfl⟩
  exact Finset.mem_coe.2 (Finset.mem_image.2 ⟨(x, y), Finset.mem_product.2 ⟨hx, hy⟩, rfl⟩)

/-- If there are more triple lines than `#T * #A`, some triple line misses `T`. -/
lemma exists_tripleLine_avoiding (A T : Finset (ℝ × ℝ))
    (h : #T * #A < (tripleLines A).ncard) :
    ∃ x ∈ A, ∃ y ∈ A, ∃ z ∈ A, x ≠ y ∧ z ≠ x ∧ z ≠ y ∧ z ∈ line[ℝ, x, y] ∧
      x ∉ T ∧ y ∉ T ∧ z ∉ T := by
  classical
  set bad : Finset (AffineSubspace ℝ (ℝ × ℝ)) :=
    (T ×ˢ A).image fun p : (ℝ × ℝ) × (ℝ × ℝ) => line[ℝ, p.1, p.2] with hbad
  have hcard : (bad : Set (AffineSubspace ℝ (ℝ × ℝ))).ncard < (tripleLines A).ncard := by
    rw [Set.ncard_coe_finset]
    refine lt_of_le_of_lt (Finset.card_image_le.trans ?_) h
    rw [Finset.card_product]
  obtain ⟨L, hL, hLbad⟩ := Set.exists_mem_notMem_of_ncard_lt_ncard hcard bad.finite_toSet
  obtain ⟨x, hx, y, hy, z, hz, hxy, hzx, hzy, hzL, rfl⟩ := hL
  have key : ∀ p ∈ T, ∀ q ∈ A, line[ℝ, p, q] ≠ line[ℝ, x, y] := by
    intro p hp q hq he
    exact hLbad (Finset.mem_coe.2 (Finset.mem_image.2 ⟨(p, q), Finset.mem_product.2 ⟨hp, hq⟩, he⟩))
  refine ⟨x, hx, y, hy, z, hz, hxy, hzx, hzy, hzL, ?_, ?_, ?_⟩
  · exact fun hxT => key x hxT y hy rfl
  · exact fun hyT => key y hyT x hx (line_eq_of_mem (right_mem_affineSpan_pair _ _ _)
      (left_mem_affineSpan_pair _ _ _) hxy.symm)
  · exact fun hzT => key z hzT x hx (line_eq_of_mem hzL (left_mem_affineSpan_pair _ _ _) hzx)

/-- Adding a triple line to a curve: three more points, one more degree. -/
lemma extend_by_line (A T : Finset (ℝ × ℝ)) (hTA : T ⊆ A) (d : ℕ)
    (h : #T * #A < (tripleLines A).ncard)
    (hT : ∃ F : MvPolynomial (Fin 2) ℝ, F ≠ 0 ∧ F.totalDegree ≤ d ∧
      ∀ a ∈ T, eval ![a.1, a.2] F = 0) :
    ∃ T' ⊆ A, #T' = #T + 3 ∧ ∃ F : MvPolynomial (Fin 2) ℝ, F ≠ 0 ∧ F.totalDegree ≤ d + 1 ∧
      ∀ a ∈ T', eval ![a.1, a.2] F = 0 := by
  classical
  obtain ⟨x, hx, y, hy, z, hz, hxy, hzx, hzy, hzL, hxT, hyT, hzT⟩ :=
    exists_tripleLine_avoiding A T h
  obtain ⟨F, hF0, hFd, hF⟩ := hT
  obtain ⟨G, hG0, hGd, hG⟩ := exists_linear_form hxy
  refine ⟨T ∪ {x, y, z}, ?_, ?_, F * G, mul_ne_zero hF0 hG0, ?_, ?_⟩
  · intro a ha
    rcases Finset.mem_union.1 ha with ha | ha
    · exact hTA ha
    · simp only [Finset.mem_insert, Finset.mem_singleton] at ha
      rcases ha with rfl | rfl | rfl <;> assumption
  · rw [Finset.card_union_of_disjoint]
    · congr 1
      rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_singleton]
      · simpa using hzy.symm
      · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨hxy, hzx.symm⟩
    · rw [Finset.disjoint_right]
      intro a ha
      simp only [Finset.mem_insert, Finset.mem_singleton] at ha
      rcases ha with rfl | rfl | rfl <;> assumption
  · exact (totalDegree_mul _ _).trans (Nat.add_le_add hFd hGd)
  · intro a ha
    rw [map_mul]
    rcases Finset.mem_union.1 ha with ha | ha
    · rw [hF a ha, zero_mul]
    · simp only [Finset.mem_insert, Finset.mem_singleton] at ha
      have : a ∈ line[ℝ, x, y] := by
        rcases ha with rfl | rfl | rfl
        · exact left_mem_affineSpan_pair _ _ _
        · exact right_mem_affineSpan_pair _ _ _
        · exact hzL
      rw [hG a this, mul_zero]

/-- Four collinear points lie on a curve of degree one. -/
lemma linear_of_not_atMostOnLine {A : Finset (ℝ × ℝ)} (h : ¬ AtMostOnLine 3 A) :
    ∃ T ⊆ A, #T = 4 ∧ ∃ F : MvPolynomial (Fin 2) ℝ, F ≠ 0 ∧ F.totalDegree ≤ 1 ∧
      ∀ a ∈ T, eval ![a.1, a.2] F = 0 := by
  classical
  unfold AtMostOnLine at h
  push Not at h
  obtain ⟨S, hSA, hcol, hcard⟩ := h
  obtain ⟨T, hTS, hT4⟩ := Finset.exists_subset_card_eq (show 4 ≤ #S by omega)
  have hcolT : Collinear ℝ (T : Set (ℝ × ℝ)) := hcol.subset (Finset.coe_subset.2 hTS)
  obtain ⟨x, hx, y, hy, hxy⟩ := Finset.one_lt_card.1 (show 1 < #T by omega)
  obtain ⟨F, hF0, hFd, hF⟩ := exists_linear_form hxy
  exact ⟨T, hTS.trans hSA, hT4, F, hF0, hFd, fun a ha =>
    hF a (hcolT.mem_affineSpan_of_mem_of_ne (Finset.mem_coe.2 hx) (Finset.mem_coe.2 hy)
      (Finset.mem_coe.2 ha) hxy)⟩

/-- Nine points carrying two independent cubics, plus any tenth point, lie on a cubic. -/
lemma ten_of_pencil (A T : Finset (ℝ × ℝ)) (hTA : T ⊆ A) (hT : #T = 9) (hA : 10 ≤ #A)
    (F G : MvPolynomial (Fin 2) ℝ) (hF : F.totalDegree ≤ 3) (hG : G.totalDegree ≤ 3)
    (hFT : ∀ a ∈ T, eval ![a.1, a.2] F = 0) (hGT : ∀ a ∈ T, eval ![a.1, a.2] G = 0)
    (hind : ∀ a b : ℝ, (a ≠ 0 ∨ b ≠ 0) → a • F + b • G ≠ 0) :
    ∃ S ⊆ A, #S = 10 ∧ OnCubic S := by
  classical
  obtain ⟨p, hpA, hpT⟩ : ∃ p ∈ A, p ∉ T := by
    by_contra hcon
    push Not at hcon
    have := Finset.card_le_card (show A ⊆ T from hcon)
    omega
  refine ⟨insert p T, Finset.insert_subset hpA hTA, ?_, ?_⟩
  · rw [Finset.card_insert_of_notMem hpT, hT]
  · by_cases hab : eval ![p.1, p.2] G ≠ 0 ∨ -eval ![p.1, p.2] F ≠ 0
    · refine ⟨eval ![p.1, p.2] G • F + (-eval ![p.1, p.2] F) • G, hind _ _ hab, ?_, ?_⟩
      · exact (totalDegree_add _ _).trans (max_le ((totalDegree_smul_le _ _).trans hF)
          ((totalDegree_smul_le _ _).trans hG))
      · intro q hq
        rcases Finset.mem_insert.1 hq with rfl | hq
        · simp only [map_add, smul_eval]
          ring
        · simp only [map_add, smul_eval, hFT q hq, hGT q hq]
          ring
    · push Not at hab
      refine ⟨F, ?_, hF, ?_⟩
      · have := hind 1 0 (Or.inl one_ne_zero)
        simpa using this
      · intro q hq
        rcases Finset.mem_insert.1 hq with rfl | hq
        · have := hab.2
          linarith
        · exact hFT q hq

/-- A crude bound on the number of triple lines. -/
lemma tripleLines_ncard_le (A : Finset (ℝ × ℝ)) : (tripleLines A).ncard ≤ #A * #A := by
  classical
  have hsub : tripleLines A ⊆
      ((A ×ˢ A).image fun p : (ℝ × ℝ) × (ℝ × ℝ) => line[ℝ, p.1, p.2] : Finset _) := by
    rintro L ⟨x, hx, y, hy, z, -, -, -, -, -, rfl⟩
    exact Finset.mem_coe.2 (Finset.mem_image.2 ⟨(x, y), Finset.mem_product.2 ⟨hx, hy⟩, rfl⟩)
  refine (Set.ncard_le_ncard hsub (Finset.finite_toSet _)).trans ?_
  rw [Set.ncard_coe_finset]
  exact Finset.card_image_le.trans (Finset.card_product _ _).le

/-- Cleaning: a subset that keeps half of the triple lines and in which every point lies on
many triple lines. -/
lemma exists_clean (A : Finset (ℝ × ℝ)) (c : ℝ) (hc : 0 < c)
    (h : c * (#A : ℝ) ^ 2 ≤ (tripleLines A).ncard) :
    ∃ B ⊆ A, c / 2 * (#A : ℝ) ^ 2 ≤ (tripleLines B).ncard ∧
      ∀ p ∈ B, c / 2 * (#A : ℝ) ≤
        ({L ∈ tripleLines B | p ∈ L} : Set (AffineSubspace ℝ (ℝ × ℝ))).ncard := by
  classical
  obtain ⟨B, hB, hmax⟩ := Finset.exists_max_image A.powerset
    (fun B : Finset (ℝ × ℝ) => ((tripleLines B).ncard : ℝ) - c / 2 * (#A : ℝ) * #B)
    ⟨A, Finset.mem_powerset_self A⟩
  have hBA := Finset.mem_powerset.1 hB
  refine ⟨B, hBA, ?_, ?_⟩
  · have h1 := hmax A (Finset.mem_powerset_self A)
    have h2 : (0 : ℝ) ≤ c / 2 * (#A : ℝ) * #B := by positivity
    nlinarith
  · intro p hp
    have h1 := hmax (B.erase p) (Finset.mem_powerset.2 ((Finset.erase_subset _ _).trans hBA))
    have hsub : tripleLines B ⊆ tripleLines (B.erase p) ∪ {L ∈ tripleLines B | p ∈ L} := by
      intro L hL
      by_cases hpL : p ∈ L
      · exact Or.inr ⟨hL, hpL⟩
      · left
        obtain ⟨x, hx, y, hy, z, hz, hxy, hzx, hzy, hzL, rfl⟩ := hL
        refine ⟨x, Finset.mem_erase.2 ⟨?_, hx⟩, y, Finset.mem_erase.2 ⟨?_, hy⟩,
          z, Finset.mem_erase.2 ⟨?_, hz⟩, hxy, hzx, hzy, hzL, rfl⟩
        · rintro rfl
          exact hpL (left_mem_affineSpan_pair _ _ _)
        · rintro rfl
          exact hpL (right_mem_affineSpan_pair _ _ _)
        · rintro rfl
          exact hpL hzL
    have hfin : (tripleLines (B.erase p) ∪ {L ∈ tripleLines B | p ∈ L}).Finite :=
      (tripleLines_finite _).union ((tripleLines_finite B).subset (Set.sep_subset _ _))
    have hcard : (tripleLines B).ncard ≤ (tripleLines (B.erase p)).ncard +
        ({L ∈ tripleLines B | p ∈ L} : Set (AffineSubspace ℝ (ℝ × ℝ))).ncard :=
      (Set.ncard_le_ncard hsub hfin).trans (Set.ncard_union_le _ _)
    have hcard' : ((tripleLines B).ncard : ℝ) ≤ (tripleLines (B.erase p)).ncard +
        (({L ∈ tripleLines B | p ∈ L} : Set (AffineSubspace ℝ (ℝ × ℝ))).ncard : ℝ) := by
      exact_mod_cast hcard
    have he : (#(B.erase p) : ℝ) + 1 = #B := by
      exact_mod_cast Finset.card_erase_add_one hp
    nlinarith

-- The conjecture for point sets on an algebraic curve of bounded degree.
def H1 : Prop :=
  ∀ d : ℕ, ∀ c : ℝ, 0 < c → ∃ n₀ : ℕ, ∀ B : Finset (ℝ × ℝ), n₀ < #B →
    AtMostOnLine 3 B →
    (∃ F : MvPolynomial (Fin 2) ℝ, F ≠ 0 ∧ F.totalDegree ≤ d ∧
      ∀ a ∈ B, MvPolynomial.eval ![a.1, a.2] F = 0) →
    c * (#B : ℝ) ^ 2 ≤ (tripleLines B).ncard → ∃ S ⊆ B, #S = 10 ∧ OnCubic S

-- The conjecture for point sets in general position with no dense part on a curve.
def H2 : Prop :=
  ∀ c : ℝ, 0 < c → ∃ d : ℕ, ∃ c' : ℝ, 0 < c' ∧ ∀ m : ℕ, ∃ n₀ : ℕ,
    ∀ A : Finset (ℝ × ℝ), n₀ < #A →
    AtMostOnLine 3 A →
    (∀ T ⊆ A, #T = 7 → ∀ F : MvPolynomial (Fin 2) ℝ, F ≠ 0 → F.totalDegree ≤ 2 →
      ∃ a ∈ T, MvPolynomial.eval ![a.1, a.2] F ≠ 0) →
    (∀ T ⊆ A, #T = 9 → ∀ F G : MvPolynomial (Fin 2) ℝ, F.totalDegree ≤ 3 → G.totalDegree ≤ 3 →
      (∀ a ∈ T, MvPolynomial.eval ![a.1, a.2] F = 0) →
      (∀ a ∈ T, MvPolynomial.eval ![a.1, a.2] G = 0) →
      ∃ a b : ℝ, (a ≠ 0 ∨ b ≠ 0) ∧ a • F + b • G = 0) →
    (∀ B ⊆ A, m ≤ #B →
      (∃ F : MvPolynomial (Fin 2) ℝ, F ≠ 0 ∧ F.totalDegree ≤ d ∧
        ∀ a ∈ B, MvPolynomial.eval ![a.1, a.2] F = 0) →
      ((tripleLines B).ncard : ℝ) < c' * (#B : ℝ) ^ 2) →
    c * (#A : ℝ) ^ 2 ≤ (tripleLines A).ncard →
    (∀ p ∈ A, c * (#A : ℝ) ≤
      ({L ∈ tripleLines A | p ∈ L} : Set (AffineSubspace ℝ (ℝ × ℝ))).ncard) →
    ∃ S ⊆ A, #S = 10 ∧ OnCubic S

theorem main : H1 → H2 → type_of% @Green69.green_69.variants.elekes_szabo := by
  intro h1 h2 c hc
  obtain ⟨d, c', hc', h2'⟩ := h2 (c / 2) (by positivity)
  obtain ⟨m₀, h1'⟩ := h1 d c' hc'
  obtain ⟨n₂, h2''⟩ := h2' (m₀ + 1)
  obtain ⟨N, hN⟩ := exists_nat_ge (max (7 / c) (2 * ((n₂ : ℝ) + 1) ^ 2 / c))
  refine ⟨N + 10, fun A hA hden => ?_⟩
  have hn10 : 10 ≤ #A := by omega
  have hnR : (N : ℝ) + 10 < (#A : ℝ) := by exact_mod_cast hA
  have hnpos : (1 : ℝ) ≤ (#A : ℝ) := by
    have : (0 : ℝ) ≤ N := Nat.cast_nonneg N
    linarith
  have h7 : 7 / c < (#A : ℝ) := by
    have := (le_max_left _ _).trans hN
    linarith
  have hbig : 2 * ((n₂ : ℝ) + 1) ^ 2 / c < (#A : ℝ) := by
    have := (le_max_right _ _).trans hN
    linarith
  have h7' : 7 < c * (#A : ℝ) := by
    rw [div_lt_iff₀ hc] at h7
    linarith
  have hlinesR : (7 * (#A : ℝ)) < ((tripleLines A).ncard : ℝ) := by nlinarith
  have hlines : 7 * #A < (tripleLines A).ncard := by exact_mod_cast hlinesR
  by_cases hL : AtMostOnLine 3 A
  swap
  · obtain ⟨T, hTA, hT4, hF⟩ := linear_of_not_atMostOnLine hL
    obtain ⟨T', hT'A, hT'c, hF'⟩ := extend_by_line A T hTA 1
      (by rw [hT4]; omega) hF
    obtain ⟨T'', hT''A, hT''c, F, hF0, hFd, hFv⟩ := extend_by_line A T' hT'A 2
      (by rw [hT'c, hT4]; omega) hF'
    exact ⟨T'', hT''A, by omega, F, hF0, hFd, hFv⟩
  by_cases hC : ∀ T ⊆ A, #T = 7 → ∀ F : MvPolynomial (Fin 2) ℝ, F ≠ 0 → F.totalDegree ≤ 2 →
      ∃ a ∈ T, MvPolynomial.eval ![a.1, a.2] F ≠ 0
  swap
  · push Not at hC
    obtain ⟨T, hTA, hT7, F, hF0, hFd, hFv⟩ := hC
    obtain ⟨T', hT'A, hT'c, F', hF0', hFd', hFv'⟩ := extend_by_line A T hTA 2
      (by rw [hT7]; omega) ⟨F, hF0, hFd, hFv⟩
    exact ⟨T', hT'A, by omega, F', hF0', hFd', hFv'⟩
  by_cases h9 : ∀ T ⊆ A, #T = 9 → ∀ F G : MvPolynomial (Fin 2) ℝ, F.totalDegree ≤ 3 →
      G.totalDegree ≤ 3 →
      (∀ a ∈ T, MvPolynomial.eval ![a.1, a.2] F = 0) →
      (∀ a ∈ T, MvPolynomial.eval ![a.1, a.2] G = 0) →
      ∃ a b : ℝ, (a ≠ 0 ∨ b ≠ 0) ∧ a • F + b • G = 0
  swap
  · push Not at h9
    obtain ⟨T, hTA, hT9, F, G, hF, hG, hFT, hGT, hind⟩ := h9
    exact ten_of_pencil A T hTA hT9 hn10 F G hF hG hFT hGT hind
  obtain ⟨B, hBA, hBden, hBdeg⟩ := exists_clean A c hc hden
  have hBn : (#B : ℝ) ≤ (#A : ℝ) := by exact_mod_cast Finset.card_le_card hBA
  have hB0 : (0 : ℝ) ≤ (#B : ℝ) := Nat.cast_nonneg _
  have hBden' : c / 2 * (#B : ℝ) ^ 2 ≤ (tripleLines B).ncard := by
    refine le_trans ?_ hBden
    have : (#B : ℝ) ^ 2 ≤ (#A : ℝ) ^ 2 := by nlinarith
    nlinarith
  have hBdeg' : ∀ p ∈ B, c / 2 * (#B : ℝ) ≤
      ({L ∈ tripleLines B | p ∈ L} : Set (AffineSubspace ℝ (ℝ × ℝ))).ncard := by
    intro p hp
    refine le_trans ?_ (hBdeg p hp)
    nlinarith
  have hBbig : n₂ < #B := by
    have hup : ((tripleLines B).ncard : ℝ) ≤ (#B : ℝ) * (#B : ℝ) := by
      exact_mod_cast tripleLines_ncard_le B
    have h3 : ((n₂ : ℝ) + 1) ^ 2 < c / 2 * (#A : ℝ) := by
      rw [div_lt_iff₀ hc] at hbig
      linarith
    have h4 : c / 2 * (#A : ℝ) ≤ c / 2 * (#A : ℝ) ^ 2 := by nlinarith
    have h5 : ((n₂ : ℝ) + 1) ^ 2 < (#B : ℝ) * (#B : ℝ) := by linarith
    have h6 : (n₂ : ℝ) + 1 < (#B : ℝ) := by
      by_contra hcon
      push Not at hcon
      have h0 : (0 : ℝ) ≤ (n₂ : ℝ) := Nat.cast_nonneg _
      nlinarith
    have h7 : ((n₂ + 1 : ℕ) : ℝ) < (#B : ℝ) := by push_cast; exact h6
    have := Nat.cast_lt.1 h7
    omega
  have hLB : AtMostOnLine 3 B := fun S hS => hL S (hS.trans hBA)
  by_cases hfree : ∀ B' ⊆ B, m₀ + 1 ≤ #B' →
      (∃ F : MvPolynomial (Fin 2) ℝ, F ≠ 0 ∧ F.totalDegree ≤ d ∧
        ∀ a ∈ B', MvPolynomial.eval ![a.1, a.2] F = 0) →
      ((tripleLines B').ncard : ℝ) < c' * (#B' : ℝ) ^ 2
  · obtain ⟨S, hS, h⟩ := h2'' B hBbig hLB
      (fun T hT => hC T (hT.trans hBA)) (fun T hT => h9 T (hT.trans hBA)) hfree hBden' hBdeg'
    exact ⟨S, hS.trans hBA, h⟩
  · push Not at hfree
    obtain ⟨B', hB'B, hm, hcurve, hden'⟩ := hfree
    obtain ⟨S, hS, h⟩ := h1' B' (by omega) (fun S hS => hLB S (hS.trans hB'B)) hcurve hden'
    exact ⟨S, hS.trans (hB'B.trans hBA), h⟩

end OMA.R_Green69_green_69_variants_elekes_szabo_R1
