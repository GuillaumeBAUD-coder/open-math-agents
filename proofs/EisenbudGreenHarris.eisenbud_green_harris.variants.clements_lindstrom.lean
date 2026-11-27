import FormalConjectures.Paper.EisenbudGreenHarris
import Mathlib.Data.Finsupp.Lex

/-!
# The Clements-Lindström Theorem

Proof of `EisenbudGreenHarris.eisenbud_green_harris.variants.clements_lindstrom`:
every homogeneous ideal in `k[x₁, ..., xₙ]` containing `purePowersIdeal hc d` (with `d` monotone)
has the same Hilbert function as `L + purePowersIdeal hc d` for some lex ideal `L`.
-/

-- Problem: The Clements-Lindström theorem
-- Upstream: formal-conjectures FormalConjectures/Paper/EisenbudGreenHarris.lean:119 (declaration EisenbudGreenHarris.eisenbud_green_harris.variants.clements_lindstrom)
-- Credit: @Dugongue (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

namespace ClementsLindstromProof

open MvPolynomial Finset

/- Part 1: Monomials of fixed degree, boxes, lex order, and upward shadow -/

/-- All exponent vectors of degree `e` in `n` variables. -/
noncomputable def monOfDeg (n e : ℕ) : Finset (Fin n →₀ ℕ) :=
  ((Fintype.piFinset (fun _ : Fin n => Finset.range (e + 1))).image
    Finsupp.equivFunOnFinite.symm).filter (fun u => u.degree = e)

lemma mem_monOfDeg {n e : ℕ} {u : Fin n →₀ ℕ} :
    u ∈ monOfDeg n e ↔ u.degree = e := by
  simp only [monOfDeg, mem_filter, mem_image, Fintype.mem_piFinset, mem_range, and_iff_right_iff_imp]
  intro hdeg
  refine ⟨fun i => u i, fun i => ?_, ?_⟩
  · have hle : u i ≤ ∑ j : Fin n, u j :=
      Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
    rw [← Finsupp.degree_eq_sum, hdeg] at hle
    dsimp only
    omega
  · ext i
    simp

/-- All exponent vectors of degree `e` bounded strictly coordinatewise by `D`. -/
noncomputable def monBox {n : ℕ} (D : Fin n → ℕ) (e : ℕ) : Finset (Fin n →₀ ℕ) :=
  (monOfDeg n e).filter (fun u => ∀ i : Fin n, u i < D i)

lemma mem_monBox {n : ℕ} {D : Fin n → ℕ} {e : ℕ} {u : Fin n →₀ ℕ} :
    u ∈ monBox D e ↔ u.degree = e ∧ ∀ i : Fin n, u i < D i := by
  simp [monBox, mem_monOfDeg]

lemma monBox_subset_monOfDeg {n : ℕ} (D : Fin n → ℕ) (e : ℕ) :
    monBox D e ⊆ monOfDeg n e :=
  Finset.filter_subset _ _

lemma lex_lt_iff {n : ℕ} {u v : Fin n →₀ ℕ} :
    toLex u < toLex v ↔ ∃ i : Fin n, (∀ j < i, u j = v j) ∧ u i < v i :=
  Finsupp.Lex.lt_iff

lemma toLex_add_single_strictMono {n : ℕ} (i : Fin n) :
    StrictMono (fun u : Lex (Fin n →₀ ℕ) => toLex (ofLex u + Finsupp.single i 1)) := by
  intro a b hab
  rw [Finsupp.Lex.lt_iff] at hab ⊢
  obtain ⟨j, hlt, hj⟩ := hab
  refine ⟨j, fun r hr => ?_, ?_⟩
  · simp [hlt r hr]
  · simp only [ofLex_toLex, Finsupp.coe_add, Pi.add_apply]
    omega

/-- The upward shadow of a set of exponent vectors. -/
noncomputable def shadow {n : ℕ} (M : Finset (Fin n →₀ ℕ)) : Finset (Fin n →₀ ℕ) :=
  M.biUnion (fun u => Finset.univ.image (fun i : Fin n => u + Finsupp.single i 1))

lemma mem_shadow {n : ℕ} {M : Finset (Fin n →₀ ℕ)} {v : Fin n →₀ ℕ} :
    v ∈ shadow M ↔ ∃ u ∈ M, ∃ i : Fin n, u + Finsupp.single i 1 = v := by
  simp [shadow]

lemma shadow_subset_monOfDeg {n e : ℕ} {M : Finset (Fin n →₀ ℕ)} (hM : M ⊆ monOfDeg n e) :
    shadow M ⊆ monOfDeg n (e + 1) := by
  intro v hv
  rw [mem_shadow] at hv
  obtain ⟨u, hu, i, rfl⟩ := hv
  rw [mem_monOfDeg, map_add, Finsupp.degree_single, (mem_monOfDeg.mp (hM hu))]

lemma shadow_mono {n : ℕ} {A B : Finset (Fin n →₀ ℕ)} (h : A ⊆ B) :
    shadow A ⊆ shadow B := by
  intro v hv
  rw [mem_shadow] at hv ⊢
  obtain ⟨u, hu, i, rfl⟩ := hv
  exact ⟨u, h hu, i, rfl⟩

/-- The upward shadow restricted to the box `D`. -/
noncomputable def shadowBox {n : ℕ} (D : Fin n → ℕ) (M : Finset (Fin n →₀ ℕ)) :
    Finset (Fin n →₀ ℕ) :=
  (shadow M).filter (fun u => ∀ i : Fin n, u i < D i)

lemma mem_shadowBox {n : ℕ} {D : Fin n → ℕ} {M : Finset (Fin n →₀ ℕ)} {v : Fin n →₀ ℕ} :
    v ∈ shadowBox D M ↔ (∃ u ∈ M, ∃ i : Fin n, u + Finsupp.single i 1 = v) ∧ ∀ i, v i < D i := by
  simp [shadowBox, mem_shadow]

lemma shadowBox_subset_monBox {n e : ℕ} {D : Fin n → ℕ} {M : Finset (Fin n →₀ ℕ)}
    (hM : M ⊆ monBox D e) :
    shadowBox D M ⊆ monBox D (e + 1) := by
  intro v hv
  rw [mem_shadowBox] at hv
  obtain ⟨⟨u, hu, i, rfl⟩, hlt⟩ := hv
  rw [mem_monBox]
  exact ⟨by rw [map_add, Finsupp.degree_single, (mem_monBox.mp (hM hu)).1], hlt⟩

lemma shadowBox_mono {n : ℕ} (D : Fin n → ℕ) {A B : Finset (Fin n →₀ ℕ)} (h : A ⊆ B) :
    shadowBox D A ⊆ shadowBox D B := by
  intro v hv
  rw [mem_shadowBox] at hv ⊢
  obtain ⟨⟨u, hu, i, rfl⟩, hlt⟩ := hv
  exact ⟨⟨u, h hu, i, rfl⟩, hlt⟩

lemma shadowBox_empty {n : ℕ} (D : Fin n → ℕ) :
    shadowBox D (∅ : Finset (Fin n →₀ ℕ)) = ∅ := by
  simp [shadowBox, shadow]

lemma sub_single_add_single {n : ℕ} {u : Fin n →₀ ℕ} {s : Fin n} (hs : 1 ≤ u s) :
    (u - Finsupp.single s 1) + Finsupp.single s 1 = u := by
  ext j
  by_cases hj : j = s
  · subst hj; simp only [Finsupp.coe_add, Finsupp.coe_tsub, Pi.add_apply, Pi.sub_apply,
      Finsupp.single_eq_same]; omega
  · simp [Ne.symm hj]

lemma degree_sub_single {n : ℕ} {u : Fin n →₀ ℕ} {s : Fin n} (hs : 1 ≤ u s) :
    (u - Finsupp.single s 1).degree + 1 = u.degree := by
  have h := congrArg Finsupp.degree (sub_single_add_single hs)
  rw [map_add, Finsupp.degree_single] at h
  exact h

/- Part 2: Lex-initial segments in a box and closure under shadowBox -/

/-- A subset of `monBox D e` that is upward-closed in `toLex` inside `monBox D e`. -/
def IsLexBox {n : ℕ} (D : Fin n → ℕ) (e : ℕ) (M : Finset (Fin n →₀ ℕ)) : Prop :=
  M ⊆ monBox D e ∧ ∀ u ∈ monBox D e, ∀ v ∈ M, toLex v < toLex u → u ∈ M

/-- The top `r` monomials of `monBox D e` under `toLex`. -/
noncomputable def lexSegBox {n : ℕ} (D : Fin n → ℕ) (e r : ℕ) : Finset (Fin n →₀ ℕ) :=
  ((((monBox D e).image toLex).sort (· ≤ ·)).reverse.take r).toFinset.image ofLex

lemma lexSegBox_subset_monBox {n : ℕ} (D : Fin n → ℕ) (e r : ℕ) :
    lexSegBox D e r ⊆ monBox D e := by
  intro u hu
  simp only [lexSegBox, mem_image, List.mem_toFinset] at hu
  obtain ⟨x, hx, rfl⟩ := hu
  have hx' : x ∈ ((monBox D e).image toLex).sort (· ≤ ·) :=
    List.mem_reverse.mp (List.mem_of_mem_take hx)
  rw [Finset.mem_sort, mem_image] at hx'
  obtain ⟨w, hw, hw'⟩ := hx'
  have : ofLex x = w := by rw [← hw']; rfl
  rwa [this]

lemma card_lexSegBox {n : ℕ} {D : Fin n → ℕ} {e r : ℕ} (hr : r ≤ (monBox D e).card) :
    (lexSegBox D e r).card = r := by
  have hinj : Function.Injective (ofLex : Lex (Fin n →₀ ℕ) → (Fin n →₀ ℕ)) := fun _ _ h => h
  rw [lexSegBox, Finset.card_image_of_injective _ hinj]
  set l := ((monBox D e).image toLex).sort (· ≤ ·)
  have hnodup : (l.reverse.take r).Nodup :=
    (List.nodup_reverse.mpr (Finset.sort_nodup _ _)).take
  rw [List.toFinset_card_of_nodup hnodup, List.length_take, List.length_reverse]
  have hlen : l.length = (monBox D e).card := by
    rw [Finset.length_sort, Finset.card_image_of_injective _ toLex.injective]
  omega

lemma isLexBox_lexSegBox {n : ℕ} (D : Fin n → ℕ) (e r : ℕ) : IsLexBox D e (lexSegBox D e r) := by
  refine ⟨lexSegBox_subset_monBox D e r, ?_⟩
  intro u hu v hv hlt
  set l := ((monBox D e).image toLex).sort (· ≤ ·)
  have hl_pair : l.reverse.Pairwise (fun a b : Lex (Fin n →₀ ℕ) => b ≤ a) := by
    rw [List.pairwise_reverse]
    exact Finset.pairwise_sort _ _
  simp only [lexSegBox, mem_image, List.mem_toFinset] at hv ⊢
  obtain ⟨vx, hvx, hv_eq⟩ := hv
  have hvx_eq : vx = toLex v := by rw [← hv_eq]; rfl
  rw [hvx_eq] at hvx
  refine ⟨toLex u, ?_, rfl⟩
  have hu_mem : toLex u ∈ l.reverse := by
    rw [List.mem_reverse, Finset.mem_sort, mem_image]
    exact ⟨u, hu, rfl⟩
  obtain ⟨iu, hiu_lt, hiu_eq⟩ := List.getElem_of_mem hu_mem
  obtain ⟨iv, hiv_lt, hiv_eq⟩ := List.getElem_of_mem hvx
  have hiv_lt_min : iv < min r l.reverse.length := by
    simpa [l, List.length_take] using hiv_lt
  have hiv_lt_r : iv < r := lt_of_lt_of_le hiv_lt_min (min_le_left _ _)
  have hiv_lt_len : iv < l.reverse.length := lt_of_lt_of_le hiv_lt_min (min_le_right _ _)
  have hiv_eq' : l.reverse[iv]'hiv_lt_len = toLex v := by
    rw [← hiv_eq, List.getElem_take]
  have hiu_lt_iv : iu < iv := by
    by_contra hge
    push Not at hge
    rcases eq_or_lt_of_le hge with rfl | hgt
    · rw [hiu_eq] at hiv_eq'
      exact lt_irrefl _ (hiv_eq' ▸ hlt)
    · have hle : l.reverse[iu]'hiu_lt ≤ l.reverse[iv]'hiv_lt_len :=
        List.pairwise_iff_getElem.mp hl_pair iv iu hiv_lt_len hiu_lt hgt
      rw [hiu_eq, hiv_eq'] at hle
      exact not_lt_of_ge hle hlt
  have hiu_lt_take : iu < (l.reverse.take r).length := by
    rw [List.length_take]
    exact lt_min (lt_trans hiu_lt_iv hiv_lt_r) hiu_lt
  have hget : (l.reverse.take r)[iu]'hiu_lt_take = toLex u := by
    rw [List.getElem_take, hiu_eq]
  rw [← hget]
  exact List.getElem_mem hiu_lt_take

lemma IsLexBox.total_subset {n e : ℕ} {D : Fin n → ℕ} {A B : Finset (Fin n →₀ ℕ)}
    (hA : IsLexBox D e A) (hB : IsLexBox D e B) : A ⊆ B ∨ B ⊆ A := by
  by_contra h
  push Not at h
  obtain ⟨h1, h2⟩ := h
  obtain ⟨a, haA, haB⟩ := Finset.not_subset.mp h1
  obtain ⟨b, hbB, hbA⟩ := Finset.not_subset.mp h2
  rcases lt_trichotomy (toLex a) (toLex b) with hlt | heq | hgt
  · exact hbA (hA.2 b (hB.1 hbB) a haA hlt)
  · have : a = b := heq
    exact haB (this ▸ hbB)
  · exact haB (hB.2 a (hA.1 haA) b hbB hgt)

lemma IsLexBox.subset_of_card_le {n e : ℕ} {D : Fin n → ℕ} {A B : Finset (Fin n →₀ ℕ)}
    (hA : IsLexBox D e A) (hB : IsLexBox D e B) (hc : A.card ≤ B.card) : A ⊆ B := by
  rcases hA.total_subset hB with h | h
  · exact h
  · exact (Finset.eq_of_subset_of_card_le h hc).symm.subset

lemma IsLexBox.eq_of_card_eq {n e : ℕ} {D : Fin n → ℕ} {A B : Finset (Fin n →₀ ℕ)}
    (hA : IsLexBox D e A) (hB : IsLexBox D e B) (hc : A.card = B.card) : A = B :=
  Finset.Subset.antisymm (hA.subset_of_card_le hB hc.le) (hB.subset_of_card_le hA hc.ge)

lemma IsLexBox.eq_lexSegBox {n e : ℕ} {D : Fin n → ℕ} {A : Finset (Fin n →₀ ℕ)}
    (hA : IsLexBox D e A) :
    A = lexSegBox D e A.card :=
  hA.eq_of_card_eq (isLexBox_lexSegBox D e A.card)
    (card_lexSegBox (Finset.card_le_card hA.1)).symm

lemma IsLexBox.card_union {n e : ℕ} {D : Fin n → ℕ} {A B : Finset (Fin n →₀ ℕ)}
    (hA : IsLexBox D e A) (hB : IsLexBox D e B) :
    (A ∪ B).card = max A.card B.card := by
  rcases hA.total_subset hB with h | h
  · rw [Finset.union_eq_right.mpr h, max_eq_right (Finset.card_le_card h)]
  · rw [Finset.union_eq_left.mpr h, max_eq_left (Finset.card_le_card h)]

/-- The box shadow of a lex box set is again a lex box set. -/
lemma IsLexBox.shadowBox {n e : ℕ} {D : Fin n → ℕ} {L : Finset (Fin n →₀ ℕ)}
    (hL : IsLexBox D e L) :
    IsLexBox D (e + 1) (shadowBox D L) := by
  refine ⟨shadowBox_subset_monBox hL.1, ?_⟩
  intro u hu v hv hlt
  rw [mem_shadowBox] at hv ⊢
  obtain ⟨⟨w, hw, r, rfl⟩, _⟩ := hv
  obtain ⟨hdeg_u, hu_box⟩ := mem_monBox.mp hu
  refine ⟨?_, hu_box⟩
  rw [lex_lt_iff] at hlt
  obtain ⟨j, hjeq, hjlt⟩ := hlt
  have hdeg_w : w.degree = e := (mem_monBox.mp (hL.1 hw)).1
  have hsub_box : ∀ s : Fin n, 1 ≤ u s → u - Finsupp.single s 1 ∈ monBox D e := by
    intro s hs
    rw [mem_monBox]
    refine ⟨by have := degree_sub_single hs; omega, fun i => ?_⟩
    have := hu_box i
    simp only [Finsupp.coe_tsub, Pi.sub_apply]
    omega
  by_cases hrj : r < j
  · have hur : 1 ≤ u r := by
      have := hjeq r hrj
      simp only [Finsupp.coe_add, Pi.add_apply, Finsupp.single_eq_same] at this
      omega
    refine ⟨u - Finsupp.single r 1, ?_, r, sub_single_add_single hur⟩
    apply hL.2 _ (hsub_box r hur) w hw
    rw [lex_lt_iff]
    refine ⟨j, fun i hi => ?_, ?_⟩
    · have hi_eq := hjeq i hi
      simp only [Finsupp.coe_add, Finsupp.coe_tsub, Pi.add_apply, Pi.sub_apply,
        Finsupp.single_apply] at hi_eq ⊢
      split_ifs at hi_eq ⊢ <;> omega
    · have hne : r ≠ j := ne_of_lt hrj
      simp only [Finsupp.coe_add, Finsupp.coe_tsub, Pi.add_apply, Pi.sub_apply,
        Finsupp.single_apply, if_neg hne] at hjlt ⊢
      omega
  · push Not at hrj
    have hu_supp : u.support.Nonempty := by
      rw [Finsupp.support_nonempty_iff]
      intro h0
      rw [h0, map_zero] at hdeg_u
      omega
    set s := u.support.max' hu_supp
    have hs_pos : 1 ≤ u s :=
      Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp (Finset.max'_mem _ hu_supp))
    have hj_pos : 0 < u j := lt_of_le_of_lt (Nat.zero_le _) hjlt
    have hjs : j ≤ s :=
      Finset.le_max' _ j (Finsupp.mem_support_iff.mpr (by omega))
    refine ⟨u - Finsupp.single s 1, ?_, s, sub_single_add_single hs_pos⟩
    rcases lt_or_eq_of_le hjs with hlt_js | hjeqs
    · apply hL.2 _ (hsub_box s hs_pos) w hw
      rw [lex_lt_iff]
      refine ⟨j, fun i hi => ?_, ?_⟩
      · have hi_eq := hjeq i hi
        have hri : r ≠ i := ne_of_gt (lt_of_lt_of_le hi hrj)
        have hsi : s ≠ i := ne_of_gt (lt_trans hi hlt_js)
        simp only [Finsupp.coe_add, Finsupp.coe_tsub, Pi.add_apply, Pi.sub_apply,
          Finsupp.single_apply, if_neg hri, if_neg hsi] at hi_eq ⊢
        omega
      · have hsj : s ≠ j := ne_of_gt hlt_js
        simp only [Finsupp.coe_add, Finsupp.coe_tsub, Pi.add_apply, Pi.sub_apply,
          Finsupp.single_apply, if_neg hsj] at hjlt ⊢
        omega
    · rw [← hjeqs] at hs_pos ⊢
      set u' : Fin n →₀ ℕ := u - Finsupp.single j 1
      have hu'_box : u' ∈ monBox D e := hsub_box j hs_pos
      have hu'_deg : u'.degree = e := (mem_monBox.mp hu'_box).1
      have hu'_apply : ∀ i : Fin n, u' i = u i - (if j = i then 1 else 0) := fun i => by
        simp [u', Finsupp.single_apply]
      have hlt_w_le : w j ≤ u' j := by
        have h1 := hu'_apply j
        simp only [ite_true] at h1
        simp only [Finsupp.coe_add, Pi.add_apply] at hjlt
        omega
      rcases lt_or_eq_of_le hlt_w_le with hj_strict | hj_eq_w
      · apply hL.2 _ hu'_box w hw
        rw [lex_lt_iff]
        refine ⟨j, fun i hi => ?_, hj_strict⟩
        have hi_eq := hjeq i hi
        have hri : r ≠ i := ne_of_gt (lt_of_lt_of_le hi hrj)
        have hji : j ≠ i := ne_of_gt hi
        have h1 := hu'_apply i
        rw [if_neg hji] at h1
        simp only [Finsupp.coe_add, Pi.add_apply, Finsupp.single_apply, if_neg hri] at hi_eq
        omega
      · have hw_eq : u' = w := by
          have hle_all : ∀ i : Fin n, u' i ≤ w i := by
            intro i
            rcases lt_trichotomy i j with hij | rfl | hij
            · have hi_eq := hjeq i hij
              have hri : r ≠ i := ne_of_gt (lt_of_lt_of_le hij hrj)
              have hji : j ≠ i := ne_of_gt hij
              have h1 := hu'_apply i
              rw [if_neg hji] at h1
              simp only [Finsupp.coe_add, Pi.add_apply, Finsupp.single_apply, if_neg hri] at hi_eq
              omega
            · omega
            · have hui0 : u i = 0 := by
                by_contra hne
                have hle : i ≤ s := Finset.le_max' _ i (Finsupp.mem_support_iff.mpr hne)
                rw [← hjeqs] at hle
                exact not_lt_of_ge hle hij
              have h1 := hu'_apply i
              omega
          have hsum_eq : ∑ i : Fin n, u' i = ∑ i : Fin n, w i := by
            rw [← Finsupp.degree_eq_sum, ← Finsupp.degree_eq_sum, hu'_deg, hdeg_w]
          ext i
          by_contra hne
          have hlt_i : u' i < w i := lt_of_le_of_ne (hle_all i) hne
          have hsum_lt := Finset.sum_lt_sum (fun x _ => hle_all x) ⟨i, Finset.mem_univ i, hlt_i⟩
          omega
        rwa [hw_eq]

/- Part 3: Coordinate deletion/insertion, slicing, and box compression -/

noncomputable def deleteCoord {m : ℕ} (i : Fin (m + 1)) (u : Fin (m + 1) →₀ ℕ) : Fin m →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun j : Fin m => u (i.succAbove j))

noncomputable def insertCoord {m : ℕ} (i : Fin (m + 1)) (a : ℕ) (w : Fin m →₀ ℕ) :
    Fin (m + 1) →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (i.insertNth a (fun j : Fin m => w j))

@[simp]
lemma deleteCoord_apply {m : ℕ} (i : Fin (m + 1)) (u : Fin (m + 1) →₀ ℕ) (j : Fin m) :
    deleteCoord i u j = u (i.succAbove j) := by
  simp [deleteCoord]

@[simp]
lemma insertCoord_apply_same {m : ℕ} (i : Fin (m + 1)) (a : ℕ) (w : Fin m →₀ ℕ) :
    insertCoord i a w i = a := by
  simp [insertCoord]

@[simp]
lemma insertCoord_apply_succAbove {m : ℕ} (i : Fin (m + 1)) (a : ℕ) (w : Fin m →₀ ℕ) (j : Fin m) :
    insertCoord i a w (i.succAbove j) = w j := by
  simp [insertCoord]

lemma deleteCoord_insertCoord {m : ℕ} (i : Fin (m + 1)) (a : ℕ) (w : Fin m →₀ ℕ) :
    deleteCoord i (insertCoord i a w) = w := by
  ext j; simp

lemma insertCoord_deleteCoord {m : ℕ} (i : Fin (m + 1)) (u : Fin (m + 1) →₀ ℕ) :
    insertCoord i (u i) (deleteCoord i u) = u := by
  ext k
  by_cases hk : k = i
  · subst hk; simp
  · obtain ⟨j, rfl⟩ := Fin.exists_succAbove_eq hk
    simp

lemma insertCoord_injective {m : ℕ} (i : Fin (m + 1)) (a : ℕ) :
    Function.Injective (insertCoord i a) := by
  intro w₁ w₂ h
  have := congrArg (deleteCoord i) h
  simpa [deleteCoord_insertCoord] using this

lemma degree_insertCoord {m : ℕ} (i : Fin (m + 1)) (a : ℕ) (w : Fin m →₀ ℕ) :
    (insertCoord i a w).degree = a + w.degree := by
  rw [Finsupp.degree_eq_sum, Finsupp.degree_eq_sum, Fin.sum_univ_succAbove _ i]
  simp

lemma degree_deleteCoord {m : ℕ} (i : Fin (m + 1)) (u : Fin (m + 1) →₀ ℕ) :
    u i + (deleteCoord i u).degree = u.degree := by
  have := degree_insertCoord i (u i) (deleteCoord i u)
  rw [insertCoord_deleteCoord] at this
  exact this.symm

lemma toLex_insertCoord_lt_iff {m : ℕ} (i : Fin (m + 1)) (a : ℕ) (w₁ w₂ : Fin m →₀ ℕ) :
    toLex (insertCoord i a w₁) < toLex (insertCoord i a w₂) ↔ toLex w₁ < toLex w₂ := by
  rw [lex_lt_iff, lex_lt_iff]
  constructor
  · rintro ⟨k, hkeq, hklt⟩
    have hki : k ≠ i := by
      rintro rfl
      simp at hklt
    obtain ⟨j, rfl⟩ := Fin.exists_succAbove_eq hki
    refine ⟨j, fun r hr => ?_, ?_⟩
    · have := hkeq (i.succAbove r) (Fin.succAbove_lt_succAbove_iff.mpr hr)
      simpa using this
    · simpa using hklt
  · rintro ⟨j, hjeq, hjlt⟩
    refine ⟨i.succAbove j, fun k hk => ?_, ?_⟩
    · by_cases hki : k = i
      · subst hki; simp
      · obtain ⟨r, rfl⟩ := Fin.exists_succAbove_eq hki
        simp [hjeq r (Fin.succAbove_lt_succAbove_iff.mp hk)]
    · simpa using hjlt

lemma insertCoord_add_single_same {m : ℕ} (i : Fin (m + 1)) (a : ℕ) (w : Fin m →₀ ℕ) :
    insertCoord i a w + Finsupp.single i 1 = insertCoord i (a + 1) w := by
  ext k
  by_cases hki : k = i
  · rw [hki]; simp
  · obtain ⟨j, rfl⟩ := Fin.exists_succAbove_eq hki
    simp

lemma insertCoord_add_single_succAbove {m : ℕ} (i : Fin (m + 1)) (a : ℕ) (w : Fin m →₀ ℕ)
    (j : Fin m) :
    insertCoord i a w + Finsupp.single (i.succAbove j) 1 =
      insertCoord i a (w + Finsupp.single j 1) := by
  ext k
  by_cases hki : k = i
  · rw [hki]; simp
  · obtain ⟨r, rfl⟩ := Fin.exists_succAbove_eq hki
    by_cases hrj : j = r
    · subst hrj; simp
    · have hne : i.succAbove j ≠ i.succAbove r := fun h => hrj (Fin.succAbove_right_injective h)
      simp [hne, hrj]

/-- Drop coordinate `i` from a bound vector `D`. -/
def delBound {m : ℕ} (D : Fin (m + 1) → ℕ) (i : Fin (m + 1)) : Fin m → ℕ :=
  fun j => D (i.succAbove j)

lemma delBound_mono {m : ℕ} {D : Fin (m + 1) → ℕ} (hD : Monotone D) (i : Fin (m + 1)) :
    Monotone (delBound D i) :=
  fun _ _ h => hD (Fin.succAbove_le_succAbove_iff.mpr h)

lemma delBound_pos {m : ℕ} {D : Fin (m + 1) → ℕ} (hD : ∀ k, 1 ≤ D k) (i : Fin (m + 1)) :
    ∀ j, 1 ≤ delBound D i j :=
  fun j => hD (i.succAbove j)

lemma insertCoord_mem_monBox_iff {m e : ℕ} {D : Fin (m + 1) → ℕ} {i : Fin (m + 1)}
    {a : ℕ} {w : Fin m →₀ ℕ} :
    insertCoord i a w ∈ monBox D e ↔
      a ≤ e ∧ a < D i ∧ w ∈ monBox (delBound D i) (e - a) := by
  rw [mem_monBox, mem_monBox, degree_insertCoord]
  constructor
  · rintro ⟨hdeg, hlt⟩
    refine ⟨by omega, by simpa using hlt i, by omega, fun j => ?_⟩
    simpa [delBound] using hlt (i.succAbove j)
  · rintro ⟨hale, haD, hdeg, hlt⟩
    refine ⟨by omega, fun k => ?_⟩
    by_cases hki : k = i
    · rw [hki]; simpa using haD
    · obtain ⟨j, rfl⟩ := Fin.exists_succAbove_eq hki
      simpa [delBound] using hlt j

/-- The `a`-th slice of `M` in coordinate `i`. -/
noncomputable def slice {m : ℕ} (i : Fin (m + 1)) (a : ℕ) (M : Finset (Fin (m + 1) →₀ ℕ)) :
    Finset (Fin m →₀ ℕ) :=
  (M.filter (fun u => u i = a)).image (deleteCoord i)

lemma mem_slice {m : ℕ} {i : Fin (m + 1)} {a : ℕ} {M : Finset (Fin (m + 1) →₀ ℕ)}
    {w : Fin m →₀ ℕ} :
    w ∈ slice i a M ↔ insertCoord i a w ∈ M := by
  simp only [slice, mem_image, mem_filter]
  constructor
  · rintro ⟨u, ⟨hu, rfl⟩, rfl⟩
    rwa [insertCoord_deleteCoord]
  · intro h
    exact ⟨insertCoord i a w, ⟨h, insertCoord_apply_same i a w⟩, deleteCoord_insertCoord i a w⟩

lemma slice_subset_monBox {m e : ℕ} {D : Fin (m + 1) → ℕ} {i : Fin (m + 1)} {a : ℕ}
    {M : Finset (Fin (m + 1) →₀ ℕ)} (hM : M ⊆ monBox D e) :
    slice i a M ⊆ monBox (delBound D i) (e - a) := by
  intro w hw
  rw [mem_slice] at hw
  exact (insertCoord_mem_monBox_iff.mp (hM hw)).2.2

lemma slice_empty_of_ge_bound {m e : ℕ} {D : Fin (m + 1) → ℕ} {i : Fin (m + 1)} {a : ℕ}
    {M : Finset (Fin (m + 1) →₀ ℕ)} (hM : M ⊆ monBox D e) (ha : D i ≤ a) :
    slice i a M = ∅ := by
  rw [Finset.eq_empty_iff_forall_notMem]
  intro w hw
  rw [mem_slice] at hw
  have := (insertCoord_mem_monBox_iff.mp (hM hw)).2.1
  omega

lemma card_eq_sum_card_slice {m e : ℕ} (i : Fin (m + 1)) {D : Fin (m + 1) → ℕ}
    {M : Finset (Fin (m + 1) →₀ ℕ)} (hM : M ⊆ monBox D e) :
    M.card = ∑ a ∈ Finset.range (e + 1), (slice i a M).card := by
  have hdisj : M = (Finset.range (e + 1)).biUnion (fun a => M.filter (fun u => u i = a)) := by
    ext u
    simp only [mem_biUnion, mem_range, mem_filter]
    constructor
    · intro hu
      refine ⟨u i, ?_, hu, rfl⟩
      have hdeg := (mem_monBox.mp (hM hu)).1
      have hle : u i ≤ u.degree := by
        rw [Finsupp.degree_eq_sum]
        exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
      omega
    · rintro ⟨_, _, hu, _⟩; exact hu
  conv_lhs => rw [hdisj]
  rw [Finset.card_biUnion]
  · refine Finset.sum_congr rfl fun a _ => ?_
    rw [slice, Finset.card_image_of_injOn]
    intro u₁ hu₁ u₂ hu₂ heq
    simp only [mem_coe, mem_filter] at hu₁ hu₂
    rw [← insertCoord_deleteCoord i u₁, ← insertCoord_deleteCoord i u₂, hu₁.2, hu₂.2, heq]
  · intro a _ b _ hab
    dsimp only [Function.onFun]
    rw [Finset.disjoint_left]
    intro u hu₁ hu₂
    simp only [mem_filter] at hu₁ hu₂
    exact hab (hu₁.2.symm.trans hu₂.2)

lemma slice_shadowBox {m e : ℕ} {D : Fin (m + 1) → ℕ} (i : Fin (m + 1)) (a : ℕ)
    {M : Finset (Fin (m + 1) →₀ ℕ)} (hM : M ⊆ monBox D e) :
    slice i a (shadowBox D M) =
      if a < D i then
        shadowBox (delBound D i) (slice i a M) ∪ (if 0 < a then slice i (a - 1) M else ∅)
      else ∅ := by
  by_cases haD : a < D i
  · rw [if_pos haD]
    ext w
    simp only [mem_slice, mem_shadowBox, mem_union]
    constructor
    · rintro ⟨⟨u, hu, k, hk⟩, hlt⟩
      have hlt' : ∀ j : Fin m, w j < delBound D i j := fun j => by
        simpa [delBound] using hlt (i.succAbove j)
      by_cases hki : k = i
      · rw [hki] at hk
        right
        have hui : u i + 1 = a := by
          have := congrArg (fun f : Fin (m + 1) →₀ ℕ => f i) hk
          simpa using this
        have ha : 0 < a := by omega
        rw [if_pos ha, mem_slice]
        have hu_eq : insertCoord i (a - 1) w = u := by
          ext r
          by_cases hri : r = i
          · rw [hri]; simp; omega
          · obtain ⟨j, rfl⟩ := Fin.exists_succAbove_eq hri
            have := congrArg (fun f : Fin (m + 1) →₀ ℕ => f (i.succAbove j)) hk
            simpa using this.symm
        rwa [hu_eq]
      · obtain ⟨j, rfl⟩ := Fin.exists_succAbove_eq hki
        left
        have hui : u i = a := by
          have := congrArg (fun f : Fin (m + 1) →₀ ℕ => f i) hk
          simpa [Fin.succAbove_ne i j] using this
        refine ⟨⟨deleteCoord i u, ?_, j, ?_⟩, hlt'⟩
        · rw [← hui, insertCoord_deleteCoord]; exact hu
        · ext r
          have := congrArg (fun f : Fin (m + 1) →₀ ℕ => f (i.succAbove r)) hk
          by_cases hrj : j = r
          · subst hrj; simpa using this
          · have hne : i.succAbove j ≠ i.succAbove r :=
              fun h => hrj (Fin.succAbove_right_injective h)
            simpa [hne, hrj] using this
    · rintro (⟨⟨u', hu', j, rfl⟩, hlt'⟩ | hw)
      · refine ⟨⟨insertCoord i a u', hu', i.succAbove j,
          insertCoord_add_single_succAbove i a u' j⟩, fun k => ?_⟩
        by_cases hki : k = i
        · rw [hki]; simpa using haD
        · obtain ⟨r, rfl⟩ := Fin.exists_succAbove_eq hki
          simpa [delBound] using hlt' r
      · split_ifs at hw with ha
        · rw [mem_slice] at hw
          have hbox := (mem_monBox.mp (hM hw)).2
          refine ⟨⟨insertCoord i (a - 1) w, hw, i, ?_⟩, fun k => ?_⟩
          · rw [insertCoord_add_single_same, Nat.sub_add_cancel ha]
          · by_cases hki : k = i
            · rw [hki]; simpa using haD
            · obtain ⟨r, rfl⟩ := Fin.exists_succAbove_eq hki
              simpa using hbox (i.succAbove r)
        · simp at hw
  · rw [if_neg haD, Finset.eq_empty_iff_forall_notMem]
    intro w hw
    rw [mem_slice, mem_shadowBox] at hw
    have := hw.2 i
    simp at this
    omega

/-- `M` is `i`-compressed inside `monBox D e`. -/
def IsCompressedBox {m : ℕ} (D : Fin (m + 1) → ℕ) (i : Fin (m + 1)) (e : ℕ)
    (M : Finset (Fin (m + 1) →₀ ℕ)) : Prop :=
  ∀ u ∈ monBox D e, ∀ v ∈ M, u i = v i → toLex v < toLex u → u ∈ M

/-- Replace every `i`-slice of `M` by the lex-initial segment of the same cardinality in the box. -/
noncomputable def compressBox {m : ℕ} (D : Fin (m + 1) → ℕ) (i : Fin (m + 1)) (e : ℕ)
    (M : Finset (Fin (m + 1) →₀ ℕ)) : Finset (Fin (m + 1) →₀ ℕ) :=
  (Finset.range (min (e + 1) (D i))).biUnion
    (fun a => (lexSegBox (delBound D i) (e - a) (slice i a M).card).image (insertCoord i a))

lemma mem_compressBox {m : ℕ} {D : Fin (m + 1) → ℕ} {i : Fin (m + 1)} {e : ℕ}
    {M : Finset (Fin (m + 1) →₀ ℕ)} {u : Fin (m + 1) →₀ ℕ} :
    u ∈ compressBox D i e M ↔
      u i ≤ e ∧ u i < D i ∧
        deleteCoord i u ∈ lexSegBox (delBound D i) (e - u i) (slice i (u i) M).card := by
  simp only [compressBox, mem_biUnion, mem_range, mem_image]
  constructor
  · rintro ⟨a, ha, w, hw, rfl⟩
    rw [insertCoord_apply_same, deleteCoord_insertCoord]
    exact ⟨by omega, by omega, hw⟩
  · rintro ⟨hle, hlt, hw⟩
    exact ⟨u i, by omega, deleteCoord i u, hw, insertCoord_deleteCoord i u⟩

lemma slice_compressBox {m : ℕ} (D : Fin (m + 1) → ℕ) (i : Fin (m + 1)) (e a : ℕ)
    (M : Finset (Fin (m + 1) →₀ ℕ)) (ha : a ≤ e) (haD : a < D i) :
    slice i a (compressBox D i e M) = lexSegBox (delBound D i) (e - a) (slice i a M).card := by
  ext w
  rw [mem_slice, mem_compressBox, insertCoord_apply_same, deleteCoord_insertCoord]
  exact ⟨fun h => h.2.2, fun h => ⟨ha, haD, h⟩⟩

lemma compressBox_subset_monBox {m : ℕ} (D : Fin (m + 1) → ℕ) (i : Fin (m + 1)) (e : ℕ)
    (M : Finset (Fin (m + 1) →₀ ℕ)) :
    compressBox D i e M ⊆ monBox D e := by
  intro u hu
  rw [mem_compressBox] at hu
  have hw := lexSegBox_subset_monBox (delBound D i) (e - u i) _ hu.2.2
  rw [← insertCoord_deleteCoord i u, insertCoord_mem_monBox_iff]
  exact ⟨hu.1, hu.2.1, hw⟩

lemma card_compressBox {m : ℕ} (D : Fin (m + 1) → ℕ) (i : Fin (m + 1)) (e : ℕ)
    {M : Finset (Fin (m + 1) →₀ ℕ)} (hM : M ⊆ monBox D e) :
    (compressBox D i e M).card = M.card := by
  rw [card_eq_sum_card_slice i (compressBox_subset_monBox D i e M), card_eq_sum_card_slice i hM]
  refine Finset.sum_congr rfl fun a ha => ?_
  rw [mem_range] at ha
  by_cases haD : a < D i
  · rw [slice_compressBox D i e a M (by omega) haD]
    exact card_lexSegBox (Finset.card_le_card (slice_subset_monBox hM))
  · push Not at haD
    rw [slice_empty_of_ge_bound (compressBox_subset_monBox D i e M) haD,
      slice_empty_of_ge_bound hM haD]

/-- Lex rank of a monomial in `monBox D e`. -/
noncomputable def lexRankBox {n : ℕ} (D : Fin n → ℕ) (e : ℕ) (u : Fin n →₀ ℕ) : ℕ :=
  ((monBox D e).filter (fun w => toLex u < toLex w)).card

lemma lexRankBox_lt_of_lt {n e : ℕ} {D : Fin n → ℕ} {u v : Fin n →₀ ℕ} (hu : u ∈ monBox D e)
    (hlt : toLex v < toLex u) :
    lexRankBox D e u < lexRankBox D e v := by
  apply Finset.card_lt_card
  rw [Finset.ssubset_iff_of_subset]
  · exact ⟨u, Finset.mem_filter.mpr ⟨hu, hlt⟩, by simp⟩
  · intro w hw
    simp only [mem_filter] at hw ⊢
    exact ⟨hw.1, lt_trans hlt hw.2⟩

/-- Total lex rank sum of a set of monomials in `monBox D e`. -/
noncomputable def lexRankSumBox {n : ℕ} (D : Fin n → ℕ) (e : ℕ) (M : Finset (Fin n →₀ ℕ)) : ℕ :=
  ∑ u ∈ M, lexRankBox D e u

lemma lexRankSumBox_slice_le {m e : ℕ} (D : Fin (m + 1) → ℕ) (i : Fin (m + 1)) (a : ℕ)
    (ha : a ≤ e) (haD : a < D i)
    {S : Finset (Fin m →₀ ℕ)} (hS : S ⊆ monBox (delBound D i) (e - a)) :
    lexRankSumBox D e ((lexSegBox (delBound D i) (e - a) S.card).image (insertCoord i a)) ≤
      lexRankSumBox D e (S.image (insertCoord i a)) ∧
    (lexSegBox (delBound D i) (e - a) S.card ≠ S →
      lexRankSumBox D e ((lexSegBox (delBound D i) (e - a) S.card).image (insertCoord i a)) <
        lexRankSumBox D e (S.image (insertCoord i a))) := by
  set D' := delBound D i
  set L := lexSegBox D' (e - a) S.card
  have hLcard : L.card = S.card := card_lexSegBox (Finset.card_le_card hS)
  have hLsub : L ⊆ monBox D' (e - a) := lexSegBox_subset_monBox D' (e - a) S.card
  have hLlex : IsLexBox D' (e - a) L := isLexBox_lexSegBox D' (e - a) S.card
  have hEq : ∀ A : Finset (Fin m →₀ ℕ),
      lexRankSumBox D e (A.image (insertCoord i a)) =
        ∑ w ∈ A, lexRankBox D e (insertCoord i a w) := fun A => by
    rw [lexRankSumBox, Finset.sum_image (fun x _ y _ h => insertCoord_injective i a h)]
  rw [hEq L, hEq S]
  have hsplit : ∀ A B : Finset (Fin m →₀ ℕ),
      ∑ w ∈ A, lexRankBox D e (insertCoord i a w) =
        (∑ w ∈ A ∩ B, lexRankBox D e (insertCoord i a w)) +
        (∑ w ∈ A \ B, lexRankBox D e (insertCoord i a w)) := fun A B => by
    have hunion : A ∩ B ∪ A \ B = A := by ext x; simp; tauto
    rw [← Finset.sum_union (Finset.disjoint_left.mpr fun x h1 h2 =>
      (Finset.mem_sdiff.mp h2).2 (Finset.mem_inter.mp h1).2), hunion]
  rw [hsplit L S, hsplit S L, Finset.inter_comm S L]
  have hdiff_card : (L \ S).card = (S \ L).card := by
    have h1 := Finset.card_sdiff_add_card_inter L S
    have h2 := Finset.card_sdiff_add_card_inter S L
    rw [Finset.inter_comm S L] at h2
    omega
  have hpt : ∀ x ∈ L \ S, ∀ y ∈ S \ L,
      lexRankBox D e (insertCoord i a x) < lexRankBox D e (insertCoord i a y) := by
    intro x hx y hy
    rw [mem_sdiff] at hx hy
    have hlt : toLex y < toLex x := by
      rcases lt_trichotomy (toLex y) (toLex x) with h | heq | h
      · exact h
      · exfalso
        have hyx : y = x := heq
        exact hy.2 (hyx ▸ hx.1)
      · exfalso; exact hy.2 (hLlex.2 y (hS hy.1) x hx.1 h)
    apply lexRankBox_lt_of_lt
    · rw [insertCoord_mem_monBox_iff]; exact ⟨ha, haD, hLsub hx.1⟩
    · exact (toLex_insertCoord_lt_iff i a y x).mpr hlt
  have hlt_or_eq : (L \ S = ∅ ∧ S \ L = ∅) ∨
      ∑ w ∈ L \ S, lexRankBox D e (insertCoord i a w) <
        ∑ w ∈ S \ L, lexRankBox D e (insertCoord i a w) := by
    by_cases hne : (L \ S).Nonempty
    · right
      have hne2 : (S \ L).Nonempty := Finset.card_pos.mp (hdiff_card ▸ hne.card_pos)
      obtain ⟨x₀, hx₀, hx₀_max⟩ :=
        Finset.exists_max_image (L \ S) (fun w => lexRankBox D e (insertCoord i a w)) hne
      obtain ⟨y₀, hy₀, hy₀_min⟩ :=
        Finset.exists_min_image (S \ L) (fun w => lexRankBox D e (insertCoord i a w)) hne2
      have h1 : ∑ w ∈ L \ S, lexRankBox D e (insertCoord i a w) ≤
          (L \ S).card * lexRankBox D e (insertCoord i a x₀) := by
        simpa using Finset.sum_le_card_nsmul (L \ S) _ _ (fun w hw => hx₀_max w hw)
      have h2 : (S \ L).card * lexRankBox D e (insertCoord i a y₀) ≤
          ∑ w ∈ S \ L, lexRankBox D e (insertCoord i a w) := by
        simpa using Finset.card_nsmul_le_sum (S \ L) _ _ (fun w hw => hy₀_min w hw)
      have h3 := hpt x₀ hx₀ y₀ hy₀
      have hpos : 0 < (L \ S).card := hne.card_pos
      rw [hdiff_card] at h1 hpos
      nlinarith
    · left
      rw [Finset.not_nonempty_iff_eq_empty] at hne
      refine ⟨hne, Finset.card_eq_zero.mp ?_⟩
      rw [← hdiff_card, hne, Finset.card_empty]
  constructor
  · rcases hlt_or_eq with ⟨h1, h2⟩ | hlt
    · simp [h1, h2]
    · omega
  · intro hneq
    rcases hlt_or_eq with ⟨h1, h2⟩ | hlt
    · exfalso
      apply hneq
      exact Finset.Subset.antisymm (Finset.sdiff_eq_empty_iff_subset.mp h1)
        (Finset.sdiff_eq_empty_iff_subset.mp h2)
    · omega

lemma lexRankSumBox_compressBox_lt {m e : ℕ} {D : Fin (m + 1) → ℕ} (i : Fin (m + 1))
    {M : Finset (Fin (m + 1) →₀ ℕ)} (hM : M ⊆ monBox D e) (hnc : ¬ IsCompressedBox D i e M) :
    lexRankSumBox D e (compressBox D i e M) < lexRankSumBox D e M := by
  have hdecomp : ∀ A : Finset (Fin (m + 1) →₀ ℕ), A ⊆ monBox D e →
      lexRankSumBox D e A =
        ∑ a ∈ Finset.range (min (e + 1) (D i)),
          lexRankSumBox D e ((slice i a A).image (insertCoord i a)) := by
    intro A hA
    have hEq : A = (Finset.range (min (e + 1) (D i))).biUnion
        (fun a => (slice i a A).image (insertCoord i a)) := by
      ext u
      simp only [mem_biUnion, mem_range, mem_image, mem_slice]
      constructor
      · intro hu
        obtain ⟨hdeg, hbox⟩ := mem_monBox.mp (hA hu)
        have hle : u i ≤ u.degree := by
          rw [Finsupp.degree_eq_sum]
          exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
        have huiD := hbox i
        exact ⟨u i, by omega, deleteCoord i u, by rwa [insertCoord_deleteCoord],
          insertCoord_deleteCoord i u⟩
      · rintro ⟨a, _, w, hw, rfl⟩; exact hw
    conv_lhs => rw [lexRankSumBox, hEq]
    rw [Finset.sum_biUnion]
    · rfl
    · intro a _ b _ hab
      dsimp only [Function.onFun]
      rw [Finset.disjoint_left]
      intro u hu₁ hu₂
      simp only [mem_image] at hu₁ hu₂
      obtain ⟨w₁, _, rfl⟩ := hu₁
      obtain ⟨w₂, _, heq⟩ := hu₂
      have := congrArg (fun f : Fin (m + 1) →₀ ℕ => f i) heq
      simp at this
      exact hab this.symm
  rw [hdecomp (compressBox D i e M) (compressBox_subset_monBox D i e M), hdecomp M hM]
  have hex : ∃ a ∈ Finset.range (min (e + 1) (D i)),
      lexSegBox (delBound D i) (e - a) (slice i a M).card ≠ slice i a M := by
    unfold IsCompressedBox at hnc
    push Not at hnc
    obtain ⟨u, hu, v, hv, huv_i, hlt, huM⟩ := hnc
    obtain ⟨hdeg_v, hbox_v⟩ := mem_monBox.mp (hM hv)
    have ha : v i ∈ Finset.range (min (e + 1) (D i)) := by
      rw [mem_range]
      have hle : v i ≤ v.degree := by
        rw [Finsupp.degree_eq_sum]
        exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
      have hvD := hbox_v i
      omega
    refine ⟨v i, ha, fun heq => huM ?_⟩
    have hlex : IsLexBox (delBound D i) (e - v i) (slice i (v i) M) :=
      heq ▸ isLexBox_lexSegBox (delBound D i) (e - v i) _
    have hdv : deleteCoord i v ∈ slice i (v i) M := by
      rw [mem_slice, insertCoord_deleteCoord]; exact hv
    have hdu_box : deleteCoord i u ∈ monBox (delBound D i) (e - v i) := by
      have hu' : insertCoord i (v i) (deleteCoord i u) ∈ monBox D e := by
        rw [← huv_i, insertCoord_deleteCoord]; exact hu
      exact (insertCoord_mem_monBox_iff.mp hu').2.2
    have hlt_d : toLex (deleteCoord i v) < toLex (deleteCoord i u) := by
      rw [← toLex_insertCoord_lt_iff i (v i), insertCoord_deleteCoord, ← huv_i,
        insertCoord_deleteCoord]
      exact hlt
    have hdu_mem := hlex.2 (deleteCoord i u) hdu_box (deleteCoord i v) hdv hlt_d
    rw [mem_slice, ← huv_i, insertCoord_deleteCoord] at hdu_mem
    exact hdu_mem
  apply Finset.sum_lt_sum
  · intro a ha
    rw [mem_range] at ha
    rw [slice_compressBox D i e a M (by omega) (by omega)]
    exact (lexRankSumBox_slice_le D i a (by omega) (by omega) (slice_subset_monBox hM)).1
  · obtain ⟨a, ha, hne⟩ := hex
    rw [mem_range] at ha
    refine ⟨a, Finset.mem_range.mpr ha, ?_⟩
    rw [slice_compressBox D i e a M (by omega) (by omega)]
    exact (lexRankSumBox_slice_le D i a (by omega) (by omega) (slice_subset_monBox hM)).2 hne

/- Part 4: Clements-Lindström Shadow Inequality -/

lemma clements_lindstrom_shadow_two (D : Fin 2 → ℕ) (hD_pos : ∀ i, 1 ≤ D i)
    (hD_mono : Monotone D) (e : ℕ) (M : Finset (Fin 2 →₀ ℕ)) (hM : M ⊆ monBox D e) :
    (shadowBox D (lexSegBox D e M.card)).card ≤ (shadowBox D M).card := by
  have hD01 : D 0 ≤ D 1 := hD_mono (by decide)
  by_cases hD0_one : D 0 = 1
  · have hlex : IsLexBox D e M := by
      refine ⟨hM, fun u hu v hv hlt => ?_⟩
      obtain ⟨hdu, hbu⟩ := mem_monBox.mp hu
      obtain ⟨hdv, hbv⟩ := mem_monBox.mp (hM hv)
      rw [Finsupp.degree_eq_sum, Fin.sum_univ_two] at hdu hdv
      have hu0 := hbu 0
      have hv0 := hbv 0
      have huv : u = v := Finsupp.ext fun r => by
        fin_cases r
        · change u 0 = v 0; omega
        · change u 1 = v 1; omega
      subst huv
      exact absurd hlt (lt_irrefl _)
    rw [← hlex.eq_lexSegBox]
  · have hD0_ge2 : 2 ≤ D 0 := by have := hD_pos 0; omega
    by_cases hne : M.Nonempty
    · set L := lexSegBox D e M.card
      have hLlex : IsLexBox D e L := isLexBox_lexSegBox D e M.card
      have hLcard : L.card = M.card := card_lexSegBox (Finset.card_le_card hM)
      have hLne : L.Nonempty := Finset.card_pos.mp (hLcard ▸ hne.card_pos)
      by_cases hfull : M = monBox D e
      · have hlex : IsLexBox D e M := ⟨hM, fun u hu _ _ _ => hfull ▸ hu⟩
        rw [show L = M from hlex.eq_lexSegBox.symm]
      · by_cases hsmall : e + 1 < D 0
        · -- Unbounded regime: every degree ≤ e+1 monomial fits inside D
          have hbox_eq : ∀ A : Finset (Fin 2 →₀ ℕ), A ⊆ monBox D e → shadowBox D A = shadow A := by
            intro A hA
            ext v
            simp only [mem_shadowBox, mem_shadow, and_iff_left_iff_imp]
            rintro ⟨u, hu, i, rfl⟩ r
            have hdeg := (mem_monBox.mp (hA hu)).1
            have hle : (u + Finsupp.single i 1 : Fin 2 →₀ ℕ) r ≤ (u + Finsupp.single i 1).degree := by
              rw [Finsupp.degree_eq_sum]
              exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ r)
            rw [map_add, Finsupp.degree_single, hdeg] at hle
            have hD : D 0 ≤ D r := hD_mono (Fin.zero_le r)
            omega
          rw [hbox_eq L hLlex.1, hbox_eq M hM]
          -- Upper bound (shadow L).card ≤ M.card + 1, lower bound M.card + 1 ≤ (shadow M).card
          obtain ⟨u_min, hu_min, hu_min_le⟩ := Finset.exists_min_image L toLex hLne
          have hsubL : shadow L ⊆
              L.image (· + Finsupp.single 0 1) ∪ {u_min + Finsupp.single 1 1} := by
            intro v hv
            rw [mem_shadow] at hv
            obtain ⟨u, hu, i, rfl⟩ := hv
            fin_cases i
            · exact Finset.mem_union_left _ (Finset.mem_image_of_mem _ hu)
            · by_cases heq : u = u_min
              · subst heq; exact Finset.mem_union_right _ (Finset.mem_singleton_self _)
              · apply Finset.mem_union_left
                rw [mem_image]
                have hlt_u : toLex u_min < toLex u :=
                  lt_of_le_of_ne (hu_min_le u hu) (fun h => heq h.symm)
                have hdu := (mem_monBox.mp (hLlex.1 hu)).1
                have hdm := (mem_monBox.mp (hLlex.1 hu_min)).1
                rw [Finsupp.degree_eq_sum, Fin.sum_univ_two] at hdu hdm
                have hu0_gt : u_min 0 < u 0 := by
                  rw [lex_lt_iff] at hlt_u
                  obtain ⟨j, hjeq, hjlt⟩ := hlt_u
                  fin_cases j
                  · exact hjlt
                  · have h0 := hjeq 0 (by decide)
                    have hjlt' : u_min 1 < u 1 := hjlt
                    omega
                set w := (u - Finsupp.single 0 1) + Finsupp.single 1 1
                have hw0 : w 0 = u 0 - 1 := by simp [w]
                have hw1 : w 1 = u 1 + 1 := by simp [w]
                have hw_box : w ∈ monBox D e := by
                  rw [mem_monBox, Finsupp.degree_eq_sum, Fin.sum_univ_two, hw0, hw1]
                  refine ⟨by omega, fun r => ?_⟩
                  fin_cases r
                  · change w 0 < D 0; omega
                  · change w 1 < D 1; omega
                have hw_ge : toLex u_min ≤ toLex w := by
                  by_cases heq0 : u_min 0 = u 0 - 1
                  · have hweq : w = u_min := by
                      ext r; fin_cases r
                      · change w 0 = u_min 0; omega
                      · change w 1 = u_min 1; omega
                    rw [hweq]
                  · apply le_of_lt
                    rw [lex_lt_iff]
                    exact ⟨0, fun j hj => absurd hj (Fin.not_lt_zero j), by omega⟩
                have hw_mem : w ∈ L := by
                  rcases eq_or_lt_of_le hw_ge with h | h
                  · have : u_min = w := h; rwa [← this]
                  · exact hLlex.2 w hw_box u_min hu_min h
                refine ⟨w, hw_mem, ?_⟩
                ext r; fin_cases r
                · simp [hw0]; omega
                · simp [hw1]
          have hcardL : (shadow L).card ≤ M.card + 1 := by
            calc (shadow L).card
                ≤ (L.image (· + Finsupp.single 0 1) ∪ {u_min + Finsupp.single 1 1}).card :=
                  Finset.card_le_card hsubL
              _ ≤ (L.image (· + Finsupp.single 0 1)).card + 1 := Finset.card_union_le _ _
              _ ≤ L.card + 1 := by
                  linarith [Finset.card_image_le (s := L) (f := (· + Finsupp.single 0 1))]
              _ = M.card + 1 := by rw [hLcard]
          obtain ⟨v_min, hv_min, hv_min_le⟩ := Finset.exists_min_image M toLex hne
          have hsubM : insert (v_min + Finsupp.single 1 1) (M.image (· + Finsupp.single 0 1)) ⊆
              shadow M := by
            intro x hx
            rw [mem_insert, mem_image] at hx
            rw [mem_shadow]
            rcases hx with rfl | ⟨u, hu, rfl⟩
            · exact ⟨v_min, hv_min, 1, rfl⟩
            · exact ⟨u, hu, 0, rfl⟩
          have hnotmem : v_min + Finsupp.single 1 1 ∉ M.image (· + Finsupp.single 0 1) := by
            rw [mem_image]
            rintro ⟨w, hw, heq⟩
            have h0 := congrArg (fun f : Fin 2 →₀ ℕ => f 0) heq
            simp only [Finsupp.coe_add, Pi.add_apply, Finsupp.single_eq_same,
              Finsupp.single_eq_of_ne (by decide : (0 : Fin 2) ≠ 1)] at h0
            have hlt_w : toLex w < toLex v_min := by
              rw [lex_lt_iff]
              exact ⟨0, fun j hj => absurd hj (Fin.not_lt_zero j), by omega⟩
            exact not_lt_of_ge (hv_min_le w hw) hlt_w
          have hcardM : M.card + 1 ≤ (shadow M).card := by
            calc M.card + 1
                = (M.image (· + Finsupp.single 0 1)).card + 1 := by
                  rw [Finset.card_image_of_injective _ (add_left_injective _)]
              _ = (insert (v_min + Finsupp.single 1 1) (M.image (· + Finsupp.single 0 1))).card := by
                  rw [Finset.card_insert_of_notMem hnotmem]
              _ ≤ (shadow M).card := Finset.card_le_card hsubM
          omega
        · -- Bounded regime `D 0 ≤ e + 1` and `M ⊊ monBox D e`:
          -- (shadowBox D L).card ≤ M.card ≤ (shadowBox D M).card
          push Not at hsmall
          -- Lower bound: pick gap g ∈ monBox D e \ M
          have hgap_ne : (monBox D e \ M).Nonempty := by
            rw [Finset.nonempty_iff_ne_empty]
            intro hemp
            exact hfull (Finset.Subset.antisymm hM (Finset.sdiff_eq_empty_iff_subset.mp hemp))
          obtain ⟨g, hg⟩ := hgap_ne
          rw [mem_sdiff] at hg
          obtain ⟨hg_box, hg_nM⟩ := hg
          obtain ⟨hg_deg, hg_lt⟩ := mem_monBox.mp hg_box
          rw [Finsupp.degree_eq_sum, Fin.sum_univ_two] at hg_deg
          let f : (Fin 2 →₀ ℕ) → (Fin 2 →₀ ℕ) := fun u =>
            if g 0 < u 0 then u + Finsupp.single 1 1 else u + Finsupp.single 0 1
          have hf_mem : ∀ u ∈ M, f u ∈ shadowBox D M := by
            intro u hu
            obtain ⟨hu_deg, hu_lt⟩ := mem_monBox.mp (hM hu)
            rw [Finsupp.degree_eq_sum, Fin.sum_univ_two] at hu_deg
            have hne_g0 : u 0 ≠ g 0 := by
              intro h0
              have hug : u = g := Finsupp.ext fun r => by
                fin_cases r
                · change u 0 = g 0; exact h0
                · change u 1 = g 1; omega
              exact hg_nM (hug ▸ hu)
            rw [mem_shadowBox]
            by_cases hgt : g 0 < u 0
            · simp only [f, if_pos hgt]
              refine ⟨⟨u, hu, 1, rfl⟩, fun r => ?_⟩
              fin_cases r
              · change (u + Finsupp.single 1 1 : Fin 2 →₀ ℕ) 0 < D 0
                have := hu_lt 0; simp; omega
              · change (u + Finsupp.single 1 1 : Fin 2 →₀ ℕ) 1 < D 1
                have := hg_lt 1; simp; omega
            · simp only [f, if_neg hgt]
              refine ⟨⟨u, hu, 0, rfl⟩, fun r => ?_⟩
              fin_cases r
              · change (u + Finsupp.single 0 1 : Fin 2 →₀ ℕ) 0 < D 0
                have := hg_lt 0; simp; omega
              · change (u + Finsupp.single 0 1 : Fin 2 →₀ ℕ) 1 < D 1
                have := hu_lt 1; simp; omega
          have hf_inj : Set.InjOn f M := by
            intro u₁ hu₁ u₂ hu₂ heq
            have h0 := congrArg (fun x : Fin 2 →₀ ℕ => x 0) heq
            by_cases h1 : g 0 < u₁ 0 <;> by_cases h2 : g 0 < u₂ 0
            · simp only [f, if_pos h1, if_pos h2] at heq
              exact add_right_cancel heq
            · exfalso
              have hne2 : u₂ 0 ≠ g 0 := by
                intro h
                obtain ⟨hd2, _⟩ := mem_monBox.mp (hM hu₂)
                rw [Finsupp.degree_eq_sum, Fin.sum_univ_two] at hd2
                have : u₂ = g := Finsupp.ext fun r => by
                  fin_cases r
                  · change u₂ 0 = g 0; exact h
                  · change u₂ 1 = g 1; omega
                exact hg_nM (this ▸ hu₂)
              simp only [f, if_pos h1, if_neg h2, Finsupp.coe_add, Pi.add_apply,
                Finsupp.single_eq_same,
                Finsupp.single_eq_of_ne (by decide : (0 : Fin 2) ≠ 1)] at h0
              omega
            · exfalso
              have hne1 : u₁ 0 ≠ g 0 := by
                intro h
                obtain ⟨hd1, _⟩ := mem_monBox.mp (hM hu₁)
                rw [Finsupp.degree_eq_sum, Fin.sum_univ_two] at hd1
                have : u₁ = g := Finsupp.ext fun r => by
                  fin_cases r
                  · change u₁ 0 = g 0; exact h
                  · change u₁ 1 = g 1; omega
                exact hg_nM (this ▸ hu₁)
              simp only [f, if_neg h1, if_pos h2, Finsupp.coe_add, Pi.add_apply,
                Finsupp.single_eq_same,
                Finsupp.single_eq_of_ne (by decide : (0 : Fin 2) ≠ 1)] at h0
              omega
            · simp only [f, if_neg h1, if_neg h2] at heq
              exact add_right_cancel heq
          have hcardM : M.card ≤ (shadowBox D M).card := by
            calc M.card = (M.image f).card := (Finset.card_image_of_injOn hf_inj).symm
              _ ≤ (shadowBox D M).card := Finset.card_le_card (by
                  intro x hx
                  rw [mem_image] at hx
                  obtain ⟨u, hu, rfl⟩ := hx
                  exact hf_mem u hu)
          -- Upper bound: (shadowBox D L).card ≤ M.card
          obtain ⟨u_max, hu_max, hu_max_ge⟩ := Finset.exists_max_image L toLex hLne
          obtain ⟨u_min, hu_min, hu_min_le⟩ := Finset.exists_min_image L toLex hLne
          have hu_max0 : u_max 0 = D 0 - 1 := by
            obtain ⟨hdm, hbm⟩ := mem_monBox.mp (hLlex.1 hu_max)
            rw [Finsupp.degree_eq_sum, Fin.sum_univ_two] at hdm
            have hbm0 := hbm 0
            by_contra hne0
            have hu_max1_pos : 1 ≤ u_max 1 := by omega
            set w := (u_max - Finsupp.single 1 1) + Finsupp.single 0 1
            have hw0 : w 0 = u_max 0 + 1 := by simp [w]
            have hw1 : w 1 = u_max 1 - 1 := by simp [w]
            have hw_box : w ∈ monBox D e := by
              rw [mem_monBox, Finsupp.degree_eq_sum, Fin.sum_univ_two, hw0, hw1]
              refine ⟨by omega, fun r => ?_⟩
              fin_cases r
              · change w 0 < D 0; omega
              · change w 1 < D 1; have := hbm 1; omega
            have hlt : toLex u_max < toLex w := by
              rw [lex_lt_iff]
              exact ⟨0, fun j hj => absurd hj (Fin.not_lt_zero j), by omega⟩
            have hwL : w ∈ L := hLlex.2 w hw_box u_max hu_max hlt
            exact not_lt_of_ge (hu_max_ge w hwL) hlt
          have hsubL : shadowBox D L ⊆
              (L.erase u_max).image (· + Finsupp.single 0 1) ∪ {u_min + Finsupp.single 1 1} := by
            intro v hv
            rw [mem_shadowBox] at hv
            obtain ⟨⟨u, hu, i, rfl⟩, hv_lt⟩ := hv
            fin_cases i
            · apply Finset.mem_union_left
              apply Finset.mem_image_of_mem
              refine Finset.mem_erase.mpr ⟨?_, hu⟩
              rintro rfl
              have := hv_lt 0
              simp at this
              omega
            · by_cases heq : u = u_min
              · subst heq; exact Finset.mem_union_right _ (Finset.mem_singleton_self _)
              · apply Finset.mem_union_left
                rw [mem_image]
                have hlt_u : toLex u_min < toLex u :=
                  lt_of_le_of_ne (hu_min_le u hu) (fun h => heq h.symm)
                obtain ⟨hdu, hbu⟩ := mem_monBox.mp (hLlex.1 hu)
                obtain ⟨hdm, hbm⟩ := mem_monBox.mp (hLlex.1 hu_min)
                rw [Finsupp.degree_eq_sum, Fin.sum_univ_two] at hdu hdm
                have hu0_gt : u_min 0 < u 0 := by
                  rw [lex_lt_iff] at hlt_u
                  obtain ⟨j, hjeq, hjlt⟩ := hlt_u
                  fin_cases j
                  · exact hjlt
                  · have h0 := hjeq 0 (by decide)
                    have hjlt' : u_min 1 < u 1 := hjlt
                    omega
                set w := (u - Finsupp.single 0 1) + Finsupp.single 1 1
                have hw0 : w 0 = u 0 - 1 := by simp [w]
                have hw1 : w 1 = u 1 + 1 := by simp [w]
                have hw_box : w ∈ monBox D e := by
                  rw [mem_monBox, Finsupp.degree_eq_sum, Fin.sum_univ_two, hw0, hw1]
                  refine ⟨by omega, fun r => ?_⟩
                  fin_cases r
                  · change w 0 < D 0; have := hbu 0; omega
                  · change w 1 < D 1; have := hbm 1; omega
                have hw_ge : toLex u_min ≤ toLex w := by
                  by_cases heq0 : u_min 0 = u 0 - 1
                  · have hweq : w = u_min := by
                      ext r; fin_cases r
                      · change w 0 = u_min 0; omega
                      · change w 1 = u_min 1; omega
                    rw [hweq]
                  · apply le_of_lt
                    rw [lex_lt_iff]
                    exact ⟨0, fun j hj => absurd hj (Fin.not_lt_zero j), by omega⟩
                have hw_mem : w ∈ L := by
                  rcases eq_or_lt_of_le hw_ge with h | h
                  · have : u_min = w := h; rwa [← this]
                  · exact hLlex.2 w hw_box u_min hu_min h
                have hw_ne_max : w ≠ u_max := by
                  intro h
                  have hbu0 := hbu 0
                  have : w 0 = u_max 0 := congrArg (fun x : Fin 2 →₀ ℕ => x 0) h
                  omega
                refine ⟨w, Finset.mem_erase.mpr ⟨hw_ne_max, hw_mem⟩, ?_⟩
                ext r; fin_cases r
                · simp [hw0]; omega
                · simp [hw1]
          have hcardL : (shadowBox D L).card ≤ M.card := by
            calc (shadowBox D L).card
                ≤ ((L.erase u_max).image (· + Finsupp.single 0 1) ∪
                    {u_min + Finsupp.single 1 1}).card := Finset.card_le_card hsubL
              _ ≤ ((L.erase u_max).image (· + Finsupp.single 0 1)).card + 1 :=
                  Finset.card_union_le _ _
              _ ≤ (L.erase u_max).card + 1 := by
                  linarith [Finset.card_image_le (s := L.erase u_max) (f := (· + Finsupp.single 0 1))]
              _ = L.card := by
                  rw [Finset.card_erase_of_mem hu_max]
                  have := hLne.card_pos; omega
              _ = M.card := hLcard
          omega
    · rw [Finset.not_nonempty_iff_eq_empty] at hne
      subst hne
      simp [lexSegBox, shadowBox, shadow]

/-- Key lemma A for `n = m + 1 ≥ 3`: `1 ≤ u (Fin.last m)`. -/
lemma max_not_mem_last_pos_box {m e : ℕ} (hm : 2 ≤ m) {D : Fin (m + 1) → ℕ}
    (hD_pos : ∀ i, 1 ≤ D i) {M : Finset (Fin (m + 1) →₀ ℕ)} (hM : M ⊆ monBox D e)
    (hcomp : ∀ i : Fin (m + 1), IsCompressedBox D i e M)
    {u v : Fin (m + 1) →₀ ℕ} (hu : u ∈ monBox D e) (huM : u ∉ M)
    (hvM : v ∈ M) (hvu : toLex v < toLex u) :
    1 ≤ u (Fin.last m) := by
  have hne_coord : ∀ i : Fin (m + 1), u i ≠ v i := fun i heq =>
    huM (hcomp i u hu v hvM heq hvu)
  have hu0_gt : v 0 < u 0 := by
    rw [lex_lt_iff] at hvu
    obtain ⟨j, hjeq, hjlt⟩ := hvu
    by_cases hj0 : j = 0
    · subst hj0; exact hjlt
    · exfalso
      exact hne_coord 0 (hjeq 0 (Nat.pos_of_ne_zero (fun h => hj0 (Fin.ext h)))).symm
  by_contra h0
  have hu_last : u (Fin.last m) = 0 := by omega
  -- Step-by-step induction on `t = z (Fin.last m)`: move mass from `Fin.last m` into middle coords
  have hstep : ∀ t : ℕ, ∀ z ∈ M, z 0 = v 0 → z (Fin.last m) = t →
      (∃ z' ∈ M, z' 0 = v 0 ∧ z' (Fin.last m) = 0) ∨
      (∃ z₁ ∈ M, z₁ 0 = v 0 ∧ ∀ i : Fin (m + 1), i ≠ 0 → i ≠ Fin.last m → z₁ i = D i - 1) := by
    intro t
    induction t with
    | zero =>
      intro z hz hz0 hzt
      exact Or.inl ⟨z, hz, hz0, hzt⟩
    | succ t ih =>
      intro z hz hz0 hzt
      by_cases hfull : ∀ i : Fin (m + 1), i ≠ 0 → i ≠ Fin.last m → z i = D i - 1
      · exact Or.inr ⟨z, hz, hz0, hfull⟩
      · push Not at hfull
        obtain ⟨i, hi0, hilast, hzi_ne⟩ := hfull
        obtain ⟨hz_deg, hz_lt⟩ := mem_monBox.mp (hM hz)
        have hzi_lt : z i + 1 < D i := by have := hz_lt i; omega
        set z' : Fin (m + 1) →₀ ℕ := (z - Finsupp.single (Fin.last m) 1) + Finsupp.single i 1
        have hz'_box : z' ∈ monBox D e := by
          rw [mem_monBox]
          refine ⟨?_, fun k => ?_⟩
          · rw [map_add, Finsupp.degree_single]
            have := degree_sub_single (u := z) (s := Fin.last m) (by omega)
            omega
          · rcases eq_or_ne k (Fin.last m) with rfl | hkl
            · simp only [z', Finsupp.coe_add, Finsupp.coe_tsub, Pi.add_apply, Pi.sub_apply,
                Finsupp.single_eq_same, Finsupp.single_eq_of_ne hilast.symm]
              have := hz_lt (Fin.last m); omega
            · rcases eq_or_ne k i with rfl | hki
              · simp only [z', Finsupp.coe_add, Finsupp.coe_tsub, Pi.add_apply, Pi.sub_apply,
                  Finsupp.single_eq_same, Finsupp.single_eq_of_ne hilast, tsub_zero]
                omega
              · simp only [z', Finsupp.coe_add, Finsupp.coe_tsub, Pi.add_apply, Pi.sub_apply,
                  Finsupp.single_eq_of_ne hkl, Finsupp.single_eq_of_ne hki, tsub_zero, add_zero]
                exact hz_lt k
        have hz'0 : z' 0 = v 0 := by
          have h0l : (0 : Fin (m + 1)) ≠ Fin.last m := by
            intro h; have := congrArg Fin.val h; simp at this; omega
          simp [z', h0l, hi0.symm, hz0]
        have hz_lt_z' : toLex z < toLex z' := by
          rw [lex_lt_iff]
          refine ⟨i, fun r hr => ?_, ?_⟩
          · have hrl : r ≠ Fin.last m := ne_of_lt (lt_of_lt_of_le hr (Fin.le_last i))
            have hri : r ≠ i := ne_of_lt hr
            simp [z', hrl, hri]
          · simp only [z', Finsupp.coe_add, Finsupp.coe_tsub, Pi.add_apply, Pi.sub_apply,
              Finsupp.single_eq_same, Finsupp.single_eq_of_ne hilast, tsub_zero]
            omega
        have hz'M : z' ∈ M := hcomp 0 z' hz'_box z hz (by omega) hz_lt_z'
        have hz'last : z' (Fin.last m) = t := by
          simp only [z', Finsupp.coe_add, Finsupp.coe_tsub, Pi.add_apply, Pi.sub_apply,
            Finsupp.single_eq_same, Finsupp.single_eq_of_ne hilast.symm]
          omega
        exact ih z' hz'M hz'0 hz'last
  rcases hstep (v (Fin.last m)) v hvM rfl rfl with ⟨z', hz'M, hz'0, hz'last⟩ | ⟨z₁, hz₁M, hz₁0, hz₁mid⟩
  · have hz'_lt_u : toLex z' < toLex u := by
      rw [lex_lt_iff]
      exact ⟨0, fun j hj => absurd hj (Fin.not_lt_zero j), by omega⟩
    exact huM (hcomp (Fin.last m) u hu z' hz'M (by omega) hz'_lt_u)
  · by_cases hz₁l : z₁ (Fin.last m) = 0
    · have hz₁_lt_u : toLex z₁ < toLex u := by
        rw [lex_lt_iff]
        exact ⟨0, fun j hj => absurd hj (Fin.not_lt_zero j), by omega⟩
      exact huM (hcomp (Fin.last m) u hu z₁ hz₁M (by omega) hz₁_lt_u)
    · have hz₁l_pos : 1 ≤ z₁ (Fin.last m) := by omega
      obtain ⟨hu_deg, hu_lt⟩ := mem_monBox.mp hu
      obtain ⟨hz₁_deg, hz₁_lt⟩ := mem_monBox.mp (hM hz₁M)
      rw [Finsupp.degree_eq_sum] at hu_deg hz₁_deg
      have h0l : (0 : Fin (m + 1)) ≠ Fin.last m := by
        intro h; have := congrArg Fin.val h; simp at this; omega
      set mid := (Finset.univ.erase (0 : Fin (m + 1))).erase (Fin.last m)
      have hsum_split : ∀ x : Fin (m + 1) →₀ ℕ,
          ∑ i : Fin (m + 1), x i = x 0 + x (Fin.last m) + ∑ i ∈ mid, x i := fun x => by
        rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : Fin (m + 1)))]
        rw [← Finset.add_sum_erase _ _ (Finset.mem_erase.mpr ⟨h0l.symm, Finset.mem_univ _⟩)]
        ring
      have hmid_le : ∀ i ∈ mid, u i ≤ z₁ i := by
        intro i hi
        rw [mem_erase, mem_erase] at hi
        rw [hz₁mid i hi.2.1 hi.1]
        have := hu_lt i; omega
      have hsum_mid_le : ∑ i ∈ mid, u i ≤ ∑ i ∈ mid, z₁ i :=
        Finset.sum_le_sum hmid_le
      have hsu := hsum_split u
      have hsz := hsum_split z₁
      have hz₁_sum_le : z₁ 0 + z₁ (Fin.last m) ≤ u 0 := by omega
      set z₂ : Fin (m + 1) →₀ ℕ :=
        (z₁ - Finsupp.single (Fin.last m) (z₁ (Fin.last m))) +
          Finsupp.single 0 (z₁ (Fin.last m))
      have hz₂0 : z₂ 0 = z₁ 0 + z₁ (Fin.last m) := by simp [z₂, h0l]
      have hz₂last : z₂ (Fin.last m) = 0 := by simp [z₂, h0l.symm]
      have hz₂mid : ∀ i : Fin (m + 1), i ≠ 0 → i ≠ Fin.last m → z₂ i = z₁ i := fun i h1 h2 => by
        simp [z₂, h1, h2]
      have hz₂_box : z₂ ∈ monBox D e := by
        rw [mem_monBox]
        refine ⟨?_, fun k => ?_⟩
        · rw [Finsupp.degree_eq_sum, hsum_split z₂, hz₂0, hz₂last]
          have hrest : ∑ i ∈ mid, z₂ i = ∑ i ∈ mid, z₁ i :=
            Finset.sum_congr rfl fun i hi => by
              rw [mem_erase, mem_erase] at hi; exact hz₂mid i hi.2.1 hi.1
          omega
        · rcases eq_or_ne k 0 with rfl | hk0
          · rw [hz₂0]; have := hu_lt 0; omega
          · rcases eq_or_ne k (Fin.last m) with rfl | hkl
            · rw [hz₂last]; have := hD_pos (Fin.last m); omega
            · rw [hz₂mid k hk0 hkl]; exact hz₁_lt k
      set c1 : Fin (m + 1) := ⟨1, by omega⟩
      have hc1_0 : c1 ≠ 0 := by intro h; have := congrArg Fin.val h; simp [c1] at this
      have hc1_last : c1 ≠ Fin.last m := by
        intro h; have := congrArg Fin.val h; simp [c1] at this; omega
      have hz₁_lt_z₂ : toLex z₁ < toLex z₂ := by
        rw [lex_lt_iff]
        exact ⟨0, fun j hj => absurd hj (Fin.not_lt_zero j), by omega⟩
      have hz₂M : z₂ ∈ M := hcomp c1 z₂ hz₂_box z₁ hz₁M (hz₂mid c1 hc1_0 hc1_last) hz₁_lt_z₂
      rcases lt_or_eq_of_le hz₁_sum_le with hlt0 | heq0
      · have hz₂_lt_u : toLex z₂ < toLex u := by
          rw [lex_lt_iff]
          exact ⟨0, fun j hj => absurd hj (Fin.not_lt_zero j), by omega⟩
        exact huM (hcomp (Fin.last m) u hu z₂ hz₂M (by omega) hz₂_lt_u)
      · have hmid_eq : ∀ i ∈ mid, u i = z₁ i := by
          intro i hi
          by_contra hne
          have hlt_i : u i < z₁ i := lt_of_le_of_ne (hmid_le i hi) hne
          have hsum_lt := Finset.sum_lt_sum hmid_le ⟨i, hi, hlt_i⟩
          omega
        have huz₂ : u = z₂ := by
          ext i
          rcases eq_or_ne i 0 with rfl | hi0
          · omega
          · rcases eq_or_ne i (Fin.last m) with rfl | hil
            · omega
            · rw [hz₂mid i hi0 hil]
              exact hmid_eq i (Finset.mem_erase.mpr ⟨hil, Finset.mem_erase.mpr ⟨hi0, Finset.mem_univ i⟩⟩)
        exact huM (huz₂ ▸ hz₂M)

/-- Key lemma B (exact dual of A) for `n = m + 1 ≥ 3`: `v (Fin.last m) + 1 < D (Fin.last m)`. -/
lemma min_mem_last_lt_box {m e : ℕ} (hm : 2 ≤ m) {D : Fin (m + 1) → ℕ}
    {M : Finset (Fin (m + 1) →₀ ℕ)} (hM : M ⊆ monBox D e)
    (hcomp : ∀ i : Fin (m + 1), IsCompressedBox D i e M)
    {u v : Fin (m + 1) →₀ ℕ} (hu : u ∈ monBox D e) (huM : u ∉ M)
    (hvM : v ∈ M) (hvu : toLex v < toLex u) :
    v (Fin.last m) + 1 < D (Fin.last m) := by
  have hne_coord : ∀ i : Fin (m + 1), u i ≠ v i := fun i heq =>
    huM (hcomp i u hu v hvM heq hvu)
  have hu0_gt : v 0 < u 0 := by
    rw [lex_lt_iff] at hvu
    obtain ⟨j, hjeq, hjlt⟩ := hvu
    by_cases hj0 : j = 0
    · subst hj0; exact hjlt
    · exfalso
      exact hne_coord 0 (hjeq 0 (Nat.pos_of_ne_zero (fun h => hj0 (Fin.ext h)))).symm
  obtain ⟨hv_deg, hv_lt⟩ := mem_monBox.mp (hM hvM)
  by_contra hge
  have hv_last : v (Fin.last m) = D (Fin.last m) - 1 := by
    have := hv_lt (Fin.last m); omega
  have hstep : ∀ t : ℕ, ∀ z ∈ monBox D e, z ∉ M → z 0 = u 0 →
      (D (Fin.last m) - 1) - z (Fin.last m) = t →
      (∃ z' ∈ monBox D e, z' ∉ M ∧ z' 0 = u 0 ∧ z' (Fin.last m) = D (Fin.last m) - 1) ∨
      (∃ z₁ ∈ monBox D e, z₁ ∉ M ∧ z₁ 0 = u 0 ∧
        ∀ i : Fin (m + 1), i ≠ 0 → i ≠ Fin.last m → z₁ i = 0) := by
    intro t
    induction t with
    | zero =>
      intro z hz hzM hz0 hzt
      have hzl := (mem_monBox.mp hz).2 (Fin.last m)
      exact Or.inl ⟨z, hz, hzM, hz0, by omega⟩
    | succ t ih =>
      intro z hz hzM hz0 hzt
      by_cases hall0 : ∀ i : Fin (m + 1), i ≠ 0 → i ≠ Fin.last m → z i = 0
      · exact Or.inr ⟨z, hz, hzM, hz0, hall0⟩
      · push Not at hall0
        obtain ⟨i, hi0, hilast, hzi_ne⟩ := hall0
        obtain ⟨hz_deg, hz_lt⟩ := mem_monBox.mp hz
        have hzi_pos : 1 ≤ z i := by omega
        set z' : Fin (m + 1) →₀ ℕ := (z - Finsupp.single i 1) + Finsupp.single (Fin.last m) 1
        have hz'_box : z' ∈ monBox D e := by
          rw [mem_monBox]
          refine ⟨?_, fun k => ?_⟩
          · rw [map_add, Finsupp.degree_single]
            have := degree_sub_single hzi_pos
            omega
          · rcases eq_or_ne k (Fin.last m) with rfl | hkl
            · simp only [z', Finsupp.coe_add, Finsupp.coe_tsub, Pi.add_apply, Pi.sub_apply,
                Finsupp.single_eq_same, Finsupp.single_eq_of_ne hilast.symm, tsub_zero]
              have := hz_lt (Fin.last m); omega
            · by_cases hki : k = i
              · rw [hki]
                simp only [z', Finsupp.coe_add, Finsupp.coe_tsub, Pi.add_apply, Pi.sub_apply,
                  Finsupp.single_eq_same, Finsupp.single_eq_of_ne hilast]
                have := hz_lt i; omega
              · simp only [z', Finsupp.coe_add, Finsupp.coe_tsub, Pi.add_apply, Pi.sub_apply,
                  Finsupp.single_eq_of_ne hkl, Finsupp.single_eq_of_ne hki, tsub_zero, add_zero]
                exact hz_lt k
        have hz'0 : z' 0 = u 0 := by
          have h0l : (0 : Fin (m + 1)) ≠ Fin.last m := by
            intro h; have := congrArg Fin.val h; simp at this; omega
          simp [z', h0l, hi0.symm, hz0]
        have hz'_lt_z : toLex z' < toLex z := by
          rw [lex_lt_iff]
          refine ⟨i, fun r hr => ?_, ?_⟩
          · have hrl : r ≠ Fin.last m := ne_of_lt (lt_of_lt_of_le hr (Fin.le_last i))
            have hri : r ≠ i := ne_of_lt hr
            simp [z', hrl, hri]
          · simp only [z', Finsupp.coe_add, Finsupp.coe_tsub, Pi.add_apply, Pi.sub_apply,
              Finsupp.single_eq_same, Finsupp.single_eq_of_ne hilast]
            omega
        have hz'M : z' ∉ M := fun hmem => hzM (hcomp 0 z hz z' hmem (by omega) hz'_lt_z)
        have hz't : (D (Fin.last m) - 1) - z' (Fin.last m) = t := by
          simp only [z', Finsupp.coe_add, Finsupp.coe_tsub, Pi.add_apply, Pi.sub_apply,
            Finsupp.single_eq_same, Finsupp.single_eq_of_ne hilast.symm, tsub_zero]
          omega
        exact ih z' hz'_box hz'M hz'0 hz't
  rcases hstep ((D (Fin.last m) - 1) - u (Fin.last m)) u hu huM rfl rfl with
      ⟨z', hz'_box, hz'M, hz'0, hz'last⟩ | ⟨z₁, hz₁_box, hz₁M, hz₁0, hz₁mid⟩
  · have hv_lt_z' : toLex v < toLex z' := by
      rw [lex_lt_iff]
      exact ⟨0, fun j hj => absurd hj (Fin.not_lt_zero j), by omega⟩
    exact hz'M (hcomp (Fin.last m) z' hz'_box v hvM (by omega) hv_lt_z')
  · by_cases hz₁l : z₁ (Fin.last m) = D (Fin.last m) - 1
    · have hv_lt_z₁ : toLex v < toLex z₁ := by
        rw [lex_lt_iff]
        exact ⟨0, fun j hj => absurd hj (Fin.not_lt_zero j), by omega⟩
      exact hz₁M (hcomp (Fin.last m) z₁ hz₁_box v hvM (by omega) hv_lt_z₁)
    · obtain ⟨hz₁_deg, hz₁_lt⟩ := mem_monBox.mp hz₁_box
      rw [Finsupp.degree_eq_sum] at hv_deg hz₁_deg
      have h0l : (0 : Fin (m + 1)) ≠ Fin.last m := by
        intro h; have := congrArg Fin.val h; simp at this; omega
      set mid := (Finset.univ.erase (0 : Fin (m + 1))).erase (Fin.last m)
      have hsum_split : ∀ x : Fin (m + 1) →₀ ℕ,
          ∑ i : Fin (m + 1), x i = x 0 + x (Fin.last m) + ∑ i ∈ mid, x i := fun x => by
        rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : Fin (m + 1)))]
        rw [← Finset.add_sum_erase _ _ (Finset.mem_erase.mpr ⟨h0l.symm, Finset.mem_univ _⟩)]
        ring
      have hsum_z₁_mid : ∑ i ∈ mid, z₁ i = 0 :=
        Finset.sum_eq_zero fun i hi => by
          rw [mem_erase, mem_erase] at hi; exact hz₁mid i hi.2.1 hi.1
      have hsz := hsum_split z₁
      have hsv := hsum_split v
      set δ : ℕ := (D (Fin.last m) - 1) - z₁ (Fin.last m)
      have hδ_pos : 1 ≤ δ := by have := hz₁_lt (Fin.last m); omega
      have hδ_le : δ ≤ z₁ 0 - v 0 := by omega
      set z₂ : Fin (m + 1) →₀ ℕ :=
        (z₁ - Finsupp.single 0 δ) + Finsupp.single (Fin.last m) δ
      have hz₂0 : z₂ 0 = z₁ 0 - δ := by simp [z₂, h0l]
      have hz₂last : z₂ (Fin.last m) = D (Fin.last m) - 1 := by
        simp only [z₂, Finsupp.coe_add, Finsupp.coe_tsub, Pi.add_apply, Pi.sub_apply,
          Finsupp.single_eq_same, Finsupp.single_eq_of_ne h0l.symm, tsub_zero]
        have := hz₁_lt (Fin.last m); omega
      have hz₂mid : ∀ i : Fin (m + 1), i ≠ 0 → i ≠ Fin.last m → z₂ i = 0 := fun i h1 h2 => by
        simp [z₂, h1, h2, hz₁mid i h1 h2]
      have hz₂_box : z₂ ∈ monBox D e := by
        rw [mem_monBox]
        refine ⟨?_, fun k => ?_⟩
        · rw [Finsupp.degree_eq_sum, hsum_split z₂, hz₂0, hz₂last]
          have hrest : ∑ i ∈ mid, z₂ i = 0 :=
            Finset.sum_eq_zero fun i hi => by
              rw [mem_erase, mem_erase] at hi; exact hz₂mid i hi.2.1 hi.1
          omega
        · rcases eq_or_ne k 0 with rfl | hk0
          · rw [hz₂0]; have := hz₁_lt 0; omega
          · rcases eq_or_ne k (Fin.last m) with rfl | hkl
            · rw [hz₂last]; have := hv_lt (Fin.last m); omega
            · rw [hz₂mid k hk0 hkl]; exact hz₁_lt k |> fun h => by omega
      set c1 : Fin (m + 1) := ⟨1, by omega⟩
      have hc1_0 : c1 ≠ 0 := by intro h; have := congrArg Fin.val h; simp [c1] at this
      have hc1_last : c1 ≠ Fin.last m := by
        intro h; have := congrArg Fin.val h; simp [c1] at this; omega
      have hz₂_lt_z₁ : toLex z₂ < toLex z₁ := by
        rw [lex_lt_iff]
        exact ⟨0, fun j hj => absurd hj (Fin.not_lt_zero j), by omega⟩
      have hz₂M : z₂ ∉ M := fun hmem =>
        hz₁M (hcomp c1 z₁ hz₁_box z₂ hmem (by rw [hz₁mid c1 hc1_0 hc1_last, hz₂mid c1 hc1_0 hc1_last]) hz₂_lt_z₁)
      have hv_le_z₂0 : v 0 ≤ z₂ 0 := by omega
      rcases lt_or_eq_of_le hv_le_z₂0 with hlt0 | heq0
      · have hv_lt_z₂ : toLex v < toLex z₂ := by
          rw [lex_lt_iff]
          exact ⟨0, fun j hj => absurd hj (Fin.not_lt_zero j), hlt0⟩
        exact hz₂M (hcomp (Fin.last m) z₂ hz₂_box v hvM (by omega) hv_lt_z₂)
      · have hsum_v_mid : ∑ i ∈ mid, v i = 0 := by omega
        have hv_mid0 : ∀ i ∈ mid, v i = 0 := fun i hi =>
          (Finset.sum_eq_zero_iff.mp hsum_v_mid) i hi
        have hvz₂ : v = z₂ := by
          ext i
          rcases eq_or_ne i 0 with rfl | hi0
          · omega
          · rcases eq_or_ne i (Fin.last m) with rfl | hil
            · omega
            · rw [hz₂mid i hi0 hil]
              exact hv_mid0 i (Finset.mem_erase.mpr ⟨hil, Finset.mem_erase.mpr ⟨hi0, Finset.mem_univ i⟩⟩)
        exact hz₂M (hvz₂ ▸ hvM)

/-- Main theorem of Part 4: Clements-Lindström shadow inequality. -/
theorem clements_lindstrom_shadow (n : ℕ) :
    ∀ (D : Fin n → ℕ), (∀ i, 1 ≤ D i) → Monotone D →
      ∀ (e : ℕ) (M : Finset (Fin n →₀ ℕ)), M ⊆ monBox D e →
        (shadowBox D (lexSegBox D e M.card)).card ≤ (shadowBox D M).card := by
  induction n with
  | zero =>
    intro D _ _ e M hM
    have hlex : IsLexBox D e M := by
      refine ⟨hM, fun u _ v _ hlt => ?_⟩
      rw [lex_lt_iff] at hlt
      obtain ⟨i, _⟩ := hlt
      exact Fin.elim0 i
    rw [← hlex.eq_lexSegBox]
  | succ m ih =>
    cases m with
    | zero =>
      intro D _ _ e M hM
      have hlex : IsLexBox D e M := by
        refine ⟨hM, fun u hu v hv hlt => ?_⟩
        have hdu := (mem_monBox.mp hu).1
        have hdv := (mem_monBox.mp (hM hv)).1
        rw [Finsupp.degree_eq_sum, Fin.sum_univ_one] at hdu hdv
        have huv : u = v := Finsupp.ext fun i => by fin_cases i; change u 0 = v 0; omega
        subst huv
        exact absurd hlt (lt_irrefl _)
      rw [← hlex.eq_lexSegBox]
    | succ m' =>
      cases m' with
      | zero => exact clements_lindstrom_shadow_two
      | succ k =>
        set m := k + 2
        have hm : 2 ≤ m := by omega
        intro D hD_pos hD_mono e M hM
        suffices hmain : ∀ r (M : Finset (Fin (m + 1) →₀ ℕ)),
            M ⊆ monBox D e → lexRankSumBox D e M = r →
            (shadowBox D (lexSegBox D e M.card)).card ≤ (shadowBox D M).card by
          exact hmain _ M hM rfl
        intro r
        induction r using Nat.strong_induction_on with
        | _ r ihr =>
          intro M hM hr
          by_cases hlex : IsLexBox D e M
          · rw [← hlex.eq_lexSegBox]
          · by_cases hall : ∀ i : Fin (m + 1), IsCompressedBox D i e M
            · have hMne : M.Nonempty := by
                by_contra hemp
                rw [Finset.not_nonempty_iff_eq_empty] at hemp
                subst hemp
                exact hlex ⟨Finset.empty_subset _, fun _ _ _ hv _ => absurd hv (by simp)⟩
              have hCne : (monBox D e \ M).Nonempty := by
                by_contra hemp
                rw [Finset.not_nonempty_iff_eq_empty, Finset.sdiff_eq_empty_iff_subset] at hemp
                have heq : M = monBox D e := Finset.Subset.antisymm hM hemp
                exact hlex ⟨hM, fun u hu _ _ _ => heq ▸ hu⟩
              obtain ⟨u, huC, hu_max⟩ := Finset.exists_max_image _ toLex hCne
              obtain ⟨v, hvM, hv_min⟩ := Finset.exists_min_image _ toLex hMne
              rw [mem_sdiff] at huC
              obtain ⟨hu_box, hu_nM⟩ := huC
              have hvu' : toLex v < toLex u := by
                by_contra hle
                push Not at hle
                apply hlex
                refine ⟨hM, fun x hx y hy hlt => ?_⟩
                by_contra hxM
                have h1 : toLex x ≤ toLex u := hu_max x (mem_sdiff.mpr ⟨hx, hxM⟩)
                have h2 : toLex v ≤ toLex y := hv_min y hy
                exact not_lt_of_ge (le_trans h1 hle) (lt_of_le_of_lt h2 hlt)
              have hu_last : 1 ≤ u (Fin.last m) :=
                max_not_mem_last_pos_box hm hD_pos hM hall hu_box hu_nM hvM hvu'
              have hv_last_lt : v (Fin.last m) + 1 < D (Fin.last m) :=
                min_mem_last_lt_box hm hM hall hu_box hu_nM hvM hvu'
              set M₀ := M.erase v
              set M' := insert u M₀
              have huM₀ : u ∉ M₀ := fun h => hu_nM (Finset.mem_of_mem_erase h)
              have hM'sub : M' ⊆ monBox D e := by
                intro x hx
                rw [mem_insert] at hx
                rcases hx with rfl | hx
                · exact hu_box
                · exact hM (Finset.mem_of_mem_erase hx)
              have hM'card : M'.card = M.card := by
                rw [Finset.card_insert_of_notMem huM₀, Finset.card_erase_of_mem hvM]
                have := hMne.card_pos; omega
              have hrank_lt : lexRankSumBox D e M' < r := by
                rw [← hr, lexRankSumBox, lexRankSumBox, Finset.sum_insert huM₀]
                have hsumM : lexRankBox D e v + ∑ x ∈ M₀, lexRankBox D e x =
                    ∑ x ∈ M, lexRankBox D e x :=
                  Finset.add_sum_erase M (lexRankBox D e) hvM
                have hlt_rk := lexRankBox_lt_of_lt hu_box hvu'
                omega
              have hshadow_le : (shadowBox D M').card ≤ (shadowBox D M).card := by
                have hsub_u : shadowBox D M' \ shadowBox D M₀ ⊆
                    {u + Finsupp.single (Fin.last m) 1} := by
                  intro x hx
                  rw [mem_sdiff, mem_shadowBox] at hx
                  obtain ⟨⟨⟨a, ha, j, rfl⟩, ha_lt⟩, hx0⟩ := hx
                  rw [mem_insert] at ha
                  rcases ha with ha_eq | ha0
                  · rw [ha_eq] at hx0 ha_lt ⊢
                    rw [mem_singleton]
                    by_cases hj : j = Fin.last m
                    · subst hj; rfl
                    · exfalso
                      have hj_lt : j < Fin.last m := lt_of_le_of_ne (Fin.le_last j) hj
                      set w := (u - Finsupp.single (Fin.last m) 1) + Finsupp.single j 1
                      have hw_box : w ∈ monBox D e := by
                        rw [mem_monBox]
                        refine ⟨?_, fun t => ?_⟩
                        · rw [map_add, Finsupp.degree_single]
                          have := degree_sub_single hu_last
                          have hdu := (mem_monBox.mp hu_box).1
                          omega
                        · rcases eq_or_ne t (Fin.last m) with rfl | ht1
                          · simp only [w, Finsupp.coe_add, Finsupp.coe_tsub, Pi.add_apply,
                              Pi.sub_apply, Finsupp.single_eq_same,
                              Finsupp.single_eq_of_ne (Ne.symm hj)]
                            have := (mem_monBox.mp hu_box).2 (Fin.last m); omega
                          · by_cases ht2 : t = j
                            · rw [ht2]
                              simp only [w, Finsupp.coe_add, Finsupp.coe_tsub, Pi.add_apply,
                                Pi.sub_apply, Finsupp.single_eq_same,
                                Finsupp.single_eq_of_ne hj, tsub_zero]
                              have := ha_lt j
                              simp only [Finsupp.coe_add, Pi.add_apply, Finsupp.single_eq_same] at this
                              exact this
                            · simp only [w, Finsupp.coe_add, Finsupp.coe_tsub, Pi.add_apply,
                                Pi.sub_apply, Finsupp.single_eq_of_ne ht1,
                                Finsupp.single_eq_of_ne ht2, tsub_zero, add_zero]
                              exact (mem_monBox.mp hu_box).2 t
                      have hu_lt_w : toLex u < toLex w := by
                        rw [lex_lt_iff]
                        refine ⟨j, fun r hr => ?_, ?_⟩
                        · have h1 : Fin.last m ≠ r := ne_of_gt (lt_trans hr hj_lt)
                          have h2 : j ≠ r := ne_of_gt hr
                          simp [w, h1, h2]
                        · simp only [w, Finsupp.coe_add, Finsupp.coe_tsub, Pi.add_apply,
                            Pi.sub_apply, Finsupp.single_eq_same,
                            Finsupp.single_eq_of_ne hj, tsub_zero]
                          omega
                      have hwM : w ∈ M := by
                        by_contra hw_nM
                        exact not_lt_of_ge (hu_max w (mem_sdiff.mpr ⟨hw_box, hw_nM⟩)) hu_lt_w
                      have hwM₀ : w ∈ M₀ := Finset.mem_erase.mpr
                        ⟨fun heq => not_lt_of_ge (le_of_lt hvu') (heq ▸ hu_lt_w), hwM⟩
                      have heq_add : w + Finsupp.single (Fin.last m) 1 = u + Finsupp.single j 1 := by
                        ext t
                        rcases eq_or_ne t (Fin.last m) with rfl | ht1
                        · simp only [w, Finsupp.coe_add, Finsupp.coe_tsub, Pi.add_apply,
                            Pi.sub_apply, Finsupp.single_eq_same,
                            Finsupp.single_eq_of_ne (Ne.symm hj)]
                          omega
                        · rcases eq_or_ne t j with rfl | ht2
                          · simp [w, ht1]
                          · simp [w, ht1, ht2]
                      exact hx0 (mem_shadowBox.mpr ⟨⟨w, hwM₀, Fin.last m, heq_add⟩, ha_lt⟩)
                  · exact absurd (mem_shadowBox.mpr ⟨⟨a, ha0, j, rfl⟩, ha_lt⟩) hx0
                have hv_lost : v + Finsupp.single (Fin.last m) 1 ∈
                    shadowBox D M \ shadowBox D M₀ := by
                  rw [mem_sdiff]
                  refine ⟨mem_shadowBox.mpr ⟨⟨v, hvM, Fin.last m, rfl⟩, fun t => ?_⟩, ?_⟩
                  · rcases eq_or_ne t (Fin.last m) with rfl | ht
                    · simp only [Finsupp.coe_add, Pi.add_apply, Finsupp.single_eq_same]
                      exact hv_last_lt
                    · simp only [Finsupp.coe_add, Pi.add_apply, Finsupp.single_eq_of_ne ht, add_zero]
                      exact (mem_monBox.mp (hM hvM)).2 t
                  · rw [mem_shadowBox]
                    rintro ⟨⟨w, hw0, j, heq⟩, _⟩
                    have hwM := Finset.mem_of_mem_erase hw0
                    have hwne : w ≠ v := (Finset.mem_erase.mp hw0).1
                    by_cases hj : j = Fin.last m
                    · subst hj
                      exact hwne (add_right_cancel heq)
                    · have hj_lt : j < Fin.last m := lt_of_le_of_ne (Fin.le_last j) hj
                      have hw_lt_v : toLex w < toLex v := by
                        rw [lex_lt_iff]
                        refine ⟨j, fun r hr => ?_, ?_⟩
                        · have h1 : r ≠ Fin.last m := ne_of_lt (lt_trans hr hj_lt)
                          have h2 : r ≠ j := ne_of_lt hr
                          have h := congrArg (fun f : Fin (m + 1) →₀ ℕ => f r) heq
                          simp only [Finsupp.coe_add, Pi.add_apply,
                            Finsupp.single_eq_of_ne h1, Finsupp.single_eq_of_ne h2] at h
                          omega
                        · have h := congrArg (fun f : Fin (m + 1) →₀ ℕ => f j) heq
                          simp only [Finsupp.coe_add, Pi.add_apply,
                            Finsupp.single_eq_same, Finsupp.single_eq_of_ne hj] at h
                          omega
                      exact not_lt_of_ge (hv_min w hwM) hw_lt_v
                have hM₀_sub_M : shadowBox D M₀ ⊆ shadowBox D M :=
                  shadowBox_mono D (Finset.erase_subset v M)
                have hM₀_sub_M' : shadowBox D M₀ ⊆ shadowBox D M' :=
                  shadowBox_mono D (Finset.subset_insert u M₀)
                have hc1 := Finset.card_sdiff_add_card_eq_card hM₀_sub_M'
                have hc2 := Finset.card_sdiff_add_card_eq_card hM₀_sub_M
                have hle1 : (shadowBox D M' \ shadowBox D M₀).card ≤ 1 :=
                  (Finset.card_le_card hsub_u).trans (by simp)
                have hge1 : 1 ≤ (shadowBox D M \ shadowBox D M₀).card :=
                  Finset.one_le_card.mpr ⟨_, hv_lost⟩
                omega
              calc (shadowBox D (lexSegBox D e M.card)).card
                  = (shadowBox D (lexSegBox D e M'.card)).card := by rw [hM'card]
                _ ≤ (shadowBox D M').card := ihr _ hrank_lt M' hM'sub rfl
                _ ≤ (shadowBox D M).card := hshadow_le
            · push Not at hall
              obtain ⟨i, hni⟩ := hall
              set C := compressBox D i e M
              have hCsub : C ⊆ monBox D e := compressBox_subset_monBox D i e M
              have hCcard : C.card = M.card := card_compressBox D i e hM
              have hrank_lt : lexRankSumBox D e C < r :=
                hr ▸ lexRankSumBox_compressBox_lt i hM hni
              have hshadow_le : (shadowBox D C).card ≤ (shadowBox D M).card := by
                rw [card_eq_sum_card_slice i (shadowBox_subset_monBox hCsub),
                    card_eq_sum_card_slice i (shadowBox_subset_monBox hM)]
                refine Finset.sum_le_sum fun a ha => ?_
                rw [mem_range] at ha
                rw [slice_shadowBox i a hCsub, slice_shadowBox i a hM]
                by_cases haD : a < D i
                · rw [if_pos haD, if_pos haD]
                  by_cases hae : a ≤ e
                  · rw [slice_compressBox D i e a M hae haD]
                    have hlex1 : IsLexBox (delBound D i) (e - a + 1)
                        (shadowBox (delBound D i) (lexSegBox (delBound D i) (e - a) (slice i a M).card)) :=
                      (isLexBox_lexSegBox (delBound D i) (e - a) _).shadowBox
                    by_cases ha0 : 0 < a
                    · rw [if_pos ha0, if_pos ha0,
                        slice_compressBox D i e (a - 1) M (by omega) (by omega)]
                      have hdeg_eq : e - a + 1 = e - (a - 1) := by omega
                      have hlex2 : IsLexBox (delBound D i) (e - a + 1)
                          (lexSegBox (delBound D i) (e - (a - 1)) (slice i (a - 1) M).card) := by
                        rw [hdeg_eq]; exact isLexBox_lexSegBox (delBound D i) (e - (a - 1)) _
                      rw [hlex1.card_union hlex2]
                      apply max_le
                      · calc (shadowBox (delBound D i) (lexSegBox (delBound D i) (e - a) (slice i a M).card)).card
                            ≤ (shadowBox (delBound D i) (slice i a M)).card :=
                              ih (delBound D i) (delBound_pos hD_pos i) (delBound_mono hD_mono i)
                                (e - a) (slice i a M) (slice_subset_monBox hM)
                          _ ≤ (shadowBox (delBound D i) (slice i a M) ∪ slice i (a - 1) M).card :=
                              Finset.card_le_card Finset.subset_union_left
                      · rw [card_lexSegBox (Finset.card_le_card (slice_subset_monBox hM))]
                        exact Finset.card_le_card Finset.subset_union_right
                    · rw [if_neg ha0, if_neg ha0, Finset.union_empty, Finset.union_empty]
                      exact ih (delBound D i) (delBound_pos hD_pos i) (delBound_mono hD_mono i)
                        (e - a) (slice i a M) (slice_subset_monBox hM)
                  · have ha_eq : a = e + 1 := by omega
                    subst ha_eq
                    have hsc0 : slice i (e + 1) C = ∅ := by
                      rw [Finset.eq_empty_iff_forall_notMem]
                      intro w hw
                      rw [mem_slice] at hw
                      have hdeg := (mem_monBox.mp (hCsub hw)).1
                      rw [degree_insertCoord] at hdeg
                      omega
                    have hsm0 : slice i (e + 1) M = ∅ := by
                      rw [Finset.eq_empty_iff_forall_notMem]
                      intro w hw
                      rw [mem_slice] at hw
                      have hdeg := (mem_monBox.mp (hM hw)).1
                      rw [degree_insertCoord] at hdeg
                      omega
                    simp only [hsc0, hsm0, shadowBox_empty, Finset.empty_union,
                      Nat.zero_lt_succ, ↓reduceIte, Nat.add_sub_cancel]
                    rw [slice_compressBox D i e e M le_rfl (by omega)]
                    rw [card_lexSegBox (Finset.card_le_card (slice_subset_monBox hM))]
                · rw [if_neg haD, if_neg haD]
              calc (shadowBox D (lexSegBox D e M.card)).card
                  = (shadowBox D (lexSegBox D e C.card)).card := by rw [hCcard]
                _ ≤ (shadowBox D C).card := ihr _ hrank_lt C hCsub rfl
                _ ≤ (shadowBox D M).card := hshadow_le

/- Part 5: Initial monomials and monomial ideals -/

section IdealPart

variable {n : ℕ} {k : Type*} [Field k]

noncomputable def lm (f : MvPolynomial (Fin n) k) (hf : f ≠ 0) : Fin n →₀ ℕ :=
  ofLex ((f.support.image toLex).max' ((f.support_nonempty.mpr hf).image toLex))

lemma lm_mem_support {f : MvPolynomial (Fin n) k} (hf : f ≠ 0) : lm f hf ∈ f.support := by
  have hmem := Finset.max'_mem (f.support.image toLex) ((f.support_nonempty.mpr hf).image toLex)
  rw [mem_image] at hmem
  obtain ⟨u, hu, heq⟩ := hmem
  have : lm f hf = u := by simp only [lm, ← heq]; rfl
  rwa [this]

lemma coeff_lm_ne_zero {f : MvPolynomial (Fin n) k} (hf : f ≠ 0) : coeff (lm f hf) f ≠ 0 :=
  mem_support_iff.mp (lm_mem_support hf)

lemma le_lm {f : MvPolynomial (Fin n) k} (hf : f ≠ 0) {u : Fin n →₀ ℕ} (hu : u ∈ f.support) :
    toLex u ≤ toLex (lm f hf) :=
  Finset.le_max' (f.support.image toLex) (toLex u) (Finset.mem_image_of_mem toLex hu)

lemma coeff_eq_zero_of_lm_lt {f : MvPolynomial (Fin n) k} (hf : f ≠ 0) {u : Fin n →₀ ℕ}
    (hlt : toLex (lm f hf) < toLex u) : coeff u f = 0 := by
  by_contra hne
  exact not_lt_of_ge (le_lm hf (mem_support_iff.mpr hne)) hlt

lemma support_X_mul (i : Fin n) (f : MvPolynomial (Fin n) k) :
    (X i * f).support = f.support.image (· + Finsupp.single i 1) := by
  ext d
  simp only [mem_support_iff, mem_image]
  have hcoeff : coeff d (X i * f) =
      if 1 ≤ d i then coeff (d - Finsupp.single i 1) f else 0 := by
    rw [X, coeff_monomial_mul']
    by_cases hle : Finsupp.single i 1 ≤ d
    · have h1 : 1 ≤ d i := by have := hle i; simpa using this
      rw [if_pos hle, if_pos h1, one_mul]
    · have h0 : ¬ 1 ≤ d i := by
        intro h1; apply hle; intro j
        by_cases hj : j = i
        · subst hj; simpa using h1
        · simp [Ne.symm hj]
      rw [if_neg hle, if_neg h0]
  rw [hcoeff]
  constructor
  · intro hne
    split_ifs at hne with h1
    · exact ⟨d - Finsupp.single i 1, hne, sub_single_add_single h1⟩
    · exact absurd rfl hne
  · rintro ⟨u, hu, rfl⟩
    have h1 : 1 ≤ (u + Finsupp.single i 1 : Fin n →₀ ℕ) i := by simp
    rw [if_pos h1]
    have hsub : u + Finsupp.single i 1 - Finsupp.single i 1 = u := add_tsub_cancel_right u _
    rwa [hsub]

lemma lm_X_mul (i : Fin n) {f : MvPolynomial (Fin n) k} (hf : f ≠ 0) (hxf : X i * f ≠ 0) :
    lm (X i * f) hxf = lm f hf + Finsupp.single i 1 := by
  apply toLex.injective
  apply le_antisymm
  · have hmem := lm_mem_support hxf
    rw [support_X_mul, mem_image] at hmem
    obtain ⟨u, hu, heq⟩ := hmem
    rw [← heq]
    exact (toLex_add_single_strictMono i).monotone (le_lm hf hu)
  · apply le_lm hxf
    rw [support_X_mul]
    exact Finset.mem_image_of_mem _ (lm_mem_support hf)

lemma weight_one_eq_degree (u : Fin n →₀ ℕ) : Finsupp.weight (1 : Fin n → ℕ) u = u.degree := by
  simp [Finsupp.weight_apply, Finsupp.degree_eq_sum, Finsupp.sum_fintype]

noncomputable def idealPiece (I : Ideal (MvPolynomial (Fin n) k)) (e : ℕ) :
    Submodule k (MvPolynomial (Fin n) k) :=
  Submodule.restrictScalars k I ⊓ homogeneousSubmodule (Fin n) k e

open Classical in
noncomputable def initMons (I : Ideal (MvPolynomial (Fin n) k)) (e : ℕ) :
    Finset (Fin n →₀ ℕ) :=
  (monOfDeg n e).filter (fun u => ∃ f ∈ idealPiece I e, ∃ hf : f ≠ 0, lm f hf = u)

lemma mem_initMons {I : Ideal (MvPolynomial (Fin n) k)} {e : ℕ} {u : Fin n →₀ ℕ} :
    u ∈ initMons I e ↔ u ∈ monOfDeg n e ∧ ∃ f ∈ idealPiece I e, ∃ hf : f ≠ 0, lm f hf = u := by
  classical
  simp [initMons]

lemma initMons_subset (I : Ideal (MvPolynomial (Fin n) k)) (e : ℕ) :
    initMons I e ⊆ monOfDeg n e := fun _ hu => (mem_initMons.mp hu).1

lemma shadow_initMons_subset (I : Ideal (MvPolynomial (Fin n) k)) (e : ℕ) :
    shadow (initMons I e) ⊆ initMons I (e + 1) := by
  intro v hv
  rw [mem_shadow] at hv
  obtain ⟨u, hu, i, rfl⟩ := hv
  rw [mem_initMons] at hu ⊢
  obtain ⟨hu_deg, f, hfI, hf0, rfl⟩ := hu
  refine ⟨shadow_subset_monOfDeg (initMons_subset I e)
    (mem_shadow.mpr ⟨lm f hf0, mem_initMons.mpr ⟨hu_deg, f, hfI, hf0, rfl⟩, i, rfl⟩), ?_⟩
  have hxf_mem : X i * f ∈ idealPiece I (e + 1) := by
    refine ⟨Ideal.mul_mem_left I (X i) hfI.1, ?_⟩
    change X i * f ∈ homogeneousSubmodule (Fin n) k (e + 1)
    rw [mem_homogeneousSubmodule]
    have h1 : (X i : MvPolynomial (Fin n) k).IsHomogeneous 1 := isHomogeneous_X k i
    have h2 : f.IsHomogeneous e := (mem_homogeneousSubmodule _ _).mp hfI.2
    simpa [add_comm] using h1.mul h2
  have hxf0 : X i * f ≠ 0 := mul_ne_zero (X_ne_zero i) hf0
  exact ⟨X i * f, hxf_mem, hxf0, lm_X_mul i hf0 hxf0⟩

lemma card_initMons_eq_hilbertFunction (I : Ideal (MvPolynomial (Fin n) k)) (e : ℕ) :
    (initMons I e).card = hilbertFunction I e := by
  classical
  set M := initMons I e
  set V := idealPiece I e
  have hpick : ∀ u : M, ∃ f ∈ V, ∃ hf : f ≠ 0, lm f hf = u.1 := fun u =>
    (mem_initMons.mp u.2).2
  let g : M → V := fun u => ⟨(hpick u).choose, (hpick u).choose_spec.1⟩
  have hg_ne : ∀ u : M, (g u : MvPolynomial (Fin n) k) ≠ 0 := fun u =>
    (hpick u).choose_spec.2.choose
  have hg_lm : ∀ u : M, lm (g u : MvPolynomial (Fin n) k) (hg_ne u) = u.1 := fun u =>
    (hpick u).choose_spec.2.choose_spec
  have hlin : LinearIndependent k g := by
    rw [Fintype.linearIndependent_iff]
    intro c hc
    by_contra hne
    push Not at hne
    set s := Finset.univ.filter (fun u : M => c u ≠ 0)
    have hs_ne : s.Nonempty := by
      obtain ⟨u, hu⟩ := hne
      exact ⟨u, Finset.mem_filter.mpr ⟨Finset.mem_univ u, hu⟩⟩
    obtain ⟨u_max, hu_max, hu_max_ge⟩ :=
      Finset.exists_max_image s (fun u : M => toLex u.1) hs_ne
    have hc_zero : coeff u_max.1 (∑ u : M, c u • (g u : MvPolynomial (Fin n) k)) = 0 := by
      have hval := congrArg Subtype.val hc
      simp only [Submodule.coe_sum, SetLike.val_smul, ZeroMemClass.coe_zero] at hval
      rw [hval, coeff_zero]
    rw [coeff_sum] at hc_zero
    have hsingle : ∑ u : M, coeff u_max.1 (c u • (g u : MvPolynomial (Fin n) k)) =
        c u_max * coeff u_max.1 (g u_max : MvPolynomial (Fin n) k) := by
      rw [Finset.sum_eq_single u_max]
      · rw [coeff_smul, smul_eq_mul]
      · intro u _ hun
        by_cases hcu : c u = 0
        · simp [hcu]
        · rw [coeff_smul, smul_eq_mul]
          have hu_s : u ∈ s := Finset.mem_filter.mpr ⟨Finset.mem_univ u, hcu⟩
          have hlt : toLex u.1 < toLex u_max.1 :=
            lt_of_le_of_ne (hu_max_ge u hu_s) (fun h => hun (Subtype.ext h))
          have h0 : coeff u_max.1 (g u : MvPolynomial (Fin n) k) = 0 :=
            coeff_eq_zero_of_lm_lt (hg_ne u) (by rwa [hg_lm u])
          simp [h0]
      · intro h; exact absurd (Finset.mem_univ u_max) h
    rw [hsingle] at hc_zero
    have hc_ne : c u_max ≠ 0 := (Finset.mem_filter.mp hu_max).2
    have hlm_ne : coeff u_max.1 (g u_max : MvPolynomial (Fin n) k) ≠ 0 := by
      rw [← hg_lm u_max]; exact coeff_lm_ne_zero (hg_ne u_max)
    exact mul_ne_zero hc_ne hlm_ne hc_zero
  have hspan : ⊤ ≤ Submodule.span k (Set.range g) := by
    intro f _
    suffices h : ∀ r (f : V),
        (∀ hf : (f : MvPolynomial (Fin n) k) ≠ 0,
          ((monOfDeg n e).filter (fun w => toLex w ≤ toLex (lm f.1 hf))).card ≤ r) →
        f ∈ Submodule.span k (Set.range g) by
      exact h (monOfDeg n e).card f (fun _ => Finset.card_le_card (Finset.filter_subset _ _))
    intro r
    induction r with
    | zero =>
      intro f hf_bound
      by_cases hf0 : (f : MvPolynomial (Fin n) k) = 0
      · have : f = 0 := Subtype.ext hf0
        rw [this]; exact Submodule.zero_mem _
      · exfalso
        have hdeg_lm : lm f.1 hf0 ∈ monOfDeg n e := by
          rw [mem_monOfDeg, ← weight_one_eq_degree]
          exact ((mem_homogeneousSubmodule _ _).mp f.2.2) (coeff_lm_ne_zero hf0)
        have hpos : 0 < ((monOfDeg n e).filter (fun w => toLex w ≤ toLex (lm f.1 hf0))).card :=
          Finset.card_pos.mpr ⟨lm f.1 hf0, Finset.mem_filter.mpr ⟨hdeg_lm, le_rfl⟩⟩
        have := hf_bound hf0
        omega
    | succ r ihr =>
      intro f hf_bound
      by_cases hf0 : (f : MvPolynomial (Fin n) k) = 0
      · have : f = 0 := Subtype.ext hf0
        rw [this]; exact Submodule.zero_mem _
      · set u := lm f.1 hf0
        have hu_deg : u ∈ monOfDeg n e := by
          rw [mem_monOfDeg, ← weight_one_eq_degree]
          exact ((mem_homogeneousSubmodule _ _).mp f.2.2) (coeff_lm_ne_zero hf0)
        have huM : u ∈ M := mem_initMons.mpr ⟨hu_deg, f.1, f.2, hf0, rfl⟩
        let u' : M := ⟨u, huM⟩
        set α : k := coeff u f.1 / coeff u (g u' : MvPolynomial (Fin n) k)
        set f' : V := f - α • g u'
        have hf'_mem : f' ∈ Submodule.span k (Set.range g) := by
          apply ihr f'
          intro hf'0
          have hlt_lm : toLex (lm f'.1 hf'0) < toLex u := by
            have hmem := lm_mem_support hf'0
            have hsub : f'.1.support ⊆ f.1.support ∪ (g u' : MvPolynomial (Fin n) k).support := by
              intro w hw
              rw [mem_support_iff] at hw
              simp only [f', Submodule.coe_sub, SetLike.val_smul, coeff_sub, coeff_smul,
                smul_eq_mul] at hw
              rw [mem_union, mem_support_iff, mem_support_iff]
              by_contra h
              push Not at h
              exact hw (by simp [h.1, h.2])
            have hle : toLex (lm f'.1 hf'0) ≤ toLex u := by
              rcases mem_union.mp (hsub hmem) with h1 | h2
              · exact le_lm hf0 h1
              · have := le_lm (hg_ne u') h2
                rwa [hg_lm u'] at this
            refine lt_of_le_of_ne hle ?_
            intro heq
            have hcu : coeff u f'.1 = 0 := by
              simp only [f', Submodule.coe_sub, SetLike.val_smul, coeff_sub, coeff_smul,
                smul_eq_mul, α]
              have hne_gu : coeff u (g u' : MvPolynomial (Fin n) k) ≠ 0 := by
                have := coeff_lm_ne_zero (hg_ne u')
                rwa [hg_lm u'] at this
              rw [div_mul_cancel₀ _ hne_gu, sub_self]
            have hne_lm := coeff_lm_ne_zero hf'0
            have : lm f'.1 hf'0 = u := heq
            rw [this] at hne_lm
            exact hne_lm hcu
          have hssub : (monOfDeg n e).filter (fun w => toLex w ≤ toLex (lm f'.1 hf'0)) ⊂
              (monOfDeg n e).filter (fun w => toLex w ≤ toLex u) := by
            rw [Finset.ssubset_iff_of_subset]
            · exact ⟨u, Finset.mem_filter.mpr ⟨hu_deg, le_rfl⟩,
                by simp [not_le_of_gt hlt_lm]⟩
            · intro w hw
              simp only [mem_filter] at hw ⊢
              exact ⟨hw.1, le_trans hw.2 (le_of_lt hlt_lm)⟩
          have hcard_lt := Finset.card_lt_card hssub
          have hbound : ((monOfDeg n e).filter (fun w => toLex w ≤ toLex u)).card ≤ r + 1 :=
            hf_bound hf0
          omega
        have heq_f : f = f' + α • g u' := by simp [f']
        rw [heq_f]
        exact Submodule.add_mem _ hf'_mem
          (Submodule.smul_mem _ α (Submodule.subset_span ⟨u', rfl⟩))
  let B : Module.Basis M k V := Module.Basis.mk hlin hspan
  have hfin := Module.finrank_eq_card_basis B
  rw [Fintype.card_coe] at hfin
  exact hfin.symm

lemma mem_monomialIdeal_iff_support {S : Set (Fin n →₀ ℕ)}
    (hclosed : ∀ u ∈ S, ∀ i : Fin n, u + Finsupp.single i 1 ∈ S)
    (f : MvPolynomial (Fin n) k) :
    f ∈ Ideal.span ((fun u => monomial u (1 : k)) '' S) ↔ ∀ u ∈ f.support, u ∈ S := by
  classical
  have hclosed_add : ∀ d : ℕ, ∀ w : Fin n →₀ ℕ, w.degree = d → ∀ u ∈ S, u + w ∈ S := by
    intro d
    induction d with
    | zero =>
      intro w hw u hu
      have hw0 : w = 0 := by
        ext i
        have hle : w i ≤ w.degree := by
          rw [Finsupp.degree_eq_sum]
          exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
        simp only [Finsupp.zero_apply]
        omega
      simpa [hw0] using hu
    | succ d ih =>
      intro w hw u hu
      have hne : w.support.Nonempty := by
        rw [Finsupp.support_nonempty_iff]
        intro h0; rw [h0, map_zero] at hw; omega
      obtain ⟨i, hi⟩ := hne
      have hi_pos : 1 ≤ w i := by
        have := Finsupp.mem_support_iff.mp hi; omega
      have hdeg_sub : (w - Finsupp.single i 1).degree = d := by
        have := degree_sub_single hi_pos; omega
      have hmem := ih (w - Finsupp.single i 1) hdeg_sub u hu
      have hmem' := hclosed _ hmem i
      rwa [add_assoc, sub_single_add_single hi_pos] at hmem'
  let J : Ideal (MvPolynomial (Fin n) k) :=
    { carrier := { f | ∀ u ∈ f.support, u ∈ S }
      add_mem' := fun {a b} ha hb u hu => by
        rcases Finset.mem_union.mp (MvPolynomial.support_add hu) with h | h
        · exact ha u h
        · exact hb u h
      zero_mem' := fun u hu => by simp at hu
      smul_mem' := fun g f hf u hu => by
        have hmul := MvPolynomial.support_mul g f hu
        rw [Finset.mem_add] at hmul
        obtain ⟨w, _, v, hv, rfl⟩ := hmul
        rw [add_comm]
        exact hclosed_add w.degree w rfl v (hf v hv) }
  constructor
  · intro hf
    have hle : Ideal.span ((fun u => monomial u (1 : k)) '' S) ≤ J := by
      rw [Ideal.span_le]
      rintro _ ⟨u, hu, rfl⟩ v hv
      rw [MvPolynomial.support_monomial, if_neg one_ne_zero, Finset.mem_singleton] at hv
      rwa [hv]
    exact hle hf
  · intro hf
    rw [f.as_sum]
    refine Ideal.sum_mem _ fun u hu => ?_
    have hmon : monomial u (coeff u f) = C (coeff u f) * monomial u (1 : k) := by
      rw [C_mul_monomial, mul_one]
    rw [hmon]
    exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨u, hf u hu, rfl⟩)

lemma hilbertFunction_monomialIdeal {L_slice : ℕ → Finset (Fin n →₀ ℕ)}
    {S : Set (Fin n →₀ ℕ)} (hS : ∀ u, u ∈ S ↔ u ∈ L_slice u.degree)
    (hdeg : ∀ e, L_slice e ⊆ monOfDeg n e)
    (hshadow : ∀ e, shadow (L_slice e) ⊆ L_slice (e + 1)) (e : ℕ) :
    hilbertFunction (Ideal.span ((fun u => monomial u (1 : k)) '' S)) e = (L_slice e).card := by
  classical
  have hclosed : ∀ u ∈ S, ∀ i : Fin n, u + Finsupp.single i 1 ∈ S := by
    intro u hu i
    rw [hS, map_add, Finsupp.degree_single]
    exact hshadow u.degree (mem_shadow.mpr ⟨u, (hS u).mp hu, i, rfl⟩)
  set L : Ideal (MvPolynomial (Fin n) k) := Ideal.span ((fun u => monomial u (1 : k)) '' S)
  set V := idealPiece L e
  have hmemV : ∀ f : MvPolynomial (Fin n) k, f ∈ V ↔ ∀ u ∈ f.support, u ∈ L_slice e := by
    intro f
    constructor
    · rintro ⟨h1, h2⟩ u hu
      have h1' : f ∈ L := h1
      have h2' : f.IsHomogeneous e := (mem_homogeneousSubmodule _ _).mp h2
      have hdu : u.degree = e := by
        rw [← weight_one_eq_degree]; exact h2' (mem_support_iff.mp hu)
      have huS : u ∈ S := (mem_monomialIdeal_iff_support hclosed f).mp h1' u hu
      have huL : u ∈ L_slice u.degree := (hS u).mp huS
      rwa [hdu] at huL
    · intro h
      refine ⟨?_, ?_⟩
      · change f ∈ L
        rw [mem_monomialIdeal_iff_support hclosed]
        intro u hu
        rw [hS, mem_monOfDeg.mp (hdeg e (h u hu))]
        exact h u hu
      · change f ∈ homogeneousSubmodule (Fin n) k e
        rw [mem_homogeneousSubmodule]
        intro u hu
        rw [weight_one_eq_degree]
        exact mem_monOfDeg.mp (hdeg e (h u (mem_support_iff.mpr hu)))
  let b : L_slice e → V := fun u =>
    ⟨monomial u.1 (1 : k), (hmemV _).mpr fun v hv => by
      rw [MvPolynomial.support_monomial, if_neg one_ne_zero, Finset.mem_singleton] at hv
      rw [hv]
      exact u.2⟩
  have hlin : LinearIndependent k b := by
    rw [Fintype.linearIndependent_iff]
    intro c hc u
    have hval := congrArg (fun x : V => coeff u.1 x.1) hc
    simp only [Submodule.coe_sum, SetLike.val_smul, ZeroMemClass.coe_zero, coeff_zero,
      coeff_sum, coeff_smul, smul_eq_mul, b, coeff_monomial] at hval
    have hsum : ∑ x : L_slice e, c x * (if x.1 = u.1 then (1 : k) else 0) = c u := by
      rw [Finset.sum_eq_single u]
      · simp
      · intro x _ hxu
        rw [if_neg (fun h => hxu (Subtype.ext h)), mul_zero]
      · intro h; exact absurd (Finset.mem_univ u) h
    rw [hsum] at hval
    exact hval
  have hspan : ⊤ ≤ Submodule.span k (Set.range b) := by
    intro f _
    have hsupp := (hmemV f.1).mp f.2
    have hfeq : f = ∑ u ∈ f.1.support.attach,
        coeff u.1 f.1 • b ⟨u.1, hsupp u.1 u.2⟩ := by
      apply Subtype.ext
      simp only [Submodule.coe_sum, SetLike.val_smul, b]
      conv_lhs => rw [f.1.as_sum]
      rw [← Finset.sum_attach f.1.support (fun u => monomial u (coeff u f.1))]
      refine Finset.sum_congr rfl fun u _ => ?_
      rw [smul_monomial, smul_eq_mul, mul_one]
    rw [hfeq]
    exact Submodule.sum_mem _ fun u _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨u.1, hsupp u.1 u.2⟩, rfl⟩)
  let B : Module.Basis (L_slice e) k V := Module.Basis.mk hlin hspan
  have hfin := Module.finrank_eq_card_basis B
  rw [Fintype.card_coe] at hfin
  exact hfin

/- Part 6: Pure powers characterization and main Clements-Lindström theorem -/

lemma X_pow_eq_monomial (i : Fin n) (m : ℕ) :
    (X i : MvPolynomial (Fin n) k) ^ m = monomial (Finsupp.single i m) (1 : k) := by
  induction m with
  | zero => simp [monomial_zero']
  | succ m ih =>
    rw [pow_succ, ih, X, monomial_mul, mul_one, ← Finsupp.single_add]

lemma purePowersIdeal_eq_monomialIdeal {c : ℕ} (hc : c ≤ n) (d : Fin c → ℕ) :
    (purePowersIdeal hc d : Ideal (MvPolynomial (Fin n) k)) =
      Ideal.span ((fun u => monomial u (1 : k)) ''
        { u : Fin n →₀ ℕ | ∃ j : Fin c, d j ≤ u (Fin.castLE hc j) }) := by
  set SP : Set (Fin n →₀ ℕ) := { u : Fin n →₀ ℕ | ∃ j : Fin c, d j ≤ u (Fin.castLE hc j) }
  apply le_antisymm
  · rw [purePowersIdeal, Ideal.span_le]
    rintro _ ⟨j, rfl⟩
    change (X (Fin.castLE hc j) : MvPolynomial (Fin n) k) ^ d j ∈
      Ideal.span ((fun u => monomial u (1 : k)) '' SP)
    rw [X_pow_eq_monomial]
    exact Ideal.subset_span ⟨Finsupp.single (Fin.castLE hc j) (d j), ⟨j, by simp⟩, rfl⟩
  · rw [Ideal.span_le]
    rintro _ ⟨u, ⟨j, hj⟩, rfl⟩
    change monomial u (1 : k) ∈ purePowersIdeal hc d
    have hsplit : u = (u - Finsupp.single (Fin.castLE hc j) (d j)) +
        Finsupp.single (Fin.castLE hc j) (d j) := by
      ext r
      rcases eq_or_ne r (Fin.castLE hc j) with rfl | hr
      · simp only [Finsupp.coe_add, Finsupp.coe_tsub, Pi.add_apply, Pi.sub_apply,
          Finsupp.single_eq_same]; omega
      · simp [hr]
    have hmon : monomial u (1 : k) =
        monomial (u - Finsupp.single (Fin.castLE hc j) (d j)) (1 : k) *
          (X (Fin.castLE hc j) : MvPolynomial (Fin n) k) ^ d j := by
      rw [X_pow_eq_monomial, monomial_mul, mul_one, ← hsplit]
    rw [hmon]
    exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨j, rfl⟩)

lemma isLexFull_shadow {e : ℕ} {L : Finset (Fin n →₀ ℕ)}
    (hLsub : L ⊆ monOfDeg n e)
    (hLlex : ∀ u ∈ monOfDeg n e, ∀ v ∈ L, toLex v < toLex u → u ∈ L) :
    ∀ u ∈ monOfDeg n (e + 1), ∀ v ∈ shadow L, toLex v < toLex u → u ∈ shadow L := by
  set D : Fin n → ℕ := fun _ => e + 2
  have hmon_eq : ∀ d ≤ e + 1, monBox D d = monOfDeg n d := fun d hd => by
    ext u
    simp only [mem_monBox, mem_monOfDeg, and_iff_left_iff_imp]
    intro hdeg i
    have hle : u i ≤ u.degree := by
      rw [Finsupp.degree_eq_sum]
      exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
    simp only [D]; omega
  have hsh_eq : shadowBox D L = shadow L := by
    ext v
    simp only [mem_shadowBox, mem_shadow, and_iff_left_iff_imp]
    rintro ⟨w, hw, i, rfl⟩ r
    have hdeg := mem_monOfDeg.mp (hLsub hw)
    have hle : (w + Finsupp.single i 1 : Fin n →₀ ℕ) r ≤ (w + Finsupp.single i 1).degree := by
      rw [Finsupp.degree_eq_sum]
      exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ r)
    rw [map_add, Finsupp.degree_single, hdeg] at hle
    simp only [D]; omega
  have hboxL : IsLexBox D e L := by
    rw [IsLexBox, hmon_eq e (by omega)]
    exact ⟨hLsub, hLlex⟩
  have hboxS := hboxL.shadowBox
  rw [IsLexBox, hmon_eq (e + 1) le_rfl, hsh_eq] at hboxS
  exact hboxS.2

/-- Degree-indexed box bound extending `d : Fin c → ℕ` to `Fin n`. -/
def clBound {c : ℕ} (d : Fin c → ℕ) (e : ℕ) (i : Fin n) : ℕ :=
  if h : i.1 < c then d ⟨i.1, h⟩ else e + 2 + ∑ j : Fin c, d j

lemma clBound_pos {c : ℕ} {d : Fin c → ℕ} (hd_pos : ∀ j : Fin c, 1 ≤ d j) (e : ℕ) (i : Fin n) :
    1 ≤ clBound d e i := by
  unfold clBound
  split_ifs with h
  · exact hd_pos ⟨i.1, h⟩
  · omega

lemma clBound_mono {c : ℕ} {d : Fin c → ℕ} (hd : Monotone d) (e : ℕ) :
    Monotone (clBound (n := n) d e) := by
  intro i₁ i₂ hle
  unfold clBound
  by_cases h1 : i₁.1 < c
  · by_cases h2 : i₂.1 < c
    · rw [dif_pos h1, dif_pos h2]
      exact hd (Fin.mk_le_mk.mpr hle)
    · rw [dif_pos h1, dif_neg h2]
      have hle_sum : d ⟨i₁.1, h1⟩ ≤ ∑ j : Fin c, d j :=
        Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ (⟨i₁.1, h1⟩ : Fin c))
      omega
  · by_cases h2 : i₂.1 < c
    · exfalso; exact h1 (lt_of_le_of_lt hle h2)
    · rw [dif_neg h1, dif_neg h2]

/-- Canonical box predicate `∀ j : Fin c, u (castLE hc j) < d j`. -/
def inBoxPred {c : ℕ} (hc : c ≤ n) (d : Fin c → ℕ) (u : Fin n →₀ ℕ) : Prop :=
  ∀ j : Fin c, u (Fin.castLE hc j) < d j

open Classical in
/-- Degree-`e` monomials inside the pure-powers box. -/
noncomputable def boxSlice {c : ℕ} (hc : c ≤ n) (d : Fin c → ℕ) (e : ℕ) : Finset (Fin n →₀ ℕ) :=
  (monOfDeg n e).filter (inBoxPred hc d)

lemma monBox_clBound_eq_boxSlice {c : ℕ} (hc : c ≤ n) (d : Fin c → ℕ) (e d_deg : ℕ)
    (hle : d_deg ≤ e + 1) :
    monBox (clBound (n := n) d e) d_deg = boxSlice hc d d_deg := by
  classical
  ext u
  simp only [mem_monBox, boxSlice, mem_filter, mem_monOfDeg, inBoxPred]
  constructor
  · rintro ⟨hdeg, hlt⟩
    refine ⟨hdeg, fun j => ?_⟩
    have := hlt (Fin.castLE hc j)
    simp only [clBound, Fin.val_castLE, j.isLt, ↓reduceDIte] at this
    exact this
  · rintro ⟨hdeg, hin⟩
    refine ⟨hdeg, fun i => ?_⟩
    unfold clBound
    split_ifs with hi
    · exact hin ⟨i.1, hi⟩
    · have hle_i : u i ≤ u.degree := by
        rw [Finsupp.degree_eq_sum]
        exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
      omega

open Classical in
lemma shadow_filter_inBox_eq_shadowBox {c : ℕ} (hc : c ≤ n) (d : Fin c → ℕ) (e : ℕ)
    {A : Finset (Fin n →₀ ℕ)} (hA : A ⊆ monOfDeg n e) :
    (shadow A).filter (inBoxPred hc d) = shadowBox (clBound (n := n) d e) A := by
  ext v
  simp only [mem_filter, mem_shadowBox, mem_shadow, inBoxPred]
  constructor
  · rintro ⟨⟨w, hw, i, rfl⟩, hin⟩
    refine ⟨⟨w, hw, i, rfl⟩, fun r => ?_⟩
    unfold clBound
    split_ifs with hr
    · exact hin ⟨r.1, hr⟩
    · have hdeg := mem_monOfDeg.mp (hA hw)
      have hle : (w + Finsupp.single i 1 : Fin n →₀ ℕ) r ≤ (w + Finsupp.single i 1).degree := by
        rw [Finsupp.degree_eq_sum]
        exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ r)
      rw [map_add, Finsupp.degree_single, hdeg] at hle
      omega
  · rintro ⟨⟨w, hw, i, rfl⟩, hlt⟩
    refine ⟨⟨w, hw, i, rfl⟩, fun j => ?_⟩
    have := hlt (Fin.castLE hc j)
    simp only [clBound, Fin.val_castLE, j.isLt, ↓reduceDIte] at this
    exact this

open Classical in
/-- Bounded initial monomials of `I` in degree `e`. -/
noncomputable def clBoxInit {c : ℕ} (hc : c ≤ n) (d : Fin c → ℕ)
    (I : Ideal (MvPolynomial (Fin n) k)) (e : ℕ) : Finset (Fin n →₀ ℕ) :=
  (initMons I e).filter (inBoxPred hc d)

/-- Lex segment in `boxSlice hc d e` with the same size as `clBoxInit hc d I e`. -/
noncomputable def clLexBox {c : ℕ} (hc : c ≤ n) (d : Fin c → ℕ)
    (I : Ideal (MvPolynomial (Fin n) k)) (e : ℕ) : Finset (Fin n →₀ ℕ) :=
  lexSegBox (clBound (n := n) d e) e (clBoxInit hc d I e).card

open Classical in
/-- Largest lex set in `monOfDeg n e` whose intersection with `boxSlice hc d e` is `clLexBox`. -/
noncomputable def clLexFull {c : ℕ} (hc : c ≤ n) (d : Fin c → ℕ)
    (I : Ideal (MvPolynomial (Fin n) k)) (e : ℕ) : Finset (Fin n →₀ ℕ) :=
  (monOfDeg n e).filter (fun u => ∀ v ∈ boxSlice hc d e \ clLexBox hc d I e, toLex v < toLex u)

/-- Exponent set of the lex ideal constructed for `I`. -/
def clLexSet {c : ℕ} (hc : c ≤ n) (d : Fin c → ℕ)
    (I : Ideal (MvPolynomial (Fin n) k)) : Set (Fin n →₀ ℕ) :=
  { u | u ∈ clLexFull hc d I u.degree }

lemma mem_clLexSet {c : ℕ} (hc : c ≤ n) (d : Fin c → ℕ)
    (I : Ideal (MvPolynomial (Fin n) k)) (u : Fin n →₀ ℕ) :
    u ∈ clLexSet hc d I ↔ u ∈ clLexFull hc d I u.degree := by
  unfold clLexSet
  exact Iff.of_eq Set.mem_ofPred_eq

/-- Exponent set of `purePowersIdeal hc d`. -/
def clPureSet {c : ℕ} (hc : c ≤ n) (d : Fin c → ℕ) : Set (Fin n →₀ ℕ) :=
  { u : Fin n →₀ ℕ | ∃ j : Fin c, d j ≤ u (Fin.castLE hc j) }

/-- Degree-`e` slice of `clLexSet ∪ clPureSet`. -/
noncomputable def clTotalSlice {c : ℕ} (hc : c ≤ n) (d : Fin c → ℕ)
    (I : Ideal (MvPolynomial (Fin n) k)) (e : ℕ) : Finset (Fin n →₀ ℕ) :=
  clLexBox hc d I e ∪ (monOfDeg n e \ boxSlice hc d e)

lemma clBoxInit_subset {c : ℕ} (hc : c ≤ n) (d : Fin c → ℕ)
    (I : Ideal (MvPolynomial (Fin n) k)) (e : ℕ) :
    clBoxInit hc d I e ⊆ boxSlice hc d e := by
  classical
  intro u hu
  simp only [clBoxInit, boxSlice, mem_filter] at hu ⊢
  exact ⟨initMons_subset I e hu.1, hu.2⟩

lemma clLexBox_subset {c : ℕ} (hc : c ≤ n) (d : Fin c → ℕ)
    (I : Ideal (MvPolynomial (Fin n) k)) (e : ℕ) :
    clLexBox hc d I e ⊆ boxSlice hc d e := by
  rw [← monBox_clBound_eq_boxSlice hc d e e (by omega)]
  exact lexSegBox_subset_monBox (clBound (n := n) d e) e _

lemma clLexBox_card {c : ℕ} (hc : c ≤ n) (d : Fin c → ℕ)
    (I : Ideal (MvPolynomial (Fin n) k)) (e : ℕ) :
    (clLexBox hc d I e).card = (clBoxInit hc d I e).card := by
  apply card_lexSegBox
  rw [monBox_clBound_eq_boxSlice hc d e e (by omega)]
  exact Finset.card_le_card (clBoxInit_subset hc d I e)

open Classical in
lemma clShadow_box {c : ℕ} (hc : c ≤ n) {d : Fin c → ℕ} (hd_pos : ∀ j : Fin c, 1 ≤ d j)
    (hd : Monotone d) (I : Ideal (MvPolynomial (Fin n) k)) (e : ℕ) :
    (shadow (clLexBox hc d I e)).filter (inBoxPred hc d) ⊆ clLexBox hc d I (e + 1) := by
  classical
  have hL_sub_deg : clLexBox hc d I e ⊆ monOfDeg n e :=
    Finset.Subset.trans (clLexBox_subset hc d I e) (Finset.filter_subset _ _)
  have hM_sub_deg : clBoxInit hc d I e ⊆ monOfDeg n e :=
    Finset.Subset.trans (clBoxInit_subset hc d I e) (Finset.filter_subset _ _)
  rw [shadow_filter_inBox_eq_shadowBox hc d e hL_sub_deg]
  have hlex_next : IsLexBox (clBound (n := n) d e) (e + 1) (clLexBox hc d I (e + 1)) := by
    have h1 := isLexBox_lexSegBox (clBound (n := n) d (e + 1)) (e + 1) (clBoxInit hc d I (e + 1)).card
    rw [IsLexBox, monBox_clBound_eq_boxSlice hc d (e + 1) (e + 1) (by omega)] at h1
    rw [IsLexBox, monBox_clBound_eq_boxSlice hc d e (e + 1) le_rfl]
    exact h1
  apply (isLexBox_lexSegBox (clBound (n := n) d e) e _).shadowBox.subset_of_card_le hlex_next
  have hMsub : clBoxInit hc d I e ⊆ monBox (clBound (n := n) d e) e := by
    rw [monBox_clBound_eq_boxSlice hc d e e (by omega)]; exact clBoxInit_subset hc d I e
  have hshM_sub : shadowBox (clBound (n := n) d e) (clBoxInit hc d I e) ⊆ clBoxInit hc d I (e + 1) := by
    rw [← shadow_filter_inBox_eq_shadowBox hc d e hM_sub_deg]
    intro v hv
    rw [mem_filter] at hv
    rw [clBoxInit, mem_filter]
    exact ⟨shadow_initMons_subset I e (shadow_mono (Finset.filter_subset _ _) hv.1), hv.2⟩
  calc (shadowBox (clBound (n := n) d e) (clLexBox hc d I e)).card
      ≤ (shadowBox (clBound (n := n) d e) (clBoxInit hc d I e)).card :=
        clements_lindstrom_shadow n (clBound (n := n) d e) (clBound_pos hd_pos e)
          (clBound_mono hd e) e (clBoxInit hc d I e) hMsub
    _ ≤ (clBoxInit hc d I (e + 1)).card := Finset.card_le_card hshM_sub
    _ = (clLexBox hc d I (e + 1)).card := (clLexBox_card hc d I (e + 1)).symm

lemma clLexFull_inter {c : ℕ} (hc : c ≤ n) (d : Fin c → ℕ)
    (I : Ideal (MvPolynomial (Fin n) k)) (e : ℕ) {u : Fin n →₀ ℕ} (huB : u ∈ boxSlice hc d e) :
    u ∈ clLexFull hc d I e ↔ u ∈ clLexBox hc d I e := by
  classical
  simp only [clLexFull, mem_filter]
  have hu_deg : u ∈ monOfDeg n e := (Finset.mem_filter.mp huB).1
  constructor
  · rintro ⟨_, hgt⟩
    by_contra huL
    exact lt_irrefl _ (hgt u (mem_sdiff.mpr ⟨huB, huL⟩))
  · intro huL
    refine ⟨hu_deg, fun v hv => ?_⟩
    rw [mem_sdiff] at hv
    rcases lt_trichotomy (toLex v) (toLex u) with h | heq | h
    · exact h
    · exfalso; have hvu : v = u := heq; exact hv.2 (hvu ▸ huL)
    · exfalso
      have hlex := isLexBox_lexSegBox (clBound (n := n) d e) e (clBoxInit hc d I e).card
      rw [IsLexBox, monBox_clBound_eq_boxSlice hc d e e (by omega)] at hlex
      exact hv.2 (hlex.2 v hv.1 u huL h)

lemma clShadow_full {c : ℕ} (hc : c ≤ n) {d : Fin c → ℕ} (hd_pos : ∀ j : Fin c, 1 ≤ d j)
    (hd : Monotone d) (I : Ideal (MvPolynomial (Fin n) k)) (e : ℕ) :
    shadow (clLexFull hc d I e) ⊆ clLexFull hc d I (e + 1) := by
  classical
  have hsub : clLexFull hc d I e ⊆ monOfDeg n e := Finset.filter_subset _ _
  have hlex : ∀ u ∈ monOfDeg n e, ∀ v ∈ clLexFull hc d I e, toLex v < toLex u →
      u ∈ clLexFull hc d I e := by
    intro u hu v hv hlt
    rw [clLexFull, mem_filter] at hv ⊢
    exact ⟨hu, fun w hw => lt_trans (hv.2 w hw) hlt⟩
  intro x hx
  have hx_deg : x ∈ monOfDeg n (e + 1) := shadow_subset_monOfDeg hsub hx
  by_contra hx_n
  simp only [clLexFull, mem_filter, hx_deg, true_and, not_forall, not_lt] at hx_n
  obtain ⟨v, hv_sdiff, hxv⟩ := hx_n
  rw [mem_sdiff] at hv_sdiff
  obtain ⟨hvB, hvL⟩ := hv_sdiff
  have hv_deg : v ∈ monOfDeg n (e + 1) := (Finset.mem_filter.mp hvB).1
  have hv_sh : v ∈ shadow (clLexFull hc d I e) := by
    rcases eq_or_lt_of_le hxv with h | h
    · have : x = v := h; rwa [← this]
    · exact isLexFull_shadow hsub hlex v hv_deg x hx h
  rw [mem_shadow] at hv_sh
  obtain ⟨w, hw, i, hw_eq⟩ := hv_sh
  have hw_inBox : inBoxPred hc d w := by
    intro j
    have hv_in := (Finset.mem_filter.mp hvB).2 j
    have hle : w (Fin.castLE hc j) ≤ v (Fin.castLE hc j) := by
      rw [← hw_eq]; simp
    omega
  have hwB : w ∈ boxSlice hc d e := Finset.mem_filter.mpr ⟨hsub hw, hw_inBox⟩
  have hwL : w ∈ clLexBox hc d I e := (clLexFull_inter hc d I e hwB).mp hw
  have hv_in_sh : v ∈ (shadow (clLexBox hc d I e)).filter (inBoxPred hc d) :=
    Finset.mem_filter.mpr ⟨mem_shadow.mpr ⟨w, hwL, i, hw_eq⟩, (Finset.mem_filter.mp hvB).2⟩
  exact hvL (clShadow_box hc hd_pos hd I e hv_in_sh)

lemma clInit_eq {c : ℕ} (hc : c ≤ n) (d : Fin c → ℕ)
    (I : Ideal (MvPolynomial (Fin n) k)) (hIp : purePowersIdeal hc d ≤ I) (e : ℕ) :
    initMons I e = clBoxInit hc d I e ∪ (monOfDeg n e \ boxSlice hc d e) := by
  classical
  ext u
  simp only [clBoxInit, boxSlice, mem_union, mem_filter, mem_sdiff]
  constructor
  · intro hu
    by_cases hin : inBoxPred hc d u
    · exact Or.inl ⟨hu, hin⟩
    · exact Or.inr ⟨initMons_subset I e hu, fun h => hin h.2⟩
  · rintro (⟨hu, _⟩ | ⟨hu_deg, hnot⟩)
    · exact hu
    · rw [mem_initMons]
      refine ⟨hu_deg, monomial u (1 : k), ⟨?_, ?_⟩, monomial_eq_zero.not.mpr one_ne_zero, ?_⟩
      · apply hIp
        rw [purePowersIdeal_eq_monomialIdeal]
        apply Ideal.subset_span
        refine ⟨u, ?_, rfl⟩
        have hnot' : ¬ inBoxPred hc d u := fun hin => hnot ⟨hu_deg, hin⟩
        unfold inBoxPred at hnot'
        push Not at hnot'
        exact hnot'
      · change monomial u (1 : k) ∈ homogeneousSubmodule (Fin n) k e
        rw [mem_homogeneousSubmodule]
        intro v hv
        rw [coeff_monomial] at hv
        split_ifs at hv with hvu
        · subst hvu
          rw [weight_one_eq_degree]
          exact mem_monOfDeg.mp hu_deg
        · exact absurd rfl hv
      · have hsupp := lm_mem_support (f := monomial u (1 : k))
          (monomial_eq_zero.not.mpr one_ne_zero)
        rw [MvPolynomial.support_monomial, if_neg one_ne_zero, Finset.mem_singleton] at hsupp
        exact hsupp

theorem clements_lindstrom_main {c : ℕ} (hc : c ≤ n) (d : Fin c → ℕ)
    (hd : Monotone d) (I : Ideal (MvPolynomial (Fin n) k))
    (hIp : purePowersIdeal hc d ≤ I) :
    ∃ L : Ideal (MvPolynomial (Fin n) k), IsLexIdeal L ∧
      ∀ e, hilbertFunction I e = hilbertFunction (L + purePowersIdeal hc d) e := by
  classical
  by_cases hzero : ∃ j : Fin c, d j = 0
  · obtain ⟨j, hj⟩ := hzero
    have h1I : (1 : MvPolynomial (Fin n) k) ∈ I := by
      apply hIp
      have hgen : (X (Fin.castLE hc j) : MvPolynomial (Fin n) k) ^ d j ∈ purePowersIdeal hc d :=
        Ideal.subset_span ⟨j, rfl⟩
      simpa [hj] using hgen
    have hItop : I = ⊤ := Ideal.eq_top_of_isUnit_mem I h1I isUnit_one
    refine ⟨⊤, isLexIdeal_top, fun e => ?_⟩
    have htop : (⊤ : Ideal (MvPolynomial (Fin n) k)) + purePowersIdeal hc d = ⊤ :=
      top_sup_eq _
    rw [hItop, htop]
  · push Not at hzero
    have hd_pos : ∀ j : Fin c, 1 ≤ d j := fun j => Nat.pos_of_ne_zero (hzero j)
    have hSL_closed : ∀ u ∈ clLexSet hc d I, ∀ i : Fin n, u + Finsupp.single i 1 ∈ clLexSet hc d I := by
      intro u hu i
      rw [mem_clLexSet, map_add, Finsupp.degree_single]
      exact clShadow_full hc hd_pos hd I u.degree (mem_shadow.mpr ⟨u, (mem_clLexSet hc d I u).mp hu, i, rfl⟩)
    refine ⟨Ideal.span ((fun u => monomial u (1 : k)) '' clLexSet hc d I),
      ⟨⟨clLexSet hc d I, rfl⟩, ?_⟩, ?_⟩
    · intro u v huv hlt hvL
      rw [mem_monomialIdeal_iff_support hSL_closed] at hvL ⊢
      intro w hw
      rw [MvPolynomial.support_monomial, if_neg one_ne_zero, Finset.mem_singleton] at hw
      rw [hw]
      have hvS : v ∈ clLexFull hc d I v.degree := (mem_clLexSet hc d I v).mp (hvL v (by
        rw [MvPolynomial.support_monomial, if_neg one_ne_zero, Finset.mem_singleton]))
      rw [mem_clLexSet, huv, clLexFull, mem_filter]
      exact ⟨mem_monOfDeg.mpr huv, fun x hx =>
        lt_trans ((Finset.mem_filter.mp hvS).2 x hx) hlt⟩
    · have hT_deg : ∀ e, clTotalSlice hc d I e ⊆ monOfDeg n e := fun e u hu => by
        rw [clTotalSlice, mem_union] at hu
        rcases hu with h | h
        · exact (Finset.mem_filter.mp (clLexBox_subset hc d I e h)).1
        · exact (mem_sdiff.mp h).1
      have hT_iff : ∀ u, u ∈ clLexSet hc d I ∪ clPureSet hc d ↔ u ∈ clTotalSlice hc d I u.degree := by
        intro u
        have hu_deg : u ∈ monOfDeg n u.degree := mem_monOfDeg.mpr rfl
        simp only [Set.mem_union, clTotalSlice, mem_union, mem_sdiff]
        by_cases hin : inBoxPred hc d u
        · have huB : u ∈ boxSlice hc d u.degree := Finset.mem_filter.mpr ⟨hu_deg, hin⟩
          have huSP : u ∉ clPureSet hc d := by
            rintro ⟨j, hj⟩; have := hin j; omega
          simp only [huSP, or_false, huB, not_true_eq_false, and_false]
          rw [mem_clLexSet]
          exact clLexFull_inter hc d I u.degree huB
        · have huB : u ∉ boxSlice hc d u.degree := fun h => hin (Finset.mem_filter.mp h).2
          have huSP : u ∈ clPureSet hc d := by
            unfold inBoxPred at hin; push Not at hin; exact hin
          simp only [huSP, or_true, hu_deg, huB, not_false_eq_true, and_self]
      have hT_shadow : ∀ e, shadow (clTotalSlice hc d I e) ⊆ clTotalSlice hc d I (e + 1) := by
        intro e v hv
        rw [mem_shadow] at hv
        obtain ⟨u, hu, i, rfl⟩ := hv
        have hv_deg : (u + Finsupp.single i 1).degree = e + 1 := by
          rw [map_add, Finsupp.degree_single, mem_monOfDeg.mp (hT_deg e hu)]
        rw [← hv_deg, ← hT_iff]
        have hu' : u ∈ clLexSet hc d I ∪ clPureSet hc d :=
          (hT_iff u).mpr (by rw [mem_monOfDeg.mp (hT_deg e hu)]; exact hu)
        rcases hu' with huSL | ⟨j, hj⟩
        · exact Or.inl (hSL_closed u huSL i)
        · refine Or.inr ⟨j, ?_⟩
          simp only [Finsupp.coe_add, Pi.add_apply]; omega
      have hsum_eq : Ideal.span ((fun u => monomial u (1 : k)) '' clLexSet hc d I) +
            purePowersIdeal hc d =
          Ideal.span ((fun u => monomial u (1 : k)) '' (clLexSet hc d I ∪ clPureSet hc d)) := by
        have hp : (purePowersIdeal hc d : Ideal (MvPolynomial (Fin n) k)) =
            Ideal.span ((fun u => monomial u (1 : k)) '' clPureSet hc d) :=
          purePowersIdeal_eq_monomialIdeal hc d
        rw [hp, Submodule.add_eq_sup, ← Ideal.span_union, Set.image_union]
      intro e
      have hhilb_rhs : hilbertFunction
          (Ideal.span ((fun u => monomial u (1 : k)) '' (clLexSet hc d I ∪ clPureSet hc d))) e =
          (clTotalSlice hc d I e).card :=
        hilbertFunction_monomialIdeal hT_iff hT_deg hT_shadow e
      have hhilb_lhs : (initMons I e).card = hilbertFunction I e :=
        card_initMons_eq_hilbertFunction I e
      have hdisj1 : Disjoint (clBoxInit hc d I e) (monOfDeg n e \ boxSlice hc d e) :=
        Finset.disjoint_left.mpr fun x h1 h2 => (mem_sdiff.mp h2).2 (clBoxInit_subset hc d I e h1)
      have hdisj2 : Disjoint (clLexBox hc d I e) (monOfDeg n e \ boxSlice hc d e) :=
        Finset.disjoint_left.mpr fun x h1 h2 => (mem_sdiff.mp h2).2 (clLexBox_subset hc d I e h1)
      have hcard_eq : (initMons I e).card = (clTotalSlice hc d I e).card := by
        rw [clInit_eq hc d I hIp e, clTotalSlice,
          Finset.card_union_of_disjoint hdisj1, Finset.card_union_of_disjoint hdisj2,
          clLexBox_card hc d I e]
      rw [hsum_eq, hhilb_rhs, ← hhilb_lhs, hcard_eq]

end IdealPart

end ClementsLindstromProof

theorem OMA.solution :
    type_of% @EisenbudGreenHarris.eisenbud_green_harris.variants.clements_lindstrom :=
  fun {_ _ _ _} hc d hd I _ hIp => ClementsLindstromProof.clements_lindstrom_main hc d hd I hIp

