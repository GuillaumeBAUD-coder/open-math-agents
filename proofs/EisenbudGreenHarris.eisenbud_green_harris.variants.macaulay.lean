import FormalConjectures.Paper.EisenbudGreenHarris
import Mathlib.Data.Finsupp.Lex

/-!
# Macaulay's Theorem

Proof of `EisenbudGreenHarris.eisenbud_green_harris.variants.macaulay`:
every homogeneous ideal in `k[x₁, ..., xₙ]` has the same Hilbert function as a lex ideal.
-/

-- Problem: Macaulay's theorem
-- Upstream: formal-conjectures FormalConjectures/Paper/EisenbudGreenHarris.lean:108 (declaration EisenbudGreenHarris.eisenbud_green_harris.variants.macaulay)
-- Credit: @Dugongue (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

namespace MacaulayProof

open MvPolynomial Finset

/- Part 1: Monomials of fixed degree, lex order, and upward shadow -/

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

/-- The upward shadow of a set of exponent vectors: multiplying by each variable `x_i`. -/
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

lemma shadow_empty {n : ℕ} : shadow (∅ : Finset (Fin n →₀ ℕ)) = ∅ := by
  simp [shadow]

/- Part 2: Lex-initial segments and closure of shadow -/

/-- A subset of `monOfDeg n e` that is upward-closed in `toLex`. -/
def IsLexSet (n e : ℕ) (M : Finset (Fin n →₀ ℕ)) : Prop :=
  M ⊆ monOfDeg n e ∧ ∀ u ∈ monOfDeg n e, ∀ v ∈ M, toLex v < toLex u → u ∈ M

/-- The top `r` monomials of degree `e` in `n` variables under `toLex`. -/
noncomputable def lexSeg (n e r : ℕ) : Finset (Fin n →₀ ℕ) :=
  ((((monOfDeg n e).image toLex).sort (· ≤ ·)).reverse.take r).toFinset.image ofLex

lemma lexSeg_subset_monOfDeg (n e r : ℕ) : lexSeg n e r ⊆ monOfDeg n e := by
  intro u hu
  simp only [lexSeg, mem_image, List.mem_toFinset] at hu
  obtain ⟨x, hx, rfl⟩ := hu
  have hx' : x ∈ ((monOfDeg n e).image toLex).sort (· ≤ ·) :=
    List.mem_reverse.mp (List.mem_of_mem_take hx)
  rw [Finset.mem_sort, mem_image] at hx'
  obtain ⟨w, hw, hw'⟩ := hx'
  have : ofLex x = w := by rw [← hw']; rfl
  rwa [this]

lemma card_lexSeg {n e r : ℕ} (hr : r ≤ (monOfDeg n e).card) :
    (lexSeg n e r).card = r := by
  have hinj : Function.Injective (ofLex : Lex (Fin n →₀ ℕ) → (Fin n →₀ ℕ)) := fun _ _ h => h
  rw [lexSeg, Finset.card_image_of_injective _ hinj]
  set l := ((monOfDeg n e).image toLex).sort (· ≤ ·)
  have hnodup : (l.reverse.take r).Nodup :=
    (List.nodup_reverse.mpr (Finset.sort_nodup _ _)).take
  rw [List.toFinset_card_of_nodup hnodup, List.length_take, List.length_reverse]
  have hlen : l.length = (monOfDeg n e).card := by
    rw [Finset.length_sort, Finset.card_image_of_injective _ toLex.injective]
  omega

lemma isLexSet_lexSeg (n e r : ℕ) : IsLexSet n e (lexSeg n e r) := by
  refine ⟨lexSeg_subset_monOfDeg n e r, ?_⟩
  intro u hu v hv hlt
  set l := ((monOfDeg n e).image toLex).sort (· ≤ ·)
  have hl_pair : l.reverse.Pairwise (fun a b : Lex (Fin n →₀ ℕ) => b ≤ a) := by
    rw [List.pairwise_reverse]
    exact Finset.pairwise_sort _ _
  simp only [lexSeg, mem_image, List.mem_toFinset] at hv ⊢
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

lemma IsLexSet.total_subset {n e : ℕ} {A B : Finset (Fin n →₀ ℕ)}
    (hA : IsLexSet n e A) (hB : IsLexSet n e B) : A ⊆ B ∨ B ⊆ A := by
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

lemma IsLexSet.subset_of_card_le {n e : ℕ} {A B : Finset (Fin n →₀ ℕ)}
    (hA : IsLexSet n e A) (hB : IsLexSet n e B) (hc : A.card ≤ B.card) : A ⊆ B := by
  rcases hA.total_subset hB with h | h
  · exact h
  · exact (Finset.eq_of_subset_of_card_le h hc).symm.subset

lemma IsLexSet.eq_of_card_eq {n e : ℕ} {A B : Finset (Fin n →₀ ℕ)}
    (hA : IsLexSet n e A) (hB : IsLexSet n e B) (hc : A.card = B.card) : A = B :=
  Finset.Subset.antisymm (hA.subset_of_card_le hB hc.le) (hB.subset_of_card_le hA hc.ge)

lemma IsLexSet.eq_lexSeg {n e : ℕ} {A : Finset (Fin n →₀ ℕ)} (hA : IsLexSet n e A) :
    A = lexSeg n e A.card :=
  hA.eq_of_card_eq (isLexSet_lexSeg n e A.card)
    (card_lexSeg (Finset.card_le_card hA.1)).symm

lemma IsLexSet.card_union {n e : ℕ} {A B : Finset (Fin n →₀ ℕ)}
    (hA : IsLexSet n e A) (hB : IsLexSet n e B) :
    (A ∪ B).card = max A.card B.card := by
  rcases hA.total_subset hB with h | h
  · rw [Finset.union_eq_right.mpr h, max_eq_right (Finset.card_le_card h)]
  · rw [Finset.union_eq_left.mpr h, max_eq_left (Finset.card_le_card h)]

/-- Helper: subtract `single s 1` from `u` when `1 ≤ u s`. -/
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

/-- The upward shadow of a lex set is again a lex set. -/
lemma IsLexSet.shadow {n e : ℕ} {L : Finset (Fin n →₀ ℕ)} (hL : IsLexSet n e L) :
    IsLexSet n (e + 1) (shadow L) := by
  refine ⟨shadow_subset_monOfDeg hL.1, ?_⟩
  intro u hu v hv hlt
  rw [mem_shadow] at hv ⊢
  obtain ⟨w, hw, r, rfl⟩ := hv
  rw [lex_lt_iff] at hlt
  obtain ⟨j, hjeq, hjlt⟩ := hlt
  have hdeg_u : u.degree = e + 1 := mem_monOfDeg.mp hu
  have hdeg_w : w.degree = e := mem_monOfDeg.mp (hL.1 hw)
  by_cases hrj : r < j
  · have hur : 1 ≤ u r := by
      have := hjeq r hrj
      simp only [Finsupp.coe_add, Pi.add_apply, Finsupp.single_eq_same] at this
      omega
    refine ⟨u - Finsupp.single r 1, ?_, r, sub_single_add_single hur⟩
    have hw'_deg : (u - Finsupp.single r 1).degree = e := by
      have := degree_sub_single hur; omega
    apply hL.2 _ (mem_monOfDeg.mpr hw'_deg) w hw
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
    have hw'_deg : (u - Finsupp.single s 1).degree = e := by
      have := degree_sub_single hs_pos; omega
    refine ⟨u - Finsupp.single s 1, ?_, s, sub_single_add_single hs_pos⟩
    rcases lt_or_eq_of_le hjs with hlt_js | hjeqs
    · apply hL.2 _ (mem_monOfDeg.mpr hw'_deg) w hw
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
    · rw [← hjeqs] at hw'_deg hs_pos ⊢
      set u' : Fin n →₀ ℕ := u - Finsupp.single j 1
      have hu'_apply : ∀ i : Fin n, u' i = u i - (if j = i then 1 else 0) := fun i => by
        simp [u', Finsupp.single_apply]
      have hlt_w_le : w j ≤ u' j := by
        have h1 := hu'_apply j
        simp only [ite_true] at h1
        simp only [Finsupp.coe_add, Pi.add_apply] at hjlt
        omega
      rcases lt_or_eq_of_le hlt_w_le with hj_strict | hj_eq_w
      · apply hL.2 _ (mem_monOfDeg.mpr hw'_deg) w hw
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
            rw [← Finsupp.degree_eq_sum, ← Finsupp.degree_eq_sum, hw'_deg, hdeg_w]
          ext i
          by_contra hne
          have hlt_i : u' i < w i := lt_of_le_of_ne (hle_all i) hne
          have hsum_lt := Finset.sum_lt_sum (fun x _ => hle_all x) ⟨i, Finset.mem_univ i, hlt_i⟩
          omega
        rwa [hw_eq]

/- Part 3: Coordinate deletion/insertion, slicing, and compression -/

/-- Delete coordinate `i` from an exponent vector in `m + 1` variables. -/
noncomputable def deleteCoord {m : ℕ} (i : Fin (m + 1)) (u : Fin (m + 1) →₀ ℕ) : Fin m →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun j : Fin m => u (i.succAbove j))

/-- Insert value `a` at coordinate `i` into an exponent vector in `m` variables. -/
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

lemma slice_subset_monOfDeg {m e : ℕ} {i : Fin (m + 1)} {a : ℕ}
    {M : Finset (Fin (m + 1) →₀ ℕ)} (hM : M ⊆ monOfDeg (m + 1) e) :
    slice i a M ⊆ monOfDeg m (e - a) := by
  intro w hw
  rw [mem_slice] at hw
  have hdeg := mem_monOfDeg.mp (hM hw)
  rw [degree_insertCoord] at hdeg
  rw [mem_monOfDeg]
  omega

lemma card_eq_sum_card_slice {m e : ℕ} (i : Fin (m + 1)) {M : Finset (Fin (m + 1) →₀ ℕ)}
    (hM : M ⊆ monOfDeg (m + 1) e) :
    M.card = ∑ a ∈ Finset.range (e + 1), (slice i a M).card := by
  have hdisj : M = (Finset.range (e + 1)).biUnion (fun a => M.filter (fun u => u i = a)) := by
    ext u
    simp only [mem_biUnion, mem_range, mem_filter]
    constructor
    · intro hu
      refine ⟨u i, ?_, hu, rfl⟩
      have hdeg := mem_monOfDeg.mp (hM hu)
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

lemma slice_shadow {m : ℕ} (i : Fin (m + 1)) (a : ℕ) (M : Finset (Fin (m + 1) →₀ ℕ)) :
    slice i a (shadow M) =
      shadow (slice i a M) ∪ (if 0 < a then slice i (a - 1) M else ∅) := by
  ext w
  simp only [mem_slice, mem_shadow, mem_union]
  constructor
  · rintro ⟨u, hu, k, hk⟩
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
      refine ⟨deleteCoord i u, ?_, j, ?_⟩
      · rw [← hui, insertCoord_deleteCoord]; exact hu
      · ext r
        have := congrArg (fun f : Fin (m + 1) →₀ ℕ => f (i.succAbove r)) hk
        by_cases hrj : j = r
        · subst hrj; simpa using this
        · have hne : i.succAbove j ≠ i.succAbove r :=
            fun h => hrj (Fin.succAbove_right_injective h)
          simpa [hne, hrj] using this
  · rintro (⟨u', hu', j, rfl⟩ | hw)
    · exact ⟨insertCoord i a u', hu', i.succAbove j, insertCoord_add_single_succAbove i a u' j⟩
    · split_ifs at hw with ha
      · rw [mem_slice] at hw
        refine ⟨insertCoord i (a - 1) w, hw, i, ?_⟩
        rw [insertCoord_add_single_same, Nat.sub_add_cancel ha]
      · simp at hw

/-- `M` is `i`-compressed if every slice in coordinate `i` is a lex set. -/
def IsCompressed {m : ℕ} (i : Fin (m + 1)) (e : ℕ) (M : Finset (Fin (m + 1) →₀ ℕ)) : Prop :=
  ∀ u ∈ monOfDeg (m + 1) e, ∀ v ∈ M, u i = v i → toLex v < toLex u → u ∈ M

/-- Replace every `i`-slice of `M` by the lex-initial segment of the same cardinality. -/
noncomputable def compress {m : ℕ} (i : Fin (m + 1)) (e : ℕ) (M : Finset (Fin (m + 1) →₀ ℕ)) :
    Finset (Fin (m + 1) →₀ ℕ) :=
  (Finset.range (e + 1)).biUnion
    (fun a => (lexSeg m (e - a) (slice i a M).card).image (insertCoord i a))

lemma mem_compress {m : ℕ} {i : Fin (m + 1)} {e : ℕ} {M : Finset (Fin (m + 1) →₀ ℕ)}
    {u : Fin (m + 1) →₀ ℕ} :
    u ∈ compress i e M ↔ u i ≤ e ∧ deleteCoord i u ∈ lexSeg m (e - u i) (slice i (u i) M).card := by
  simp only [compress, mem_biUnion, mem_range, mem_image]
  constructor
  · rintro ⟨a, ha, w, hw, rfl⟩
    rw [insertCoord_apply_same, deleteCoord_insertCoord]
    exact ⟨by omega, hw⟩
  · rintro ⟨hle, hw⟩
    exact ⟨u i, by omega, deleteCoord i u, hw, insertCoord_deleteCoord i u⟩

lemma slice_compress {m : ℕ} (i : Fin (m + 1)) (e a : ℕ) (M : Finset (Fin (m + 1) →₀ ℕ))
    (ha : a ≤ e) :
    slice i a (compress i e M) = lexSeg m (e - a) (slice i a M).card := by
  ext w
  rw [mem_slice, mem_compress, insertCoord_apply_same, deleteCoord_insertCoord]
  exact and_iff_right ha

lemma compress_subset_monOfDeg {m : ℕ} (i : Fin (m + 1)) (e : ℕ)
    (M : Finset (Fin (m + 1) →₀ ℕ)) :
    compress i e M ⊆ monOfDeg (m + 1) e := by
  intro u hu
  rw [mem_compress] at hu
  have hdeg := mem_monOfDeg.mp (lexSeg_subset_monOfDeg m (e - u i) _ hu.2)
  rw [mem_monOfDeg, ← degree_deleteCoord i u, hdeg]
  omega

lemma card_compress {m : ℕ} (i : Fin (m + 1)) (e : ℕ) {M : Finset (Fin (m + 1) →₀ ℕ)}
    (hM : M ⊆ monOfDeg (m + 1) e) :
    (compress i e M).card = M.card := by
  rw [card_eq_sum_card_slice i (compress_subset_monOfDeg i e M), card_eq_sum_card_slice i hM]
  refine Finset.sum_congr rfl fun a ha => ?_
  rw [mem_range] at ha
  rw [slice_compress i e a M (by omega)]
  exact card_lexSeg (Finset.card_le_card (slice_subset_monOfDeg hM))

/-- Lex rank of a monomial in `monOfDeg n e`: `0` for the largest lex monomial. -/
noncomputable def lexRank (n e : ℕ) (u : Fin n →₀ ℕ) : ℕ :=
  ((monOfDeg n e).filter (fun w => toLex u < toLex w)).card

lemma lexRank_lt_of_lt {n e : ℕ} {u v : Fin n →₀ ℕ} (hu : u ∈ monOfDeg n e)
    (hlt : toLex v < toLex u) :
    lexRank n e u < lexRank n e v := by
  apply Finset.card_lt_card
  rw [Finset.ssubset_iff_of_subset]
  · exact ⟨u, Finset.mem_filter.mpr ⟨hu, hlt⟩, by simp⟩
  · intro w hw
    simp only [mem_filter] at hw ⊢
    exact ⟨hw.1, lt_trans hlt hw.2⟩

/-- Total lex rank sum of a set of monomials. -/
noncomputable def lexRankSum (n e : ℕ) (M : Finset (Fin n →₀ ℕ)) : ℕ :=
  ∑ u ∈ M, lexRank n e u

lemma lexRankSum_slice_le {m e : ℕ} (i : Fin (m + 1)) (a : ℕ) (ha : a ≤ e)
    {S : Finset (Fin m →₀ ℕ)} (hS : S ⊆ monOfDeg m (e - a)) :
    lexRankSum (m + 1) e ((lexSeg m (e - a) S.card).image (insertCoord i a)) ≤
      lexRankSum (m + 1) e (S.image (insertCoord i a)) ∧
    (lexSeg m (e - a) S.card ≠ S →
      lexRankSum (m + 1) e ((lexSeg m (e - a) S.card).image (insertCoord i a)) <
        lexRankSum (m + 1) e (S.image (insertCoord i a))) := by
  set L := lexSeg m (e - a) S.card
  have hLcard : L.card = S.card := card_lexSeg (Finset.card_le_card hS)
  have hLsub : L ⊆ monOfDeg m (e - a) := lexSeg_subset_monOfDeg m (e - a) S.card
  have hLlex : IsLexSet m (e - a) L := isLexSet_lexSeg m (e - a) S.card
  have hEq : ∀ A : Finset (Fin m →₀ ℕ),
      lexRankSum (m + 1) e (A.image (insertCoord i a)) =
        ∑ w ∈ A, lexRank (m + 1) e (insertCoord i a w) := fun A => by
    rw [lexRankSum, Finset.sum_image (fun x _ y _ h => insertCoord_injective i a h)]
  rw [hEq L, hEq S]
  have hsplit : ∀ A B : Finset (Fin m →₀ ℕ),
      ∑ w ∈ A, lexRank (m + 1) e (insertCoord i a w) =
        (∑ w ∈ A ∩ B, lexRank (m + 1) e (insertCoord i a w)) +
        (∑ w ∈ A \ B, lexRank (m + 1) e (insertCoord i a w)) := fun A B => by
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
      lexRank (m + 1) e (insertCoord i a x) < lexRank (m + 1) e (insertCoord i a y) := by
    intro x hx y hy
    rw [mem_sdiff] at hx hy
    have hlt : toLex y < toLex x := by
      rcases lt_trichotomy (toLex y) (toLex x) with h | heq | h
      · exact h
      · exfalso
        have hyx : y = x := heq
        exact hy.2 (hyx ▸ hx.1)
      · exfalso; exact hy.2 (hLlex.2 y (hS hy.1) x hx.1 h)
    apply lexRank_lt_of_lt
    · rw [mem_monOfDeg, degree_insertCoord, mem_monOfDeg.mp (hLsub hx.1)]; omega
    · exact (toLex_insertCoord_lt_iff i a y x).mpr hlt
  have hlt_or_eq : (L \ S = ∅ ∧ S \ L = ∅) ∨
      ∑ w ∈ L \ S, lexRank (m + 1) e (insertCoord i a w) <
        ∑ w ∈ S \ L, lexRank (m + 1) e (insertCoord i a w) := by
    by_cases hne : (L \ S).Nonempty
    · right
      have hne2 : (S \ L).Nonempty := Finset.card_pos.mp (hdiff_card ▸ hne.card_pos)
      obtain ⟨x₀, hx₀, hx₀_max⟩ :=
        Finset.exists_max_image (L \ S) (fun w => lexRank (m + 1) e (insertCoord i a w)) hne
      obtain ⟨y₀, hy₀, hy₀_min⟩ :=
        Finset.exists_min_image (S \ L) (fun w => lexRank (m + 1) e (insertCoord i a w)) hne2
      have h1 : ∑ w ∈ L \ S, lexRank (m + 1) e (insertCoord i a w) ≤
          (L \ S).card * lexRank (m + 1) e (insertCoord i a x₀) := by
        simpa using Finset.sum_le_card_nsmul (L \ S) _ _ (fun w hw => hx₀_max w hw)
      have h2 : (S \ L).card * lexRank (m + 1) e (insertCoord i a y₀) ≤
          ∑ w ∈ S \ L, lexRank (m + 1) e (insertCoord i a w) := by
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

lemma lexRankSum_compress_lt {m e : ℕ} (i : Fin (m + 1)) {M : Finset (Fin (m + 1) →₀ ℕ)}
    (hM : M ⊆ monOfDeg (m + 1) e) (hnc : ¬ IsCompressed i e M) :
    lexRankSum (m + 1) e (compress i e M) < lexRankSum (m + 1) e M := by
  have hdecomp : ∀ A : Finset (Fin (m + 1) →₀ ℕ), A ⊆ monOfDeg (m + 1) e →
      lexRankSum (m + 1) e A =
        ∑ a ∈ Finset.range (e + 1), lexRankSum (m + 1) e ((slice i a A).image (insertCoord i a)) := by
    intro A hA
    have hEq : A = (Finset.range (e + 1)).biUnion (fun a => (slice i a A).image (insertCoord i a)) := by
      ext u
      simp only [mem_biUnion, mem_range, mem_image, mem_slice]
      constructor
      · intro hu
        have hdeg := mem_monOfDeg.mp (hA hu)
        have hle : u i ≤ u.degree := by
          rw [Finsupp.degree_eq_sum]
          exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
        exact ⟨u i, by omega, deleteCoord i u, by rwa [insertCoord_deleteCoord],
          insertCoord_deleteCoord i u⟩
      · rintro ⟨a, _, w, hw, rfl⟩; exact hw
    conv_lhs => rw [lexRankSum, hEq]
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
  rw [hdecomp (compress i e M) (compress_subset_monOfDeg i e M), hdecomp M hM]
  have hex : ∃ a ∈ Finset.range (e + 1), lexSeg m (e - a) (slice i a M).card ≠ slice i a M := by
    unfold IsCompressed at hnc
    push Not at hnc
    obtain ⟨u, hu, v, hv, huv_i, hlt, huM⟩ := hnc
    have ha : v i ∈ Finset.range (e + 1) := by
      rw [mem_range]
      have hdeg := mem_monOfDeg.mp (hM hv)
      have hle : v i ≤ v.degree := by
        rw [Finsupp.degree_eq_sum]
        exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
      omega
    refine ⟨v i, ha, fun heq => huM ?_⟩
    have hlex : IsLexSet m (e - v i) (slice i (v i) M) := heq ▸ isLexSet_lexSeg m (e - v i) _
    have hdv : deleteCoord i v ∈ slice i (v i) M := by
      rw [mem_slice, insertCoord_deleteCoord]; exact hv
    have hdu_deg : deleteCoord i u ∈ monOfDeg m (e - v i) := by
      rw [mem_monOfDeg]
      have h1 := degree_deleteCoord i u
      have h2 := mem_monOfDeg.mp hu
      omega
    have hlt_d : toLex (deleteCoord i v) < toLex (deleteCoord i u) := by
      rw [← toLex_insertCoord_lt_iff i (v i), insertCoord_deleteCoord, ← huv_i,
        insertCoord_deleteCoord]
      exact hlt
    have hdu_mem := hlex.2 (deleteCoord i u) hdu_deg (deleteCoord i v) hdv hlt_d
    rw [mem_slice, ← huv_i, insertCoord_deleteCoord] at hdu_mem
    exact hdu_mem
  apply Finset.sum_lt_sum
  · intro a ha
    rw [mem_range] at ha
    rw [slice_compress i e a M (by omega)]
    exact (lexRankSum_slice_le i a (by omega) (slice_subset_monOfDeg hM)).1
  · obtain ⟨a, ha, hne⟩ := hex
    rw [mem_range] at ha
    refine ⟨a, Finset.mem_range.mpr ha, ?_⟩
    rw [slice_compress i e a M (by omega)]
    exact (lexRankSum_slice_le i a (by omega) (slice_subset_monOfDeg hM)).2 hne

/- Part 4: Macaulay's Shadow Inequality -/

lemma macaulay_shadow_two (e : ℕ) (M : Finset (Fin 2 →₀ ℕ)) (hM : M ⊆ monOfDeg 2 e) :
    (shadow (lexSeg 2 e M.card)).card ≤ (shadow M).card := by
  by_cases hne : M.Nonempty
  · set L := lexSeg 2 e M.card
    have hLlex : IsLexSet 2 e L := isLexSet_lexSeg 2 e M.card
    have hLcard : L.card = M.card := card_lexSeg (Finset.card_le_card hM)
    have hLne : L.Nonempty := Finset.card_pos.mp (hLcard ▸ hne.card_pos)
    obtain ⟨u_min, hu_min, hu_min_le⟩ := Finset.exists_min_image L toLex hLne
    have hsubL : shadow L ⊆ L.image (· + Finsupp.single 0 1) ∪ {u_min + Finsupp.single 1 1} := by
      intro v hv
      rw [mem_shadow] at hv
      obtain ⟨u, hu, i, rfl⟩ := hv
      fin_cases i
      · exact Finset.mem_union_left _ (Finset.mem_image_of_mem _ hu)
      · by_cases heq : u = u_min
        · subst heq
          exact Finset.mem_union_right _ (Finset.mem_singleton_self _)
        · apply Finset.mem_union_left
          rw [mem_image]
          have hlt_u : toLex u_min < toLex u :=
            lt_of_le_of_ne (hu_min_le u hu) (fun h => heq h.symm)
          have hdu := mem_monOfDeg.mp (hLlex.1 hu)
          have hdm := mem_monOfDeg.mp (hLlex.1 hu_min)
          rw [Finsupp.degree_eq_sum, Fin.sum_univ_two] at hdu hdm
          have hu0_gt : u_min 0 < u 0 := by
            rw [lex_lt_iff] at hlt_u
            obtain ⟨j, hjeq, hjlt⟩ := hlt_u
            fin_cases j
            · exact hjlt
            · have h0 := hjeq 0 (by decide)
              have hjlt' : u_min 1 < u 1 := hjlt
              omega
          have hu0_pos : 1 ≤ u 0 := by omega
          set w := (u - Finsupp.single 0 1) + Finsupp.single 1 1
          have hw0 : w 0 = u 0 - 1 := by simp [w]
          have hw1 : w 1 = u 1 + 1 := by simp [w]
          have hw_deg : w ∈ monOfDeg 2 e := by
            rw [mem_monOfDeg, Finsupp.degree_eq_sum, Fin.sum_univ_two, hw0, hw1]
            omega
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
            · have : u_min = w := h
              rwa [← this]
            · exact hLlex.2 w hw_deg u_min hu_min h
          refine ⟨w, hw_mem, ?_⟩
          ext r; fin_cases r
          · simp [hw0]; omega
          · simp [hw1]
    have hcardL : (shadow L).card ≤ M.card + 1 := by
      calc (shadow L).card
          ≤ (L.image (· + Finsupp.single 0 1) ∪ {u_min + Finsupp.single 1 1}).card :=
            Finset.card_le_card hsubL
        _ ≤ (L.image (· + Finsupp.single 0 1)).card + 1 := Finset.card_union_le _ _
        _ ≤ L.card + 1 := by linarith [Finset.card_image_le (s := L) (f := (· + Finsupp.single 0 1))]
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
  · rw [Finset.not_nonempty_iff_eq_empty] at hne
    subst hne
    simp [lexSeg, shadow]

/-- Key lemma for `n = m + 1 ≥ 3`: if `M` is compressed in every coordinate but not a lex set,
then `u = max_lex (monOfDeg \ M)` has `u (Fin.last m) ≥ 1`. -/
lemma max_not_mem_last_pos {m e : ℕ} (hm : 2 ≤ m) {M : Finset (Fin (m + 1) →₀ ℕ)}
    (hM : M ⊆ monOfDeg (m + 1) e)
    (hcomp : ∀ i : Fin (m + 1), IsCompressed i e M)
    {u v : Fin (m + 1) →₀ ℕ} (hu : u ∈ monOfDeg (m + 1) e) (huM : u ∉ M)
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
  have hv_last : 1 ≤ v (Fin.last m) := by
    have := hne_coord (Fin.last m)
    omega
  set p : Fin (m + 1) := ⟨m - 1, by omega⟩
  have hp_lt_last : p < Fin.last m := by
    change m - 1 < m; omega
  have hp_pos : (0 : Fin (m + 1)) < p := by
    change 0 < m - 1; omega
  have hp_ne : p ≠ Fin.last m := ne_of_lt hp_lt_last
  set z : Fin (m + 1) →₀ ℕ :=
    (v - Finsupp.single (Fin.last m) (v (Fin.last m))) + Finsupp.single p (v (Fin.last m))
  have hz_deg : z ∈ monOfDeg (m + 1) e := by
    rw [mem_monOfDeg, Finsupp.degree_eq_sum]
    have hdv := mem_monOfDeg.mp (hM hvM)
    rw [Finsupp.degree_eq_sum] at hdv
    have hsum : ∑ i : Fin (m + 1), z i = ∑ i : Fin (m + 1), v i := by
      have h1 : ∑ i : Fin (m + 1), z i =
          z p + z (Fin.last m) + ∑ i ∈ (Finset.univ.erase p).erase (Fin.last m), z i := by
        rw [← Finset.add_sum_erase _ _ (Finset.mem_univ p)]
        rw [← Finset.add_sum_erase _ _ (Finset.mem_erase.mpr ⟨hp_ne.symm, Finset.mem_univ _⟩)]
        ring
      have h2 : ∑ i : Fin (m + 1), v i =
          v p + v (Fin.last m) + ∑ i ∈ (Finset.univ.erase p).erase (Fin.last m), v i := by
        rw [← Finset.add_sum_erase _ _ (Finset.mem_univ p)]
        rw [← Finset.add_sum_erase _ _ (Finset.mem_erase.mpr ⟨hp_ne.symm, Finset.mem_univ _⟩)]
        ring
      rw [h1, h2]
      have hzp : z p = v p + v (Fin.last m) := by simp [z, hp_ne.symm]
      have hzlast : z (Fin.last m) = 0 := by simp [z, hp_ne]
      have hrest : ∑ i ∈ (Finset.univ.erase p).erase (Fin.last m), z i =
          ∑ i ∈ (Finset.univ.erase p).erase (Fin.last m), v i := by
        refine Finset.sum_congr rfl fun i hi => ?_
        rw [mem_erase, mem_erase] at hi
        simp [z, hi.1.symm, hi.2.1.symm]
      omega
    omega
  have hz0 : z 0 = v 0 := by
    have h1 : Fin.last m ≠ (0 : Fin (m + 1)) := ne_of_gt (lt_trans hp_pos hp_lt_last)
    have h2 : p ≠ (0 : Fin (m + 1)) := ne_of_gt hp_pos
    simp [z, h1, h2]
  have hz_gt_v : toLex v < toLex z := by
    rw [lex_lt_iff]
    refine ⟨p, fun j hj => ?_, ?_⟩
    · have h1 : Fin.last m ≠ j := ne_of_gt (lt_trans hj hp_lt_last)
      have h2 : p ≠ j := ne_of_gt hj
      simp [z, h1, h2]
    · simp only [z, Finsupp.coe_add, Finsupp.coe_tsub, Pi.add_apply, Pi.sub_apply,
        Finsupp.single_eq_same, Finsupp.single_eq_of_ne hp_ne, tsub_zero]
      omega
  have hzM : z ∈ M := hcomp 0 z hz_deg v hvM hz0 hz_gt_v
  have hz_last : z (Fin.last m) = 0 := by simp [z, hp_ne]
  have hz_lt_u : toLex z < toLex u := by
    rw [lex_lt_iff]
    exact ⟨0, fun j hj => absurd hj (Fin.not_lt_zero j), by omega⟩
  exact huM (hcomp (Fin.last m) u hu z hzM (by omega) hz_lt_u)

/-- Main theorem of Part 4: Macaulay's shadow inequality. -/
theorem macaulay_shadow (n : ℕ) :
    ∀ (e : ℕ) (M : Finset (Fin n →₀ ℕ)), M ⊆ monOfDeg n e →
      (shadow (lexSeg n e M.card)).card ≤ (shadow M).card := by
  induction n with
  | zero =>
    intro e M hM
    have hlex : IsLexSet 0 e M := by
      refine ⟨hM, fun u _ v _ hlt => ?_⟩
      rw [lex_lt_iff] at hlt
      obtain ⟨i, _⟩ := hlt
      exact Fin.elim0 i
    rw [← hlex.eq_lexSeg]
  | succ m ih =>
    cases m with
    | zero =>
      intro e M hM
      have hlex : IsLexSet 1 e M := by
        refine ⟨hM, fun u hu v hv hlt => ?_⟩
        have hdu := mem_monOfDeg.mp hu
        have hdv := mem_monOfDeg.mp (hM hv)
        rw [Finsupp.degree_eq_sum, Fin.sum_univ_one] at hdu hdv
        have huv : u = v := Finsupp.ext fun i => by
          fin_cases i; change u 0 = v 0; omega
        subst huv
        exact absurd hlt (lt_irrefl _)
      rw [← hlex.eq_lexSeg]
    | succ m' =>
      cases m' with
      | zero => exact macaulay_shadow_two
      | succ k =>
        set m := k + 2
        have hm : 2 ≤ m := by omega
        intro e M hM
        suffices hmain : ∀ r (M : Finset (Fin (m + 1) →₀ ℕ)),
            M ⊆ monOfDeg (m + 1) e → lexRankSum (m + 1) e M = r →
            (shadow (lexSeg (m + 1) e M.card)).card ≤ (shadow M).card by
          exact hmain _ M hM rfl
        intro r
        induction r using Nat.strong_induction_on with
        | _ r ihr =>
          intro M hM hr
          by_cases hlex : IsLexSet (m + 1) e M
          · rw [← hlex.eq_lexSeg]
          · by_cases hall : ∀ i : Fin (m + 1), IsCompressed i e M
            · have hMne : M.Nonempty := by
                by_contra hemp
                rw [Finset.not_nonempty_iff_eq_empty] at hemp
                subst hemp
                exact hlex ⟨Finset.empty_subset _, fun _ _ _ hv _ => absurd hv (by simp)⟩
              have hCne : (monOfDeg (m + 1) e \ M).Nonempty := by
                by_contra hemp
                rw [Finset.not_nonempty_iff_eq_empty, Finset.sdiff_eq_empty_iff_subset] at hemp
                have heq : M = monOfDeg (m + 1) e := Finset.Subset.antisymm hM hemp
                exact hlex ⟨hM, fun u hu _ _ _ => heq ▸ hu⟩
              obtain ⟨u, huC, hu_max⟩ := Finset.exists_max_image _ toLex hCne
              obtain ⟨v, hvM, hv_min⟩ := Finset.exists_min_image _ toLex hMne
              rw [mem_sdiff] at huC
              obtain ⟨hu_deg, hu_nM⟩ := huC
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
                max_not_mem_last_pos hm hM hall hu_deg hu_nM hvM hvu'
              set M₀ := M.erase v
              set M' := insert u M₀
              have huM₀ : u ∉ M₀ := fun h => hu_nM (Finset.mem_of_mem_erase h)
              have hM'sub : M' ⊆ monOfDeg (m + 1) e := by
                intro x hx
                rw [mem_insert] at hx
                rcases hx with rfl | hx
                · exact hu_deg
                · exact hM (Finset.mem_of_mem_erase hx)
              have hM'card : M'.card = M.card := by
                rw [Finset.card_insert_of_notMem huM₀, Finset.card_erase_of_mem hvM]
                have := hMne.card_pos; omega
              have hrank_lt : lexRankSum (m + 1) e M' < r := by
                rw [← hr, lexRankSum, lexRankSum]
                rw [Finset.sum_insert huM₀]
                have hsumM : lexRank (m + 1) e v + ∑ x ∈ M₀, lexRank (m + 1) e x =
                    ∑ x ∈ M, lexRank (m + 1) e x :=
                  Finset.add_sum_erase M (lexRank (m + 1) e) hvM
                have hlt_rk := lexRank_lt_of_lt hu_deg hvu'
                omega
              have hshadow_le : (shadow M').card ≤ (shadow M).card := by
                have hsub_u : shadow M' \ shadow M₀ ⊆ {u + Finsupp.single (Fin.last m) 1} := by
                  intro x hx
                  rw [mem_sdiff, mem_shadow] at hx
                  obtain ⟨⟨a, ha, j, rfl⟩, hx0⟩ := hx
                  rw [mem_insert] at ha
                  rcases ha with ha_eq | ha0
                  · rw [ha_eq] at hx0 ⊢
                    rw [mem_singleton]
                    by_cases hj : j = Fin.last m
                    · subst hj; rfl
                    · exfalso
                      have hj_lt : j < Fin.last m := lt_of_le_of_ne (Fin.le_last j) hj
                      set w := (u - Finsupp.single (Fin.last m) 1) + Finsupp.single j 1
                      have hw_deg : w ∈ monOfDeg (m + 1) e := by
                        rw [mem_monOfDeg, map_add, Finsupp.degree_single]
                        have := degree_sub_single hu_last
                        have hdu := mem_monOfDeg.mp hu_deg
                        omega
                      have hu_lt_w : toLex u < toLex w := by
                        rw [lex_lt_iff]
                        refine ⟨j, fun r hr => ?_, ?_⟩
                        · have h1 : Fin.last m ≠ r := ne_of_gt (lt_trans hr hj_lt)
                          have h2 : j ≠ r := ne_of_gt hr
                          simp [w, h1, h2]
                        · have h1 : j ≠ Fin.last m := hj
                          simp only [w, Finsupp.coe_add, Finsupp.coe_tsub, Pi.add_apply,
                            Pi.sub_apply, Finsupp.single_eq_same,
                            Finsupp.single_eq_of_ne h1, tsub_zero]
                          omega
                      have hwM : w ∈ M := by
                        by_contra hw_nM
                        exact not_lt_of_ge (hu_max w (mem_sdiff.mpr ⟨hw_deg, hw_nM⟩)) hu_lt_w
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
                      exact hx0 (mem_shadow.mpr ⟨w, hwM₀, Fin.last m, heq_add⟩)
                  · exact absurd (mem_shadow.mpr ⟨a, ha0, j, rfl⟩) hx0
                have hv_lost : v + Finsupp.single (Fin.last m) 1 ∈ shadow M \ shadow M₀ := by
                  rw [mem_sdiff]
                  refine ⟨mem_shadow.mpr ⟨v, hvM, Fin.last m, rfl⟩, ?_⟩
                  rw [mem_shadow]
                  rintro ⟨w, hw0, j, heq⟩
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
                have hM₀_sub_M : shadow M₀ ⊆ shadow M := shadow_mono (Finset.erase_subset v M)
                have hM₀_sub_M' : shadow M₀ ⊆ shadow M' := shadow_mono (Finset.subset_insert u M₀)
                have hc1 := Finset.card_sdiff_add_card_eq_card hM₀_sub_M'
                have hc2 := Finset.card_sdiff_add_card_eq_card hM₀_sub_M
                have hle1 : (shadow M' \ shadow M₀).card ≤ 1 :=
                  (Finset.card_le_card hsub_u).trans (by simp)
                have hge1 : 1 ≤ (shadow M \ shadow M₀).card :=
                  Finset.one_le_card.mpr ⟨_, hv_lost⟩
                omega
              calc (shadow (lexSeg (m + 1) e M.card)).card
                  = (shadow (lexSeg (m + 1) e M'.card)).card := by rw [hM'card]
                _ ≤ (shadow M').card := ihr _ hrank_lt M' hM'sub rfl
                _ ≤ (shadow M).card := hshadow_le
            · push Not at hall
              obtain ⟨i, hni⟩ := hall
              set C := compress i e M
              have hCsub : C ⊆ monOfDeg (m + 1) e := compress_subset_monOfDeg i e M
              have hCcard : C.card = M.card := card_compress i e hM
              have hrank_lt : lexRankSum (m + 1) e C < r :=
                hr ▸ lexRankSum_compress_lt i hM hni
              have hshadow_le : (shadow C).card ≤ (shadow M).card := by
                rw [card_eq_sum_card_slice i (shadow_subset_monOfDeg hCsub),
                    card_eq_sum_card_slice i (shadow_subset_monOfDeg hM)]
                refine Finset.sum_le_sum fun a ha => ?_
                rw [mem_range] at ha
                rw [slice_shadow, slice_shadow]
                by_cases hae : a ≤ e
                · rw [slice_compress i e a M hae]
                  have hlex1 : IsLexSet m (e - a + 1)
                      (shadow (lexSeg m (e - a) (slice i a M).card)) :=
                    (isLexSet_lexSeg m (e - a) _).shadow
                  by_cases ha0 : 0 < a
                  · rw [if_pos ha0, if_pos ha0, slice_compress i e (a - 1) M (by omega)]
                    have hdeg_eq : e - a + 1 = e - (a - 1) := by omega
                    have hlex2 : IsLexSet m (e - a + 1)
                        (lexSeg m (e - (a - 1)) (slice i (a - 1) M).card) := by
                      rw [hdeg_eq]; exact isLexSet_lexSeg m (e - (a - 1)) _
                    rw [hlex1.card_union hlex2]
                    apply max_le
                    · calc (shadow (lexSeg m (e - a) (slice i a M).card)).card
                          ≤ (shadow (slice i a M)).card :=
                            ih (e - a) (slice i a M) (slice_subset_monOfDeg hM)
                        _ ≤ (shadow (slice i a M) ∪ slice i (a - 1) M).card :=
                            Finset.card_le_card Finset.subset_union_left
                    · rw [card_lexSeg (Finset.card_le_card (slice_subset_monOfDeg hM))]
                      exact Finset.card_le_card Finset.subset_union_right
                  · rw [if_neg ha0, if_neg ha0, Finset.union_empty, Finset.union_empty]
                    exact ih (e - a) (slice i a M) (slice_subset_monOfDeg hM)
                · have ha_eq : a = e + 1 := by omega
                  subst ha_eq
                  have hsc0 : slice i (e + 1) C = ∅ := by
                    rw [Finset.eq_empty_iff_forall_notMem]
                    intro w hw
                    rw [mem_slice] at hw
                    have hdeg := mem_monOfDeg.mp (hCsub hw)
                    rw [degree_insertCoord] at hdeg
                    omega
                  have hsm0 : slice i (e + 1) M = ∅ := by
                    rw [Finset.eq_empty_iff_forall_notMem]
                    intro w hw
                    rw [mem_slice] at hw
                    have hdeg := mem_monOfDeg.mp (hM hw)
                    rw [degree_insertCoord] at hdeg
                    omega
                  simp only [hsc0, hsm0, shadow_empty, Finset.empty_union,
                    Nat.zero_lt_succ, ↓reduceIte, Nat.add_sub_cancel]
                  rw [slice_compress i e e M le_rfl]
                  rw [card_lexSeg (Finset.card_le_card (slice_subset_monOfDeg hM))]
              calc (shadow (lexSeg (m + 1) e M.card)).card
                  = (shadow (lexSeg (m + 1) e C.card)).card := by rw [hCcard]
                _ ≤ (shadow C).card := ihr _ hrank_lt C hCsub rfl
                _ ≤ (shadow M).card := hshadow_le

/- Part 5: Initial monomials of an ideal and Hilbert function preservation -/

section IdealPart

variable {n : ℕ} {k : Type*} [Field k]

/-- Leading exponent vector of a nonzero polynomial under `toLex`. -/
noncomputable def lm (f : MvPolynomial (Fin n) k) (hf : f ≠ 0) : Fin n →₀ ℕ :=
  ofLex ((f.support.image toLex).max' ((f.support_nonempty.mpr hf).image toLex))

lemma lm_mem_support {f : MvPolynomial (Fin n) k} (hf : f ≠ 0) : lm f hf ∈ f.support := by
  have hmem := Finset.max'_mem (f.support.image toLex) ((f.support_nonempty.mpr hf).image toLex)
  rw [mem_image] at hmem
  obtain ⟨u, hu, heq⟩ := hmem
  have : lm f hf = u := by
    simp only [lm, ← heq]; rfl
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
    · have h1 : 1 ≤ d i := by
        have := hle i; simpa using this
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

lemma lm_X_mul (i : Fin n) {f : MvPolynomial (Fin n) k} (hf : f ≠ 0)
    (hxf : X i * f ≠ 0) :
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

/-- The `e`-th graded piece of `I` as a `k`-submodule. -/
noncomputable def idealPiece (I : Ideal (MvPolynomial (Fin n) k)) (e : ℕ) :
    Submodule k (MvPolynomial (Fin n) k) :=
  Submodule.restrictScalars k I ⊓ homogeneousSubmodule (Fin n) k e

lemma weight_one_eq_degree (u : Fin n →₀ ℕ) : Finsupp.weight (1 : Fin n → ℕ) u = u.degree := by
  simp [Finsupp.weight_apply, Finsupp.degree_eq_sum, Finsupp.sum_fintype]

open Classical in
/-- The finite set of leading monomials of nonzero elements of `idealPiece I e`. -/
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

/- Part 6: Constructing the lex ideal from the degree slices -/

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

theorem macaulay_main (I : Ideal (MvPolynomial (Fin n) k)) :
    ∃ L : Ideal (MvPolynomial (Fin n) k), IsLexIdeal L ∧
      ∀ e, hilbertFunction I e = hilbertFunction L e := by
  classical
  let L_slice : ℕ → Finset (Fin n →₀ ℕ) := fun e => lexSeg n e (initMons I e).card
  have hdeg : ∀ e, L_slice e ⊆ monOfDeg n e := fun e => lexSeg_subset_monOfDeg n e _
  have hlex : ∀ e, IsLexSet n e (L_slice e) := fun e => isLexSet_lexSeg n e _
  have hcard : ∀ e, (L_slice e).card = (initMons I e).card := fun e =>
    card_lexSeg (Finset.card_le_card (initMons_subset I e))
  have hshadow : ∀ e, shadow (L_slice e) ⊆ L_slice (e + 1) := by
    intro e
    apply (hlex e).shadow.subset_of_card_le (hlex (e + 1))
    calc (shadow (L_slice e)).card
        ≤ (shadow (initMons I e)).card := macaulay_shadow n e (initMons I e) (initMons_subset I e)
      _ ≤ (initMons I (e + 1)).card := Finset.card_le_card (shadow_initMons_subset I e)
      _ = (L_slice (e + 1)).card := (hcard (e + 1)).symm
  let S : Set (Fin n →₀ ℕ) := { u | u ∈ L_slice u.degree }
  have hS : ∀ u, u ∈ S ↔ u ∈ L_slice u.degree := fun _ => Iff.rfl
  have hclosed : ∀ u ∈ S, ∀ i : Fin n, u + Finsupp.single i 1 ∈ S := by
    intro u hu i
    rw [hS, map_add, Finsupp.degree_single]
    exact hshadow u.degree (mem_shadow.mpr ⟨u, (hS u).mp hu, i, rfl⟩)
  refine ⟨Ideal.span ((fun u => monomial u (1 : k)) '' S), ⟨⟨S, rfl⟩, ?_⟩, ?_⟩
  · intro u v huv hlt hvL
    rw [mem_monomialIdeal_iff_support hclosed] at hvL ⊢
    intro w hw
    rw [MvPolynomial.support_monomial, if_neg one_ne_zero, Finset.mem_singleton] at hw
    rw [hw]
    have hvS : v ∈ S := hvL v (by
      rw [MvPolynomial.support_monomial, if_neg one_ne_zero, Finset.mem_singleton])
    rw [hS, huv]
    exact (hlex v.degree).2 u (mem_monOfDeg.mpr huv) v ((hS v).mp hvS) hlt
  · intro e
    exact (card_initMons_eq_hilbertFunction I e).symm.trans
      ((hcard e).symm.trans (hilbertFunction_monomialIdeal hS hdeg hshadow e).symm)

end IdealPart

end MacaulayProof

theorem OMA.solution : type_of% @EisenbudGreenHarris.eisenbud_green_harris.variants.macaulay :=
  fun {_ _ _} I _ => MacaulayProof.macaulay_main I
