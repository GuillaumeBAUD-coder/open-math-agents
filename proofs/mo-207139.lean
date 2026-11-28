import OMAStatements.S_mo_207139

namespace OMA.S_mo_207139_Proof
open OMA.S_mo_207139 Finset

noncomputable section

private def prefSet {n : ℕ} (k : Layer n) : Finset (Fin n) :=
  Finset.univ.filter (fun i : Fin n => i.val < k.val)

private def indVec {n : ℕ} (a : ℝ) (A : Finset (Fin n)) : V n :=
  fun i => if i ∈ A then a else 0

private lemma card_prefSet {n : ℕ} (k : Layer n) : (prefSet k).card = k.val := by
  have hle : k.val ≤ n := Nat.lt_succ_iff.mp k.isLt
  rw [← Finset.card_range k.val]
  refine Finset.card_bij (fun i _ => i.val) ?_ ?_ ?_
  · intro i hi
    exact Finset.mem_range.mpr (Finset.mem_filter.mp hi).2
  · intro i₁ _ i₂ _ h
    exact Fin.ext h
  · intro m hm
    have hmk : m < k.val := Finset.mem_range.mp hm
    refine ⟨⟨m, lt_of_lt_of_le hmk hle⟩, ?_, rfl⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hmk⟩

private lemma pref_nonneg {n : ℕ} {d : Layer n → ℝ} (hd : ∀ k, 0 ≤ d k) (k : Layer n) (i : Fin n) :
    0 ≤ pref d k i := by
  unfold pref
  split_ifs
  · exact hd k
  · exact le_rfl

private lemma sum_pref {n : ℕ} (d : Layer n → ℝ) (k : Layer n) :
    ∑ i : Fin n, pref d k i = ht d k := by
  have h1 : (∑ i : Fin n, pref d k i) = ∑ i ∈ prefSet k, d k := by
    unfold prefSet
    rw [Finset.sum_filter]
    rfl
  rw [h1, Finset.sum_const, nsmul_eq_mul, card_prefSet, ht]

private lemma orbit_nonneg {n : ℕ} {v : V n} (hv : ∀ i, 0 ≤ v i) (σ : Equiv.Perm (Fin n)) (i : Fin n) :
    0 ≤ orbit σ v i :=
  hv (σ i)

private lemma sum_orbit {n : ℕ} (σ : Equiv.Perm (Fin n)) (v : V n) :
    ∑ i : Fin n, orbit σ v i = ∑ i : Fin n, v i :=
  Equiv.sum_comp σ v

private lemma card_filter_perm {n : ℕ} (k : Layer n) (σ : Equiv.Perm (Fin n)) :
    (Finset.univ.filter (fun i : Fin n => (σ i).val < k.val)).card = k.val := by
  have h : (Finset.univ.filter (fun i : Fin n => (σ i).val < k.val)).card = (prefSet k).card := by
    refine Finset.card_bij (fun i _ => σ i) ?_ ?_ ?_
    · intro i hi
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hi).2⟩
    · intro i₁ _ i₂ _ h
      exact σ.injective h
    · intro j hj
      refine ⟨σ.symm j, ?_, σ.apply_symm_apply j⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simpa using (Finset.mem_filter.mp hj).2⟩
  rw [h, card_prefSet]

private lemma mem_simplex_iff {n : ℕ} {e : ℝ} (he : 0 < e) (x : V n) :
    x ∈ simplex n e ↔ (∀ i, 0 ≤ x i) ∧ ∑ i, x i = e := by
  constructor
  · intro hx
    let S : Set (V n) := {y | (∀ i, 0 ≤ y i) ∧ ∑ i, y i = e}
    have hconv : Convex ℝ S := by
      intro u hu v hv a b ha hb hab
      refine ⟨fun i => add_nonneg (mul_nonneg ha (hu.1 i)) (mul_nonneg hb (hv.1 i)), ?_⟩
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_add_distrib, ← Finset.mul_sum,
        hu.2, hv.2]
      calc a * e + b * e = (a + b) * e := by ring
        _ = e := by rw [hab, one_mul]
    have hsub : Set.range (fun i : Fin n => Pi.single i e) ⊆ S := by
      rintro _ ⟨i, rfl⟩
      refine ⟨fun j => ?_, ?_⟩
      · simp only [Pi.single_apply]
        split_ifs
        · exact he.le
        · exact le_rfl
      · simp [Pi.single_apply]
    exact convexHull_min hsub hconv hx
  · rintro ⟨hx0, hxsum⟩
    have hmem :
        (∑ i : Fin n, (x i / e) • Pi.single i e) ∈ simplex n e := by
      refine (convex_convexHull ℝ _).sum_mem (t := Finset.univ) (w := fun i => x i / e)
        (z := fun i => Pi.single i e) ?_ ?_ ?_
      · intro i _
        exact div_nonneg (hx0 i) he.le
      · rw [← Finset.sum_div, hxsum, div_self he.ne']
      · intro i _
        exact subset_convexHull ℝ _ ⟨i, rfl⟩
    have heq : (∑ i : Fin n, (x i / e) • Pi.single i e) = x := by
      ext j
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply, mul_ite, mul_zero,
        Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]
      exact div_mul_cancel₀ (x j) he.ne'
    rwa [heq] at hmem

private lemma exists_perm_of_subset {n : ℕ} {k l : Layer n} (hkl : k.val ≤ l.val)
    {A B : Finset (Fin n)} (hA : A.card = k.val) (hB : B.card = l.val) (hAB : A ⊆ B) :
    ∃ σ : Equiv.Perm (Fin n),
      (∀ i, i ∈ A ↔ σ i ∈ prefSet k) ∧ (∀ i, i ∈ B ↔ σ i ∈ prefSet l) := by
  let P1 : Finset (Fin n) := prefSet k
  let P2 : Finset (Fin n) := prefSet l \ prefSet k
  let P3 : Finset (Fin n) := Finset.univ \ prefSet l
  have hP1P : P1 ⊆ prefSet l := by
    intro i hi
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, lt_of_lt_of_le (Finset.mem_filter.mp hi).2 hkl⟩
  have hP1c : P1.card = k.val := card_prefSet k
  have hP2c : P2.card = l.val - k.val := by
    dsimp only [P2]
    rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hP1P, card_prefSet l, hP1c]
  have hP3c : P3.card = n - l.val := by
    dsimp only [P3]
    rw [Finset.card_sdiff, Finset.inter_univ, Finset.card_univ, Fintype.card_fin, card_prefSet l]
  have hBAs : (B \ A).card = l.val - k.val := by
    rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hAB, hB, hA]
  have hUBs : (Finset.univ \ B).card = n - l.val := by
    rw [Finset.card_sdiff, Finset.inter_univ, Finset.card_univ, Fintype.card_fin, hB]
  let e1 : {i // i ∈ A} ≃ {j // j ∈ P1} :=
    Fintype.equivOfCardEq (by rw [Fintype.card_coe, Fintype.card_coe, hA, hP1c])
  let e2 : {i // i ∈ B \ A} ≃ {j // j ∈ P2} :=
    Fintype.equivOfCardEq (by rw [Fintype.card_coe, Fintype.card_coe, hBAs, hP2c])
  let e3 : {i // i ∈ Finset.univ \ B} ≃ {j // j ∈ P3} :=
    Fintype.equivOfCardEq (by rw [Fintype.card_coe, Fintype.card_coe, hUBs, hP3c])
  let f : Fin n → Fin n := fun i =>
    if h1 : i ∈ A then (e1 ⟨i, h1⟩).val
    else if h2 : i ∈ B then (e2 ⟨i, Finset.mem_sdiff.mpr ⟨h2, h1⟩⟩).val
    else (e3 ⟨i, Finset.mem_sdiff.mpr ⟨Finset.mem_univ i, h2⟩⟩).val
  let g : Fin n → Fin n := fun j =>
    if h1 : j ∈ P1 then (e1.symm ⟨j, h1⟩).val
    else if h2 : j ∈ prefSet l then (e2.symm ⟨j, Finset.mem_sdiff.mpr ⟨h2, h1⟩⟩).val
    else (e3.symm ⟨j, Finset.mem_sdiff.mpr ⟨Finset.mem_univ j, h2⟩⟩).val
  have hgf : Function.LeftInverse g f := by
    intro i
    dsimp only [f, g]
    by_cases h1 : i ∈ A
    · rw [dif_pos h1]
      have hp1 : (e1 ⟨i, h1⟩).val ∈ P1 := (e1 ⟨i, h1⟩).property
      rw [dif_pos hp1]
      exact congrArg Subtype.val (e1.symm_apply_apply ⟨i, h1⟩)
    · rw [dif_neg h1]
      by_cases h2 : i ∈ B
      · rw [dif_pos h2]
        have hp2 : (e2 ⟨i, Finset.mem_sdiff.mpr ⟨h2, h1⟩⟩).val ∈ P2 :=
          (e2 ⟨i, Finset.mem_sdiff.mpr ⟨h2, h1⟩⟩).property
        have hnp1 : (e2 ⟨i, Finset.mem_sdiff.mpr ⟨h2, h1⟩⟩).val ∉ P1 := (Finset.mem_sdiff.mp hp2).2
        have hpl : (e2 ⟨i, Finset.mem_sdiff.mpr ⟨h2, h1⟩⟩).val ∈ prefSet l := (Finset.mem_sdiff.mp hp2).1
        rw [dif_neg hnp1, dif_pos hpl]
        exact congrArg Subtype.val (e2.symm_apply_apply ⟨i, Finset.mem_sdiff.mpr ⟨h2, h1⟩⟩)
      · rw [dif_neg h2]
        have hp3 : (e3 ⟨i, Finset.mem_sdiff.mpr ⟨Finset.mem_univ i, h2⟩⟩).val ∈ P3 :=
          (e3 ⟨i, Finset.mem_sdiff.mpr ⟨Finset.mem_univ i, h2⟩⟩).property
        have hnpl : (e3 ⟨i, Finset.mem_sdiff.mpr ⟨Finset.mem_univ i, h2⟩⟩).val ∉ prefSet l :=
          (Finset.mem_sdiff.mp hp3).2
        have hnp1 : (e3 ⟨i, Finset.mem_sdiff.mpr ⟨Finset.mem_univ i, h2⟩⟩).val ∉ P1 :=
          fun h => hnpl (hP1P h)
        rw [dif_neg hnp1, dif_neg hnpl]
        exact congrArg Subtype.val (e3.symm_apply_apply ⟨i, Finset.mem_sdiff.mpr ⟨Finset.mem_univ i, h2⟩⟩)
  have hfg : Function.RightInverse g f := by
    intro j
    dsimp only [f, g]
    by_cases h1 : j ∈ P1
    · rw [dif_pos h1]
      have ha : (e1.symm ⟨j, h1⟩).val ∈ A := (e1.symm ⟨j, h1⟩).property
      rw [dif_pos ha]
      exact congrArg Subtype.val (e1.apply_symm_apply ⟨j, h1⟩)
    · rw [dif_neg h1]
      by_cases h2 : j ∈ prefSet l
      · rw [dif_pos h2]
        have hba : (e2.symm ⟨j, Finset.mem_sdiff.mpr ⟨h2, h1⟩⟩).val ∈ B \ A :=
          (e2.symm ⟨j, Finset.mem_sdiff.mpr ⟨h2, h1⟩⟩).property
        have hna : (e2.symm ⟨j, Finset.mem_sdiff.mpr ⟨h2, h1⟩⟩).val ∉ A := (Finset.mem_sdiff.mp hba).2
        have hb : (e2.symm ⟨j, Finset.mem_sdiff.mpr ⟨h2, h1⟩⟩).val ∈ B := (Finset.mem_sdiff.mp hba).1
        rw [dif_neg hna, dif_pos hb]
        exact congrArg Subtype.val (e2.apply_symm_apply ⟨j, Finset.mem_sdiff.mpr ⟨h2, h1⟩⟩)
      · rw [dif_neg h2]
        have hub : (e3.symm ⟨j, Finset.mem_sdiff.mpr ⟨Finset.mem_univ j, h2⟩⟩).val ∈ Finset.univ \ B :=
          (e3.symm ⟨j, Finset.mem_sdiff.mpr ⟨Finset.mem_univ j, h2⟩⟩).property
        have hnb : (e3.symm ⟨j, Finset.mem_sdiff.mpr ⟨Finset.mem_univ j, h2⟩⟩).val ∉ B :=
          (Finset.mem_sdiff.mp hub).2
        have hna : (e3.symm ⟨j, Finset.mem_sdiff.mpr ⟨Finset.mem_univ j, h2⟩⟩).val ∉ A :=
          fun h => hnb (hAB h)
        rw [dif_neg hna, dif_neg hnb]
        exact congrArg Subtype.val (e3.apply_symm_apply ⟨j, Finset.mem_sdiff.mpr ⟨Finset.mem_univ j, h2⟩⟩)
  refine ⟨⟨f, g, hgf, hfg⟩, ?_, ?_⟩
  · intro i
    change i ∈ A ↔ f i ∈ P1
    dsimp only [f]
    by_cases h1 : i ∈ A
    · rw [dif_pos h1]
      exact ⟨fun _ => (e1 ⟨i, h1⟩).property, fun _ => h1⟩
    · rw [dif_neg h1]
      by_cases h2 : i ∈ B
      · rw [dif_pos h2]
        have hp2 := (e2 ⟨i, Finset.mem_sdiff.mpr ⟨h2, h1⟩⟩).property
        exact ⟨fun h => (h1 h).elim, fun h => ((Finset.mem_sdiff.mp hp2).2 h).elim⟩
      · rw [dif_neg h2]
        have hp3 := (e3 ⟨i, Finset.mem_sdiff.mpr ⟨Finset.mem_univ i, h2⟩⟩).property
        exact ⟨fun h => (h1 h).elim, fun h => ((Finset.mem_sdiff.mp hp3).2 (hP1P h)).elim⟩
  · intro i
    change i ∈ B ↔ f i ∈ prefSet l
    dsimp only [f]
    by_cases h1 : i ∈ A
    · rw [dif_pos h1]
      exact ⟨fun _ => hP1P (e1 ⟨i, h1⟩).property, fun _ => hAB h1⟩
    · rw [dif_neg h1]
      by_cases h2 : i ∈ B
      · rw [dif_pos h2]
        have hp2 := (e2 ⟨i, Finset.mem_sdiff.mpr ⟨h2, h1⟩⟩).property
        exact ⟨fun _ => (Finset.mem_sdiff.mp hp2).1, fun _ => h2⟩
      · rw [dif_neg h2]
        have hp3 := (e3 ⟨i, Finset.mem_sdiff.mpr ⟨Finset.mem_univ i, h2⟩⟩).property
        exact ⟨fun h => (h2 h).elim, fun h => ((Finset.mem_sdiff.mp hp3).2 h).elim⟩

private lemma indVec_add_mem_nested_le {n : ℕ} {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    {k l : Layer n} (hkl : k.val ≤ l.val) :
    ∀ (m : ℕ) (A B : Finset (Fin n)), A.card = k.val → B.card = l.val → (A \ B).card = m →
    indVec a A + indVec b B ∈ convexHull ℝ
      {v : V n | ∃ σ : Equiv.Perm (Fin n), v = orbit σ (indVec a (prefSet k) + indVec b (prefSet l))} := by
  intro m
  induction m with
  | zero =>
    intro A B hA hB hm
    have hAB : A ⊆ B := Finset.sdiff_eq_empty_iff_subset.mp (Finset.card_eq_zero.mp hm)
    obtain ⟨σ, hσA, hσB⟩ := exists_perm_of_subset hkl hA hB hAB
    refine subset_convexHull ℝ _ ⟨σ, ?_⟩
    ext i
    simp only [Pi.add_apply, orbit, Function.comp_apply, indVec, hσA i, hσB i]
  | succ m ih =>
    intro A B hA hB hm
    have hneA : (A \ B).Nonempty := Finset.card_pos.mp (by omega)
    obtain ⟨u, hu⟩ := hneA
    have huA : u ∈ A := (Finset.mem_sdiff.mp hu).1
    have huB : u ∉ B := (Finset.mem_sdiff.mp hu).2
    have hBA_pos : 0 < (B \ A).card := by
      have h1 : (A \ B).card + (A ∩ B).card = A.card := Finset.card_sdiff_add_card_inter A B
      have h2 : (B \ A).card + (B ∩ A).card = B.card := Finset.card_sdiff_add_card_inter B A
      rw [Finset.inter_comm] at h2
      omega
    obtain ⟨v, hv⟩ := Finset.card_pos.mp hBA_pos
    have hvB : v ∈ B := (Finset.mem_sdiff.mp hv).1
    have hvA : v ∉ A := (Finset.mem_sdiff.mp hv).2
    have huv : u ≠ v := fun h => huB (h ▸ hvB)
    let B' : Finset (Fin n) := insert u (B.erase v)
    let A'' : Finset (Fin n) := insert v (A.erase u)
    have hB'card : B'.card = l.val := by
      have huBe : u ∉ B.erase v := fun h => huB (Finset.mem_of_mem_erase h)
      rw [Finset.card_insert_of_notMem huBe, Finset.card_erase_of_mem hvB, hB]
      have : 0 < B.card := Finset.card_pos.mpr ⟨v, hvB⟩
      omega
    have hA''card : A''.card = k.val := by
      have hvAe : v ∉ A.erase u := fun h => hvA (Finset.mem_of_mem_erase h)
      rw [Finset.card_insert_of_notMem hvAe, Finset.card_erase_of_mem huA, hA]
      have : 0 < A.card := Finset.card_pos.mpr ⟨u, huA⟩
      omega
    have hAB' : A \ B' = (A \ B).erase u := by
      ext i
      simp only [B', Finset.mem_sdiff, Finset.mem_insert, Finset.mem_erase, not_or, not_and]
      constructor
      · rintro ⟨hiA, hiu, hiBv⟩
        refine ⟨hiu, hiA, fun hiB => ?_⟩
        by_cases hiv : i = v
        · exact hvA (hiv ▸ hiA)
        · exact hiBv hiv hiB
      · rintro ⟨hiu, hiA, hiB⟩
        exact ⟨hiA, hiu, fun _ h => hiB h⟩
    have hA''B : A'' \ B = (A \ B).erase u := by
      ext i
      simp only [A'', Finset.mem_sdiff, Finset.mem_insert, Finset.mem_erase]
      constructor
      · rintro ⟨rfl | ⟨hiu, hiA⟩, hiB⟩
        · exact (hiB hvB).elim
        · exact ⟨hiu, hiA, hiB⟩
      · rintro ⟨hiu, hiA, hiB⟩
        exact ⟨Or.inr ⟨hiu, hiA⟩, hiB⟩
    have hm1 : (A \ B').card = m := by
      rw [hAB', Finset.card_erase_of_mem hu, hm]
      omega
    have hm2 : (A'' \ B).card = m := by
      rw [hA''B, Finset.card_erase_of_mem hu, hm]
      omega
    have hx' := ih A B' hA hB'card hm1
    have hx'' := ih A'' B hA''card hB hm2
    by_cases hab : a + b = 0
    · have ha0 : a = 0 := by linarith
      have hb0 : b = 0 := by linarith
      have heq : indVec a A + indVec b B = indVec a A + indVec b B' := by
        ext i; simp [indVec, ha0, hb0]
      rwa [heq]
    · have hab_pos : 0 < a + b := lt_of_le_of_ne (add_nonneg ha hb) (Ne.symm hab)
      have hcomb :
          indVec a A + indVec b B =
            (a / (a + b)) • (indVec a A + indVec b B') +
            (b / (a + b)) • (indVec a A'' + indVec b B) := by
        ext i
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, indVec, B', A'', Finset.mem_insert,
          Finset.mem_erase]
        by_cases hiu : i = u
        · subst hiu
          simp only [huA, huB, huv, ↓reduceIte, true_or, false_or, false_and, ne_eq,
            not_true_eq_false]
          field_simp [hab]
          ring
        · by_cases hiv : i = v
          · subst hiv
            simp only [hvA, hvB, huv.symm, ↓reduceIte, true_or, false_or, false_and, ne_eq,
              not_true_eq_false]
            field_simp [hab]
            ring
          · have h1 : (i = u ∨ i ≠ v ∧ i ∈ B) ↔ i ∈ B := by
              simp [hiu, hiv]
            have h2 : (i = v ∨ i ≠ u ∧ i ∈ A) ↔ i ∈ A := by
              simp [hiu, hiv]
            rw [if_congr h1 rfl rfl, if_congr h2 rfl rfl]
            by_cases hiA : i ∈ A <;> by_cases hiB : i ∈ B <;>
              simp only [hiA, hiB, ↓reduceIte, add_zero, zero_add, mul_zero]
            · field_simp [hab]
            · field_simp [hab]
            · field_simp [hab]
      rw [hcomb]
      exact (convex_convexHull ℝ _) hx' hx'' (div_nonneg ha hab_pos.le) (div_nonneg hb hab_pos.le)
        (by field_simp [hab])

private lemma indVec_add_mem_nested {n : ℕ} {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    {k l : Layer n} (A B : Finset (Fin n)) (hA : A.card = k.val) (hB : B.card = l.val) :
    indVec a A + indVec b B ∈ convexHull ℝ
      {v : V n | ∃ σ : Equiv.Perm (Fin n), v = orbit σ (indVec a (prefSet k) + indVec b (prefSet l))} := by
  rcases le_total k.val l.val with hkl | hlk
  · exact indVec_add_mem_nested_le ha hb hkl (A \ B).card A B hA hB rfl
  · have hswap := indVec_add_mem_nested_le hb ha hlk (B \ A).card B A hB hA rfl
    have hset :
        {v : V n | ∃ σ : Equiv.Perm (Fin n), v = orbit σ (indVec b (prefSet l) + indVec a (prefSet k))} =
        {v : V n | ∃ σ : Equiv.Perm (Fin n), v = orbit σ (indVec a (prefSet k) + indVec b (prefSet l))} := by
      ext v
      simp only [Set.mem_ofPred_eq, add_comm]
    rw [hset] at hswap
    rw [add_comm (indVec a A)]
    exact hswap

private lemma pair_cut_mem_convexHull_candidates {n : ℕ} {d : Layer n → ℝ} (hd : ∀ k, 0 ≤ d k)
    {e : ℝ} {k l : Layer n} (hk : ht d k < e) (hl : e < ht d l)
    (σ₁ σ₂ : Equiv.Perm (Fin n)) :
    ((ht d l - e) / (ht d l - ht d k)) • orbit σ₁ (pref d k) +
      ((e - ht d k) / (ht d l - ht d k)) • orbit σ₂ (pref d l) ∈
      convexHull ℝ (candidates d e) := by
  have hden : 0 < ht d l - ht d k := by linarith
  set α : ℝ := (ht d l - e) / (ht d l - ht d k)
  set β : ℝ := (e - ht d k) / (ht d l - ht d k)
  have hα : 0 ≤ α := div_nonneg (by linarith) hden.le
  have hβ : 0 ≤ β := div_nonneg (by linarith) hden.le
  let A : Finset (Fin n) := Finset.univ.filter (fun i : Fin n => (σ₁ i).val < k.val)
  let B : Finset (Fin n) := Finset.univ.filter (fun i : Fin n => (σ₂ i).val < l.val)
  have hA : A.card = k.val := card_filter_perm k σ₁
  have hB : B.card = l.val := card_filter_perm l σ₂
  have hvec :
      α • orbit σ₁ (pref d k) + β • orbit σ₂ (pref d l) =
        indVec (α * d k) A + indVec (β * d l) B := by
    ext i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, orbit, Function.comp_apply, pref, indVec,
      A, B, Finset.mem_filter, Finset.mem_univ, true_and, mul_ite, mul_zero]
  have hcut : indVec (α * d k) (prefSet k) + indVec (β * d l) (prefSet l) = cut d e k l := by
    ext i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, cut, pref, indVec, prefSet,
      Finset.mem_filter, Finset.mem_univ, true_and, mul_ite, mul_zero, α, β]
  have hmem := indVec_add_mem_nested (mul_nonneg hα (hd k)) (mul_nonneg hβ (hd l)) A B hA hB
  rw [← hvec, hcut] at hmem
  refine convexHull_mono ?_ hmem
  rintro v ⟨σ, rfl⟩
  exact Or.inr ⟨k, l, σ, hk, hl, rfl⟩

private lemma scaleHull_eq_convex_comb {n : ℕ} (d : Layer n → ℝ) (x : V n)
    (hx : x ∈ scaleHull d) :
    ∃ w : Layer n × Equiv.Perm (Fin n) → ℝ,
      (∀ p, 0 ≤ w p) ∧
      (∑ p, w p = 1) ∧
      (∑ p, w p • orbit p.2 (pref d p.1) = x) := by
  let P := Layer n × Equiv.Perm (Fin n)
  let g : P → V n := fun p => orbit p.2 (pref d p.1)
  let S : Set (V n) :=
    {y | ∃ w : P → ℝ, (∀ p, 0 ≤ w p) ∧ (∑ p, w p = 1) ∧ (∑ p, w p • g p = y)}
  have hconv : Convex ℝ S := by
    rintro u ⟨w₁, hw₁0, hw₁1, rfl⟩ v ⟨w₂, hw₂0, hw₂1, rfl⟩ a b ha hb hab
    refine ⟨fun p => a * w₁ p + b * w₂ p, ?_, ?_, ?_⟩
    · intro p
      exact add_nonneg (mul_nonneg ha (hw₁0 p)) (mul_nonneg hb (hw₂0 p))
    · simp only [Finset.sum_add_distrib, ← Finset.mul_sum, hw₁1, hw₂1, mul_one, hab]
    · simp only [add_smul, mul_smul, Finset.sum_add_distrib, ← Finset.smul_sum]
  have hsub : Set.range g ⊆ S := by
    rintro _ ⟨p₀, rfl⟩
    refine ⟨fun p => if p = p₀ then 1 else 0, ?_, ?_, ?_⟩
    · intro p; dsimp only; split_ifs <;> norm_num
    · simp
    · simp
  exact convexHull_min hsub hconv hx

private lemma section_eq_convexHull_candidates {n : ℕ} (d : Layer n → ℝ) (e : ℝ)
    (hd : ∀ k, 0 ≤ d k) (he : 0 < e) :
    scaleHull d ∩ simplex n e = convexHull ℝ (candidates d e) := by
  apply Set.Subset.antisymm
  · intro x ⟨hxH, hxS⟩
    have hxsum : ∑ i, x i = e := ((mem_simplex_iff he x).mp hxS).2
    obtain ⟨w, hw0, hw1, hwx⟩ := scaleHull_eq_convex_comb d x hxH
    let P := Layer n × Equiv.Perm (Fin n)
    let g : P → V n := fun p => orbit p.2 (pref d p.1)
    let Ineg : Finset P := Finset.univ.filter (fun p => ht d p.1 < e)
    let Izero : Finset P := Finset.univ.filter (fun p => ht d p.1 = e)
    let Ipos : Finset P := Finset.univ.filter (fun p => e < ht d p.1)
    have hsplit : ∀ {M : Type} [AddCommMonoid M] (F : P → M),
        (∑ p : P, F p) = (∑ p ∈ Ineg, F p) + (∑ p ∈ Izero, F p) + (∑ p ∈ Ipos, F p) := by
      intro M _ F
      have h1 : (∑ p : P, F p) =
          (∑ p ∈ Finset.univ.filter (fun p : P => ht d p.1 < e), F p) +
          (∑ p ∈ Finset.univ.filter (fun p : P => ¬ ht d p.1 < e), F p) :=
        (Finset.sum_filter_add_sum_filter_not Finset.univ (fun p : P => ht d p.1 < e) F).symm
      have h2 : (∑ p ∈ Finset.univ.filter (fun p : P => ¬ ht d p.1 < e), F p) =
          (∑ p ∈ Izero, F p) + (∑ p ∈ Ipos, F p) := by
        have hdisj : Disjoint Izero Ipos := by
          rw [Finset.disjoint_filter]
          intro p _ h1 h2
          linarith
        have hunion : Izero ∪ Ipos = Finset.univ.filter (fun p : P => ¬ ht d p.1 < e) := by
          ext p
          simp only [Izero, Ipos, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and,
            not_lt]
          constructor
          · rintro (h | h) <;> linarith
          · intro h
            rcases eq_or_lt_of_le h with h | h
            · exact Or.inl h.symm
            · exact Or.inr h
        rw [← Finset.sum_union hdisj, hunion]
      rw [h1, h2, ← add_assoc]
    have hsum_ht : (∑ p : P, w p * ht d p.1) = e := by
      have h1 : ∑ i : Fin n, x i = ∑ p : P, w p * (∑ i : Fin n, g p i) := by
        rw [← hwx]
        simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun p _ => ?_
        rw [← Finset.mul_sum]
      rw [hxsum] at h1
      rw [h1]
      refine Finset.sum_congr rfl fun p _ => ?_
      dsimp only [g]
      rw [sum_orbit, sum_pref]
    let A : ℝ := ∑ p ∈ Ineg, w p * (e - ht d p.1)
    let B : ℝ := ∑ q ∈ Ipos, w q * (ht d q.1 - e)
    have hAB : A = B := by
      have hzero : (∑ p : P, w p * (ht d p.1 - e)) = 0 := by
        have : (∑ p : P, w p * (ht d p.1 - e)) = (∑ p : P, w p * ht d p.1) - (∑ p : P, w p) * e := by
          simp only [mul_sub, Finset.sum_sub_distrib, Finset.sum_mul]
        rw [this, hsum_ht, hw1, one_mul, sub_self]
      rw [hsplit (fun p => w p * (ht d p.1 - e))] at hzero
      have hz0 : (∑ p ∈ Izero, w p * (ht d p.1 - e)) = 0 := by
        refine Finset.sum_eq_zero fun p hp => ?_
        have hpe : ht d p.1 = e := (Finset.mem_filter.mp hp).2
        rw [hpe, sub_self, mul_zero]
      have hneg : (∑ p ∈ Ineg, w p * (ht d p.1 - e)) = -A := by
        dsimp only [A]
        rw [← Finset.sum_neg_distrib]
        refine Finset.sum_congr rfl fun p _ => by ring
      rw [hz0, add_zero, hneg] at hzero
      linarith
    have hA_nonneg : 0 ≤ A := by
      refine Finset.sum_nonneg fun p hp => mul_nonneg (hw0 p) ?_
      linarith [(Finset.mem_filter.mp hp).2]
    by_cases hA0 : A = 0
    · have hw_neg : ∀ p ∈ Ineg, w p = 0 := by
        intro p hp
        have hterm : w p * (e - ht d p.1) = 0 :=
          (Finset.sum_eq_zero_iff_of_nonneg fun q hq =>
            mul_nonneg (hw0 q) (by linarith [(Finset.mem_filter.mp hq).2])).mp hA0 p hp
        have hpos : 0 < e - ht d p.1 := by linarith [(Finset.mem_filter.mp hp).2]
        exact (mul_eq_zero.mp hterm).resolve_right hpos.ne'
      have hw_pos : ∀ q ∈ Ipos, w q = 0 := by
        intro q hq
        have hB0 : B = 0 := hAB.symm.trans hA0
        have hterm : w q * (ht d q.1 - e) = 0 :=
          (Finset.sum_eq_zero_iff_of_nonneg fun r hr =>
            mul_nonneg (hw0 r) (by linarith [(Finset.mem_filter.mp hr).2])).mp hB0 q hq
        have hpos : 0 < ht d q.1 - e := by linarith [(Finset.mem_filter.mp hq).2]
        exact (mul_eq_zero.mp hterm).resolve_right hpos.ne'
      have hw1_zero : (∑ p ∈ Izero, w p) = 1 := by
        have := hsplit w
        rw [hw1, Finset.sum_eq_zero hw_neg, Finset.sum_eq_zero hw_pos, zero_add, add_zero] at this
        exact this.symm
      have hx_zero : (∑ p ∈ Izero, w p • g p) = x := by
        have hneg0 : (∑ p ∈ Ineg, w p • g p) = 0 :=
          Finset.sum_eq_zero fun p hp => by rw [hw_neg p hp, zero_smul]
        have hpos0 : (∑ q ∈ Ipos, w q • g q) = 0 :=
          Finset.sum_eq_zero fun q hq => by rw [hw_pos q hq, zero_smul]
        have h := hsplit (fun p => w p • g p)
        rw [hwx, hneg0, hpos0, zero_add, add_zero] at h
        exact h.symm
      rw [← hx_zero]
      refine (convex_convexHull ℝ _).sum_mem (fun p _ => hw0 p) hw1_zero fun p hp => ?_
      exact subset_convexHull ℝ _ (Or.inl ⟨p.1, p.2, (Finset.mem_filter.mp hp).2, rfl⟩)
    · have hA_pos : 0 < A := lt_of_le_of_ne hA_nonneg (Ne.symm hA0)
      let lam : P × P → ℝ := fun pq => w pq.1 * w pq.2 * (ht d pq.2.1 - ht d pq.1.1) / A
      let z : P × P → V n := fun pq =>
        ((ht d pq.2.1 - e) / (ht d pq.2.1 - ht d pq.1.1)) • g pq.1 +
        ((e - ht d pq.1.1) / (ht d pq.2.1 - ht d pq.1.1)) • g pq.2
      have hlam_nonneg : ∀ pq ∈ Ineg ×ˢ Ipos, 0 ≤ lam pq := by
        intro pq hpq
        have hp := (Finset.mem_filter.mp (Finset.mem_product.mp hpq).1).2
        have hq := (Finset.mem_filter.mp (Finset.mem_product.mp hpq).2).2
        exact div_nonneg (mul_nonneg (mul_nonneg (hw0 pq.1) (hw0 pq.2)) (by linarith)) hA_pos.le
      have hz_mem : ∀ pq ∈ Ineg ×ˢ Ipos, z pq ∈ convexHull ℝ (candidates d e) := by
        intro pq hpq
        have hp := (Finset.mem_filter.mp (Finset.mem_product.mp hpq).1).2
        have hq := (Finset.mem_filter.mp (Finset.mem_product.mp hpq).2).2
        exact pair_cut_mem_convexHull_candidates hd hp hq pq.1.2 pq.2.2
      have hlam_sum : (∑ pq ∈ Ineg ×ˢ Ipos, lam pq) = (∑ p ∈ Ineg, w p) + (∑ q ∈ Ipos, w q) := by
        rw [Finset.sum_product]
        have hinner : ∀ p ∈ Ineg,
            (∑ q ∈ Ipos, lam (p, q)) = w p + (w p * (e - ht d p.1) / A) * (∑ q ∈ Ipos, w q) := by
          intro p _
          have hstep : ∀ q ∈ Ipos,
              lam (p, q) = (w p / A) * (w q * (ht d q.1 - e)) + (w p * (e - ht d p.1) / A) * w q := by
            intro q _
            dsimp only [lam]
            ring
          rw [Finset.sum_congr rfl hstep, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
          change (w p / A) * B + _ = _
          rw [← hAB, div_mul_cancel₀ _ hA0]
        rw [Finset.sum_congr rfl hinner, Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.sum_div]
        change (∑ p ∈ Ineg, w p) + (A / A) * (∑ q ∈ Ipos, w q) = _
        rw [div_self hA0, one_mul]
      have hlam_vec :
          (∑ pq ∈ Ineg ×ˢ Ipos, lam pq • z pq) =
            (∑ p ∈ Ineg, w p • g p) + (∑ q ∈ Ipos, w q • g q) := by
        rw [Finset.sum_product]
        have hterm : ∀ p ∈ Ineg, ∀ q ∈ Ipos,
            lam (p, q) • z (p, q) =
              ((w p / A) * (w q * (ht d q.1 - e))) • g p +
              ((w p * (e - ht d p.1) / A) * w q) • g q := by
          intro p hp q hq
          have hlt1 : ht d p.1 < e := (Finset.mem_filter.mp hp).2
          have hlt2 : e < ht d q.1 := (Finset.mem_filter.mp hq).2
          have hden : ht d q.1 - ht d p.1 ≠ 0 := by linarith
          dsimp only [lam, z]
          rw [smul_add, smul_smul, smul_smul]
          congr 1
          · congr 1; field_simp [hden, hA0]
          · congr 1; field_simp [hden, hA0]
        have hsum1 :
            (∑ p ∈ Ineg, ∑ q ∈ Ipos, lam (p, q) • z (p, q)) =
              (∑ p ∈ Ineg, ∑ q ∈ Ipos, ((w p / A) * (w q * (ht d q.1 - e))) • g p) +
              (∑ p ∈ Ineg, ∑ q ∈ Ipos, ((w p * (e - ht d p.1) / A) * w q) • g q) := by
          rw [← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun p hp => ?_
          rw [← Finset.sum_add_distrib]
          exact Finset.sum_congr rfl fun q hq => hterm p hp q hq
        rw [hsum1]
        congr 1
        · refine Finset.sum_congr rfl fun p _ => ?_
          rw [← Finset.sum_smul, ← Finset.mul_sum]
          change ((w p / A) * B) • g p = w p • g p
          rw [← hAB, div_mul_cancel₀ _ hA0]
        · rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun q _ => ?_
          rw [← Finset.sum_smul, ← Finset.sum_mul, ← Finset.sum_div]
          change ((A / A) * w q) • g q = w q • g q
          rw [div_self hA0, one_mul]
      set S0 : ℝ := ∑ p ∈ Izero, w p
      set Sp : ℝ := ∑ pq ∈ Ineg ×ˢ Ipos, lam pq
      have hS0_nonneg : 0 ≤ S0 := Finset.sum_nonneg fun p _ => hw0 p
      have hSp_nonneg : 0 ≤ Sp := Finset.sum_nonneg hlam_nonneg
      have hS_sum : S0 + Sp = 1 := by
        have hs := hsplit w
        rw [hw1] at hs
        rw [hlam_sum]
        dsimp only [S0]
        linarith
      have hSp_pos : 0 < Sp := by
        by_contra hle
        rw [not_lt] at hle
        have hSp0 : Sp = 0 := le_antisymm hle hSp_nonneg
        have hneg0 : (∑ p ∈ Ineg, w p) = 0 := by
          have h1 : 0 ≤ ∑ p ∈ Ineg, w p := Finset.sum_nonneg fun p _ => hw0 p
          have h2 : 0 ≤ ∑ q ∈ Ipos, w q := Finset.sum_nonneg fun q _ => hw0 q
          dsimp only [Sp] at hSp0
          linarith [hlam_sum]
        have hw_neg0 : ∀ p ∈ Ineg, w p = 0 :=
          (Finset.sum_eq_zero_iff_of_nonneg fun p _ => hw0 p).mp hneg0
        have : A = 0 := Finset.sum_eq_zero fun p hp => by rw [hw_neg0 p hp, zero_mul]
        exact hA0 this
      have hx_split : x = (∑ p ∈ Izero, w p • g p) + (∑ pq ∈ Ineg ×ˢ Ipos, lam pq • z pq) := by
        have hs := hsplit (fun p => w p • g p)
        rw [hwx] at hs
        rw [hs, hlam_vec]
        abel
      have hx1_mem : Sp⁻¹ • (∑ pq ∈ Ineg ×ˢ Ipos, lam pq • z pq) ∈ convexHull ℝ (candidates d e) := by
        have hrew : Sp⁻¹ • (∑ pq ∈ Ineg ×ˢ Ipos, lam pq • z pq) =
            ∑ pq ∈ Ineg ×ˢ Ipos, (Sp⁻¹ * lam pq) • z pq := by
          rw [Finset.smul_sum]
          refine Finset.sum_congr rfl fun pq _ => ?_
          rw [smul_smul]
        rw [hrew]
        refine (convex_convexHull ℝ _).sum_mem ?_ ?_ hz_mem
        · intro pq hpq
          exact mul_nonneg (inv_nonneg.mpr hSp_pos.le) (hlam_nonneg pq hpq)
        · rw [← Finset.mul_sum]
          exact inv_mul_cancel₀ hSp_pos.ne'
      by_cases hS0_zero : S0 = 0
      · have hw_zero0 : ∀ p ∈ Izero, w p = 0 :=
          (Finset.sum_eq_zero_iff_of_nonneg fun p _ => hw0 p).mp hS0_zero
        have hSp1 : Sp = 1 := by linarith
        have hsum0 : (∑ p ∈ Izero, w p • g p) = 0 :=
          Finset.sum_eq_zero fun p hp => by rw [hw_zero0 p hp, zero_smul]
        rw [hx_split, hsum0, zero_add]
        simpa [hSp1] using hx1_mem
      · have hS0_pos : 0 < S0 := lt_of_le_of_ne hS0_nonneg (Ne.symm hS0_zero)
        have hx0_mem : S0⁻¹ • (∑ p ∈ Izero, w p • g p) ∈ convexHull ℝ (candidates d e) := by
          have hrew : S0⁻¹ • (∑ p ∈ Izero, w p • g p) =
              ∑ p ∈ Izero, (S0⁻¹ * w p) • g p := by
            rw [Finset.smul_sum]
            refine Finset.sum_congr rfl fun p _ => ?_
            rw [smul_smul]
          rw [hrew]
          refine (convex_convexHull ℝ _).sum_mem ?_ ?_ ?_
          · intro p _
            exact mul_nonneg (inv_nonneg.mpr hS0_pos.le) (hw0 p)
          · rw [← Finset.mul_sum]
            exact inv_mul_cancel₀ hS0_pos.ne'
          · intro p hp
            exact subset_convexHull ℝ _ (Or.inl ⟨p.1, p.2, (Finset.mem_filter.mp hp).2, rfl⟩)
        have hx_comb :
            x = S0 • (S0⁻¹ • (∑ p ∈ Izero, w p • g p)) +
                Sp • (Sp⁻¹ • (∑ pq ∈ Ineg ×ˢ Ipos, lam pq • z pq)) := by
          rw [smul_smul, mul_inv_cancel₀ hS0_pos.ne', one_smul,
            smul_smul, mul_inv_cancel₀ hSp_pos.ne', one_smul]
          exact hx_split
        rw [hx_comb]
        exact (convex_convexHull ℝ _) hx0_mem hx1_mem hS0_nonneg hSp_nonneg hS_sum
  · refine convexHull_min ?_ ((convex_convexHull ℝ _).inter (convex_convexHull ℝ _))
    rintro x (⟨k, σ, hk, rfl⟩ | ⟨k, l, σ, hk, hl, rfl⟩)
    · refine ⟨subset_convexHull ℝ _ ⟨(k, σ), rfl⟩, (mem_simplex_iff he _).mpr ⟨?_, ?_⟩⟩
      · exact orbit_nonneg (pref_nonneg hd k) σ
      · rw [sum_orbit, sum_pref, hk]
    · have hden : 0 < ht d l - ht d k := by linarith
      set α : ℝ := (ht d l - e) / (ht d l - ht d k)
      set β : ℝ := (e - ht d k) / (ht d l - ht d k)
      have hα : 0 ≤ α := div_nonneg (by linarith) hden.le
      have hβ : 0 ≤ β := div_nonneg (by linarith) hden.le
      have hαβ : α + β = 1 := by
        dsimp only [α, β]
        field_simp [hden.ne']
        ring
      have hcut_orb :
          orbit σ (cut d e k l) = α • orbit σ (pref d k) + β • orbit σ (pref d l) := rfl
      refine ⟨?_, (mem_simplex_iff he _).mpr ⟨?_, ?_⟩⟩
      · rw [hcut_orb]
        refine (convex_convexHull ℝ _) ?_ ?_ hα hβ hαβ
        · exact subset_convexHull ℝ _ ⟨(k, σ), rfl⟩
        · exact subset_convexHull ℝ _ ⟨(l, σ), rfl⟩
      · intro i
        rw [hcut_orb]
        exact add_nonneg
          (mul_nonneg hα (orbit_nonneg (pref_nonneg hd k) σ i))
          (mul_nonneg hβ (orbit_nonneg (pref_nonneg hd l) σ i))
      · rw [hcut_orb]
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_add_distrib,
          ← Finset.mul_sum, sum_orbit, sum_pref]
        dsimp only [α, β]
        field_simp [hden.ne']
        ring

private lemma candidates_finite {n : ℕ} (d : Layer n → ℝ) (e : ℝ) : (candidates d e).Finite := by
  have hsub :
      candidates d e ⊆
        Set.range (fun p : Layer n × Equiv.Perm (Fin n) => orbit p.2 (pref d p.1)) ∪
        Set.range (fun p : Layer n × Layer n × Equiv.Perm (Fin n) => orbit p.2.2 (cut d e p.1 p.2.1)) := by
    rintro x (⟨k, σ, _, rfl⟩ | ⟨k, l, σ, _, _, rfl⟩)
    · exact Or.inl ⟨(k, σ), rfl⟩
    · exact Or.inr ⟨(k, l, σ), rfl⟩
  exact ((Set.finite_range _).union (Set.finite_range _)).subset hsub

private lemma score_add {n : ℕ} (c u v : V n) : score c (u + v) = score c u + score c v := by
  simp [score, mul_add, Finset.sum_add_distrib]

private lemma score_smul {n : ℕ} (c : V n) (a : ℝ) (u : V n) : score c (a • u) = a * score c u := by
  simp only [score, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => by ring

private lemma clm_eq_score {n : ℕ} (f : V n →L[ℝ] ℝ) (z : V n) :
    f z = score (fun i => f (Pi.single i 1)) z := by
  have hz : z = ∑ i : Fin n, z i • Pi.single i (1 : ℝ) := by
    ext j
    simp [Pi.single_apply]
  conv_lhs => rw [hz]
  rw [map_sum]
  simp only [map_smul, smul_eq_mul, score]
  refine Finset.sum_congr rfl fun i _ => mul_comm _ _

private lemma mem_extremePoints_convexHull_iff_strict_score {n : ℕ} {C : Set (V n)} (hC : C.Finite)
    (x : V n) :
    x ∈ (convexHull ℝ C).extremePoints ℝ ↔
      x ∈ C ∧ ∃ c : V n, ∀ y ∈ C, y ≠ x → score c y < score c x := by
  constructor
  · intro hx
    have hK_conv : Convex ℝ (convexHull ℝ C) := convex_convexHull ℝ C
    have hdiff_conv : Convex ℝ ((convexHull ℝ C) \ {x}) := by
      rintro u ⟨huK, hux⟩ v ⟨hvK, hvx⟩ a b ha hb hab
      refine ⟨hK_conv huK hvK ha hb hab, ?_⟩
      intro hcomb
      by_cases ha0 : a = 0
      · have hb1 : b = 1 := by linarith
        rw [ha0, hb1, zero_smul, one_smul, zero_add] at hcomb
        exact hvx hcomb
      · by_cases hb0 : b = 0
        · have ha1 : a = 1 := by linarith
          rw [ha1, hb0, one_smul, zero_smul, add_zero] at hcomb
          exact hux hcomb
        · have ha_pos : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
          have hb_pos : 0 < b := lt_of_le_of_ne hb (Ne.symm hb0)
          have hseg : x ∈ openSegment ℝ u v := ⟨a, b, ha_pos, hb_pos, hab, hcomb⟩
          exact hux (hx.2 huK hvK hseg)
    have hsub_diff : convexHull ℝ (C \ {x}) ⊆ (convexHull ℝ C) \ {x} := by
      refine convexHull_min ?_ hdiff_conv
      intro y hy
      exact ⟨subset_convexHull ℝ C hy.1, hy.2⟩
    have hx_not : x ∉ convexHull ℝ (C \ {x}) := fun h => (hsub_diff h).2 rfl
    have hxC : x ∈ C := by
      by_contra hnot
      have hCe : C \ {x} = C := Set.sdiff_singleton_eq_self hnot
      rw [hCe] at hx_not
      exact hx_not hx.1
    refine ⟨hxC, ?_⟩
    have hK'_closed : IsClosed (convexHull ℝ (C \ {x})) :=
      hC.sdiff.isClosed_convexHull ℝ
    obtain ⟨f, u, hfx, hfK'⟩ :=
      geometric_hahn_banach_point_closed (convex_convexHull ℝ (C \ {x})) hK'_closed hx_not
    refine ⟨fun i => -(f (Pi.single i 1)), ?_⟩
    intro y hyC hyne
    have hyK' : y ∈ convexHull ℝ (C \ {x}) := subset_convexHull ℝ _ ⟨hyC, hyne⟩
    have hlt : f x < f y := lt_trans hfx (hfK' y hyK')
    have hneg : ∀ z : V n, score (fun i => -(f (Pi.single i 1))) z = -(f z) := by
      intro z
      rw [clm_eq_score f z]
      simp [score, Finset.sum_neg_distrib]
    rw [hneg y, hneg x]
    linarith
  · rintro ⟨hxC, c, hc⟩
    let M : Set (V n) := {z | score c z < score c x ∨ z = x}
    have hM_conv : Convex ℝ M := by
      intro u hu v hv a b ha hb hab
      have hsumx : a * score c x + b * score c x = score c x := by
        calc a * score c x + b * score c x = (a + b) * score c x := by ring
          _ = score c x := by rw [hab, one_mul]
      rcases hu with hu | hux <;> rcases hv with hv | hvx
      · left
        rw [score_add, score_smul, score_smul]
        by_cases ha0 : a = 0
        · have hb1 : b = 1 := by linarith
          rw [ha0, hb1]
          linarith
        · have ha_pos : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
          have h1 : a * score c u < a * score c x := mul_lt_mul_of_pos_left hu ha_pos
          have h2 : b * score c v ≤ b * score c x := mul_le_mul_of_nonneg_left hv.le hb
          linarith
      · rw [hvx]
        by_cases ha0 : a = 0
        · right
          have hb1 : b = 1 := by linarith
          rw [ha0, hb1, zero_smul, one_smul, zero_add]
        · left
          have ha_pos : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
          rw [score_add, score_smul, score_smul]
          have h1 : a * score c u < a * score c x := mul_lt_mul_of_pos_left hu ha_pos
          linarith
      · rw [hux]
        by_cases hb0 : b = 0
        · right
          have ha1 : a = 1 := by linarith
          rw [ha1, hb0, one_smul, zero_smul, add_zero]
        · left
          have hb_pos : 0 < b := lt_of_le_of_ne hb (Ne.symm hb0)
          rw [score_add, score_smul, score_smul]
          have h2 : b * score c v < b * score c x := mul_lt_mul_of_pos_left hv hb_pos
          linarith
      · right
        rw [hux, hvx, ← add_smul, hab, one_smul]
    have hsubM : convexHull ℝ C ⊆ M := by
      refine convexHull_min ?_ hM_conv
      intro y hy
      by_cases hyx : y = x
      · exact Or.inr hyx
      · exact Or.inl (hc y hy hyx)
    refine ⟨subset_convexHull ℝ C hxC, ?_⟩
    intro u hu v hv hseg
    rcases hseg with ⟨a, b, ha, hb, hab, hcomb⟩
    have hscore : a * score c u + b * score c v = score c x := by
      have := congrArg (score c) hcomb
      rwa [score_add, score_smul, score_smul] at this
    have hsumx : a * score c x + b * score c x = score c x := by
      calc a * score c x + b * score c x = (a + b) * score c x := by ring
        _ = score c x := by rw [hab, one_mul]
    have huM := hsubM hu
    have hvM := hsubM hv
    have hv_le : score c v ≤ score c x := by
      rcases hvM with h | rfl
      · exact h.le
      · exact le_rfl
    rcases huM with h | rfl
    · exfalso
      have h1 : a * score c u < a * score c x := mul_lt_mul_of_pos_left h ha
      have h2 : b * score c v ≤ b * score c x := mul_le_mul_of_nonneg_left hv_le hb.le
      linarith
    · rfl

theorem main_proof : ∀ (n : ℕ) (d : Layer n → ℝ) (e : ℝ), (∀ k, 0 ≤ d k) → 0 < e →
    scaleHull d ∩ simplex n e = convexHull ℝ (candidates d e) ∧
    ∀ x, x ∈ (scaleHull d ∩ simplex n e).extremePoints ℝ ↔
      x ∈ candidates d e ∧ ∃ c : V n, ∀ y ∈ candidates d e, y ≠ x → score c y < score c x := by
  intro n d e hd he
  have hsec := section_eq_convexHull_candidates d e hd he
  refine ⟨hsec, ?_⟩
  intro x
  rw [hsec]
  exact mem_extremePoints_convexHull_iff_strict_score (candidates_finite d e) x

end
end OMA.S_mo_207139_Proof

theorem OMA.solution : type_of% @OMA.S_mo_207139.main :=
  OMA.S_mo_207139_Proof.main_proof
