import OMAStatements.S_mo_381998

/-! The complement of the nine-cycle gives the requested example.
Its singleton branch sets form a clique, and adding a missing edge permits seven branch sets. -/

namespace HadwigerNine

open SimpleGraph Finset OMA.S_mo_381998

private def G : SimpleGraph (Fin 9) where
  Adj i j := i ≠ j ∧ i + 1 ≠ j ∧ j + 1 ≠ i
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.2, h.2.1⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

private instance : DecidableRel G.Adj := fun i j =>
  inferInstanceAs (Decidable (i ≠ j ∧ i + 1 ≠ j ∧ j + 1 ≠ i))

private theorem two_step : ∀ x y : Fin 9,
    x = y ∨ G.Adj x y ∨ ∃ z, G.Adj x z ∧ G.Adj z y := by decide

private theorem connected : G.Connected := by
  refine { preconnected := ?_, nonempty := ⟨0⟩ }
  intro x y
  rcases two_step x y with rfl | h | ⟨z, hx, hy⟩
  · exact Reachable.rfl
  · exact h.reachable
  · exact hx.reachable.trans hy.reachable

private theorem has_adj_triple : ∀ x y z : Fin 9, x ≠ y → x ≠ z → y ≠ z →
    G.Adj x y ∨ G.Adj x z ∨ G.Adj y z := by decide

private theorem chromatic_lower : 4 < G.chromaticNumber := by
  by_contra! h
  obtain ⟨c⟩ := chromaticNumber_le_iff_colorable.mp h
  obtain ⟨z, hz⟩ := Fintype.exists_lt_card_fiber_of_mul_lt_card
    (f := (fun x : Fin 9 => c x)) (n := 2) (by decide)
  obtain ⟨x, y, w, hx, hy, hw, hxy, hxw, hyw⟩ := two_lt_card_iff.mp hz
  have ex := (mem_filter.mp hx).2
  have ey := (mem_filter.mp hy).2
  have ew := (mem_filter.mp hw).2
  rcases has_adj_triple x y w hxy hxw hyw with hxy' | hxw' | hyw'
  · exact c.valid hxy' (ex.trans ey.symm)
  · exact c.valid hxw' (ex.trans ew.symm)
  · exact c.valid hyw' (ey.trans ew.symm)

private def removeColor (v x : Fin 9) : Fin 4 :=
  ⟨((x - v).val - 1) / 2, by have := (x - v).isLt; omega⟩

private theorem removeColor_valid : ∀ v x y : Fin 9, x ≠ v → y ≠ v →
    G.Adj x y → removeColor v x ≠ removeColor v y := by decide

private theorem critical (v : Fin 9) :
    (G.induce ({v}ᶜ : Set (Fin 9))).chromaticNumber < G.chromaticNumber := by
  refine lt_of_le_of_lt (chromaticNumber_le_iff_colorable.mpr ⟨Coloring.mk
    (fun x => removeColor v x.val) ?_⟩) chromatic_lower
  intro x y h
  exact removeColor_valid v x.val y.val x.property y.property h

private theorem clique_bound (S : Finset (Fin 9)) (hs : (S : Set (Fin 9)).Pairwise G.Adj) :
    S.card ≤ 4 := by
  have hinj : Function.Injective (fun x : Fin 9 => x + 1) := by decide
  have hne : ∀ x : Fin 9, x ≠ x + 1 := by decide
  have hd : Disjoint S (S.image (fun x => x + 1)) := by
    rw [Finset.disjoint_left]
    intro x hx hxi
    obtain ⟨y, hy, rfl⟩ := mem_image.mp hxi
    exact (hs hy hx (hne y)).2.1 rfl
  have hc := card_le_univ (s := S ∪ S.image (fun x => x + 1))
  rw [card_union_of_disjoint hd, card_image_of_injective _ hinj] at hc
  simp only [Fintype.card_fin] at hc
  omega

private theorem branch_bound {H : SimpleGraph (Fin 9)} {t : ℕ} (h : HasCompleteMinor H t) :
    t ≤ 9 := by
  classical
  obtain ⟨B, hcon, hd, _⟩ := h
  let rep (i : Fin t) := (Classical.choice (hcon i).nonempty).val
  have hrep (i : Fin t) : rep i ∈ B i := (Classical.choice (hcon i).nonempty).property
  have hinj : Function.Injective rep := by
    intro i j h
    by_contra hn
    exact Set.disjoint_left.mp (hd hn) (hrep i) (h ▸ hrep j)
  simpa using Fintype.card_le_of_injective rep hinj

private theorem original_bound {t : ℕ} (h : HasCompleteMinor G t) : t ≤ 6 := by
  classical
  obtain ⟨B, hcon, hd, hadj⟩ := h
  let T (i : Fin t) : Finset (Fin 9) := (B i).toFinset
  let rep (i : Fin t) := (Classical.choice (hcon i).nonempty).val
  have hrep (i : Fin t) : rep i ∈ B i := (Classical.choice (hcon i).nonempty).property
  have hrepT (i : Fin t) : rep i ∈ T i := by simpa [T] using hrep i
  have hinj : Function.Injective rep := by
    intro i j h
    by_contra hn
    exact Set.disjoint_left.mp (hd hn) (hrep i) (h ▸ hrep j)
  let I : Finset (Fin t) := univ.filter fun i => (T i).card = 1
  have hI (i) : i ∈ I ↔ (T i).card = 1 := by simp [I]
  have huniq {i x} (hi : i ∈ I) (hx : x ∈ B i) : x = rep i :=
    card_le_one_iff.mp (le_of_eq ((hI i).mp hi)) (by simpa [T] using hx) (hrepT i)
  have hsup : I.card ≤ 4 := by
    rw [← card_image_of_injective I hinj]
    apply clique_bound
    intro x hx y hy hxy
    obtain ⟨i, hi, rfl⟩ := mem_image.mp hx
    obtain ⟨j, hj, rfl⟩ := mem_image.mp hy
    obtain ⟨a, ha, b, hb, hab⟩ := hadj i j (fun he => hxy (congrArg rep he))
    simpa only [huniq hi ha, huniq hj hb] using hab
  have hsum : (∑ i, (T i).card) ≤ 9 := by
    have hc := card_le_univ (s := univ.biUnion T)
    rw [card_biUnion] at hc
    · simpa using hc
    · intro i _ j _ hij
      change Disjoint (T i) (T j)
      rw [Finset.disjoint_left]
      intro x hx hy
      exact Set.disjoint_left.mp (hd hij) (by simpa [T] using hx) (by simpa [T] using hy)
  have hcount : 2 * t ≤ (∑ i, (T i).card) + I.card := by
    calc
      2 * t = ∑ _i : Fin t, (2 : ℕ) := by simp [mul_comm]
      _ ≤ ∑ i : Fin t, ((T i).card + if (T i).card = 1 then 1 else 0) := by
        apply sum_le_sum
        intro i _
        have hpos := card_pos.mpr (show (T i).Nonempty from ⟨rep i, hrepT i⟩)
        split <;> omega
      _ = _ := by simp [sum_add_distrib, I]
  omega

private theorem no_big_minor : hadwigerNumber G ≤ 6 := by
  apply csSup_le
  · refine ⟨0, ⟨fun i => Fin.elim0 i, ?_, ?_, ?_⟩⟩
    · intro i; exact Fin.elim0 i
    · intro i; exact Fin.elim0 i
    · intro i; exact Fin.elim0 i
  · exact fun _ h => original_bound h

private def added (k : Fin 9) := G ⊔ SimpleGraph.edge (k + 8) k

private def model (k : Fin 9) : Fin 7 → Finset (Fin 9) :=
  ![{k}, {k + 2}, {k + 4}, {k + 6}, {k + 8}, {k + 1, k + 5}, {k + 3, k + 7}]

private theorem model_connected : ∀ (k : Fin 9) (i : Fin 7), (model k i).Nonempty ∧
    ∀ x ∈ model k i, ∀ y ∈ model k i, x ≠ y → (added k).Adj x y := by
  simp only [added, sup_adj, edge_adj]
  decide

private theorem model_pairs : ∀ (k : Fin 9) (i j : Fin 7), i ≠ j →
    Disjoint (model k i) (model k j) ∧
    ∃ x ∈ model k i, ∃ y ∈ model k j, (added k).Adj x y := by
  simp only [added, sup_adj, edge_adj]
  intro k
  fin_cases k <;> decide

private theorem added_has_minor (k : Fin 9) : HasCompleteMinor (added k) 7 := by
  refine ⟨fun i => (model k i : Set (Fin 9)), ?_, ?_, ?_⟩
  · intro i
    obtain ⟨⟨a, ha⟩, hclique⟩ := model_connected k i
    refine { preconnected := ?_, nonempty := ⟨⟨a, ha⟩⟩ }
    intro x y
    by_cases h : x = y
    · subst y
      exact Reachable.rfl
    · exact (show ((added k).induce (model k i)).Adj x y from
        hclique x.val x.property y.val y.property (fun he => h (Subtype.ext he))).reachable
  · intro i j h
    simpa only [Finset.disjoint_coe] using (model_pairs k i j h).1
  · intro i j h
    exact (model_pairs k i j h).2

private theorem added_large (k : Fin 9) : 7 ≤ hadwigerNumber (added k) :=
  le_csSup (show BddAbove {t | HasCompleteMinor (added k) t} from
    ⟨9, fun _ h => branch_bound h⟩) (added_has_minor k)

end HadwigerNine

open SimpleGraph OMA.S_mo_381998 HadwigerNine

theorem OMA.solution : type_of% @OMA.S_mo_381998.main := by
  refine ⟨9, G, connected, ?_, critical, ?_⟩
  · intro h
    have : G.Adj 0 1 := by simp [h]
    exact (by decide : ¬ G.Adj 0 1) this
  · intro v w hne h
    have hor : v + 1 = w ∨ w + 1 = v := by
      by_contra hn
      push Not at hn
      exact h ⟨hne, hn.1, hn.2⟩
    have hm : ∀ x y : Fin 9, x + 1 = y → y + 8 = x := by decide
    rcases hor with h | h
    · have hx := added_large w
      simpa [added, hm v w h] using lt_of_le_of_lt no_big_minor (lt_of_lt_of_le (by decide : 6 < 7) hx)
    · have hx := added_large v
      simpa [added, hm w v h, edge_comm w v] using
        lt_of_le_of_lt no_big_minor (lt_of_lt_of_le (by decide : 6 < 7) hx)
