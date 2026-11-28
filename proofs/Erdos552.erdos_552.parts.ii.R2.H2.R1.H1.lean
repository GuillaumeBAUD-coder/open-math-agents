import OMAReductions.R_Erdos552_erdos_552_parts_ii_R2_H2_R1

/-!
Step H1 of reduction Erdos552.erdos_552.parts.ii.R2.H2.R1: every quadrilateral-free graph on
`Fin N` extends to a saturated one. Take a quadrilateral-free supergraph with the most edges.
For a nonedge `xy`, adding it creates a copy of `C₄`; exactly one cycle edge is the new edge
(the copy is injective), and the other three edges form the required path from `x` to `y`.
-/

open SimpleGraph Finset

namespace OMA.E552H1

lemma cyc_adj (i : Fin 4) : (cycleGraph 4).Adj i (i + 1) := by
  revert i; decide

lemma cyc_cases {u v : Fin 4} (h : (cycleGraph 4).Adj u v) : v = u + 1 ∨ u = v + 1 := by
  revert u v; decide

lemma fin4_ne2 (i : Fin 4) : i + 1 ≠ i ∧ i + 2 ≠ i ∧ i + 3 ≠ i := by
  revert i; decide

lemma fin4_cross : ∀ i j : Fin 4, j ≠ i → ¬ (j = i ∧ j + 1 = i + 1) ∧ ¬ (j = i + 1 ∧ j + 1 = i) := by
  decide

lemma fin4_ne (i : Fin 4) : i + 3 ≠ i + 1 ∧ i + 2 ≠ i ∧ i + 3 + 1 = i ∧ i + 1 + 1 = i + 2 ∧
    i + 2 + 1 = i + 3 := by
  revert i; decide

/-- The only cycle edge that may be missing from `S` is the new edge. -/
lemma key {N : ℕ} (S : SimpleGraph (Fin N)) (x y : Fin N)
    (f : Copy (cycleGraph 4) (S ⊔ edge x y)) (hno : ¬ (cycleGraph 4).IsContained S) :
    ∃ a b, a ≠ y ∧ b ≠ x ∧ S.Adj x a ∧ S.Adj a b ∧ S.Adj b y := by
  have hinj := f.injective
  have hadj : ∀ j : Fin 4, (S ⊔ edge x y).Adj (f j) (f (j + 1)) :=
    fun j => f.toHom.map_adj (cyc_adj j)
  -- some cycle edge is not in `S`
  have hex : ∃ i : Fin 4, ¬ S.Adj (f i) (f (i + 1)) := by
    by_contra hall
    simp only [not_exists, not_not] at hall
    apply hno
    refine ⟨⟨⟨f, fun {u v} huv => ?_⟩, hinj⟩⟩
    rcases cyc_cases huv with rfl | rfl
    · exact hall u
    · exact (hall v).symm
  obtain ⟨i, hi⟩ := hex
  have hnew : ∀ j : Fin 4, ¬ S.Adj (f j) (f (j + 1)) →
      (f j = x ∧ f (j + 1) = y) ∨ (f j = y ∧ f (j + 1) = x) := by
    intro j hj
    have := hadj j
    rw [sup_adj, edge_adj] at this
    rcases this with h | ⟨h, _⟩
    · exact absurd h hj
    · exact h
  have hold : ∀ j : Fin 4, j ≠ i → S.Adj (f j) (f (j + 1)) := by
    intro j hji
    by_contra hj
    have h1 := hnew i hi
    have h2 := hnew j hj
    obtain ⟨c1, c2⟩ := fin4_cross i j hji
    rcases h1 with ⟨a1, b1⟩ | ⟨a1, b1⟩ <;> rcases h2 with ⟨a2, b2⟩ | ⟨a2, b2⟩
    · exact c1 ⟨hinj (a2.trans a1.symm), hinj (b2.trans b1.symm)⟩
    · exact c2 ⟨hinj (a2.trans b1.symm), hinj (b2.trans a1.symm)⟩
    · exact c2 ⟨hinj (a2.trans b1.symm), hinj (b2.trans a1.symm)⟩
    · exact c1 ⟨hinj (a2.trans a1.symm), hinj (b2.trans b1.symm)⟩
  obtain ⟨n31, n20, e3, e1, e2⟩ := fin4_ne i
  have hfin2 := fin4_ne2 i
  have s1 := hold (i + 1) hfin2.1
  have s2 := hold (i + 2) hfin2.2.1
  have s3 := hold (i + 3) hfin2.2.2
  rw [e1] at s1
  rw [e2] at s2
  rw [e3] at s3
  rcases hnew i hi with ⟨hx, hy⟩ | ⟨hy, hx⟩
  · -- x = f i, y = f (i+1): path x, f (i+3), f (i+2), y
    rw [hx] at s3
    rw [hy] at s1
    refine ⟨f (i + 3), f (i + 2), fun h => n31 (hinj (h.trans hy.symm)),
      fun h => n20 (hinj (h.trans hx.symm)), s3.symm, s2.symm, s1.symm⟩
  · -- y = f i, x = f (i+1): path x, f (i+2), f (i+3), y
    rw [hy] at s3
    rw [hx] at s1
    refine ⟨f (i + 2), f (i + 3), fun h => n20 (hinj (h.trans hy.symm)),
      fun h => n31 (hinj (h.trans hx.symm)), s1, s2, s3⟩

end OMA.E552H1

open Classical in
theorem OMA.solution : OMA.R_Erdos552_erdos_552_parts_ii_R2_H2_R1.H1 := by
  intro N G hG
  let s := (univ : Finset (SimpleGraph (Fin N))).filter
    (fun S => G ≤ S ∧ ¬ (cycleGraph 4).IsContained S)
  let w : SimpleGraph (Fin N) → ℕ := fun S =>
    ((univ : Finset (Fin N × Fin N)).filter (fun p => S.Adj p.1 p.2)).card
  obtain ⟨S, hS, hmax⟩ := exists_max_image s w ⟨G, by
    simp only [s, mem_filter, mem_univ, true_and]; exact ⟨le_rfl, hG⟩⟩
  simp only [s, mem_filter, mem_univ, true_and] at hS hmax
  refine ⟨S, hS.1, hS.2, fun x y hxy hnadj => ?_⟩
  by_cases hC : (cycleGraph 4).IsContained (S ⊔ edge x y)
  · obtain ⟨f⟩ := hC
    exact OMA.E552H1.key S x y f hS.2
  · exfalso
    have hle := hmax (S ⊔ edge x y) ⟨hS.1.trans le_sup_left, hC⟩
    have hlt : w S < w (S ⊔ edge x y) := by
      apply card_lt_card
      rw [Finset.ssubset_iff_of_subset]
      · refine ⟨(x, y), ?_, ?_⟩
        · simp [edge_adj, hxy]
        · simp [hnadj]
      · intro p hp
        simp only [mem_filter, mem_univ, true_and] at hp ⊢
        exact Or.inl hp
    omega
