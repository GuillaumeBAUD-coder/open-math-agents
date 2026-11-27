import OMAReductions.R_Erdos629_erdos_629_variants_n_three_R1

-- Step Erdos629.erdos_629.variants.n_three.R1.H1: hypothesis H1 of reduction Erdos629.erdos_629.variants.n_three.R1
-- Credit: @BeautifulPrinessxx
-- H1 := Erdos629.n 3 ≤ 14

/-!
# `n(3) ≤ 14`

The witness is the complete bipartite graph `K_{7,7}` on `Fin 14` (vertices `0..6` on the left,
`7..13` on the right). Give vertex `v` the list made of the points of line number `v % 7` of the
Fano plane. A choice of colours from these lists would put, on each line, a point chosen on the
left and a point chosen on the right; since every left vertex is adjacent to every right vertex,
the colours used on the left are never used on the right. Colouring the Fano plane by
"used on the left or not" would then give a 2-colouring without monochromatic line, which does
not exist (the Fano plane does not have property B, checked by `decide`).
-/

namespace OMA.Erdos629N3H1

open SimpleGraph

/-- `K_{7,7}` on `Fin 14`: `v` is on the left when `v < 7`. -/
def K77 : SimpleGraph (Fin 14) where
  Adj i j := (i.val < 7 ∧ 7 ≤ j.val) ∨ (7 ≤ i.val ∧ j.val < 7)
  symm := ⟨fun i j h => by
    rcases h with h | h
    · exact Or.inr ⟨h.2, h.1⟩
    · exact Or.inl ⟨h.2, h.1⟩⟩
  loopless := ⟨fun i h => by
    rcases h with h | h <;> omega⟩

/-- The seven lines of the Fano plane on the points `Fin 7`. -/
def fanoLine : Fin 7 → Finset (Fin 7)
  | 0 => {0, 1, 2}
  | 1 => {0, 3, 4}
  | 2 => {0, 5, 6}
  | 3 => {1, 3, 5}
  | 4 => {1, 4, 6}
  | 5 => {2, 3, 6}
  | 6 => {2, 4, 5}

set_option maxRecDepth 100000 in
/-- The Fano plane does not have property B: every 2-colouring has a monochromatic line. -/
lemma fano_no_property_B : ∀ g : Fin 7 → Bool, ∃ i : Fin 7, ∃ b : Bool, ∀ p ∈ fanoLine i, g p = b := by
  decide

lemma fanoLine_card (i : Fin 7) : (fanoLine i).card = 3 := by
  fin_cases i <;> rfl

/-- The line attached to a vertex of `K_{7,7}`. -/
def lineOf (v : Fin 14) : Fin 7 := ⟨v.val % 7, Nat.mod_lt _ (by norm_num)⟩

/-- The list of vertex `v`: the points of its Fano line, as natural numbers. -/
def lists (v : Fin 14) : Finset ℕ := (fanoLine (lineOf v)).map Fin.valEmbedding

lemma lists_card (v : Fin 14) : (lists v).card = 3 := by
  simp [lists, fanoLine_card]

lemma K77_colorable : K77.Colorable 2 := by
  refine ⟨Coloring.mk (fun v => if v.val < 7 then (0 : Fin 2) else 1) ?_⟩
  intro v w h
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · have h3 : ¬ w.val < 7 := by omega
    simp [h1, h3]
  · have h3 : ¬ v.val < 7 := by omega
    simp [h2, h3]

/-- The lists `lists` admit no proper choice: `K_{7,7}` is not 3-choosable. -/
lemma not_choosable_three : ¬ K77.IsKChoosable 3 := by
  intro h
  obtain ⟨C, hC⟩ := h lists lists_card
  let left : Fin 7 → Fin 14 := fun i => ⟨i.val, by omega⟩
  let right : Fin 7 → Fin 14 := fun i => ⟨i.val + 7, by omega⟩
  have hleft : ∀ i : Fin 7, lineOf (left i) = i := by
    intro i; ext; simp [lineOf, left, Nat.mod_eq_of_lt i.isLt]
  have hright : ∀ i : Fin 7, lineOf (right i) = i := by
    intro i; ext; simp [lineOf, right, Nat.mod_eq_of_lt i.isLt]
  have hadj : ∀ i j : Fin 7, K77.Adj (left i) (right j) := by
    intro i j; left; exact ⟨by simp [left], by simp [right]⟩
  -- colour of a point: is it used on the left?
  let g : Fin 7 → Bool := fun p => decide (∃ i : Fin 7, C (left i) = p.val)
  obtain ⟨i, b, hb⟩ := fano_no_property_B g
  cases b with
  | true =>
    -- the right vertex of line `i` picks a point of the line, which is used on the left
    have hmem := hC (right i)
    simp only [lists, hright, Finset.mem_map, Fin.valEmbedding_apply] at hmem
    obtain ⟨p, hp, hpC⟩ := hmem
    have hgp := hb p hp
    simp only [g, decide_eq_true_eq] at hgp
    obtain ⟨j, hj⟩ := hgp
    exact C.valid (hadj j i) (hj.trans hpC)
  | false =>
    -- the left vertex of line `i` picks a point of the line, which is then used on the left
    have hmem := hC (left i)
    simp only [lists, hleft, Finset.mem_map, Fin.valEmbedding_apply] at hmem
    obtain ⟨p, hp, hpC⟩ := hmem
    have hgp := hb p hp
    simp only [g, decide_eq_false_iff_not, not_exists] at hgp
    exact hgp i hpC.symm

/-- Choosability is monotone in the list size. -/
lemma choosable_mono {j k : ℕ} (hjk : j ≤ k) (h : K77.IsKChoosable j) : K77.IsKChoosable k := by
  intro L hL
  have hsub : ∀ v, ∃ t ⊆ L v, t.card = j := fun v =>
    Finset.exists_subset_card_eq (by rw [hL v]; exact hjk)
  choose L' hL'sub hL'card using hsub
  obtain ⟨C, hC⟩ := h L' hL'card
  exact ⟨C, fun v => hL'sub v (hC v)⟩

/-- `K_{7,7}` is 14-choosable: choose freely on the left, then avoid those at most 7 colours on
the right. -/
lemma choosable_fourteen : K77.IsKChoosable 14 := by
  intro L hL
  have hne : ∀ v, (L v).Nonempty := fun v => by
    rw [← Finset.card_pos, hL v]; norm_num
  choose f hf using hne
  let T : Finset ℕ := (Finset.univ.filter (fun v : Fin 14 => v.val < 7)).image f
  have hT : T.card ≤ 7 :=
    Finset.card_image_le.trans (by decide)
  have hne2 : ∀ v, (L v \ T).Nonempty := by
    intro v
    rw [← Finset.card_pos]
    have := Finset.le_card_sdiff T (L v)
    rw [hL v] at this
    omega
  choose g hg using hne2
  have hfT : ∀ v : Fin 14, v.val < 7 → f v ∈ T := fun v hv =>
    Finset.mem_image.mpr ⟨v, by simp [hv], rfl⟩
  have hgT : ∀ v : Fin 14, g v ∉ T := fun v => (Finset.mem_sdiff.mp (hg v)).2
  refine ⟨Coloring.mk (fun v => if v.val < 7 then f v else g v) ?_, ?_⟩
  · intro v w h
    rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · have h3 : ¬ w.val < 7 := by omega
      simp only [h1, h3, if_true, if_false]
      intro heq
      exact hgT w (heq ▸ hfT v h1)
    · have h3 : ¬ v.val < 7 := by omega
      simp only [h2, h3, if_true, if_false]
      intro heq
      exact hgT v (heq.symm ▸ hfT w h2)
  · intro v
    show (if v.val < 7 then f v else g v) ∈ L v
    by_cases hv : v.val < 7
    · rw [if_pos hv]; exact hf v
    · rw [if_neg hv]; exact (Finset.mem_sdiff.mp (hg v)).1

lemma three_lt_listChromaticNumber : 3 < K77.listChromaticNumber := by
  unfold listChromaticNumber
  apply Nat.lt_of_succ_le
  apply le_csInf ⟨14, choosable_fourteen⟩
  intro k hk
  by_contra hlt
  exact not_choosable_three (choosable_mono (by omega) hk)

end OMA.Erdos629N3H1

theorem OMA.solution : OMA.R_Erdos629_erdos_629_variants_n_three_R1.H1 :=
  Erdos629.n_le OMA.Erdos629N3H1.K77 OMA.Erdos629N3H1.K77_colorable
    OMA.Erdos629N3H1.three_lt_listChromaticNumber
