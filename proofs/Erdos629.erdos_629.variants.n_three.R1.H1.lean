import OMAReductions.R_Erdos629_erdos_629_variants_n_three_R1

/-!
# Proof of `Erdos629.erdos_629.variants.n_three.R1.H1`

We exhibit `K_{7,7}` as a bipartite (`2`-colorable) graph on `14` vertices whose list chromatic
number exceeds `3`: assigning the `7` lines of the Fano plane to each part forces any proper list
coloring to induce a monochromatic line on one side, contradicting that the Fano plane has no
`2`-coloring without monochromatic lines.
-/

open SimpleGraph

namespace OMA.Erdos629H1

/-- The complete bipartite graph `K_{7,7}` on `Fin 14` (`0..6` vs `7..13`). -/
def K77 : SimpleGraph (Fin 14) where
  Adj u v := (u.val < 7 ∧ 7 ≤ v.val) ∨ (7 ≤ u.val ∧ v.val < 7)
  symm := ⟨fun _ _ h => by
    rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inr ⟨h2, h1⟩
    · exact Or.inl ⟨h2, h1⟩⟩
  loopless := ⟨fun _ h => by omega⟩

lemma K77_colorable2 : K77.Colorable 2 := by
  refine ⟨Coloring.mk (fun u => if u.val < 7 then (0 : Fin 2) else 1) ?_⟩
  intro u v h
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [if_pos h1, if_neg (by omega)]; decide
  · rw [if_neg (by omega), if_pos h2]; decide

lemma isKChoosable_of_card {m : ℕ} (G : SimpleGraph (Fin m)) : G.IsKChoosable m := by
  intro L hL
  have hrec : ∀ r, ∀ (hr : r ≤ m), ∃ f : Fin r → ℕ, Function.Injective f ∧
      ∀ i : Fin r, f i ∈ L ⟨i.val, by have := i.isLt; omega⟩ := by
    intro r
    induction r with
    | zero =>
      intro _
      exact ⟨Fin.elim0, fun i => Fin.elim0 i, fun i => Fin.elim0 i⟩
    | succ r ih =>
      intro hr
      obtain ⟨f, hfinj, hfmem⟩ := ih (by omega)
      let used : Finset ℕ := Finset.univ.image f
      have hcard_used : used.card ≤ r := by
        calc used.card ≤ (Finset.univ : Finset (Fin r)).card := Finset.card_image_le
          _ = r := Finset.card_fin r
      have hne : (L ⟨r, by omega⟩ \ used).Nonempty := by
        by_contra hnone
        rw [Finset.not_nonempty_iff_eq_empty, Finset.sdiff_eq_empty_iff_subset] at hnone
        have hle := Finset.card_le_card hnone
        rw [hL ⟨r, by omega⟩] at hle
        omega
      obtain ⟨c, hc⟩ := hne
      rw [Finset.mem_sdiff, Finset.mem_image] at hc
      let g : Fin (r + 1) → ℕ := fun i => if hi : i.val < r then f ⟨i.val, hi⟩ else c
      refine ⟨g, ?_, ?_⟩
      · intro i j hij
        dsimp only [g] at hij
        by_cases hi : i.val < r <;> by_cases hj : j.val < r
        · simp only [dif_pos hi, dif_pos hj] at hij
          have hval := congrArg Fin.val (hfinj hij)
          exact Fin.ext hval
        · simp only [dif_pos hi, dif_neg hj] at hij
          exfalso
          exact hc.2 ⟨⟨i.val, hi⟩, Finset.mem_univ _, hij⟩
        · simp only [dif_neg hi, dif_pos hj] at hij
          exfalso
          exact hc.2 ⟨⟨j.val, hj⟩, Finset.mem_univ _, hij.symm⟩
        · have hi' : i.val = r := by have := i.isLt; omega
          have hj' : j.val = r := by have := j.isLt; omega
          exact Fin.ext (hi'.trans hj'.symm)
      · intro i
        dsimp only [g]
        by_cases hi : i.val < r
        · simp only [dif_pos hi]
          exact hfmem ⟨i.val, hi⟩
        · simp only [dif_neg hi]
          have hi' : i.val = r := by have := i.isLt; omega
          convert hc.1 using 2
          exact Fin.ext hi'
  obtain ⟨f, hfinj, hfmem⟩ := hrec m le_rfl
  refine ⟨Coloring.mk (fun v => f ⟨v.val, v.isLt⟩) ?_, ?_⟩
  · intro u v huv
    exact hfinj.ne (Fin.ext_iff.not.mpr (Fin.ext_iff.not.mp (G.ne_of_adj huv)))
  · intro v
    exact hfmem ⟨v.val, v.isLt⟩

lemma isKChoosable_mono {W : Type*} {G : SimpleGraph W} {k m : ℕ}
    (hkm : k ≤ m) (hk : G.IsKChoosable k) : G.IsKChoosable m := by
  intro L hL
  have hex : ∀ v, ∃ s ⊆ L v, s.card = k := fun v =>
    Finset.exists_subset_card_eq (by rw [hL v]; exact hkm)
  let L' : W → Finset ℕ := fun v => Classical.choose (hex v)
  have hL'_sub : ∀ v, L' v ⊆ L v := fun v => (Classical.choose_spec (hex v)).1
  have hL'_card : ∀ v, (L' v).card = k := fun v => (Classical.choose_spec (hex v)).2
  obtain ⟨C, hC⟩ := hk L' hL'_card
  exact ⟨C, fun v => hL'_sub v (hC v)⟩

/-- Helper indexing a `7`-tuple of Booleans by `Fin 7`. -/
def boolAt (b0 b1 b2 b3 b4 b5 b6 : Bool) : Fin 7 → Bool
  | 0 => b0
  | 1 => b1
  | 2 => b2
  | 3 => b3
  | 4 => b4
  | 5 => b5
  | 6 => b6

/-- The `7` lines of the Fano plane on `{0, ..., 6}`. -/
def fanoLine : Fin 7 → Finset ℕ
  | 0 => {0, 1, 3}
  | 1 => {1, 2, 4}
  | 2 => {2, 3, 5}
  | 3 => {3, 4, 6}
  | 4 => {4, 5, 0}
  | 5 => {5, 6, 1}
  | 6 => {6, 0, 2}

lemma fanoLine_card (i : Fin 7) : (fanoLine i).card = 3 := by
  fin_cases i <;> decide

lemma fanoLine_lt (i : Fin 7) {x : ℕ} (hx : x ∈ fanoLine i) : x < 7 := by
  fin_cases i <;> simp [fanoLine] at hx <;> omega

lemma fano_no_two_coloring :
    ∀ b0 b1 b2 b3 b4 b5 b6 : Bool,
      ¬ ∀ i : Fin 7,
        (∃ x : Fin 7, x.val ∈ fanoLine i ∧ boolAt b0 b1 b2 b3 b4 b5 b6 x = true) ∧
        (∃ y : Fin 7, y.val ∈ fanoLine i ∧ boolAt b0 b1 b2 b3 b4 b5 b6 y = false) := by
  decide

lemma K77_not_choosable3 : ¬ K77.IsKChoosable 3 := by
  intro h
  let L : Fin 14 → Finset ℕ := fun u => fanoLine ⟨u.val % 7, Nat.mod_lt _ (by decide)⟩
  have hL : ∀ u, (L u).card = 3 := fun u => fanoLine_card _
  obtain ⟨C, hC⟩ := h L hL
  let f : Fin 7 → Bool := fun x => decide (∃ j : Fin 7, C ⟨j.val, by omega⟩ = x.val)
  have hbool : ∀ x : Fin 7, boolAt (f 0) (f 1) (f 2) (f 3) (f 4) (f 5) (f 6) x = f x := by
    intro x
    fin_cases x <;> rfl
  refine fano_no_two_coloring (f 0) (f 1) (f 2) (f 3) (f 4) (f 5) (f 6) ?_
  intro i
  constructor
  · have hmem : C ⟨i.val, by omega⟩ ∈ fanoLine i := by
      have hi := hC ⟨i.val, by omega⟩
      dsimp only [L] at hi
      have hmod : i.val % 7 = i.val := Nat.mod_eq_of_lt i.isLt
      convert hi using 2
      exact Fin.ext hmod.symm
    refine ⟨⟨C ⟨i.val, by omega⟩, fanoLine_lt i hmem⟩, hmem, ?_⟩
    rw [hbool]
    exact decide_eq_true ⟨i, rfl⟩
  · have hmem : C ⟨i.val + 7, by omega⟩ ∈ fanoLine i := by
      have hi := hC ⟨i.val + 7, by omega⟩
      dsimp only [L] at hi
      have hmod : (i.val + 7) % 7 = i.val := by have := i.isLt; omega
      convert hi using 2
      exact Fin.ext hmod.symm
    refine ⟨⟨C ⟨i.val + 7, by omega⟩, fanoLine_lt i hmem⟩, hmem, ?_⟩
    rw [hbool]
    rw [decide_eq_false_iff_not]
    rintro ⟨j, hj⟩
    have hadj : K77.Adj ⟨j.val, by have := j.isLt; omega⟩ ⟨i.val + 7, by have := i.isLt; omega⟩ :=
      Or.inl ⟨j.isLt, by dsimp; omega⟩
    exact C.valid hadj hj

lemma K77_listChromaticNumber_gt_three : 3 < K77.listChromaticNumber := by
  by_contra hle
  have hle3 : K77.listChromaticNumber ≤ 3 := Nat.not_lt.mp hle
  have hne : {k : ℕ | K77.IsKChoosable k}.Nonempty := ⟨14, isKChoosable_of_card K77⟩
  have hchoos : K77.IsKChoosable K77.listChromaticNumber := Nat.sInf_mem hne
  exact K77_not_choosable3 (isKChoosable_mono hle3 hchoos)

end OMA.Erdos629H1

theorem OMA.solution : OMA.R_Erdos629_erdos_629_variants_n_three_R1.H1 :=
  Erdos629.n_le OMA.Erdos629H1.K77 OMA.Erdos629H1.K77_colorable2
    OMA.Erdos629H1.K77_listChromaticNumber_gt_three
