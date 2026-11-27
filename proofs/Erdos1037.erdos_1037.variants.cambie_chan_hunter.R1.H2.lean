import OMAReductions.R_Erdos1037_erdos_1037_variants_cambie_chan_hunter_R1

/-! Each of eight blocks induces the input graph. Complementary adjacency into
a second block cancels the internal degree. A staircase into a third adds
the vertex index. Complete joins give six consecutive disjoint degree intervals. -/

namespace OMA.DegreeBlocks
open SimpleGraph
open scoped Classical

private def tag : Fin 8 → Fin 8 → ℕ :=
  ![![0, 1, 2, 4, 4, 4, 4, 4],
    ![1, 0, 3, 2, 3, 3, 3, 3],
    ![2, 3, 0, 1, 3, 3, 3, 4],
    ![4, 2, 1, 0, 4, 3, 4, 4],
    ![4, 3, 3, 4, 0, 1, 2, 4],
    ![4, 3, 3, 3, 1, 0, 4, 2],
    ![4, 3, 3, 4, 2, 4, 0, 1],
    ![4, 3, 4, 4, 4, 2, 1, 0]]

private def band : Fin 8 → Fin 7 := ![1, 6, 5, 2, 3, 4, 3, 2]
private def bit : Fin 8 → Fin 2 := ![0, 0, 0, 0, 0, 0, 1, 1]
private def repr : Fin 6 → Fin 8 := ![0, 3, 4, 5, 2, 1]

private lemma tag_symm : ∀ a b, tag a b = tag b a := by decide
private lemma tag_diag : ∀ a, tag a a = 0 := by decide

private def relation {m} (G : SimpleGraph (Fin m)) (a b : Fin 8) (x y : Fin m) : Prop :=
  match tag a b with
  | 0 => G.Adj x y
  | 1 => ¬G.Adj x y
  | 2 => m ≤ x.val + y.val
  | 3 => True
  | _ => False

private def graph {m} (G : SimpleGraph (Fin m)) : SimpleGraph (Fin 8 × Fin m) where
  Adj u v := relation G u.1 v.1 u.2 v.2
  symm := by
    constructor
    rintro ⟨a,x⟩ ⟨b,y⟩
    change relation G a b x y → relation G b a y x
    simp only [relation, tag_symm b a, G.adj_comm y x, Nat.add_comm y.val x.val, imp_self]
  loopless := by
    constructor
    rintro ⟨a,x⟩
    simp [relation, tag_diag]

private lemma slices {α β γ : Type} [Fintype α] [Fintype β] [Fintype γ]
    (e : α × β ≃ γ) (s : Set γ) :
    s.ncard = ∑ a, {x : β | e (a,x) ∈ s}.ncard := by
  classical
  let u : {v : α × β // e v ∈ s} ≃ Σ a : α, {x : β // e (a,x) ∈ s} :=
    { toFun := fun v => ⟨v.val.1, v.val.2, v.property⟩
      invFun := fun ⟨a,x⟩ => ⟨(a,x.val), x.property⟩
      left_inv := by intro v; rfl
      right_inv := by rintro ⟨a,x⟩; rfl }
  let f : {v : α × β // e v ∈ s} ≃ s :=
    { toFun := fun v => ⟨e v.val, v.property⟩
      invFun := fun v => ⟨e.symm v.val, by simp⟩
      left_inv := by intro v; apply Subtype.ext; exact e.symm_apply_apply _
      right_inv := by intro v; apply Subtype.ext; exact e.apply_symm_apply _ }
  change Nat.card s = ∑ a, Nat.card {x : β // e (a,x) ∈ s}
  simpa only [Nat.card_sigma] using Nat.card_congr (f.symm.trans u)

private lemma staircase {m : ℕ} (x : Fin m) :
    {y : Fin m | m ≤ x.val + y.val}.ncard = x.val := by
  let e : {y : Fin m // m ≤ x.val + y.val} ≃ Fin x.val :=
    { toFun := fun y => ⟨y.val.val - (m - x.val), by have := y.val.isLt; omega⟩
      invFun := fun i => ⟨⟨m - x.val + i.val, by have := i.isLt; omega⟩, by dsimp; omega⟩
      left_inv := by intro y; apply Subtype.ext; apply Fin.ext; have := y.property; dsimp; omega
      right_inv := by intro i; apply Fin.ext; dsimp; omega }
  change Nat.card {y : Fin m // m ≤ x.val + y.val} = x.val
  simpa only [Nat.card_fin] using Nat.card_congr e

private def rowCount (m p q x : ℕ) : ℕ → ℕ
  | 0 => p
  | 1 => q
  | 2 => x
  | 3 => m
  | _ => 0

private lemma count_rows (m p q x : ℕ) (h : p + q = m) (a : Fin 8) :
    (∑ b, rowCount m p q x (tag a b)) = x + m * (band a).val := by
  fin_cases a <;> simp [Fin.sum_univ_succ, tag, band, rowCount, Matrix.cons_val_succ] <;> omega

private lemma count_slice {m} (G : SimpleGraph (Fin m)) (a b : Fin 8) (x : Fin m) :
    {y : Fin m | relation G a b x y}.ncard =
      rowCount m (G.neighborSet x).ncard (G.neighborSet x)ᶜ.ncard x.val (tag a b) := by
  unfold relation
  generalize tag a b = z
  match z with
  | 0 => rfl
  | 1 => rfl
  | 2 => exact staircase x
  | 3 => simp [rowCount]
  | n + 4 => simp [rowCount]

private def build {m} (G : SimpleGraph (Fin m)) : SimpleGraph (Fin (8*m)) :=
  (graph G).comap finProdFinEquiv.symm

private lemma adj_build {m} (G : SimpleGraph (Fin m)) (a b : Fin 8) (x y : Fin m) :
    (build G).Adj (finProdFinEquiv (a,x)) (finProdFinEquiv (b,y)) ↔
      relation G a b x y := by simp [build, SimpleGraph.comap_adj, graph]

private lemma degree_build {m} (G : SimpleGraph (Fin m)) (a : Fin 8) (x : Fin m) :
    ((build G).neighborSet (finProdFinEquiv (a,x))).ncard =
      (finProdFinEquiv (band a,x)).val := by
  rw [slices finProdFinEquiv]
  simp only [SimpleGraph.mem_neighborSet, adj_build, count_slice]
  exact count_rows _ _ _ _ (by simpa using Set.ncard_add_ncard_compl (G.neighborSet x)) a

end OMA.DegreeBlocks

open OMA.DegreeBlocks in
theorem OMA.solution : OMA.R_Erdos1037_erdos_1037_variants_cambie_chan_hunter_R1.H2 := by
  classical
  intro m hm G t ht
  let e : Fin 8 × Fin m ≃ Fin (8*m) := finProdFinEquiv
  let F := build G
  let degree := fun v => (F.neighborSet v).ncard
  have hd (a : Fin 8) (x : Fin m) : degree (e (a,x)) = (finProdFinEquiv (band a,x)).val :=
    degree_build G a x
  have heq {a b : Fin 8} {x y : Fin m} (h : degree (e (a,x)) = degree (e (b,y))) :
      (band a,x) = (band b,y) := finProdFinEquiv.injective (Fin.ext ((hd a x).symm.trans (h.trans (hd b y))))
  refine ⟨F, ?_, ?_, ?_, ?_⟩
  · intro d
    let s := {v | degree v = d}
    have inj : Set.InjOn (fun v => bit (e.symm v).1) s := by
      intro v hv w hw h
      obtain ⟨⟨a,x⟩,rfl⟩ := e.surjective v
      obtain ⟨⟨b,y⟩,rfl⟩ := e.surjective w
      simp only [e.symm_apply_apply] at h
      obtain ⟨hab,hxy⟩ := Prod.mk.inj (heq (hv.trans hw.symm))
      have uniq : ∀ i j, band i = band j → bit i = bit j → i = j := by decide
      rw [uniq a b hab h, hxy]
    simpa using Set.ncard_le_ncard_of_injOn (t := (Set.univ : Set (Fin 2))) _ (fun _ _ => Set.mem_univ _) inj
  · let f : Fin 6 × Fin m → ℕ := fun u => degree (e (repr u.1,u.2))
    have hf : Function.Injective f := by
      rintro ⟨a,x⟩ ⟨b,y⟩ h
      obtain ⟨hab,hxy⟩ := Prod.mk.inj (heq h)
      have unique : ∀ i j, band (repr i) = band (repr j) → i = j := by decide
      exact Prod.ext (unique a b hab) hxy
    have hsub : Set.range f ⊆ Set.range degree := by
      rintro _ ⟨u,rfl⟩
      exact ⟨_,rfl⟩
    have h := Set.ncard_le_ncard hsub (Set.finite_range _)
    rw [Set.ncard_range_of_injective hf] at h
    have h' : 6*m ≤ (Set.range degree).ncard := by simpa using h
    change 3/4 * ((8*m : ℕ) : ℝ) ≤ ((Set.range degree).ncard : ℝ)
    exact_mod_cast (show (3:ℝ)/4 * (8*(m:ℝ)) ≤ ((Set.range degree).ncard : ℝ) by
      have hh : (6:ℝ)*m ≤ ((Set.range degree).ncard : ℝ) := by exact_mod_cast h'
      linarith)
  · intro s hs
    have hadj (a : Fin 8) (x y : Fin m) : F.Adj (e (a,x)) (e (a,y)) ↔ G.Adj x y := by
      simpa [relation, tag_diag] using adj_build G a a x y
    have bound (a : Fin 8) : ({x : Fin m | e (a,x) ∈ s}.ncard : ℝ) ≤ t := by
      apply ht
      rcases hs with h | h
      · left
        intro x hx y hy hxy
        apply (hadj a x y).mp
        exact h hx hy (fun he => hxy (congrArg Prod.snd (e.injective he)))
      · right
        intro x hx y hy hxy hG
        exact h hx hy (fun he => hxy (congrArg Prod.snd (e.injective he))) ((hadj a x y).mpr hG)
    rw [slices e s, Nat.cast_sum]
    simpa using Finset.sum_le_sum (s := Finset.univ) (fun a _ => bound a)
  · intro v
    obtain ⟨⟨a,x⟩,rfl⟩ := e.surjective v
    change 0 < degree (e (a,x))
    rw [hd]
    change 0 < x.val + m * (band a).val
    have pos : ∀ i, 0 < (band i).val := by decide
    have := Nat.mul_pos (show 0 < m by omega) (pos a)
    omega
