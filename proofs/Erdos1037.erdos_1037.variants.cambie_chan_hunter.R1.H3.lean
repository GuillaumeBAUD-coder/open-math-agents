import OMAReductions.R_Erdos1037_erdos_1037_variants_cambie_chan_hunter_R1

/-! # Padding a graph while preserving degree multiplicities -/
-- Credit: @steveDOTdigital
namespace OMA.GraphPadding
open Finset Set
open scoped Classical

private noncomputable def deg {n : ℕ} (G : SimpleGraph (Fin n)) (v : Fin n) :=
  (G.neighborSet v).ncard

private lemma deg_eq {n : ℕ} (G : SimpleGraph (Fin n)) (v : Fin n) :
    deg G v = G.degree v := by
  classical
  rw [deg, Set.ncard_eq_toFinset_card']
  rfl

private lemma deg_lt {n : ℕ} (G : SimpleGraph (Fin n)) (v : Fin n) : deg G v < n := by
  classical
  simpa [deg_eq] using G.degree_lt_card_verts v

-- Add an isolated vertex at zero, then take the complement. The next step
-- can again start with a graph without isolated vertices.
private def grow {n : ℕ} (G : SimpleGraph (Fin n)) : SimpleGraph (Fin (n+1)) :=
  (G.map (Fin.succEmb n))ᶜ

private lemma deg_complement {n : ℕ} (F : SimpleGraph (Fin (n+1))) (v : Fin (n+1)) :
    deg Fᶜ v = n-deg F v := by
  have eq : Fᶜ.neighborSet v = (insert v (F.neighborSet v))ᶜ := by
    ext x
    simp only [SimpleGraph.mem_neighborSet,SimpleGraph.compl_adj,Set.mem_compl_iff,
      Set.mem_insert_iff,not_or]
    tauto
  have ne : v ∉ F.neighborSet v := F.loopless.irrefl v
  rw [deg,eq,Set.ncard_compl,Set.ncard_insert_of_notMem ne,Nat.card_fin,deg]
  omega

private lemma deg_zero {n : ℕ} (G : SimpleGraph (Fin n)) : deg (grow G) 0 = n := by
  classical
  have e : (G.map (Fin.succEmb n)).neighborSet 0 = ∅ := by
    ext x
    change (G.map (Fin.succEmb n)).Adj 0 x ↔ False
    rw [SimpleGraph.map_adj]
    simp [Fin.coe_succEmb]
  rw [grow,deg_complement,deg,e]
  simp

private lemma deg_succ {n : ℕ} (G : SimpleGraph (Fin n)) (v : Fin n) :
    deg (grow G) v.succ = n-deg G v := by
  classical
  rw [grow,deg_complement]
  congr 1
  change ((G.map (Fin.succEmb n)).neighborSet (Fin.succEmb n v)).ncard = (G.neighborSet v).ncard
  rw [SimpleGraph.neighborSet_map,Set.ncard_image_of_injective _ (Fin.succEmb n).injective]

private lemma frequencies {n : ℕ} (G : SimpleGraph (Fin n))
    (pos : ∀ v, 0 < deg G v)
    (mult : ∀ d : ℕ, {v | deg G v = d}.ncard ≤ 2) :
    ∀ d : ℕ, {x | deg (grow G) x = d}.ncard ≤ 2 := by
  intro d
  by_cases e : d = n
  · subst d
    have eq : {x | deg (grow G) x = n} = {0} := by
      ext x
      induction x using Fin.cases with
      | zero => simp [deg_zero]
      | succ v =>
        have := pos v
        have := deg_lt G v
        simp [deg_succ,show n - deg G v ≠ n by omega]
    simp [eq]
  · have eq : {x | deg (grow G) x = d} = Fin.succ '' {v | deg G v = n-d ∧ d ≤ n} := by
      ext x
      induction x using Fin.cases with
      | zero => simp [deg_zero,Ne.symm e]
      | succ v =>
        have := deg_lt G v
        simp only [Set.mem_ofPred_eq,Set.mem_image, Fin.succ_inj,exists_eq_right,
          deg_succ]
        omega
    rw [eq,Set.ncard_image_of_injective _ (Fin.succ_injective n)]
    exact (Set.ncard_le_ncard (show {v | deg G v = n-d ∧ d ≤ n} ⊆ {v | deg G v = n-d}
      from fun _ h => h.1)).trans (mult _)

private lemma distinct {n : ℕ} (G : SimpleGraph (Fin n)) (pos : ∀ v, 0 < deg G v) :
    (Set.range (deg (grow G))).ncard = (Set.range (deg G)).ncard+1 := by
  let f := fun d : ℕ => n-d
  have inj : Set.InjOn f (Set.range (deg G)) := by
    rintro _ ⟨u,rfl⟩ _ ⟨v,rfl⟩ e
    dsimp [f] at e
    have := deg_lt G u
    have := deg_lt G v
    omega
  have notin : n ∉ f '' Set.range (deg G) := by
    rintro ⟨_,⟨v,rfl⟩,e⟩
    dsimp [f] at e
    have := pos v
    have := deg_lt G v
    omega
  have eq : Set.range (deg (grow G)) = insert n (f '' Set.range (deg G)) := by
    ext d
    constructor
    · rintro ⟨x,rfl⟩
      induction x using Fin.cases with
      | zero => exact Or.inl (deg_zero G)
      | succ v => exact Or.inr ⟨deg G v,⟨v,rfl⟩,(deg_succ G v).symm⟩
    · rintro (rfl | ⟨_,⟨v,rfl⟩,rfl⟩)
      · exact ⟨0,deg_zero G⟩
      · exact ⟨v.succ,deg_succ G v⟩
  rw [eq, Set.ncard_insert_of_notMem notin,inj.ncard_image]

private lemma small_sets {n : ℕ} (G : SimpleGraph (Fin n)) (t : ℝ)
    (small : ∀ s : Set (Fin n), G.IsHomogeneous s → (s.ncard : ℝ) ≤ t)
    (s : Set (Fin (n+1))) (hs : (grow G).IsHomogeneous s) : (s.ncard : ℝ) ≤ t+1 := by
  have inv := (SimpleGraph.isHomogeneous_compl).mp hs
  let A := Fin.succ ⁻¹' s
  have ha : G.IsHomogeneous A := by
    rcases inv with cl | ind
    · left
      intro v hv w hw ne
      exact SimpleGraph.map_adj_apply.mp (cl hv hw ((Fin.succ_injective n).ne ne))
    · right
      intro v hv w hw ne adj
      exact ind hv hw ((Fin.succ_injective n).ne ne) (SimpleGraph.map_adj_apply.mpr adj)
  have sub : s ⊆ insert 0 (Fin.succ '' A) := by
    intro x hx
    induction x using Fin.cases with
    | zero => exact Or.inl rfl
    | succ v => exact Or.inr ⟨v,hx,rfl⟩
  have nz : (0 : Fin (n+1)) ∉ Fin.succ '' A := by simp
  have card := Set.ncard_le_ncard sub
  rw [Set.ncard_insert_of_notMem nz,Set.ncard_image_of_injective _ (Fin.succ_injective n)] at card
  have cr : (s.ncard : ℝ) ≤ A.ncard+1 := by exact_mod_cast card
  linarith [small A ha]

private def Quality {n : ℕ} (G : SimpleGraph (Fin n)) (t : ℝ) : Prop :=
  (∀ d : ℕ, {v | deg G v = d}.ncard ≤ 2) ∧
  3/4 * (n : ℝ) ≤ ((Set.range (deg G)).ncard : ℝ) ∧
  (∀ s : Set (Fin n), G.IsHomogeneous s → (s.ncard : ℝ) ≤ t) ∧
  ∀ v, 0 < deg G v

private lemma step {n : ℕ} (hn : 0 < n) (G : SimpleGraph (Fin n)) (t : ℝ)
    (h : Quality G t) : Quality (grow G) (t+1) := by
  obtain ⟨mult,count,small,pos⟩ := h
  refine ⟨frequencies G pos mult,?_,small_sets G t small,?_⟩
  · rw [distinct G pos]
    push_cast
    linarith
  · intro v
    induction v using Fin.cases with
    | zero => simpa only [deg_zero] using hn
    | succ x =>
      rw [deg_succ]
      exact Nat.sub_pos_of_lt (deg_lt G x)

private lemma iterate {n : ℕ} (hn : 0 < n) (G : SimpleGraph (Fin n)) (t : ℝ)
    (h : Quality G t) (r : ℕ) : ∃ F : SimpleGraph (Fin (n+r)), Quality F (t+r) := by
  induction r with
  | zero => exact ⟨G,by simpa using h⟩
  | succ r ih =>
    obtain ⟨F,hF⟩ := ih
    refine ⟨grow F,?_⟩
    simpa [add_assoc] using step (by omega : 0 < n+r) F _ hF

end OMA.GraphPadding

theorem OMA.solution : OMA.R_Erdos1037_erdos_1037_variants_cambie_chan_hunter_R1.H3 := by
  intro N r hn _ F t mult count small pos
  obtain ⟨G,m,d,s,_⟩ := OMA.GraphPadding.iterate hn F t ⟨mult,count,small,pos⟩ r
  exact ⟨G,m,d,s⟩
