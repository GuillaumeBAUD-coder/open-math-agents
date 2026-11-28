import FormalConjectures.ErdosProblems.«1114»

/-! Select one Rolle root in each gap and exhaust the derivative roots by a degree bound. -/

open Finset Polynomial

theorem OMA.solution : type_of% @Erdos1114.erdos_1114.variants.rolle := by
  classical
  intro N a d hd f hdegree hroots
  let x (k : ℕ) : ℝ := a + d * k
  have mono : StrictMono x := by
    intro i j hij
    dsimp [x]
    gcongr
  have existsRoot (i : Fin N) :
      ∃ z ∈ Set.Ioo (x i) (x ((i : ℕ) + 1)), f.derivative.eval z = 0 :=
    exists_hasDerivAt_eq_zero (mono (Nat.lt_succ_self _)) f.continuous.continuousOn
      ((hroots _ i.isLt.le).trans (hroots _ i.isLt).symm) fun z _ => f.hasDerivAt z
  choose y hy hzero using existsRoot
  have distinct (i j : Fin N) (hij : i < j) :
      x ((i : ℕ) + 1) ≤ x j :=
    mono.monotone (Nat.succ_le_of_lt hij)
  have rootsNotZero : f.derivative ≠ 0 := by
    intro h
    simpa [hdegree] using derivative_eq_zero.mp h
  have memRoots (z : ℝ) :
      z ∈ f.derivative.roots.toFinset ↔ f.derivative.eval z = 0 := by
    simp [mem_roots rootsNotZero, IsRoot]
  have yMono : StrictMono y :=
    fun i j hij => (hy i).2.trans ((distinct i j hij).trans_lt (hy j).1)
  have exhausted : univ.image y = f.derivative.roots.toFinset := by
    apply eq_of_subset_of_card_le
    · intro z hz
      obtain ⟨i, _, rfl⟩ := mem_image.mp hz
      exact (memRoots _).2 (hzero i)
    · rw [card_image_of_injective _ yMono.injective, card_univ, Fintype.card_fin]
      have hd' := natDegree_derivative_le f
      rw [hdegree, Nat.add_sub_cancel] at hd'
      exact (Multiset.toFinset_card_le _).trans ((card_roots' _).trans hd')
  have index (z : ℝ) (hz : f.derivative.eval z = 0) : ∃ i, y i = z := by
    have hm : z ∈ univ.image y := exhausted ▸ (memRoots z).2 hz
    obtain ⟨i, _, hi⟩ := mem_image.mp hm
    exact ⟨i, hi⟩
  refine ⟨fun k hk => ?_, fun z hz => ?_⟩
  · let i : Fin N := ⟨k, hk⟩
    refine ⟨y i, ⟨by simpa [x, i] using hy i, hzero i⟩, ?_⟩
    rintro z ⟨hz, hz0⟩
    obtain ⟨j, rfl⟩ := index z hz0
    have hz' : y j ∈ Set.Ioo (x i) (x ((i : ℕ) + 1)) := by simpa [x, i] using hz
    rcases lt_trichotomy i j with hij | rfl | hji
    · exact (hz'.2.not_ge ((distinct i j hij).trans (hy j).1.le)).elim
    · rfl
    · exact ((hy j).2.not_ge ((distinct j i hji).trans hz'.1.le)).elim
  · obtain ⟨i, rfl⟩ := index z hz
    exact ⟨i, i.isLt, by simpa [x] using hy i⟩

