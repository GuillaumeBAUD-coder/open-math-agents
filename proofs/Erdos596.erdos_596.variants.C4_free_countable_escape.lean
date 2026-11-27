import FormalConjectures.ErdosProblems.«596»

/-! Erdős–Hajnal countable edge coloring of arbitrary C₄-free graphs.
Credit: @JaviSoto. -/

/- Color the edges of a quadrilateral-free graph by countably many cycle-free classes. -/

namespace OMA.Escape596

open Cardinal Set SimpleGraph
open scoped Cardinal

variable {W : Type}

private def iter (op : W → W → W) (U : Set W) : ℕ → Set W
  | 0 => U
  | n+1 => iter op U n ∪ Set.range (fun p : (iter op U n) × (iter op U n) => op p.1 p.2)

private def cl (op : W → W → W) (U : Set W) : Set W := ⋃ n, iter op U n

private lemma iter_step (op : W → W → W) (U : Set W) :
    Monotone (iter op U) := monotone_nat_of_le_succ fun _ => Set.subset_union_left

private lemma cl_mono (op : W → W → W) : Monotone (cl op) := by
  intro U V hUV
  apply Set.iUnion_mono
  intro n
  induction n with
  | zero => exact hUV
  | succ n ih =>
    apply Set.union_subset_union ih
    rintro _ ⟨⟨x,y⟩,rfl⟩
    exact ⟨(⟨x,ih x.2⟩,⟨y,ih y.2⟩),rfl⟩

private lemma generator (op : W → W → W) (U : Set W) : U ⊆ cl op U :=
  fun _ hx => Set.mem_iUnion.mpr ⟨0,hx⟩

private lemma cl_closed (op : W → W → W) {U : Set W} {x y : W}
    (hx : x ∈ cl op U) (hy : y ∈ cl op U) : op x y ∈ cl op U := by
  obtain ⟨i,hi⟩ := Set.mem_iUnion.mp hx
  obtain ⟨j,hj⟩ := Set.mem_iUnion.mp hy
  let k := max i j
  exact Set.mem_iUnion.mpr ⟨k+1, Or.inr ⟨(⟨x,iter_step op U (le_max_left i j) hi⟩,
    ⟨y,iter_step op U (le_max_right i j) hj⟩),rfl⟩⟩

private lemma cl_small (op : W → W → W) (U : Set W) :
    #(cl op U) ≤ max ℵ₀ #U := by
  let k := max ℵ₀ #U
  have hk : ℵ₀ ≤ k := le_max_left _ _
  have h (n : ℕ) : #(iter op U n) ≤ k := by
    induction n with
    | zero => exact le_max_right _ _
    | succ n ih =>
      apply (Cardinal.mk_union_le _ _).trans
      apply (add_le_add ih ?_).trans_eq (Cardinal.add_eq_self hk)
      apply Cardinal.mk_range_le.trans
      rw [Cardinal.mk_prod]
      simpa using (mul_le_mul' ih ih).trans_eq (Cardinal.mul_eq_self hk)
  apply (Cardinal.mk_iUnion_le _).trans
  rw [Cardinal.mk_nat]
  exact (mul_le_mul' hk (ciSup_le h)).trans_eq (Cardinal.mul_eq_self hk)

private lemma split_set (op : W → W → W) (S : Set W) (hS : ℵ₀ < #S) :
    ∃ (I : Type) (_ : LinearOrder I) (rank : W → I),
      (∀ i, #(S ∩ {x | rank x = i} : Set W) < #S) ∧
      (∀ x ∈ S, ∀ y ∈ S, ∀ z ∈ S, op x y = z →
        ¬ (rank x < rank z ∧ rank y < rank z)) := by
  classical
  let I := (Cardinal.ord #S).ToType
  have hi : #I = #S := by simp [I]
  let e : I ≃ S := (Cardinal.eq.mp hi).some
  have : Nonempty S := by
    by_contra! h
    simp at hS
  have : Nonempty I := Nonempty.map e.symm ‹Nonempty S›
  let U (i : I) : Set W := (fun j : I => (e j : W)) '' Set.Iic i
  have mono : Monotone U := fun _ _ hij => Set.image_mono (Set.Iic_subset_Iic.mpr hij)
  let F (i : I) := cl op (U i)
  have fm : Monotone F := (cl_mono op).comp mono
  have exists_stage (x : S) : ({i | x.val ∈ F i} : Set I).Nonempty := by
    refine ⟨e.symm x, generator op _ ?_⟩
    exact ⟨e.symm x,Set.mem_Iic.mpr le_rfl,by simp⟩
  let r (x : S) := (wellFounded_lt (α := I)).min _ (exists_stage x)
  have hr (x : S) : x.val ∈ F (r x) :=
    (wellFounded_lt (α := I)).min_mem {i | x.val ∈ F i} (exists_stage x)
  have least (x : S) (i : I) (hx : x.val ∈ F i) : r x ≤ i :=
    le_of_not_gt ((wellFounded_lt (α := I)).not_lt_min {i | x.val ∈ F i} hx)
  let rank (x : W) : I := if h : x ∈ S then r ⟨x,h⟩ else Classical.choice ‹Nonempty I›
  have rank_mem {x : W} (hx : x ∈ S) : x ∈ F (rank x) := by simpa [rank,hx] using hr ⟨x,hx⟩
  have rank_le {x : W} (hx : x ∈ S) {i : I} (hi : x ∈ F i) : rank x ≤ i := by
    simpa [rank,hx] using least ⟨x,hx⟩ i hi
  refine ⟨I, inferInstance, rank, ?_, ?_⟩
  · intro i
    have sub : S ∩ {x | rank x = i} ⊆ F i := by
      intro x hx
      rw [← (show rank x = i from hx.2)]
      exact rank_mem hx.1
    apply (Cardinal.mk_le_mk_of_subset sub).trans_lt
    apply (cl_small op (U i)).trans_lt
    apply max_lt hS
    apply Cardinal.mk_image_le.trans_lt
    have hI := Cardinal.mk_Iic_lt i (by simp [I])
      (hi ▸ hS.le)
    simpa only [hi] using hI
  · intro x hx y hy z hz hop ⟨h1,h2⟩
    let j := max (rank x) (rank y)
    have hx' : x ∈ F j := fm (le_max_left _ _) (rank_mem hx)
    have hy' : y ∈ F j := fm (le_max_right _ _) (rank_mem hy)
    have hz' : z ∈ F j := hop ▸ cl_closed op hx' hy'
    exact (max_lt h1 h2).not_ge (rank_le hz hz')

private lemma unique_common (G : SimpleGraph W) (hG : (cycleGraph 4).Free G)
    {x y u v : W} (hxy : x ≠ y) (hxu : G.Adj x u) (hyu : G.Adj y u)
    (hxv : G.Adj x v) (hyv : G.Adj y v) : u = v := by
  by_contra huv
  let f : Fin 4 → W := ![x,u,y,v]
  have hf : Function.Injective f := by
    have h1 := hxu.ne
    have h2 := hxv.ne
    have h3 := hyu.ne
    have h4 := hyv.ne
    intro i j
    fin_cases i <;> fin_cases j <;> simp [f] <;> grind
  apply hG
  refine ⟨⟨⟨f,?_⟩,hf⟩⟩
  intro i j hij
  fin_cases i <;> fin_cases j <;> first
    | exact hxu | exact hxu.symm | exact hyu | exact hyu.symm
    | exact hxv | exact hxv.symm | exact hyv | exact hyv.symm
    | exact (by decide : ¬ _ ) hij | contradiction

/-- Within a vertex subset, color adjacent pairs symmetrically so a six-cycle cannot be monochrome. -/
private def Colored (G : SimpleGraph W) (S : Set W) : Prop :=
  ∃ c : W → W → ℕ, (∀ x y, c x y = c y x) ∧
    ∀ f : Fin 6 ↪ W, (∀ i, f i ∈ S) → (∀ i, G.Adj (f i) (f (i+1))) →
      ∀ j, ¬ (∀ i, c (f i) (f (i+1)) = j)

private lemma colored_countable (G : SimpleGraph W) (S : Set W) (hS : #S ≤ ℵ₀) :
    Colored G S := by
  classical
  have : Countable S := Cardinal.mk_le_aleph0_iff.mp hS
  obtain ⟨label, inj⟩ := Countable.exists_injective_nat S
  let l (x : W) : ℕ := if hx : x ∈ S then label ⟨x,hx⟩ else 0
  have unique {x y : W} (hx : x ∈ S) (hy : y ∈ S) (h : l x = l y) : x = y :=
    congrArg Subtype.val (inj (by simpa [l,hx,hy] using h))
  refine ⟨fun x y => min (l x) (l y), fun _ _ => min_comm _ _, ?_⟩
  intro f hf _ j h
  have hj : min (l (f 0)) (l (f 1)) = min (l (f 2)) (l (f 3)) := (h 0).trans (h 2).symm
  have disj (i k : Fin 6) (hik : i ≠ k) : l (f i) ≠ l (f k) :=
    fun h' => hik (f.injective (unique (hf i) (hf k) h'))
  have h02 := disj 0 2 (by decide)
  have h03 := disj 0 3 (by decide)
  have h12 := disj 1 2 (by decide)
  have h13 := disj 1 3 (by decide)
  omega

private lemma colored_join (G : SimpleGraph W) (S : Set W) {I : Type} [LinearOrder I]
    (r : W → I)
    (hlower : ∀ x ∈ S, ∀ y ∈ S, ∀ z ∈ S, x ≠ y → G.Adj x z → G.Adj y z →
      ¬ (r x < r z ∧ r y < r z))
    (hC : ∀ i, Colored G (S ∩ {x | r x = i})) : Colored G S := by
  classical
  choose c symm good using hC
  let d (x y : W) := if r x = r y then c (r x) x y + 1 else 0
  refine ⟨d, ?_, ?_⟩
  · intro x y
    by_cases he : r x = r y
    · simp [d,he,symm (r y) x y]
    · simp [d,he,Ne.symm he]
  intro f hf adj j hj
  cases j with
  | zero =>
    have diff (i : Fin 6) : r (f i) ≠ r (f (i+1)) := by
      intro h
      simpa [d,h] using hj i
    obtain ⟨i, _, hmax⟩ := Finset.exists_max_image Finset.univ (fun i : Fin 6 => r (f i))
      (by simp)
    have hpred : i-1+1 = i := sub_add_cancel ..
    have hpre : r (f (i-1)) < r (f i) := lt_of_le_of_ne (hmax _ (by simp))
      (by simpa only [hpred] using diff (i-1))
    have hnxt : r (f (i+1)) < r (f i) := lt_of_le_of_ne (hmax _ (by simp)) (diff i).symm
    exact hlower _ (hf (i-1)) _ (hf (i+1)) _ (hf i)
      (fun h => (show ∀ k : Fin 6, k-1 ≠ k+1 by decide) i (f.injective h))
      (by simpa only [hpred] using adj (i-1)) (adj i).symm ⟨hpre, hnxt⟩
  | succ j =>
    have same (i : Fin 6) : r (f i) = r (f (i+1)) := by
      by_contra h
      simpa [d,h] using hj i
    have hsame : ∀ i : Fin 6, r (f i) = r (f 0) := by
      have h0 : r (f 0) = r (f 1) := same 0
      have h1 : r (f 1) = r (f 2) := same 1
      have h2 : r (f 2) = r (f 3) := same 2
      have h3 : r (f 3) = r (f 4) := same 3
      have h4 : r (f 4) = r (f 5) := same 4
      intro i
      fin_cases i
      · rfl
      · exact h0.symm
      · exact (h0.trans h1).symm
      · exact ((h0.trans h1).trans h2).symm
      · exact (((h0.trans h1).trans h2).trans h3).symm
      · exact ((((h0.trans h1).trans h2).trans h3).trans h4).symm
    apply good (r (f 0)) f (fun i => ⟨hf i, hsame i⟩) adj j
    intro i
    simpa only [d, if_pos (same i), Nat.add_right_cancel_iff, hsame i] using hj i

private theorem colored_all (G : SimpleGraph W) (hG : (cycleGraph 4).Free G) (S : Set W) :
    Colored G S := by
  classical
  let op (x y : W) : W :=
    if h : ∃ z, G.Adj x z ∧ G.Adj y z then h.choose else x
  have hop {x y z : W} (hne : x ≠ y) (hx : G.Adj x z) (hy : G.Adj y z) : op x y = z := by
    have h : ∃ z, G.Adj x z ∧ G.Adj y z := ⟨z,hx,hy⟩
    exact (show op x y = h.choose by simp [op,h]).trans
      (unique_common G hG hne h.choose_spec.1 h.choose_spec.2 hx hy)
  generalize hsize : #S = k
  induction k using WellFoundedLT.induction generalizing S with
  | ind k ih =>
    subst k
    by_cases h : #S ≤ ℵ₀
    · exact colored_countable G S h
    obtain ⟨I, inst, rank, small, order⟩ := split_set op S (lt_of_not_ge h)
    let _ := inst
    apply colored_join G S rank
    · intro x hx y hy z hz hxy hxz hyz
      exact order x hx y hy z hz (hop hxy hxz hyz)
    · intro i
      exact ih _ (small i) _ rfl

theorem escape : type_of% @Erdos596.erdos_596.variants.C4_free_countable_escape := by
  intro W G hG
  obtain ⟨c,cs,good⟩ := colored_all G hG Set.univ
  let d (j : ℕ) : SimpleGraph W := {
    Adj := fun x y => G.Adj x y ∧ c x y = j
    symm := ⟨fun x y h => ⟨h.1.symm, (cs y x).trans h.2⟩⟩
    loopless := ⟨fun x h => G.loopless.irrefl x h.1⟩ }
  refine ⟨d, ⟨?_,?_⟩, ?_⟩
  · ext x y
    simp [SimpleGraph.iSup_adj,d]
  · intro i j hij
    apply disjoint_iff_inf_le.mpr
    intro x y h
    exact (hij (h.1.2.symm.trans h.2.2)).elim
  · rintro j ⟨f⟩
    have hedge (i : Fin 6) : (d j).Adj (f i) (f (i+1)) :=
      f.toHom.map_adj ((by decide : ∀ i : Fin 6, (cycleGraph 6).Adj i (i+1)) i)
    exact good f.toEmbedding (fun _ => Set.mem_univ _) (fun i => (hedge i).1) j
      (fun i => (hedge i).2)

end OMA.Escape596

theorem OMA.solution : type_of% @Erdos596.erdos_596.variants.C4_free_countable_escape :=
  OMA.Escape596.escape
