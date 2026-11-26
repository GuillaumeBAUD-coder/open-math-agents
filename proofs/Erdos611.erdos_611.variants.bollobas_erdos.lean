import FormalConjectures.ErdosProblems.«611»

/-! Private neighbors of a minimum dominating set control a large clique in the complement. -/

open Finset SimpleGraph

lemma OMA.extend_clique {V : Type} [DecidableEq V] (G : SimpleGraph V)
    (U P : Finset V) (hPU : P ⊆ U) (hP : G.IsClique (P : Set V)) :
    ∃ S : Finset V, P ⊆ S ∧ S ⊆ U ∧ G.IsClique (S : Set V) ∧
      ∀ T : Finset V, G.IsClique (T : Set V) → T ⊆ U → S ⊆ T → T ⊆ S := by
  classical
  let F := U.powerset.filter (fun S => P ⊆ S ∧ G.IsClique (S : Set V))
  have memF (S : Finset V) :
      S ∈ F ↔ S ⊆ U ∧ P ⊆ S ∧ G.IsClique (S : Set V) := by
    simp [F]
  obtain ⟨S, hS, hmax⟩ := Finset.exists_max_image F Finset.card
    ⟨P, (memF P).mpr ⟨hPU, Subset.rfl, hP⟩⟩
  obtain ⟨hSU, hPS, hcl⟩ := (memF S).mp hS
  refine ⟨S, hPS, hSU, hcl, ?_⟩
  intro T hT hTU hST
  have hcard := hmax T ((memF T).mpr ⟨hTU, hPS.trans hST, hT⟩)
  exact (Finset.eq_of_subset_of_card_le hST hcard).symm.subset

def OMA.dominates {V : Type} (H : SimpleGraph V) (D : Finset V) : Prop :=
  ∀ v, v ∈ D ∨ ∃ u ∈ D, H.Adj u v

lemma OMA.private_dominating {V : Type} [Fintype V] (H : SimpleGraph V)
    (hiso : ∀ x, ∃ y, H.Adj x y) :
    ∃ D : Finset V, OMA.dominates H D ∧
      ∀ x ∈ D, ∃ z, z ∉ D ∧ H.Adj x z ∧ ∀ y ∈ D, H.Adj y z → y = x := by
  classical
  let F := (Finset.univ : Finset (Finset V)).filter (OMA.dominates H)
  have memF (S : Finset V) : S ∈ F ↔ OMA.dominates H S := by simp [F]
  obtain ⟨D₀, hD₀, hmin⟩ := Finset.exists_min_image F Finset.card
    ⟨Finset.univ, (memF _).mpr (fun x => Or.inl (Finset.mem_univ x))⟩
  let support (D : Finset V) : Finset V := D.filter fun x => ∃ y ∈ D, H.Adj x y
  let M := F.filter fun D => D.card = D₀.card
  have memM (S : Finset V) : S ∈ M ↔ OMA.dominates H S ∧ S.card = D₀.card := by
    simp [M, memF]
  obtain ⟨D, hD, hmax⟩ := Finset.exists_max_image M (fun S => (support S).card)
    ⟨D₀, (memM _).mpr ⟨(memF _).mp hD₀, rfl⟩⟩
  obtain ⟨hdom, hcard⟩ := (memM D).mp hD
  have minD (A : Finset V) (hA : OMA.dominates H A) : D.card ≤ A.card := by
    rw [hcard]
    exact hmin A ((memF A).mpr hA)
  refine ⟨D, hdom, ?_⟩
  intro x hx
  by_contra hno
  have replace (z : V) (hz : z ∉ D) (hxz : H.Adj x z) :
      ∃ y ∈ D.erase x, H.Adj y z := by
    by_contra h
    apply hno
    refine ⟨z, hz, hxz, ?_⟩
    intro y hy hyz
    by_contra hne
    exact h ⟨y, Finset.mem_erase.mpr ⟨hne, hy⟩, hyz⟩
  have cover (z : V) (hzx : z ≠ x) :
      z ∈ D.erase x ∨ ∃ y ∈ D.erase x, H.Adj y z := by
    by_cases hz : z ∈ D
    · exact Or.inl (Finset.mem_erase.mpr ⟨hzx, hz⟩)
    · obtain ⟨y, hy, hyz⟩ := (hdom z).resolve_left hz
      right
      by_cases hyx : y = x
      · subst y
        exact replace z hz hyz
      · exact ⟨y, Finset.mem_erase.mpr ⟨hyx, hy⟩, hyz⟩
  by_cases hadj : ∃ y ∈ D, H.Adj y x
  · have hsmall : OMA.dominates H (D.erase x) := by
      intro z
      by_cases hz : z = x
      · subst z
        obtain ⟨y, hy, hyx⟩ := hadj
        exact Or.inr ⟨y, Finset.mem_erase.mpr ⟨hyx.ne, hy⟩, hyx⟩
      · exact cover z hz
    have hle := minD _ hsmall
    rw [Finset.card_erase_of_mem hx] at hle
    have hpos := Finset.card_pos.mpr ⟨x, hx⟩
    omega
  · obtain ⟨u, hxu⟩ := hiso x
    have hu : u ∉ D := fun hu => hadj ⟨u, hu, hxu.symm⟩
    let A := insert u (D.erase x)
    have hA : OMA.dominates H A := by
      intro z
      by_cases hz : z = x
      · subst z
        exact Or.inr ⟨u, Finset.mem_insert_self _ _, hxu.symm⟩
      · rcases cover z hz with h | ⟨y, hy, hyz⟩
        · exact Or.inl (Finset.mem_insert_of_mem h)
        · exact Or.inr ⟨y, Finset.mem_insert_of_mem hy, hyz⟩
    have hAcard : A.card = D.card := by
      dsimp [A]
      rw [Finset.card_insert_of_notMem (fun h => hu (Finset.mem_of_mem_erase h)),
        Finset.card_erase_of_mem hx]
      have hpos := Finset.card_pos.mpr ⟨x, hx⟩
      omega
    have hsub : support D ⊆ support A := by
      intro y hy
      obtain ⟨hyD, z, hzD, hyz⟩ := Finset.mem_filter.mp hy
      have hyx : y ≠ x := fun e => hadj ⟨z, hzD, e ▸ hyz.symm⟩
      have hzx : z ≠ x := fun e => hadj ⟨y, hyD, e ▸ hyz⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨hyx, hyD⟩),
        z, Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨hzx, hzD⟩), hyz⟩
    have hus : u ∈ support A := by
      obtain ⟨y, hy, hyu⟩ := replace u hu hxu
      exact Finset.mem_filter.mpr ⟨Finset.mem_insert_self _ _, y, Finset.mem_insert_of_mem hy, hyu.symm⟩
    have hstrict : support D ⊂ support A := by
      refine Finset.ssubset_iff_subset_ne.mpr ⟨hsub, ?_⟩
      intro heq
      exact hu (Finset.mem_filter.mp (heq.symm ▸ hus)).1
    have hle := hmax A ((memM A).mpr ⟨hA, hAcard.trans hcard⟩)
    exact (not_lt_of_ge hle) (Finset.card_lt_card hstrict)

lemma OMA.small_maximal_clique (n : ℕ) (hn : 0 < n) (G : SimpleGraph (Fin n))
    (hiso : ∀ x, ∃ y, Gᶜ.Adj x y) :
    ∃ J : Finset (Fin n), Maximal (fun S : Finset (Fin n) => G.IsClique (S : Set (Fin n))) J ∧
      (J.card : ℝ) ≤ (n : ℝ) + 2 - 2 * Real.sqrt (n : ℝ) := by
  classical
  obtain ⟨D, hdom, hprivate⟩ := OMA.private_dominating Gᶜ hiso
  have hD : D.Nonempty := by
    let v : Fin n := ⟨0, hn⟩
    rcases hdom v with hv | ⟨u, hu, _⟩
    · exact ⟨v, hv⟩
    · exact ⟨u, hu⟩
  let exterior (x : Fin n) : Finset (Fin n) :=
    Finset.univ.filter fun y => y ∉ D ∧ Gᶜ.Adj x y
  have mem_exterior (x y : Fin n) : y ∈ exterior x ↔ y ∉ D ∧ Gᶜ.Adj x y := by
    simp [exterior]
  obtain ⟨x, hx, hmax⟩ := Finset.exists_max_image D (fun x => (exterior x).card) hD
  let B := exterior x
  have cover : (Finset.univ \ D) ⊆ D.biUnion exterior := by
    intro y hy
    have hnot : y ∉ D := (Finset.mem_sdiff.mp hy).2
    obtain ⟨u, hu, hadj⟩ := (hdom y).resolve_left hnot
    exact Finset.mem_biUnion.mpr ⟨u, hu, (mem_exterior _ _).mpr ⟨hnot, hadj⟩⟩
  have hbound := (Finset.card_le_card cover).trans
    (Finset.card_biUnion_le_card_mul D exterior B.card hmax)
  rw [Finset.card_univ_sdiff, Fintype.card_fin] at hbound
  have hDle : D.card ≤ n := by simpa using Finset.card_le_univ D
  have hproduct : n ≤ D.card * (B.card + 1) := by
    rw [Nat.mul_add, Nat.mul_one]
    omega
  have hproductR : (n : ℝ) ≤ (D.card : ℝ) * ((B.card : ℝ) + 1) := by
    exact_mod_cast hproduct
  obtain ⟨I, hxI, hID, hI, hImax⟩ := OMA.extend_clique G D {x}
    (Finset.singleton_subset_iff.mpr hx) (by simp)
  have hxi : x ∈ I := hxI (Finset.mem_singleton_self x)
  obtain ⟨J, hIJ, _, hJ, hJmax⟩ := OMA.extend_clique G Finset.univ I (Finset.subset_univ _) hI
  have hJx : x ∈ J := hIJ hxi
  have hJI : J ∩ D ⊆ I := by
    refine hImax (J ∩ D) (hJ.subset ?_) Finset.inter_subset_right ?_
    · exact Finset.inter_subset_left
    · intro y hy
      exact Finset.mem_inter.mpr ⟨hIJ hy, hID hy⟩
  have no_edge {v w : Fin n} (hv : v ∈ J) (hw : w ∈ J) (he : Gᶜ.Adj v w) : False := by
    obtain ⟨hne, hnot⟩ := (SimpleGraph.compl_adj G v w).mp he
    exact hnot (hJ hv hw hne)
  let privateNeighbor (v : Fin n) : Fin n :=
    if h : v ∈ D then Classical.choose (hprivate v h) else v
  have priv (v : Fin n) (hv : v ∈ D) :
      privateNeighbor v ∉ D ∧ Gᶜ.Adj v (privateNeighbor v) ∧
        ∀ y ∈ D, Gᶜ.Adj y (privateNeighbor v) → y = v := by
    simpa only [privateNeighbor, dif_pos hv] using Classical.choose_spec (hprivate v hv)
  let A := D \ I
  let C := (I.erase x).image privateNeighbor
  have C_spec (z : Fin n) (hz : z ∈ C) : z ∉ D ∧ ¬ Gᶜ.Adj x z ∧ z ∉ J := by
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hz
    obtain ⟨hvx, hvI⟩ := Finset.mem_erase.mp hv
    obtain ⟨hout, hadj, hunique⟩ := priv v (hID hvI)
    exact ⟨hout, fun h => hvx (hunique x hx h).symm, fun h => no_edge (hIJ hvI) h hadj⟩
  have hCcard : C.card = I.card - 1 := by
    have hinj : Set.InjOn privateNeighbor (↑(I.erase x) : Set (Fin n)) := by
      intro v hv w hw he
      have hvi := hID (Finset.mem_of_mem_erase (show v ∈ I.erase x from hv))
      have hwi := hID (Finset.mem_of_mem_erase (show w ∈ I.erase x from hw))
      have ht : Gᶜ.Adj w (privateNeighbor v) := he.symm ▸ (priv w hwi).2.1
      exact ((priv v hvi).2.2 w hwi ht).symm
    rw [show C = (I.erase x).image privateNeighbor from rfl, Finset.card_image_of_injOn hinj,
      Finset.card_erase_of_mem hxi]
  have hdBC : Disjoint B C := by
    refine Finset.disjoint_left.mpr ?_
    intro z hb hc
    exact (C_spec z hc).2.1 ((mem_exterior x z).mp hb).2
  have hdA : Disjoint A (B ∪ C) := by
    refine Finset.disjoint_left.mpr ?_
    intro z ha hBC
    have hzD := (Finset.mem_sdiff.mp ha).1
    rcases Finset.mem_union.mp hBC with hb | hc
    · exact ((mem_exterior x z).mp hb).1 hzD
    · exact (C_spec z hc).1 hzD
  have hdJ : Disjoint J (A ∪ (B ∪ C)) := by
    refine Finset.disjoint_left.mpr ?_
    intro z hj ht
    rcases Finset.mem_union.mp ht with ha | hBC
    · obtain ⟨hzD, hzI⟩ := Finset.mem_sdiff.mp ha
      exact hzI (hJI (Finset.mem_inter.mpr ⟨hj, hzD⟩))
    · rcases Finset.mem_union.mp hBC with hb | hc
      · exact no_edge hJx hj ((mem_exterior x z).mp hb).2
      · exact (C_spec z hc).2.2 hj
  have hAcard : A.card = D.card - I.card := Finset.card_sdiff_of_subset hID
  have htotal := Finset.card_le_card (Finset.subset_univ (J ∪ (A ∪ (B ∪ C))))
  rw [Finset.card_union_of_disjoint hdJ, Finset.card_union_of_disjoint hdA,
    Finset.card_union_of_disjoint hdBC, hAcard, hCcard, Finset.card_univ, Fintype.card_fin] at htotal
  have hIle : I.card ≤ D.card := Finset.card_le_card hID
  have hIpos : 0 < I.card := Finset.card_pos.mpr ⟨x, hxi⟩
  have hcount : J.card + D.card + B.card ≤ n + 1 := by omega
  have hcountR : (J.card : ℝ) + (D.card : ℝ) + (B.card : ℝ) ≤ (n : ℝ) + 1 := by
    exact_mod_cast hcount
  have hsq : (Real.sqrt (n : ℝ)) ^ 2 = (n : ℝ) := Real.sq_sqrt (by positivity)
  have hsquared : (2 * Real.sqrt (n : ℝ)) ^ 2 ≤ ((D.card : ℝ) + (B.card : ℝ) + 1) ^ 2 := by
    nlinarith only [hproductR, hsq, sq_nonneg ((D.card : ℝ) - ((B.card : ℝ) + 1))]
  have hroot : 2 * Real.sqrt (n : ℝ) ≤ (D.card : ℝ) + (B.card : ℝ) + 1 :=
    le_of_pow_le_pow_left₀ (by decide : (2 : ℕ) ≠ 0) (by positivity) hsquared
  refine ⟨J, ⟨hJ, fun T hT hJT => hJmax T hT (Finset.subset_univ T) hJT⟩, ?_⟩
  linarith

theorem OMA.solution : type_of% @Erdos611.erdos_611.variants.bollobas_erdos := by
  classical
  intro n G hmax
  have hn : 0 < n := by
    by_contra! h
    have hz : n = 0 := by omega
    subst n
    have hZ : (0 : ℕ) ∈ G.cliqueSizes := by
      refine ⟨∅, ⟨by simp, ?_⟩, by simp⟩
      intro S hS hsub v hv
      exact Fin.elim0 v
    have hbad := hmax 0 hZ
    norm_num at hbad
  have universal : ∃ x : Fin n, ∀ y : Fin n, x ≠ y → G.Adj x y := by
    by_contra hno
    have hiso (x : Fin n) : ∃ y, Gᶜ.Adj x y := by
      by_contra hbad
      apply hno
      refine ⟨x, fun y hne => ?_⟩
      by_contra hnot
      exact hbad ⟨y, (SimpleGraph.compl_adj G x y).mpr ⟨hne, hnot⟩⟩
    obtain ⟨J, hJ, hsmall⟩ := OMA.small_maximal_clique n hn G hiso
    have hlarge := hmax J.card ⟨J, hJ, rfl⟩
    linarith
  obtain ⟨x, hx⟩ := universal
  have hit : G.IsCliqueTransversal {x} := by
    intro S hs
    have hinsert : G.IsClique (↑(insert x S) : Set (Fin n)) := by
      rw [Finset.coe_insert]
      exact hs.1.1.insert (fun y _ hne => hx y hne)
    have hsub : insert x S ⊆ S := hs.1.2 hinsert (Finset.subset_insert x S)
    exact ⟨x, hsub (Finset.mem_insert_self x S), Finset.mem_singleton_self x⟩
  obtain ⟨K, _, _, hKcl, hKmax⟩ := OMA.extend_clique G Finset.univ {x}
    (Finset.subset_univ _) (by simp)
  have hK : Maximal (fun S : Finset (Fin n) => G.IsClique (S : Set (Fin n))) K :=
    ⟨hKcl, fun S hS hKS => hKmax S hS (Finset.subset_univ S) hKS⟩
  have hlarge := hmax K.card ⟨K, hK, rfl⟩
  have hmin : (2 : ℝ) ≤ (n : ℝ) + 3 - 2 * Real.sqrt (n : ℝ) := by
    nlinarith only [Real.sq_sqrt (show (0 : ℝ) ≤ (n : ℝ) by positivity),
      sq_nonneg (Real.sqrt (n : ℝ) - 1)]
  have hbig : G.IsBigMaximalClique K :=
    ⟨hK, by exact_mod_cast hmin.trans hlarge⟩
  unfold SimpleGraph.cliqueTransversalNumber
  apply le_antisymm
  · exact Nat.sInf_le ⟨{x}, hit, Finset.card_singleton x⟩
  · apply le_csInf
    · exact ⟨1, {x}, hit, Finset.card_singleton x⟩
    · intro k hk
      obtain ⟨T, hT, rfl⟩ := hk
      obtain ⟨v, _, hv⟩ := hT K hbig
      exact Finset.card_pos.mpr ⟨v, hv⟩