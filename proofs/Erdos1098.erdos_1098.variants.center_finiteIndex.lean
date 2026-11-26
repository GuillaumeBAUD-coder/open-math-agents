import FormalConjectures.ErdosProblems.«1098»
import Mathlib.GroupTheory.CosetCover

/-! A noncommuting clique injects into the quotient by the center. In the other
direction, a finite coset cover first gives a finite-index subgroup of elements
with finite-index centralizers. If every finite-index subgroup of that subgroup
were nonabelian, the recursive construction below would produce an infinite
clique. An abelian subgroup of finite index then forces the center to have
finite index as well. -/

open scoped Pointwise

namespace OMA

private abbrev centralizerOf {G : Type*} [Group G] (x : G) :=
  Subgroup.centralizer ({x} : Set G)

private theorem centralizer_mul_le {G : Type*} [Group G] (x y : G) :
    centralizerOf x ⊓ centralizerOf y ≤ centralizerOf (x * y) := by
  rintro z ⟨hx, hy⟩
  change z ∈ centralizerOf x at hx
  change z ∈ centralizerOf y at hy
  rw [Subgroup.mem_centralizer_singleton_iff] at hx hy ⊢
  symm
  calc
    (x * y) * z = x * (y * z) := mul_assoc _ _ _
    _ = x * (z * y) := by rw [← hy]
    _ = (x * z) * y := (mul_assoc _ _ _).symm
    _ = (z * x) * y := by rw [← hx]
    _ = z * (x * y) := mul_assoc _ _ _

private def finiteCentralizers (G : Type*) [Group G] : Subgroup G where
  carrier := {x | (centralizerOf x).FiniteIndex}
  one_mem' := by
    change (centralizerOf (1 : G)).FiniteIndex
    have h : centralizerOf (1 : G) = ⊤ := by
      ext z
      simp [centralizerOf, Subgroup.mem_centralizer_singleton_iff]
    rw [h]
    infer_instance
  mul_mem' := by
    intro x y hx hy
    letI : (centralizerOf x).FiniteIndex := hx
    letI : (centralizerOf y).FiniteIndex := hy
    exact Subgroup.finiteIndex_of_le (centralizer_mul_le x y)
  inv_mem' := by
    intro x hx
    have h : centralizerOf x⁻¹ = centralizerOf x := by
      ext z
      simp only [centralizerOf, Subgroup.mem_centralizer_singleton_iff]
      change Commute z x⁻¹ ↔ Commute z x
      exact ⟨fun hz => by simpa using hz.inv_right, fun hz => hz.inv_right⟩
    change (centralizerOf x⁻¹).FiniteIndex
    rw [h]
    exact hx

private theorem finite_clique_of_center_finiteIndex {G : Type*} [Group G]
    [(Subgroup.center G).FiniteIndex] (s : Set G)
    (hs : (Erdos1098.nonCommutingGraph G).IsClique s) : s.Finite := by
  have hinj : Set.InjOn (QuotientGroup.mk (s := Subgroup.center G)) s := by
    intro x hx y hy hxy
    by_contra hne
    have hc := QuotientGroup.eq.mp hxy
    have hcomm : Commute x (x⁻¹ * y) :=
      Subgroup.mem_center_iff.mp hc x
    have hcomm' := (Commute.refl x).mul_right hcomm
    apply (Erdos1098.nonCommutingGraph_adj x y).mp (hs hx hy hne)
    simpa using hcomm'.eq
  exact Set.Finite.of_finite_image (Set.toFinite _) hinj

private theorem finiteCentralizers_finiteIndex {G : Type*} [Group G]
    (h : ∀ s : Set G, (Erdos1098.nonCommutingGraph G).IsClique s → s.Finite) :
    (finiteCentralizers G).FiniteIndex := by
  classical
  let F := finiteCentralizers G
  let cliques : Set (Set G) :=
    {s | s ⊆ (F : Set G)ᶜ ∧ (Erdos1098.nonCommutingGraph G).IsClique s}
  obtain ⟨s, hs⟩ := zorn_subset cliques (by
    intro c hc hchain
    refine ⟨⋃₀ c, ⟨?_, ?_⟩, fun t ht => Set.subset_sUnion_of_mem ht⟩
    · intro x hx
      obtain ⟨t, ht, hxt⟩ := Set.mem_sUnion.mp hx
      exact (hc ht).1 hxt
    · intro x hx y hy hxy
      obtain ⟨u, hu, hxu⟩ := Set.mem_sUnion.mp hx
      obtain ⟨v, hv, hyv⟩ := Set.mem_sUnion.mp hy
      rcases hchain.total hu hv with huv | hvu
      · exact (hc hv).2 (huv hxu) hyv hxy
      · exact (hc hu).2 hxu (hvu hyv) hxy)
  have hsFinite := h s hs.1.2
  have hcover (x : G) : x ∈ F ∨ ∃ y ∈ s, x ∈ centralizerOf y := by
    by_contra! hn
    have hclique : (Erdos1098.nonCommutingGraph G).IsClique (insert x s) := by
      apply hs.1.2.insert
      intro y hy hyx
      exact (Erdos1098.nonCommutingGraph_adj x y).2 fun heq =>
        hn.2 y hy (Subgroup.mem_centralizer_singleton_iff.mpr heq)
    have hm : insert x s ∈ cliques :=
      ⟨Set.insert_subset_iff.mpr ⟨hn.1, hs.1.1⟩, hclique⟩
    have hx : x ∈ s := hs.2 hm (Set.subset_insert x s) (Set.mem_insert x s)
    exact hn.2 x hx (Subgroup.mem_centralizer_singleton_iff.mpr rfl)
  let H : Option G → Subgroup G
    | none => F
    | some y => centralizerOf y
  let indices := insert none (hsFinite.toFinset.image some)
  have hc : (⋃ i ∈ indices, (1 : G) • (H i : Set G)) = Set.univ := by
    apply Set.eq_univ_of_forall
    intro x
    rcases hcover x with hx | ⟨y, hy, hxy⟩
    · exact Set.mem_iUnion₂.mpr ⟨none, by simp [indices], by simpa [H] using hx⟩
    · exact Set.mem_iUnion₂.mpr ⟨some y, by simp [indices, hy], by simpa [H] using hxy⟩
  obtain ⟨i, hi, hfin⟩ := Subgroup.exists_finiteIndex_of_leftCoset_cover hc
  cases i with
  | none => exact hfin
  | some y =>
      have hy : y ∈ s := by simpa [indices] using hi
      exact False.elim (hs.1.1 hy hfin)

-- Keep a prefix that fails to commute with all earlier vertices. The subgroup
-- available for the next step commutes with that prefix and all earlier vertices.
private structure CliqueState (G : Type*) [Group G] where
  D : Subgroup G
  p : G
  seen : Set G
  finiteIndex : D.FiniteIndex
  commutePrefix : ∀ d ∈ D, Commute d p
  commuteSeen : ∀ d ∈ D, ∀ z ∈ seen, Commute d z
  prefixSeparates : ∀ z ∈ seen, ¬ Commute z p

private theorem extendCliqueState {G : Type*} [Group G]
    (hcentralizer : ∀ x : G, (centralizerOf x).FiniteIndex)
    (hnoncommute : ∀ D : Subgroup G, D.FiniteIndex →
      ∃ x ∈ D, ∃ y ∈ D, ¬ Commute x y)
    (S : CliqueState G) :
    ∃ (z : G) (T : CliqueState G), T.seen = insert z S.seen ∧
      ∀ w ∈ S.seen, ¬ Commute w z := by
  obtain ⟨x, hx, y, hy, hxy⟩ := hnoncommute S.D S.finiteIndex
  let D' := S.D ⊓ centralizerOf x ⊓ centralizerOf y
  let p' := S.p * x
  let z := S.p * y
  have hcancel (a b c : G) (ha : Commute a c) :
      Commute a (b * c) → Commute a b := fun h => by
    simpa [mul_assoc] using h.mul_right ha.inv_right
  letI := S.finiteIndex
  letI := hcentralizer x
  letI := hcentralizer y
  refine ⟨z, ⟨D', p', insert z S.seen, inferInstance, ?_, ?_, ?_⟩, rfl, ?_⟩
  · intro d hd
    exact (S.commutePrefix d hd.1.1).mul_right
      (Subgroup.mem_centralizer_singleton_iff.mp hd.1.2)
  · intro d hd w hw
    rcases Set.mem_insert_iff.mp hw with rfl | hw
    · exact (S.commutePrefix d hd.1.1).mul_right
        (Subgroup.mem_centralizer_singleton_iff.mp hd.2)
    · exact S.commuteSeen d hd.1.1 w hw
  · intro w hw hc
    rcases Set.mem_insert_iff.mp hw with rfl | hw
    · have hpz : Commute z S.p :=
        (Commute.refl S.p).mul_left (S.commutePrefix y hy)
      have hzx : Commute z x := by
        simpa [p', mul_assoc] using hpz.inv_right.mul_right hc
      exact hxy (by
        have h := (S.commutePrefix x hx).inv_right.mul_right hzx.symm
        simpa [z, mul_assoc] using h)
    · exact S.prefixSeparates w hw
        (hcancel w S.p x (S.commuteSeen x hx w hw).symm hc)
  · intro w hw hc
    exact S.prefixSeparates w hw
      (hcancel w S.p y (S.commuteSeen y hy w hw).symm hc)

private theorem infinite_clique_of_noncommuting_subgroups {G : Type*} [Group G]
    (hcentralizer : ∀ x : G, (centralizerOf x).FiniteIndex)
    (hnoncommute : ∀ D : Subgroup G, D.FiniteIndex →
      ∃ x ∈ D, ∃ y ∈ D, ¬ Commute x y) :
    ∃ s : Set G, (Erdos1098.nonCommutingGraph G).IsClique s ∧ s.Infinite := by
  classical
  let step (S : CliqueState G) :=
    Classical.choose (extendCliqueState hcentralizer hnoncommute S)
  let advance (S : CliqueState G) :=
    Classical.choose (Classical.choose_spec (extendCliqueState hcentralizer hnoncommute S))
  let state : ℕ → CliqueState G :=
    Nat.rec ⟨⊤, 1, ∅, inferInstance, fun d _ => Commute.one_right d,
      by simp, by simp⟩ fun _ S => advance S
  let z (n : ℕ) := step (state n)
  have hstep (n : ℕ) : (state (n + 1)).seen = insert (z n) (state n).seen ∧
      ∀ w ∈ (state n).seen, ¬ Commute w (z n) :=
    Classical.choose_spec (Classical.choose_spec
      (extendCliqueState hcentralizer hnoncommute (state n)))
  have hmono : Monotone (fun n => (state n).seen) :=
    monotone_nat_of_le_succ fun n => (hstep n).1.symm ▸ Set.subset_insert _ _
  have hlt (i j : ℕ) (hij : i < j) : ¬ Commute (z i) (z j) := by
    apply (hstep j).2
    apply hmono hij
    change z i ∈ (state (i + 1)).seen
    rw [(hstep i).1]
    exact Set.mem_insert _ _
  have hinj : Function.Injective z := by
    intro i j heq
    by_contra hne
    rcases lt_or_gt_of_ne hne with h | h
    · exact hlt i j h (heq ▸ Commute.refl _)
    · exact hlt j i h (heq ▸ Commute.refl _)
  refine ⟨Set.range z, ?_, Set.infinite_range_of_injective hinj⟩
  rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩ hne
  rcases lt_or_gt_of_ne (fun heq => hne (congrArg z heq)) with hij | hji
  · exact hlt i j hij
  · exact fun hc => hlt j i hji hc.symm

private theorem centralizer_finiteIndex_of_abelian {G : Type*} [Group G]
    (D : Subgroup G) [D.FiniteIndex]
    (hD : ∀ a b : D, Commute (a : G) (b : G))
    (h : ∀ s : Set G, (Erdos1098.nonCommutingGraph G).IsClique s → s.Finite)
    (g : G) : (centralizerOf g).FiniteIndex := by
  classical
  let K := (centralizerOf g).subgroupOf D
  by_contra hn
  have hnot : ¬ K.FiniteIndex := by
    intro hK
    have hmap : (K.map D.subtype).FiniteIndex := by
      constructor
      rw [Subgroup.index_map_subtype]
      exact mul_ne_zero hK.index_ne_zero (inferInstance : D.FiniteIndex).index_ne_zero
    letI := hmap
    apply hn
    apply Subgroup.finiteIndex_of_le (H := K.map D.subtype)
    rintro _ ⟨x, hx, rfl⟩
    exact hx
  haveI : Infinite (D ⧸ K) := by
    rw [← not_finite_iff_infinite]
    exact fun hf => hnot (K.finiteIndex_of_finite_quotient)
  let rep : D ⧸ K → D := fun q =>
    Classical.choose (QuotientGroup.mk_surjective (s := K) q)
  have hrep (q : D ⧸ K) : QuotientGroup.mk (s := K) (rep q) = q :=
    Classical.choose_spec (QuotientGroup.mk_surjective (s := K) q)
  let f (q : D ⧸ K) := g * (rep q : G)
  have hsep (i j : D ⧸ K) (hc : Commute (f i) (f j)) : i = j := by
    let a := rep i
    let b := rep j
    have hab : (a : G) * g * (b : G) = (b : G) * g * (a : G) := by
      apply mul_left_cancel (a := g)
      simpa [f, a, b, mul_assoc] using hc.eq
    have heq := congrArg (fun w : G => (a : G)⁻¹ * w * (a : G)⁻¹) hab
    have hcomm : Commute ((a : G)⁻¹ * (b : G)) g := by
      have hswap := (hD a b).symm.inv_right.eq
      change ((a : G)⁻¹ * (b : G)) * g = g * ((a : G)⁻¹ * (b : G))
      calc
        ((a : G)⁻¹ * (b : G)) * g =
            (a : G)⁻¹ * ((b : G) * g * (a : G)) * (a : G)⁻¹ := by group
        _ = (a : G)⁻¹ * ((a : G) * g * (b : G)) * (a : G)⁻¹ := heq.symm
        _ = g * ((b : G) * (a : G)⁻¹) := by group
        _ = _ := congrArg (g * ·) hswap
    have hq : QuotientGroup.mk (s := K) a = QuotientGroup.mk (s := K) b :=
      QuotientGroup.eq.mpr (Subgroup.mem_centralizer_singleton_iff.mpr hcomm.eq)
    exact (hrep i).symm.trans (hq.trans (hrep j))
  have hf : Function.Injective f := fun i j hij => hsep i j (hij ▸ Commute.refl _)
  have hc : (Erdos1098.nonCommutingGraph G).IsClique (Set.range f) := by
    rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩ hij hcomm
    exact hij (congrArg f (hsep i j hcomm))
  exact (Set.infinite_range_of_injective hf) (h _ hc)

private theorem center_finiteIndex_of_abelian {G : Type*} [Group G]
    (D : Subgroup G) [D.FiniteIndex]
    (hD : ∀ a b : D, Commute (a : G) (b : G))
    (hcentralizer : ∀ g : G, (centralizerOf g).FiniteIndex) :
    (Subgroup.center G).FiniteIndex := by
  classical
  obtain ⟨t, _, ht⟩ := Subgroup.exists_leftTransversal_of_FiniteIndex
    (D := D) (H := ⊤) le_top
  let K := ⨅ i ∈ t, centralizerOf (i : G)
  letI : K.FiniteIndex := Subgroup.finiteIndex_iInf' _ fun i _ => hcentralizer i
  apply Subgroup.finiteIndex_of_le (H := D ⊓ K)
  intro x hx
  refine Subgroup.mem_center_iff.mpr fun g => ?_
  have hg : g ∈ ⋃ i ∈ t, (i : G) • (D : Set G) := ht.symm ▸ Subgroup.mem_top g
  obtain ⟨i, hi, hgi⟩ := Set.mem_iUnion₂.mp hg
  obtain ⟨d, hd, rfl⟩ := Set.mem_smul_set.mp hgi
  have hxi : x ∈ centralizerOf (i : G) :=
    (Subgroup.mem_iInf.mp ((Subgroup.mem_iInf.mp hx.2) i)) hi
  have hxiC : Commute x (i : G) := Subgroup.mem_centralizer_singleton_iff.mp hxi
  exact (hxiC.mul_right (hD ⟨x, hx.1⟩ ⟨d, hd⟩)).eq.symm

end OMA

theorem OMA.solution : type_of% @Erdos1098.erdos_1098.variants.center_finiteIndex := by
  intro G _
  constructor
  · intro h
    classical
    let F := OMA.finiteCentralizers G
    letI : F.FiniteIndex := OMA.finiteCentralizers_finiteIndex h
    have hF (s : Set F) (hs : (Erdos1098.nonCommutingGraph F).IsClique s) : s.Finite := by
      apply Set.Finite.of_finite_image (f := Subtype.val) _ Subtype.val_injective.injOn
      apply h
      rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩ hne hxy
      exact hs hx hy (fun heq => hne (congrArg Subtype.val heq)) (Subtype.ext hxy)
    have hcent (x : F) : (OMA.centralizerOf x).FiniteIndex := by
      letI : (OMA.centralizerOf (x : G)).FiniteIndex := x.property
      have heq : OMA.centralizerOf x = (OMA.centralizerOf (x : G)).subgroupOf F := by
        ext y
        rw [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_subgroupOf,
          Subgroup.mem_centralizer_singleton_iff]
        exact Subtype.ext_iff
      rw [heq]
      infer_instance
    have hab : ∃ A : Subgroup F, A.FiniteIndex ∧ ∀ a b : A, Commute (a : F) (b : F) := by
      by_contra! hn
      obtain ⟨s, hs, hi⟩ := OMA.infinite_clique_of_noncommuting_subgroups hcent (by
        intro A hA
        obtain ⟨a, b, hab⟩ := hn A hA
        exact ⟨a, a.property, b, b.property, hab⟩)
      exact hi (hF s hs)
    obtain ⟨A, hA, hcomm⟩ := hab
    let D := A.map F.subtype
    letI : D.FiniteIndex := by
      constructor
      rw [Subgroup.index_map_subtype]
      exact mul_ne_zero hA.index_ne_zero (inferInstance : F.FiniteIndex).index_ne_zero
    have hD (a b : D) : Commute (a : G) (b : G) := by
      obtain ⟨a', ha', ha⟩ := a.property
      obtain ⟨b', hb', hb⟩ := b.property
      rw [← ha, ← hb]
      exact (hcomm ⟨a', ha'⟩ ⟨b', hb'⟩).map F.subtype
    exact OMA.center_finiteIndex_of_abelian D hD
      (OMA.centralizer_finiteIndex_of_abelian D hD h)
  · intro h
    letI := h
    exact OMA.finite_clique_of_center_finiteIndex
