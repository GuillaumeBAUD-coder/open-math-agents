import OMAReductions.R_Hilbert17_hilbert_17th_problem_R1
import Mathlib.Order.Zorn

-- Step Hilbert17.hilbert_17th_problem.R1.H1 (Artin-Schreier preordering theorem)
-- Credit: @jared-jasinski

namespace Hilbert17H1

private structure IsPreorder {K : Type} [Field K] (P : Set K) : Prop where
  sq_mem : ∀ x : K, x * x ∈ P
  add_mem : ∀ {x y : K}, x ∈ P → y ∈ P → x + y ∈ P
  mul_mem : ∀ {x y : K}, x ∈ P → y ∈ P → x * y ∈ P
  neg_one_not_mem : (-1 : K) ∉ P

private lemma IsPreorder.zero_mem {K : Type} [Field K] {P : Set K} (hP : IsPreorder P) :
    (0 : K) ∈ P := by
  simpa using hP.sq_mem 0

private lemma IsPreorder.one_mem {K : Type} [Field K] {P : Set K} (hP : IsPreorder P) :
    (1 : K) ∈ P := by
  simpa using hP.sq_mem 1

-- Initial preordering P0 = { s + (-a) * t | IsSumSq s ∧ IsSumSq t }.
private lemma init_preorder {K : Type} [Field K] [hSR : IsSemireal K] {a : K} (ha : ¬ IsSumSq a) :
    let P0 : Set K := {x | ∃ s t : K, IsSumSq s ∧ IsSumSq t ∧ x = s + (-a) * t}
    IsPreorder P0 ∧ (-a) ∈ P0 := by
  intro P0
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ⟨0, 1, IsSumSq.zero, IsSumSq.one, by ring⟩⟩
  · intro x
    exact ⟨x * x, 0, IsSumSq.mul_self x, IsSumSq.zero, by ring⟩
  · rintro x y ⟨s1, t1, hs1, ht1, rfl⟩ ⟨s2, t2, hs2, ht2, rfl⟩
    exact ⟨s1 + s2, t1 + t2, hs1.add hs2, ht1.add ht2, by ring⟩
  · rintro x y ⟨s1, t1, hs1, ht1, rfl⟩ ⟨s2, t2, hs2, ht2, rfl⟩
    refine ⟨s1 * s2 + (a * a) * (t1 * t2), s1 * t2 + s2 * t1,
      (hs1.mul hs2).add ((IsSumSq.mul_self a).mul (ht1.mul ht2)),
      (hs1.mul ht2).add (hs2.mul ht1), by ring⟩
  · rintro ⟨s, t, hs, ht, hneg⟩
    by_cases ht0 : t = 0
    · subst ht0
      have h1s : 1 + s = 0 := by linear_combination -hneg
      exact hSR.1 hs h1s
    · have hat : a * t = 1 + s := by linear_combination hneg
      have ha_eq : a = (1 + s) * t * (t⁻¹ * t⁻¹) := by
        field_simp [ht0]
        linear_combination hat
      have hsq : IsSumSq a := by
        rw [ha_eq]
        exact ((IsSumSq.one.add hs).mul ht).mul (IsSumSq.mul_self t⁻¹)
      exact ha hsq

-- Adjoining an element x to a preordering P produces a preordering unless -1 is generated.
private lemma adjoin_total {K : Type} [Field K] {P : Set K} (hP : IsPreorder P)
    (hmax : ∀ Q : Set K, IsPreorder Q → P ⊆ Q → Q = P) (x : K) :
    x ∈ P ∨ -x ∈ P := by
  by_contra hneither
  push Not at hneither
  let Q : Set K := {z | ∃ u v : K, u ∈ P ∧ v ∈ P ∧ z = u + x * v}
  have hPQ : P ⊆ Q := fun u hu => ⟨u, 0, hu, hP.zero_mem, by ring⟩
  have hxQ : x ∈ Q := ⟨0, 1, hP.zero_mem, hP.one_mem, by ring⟩
  have hQ_not_prop : (-1 : K) ∈ Q := by
    by_contra hneg1
    have hQ : IsPreorder Q := by
      refine ⟨?_, ?_, ?_, hneg1⟩
      · intro z; exact hPQ (hP.sq_mem z)
      · rintro z1 z2 ⟨u1, v1, hu1, hv1, rfl⟩ ⟨u2, v2, hu2, hv2, rfl⟩
        exact ⟨u1 + u2, v1 + v2, hP.add_mem hu1 hu2, hP.add_mem hv1 hv2, by ring⟩
      · rintro z1 z2 ⟨u1, v1, hu1, hv1, rfl⟩ ⟨u2, v2, hu2, hv2, rfl⟩
        exact ⟨u1 * u2 + (x * x) * (v1 * v2), u1 * v2 + u2 * v1,
          hP.add_mem (hP.mul_mem hu1 hu2) (hP.mul_mem (hP.sq_mem x) (hP.mul_mem hv1 hv2)),
          hP.add_mem (hP.mul_mem hu1 hv2) (hP.mul_mem hu2 hv1), by ring⟩
    have hQP : Q = P := hmax Q hQ hPQ
    exact hneither.1 (hQP ▸ hxQ)
  obtain ⟨u, v, hu, hv, hneg⟩ := hQ_not_prop
  by_cases hv0 : v = 0
  · subst hv0
    have h1u : (-1 : K) = u := by linear_combination hneg
    exact hP.neg_one_not_mem (h1u ▸ hu)
  · have hxv : -x * v = 1 + u := by linear_combination hneg
    have hnx_eq : -x = (1 + u) * v * (v⁻¹ * v⁻¹) := by
      field_simp [hv0]
      linear_combination hxv
    have hnx_mem : -x ∈ P := by
      rw [hnx_eq]
      exact hP.mul_mem (hP.mul_mem (hP.add_mem hP.one_mem hu) hv) (hP.sq_mem v⁻¹)
    exact hneither.2 hnx_mem

private lemma antisymm_of_preorder {K : Type} [Field K] {P : Set K} (hP : IsPreorder P)
    {x : K} (hx : x ∈ P) (hnx : -x ∈ P) : x = 0 := by
  by_contra hx0
  have hneg1 : (-1 : K) = (-x) * x * (x⁻¹ * x⁻¹) := by
    field_simp [hx0]
  exact hP.neg_one_not_mem (hneg1 ▸ hP.mul_mem (hP.mul_mem hnx hx) (hP.sq_mem x⁻¹))

-- Maximal preordering extending P0 via Zorn's lemma.
private lemma exists_max_preorder {K : Type} [Field K] {P0 : Set K} (hP0 : IsPreorder P0) :
    ∃ P : Set K, P0 ⊆ P ∧ IsPreorder P ∧ ∀ Q : Set K, IsPreorder Q → P ⊆ Q → Q = P := by
  let S : Set (Set K) := {Q | P0 ⊆ Q ∧ IsPreorder Q}
  have hchain : ∀ c ⊆ S, IsChain (· ⊆ ·) c → c.Nonempty → ∃ ub ∈ S, ∀ s ∈ c, s ⊆ ub := by
    intro c hc hch hne
    refine ⟨⋃₀ c, ⟨?_, ?_⟩, fun s hs => Set.subset_sUnion_of_mem hs⟩
    · obtain ⟨s0, hs0⟩ := hne
      exact (hc hs0).1.trans (Set.subset_sUnion_of_mem hs0)
    · refine ⟨?_, ?_, ?_, ?_⟩
      · intro x
        obtain ⟨s0, hs0⟩ := hne
        exact Set.mem_sUnion.mpr ⟨s0, hs0, (hc hs0).2.sq_mem x⟩
      · intro x y hx hy
        obtain ⟨s1, hs1, hx1⟩ := Set.mem_sUnion.mp hx
        obtain ⟨s2, hs2, hy2⟩ := Set.mem_sUnion.mp hy
        rcases hch.total hs1 hs2 with h12 | h21
        · exact Set.mem_sUnion.mpr ⟨s2, hs2, (hc hs2).2.add_mem (h12 hx1) hy2⟩
        · exact Set.mem_sUnion.mpr ⟨s1, hs1, (hc hs1).2.add_mem hx1 (h21 hy2)⟩
      · intro x y hx hy
        obtain ⟨s1, hs1, hx1⟩ := Set.mem_sUnion.mp hx
        obtain ⟨s2, hs2, hy2⟩ := Set.mem_sUnion.mp hy
        rcases hch.total hs1 hs2 with h12 | h21
        · exact Set.mem_sUnion.mpr ⟨s2, hs2, (hc hs2).2.mul_mem (h12 hx1) hy2⟩
        · exact Set.mem_sUnion.mpr ⟨s1, hs1, (hc hs1).2.mul_mem hx1 (h21 hy2)⟩
      · intro hneg1
        obtain ⟨s0, hs0, hmem⟩ := Set.mem_sUnion.mp hneg1
        exact (hc hs0).2.neg_one_not_mem hmem
  obtain ⟨P, hP0P, hPmax⟩ := zorn_subset_nonempty S hchain P0 ⟨Set.Subset.rfl, hP0⟩
  have hPS : P ∈ S := hPmax.prop
  refine ⟨P, hP0P, hPS.2, fun Q hQ hPQ => ?_⟩
  exact (hPmax.eq_of_subset ⟨hP0P.trans hPQ, hQ⟩ hPQ).symm

end Hilbert17H1

theorem OMA.solution : OMA.R_Hilbert17_hilbert_17th_problem_R1.H1 := by
  classical
  intro K _ _ a ha
  obtain ⟨hP0, hna0⟩ := Hilbert17H1.init_preorder ha
  obtain ⟨P, hP0P, hP, hmax⟩ := Hilbert17H1.exists_max_preorder hP0
  have htotal : ∀ x : K, x ∈ P ∨ -x ∈ P := Hilbert17H1.adjoin_total hP hmax
  letI leInst : LE K := ⟨fun x y => y - x ∈ P⟩
  letI ltInst : LT K := ⟨fun x y => y - x ∈ P ∧ x ≠ y⟩
  have hle_iff : ∀ x y : K, x ≤ y ↔ y - x ∈ P := fun _ _ => Iff.rfl
  have hlt_iff : ∀ x y : K, x < y ↔ y - x ∈ P ∧ x ≠ y := fun _ _ => Iff.rfl
  let linOrd : LinearOrder K :=
    { le := leInst.le
      lt := ltInst.lt
      le_refl := fun x => by change x - x ∈ P; simpa using hP.zero_mem
      le_trans := fun x y z hxy hyz => by
        change z - x ∈ P
        have : z - x = (z - y) + (y - x) := by ring
        rw [this]
        exact hP.add_mem hyz hxy
      le_antisymm := fun x y hxy hyx => by
        have hneg : -(y - x) = x - y := by ring
        have h0 : y - x = 0 := Hilbert17H1.antisymm_of_preorder hP hxy (hneg ▸ hyx)
        exact (sub_eq_zero.mp h0).symm
      lt_iff_le_not_ge := fun x y => by
        change (y - x ∈ P ∧ x ≠ y) ↔ (y - x ∈ P ∧ ¬ x - y ∈ P)
        constructor
        · rintro ⟨hxy, hne⟩
          refine ⟨hxy, fun hyx => hne ?_⟩
          have hneg : -(y - x) = x - y := by ring
          exact (sub_eq_zero.mp (Hilbert17H1.antisymm_of_preorder hP hxy (hneg ▸ hyx))).symm
        · rintro ⟨hxy, hnot⟩
          refine ⟨hxy, ?_⟩
          rintro rfl
          exact hnot (by simpa using hP.zero_mem)
      le_total := fun x y => by
        change y - x ∈ P ∨ x - y ∈ P
        rcases htotal (y - x) with h | h
        · exact Or.inl h
        · exact Or.inr (by convert h using 1; ring)
      toDecidableLE := Classical.decRel _ }
  letI : LinearOrder K := linOrd
  have hstrict : IsStrictOrderedRing K :=
    { add_le_add_left := fun x y hxy z => by
        change (y + z) - (x + z) ∈ P
        have : (y + z) - (x + z) = y - x := by ring
        rw [this]
        exact hxy
      le_of_add_le_add_left := fun x y z h => by
        change z - y ∈ P
        have h' : (x + z) - (x + y) ∈ P := h
        have : z - y = (x + z) - (x + y) := by ring
        rw [this]
        exact h'
      zero_le_one := by
        change (1 : K) - 0 ∈ P
        simpa using hP.one_mem
      mul_lt_mul_of_pos_left := fun x hx y z hyz => by
        have hxP : x ∈ P := by simpa using hx.1
        have hx0 : x ≠ 0 := hx.2.symm
        have hyzP : z - y ∈ P := hyz.1
        have hyz0 : z - y ≠ 0 := sub_ne_zero.mpr hyz.2.symm
        refine ⟨?_, ?_⟩
        · change x * z - x * y ∈ P
          have : x * z - x * y = x * (z - y) := by ring
          rw [this]
          exact hP.mul_mem hxP hyzP
        · intro heq
          have : x * (z - y) = 0 := by linear_combination -heq
          exact mul_ne_zero hx0 hyz0 this
      mul_lt_mul_of_pos_right := fun x hx y z hyz => by
        have hxP : x ∈ P := by simpa using hx.1
        have hx0 : x ≠ 0 := hx.2.symm
        have hyzP : z - y ∈ P := hyz.1
        have hyz0 : z - y ≠ 0 := sub_ne_zero.mpr hyz.2.symm
        refine ⟨?_, ?_⟩
        · change z * x - y * x ∈ P
          have : z * x - y * x = (z - y) * x := by ring
          rw [this]
          exact hP.mul_mem hyzP hxP
        · intro heq
          have : (z - y) * x = 0 := by linear_combination -heq
          exact mul_ne_zero hyz0 hx0 this }
  refine ⟨linOrd, hstrict, ?_⟩
  change (0 : K) - a ∈ P ∧ a ≠ 0
  refine ⟨by simpa using hP0P hna0, fun ha0 => ha (ha0 ▸ IsSumSq.zero)⟩
