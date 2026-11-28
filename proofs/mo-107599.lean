import OMAStatements.S_mo_107599
import Mathlib

open Filter MeasureTheory
open scoped ENNReal Topology

namespace OMA.Helpers

/-- The clopen algebra of the one-point compactification of the positive integers, with `0`
playing the role of the point at infinity. -/
def moF : Set (Set ℕ) := {A | (A.Finite ∧ 0 ∉ A) ∨ (Aᶜ.Finite ∧ 0 ∈ A)}

theorem moF_countable : moF.Countable := by
  refine (Set.Countable.ofPred_finite.union (Set.Countable.ofPred_finite.image compl)).mono ?_
  rintro A (⟨hA, _⟩ | ⟨hA, _⟩)
  · exact Or.inl hA
  · exact Or.inr ⟨Aᶜ, hA, compl_compl A⟩

theorem moF_empty : (∅ : Set ℕ) ∈ moF := Or.inl ⟨Set.finite_empty, fun h => h⟩

theorem moF_compl {A : Set ℕ} (hA : A ∈ moF) : Aᶜ ∈ moF := by
  rcases hA with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact Or.inr ⟨by rw [compl_compl]; exact h1, h2⟩
  · exact Or.inl ⟨h1, fun h => h h2⟩

theorem moF_union {A B : Set ℕ} (hA : A ∈ moF) (hB : B ∈ moF) : A ∪ B ∈ moF := by
  rcases hA with ⟨a1, a2⟩ | ⟨a1, a2⟩
  · rcases hB with ⟨b1, b2⟩ | ⟨b1, b2⟩
    · exact Or.inl ⟨a1.union b1, by simp [a2, b2]⟩
    · exact Or.inr ⟨b1.subset (by rw [Set.compl_union]; exact Set.inter_subset_right), Or.inr b2⟩
  · exact Or.inr ⟨a1.subset (by rw [Set.compl_union]; exact Set.inter_subset_left), Or.inl a2⟩

theorem moF_eventually_empty (s : ℕ → Set ℕ) (hs : ∀ n, s n ∈ moF)
    (hd : Pairwise (fun i j => Disjoint (s i) (s j))) (hU : (⋃ n, s n) ∈ moF) :
    ∃ N, ∀ n, N ≤ n → s n = ∅ := by
  -- a finite set `K` and an index `k` with `s n ⊆ K` for every `n ≠ k`
  obtain ⟨K, k, hK, hsub⟩ : ∃ K : Set ℕ, ∃ k : ℕ, K.Finite ∧ ∀ n, n ≠ k → s n ⊆ K := by
    rcases hU with ⟨h1, _⟩ | ⟨_, h2⟩
    · exact ⟨_, 0, h1, fun n _ => Set.subset_iUnion s n⟩
    · obtain ⟨k, hk⟩ := Set.mem_iUnion.mp h2
      have hck : (s k)ᶜ.Finite := by
        rcases hs k with ⟨_, h⟩ | ⟨h, _⟩
        · exact absurd hk h
        · exact h
      refine ⟨_, k, hck, fun n hn x hx hxk => ?_⟩
      exact Set.disjoint_left.mp (hd hn) hx hxk
  have hI : {n | n ≠ k ∧ (s n).Nonempty}.Finite := by
    refine (hK.biUnion (fun x _ => (show {n | x ∈ s n}.Subsingleton from ?_).finite)).subset ?_
    · intro i hi j hj
      by_contra hij
      exact Set.disjoint_left.mp (hd hij) hi hj
    · rintro n ⟨hn, x, hx⟩
      exact Set.mem_biUnion (hsub n hn hx) hx
  obtain ⟨M, hM⟩ := (hI.insert k).bddAbove
  refine ⟨M + 1, fun n hn => ?_⟩
  by_contra hne
  have hn' : n ∈ insert k {n | n ≠ k ∧ (s n).Nonempty} := by
    by_cases hk : n = k
    · exact Or.inl hk
    · exact Or.inr ⟨hk, Set.nonempty_iff_ne_empty.mpr hne⟩
  have := hM hn'
  omega

theorem moF_finite_add (v : Set ℕ → ℝ≥0∞) (hv0 : v ∅ = 0)
    (hadd : ∀ A ∈ moF, ∀ B ∈ moF, Disjoint A B → v (A ∪ B) = v A + v B)
    (s : ℕ → Set ℕ) (hs : ∀ n, s n ∈ moF)
    (hd : Pairwise (fun i j => Disjoint (s i) (s j))) (N : ℕ) :
    (⋃ n ∈ Finset.range N, s n) ∈ moF ∧
      v (⋃ n ∈ Finset.range N, s n) = ∑ n ∈ Finset.range N, v (s n) := by
  induction N with
  | zero => simp [moF_empty, hv0]
  | succ N ih =>
    rw [Finset.range_add_one, Finset.set_biUnion_insert, Finset.sum_insert Finset.notMem_range_self]
    have hdis : Disjoint (s N) (⋃ n ∈ Finset.range N, s n) := by
      rw [Set.disjoint_iUnion₂_right]
      intro i hi
      exact hd (by simp at hi; omega)
    refine ⟨moF_union (hs N) ih.1, ?_⟩
    rw [hadd _ (hs N) _ ih.1 hdis, ih.2]

theorem moF_standard : OMA.S_mo_107599.MaoStandardField moF := by
  refine ⟨moF_countable, moF_empty, fun A hA => moF_compl hA, fun A hA B hB => moF_union hA hB, ?_⟩
  intro v hv0 _ hadd s hs hd hU
  obtain ⟨N, hN⟩ := moF_eventually_empty s hs hd hU
  have hUeq : (⋃ n, s n) = ⋃ n ∈ Finset.range N, s n := by
    ext x
    simp only [Set.mem_iUnion, Finset.mem_range]
    constructor
    · rintro ⟨n, hn⟩
      refine ⟨n, ?_, hn⟩
      by_contra h
      rw [hN n (by omega)] at hn
      exact hn
    · rintro ⟨n, _, hn⟩
      exact ⟨n, hn⟩
  rw [hUeq, (moF_finite_add v hv0 hadd s hs hd N).2]
  rw [tsum_eq_sum (s := Finset.range N)]
  intro b hb
  rw [hN b (by simp at hb; omega), hv0]

theorem mo_dirac_apply {α : Type} (m : MeasurableSpace α) (A : Set α) (x : α)
    (hA : MeasurableSet[m] A) : @Measure.dirac α m x A = A.indicator 1 x :=
  Measure.dirac_apply' x hA

theorem mo_dirac_prob {α : Type} (m : MeasurableSpace α) (x : α) :
    @IsProbabilityMeasure α m (@Measure.dirac α m x) := inferInstance

end OMA.Helpers

open OMA.Helpers in
/-- Counterexample: the clopen algebra of the one-point compactification of the positive
integers is standard, the Dirac measures at `n + 1` converge to the Dirac measure at the point
at infinity `0` on every set of the field, but not on the singleton of `0`. -/
theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_107599.main) := by
  intro h
  have hconv : ∀ A ∈ moF, Tendsto (fun n => @Measure.dirac ℕ (MeasurableSpace.generateFrom moF) (n + 1) A)
      atTop (𝓝 (@Measure.dirac ℕ (MeasurableSpace.generateFrom moF) 0 A)) := by
    intro A hA
    have hm := MeasurableSpace.measurableSet_generateFrom hA
    simp only [mo_dirac_apply _ A _ hm]
    rcases hA with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · obtain ⟨M, hM⟩ := h1.bddAbove
      refine tendsto_const_nhds.congr' (Filter.eventually_atTop.mpr ⟨M, fun n hn => ?_⟩)
      have hn1 : n + 1 ∉ A := fun hx => by have := hM hx; omega
      simp [Set.indicator_of_notMem h2, Set.indicator_of_notMem hn1]
    · obtain ⟨M, hM⟩ := h1.bddAbove
      refine tendsto_const_nhds.congr' (Filter.eventually_atTop.mpr ⟨M, fun n hn => ?_⟩)
      have hn1 : n + 1 ∈ A := by
        by_contra hx
        have := hM hx
        omega
      simp [Set.indicator_of_mem h2, Set.indicator_of_mem hn1]
  have h0 : MeasurableSet[MeasurableSpace.generateFrom moF] ({0} : Set ℕ) := by
    have hU : MeasurableSet[MeasurableSpace.generateFrom moF] (⋃ n : ℕ, ({n + 1} : Set ℕ)) :=
      MeasurableSet.iUnion fun n => MeasurableSpace.measurableSet_generateFrom
        (Or.inl ⟨Set.finite_singleton _, by simp⟩)
    have he : ({0} : Set ℕ) = (⋃ n : ℕ, ({n + 1} : Set ℕ))ᶜ := by
      ext x
      simp only [Set.mem_singleton_iff, Set.mem_compl_iff, Set.mem_iUnion]
      constructor
      · rintro rfl ⟨n, hn⟩
        omega
      · intro hx
        by_contra hx0
        exact hx ⟨x - 1, by omega⟩
    rw [he]
    exact hU.compl
  have key := h ℕ moF moF_standard (fun n => @Measure.dirac ℕ (MeasurableSpace.generateFrom moF) (n + 1))
    (@Measure.dirac ℕ (MeasurableSpace.generateFrom moF) 0) (fun n => mo_dirac_prob _ _)
    (mo_dirac_prob _ _) hconv {0} h0
  simp only [mo_dirac_apply _ _ _ h0] at key
  have hz : (fun n : ℕ => ({0} : Set ℕ).indicator (1 : ℕ → ℝ≥0∞) (n + 1)) = fun _ => 0 := by
    funext n
    exact Set.indicator_of_notMem (by simp) _
  rw [hz, Set.indicator_of_mem (Set.mem_singleton 0)] at key
  have := tendsto_nhds_unique key tendsto_const_nhds
  simp at this
