import FormalConjectures.ErdosProblems.«393»
import Mathlib

/-! Berend and Osgood, On the equation P(x) = n! and a question of Erdős, J. Number Theory 42
(1992): for every integer polynomial P of degree at least 2, the n for which P(x) = n! is solvable
have density 0. Only split polynomials matter here. If f n = m, translating the factors of a
minimal factorisation of n! gives n! = (a + i_1) ... (a + i_t) with t at least 2 and every shift
in {0, ..., m}; this is H3. H1 is the case of two factors, written as a (a + m) = n!, which is the
Brocard type equation (2a + m)^2 = 4 n! + m^2. H2 is the case of three or more factors. Finitely
many shift sets occur for a fixed m, and finite unions and subsets of density zero sets have
density zero, so the three steps give the theorem. -/

namespace OMA.R_Erdos393_erdos_393_variants_berend_osgood_R1

open Finset Filter Erdos393
open scoped Nat Topology

private lemma dens_le {S T : Set ℕ} (h : S ⊆ T) (b : ℕ) :
    S.partialDensity Set.univ b ≤ T.partialDensity Set.univ b := by
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  exact_mod_cast Set.ncard_le_ncard (Set.inter_subset_inter_left _
    (Set.inter_subset_inter_left _ h)) ((Set.finite_Iio b).inter_of_right _)

private lemma dens_union_le (A B : Set ℕ) (b : ℕ) :
    (A ∪ B).partialDensity Set.univ b ≤
      A.partialDensity Set.univ b + B.partialDensity Set.univ b := by
  simp only [Set.partialDensity, Set.inter_univ]
  rw [← add_div]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  rw [Set.union_inter_distrib_right]
  exact_mod_cast Set.ncard_union_le _ _

private lemma dens_nonneg (A : Set ℕ) (b : ℕ) : 0 ≤ A.partialDensity Set.univ b :=
  div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

private lemma zero_of_subset {S T : Set ℕ} (h : S ⊆ T) (hT : T.HasDensity 0) :
    S.HasDensity 0 :=
  tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hT (dens_nonneg S) (dens_le h)

private lemma zero_union {A B : Set ℕ} (hA : A.HasDensity 0) (hB : B.HasDensity 0) :
    (A ∪ B).HasDensity 0 := by
  have h := hA.add hB
  rw [add_zero] at h
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h (dens_nonneg _)
    (dens_union_le A B)

private lemma zero_biUnion {ι : Type*} (s : Finset ι) (A : ι → Set ℕ)
    (h : ∀ i ∈ s, (A i).HasDensity 0) : (⋃ i ∈ s, A i).HasDensity 0 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [Set.HasDensity.empty]
  | insert j s hj ih =>
    rw [Finset.set_biUnion_insert]
    exact zero_union (h j (Finset.mem_insert_self j s))
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

private lemma two_factors
    (h1 : ∀ m : ℕ, 1 ≤ m → {n : ℕ | ∃ a : ℕ, a * (a + m) = n !}.HasDensity 0) (T : Finset ℕ) (hT : T.card = 2) :
    {n : ℕ | ∃ a : ℕ, ∏ i ∈ T, (a + i) = n !}.HasDensity 0 := by
  obtain ⟨x, y, hxy, rfl⟩ := Finset.card_eq_two.mp hT
  rcases lt_or_gt_of_ne hxy with hlt | hlt
  · refine zero_of_subset ?_ (h1 (y - x) (by omega))
    rintro n ⟨a, ha⟩
    refine ⟨a + x, ?_⟩
    rw [Finset.prod_pair hxy] at ha
    rw [← ha, show a + x + (y - x) = a + y by omega]
  · refine zero_of_subset ?_ (h1 (x - y) (by omega))
    rintro n ⟨a, ha⟩
    refine ⟨a + y, ?_⟩
    rw [Finset.prod_pair hxy] at ha
    rw [← ha, show a + y + (x - y) = a + x by omega, mul_comm]

/-- Two factors (Berend and Osgood for P(x) = x (x + m)). -/
def H1 : Prop := ∀ m : ℕ, 1 ≤ m → {n : ℕ | ∃ a : ℕ, a * (a + m) = n !}.HasDensity 0

/-- Three or more factors (Berend and Osgood for P(x) = the product of x + i over i in T). -/
def H2 : Prop := ∀ T : Finset ℕ, 3 ≤ T.card →
  {n : ℕ | ∃ a : ℕ, ∏ i ∈ T, (a + i) = n !}.HasDensity 0

/-- A minimal factorisation of n!, translated, is a product of shifts of a by at least two
distinct elements of {0, ..., f n}. -/
def H3 : Prop := ∀ n : ℕ, 2 ≤ n →
  ∃ T ⊆ Finset.range (f n + 1), 2 ≤ T.card ∧ ∃ a : ℕ, ∏ i ∈ T, (a + i) = n !

theorem main : H1 → H2 → H3 → type_of% @Erdos393.erdos_393.variants.berend_osgood := by
  intro h1 h2 h3 m
  classical
  let U := (Finset.range (m + 1)).powerset.filter (fun T => 2 ≤ T.card)
  let A : Finset ℕ → Set ℕ := fun T => {n : ℕ | ∃ a : ℕ, ∏ i ∈ T, (a + i) = n !}
  have hU : (⋃ T ∈ U, A T).HasDensity 0 := by
    refine zero_biUnion U A fun T hT => ?_
    have hc := (Finset.mem_filter.mp hT).2
    rcases Nat.lt_or_ge T.card 3 with hlt | hge
    · exact two_factors h1 T (by omega)
    · exact h2 T hge
  have hsmall : ({0, 1} : Set ℕ).HasDensity 0 :=
    Nat.hasDensity_zero_of_finite (Set.toFinite _)
  refine zero_of_subset ?_ (zero_union hsmall hU)
  intro n hn
  change f n = m at hn
  by_cases hn2 : n < 2
  · left
    interval_cases n <;> simp
  · right
    obtain ⟨T, hTs, hT2, a, ha⟩ := h3 n (by omega)
    rw [hn] at hTs
    simp only [Set.mem_iUnion]
    exact ⟨T, Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hTs, hT2⟩, a, ha⟩

end OMA.R_Erdos393_erdos_393_variants_berend_osgood_R1
