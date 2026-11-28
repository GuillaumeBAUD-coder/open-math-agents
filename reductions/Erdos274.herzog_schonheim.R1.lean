import FormalConjectures.ErdosProblems.«274»
import Mathlib.GroupTheory.CosetCover
import Mathlib.GroupTheory.Nilpotent
import Mathlib.GroupTheory.Solvable
import Mathlib.Data.Nat.Totient
import Mathlib.Data.Set.Card.Arithmetic
import Mathlib.Algebra.Group.TransferInstance
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
Reduction `Erdos274.herzog_schonheim.R1` of the Herzog-Schonheim conjecture
(`Erdos274.herzog_schonheim`).

Unconditionally proved in-file:
1. B. H. Neumann finite-index theorem for exact coverings (`∀ i, (P.parts i).FiniteIndex`) and
   common-normal-core descent to a finite quotient group in `Type 0` with trivial common core
   `⨅ i, (P.parts i).normalCore = ⊥` and identical subgroup indices.
2. Exact Egyptian-fraction identity `∑ i, ((P.parts i).index : ℚ)⁻¹ = 1` and `2 ≤ (P.parts i).index`.
3. Index-2 coset-restriction lemma and minimal-counterexample index-2 elimination (`∀ i, 3 ≤ index`),
   together with complete unconditional proofs for all `k ≤ 4` (`k = 2, 3, 4`) in arbitrary groups.
4. Complete Berger-Felzenbaum-Fraenkel (1986) proof of the Herzog-Schonheim conjecture for all
   nilpotent groups (finite and infinite, hence all abelian groups), via the totient union bound
   for normal Sylow `p`-subgroups at the largest prime factor of `|G|`.

Remaining frontier (finite groups in `Type 0`, `k ≥ 5`, trivial common core, all indices `≥ 3`,
exact Egyptian-fraction sum `∑ 1 / index = 1`):
- `H1`: Finite non-nilpotent solvable groups (Menon, arXiv:2611.11002).
- `H2`: Finite non-solvable groups (the remaining open frontier).
-/

-- Reduction Erdos274.herzog_schonheim.R1 of Erdős Problem 274 — herzog schonheim
-- Credit: @paynebrowning

namespace OMA.R_Erdos274_herzog_schonheim_R1

def H1 : Prop :=
  ∀ (G : Type) [Group G] [Fintype G] [Group.IsSolvable G], ¬ Group.IsNilpotent G →
    ∀ {k : ℕ}, 5 ≤ k →
      ∀ (P : Erdos274.Group.ExactCovering G (Fin k)),
        (⨅ i : Fin k, (P.parts i).normalCore) = ⊥ →
        (∀ i : Fin k, 3 ≤ (P.parts i).index) →
        (∑ i : Fin k, ((P.parts i).index : ℚ)⁻¹ = 1) →
        ∃ i j : Fin k, i ≠ j ∧ (P.parts i).index = (P.parts j).index

def H2 : Prop :=
  ∀ (G : Type) [Group G] [Fintype G], ¬ Group.IsSolvable G →
    ∀ {k : ℕ}, 5 ≤ k →
      ∀ (P : Erdos274.Group.ExactCovering G (Fin k)),
        (⨅ i : Fin k, (P.parts i).normalCore) = ⊥ →
        (∀ i : Fin k, 3 ≤ (P.parts i).index) →
        (∑ i : Fin k, ((P.parts i).index : ℚ)⁻¹ = 1) →
        ∃ i j : Fin k, i ≠ j ∧ (P.parts i).index = (P.parts j).index

section ReductionProofs

open Finset
open scoped Pointwise Cardinal

/- ### Module 1: Finite-Index, Common-Core Quotient Descent, and Type-0 Transport -/

private lemma coset_nonempty {G ι : Type*} [Group G] [Fintype ι]
    (P : Erdos274.Group.ExactCovering G ι) (i : ι) :
    (P.reps i • (P.parts i : Set G)).Nonempty :=
  ⟨P.reps i, ⟨1, (P.parts i).one_mem, mul_one _⟩⟩

private lemma part_finiteIndex {G ι : Type*} [Group G] [Fintype ι]
    (P : Erdos274.Group.ExactCovering G ι) (i : ι) : (P.parts i).FiniteIndex := by
  classical
  let s : Finset ι := Finset.univ.filter fun j => (P.parts j).FiniteIndex
  have hcov_univ : ⋃ j ∈ (Finset.univ : Finset ι), P.reps j • (P.parts j : Set G) = Set.univ := by
    simpa using P.covers
  have hs_cover : ⋃ j ∈ s, P.reps j • (P.parts j : Set G) = Set.univ := by
    simpa [s] using Subgroup.leftCoset_cover_filter_FiniteIndex hcov_univ
  have hpairwise : ((Set.univ : Set ι) ∪ (s : Set ι)).PairwiseDisjoint
      (fun j => P.reps j • (P.parts j : Set G)) := by
    simpa using P.disjoint
  have hsubset : (⋃ j ∈ (Set.univ : Set ι), P.reps j • (P.parts j : Set G)) ⊆
      ⋃ j ∈ (s : Set ι), P.reps j • (P.parts j : Set G) := by
    rw [show (⋃ j ∈ (Set.univ : Set ι), P.reps j • (P.parts j : Set G)) = Set.univ by
      simpa using P.covers]
    rw [Finset.set_biUnion_coe, hs_cover]
  have hi : i ∈ (s : Set ι) :=
    hpairwise.subset_of_biUnion_subset_biUnion
      (fun j _ => coset_nonempty P j) hsubset (Set.mem_univ i)
  simpa [s] using hi

private lemma commonCore_finiteIndex {G ι : Type*} [Group G] [Fintype ι]
    (P : Erdos274.Group.ExactCovering G ι) :
    (⨅ i : ι, (P.parts i).normalCore).FiniteIndex := by
  have hfi : ∀ i : ι, (P.parts i).normalCore.FiniteIndex := fun i => by
    let : (P.parts i).FiniteIndex := part_finiteIndex P i
    infer_instance
  exact Subgroup.finiteIndex_iInf hfi

private lemma commonCore_normal {G ι : Type*} [Group G] [Fintype ι]
    (P : Erdos274.Group.ExactCovering G ι) :
    (⨅ i : ι, (P.parts i).normalCore).Normal :=
  { conj_mem := fun n hn g => Subgroup.mem_iInf.mpr fun i =>
      (Subgroup.normalCore_normal _).conj_mem n (Subgroup.mem_iInf.mp hn i) g }

private lemma mul_mem_smul_coset {G : Type*} [Group G] {g y h : G} {H : Subgroup G}
    (hy : y ∈ g • (H : Set G)) (hh : h ∈ H) : y * h ∈ g • (H : Set G) := by
  rw [mem_leftCoset_iff] at hy ⊢
  simpa [mul_assoc] using H.mul_mem hy hh

private lemma quotient_covering_exists {G ι : Type*} [Group G] [Fintype ι]
    (P : Erdos274.Group.ExactCovering G ι) (N : Subgroup G) [N.Normal]
    (hN : ∀ i, N ≤ P.parts i) :
    ∃ Q : Erdos274.Group.ExactCovering (G ⧸ N) ι,
      (∀ i, Q.parts i = (P.parts i).map (QuotientGroup.mk' N)) ∧
      (∀ i, (Q.parts i).index = (P.parts i).index) := by
  let Q : Erdos274.Group.ExactCovering (G ⧸ N) ι := {
    parts := fun i => (P.parts i).map (QuotientGroup.mk' N)
    reps := fun i => QuotientGroup.mk (P.reps i)
    nonempty := fun i => ⟨1, ((P.parts i).map (QuotientGroup.mk' N)).one_mem⟩
    disjoint := by
      rintro i - j - hij
      refine Set.disjoint_left.mpr fun {c} hci hcj => ?_
      have hci' : c ∈ (QuotientGroup.mk' N) '' (P.reps i • (P.parts i : Set G)) := by
        rw [Set.image_smul_distrib, ← Subgroup.coe_map]
        exact hci
      have hcj' : c ∈ (QuotientGroup.mk' N) '' (P.reps j • (P.parts j : Set G)) := by
        rw [Set.image_smul_distrib, ← Subgroup.coe_map]
        exact hcj
      obtain ⟨x, hx, hcx⟩ := hci'
      obtain ⟨y, hy, hcy⟩ := hcj'
      have hxy : y⁻¹ * x ∈ N := by
        rw [← QuotientGroup.eq]
        change (QuotientGroup.mk' N) y = (QuotientGroup.mk' N) x
        rw [hcx, hcy]
      have hx' : x ∈ P.reps j • (P.parts j : Set G) := by
        simpa only [mul_inv_cancel_left] using mul_mem_smul_coset hy (hN j hxy)
      exact Set.disjoint_left.mp (P.disjoint (Set.mem_univ i) (Set.mem_univ j) hij) hx hx'
    covers := by
      rw [Set.eq_univ_iff_forall]
      intro c
      obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective c
      have hx : x ∈ ⋃ i, P.reps i • (P.parts i : Set G) := P.covers ▸ Set.mem_univ x
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
      refine Set.mem_iUnion.mpr ⟨i, ?_⟩
      change (QuotientGroup.mk' N) x ∈ (QuotientGroup.mk' N) (P.reps i) •
        (((P.parts i).map (QuotientGroup.mk' N) : Subgroup (G ⧸ N)) : Set (G ⧸ N))
      rw [Subgroup.coe_map, ← Set.image_smul_distrib]
      exact ⟨x, hi, rfl⟩
  }
  refine ⟨Q, fun i => rfl, fun i => ?_⟩
  have hker : (QuotientGroup.mk' N).ker ≤ P.parts i := by
    rw [QuotientGroup.ker_mk']
    exact hN i
  have hcomap : ((P.parts i).map (QuotientGroup.mk' N)).comap (QuotientGroup.mk' N) = P.parts i :=
    Subgroup.comap_map_eq_self hker
  calc ((P.parts i).map (QuotientGroup.mk' N)).index
      = (((P.parts i).map (QuotientGroup.mk' N)).comap (QuotientGroup.mk' N)).index :=
        (Subgroup.index_comap_of_surjective (H := (P.parts i).map (QuotientGroup.mk' N))
          (QuotientGroup.mk'_surjective N)).symm
    _ = (P.parts i).index := by rw [hcomap]

private lemma quotient_commonCore_eq_bot {G ι : Type*} [Group G] [Fintype ι]
    (P : Erdos274.Group.ExactCovering G ι)
    (N : Subgroup G) [N.Normal] (hN_eq : N = ⨅ i : ι, (P.parts i).normalCore)
    (Q : Erdos274.Group.ExactCovering (G ⧸ N) ι)
    (hQ : ∀ i, Q.parts i = (P.parts i).map (QuotientGroup.mk' N)) :
    (⨅ i : ι, (Q.parts i).normalCore) = ⊥ := by
  rw [eq_bot_iff]
  intro c hc
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective c
  have hxN : x ∈ N := by
    rw [hN_eq, Subgroup.mem_iInf]
    intro i
    change ∀ g : G, g * x * g⁻¹ ∈ P.parts i
    intro g
    have hci : (QuotientGroup.mk x : G ⧸ N) ∈ (Q.parts i).normalCore :=
      Subgroup.mem_iInf.mp hc i
    have hconj : (QuotientGroup.mk g : G ⧸ N) * QuotientGroup.mk x * (QuotientGroup.mk g)⁻¹ ∈ Q.parts i :=
      hci (QuotientGroup.mk g)
    rw [hQ i] at hconj
    change (QuotientGroup.mk' N) (g * x * g⁻¹) ∈ (P.parts i).map (QuotientGroup.mk' N) at hconj
    have hker : (QuotientGroup.mk' N).ker ≤ P.parts i := by
      rw [QuotientGroup.ker_mk', hN_eq]
      exact (iInf_le (fun j => (P.parts j).normalCore) i).trans (Subgroup.normalCore_le _)
    rwa [← Subgroup.mem_comap, Subgroup.comap_map_eq_self hker] at hconj
  exact (QuotientGroup.eq_one_iff x).mpr hxN

private lemma transport_covering_fin {G : Type*} [Group G] [Fintype G]
    {ι : Type*} [Fintype ι] (P : Erdos274.Group.ExactCovering G ι) :
    ∃ (G0 : Type) (_ : Group G0) (_ : Fintype G0) (_e : G0 ≃* G)
      (P0 : Erdos274.Group.ExactCovering G0 (Fin (Fintype.card ι))),
      (∀ i, (P0.parts i).index = (P.parts ((Fintype.equivFin ι).symm i)).index) ∧
      ((⨅ i, (P.parts i).normalCore) = ⊥ → (⨅ i, (P0.parts i).normalCore) = ⊥) := by
  let G0 : Type := { _x : Fin (Fintype.card G) // True }
  let eG : G0 ≃ G := (Equiv.subtypeUnivEquiv fun _ => trivial).trans (Fintype.equivFin G).symm
  let _instG : Group G0 := eG.group
  let φ : G0 ≃* G := {
    toEquiv := eG
    map_mul' := fun x y => by
      show eG (eG.symm (eG x * eG y)) = eG x * eG y
      exact eG.apply_symm_apply (eG x * eG y)
  }
  let eι : Fin (Fintype.card ι) ≃ ι := (Fintype.equivFin ι).symm
  let P0 : Erdos274.Group.ExactCovering G0 (Fin (Fintype.card ι)) := {
    parts := fun i => (P.parts (eι i)).comap φ.toMonoidHom
    reps := fun i => φ.symm (P.reps (eι i))
    nonempty := fun i => ⟨1, Subgroup.one_mem _⟩
    disjoint := by
      rintro i - j - hij
      refine Set.disjoint_left.mpr fun {x} hxi hxj => ?_
      have hij' : eι i ≠ eι j := fun h => hij (eι.injective h)
      have hxi' : φ x ∈ P.reps (eι i) • (P.parts (eι i) : Set G) := by
        rw [mem_leftCoset_iff, SetLike.mem_coe, Subgroup.mem_comap] at hxi
        rw [mem_leftCoset_iff, SetLike.mem_coe]
        change φ ((φ.symm (P.reps (eι i)))⁻¹ * x) ∈ P.parts (eι i) at hxi
        simpa [map_mul, map_inv, φ.apply_symm_apply] using hxi
      have hxj' : φ x ∈ P.reps (eι j) • (P.parts (eι j) : Set G) := by
        rw [mem_leftCoset_iff, SetLike.mem_coe, Subgroup.mem_comap] at hxj
        rw [mem_leftCoset_iff, SetLike.mem_coe]
        change φ ((φ.symm (P.reps (eι j)))⁻¹ * x) ∈ P.parts (eι j) at hxj
        simpa [map_mul, map_inv, φ.apply_symm_apply] using hxj
      exact Set.disjoint_left.mp (P.disjoint (Set.mem_univ (eι i)) (Set.mem_univ (eι j)) hij') hxi' hxj'
    covers := by
      rw [Set.eq_univ_iff_forall]
      intro x
      have hx : φ x ∈ ⋃ j, P.reps j • (P.parts j : Set G) := P.covers ▸ Set.mem_univ (φ x)
      obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hx
      refine Set.mem_iUnion.mpr ⟨eι.symm j, ?_⟩
      rw [Equiv.apply_symm_apply, mem_leftCoset_iff, SetLike.mem_coe, Subgroup.mem_comap]
      change φ ((φ.symm (P.reps j))⁻¹ * x) ∈ P.parts j
      rw [map_mul, map_inv, φ.apply_symm_apply]
      rwa [mem_leftCoset_iff] at hj
  }
  refine ⟨G0, _instG, inferInstance, φ, P0, ?_, ?_⟩
  · intro i
    exact Subgroup.index_comap_of_surjective (H := P.parts (eι i)) φ.surjective
  · intro hbot
    rw [eq_bot_iff]
    intro x hx
    apply φ.injective
    rw [map_one, ← Subgroup.mem_bot, ← hbot, Subgroup.mem_iInf]
    intro j
    change ∀ g : G, g * φ x * g⁻¹ ∈ P.parts j
    intro g
    have hxj : x ∈ (P0.parts (eι.symm j)).normalCore := Subgroup.mem_iInf.mp hx (eι.symm j)
    have hconj : φ.symm g * x * (φ.symm g)⁻¹ ∈ P0.parts (eι.symm j) := hxj (φ.symm g)
    change φ (φ.symm g * x * (φ.symm g)⁻¹) ∈ P.parts (eι (eι.symm j)) at hconj
    simpa [map_mul, map_inv, φ.apply_symm_apply, Equiv.apply_symm_apply] using hconj

/- ### Module 2: Cardinality, Index-Sum Identity, Index-2 Reduction, and k ≤ 4 -/

private lemma ncard_smul_coset {G : Type*} [Group G] [Finite G] (g : G) (H : Subgroup G) :
    (g • (H : Set G)).ncard = Nat.card H := by
  have h1 : (g • (H : Set G)).ncard = (H : Set G).ncard := by simp
  rw [h1, ← Nat.card_coe_set_eq]
  rfl

private lemma sum_inv_index_eq_one {G : Type*} [Group G] [Fintype G]
    {ι : Type*} [Fintype ι] (P : Erdos274.Group.ExactCovering G ι) :
    ∑ i : ι, ((P.parts i).index : ℚ)⁻¹ = 1 := by
  classical
  have hsum_card : ∑ i : ι, (Nat.card (P.parts i) : ℚ) = (Fintype.card G : ℚ) := by
    have hdisj : (Set.univ : Set ι).PairwiseDisjoint (fun i => P.reps i • (P.parts i : Set G)) :=
      P.disjoint
    have hncard : (⋃ i, P.reps i • (P.parts i : Set G)).ncard =
        ∑ i : ι, (P.reps i • (P.parts i : Set G)).ncard := by
      rw [Set.ncard_iUnion_of_finite (fun i => Set.toFinite _) (Set.pairwise_univ.mp hdisj),
        finsum_eq_sum_of_fintype]
    rw [P.covers, Set.ncard_univ, Nat.card_eq_fintype_card] at hncard
    have hnat : Fintype.card G = ∑ i : ι, Nat.card (P.parts i) := by
      rw [hncard]
      exact Finset.sum_congr rfl fun i _ => ncard_smul_coset (P.reps i) (P.parts i)
    exact_mod_cast hnat.symm
  have hGpos : (Fintype.card G : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hterm : ∀ i : ι, ((P.parts i).index : ℚ)⁻¹ = (Nat.card (P.parts i) : ℚ) / (Fintype.card G : ℚ) := by
    intro i
    have hmul : (Nat.card (P.parts i) : ℚ) * ((P.parts i).index : ℚ) = (Fintype.card G : ℚ) := by
      have hnat := Subgroup.card_mul_index (P.parts i)
      rw [Nat.card_eq_fintype_card (α := G)] at hnat
      exact_mod_cast hnat
    have hidx : ((P.parts i).index : ℚ) ≠ 0 := by
      intro h0
      rw [h0, mul_zero] at hmul
      exact hGpos hmul.symm
    field_simp [hidx, hGpos]
    linarith
  rw [Finset.sum_congr rfl fun i _ => hterm i, ← Finset.sum_div, hsum_card, div_self hGpos]

private lemma two_le_index_of_one_lt_card {G ι : Type*} [Group G] [Fintype ι]
    (hι : 1 < Fintype.card ι) (P : Erdos274.Group.ExactCovering G ι) (i : ι) :
    2 ≤ (P.parts i).index := by
  have hne0 : (P.parts i).index ≠ 0 := by
    let : (P.parts i).FiniteIndex := part_finiteIndex P i
    exact Subgroup.FiniteIndex.index_ne_zero
  have hne1 : (P.parts i).index ≠ 1 := by
    intro h1
    have htop : P.parts i = ⊤ := Subgroup.index_eq_one.mp h1
    have huniv : P.reps i • (P.parts i : Set G) = Set.univ := by
      ext x
      simp [htop]
    let : Nontrivial ι := Fintype.one_lt_card_iff_nontrivial.mp hι
    obtain ⟨j, hij⟩ := exists_ne i
    obtain ⟨x, hxj⟩ := coset_nonempty P j
    have hxi : x ∈ P.reps i • (P.parts i : Set G) := by rw [huniv]; trivial
    exact Set.disjoint_left.mp (P.disjoint (Set.mem_univ i) (Set.mem_univ j) hij.symm) hxi hxj
  omega

private lemma index_two_restrict {G : Type} [Group G] [Fintype G]
    {k : ℕ} (hk : 2 ≤ k) (P : Erdos274.Group.ExactCovering G (Fin k))
    (i0 : Fin k) (hi0 : (P.parts i0).index = 2) :
    ∃ (Q : Erdos274.Group.ExactCovering (P.parts i0) (Fin (k - 1))),
      Nat.card (P.parts i0) < Nat.card G ∧
      (∀ j : Fin (k - 1), ∃ j' : Fin k, j' ≠ i0 ∧ 2 * (Q.parts j).index = (P.parts j').index) ∧
      (∀ i j : Fin (k - 1), i ≠ j → (Q.parts i).index = (Q.parts j).index →
        ∃ i' j' : Fin k, i' ≠ j' ∧ (P.parts i').index = (P.parts j').index) := by
  classical
  let Hsub : Subgroup G := P.parts i0
  let j1 : Fin k := if i0 = ⟨0, by omega⟩ then ⟨1, by omega⟩ else ⟨0, by omega⟩
  have hj1_ne : j1 ≠ i0 := by
    dsimp [j1]
    split_ifs with h
    · intro heq; rw [h] at heq; exact Nat.one_ne_zero (congrArg Fin.val heq)
    · exact Ne.symm h
  let g1 : G := P.reps j1
  have hg1_not : g1 ∉ P.reps i0 • (Hsub : Set G) := by
    intro hmem
    have hg1j : g1 ∈ P.reps j1 • (P.parts j1 : Set G) := ⟨1, (P.parts j1).one_mem, mul_one _⟩
    exact Set.disjoint_left.mp (P.disjoint (Set.mem_univ j1) (Set.mem_univ i0) hj1_ne) hg1j hmem
  let : Fintype (G ⧸ Hsub) := Fintype.ofFinite _
  have hquot_card : Fintype.card (G ⧸ Hsub) = 2 := by
    rw [← Nat.card_eq_fintype_card]
    exact hi0
  have hcomp : ∀ x : G, x ∉ P.reps i0 • (Hsub : Set G) → x ∈ g1 • (Hsub : Set G) := by
    intro x hx
    have hq_ne1 : (QuotientGroup.mk g1 : G ⧸ Hsub) ≠ QuotientGroup.mk (P.reps i0) := by
      intro heq
      apply hg1_not
      rwa [mem_leftCoset_iff, SetLike.mem_coe, ← QuotientGroup.eq, eq_comm]
    have hq_ne2 : (QuotientGroup.mk x : G ⧸ Hsub) ≠ QuotientGroup.mk (P.reps i0) := by
      intro heq
      apply hx
      rwa [mem_leftCoset_iff, SetLike.mem_coe, ← QuotientGroup.eq, eq_comm]
    have hq_eq : (QuotientGroup.mk x : G ⧸ Hsub) = QuotientGroup.mk g1 := by
      by_contra hne
      have h3 : 3 ≤ Fintype.card (G ⧸ Hsub) := by
        have hsub : ({QuotientGroup.mk (P.reps i0), QuotientGroup.mk g1, QuotientGroup.mk x} :
            Finset (G ⧸ Hsub)).card = 3 := by
          have hb : QuotientGroup.mk g1 ∉ ({QuotientGroup.mk x} : Finset (G ⧸ Hsub)) := by
            simp [Ne.symm hne]
          have ha : QuotientGroup.mk (P.reps i0) ∉
              ({QuotientGroup.mk g1, QuotientGroup.mk x} : Finset (G ⧸ Hsub)) := by
            simp [hq_ne1.symm, hq_ne2.symm]
          rw [Finset.card_insert_of_notMem ha, Finset.card_insert_of_notMem hb,
            Finset.card_singleton]
        exact hsub ▸ Finset.card_le_univ _
      omega
    rw [mem_leftCoset_iff, SetLike.mem_coe, ← QuotientGroup.eq]
    exact hq_eq.symm
  have hsub_coset : ∀ j : Fin k, j ≠ i0 →
      (g1⁻¹ * P.reps j) • (P.parts j : Set G) ⊆ (Hsub : Set G) := by
    intro j hj x hx
    rw [Set.mem_smul_set] at hx
    obtain ⟨h, hh, rfl⟩ := hx
    have hmem : P.reps j * h ∈ P.reps j • (P.parts j : Set G) := ⟨h, hh, rfl⟩
    have hnot : P.reps j * h ∉ P.reps i0 • (Hsub : Set G) := fun hbad =>
      Set.disjoint_left.mp (P.disjoint (Set.mem_univ j) (Set.mem_univ i0) hj) hmem hbad
    have hcos := hcomp (P.reps j * h) hnot
    rw [mem_leftCoset_iff] at hcos
    simpa [mul_assoc] using hcos
  have hrep_mem : ∀ j : Fin k, j ≠ i0 → g1⁻¹ * P.reps j ∈ Hsub := fun j hj =>
    hsub_coset j hj ⟨1, (P.parts j).one_mem, mul_one _⟩
  have hle_H : ∀ j : Fin k, j ≠ i0 → P.parts j ≤ Hsub := by
    intro j hj h hh
    have h1 := hrep_mem j hj
    have h2 : (g1⁻¹ * P.reps j) * h ∈ Hsub := hsub_coset j hj ⟨h, hh, rfl⟩
    simpa [mul_assoc] using Hsub.mul_mem (Hsub.inv_mem h1) h2
  have hcard_sub : Fintype.card {j : Fin k // j ≠ i0} = k - 1 := by
    rw [Fintype.card_subtype_compl]
    simp
  let e_idx : Fin (k - 1) ≃ {j : Fin k // j ≠ i0} :=
    (Fintype.equivFinOfCardEq hcard_sub).symm
  let Q : Erdos274.Group.ExactCovering Hsub (Fin (k - 1)) := {
    parts := fun j => (P.parts (e_idx j).1).subgroupOf Hsub
    reps := fun j => ⟨g1⁻¹ * P.reps (e_idx j).1, hrep_mem (e_idx j).1 (e_idx j).2⟩
    nonempty := fun j => ⟨1, Subgroup.one_mem _⟩
    disjoint := by
      rintro i - j - hij
      refine Set.disjoint_left.mpr fun {x} hxi hxj => ?_
      have hij' : (e_idx i).1 ≠ (e_idx j).1 := fun heq => hij (e_idx.injective (Subtype.ext heq))
      have hxi' : g1 * (x : G) ∈ P.reps (e_idx i).1 • (P.parts (e_idx i).1 : Set G) := by
        rw [mem_leftCoset_iff] at hxi ⊢
        change ((⟨g1⁻¹ * P.reps (e_idx i).1, _⟩ : Hsub)⁻¹ * x : G) ∈ P.parts (e_idx i).1 at hxi
        simpa [mul_assoc] using hxi
      have hxj' : g1 * (x : G) ∈ P.reps (e_idx j).1 • (P.parts (e_idx j).1 : Set G) := by
        rw [mem_leftCoset_iff] at hxj ⊢
        change ((⟨g1⁻¹ * P.reps (e_idx j).1, _⟩ : Hsub)⁻¹ * x : G) ∈ P.parts (e_idx j).1 at hxj
        simpa [mul_assoc] using hxj
      exact Set.disjoint_left.mp
        (P.disjoint (Set.mem_univ (e_idx i).1) (Set.mem_univ (e_idx j).1) hij') hxi' hxj'
    covers := by
      rw [Set.eq_univ_iff_forall]
      intro x
      have hx_not : g1 * (x : G) ∉ P.reps i0 • (Hsub : Set G) := by
        intro hbad
        rw [mem_leftCoset_iff] at hbad
        have hbad' : (P.reps i0)⁻¹ * g1 ∈ Hsub := by
          have := Hsub.mul_mem hbad (Hsub.inv_mem x.2)
          simpa [mul_assoc] using this
        apply hg1_not
        rwa [mem_leftCoset_iff]
      have hx_cov : g1 * (x : G) ∈ ⋃ j : Fin k, P.reps j • (P.parts j : Set G) :=
        P.covers ▸ Set.mem_univ _
      obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hx_cov
      have hji0 : j ≠ i0 := by
        intro heq
        subst heq
        exact hx_not hj
      refine Set.mem_iUnion.mpr ⟨e_idx.symm ⟨j, hji0⟩, ?_⟩
      rw [mem_leftCoset_iff, SetLike.mem_coe, Subgroup.mem_subgroupOf]
      have heq_idx : (e_idx (e_idx.symm ⟨j, hji0⟩)).1 = j :=
        congrArg Subtype.val (e_idx.apply_symm_apply ⟨j, hji0⟩)
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      rw [heq_idx]
      rw [mem_leftCoset_iff] at hj
      simpa [mul_assoc] using hj
  }
  have hmul_idx : ∀ j : Fin (k - 1), 2 * (Q.parts j).index = (P.parts (e_idx j).1).index := by
    intro j
    have hcard_eq : Nat.card (Q.parts j) = Nat.card (P.parts (e_idx j).1) :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe (hle_H (e_idx j).1 (e_idx j).2)).toEquiv
    have hmulG := Subgroup.card_mul_index (P.parts (e_idx j).1)
    have hmulH := Subgroup.card_mul_index (Q.parts j)
    have hmulH0 := Subgroup.card_mul_index Hsub
    rw [hi0] at hmulH0
    have hpos : 0 < Nat.card (P.parts (e_idx j).1) := Nat.card_pos
    have heq_mul : Nat.card (P.parts (e_idx j).1) * (2 * (Q.parts j).index) =
        Nat.card (P.parts (e_idx j).1) * (P.parts (e_idx j).1).index := by
      calc Nat.card (P.parts (e_idx j).1) * (2 * (Q.parts j).index)
          = 2 * (Nat.card (Q.parts j) * (Q.parts j).index) := by rw [← hcard_eq]; ring
        _ = Nat.card Hsub * 2 := by rw [hmulH]; ring
        _ = Nat.card G := hmulH0
        _ = Nat.card (P.parts (e_idx j).1) * (P.parts (e_idx j).1).index := hmulG.symm
    exact Nat.mul_left_cancel hpos heq_mul
  refine ⟨Q, ?_, ?_, ?_⟩
  · have hmul := Subgroup.card_mul_index Hsub
    rw [hi0] at hmul
    have hHpos : 0 < Nat.card Hsub := Nat.card_pos
    change Nat.card Hsub < Nat.card G
    omega
  · intro j
    exact ⟨(e_idx j).1, (e_idx j).2, hmul_idx j⟩
  · intro i j hij heq
    refine ⟨(e_idx i).1, (e_idx j).1, fun h => hij (e_idx.injective (Subtype.ext h)), ?_⟩
    rw [← hmul_idx i, ← hmul_idx j, heq]

private lemma hs_card_two {G : Type} [Group G] [Fintype G]
    (P : Erdos274.Group.ExactCovering G (Fin 2)) :
    ∃ i j : Fin 2, i ≠ j ∧ (P.parts i).index = (P.parts j).index := by
  have hsum := sum_inv_index_eq_one P
  rw [Fin.sum_univ_two] at hsum
  have h0 : 2 ≤ (P.parts 0).index := two_le_index_of_one_lt_card (by decide) P 0
  have h1 : 2 ≤ (P.parts 1).index := two_le_index_of_one_lt_card (by decide) P 1
  by_contra hcon
  push Not at hcon
  have hne : (P.parts 0).index ≠ (P.parts 1).index := hcon 0 1 (by decide)
  have hlt : ((P.parts 0).index : ℚ)⁻¹ + ((P.parts 1).index : ℚ)⁻¹ < 1 := by
    have ha0 : (0 : ℚ) < (P.parts 0).index := by exact_mod_cast (by omega : 0 < (P.parts 0).index)
    have ha1 : (0 : ℚ) < (P.parts 1).index := by exact_mod_cast (by omega : 0 < (P.parts 1).index)
    rcases Nat.lt_or_gt_of_ne hne with h | h
    · have h0' : ((P.parts 0).index : ℚ)⁻¹ ≤ 1 / 2 := by
        rw [inv_eq_one_div, one_div_le_one_div ha0 (by norm_num)]; exact_mod_cast h0
      have h1' : ((P.parts 1).index : ℚ)⁻¹ ≤ 1 / 3 := by
        rw [inv_eq_one_div, one_div_le_one_div ha1 (by norm_num)]; exact_mod_cast (by omega : 3 ≤ (P.parts 1).index)
      linarith
    · have h0' : ((P.parts 0).index : ℚ)⁻¹ ≤ 1 / 3 := by
        rw [inv_eq_one_div, one_div_le_one_div ha0 (by norm_num)]; exact_mod_cast (by omega : 3 ≤ (P.parts 0).index)
      have h1' : ((P.parts 1).index : ℚ)⁻¹ ≤ 1 / 2 := by
        rw [inv_eq_one_div, one_div_le_one_div ha1 (by norm_num)]; exact_mod_cast h1
      linarith
  linarith

private lemma hs_card_three {G : Type} [Group G] [Fintype G]
    (P : Erdos274.Group.ExactCovering G (Fin 3)) :
    ∃ i j : Fin 3, i ≠ j ∧ (P.parts i).index = (P.parts j).index := by
  by_contra hcon
  push Not at hcon
  have hge2 : ∀ i : Fin 3, 2 ≤ (P.parts i).index := fun i =>
    two_le_index_of_one_lt_card (by decide) P i
  by_cases h2 : ∃ i0 : Fin 3, (P.parts i0).index = 2
  · obtain ⟨i0, hi0⟩ := h2
    obtain ⟨Q, -, -, hback⟩ := index_two_restrict (by omega : 2 ≤ 3) P i0 hi0
    let : Fintype (P.parts i0) := Fintype.ofFinite _
    obtain ⟨i, j, hij, heq⟩ := hs_card_two Q
    obtain ⟨i', j', hij', heq'⟩ := hback i j hij heq
    exact hcon i' j' hij' heq'
  · push Not at h2
    have hge3 : ∀ i : Fin 3, 3 ≤ (P.parts i).index := fun i => by
      have := hge2 i; have := h2 i; omega
    have hsum := sum_inv_index_eq_one P
    have hinv_le : ∀ i : Fin 3, ((P.parts i).index : ℚ)⁻¹ ≤ 1 / 3 := fun i => by
      have hi : (0 : ℚ) < (P.parts i).index := by exact_mod_cast (by have := hge3 i; omega : 0 < (P.parts i).index)
      rw [inv_eq_one_div, one_div_le_one_div hi (by norm_num)]
      exact_mod_cast hge3 i
    have hneq : (P.parts 0).index ≠ (P.parts 1).index ∧
        (P.parts 0).index ≠ (P.parts 2).index ∧
        (P.parts 1).index ≠ (P.parts 2).index :=
      ⟨hcon 0 1 (by decide), hcon 0 2 (by decide), hcon 1 2 (by decide)⟩
    -- Three distinct integers >= 3 have reciprocal sum <= 1/3 + 1/4 + 1/5 < 1.
    have hnot_all_3 : ∃ i : Fin 3, 4 ≤ (P.parts i).index := by
      by_contra hall
      push Not at hall
      have := hge3 0; have := hge3 1; have := hall 0; have := hall 1
      omega
    have hlt1 : ∑ i : Fin 3, ((P.parts i).index : ℚ)⁻¹ < 1 := by
      rw [Fin.sum_univ_three]
      have ha0 := hge3 0; have ha1 := hge3 1; have ha2 := hge3 2
      have h0p : (0 : ℚ) < (P.parts 0).index := by exact_mod_cast (by omega : 0 < (P.parts 0).index)
      have h1p : (0 : ℚ) < (P.parts 1).index := by exact_mod_cast (by omega : 0 < (P.parts 1).index)
      have h2p : (0 : ℚ) < (P.parts 2).index := by exact_mod_cast (by omega : 0 < (P.parts 2).index)
      -- At least one is >= 5 since three distinct naturals >= 3 cannot all be <= 4.
      have h5 : 5 ≤ (P.parts 0).index ∨ 5 ≤ (P.parts 1).index ∨ 5 ≤ (P.parts 2).index := by omega
      rcases h5 with h | h | h
      · have h05 : ((P.parts 0).index : ℚ)⁻¹ ≤ 1 / 5 := by
          rw [inv_eq_one_div, one_div_le_one_div h0p (by norm_num)]; exact_mod_cast h
        linarith [hinv_le 1, hinv_le 2]
      · have h15 : ((P.parts 1).index : ℚ)⁻¹ ≤ 1 / 5 := by
          rw [inv_eq_one_div, one_div_le_one_div h1p (by norm_num)]; exact_mod_cast h
        linarith [hinv_le 0, hinv_le 2]
      · have h25 : ((P.parts 2).index : ℚ)⁻¹ ≤ 1 / 5 := by
          rw [inv_eq_one_div, one_div_le_one_div h2p (by norm_num)]; exact_mod_cast h
        linarith [hinv_le 0, hinv_le 1]
    linarith

private lemma sum_inv_four_distinct_ge_three_lt_one (S : Finset ℕ) (hcard : S.card = 4)
    (hge : ∀ x ∈ S, 3 ≤ x) : ∑ x ∈ S, (x : ℚ)⁻¹ < 1 := by
  classical
  let A : Finset ℕ := S ∩ {3, 4, 5}
  let B : Finset ℕ := S \ {3, 4, 5}
  have hsplit : S = A ∪ B := by
    ext x; simp only [Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff, A, B]; tauto
  have hdisj : Disjoint A B := Finset.disjoint_left.mpr fun x hxA hxB => by
    simp only [Finset.mem_inter, Finset.mem_sdiff, A, B] at hxA hxB
    exact hxB.2 hxA.2
  have hcardAB : A.card + B.card = 4 := by
    rw [← Finset.card_union_of_disjoint hdisj, ← hsplit, hcard]
  have hB_ge6 : ∀ x ∈ B, 6 ≤ x := by
    intro x hx
    rw [Finset.mem_sdiff] at hx
    have hxS := hge x hx.1
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hx
    omega
  have hB_sum : ∑ x ∈ B, (x : ℚ)⁻¹ ≤ (B.card : ℚ) * (1 / 6) := by
    have hterm : ∀ x ∈ B, (x : ℚ)⁻¹ ≤ 1 / 6 := fun x hx => by
      have hx6 := hB_ge6 x hx
      have hxp : (0 : ℚ) < x := by exact_mod_cast (by omega : 0 < x)
      rw [inv_eq_one_div, one_div_le_one_div hxp (by norm_num)]
      exact_mod_cast hx6
    calc ∑ x ∈ B, (x : ℚ)⁻¹ ≤ ∑ _x ∈ B, (1 / 6 : ℚ) := Finset.sum_le_sum hterm
      _ = (B.card : ℚ) * (1 / 6) := by simp
  have hsum_eq : ∑ x ∈ S, (x : ℚ)⁻¹ = ∑ x ∈ A, (x : ℚ)⁻¹ + ∑ x ∈ B, (x : ℚ)⁻¹ := by
    rw [hsplit, Finset.sum_union hdisj]
  have hA_sub : A ⊆ {3, 4, 5} := Finset.inter_subset_right
  have hlt_bound : ∑ x ∈ A, (x : ℚ)⁻¹ + (B.card : ℚ) * (1 / 6) < 1 := by
    by_cases h3 : 3 ∈ A <;> by_cases h4 : 4 ∈ A <;> by_cases h5 : 5 ∈ A
    · have hAeq : A = {3, 4, 5} := by
        ext x; simp only [Finset.mem_insert, Finset.mem_singleton]
        exact ⟨fun hx => by have := hA_sub hx; simpa using this,
               fun hx => by rcases hx with rfl | rfl | rfl <;> assumption⟩
      have hAc : A.card = 3 := by rw [hAeq]; decide
      have hBc : (B.card : ℚ) = 1 := by exact_mod_cast (by omega : B.card = 1)
      rw [hAeq, hBc]; norm_num
    · have hAeq : A = {3, 4} := by
        ext x; simp only [Finset.mem_insert, Finset.mem_singleton]
        exact ⟨fun hx => by have := hA_sub hx; simp only [Finset.mem_insert, Finset.mem_singleton] at this; rcases this with rfl | rfl | rfl <;> tauto,
               fun hx => by rcases hx with rfl | rfl <;> assumption⟩
      have hAc : A.card = 2 := by rw [hAeq]; decide
      have hBc : (B.card : ℚ) = 2 := by exact_mod_cast (by omega : B.card = 2)
      rw [hAeq, hBc]; norm_num
    · have hAeq : A = {3, 5} := by
        ext x; simp only [Finset.mem_insert, Finset.mem_singleton]
        exact ⟨fun hx => by have := hA_sub hx; simp only [Finset.mem_insert, Finset.mem_singleton] at this; rcases this with rfl | rfl | rfl <;> tauto,
               fun hx => by rcases hx with rfl | rfl <;> assumption⟩
      have hAc : A.card = 2 := by rw [hAeq]; decide
      have hBc : (B.card : ℚ) = 2 := by exact_mod_cast (by omega : B.card = 2)
      rw [hAeq, hBc]; norm_num
    · have hAeq : A = {3} := by
        ext x; simp only [Finset.mem_singleton]
        exact ⟨fun hx => by have := hA_sub hx; simp only [Finset.mem_insert, Finset.mem_singleton] at this; rcases this with rfl | rfl | rfl <;> tauto,
               fun hx => by subst hx; exact h3⟩
      have hAc : A.card = 1 := by rw [hAeq]; decide
      have hBc : (B.card : ℚ) = 3 := by exact_mod_cast (by omega : B.card = 3)
      rw [hAeq, hBc]; norm_num
    · have hAeq : A = {4, 5} := by
        ext x; simp only [Finset.mem_insert, Finset.mem_singleton]
        exact ⟨fun hx => by have := hA_sub hx; simp only [Finset.mem_insert, Finset.mem_singleton] at this; rcases this with rfl | rfl | rfl <;> tauto,
               fun hx => by rcases hx with rfl | rfl <;> assumption⟩
      have hAc : A.card = 2 := by rw [hAeq]; decide
      have hBc : (B.card : ℚ) = 2 := by exact_mod_cast (by omega : B.card = 2)
      rw [hAeq, hBc]; norm_num
    · have hAeq : A = {4} := by
        ext x; simp only [Finset.mem_singleton]
        exact ⟨fun hx => by have := hA_sub hx; simp only [Finset.mem_insert, Finset.mem_singleton] at this; rcases this with rfl | rfl | rfl <;> tauto,
               fun hx => by subst hx; exact h4⟩
      have hAc : A.card = 1 := by rw [hAeq]; decide
      have hBc : (B.card : ℚ) = 3 := by exact_mod_cast (by omega : B.card = 3)
      rw [hAeq, hBc]; norm_num
    · have hAeq : A = {5} := by
        ext x; simp only [Finset.mem_singleton]
        exact ⟨fun hx => by have := hA_sub hx; simp only [Finset.mem_insert, Finset.mem_singleton] at this; rcases this with rfl | rfl | rfl <;> tauto,
               fun hx => by subst hx; exact h5⟩
      have hAc : A.card = 1 := by rw [hAeq]; decide
      have hBc : (B.card : ℚ) = 3 := by exact_mod_cast (by omega : B.card = 3)
      rw [hAeq, hBc]; norm_num
    · have hAeq : A = ∅ := by
        ext x; simp only [Finset.notMem_empty, iff_false]
        intro hx; have := hA_sub hx; simp only [Finset.mem_insert, Finset.mem_singleton] at this; rcases this with rfl | rfl | rfl <;> tauto
      have hAc : A.card = 0 := by rw [hAeq]; decide
      have hBc : (B.card : ℚ) = 4 := by exact_mod_cast (by omega : B.card = 4)
      rw [hAeq, hBc]; norm_num
  linarith

private lemma hs_card_four {G : Type} [Group G] [Fintype G]
    (P : Erdos274.Group.ExactCovering G (Fin 4)) :
    ∃ i j : Fin 4, i ≠ j ∧ (P.parts i).index = (P.parts j).index := by
  by_contra hcon
  push Not at hcon
  have hge2 : ∀ i : Fin 4, 2 ≤ (P.parts i).index := fun i =>
    two_le_index_of_one_lt_card (by decide) P i
  by_cases h2 : ∃ i0 : Fin 4, (P.parts i0).index = 2
  · obtain ⟨i0, hi0⟩ := h2
    obtain ⟨Q, -, -, hback⟩ := index_two_restrict (by omega : 2 ≤ 4) P i0 hi0
    let : Fintype (P.parts i0) := Fintype.ofFinite _
    obtain ⟨i, j, hij, heq⟩ := hs_card_three Q
    obtain ⟨i', j', hij', heq'⟩ := hback i j hij heq
    exact hcon i' j' hij' heq'
  · push Not at h2
    have hge3 : ∀ i : Fin 4, 3 ≤ (P.parts i).index := fun i => by
      have := hge2 i; have := h2 i; omega
    let S : Finset ℕ := Finset.univ.image (fun i : Fin 4 => (P.parts i).index)
    have hinj : Function.Injective (fun i : Fin 4 => (P.parts i).index) := fun i j hij => by
      by_contra hne; exact hcon i j hne hij
    have hScard : S.card = 4 := by
      rw [Finset.card_image_of_injective _ hinj, Finset.card_fin]
    have hSge3 : ∀ x ∈ S, 3 ≤ x := fun x hx => by
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hx
      exact hge3 i
    have hlt := sum_inv_four_distinct_ge_three_lt_one S hScard hSge3
    have heq_sum : ∑ x ∈ S, (x : ℚ)⁻¹ = ∑ i : Fin 4, ((P.parts i).index : ℚ)⁻¹ :=
      Finset.sum_image (fun i _ j _ h => hinj h)
    rw [heq_sum, sum_inv_index_eq_one P] at hlt
    linarith

/- ### Module 3: Berger-Felzenbaum-Fraenkel (1986) for All Finite Nilpotent Groups -/

private lemma le_mul_totient :
    ∀ {d : ℕ}, 0 < d → ∀ {M : ℕ}, 1 ≤ M →
      (∀ q ∈ d.primeFactors, q ≤ M) → d ≤ M * d.totient := by
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
    intro hd M hM hfac
    rcases eq_or_lt_of_le (Nat.succ_le_of_lt hd) with h1 | h1
    · simpa [← h1] using hM
    obtain ⟨q, hq_mem, hq_max⟩ :=
      Finset.exists_max_image d.primeFactors id
        ⟨d.minFac, Nat.mem_primeFactors.mpr ⟨Nat.minFac_prime (by omega), d.minFac_dvd, hd.ne'⟩⟩
    have hq : q.Prime := Nat.prime_of_mem_primeFactors hq_mem
    have hqd : q ∣ d := Nat.dvd_of_mem_primeFactors hq_mem
    set e := d.factorization q
    set d' := d / q ^ e
    have hsplit : q ^ e * d' = d := Nat.ordProj_mul_ordCompl_eq_self d q
    have hd'pos : 0 < d' := Nat.ordCompl_pos q hd.ne'
    have hqe : 0 < e := hq.factorization_pos_of_dvd hd.ne' hqd
    have hd'lt : d' < d := Nat.div_lt_self hd (Nat.one_lt_pow hqe.ne' hq.one_lt)
    have hfac' : ∀ r ∈ d'.primeFactors, r ≤ q - 1 := by
      intro r hr
      obtain ⟨hrp, hrd', -⟩ := Nat.mem_primeFactors.mp hr
      have hd'd : d' ∣ d := Nat.ordCompl_dvd d q
      have hrd : r ∈ d.primeFactors := Nat.mem_primeFactors.mpr ⟨hrp, hrd'.trans hd'd, hd.ne'⟩
      have hrq : r ≠ q := by
        rintro rfl
        exact Nat.not_dvd_ordCompl hq hd.ne' hrd'
      have := hq_max r hrd
      simp only [id] at this
      omega
    have hIH : d' ≤ (q - 1) * d'.totient := ih d' hd'lt hd'pos (by have := hq.two_le; omega) hfac'
    have htot : d.totient = q ^ (e - 1) * (q - 1) * d'.totient := by
      rw [← hsplit, Nat.totient_mul (Nat.Coprime.pow_left e (Nat.coprime_ordCompl hq hd.ne')),
        Nat.totient_prime_pow hq hqe]
    calc d = q ^ e * d' := hsplit.symm
      _ ≤ q ^ e * ((q - 1) * d'.totient) := Nat.mul_le_mul_left _ hIH
      _ = q * (q ^ (e - 1) * (q - 1) * d'.totient) := by
          rw [show q ^ e = q * q ^ (e - 1) from by rw [← pow_succ', Nat.sub_add_cancel hqe]]
          ring
      _ = q * d.totient := by rw [htot]
      _ ≤ M * d.totient := Nat.mul_le_mul_right _ (hfac q hq_mem)

private lemma sum_totient_biUnion_le {κ : Type*} [Fintype κ] {p : ℕ} (hp : p.Prime)
    (m a : κ → ℕ) (hm : ∀ j, ¬ p ∣ m j) (hm0 : ∀ j, 0 < m j) :
    ∑ d ∈ Finset.univ.biUnion fun j => (m j * p ^ a j).divisors, d.totient ≤
      ∑ d' ∈ Finset.univ.biUnion fun j => (m j).divisors,
        d'.totient * p ^ ((Finset.univ.filter fun j => d' ∣ m j).sup a) := by
  classical
  set D : Finset ℕ := Finset.univ.biUnion fun j => (m j * p ^ a j).divisors
  set D' : Finset ℕ := Finset.univ.biUnion fun j => (m j).divisors
  let ψ : ℕ → ℕ := fun d => ordCompl[p] d
  have hkey : ∀ d ∈ D, ∃ j, ψ d ∣ m j ∧ d.factorization p ≤ a j := by
    intro d hd
    obtain ⟨j, -, hdj⟩ := Finset.mem_biUnion.mp hd
    obtain ⟨hdvd, hne⟩ := Nat.mem_divisors.mp hdj
    refine ⟨j, ?_, ?_⟩
    · have h1 := Nat.ordCompl_dvd_ordCompl_of_dvd hdvd p
      rwa [Nat.ordCompl_mul, Nat.ordCompl_self_pow hp,
        show ordCompl[p] (m j) = m j by simp [Nat.factorization_eq_zero_of_not_dvd (hm j)],
        mul_one] at h1
    · have h2 := (Nat.factorization_le_iff_dvd (Nat.pos_of_mem_divisors hdj).ne' hne).mpr hdvd
      have h3 := Finsupp.le_def.mp h2 p
      rwa [Nat.factorization_mul (hm0 j).ne' (pow_ne_zero _ hp.pos.ne'),
        hp.factorization_pow, Finsupp.add_apply,
        Nat.factorization_eq_zero_of_not_dvd (hm j), Finsupp.single_eq_same, zero_add] at h3
  have hmaps : ∀ d ∈ D, ψ d ∈ D' := fun d hd => by
    obtain ⟨j, hj, -⟩ := hkey d hd
    exact Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ j, Nat.mem_divisors.mpr ⟨hj, (hm0 j).ne'⟩⟩
  rw [← Finset.sum_fiberwise_of_maps_to hmaps (fun d => d.totient)]
  refine Finset.sum_le_sum fun d' hd' => ?_
  set A := (Finset.univ.filter fun j => d' ∣ m j).sup a
  have hd'p : ¬ p ∣ d' := by
    obtain ⟨j, -, hj⟩ := Finset.mem_biUnion.mp hd'
    exact fun hdvd => hm j (hdvd.trans (Nat.mem_divisors.mp hj).1)
  have hfib : ∀ d ∈ D.filter fun d => ψ d = d', d' * p ^ d.factorization p = d := by
    intro d hd
    obtain ⟨-, hdψ⟩ := Finset.mem_filter.mp hd
    rw [← hdψ]
    dsimp [ψ]
    rw [mul_comm]
    exact Nat.ordProj_mul_ordCompl_eq_self d p
  have hinj : ∀ x ∈ D.filter fun d => ψ d = d', ∀ y ∈ D.filter fun d => ψ d = d',
      x.factorization p = y.factorization p → x = y := fun x hx y hy hxy => by
    rw [← hfib x hx, ← hfib y hy, hxy]
  calc ∑ d ∈ D.filter (fun d => ψ d = d'), d.totient
      = ∑ c ∈ (D.filter fun d => ψ d = d').image fun d => d.factorization p, (d' * p ^ c).totient := by
          rw [Finset.sum_image hinj]
          exact Finset.sum_congr rfl fun d hd => by rw [hfib d hd]
    _ ≤ ∑ c ∈ Finset.range (A + 1), (d' * p ^ c).totient := by
          refine Finset.sum_le_sum_of_subset fun c hc => ?_
          obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hc
          obtain ⟨hdD, -⟩ := Finset.mem_filter.mp hd
          obtain ⟨j, hj1, hj2⟩ := hkey d hdD
          have : d.factorization p ≤ A := le_trans hj2 (Finset.le_sup
            (Finset.mem_filter.mpr ⟨Finset.mem_univ j, (Finset.mem_filter.mp hd).2 ▸ hj1⟩))
          exact Finset.mem_range.mpr (Nat.lt_succ_of_le this)
    _ = d'.totient * ∑ c ∈ Finset.range (A + 1), (p ^ c).totient := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun c _ =>
            Nat.totient_mul (Nat.Coprime.pow_right c ((hp.coprime_iff_not_dvd.mpr hd'p).symm))
    _ = d'.totient * p ^ A := by
          congr 1
          have := Nat.sum_totient (p ^ A)
          rwa [Nat.divisors_prime_pow hp, Finset.sum_map] at this

private lemma exists_largest_prime_split {n : ℕ} (hn2 : 2 ≤ n) :
    ∃ p l s t : ℕ, p.Prime ∧ (∀ q ∈ n.primeFactors, q ≤ p) ∧
      l = n.factorization p ∧ s = p ^ l ∧ t = ordCompl[p] n ∧ s * t = n ∧ s.Coprime t ∧ 1 < s ∧ t < n := by
  have hn0 : n ≠ 0 := by omega
  have hpne : n.primeFactors.Nonempty := Nat.nonempty_primeFactors.mpr (by omega)
  let p := n.primeFactors.max' hpne
  have hp : p.Prime := Nat.prime_of_mem_primeFactors (n.primeFactors.max'_mem hpne)
  have hp_dvd : p ∣ n := Nat.dvd_of_mem_primeFactors (n.primeFactors.max'_mem hpne)
  have hpmax : ∀ q ∈ n.primeFactors, q ≤ p := fun q hq => n.primeFactors.le_max' q hq
  let l := n.factorization p
  let s := p ^ l
  let t := ordCompl[p] n
  have hst : s * t = n := Nat.ordProj_mul_ordCompl_eq_self n p
  have hco : s.Coprime t := Nat.Coprime.pow_left _ (Nat.coprime_ordCompl hp hn0)
  have hs1 : 1 < s := Nat.one_lt_pow (hp.factorization_pos_of_dvd hn0 hp_dvd).ne' hp.one_lt
  have ht_pos : 0 < t := Nat.ordCompl_pos p hn0
  have ht_lt : t < n := by
    rw [← hst]
    calc t = 1 * t := (one_mul t).symm
      _ < s * t := Nat.mul_lt_mul_of_lt_of_le hs1 le_rfl ht_pos
  exact ⟨p, l, s, t, hp, hpmax, rfl, rfl, rfl, hst, hco, hs1, ht_lt⟩

private lemma card_inf_mul_card_map {G : Type*} [Group G] [Finite G]
    (P H : Subgroup G) [P.Normal] :
    Nat.card (H ⊓ P : Subgroup G) * Nat.card (H.map (QuotientGroup.mk' P)) = Nat.card H := by
  let φ : H →* H.map (QuotientGroup.mk' P) := (QuotientGroup.mk' P).subgroupMap H
  have h1 : Nat.card H = Nat.card (H ⧸ φ.ker) * Nat.card φ.ker :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup φ.ker
  have hq : Nat.card (H ⧸ φ.ker) = Nat.card (H.map (QuotientGroup.mk' P)) :=
    Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective φ (MonoidHom.subgroupMap_surjective _ H)).toEquiv
  have hk : Nat.card φ.ker = Nat.card (H ⊓ P : Subgroup G) := by
    rw [Subgroup.ker_subgroupMap, QuotientGroup.ker_mk']
    have heq : (P.subgroupOf H : Subgroup H) ≃* (H ⊓ P : Subgroup G) := {
      toFun := fun x => ⟨x.1.1, x.1.2, x.2⟩
      invFun := fun y => ⟨⟨y.1, y.2.1⟩, y.2.2⟩
      left_inv := fun ⟨⟨_, _⟩, _⟩ => rfl
      right_inv := fun ⟨_, ⟨_, _⟩⟩ => rfl
      map_mul' := fun _ _ => rfl
    }
    exact Nat.card_congr heq.toEquiv
  rw [h1, hq, hk, mul_comm]

private lemma ncard_coset_inter_fiber_ge {G : Type*} [Group G] [Finite G]
    (P H : Subgroup G) [P.Normal] (g : G) (b : G ⧸ P)
    (hb : b ∈ (QuotientGroup.mk g : G ⧸ P) • ((H.map (QuotientGroup.mk' P) : Subgroup (G ⧸ P)) : Set (G ⧸ P))) :
    Nat.card (H ⊓ P : Subgroup G) ≤ ((g • (H : Set G)) ∩ ((QuotientGroup.mk' P) ⁻¹' {b})).ncard := by
  rw [mem_leftCoset_iff, SetLike.mem_coe, Subgroup.mem_map] at hb
  obtain ⟨h, hh, hbh⟩ := hb
  have hmk_g : QuotientGroup.mk g = (QuotientGroup.mk' P) g := rfl
  let y : G := g * h
  have hy_coset : y ∈ g • (H : Set G) := ⟨h, hh, rfl⟩
  have hy_fib : (QuotientGroup.mk' P) y = b := by
    change (QuotientGroup.mk' P) (g * h) = b
    rw [map_mul]
    have : (QuotientGroup.mk' P) h = ((QuotientGroup.mk g : G ⧸ P))⁻¹ * b := hbh
    rw [← hmk_g, this]
    group
  have hsub : y • ((H ⊓ P : Subgroup G) : Set G) ⊆ (g • (H : Set G)) ∩ ((QuotientGroup.mk' P) ⁻¹' {b}) := by
    intro z hz
    rw [Set.mem_smul_set] at hz
    obtain ⟨w, hw, rfl⟩ := hz
    refine ⟨?_, ?_⟩
    · exact mul_mem_smul_coset hy_coset hw.1
    · change (QuotientGroup.mk' P) (y * w) = b
      rw [map_mul, hy_fib]
      have hw1 : (QuotientGroup.mk' P) w = 1 := (QuotientGroup.eq_one_iff w).mpr hw.2
      rw [hw1, mul_one]
  have hnc : (y • ((H ⊓ P : Subgroup G) : Set G)).ncard = Nat.card (H ⊓ P : Subgroup G) :=
    ncard_smul_coset y (H ⊓ P)
  rw [← hnc]
  exact Set.ncard_le_ncard hsub (Set.toFinite _)

private lemma sum_totient_le_ncard_iUnion_nilpotent :
    ∀ (n : ℕ) (G : Type) [Group G] [Finite G] [Group.IsNilpotent G], Nat.card G = n →
      ∀ (κ : Type) [Fintype κ] [Nonempty κ] (g : κ → G) (H : κ → Subgroup G),
      ∑ d ∈ Finset.univ.biUnion (fun j => (Nat.card (H j)).divisors), d.totient ≤
        (⋃ j, g j • (H j : Set G)).ncard := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro G _ _ _ hn κ _ _ g H
    classical
    have hnpos : 0 < n := hn ▸ Nat.card_pos
    rcases Nat.lt_or_ge n 2 with hn1 | hn2
    · have hHj : ∀ j : κ, Nat.card (H j) = 1 := fun j => by
        have h1 : Nat.card (H j) ∣ n := hn ▸ Subgroup.card_subgroup_dvd_card (H j)
        have h2 : 0 < Nat.card (H j) := Nat.card_pos
        have h3 := Nat.le_of_dvd hnpos h1
        omega
      have hD : Finset.univ.biUnion (fun j => (Nat.card (H j)).divisors) = {1} := by
        ext d; simp [hHj, Nat.divisors_one]
      rw [hD, Finset.sum_singleton, Nat.totient_one]
      obtain ⟨j0⟩ := ‹Nonempty κ›
      exact (Set.ncard_pos (Set.toFinite _)).mpr ⟨g j0, Set.mem_iUnion.mpr ⟨j0, ⟨1, (H j0).one_mem, mul_one _⟩⟩⟩
    · obtain ⟨p, l, s, t, hp, _, hl, hs, ht, hst, hco, hs1, ht_lt⟩ := exists_largest_prime_split hn2
      have : Fact p.Prime := ⟨hp⟩
      let Psyl : Sylow p G := default
      let P : Subgroup G := (Psyl : Subgroup G)
      have : P.Normal := inferInstance
      have hcardP : Nat.card P = s := by
        calc Nat.card P = p ^ Nat.factorization (Nat.card G) p := Psyl.card_eq_multiplicity
          _ = p ^ n.factorization p := by rw [hn]
          _ = p ^ l := by rw [hl]
          _ = s := hs.symm
      have hcardGP : Nat.card (G ⧸ P) = t := by
        have hmul := Subgroup.card_eq_card_quotient_mul_card_subgroup P
        rw [hn, hcardP, ← hst] at hmul
        have hs0 : 0 < s := by omega
        exact Nat.mul_right_cancel hs0 (hmul.symm.trans (mul_comm s t))
      have hsplitH : ∀ j : κ, Nat.card (H j) =
          Nat.card (H j ⊓ P : Subgroup G) * Nat.card ((H j).map (QuotientGroup.mk' P)) :=
        fun j => (card_inf_mul_card_map P (H j)).symm
      have ha_dvd : ∀ j : κ, Nat.card (H j ⊓ P : Subgroup G) ∣ p ^ l := fun j => by
        have := Subgroup.card_dvd_of_le (inf_le_right : H j ⊓ P ≤ P)
        rwa [hcardP, hs] at this
      choose a ha_le ha_eq using fun j => (Nat.dvd_prime_pow hp).mp (ha_dvd j)
      let m : κ → ℕ := fun j => Nat.card ((H j).map (QuotientGroup.mk' P))
      have hm_dvd : ∀ j : κ, m j ∣ t := fun j => by
        have := Subgroup.card_subgroup_dvd_card ((H j).map (QuotientGroup.mk' P))
        rwa [hcardGP] at this
      have hm0 : ∀ j : κ, 0 < m j := fun _ => Nat.card_pos
      have hm_not_dvd : ∀ j : κ, ¬ p ∣ m j := fun j hdvd => by
        have : p ∣ t := hdvd.trans (hm_dvd j)
        rw [ht] at this
        exact Nat.not_dvd_ordCompl hp hnpos.ne' this
      let U : Set G := ⋃ j, g j • (H j : Set G)
      let : Fintype (G ⧸ P) := Fintype.ofFinite _
      have hU_fiber : ∑ b : G ⧸ P, (U ∩ ((QuotientGroup.mk' P) ⁻¹' {b})).ncard ≤ U.ncard := by
        have hdisj : (Set.univ : Set (G ⧸ P)).PairwiseDisjoint
            (fun b => U ∩ ((QuotientGroup.mk' P) ⁻¹' {b})) := by
          rintro b1 - b2 - hb12
          refine Set.disjoint_left.mpr fun {x} hx1 hx2 => hb12 ?_
          exact hx1.2.symm.trans hx2.2
        have hunion : (⋃ b : G ⧸ P, U ∩ ((QuotientGroup.mk' P) ⁻¹' {b})) = U := by
          ext x; simp
        have hU_eq : U.ncard = (⋃ b : G ⧸ P, U ∩ ((QuotientGroup.mk' P) ⁻¹' {b})).ncard :=
          congrArg Set.ncard hunion.symm
        rw [hU_eq, Set.ncard_iUnion_of_finite (fun _ => Set.toFinite _) (Set.pairwise_univ.mp hdisj),
          finsum_eq_sum_of_fintype]
      let g' : κ → G ⧸ P := fun j => QuotientGroup.mk (g j)
      let H' : κ → Subgroup (G ⧸ P) := fun j => (H j).map (QuotientGroup.mk' P)
      have hU_fiber_ge : ∀ b : G ⧸ P, ∀ c ≤ l,
          (∃ j : κ, c ≤ a j ∧ b ∈ g' j • (H' j : Set (G ⧸ P))) →
          p ^ c ≤ (U ∩ ((QuotientGroup.mk' P) ⁻¹' {b})).ncard := by
        rintro b c - ⟨j, hcj, hbj⟩
        have h1 : p ^ c ≤ p ^ a j := Nat.pow_le_pow_right hp.pos hcj
        have h2 : p ^ a j ≤ ((g j • (H j : Set G)) ∩ ((QuotientGroup.mk' P) ⁻¹' {b})).ncard := by
          rw [← ha_eq j]
          exact ncard_coset_inter_fiber_ge P (H j) (g j) b hbj
        have h3 : ((g j • (H j : Set G)) ∩ ((QuotientGroup.mk' P) ⁻¹' {b})).ncard ≤
            (U ∩ ((QuotientGroup.mk' P) ⁻¹' {b})).ncard := by
          refine Set.ncard_le_ncard ?_ (Set.toFinite _)
          exact Set.inter_subset_inter_left _ (Set.subset_iUnion (fun k => g k • (H k : Set G)) j)
        exact le_trans h1 (le_trans h2 h3)
      -- Layer decomposition over exponents c ∈ range (l + 1):
      -- For each b ∈ G ⧸ P, let A(b) = sup of a j over j hitting b (if nonempty).
      have hlayer : ∀ b : G ⧸ P,
          ∑ c ∈ Finset.range (l + 1), (if ∃ j : κ, c ≤ a j ∧ b ∈ g' j • (H' j : Set (G ⧸ P))
            then (p ^ c).totient else 0) ≤ (U ∩ ((QuotientGroup.mk' P) ⁻¹' {b})).ncard := by
        intro b
        by_cases hne : ∃ j : κ, b ∈ g' j • (H' j : Set (G ⧸ P))
        · let S_b := Finset.univ.filter fun j : κ => b ∈ g' j • (H' j : Set (G ⧸ P))
          have hS_b : S_b.Nonempty := by
            obtain ⟨j, hj⟩ := hne
            exact ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ j, hj⟩⟩
          let A_b := S_b.sup a
          have hA_b_le : A_b ≤ l := Finset.sup_le fun j _ => ha_le j
          obtain ⟨j_max, hj_max_mem, hj_max_eq⟩ := Finset.exists_mem_eq_sup S_b hS_b a
          have hmax_cond : ∃ j : κ, A_b ≤ a j ∧ b ∈ g' j • (H' j : Set (G ⧸ P)) :=
            ⟨j_max, le_of_eq hj_max_eq, (Finset.mem_filter.mp hj_max_mem).2⟩
          have hsum_le : ∑ c ∈ Finset.range (l + 1),
              (if ∃ j : κ, c ≤ a j ∧ b ∈ g' j • (H' j : Set (G ⧸ P)) then (p ^ c).totient else 0) ≤
              ∑ c ∈ Finset.range (A_b + 1), (p ^ c).totient := by
            have hle_iff : ∀ c, (∃ j : κ, c ≤ a j ∧ b ∈ g' j • (H' j : Set (G ⧸ P))) → c ≤ A_b := by
              rintro c ⟨j, hcj, hbj⟩
              exact le_trans hcj (Finset.le_sup (Finset.mem_filter.mpr ⟨Finset.mem_univ j, hbj⟩))
            calc ∑ c ∈ Finset.range (l + 1),
                  (if ∃ j : κ, c ≤ a j ∧ b ∈ g' j • (H' j : Set (G ⧸ P)) then (p ^ c).totient else 0)
                ≤ ∑ c ∈ Finset.range (l + 1), (if c ≤ A_b then (p ^ c).totient else 0) := by
                    refine Finset.sum_le_sum fun c _ => ?_
                    split_ifs with h1 h2 h2
                    · exact le_rfl
                    · exact absurd (hle_iff c h1) h2
                    · exact Nat.zero_le _
                    · exact le_rfl
              _ = ∑ c ∈ Finset.range (A_b + 1), (p ^ c).totient := by
                    rw [← Finset.sum_filter]
                    congr 1
                    ext c
                    simp only [Finset.mem_filter, Finset.mem_range]
                    omega
          have htot_sum : ∑ c ∈ Finset.range (A_b + 1), (p ^ c).totient = p ^ A_b := by
            have := Nat.sum_totient (p ^ A_b)
            rwa [Nat.divisors_prime_pow hp, Finset.sum_map] at this
          rw [htot_sum] at hsum_le
          exact le_trans hsum_le (hU_fiber_ge b A_b hA_b_le hmax_cond)
        · have hzero : ∑ c ∈ Finset.range (l + 1),
              (if ∃ j : κ, c ≤ a j ∧ b ∈ g' j • (H' j : Set (G ⧸ P)) then (p ^ c).totient else 0) = 0 := by
            refine Finset.sum_eq_zero fun c _ => ?_
            rw [if_neg]
            rintro ⟨j, -, hj⟩
            exact hne ⟨j, hj⟩
          rw [hzero]
          exact Nat.zero_le _
      have htot_eq : ∀ d' ∈ Finset.univ.biUnion (fun j => (m j).divisors),
          d'.totient * p ^ ((Finset.univ.filter fun j => d' ∣ m j).sup a) =
          ∑ c ∈ Finset.range (l + 1),
            if d' ∈ (Finset.univ.filter fun j => c ≤ a j).biUnion (fun j => (m j).divisors)
            then (p ^ c).totient * d'.totient else 0 := by
        intro d' hd'
        set A_d := (Finset.univ.filter fun j => d' ∣ m j).sup a
        have hA_d_le : A_d ≤ l := Finset.sup_le fun j _ => ha_le j
        have hmem_iff : ∀ c, d' ∈ (Finset.univ.filter fun j => c ≤ a j).biUnion (fun j => (m j).divisors) ↔ c ≤ A_d := by
          intro c
          constructor
          · intro hc
            obtain ⟨j, hjf, hjd⟩ := Finset.mem_biUnion.mp hc
            have hcj : c ≤ a j := (Finset.mem_filter.mp hjf).2
            have hd'm : d' ∣ m j := (Nat.mem_divisors.mp hjd).1
            exact le_trans hcj (Finset.le_sup (Finset.mem_filter.mpr ⟨Finset.mem_univ j, hd'm⟩))
          · intro hc
            have hfilt_ne : (Finset.univ.filter fun j => d' ∣ m j).Nonempty := by
              obtain ⟨j, -, hjd⟩ := Finset.mem_biUnion.mp hd'
              exact ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ j, (Nat.mem_divisors.mp hjd).1⟩⟩
            obtain ⟨j, hjf, hj_eq⟩ := Finset.exists_mem_eq_sup _ hfilt_ne a
            refine Finset.mem_biUnion.mpr ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ j, ?_⟩, ?_⟩
            · exact hj_eq ▸ hc
            · exact Nat.mem_divisors.mpr ⟨(Finset.mem_filter.mp hjf).2, (hm0 j).ne'⟩
        have hsum_A : ∑ c ∈ Finset.range (l + 1),
            (if d' ∈ (Finset.univ.filter fun j => c ≤ a j).biUnion (fun j => (m j).divisors)
              then (p ^ c).totient * d'.totient else 0) =
            ∑ c ∈ Finset.range (A_d + 1), (p ^ c).totient * d'.totient := by
          have h1 : ∀ c ∈ Finset.range (l + 1),
              (if d' ∈ (Finset.univ.filter fun j => c ≤ a j).biUnion (fun j => (m j).divisors)
                then (p ^ c).totient * d'.totient else 0) =
              (if c ≤ A_d then (p ^ c).totient * d'.totient else 0) := fun c _ => by
            simp [hmem_iff c]
          rw [Finset.sum_congr rfl h1, ← Finset.sum_filter]
          congr 1
          ext c
          simp only [Finset.mem_filter, Finset.mem_range]
          omega
        rw [hsum_A, ← Finset.sum_mul, mul_comm d'.totient]
        congr 1
        have hst_tot := (Nat.sum_totient (p ^ A_d)).symm
        simp only [Nat.divisors_prime_pow hp, Finset.sum_map, Function.Embedding.coeFn_mk] at hst_tot
        exact hst_tot
      -- Now apply IH on G ⧸ P for each c ∈ range (l + 1)!
      have hIH_c : ∀ c ∈ Finset.range (l + 1),
          ∑ d' ∈ (Finset.univ.filter fun j => c ≤ a j).biUnion (fun j => (m j).divisors), d'.totient ≤
          (Finset.univ.filter fun b : G ⧸ P => ∃ j : κ, c ≤ a j ∧ b ∈ g' j • (H' j : Set (G ⧸ P))).card := by
        intro c hc
        let κ_c := {j : κ // c ≤ a j}
        by_cases hκc : Nonempty κ_c
        · let : Nonempty κ_c := hκc
          have hih := ih t ht_lt (G ⧸ P) hcardGP κ_c (fun j => g' j.1) (fun j => H' j.1)
          have hD_eq : Finset.univ.biUnion (fun j : κ_c => (Nat.card (H' j.1)).divisors) =
              (Finset.univ.filter fun j => c ≤ a j).biUnion (fun j => (m j).divisors) := by
            ext d'
            simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_filter]
            exact ⟨fun ⟨j, hjd⟩ => ⟨j.1, j.2, hjd⟩, fun ⟨j, hjc, hjd⟩ => ⟨⟨j, hjc⟩, hjd⟩⟩
          have hU_eq : (⋃ j : κ_c, g' j.1 • (H' j.1 : Set (G ⧸ P))).ncard =
              (Finset.univ.filter fun b : G ⧸ P => ∃ j : κ, c ≤ a j ∧ b ∈ g' j • (H' j : Set (G ⧸ P))).card := by
            rw [← Set.ncard_coe_finset]
            congr 1
            ext b
            simp only [Set.mem_iUnion, Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and]
            exact ⟨fun ⟨j, hjb⟩ => ⟨j.1, j.2, hjb⟩, fun ⟨j, hjc, hjb⟩ => ⟨⟨j, hjc⟩, hjb⟩⟩
          rwa [hD_eq, hU_eq] at hih
        · rw [not_nonempty_iff] at hκc
          have hempty : (Finset.univ.filter fun j => c ≤ a j) = ∅ := by
            ext j; simp only [Finset.notMem_empty, Finset.mem_filter, Finset.mem_univ, true_and, iff_false]
            intro hcj; exact hκc.false ⟨j, hcj⟩
          rw [hempty, Finset.biUnion_empty, Finset.sum_empty]
          exact Nat.zero_le _
      -- Combine everything!
      have hstep1 : ∑ d ∈ Finset.univ.biUnion (fun j => (Nat.card (H j)).divisors), d.totient =
          ∑ d ∈ Finset.univ.biUnion (fun j => (m j * p ^ a j).divisors), d.totient := by
        congr 1; ext d; simp only [Finset.mem_biUnion, Finset.mem_univ, true_and]
        exact exists_congr fun j => by rw [hsplitH j, ha_eq j, mul_comm]
      have hstep2 := sum_totient_biUnion_le hp m a hm_not_dvd hm0
      have hstep3 : ∑ d' ∈ Finset.univ.biUnion (fun j => (m j).divisors),
          d'.totient * p ^ ((Finset.univ.filter fun j => d' ∣ m j).sup a) =
          ∑ c ∈ Finset.range (l + 1), (p ^ c).totient *
            ∑ d' ∈ (Finset.univ.filter fun j => c ≤ a j).biUnion (fun j => (m j).divisors), d'.totient := by
        rw [Finset.sum_congr rfl htot_eq, Finset.sum_comm]
        refine Finset.sum_congr rfl fun c _ => ?_
        have hsub : (Finset.univ.filter fun j => c ≤ a j).biUnion (fun j => (m j).divisors) ⊆
            Finset.univ.biUnion (fun j => (m j).divisors) := by
          intro d' hd'
          obtain ⟨j, _, hjd⟩ := Finset.mem_biUnion.mp hd'
          exact Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ j, hjd⟩
        rw [Finset.mul_sum, Finset.sum_ite_mem, Finset.inter_eq_right.mpr hsub]
      have hstep4 : ∑ c ∈ Finset.range (l + 1), (p ^ c).totient *
            ∑ d' ∈ (Finset.univ.filter fun j => c ≤ a j).biUnion (fun j => (m j).divisors), d'.totient ≤
          ∑ c ∈ Finset.range (l + 1), (p ^ c).totient *
            (Finset.univ.filter fun b : G ⧸ P => ∃ j : κ, c ≤ a j ∧ b ∈ g' j • (H' j : Set (G ⧸ P))).card :=
        Finset.sum_le_sum fun c hc => Nat.mul_le_mul_left _ (hIH_c c hc)
      have hstep5 : ∑ c ∈ Finset.range (l + 1), (p ^ c).totient *
            (Finset.univ.filter fun b : G ⧸ P => ∃ j : κ, c ≤ a j ∧ b ∈ g' j • (H' j : Set (G ⧸ P))).card =
          ∑ b : G ⧸ P, ∑ c ∈ Finset.range (l + 1),
            (if ∃ j : κ, c ≤ a j ∧ b ∈ g' j • (H' j : Set (G ⧸ P)) then (p ^ c).totient else 0) := by
        have hterm : ∀ c ∈ Finset.range (l + 1), (p ^ c).totient *
            (Finset.univ.filter fun b : G ⧸ P => ∃ j : κ, c ≤ a j ∧ b ∈ g' j • (H' j : Set (G ⧸ P))).card =
            ∑ b : G ⧸ P, if ∃ j : κ, c ≤ a j ∧ b ∈ g' j • (H' j : Set (G ⧸ P)) then (p ^ c).totient else 0 := by
          intro c _
          rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, smul_eq_mul, mul_comm]
        rw [Finset.sum_congr rfl hterm, Finset.sum_comm]
      have hstep6 : ∑ b : G ⧸ P, ∑ c ∈ Finset.range (l + 1),
            (if ∃ j : κ, c ≤ a j ∧ b ∈ g' j • (H' j : Set (G ⧸ P)) then (p ^ c).totient else 0) ≤
          ∑ b : G ⧸ P, (U ∩ ((QuotientGroup.mk' P) ⁻¹' {b})).ncard :=
        Finset.sum_le_sum fun b _ => hlayer b
      calc ∑ d ∈ Finset.univ.biUnion (fun j => (Nat.card (H j)).divisors), d.totient
          = ∑ d ∈ Finset.univ.biUnion (fun j => (m j * p ^ a j).divisors), d.totient := hstep1
        _ ≤ ∑ d' ∈ Finset.univ.biUnion (fun j => (m j).divisors),
            d'.totient * p ^ ((Finset.univ.filter fun j => d' ∣ m j).sup a) := hstep2
        _ = ∑ c ∈ Finset.range (l + 1), (p ^ c).totient *
            ∑ d' ∈ (Finset.univ.filter fun j => c ≤ a j).biUnion (fun j => (m j).divisors), d'.totient := hstep3
        _ ≤ ∑ c ∈ Finset.range (l + 1), (p ^ c).totient *
            (Finset.univ.filter fun b : G ⧸ P => ∃ j : κ, c ≤ a j ∧ b ∈ g' j • (H' j : Set (G ⧸ P))).card := hstep4
        _ = ∑ b : G ⧸ P, ∑ c ∈ Finset.range (l + 1),
            (if ∃ j : κ, c ≤ a j ∧ b ∈ g' j • (H' j : Set (G ⧸ P)) then (p ^ c).totient else 0) := hstep5
        _ ≤ ∑ b : G ⧸ P, (U ∩ ((QuotientGroup.mk' P) ⁻¹' {b})).ncard := hstep6
        _ ≤ U.ncard := hU_fiber

private lemma hs_nilpotent_aux :
    ∀ (n : ℕ) (G : Type) [Group G] [Finite G] [Group.IsNilpotent G], Nat.card G = n →
      ∀ (k : ℕ), 1 < k → ∀ (C : Erdos274.Group.ExactCovering G (Fin k)),
      ∃ i j : Fin k, i ≠ j ∧ Nat.card (C.parts i) = Nat.card (C.parts j) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro G _ _ _ hn k hk C
    classical
    by_contra hcon
    push Not at hcon
    have hinj : Function.Injective fun j : Fin k => Nat.card (C.parts j) := fun i j hij =>
      by_contra fun hne => hcon i j hne hij
    have hnpos : 0 < n := hn ▸ Nat.card_pos
    let : Nontrivial (Fin k) := Fintype.one_lt_card_iff_nontrivial.mp (by rw [Fintype.card_fin]; exact hk)
    obtain ⟨i0, j0, hij0⟩ := exists_pair_ne (Fin k)
    have hn2 : 2 ≤ n := by
      by_contra h
      have hone : Nat.card G = 1 := by omega
      let := (Nat.card_eq_one_iff_unique.mp hone).1
      have h1 : C.reps i0 ∈ C.reps i0 • (C.parts i0 : Set G) := ⟨1, (C.parts i0).one_mem, mul_one _⟩
      have h2 : C.reps i0 ∈ C.reps j0 • (C.parts j0 : Set G) := ⟨1, (C.parts j0).one_mem, Subsingleton.elim _ _⟩
      exact Set.disjoint_left.mp (C.disjoint (Set.mem_univ i0) (Set.mem_univ j0) hij0) h1 h2
    obtain ⟨p, l, s, t, hp, hpmax, hl, hs, ht, hst, _, hs1, ht_lt⟩ := exists_largest_prime_split hn2
    have : Fact p.Prime := ⟨hp⟩
    let Psyl : Sylow p G := default
    let P : Subgroup G := (Psyl : Subgroup G)
    have : P.Normal := inferInstance
    have hcardP : Nat.card P = s := by
      calc Nat.card P = p ^ Nat.factorization (Nat.card G) p := Psyl.card_eq_multiplicity
        _ = p ^ n.factorization p := by rw [hn]
        _ = p ^ l := by rw [hl]
        _ = s := hs.symm
    have hcardGP : Nat.card (G ⧸ P) = t := by
      have hmul := Subgroup.card_eq_card_quotient_mul_card_subgroup P
      rw [hn, hcardP, ← hst] at hmul
      have hs0 : 0 < s := by omega
      exact Nat.mul_right_cancel hs0 (hmul.symm.trans (mul_comm s t))
    have hsplitj : ∀ j : Fin k, Nat.card (C.parts j ⊓ P : Subgroup G) *
        Nat.card ((C.parts j).map (QuotientGroup.mk' P)) = Nat.card (C.parts j) :=
      fun j => card_inf_mul_card_map P (C.parts j)
    have h𝔞_dvd : ∀ j : Fin k, Nat.card (C.parts j ⊓ P : Subgroup G) ∣ p ^ l := fun j => by
      have h := Subgroup.card_dvd_of_le (inf_le_right : C.parts j ⊓ P ≤ P)
      rwa [← hs, ← hcardP]
    choose a ha_le ha_eq using fun j => (Nat.dvd_prime_pow hp).mp (h𝔞_dvd j)
    let m : Fin k → ℕ := fun j => Nat.card ((C.parts j).map (QuotientGroup.mk' P))
    have hm_dvd : ∀ j : Fin k, m j ∣ t := fun j => by
      have := Subgroup.card_subgroup_dvd_card ((C.parts j).map (QuotientGroup.mk' P))
      rwa [hcardGP] at this
    have hm_pos : ∀ j : Fin k, 0 < m j := fun _ => Nat.card_pos
    have hm_fac : ∀ j : Fin k, ∀ q ∈ (m j).primeFactors, q ≤ p - 1 := fun j q hq => by
      have hqp : q.Prime := Nat.prime_of_mem_primeFactors hq
      obtain ⟨-, hq_dvd, -⟩ := Nat.mem_primeFactors.mp hq
      have hqt : q ∣ t := hq_dvd.trans (hm_dvd j)
      have htn : t ∣ n := by rw [ht]; exact Nat.ordCompl_dvd n p
      have hqn : q ∈ n.primeFactors := Nat.mem_primeFactors.mpr ⟨hqp, hqt.trans htn, hnpos.ne'⟩
      have hqne : q ≠ p := by rintro rfl; rw [ht] at hqt; exact Nat.not_dvd_ordCompl hp hnpos.ne' hqt
      have := hpmax q hqn
      omega
    have hfull_iff : ∀ j : Fin k, P ≤ C.parts j ↔ Nat.card (C.parts j ⊓ P : Subgroup G) = s := by
      intro j
      constructor
      · intro hle
        have : C.parts j ⊓ P = P := inf_eq_right.mpr hle
        rw [this, hcardP]
      · intro heq
        have h1 : (C.parts j ⊓ P : Subgroup G) = P :=
          Subgroup.eq_of_le_of_card_ge inf_le_right (by rw [hcardP, ← heq])
        rw [← h1]
        exact inf_le_left
    set 𝒯 : Finset (Fin k) := Finset.univ.filter fun j => ¬ P ≤ C.parts j
    rcases 𝒯.eq_empty_or_nonempty with h𝒯 | h𝒯
    · have hfull : ∀ j : Fin k, P ≤ C.parts j := fun j => by
        by_contra h
        exact absurd (h𝒯 ▸ Finset.mem_filter.mpr ⟨Finset.mem_univ j, h⟩) (Finset.notMem_empty j)
      obtain ⟨Q, hQparts, -⟩ := quotient_covering_exists C P hfull
      obtain ⟨i, j, hij, hcards⟩ := ih t ht_lt (G ⧸ P) hcardGP k hk Q
      refine absurd (hinj ?_) hij
      have hmi : m i = m j := by simpa [m, hQparts i, hQparts j] using hcards
      calc Nat.card (C.parts i) = Nat.card (C.parts i ⊓ P : Subgroup G) * m i := (hsplitj i).symm
        _ = s * m i := by rw [(hfull_iff i).mp (hfull i)]
        _ = s * m j := by rw [hmi]
        _ = Nat.card (C.parts j ⊓ P : Subgroup G) * m j := by rw [(hfull_iff j).mp (hfull j)]
        _ = Nat.card (C.parts j) := hsplitj j
    · obtain ⟨j1, hj1⟩ := h𝒯
      have ha_lt : ∀ j ∈ 𝒯, a j < l := fun j hj => by
        have hnfull : ¬ P ≤ C.parts j := (Finset.mem_filter.mp hj).2
        rcases Nat.lt_or_ge (a j) l with h | h
        · exact h
        · exact absurd ((hfull_iff j).mpr (by rw [ha_eq j, le_antisymm (ha_le j) h, ← hs])) hnfull
      set U₁ : Set G := ⋃ j : {j : Fin k // j ∈ 𝒯}, C.reps j.1 • (C.parts j.1 : Set G)
      have hsat : ∀ x ∈ U₁, ∀ y : G,
          (QuotientGroup.mk y : G ⧸ P) = QuotientGroup.mk x → y ∈ U₁ := by
        intro x hx y hxy
        have hy : y ∈ ⋃ j, C.reps j • (C.parts j : Set G) := C.covers ▸ Set.mem_univ y
        obtain ⟨r, hr⟩ := Set.mem_iUnion.mp hy
        obtain ⟨⟨j, hj⟩, hxj⟩ := Set.mem_iUnion.mp hx
        by_cases hfr : P ≤ C.parts r
        · exfalso
          have h1 : y⁻¹ * x ∈ P := QuotientGroup.eq.mp hxy
          have h2 : x ∈ C.reps r • (C.parts r : Set G) := by
            simpa using mul_mem_smul_coset hr (hfr h1)
          have hjr : j = r := by
            by_contra hne
            exact Set.disjoint_left.mp (C.disjoint (Set.mem_univ j) (Set.mem_univ r) hne) hxj h2
          exact (Finset.mem_filter.mp hj).2 (hjr ▸ hfr)
        · exact Set.mem_iUnion.mpr ⟨⟨r, Finset.mem_filter.mpr ⟨Finset.mem_univ r, hfr⟩⟩, hr⟩
      set B₁ : Set (G ⧸ P) := QuotientGroup.mk '' U₁
      let : Fintype G := Fintype.ofFinite _
      let : Fintype (G ⧸ P) := Fintype.ofFinite _
      have h4 : U₁.ncard = s * B₁.ncard := by
        have hdisj_b : (Set.univ : Set (G ⧸ P)).PairwiseDisjoint
            (fun b => U₁ ∩ ((QuotientGroup.mk' P) ⁻¹' {b})) := by
          rintro b1 - b2 - hb12
          refine Set.disjoint_left.mpr fun {x} hx1 hx2 => hb12 ?_
          exact hx1.2.symm.trans hx2.2
        have hunion : (⋃ b : G ⧸ P, U₁ ∩ ((QuotientGroup.mk' P) ⁻¹' {b})) = U₁ := by
          ext y; simp
        have hfib_in : ∀ b ∈ B₁, (U₁ ∩ ((QuotientGroup.mk' P) ⁻¹' {b})).ncard = s := by
          intro b hb
          have heq_inter : U₁ ∩ ((QuotientGroup.mk' P) ⁻¹' {b}) = (QuotientGroup.mk' P) ⁻¹' {b} := by
            ext y
            simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff, and_iff_right_iff_imp]
            intro hy
            obtain ⟨x, hx, rfl⟩ := hb
            exact hsat x hx y hy
          obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective b
          have heq_coset : (QuotientGroup.mk' P) ⁻¹' {QuotientGroup.mk x} = x • (P : Set G) := by
            ext y
            rw [Set.mem_preimage, Set.mem_singleton_iff, mem_leftCoset_iff, SetLike.mem_coe]
            change (QuotientGroup.mk y : G ⧸ P) = QuotientGroup.mk x ↔ x⁻¹ * y ∈ P
            rw [eq_comm, QuotientGroup.eq]
          rw [heq_inter, heq_coset, ncard_smul_coset, hcardP]
        have hfib_out : ∀ b : G ⧸ P, b ∉ B₁ → (U₁ ∩ ((QuotientGroup.mk' P) ⁻¹' {b})).ncard = 0 := by
          intro b hb
          have hempty : U₁ ∩ ((QuotientGroup.mk' P) ⁻¹' {b}) = ∅ := by
            ext y
            simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff,
              Set.mem_empty_iff_false, iff_false, not_and]
            intro hy hby
            exact hb ⟨y, hy, hby⟩
          rw [hempty, Set.ncard_empty]
        have hBcard : (Finset.univ.filter (· ∈ B₁)).card = B₁.ncard := by
          rw [← Set.ncard_coe_finset]
          congr 1; ext b; simp
        calc U₁.ncard
            = (⋃ b : G ⧸ P, U₁ ∩ ((QuotientGroup.mk' P) ⁻¹' {b})).ncard :=
                congrArg Set.ncard hunion.symm
          _ = ∑ b : G ⧸ P, (U₁ ∩ ((QuotientGroup.mk' P) ⁻¹' {b})).ncard := by
                rw [Set.ncard_iUnion_of_finite (fun _ => Set.toFinite _) (Set.pairwise_univ.mp hdisj_b),
                  finsum_eq_sum_of_fintype]
          _ = ∑ b : G ⧸ P, (if b ∈ B₁ then s else 0) := by
                refine Finset.sum_congr rfl fun b _ => ?_
                split_ifs with hb
                · exact hfib_in b hb
                · exact hfib_out b hb
          _ = (Finset.univ.filter (· ∈ B₁)).card * s := by
                rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, smul_eq_mul]
          _ = s * B₁.ncard := by rw [mul_comm, hBcard]
      have hdisj₁ : (Set.univ : Set {j : Fin k // j ∈ 𝒯}).PairwiseDisjoint
          (fun j => C.reps j.1 • (C.parts j.1 : Set G)) := by
        rintro ⟨i, hi⟩ - ⟨j, hj⟩ - hij
        exact C.disjoint (Set.mem_univ i) (Set.mem_univ j) (by simpa using hij)
      have hUsum : U₁.ncard = ∑ j ∈ 𝒯, Nat.card (C.parts j) := by
        rw [Set.ncard_iUnion_of_finite (fun _ => Set.toFinite _) (Set.pairwise_univ.mp hdisj₁),
          finsum_eq_sum_of_fintype, ← Finset.sum_coe_sort 𝒯]
        exact Finset.sum_congr rfl fun j _ => ncard_smul_coset _ _
      have hB₁_eq : B₁ = ⋃ j : {j : Fin k // j ∈ 𝒯},
          (QuotientGroup.mk (C.reps j.1) : G ⧸ P) •
            (((C.parts j.1).map (QuotientGroup.mk' P) : Subgroup (G ⧸ P)) : Set (G ⧸ P)) := by
        dsimp only [B₁, U₁]
        have hmk : (QuotientGroup.mk : G → G ⧸ P) = QuotientGroup.mk' P := rfl
        rw [hmk, Set.image_iUnion]
        refine Set.iUnion_congr fun j => ?_
        rw [Set.image_smul_distrib, Subgroup.coe_map]
      let : Nonempty {j : Fin k // j ∈ 𝒯} := ⟨⟨j1, hj1⟩⟩
      have h6 : ∑ d ∈ 𝒯.biUnion (fun j => (m j).divisors), d.totient ≤ B₁.ncard := by
        have h := sum_totient_le_ncard_iUnion_nilpotent t (G ⧸ P) hcardGP
          {j : Fin k // j ∈ 𝒯}
          (fun j => QuotientGroup.mk (C.reps j.1))
          (fun j => (C.parts j.1).map (QuotientGroup.mk' P))
        have hD_eq : Finset.univ.biUnion (fun j : {j : Fin k // j ∈ 𝒯} => (m j.1).divisors) =
            𝒯.biUnion (fun j => (m j).divisors) := by
          ext d
          simp only [Finset.mem_biUnion, Finset.mem_univ, true_and]
          exact ⟨fun ⟨j, hjd⟩ => ⟨j.1, j.2, hjd⟩, fun ⟨j, hjT, hjd⟩ => ⟨⟨j, hjT⟩, hjd⟩⟩
        change _ ≤ (⋃ j : {j : Fin k // j ∈ 𝒯}, _).ncard at h
        rw [hD_eq] at h
        rwa [hB₁_eq]
      set Φ := ∑ d ∈ 𝒯.biUnion (fun j => (m j).divisors), d.totient
      have hΦ1 : 1 ≤ Φ := by
        have h1D : 1 ∈ 𝒯.biUnion (fun j => (m j).divisors) :=
          Finset.mem_biUnion.mpr ⟨j1, hj1, Nat.one_mem_divisors.mpr (hm_pos j1).ne'⟩
        calc 1 = Nat.totient 1 := Nat.totient_one.symm
          _ ≤ Φ := Finset.single_le_sum (fun _ _ => Nat.zero_le _) h1D
      have h5 : (p - 1) * ∑ j ∈ 𝒯, Nat.card (C.parts j) ≤ (s - 1) * ∑ m' ∈ 𝒯.image m, m' := by
        rw [← Finset.sum_fiberwise_of_maps_to (fun j hj => Finset.mem_image_of_mem m hj)
          (fun j => Nat.card (C.parts j)), Finset.mul_sum, Finset.mul_sum]
        refine Finset.sum_le_sum fun m' hm' => ?_
        have hfib_eq : ∀ j ∈ 𝒯.filter (fun j => m j = m'), Nat.card (C.parts j) = p ^ a j * m' := by
          intro j hj
          obtain ⟨-, hjm⟩ := Finset.mem_filter.mp hj
          rw [← hsplitj j, ha_eq j]
          exact congrArg (p ^ a j * ·) hjm
        rw [Finset.sum_congr rfl hfib_eq, ← Finset.sum_mul]
        have hainj : ∀ x ∈ 𝒯.filter (fun j => m j = m'),
            ∀ y ∈ 𝒯.filter (fun j => m j = m'), a x = a y → x = y := by
          intro x hx y hy hxy
          obtain ⟨-, hxm⟩ := Finset.mem_filter.mp hx
          obtain ⟨-, hym⟩ := Finset.mem_filter.mp hy
          refine hinj ?_
          calc Nat.card (C.parts x) = Nat.card (C.parts x ⊓ P : Subgroup G) * m x := (hsplitj x).symm
            _ = p ^ a x * m x := by rw [ha_eq x]
            _ = p ^ a y * m y := by rw [hxy, hxm, hym]
            _ = Nat.card (C.parts y ⊓ P : Subgroup G) * m y := by rw [← ha_eq y]
            _ = Nat.card (C.parts y) := hsplitj y
        have hsum_a : ∑ j ∈ 𝒯.filter (fun j => m j = m'), p ^ a j =
            ∑ c ∈ (𝒯.filter (fun j => m j = m')).image a, p ^ c := by rw [Finset.sum_image hainj]
        have hgeom : ∑ c ∈ (𝒯.filter (fun j => m j = m')).image a, p ^ c ≤
            ∑ c ∈ Finset.range l, p ^ c := by
          refine Finset.sum_le_sum_of_subset fun c hc => ?_
          obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hc
          exact Finset.mem_range.mpr (ha_lt j (Finset.mem_filter.mp hj).1)
        have hgeom_id : (p - 1) * ∑ c ∈ Finset.range l, p ^ c = s - 1 := by
          rw [hs]
          have h := geom_sum_mul_add (p - 1) l
          rw [Nat.sub_add_cancel (show 1 ≤ p from hp.pos), mul_comm] at h
          omega
        calc (p - 1) * ((∑ j ∈ 𝒯.filter (fun j => m j = m'), p ^ a j) * m')
            = ((p - 1) * ∑ j ∈ 𝒯.filter (fun j => m j = m'), p ^ a j) * m' := by ring
          _ ≤ ((p - 1) * ∑ c ∈ Finset.range l, p ^ c) * m' := by
              refine Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ ?_)
              rw [hsum_a]; exact hgeom
          _ = (s - 1) * m' := by rw [hgeom_id]
      have h7 : ∑ m' ∈ 𝒯.image m, m' ≤ (p - 1) * Φ := by
        have h71 : ∀ m' ∈ 𝒯.image m, m' ≤ (p - 1) * m'.totient := fun m' hm' => by
          obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hm'
          exact le_mul_totient (hm_pos j) (by have := hp.two_le; omega) (hm_fac j)
        have hsub : 𝒯.image m ⊆ 𝒯.biUnion (fun j => (m j).divisors) := fun m' hm' => by
          obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hm'
          exact Finset.mem_biUnion.mpr ⟨j, hj, Nat.mem_divisors.mpr ⟨dvd_rfl, (hm_pos j).ne'⟩⟩
        calc ∑ m' ∈ 𝒯.image m, m' ≤ ∑ m' ∈ 𝒯.image m, (p - 1) * m'.totient := Finset.sum_le_sum h71
          _ = (p - 1) * ∑ m' ∈ 𝒯.image m, m'.totient := by rw [Finset.mul_sum]
          _ ≤ (p - 1) * Φ := Nat.mul_le_mul_left _ (Finset.sum_le_sum_of_subset hsub)
      have hchain : (p - 1) * (s * Φ) ≤ (p - 1) * ((s - 1) * Φ) := by
        calc (p - 1) * (s * Φ) ≤ (p - 1) * (s * B₁.ncard) :=
              Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ h6)
          _ = (p - 1) * U₁.ncard := by rw [h4]
          _ = (p - 1) * ∑ j ∈ 𝒯, Nat.card (C.parts j) := by rw [hUsum]
          _ ≤ (s - 1) * ∑ m' ∈ 𝒯.image m, m' := h5
          _ ≤ (s - 1) * ((p - 1) * Φ) := Nat.mul_le_mul_left _ h7
          _ = (p - 1) * ((s - 1) * Φ) := by ring
      have hp1 : 0 < p - 1 := by have := hp.two_le; omega
      have hfinal : s * Φ ≤ (s - 1) * Φ := Nat.le_of_mul_le_mul_left hchain hp1
      have : s ≤ s - 1 := Nat.le_of_mul_le_mul_right hfinal (by omega)
      omega

private lemma hs_nilpotent {G : Type} [Group G] [Fintype G] [Group.IsNilpotent G]
    {k : ℕ} (hk : 1 < k) (P : Erdos274.Group.ExactCovering G (Fin k)) :
    ∃ i j : Fin k, i ≠ j ∧ (P.parts i).index = (P.parts j).index := by
  obtain ⟨i, j, hij, hcard⟩ := hs_nilpotent_aux (Nat.card G) G rfl k hk P
  refine ⟨i, j, hij, ?_⟩
  have hmuli := Subgroup.card_mul_index (P.parts i)
  have hmulj := Subgroup.card_mul_index (P.parts j)
  have hpos : 0 < Nat.card (P.parts i) := Nat.card_pos
  have heq : Nat.card (P.parts i) * (P.parts i).index =
      Nat.card (P.parts i) * (P.parts j).index := by
    rw [hmuli, ← hmulj, ← hcard]
  exact Nat.mul_left_cancel hpos heq

end ReductionProofs

theorem main : H1 → H2 → type_of% @Erdos274.herzog_schonheim := by
  intro hH1 hH2 G _ _ ι _ hι P
  have hcore_fi : (⨅ i : ι, (P.parts i).normalCore).FiniteIndex := commonCore_finiteIndex P
  have hcore_norm : (⨅ i : ι, (P.parts i).normalCore).Normal := commonCore_normal P
  have hcore_le : ∀ i : ι, (⨅ j : ι, (P.parts j).normalCore) ≤ P.parts i := fun i =>
    (iInf_le (fun j => (P.parts j).normalCore) i).trans (Subgroup.normalCore_le _)
  obtain ⟨Q, hQparts, hQidx⟩ := quotient_covering_exists P _ hcore_le
  have : Fintype (G ⧸ ⨅ i : ι, (P.parts i).normalCore) :=
    @Fintype.ofFinite _ (@Subgroup.finite_quotient_of_finiteIndex _ _ _ hcore_fi)
  obtain ⟨G0, _, _, _, P0, hP0idx, _⟩ := transport_covering_fin Q
  have hcore_ind : ∀ (n : ℕ) (G' : Type) [Group G'] [Fintype G'], Fintype.card G' = n →
      ∀ (k : ℕ), 2 ≤ k → ∀ (P' : Erdos274.Group.ExactCovering G' (Fin k)),
      ∃ i j : Fin k, i ≠ j ∧ (P'.parts i).index = (P'.parts j).index := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro G' _ _ hn k hk P'
      by_cases hnil : Group.IsNilpotent G'
      · exact hs_nilpotent (by omega) P'
      · rcases eq_or_ne k 2 with rfl | hk2'
        · exact hs_card_two P'
        rcases eq_or_ne k 3 with rfl | hk3'
        · exact hs_card_three P'
        rcases eq_or_ne k 4 with rfl | hk4'
        · exact hs_card_four P'
        have hk5 : 5 ≤ k := by omega
        by_cases h2 : ∃ i0 : Fin k, (P'.parts i0).index = 2
        · obtain ⟨i0, hi0⟩ := h2
          obtain ⟨R, hRlt, -, hRback⟩ := index_two_restrict (by omega) P' i0 hi0
          let : Fintype (P'.parts i0) := Fintype.ofFinite _
          have hRlt' : Fintype.card (P'.parts i0) < n := by
            rw [← hn, ← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card (α := G')]
            exact hRlt
          have hk1_ge : 2 ≤ k - 1 := by omega
          obtain ⟨a, b, hab, heq⟩ := ih (Fintype.card (P'.parts i0)) hRlt'
            (P'.parts i0) rfl (k - 1) hk1_ge R
          exact hRback a b hab heq
        · push Not at h2
          have hge3 : ∀ i : Fin k, 3 ≤ (P'.parts i).index := fun i => by
            have := two_le_index_of_one_lt_card (by simpa using (by omega : 1 < k)) P' i
            have := h2 i
            omega
          by_cases hbot : (⨅ i : Fin k, (P'.parts i).normalCore) = ⊥
          · have hsum := sum_inv_index_eq_one P'
            by_cases hsol : Group.IsSolvable G'
            · exact hH1 G' hnil hk5 P' hbot hge3 hsum
            · exact hH2 G' hsol hk5 P' hbot hge3 hsum
          · have hfi' : (⨅ i : Fin k, (P'.parts i).normalCore).FiniteIndex :=
              commonCore_finiteIndex P'
            have hnorm' : (⨅ i : Fin k, (P'.parts i).normalCore).Normal :=
              commonCore_normal P'
            have hle' : ∀ i : Fin k, (⨅ j : Fin k, (P'.parts j).normalCore) ≤ P'.parts i := fun i =>
              (iInf_le (fun j => (P'.parts j).normalCore) i).trans (Subgroup.normalCore_le _)
            obtain ⟨Q', _, hQ'idx⟩ := quotient_covering_exists P' _ hle'
            let N' := ⨅ i : Fin k, (P'.parts i).normalCore
            have : Fintype (G' ⧸ N') :=
              @Fintype.ofFinite _ (@Subgroup.finite_quotient_of_finiteIndex _ _ _ hfi')
            have hcard_lt : Fintype.card (G' ⧸ N') < n := by
              rw [← hn, ← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card]
              have hmul := Subgroup.card_eq_card_quotient_mul_card_subgroup N'
              have hN1 : 1 < Nat.card N' := (Subgroup.one_lt_card_iff_ne_bot N').mpr hbot
              have hqpos : 0 < Nat.card (G' ⧸ N') := Nat.card_pos
              rw [hmul]
              exact lt_mul_of_one_lt_right hqpos hN1
            obtain ⟨a, b, hab, heq⟩ := ih (Fintype.card (G' ⧸ N')) hcard_lt (G' ⧸ N') rfl k (by omega) Q'
            refine ⟨a, b, hab, ?_⟩
            rw [← hQ'idx a, ← hQ'idx b]
            exact heq
  obtain ⟨a, b, hab, heq⟩ := hcore_ind (Fintype.card G0) G0 rfl (Fintype.card ι) (by omega) P0
  let i := (Fintype.equivFin ι).symm a
  let j := (Fintype.equivFin ι).symm b
  refine ⟨i, j, fun h => hab ((Fintype.equivFin ι).symm.injective h), ?_⟩
  rw [← hQidx i, ← hQidx j, ← hP0idx a, ← hP0idx b]
  exact heq

end OMA.R_Erdos274_herzog_schonheim_R1
