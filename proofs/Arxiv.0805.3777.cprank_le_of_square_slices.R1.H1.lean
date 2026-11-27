import OMAReductions.R_Arxiv_0805_3777_cprank_le_of_square_slices_R1
import Mathlib

-- Step Arxiv.0805.3777.cprank_le_of_square_slices.R1.H1: hypothesis H1 of reduction Arxiv.0805.3777.cprank_le_of_square_slices.R1
-- Credit: @ivillar
--
-- REUSE. The section Pencil below (PRank, span_ker, prank_of_noLeft, prank_le: every pencil
-- V -> W is a sum of at most dim W + dim V / 2 rank-one pencils) is taken unchanged from the
-- merged proof proofs/Arxiv.0805.3777.isMaxRank_two.lean of this repository (PR #3391, same
-- owner). The section Regular is new.

/-!
# Regular pencils of square matrices: diagonal up to rank `n / 2`

H1: if some combination `s • A + t • B` of two complex `n × n` matrices is invertible, then
`A = P * diagonal a * Q + ∑ j, α j • u j (v j)ᵀ` and `B = P * diagonal b * Q + ∑ j, β j • u j (v j)ᵀ`
with `P`, `Q` invertible and `n / 2` rank-one matrices `u j (v j)ᵀ`.

Proof.
* `prank_le` (from the maximal rank of `2 × n × n` tensors): the pencil is a sum of at most
  `n + n / 2` rank-one pencils, `A = ∑ l, a l • x l (y l)ᵀ` and `B = ∑ l, b l • x l (y l)ᵀ`.
* Then `s • A + t • B = ∑ l, (s * a l + t * b l) • x l (y l)ᵀ` is invertible. An invertible sum
  `G` of more than `n` rank-one matrices `c l • x l (y l)ᵀ` stays invertible after removing a
  suitable term (`exists_erase`): by the matrix determinant lemma, removing the term `l` keeps `G`
  invertible unless `c l * (y l)ᵀ G⁻¹ (x l) = 1`, and these numbers sum to `trace (G⁻¹ G) = n`,
  which is less than the number of terms. Removing terms one at a time leaves exactly `n` terms
  with an invertible sum (`exists_subsum`); at least `n` terms are needed (`card_ge_of_isUnit`).
* With `P` the matrix of the `n` remaining columns `x l` and `Q` the matrix of the rows `y l`,
  the invertible subsum is `P * diagonal c * Q` (`sum_eq_mul_diag_mul`), so `P` and `Q` are
  invertible, and the same `n` terms of `A` and of `B` are `P * diagonal a * Q` and
  `P * diagonal b * Q`. The at most `n / 2` other terms are the rank-one part (`exists_pad`).
-/

open Module

namespace SqH1

section Pencil

variable {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

/-- The pair `(A, B)` is a sum of at most `r` rank-one pencils. -/
def PRank (r : ℕ) (A B : V →ₗ[ℂ] W) : Prop :=
  ∃ (ι : Type) (_ : Fintype ι) (a b : ι → ℂ) (ψ : ι → V →ₗ[ℂ] ℂ) (u : ι → W),
    Fintype.card ι ≤ r ∧ A = ∑ i, a i • (ψ i).smulRight (u i) ∧
      B = ∑ i, b i • (ψ i).smulRight (u i)

theorem PRank.mono {r r' : ℕ} {A B : V →ₗ[ℂ] W} (h : PRank r A B) (hr : r ≤ r') :
    PRank r' A B := by
  obtain ⟨ι, _, a, b, ψ, u, hc, hA, hB⟩ := h
  exact ⟨ι, _, a, b, ψ, u, hc.trans hr, hA, hB⟩

theorem PRank.comp_right {V' : Type} [AddCommGroup V'] [Module ℂ V'] {r : ℕ}
    {A B : V →ₗ[ℂ] W} (h : PRank r A B) (M : V' →ₗ[ℂ] V) :
    PRank r (A ∘ₗ M) (B ∘ₗ M) := by
  obtain ⟨ι, _, a, b, ψ, u, hc, rfl, rfl⟩ := h
  refine ⟨ι, _, a, b, fun i => ψ i ∘ₗ M, u, hc, ?_, ?_⟩ <;>
  · ext x
    simp [LinearMap.sum_apply]

theorem PRank.comp_left {W' : Type} [AddCommGroup W'] [Module ℂ W'] {r : ℕ}
    {A B : V →ₗ[ℂ] W} (h : PRank r A B) (L : W →ₗ[ℂ] W') :
    PRank r (L ∘ₗ A) (L ∘ₗ B) := by
  obtain ⟨ι, _, a, b, ψ, u, hc, rfl, rfl⟩ := h
  refine ⟨ι, _, a, b, ψ, fun i => L (u i), hc, ?_, ?_⟩ <;>
  · ext x
    simp [LinearMap.sum_apply]

theorem PRank.add_smulRight {r : ℕ} {A B : V →ₗ[ℂ] W} (h : PRank r A B) (a b : ℂ)
    (ψ : V →ₗ[ℂ] ℂ) (u : W) :
    PRank (r + 1) (A + a • ψ.smulRight u) (B + b • ψ.smulRight u) := by
  obtain ⟨ι, _, a', b', ψ', u', hc, rfl, rfl⟩ := h
  refine ⟨Option ι, inferInstance, fun o => o.elim a a', fun o => o.elim b b',
    fun o => o.elim ψ ψ', fun o => o.elim u u', by simpa using hc, ?_, ?_⟩ <;>
  · rw [Fintype.sum_option]
    simp [add_comm]

theorem prank_of_basis {ι : Type} [Fintype ι] (bs : Basis ι ℂ V) (t : ι → ℂ)
    (A B : V →ₗ[ℂ] W) (h : ∀ i, A (bs i) = t i • B (bs i)) :
    PRank (Fintype.card ι) A B := by
  classical
  refine ⟨ι, inferInstance, t, fun _ => 1, bs.coord, fun i => B (bs i), le_rfl, ?_, ?_⟩ <;>
  · refine bs.ext fun j => ?_
    simp [LinearMap.sum_apply, h, Finsupp.single_apply]

/-- No left eigenvector: every nontrivial combination is surjective. -/
def NoLeft (A B : V →ₗ[ℂ] W) : Prop :=
  ∀ s t : ℂ, (s ≠ 0 ∨ t ≠ 0) → Function.Surjective (s • A + t • B)

theorem NoLeft.finrank_lt [FiniteDimensional ℂ V] [FiniteDimensional ℂ W] {A B : V →ₗ[ℂ] W}
    (h : NoLeft A B) (hW : 0 < finrank ℂ W) : finrank ℂ W < finrank ℂ V := by
  by_contra hlt
  have hB : Function.Surjective B := by
    have := h 0 1 (Or.inr one_ne_zero)
    simpa using this
  have hle : finrank ℂ W ≤ finrank ℂ V := LinearMap.finrank_le_finrank_of_surjective hB
  have heq : finrank ℂ V = finrank ℂ W := by omega
  have hBi : Function.Injective B :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank heq).mpr hB
  let e : V ≃ₗ[ℂ] W := LinearEquiv.ofBijective B ⟨hBi, hB⟩
  have : Nontrivial V := Module.nontrivial_of_finrank_pos (R := ℂ) (by omega)
  obtain ⟨c, hc⟩ := Module.End.exists_eigenvalue (e.symm.toLinearMap ∘ₗ A)
  obtain ⟨v, hv⟩ := hc.exists_hasEigenvector
  have h1 : e.symm (A v) = c • v := by
    have := hv.apply_eq_smul
    simpa using this
  have h2 : A v = c • B v := by
    have h := congrArg e h1
    rw [LinearEquiv.apply_symm_apply, map_smul] at h
    exact h
  have hs := h 1 (-c) (Or.inl one_ne_zero)
  have hi : Function.Injective ((1 : ℂ) • A + (-c) • B) :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank heq).mpr hs
  have h3 : ((1 : ℂ) • A + (-c) • B) v = ((1 : ℂ) • A + (-c) • B) 0 := by
    simp [h2]
  exact hv.2 (hi h3)

theorem span_ker (n : ℕ) : ∀ (V W : Type) [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (A B : V →ₗ[ℂ] W), finrank ℂ V = n → NoLeft A B → ∀ Λ : Finset ℂ,
    (⨆ (t : ℂ) (_ : t ∉ Λ), LinearMap.ker (A + t • B)) = ⊤ := by
  induction n with
  | zero =>
    intro V W _ _ _ _ _ _ A B hn hNL Λ
    have hW : finrank ℂ W = 0 := by
      by_contra hW
      have := hNL.finrank_lt (Nat.pos_of_ne_zero hW)
      omega
    have : Subsingleton W := Module.finrank_zero_iff.mp hW
    obtain ⟨t0, ht0⟩ := Infinite.exists_notMem_finset Λ
    refine top_le_iff.mp (le_iSup₂_of_le t0 ht0 ?_)
    intro x _
    exact Subsingleton.elim _ _
  | succ n ih =>
    intro V W _ _ _ _ _ _ A B hn hNL Λ
    obtain ⟨t0, ht0⟩ := Infinite.exists_notMem_finset Λ
    by_cases hW : finrank ℂ W = 0
    · have : Subsingleton W := Module.finrank_zero_iff.mp hW
      refine top_le_iff.mp (le_iSup₂_of_le t0 ht0 ?_)
      intro x _
      exact Subsingleton.elim _ _
    have hlt := hNL.finrank_lt (Nat.pos_of_ne_zero hW)
    have hker : LinearMap.ker (A + t0 • B) ≠ ⊥ := LinearMap.ker_ne_bot_of_finrank_lt hlt
    obtain ⟨v, hvk, hv⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker
    have hAv : A v = -(t0 • B v) := by
      have h : A v + t0 • B v = 0 := by simpa using hvk
      exact eq_neg_of_add_eq_zero_left h
    set p : Submodule ℂ V := Submodule.span ℂ {v} with hp
    set q : Submodule ℂ W := Submodule.span ℂ {B v} with hq
    have hBq : B v ∈ q := Submodule.mem_span_singleton_self _
    have hpA : p ≤ q.comap A := by
      rw [hp, Submodule.span_le, Set.singleton_subset_iff]
      show A v ∈ q
      rw [hAv]
      exact q.neg_mem (q.smul_mem _ hBq)
    have hpB : p ≤ q.comap B := by
      rw [hp, Submodule.span_le, Set.singleton_subset_iff]
      exact hBq
    have hNL' : NoLeft (p.mapQ q A hpA) (p.mapQ q B hpB) := by
      intro s t hst w'
      obtain ⟨w, rfl⟩ := Submodule.Quotient.mk_surjective q w'
      obtain ⟨x, hx⟩ := hNL s t hst w
      refine ⟨Submodule.Quotient.mk x, ?_⟩
      rw [← hx]
      simp [Submodule.mapQ_apply]
    have hfr : finrank ℂ (V ⧸ p) = n := by
      have h1 := Submodule.finrank_quotient_add_finrank p
      have h2 : finrank ℂ p = 1 := finrank_span_singleton hv
      omega
    have IH := ih (V ⧸ p) (W ⧸ q) (p.mapQ q A hpA) (p.mapQ q B hpB) hfr hNL' (insert t0 Λ)
    set S : Submodule ℂ V := ⨆ (t : ℂ) (_ : t ∉ Λ), LinearMap.ker (A + t • B) with hS
    have hvS : v ∈ S := (le_iSup₂_of_le (f := fun (t : ℂ) (_ : t ∉ Λ) => LinearMap.ker (A + t • B))
      t0 ht0 le_rfl) hvk
    have hpS : p ≤ S := by
      rw [hp, Submodule.span_le, Set.singleton_subset_iff]
      exact hvS
    have hmap : S.map p.mkQ = ⊤ := by
      rw [← top_le_iff, ← IH]
      refine iSup₂_le fun t ht => ?_
      have htΛ : t ∉ Λ := fun h => ht (Finset.mem_insert_of_mem h)
      have htt : t ≠ t0 := fun h => ht (h ▸ Finset.mem_insert_self _ _)
      intro xb hxb
      obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective p xb
      have h1 : (A + t • B) x ∈ q := by
        have h := LinearMap.mem_ker.mp hxb
        rw [← Submodule.Quotient.mk_eq_zero q]
        simpa [Submodule.mapQ_apply] using h
      obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp h1
      have htt' : t - t0 ≠ 0 := sub_ne_zero.mpr htt
      refine ⟨x - (c / (t - t0)) • v, ?_, ?_⟩
      · refine (le_iSup₂_of_le (f := fun (t : ℂ) (_ : t ∉ Λ) => LinearMap.ker (A + t • B))
          t htΛ le_rfl) ?_
        rw [LinearMap.mem_ker, map_sub, ← hc, map_smul, LinearMap.add_apply, LinearMap.smul_apply,
          hAv, ← sub_eq_zero]
        have : c • B v - (c / (t - t0)) • (-(t0 • B v) + t • B v) - 0
            = (c - (c / (t - t0)) * (t - t0)) • B v := by
          module
        rw [this, div_mul_cancel₀ _ htt', sub_self, zero_smul]
      · rw [Submodule.mkQ_apply, Submodule.Quotient.mk_sub, sub_eq_self,
          Submodule.Quotient.mk_eq_zero]
        exact p.smul_mem _ (Submodule.mem_span_singleton_self _)
    have h2 := (Submodule.map_mkQ_eq_top p S).mp hmap
    rwa [sup_eq_right.mpr hpS] at h2

theorem prank_of_noLeft [FiniteDimensional ℂ V] [FiniteDimensional ℂ W] {A B : V →ₗ[ℂ] W}
    (h : NoLeft A B) : PRank (finrank ℂ V) A B := by
  classical
  have hspan := span_ker (finrank ℂ V) V W A B rfl h ∅
  set E : Set V := {v | ∃ t : ℂ, A v = t • B v} with hE
  have hE' : Submodule.span ℂ E = ⊤ := by
    rw [← top_le_iff, ← hspan]
    refine iSup₂_le fun t _ => ?_
    intro x hx
    refine Submodule.subset_span ⟨-t, ?_⟩
    have h1 : A x + t • B x = 0 := by simpa using hx
    rw [neg_smul]
    exact eq_neg_of_add_eq_zero_left h1
  obtain ⟨b, hbE, hbspan, hli⟩ := exists_linearIndependent ℂ E
  have hb : ⊤ ≤ Submodule.span ℂ (Set.range (Subtype.val : b → V)) := by
    rw [Subtype.range_coe, hbspan, hE']
  let bs : Basis b ℂ V := Basis.mk hli hb
  have : Fintype b := FiniteDimensional.fintypeBasisIndex bs
  have hcard : finrank ℂ V = Fintype.card b := Module.finrank_eq_card_basis bs
  have ht : ∀ i : b, ∃ t : ℂ, A (bs i) = t • B (bs i) := by
    intro i
    have h1 : bs i = (i : V) := by simp [bs]
    rw [h1]
    exact hbE i.2
  choose t ht using ht
  rw [hcard]
  exact prank_of_basis bs t A B ht

theorem prank_le (k : ℕ) : ∀ (V W : Type) [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (A B : V →ₗ[ℂ] W), finrank ℂ V + finrank ℂ W = k →
    PRank (finrank ℂ W + finrank ℂ V / 2) A B := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro V W _ _ _ _ _ _ A B hk
    by_cases h0 : ∃ v : V, v ≠ 0 ∧ A v = 0 ∧ B v = 0
    · obtain ⟨v, hv, hAv, hBv⟩ := h0
      set p : Submodule ℂ V := Submodule.span ℂ {v} with hp
      have hpA : p ≤ LinearMap.ker A := by
        rw [hp, Submodule.span_le, Set.singleton_subset_iff]
        exact hAv
      have hpB : p ≤ LinearMap.ker B := by
        rw [hp, Submodule.span_le, Set.singleton_subset_iff]
        exact hBv
      have hfr : finrank ℂ (V ⧸ p) + 1 = finrank ℂ V := by
        have h1 := Submodule.finrank_quotient_add_finrank p
        have h2 : finrank ℂ p = 1 := finrank_span_singleton hv
        omega
      have IH := ih (finrank ℂ (V ⧸ p) + finrank ℂ W) (by omega) (V ⧸ p) W
        (p.liftQ A hpA) (p.liftQ B hpB) rfl
      have h2 := IH.comp_right p.mkQ
      rw [Submodule.liftQ_mkQ, Submodule.liftQ_mkQ] at h2
      exact h2.mono (by omega)
    by_cases h1 : NoLeft A B
    · have h2 := prank_of_noLeft h1
      have hinj : Function.Injective (A.prod B) := by
        rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
        intro x hx
        by_contra hx0
        have hx' : (A x, B x) = 0 := by simpa using hx
        exact h0 ⟨x, hx0, congrArg Prod.fst hx', congrArg Prod.snd hx'⟩
      have h3 := LinearMap.finrank_le_finrank_of_injective hinj
      rw [Module.finrank_prod] at h3
      exact h2.mono (by omega)
    · simp only [NoLeft, not_forall] at h1
      obtain ⟨s, t, hst, hns⟩ := h1
      have hr : LinearMap.range (s • A + t • B) < ⊤ :=
        lt_top_iff_ne_top.mpr (fun h => hns (LinearMap.range_eq_top.mp h))
      obtain ⟨φ, hφ, hφr⟩ := Submodule.exists_dual_map_eq_bot_of_lt_top hr inferInstance
      have hφ0 : ∀ x, s * φ (A x) + t * φ (B x) = 0 := by
        intro x
        have hmem : φ ((s • A + t • B) x) ∈ (LinearMap.range (s • A + t • B)).map φ :=
          ⟨_, ⟨x, rfl⟩, rfl⟩
        rw [hφr] at hmem
        simpa using hmem
      obtain ⟨w0, hw0⟩ : ∃ w, φ w ≠ 0 := by
        by_contra h
        exact hφ (LinearMap.ext fun x => by_contra fun hx => h ⟨x, hx⟩)
      set w : W := (φ w0)⁻¹ • w0 with hw
      have hφw : φ w = 1 := by simp [hw, hw0]
      let K : Submodule ℂ W := LinearMap.ker φ
      let P : W →ₗ[ℂ] K := LinearMap.codRestrict K (LinearMap.id - φ.smulRight w) (by
        intro x
        simp [K, hφw])
      have hP : ∀ x, ((P x : K) : W) = x - φ x • w := fun x => rfl
      have hfr : finrank ℂ K + 1 = finrank ℂ W := by
        have h1 : finrank ℂ (LinearMap.range φ) + finrank ℂ K = finrank ℂ W :=
          LinearMap.finrank_range_add_finrank_ker φ
        have hsurj : Function.Surjective φ := by
          intro c
          exact ⟨c • w, by simp [hφw]⟩
        have h2 : finrank ℂ (LinearMap.range φ) = 1 := by
          rw [LinearMap.range_eq_top.mpr hsurj, finrank_top, finrank_self]
        omega
      have IH := ih (finrank ℂ V + finrank ℂ K) (by omega) V K (P ∘ₗ A) (P ∘ₗ B) rfl
      have h2 := IH.comp_left K.subtype
      by_cases hs : s = 0
      · have ht : t ≠ 0 := by tauto
        have hφB : ∀ x, φ (B x) = 0 := by
          intro x
          have := hφ0 x
          simpa [hs, ht] using this
        have h3 := h2.add_smulRight 1 0 (φ ∘ₗ A) w
        have eA : K.subtype ∘ₗ P ∘ₗ A + (1 : ℂ) • (φ ∘ₗ A).smulRight w = A := by
          ext x
          simp [hP]
        have eB : K.subtype ∘ₗ P ∘ₗ B + (0 : ℂ) • (φ ∘ₗ A).smulRight w = B := by
          ext x
          simp [hP, hφB]
        rw [eA, eB] at h3
        exact h3.mono (by omega)
      · have hφA : ∀ x, φ (A x) = (-(t / s)) * φ (B x) := by
          intro x
          have := hφ0 x
          field_simp
          linear_combination this
        have h3 := h2.add_smulRight (-(t / s)) 1 (φ ∘ₗ B) w
        have eA : K.subtype ∘ₗ P ∘ₗ A + (-(t / s)) • (φ ∘ₗ B).smulRight w = A := by
          ext x
          simp [hP, hφA, mul_smul]
        have eB : K.subtype ∘ₗ P ∘ₗ B + (1 : ℂ) • (φ ∘ₗ B).smulRight w = B := by
          ext x
          simp [hP]
        rw [eA, eB] at h3
        exact h3.mono (by omega)

end Pencil
section Regular

open Matrix

/-- An invertible sum of rank-one matrices has at least `n` terms. -/
theorem card_ge_of_isUnit {n : ℕ} {ι : Type} [DecidableEq ι] (s : Finset ι) (c : ι → ℂ)
    (x y : ι → Fin n → ℂ) (h : IsUnit (∑ l ∈ s, c l • vecMulVec (x l) (y l))) : n ≤ s.card := by
  have hprod : ∑ l ∈ s, c l • vecMulVec (x l) (y l) =
      (Matrix.of fun (i : Fin n) (l : s) => c l * x l i) *
        (Matrix.of fun (l : s) (j : Fin n) => y l j) := by
    ext i j
    simp only [Matrix.sum_apply, Matrix.smul_apply, vecMulVec_apply, Matrix.mul_apply,
      Matrix.of_apply, smul_eq_mul]
    rw [← Finset.sum_coe_sort s]
    exact Finset.sum_congr rfl fun l _ => by ring
  have hr : (∑ l ∈ s, c l • vecMulVec (x l) (y l)).rank = n := by
    rw [Matrix.rank_of_isUnit _ h, Fintype.card_fin]
  rw [hprod] at hr
  have hle := (Matrix.rank_mul_le_left (Matrix.of fun (i : Fin n) (l : s) => c l * x l i)
    (Matrix.of fun (l : s) (j : Fin n) => y l j)).trans (Matrix.rank_le_card_width _)
  rw [hr, Fintype.card_coe] at hle
  exact hle

/-- From an invertible sum of more than `n` rank-one matrices one term can be removed. -/
theorem exists_erase {n : ℕ} {ι : Type} [DecidableEq ι] (s : Finset ι) (c : ι → ℂ)
    (x y : ι → Fin n → ℂ) (h : IsUnit (∑ l ∈ s, c l • vecMulVec (x l) (y l)))
    (hcard : n < s.card) :
    ∃ l₀ ∈ s, IsUnit (∑ l ∈ s.erase l₀, c l • vecMulVec (x l) (y l)) := by
  set G := ∑ l ∈ s, c l • vecMulVec (x l) (y l) with hG
  have hGdet : IsUnit G.det := (isUnit_iff_isUnit_det G).mp h
  have htr : (G⁻¹ * G).trace = (n : ℂ) := by
    rw [nonsing_inv_mul _ hGdet, Matrix.trace_one, Fintype.card_fin]
  have htr2 : (G⁻¹ * G).trace = ∑ l ∈ s, c l * ((G⁻¹ *ᵥ x l) ⬝ᵥ y l) := by
    have e : G⁻¹ * G = ∑ l ∈ s, c l • vecMulVec (G⁻¹ *ᵥ x l) (y l) := by
      conv_lhs => rw [hG]
      rw [Matrix.mul_sum]
      exact Finset.sum_congr rfl fun l _ => by rw [Matrix.mul_smul, mul_vecMulVec]
    rw [e, Matrix.trace_sum]
    exact Finset.sum_congr rfl fun l _ => by
      rw [Matrix.trace_smul, Matrix.trace_vecMulVec, smul_eq_mul]
  by_contra hall
  have h1 : ∀ l ∈ s, c l * ((G⁻¹ *ᵥ x l) ⬝ᵥ y l) = 1 := by
    intro l hl
    by_contra hne
    apply hall
    refine ⟨l, hl, ?_⟩
    rw [Finset.sum_erase_eq_sub hl, ← hG]
    have hfac : G - c l • vecMulVec (x l) (y l) =
        G * (1 + vecMulVec (-(c l) • (G⁻¹ *ᵥ x l)) (y l)) := by
      rw [Matrix.mul_add, Matrix.mul_one, mul_vecMulVec, Matrix.mulVec_smul,
        Matrix.mulVec_mulVec, mul_nonsing_inv _ hGdet, Matrix.one_mulVec, ← smul_vecMulVec,
        neg_smul, sub_eq_add_neg, neg_vecMulVec]
    rw [hfac, isUnit_iff_isUnit_det, Matrix.det_mul, Matrix.vecMulVec_eq Unit,
      Matrix.det_one_add_replicateCol_mul_replicateRow]
    refine hGdet.mul (isUnit_iff_ne_zero.mpr ?_)
    rw [dotProduct_smul, smul_eq_mul, dotProduct_comm]
    intro h0
    apply hne
    linear_combination -h0
  have hsum : (n : ℂ) = (s.card : ℂ) := by
    rw [← htr, htr2, Finset.sum_congr rfl h1, Finset.sum_const, nsmul_eq_mul, mul_one]
  have : n = s.card := by exact_mod_cast hsum
  omega

/-- An invertible sum of rank-one matrices contains an invertible subsum with exactly `n`
terms. -/
theorem exists_subsum {n : ℕ} {ι : Type} [DecidableEq ι] (c : ι → ℂ) (x y : ι → Fin n → ℂ) :
    ∀ (k : ℕ) (s : Finset ι), s.card = n + k →
      IsUnit (∑ l ∈ s, c l • vecMulVec (x l) (y l)) →
      ∃ s' ⊆ s, s'.card = n ∧ IsUnit (∑ l ∈ s', c l • vecMulVec (x l) (y l)) := by
  intro k
  induction k with
  | zero => exact fun s hs h => ⟨s, Finset.Subset.refl s, by simpa using hs, h⟩
  | succ k ih =>
    intro s hs h
    obtain ⟨l₀, hl₀, h'⟩ := exists_erase s c x y h (by omega)
    obtain ⟨s', hs', hc, hu⟩ := ih (s.erase l₀) (by rw [Finset.card_erase_of_mem hl₀]; omega) h'
    exact ⟨s', hs'.trans (Finset.erase_subset _ _), hc, hu⟩

/-- A sum of rank-one matrices over a finset of `n` indices, as `P * diagonal * Q`. -/
theorem sum_eq_mul_diag_mul {n : ℕ} {ι : Type} (s : Finset ι) (e : Fin n ≃ s)
    (d : ι → ℂ) (x y : ι → Fin n → ℂ) :
    ∑ l ∈ s, d l • vecMulVec (x l) (y l) =
      (Matrix.of fun (i : Fin n) (k : Fin n) => x (e k) i) *
        Matrix.diagonal (fun k => d (e k)) * (Matrix.of fun (k : Fin n) (j : Fin n) => y (e k) j) := by
  ext i j
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, Matrix.of_apply, Matrix.sum_apply, Matrix.smul_apply,
    vecMulVec_apply, smul_eq_mul]
  rw [← Finset.sum_coe_sort s, ← Equiv.sum_comp e]
  exact Finset.sum_congr rfl fun k _ => by ring

/-- A sum of rank-one matrices over a finset with at most `m` elements, padded by zeros to a
sum over `Fin m`, simultaneously for two families of coefficients. -/
theorem exists_pad {n m : ℕ} {ι : Type} (s : Finset ι) (hs : s.card ≤ m)
    (a b : ι → ℂ) (x y : ι → Fin n → ℂ) :
    ∃ (u v : Fin m → Fin n → ℂ) (α β : Fin m → ℂ),
      ∑ l ∈ s, a l • vecMulVec (x l) (y l) = ∑ j, α j • vecMulVec (u j) (v j) ∧
      ∑ l ∈ s, b l • vecMulVec (x l) (y l) = ∑ j, β j • vecMulVec (u j) (v j) := by
  have hcard : Fintype.card s ≤ Fintype.card (Fin m) := by
    rw [Fintype.card_coe, Fintype.card_fin]
    exact hs
  obtain ⟨emb⟩ := Function.Embedding.nonempty_of_card_le hcard
  refine ⟨Function.extend emb (fun l : s => x l) 0, Function.extend emb (fun l : s => y l) 0,
    Function.extend emb (fun l : s => a l) 0, Function.extend emb (fun l : s => b l) 0, ?_, ?_⟩
  · rw [← Finset.sum_coe_sort s]
    refine Fintype.sum_of_injective emb emb.injective _ _ (fun j hj => ?_) (fun l => ?_)
    · rw [Function.extend_apply' _ _ _ (fun h => hj h), Pi.zero_apply, zero_smul]
    · rw [emb.injective.extend_apply, emb.injective.extend_apply, emb.injective.extend_apply]
  · rw [← Finset.sum_coe_sort s]
    refine Fintype.sum_of_injective emb emb.injective _ _ (fun j hj => ?_) (fun l => ?_)
    · rw [Function.extend_apply' _ _ _ (fun h => hj h), Pi.zero_apply, zero_smul]
    · rw [emb.injective.extend_apply, emb.injective.extend_apply, emb.injective.extend_apply]

/-- A pencil of square matrices as a sum of `n + n / 2` rank-one pencils, in matrix form. -/
theorem exists_rank_one_sum (n : ℕ) (A B : Matrix (Fin n) (Fin n) ℂ) :
    ∃ (ι : Type) (_ : Fintype ι) (a b : ι → ℂ) (x y : ι → Fin n → ℂ),
      Fintype.card ι ≤ n + n / 2 ∧ A = ∑ l, a l • vecMulVec (x l) (y l) ∧
        B = ∑ l, b l • vecMulVec (x l) (y l) := by
  have h := prank_le (n + n) (Fin n → ℂ) (Fin n → ℂ) (Matrix.toLin' A) (Matrix.toLin' B)
    (by simp)
  rw [Module.finrank_fin_fun] at h
  obtain ⟨ι, hι, a, b, ψ, w, hc, hA, hB⟩ := h
  refine ⟨ι, hι, a, b, w, fun l j => ψ l (Pi.single j 1), hc, ?_, ?_⟩
  · ext i j
    have h1 := congrFun (LinearMap.congr_fun hA (Pi.single j 1)) i
    rw [Matrix.toLin'_apply, Matrix.mulVec_single_one] at h1
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.smulRight_apply,
      Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Matrix.col_apply] at h1
    simp only [Matrix.sum_apply, Matrix.smul_apply, vecMulVec_apply, smul_eq_mul]
    rw [h1]
    exact Finset.sum_congr rfl fun l _ => by ring
  · ext i j
    have h1 := congrFun (LinearMap.congr_fun hB (Pi.single j 1)) i
    rw [Matrix.toLin'_apply, Matrix.mulVec_single_one] at h1
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.smulRight_apply,
      Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Matrix.col_apply] at h1
    simp only [Matrix.sum_apply, Matrix.smul_apply, vecMulVec_apply, smul_eq_mul]
    rw [h1]
    exact Finset.sum_congr rfl fun l _ => by ring

/-- The regular case: a pencil of `n × n` matrices containing an invertible matrix is, in
suitable bases, simultaneously diagonal up to `n / 2` rank-one pencils. -/
theorem regular_pencil (n : ℕ) (A B : Matrix (Fin n) (Fin n) ℂ)
    (h : ∃ s t : ℂ, IsUnit (s • A + t • B)) :
    ∃ (P Q : Matrix (Fin n) (Fin n) ℂ) (a b : Fin n → ℂ) (u v : Fin (n / 2) → Fin n → ℂ)
      (α β : Fin (n / 2) → ℂ), IsUnit P ∧ IsUnit Q ∧
      A = P * Matrix.diagonal a * Q + ∑ j, α j • Matrix.vecMulVec (u j) (v j) ∧
      B = P * Matrix.diagonal b * Q + ∑ j, β j • Matrix.vecMulVec (u j) (v j) := by
  classical
  obtain ⟨s, t, hst⟩ := h
  obtain ⟨ι, _, a, b, x, y, hc, hA, hB⟩ := exists_rank_one_sum n A B
  have hsum : s • A + t • B = ∑ l ∈ Finset.univ, (s * a l + t * b l) • vecMulVec (x l) (y l) := by
    rw [hA, hB, Finset.smul_sum, Finset.smul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun l _ => by rw [smul_smul, smul_smul, add_smul]
  rw [hsum] at hst
  have hge : n ≤ (Finset.univ : Finset ι).card := card_ge_of_isUnit _ _ x y hst
  obtain ⟨s', hs', hcard, hu⟩ := exists_subsum (fun l => s * a l + t * b l) x y
    ((Finset.univ : Finset ι).card - n) Finset.univ (by omega) hst
  have e : Fin n ≃ s' := (Finset.equivFinOfCardEq hcard).symm
  rw [sum_eq_mul_diag_mul s' e] at hu
  have hdet := (isUnit_iff_isUnit_det _).mp hu
  rw [Matrix.det_mul, Matrix.det_mul] at hdet
  have hP : IsUnit (Matrix.of fun (i : Fin n) (k : Fin n) => x (e k) i) :=
    (isUnit_iff_isUnit_det _).mpr (isUnit_of_mul_isUnit_left (isUnit_of_mul_isUnit_left hdet))
  have hQ : IsUnit (Matrix.of fun (k : Fin n) (j : Fin n) => y (e k) j) :=
    (isUnit_iff_isUnit_det _).mpr (isUnit_of_mul_isUnit_right hdet)
  have hrest : (Finset.univ \ s').card ≤ n / 2 := by
    rw [Finset.card_sdiff_of_subset hs', hcard]
    rw [Finset.card_univ]
    omega
  obtain ⟨u, v, α, β, hα, hβ⟩ := exists_pad (Finset.univ \ s') hrest a b x y
  refine ⟨_, _, fun k => a (e k), fun k => b (e k), u, v, α, β, hP, hQ, ?_, ?_⟩
  · rw [← sum_eq_mul_diag_mul s' e a x y, ← hα, add_comm, Finset.sum_sdiff hs']
    exact hA
  · rw [← sum_eq_mul_diag_mul s' e b x y, ← hβ, add_comm, Finset.sum_sdiff hs']
    exact hB

end Regular

end SqH1

theorem OMA.solution : OMA.R_Arxiv_0805_3777_cprank_le_of_square_slices_R1.H1 :=
  SqH1.regular_pencil
