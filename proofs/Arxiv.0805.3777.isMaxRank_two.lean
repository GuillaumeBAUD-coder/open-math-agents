import FormalConjectures.Arxiv.«0805.3777».TensorRank
import Mathlib

-- Problem: Generic and maximal rank of 3-tensors — isMaxRank two
-- Upstream: formal-conjectures FormalConjectures/Arxiv/0805.3777/TensorRank.lean:285 (declaration Arxiv.«0805.3777».isMaxRank_two)
-- Credit: @ivillar (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.
--
-- REUSE AND CREDIT. The generic Holor plumbing in the section Bridge below (ix, ix_surjective, ev,
-- holor_ext, ev_sum, headI_lt, forall₂_tail, idxHead, idxTail, vec, one0, r1, ev_r1,
-- cprankMax1_r1, cprankMax1_cons, ix1, cprankMax1_iff, exists_sum_of_cprankMax, cprankMax_cprank,
-- cprank_le_of_cprankMax) is adapted from the format [3, 3, 5] to the format [2, m, n] from the
-- merged proof proofs/Arxiv.0805.3777.isMaxRank_three_three_five_bounds.lean of this repository
-- (PR #2438, credited there to @DomTheDeveloper; that file is itself a port of Kenta Kitamura's
-- https://github.com/KitaKen1/mrank-3-3-5-lean, Apache License 2.0). Everything else is new.

/-!
# The maximal rank of complex `2 × m × n` tensors

For `m ≤ n` the maximal rank of a tensor of format `2 × m × n` is `m + min m (n / 2)`
(Ja'Ja' 1979, classically via Kronecker's canonical form of matrix pencils). The proof below
avoids the canonical form.

A tensor of format `2 × m × n` is a pair of linear maps `A B : ℂⁿ → ℂᵐ`, a *pencil*; its rank is
the least number of rank-one pencils `(a • ψ ⊗ u, b • ψ ⊗ u)` summing to it (`PRank`).

**Upper bound** (`prank_le`): every pencil `V → W` has rank at most `dim W + dim V / 2`, by
induction on `dim V + dim W`.
* If `A` and `B` have a common kernel vector, pass to the quotient of `V` by it (free).
* If some combination `s • A + t • B` is not surjective, a functional `φ` kills its range, so
  `φ ∘ A` and `φ ∘ B` are proportional: split off that one row at cost one and recurse on `ker φ`.
* Otherwise every `s • A + t • B` is surjective. Then the eigenvectors (kernel vectors of the
  `A + t • B`) span `V` (`span_ker`, an induction on `dim V` that quotients by one eigenvector at a
  time and lifts eigenvectors, avoiding finitely many parameters `t`). A basis of eigenvectors
  writes the pencil with `dim V` terms, and `dim V ≤ 2 dim W` because there is no common kernel.
Together with the trivial bound `2 m` this gives `m + min m (n / 2)`.

**Lower bound** (`lower_core`): the tensor `T0` with slices `[I 0]` and a partial identity shifted
to the last `q = min m (n / 2)` columns has rank at least `m + q`. In a decomposition
`∑ (a l, b l) ⊗ x l ⊗ y l` with `r` terms the `x l` span `ℂᵐ`; choose `m` of them forming a basis.
Modulo the span `Z` of the other `y l` (of dimension at most `r - m`), the two slices are
simultaneously diagonal in the dual basis. With the shift `Φ` satisfying `Φ ∘ F = G`, `Φ ∘ G = 0`
this forces the range of the second slice, of dimension `q`, into `(Z ⊓ ker Φ) ⊔ Φ Z`, whose
dimension is at most `dim Z`. Hence `q ≤ r - m`.
-/

open Module

namespace F1

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

theorem prank_two_mul {ι : Type} [Fintype ι] (bs : Basis ι ℂ W) (A B : V →ₗ[ℂ] W) :
    PRank (2 * Fintype.card ι) A B := by
  classical
  refine ⟨ι ⊕ ι, inferInstance, Sum.elim 1 0, Sum.elim 0 1,
    Sum.elim (fun i => bs.coord i ∘ₗ A) (fun i => bs.coord i ∘ₗ B), Sum.elim bs bs,
    by simp [two_mul], ?_, ?_⟩ <;>
  · ext x
    simp [LinearMap.sum_apply, Fintype.sum_sum_type, bs.sum_repr]

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

section Bridge

variable {m n : ℕ}

/-- The index `(c, i, j)` of a `2 × m × n` holor. -/
def ix (c : Fin 2) (i : Fin m) (j : Fin n) : HolorIndex [2, m, n] :=
  ⟨[c.1, i.1, j.1], .cons c.2 (.cons i.2 (.cons j.2 .nil))⟩

theorem ix_surjective (t : HolorIndex [2, m, n]) : ∃ c i j, t = ix c i j := by
  obtain ⟨l, h⟩ := t
  cases h with
  | cons ha h =>
    cases h with
    | cons hb h =>
      cases h with
      | cons hc h =>
        cases h
        exact ⟨⟨_, ha⟩, ⟨_, hb⟩, ⟨_, hc⟩, rfl⟩

/-- Entry `(c, i, j)` of a `2 × m × n` holor. -/
def ev (T : Holor ℂ [2, m, n]) (c : Fin 2) (i : Fin m) (j : Fin n) : ℂ :=
  T (ix c i j)

theorem holor_ext {T T' : Holor ℂ [2, m, n]} (h : ∀ c i j, ev T c i j = ev T' c i j) :
    T = T' := by
  funext t
  obtain ⟨c, i, j, rfl⟩ := ix_surjective t
  exact h c i j

theorem ev_zero (c : Fin 2) (i : Fin m) (j : Fin n) : ev (0 : Holor ℂ [2, m, n]) c i j = 0 :=
  rfl

theorem ev_add (T T' : Holor ℂ [2, m, n]) (c : Fin 2) (i : Fin m) (j : Fin n) :
    ev (T + T') c i j = ev T c i j + ev T' c i j :=
  rfl

theorem ev_sum {ι : Type} (s : Finset ι) (f : ι → Holor ℂ [2, m, n]) (c : Fin 2) (i : Fin m)
    (j : Fin n) : ev (∑ l ∈ s, f l) c i j = ∑ l ∈ s, ev (f l) c i j := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [ev_zero]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, ev_add, ih]

theorem headI_lt {d : ℕ} {ds : List ℕ} (t : HolorIndex (d :: ds)) : t.1.headI < d := by
  obtain ⟨l, h⟩ := t
  cases h with
  | cons ha _ => exact ha

theorem forall₂_tail {d : ℕ} {ds : List ℕ} (t : HolorIndex (d :: ds)) :
    List.Forall₂ (· < ·) t.1.tail ds := by
  obtain ⟨l, h⟩ := t
  cases h with
  | cons _ h => exact h

/-- The first coordinate of a holor index. -/
def idxHead {d : ℕ} {ds : List ℕ} (t : HolorIndex (d :: ds)) : Fin d :=
  ⟨t.1.headI, headI_lt t⟩

/-- The remaining coordinates of a holor index. -/
def idxTail {d : ℕ} {ds : List ℕ} (t : HolorIndex (d :: ds)) : HolorIndex ds :=
  ⟨t.1.tail, forall₂_tail t⟩

/-- A vector as a one-dimensional holor. -/
def vec {k : ℕ} (u : Fin k → ℂ) : Holor ℂ [k] := fun t => u (idxHead t)

/-- The scalar holor `1`. -/
def one0 : Holor ℂ [] := fun _ => 1

/-- The rank-one holor `u ⊗ v ⊗ w`. -/
def r1 (u : Fin 2 → ℂ) (v : Fin m → ℂ) (w : Fin n → ℂ) : Holor ℂ [2, m, n] :=
  Holor.mul (vec u) (Holor.mul (vec v) (Holor.mul (vec w) one0))

theorem ev_r1 (u : Fin 2 → ℂ) (v : Fin m → ℂ) (w : Fin n → ℂ) (c : Fin 2) (i : Fin m)
    (j : Fin n) : ev (r1 u v w) c i j = u c * v i * w j := by
  show u c * (v i * (w j * 1)) = _
  ring

theorem cprankMax1_r1 (u : Fin 2 → ℂ) (v : Fin m → ℂ) (w : Fin n → ℂ) :
    Holor.CPRankMax1 (r1 u v w) :=
  .cons _ _ (.cons _ _ (.cons _ _ (.nil _)))

theorem cprankMax1_cons {α : Type} [Mul α] {d : ℕ} {ds : List ℕ} {x : Holor α (d :: ds)}
    (h : Holor.CPRankMax1 x) :
    ∃ (u : Holor α [d]) (y : Holor α ds), Holor.CPRankMax1 y ∧ x = Holor.mul u y := by
  cases h with
  | cons u y hy => exact ⟨u, y, hy, rfl⟩

/-- The one-coordinate holor index `[i]`. -/
def ix1 {k : ℕ} (i : Fin k) : HolorIndex [k] :=
  ⟨[i.1], .cons i.2 .nil⟩

theorem cprankMax1_iff {x : Holor ℂ [2, m, n]} :
    Holor.CPRankMax1 x ↔ ∃ u v w, x = r1 u v w := by
  constructor
  · intro h
    obtain ⟨u₁, y₁, h₁, rfl⟩ := cprankMax1_cons h
    obtain ⟨u₂, y₂, h₂, rfl⟩ := cprankMax1_cons h₁
    obtain ⟨u₃, y₃, -, rfl⟩ := cprankMax1_cons h₂
    refine ⟨fun i => u₁ (ix1 i), fun j => u₂ (ix1 j), fun k => u₃ (ix1 k) * y₃ ⟨[], .nil⟩,
      holor_ext fun c i j => ?_⟩
    rw [ev_r1]
    show u₁ (ix1 c) * (u₂ (ix1 i) * (u₃ (ix1 j) * y₃ ⟨[], .nil⟩)) = _
    ring
  · rintro ⟨u, v, w, rfl⟩
    exact cprankMax1_r1 u v w

/-- A holor of CP rank at most `n` is a sum of `n` holors of rank at most one. -/
theorem exists_sum_of_cprankMax {α : Type} [Mul α] [AddCommMonoid α] {ds : List ℕ} {k : ℕ}
    {x : Holor α ds} (h : Holor.CPRankMax k x) :
    ∃ f : Fin k → Holor α ds, (∀ l, Holor.CPRankMax1 (f l)) ∧ x = ∑ l, f l := by
  induction h with
  | zero => exact ⟨Fin.elim0, fun l => l.elim0, by simp⟩
  | succ n x y hx _ ih =>
    obtain ⟨f, hf, rfl⟩ := ih
    refine ⟨Fin.cons x f, fun l => Fin.cases hx hf l, ?_⟩
    rw [Fin.sum_univ_succ]
    rfl

theorem cprankMax_cprank {ds : List ℕ} (x : Holor ℂ ds) : Holor.CPRankMax x.cprank x :=
  @Nat.find_spec (fun n => Holor.CPRankMax n x) (Classical.decPred _)
    ⟨ds.prod, Holor.cprankMax_upper_bound x⟩

theorem cprank_le_of_cprankMax {ds : List ℕ} {x : Holor ℂ ds} {k : ℕ}
    (h : Holor.CPRankMax k x) : x.cprank ≤ k :=
  @Nat.find_min' (fun n => Holor.CPRankMax n x) (Classical.decPred _)
    ⟨ds.prod, Holor.cprankMax_upper_bound x⟩ k h

theorem cprank_le_of_sum {ι : Type} [Fintype ι] (T : Holor ℂ [2, m, n]) (u : ι → Fin 2 → ℂ)
    (v : ι → Fin m → ℂ) (w : ι → Fin n → ℂ)
    (h : ∀ c i j, ev T c i j = ∑ l, u l c * v l i * w l j) : T.cprank ≤ Fintype.card ι := by
  have hT : T = ∑ l, r1 (u l) (v l) (w l) := by
    refine holor_ext fun c i j => ?_
    rw [ev_sum, h]
    exact Finset.sum_congr rfl fun l _ => (ev_r1 _ _ _ _ _ _).symm
  have hr := Holor.cprankMax_sum (n := 1) Finset.univ (fun l => r1 (u l) (v l) (w l))
    fun l _ => Holor.cprankMax_1 (cprankMax1_r1 _ _ _)
  rw [Finset.card_univ, mul_one, ← hT] at hr
  exact cprank_le_of_cprankMax hr

theorem exists_sum_of_cprank (T : Holor ℂ [2, m, n]) :
    ∃ (u : Fin T.cprank → Fin 2 → ℂ) (v : Fin T.cprank → Fin m → ℂ)
      (w : Fin T.cprank → Fin n → ℂ), ∀ c i j, ev T c i j = ∑ l, u l c * v l i * w l j := by
  obtain ⟨f, hf, hT⟩ := exists_sum_of_cprankMax (cprankMax_cprank T)
  choose u v w huvw using fun l => cprankMax1_iff.mp (hf l)
  refine ⟨u, v, w, fun c i j => ?_⟩
  conv_lhs => rw [hT]
  rw [ev_sum]
  exact Finset.sum_congr rfl fun l _ => by rw [huvw, ev_r1]

/-- The two slices of a `2 × m × n` holor, as linear maps. -/
def penc (T : Holor ℂ [2, m, n]) (c : Fin 2) : (Fin n → ℂ) →ₗ[ℂ] (Fin m → ℂ) :=
  Matrix.mulVecLin (Matrix.of fun i j => ev T c i j)

theorem penc_single (T : Holor ℂ [2, m, n]) (c : Fin 2) (i : Fin m) (j : Fin n) :
    penc T c (Pi.single j 1) i = ev T c i j := by
  simp [penc]

theorem cprank_le_of_prank {T : Holor ℂ [2, m, n]} {r : ℕ}
    (h : PRank r (penc T 0) (penc T 1)) : T.cprank ≤ r := by
  obtain ⟨ι, _, a, b, ψ, u, hc, hA, hB⟩ := h
  refine (cprank_le_of_sum T (fun l => ![a l, b l]) u (fun l j => ψ l (Pi.single j 1))
    ?_).trans hc
  intro c i j
  rw [← penc_single]
  fin_cases c
  · show penc T 0 (Pi.single j 1) i = ∑ l, a l * u l i * ψ l (Pi.single j 1)
    rw [hA]
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.smulRight_apply,
      Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    exact Finset.sum_congr rfl fun l _ => by ring
  · show penc T 1 (Pi.single j 1) i = ∑ l, b l * u l i * ψ l (Pi.single j 1)
    rw [hB]
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.smulRight_apply,
      Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    exact Finset.sum_congr rfl fun l _ => by ring

theorem cprank_le (T : Holor ℂ [2, m, n]) : T.cprank ≤ m + min m (n / 2) := by
  have h1 : PRank (m + n / 2) (penc T 0) (penc T 1) := by
    have h := prank_le _ (Fin n → ℂ) (Fin m → ℂ) (penc T 0) (penc T 1) rfl
    simpa using h
  have h2 : PRank (2 * m) (penc T 0) (penc T 1) := by
    have h := prank_two_mul (Pi.basisFun ℂ (Fin m)) (penc T 0) (penc T 1)
    simpa using h
  rcases le_total m (n / 2) with h | h
  · rw [min_eq_left h]
    exact cprank_le_of_prank (h2.mono (by omega))
  · rw [min_eq_right h]
    exact cprank_le_of_prank h1

end Bridge

section Lower

theorem lower_core {m n q r : ℕ} (hq : q ≤ m) (hmn : m ≤ n) (h2q : 2 * q ≤ n)
    (a b : Fin r → ℂ) (x : Fin r → Fin m → ℂ) (y : Fin r → Fin n → ℂ)
    (hA : ∀ (i : Fin m) (j : Fin n), ∑ l, a l * x l i * y l j = if j.1 = i.1 then 1 else 0)
    (hB : ∀ (i : Fin m) (j : Fin n), ∑ l, b l * x l i * y l j =
      if i.1 < q ∧ j.1 = n - q + i.1 then 1 else 0) :
    m + q ≤ r := by
  classical
  set cA : Fin n → Fin m → ℂ := fun j i => if j.1 = i.1 then 1 else 0 with hcA
  set cB : Fin n → Fin m → ℂ := fun j i => if i.1 < q ∧ j.1 = n - q + i.1 then 1 else 0
    with hcB
  have hcA' : ∀ j, ∑ l, (a l * y l j) • x l = cA j := by
    intro j
    funext i
    rw [Finset.sum_apply]
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [hcA]
    simp only
    rw [← hA i j]
    exact Finset.sum_congr rfl fun l _ => by ring
  have hcB' : ∀ j, ∑ l, (b l * y l j) • x l = cB j := by
    intro j
    funext i
    rw [Finset.sum_apply]
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [hcB]
    simp only
    rw [← hB i j]
    exact Finset.sum_congr rfl fun l _ => by ring
  -- the `x l` span everything
  have hspan : Submodule.span ℂ (Set.range x) = ⊤ := by
    rw [eq_top_iff, ← (Pi.basisFun ℂ (Fin m)).span_eq, Submodule.span_le]
    rintro _ ⟨i0, rfl⟩
    have h1 : (Pi.basisFun ℂ (Fin m)) i0 = cA ⟨i0.1, by omega⟩ := by
      funext i
      simp only [Pi.basisFun_apply, Pi.single_apply, hcA, Fin.ext_iff]
      by_cases h : i.1 = i0.1
      · rw [if_pos h, if_pos h.symm]
      · rw [if_neg h, if_neg (fun h' => h h'.symm)]
    rw [h1, ← hcA']
    exact Submodule.sum_mem _ fun l _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨l, rfl⟩)
  obtain ⟨κ, e, he, hsp, hli⟩ := exists_linearIndependent' ℂ x
  have hb : ⊤ ≤ Submodule.span ℂ (Set.range (x ∘ e)) := by rw [hsp, hspan]
  let bs : Basis κ ℂ (Fin m → ℂ) := Basis.mk hli hb
  have hbs : ∀ k, bs k = x (e k) := fun k => by simp [bs]
  have : Fintype κ := FiniteDimensional.fintypeBasisIndex bs
  have hcard : Fintype.card κ = m := by
    have h := Module.finrank_eq_card_basis bs
    simpa using h.symm
  set Sf : Finset (Fin r) := Finset.univ.image e with hSf
  have hSfcard : Sf.card = m := by
    rw [hSf, Finset.card_image_of_injective _ he, Finset.card_univ, hcard]
  have hmr : m ≤ r := by
    have h := Finset.card_le_univ Sf
    rw [hSfcard, Fintype.card_fin] at h
    exact h
  set Z : Submodule ℂ (Fin n → ℂ) :=
    Submodule.span ℂ ((Sfᶜ.image y : Finset (Fin n → ℂ)) : Set (Fin n → ℂ)) with hZ
  have hZdim : finrank ℂ Z ≤ r - m := by
    have h1 : finrank ℂ Z ≤ (Sfᶜ.image y).card := finrank_span_finset_le_card (R := ℂ) (Sfᶜ.image y)
    have h2 : (Sfᶜ.image y).card ≤ Sfᶜ.card := Finset.card_image_le
    have h3 : Sfᶜ.card = r - m := by rw [Finset.card_compl, Fintype.card_fin, hSfcard]
    omega
  -- the two slices as maps on the dual
  let Fd : Module.Dual ℂ (Fin m → ℂ) →ₗ[ℂ] (Fin n → ℂ) :=
    ∑ l, a l • (Module.Dual.eval ℂ (Fin m → ℂ) (x l)).smulRight (y l)
  let Gd : Module.Dual ℂ (Fin m → ℂ) →ₗ[ℂ] (Fin n → ℂ) :=
    ∑ l, b l • (Module.Dual.eval ℂ (Fin m → ℂ) (x l)).smulRight (y l)
  have hFd : ∀ θ, Fd θ = ∑ l, (a l * θ (x l)) • y l := by
    intro θ
    simp [Fd, LinearMap.sum_apply, mul_smul]
  have hGd : ∀ θ, Gd θ = ∑ l, (b l * θ (x l)) • y l := by
    intro θ
    simp [Gd, LinearMap.sum_apply, mul_smul]
  have hFdj : ∀ (θ : Module.Dual ℂ (Fin m → ℂ)) (j : Fin n), Fd θ j = θ (cA j) := by
    intro θ j
    rw [hFd, ← hcA', map_sum, Finset.sum_apply]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [map_smul, Pi.smul_apply, smul_eq_mul, smul_eq_mul]
    ring
  have hGdj : ∀ (θ : Module.Dual ℂ (Fin m → ℂ)) (j : Fin n), Gd θ j = θ (cB j) := by
    intro θ j
    rw [hGd, ← hcB', map_sum, Finset.sum_apply]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [map_smul, Pi.smul_apply, smul_eq_mul, smul_eq_mul]
    ring
  -- the shift
  let sh : Fin n → Fin n := fun j => ⟨j.1 - (n - q), by omega⟩
  let Φ : (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ) :=
    { toFun := fun z j => if n - q ≤ j.1 then z (sh j) else 0
      map_add' := by
        intro z z'
        funext j
        show (if n - q ≤ j.1 then (z + z') (sh j) else 0) =
          (if n - q ≤ j.1 then z (sh j) else 0) + (if n - q ≤ j.1 then z' (sh j) else 0)
        split_ifs
        · rfl
        · exact (add_zero 0).symm
      map_smul' := by
        intro c z
        funext j
        show (if n - q ≤ j.1 then (c • z) (sh j) else 0) =
          c • (if n - q ≤ j.1 then z (sh j) else 0)
        split_ifs
        · rfl
        · exact (smul_zero c).symm }
  have hΦ : ∀ (z : Fin n → ℂ) (j : Fin n), Φ z j = if n - q ≤ j.1 then z (sh j) else 0 :=
    fun z j => rfl
  have hΦF : ∀ θ, Φ (Fd θ) = Gd θ := by
    intro θ
    funext j
    rw [hΦ, hGdj]
    by_cases h : n - q ≤ j.1
    · rw [if_pos h, hFdj]
      congr 1
      funext i
      have hj := j.2
      have hiff : (j.1 - (n - q) = i.1) ↔ (i.1 < q ∧ j.1 = n - q + i.1) := by omega
      simp only [hcA, hcB, sh]
      rw [if_congr hiff rfl rfl]
    · rw [if_neg h]
      have h0 : cB j = 0 := by
        funext i
        simp only [hcB, Pi.zero_apply]
        rw [if_neg]
        omega
      rw [h0, map_zero]
  have hΦG : ∀ θ, Φ (Gd θ) = 0 := by
    intro θ
    funext j
    rw [hΦ]
    by_cases h : n - q ≤ j.1
    · rw [if_pos h, hGdj]
      have h0 : cB (sh j) = 0 := by
        funext i
        have hj := j.2
        simp only [hcB, sh, Pi.zero_apply]
        rw [if_neg]
        omega
      rw [h0, map_zero]
      rfl
    · rw [if_neg h]
      rfl
  set Z' : Submodule ℂ (Fin n → ℂ) := (Z ⊓ LinearMap.ker Φ) ⊔ Z.map Φ with hZ'
  have hZ'dim : finrank ℂ Z' ≤ finrank ℂ Z := by
    have h1 : finrank ℂ Z' ≤ finrank ℂ (Z ⊓ LinearMap.ker Φ : Submodule ℂ (Fin n → ℂ)) +
        finrank ℂ (Z.map Φ) :=
      Submodule.finrank_add_le_finrank_add_finrank (Z ⊓ LinearMap.ker Φ) (Z.map Φ)
    have h2 := LinearMap.finrank_range_add_finrank_ker (Φ.domRestrict Z)
    rw [LinearMap.range_domRestrict, LinearMap.ker_domRestrict] at h2
    have h3 : finrank ℂ ((LinearMap.ker Φ).comap Z.subtype) =
        finrank ℂ (Z ⊓ LinearMap.ker Φ : Submodule ℂ (Fin n → ℂ)) := by
      rw [← Submodule.finrank_map_subtype_eq, Submodule.map_comap_subtype]
    omega
  have hmem : ∀ (c : Fin r → ℂ) (k : κ), (∀ k', k' ≠ k → c (e k') = 0) →
      ∑ l, c l • y l - c (e k) • y (e k) ∈ Z := by
    intro c k hc
    rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ (e k)), add_sub_cancel_left]
    refine Submodule.sum_mem _ fun l hl => ?_
    by_cases hlS : l ∈ Sf
    · obtain ⟨k', -, rfl⟩ := Finset.mem_image.mp hlS
      have hne : k' ≠ k := fun h => (Finset.ne_of_mem_erase hl) (by rw [h])
      rw [hc k' hne, zero_smul]
      exact Z.zero_mem
    · exact Z.smul_mem _ (Submodule.subset_span
        (Finset.mem_coe.mpr (Finset.mem_image_of_mem y (Finset.mem_compl.mpr hlS))))
  have hcoord : ∀ k k', bs.coord k (x (e k')) = if k' = k then 1 else 0 := by
    intro k k'
    rw [← hbs, Basis.coord_apply, Basis.repr_self, Finsupp.single_apply]
  have hkey : ∀ k : κ, Gd (bs.coord k) ∈ Z' := by
    intro k
    have hF : Fd (bs.coord k) - a (e k) • y (e k) ∈ Z := by
      have h := hmem (fun l => a l * bs.coord k (x l)) k (by
        intro k' hk'
        simp only [hcoord, if_neg hk', mul_zero])
      simp only [hcoord, if_true, mul_one] at h
      rw [hFd]
      exact h
    have hG : Gd (bs.coord k) - b (e k) • y (e k) ∈ Z := by
      have h := hmem (fun l => b l * bs.coord k (x l)) k (by
        intro k' hk'
        simp only [hcoord, if_neg hk', mul_zero])
      simp only [hcoord, if_true, mul_one] at h
      rw [hGd]
      exact h
    have hGker : Gd (bs.coord k) ∈ LinearMap.ker Φ := hΦG _
    by_cases hb0 : b (e k) = 0
    · rw [hb0, zero_smul, sub_zero] at hG
      exact Submodule.mem_sup_left ⟨hG, hGker⟩
    · refine Submodule.mem_sup_right ⟨(Fd (bs.coord k) - a (e k) • y (e k)) -
        (a (e k) / b (e k)) • (Gd (bs.coord k) - b (e k) • y (e k)),
        Z.sub_mem hF (Z.smul_mem _ hG), ?_⟩
      have h1 : (Fd (bs.coord k) - a (e k) • y (e k)) -
          (a (e k) / b (e k)) • (Gd (bs.coord k) - b (e k) • y (e k)) =
          Fd (bs.coord k) - (a (e k) / b (e k)) • Gd (bs.coord k) := by
        rw [smul_sub, smul_smul, div_mul_cancel₀ _ hb0]
        abel
      rw [h1, map_sub, map_smul, hΦF, hΦG, smul_zero, sub_zero]
  have hall : ∀ θ, Gd θ ∈ Z' := by
    intro θ
    rw [← bs.sum_dual_apply_smul_coord θ, map_sum]
    exact Submodule.sum_mem _ fun k _ => by
      rw [map_smul]
      exact Z'.smul_mem _ (hkey k)
  have hq' : q ≤ finrank ℂ Z' := by
    let emb : Fin q → Fin n := fun i => ⟨n - q + i.1, by omega⟩
    have hemb : Function.Injective emb := by
      intro i i' h
      have h' : n - q + i.1 = n - q + i'.1 := congrArg Fin.val h
      exact Fin.ext (by omega)
    have hli2 : LinearIndependent ℂ (fun i : Fin q => (Pi.basisFun ℂ (Fin n)) (emb i)) :=
      (Pi.basisFun ℂ (Fin n)).linearIndependent.comp emb hemb
    have hle : Submodule.span ℂ (Set.range fun i : Fin q => (Pi.basisFun ℂ (Fin n)) (emb i))
        ≤ Z' := by
      rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      show (Pi.basisFun ℂ (Fin n)) (emb i) ∈ Z'
      have h1 : (Pi.basisFun ℂ (Fin n)) (emb i) =
          Gd (LinearMap.proj (⟨i.1, by omega⟩ : Fin m)) := by
        funext j
        rw [hGdj]
        simp only [Pi.basisFun_apply, Pi.single_apply, LinearMap.proj_apply, hcB, emb,
          Fin.ext_iff]
        by_cases h : j.1 = n - q + i.1
        · rw [if_pos h, if_pos ⟨i.2, h⟩]
        · rw [if_neg h, if_neg (fun h' => h h'.2)]
      rw [h1]
      exact hall _
    have h := Submodule.finrank_mono hle
    rw [finrank_span_eq_card hli2, Fintype.card_fin] at h
    exact h
  omega

/-- The extremal tensor: slices `[I 0]` and a shifted partial identity. -/
def T0 (m n q : ℕ) : Holor ℂ [2, m, n] := fun t =>
  if (idxHead t).1 = 0 then
    (if (idxHead (idxTail (idxTail t))).1 = (idxHead (idxTail t)).1 then 1 else 0)
  else
    (if (idxHead (idxTail t)).1 < q ∧
      (idxHead (idxTail (idxTail t))).1 = n - q + (idxHead (idxTail t)).1 then 1 else 0)

theorem ev_T0_zero (m n q : ℕ) (i : Fin m) (j : Fin n) :
    ev (T0 m n q) 0 i j = if j.1 = i.1 then 1 else 0 :=
  rfl

theorem ev_T0_one (m n q : ℕ) (i : Fin m) (j : Fin n) :
    ev (T0 m n q) 1 i j = if i.1 < q ∧ j.1 = n - q + i.1 then 1 else 0 :=
  rfl

theorem le_cprank_T0 {m n q : ℕ} (hq : q ≤ m) (hmn : m ≤ n) (h2q : 2 * q ≤ n) :
    m + q ≤ (T0 m n q).cprank := by
  obtain ⟨u, v, w, h⟩ := exists_sum_of_cprank (T0 m n q)
  refine lower_core hq hmn h2q (fun l => u l 0) (fun l => u l 1) v w ?_ ?_
  · intro i j
    rw [← ev_T0_zero m n q i j, h]
  · intro i j
    rw [← ev_T0_one m n q i j, h]

theorem main {m n : ℕ} (hmn : m ≤ n) :
    Arxiv.«0805.3777».IsMaxRank [2, m, n] (m + min m (n / 2)) := by
  refine ⟨⟨T0 m n (min m (n / 2)), ?_⟩, ?_⟩
  · show (T0 m n (min m (n / 2))).cprank = m + min m (n / 2)
    refine le_antisymm (cprank_le _) (le_cprank_T0 (min_le_left _ _) hmn ?_)
    have h := min_le_right m (n / 2)
    omega
  · rintro _ ⟨T, rfl⟩
    exact cprank_le T

end Lower

end F1

theorem OMA.solution : type_of% @Arxiv.«0805.3777».isMaxRank_two := by
  intro m n _ hmn
  exact F1.main hmn
