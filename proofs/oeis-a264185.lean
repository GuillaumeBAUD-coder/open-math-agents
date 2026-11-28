import OMAStatements.S_oeis_a264185

-- Problem: OEIS A264185: (n+1) x 4 arrays of permutations with moves {±(0,0), ±(1,-1), ±(2,2)}
-- Credit: @ceejcake
-- Proof:
-- 1. Every allowed move preserves `(r + c) % 4`, so `a n = ∏ m : Fin 4, permCount (compAdj m) (n + 1)`
--    where each component is canonically indexed by `Fin (n + 1)` via `r ↦ (r, colOf m r)`.
-- 2. Prove the general bridge-splitting theorem for cycle covers (`permCount`):
--      if `(k-1) — k` is the sole edge between `< k` and `≥ k`, then
--      `permCount E N = permCount E k * permCount (shiftE E k) (N - k) +
--                       permCount E (k - 1) * permCount (shiftE E (k + 1)) (N - (k + 1))`.
-- 3. Each component `compAdj m` is periodic of period 4 and consists of 4-cycles linked by single
--    bridges; the bridge transfer matrix `[[9, 3], [3, 1]]` has rank 1 and eigenvalue 10, yielding
--    `permCount (compAdj m) (N + 4) = 10 * permCount (compAdj m) N` for all `N ≥ 5`, hence
--    `a (n + 4) = 10000 * a n` for `n ≥ 4`, the closed form, recurrence, and generating function.

namespace ProofA264185

open OMA.S_oeis_a264185 PowerSeries

-- Part 1: General permutation-count and bridge-splitting engine

private noncomputable def permCount (E : ℕ → ℕ → Prop) [DecidableRel E] (N : ℕ) : ℕ :=
  Nat.card {σ : Equiv.Perm (Fin N) // ∀ i : Fin N, E i.1 (σ i).1}

private lemma permCount_eq_fintype (E : ℕ → ℕ → Prop) [DecidableRel E] (N : ℕ) :
    permCount E N = Fintype.card {σ : Equiv.Perm (Fin N) // ∀ i : Fin N, E i.1 (σ i).1} :=
  Nat.card_eq_fintype_card

private def shiftE (E : ℕ → ℕ → Prop) (a : ℕ) (i j : ℕ) : Prop := E (a + i) (a + j)

private instance (E : ℕ → ℕ → Prop) [DecidableRel E] (a : ℕ) : DecidableRel (shiftE E a) :=
  fun i j => inferInstanceAs (Decidable (E (a + i) (a + j)))

private lemma permCount_congr {E₁ E₂ : ℕ → ℕ → Prop} [DecidableRel E₁] [DecidableRel E₂] {N : ℕ}
    (h : ∀ i < N, ∀ j < N, E₁ i j ↔ E₂ i j) : permCount E₁ N = permCount E₂ N := by
  simp only [permCount_eq_fintype]
  exact Fintype.card_congr (Equiv.subtypeEquivRight fun σ =>
    ⟨fun h1 i => (h i.1 i.2 (σ i).1 (σ i).2).mp (h1 i),
     fun h2 i => (h i.1 i.2 (σ i).1 (σ i).2).mpr (h2 i)⟩)

private lemma permCount_zero (E : ℕ → ℕ → Prop) [DecidableRel E] : permCount E 0 = 1 := by
  rw [permCount_eq_fintype]
  have : Unique {σ : Equiv.Perm (Fin 0) // ∀ i : Fin 0, E i.1 (σ i).1} :=
    { default := ⟨Equiv.refl _, fun i => i.elim0⟩
      uniq := fun ⟨σ, _⟩ => Subtype.ext (Equiv.ext fun i => i.elim0) }
  exact Fintype.card_unique

private lemma permCount_one (E : ℕ → ℕ → Prop) [DecidableRel E] (hrefl : E 0 0) :
    permCount E 1 = 1 := by
  rw [permCount_eq_fintype]
  have : Unique {σ : Equiv.Perm (Fin 1) // ∀ i : Fin 1, E i.1 (σ i).1} :=
    { default := ⟨Equiv.refl _, fun i => by fin_cases i; exact hrefl⟩
      uniq := fun ⟨σ, _⟩ => Subtype.ext (Equiv.ext fun i => by fin_cases i; exact Subsingleton.elim _ _) }
  exact Fintype.card_unique

private lemma bridge_no_cross {E : ℕ → ℕ → Prop} {N k : ℕ}
    (hk1 : 1 ≤ k) (hkN : k < N)
    (hLR : ∀ i < k, ∀ j, k ≤ j → j < N → E i j → i = k - 1 ∧ j = k)
    (σ : Equiv.Perm (Fin N)) (hσ : ∀ i, E i.1 (σ i).1)
    (hlt : (σ ⟨k - 1, by omega⟩).1 < k) :
    (∀ i : Fin N, i.1 < k → (σ i).1 < k) ∧ (∀ j : Fin N, k ≤ j.1 → k ≤ (σ j).1) := by
  classical
  have hL : ∀ i : Fin N, i.1 < k → (σ i).1 < k := by
    intro i hi
    by_contra hge
    push Not at hge
    have ⟨h1, _⟩ := hLR i.1 hi (σ i).1 hge (σ i).2 (hσ i)
    have hi_eq : i = ⟨k - 1, by omega⟩ := Fin.ext h1
    rw [hi_eq] at hge; omega
  have hR : ∀ j : Fin N, k ≤ j.1 → k ≤ (σ j).1 := by
    intro j hj
    by_contra hltj
    push Not at hltj
    let S : Finset (Fin N) := Finset.univ.filter (fun i : Fin N => i.1 < k)
    have hmaps : Finset.image σ S ⊆ S := by
      intro x hx
      rcases Finset.mem_image.mp hx with ⟨i, hi, rfl⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hL i (Finset.mem_filter.mp hi).2⟩
    have hcard : (Finset.image σ S).card = S.card :=
      Finset.card_image_of_injective S σ.injective
    have heqS : Finset.image σ S = S := Finset.eq_of_subset_of_card_le hmaps (by omega)
    have hmem : σ j ∈ Finset.image σ S := by
      rw [heqS]; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hltj⟩
    rcases Finset.mem_image.mp hmem with ⟨i, hi, hij⟩
    have := σ.injective hij
    subst this
    have := (Finset.mem_filter.mp hi).2
    omega
  exact ⟨hL, hR⟩

private lemma bridge_cross {E : ℕ → ℕ → Prop} {N k : ℕ}
    (hk1 : 1 ≤ k) (hkN : k < N)
    (hLR : ∀ i < k, ∀ j, k ≤ j → j < N → E i j → i = k - 1 ∧ j = k)
    (hRL : ∀ j, k ≤ j → j < N → ∀ i < k, E j i → j = k ∧ i = k - 1)
    (σ : Equiv.Perm (Fin N)) (hσ : ∀ i, E i.1 (σ i).1)
    (hge : k ≤ (σ ⟨k - 1, by omega⟩).1) :
    σ ⟨k - 1, by omega⟩ = ⟨k, by omega⟩ ∧ σ ⟨k, by omega⟩ = ⟨k - 1, by omega⟩ ∧
    (∀ i : Fin N, i.1 < k - 1 → (σ i).1 < k - 1) ∧
    (∀ j : Fin N, k + 1 ≤ j.1 → k + 1 ≤ (σ j).1) := by
  classical
  have h1 : σ ⟨k - 1, by omega⟩ = ⟨k, by omega⟩ := by
    have ⟨_, hval⟩ := hLR (k - 1) (by omega) (σ ⟨k - 1, by omega⟩).1 hge (σ _).2 (hσ ⟨k - 1, by omega⟩)
    exact Fin.ext hval
  have hLlt : ∀ i : Fin N, i.1 < k - 1 → (σ i).1 < k := by
    intro i hi
    by_contra hgei; push Not at hgei
    have ⟨heq, _⟩ := hLR i.1 (by omega) (σ i).1 hgei (σ i).2 (hσ i)
    omega
  have hex : ∃ j : Fin N, k ≤ j.1 ∧ (σ j).1 < k := by
    by_contra hnone; push Not at hnone
    let S : Finset (Fin N) := Finset.univ.filter (fun i : Fin N => i.1 < k)
    let T : Finset (Fin N) := Finset.univ.filter (fun i : Fin N => i.1 < k - 1)
    have hsub : S ⊆ Finset.image σ T := by
      intro x hx
      have hxk := (Finset.mem_filter.mp hx).2
      have hpre_lt : (σ.symm x).1 < k := by
        by_contra hgep; push Not at hgep
        have := hnone (σ.symm x) hgep
        simp at this; omega
      have hpre_ne : (σ.symm x).1 ≠ k - 1 := by
        intro heq
        have : σ.symm x = ⟨k - 1, by omega⟩ := Fin.ext heq
        have hx_eq : x = σ ⟨k - 1, by omega⟩ := by rw [← this]; simp
        rw [hx_eq, h1] at hxk; simp at hxk
      exact Finset.mem_image.mpr ⟨σ.symm x, Finset.mem_filter.mpr ⟨Finset.mem_univ _, by omega⟩, by simp⟩
    have hcard_le := Finset.card_le_card hsub
    rw [Finset.card_image_of_injective _ σ.injective] at hcard_le
    have hS_gt : T.card < S.card := by
      apply Finset.card_lt_card
      rw [Finset.ssubset_iff_subset_ne]
      refine ⟨fun x hx => Finset.mem_filter.mpr ⟨Finset.mem_univ _, by have := (Finset.mem_filter.mp hx).2; omega⟩, ?_⟩
      intro heq
      have hmem : (⟨k - 1, by omega⟩ : Fin N) ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ _, by dsimp only; omega⟩
      rw [← heq] at hmem
      have := (Finset.mem_filter.mp hmem).2; dsimp only at this; omega
    omega
  rcases hex with ⟨j0, hj0_ge, hj0_lt⟩
  have ⟨hj0_eq, hsig_eq⟩ := hRL j0.1 hj0_ge j0.2 (σ j0).1 hj0_lt (hσ j0)
  have h2 : σ ⟨k, by omega⟩ = ⟨k - 1, by omega⟩ := by
    have : j0 = ⟨k, by omega⟩ := Fin.ext hj0_eq
    rw [← this]; exact Fin.ext hsig_eq
  have hL : ∀ i : Fin N, i.1 < k - 1 → (σ i).1 < k - 1 := by
    intro i hi
    have hlt := hLlt i hi
    have hne : (σ i).1 ≠ k - 1 := by
      intro heq
      have : σ i = σ ⟨k, by omega⟩ := by rw [h2]; exact Fin.ext heq
      have := σ.injective this
      have : i.1 = k := congr_arg Fin.val this
      omega
    omega
  have hR : ∀ j : Fin N, k + 1 ≤ j.1 → k + 1 ≤ (σ j).1 := by
    intro j hj
    have hge_k : k ≤ (σ j).1 := by
      by_contra hltj; push Not at hltj
      have ⟨heq, _⟩ := hRL j.1 (by omega) j.2 (σ j).1 hltj (hσ j)
      omega
    have hne_k : (σ j).1 ≠ k := by
      intro heq
      have : σ j = σ ⟨k - 1, by omega⟩ := by rw [h1]; exact Fin.ext heq
      have := σ.injective this
      have : j.1 = k - 1 := congr_arg Fin.val this
      omega
    omega
  exact ⟨h1, h2, hL, hR⟩

private def permJoinNoCross {N k : ℕ} (hkN : k ≤ N)
    (τ : Equiv.Perm (Fin k)) (ρ : Equiv.Perm (Fin (N - k))) : Equiv.Perm (Fin N) where
  toFun i :=
    if hi : i.1 < k then ⟨(τ ⟨i.1, hi⟩).1, by omega⟩
    else ⟨k + (ρ ⟨i.1 - k, by omega⟩).1, by omega⟩
  invFun i :=
    if hi : i.1 < k then ⟨(τ.symm ⟨i.1, hi⟩).1, by omega⟩
    else ⟨k + (ρ.symm ⟨i.1 - k, by omega⟩).1, by omega⟩
  left_inv i := by
    by_cases hi : i.1 < k
    · simp [hi]
    · have hge : ¬ k + (ρ ⟨i.1 - k, by omega⟩).1 < k := by omega
      simp only [hi, hge, ↓reduceDIte]
      apply Fin.ext; dsimp only
      have hfin : (⟨k + (ρ ⟨i.1 - k, by omega⟩).1 - k, by omega⟩ : Fin (N - k)) = ρ ⟨i.1 - k, by omega⟩ :=
        Fin.ext (by dsimp only; omega)
      rw [hfin, ρ.symm_apply_apply]; dsimp only; omega
  right_inv i := by
    by_cases hi : i.1 < k
    · simp [hi]
    · have hge : ¬ k + (ρ.symm ⟨i.1 - k, by omega⟩).1 < k := by omega
      simp only [hi, hge, ↓reduceDIte]
      apply Fin.ext; dsimp only
      have hfin : (⟨k + (ρ.symm ⟨i.1 - k, by omega⟩).1 - k, by omega⟩ : Fin (N - k)) = ρ.symm ⟨i.1 - k, by omega⟩ :=
        Fin.ext (by dsimp only; omega)
      rw [hfin, ρ.apply_symm_apply]; dsimp only; omega

private def permJoinCross {N k : ℕ} (hk1 : 1 ≤ k) (hkN : k < N)
    (τ : Equiv.Perm (Fin (k - 1))) (ρ : Equiv.Perm (Fin (N - (k + 1)))) : Equiv.Perm (Fin N) where
  toFun i :=
    if hi1 : i.1 < k - 1 then ⟨(τ ⟨i.1, hi1⟩).1, by omega⟩
    else if hi2 : i.1 = k - 1 then ⟨k, by omega⟩
    else if hi3 : i.1 = k then ⟨k - 1, by omega⟩
    else ⟨k + 1 + (ρ ⟨i.1 - (k + 1), by omega⟩).1, by omega⟩
  invFun i :=
    if hi1 : i.1 < k - 1 then ⟨(τ.symm ⟨i.1, hi1⟩).1, by omega⟩
    else if hi2 : i.1 = k - 1 then ⟨k, by omega⟩
    else if hi3 : i.1 = k then ⟨k - 1, by omega⟩
    else ⟨k + 1 + (ρ.symm ⟨i.1 - (k + 1), by omega⟩).1, by omega⟩
  left_inv i := by
    by_cases hi1 : i.1 < k - 1
    · simp [hi1]
    · by_cases hi2 : i.1 = k - 1
      · simp only [hi1, ↓reduceDIte]; simp only [hi2, ↓reduceDIte]
        have hk1' : ¬ k < k - 1 := by omega
        have hk2' : k ≠ k - 1 := by omega
        simp only [hk1', hk2', ↓reduceDIte]
        exact Fin.ext hi2.symm
      · by_cases hi3 : i.1 = k
        · simp only [hi1, ↓reduceDIte]; simp only [hi2, ↓reduceDIte]; simp only [hi3, ↓reduceDIte]
          have hk1' : ¬ k - 1 < k - 1 := by omega
          simp only [hk1', ↓reduceDIte]
          exact Fin.ext hi3.symm
        · simp only [hi1, hi2, hi3, ↓reduceDIte]
          have hge1 : ¬ k + 1 + (ρ ⟨i.1 - (k + 1), by omega⟩).1 < k - 1 := by omega
          have hge2 : k + 1 + (ρ ⟨i.1 - (k + 1), by omega⟩).1 ≠ k - 1 := by omega
          have hge3 : k + 1 + (ρ ⟨i.1 - (k + 1), by omega⟩).1 ≠ k := by omega
          simp only [hge1, hge2, hge3, ↓reduceDIte]
          apply Fin.ext; dsimp only
          have hfin : (⟨k + 1 + (ρ ⟨i.1 - (k + 1), by omega⟩).1 - (k + 1), by omega⟩ : Fin (N - (k + 1))) =
              ρ ⟨i.1 - (k + 1), by omega⟩ := Fin.ext (by dsimp only; omega)
          rw [hfin, ρ.symm_apply_apply]; dsimp only; omega
  right_inv i := by
    by_cases hi1 : i.1 < k - 1
    · simp [hi1]
    · by_cases hi2 : i.1 = k - 1
      · simp only [hi1, ↓reduceDIte]; simp only [hi2, ↓reduceDIte]
        have hk1' : ¬ k < k - 1 := by omega
        have hk2' : k ≠ k - 1 := by omega
        simp only [hk1', hk2', ↓reduceDIte]
        exact Fin.ext hi2.symm
      · by_cases hi3 : i.1 = k
        · simp only [hi1, ↓reduceDIte]; simp only [hi2, ↓reduceDIte]; simp only [hi3, ↓reduceDIte]
          have hk1' : ¬ k - 1 < k - 1 := by omega
          simp only [hk1', ↓reduceDIte]
          exact Fin.ext hi3.symm
        · simp only [hi1, hi2, hi3, ↓reduceDIte]
          have hge1 : ¬ k + 1 + (ρ.symm ⟨i.1 - (k + 1), by omega⟩).1 < k - 1 := by omega
          have hge2 : k + 1 + (ρ.symm ⟨i.1 - (k + 1), by omega⟩).1 ≠ k - 1 := by omega
          have hge3 : k + 1 + (ρ.symm ⟨i.1 - (k + 1), by omega⟩).1 ≠ k := by omega
          simp only [hge1, hge2, hge3, ↓reduceDIte]
          apply Fin.ext; dsimp only
          have hfin : (⟨k + 1 + (ρ.symm ⟨i.1 - (k + 1), by omega⟩).1 - (k + 1), by omega⟩ : Fin (N - (k + 1))) =
              ρ.symm ⟨i.1 - (k + 1), by omega⟩ := Fin.ext (by dsimp only; omega)
          rw [hfin, ρ.apply_symm_apply]; dsimp only; omega

/-- General bridge-splitting lemma for cycle covers (permutations respecting `E`). -/
private lemma bridge_split (E : ℕ → ℕ → Prop) [DecidableRel E] {N k : ℕ}
    (hk1 : 1 ≤ k) (hkN : k < N)
    (hLR : ∀ i < k, ∀ j, k ≤ j → j < N → E i j → i = k - 1 ∧ j = k)
    (hRL : ∀ j, k ≤ j → j < N → ∀ i < k, E j i → j = k ∧ i = k - 1)
    (heLR : E (k - 1) k) (heRL : E k (k - 1)) :
    permCount E N =
      permCount E k * permCount (shiftE E k) (N - k) +
      permCount E (k - 1) * permCount (shiftE E (k + 1)) (N - (k + 1)) := by
  let A := {σ : Equiv.Perm (Fin N) // ∀ i : Fin N, E i.1 (σ i).1}
  let P1 := {τ : Equiv.Perm (Fin k) // ∀ i, E i.1 (τ i).1} ×
            {ρ : Equiv.Perm (Fin (N - k)) // ∀ i, shiftE E k i.1 (ρ i).1}
  let P2 := {τ : Equiv.Perm (Fin (k - 1)) // ∀ i, E i.1 (τ i).1} ×
            {ρ : Equiv.Perm (Fin (N - (k + 1))) // ∀ i, shiftE E (k + 1) i.1 (ρ i).1}
  let invF : P1 ⊕ P2 → A := fun s =>
    match s with
    | Sum.inl (⟨τ, hτ⟩, ⟨ρ, hρ⟩) =>
      ⟨permJoinNoCross (by omega) τ ρ, fun i => by
        simp only [permJoinNoCross, Equiv.coe_fn_mk]
        by_cases hi : i.1 < k
        · simp only [hi, ↓reduceDIte]; exact hτ ⟨i.1, hi⟩
        · simp only [hi, ↓reduceDIte]
          have h := hρ ⟨i.1 - k, by omega⟩
          dsimp only [shiftE] at h
          have hadd : k + (i.1 - k) = i.1 := by omega
          rwa [hadd] at h⟩
    | Sum.inr (⟨τ, hτ⟩, ⟨ρ, hρ⟩) =>
      ⟨permJoinCross hk1 hkN τ ρ, fun i => by
        simp only [permJoinCross, Equiv.coe_fn_mk]
        by_cases hi1 : i.1 < k - 1
        · simp only [hi1, ↓reduceDIte]; exact hτ ⟨i.1, hi1⟩
        · by_cases hi2 : i.1 = k - 1
          · simp only [hi1, ↓reduceDIte]; simp only [hi2, ↓reduceDIte]; exact heLR
          · by_cases hi3 : i.1 = k
            · simp only [hi1, ↓reduceDIte]; simp only [hi2, ↓reduceDIte]; simp only [hi3, ↓reduceDIte]; exact heRL
            · simp only [hi1, hi2, hi3, ↓reduceDIte]
              have h := hρ ⟨i.1 - (k + 1), by omega⟩
              dsimp only [shiftE] at h
              have hadd : k + 1 + (i.1 - (k + 1)) = i.1 := by omega
              rwa [hadd] at h⟩
  have hbij : Function.Bijective invF := by
    constructor
    · intro s1 s2 heq
      have hval : (invF s1).1 = (invF s2).1 := congr_arg Subtype.val heq
      rcases s1 with ⟨⟨τ1, _⟩, ⟨ρ1, _⟩⟩ | ⟨⟨τ1, _⟩, ⟨ρ1, _⟩⟩ <;>
      rcases s2 with ⟨⟨τ2, _⟩, ⟨ρ2, _⟩⟩ | ⟨⟨τ2, _⟩, ⟨ρ2, _⟩⟩
      · congr 1; apply Prod.ext
        · apply Subtype.ext; apply Equiv.ext; intro i
          have h := congr_arg (fun f => f ⟨i.1, by omega⟩) hval
          have hi : i.1 < k := i.2
          simp [invF, permJoinNoCross, hi] at h; exact Fin.ext h
        · apply Subtype.ext; apply Equiv.ext; intro i
          have h := congr_arg (fun f => f ⟨k + i.1, by omega⟩) hval
          have hi : ¬ k + i.1 < k := by omega
          simp [invF, permJoinNoCross, hi] at h; exact Fin.ext h
      · exfalso
        have h := congr_arg (fun f => (f ⟨k - 1, by omega⟩).1) hval
        simp [invF, permJoinNoCross, permJoinCross, show k - 1 < k by omega] at h
        have := (τ1 ⟨k - 1, by omega⟩).2; omega
      · exfalso
        have h := congr_arg (fun f => (f ⟨k - 1, by omega⟩).1) hval
        simp [invF, permJoinNoCross, permJoinCross, show k - 1 < k by omega] at h
        have := (τ2 ⟨k - 1, by omega⟩).2; omega
      · congr 1; apply Prod.ext
        · apply Subtype.ext; apply Equiv.ext; intro i
          have h := congr_arg (fun f => f ⟨i.1, by omega⟩) hval
          have hi : i.1 < k - 1 := i.2
          simp [invF, permJoinCross, hi] at h; exact Fin.ext h
        · apply Subtype.ext; apply Equiv.ext; intro i
          have h := congr_arg (fun f => f ⟨k + 1 + i.1, by omega⟩) hval
          have h1 : ¬ k + 1 + i.1 < k - 1 := by omega
          have h2 : k + 1 + i.1 ≠ k - 1 := by omega
          have h3 : k + 1 + i.1 ≠ k := by omega
          simp [invF, permJoinCross, h1, h2, h3] at h; exact Fin.ext h
    · intro ⟨σ, hσ⟩
      by_cases hlt : (σ ⟨k - 1, by omega⟩).1 < k
      · have ⟨hL, hR⟩ := bridge_no_cross hk1 hkN hLR σ hσ hlt
        have hLinv : ∀ i : Fin N, i.1 < k → (σ.symm i).1 < k := by
          intro i hi; by_contra hge; push Not at hge
          have := hR (σ.symm i) hge; simp at this; omega
        have hRinv : ∀ j : Fin N, k ≤ j.1 → k ≤ (σ.symm j).1 := by
          intro j hj; by_contra hltj; push Not at hltj
          have := hL (σ.symm j) hltj; simp at this; omega
        let τ : Equiv.Perm (Fin k) :=
          { toFun := fun i => ⟨(σ ⟨i.1, by omega⟩).1, hL ⟨i.1, by omega⟩ i.2⟩
            invFun := fun i => ⟨(σ.symm ⟨i.1, by omega⟩).1, hLinv ⟨i.1, by omega⟩ i.2⟩
            left_inv := fun i => Fin.ext (by simp [σ.symm_apply_apply])
            right_inv := fun i => Fin.ext (by simp [σ.apply_symm_apply]) }
        let ρ : Equiv.Perm (Fin (N - k)) :=
          { toFun := fun i => ⟨(σ ⟨k + i.1, by omega⟩).1 - k, by
              have := hR ⟨k + i.1, by omega⟩ (by dsimp only; omega); omega⟩
            invFun := fun i => ⟨(σ.symm ⟨k + i.1, by omega⟩).1 - k, by
              have := hRinv ⟨k + i.1, by omega⟩ (by dsimp only; omega); omega⟩
            left_inv := fun i => Fin.ext (by
              have hge := hR ⟨k + i.1, by omega⟩ (by dsimp only; omega)
              have hfin : (⟨k + ((σ ⟨k + i.1, by omega⟩).1 - k), by omega⟩ : Fin N) = σ ⟨k + i.1, by omega⟩ :=
                Fin.ext (by dsimp only; omega)
              dsimp only; rw [hfin, σ.symm_apply_apply]; dsimp only; omega)
            right_inv := fun i => Fin.ext (by
              have hge := hRinv ⟨k + i.1, by omega⟩ (by dsimp only; omega)
              have hfin : (⟨k + ((σ.symm ⟨k + i.1, by omega⟩).1 - k), by omega⟩ : Fin N) = σ.symm ⟨k + i.1, by omega⟩ :=
                Fin.ext (by dsimp only; omega)
              dsimp only; rw [hfin, σ.apply_symm_apply]; dsimp only; omega) }
        refine ⟨Sum.inl (⟨τ, fun i => hσ ⟨i.1, by omega⟩⟩, ⟨ρ, fun i => by
          change E (k + i.1) (k + ((σ ⟨k + i.1, by omega⟩).1 - k))
          have hge := hR ⟨k + i.1, by omega⟩ (by dsimp only; omega)
          have hadd : k + ((σ ⟨k + i.1, by omega⟩).1 - k) = (σ ⟨k + i.1, by omega⟩).1 := by omega
          rw [hadd]; exact hσ ⟨k + i.1, by omega⟩⟩), ?_⟩
        apply Subtype.ext; apply Equiv.ext; intro i
        change (if hi : i.1 < k then ⟨(σ ⟨i.1, by omega⟩).1, by omega⟩
          else ⟨k + ((σ ⟨k + (i.1 - k), by omega⟩).1 - k), by omega⟩) = σ i
        by_cases hi : i.1 < k
        · simp only [hi, ↓reduceDIte]
        · simp only [hi, ↓reduceDIte]
          have hfin : (⟨k + (i.1 - k), by omega⟩ : Fin N) = i := Fin.ext (by dsimp only; omega)
          have hge := hR i (by omega)
          apply Fin.ext; dsimp only; rw [hfin]; omega
      · have ⟨h1, h2, hL, hR⟩ := bridge_cross hk1 hkN hLR hRL σ hσ (by omega)
        have hLinv : ∀ i : Fin N, i.1 < k - 1 → (σ.symm i).1 < k - 1 := by
          intro i hi; by_contra hgep; push Not at hgep
          by_cases heq1 : (σ.symm i).1 = k - 1
          · have htmp : σ.symm i = ⟨k - 1, by omega⟩ := Fin.ext heq1
            have : i = σ ⟨k - 1, by omega⟩ := by rw [← htmp]; simp
            rw [this, h1] at hi; dsimp only at hi; omega
          · by_cases heq2 : (σ.symm i).1 = k
            · have htmp : σ.symm i = ⟨k, by omega⟩ := Fin.ext heq2
              have : i = σ ⟨k, by omega⟩ := by rw [← htmp]; simp
              rw [this, h2] at hi; dsimp only at hi; omega
            · have := hR (σ.symm i) (by omega); simp at this; omega
        have hRinv : ∀ j : Fin N, k + 1 ≤ j.1 → k + 1 ≤ (σ.symm j).1 := by
          intro j hj; by_contra hltj; push Not at hltj
          by_cases heq1 : (σ.symm j).1 = k - 1
          · have htmp : σ.symm j = ⟨k - 1, by omega⟩ := Fin.ext heq1
            have : j = σ ⟨k - 1, by omega⟩ := by rw [← htmp]; simp
            rw [this, h1] at hj; dsimp only at hj; omega
          · by_cases heq2 : (σ.symm j).1 = k
            · have htmp : σ.symm j = ⟨k, by omega⟩ := Fin.ext heq2
              have : j = σ ⟨k, by omega⟩ := by rw [← htmp]; simp
              rw [this, h2] at hj; dsimp only at hj; omega
            · have := hL (σ.symm j) (by omega); simp at this; omega
        let τ : Equiv.Perm (Fin (k - 1)) :=
          { toFun := fun i => ⟨(σ ⟨i.1, by omega⟩).1, hL ⟨i.1, by omega⟩ i.2⟩
            invFun := fun i => ⟨(σ.symm ⟨i.1, by omega⟩).1, hLinv ⟨i.1, by omega⟩ i.2⟩
            left_inv := fun i => Fin.ext (by simp [σ.symm_apply_apply])
            right_inv := fun i => Fin.ext (by simp [σ.apply_symm_apply]) }
        let ρ : Equiv.Perm (Fin (N - (k + 1))) :=
          { toFun := fun i => ⟨(σ ⟨k + 1 + i.1, by omega⟩).1 - (k + 1), by
              have := hR ⟨k + 1 + i.1, by omega⟩ (by dsimp only; omega); omega⟩
            invFun := fun i => ⟨(σ.symm ⟨k + 1 + i.1, by omega⟩).1 - (k + 1), by
              have := hRinv ⟨k + 1 + i.1, by omega⟩ (by dsimp only; omega); omega⟩
            left_inv := fun i => Fin.ext (by
              have hgeR := hR ⟨k + 1 + i.1, by omega⟩ (by dsimp only; omega)
              have hfin : (⟨k + 1 + ((σ ⟨k + 1 + i.1, by omega⟩).1 - (k + 1)), by omega⟩ : Fin N) = σ ⟨k + 1 + i.1, by omega⟩ :=
                Fin.ext (by dsimp only; omega)
              dsimp only; rw [hfin, σ.symm_apply_apply]; dsimp only; omega)
            right_inv := fun i => Fin.ext (by
              have hgeR := hRinv ⟨k + 1 + i.1, by omega⟩ (by dsimp only; omega)
              have hfin : (⟨k + 1 + ((σ.symm ⟨k + 1 + i.1, by omega⟩).1 - (k + 1)), by omega⟩ : Fin N) = σ.symm ⟨k + 1 + i.1, by omega⟩ :=
                Fin.ext (by dsimp only; omega)
              dsimp only; rw [hfin, σ.apply_symm_apply]; dsimp only; omega) }
        refine ⟨Sum.inr (⟨τ, fun i => hσ ⟨i.1, by omega⟩⟩, ⟨ρ, fun i => by
          change E (k + 1 + i.1) (k + 1 + ((σ ⟨k + 1 + i.1, by omega⟩).1 - (k + 1)))
          have hgeR := hR ⟨k + 1 + i.1, by omega⟩ (by dsimp only; omega)
          have hadd : k + 1 + ((σ ⟨k + 1 + i.1, by omega⟩).1 - (k + 1)) = (σ ⟨k + 1 + i.1, by omega⟩).1 := by omega
          rw [hadd]; exact hσ ⟨k + 1 + i.1, by omega⟩⟩), ?_⟩
        apply Subtype.ext; apply Equiv.ext; intro i
        change (if hi1 : i.1 < k - 1 then ⟨(σ ⟨i.1, by omega⟩).1, by omega⟩
          else if hi2 : i.1 = k - 1 then ⟨k, by omega⟩
          else if hi3 : i.1 = k then ⟨k - 1, by omega⟩
          else ⟨k + 1 + ((σ ⟨k + 1 + (i.1 - (k + 1)), by omega⟩).1 - (k + 1)), by omega⟩) = σ i
        by_cases hi1 : i.1 < k - 1
        · simp only [hi1, ↓reduceDIte]
        · by_cases hi2 : i.1 = k - 1
          · simp only [hi1, ↓reduceDIte]; simp only [hi2, ↓reduceDIte]
            have hi_eq : i = ⟨k - 1, by omega⟩ := Fin.ext hi2
            exact ((congr_arg σ hi_eq).trans h1).symm
          · by_cases hi3 : i.1 = k
            · simp only [hi1, ↓reduceDIte]; simp only [hi2, ↓reduceDIte]; simp only [hi3, ↓reduceDIte]
              have hi_eq : i = ⟨k, by omega⟩ := Fin.ext hi3
              exact ((congr_arg σ hi_eq).trans h2).symm
            · simp only [hi1, hi2, hi3, ↓reduceDIte]
              have hfin : (⟨k + 1 + (i.1 - (k + 1)), by omega⟩ : Fin N) = i := Fin.ext (by dsimp only; omega)
              have hgeR := hR i (by omega)
              apply Fin.ext; dsimp only; rw [hfin]; omega
  have hc := Fintype.card_congr (Equiv.ofBijective invF hbij)
  rw [Fintype.card_sum, Fintype.card_prod, Fintype.card_prod] at hc
  simp only [permCount_eq_fintype]
  exact hc.symm

-- Part 2: Component decomposition for A264185

private def colOf (m : Fin 4) (r : ℕ) : Fin 4 :=
  ⟨(m.1 + 4 - r % 4) % 4, Nat.mod_lt _ (by omega)⟩

private def compAdj (m : Fin 4) (i j : ℕ) : Prop :=
  i = j ∨
  (j = i + 1 ∧ (colOf m i).1 ≠ 0) ∨
  (i = j + 1 ∧ (colOf m j).1 ≠ 0) ∨
  (j = i + 2 ∧ (colOf m i).1 ≤ 1) ∨
  (i = j + 2 ∧ (colOf m j).1 ≤ 1)

private instance (m : Fin 4) : DecidableRel (compAdj m) := fun i j => by
  unfold compAdj; infer_instance

private lemma compAdj_period4 (m : Fin 4) (i j : ℕ) :
    compAdj m (i + 4) (j + 4) ↔ compAdj m i j := by
  unfold compAdj colOf
  have hi : (i + 4) % 4 = i % 4 := by omega
  have hj : (j + 4) % 4 = j % 4 := by omega
  simp only [hi, hj]
  omega

private def gridEquiv (n : ℕ) : Fin (n + 1) × Fin 4 ≃ Fin 4 × Fin (n + 1) where
  toFun p := (⟨(p.1.1 + p.2.1) % 4, Nat.mod_lt _ (by omega)⟩, p.1)
  invFun q := (q.2, colOf q.1 q.2.1)
  left_inv p := by
    apply Prod.ext
    · rfl
    · apply Fin.ext; dsimp only [colOf]; omega
  right_inv q := by
    apply Prod.ext
    · apply Fin.ext; dsimp only [colOf]; omega
    · rfl

private lemma validMove_iff_compAdj {n : ℕ} (q₁ q₂ : Fin 4 × Fin (n + 1)) :
    validMove ((gridEquiv n).symm q₁) ((gridEquiv n).symm q₂) ↔
      q₁.1 = q₂.1 ∧ compAdj q₁.1 q₁.2.1 q₂.2.1 := by
  rcases q₁ with ⟨m₁, r₁⟩
  rcases q₂ with ⟨m₂, r₂⟩
  have hsymm : ∀ m r, (gridEquiv n).symm (m, r) = (r, colOf m r.1) := fun _ _ => rfl
  rw [hsymm, hsymm]
  unfold validMove compAdj colOf
  dsimp only
  constructor
  · intro h
    have hm : m₁ = m₂ := by apply Fin.ext; omega
    subst hm
    refine ⟨rfl, ?_⟩
    rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega
  · rintro ⟨rfl, h⟩
    rcases h with h | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega

private lemma a_eq_prod (n : ℕ) (hn : 1 ≤ n) :
    a n = ∏ m : Fin 4, permCount (compAdj m) (n + 1) := by
  have hne : n ≠ 0 := by omega
  unfold a
  simp only [hne, ↓reduceIte]
  let e1 : {σ : Equiv.Perm (Fin (n + 1) × Fin 4) // ∀ p, validMove p (σ p)} ≃
      {σ : Equiv.Perm (Fin 4 × Fin (n + 1)) // ∀ q, q.1 = (σ q).1 ∧ compAdj q.1 q.2.1 (σ q).2.1} :=
    { toFun := fun ⟨σ, hσ⟩ =>
        ⟨(gridEquiv n).symm.trans (σ.trans (gridEquiv n)), fun q => by
          have h := hσ ((gridEquiv n).symm q)
          rw [← validMove_iff_compAdj]
          simpa using h⟩
      invFun := fun ⟨σ, hσ⟩ =>
        ⟨(gridEquiv n).trans (σ.trans (gridEquiv n).symm), fun p => by
          have h := (validMove_iff_compAdj (gridEquiv n p) (σ (gridEquiv n p))).mpr (hσ (gridEquiv n p))
          simpa using h⟩
      left_inv := fun ⟨σ, _⟩ => Subtype.ext (Equiv.ext fun p => by simp)
      right_inv := fun ⟨σ, _⟩ => Subtype.ext (Equiv.ext fun q => by simp) }
  let e2 : {σ : Equiv.Perm (Fin 4 × Fin (n + 1)) // ∀ q, q.1 = (σ q).1 ∧ compAdj q.1 q.2.1 (σ q).2.1} ≃
      (∀ m : Fin 4, {τ : Equiv.Perm (Fin (n + 1)) // ∀ i : Fin (n + 1), compAdj m i.1 (τ i).1}) :=
    { toFun := fun ⟨σ, hσ⟩ m =>
        ⟨{ toFun := fun i => (σ (m, i)).2
           invFun := fun i => (σ.symm (m, i)).2
           left_inv := fun i => by
             dsimp only
             have hm : (σ (m, i)).1 = m := (hσ (m, i)).1.symm
             have hpair : (m, (σ (m, i)).2) = σ (m, i) := Prod.ext hm.symm rfl
             rw [hpair, σ.symm_apply_apply]
           right_inv := fun i => by
             dsimp only
             have hm : (σ.symm (m, i)).1 = m := by
               have := (hσ (σ.symm (m, i))).1
               simp at this; exact this
             have hpair : (m, (σ.symm (m, i)).2) = σ.symm (m, i) := Prod.ext hm.symm rfl
             rw [hpair, σ.apply_symm_apply] },
         fun i => (hσ (m, i)).2⟩
      invFun := fun f =>
        ⟨{ toFun := fun q => (q.1, (f q.1).1 q.2)
           invFun := fun q => (q.1, (f q.1).1.symm q.2)
           left_inv := fun ⟨m, i⟩ => by simp
           right_inv := fun ⟨m, i⟩ => by simp },
         fun ⟨m, i⟩ => ⟨rfl, (f m).2 i⟩⟩
      left_inv := fun ⟨σ, hσ⟩ => by
        apply Subtype.ext; apply Equiv.ext; intro ⟨m, i⟩
        exact Prod.ext (hσ (m, i)).1 rfl
      right_inv := fun f => by
        funext m; apply Subtype.ext; apply Equiv.ext; intro i; rfl }
  rw [Fintype.card_congr (e1.trans e2), Fintype.card_pi]
  simp only [permCount_eq_fintype]

-- Part 3: Bridge structure of `compAdj m` and 10x scaling per 4-cycle

private lemma compAdj_bridge (m : Fin 4) {N k : ℕ} (hk1 : 1 ≤ k) (hkN : k < N)
    (hcol : (colOf m (k - 1)).1 = 2) :
    permCount (compAdj m) N =
      permCount (compAdj m) k * permCount (shiftE (compAdj m) k) (N - k) +
      permCount (compAdj m) (k - 1) * permCount (shiftE (compAdj m) (k + 1)) (N - (k + 1)) := by
  dsimp only [colOf] at hcol
  apply bridge_split (compAdj m) hk1 hkN
  · intro i hi j hj _ hij
    dsimp only [compAdj, colOf] at hij
    rcases hij with h | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega
  · intro j hj _ i hi hji
    dsimp only [compAdj, colOf] at hji
    rcases hji with h | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega
  · dsimp only [compAdj, colOf]; right; left; omega
  · dsimp only [compAdj, colOf]; right; right; left; omega

-- Standard 4-cycle starting at col = 1 (`compAdj 1`): vertices 0..3 have cols 1, 0, 3, 2
private lemma shift_to_m1 (m : Fin 4) (k : ℕ) (hcol : (colOf m k).1 = 1) (i j : ℕ) :
    shiftE (compAdj m) k i j ↔ compAdj 1 i j := by
  dsimp only [colOf] at hcol
  unfold shiftE compAdj colOf
  have h : ∀ t, (m.1 + 4 - (k + t) % 4) % 4 = (1 + 4 - t % 4) % 4 := fun t => by omega
  simp only [h]
  omega

private lemma shift_to_m0 (m : Fin 4) (k : ℕ) (hcol : (colOf m k).1 = 0) (i j : ℕ) :
    shiftE (compAdj m) k i j ↔ compAdj 0 i j := by
  dsimp only [colOf] at hcol
  unfold shiftE compAdj colOf
  have h : ∀ t, (m.1 + 4 - (k + t) % 4) % 4 = (0 + 4 - t % 4) % 4 := fun t => by omega
  simp only [h]
  omega

-- Fast tuple-based evaluators for permCount at N = 2, 3, 4 (avoiding Equiv.Perm.fintype in decide)
private lemma permCount_eq_card2 (E : ℕ → ℕ → Prop) [DecidableRel E] :
    permCount E 2 = Fintype.card {p : Fin 2 × Fin 2 // p.1 ≠ p.2 ∧ E 0 p.1.1 ∧ E 1 p.2.1} := by
  rw [permCount_eq_fintype]
  refine Fintype.card_congr
    { toFun := fun ⟨σ, hσ⟩ => ⟨(σ 0, σ 1), σ.injective.ne (by decide), hσ 0, hσ 1⟩
      invFun := fun ⟨⟨a, b⟩, hne, h0, h1⟩ =>
        let f : Fin 2 → Fin 2 := fun i => if i = 0 then a else b
        have hinj : Function.Injective f := by
          intro i j hij; fin_cases i <;> fin_cases j <;> simp_all [f]
        ⟨Equiv.ofBijective f (Finite.injective_iff_bijective.mp hinj), fun i => by
          fin_cases i <;> simpa [f]⟩
      left_inv := fun ⟨σ, _⟩ => by
        apply Subtype.ext; apply Equiv.ext; intro i; fin_cases i <;> rfl
      right_inv := fun ⟨⟨a, b⟩, _, _, _⟩ => rfl }

private lemma permCount_eq_card3 (E : ℕ → ℕ → Prop) [DecidableRel E] :
    permCount E 3 = Fintype.card {p : Fin 3 × Fin 3 × Fin 3 //
      p.1 ≠ p.2.1 ∧ p.1 ≠ p.2.2 ∧ p.2.1 ≠ p.2.2 ∧ E 0 p.1.1 ∧ E 1 p.2.1.1 ∧ E 2 p.2.2.1} := by
  rw [permCount_eq_fintype]
  refine Fintype.card_congr
    { toFun := fun ⟨σ, hσ⟩ =>
        ⟨(σ 0, σ 1, σ 2), σ.injective.ne (by decide), σ.injective.ne (by decide),
          σ.injective.ne (by decide), hσ 0, hσ 1, hσ 2⟩
      invFun := fun ⟨⟨a, b, c⟩, h1, h2, h3, e0, e1, e2⟩ =>
        let f : Fin 3 → Fin 3 := fun i => match i with | 0 => a | 1 => b | 2 => c
        have hinj : Function.Injective f := by
          intro i j hij; fin_cases i <;> fin_cases j <;> simp_all [f]
        ⟨Equiv.ofBijective f (Finite.injective_iff_bijective.mp hinj), fun i => by
          fin_cases i <;> simpa [f]⟩
      left_inv := fun ⟨σ, _⟩ => by
        apply Subtype.ext; apply Equiv.ext; intro i; fin_cases i <;> rfl
      right_inv := fun ⟨⟨a, b, c⟩, _, _, _, _, _, _⟩ => rfl }

private lemma permCount_eq_card4 (E : ℕ → ℕ → Prop) [DecidableRel E] :
    permCount E 4 = Fintype.card {p : Fin 4 × Fin 4 × Fin 4 × Fin 4 //
      p.1 ≠ p.2.1 ∧ p.1 ≠ p.2.2.1 ∧ p.1 ≠ p.2.2.2 ∧
      p.2.1 ≠ p.2.2.1 ∧ p.2.1 ≠ p.2.2.2 ∧ p.2.2.1 ≠ p.2.2.2 ∧
      E 0 p.1.1 ∧ E 1 p.2.1.1 ∧ E 2 p.2.2.1.1 ∧ E 3 p.2.2.2.1} := by
  rw [permCount_eq_fintype]
  refine Fintype.card_congr
    { toFun := fun ⟨σ, hσ⟩ =>
        ⟨(σ 0, σ 1, σ 2, σ 3),
          σ.injective.ne (by decide), σ.injective.ne (by decide), σ.injective.ne (by decide),
          σ.injective.ne (by decide), σ.injective.ne (by decide), σ.injective.ne (by decide),
          hσ 0, hσ 1, hσ 2, hσ 3⟩
      invFun := fun ⟨⟨a, b, c, d⟩, h1, h2, h3, h4, h5, h6, e0, e1, e2, e3⟩ =>
        let f : Fin 4 → Fin 4 := fun i => match i with | 0 => a | 1 => b | 2 => c | 3 => d
        have hinj : Function.Injective f := by
          intro i j hij; fin_cases i <;> fin_cases j <;> simp_all [f]
        ⟨Equiv.ofBijective f (Finite.injective_iff_bijective.mp hinj), fun i => by
          fin_cases i <;> simpa [f]⟩
      left_inv := fun ⟨σ, _⟩ => by
        apply Subtype.ext; apply Equiv.ext; intro i; fin_cases i <;> rfl
      right_inv := fun ⟨⟨a, b, c, d⟩, _, _, _, _, _, _, _, _, _, _⟩ => rfl }

attribute [irreducible] permCount

-- Base counts (instant via expanded Fin.sum_univ_two / Fin.sum_univ_three + bridge_split!)
private lemma pc_m0_1 : permCount (compAdj 0) 1 = 1 := permCount_one _ (Or.inl rfl)
private lemma pc_m0_2 : permCount (compAdj 0) 2 = 1 := by
  rw [permCount_eq_card2, Fintype.card_subtype, Finset.card_filter, Fintype.sum_prod_type]
  simp only [Fin.sum_univ_two]; decide
private lemma pc_m0_3 : permCount (compAdj 0) 3 = 3 := by
  rw [permCount_eq_card3, Fintype.card_subtype, Finset.card_filter, Fintype.sum_prod_type]
  simp only [Fintype.sum_prod_type, Fin.sum_univ_three]; decide

private lemma pc_m1_1 : permCount (compAdj 1) 1 = 1 := permCount_one _ (Or.inl rfl)
private lemma pc_m1_2 : permCount (compAdj 1) 2 = 2 := by
  rw [permCount_eq_card2, Fintype.card_subtype, Finset.card_filter, Fintype.sum_prod_type]
  simp only [Fin.sum_univ_two]; decide
private lemma pc_m1_3 : permCount (compAdj 1) 3 = 3 := by
  rw [permCount_eq_card3, Fintype.card_subtype, Finset.card_filter, Fintype.sum_prod_type]
  simp only [Fintype.sum_prod_type, Fin.sum_univ_three]; decide
private lemma pc_m1_4 : permCount (compAdj 1) 4 = 9 := by
  have heq : permCount (compAdj 1) 4 = permCount (fun i j => i = j ∨ i + j ≠ 3) 4 :=
    permCount_congr (fun i hi j hj => by
      have h : ∀ a b : Fin 4, compAdj 1 a.1 b.1 ↔ a.1 = b.1 ∨ a.1 + b.1 ≠ 3 := by decide
      exact h ⟨i, hi⟩ ⟨j, hj⟩)
  rw [heq, permCount_eq_card4]
  let P (p : Fin 4 × Fin 4 × Fin 4 × Fin 4) : Prop :=
    p.1 ≠ p.2.1 ∧ p.1 ≠ p.2.2.1 ∧ p.1 ≠ p.2.2.2 ∧
    p.2.1 ≠ p.2.2.1 ∧ p.2.1 ≠ p.2.2.2 ∧ p.2.2.1 ≠ p.2.2.2 ∧
    (0 = p.1.1 ∨ 0 + p.1.1 ≠ 3) ∧ (1 = p.2.1.1 ∨ 1 + p.2.1.1 ≠ 3) ∧
    (2 = p.2.2.1.1 ∨ 2 + p.2.2.1.1 ≠ 3) ∧ (3 = p.2.2.2.1 ∨ 3 + p.2.2.2.1 ≠ 3)
  let list9 : Fin 9 → Fin 4 × Fin 4 × Fin 4 × Fin 4
    | 0 => (0, 1, 2, 3) | 1 => (0, 1, 3, 2) | 2 => (0, 3, 2, 1)
    | 3 => (1, 0, 2, 3) | 4 => (1, 0, 3, 2) | 5 => (1, 3, 0, 2)
    | 6 => (2, 0, 3, 1) | 7 => (2, 1, 0, 3) | 8 => (2, 3, 0, 1)
  have hP9 : ∀ i : Fin 9, P (list9 i) := by intro i; fin_cases i <;> decide
  let f : Fin 9 → {p : Fin 4 × Fin 4 × Fin 4 × Fin 4 // P p} := fun i => ⟨list9 i, hP9 i⟩
  have hbij : Function.Bijective f := by
    constructor
    · intro i j hij
      have h : ∀ x y : Fin 9, list9 x = list9 y → x = y := by decide
      exact h i j (congr_arg Subtype.val hij)
    · rintro ⟨⟨a, b, c, d⟩, h1, h2, h3, h4, h5, h6, e0, e1, e2, e3⟩
      fin_cases a
      · fin_cases b
        · exact absurd rfl h1
        · fin_cases c
          · exact absurd rfl h2
          · exact absurd rfl h4
          · fin_cases d
            · exact absurd rfl h3
            · exact absurd rfl h5
            · exact absurd rfl h6
            · exact ⟨0, rfl⟩
          · fin_cases d
            · exact absurd rfl h3
            · exact absurd rfl h5
            · exact ⟨1, rfl⟩
            · exact absurd rfl h6
        · exfalso; simp at e1
        · fin_cases c
          · exact absurd rfl h2
          · exfalso; simp at e2
          · fin_cases d
            · exact absurd rfl h3
            · exact ⟨2, rfl⟩
            · exact absurd rfl h6
            · exact absurd rfl h5
          · exact absurd rfl h4
      · fin_cases b
        · fin_cases c
          · exact absurd rfl h4
          · exact absurd rfl h2
          · fin_cases d
            · exact absurd rfl h5
            · exact absurd rfl h3
            · exact absurd rfl h6
            · exact ⟨3, rfl⟩
          · fin_cases d
            · exact absurd rfl h5
            · exact absurd rfl h3
            · exact ⟨4, rfl⟩
            · exact absurd rfl h6
        · exact absurd rfl h1
        · exfalso; simp at e1
        · fin_cases c
          · fin_cases d
            · exact absurd rfl h6
            · exact absurd rfl h3
            · exact ⟨5, rfl⟩
            · exact absurd rfl h5
          · exact absurd rfl h2
          · fin_cases d
            · exfalso; simp at e3
            · exact absurd rfl h3
            · exact absurd rfl h6
            · exact absurd rfl h5
          · exact absurd rfl h4
      · fin_cases b
        · fin_cases c
          · exact absurd rfl h4
          · exfalso; simp at e2
          · exact absurd rfl h2
          · fin_cases d
            · exact absurd rfl h5
            · exact ⟨6, rfl⟩
            · exact absurd rfl h3
            · exact absurd rfl h6
        · fin_cases c
          · fin_cases d
            · exact absurd rfl h6
            · exact absurd rfl h5
            · exact absurd rfl h3
            · exact ⟨7, rfl⟩
          · exact absurd rfl h4
          · exact absurd rfl h2
          · fin_cases d
            · exfalso; simp at e3
            · exact absurd rfl h5
            · exact absurd rfl h3
            · exact absurd rfl h6
        · exact absurd rfl h1
        · fin_cases c
          · fin_cases d
            · exact absurd rfl h6
            · exact ⟨8, rfl⟩
            · exact absurd rfl h3
            · exact absurd rfl h5
          · exfalso; simp at e2
          · exact absurd rfl h2
          · exact absurd rfl h4
      · exfalso; simp at e0
  have hc := Fintype.card_congr (Equiv.ofBijective f hbij)
  exact hc.symm.trans (Fintype.card_fin 9)

private lemma pc_m2_1 : permCount (compAdj 2) 1 = 1 := permCount_one _ (Or.inl rfl)
private lemma pc_m2_2 : permCount (compAdj 2) 2 = 2 := by
  rw [permCount_eq_card2, Fintype.card_subtype, Finset.card_filter, Fintype.sum_prod_type]
  simp only [Fin.sum_univ_two]; decide
private lemma pc_m2_3 : permCount (compAdj 2) 3 = 3 := by
  rw [permCount_eq_card3, Fintype.card_subtype, Finset.card_filter, Fintype.sum_prod_type]
  simp only [Fintype.sum_prod_type, Fin.sum_univ_three]; decide

private lemma pc_m3_1 : permCount (compAdj 3) 1 = 1 := permCount_one _ (Or.inl rfl)
private lemma pc_m3_2 : permCount (compAdj 3) 2 = 2 := by
  rw [permCount_eq_card2, Fintype.card_subtype, Finset.card_filter, Fintype.sum_prod_type]
  simp only [Fin.sum_univ_two]; decide
private lemma pc_m3_3 : permCount (compAdj 3) 3 = 3 := by
  rw [permCount_eq_card3, Fintype.card_subtype, Finset.card_filter, Fintype.sum_prod_type]
  simp only [Fintype.sum_prod_type, Fin.sum_univ_three]; decide

private lemma pc_m0_4 : permCount (compAdj 0) 4 = 4 := by
  have hb := compAdj_bridge 0 (N := 4) (k := 3) (by omega) (by omega) (by decide)
  simp only [Nat.reduceAdd, Nat.reduceSub] at hb
  have hs1 : permCount (shiftE (compAdj 0) 3) 1 = permCount (compAdj 1) 1 :=
    permCount_congr (fun i _ j _ => shift_to_m1 0 3 (by decide) i j)
  rw [hb, pc_m0_3, pc_m0_2, hs1, pc_m1_1, permCount_zero]

private lemma pc_m2_4 : permCount (compAdj 2) 4 = 4 := by
  have hb := compAdj_bridge 2 (N := 4) (k := 1) (by omega) (by omega) (by decide)
  simp only [Nat.reduceAdd, Nat.reduceSub] at hb
  have hs1 : permCount (shiftE (compAdj 2) 1) 3 = permCount (compAdj 1) 3 :=
    permCount_congr (fun i _ j _ => shift_to_m1 2 1 (by decide) i j)
  have hs2 : permCount (shiftE (compAdj 2) 2) 2 = permCount (compAdj 0) 2 :=
    permCount_congr (fun i _ j _ => shift_to_m0 2 2 (by decide) i j)
  rw [hb, pc_m2_1, permCount_zero, hs1, hs2, pc_m1_3, pc_m0_2]

private lemma pc_m3_4 : permCount (compAdj 3) 4 = 5 := by
  have hb := compAdj_bridge 3 (N := 4) (k := 2) (by omega) (by omega) (by decide)
  simp only [Nat.reduceAdd, Nat.reduceSub] at hb
  have hs1 : permCount (shiftE (compAdj 3) 2) 2 = permCount (compAdj 1) 2 :=
    permCount_congr (fun i _ j _ => shift_to_m1 3 2 (by decide) i j)
  have hs2 : permCount (shiftE (compAdj 3) 3) 1 = permCount (compAdj 0) 1 :=
    permCount_congr (fun i _ j _ => shift_to_m0 3 3 (by decide) i j)
  rw [hb, pc_m3_2, pc_m3_1, hs1, hs2, pc_m1_2, pc_m0_1]

-- Inserting a 4-cycle in `compAdj 1` (at bridge 3 — 4) and `compAdj 0` (at bridge 2 — 3)
private lemma pc_m1_add4 (M : ℕ) (hM : 1 ≤ M) :
    permCount (compAdj 1) (M + 4) =
      9 * permCount (compAdj 1) M + 3 * permCount (compAdj 0) (M - 1) := by
  have hb := compAdj_bridge 1 (N := M + 4) (k := 4) (by omega) (by omega) (by decide)
  rw [hb, pc_m1_4, pc_m1_3]
  have h1 : permCount (shiftE (compAdj 1) 4) (M + 4 - 4) = permCount (compAdj 1) M := by
    have heq : M + 4 - 4 = M := by omega
    rw [heq]
    exact permCount_congr (fun i _ j _ => shift_to_m1 1 4 (by decide) i j)
  have h2 : permCount (shiftE (compAdj 1) 5) (M + 4 - 5) = permCount (compAdj 0) (M - 1) := by
    have heq : M + 4 - 5 = M - 1 := by omega
    rw [heq]
    exact permCount_congr (fun i _ j _ => shift_to_m0 1 5 (by decide) i j)
  rw [h1, h2]

private lemma pc_m0_add4 (M : ℕ) (hM : 1 ≤ M) :
    permCount (compAdj 0) (M + 3) =
      3 * permCount (compAdj 1) M + permCount (compAdj 0) (M - 1) := by
  have hb := compAdj_bridge 0 (N := M + 3) (k := 3) (by omega) (by omega) (by decide)
  rw [hb, pc_m0_3, pc_m0_2, one_mul]
  have h1 : permCount (shiftE (compAdj 0) 3) (M + 3 - 3) = permCount (compAdj 1) M := by
    have heq : M + 3 - 3 = M := by omega
    rw [heq]
    exact permCount_congr (fun i _ j _ => shift_to_m1 0 3 (by decide) i j)
  have h2 : permCount (shiftE (compAdj 0) 4) (M + 3 - 4) = permCount (compAdj 0) (M - 1) := by
    have heq : M + 3 - 4 = M - 1 := by omega
    rw [heq]
    exact permCount_congr (fun i _ j _ => shift_to_m0 0 4 (by decide) i j)
  rw [h1, h2]

-- General 10x scaling when a bridge `k` has `L = 3 * L_del` (with col(k-1) = 2)
private lemma pc_scale10_left (m : Fin 4) {N k : ℕ} (hk1 : 1 ≤ k) (hkN : k < N)
    (hcol : (colOf m (k - 1)).1 = 2)
    (h3 : permCount (compAdj m) k = 3 * permCount (compAdj m) (k - 1)) :
    permCount (compAdj m) (N + 4) = 10 * permCount (compAdj m) N := by
  have hcolk : (colOf m k).1 = 1 := by dsimp only [colOf] at hcol ⊢; omega
  have hcolk1 : (colOf m (k + 1)).1 = 0 := by dsimp only [colOf] at hcol ⊢; omega
  have hb1 := compAdj_bridge m (N := N) (k := k) hk1 hkN hcol
  have hb2 := compAdj_bridge m (N := N + 4) (k := k) hk1 (by omega) hcol
  have hs1 : permCount (shiftE (compAdj m) k) (N - k) = permCount (compAdj 1) (N - k) :=
    permCount_congr (fun i _ j _ => shift_to_m1 m k hcolk i j)
  have hs2 : permCount (shiftE (compAdj m) (k + 1)) (N - (k + 1)) = permCount (compAdj 0) (N - k - 1) := by
    have heq : N - (k + 1) = N - k - 1 := by omega
    rw [heq]
    exact permCount_congr (fun i _ j _ => shift_to_m0 m (k + 1) hcolk1 i j)
  have hs3 : permCount (shiftE (compAdj m) k) (N + 4 - k) = permCount (compAdj 1) ((N - k) + 4) := by
    have heq : N + 4 - k = (N - k) + 4 := by omega
    rw [heq]
    exact permCount_congr (fun i _ j _ => shift_to_m1 m k hcolk i j)
  have hs4 : permCount (shiftE (compAdj m) (k + 1)) (N + 4 - (k + 1)) = permCount (compAdj 0) ((N - k) + 3) := by
    have heq : N + 4 - (k + 1) = (N - k) + 3 := by omega
    rw [heq]
    exact permCount_congr (fun i _ j _ => shift_to_m0 m (k + 1) hcolk1 i j)
  rw [hb2, hb1, hs1, hs2, hs3, hs4, pc_m1_add4 (N - k) (by omega), pc_m0_add4 (N - k) (by omega), h3]
  ring

-- General 10x scaling when a bridge `k` has `R = 3 * R_del` (i.e. `compAdj 1 (N-k) = 3 * compAdj 0 (N-k-1)`)
private lemma pc_scale10_right (m : Fin 4) {N k : ℕ} (hk1 : 1 ≤ k) (hkN : k < N)
    (hcol : (colOf m (k - 1)).1 = 2)
    (h3 : permCount (compAdj 1) (N - k) = 3 * permCount (compAdj 0) (N - k - 1)) :
    permCount (compAdj m) (N + 4) = 10 * permCount (compAdj m) N := by
  have hcolk : (colOf m k).1 = 1 := by dsimp only [colOf] at hcol ⊢; omega
  have hcolk1 : (colOf m (k + 1)).1 = 0 := by dsimp only [colOf] at hcol ⊢; omega
  have hb1 := compAdj_bridge m (N := N) (k := k) hk1 hkN hcol
  have hb2 := compAdj_bridge m (N := N + 4) (k := k) hk1 (by omega) hcol
  have hs1 : permCount (shiftE (compAdj m) k) (N - k) = permCount (compAdj 1) (N - k) :=
    permCount_congr (fun i _ j _ => shift_to_m1 m k hcolk i j)
  have hs2 : permCount (shiftE (compAdj m) (k + 1)) (N - (k + 1)) = permCount (compAdj 0) (N - k - 1) := by
    have heq : N - (k + 1) = N - k - 1 := by omega
    rw [heq]
    exact permCount_congr (fun i _ j _ => shift_to_m0 m (k + 1) hcolk1 i j)
  have hs3 : permCount (shiftE (compAdj m) k) (N + 4 - k) = permCount (compAdj 1) ((N - k) + 4) := by
    have heq : N + 4 - k = (N - k) + 4 := by omega
    rw [heq]
    exact permCount_congr (fun i _ j _ => shift_to_m1 m k hcolk i j)
  have hs4 : permCount (shiftE (compAdj m) (k + 1)) (N + 4 - (k + 1)) = permCount (compAdj 0) ((N - k) + 3) := by
    have heq : N + 4 - (k + 1) = (N - k) + 3 := by omega
    rw [heq]
    exact permCount_congr (fun i _ j _ => shift_to_m0 m (k + 1) hcolk1 i j)
  rw [hb2, hb1, hs1, hs2, hs3, hs4, pc_m1_add4 (N - k) (by omega), pc_m0_add4 (N - k) (by omega), h3]
  ring

private lemma pc_m2_5 : permCount (compAdj 2) 5 = 12 := by
  have hb := compAdj_bridge 2 (N := 5) (k := 1) (by omega) (by omega) (by decide)
  simp only [Nat.reduceAdd, Nat.reduceSub] at hb
  have hs1 : permCount (shiftE (compAdj 2) 1) 4 = permCount (compAdj 1) 4 :=
    permCount_congr (fun i _ j _ => shift_to_m1 2 1 (by decide) i j)
  have hs2 : permCount (shiftE (compAdj 2) 2) 3 = permCount (compAdj 0) 3 :=
    permCount_congr (fun i _ j _ => shift_to_m0 2 2 (by decide) i j)
  rw [hb, pc_m2_1, permCount_zero, hs1, hs2, pc_m1_4, pc_m0_3]

private lemma pc_m3_5 : permCount (compAdj 3) 5 = 7 := by
  have hb := compAdj_bridge 3 (N := 5) (k := 2) (by omega) (by omega) (by decide)
  simp only [Nat.reduceAdd, Nat.reduceSub] at hb
  have hs1 : permCount (shiftE (compAdj 3) 2) 3 = permCount (compAdj 1) 3 :=
    permCount_congr (fun i _ j _ => shift_to_m1 3 2 (by decide) i j)
  have hs2 : permCount (shiftE (compAdj 3) 3) 2 = permCount (compAdj 0) 2 :=
    permCount_congr (fun i _ j _ => shift_to_m0 3 3 (by decide) i j)
  rw [hb, pc_m3_2, pc_m3_1, hs1, hs2, pc_m1_3, pc_m0_2]

private lemma pc_m3_6 : permCount (compAdj 3) 6 = 21 := by
  have hb := compAdj_bridge 3 (N := 6) (k := 2) (by omega) (by omega) (by decide)
  simp only [Nat.reduceAdd, Nat.reduceSub] at hb
  have hs1 : permCount (shiftE (compAdj 3) 2) 4 = permCount (compAdj 1) 4 :=
    permCount_congr (fun i _ j _ => shift_to_m1 3 2 (by decide) i j)
  have hs2 : permCount (shiftE (compAdj 3) 3) 3 = permCount (compAdj 0) 3 :=
    permCount_congr (fun i _ j _ => shift_to_m0 3 3 (by decide) i j)
  rw [hb, pc_m3_2, pc_m3_1, hs1, hs2, pc_m1_4, pc_m0_3]

private lemma pc_all_scale10 (m : Fin 4) (N : ℕ) (hN : 5 ≤ N) :
    permCount (compAdj m) (N + 4) = 10 * permCount (compAdj m) N := by
  fin_cases m
  · change permCount (compAdj 0) (N + 4) = 10 * permCount (compAdj 0) N
    exact pc_scale10_left 0 (k := 3) (by omega) (by omega) (by decide)
      (by simp only [Nat.reduceSub]; rw [pc_m0_3, pc_m0_2])
  · change permCount (compAdj 1) (N + 4) = 10 * permCount (compAdj 1) N
    exact pc_scale10_left 1 (k := 4) (by omega) (by omega) (by decide)
      (by simp only [Nat.reduceSub]; rw [pc_m1_4, pc_m1_3])
  · change permCount (compAdj 2) (N + 4) = 10 * permCount (compAdj 2) N
    by_cases h5 : N = 5
    · subst h5
      exact pc_scale10_right 2 (k := 1) (by omega) (by omega) (by decide)
        (by simp only [Nat.reduceSub]; rw [pc_m1_4, pc_m0_3])
    · exact pc_scale10_left 2 (k := 5) (by omega) (by omega) (by decide)
        (by simp only [Nat.reduceSub]; rw [pc_m2_5, pc_m2_4])
  · change permCount (compAdj 3) (N + 4) = 10 * permCount (compAdj 3) N
    by_cases h5 : N = 5
    · subst h5
      exact pc_scale10_right 3 (k := 2) (by omega) (by omega) (by decide)
        (by simp only [Nat.reduceSub]; rw [pc_m1_3, pc_m0_2])
    · by_cases h6 : N = 6
      · subst h6
        exact pc_scale10_right 3 (k := 2) (by omega) (by omega) (by decide)
          (by simp only [Nat.reduceSub]; rw [pc_m1_4, pc_m0_3])
      · exact pc_scale10_left 3 (k := 6) (by omega) (by omega) (by decide)
          (by simp only [Nat.reduceSub]; rw [pc_m3_6, pc_m3_5])

private lemma a_add4 (n : ℕ) (hn : 4 ≤ n) : a (n + 4) = 10000 * a n := by
  rw [a_eq_prod (n + 4) (by omega), a_eq_prod n (by omega)]
  have hterm : ∀ m : Fin 4, permCount (compAdj m) (n + 4 + 1) = 10 * permCount (compAdj m) (n + 1) := by
    intro m
    have heq : n + 4 + 1 = (n + 1) + 4 := by omega
    rw [heq]
    exact pc_all_scale10 m (n + 1) (by omega)
  rw [Fin.prod_univ_four, Fin.prod_univ_four, hterm 0, hterm 1, hterm 2, hterm 3]
  ring

-- Base values a 0 .. a 7

private lemma a_0 : a 0 = 0 := by simp [a]

private lemma a_1 : a 1 = 8 := by
  rw [a_eq_prod 1 (by omega), Fin.prod_univ_four]; simp only [Nat.reduceAdd]
  rw [pc_m0_2, pc_m1_2, pc_m2_2, pc_m3_2]; norm_num

private lemma a_2 : a 2 = 81 := by
  rw [a_eq_prod 2 (by omega), Fin.prod_univ_four]; simp only [Nat.reduceAdd]
  rw [pc_m0_3, pc_m1_3, pc_m2_3, pc_m3_3]; norm_num

private lemma a_3 : a 3 = 720 := by
  rw [a_eq_prod 3 (by omega), Fin.prod_univ_four]; simp only [Nat.reduceAdd]
  rw [pc_m0_4, pc_m1_4, pc_m2_4, pc_m3_4]; norm_num

private lemma pc_m0_5 : permCount (compAdj 0) 5 = 7 := by
  have h := pc_m0_add4 2 (by omega); simp only [Nat.reduceAdd, Nat.reduceSub] at h
  rw [pc_m1_2, pc_m0_1] at h; exact h

private lemma pc_m1_5 : permCount (compAdj 1) 5 = 12 := by
  have h := pc_m1_add4 1 (by omega); simp only [Nat.reduceAdd, Nat.reduceSub] at h
  rw [pc_m1_1, permCount_zero] at h; exact h

private lemma pc_m0_6 : permCount (compAdj 0) 6 = 10 := by
  have h := pc_m0_add4 3 (by omega); simp only [Nat.reduceAdd, Nat.reduceSub] at h
  rw [pc_m1_3, pc_m0_2] at h; exact h

private lemma pc_m1_6 : permCount (compAdj 1) 6 = 21 := by
  have h := pc_m1_add4 2 (by omega); simp only [Nat.reduceAdd, Nat.reduceSub] at h
  rw [pc_m1_2, pc_m0_1] at h; exact h

private lemma pc_m2_6 : permCount (compAdj 2) 6 = 16 := by
  have hb := compAdj_bridge 2 (N := 6) (k := 5) (by omega) (by omega) (by decide)
  simp only [Nat.reduceAdd, Nat.reduceSub] at hb
  have hs1 : permCount (shiftE (compAdj 2) 5) 1 = permCount (compAdj 1) 1 :=
    permCount_congr (fun i _ j _ => shift_to_m1 2 5 (by decide) i j)
  have hs2 : permCount (shiftE (compAdj 2) 6) 0 = 1 := permCount_zero _
  rw [hb, pc_m2_5, pc_m2_4, hs1, hs2, pc_m1_1]

private lemma pc_m0_7 : permCount (compAdj 0) 7 = 30 := by
  have h := pc_m0_add4 4 (by omega); simp only [Nat.reduceAdd, Nat.reduceSub] at h
  rw [pc_m1_4, pc_m0_3] at h; exact h

private lemma pc_m1_7 : permCount (compAdj 1) 7 = 30 := by
  have h := pc_m1_add4 3 (by omega); simp only [Nat.reduceAdd, Nat.reduceSub] at h
  rw [pc_m1_3, pc_m0_2] at h; exact h

private lemma pc_m2_7 : permCount (compAdj 2) 7 = 28 := by
  have hb := compAdj_bridge 2 (N := 7) (k := 5) (by omega) (by omega) (by decide)
  simp only [Nat.reduceAdd, Nat.reduceSub] at hb
  have hs1 : permCount (shiftE (compAdj 2) 5) 2 = permCount (compAdj 1) 2 :=
    permCount_congr (fun i _ j _ => shift_to_m1 2 5 (by decide) i j)
  have hs2 : permCount (shiftE (compAdj 2) 6) 1 = permCount (compAdj 0) 1 :=
    permCount_congr (fun i _ j _ => shift_to_m0 2 6 (by decide) i j)
  rw [hb, pc_m2_5, pc_m2_4, hs1, hs2, pc_m1_2, pc_m0_1]

private lemma pc_m3_7 : permCount (compAdj 3) 7 = 28 := by
  have hb := compAdj_bridge 3 (N := 7) (k := 6) (by omega) (by omega) (by decide)
  simp only [Nat.reduceAdd, Nat.reduceSub] at hb
  have hs1 : permCount (shiftE (compAdj 3) 6) 1 = permCount (compAdj 1) 1 :=
    permCount_congr (fun i _ j _ => shift_to_m1 3 6 (by decide) i j)
  have hs2 : permCount (shiftE (compAdj 3) 7) 0 = 1 := permCount_zero _
  rw [hb, pc_m3_6, pc_m3_5, hs1, hs2, pc_m1_1]

private lemma pc_m0_8 : permCount (compAdj 0) 8 = 40 := by
  have h := pc_scale10_left 0 (N := 4) (k := 3) (by omega) (by omega) (by decide)
    (by simp only [Nat.reduceSub]; rw [pc_m0_3, pc_m0_2])
  simp only [Nat.reduceAdd] at h; rw [pc_m0_4] at h; exact h

private lemma pc_m1_8 : permCount (compAdj 1) 8 = 90 := by
  have h := pc_m1_add4 4 (by omega); simp only [Nat.reduceAdd, Nat.reduceSub] at h
  rw [pc_m1_4, pc_m0_3] at h; exact h

private lemma pc_m2_8 : permCount (compAdj 2) 8 = 40 := by
  have hb := compAdj_bridge 2 (N := 8) (k := 5) (by omega) (by omega) (by decide)
  simp only [Nat.reduceAdd, Nat.reduceSub] at hb
  have hs1 : permCount (shiftE (compAdj 2) 5) 3 = permCount (compAdj 1) 3 :=
    permCount_congr (fun i _ j _ => shift_to_m1 2 5 (by decide) i j)
  have hs2 : permCount (shiftE (compAdj 2) 6) 2 = permCount (compAdj 0) 2 :=
    permCount_congr (fun i _ j _ => shift_to_m0 2 6 (by decide) i j)
  rw [hb, pc_m2_5, pc_m2_4, hs1, hs2, pc_m1_3, pc_m0_2]

private lemma pc_m3_8 : permCount (compAdj 3) 8 = 49 := by
  have hb := compAdj_bridge 3 (N := 8) (k := 6) (by omega) (by omega) (by decide)
  simp only [Nat.reduceAdd, Nat.reduceSub] at hb
  have hs1 : permCount (shiftE (compAdj 3) 6) 2 = permCount (compAdj 1) 2 :=
    permCount_congr (fun i _ j _ => shift_to_m1 3 6 (by decide) i j)
  have hs2 : permCount (shiftE (compAdj 3) 7) 1 = permCount (compAdj 0) 1 :=
    permCount_congr (fun i _ j _ => shift_to_m0 3 7 (by decide) i j)
  rw [hb, pc_m3_6, pc_m3_5, hs1, hs2, pc_m1_2, pc_m0_1]

private lemma a_eq_prod' (n N : ℕ) (hN : N = n + 1) (hn : 1 ≤ n) :
    a n = ∏ m : Fin 4, permCount (compAdj m) N := by
  subst hN; exact a_eq_prod n hn

private lemma a_4 : a 4 = 7056 := by
  calc a 4 = ∏ m : Fin 4, permCount (compAdj m) 5 := a_eq_prod' 4 5 rfl (by omega)
    _ = permCount (compAdj 0) 5 * permCount (compAdj 1) 5 *
        permCount (compAdj 2) 5 * permCount (compAdj 3) 5 := Fin.prod_univ_four _
    _ = 7 * 12 * 12 * 7 := by rewrite [pc_m0_5, pc_m1_5, pc_m2_5, pc_m3_5]; rfl
    _ = 7056 := by decide

private lemma a_5 : a 5 = 70560 := by
  calc a 5 = ∏ m : Fin 4, permCount (compAdj m) 6 := a_eq_prod' 5 6 rfl (by omega)
    _ = permCount (compAdj 0) 6 * permCount (compAdj 1) 6 *
        permCount (compAdj 2) 6 * permCount (compAdj 3) 6 := Fin.prod_univ_four _
    _ = 10 * 21 * 16 * 21 := by rewrite [pc_m0_6, pc_m1_6, pc_m2_6, pc_m3_6]; rfl
    _ = 70560 := by decide

private lemma a_6 : a 6 = 705600 := by
  calc a 6 = ∏ m : Fin 4, permCount (compAdj m) 7 := a_eq_prod' 6 7 rfl (by omega)
    _ = permCount (compAdj 0) 7 * permCount (compAdj 1) 7 *
        permCount (compAdj 2) 7 * permCount (compAdj 3) 7 := Fin.prod_univ_four _
    _ = 30 * 30 * 28 * 28 := by rewrite [pc_m0_7, pc_m1_7, pc_m2_7, pc_m3_7]; rfl
    _ = 705600 := by decide

private lemma a_7 : a 7 = 7056000 := by
  calc a 7 = ∏ m : Fin 4, permCount (compAdj m) 8 := a_eq_prod' 7 8 rfl (by omega)
    _ = permCount (compAdj 0) 8 * permCount (compAdj 1) 8 *
        permCount (compAdj 2) 8 * permCount (compAdj 3) 8 := Fin.prod_univ_four _
    _ = 40 * 90 * 40 * 49 := by rewrite [pc_m0_8, pc_m1_8, pc_m2_8, pc_m3_8]; rfl
    _ = 7056000 := by decide

-- Part 4: Closed form, recurrence, and generating function

private lemma a_closed (n : ℕ) (hn : 3 < n) : a n = 441 * 2 ^ n * 5 ^ (n - 4) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hlt : n < 8
    · interval_cases n
      · exact a_4.trans (by decide)
      · exact a_5.trans (by decide)
      · exact a_6.trans (by decide)
      · exact a_7.trans (by decide)
    · have hsub : n = (n - 4) + 4 := by omega
      rw [hsub, a_add4 (n - 4) (by omega), ih (n - 4) (by omega) (by omega)]
      have he1 : (n - 4) + 4 - 4 = (n - 4 - 4) + 4 := by omega
      have he2 : (n - 4) + 4 = (n - 4) + 4 := rfl
      rw [he1]
      ring

private lemma a_rec (n : ℕ) (hn : 4 < n) : a n = 10 * a (n - 1) := by
  rw [a_closed n (by omega), a_closed (n - 1) (by omega)]
  have h1 : n = (n - 1) + 1 := by omega
  have h2 : n - 4 = (n - 1 - 4) + 1 := by omega
  nth_rw 1 [h1]
  rw [h2]
  ring

private lemma gf_eq :
    let X : PowerSeries ℤ := PowerSeries.X
    PowerSeries.mk (fun n => (a n : ℤ)) * (1 - 10 * X) =
      X * (8 + X - 90 * X ^ 2 - 144 * X ^ 3) := by
  intro X
  have hlhs_exp : PowerSeries.mk (fun n => (a n : ℤ)) * (1 - 10 * X) =
      PowerSeries.mk (fun n => (a n : ℤ)) - (10 : ℤ) • (X * PowerSeries.mk (fun n => (a n : ℤ))) := by
    simp only [zsmul_eq_mul, Int.cast_ofNat]; ring
  have hrhs_exp : X * (8 + X - 90 * X ^ 2 - 144 * X ^ 3) =
      (8 : ℤ) • X + X ^ 2 - (90 : ℤ) • X ^ 3 - (144 : ℤ) • X ^ 4 := by
    simp only [zsmul_eq_mul, Int.cast_ofNat]; ring
  rw [hlhs_exp, hrhs_exp]
  ext n
  have hX1 : (PowerSeries.coeff n) (X * PowerSeries.mk fun m => (a m : ℤ)) =
      if 1 ≤ n then (a (n - 1) : ℤ) else 0 := by
    have h1 : X * (PowerSeries.mk fun m => (a m : ℤ)) = X ^ 1 * (PowerSeries.mk fun m => (a m : ℤ)) := by simp
    rw [h1, PowerSeries.coeff_X_pow_mul']
    simp
  have hX1' : (PowerSeries.coeff n) X = if n = 1 then 1 else 0 := by
    simp [X, PowerSeries.coeff_X]
  have hXk' : ∀ k : ℕ, (PowerSeries.coeff n) (X ^ k) = if n = k then 1 else 0 := by
    intro k; simp [X, PowerSeries.coeff_X_pow]
  simp only [map_sub, map_add, map_zsmul]
  rw [hX1]
  simp only [zsmul_eq_mul, Int.cast_id, PowerSeries.coeff_mk, hX1', hXk']
  by_cases hn : 5 ≤ n
  · have hrec := a_rec n (by omega)
    have hne : n ≠ 1 ∧ n ≠ 2 ∧ n ≠ 3 ∧ n ≠ 4 := by omega
    have hge : 1 ≤ n := by omega
    simp only [hne, hge, ↓reduceIte]
    omega
  · interval_cases n
    · simp only [show ¬ (1 : ℕ) ≤ 0 by omega, show (0 : ℕ) ≠ 1 by omega, show (0 : ℕ) ≠ 2 by omega,
        show (0 : ℕ) ≠ 3 by omega, show (0 : ℕ) ≠ 4 by omega, ↓reduceIte, a_0]; norm_num
    · simp only [show (1 : ℕ) ≤ 1 by omega, show (1 - 1 : ℕ) = 0 from rfl, show (1 : ℕ) ≠ 2 by omega,
        show (1 : ℕ) ≠ 3 by omega, show (1 : ℕ) ≠ 4 by omega, ↓reduceIte, a_0, a_1]; norm_num
    · simp only [show (1 : ℕ) ≤ 2 by omega, show (2 - 1 : ℕ) = 1 from rfl, show (2 : ℕ) ≠ 1 by omega,
        show (2 : ℕ) ≠ 3 by omega, show (2 : ℕ) ≠ 4 by omega, ↓reduceIte, a_1, a_2]; norm_num
    · simp only [show (1 : ℕ) ≤ 3 by omega, show (3 - 1 : ℕ) = 2 from rfl, show (3 : ℕ) ≠ 1 by omega,
        show (3 : ℕ) ≠ 2 by omega, show (3 : ℕ) ≠ 4 by omega, ↓reduceIte, a_2, a_3]; norm_num
    · simp only [show (1 : ℕ) ≤ 4 by omega, show (4 - 1 : ℕ) = 3 from rfl, show (4 : ℕ) ≠ 1 by omega,
        show (4 : ℕ) ≠ 2 by omega, show (4 : ℕ) ≠ 3 by omega, ↓reduceIte, a_3, a_4]; norm_num

end ProofA264185

theorem OMA.solution : type_of% @OMA.S_oeis_a264185.main :=
  ⟨ProofA264185.a_rec, ProofA264185.a_closed, ProofA264185.gf_eq⟩
