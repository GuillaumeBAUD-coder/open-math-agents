import OMAStatements.S_mo_513259
import Mathlib

/-!
# Proof of MathOverflow 513259

For any simple graph adjacency matrix `A` (symmetric, zero diagonal, `{0, 1}` entries):
1. Over `ZMod 8`, if `IsUnit A.det`, then `(A⁻¹).permanent = 1`.
2. Over `ZMod 24`, if `IsUnit A.det`, then `2 * A.permanent + (A⁻¹).permanent - 3 = 0`.
-/

namespace OMA.MO513259

open Finset BigOperators Matrix Equiv

/-! ### Section 1: Ring homomorphisms, CRT, and `ZMod 3` permanent inversion -/

private lemma det_map {α R S : Type*} [DecidableEq α] [Fintype α]
    [CommRing R] [CommRing S] (f : R →+* S) (M : Matrix α α R) :
    (M.map f).det = f M.det := by
  change (f.mapMatrix M).det = f M.det
  exact (RingHom.map_det f M).symm

private lemma permanent_map {α R S : Type*} [DecidableEq α] [Fintype α]
    [CommSemiring R] [CommSemiring S] (f : R →+* S) (M : Matrix α α R) :
    (M.map f).permanent = f M.permanent := by
  simp only [Matrix.permanent, map_sum, map_prod, Matrix.map_apply]

private lemma inv_map_of_isUnit {α R S : Type*} [DecidableEq α] [Fintype α]
    [CommRing R] [CommRing S] (f : R →+* S) (A : Matrix α α R) (hA : IsUnit A.det) :
    (A.map f)⁻¹ = A⁻¹.map f := by
  have hAf : IsUnit (A.map f).det := by
    rw [det_map]; exact hA.map f
  have hmul : A.map f * A⁻¹.map f = 1 := by
    rw [← Matrix.map_mul, Matrix.mul_nonsing_inv A hA, Matrix.map_one f (map_zero f) (map_one f)]
  have hmul' : (A.map f)⁻¹ * (A.map f * A⁻¹.map f) = (A.map f)⁻¹ * 1 := congrArg _ hmul
  rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hAf, Matrix.one_mul, Matrix.mul_one] at hmul'
  exact hmul'.symm

private lemma eq_zero_zmod24_of_casts :
    ∀ z : ZMod 24,
      ZMod.castHom (by norm_num : 8 ∣ 24) (ZMod 8) z = 0 →
      ZMod.castHom (by norm_num : 3 ∣ 24) (ZMod 3) z = 0 → z = 0 := by
  decide

private def S3 {n : ℕ} (M : Matrix (Fin n) (Fin n) (ZMod 3)) : ZMod 3 :=
  ∑ x : Fin n → ZMod 3, (∏ i : Fin n, x i) * (∏ i : Fin n, M.mulVec x i)

private lemma zmod3_sum_pow_one : ∑ t : ZMod 3, t = 0 := by decide
private lemma zmod3_sum_pow_two : ∑ t : ZMod 3, t ^ 2 = -1 := by decide

private lemma S3_eq_perm {n : ℕ} (M : Matrix (Fin n) (Fin n) (ZMod 3)) :
    S3 M = (-1 : ZMod 3) ^ n * M.permanent := by
  unfold S3
  have hexp : ∀ x : Fin n → ZMod 3,
      ∏ i : Fin n, M.mulVec x i =
        ∑ f : Fin n → Fin n, ∏ i : Fin n, M i (f i) * x (f i) := by
    intro x
    simp only [Matrix.mulVec, dotProduct]
    exact Fintype.prod_sum (fun i j => M i j * x j)
  simp_rw [hexp, Finset.mul_sum]
  rw [Finset.sum_comm]
  have hterm : ∀ f : Fin n → Fin n,
      (∑ x : Fin n → ZMod 3, (∏ i : Fin n, x i) * ∏ i : Fin n, M i (f i) * x (f i)) =
      (∏ i : Fin n, M i (f i)) *
        ∏ k : Fin n, ∑ t : ZMod 3, t ^ (1 + (Finset.univ.filter (fun i => f i = k)).card) := by
    intro f
    have hinner : ∀ x : Fin n → ZMod 3,
        (∏ i : Fin n, x i) * ∏ i : Fin n, M i (f i) * x (f i) =
        (∏ i : Fin n, M i (f i)) *
          ∏ k : Fin n, (x k) ^ (1 + (Finset.univ.filter (fun i => f i = k)).card) := by
      intro x
      rw [Finset.prod_mul_distrib]
      have hfib : ∏ i : Fin n, x (f i) =
          ∏ k : Fin n, (x k) ^ (Finset.univ.filter (fun i => f i = k)).card := by
        rw [← Finset.prod_fiberwise_of_maps_to (g := f) (t := Finset.univ) (fun _ _ => mem_univ _)]
        refine Finset.prod_congr rfl fun k _ => ?_
        rw [Finset.prod_congr rfl (fun i hi => by rw [(mem_filter.mp hi).2]), Finset.prod_const]
      rw [hfib]
      have hcomb : (∏ k : Fin n, x k) * ∏ k : Fin n, x k ^ (Finset.univ.filter (fun i => f i = k)).card =
          ∏ k : Fin n, x k ^ (1 + (Finset.univ.filter (fun i => f i = k)).card) := by
        rw [← Finset.prod_mul_distrib]
        refine Finset.prod_congr rfl fun k _ => by rw [pow_add, pow_one]
      rw [← hcomb]; ring
    simp_rw [hinner, ← Finset.mul_sum]
    congr 1
    exact (Fintype.prod_sum (fun k (t : ZMod 3) =>
      t ^ (1 + (Finset.univ.filter (fun i => f i = k)).card))).symm
  simp_rw [hterm]
  have hbij_only : ∀ f : Fin n → Fin n, ¬ Function.Bijective f →
      (∏ i : Fin n, M i (f i)) *
        ∏ k : Fin n, ∑ t : ZMod 3, t ^ (1 + (Finset.univ.filter (fun i => f i = k)).card) = 0 := by
    intro f hnb
    have hnsurj : ¬ Function.Surjective f := fun hs =>
      hnb ⟨Finite.injective_iff_surjective.mpr hs, hs⟩
    rw [Function.Surjective] at hnsurj
    push Not at hnsurj
    obtain ⟨k0, hk0⟩ := hnsurj
    have hcard : (Finset.univ.filter (fun i => f i = k0)).card = 0 := by
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro i _; exact hk0 i
    have hzero : ∏ k : Fin n, ∑ t : ZMod 3, t ^ (1 + (Finset.univ.filter (fun i => f i = k)).card) = 0 := by
      refine Finset.prod_eq_zero (mem_univ k0) ?_
      rw [hcard]
      simpa using zmod3_sum_pow_one
    rw [hzero, mul_zero]
  rw [← Finset.sum_subset (Finset.subset_univ (Finset.univ.filter Function.Bijective))
      (fun f _ hf => hbij_only f (by simpa using hf))]
  have hperm_eq :
      ∑ f ∈ Finset.univ.filter Function.Bijective,
        (∏ i : Fin n, M i (f i)) *
          ∏ k : Fin n, ∑ t : ZMod 3, t ^ (1 + (Finset.univ.filter (fun i => f i = k)).card) =
      ∑ σ : Equiv.Perm (Fin n),
        (∏ i : Fin n, M i (σ i)) * (-1 : ZMod 3) ^ n := by
    refine Finset.sum_bij'
      (fun f hf => Equiv.ofBijective f (mem_filter.mp hf).2)
      (fun σ _ => (σ : Fin n → Fin n))
      (fun f hf => mem_univ _)
      (fun σ _ => mem_filter.mpr ⟨mem_univ _, σ.bijective⟩)
      (fun f hf => by ext x; rfl)
      (fun σ _ => by ext x; rfl)
      (fun f hf => ?_)
    congr 1
    have hcard1 : ∀ k : Fin n, (Finset.univ.filter (fun i => f i = k)).card = 1 := by
      intro k
      obtain ⟨i0, hi0⟩ := (mem_filter.mp hf).2.2 k
      have heq : Finset.univ.filter (fun i => f i = k) = {i0} := by
        ext i
        simp only [mem_filter, mem_univ, true_and, mem_singleton]
        exact ⟨fun h => (mem_filter.mp hf).2.1 (h.trans hi0.symm), fun h => h ▸ hi0⟩
      rw [heq, Finset.card_singleton]
    simp_rw [hcard1]
    simp only [Nat.reduceAdd, zmod3_sum_pow_two, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [hperm_eq, ← Finset.sum_mul, mul_comm, ← Matrix.permanent_transpose]
  rfl

private lemma perm_inv_eq_perm_zmod3 {n : ℕ} (A : Matrix (Fin n) (Fin n) (ZMod 3))
    (hA : IsUnit A.det) : (A⁻¹).permanent = A.permanent := by
  have hS : S3 A = S3 A⁻¹ := by
    unfold S3
    let e : (Fin n → ZMod 3) ≃ (Fin n → ZMod 3) :=
      { toFun := A.mulVec
        invFun := A⁻¹.mulVec
        left_inv := fun x => by rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul A hA, Matrix.one_mulVec]
        right_inv := fun y => by rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv A hA, Matrix.one_mulVec] }
    refine Fintype.sum_equiv e _ _ fun x => ?_
    have hx : A⁻¹.mulVec (A.mulVec x) = x := e.left_inv x
    change (∏ i : Fin n, x i) * (∏ i : Fin n, A.mulVec x i) =
      (∏ i : Fin n, A.mulVec x i) * (∏ i : Fin n, A⁻¹.mulVec (A.mulVec x) i)
    rw [hx, mul_comm]
  rw [S3_eq_perm, S3_eq_perm] at hS
  have hneg : ((-1 : ZMod 3) ^ n) * ((-1 : ZMod 3) ^ n) = 1 := by
    rw [← mul_pow]; norm_num
  have h := congrArg (fun v => (-1 : ZMod 3) ^ n * v) hS
  rw [← mul_assoc, ← mul_assoc, hneg, one_mul, one_mul] at h
  exact h.symm

/-! ### Section 2: `ZMod 4` permanent theorem (`A.permanent = 1`) -/

private def IsSkew {α R : Type*} [AddGroup R] (B : Matrix α α R) : Prop :=
  (∀ i, B i i = 0) ∧ ∀ i j, B j i = -B i j

private lemma isSkew_submatrix_perm {α R : Type*} [AddGroup R]
    {B : Matrix α α R} (hB : IsSkew B) (σ : Equiv.Perm α) :
    IsSkew (B.submatrix σ σ) :=
  ⟨fun i => hB.1 (σ i), fun i j => hB.2 (σ i) (σ j)⟩

private lemma sum_skew_quad_eq_zero {n : ℕ} {R : Type*} [CommRing R]
    {B : Matrix (Fin n) (Fin n) R} (hB : IsSkew B) (v : Fin n → R) :
    ∑ k : Fin n, ∑ l : Fin n, v l * B l k * v k = 0 := by
  have hsplit : ∀ k l : Fin n,
      v l * B l k * v k =
        (if l < k then v l * B l k * v k else 0) +
        (if k < l then v l * B l k * v k else 0) := by
    intro k l
    rcases lt_trichotomy l k with h | rfl | h
    · simp [h, not_lt_of_gt h]
    · simp only [lt_self_iff_false, ↓reduceIte, hB.1, mul_zero, zero_mul, add_zero]
    · simp [h, not_lt_of_gt h]
  have hrew : (∑ k : Fin n, ∑ l : Fin n, v l * B l k * v k) =
      (∑ k : Fin n, ∑ l : Fin n, (if l < k then v l * B l k * v k else 0)) +
      (∑ k : Fin n, ∑ l : Fin n, (if k < l then v l * B l k * v k else 0)) := by
    simp_rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => hsplit k l
  rw [hrew]
  have hneg : ∑ k : Fin n, ∑ l : Fin n, (if k < l then v l * B l k * v k else 0) =
      -(∑ k : Fin n, ∑ l : Fin n, (if l < k then v l * B l k * v k else 0)) := by
    rw [Finset.sum_comm, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun l _ => ?_
    split_ifs
    · rw [hB.2]; ring
    · simp
  rw [hneg, add_neg_cancel]

private lemma isSkew_congr {n : ℕ} {R : Type*} [CommRing R]
    {B : Matrix (Fin n) (Fin n) R} (hB : IsSkew B) (E : Matrix (Fin n) (Fin n) R) :
    IsSkew (Eᵀ * B * E) := by
  constructor
  · intro i
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul]
    exact sum_skew_quad_eq_zero hB (fun l => E l i)
  · intro i j
    have hT : (Eᵀ * B * E)ᵀ = -(Eᵀ * B * E) := by
      have hBT : Bᵀ = -B := by
        ext a b; simp only [Matrix.transpose_apply, Matrix.neg_apply]; exact hB.2 a b
      rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, hBT]
      simp [Matrix.mul_assoc]
    exact congrFun (congrFun hT i) j

private lemma zmod4_not_isUnit_zero : ¬ IsUnit (0 : ZMod 4) := by
  rintro ⟨u, hu⟩
  have h1 : (0 : ZMod 4) * (u⁻¹ : (ZMod 4)ˣ) = 1 := by
    rw [← hu]; exact Units.mul_inv u
  rw [zero_mul] at h1
  exact absurd h1 (by decide)

private lemma zmod4_isUnit_iff (u : ZMod 4) : IsUnit u ↔ u = 1 ∨ u = 3 := by
  constructor
  · rintro ⟨v, hv⟩
    have hmul : u * (v⁻¹ : (ZMod 4)ˣ).val = 1 := by rw [← hv]; exact Units.mul_inv v
    generalize (v⁻¹ : (ZMod 4)ˣ).val = w at hmul
    clear v hv
    revert u w hmul; decide
  · rintro (rfl | rfl)
    · exact isUnit_one
    · exact ⟨⟨3, 3, by decide, by decide⟩, rfl⟩

private lemma zmod4_unit_sq (u : ZMod 4) (hu : IsUnit u) : u * u = 1 := by
  rcases (zmod4_isUnit_iff u).mp hu with rfl | rfl <;> decide

private lemma zmod4_cast2_zero_of_not_isUnit (x : ZMod 4) (hx : ¬ IsUnit x) :
    ZMod.castHom (by norm_num : 2 ∣ 4) (ZMod 2) x = 0 := by
  rw [zmod4_isUnit_iff] at hx
  revert x hx; decide

private lemma zmod4_isUnit_of_cast2_eq_one (x : ZMod 4)
    (hx : ZMod.castHom (by norm_num : 2 ∣ 4) (ZMod 2) x = 1) : IsUnit x := by
  rw [zmod4_isUnit_iff]
  revert x hx; decide

private lemma even_of_isUnit_det_skew_zmod4 {n : ℕ} {B : Matrix (Fin n) (Fin n) (ZMod 4)}
    (hB : IsSkew B) (hu : IsUnit B.det) : Even n := by
  have hBT : Bᵀ = -B := by
    ext i j; simp only [Matrix.transpose_apply, Matrix.neg_apply]; exact hB.2 i j
  have hdet : B.det = (-1 : ZMod 4) ^ n * B.det := by
    calc B.det = Bᵀ.det := (Matrix.det_transpose B).symm
      _ = (-B).det := by rw [hBT]
      _ = (-1 : ZMod 4) ^ n * B.det := by rw [Matrix.det_neg, Fintype.card_fin]
  rcases Nat.even_or_odd n with hev | hodd
  · exact hev
  · rw [Odd.neg_one_pow hodd] at hdet
    have h2 : (2 : ZMod 4) * B.det = 0 := by
      have : B.det + B.det = 0 := by linear_combination hdet
      simpa [two_mul] using this
    rcases (zmod4_isUnit_iff B.det).mp hu with h | h <;> rw [h] at h2 <;>
      exact absurd h2 (by decide)

private lemma det_skew_zmod4 : ∀ n : ℕ, ∀ B : Matrix (Fin n) (Fin n) (ZMod 4),
    IsSkew B → IsUnit B.det → B.det = 1 := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro B hB hu
    rcases n with _ | _ | m
    · exact Matrix.det_isEmpty
    · exfalso
      have h0 : B.det = 0 := by
        rw [Matrix.det_fin_one]
        exact hB.1 0
      rw [h0] at hu
      exact zmod4_not_isUnit_zero hu
    · have hex : ∃ j : Fin (m + 2), IsUnit (B 0 j) := by
        by_contra hno
        push Not at hno
        let f2 : ZMod 4 →+* ZMod 2 := ZMod.castHom (by norm_num : 2 ∣ 4) (ZMod 2)
        have hrow0 : ∀ j : Fin (m + 2), f2 (B 0 j) = 0 := fun j =>
          zmod4_cast2_zero_of_not_isUnit (B 0 j) (hno j)
        have hdet0 : (B.map f2).det = 0 :=
          Matrix.det_eq_zero_of_row_eq_zero 0 (fun j => by simp [hrow0 j])
        have hu2 : IsUnit (B.map f2).det := by rw [det_map]; exact hu.map f2
        rw [hdet0] at hu2
        exact not_isUnit_zero hu2
      obtain ⟨j0, hj0⟩ := hex
      have hj0_ne : j0 ≠ 0 := by
        intro h; rw [h, hB.1] at hj0; exact zmod4_not_isUnit_zero hj0
      let i1 : Fin (m + 2) := ⟨1, by omega⟩
      have hi1_ne0 : i1 ≠ 0 := by intro h; have := congrArg Fin.val h; simp [i1] at this
      let σ : Equiv.Perm (Fin (m + 2)) := Equiv.swap i1 j0
      let B1 : Matrix (Fin (m + 2)) (Fin (m + 2)) (ZMod 4) := B.submatrix σ σ
      have hB1_det : B1.det = B.det := Matrix.det_submatrix_equiv_self σ B
      have hB1_skew : IsSkew B1 := isSkew_submatrix_perm hB σ
      have hσ0 : σ 0 = 0 := Equiv.swap_apply_of_ne_of_ne hi1_ne0.symm hj0_ne.symm
      have hσ1 : σ i1 = j0 := Equiv.swap_apply_left i1 j0
      let u : ZMod 4 := B1 0 i1
      have hu_unit : IsUnit u := by
        dsimp only [u, B1]; rw [Matrix.submatrix_apply, hσ0, hσ1]; exact hj0
      have hu_sq : u * u = 1 := zmod4_unit_sq u hu_unit
      let E : Matrix (Fin (m + 2)) (Fin (m + 2)) (ZMod 4) := Matrix.of fun i k =>
        if i = k then 1
        else if i.val = 0 ∧ 2 ≤ k.val then u * B1 i1 k
        else if i.val = 1 ∧ 2 ≤ k.val then -(u * B1 0 k)
        else 0
      have hE_tri : E.BlockTriangular id := by
        intro i k hik
        dsimp only [id] at hik
        have hne : i ≠ k := ne_of_gt hik
        have hlt : k.val < i.val := hik
        simp only [E, Matrix.of_apply, hne, ↓reduceIte]
        split_ifs with h1 h2
        · omega
        · omega
        · rfl
      have hE_det : E.det = 1 := by
        rw [Matrix.det_of_isUpperTriangular hE_tri]
        refine Finset.prod_eq_one fun i _ => ?_
        simp [E]
      let B2 : Matrix (Fin (m + 2)) (Fin (m + 2)) (ZMod 4) := Eᵀ * B1 * E
      have hB2_det : B2.det = B.det := by
        simp only [B2, Matrix.det_mul, Matrix.det_transpose, hE_det, one_mul, mul_one, hB1_det]
      have hB2_skew : IsSkew B2 := isSkew_congr hB1_skew E
      have hE_col0 : ∀ i : Fin (m + 2), E i 0 = if i = 0 then 1 else 0 := by
        intro i; simp [E]
      have hE_col1 : ∀ i : Fin (m + 2), E i i1 = if i = i1 then 1 else 0 := by
        intro i
        simp only [E, Matrix.of_apply]
        split_ifs with h1 h2 h3
        · rfl
        · exact absurd h2.2 (by simp [i1])
        · exact absurd h3.2 (by simp [i1])
        · rfl
      have hB2_01 : B2 0 i1 = u := by
        simp only [B2, Matrix.mul_apply, Matrix.transpose_apply, hE_col0, hE_col1]
        simp [u]
      have hB2_0k : ∀ k : Fin (m + 2), 2 ≤ k.val → B2 0 k = 0 := by
        intro k hk
        have hk0 : k ≠ 0 := by intro h; have := congrArg Fin.val h; change k.val = 0 at this; omega
        have hk1 : k ≠ i1 := by intro h; have := congrArg Fin.val h; change k.val = 1 at this; omega
        simp only [B2, Matrix.mul_apply, Matrix.transpose_apply, hE_col0]
        simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
        have hsum : ∑ l : Fin (m + 2), B1 0 l * E l k =
            B1 0 0 * E 0 k + B1 0 i1 * E i1 k + B1 0 k * E k k := by
          have hmem : ∀ l : Fin (m + 2), l ≠ 0 → l ≠ i1 → l ≠ k → E l k = 0 := by
            intro l hl0 hl1 hlk
            simp only [E, Matrix.of_apply, hlk, ↓reduceIte]
            split_ifs with h1 h2
            · exact absurd (Fin.ext h1.1) hl0
            · exact absurd (Fin.ext h2.1) hl1
            · rfl
          rw [← Finset.add_sum_erase _ _ (mem_univ (0 : Fin (m + 2)))]
          have hi1_mem : i1 ∈ Finset.univ.erase (0 : Fin (m + 2)) :=
            mem_erase.mpr ⟨hi1_ne0, mem_univ _⟩
          rw [← Finset.add_sum_erase _ _ hi1_mem]
          have hk_mem : k ∈ (Finset.univ.erase (0 : Fin (m + 2))).erase i1 :=
            mem_erase.mpr ⟨hk1, mem_erase.mpr ⟨hk0, mem_univ _⟩⟩
          rw [← Finset.add_sum_erase _ _ hk_mem]
          have hrest : ∑ l ∈ ((Finset.univ.erase (0 : Fin (m + 2))).erase i1).erase k, B1 0 l * E l k = 0 := by
            refine Finset.sum_eq_zero fun l hl => ?_
            have hlk : l ≠ k := (mem_erase.mp hl).1
            have hl1 : l ≠ i1 := (mem_erase.mp (mem_erase.mp hl).2).1
            have hl0 : l ≠ 0 := (mem_erase.mp (mem_erase.mp (mem_erase.mp hl).2).2).1
            rw [hmem l hl0 hl1 hlk, mul_zero]
          rw [hrest, add_zero, add_assoc]
        rw [hsum, hB1_skew.1 0, zero_mul, zero_add]
        have hE1k : E i1 k = -(u * B1 0 k) := by
          simp only [E, Matrix.of_apply, hk1.symm, ↓reduceIte]
          have h11 : i1.val = 1 ∧ 2 ≤ k.val := ⟨rfl, hk⟩
          simp [i1, h11]
        have hEkk : E k k = 1 := by simp [E]
        rw [hE1k, hEkk, mul_one]
        change u * -(u * B1 0 k) + B1 0 k = 0
        linear_combination -(B1 0 k) * hu_sq
      have hB2_1k : ∀ k : Fin (m + 2), 2 ≤ k.val → B2 i1 k = 0 := by
        intro k hk
        have hk0 : k ≠ 0 := by intro h; have := congrArg Fin.val h; change k.val = 0 at this; omega
        have hk1 : k ≠ i1 := by intro h; have := congrArg Fin.val h; change k.val = 1 at this; omega
        simp only [B2, Matrix.mul_apply, Matrix.transpose_apply, hE_col1]
        simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
        have hsum : ∑ l : Fin (m + 2), B1 i1 l * E l k =
            B1 i1 0 * E 0 k + B1 i1 i1 * E i1 k + B1 i1 k * E k k := by
          have hmem : ∀ l : Fin (m + 2), l ≠ 0 → l ≠ i1 → l ≠ k → E l k = 0 := by
            intro l hl0 hl1 hlk
            simp only [E, Matrix.of_apply, hlk, ↓reduceIte]
            split_ifs with h1 h2
            · exact absurd (Fin.ext h1.1) hl0
            · exact absurd (Fin.ext h2.1) hl1
            · rfl
          rw [← Finset.add_sum_erase _ _ (mem_univ (0 : Fin (m + 2)))]
          have hi1_mem : i1 ∈ Finset.univ.erase (0 : Fin (m + 2)) :=
            mem_erase.mpr ⟨hi1_ne0, mem_univ _⟩
          rw [← Finset.add_sum_erase _ _ hi1_mem]
          have hk_mem : k ∈ (Finset.univ.erase (0 : Fin (m + 2))).erase i1 :=
            mem_erase.mpr ⟨hk1, mem_erase.mpr ⟨hk0, mem_univ _⟩⟩
          rw [← Finset.add_sum_erase _ _ hk_mem]
          have hrest : ∑ l ∈ ((Finset.univ.erase (0 : Fin (m + 2))).erase i1).erase k, B1 i1 l * E l k = 0 := by
            refine Finset.sum_eq_zero fun l hl => ?_
            have hlk : l ≠ k := (mem_erase.mp hl).1
            have hl1 : l ≠ i1 := (mem_erase.mp (mem_erase.mp hl).2).1
            have hl0 : l ≠ 0 := (mem_erase.mp (mem_erase.mp (mem_erase.mp hl).2).2).1
            rw [hmem l hl0 hl1 hlk, mul_zero]
          rw [hrest, add_zero, add_assoc]
        rw [hsum, hB1_skew.1 i1, zero_mul, add_zero]
        have hE0k : E 0 k = u * B1 i1 k := by
          simp only [E, Matrix.of_apply, hk0.symm, ↓reduceIte]
          have h00 : (0 : Fin (m + 2)).val = 0 ∧ 2 ≤ k.val := ⟨rfl, hk⟩
          simp [h00]
        have hEkk : E k k = 1 := by simp [E]
        have h10 : B1 i1 0 = -u := hB1_skew.2 0 i1
        rw [hE0k, hEkk, mul_one, h10]
        linear_combination -(B1 i1 k) * hu_sq
      let e : Fin 2 ⊕ Fin m ≃ Fin (m + 2) :=
        { toFun := Sum.elim (fun a => ⟨a.val, by omega⟩) (fun b => ⟨b.val + 2, by omega⟩)
          invFun := fun i => if h : i.val < 2 then Sum.inl ⟨i.val, h⟩ else Sum.inr ⟨i.val - 2, by omega⟩
          left_inv := fun x => by
            rcases x with a | b
            · simp [a.isLt]
            · simp [show ¬(b.val + 2 < 2) by omega]
          right_inv := fun i => by
            dsimp only
            split_ifs with h
            · simp
            · ext; dsimp; omega }
      let U : Matrix (Fin 2) (Fin 2) (ZMod 4) := Matrix.of fun a b => B2 (e (Sum.inl a)) (e (Sum.inl b))
      let S : Matrix (Fin m) (Fin m) (ZMod 4) := Matrix.of fun a b => B2 (e (Sum.inr a)) (e (Sum.inr b))
      have he0 : e (Sum.inl 0) = 0 := by ext; rfl
      have he1 : e (Sum.inl 1) = i1 := by ext; rfl
      have hblk : B2.submatrix e e = Matrix.fromBlocks U 0 0 S := by
        ext x y
        rcases x with a | a <;> rcases y with b | b
        · simp [U]
        · simp only [Matrix.submatrix_apply, Matrix.fromBlocks_apply₁₂, Matrix.zero_apply]
          have hge : 2 ≤ (e (Sum.inr b)).val := by simp [e]
          rcases a with ⟨av, hav⟩
          interval_cases av
          · change B2 (e (Sum.inl 0)) (e (Sum.inr b)) = 0; rw [he0]; exact hB2_0k _ hge
          · change B2 (e (Sum.inl 1)) (e (Sum.inr b)) = 0; rw [he1]; exact hB2_1k _ hge
        · simp only [Matrix.submatrix_apply, Matrix.fromBlocks_apply₂₁, Matrix.zero_apply]
          have hge : 2 ≤ (e (Sum.inr a)).val := by simp [e]
          rw [hB2_skew.2]
          rcases b with ⟨bv, hbv⟩
          interval_cases bv
          · change -B2 (e (Sum.inl 0)) (e (Sum.inr a)) = 0; rw [he0, hB2_0k _ hge, neg_zero]
          · change -B2 (e (Sum.inl 1)) (e (Sum.inr a)) = 0; rw [he1, hB2_1k _ hge, neg_zero]
        · simp [S]
      have hU_det : U.det = 1 := by
        rw [Matrix.det_fin_two]
        have h00 : U 0 0 = 0 := hB2_skew.1 _
        have h11 : U 1 1 = 0 := hB2_skew.1 _
        have h01 : U 0 1 = u := by simp only [U, Matrix.of_apply, he0, he1]; exact hB2_01
        have h10 : U 1 0 = -u := by rw [← h01]; exact hB2_skew.2 _ _
        rw [h00, h11, h01, h10]; linear_combination hu_sq
      have hdet_eq : B.det = S.det := by
        rw [← hB2_det, ← Matrix.det_submatrix_equiv_self e B2, hblk,
          Matrix.det_fromBlocks_zero₁₂, hU_det, one_mul]
      have hS_skew : IsSkew S := ⟨fun a => hB2_skew.1 _, fun a b => hB2_skew.2 _ _⟩
      have hS_unit : IsUnit S.det := hdet_eq ▸ hu
      rw [hdet_eq]
      exact ih m (by omega) S hS_skew hS_unit

private lemma perm_invol_apply {α : Type*} {σ : Equiv.Perm α} (hinv : σ⁻¹ = σ) (x : α) :
    σ (σ x) = x := by
  have hmul : σ * σ = 1 := by
    calc σ * σ = σ⁻¹ * σ := by rw [hinv]
      _ = 1 := inv_mul_cancel σ
  exact congrArg (fun p : Equiv.Perm α => p x) hmul

private lemma sign_fpf_involution : ∀ (n : ℕ) (σ : Equiv.Perm (Fin n)),
    σ⁻¹ = σ → (∀ i, σ i ≠ i) →
    (Equiv.Perm.sign σ : ℤ) = (-1 : ℤ) ^ (Finset.univ.filter (fun i : Fin n => σ i < i)).card := by
  intro n
  have hgen : ∀ (k : ℕ) (σ : Equiv.Perm (Fin n)),
      σ.support.card = k → σ⁻¹ = σ →
      (Equiv.Perm.sign σ : ℤ) = (-1 : ℤ) ^ (Finset.univ.filter (fun i : Fin n => σ i < i)).card := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro σ hcard hinv
      by_cases h1 : σ = 1
      · subst h1
        simp
      · have hne : σ.support.Nonempty := by
          rw [Finset.nonempty_iff_ne_empty]
          intro hempty
          exact h1 (Equiv.Perm.support_eq_empty_iff.mp hempty)
        obtain ⟨a, ha⟩ := hne
        have hσa : σ a ≠ a := Equiv.Perm.mem_support.mp ha
        have hσσ : ∀ x, σ (σ x) = x := perm_invol_apply hinv
        let τ : Equiv.Perm (Fin n) := Equiv.swap a (σ a) * σ
        have hτ_apply : ∀ x : Fin n, τ x = if x = a then a else if x = σ a then σ a else σ x := by
          intro x
          dsimp only [τ, Equiv.Perm.mul_apply]
          by_cases hxa : x = a
          · subst hxa; simp [Equiv.swap_apply_right]
          · by_cases hxsa : x = σ a
            · subst hxsa; simp [hxa, hσσ a, Equiv.swap_apply_left]
            · have h1' : σ x ≠ a := fun h => hxsa (by rw [← h, hσσ x])
              have h2' : σ x ≠ σ a := fun h => hxa (σ.injective h)
              simp [hxa, hxsa, Equiv.swap_apply_of_ne_of_ne h1' h2']
        have hτ_inv : τ⁻¹ = τ := by
          rw [inv_eq_iff_mul_eq_one]
          apply Equiv.ext
          intro x
          change τ (τ x) = x
          by_cases h1' : x = a
          · subst h1'; simp [hτ_apply]
          · by_cases h2' : x = σ a
            · subst h2'; simp [hτ_apply, h1']
            · have hσx_a : σ x ≠ a := fun h => h2' (by rw [← h, hσσ x])
              have hσx_sa : σ x ≠ σ a := fun h => h1' (σ.injective h)
              simp [hτ_apply, h1', h2', hσx_a, hσx_sa, hσσ x]
        have hsupp : σ.support = insert a (insert (σ a) τ.support) := by
          ext x
          simp only [Equiv.Perm.mem_support, mem_insert, hτ_apply]
          by_cases hxa : x = a
          · subst hxa; simp [hσa]
          · by_cases hxsa : x = σ a
            · subst hxsa; simp [hxa, hσσ a, hσa.symm]
            · simp [hxa, hxsa]
        have ha_not : a ∉ τ.support := by simp [Equiv.Perm.mem_support, hτ_apply]
        have hsa_not : σ a ∉ τ.support := by simp [Equiv.Perm.mem_support, hτ_apply, hσa]
        have hcard_τ : τ.support.card + 2 = k := by
          rw [← hcard, hsupp, Finset.card_insert_of_notMem (by simp [hσa.symm, ha_not]),
            Finset.card_insert_of_notMem hsa_not]
        have hlt_card : (Finset.univ.filter (fun i : Fin n => σ i < i)).card =
            (Finset.univ.filter (fun i : Fin n => τ i < i)).card + 1 := by
          let mx := max a (σ a)
          have hmx_eq : Finset.univ.filter (fun i : Fin n => σ i < i) =
              insert mx (Finset.univ.filter (fun i : Fin n => τ i < i)) := by
            ext x
            simp only [mem_filter, mem_univ, true_and, mem_insert, hτ_apply]
            rcases lt_or_gt_of_ne hσa with hlt | hgt
            · have hmx : mx = a := max_eq_left hlt.le
              rw [hmx]
              by_cases hxa : x = a
              · subst hxa; simp [hlt]
              · by_cases hxsa : x = σ a
                · subst hxsa; simp [hxa, hσσ a, not_lt_of_gt hlt]
                · simp [hxa, hxsa]
            · have hmx : mx = σ a := max_eq_right hgt.le
              rw [hmx]
              by_cases hxa : x = a
              · subst hxa; simp [hσa.symm, not_lt_of_gt hgt]
              · by_cases hxsa : x = σ a
                · subst hxsa; simp [hσσ a, hgt]
                · simp [hxa, hxsa]
          have hmx_not : mx ∉ Finset.univ.filter (fun i : Fin n => τ i < i) := by
            simp only [mem_filter, mem_univ, true_and, hτ_apply]
            rcases lt_or_gt_of_ne hσa with hlt | hgt
            · have hmx : mx = a := max_eq_left hlt.le
              rw [hmx]; simp
            · have hmx : mx = σ a := max_eq_right hgt.le
              rw [hmx]; simp [hσa]
          rw [hmx_eq, Finset.card_insert_of_notMem hmx_not]
        have hsign_τ := ih τ.support.card (by omega) τ rfl hτ_inv
        have hsign_mul : (Equiv.Perm.sign τ : ℤ) = -(Equiv.Perm.sign σ : ℤ) := by
          dsimp only [τ]
          rw [map_mul, Equiv.Perm.sign_swap hσa.symm]
          simp
        rw [hlt_card, pow_succ]
        linarith
  intro σ hinv _
  exact hgen σ.support.card σ rfl hinv

private lemma perm_symm_eq_one_zmod4 {n : ℕ} (A : Matrix (Fin n) (Fin n) (ZMod 4))
    (hSym : A.IsSymm) (hDiag : ∀ i, A i i = 0 ∨ A i i = 2) (hA : IsUnit A.det) :
    A.permanent = 1 := by
  let B : Matrix (Fin n) (Fin n) (ZMod 4) := Matrix.of fun i j =>
    if i < j then A i j else if j < i then -A i j else 0
  have hB_skew : IsSkew B := by
    constructor
    · intro i; simp [B]
    · intro i j
      rcases lt_trichotomy i j with h | rfl | h
      · simp [B, h, not_lt_of_gt h, hSym.apply j i]
      · simp [B]
      · simp [B, h, not_lt_of_gt h, hSym.apply j i]
  have hB_unit : IsUnit B.det := by
    let f2 : ZMod 4 →+* ZMod 2 := ZMod.castHom (by norm_num : 2 ∣ 4) (ZMod 2)
    have hmap : B.map f2 = A.map f2 := by
      ext i j
      simp only [Matrix.map_apply, B, Matrix.of_apply]
      rcases lt_trichotomy i j with h | rfl | h
      · simp [h]
      · rcases hDiag i with hi | hi
        · simp [hi]
        · rw [hi]; simp only [lt_self_iff_false, ↓reduceIte]; decide
      · simp only [not_lt_of_gt h, ↓reduceIte, h, map_neg]
        generalize f2 (A i j) = y
        fin_cases y <;> rfl
    have hdet2 : f2 B.det = f2 A.det := by
      rw [← det_map f2 B, ← det_map f2 A, hmap]
    have hu2 : IsUnit (f2 A.det) := hA.map f2
    have h1 : f2 B.det = 1 := by
      rw [hdet2]
      generalize f2 A.det = y at hu2 ⊢
      fin_cases y
      · exact absurd hu2 not_isUnit_zero
      · rfl
    exact zmod4_isUnit_of_cast2_eq_one B.det h1
  have heven : Even n := even_of_isUnit_det_skew_zmod4 hB_skew hB_unit
  have hB_det : B.det = 1 := det_skew_zmod4 n B hB_skew hB_unit
  suffices hdiff : A.permanent - B.det = 0 by linear_combination hdiff + hB_det
  rw [Matrix.permanent, Matrix.det_apply', ← Finset.sum_sub_distrib]
  let g : Equiv.Perm (Fin n) → ZMod 4 := fun σ =>
    ∏ i : Fin n, A (σ i) i - (Equiv.Perm.sign σ : ZMod 4) * ∏ i : Fin n, B (σ i) i
  change ∑ σ : Equiv.Perm (Fin n), g σ = 0
  have hg_inv : ∀ σ : Equiv.Perm (Fin n), g σ⁻¹ = g σ := by
    intro σ
    dsimp only [g]
    have h1 : ∏ i : Fin n, A (σ⁻¹ i) i = ∏ i : Fin n, A (σ i) i := by
      refine Fintype.prod_equiv σ⁻¹ _ _ fun i => ?_
      change A (σ⁻¹ i) i = A (σ (σ⁻¹ i)) (σ⁻¹ i)
      have hss : σ (σ⁻¹ i) = i := Equiv.apply_symm_apply σ i
      rw [hss, hSym.apply]
    have h2 : ∏ i : Fin n, B (σ⁻¹ i) i = ∏ i : Fin n, B (σ i) i := by
      calc ∏ i : Fin n, B (σ⁻¹ i) i
          = ∏ i : Fin n, B i (σ i) := by
              refine Fintype.prod_equiv σ⁻¹ _ _ fun i => ?_
              change B (σ⁻¹ i) i = B (σ⁻¹ i) (σ (σ⁻¹ i))
              have hss : σ (σ⁻¹ i) = i := Equiv.apply_symm_apply σ i
              rw [hss]
        _ = ∏ i : Fin n, (-B (σ i) i) := Finset.prod_congr rfl fun i _ => hB_skew.2 (σ i) i
        _ = (-1 : ZMod 4) ^ n * ∏ i : Fin n, B (σ i) i := by
              rw [Finset.prod_neg, Finset.card_univ, Fintype.card_fin]
        _ = ∏ i : Fin n, B (σ i) i := by rw [heven.neg_one_pow, one_mul]
    have hsign_inv : (Equiv.Perm.sign σ⁻¹ : ZMod 4) = (Equiv.Perm.sign σ : ZMod 4) := by
      rw [map_inv]
      rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [h]
    rw [h1, h2, hsign_inv]
  have h2g : ∀ σ : Equiv.Perm (Fin n), 2 * g σ = 0 := by
    intro σ
    dsimp only [g]
    by_cases hfp : ∃ i : Fin n, σ i = i
    · obtain ⟨i0, hi0⟩ := hfp
      have hB0 : ∏ i : Fin n, B (σ i) i = 0 :=
        Finset.prod_eq_zero (mem_univ i0) (by rw [hi0, hB_skew.1])
      have hA0 : (2 : ZMod 4) * ∏ i : Fin n, A (σ i) i = 0 := by
        rw [← Finset.mul_prod_erase _ _ (mem_univ i0), ← mul_assoc, hi0]
        rcases hDiag i0 with h | h
        · simp [h]
        · rw [h]; exact (by decide : (2 : ZMod 4) * 2 = 0) ▸ zero_mul _
      rw [hB0, mul_zero, sub_zero, hA0]
    · push Not at hfp
      have hBprod : ∏ i : Fin n, B (σ i) i =
          (-1 : ZMod 4) ^ (Finset.univ.filter (fun i : Fin n => i < σ i)).card *
            ∏ i : Fin n, A (σ i) i := by
        have hterm : ∀ i : Fin n, B (σ i) i =
            (if i < σ i then (-1 : ZMod 4) else 1) * A (σ i) i := by
          intro i
          rcases lt_trichotomy (σ i) i with h | h | h
          · simp [B, h, not_lt_of_gt h]
          · exact absurd h (hfp i)
          · simp [B, h, not_lt_of_gt h]
        simp_rw [hterm, Finset.prod_mul_distrib]
        congr 1
        rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const_one, mul_one]
      rw [hBprod]
      have hs : (Equiv.Perm.sign σ : ZMod 4) * (-1 : ZMod 4) ^ (Finset.univ.filter (fun i : Fin n => i < σ i)).card = 1 ∨
          (Equiv.Perm.sign σ : ZMod 4) * (-1 : ZMod 4) ^ (Finset.univ.filter (fun i : Fin n => i < σ i)).card = -1 := by
        rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h
        · rcases Nat.even_or_odd (Finset.univ.filter (fun i : Fin n => i < σ i)).card with he | ho
          · left; simp [h, Even.neg_one_pow he]
          · right; simp [h, Odd.neg_one_pow ho]
        · rcases Nat.even_or_odd (Finset.univ.filter (fun i : Fin n => i < σ i)).card with he | ho
          · right; simp [h, Even.neg_one_pow he]
          · left; simp [h, Odd.neg_one_pow ho]
      rcases hs with h | h
      · rw [← mul_assoc, h, one_mul, sub_self, mul_zero]
      · rw [← mul_assoc, h, neg_one_mul, sub_neg_eq_add, ← two_mul, ← mul_assoc]
        have : (2 : ZMod 4) * 2 = 0 := by decide
        rw [this, zero_mul]
  have hsplit : ∑ σ : Equiv.Perm (Fin n), g σ =
      (∑ σ ∈ Finset.univ.filter (fun σ : Equiv.Perm (Fin n) => σ⁻¹ = σ), g σ) +
      (∑ σ ∈ Finset.univ.filter (fun σ : Equiv.Perm (Fin n) => σ⁻¹ ≠ σ), g σ) := by
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun σ : Equiv.Perm (Fin n) => σ⁻¹ = σ)]
  rw [hsplit]
  have hnoninv : ∑ σ ∈ Finset.univ.filter (fun σ : Equiv.Perm (Fin n) => σ⁻¹ ≠ σ), g σ = 0 := by
    refine Finset.sum_involution (fun σ _ => σ⁻¹) ?_ ?_ ?_ ?_
    · intro σ _
      rw [hg_inv, ← two_mul, h2g]
    · intro σ hσ _
      exact (mem_filter.mp hσ).2
    · intro σ hσ
      simp only [mem_filter, mem_univ, true_and, inv_inv]
      exact (mem_filter.mp hσ).2.symm
    · intro σ _; exact inv_inv σ
  have hinv_zero : ∑ σ ∈ Finset.univ.filter (fun σ : Equiv.Perm (Fin n) => σ⁻¹ = σ), g σ = 0 := by
    refine Finset.sum_eq_zero fun σ hσ => ?_
    have hinv : σ⁻¹ = σ := (mem_filter.mp hσ).2
    have hσσ : ∀ x, σ (σ x) = x := perm_invol_apply hinv
    have hlt_eq : (Finset.univ.filter (fun i : Fin n => σ i < i)).card =
        (Finset.univ.filter (fun i : Fin n => i < σ i)).card := by
      refine Finset.card_bij (fun i _ => σ i) ?_ ?_ ?_
      · intro i hi
        have hlt : σ i < i := (mem_filter.mp hi).2
        exact mem_filter.mpr ⟨mem_univ _, by rwa [hσσ i]⟩
      · intro i₁ _ i₂ _ h; exact σ.injective h
      · intro j hj
        refine ⟨σ j, ?_, hσσ j⟩
        have hlt : j < σ j := (mem_filter.mp hj).2
        exact mem_filter.mpr ⟨mem_univ _, by rwa [hσσ j]⟩
    by_cases hfp : ∃ i : Fin n, σ i = i
    · obtain ⟨i0, hi0⟩ := hfp
      have hB0 : ∏ i : Fin n, B (σ i) i = 0 :=
        Finset.prod_eq_zero (mem_univ i0) (by rw [hi0, hB_skew.1])
      have hcard_fp_even : Even (Finset.univ.filter (fun i : Fin n => σ i = i)).card := by
        have hpart : (Finset.univ.filter (fun i : Fin n => σ i = i)).card +
            (Finset.univ.filter (fun i : Fin n => σ i < i)).card +
            (Finset.univ.filter (fun i : Fin n => i < σ i)).card = n := by
          have h1 : Finset.univ.filter (fun i : Fin n => σ i = i) ∪
              Finset.univ.filter (fun i : Fin n => σ i < i) ∪
              Finset.univ.filter (fun i : Fin n => i < σ i) = Finset.univ := by
            ext i; simp only [mem_union, mem_filter, mem_univ, true_and, iff_true]
            rcases lt_trichotomy (σ i) i with h | h | h
            · exact Or.inl (Or.inr h)
            · exact Or.inl (Or.inl h)
            · exact Or.inr h
          have hd1 : Disjoint (Finset.univ.filter (fun i : Fin n => σ i = i))
              (Finset.univ.filter (fun i : Fin n => σ i < i)) := by
            rw [Finset.disjoint_filter]; intro i _ h1 h2; exact ne_of_lt h2 h1
          have hd2 : Disjoint (Finset.univ.filter (fun i : Fin n => σ i = i) ∪
              Finset.univ.filter (fun i : Fin n => σ i < i))
              (Finset.univ.filter (fun i : Fin n => i < σ i)) := by
            rw [Finset.disjoint_left]; intro i hi h2
            simp only [mem_union, mem_filter, mem_univ, true_and] at hi h2
            rcases hi with h1 | h1
            · exact ne_of_gt h2 h1
            · exact lt_asymm h1 h2
          rw [← Finset.card_union_of_disjoint hd1, ← Finset.card_union_of_disjoint hd2, h1,
            Finset.card_univ, Fintype.card_fin]
        obtain ⟨r, hr⟩ := heven
        refine ⟨r - (Finset.univ.filter (fun i : Fin n => σ i < i)).card, by omega⟩
      have hge2 : 1 < (Finset.univ.filter (fun i : Fin n => σ i = i)).card := by
        have hpos : 0 < (Finset.univ.filter (fun i : Fin n => σ i = i)).card :=
          Finset.card_pos.mpr ⟨i0, mem_filter.mpr ⟨mem_univ _, hi0⟩⟩
        obtain ⟨r, hr⟩ := hcard_fp_even
        omega
      obtain ⟨j0, hj0_mem, hj0_ne⟩ := Finset.exists_mem_ne hge2 i0
      have hj0 : σ j0 = j0 := (mem_filter.mp hj0_mem).2
      have hA0 : ∏ i : Fin n, A (σ i) i = 0 := by
        rw [← Finset.mul_prod_erase _ _ (mem_univ i0)]
        have hj0_er : j0 ∈ Finset.univ.erase i0 := mem_erase.mpr ⟨hj0_ne, mem_univ _⟩
        rw [← Finset.mul_prod_erase _ _ hj0_er, ← mul_assoc, hi0, hj0]
        rcases hDiag i0 with h1 | h1 <;> rcases hDiag j0 with h2 | h2
        · simp [h1]
        · simp [h1]
        · simp [h2]
        · rw [h1, h2]; exact (by decide : (2 : ZMod 4) * 2 = 0) ▸ zero_mul _
      dsimp only [g]
      rw [hA0, hB0, mul_zero, sub_zero]
    · push Not at hfp
      have hsign := sign_fpf_involution n σ hinv hfp
      have hBprod : ∏ i : Fin n, B (σ i) i =
          (-1 : ZMod 4) ^ (Finset.univ.filter (fun i : Fin n => i < σ i)).card *
            ∏ i : Fin n, A (σ i) i := by
        have hterm : ∀ i : Fin n, B (σ i) i =
            (if i < σ i then (-1 : ZMod 4) else 1) * A (σ i) i := by
          intro i
          rcases lt_trichotomy (σ i) i with h | h | h
          · simp [B, h, not_lt_of_gt h]
          · exact absurd h (hfp i)
          · simp [B, h, not_lt_of_gt h]
        simp_rw [hterm, Finset.prod_mul_distrib]
        congr 1
        rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const_one, mul_one]
      dsimp only [g]
      have hsign4 : (Equiv.Perm.sign σ : ZMod 4) =
          (-1 : ZMod 4) ^ (Finset.univ.filter (fun i : Fin n => σ i < i)).card := by
        have := congrArg (Int.cast : ℤ → ZMod 4) hsign
        simpa using this
      rw [hBprod, hsign4, ← hlt_eq, ← mul_assoc, ← mul_pow]
      norm_num
  rw [hinv_zero, hnoninv, add_zero]

/-! ### Section 3: `ZMod 2` even-diagonal of inverse, `subPerm`, and Jacobi minors -/

private lemma inv_diag_zero_zmod2 {n : ℕ} (A : Matrix (Fin n) (Fin n) (ZMod 2))
    (hSym : A.IsSymm) (hDiag : ∀ i, A i i = 0) (hA : IsUnit A.det) (i : Fin n) :
    A⁻¹ i i = 0 := by
  have hinv_sym : (A⁻¹).IsSymm := by
    rw [Matrix.IsSymm, Matrix.transpose_nonsing_inv, hSym]
  have hmul : A⁻¹ * A * A⁻¹ = A⁻¹ := by
    rw [Matrix.nonsing_inv_mul A hA, Matrix.one_mul]
  have hii : A⁻¹ i i = (A⁻¹ * A * A⁻¹) i i := by rw [hmul]
  rw [hii]
  simp only [Matrix.mul_apply, Finset.sum_mul]
  have hSkew2 : IsSkew A := by
    refine ⟨hDiag, fun a b => ?_⟩
    rw [hSym.apply a b]
    generalize A a b = x
    fin_cases x <;> rfl
  have hquad := sum_skew_quad_eq_zero hSkew2 (fun l => A⁻¹ l i)
  convert hquad using 1
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  rw [hinv_sym.apply i l]

private def subPerm {n : ℕ} {R : Type*} [CommSemiring R]
    (M : Matrix (Fin n) (Fin n) R) (I J : Finset (Fin n)) : R :=
  ∑ e : {x // x ∈ J} ≃ {y // y ∈ I}, ∏ x : {x // x ∈ J}, M (e x).1 x.1

private lemma subPerm_symm {n : ℕ} {R : Type*} [CommSemiring R]
    {M : Matrix (Fin n) (Fin n) R} (hSym : M.IsSymm) (I J : Finset (Fin n)) :
    subPerm M I J = subPerm M J I := by
  unfold subPerm
  refine Fintype.sum_equiv (⟨Equiv.symm, Equiv.symm, Equiv.symm_symm, Equiv.symm_symm⟩) _ _ fun e => ?_
  refine Fintype.prod_equiv e _ _ fun x => ?_
  simp [hSym.apply]

private lemma subPerm_map {n : ℕ} {R S : Type*} [CommSemiring R] [CommSemiring S]
    (f : R →+* S) (M : Matrix (Fin n) (Fin n) R) (I J : Finset (Fin n)) :
    subPerm (M.map f) I J = f (subPerm M I J) := by
  simp only [subPerm, map_sum, map_prod, Matrix.map_apply]

private lemma subPerm_eq_det_zmod2 {n : ℕ} (M : Matrix (Fin n) (Fin n) (ZMod 2))
    (I J : Finset (Fin n)) (e0 : {x // x ∈ J} ≃ {y // y ∈ I}) :
    subPerm M I J = (Matrix.of fun a b : {x // x ∈ J} => M (e0 a).1 b.1).det := by
  rw [Matrix.det_apply']
  have hsign1 : ∀ σ : Equiv.Perm {x // x ∈ J}, (Equiv.Perm.sign σ : ZMod 2) = 1 := by
    intro σ
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [h]
  simp_rw [hsign1, one_mul, Matrix.of_apply]
  unfold subPerm
  let φ : Equiv.Perm {x // x ∈ J} ≃ ({x // x ∈ J} ≃ {y // y ∈ I}) :=
    { toFun := fun σ => σ.trans e0
      invFun := fun e => e.trans e0.symm
      left_inv := fun σ => by ext x; simp
      right_inv := fun e => by ext x; simp }
  exact (Fintype.sum_equiv φ _ _ fun σ => rfl).symm

private lemma jacobi_minor_zmod2 {n : ℕ} (M A : Matrix (Fin n) (Fin n) (ZMod 2))
    (hMA : M * A = 1) (I J : Finset (Fin n)) (hcard : I.card = J.card) :
    subPerm M Iᶜ Jᶜ = subPerm A J I := by
  have hc1 : Fintype.card {x // x ∈ J} = Fintype.card {y // y ∈ I} := by simp [hcard]
  have hc2 : Fintype.card {x // x ∈ Jᶜ} = Fintype.card {y // y ∈ Iᶜ} := by simp [hcard]
  obtain ⟨e1⟩ := Fintype.truncEquivOfCardEq hc1
  obtain ⟨e2⟩ := Fintype.truncEquivOfCardEq hc2
  rw [subPerm_eq_det_zmod2 M Iᶜ Jᶜ e2, subPerm_eq_det_zmod2 A J I e1.symm]
  let α := {x // x ∈ I}
  let β := {x // x ∈ Iᶜ}
  let σ : α ⊕ β ≃ Fin n :=
    { toFun := Sum.elim Subtype.val Subtype.val
      invFun := fun x => if h : x ∈ I then Sum.inl ⟨x, h⟩ else Sum.inr ⟨x, Finset.mem_compl.mpr h⟩
      left_inv := fun x => by
        rcases x with ⟨x, hx⟩ | ⟨x, hx⟩
        · simp [hx]
        · have hx' : x ∉ I := Finset.mem_compl.mp hx
          simp [hx']
      right_inv := fun x => by dsimp; split_ifs <;> rfl }
  let τ : α ⊕ β ≃ Fin n :=
    { toFun := Sum.elim (fun a => (e1.symm a).1) (fun b => (e2.symm b).1)
      invFun := fun y => if h : y ∈ J then Sum.inl (e1 ⟨y, h⟩) else Sum.inr (e2 ⟨y, Finset.mem_compl.mpr h⟩)
      left_inv := fun x => by
        rcases x with a | b
        · simp [(e1.symm a).2]
        · have hb : (e2.symm b).1 ∉ J := Finset.mem_compl.mp (e2.symm b).2
          simp [hb]
      right_inv := fun y => by dsimp; split_ifs <;> simp }
  let M' : Matrix (α ⊕ β) (α ⊕ β) (ZMod 2) := M.submatrix σ τ
  let A' : Matrix (α ⊕ β) (α ⊕ β) (ZMod 2) := A.submatrix τ σ
  have hM'A' : M' * A' = 1 := by
    ext x y
    simp only [M', A', Matrix.mul_apply, Matrix.submatrix_apply, Matrix.one_apply]
    have hsum : ∑ k : α ⊕ β, M (σ x) (τ k) * A (τ k) (σ y) =
        ∑ k : Fin n, M (σ x) k * A k (σ y) :=
      Fintype.sum_equiv τ _ _ fun _ => rfl
    rw [hsum]
    have := congrFun (congrFun hMA (σ x)) (σ y)
    simp only [Matrix.mul_apply, Matrix.one_apply] at this
    rw [this]
    simp
  have hM'_det : M'.det = 1 := by
    have h1 : M'.det * A'.det = 1 := by rw [← Matrix.det_mul, hM'A', Matrix.det_one]
    have hz : ∀ d a : ZMod 2, d * a = 1 → d = 1 := by decide
    exact hz M'.det A'.det h1
  let N : Matrix (α ⊕ β) (α ⊕ β) (ZMod 2) :=
    Matrix.fromBlocks A'.toBlocks₁₁ 0 A'.toBlocks₂₁ 1
  have hprod : M' * N = Matrix.fromBlocks 1 M'.toBlocks₁₂ 0 M'.toBlocks₂₂ := by
    have hMA11 : M'.toBlocks₁₁ * A'.toBlocks₁₁ + M'.toBlocks₁₂ * A'.toBlocks₂₁ = 1 := by
      have h := congrArg Matrix.toBlocks₁₁ hM'A'
      rw [← Matrix.fromBlocks_toBlocks M', ← Matrix.fromBlocks_toBlocks A',
        Matrix.fromBlocks_multiply] at h
      have h1 : (1 : Matrix (α ⊕ β) (α ⊕ β) (ZMod 2)).toBlocks₁₁ = 1 := by
        ext a b; simp [Matrix.toBlocks₁₁, Matrix.one_apply]
      simpa [h1] using h
    have hMA21 : M'.toBlocks₂₁ * A'.toBlocks₁₁ + M'.toBlocks₂₂ * A'.toBlocks₂₁ = 0 := by
      have h := congrArg Matrix.toBlocks₂₁ hM'A'
      rw [← Matrix.fromBlocks_toBlocks M', ← Matrix.fromBlocks_toBlocks A',
        Matrix.fromBlocks_multiply] at h
      have h0 : (1 : Matrix (α ⊕ β) (α ⊕ β) (ZMod 2)).toBlocks₂₁ = 0 := by
        ext a b; simp [Matrix.toBlocks₂₁]
      simpa [h0] using h
    conv_lhs => rw [← Matrix.fromBlocks_toBlocks M']
    dsimp only [N]
    rw [Matrix.fromBlocks_multiply]
    simp [hMA11, hMA21]
  have hdet_prod := congrArg Matrix.det hprod
  rw [Matrix.det_mul, hM'_det, one_mul, Matrix.det_fromBlocks_zero₁₂, Matrix.det_one, mul_one,
    Matrix.det_fromBlocks_zero₂₁, Matrix.det_one, one_mul] at hdet_prod
  have h22 : (Matrix.of fun a b : {x // x ∈ Jᶜ} => M (e2 a).1 b.1).det = M'.toBlocks₂₂.det := by
    have hsub : M'.toBlocks₂₂.submatrix e2 e2 =
        Matrix.of fun a b : {x // x ∈ Jᶜ} => M (e2 a).1 b.1 := by
      ext a b
      simp [M', Matrix.toBlocks₂₂, σ, τ]
    rw [← hsub, Matrix.det_submatrix_equiv_self]
  have h11 : (Matrix.of fun a b : {x // x ∈ I} => A (e1.symm a).1 b.1).det = A'.toBlocks₁₁.det := rfl
  rw [h22, h11, hdet_prod]

/-! ### Section 4: `ZMod 8` lift invariance and even-entry shear invariance -/

private def f2_8 : ZMod 8 →+* ZMod 2 := ZMod.castHom (by norm_num : 2 ∣ 8) (ZMod 2)
private def f4_8 : ZMod 8 →+* ZMod 4 := ZMod.castHom (by norm_num : 4 ∣ 8) (ZMod 4)

private lemma zmod8_isUnit_iff (u : ZMod 8) : IsUnit u ↔ u = 1 ∨ u = 3 ∨ u = 5 ∨ u = 7 := by
  constructor
  · rintro ⟨v, hv⟩
    have hmul : u * (v⁻¹ : (ZMod 8)ˣ).val = 1 := by rw [← hv]; exact Units.mul_inv v
    generalize (v⁻¹ : (ZMod 8)ˣ).val = w at hmul
    clear v hv
    revert u w hmul; decide
  · rintro (rfl | rfl | rfl | rfl)
    · exact isUnit_one
    · exact ⟨⟨3, 3, by decide, by decide⟩, rfl⟩
    · exact ⟨⟨5, 5, by decide, by decide⟩, rfl⟩
    · exact ⟨⟨7, 7, by decide, by decide⟩, rfl⟩

private lemma zmod8_isUnit_of_cast2_eq_one : ∀ a : ZMod 8, f2_8 a = 1 → IsUnit a := by
  intro a ha
  rw [zmod8_isUnit_iff]
  revert a ha; decide

private lemma zmod8_cast2_eq_one_of_isUnit (a : ZMod 8) (ha : IsUnit a) : f2_8 a = 1 := by
  rw [zmod8_isUnit_iff] at ha
  revert a ha; decide

private lemma zmod8_four_mul_eq_of_cast2 : ∀ a b : ZMod 8, f2_8 a = f2_8 b → 4 * a = 4 * b := by
  decide

private lemma zmod8_four_mul_eq_zero_of_cast2 : ∀ a : ZMod 8, f2_8 a = 0 → 4 * a = 0 := by
  decide

private lemma zmod8_two_pow_ge_three {k : ℕ} (hk : 3 ≤ k) : (2 : ZMod 8) ^ k = 0 := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 3 := ⟨k - 3, by omega⟩
  rw [pow_add]
  have h8 : (2 : ZMod 8) ^ 3 = 0 := by decide
  rw [h8, mul_zero]

private lemma zmod2_sq (x : ZMod 2) : x * x = x := by
  revert x; decide

private lemma zmod2_add_self (x : ZMod 2) : x + x = 0 := by
  revert x; decide

private lemma inv_diag_cast2_zero_zmod8 {n : ℕ} (A : Matrix (Fin n) (Fin n) (ZMod 8))
    (hSym : A.IsSymm) (hDiag : ∀ i, f2_8 (A i i) = 0) (hA : IsUnit A.det) (i : Fin n) :
    f2_8 (A⁻¹ i i) = 0 := by
  have h1 : f2_8 (A⁻¹ i i) = (A.map f2_8)⁻¹ i i := by
    rw [inv_map_of_isUnit f2_8 A hA, Matrix.map_apply]
  rw [h1]
  refine inv_diag_zero_zmod2 (A.map f2_8) ?_ (fun j => by simp [hDiag j]) ?_ i
  · ext a b; simp [hSym.apply a b]
  · rw [det_map]; exact hA.map f2_8

private lemma even_of_isUnit_det_symm_diag2_zmod8 {n : ℕ} (A : Matrix (Fin n) (Fin n) (ZMod 8))
    (hSym : A.IsSymm) (hDiag : ∀ i, f2_8 (A i i) = 0) (hA : IsUnit A.det) : Even n := by
  let A4 : Matrix (Fin n) (Fin n) (ZMod 4) := A.map f4_8
  let B : Matrix (Fin n) (Fin n) (ZMod 4) := Matrix.of fun i j =>
    if i < j then A4 i j else if j < i then -A4 i j else 0
  have hB_skew : IsSkew B := by
    constructor
    · intro i; simp [B]
    · intro i j
      rcases lt_trichotomy i j with h | rfl | h
      · simp [B, h, not_lt_of_gt h, A4, hSym.apply j i]
      · simp [B]
      · simp [B, h, not_lt_of_gt h, A4, hSym.apply j i]
  let f2_4 : ZMod 4 →+* ZMod 2 := ZMod.castHom (by norm_num : 2 ∣ 4) (ZMod 2)
  have hcomp : ∀ x : ZMod 8, f2_4 (f4_8 x) = f2_8 x := by decide
  have hB_unit : IsUnit B.det := by
    have hmap : B.map f2_4 = A.map f2_8 := by
      ext i j
      simp only [Matrix.map_apply, B, A4, Matrix.of_apply]
      rcases lt_trichotomy i j with h | rfl | h
      · simp [h, hcomp]
      · simp [hDiag i]
      · simp only [not_lt_of_gt h, ↓reduceIte, h, map_neg, hcomp]
        generalize f2_8 (A i j) = y
        revert y; decide
    have hdet2 : f2_4 B.det = f2_8 A.det := by
      rw [← det_map f2_4 B, hmap, det_map f2_8 A]
    have h1 : f2_4 B.det = 1 := by
      rw [hdet2]; exact zmod8_cast2_eq_one_of_isUnit A.det hA
    exact zmod4_isUnit_of_cast2_eq_one B.det h1
  exact even_of_isUnit_det_skew_zmod4 hB_skew hB_unit

private lemma subPerm_empty {n : ℕ} {R : Type*} [CommSemiring R]
    (M : Matrix (Fin n) (Fin n) R) : subPerm M ∅ ∅ = 1 := by
  unfold subPerm
  have huniq : Unique ({x : Fin n // x ∈ (∅ : Finset (Fin n))} ≃ {y : Fin n // y ∈ (∅ : Finset (Fin n))}) :=
    ⟨⟨Equiv.refl _⟩, fun e => by ext ⟨x, hx⟩; exact (Finset.notMem_empty x hx).elim⟩
  rw [Fintype.sum_unique]
  simp

private lemma subPerm_univ {n : ℕ} {R : Type*} [CommSemiring R]
    (M : Matrix (Fin n) (Fin n) R) : subPerm M Finset.univ Finset.univ = M.permanent := by
  unfold subPerm Matrix.permanent
  let φ : ({x : Fin n // x ∈ (Finset.univ : Finset (Fin n))} ≃ {y : Fin n // y ∈ (Finset.univ : Finset (Fin n))}) ≃
      Equiv.Perm (Fin n) :=
    Equiv.equivCongr (Equiv.subtypeUnivEquiv mem_univ) (Equiv.subtypeUnivEquiv mem_univ)
  refine Fintype.sum_equiv φ _ _ fun e => ?_
  refine Fintype.prod_equiv (Equiv.subtypeUnivEquiv mem_univ) _ _ fun x => ?_
  rfl

private lemma subPerm_singleton {n : ℕ} {R : Type*} [CommSemiring R]
    (M : Matrix (Fin n) (Fin n) R) (i j : Fin n) : subPerm M {i} {j} = M i j := by
  unfold subPerm
  let e0 : {x : Fin n // x ∈ ({j} : Finset (Fin n))} ≃ {y : Fin n // y ∈ ({i} : Finset (Fin n))} :=
    { toFun := fun _ => ⟨i, mem_singleton_self i⟩
      invFun := fun _ => ⟨j, mem_singleton_self j⟩
      left_inv := fun ⟨x, hx⟩ => Subtype.ext (mem_singleton.mp hx).symm
      right_inv := fun ⟨y, hy⟩ => Subtype.ext (mem_singleton.mp hy).symm }
  have huniv_e : (Finset.univ : Finset ({x : Fin n // x ∈ ({j} : Finset (Fin n))} ≃
      {y : Fin n // y ∈ ({i} : Finset (Fin n))})) = {e0} := by
    ext e; simp only [mem_univ, mem_singleton, true_iff]
    exact Equiv.ext fun ⟨x, hx⟩ => Subtype.ext (mem_singleton.mp (e ⟨x, hx⟩).2)
  have huniv_j : (Finset.univ : Finset {x : Fin n // x ∈ ({j} : Finset (Fin n))}) =
      {⟨j, mem_singleton_self j⟩} := by
    ext ⟨x, hx⟩; simp only [mem_univ, mem_singleton, true_iff]
    exact Subtype.ext (mem_singleton.mp hx)
  rw [huniv_e, Finset.sum_singleton, huniv_j, Finset.prod_singleton]
  rfl

private lemma subPerm_pair {n : ℕ} {R : Type*} [CommSemiring R]
    (M : Matrix (Fin n) (Fin n) R) {i₁ i₂ j₁ j₂ : Fin n} (hi : i₁ ≠ i₂) (hj : j₁ ≠ j₂) :
    subPerm M {i₁, i₂} {j₁, j₂} = M i₁ j₁ * M i₂ j₂ + M i₁ j₂ * M i₂ j₁ := by
  unfold subPerm
  let a₁ : {x : Fin n // x ∈ ({j₁, j₂} : Finset (Fin n))} := ⟨j₁, by simp⟩
  let a₂ : {x : Fin n // x ∈ ({j₁, j₂} : Finset (Fin n))} := ⟨j₂, by simp⟩
  let b₁ : {y : Fin n // y ∈ ({i₁, i₂} : Finset (Fin n))} := ⟨i₁, by simp⟩
  let b₂ : {y : Fin n // y ∈ ({i₁, i₂} : Finset (Fin n))} := ⟨i₂, by simp⟩
  have ha_ne : a₁ ≠ a₂ := fun h => hj (congrArg Subtype.val h)
  have hb_ne : b₁ ≠ b₂ := fun h => hi (congrArg Subtype.val h)
  let e1 : {x // x ∈ ({j₁, j₂} : Finset (Fin n))} ≃ {y // y ∈ ({i₁, i₂} : Finset (Fin n))} :=
    { toFun := fun x => if x = a₁ then b₁ else b₂
      invFun := fun y => if y = b₁ then a₁ else a₂
      left_inv := fun ⟨x, hx⟩ => by
        rcases mem_insert.mp hx with rfl | hx2
        · simp [a₁, b₁]
        · have hxeq := mem_singleton.mp hx2; subst hxeq
          simp [a₁, a₂, b₁, b₂, hj.symm, hi.symm]
      right_inv := fun ⟨y, hy⟩ => by
        rcases mem_insert.mp hy with rfl | hy2
        · simp [a₁, b₁]
        · have hyeq := mem_singleton.mp hy2; subst hyeq
          simp [a₁, a₂, b₁, b₂, hj.symm, hi.symm] }
  let e2 : {x // x ∈ ({j₁, j₂} : Finset (Fin n))} ≃ {y // y ∈ ({i₁, i₂} : Finset (Fin n))} :=
    { toFun := fun x => if x = a₁ then b₂ else b₁
      invFun := fun y => if y = b₂ then a₁ else a₂
      left_inv := fun ⟨x, hx⟩ => by
        rcases mem_insert.mp hx with rfl | hx2
        · simp [a₁, b₂]
        · have hxeq := mem_singleton.mp hx2; subst hxeq
          simp [a₁, a₂, b₁, b₂, hj.symm, hi]
      right_inv := fun ⟨y, hy⟩ => by
        rcases mem_insert.mp hy with rfl | hy2
        · simp [a₁, a₂, b₁, b₂, hi, hj.symm]
        · have hyeq := mem_singleton.mp hy2; subst hyeq
          simp [a₁, b₂] }
  have he_ne : e1 ≠ e2 := fun h => hb_ne (by simpa [e1, e2] using congrArg (fun f => f a₁) h)
  have huniv_e : (Finset.univ : Finset ({x // x ∈ ({j₁, j₂} : Finset (Fin n))} ≃
      {y // y ∈ ({i₁, i₂} : Finset (Fin n))})) = {e1, e2} := by
    ext e
    simp only [mem_univ, mem_insert, mem_singleton, true_iff]
    have h1 : e a₁ = b₁ ∨ e a₁ = b₂ := by
      rcases mem_insert.mp (e a₁).2 with h | h
      · left; exact Subtype.ext h
      · right; exact Subtype.ext (mem_singleton.mp h)
    have h2 : e a₂ = b₁ ∨ e a₂ = b₂ := by
      rcases mem_insert.mp (e a₂).2 with h | h
      · left; exact Subtype.ext h
      · right; exact Subtype.ext (mem_singleton.mp h)
    have h12 : e a₁ ≠ e a₂ := fun h => ha_ne (e.injective h)
    rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
    · exact (h12 (h1.trans h2.symm)).elim
    · left; refine Equiv.ext fun ⟨x, hx⟩ => ?_
      rcases mem_insert.mp hx with rfl | hx2
      · simpa [e1, a₁, b₁] using h1
      · have hxeq := mem_singleton.mp hx2; subst hxeq
        simpa [e1, a₁, a₂, b₂, hj.symm] using h2
    · right; refine Equiv.ext fun ⟨x, hx⟩ => ?_
      rcases mem_insert.mp hx with rfl | hx2
      · simpa [e2, a₁, b₂] using h1
      · have hxeq := mem_singleton.mp hx2; subst hxeq
        simpa [e2, a₁, a₂, b₁, hj.symm] using h2
    · exact (h12 (h1.trans h2.symm)).elim
  have huniv_a : (Finset.univ : Finset {x // x ∈ ({j₁, j₂} : Finset (Fin n))}) = {a₁, a₂} := by
    ext ⟨x, hx⟩
    simp only [mem_univ, mem_insert, mem_singleton, true_iff]
    rcases mem_insert.mp hx with rfl | hx2
    · exact Or.inl rfl
    · exact Or.inr (Subtype.ext (mem_singleton.mp hx2))
  rw [huniv_e, Finset.sum_pair he_ne, huniv_a, Finset.prod_pair ha_ne, Finset.prod_pair ha_ne]
  simp only [e1, e2, Equiv.coe_fn_mk, ↓reduceIte, ha_ne.symm, a₁, a₂, b₁, b₂]
  ring

private lemma subPerm_smul {n : ℕ} {R : Type*} [CommSemiring R]
    (c : R) (M : Matrix (Fin n) (Fin n) R) (I J : Finset (Fin n)) :
    subPerm (c • M) I J = c ^ J.card * subPerm M I J := by
  unfold subPerm
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun e _ => ?_
  simp only [Matrix.smul_apply, smul_eq_mul, Finset.prod_mul_distrib, Finset.prod_const,
    Finset.card_univ, Fintype.card_coe]

private lemma sum_perm_prod_compl {n : ℕ} {R : Type*} [CommSemiring R]
    (S : Finset (Fin n)) (D M : Matrix (Fin n) (Fin n) R) :
    ∑ σ : Equiv.Perm (Fin n), (∏ j ∈ S, D (σ j) j) * (∏ j ∈ Sᶜ, M (σ j) j) =
      ∑ I ∈ Finset.powersetCard S.card Finset.univ, subPerm D I S * subPerm M Iᶜ Sᶜ := by
  rw [← Finset.sum_fiberwise_of_maps_to
    (g := fun σ : Equiv.Perm (Fin n) => S.image σ)
    (t := Finset.powersetCard S.card Finset.univ)
    (fun σ _ => Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, Finset.card_image_of_injective S σ.injective⟩)]
  refine Finset.sum_congr rfl fun I hI => ?_
  unfold subPerm
  rw [Finset.sum_mul_sum, ← Finset.sum_product']
  refine Finset.sum_bij'
    (fun σ hσ =>
      have hmemI : ∀ {z : Fin n}, z ∈ S.image σ ↔ z ∈ I := fun {z} => by
        rw [(mem_filter.mp hσ).2]
      ( { toFun := fun x => ⟨σ x.1, hmemI.mp (mem_image_of_mem σ x.2)⟩
          invFun := fun y => ⟨σ⁻¹ y.1, by
            obtain ⟨x, hx, hxy⟩ := mem_image.mp (hmemI.mpr y.2)
            have : σ⁻¹ y.1 = x := by rw [← hxy]; exact Equiv.symm_apply_apply σ x
            rwa [this]⟩
          left_inv := fun x => Subtype.ext (Equiv.symm_apply_apply σ x.1)
          right_inv := fun y => Subtype.ext (Equiv.apply_symm_apply σ y.1) },
        { toFun := fun x => ⟨σ x.1, Finset.mem_compl.mpr fun hm => by
            obtain ⟨z, hz, hzx⟩ := mem_image.mp (hmemI.mpr hm)
            exact (Finset.mem_compl.mp x.2) (σ.injective hzx ▸ hz)⟩
          invFun := fun y => ⟨σ⁻¹ y.1, Finset.mem_compl.mpr fun hmem =>
            (Finset.mem_compl.mp y.2) (hmemI.mp (mem_image.mpr ⟨σ⁻¹ y.1, hmem, Equiv.apply_symm_apply σ y.1⟩))⟩
          left_inv := fun x => Subtype.ext (Equiv.symm_apply_apply σ x.1)
          right_inv := fun y => Subtype.ext (Equiv.apply_symm_apply σ y.1) } ))
    (fun p _ =>
      { toFun := fun x => if hx : x ∈ S then (p.1 ⟨x, hx⟩).1 else (p.2 ⟨x, Finset.mem_compl.mpr hx⟩).1
        invFun := fun y => if hy : y ∈ I then (p.1.symm ⟨y, hy⟩).1 else (p.2.symm ⟨y, Finset.mem_compl.mpr hy⟩).1
        left_inv := fun x => by
          dsimp only
          by_cases hx : x ∈ S
          · simp only [hx, ↓reduceDIte, (p.1 ⟨x, hx⟩).2, Subtype.coe_eta, Equiv.symm_apply_apply]
          · have hnot : (p.2 ⟨x, Finset.mem_compl.mpr hx⟩).1 ∉ I :=
              Finset.mem_compl.mp (p.2 ⟨x, Finset.mem_compl.mpr hx⟩).2
            simp only [hx, ↓reduceDIte, hnot, Subtype.coe_eta, Equiv.symm_apply_apply]
        right_inv := fun y => by
          dsimp only
          by_cases hy : y ∈ I
          · simp only [hy, ↓reduceDIte, (p.1.symm ⟨y, hy⟩).2, Subtype.coe_eta, Equiv.apply_symm_apply]
          · have hnot : (p.2.symm ⟨y, Finset.mem_compl.mpr hy⟩).1 ∉ S :=
              Finset.mem_compl.mp (p.2.symm ⟨y, Finset.mem_compl.mpr hy⟩).2
            simp only [hy, ↓reduceDIte, hnot, Subtype.coe_eta, Equiv.apply_symm_apply] })
    (fun _ _ => mem_univ _)
    (fun p _ => by
      refine mem_filter.mpr ⟨mem_univ _, ?_⟩
      ext y
      simp only [mem_image]
      constructor
      · rintro ⟨x, hx, rfl⟩
        simp only [Equiv.coe_fn_mk, hx, ↓reduceDIte]
        exact (p.1 ⟨x, hx⟩).2
      · intro hy
        refine ⟨(p.1.symm ⟨y, hy⟩).1, (p.1.symm ⟨y, hy⟩).2, ?_⟩
        simp only [Equiv.coe_fn_mk, (p.1.symm ⟨y, hy⟩).2, ↓reduceDIte, Subtype.coe_eta, Equiv.apply_symm_apply])
    (fun σ hσ => by
      ext x
      dsimp only [Equiv.coe_fn_mk]
      split_ifs <;> rfl)
    (fun p _ => by
      ext x
      · simp only [Equiv.coe_fn_mk, x.2, ↓reduceDIte]
      · have hx : x.1 ∉ S := Finset.mem_compl.mp x.2
        simp only [Equiv.coe_fn_mk, hx, ↓reduceDIte])
    (fun σ hσ => by
      dsimp only [Equiv.coe_fn_mk]
      congr 1
      · exact (Finset.prod_coe_sort S (fun j => D (σ j) j)).symm
      · exact (Finset.prod_coe_sort Sᶜ (fun j => M (σ j) j)).symm)

private lemma perm_add_two_smul {n : ℕ} (M E : Matrix (Fin n) (Fin n) (ZMod 8)) :
    (M + (2 : ZMod 8) • E).permanent =
      M.permanent
      + 2 * (∑ j : Fin n, ∑ i : Fin n, E i j * subPerm M ({i}ᶜ) ({j}ᶜ))
      + 4 * (∑ J ∈ Finset.powersetCard 2 (Finset.univ : Finset (Fin n)),
             ∑ I ∈ Finset.powersetCard 2 (Finset.univ : Finset (Fin n)),
               subPerm E I J * subPerm M Iᶜ Jᶜ) := by
  have hexp : (M + (2 : ZMod 8) • E).permanent =
      ∑ S : Finset (Fin n),
        (2 : ZMod 8) ^ S.card *
          ∑ I ∈ Finset.powersetCard S.card Finset.univ, subPerm E I S * subPerm M Iᶜ Sᶜ := by
    rw [Matrix.permanent]
    have hprod : ∀ σ : Equiv.Perm (Fin n),
        ∏ j : Fin n, (M + (2 : ZMod 8) • E) (σ j) j =
        ∑ S : Finset (Fin n),
          (∏ j ∈ S, ((2 : ZMod 8) • E) (σ j) j) * (∏ j ∈ Sᶜ, M (σ j) j) := by
      intro σ
      have h1 : ∀ j : Fin n, (M + (2 : ZMod 8) • E) (σ j) j =
          ((2 : ZMod 8) • E) (σ j) j + M (σ j) j := fun j => by simp [add_comm]
      simp_rw [h1]
      rw [Finset.prod_add]
      have hp : (Finset.univ : Finset (Fin n)).powerset = Finset.univ := by ext S; simp
      rw [hp]
      refine Finset.sum_congr rfl fun S _ => ?_
      have hcompl : Finset.univ \ S = Sᶜ := by ext j; simp
      rw [hcompl]
    simp_rw [hprod]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun S _ => ?_
    rw [sum_perm_prod_compl S ((2 : ZMod 8) • E) M, Finset.mul_sum]
    refine Finset.sum_congr rfl fun I _ => ?_
    rw [subPerm_smul, mul_assoc]
  rw [hexp]
  let F : Finset (Fin n) → ZMod 8 := fun S =>
    (2 : ZMod 8) ^ S.card *
      ∑ I ∈ Finset.powersetCard S.card Finset.univ, subPerm E I S * subPerm M Iᶜ Sᶜ
  have hge3 : ∀ S : Finset (Fin n), 3 ≤ S.card → F S = 0 := by
    intro S hS; dsimp only [F]; rw [zmod8_two_pow_ge_three hS, zero_mul]
  have hpart : ∑ S : Finset (Fin n), F S =
      (∑ S ∈ Finset.powersetCard 0 Finset.univ, F S) +
      (∑ S ∈ Finset.powersetCard 1 Finset.univ, F S) +
      (∑ S ∈ Finset.powersetCard 2 Finset.univ, F S) := by
    have hsub : (Finset.powersetCard 0 (Finset.univ : Finset (Fin n)) ∪
        Finset.powersetCard 1 Finset.univ ∪ Finset.powersetCard 2 Finset.univ) ⊆ Finset.univ :=
      Finset.subset_univ _
    rw [← Finset.sum_subset hsub]
    · have hd01 : Disjoint (Finset.powersetCard 0 (Finset.univ : Finset (Fin n)))
          (Finset.powersetCard 1 Finset.univ) := by
        rw [Finset.disjoint_left]; intro S h0 h1
        have := (Finset.mem_powersetCard.mp h0).2
        have := (Finset.mem_powersetCard.mp h1).2
        omega
      have hd012 : Disjoint (Finset.powersetCard 0 (Finset.univ : Finset (Fin n)) ∪
          Finset.powersetCard 1 Finset.univ) (Finset.powersetCard 2 Finset.univ) := by
        rw [Finset.disjoint_left]; intro S h01 h2
        have h2c := (Finset.mem_powersetCard.mp h2).2
        rcases mem_union.mp h01 with h0 | h1
        · have := (Finset.mem_powersetCard.mp h0).2; omega
        · have := (Finset.mem_powersetCard.mp h1).2; omega
      rw [Finset.sum_union hd012, Finset.sum_union hd01]
    · intro S _ hS
      simp only [mem_union, Finset.mem_powersetCard, Finset.subset_univ, true_and] at hS
      exact hge3 S (by omega)
  rw [hpart]
  have h0 : ∑ S ∈ Finset.powersetCard 0 (Finset.univ : Finset (Fin n)), F S = M.permanent := by
    rw [Finset.powersetCard_zero, Finset.sum_singleton]
    dsimp only [F]
    rw [Finset.card_empty, pow_zero, one_mul, Finset.powersetCard_zero, Finset.sum_singleton,
      subPerm_empty, one_mul, Finset.compl_empty, subPerm_univ]
  have h1 : ∑ S ∈ Finset.powersetCard 1 (Finset.univ : Finset (Fin n)), F S =
      2 * (∑ j : Fin n, ∑ i : Fin n, E i j * subPerm M ({i}ᶜ) ({j}ᶜ)) := by
    rw [Finset.powersetCard_one, Finset.sum_map, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    dsimp only [F, Function.Embedding.coeFn_mk]
    rw [Finset.card_singleton, pow_one, Finset.powersetCard_one, Finset.sum_map]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    dsimp only [Function.Embedding.coeFn_mk]
    rw [subPerm_singleton]
  have h2 : ∑ S ∈ Finset.powersetCard 2 (Finset.univ : Finset (Fin n)), F S =
      4 * (∑ J ∈ Finset.powersetCard 2 (Finset.univ : Finset (Fin n)),
           ∑ I ∈ Finset.powersetCard 2 (Finset.univ : Finset (Fin n)),
             subPerm E I J * subPerm M Iᶜ Jᶜ) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun J hJ => ?_
    dsimp only [F]
    rw [(Finset.mem_powersetCard.mp hJ).2]
    have h22 : (2 : ZMod 8) ^ 2 = 4 := by decide
    rw [h22]
  rw [h0, h1, h2]

private lemma cauchy_binet_two_zmod2 {n : ℕ} (A M : Matrix (Fin n) (Fin n) (ZMod 2))
    (hAM : A * M = 1) (J K : Finset (Fin n)) (hJ : J.card = 2) (hK : K.card = 2) :
    ∑ I ∈ Finset.powersetCard 2 (Finset.univ : Finset (Fin n)),
      subPerm A J I * subPerm M I K = if J = K then 1 else 0 := by
  obtain ⟨j₁, j₂, hj, rfl⟩ := Finset.card_eq_two.mp hJ
  obtain ⟨k₁, k₂, hk, rfl⟩ := Finset.card_eq_two.mp hK
  have hcb : ∀ (a b c d : Fin n → ZMod 2),
      ∑ I ∈ Finset.powersetCard 2 (Finset.univ : Finset (Fin n)),
        (∑ e : {x // x ∈ I} ≃ {y // y ∈ ({j₁, j₂} : Finset (Fin n))}, ∏ x, (if (e x).1 = j₁ then a x.1 else b x.1)) *
        (∑ e : {x // x ∈ ({k₁, k₂} : Finset (Fin n))} ≃ {y // y ∈ I}, ∏ x, (if x.1 = k₁ then c (e x).1 else d (e x).1)) =
      (∑ i, a i * c i) * (∑ i, b i * d i) + (∑ i, a i * d i) * (∑ i, b i * c i) := by
    intro a b c d
    let G : Fin n → Fin n → ZMod 2 := fun i₁ i₂ =>
      (a i₁ * b i₂ + a i₂ * b i₁) * (c i₁ * d i₂ + c i₂ * d i₁)
    have hG_sym : ∀ i₁ i₂, G i₁ i₂ = G i₂ i₁ := fun i₁ i₂ => by dsimp only [G]; ring
    have hG_diag : ∀ i, G i i = 0 := fun i => by
      dsimp only [G]
      have : a i * b i + a i * b i = 0 := zmod2_add_self _
      rw [this, zero_mul]
    have hterm : ∀ I ∈ Finset.powersetCard 2 (Finset.univ : Finset (Fin n)),
        (∑ e : {x // x ∈ I} ≃ {y // y ∈ ({j₁, j₂} : Finset (Fin n))}, ∏ x, (if (e x).1 = j₁ then a x.1 else b x.1)) *
        (∑ e : {x // x ∈ ({k₁, k₂} : Finset (Fin n))} ≃ {y // y ∈ I}, ∏ x, (if x.1 = k₁ then c (e x).1 else d (e x).1)) =
        ∑ i₁ ∈ I, ∑ i₂ ∈ I, if i₁ < i₂ then G i₁ i₂ else 0 := by
      intro I hI
      obtain ⟨i₁, i₂, hi, rfl⟩ := Finset.card_eq_two.mp (Finset.mem_powersetCard.mp hI).2
      have h1 : (∑ e : {x // x ∈ ({i₁, i₂} : Finset (Fin n))} ≃ {y // y ∈ ({j₁, j₂} : Finset (Fin n))},
          ∏ x, (if (e x).1 = j₁ then a x.1 else b x.1)) = a i₁ * b i₂ + a i₂ * b i₁ := by
        have := subPerm_pair (Matrix.of fun y x : Fin n => if y = j₁ then a x else b x) hj hi
        simpa [subPerm, hj.symm] using this
      have h2 : (∑ e : {x // x ∈ ({k₁, k₂} : Finset (Fin n))} ≃ {y // y ∈ ({i₁, i₂} : Finset (Fin n))},
          ∏ x, (if x.1 = k₁ then c (e x).1 else d (e x).1)) = c i₁ * d i₂ + c i₂ * d i₁ := by
        have := subPerm_pair (Matrix.of fun y x : Fin n => if x = k₁ then c y else d y) hi hk
        simpa [subPerm, hk.symm, mul_comm] using this
      rw [h1, h2]
      rw [Finset.sum_pair hi, Finset.sum_pair hi, Finset.sum_pair hi]
      rcases lt_or_gt_of_ne hi with hlt | hgt
      · simp [G, hlt, not_lt_of_gt hlt]
      · simp only [lt_self_iff_false, ↓reduceIte, not_lt_of_gt hgt, hgt, zero_add, add_zero]
        exact hG_sym i₁ i₂
    rw [Finset.sum_congr rfl hterm]
    have hlt_bij : ∑ I ∈ Finset.powersetCard 2 (Finset.univ : Finset (Fin n)),
        (∑ i₁ ∈ I, ∑ i₂ ∈ I, if i₁ < i₂ then G i₁ i₂ else 0) =
        ∑ i₁ : Fin n, ∑ i₂ : Fin n, if i₁ < i₂ then G i₁ i₂ else 0 := by
      rw [← Finset.sum_product', Finset.univ_product_univ]
      have hfilt : ∑ p : Fin n × Fin n, (if p.1 < p.2 then G p.1 p.2 else 0) =
          ∑ p ∈ Finset.univ.filter (fun p : Fin n × Fin n => p.1 < p.2), G p.1 p.2 := by
        rw [Finset.sum_filter]
      rw [hfilt]
      refine Finset.sum_bij'
        (fun I hI => (I.min' (Finset.card_pos.mp (by rw [(Finset.mem_powersetCard.mp hI).2]; omega)),
                      I.max' (Finset.card_pos.mp (by rw [(Finset.mem_powersetCard.mp hI).2]; omega))))
        (fun p _ => {p.1, p.2})
        (fun I hI => by
          have hc := (Finset.mem_powersetCard.mp hI).2
          have hne_I : I.Nonempty := Finset.card_pos.mp (by rw [hc]; omega)
          obtain ⟨x, y, hxy, hIeq⟩ := Finset.card_eq_two.mp hc
          refine mem_filter.mpr ⟨mem_univ _, ?_⟩
          have hle : I.min' hne_I ≤ I.max' hne_I := Finset.min'_le I _ (Finset.max'_mem I hne_I)
          have hne : I.min' hne_I ≠ I.max' hne_I := by
            intro heq
            have hle1 : x ≤ I.max' hne_I := Finset.le_max' I x (by rw [hIeq]; simp)
            have hge1 : I.min' hne_I ≤ x := Finset.min'_le I x (by rw [hIeq]; simp)
            have hle2 : y ≤ I.max' hne_I := Finset.le_max' I y (by rw [hIeq]; simp)
            have hge2 : I.min' hne_I ≤ y := Finset.min'_le I y (by rw [hIeq]; simp)
            exact hxy (le_antisymm (by rw [← heq] at hle1; exact hle1.trans hge2)
              (by rw [← heq] at hle2; exact hle2.trans hge1))
          exact lt_of_le_of_ne hle hne)
        (fun p hp => Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _,
          Finset.card_pair (ne_of_lt (mem_filter.mp hp).2)⟩)
        (fun I hI => by
          have hc := (Finset.mem_powersetCard.mp hI).2
          obtain ⟨x, y, hxy, rfl⟩ := Finset.card_eq_two.mp hc
          rcases lt_or_gt_of_ne hxy with hlt | hgt
          · have hmin : ({x, y} : Finset (Fin n)).min' (by simp) = x := by
              refine le_antisymm (Finset.min'_le _ _ (by simp)) (Finset.le_min' _ _ _ ?_)
              intro z hz; rcases mem_insert.mp hz with rfl | hz2
              · exact le_rfl
              · rw [mem_singleton.mp hz2]; exact hlt.le
            have hmax : ({x, y} : Finset (Fin n)).max' (by simp) = y := by
              refine le_antisymm (Finset.max'_le _ _ _ ?_) (Finset.le_max' _ _ (by simp))
              intro z hz; rcases mem_insert.mp hz with rfl | hz2
              · exact hlt.le
              · rw [mem_singleton.mp hz2]
            dsimp only; rw [hmin, hmax]
          · have hmin : ({x, y} : Finset (Fin n)).min' (by simp) = y := by
              refine le_antisymm (Finset.min'_le _ _ (by simp)) (Finset.le_min' _ _ _ ?_)
              intro z hz; rcases mem_insert.mp hz with rfl | hz2
              · exact hgt.le
              · rw [mem_singleton.mp hz2]
            have hmax : ({x, y} : Finset (Fin n)).max' (by simp) = x := by
              refine le_antisymm (Finset.max'_le _ _ _ ?_) (Finset.le_max' _ _ (by simp))
              intro z hz; rcases mem_insert.mp hz with rfl | hz2
              · exact le_rfl
              · rw [mem_singleton.mp hz2]; exact hgt.le
            dsimp only; rw [hmin, hmax, Finset.pair_comm])
        (fun p hp => by
          have hlt : p.1 < p.2 := (mem_filter.mp hp).2
          have hmin : ({p.1, p.2} : Finset (Fin n)).min' (by simp) = p.1 := by
            refine le_antisymm (Finset.min'_le _ _ (by simp)) (Finset.le_min' _ _ _ ?_)
            intro z hz; rcases mem_insert.mp hz with rfl | hz2
            · exact le_rfl
            · rw [mem_singleton.mp hz2]; exact hlt.le
          have hmax : ({p.1, p.2} : Finset (Fin n)).max' (by simp) = p.2 := by
            refine le_antisymm (Finset.max'_le _ _ _ ?_) (Finset.le_max' _ _ (by simp))
            intro z hz; rcases mem_insert.mp hz with rfl | hz2
            · exact hlt.le
            · rw [mem_singleton.mp hz2]
          exact Prod.ext hmin hmax)
        (fun I hI => by
          have hc := (Finset.mem_powersetCard.mp hI).2
          obtain ⟨x, y, hxy, rfl⟩ := Finset.card_eq_two.mp hc
          rw [Finset.sum_pair hxy, Finset.sum_pair hxy, Finset.sum_pair hxy]
          rcases lt_or_gt_of_ne hxy with hlt | hgt
          · have hmin : ({x, y} : Finset (Fin n)).min' (by simp) = x := by
              refine le_antisymm (Finset.min'_le _ _ (by simp)) (Finset.le_min' _ _ _ ?_)
              intro z hz; rcases mem_insert.mp hz with rfl | hz2
              · exact le_rfl
              · rw [mem_singleton.mp hz2]; exact hlt.le
            have hmax : ({x, y} : Finset (Fin n)).max' (by simp) = y := by
              refine le_antisymm (Finset.max'_le _ _ _ ?_) (Finset.le_max' _ _ (by simp))
              intro z hz; rcases mem_insert.mp hz with rfl | hz2
              · exact hlt.le
              · rw [mem_singleton.mp hz2]
            simp [hmin, hmax, hlt, not_lt_of_gt hlt]
          · have hmin : ({x, y} : Finset (Fin n)).min' (by simp) = y := by
              refine le_antisymm (Finset.min'_le _ _ (by simp)) (Finset.le_min' _ _ _ ?_)
              intro z hz; rcases mem_insert.mp hz with rfl | hz2
              · exact hgt.le
              · rw [mem_singleton.mp hz2]
            have hmax : ({x, y} : Finset (Fin n)).max' (by simp) = x := by
              refine le_antisymm (Finset.max'_le _ _ _ ?_) (Finset.le_max' _ _ (by simp))
              intro z hz; rcases mem_insert.mp hz with rfl | hz2
              · exact le_rfl
              · rw [mem_singleton.mp hz2]; exact hgt.le
            simp [hmin, hmax, hgt, not_lt_of_gt hgt])
    rw [hlt_bij]
    have hexpand : ∀ i₁ i₂ : Fin n, G i₁ i₂ =
        (a i₁ * c i₁) * (b i₂ * d i₂) + (a i₂ * c i₂) * (b i₁ * d i₁) +
        (a i₁ * d i₁) * (b i₂ * c i₂) + (a i₂ * d i₂) * (b i₁ * c i₁) := by
      intro i₁ i₂; dsimp only [G]; ring
    have hsplit_pair : ∀ (f g : Fin n → ZMod 2),
        (∑ i₁ : Fin n, ∑ i₂ : Fin n, if i₁ < i₂ then f i₁ * g i₂ + f i₂ * g i₁ else 0) =
        (∑ i : Fin n, f i) * (∑ i : Fin n, g i) + ∑ i : Fin n, f i * g i := by
      intro f g
      have h1 : ∀ i₁ i₂ : Fin n, f i₁ * g i₂ =
          (if i₁ < i₂ then f i₁ * g i₂ else 0) + (if i₂ < i₁ then f i₁ * g i₂ else 0) +
          (if i₁ = i₂ then f i₁ * g i₂ else 0) := by
        intro i₁ i₂
        rcases lt_trichotomy i₁ i₂ with h | rfl | h
        · simp [h, ne_of_lt h, not_lt_of_gt h]
        · simp
        · simp [h, ne_of_gt h, not_lt_of_gt h]
      have htot : (∑ i : Fin n, f i) * (∑ i : Fin n, g i) =
          (∑ i₁ : Fin n, ∑ i₂ : Fin n, if i₁ < i₂ then f i₁ * g i₂ else 0) +
          (∑ i₁ : Fin n, ∑ i₂ : Fin n, if i₂ < i₁ then f i₁ * g i₂ else 0) +
          (∑ i₁ : Fin n, ∑ i₂ : Fin n, if i₁ = i₂ then f i₁ * g i₂ else 0) := by
        rw [Finset.sum_mul]
        simp_rw [Finset.mul_sum, ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun i₁ _ => Finset.sum_congr rfl fun i₂ _ => h1 i₁ i₂
      rw [htot]
      have hswap : (∑ i₁ : Fin n, ∑ i₂ : Fin n, if i₂ < i₁ then f i₁ * g i₂ else 0) =
          ∑ i₁ : Fin n, ∑ i₂ : Fin n, if i₁ < i₂ then f i₂ * g i₁ else 0 := by
        rw [Finset.sum_comm]
      have hdiag : (∑ i₁ : Fin n, ∑ i₂ : Fin n, if i₁ = i₂ then f i₁ * g i₂ else 0) =
          ∑ i : Fin n, f i * g i := by
        refine Finset.sum_congr rfl fun i _ => by simp
      rw [hswap, hdiag, add_assoc]
      have hcancel : (∑ i : Fin n, f i * g i) + (∑ i : Fin n, f i * g i) = 0 := zmod2_add_self _
      rw [hcancel, add_zero]
      simp_rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i₁ _ => Finset.sum_congr rfl fun i₂ _ => ?_
      split_ifs <;> ring
    have hsplitG : (∑ i₁ : Fin n, ∑ i₂ : Fin n, if i₁ < i₂ then G i₁ i₂ else 0) =
        (∑ i₁ : Fin n, ∑ i₂ : Fin n, if i₁ < i₂ then
          (a i₁ * c i₁) * (b i₂ * d i₂) + (a i₂ * c i₂) * (b i₁ * d i₁) else 0) +
        (∑ i₁ : Fin n, ∑ i₂ : Fin n, if i₁ < i₂ then
          (a i₁ * d i₁) * (b i₂ * c i₂) + (a i₂ * d i₂) * (b i₁ * c i₁) else 0) := by
      simp_rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i₁ _ => Finset.sum_congr rfl fun i₂ _ => ?_
      split_ifs
      · rw [hexpand]; ring
      · simp
    rw [hsplitG, hsplit_pair (fun i => a i * c i) (fun i => b i * d i),
      hsplit_pair (fun i => a i * d i) (fun i => b i * c i)]
    have hdiag_eq : (∑ i : Fin n, a i * c i * (b i * d i)) =
        ∑ i : Fin n, a i * d i * (b i * c i) :=
      Finset.sum_congr rfl fun i _ => by ring
    rw [hdiag_eq]
    have hcan : (∑ i : Fin n, a i * d i * (b i * c i)) + (∑ i : Fin n, a i * d i * (b i * c i)) = 0 :=
      zmod2_add_self _
    linear_combination hcan
  have h1 := hcb (fun i => A j₁ i) (fun i => A j₂ i) (fun i => M i k₁) (fun i => M i k₂)
  have hcongr : ∑ I ∈ Finset.powersetCard 2 (Finset.univ : Finset (Fin n)),
      subPerm A {j₁, j₂} I * subPerm M I {k₁, k₂} =
      (∑ i, A j₁ i * M i k₁) * (∑ i, A j₂ i * M i k₂) +
      (∑ i, A j₁ i * M i k₂) * (∑ i, A j₂ i * M i k₁) := by
    rw [← h1]
    refine Finset.sum_congr rfl fun I _ => ?_
    unfold subPerm
    congr 1
    · refine Finset.sum_congr rfl fun e _ => Finset.prod_congr rfl fun x _ => ?_
      rcases mem_insert.mp (e x).2 with h | h
      · simp [h]
      · rw [mem_singleton.mp h]; simp [hj.symm]
    · refine Finset.sum_congr rfl fun e _ => Finset.prod_congr rfl fun x _ => ?_
      rcases mem_insert.mp x.2 with h | h
      · simp [h]
      · rw [mem_singleton.mp h]; simp [hk.symm]
  rw [hcongr]
  have ham : ∀ u v : Fin n, ∑ i : Fin n, A u i * M i v = if u = v then 1 else 0 := by
    intro u v
    have := congrFun (congrFun hAM u) v
    simpa [Matrix.mul_apply, Matrix.one_apply] using this
  rw [ham j₁ k₁, ham j₂ k₂, ham j₁ k₂, ham j₂ k₁]
  by_cases heq : ({j₁, j₂} : Finset (Fin n)) = {k₁, k₂}
  · rw [if_pos heq]
    have hmem1 : j₁ ∈ ({k₁, k₂} : Finset (Fin n)) := by rw [← heq]; simp
    have hmem2 : j₂ ∈ ({k₁, k₂} : Finset (Fin n)) := by rw [← heq]; simp
    rcases mem_insert.mp hmem1 with rfl | h1
    · rcases mem_insert.mp hmem2 with h2 | h2
      · exact (hj h2.symm).elim
      · rw [mem_singleton.mp h2]; simp [hk]
    · rw [mem_singleton.mp h1] at hj ⊢
      rcases mem_insert.mp hmem2 with rfl | h2
      · simp [hk, hk.symm]
      · exact (hj (mem_singleton.mp h2).symm).elim
  · rw [if_neg heq]
    have hprod1 : (if j₁ = k₁ then (1 : ZMod 2) else 0) * (if j₂ = k₂ then 1 else 0) = 0 := by
      split_ifs with h1 h2
      · exact (heq (by rw [h1, h2])).elim
      · simp
      · simp
      · simp
    have hprod2 : (if j₁ = k₂ then (1 : ZMod 2) else 0) * (if j₂ = k₁ then 1 else 0) = 0 := by
      split_ifs with h1 h2
      · exact (heq (by rw [h1, h2, Finset.pair_comm])).elim
      · simp
      · simp
      · simp
    rw [hprod1, hprod2, add_zero]

private lemma perm_inv_add_two_offdiag_zmod8 {n : ℕ}
    (A : Matrix (Fin n) (Fin n) (ZMod 8)) (hSym : A.IsSymm)
    (hDiag : ∀ i, f2_8 (A i i) = 0) (hA : IsUnit A.det)
    {u v : Fin n} (huv : u ≠ v) :
    let A' := A + (2 : ZMod 8) • (Matrix.single u v (1 : ZMod 8) + Matrix.single v u 1)
    IsUnit A'.det ∧ (A'⁻¹).permanent = (A⁻¹).permanent := by
  intro A'
  let M : Matrix (Fin n) (Fin n) (ZMod 8) := A⁻¹
  have hAM : A * M = 1 := Matrix.mul_nonsing_inv A hA
  have hMA : M * A = 1 := Matrix.nonsing_inv_mul A hA
  have hMsym : M.IsSymm := by rw [Matrix.IsSymm, Matrix.transpose_nonsing_inv, hSym]
  have hMdiag : ∀ i, f2_8 (M i i) = 0 := inv_diag_cast2_zero_zmod8 A hSym hDiag hA
  let E : Matrix (Fin n) (Fin n) (ZMod 8) := Matrix.of fun i j => M i u * M j v + M i v * M j u
  let lam : ZMod 8 := -1 + 2 * M u v
  let M' : Matrix (Fin n) (Fin n) (ZMod 8) := M + (2 : ZMod 8) • (lam • E)
  have h4uu : (4 : ZMod 8) * M u u = 0 := zmod8_four_mul_eq_zero_of_cast2 _ (hMdiag u)
  have h4vv : (4 : ZMod 8) * M v v = 0 := zmod8_four_mul_eq_zero_of_cast2 _ (hMdiag v)
  have hA'M' : A' * M' = 1 := by
    ext i j
    have hAE : (A * E) i j = (if i = u then M j v else 0) + (if i = v then M j u else 0) := by
      simp only [Matrix.mul_apply, E, Matrix.of_apply, mul_add, Finset.sum_add_distrib]
      rw [Finset.sum_congr rfl (fun k _ => by ring : ∀ k ∈ Finset.univ, A i k * (M k u * M j v) = A i k * M k u * M j v),
        Finset.sum_congr rfl (fun k _ => by ring : ∀ k ∈ Finset.univ, A i k * (M k v * M j u) = A i k * M k v * M j u)]
      rw [← Finset.sum_mul, ← Finset.sum_mul]
      have hu' := congrFun (congrFun hAM i) u
      have hv' := congrFun (congrFun hAM i) v
      simp only [Matrix.mul_apply, Matrix.one_apply] at hu' hv'
      rw [hu', hv']
      split_ifs <;> simp
    let S : Matrix (Fin n) (Fin n) (ZMod 8) := Matrix.single u v 1 + Matrix.single v u 1
    have hSM : (S * M) i j = (if i = u then M v j else 0) + (if i = v then M u j else 0) := by
      simp only [S, Matrix.mul_apply, Matrix.add_apply, Matrix.single_apply, add_mul,
        Finset.sum_add_distrib]
      congr 1
      · by_cases hiu : i = u
        · rw [hiu]; simp
        · simp [hiu, Ne.symm hiu]
      · by_cases hiv : i = v
        · rw [hiv]; simp
        · simp [hiv, Ne.symm hiv]
    have hSE : (S * E) i j = (if i = u then E v j else 0) + (if i = v then E u j else 0) := by
      simp only [S, Matrix.mul_apply, Matrix.add_apply, Matrix.single_apply, add_mul,
        Finset.sum_add_distrib]
      congr 1
      · by_cases hiu : i = u
        · rw [hiu]; simp
        · simp [hiu, Ne.symm hiu]
      · by_cases hiv : i = v
        · rw [hiv]; simp
        · simp [hiv, Ne.symm hiv]
    have hmul_exp : A' * M' = A * M + (2 * lam) • (A * E) +
        (2 : ZMod 8) • (S * M) + (4 * lam) • (S * E) := by
      change (A + (2 : ZMod 8) • S) * (M + (2 : ZMod 8) • (lam • E)) = _
      rw [Matrix.add_mul, Matrix.mul_add, Matrix.mul_add, Matrix.mul_smul, Matrix.mul_smul,
        Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_smul, smul_smul, smul_smul,
        smul_smul]
      have h4 : (2 : ZMod 8) * 2 * lam = 4 * lam := by ring
      rw [h4]
      abel
    rw [hmul_exp, hAM]
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, hAE, hSM, hSE,
      hMsym.apply v j, hMsym.apply u j]
    have h4lam : (4 : ZMod 8) * lam = 4 := by
      dsimp only [lam]
      have h8 : (8 : ZMod 8) = 0 := rfl
      linear_combination (M u v - 1) * h8
    rw [h4lam]
    have hEv : (4 : ZMod 8) * E v j = 4 * M u v * M v j := by
      simp only [E, Matrix.of_apply, hMsym.apply v u, hMsym.apply v j]
      linear_combination M j u * h4vv
    have hEu : (4 : ZMod 8) * E u j = 4 * M u v * M u j := by
      simp only [E, Matrix.of_apply, hMsym.apply u j]
      linear_combination M j v * h4uu
    have h2lam : (2 : ZMod 8) * lam + 2 = 4 * M u v := by dsimp only [lam]; ring
    by_cases hiu : i = u
    · rw [hiu]
      simp only [↓reduceIte, huv, add_zero, hEv]
      have h8 : (8 : ZMod 8) = 0 := rfl
      linear_combination M v j * h2lam + (M u v * M v j) * h8
    · by_cases hiv : i = v
      · rw [hiv]
        simp only [huv.symm, ↓reduceIte, zero_add, hEu]
        have h8 : (8 : ZMod 8) = 0 := rfl
        linear_combination M u j * h2lam + (M u v * M u j) * h8
      · simp [hiu, hiv]
  have hA'_unit : IsUnit A'.det := by
    have h1 : A'.det * M'.det = 1 := by rw [← Matrix.det_mul, hA'M', Matrix.det_one]
    exact isUnit_iff_exists_inv.mpr ⟨M'.det, h1⟩
  have hA'_inv : A'⁻¹ = M' := by
    have h1 := congrArg (fun X => A'⁻¹ * X) hA'M'
    rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul A' hA'_unit, Matrix.one_mul, Matrix.mul_one] at h1
    exact h1.symm
  refine ⟨hA'_unit, ?_⟩
  rw [hA'_inv]
  dsimp only [M']
  rw [perm_add_two_smul M (lam • E)]
  let A2 := A.map f2_8
  let M2 := M.map f2_8
  let E2 := E.map f2_8
  have hM2A2 : M2 * A2 = 1 := by
    rw [← Matrix.map_mul, hMA, Matrix.map_one f2_8 (map_zero f2_8) (map_one f2_8)]
  have hA2M2 : A2 * M2 = 1 := by
    rw [← Matrix.map_mul, hAM, Matrix.map_one f2_8 (map_zero f2_8) (map_one f2_8)]
  have hM2sym : M2.IsSymm := by ext a b; simp [M2, hMsym.apply a b]
  have hM2diag : ∀ i, M2 i i = 0 := fun i => hMdiag i
  -- Term 1: 2 * ∑ j, ∑ i, (lam * E i j) * subPerm M {i}ᶜ {j}ᶜ = 4 * M u v
  have hT1 : (2 : ZMod 8) * (∑ j : Fin n, ∑ i : Fin n, (lam • E) i j * subPerm M ({i}ᶜ) ({j}ᶜ)) =
      4 * M u v := by
    have hsplit : (∑ j : Fin n, ∑ i : Fin n, (lam • E) i j * subPerm M ({i}ᶜ) ({j}ᶜ)) =
        2 * lam * (∑ j : Fin n, ∑ i : Fin n, M i u * M j v * subPerm M ({i}ᶜ) ({j}ᶜ)) := by
      have hswap : (∑ j : Fin n, ∑ i : Fin n, M i v * M j u * subPerm M ({i}ᶜ) ({j}ᶜ)) =
          ∑ j : Fin n, ∑ i : Fin n, M i u * M j v * subPerm M ({i}ᶜ) ({j}ᶜ) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
        rw [subPerm_symm hMsym]; ring
      have hre : ∀ j i : Fin n, (lam • E) i j * subPerm M ({i}ᶜ) ({j}ᶜ) =
          lam * (M i u * M j v * subPerm M ({i}ᶜ) ({j}ᶜ)) +
          lam * (M i v * M j u * subPerm M ({i}ᶜ) ({j}ᶜ)) := fun j i => by
        simp only [Matrix.smul_apply, smul_eq_mul, E, Matrix.of_apply]; ring
      simp_rw [hre, Finset.sum_add_distrib, ← Finset.mul_sum]
      rw [hswap]; ring
    rw [hsplit, ← mul_assoc]
    have h4lam : (2 : ZMod 8) * (2 * lam) = 4 := by
      dsimp only [lam]
      have h8 : (8 : ZMod 8) = 0 := rfl
      linear_combination (M u v - 1) * h8
    rw [h4lam]
    refine zmod8_four_mul_eq_of_cast2 _ _ ?_
    simp only [map_sum, map_mul]
    have hterm2 : ∀ j i : Fin n,
        f2_8 (M i u) * f2_8 (M j v) * f2_8 (subPerm M ({i}ᶜ) ({j}ᶜ)) =
        M2 i u * M2 j v * A2 j i := by
      intro j i
      rw [← subPerm_map f2_8 M, jacobi_minor_zmod2 M2 A2 hM2A2 {i} {j} (by simp),
        subPerm_singleton]
      rfl
    simp_rw [hterm2]
    have hcollapse : (∑ j : Fin n, ∑ i : Fin n, M2 i u * M2 j v * A2 j i) = M2 u v := by
      rw [Finset.sum_comm]
      have hinner : ∀ i : Fin n, (∑ j : Fin n, M2 i u * M2 j v * A2 j i) =
          M2 i u * (if i = v then 1 else 0) := by
        intro i
        have hre : ∀ j, M2 i u * M2 j v * A2 j i = M2 i u * (M2 v j * A2 j i) := fun j => by
          rw [hM2sym.apply v j]; ring
        simp_rw [hre, ← Finset.mul_sum]
        congr 1
        have := congrFun (congrFun hM2A2 v) i
        simp only [Matrix.mul_apply, Matrix.one_apply] at this
        rw [this]
        by_cases hiv : i = v
        · simp [hiv]
        · simp [hiv, Ne.symm hiv]
      simp_rw [hinner]
      simp [hM2sym.apply v u]
    exact hcollapse
  -- Term 2: 4 * ∑_{|J|=2} ∑_{|I|=2} subPerm (lam • E) I J * subPerm M Iᶜ Jᶜ = 4 * M u v
  have hT2 : (4 : ZMod 8) *
      (∑ J ∈ Finset.powersetCard 2 (Finset.univ : Finset (Fin n)),
       ∑ I ∈ Finset.powersetCard 2 (Finset.univ : Finset (Fin n)),
         subPerm (lam • E) I J * subPerm M Iᶜ Jᶜ) = 4 * M u v := by
    refine zmod8_four_mul_eq_of_cast2 _ _ ?_
    simp only [map_sum, map_mul]
    have hlam2 : f2_8 lam = 1 := by
      dsimp only [lam]
      have : ∀ x : ZMod 8, f2_8 (-1 + 2 * x) = 1 := by decide
      exact this (M u v)
    have hterm2 : ∀ J ∈ Finset.powersetCard 2 (Finset.univ : Finset (Fin n)),
        ∀ I ∈ Finset.powersetCard 2 (Finset.univ : Finset (Fin n)),
        f2_8 (subPerm (lam • E) I J) * f2_8 (subPerm M Iᶜ Jᶜ) =
        subPerm M2 J {u, v} * (subPerm A2 J I * subPerm M2 I {u, v}) := by
      intro J hJ I hI
      rw [subPerm_smul, map_mul, map_pow, hlam2, one_pow, one_mul, ← subPerm_map f2_8 E,
        ← subPerm_map f2_8 M, jacobi_minor_zmod2 M2 A2 hM2A2 I J
          (by rw [(Finset.mem_powersetCard.mp hI).2, (Finset.mem_powersetCard.mp hJ).2])]
      obtain ⟨i₁, i₂, hi, rfl⟩ := Finset.card_eq_two.mp (Finset.mem_powersetCard.mp hI).2
      obtain ⟨j₁, j₂, hj, rfl⟩ := Finset.card_eq_two.mp (Finset.mem_powersetCard.mp hJ).2
      have hE2_pair : subPerm E2 {i₁, i₂} {j₁, j₂} =
          subPerm M2 {i₁, i₂} {u, v} * subPerm M2 {j₁, j₂} {u, v} := by
        rw [subPerm_pair E2 hi hj, subPerm_pair M2 hi huv, subPerm_pair M2 hj huv]
        simp only [E2, E, Matrix.map_apply, Matrix.of_apply, map_add, map_mul]
        change (M2 i₁ u * M2 j₁ v + M2 i₁ v * M2 j₁ u) * (M2 i₂ u * M2 j₂ v + M2 i₂ v * M2 j₂ u) +
            (M2 i₁ u * M2 j₂ v + M2 i₁ v * M2 j₂ u) * (M2 i₂ u * M2 j₁ v + M2 i₂ v * M2 j₁ u) =
            (M2 i₁ u * M2 i₂ v + M2 i₁ v * M2 i₂ u) * (M2 j₁ u * M2 j₂ v + M2 j₁ v * M2 j₂ u)
        have hdiff : (M2 i₁ u * M2 j₁ v + M2 i₁ v * M2 j₁ u) * (M2 i₂ u * M2 j₂ v + M2 i₂ v * M2 j₂ u) +
            (M2 i₁ u * M2 j₂ v + M2 i₁ v * M2 j₂ u) * (M2 i₂ u * M2 j₁ v + M2 i₂ v * M2 j₁ u) =
            (M2 i₁ u * M2 i₂ v + M2 i₁ v * M2 i₂ u) * (M2 j₁ u * M2 j₂ v + M2 j₁ v * M2 j₂ u) +
            (M2 i₁ u * M2 i₂ u * M2 j₁ v * M2 j₂ v + M2 i₁ u * M2 i₂ u * M2 j₁ v * M2 j₂ v) +
            (M2 i₁ v * M2 i₂ v * M2 j₁ u * M2 j₂ u + M2 i₁ v * M2 i₂ v * M2 j₁ u * M2 j₂ u) := by ring
        rw [hdiff, zmod2_add_self, zmod2_add_self, add_zero, add_zero]
      rw [hE2_pair]; ring
    have hsum_eq : ∑ J ∈ Finset.powersetCard 2 (Finset.univ : Finset (Fin n)),
        ∑ I ∈ Finset.powersetCard 2 (Finset.univ : Finset (Fin n)),
          f2_8 (subPerm (lam • E) I J) * f2_8 (subPerm M Iᶜ Jᶜ) =
        ∑ J ∈ Finset.powersetCard 2 (Finset.univ : Finset (Fin n)),
          subPerm M2 J {u, v} *
            (∑ I ∈ Finset.powersetCard 2 (Finset.univ : Finset (Fin n)),
              subPerm A2 J I * subPerm M2 I {u, v}) := by
      refine Finset.sum_congr rfl fun J hJ => ?_
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun I hI => hterm2 J hJ I hI
    rw [hsum_eq]
    have hcb_app : ∀ J ∈ Finset.powersetCard 2 (Finset.univ : Finset (Fin n)),
        subPerm M2 J {u, v} *
          (∑ I ∈ Finset.powersetCard 2 (Finset.univ : Finset (Fin n)),
            subPerm A2 J I * subPerm M2 I {u, v}) =
        if J = {u, v} then subPerm M2 {u, v} {u, v} else 0 := by
      intro J hJ
      rw [cauchy_binet_two_zmod2 A2 M2 hA2M2 J {u, v} (Finset.mem_powersetCard.mp hJ).2
        (Finset.card_pair huv)]
      split_ifs with h
      · rw [h, mul_one]
      · rw [mul_zero]
    rw [Finset.sum_congr rfl hcb_app, Finset.sum_ite_eq']
    have huv_mem : ({u, v} : Finset (Fin n)) ∈ Finset.powersetCard 2 Finset.univ :=
      Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, Finset.card_pair huv⟩
    simp only [huv_mem, ↓reduceIte]
    rw [subPerm_pair M2 huv huv, hM2diag u, zero_mul, zero_add, hM2sym.apply v u, zmod2_sq,
      hM2sym.apply u v]
    rfl
  rw [hT1, hT2, add_assoc]
  have h8 : (4 : ZMod 8) * M u v + 4 * M u v = 0 := by
    have : (4 : ZMod 8) + 4 = 0 := rfl
    linear_combination M u v * this
  rw [h8, add_zero]

private lemma perm_inv_add_four_diag_zmod8 {n : ℕ}
    (A : Matrix (Fin n) (Fin n) (ZMod 8)) (hSym : A.IsSymm)
    (hDiag : ∀ i, f2_8 (A i i) = 0) (hA : IsUnit A.det) (u : Fin n) :
    let A' := A + (4 : ZMod 8) • Matrix.single u u (1 : ZMod 8)
    IsUnit A'.det ∧ (A'⁻¹).permanent = (A⁻¹).permanent := by
  intro A'
  let M : Matrix (Fin n) (Fin n) (ZMod 8) := A⁻¹
  have hAM : A * M = 1 := Matrix.mul_nonsing_inv A hA
  have hMA : M * A = 1 := Matrix.nonsing_inv_mul A hA
  have hMsym : M.IsSymm := by rw [Matrix.IsSymm, Matrix.transpose_nonsing_inv, hSym]
  have hMdiag : ∀ i, f2_8 (M i i) = 0 := inv_diag_cast2_zero_zmod8 A hSym hDiag hA
  let E : Matrix (Fin n) (Fin n) (ZMod 8) := Matrix.of fun i j => -(2 : ZMod 8) * (M i u * M j u)
  let M' : Matrix (Fin n) (Fin n) (ZMod 8) := M + (2 : ZMod 8) • E
  have hA'M' : A' * M' = 1 := by
    ext i j
    have hAE : (A * E) i j = if i = u then -(2 : ZMod 8) * M j u else 0 := by
      simp only [Matrix.mul_apply, E, Matrix.of_apply]
      have hre : ∀ k, A i k * (-(2 : ZMod 8) * (M k u * M j u)) = (A i k * M k u) * (-(2 : ZMod 8) * M j u) :=
        fun k => by ring
      simp_rw [hre, ← Finset.sum_mul]
      have hu' := congrFun (congrFun hAM i) u
      simp only [Matrix.mul_apply, Matrix.one_apply] at hu'
      rw [hu']; split_ifs <;> simp
    have hSM : (Matrix.single u u (1 : ZMod 8) * M) i j = if i = u then M u j else 0 := by
      simp only [Matrix.mul_apply, Matrix.single_apply]
      by_cases hiu : i = u
      · rw [hiu]; simp
      · simp [hiu, Ne.symm hiu]
    have hSE : (Matrix.single u u (1 : ZMod 8) * E) i j = if i = u then E u j else 0 := by
      simp only [Matrix.mul_apply, Matrix.single_apply]
      by_cases hiu : i = u
      · rw [hiu]; simp
      · simp [hiu, Ne.symm hiu]
    have hmul_exp : A' * M' = A * M + (2 : ZMod 8) • (A * E) +
        (4 : ZMod 8) • (Matrix.single u u 1 * M) + (8 : ZMod 8) • (Matrix.single u u 1 * E) := by
      dsimp only [A', M']
      rw [Matrix.add_mul, Matrix.mul_add, Matrix.mul_add, Matrix.mul_smul, Matrix.smul_mul,
        Matrix.smul_mul, Matrix.mul_smul, smul_smul]
      have h8 : (4 : ZMod 8) * 2 = 8 := by decide
      rw [h8]; abel
    have h80 : (8 : ZMod 8) = 0 := rfl
    rw [hmul_exp, hAM, h80, zero_smul, add_zero]
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, hAE, hSM, hMsym.apply u j]
    split_ifs <;> ring
  have hA'_unit : IsUnit A'.det :=
    isUnit_iff_exists_inv.mpr ⟨M'.det, by rw [← Matrix.det_mul, hA'M', Matrix.det_one]⟩
  have hA'_inv : A'⁻¹ = M' := by
    have h1 := congrArg (fun X => A'⁻¹ * X) hA'M'
    rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul A' hA'_unit, Matrix.one_mul, Matrix.mul_one] at h1
    exact h1.symm
  refine ⟨hA'_unit, ?_⟩
  rw [hA'_inv]
  dsimp only [M']
  rw [perm_add_two_smul M E]
  have hT2 : (4 : ZMod 8) *
      (∑ J ∈ Finset.powersetCard 2 (Finset.univ : Finset (Fin n)),
       ∑ I ∈ Finset.powersetCard 2 (Finset.univ : Finset (Fin n)),
         subPerm E I J * subPerm M Iᶜ Jᶜ) = 0 := by
    refine zmod8_four_mul_eq_zero_of_cast2 _ ?_
    simp only [map_sum, map_mul]
    refine Finset.sum_eq_zero fun J hJ => Finset.sum_eq_zero fun I hI => ?_
    have hE2 : E.map f2_8 = 0 := by
      ext a b; simp only [E, Matrix.map_apply, Matrix.of_apply, Matrix.zero_apply, map_mul, map_neg]
      have : f2_8 2 = 0 := by decide
      rw [this]; simp
    rw [← subPerm_map f2_8 E, hE2]
    obtain ⟨j₁, j₂, hj, rfl⟩ := Finset.card_eq_two.mp (Finset.mem_powersetCard.mp hJ).2
    obtain ⟨i₁, i₂, hi, rfl⟩ := Finset.card_eq_two.mp (Finset.mem_powersetCard.mp hI).2
    rw [subPerm_pair (0 : Matrix (Fin n) (Fin n) (ZMod 2)) hi hj]
    simp
  have hT1 : (2 : ZMod 8) * (∑ j : Fin n, ∑ i : Fin n, E i j * subPerm M ({i}ᶜ) ({j}ᶜ)) = 0 := by
    have hpull : (2 : ZMod 8) * (∑ j : Fin n, ∑ i : Fin n, E i j * subPerm M ({i}ᶜ) ({j}ᶜ)) =
        4 * (∑ j : Fin n, ∑ i : Fin n, M i u * M j u * subPerm M ({i}ᶜ) ({j}ᶜ)) := by
      simp only [E, Matrix.of_apply, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
      have h4neg : (2 : ZMod 8) * -(2 : ZMod 8) = 4 := by decide
      linear_combination (M i u * M j u * subPerm M ({i}ᶜ) ({j}ᶜ)) * h4neg
    rw [hpull]
    refine zmod8_four_mul_eq_zero_of_cast2 _ ?_
    let A2 := A.map f2_8
    let M2 := M.map f2_8
    have hM2A2 : M2 * A2 = 1 := by
      rw [← Matrix.map_mul, hMA, Matrix.map_one f2_8 (map_zero f2_8) (map_one f2_8)]
    have hM2sym : M2.IsSymm := by ext a b; simp [M2, hMsym.apply a b]
    simp only [map_sum, map_mul]
    have hterm2 : ∀ j i : Fin n,
        f2_8 (M i u) * f2_8 (M j u) * f2_8 (subPerm M ({i}ᶜ) ({j}ᶜ)) =
        M2 i u * M2 j u * A2 j i := by
      intro j i
      rw [← subPerm_map f2_8 M, jacobi_minor_zmod2 M2 A2 hM2A2 {i} {j} (by simp),
        subPerm_singleton]
      rfl
    simp_rw [hterm2]
    rw [Finset.sum_comm]
    have hinner : ∀ i : Fin n, (∑ j : Fin n, M2 i u * M2 j u * A2 j i) =
        M2 i u * (if i = u then 1 else 0) := by
      intro i
      have hre : ∀ j, M2 i u * M2 j u * A2 j i = M2 i u * (M2 u j * A2 j i) := fun j => by
        rw [hM2sym.apply u j]; ring
      simp_rw [hre, ← Finset.mul_sum]
      congr 1
      have := congrFun (congrFun hM2A2 u) i
      simp only [Matrix.mul_apply, Matrix.one_apply] at this
      rw [this]
      by_cases hiu : i = u
      · simp [hiu]
      · simp [hiu, Ne.symm hiu]
    simp_rw [hinner]
    simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', mem_univ, ↓reduceIte]
    exact hMdiag u
  rw [hT1, hT2, add_zero, add_zero]

private lemma perm_inv_add_two_mul_offdiag_zmod8 {n : ℕ} (k : ℕ)
    (A : Matrix (Fin n) (Fin n) (ZMod 8)) (hSym : A.IsSymm)
    (hDiag : ∀ i, f2_8 (A i i) = 0) (hA : IsUnit A.det)
    {u v : Fin n} (huv : u ≠ v) :
    let A' := A + ((2 * k : ℕ) : ZMod 8) • (Matrix.single u v (1 : ZMod 8) + Matrix.single v u 1)
    IsUnit A'.det ∧ (A'⁻¹).permanent = (A⁻¹).permanent := by
  induction k generalizing A with
  | zero => simp [hA]
  | succ k ih =>
    intro A'
    let A1 := A + (2 : ZMod 8) • (Matrix.single u v (1 : ZMod 8) + Matrix.single v u 1)
    have h1 := perm_inv_add_two_offdiag_zmod8 A hSym hDiag hA huv
    have hA1_sym : A1.IsSymm := by
      ext i j; simp only [A1, Matrix.transpose_apply, Matrix.add_apply, Matrix.smul_apply,
        Matrix.single_apply, smul_eq_mul, hSym.apply i j]
      by_cases h1' : i = u <;> by_cases h2' : j = v <;> by_cases h3' : i = v <;> by_cases h4' : j = u <;>
        simp [h1', h2', h3', h4', Ne.symm, eq_comm, add_comm]
    have hA1_diag : ∀ i, f2_8 (A1 i i) = 0 := by
      intro i
      simp only [A1, Matrix.add_apply, Matrix.smul_apply, Matrix.single_apply, smul_eq_mul, map_add, map_mul]
      have h20 : f2_8 2 = 0 := by decide
      rw [hDiag i, h20, zero_mul, add_zero]
    have hstep := ih A1 hA1_sym hA1_diag h1.1
    have heq : A' = A1 + ((2 * k : ℕ) : ZMod 8) • (Matrix.single u v (1 : ZMod 8) + Matrix.single v u 1) := by
      ext i j
      simp only [A', A1, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
      push_cast; ring
    rw [heq]
    exact ⟨hstep.1, hstep.2.trans h1.2⟩

private lemma perm_inv_eq_of_cast2_eq {n : ℕ}
    (A B : Matrix (Fin n) (Fin n) (ZMod 8))
    (hAsym : A.IsSymm) (hBsym : B.IsSymm)
    (hAdiag : ∀ i, A i i = 0 ∨ A i i = 4) (hBdiag : ∀ i, B i i = 0 ∨ B i i = 4)
    (hA : IsUnit A.det) (hmod2 : A.map f2_8 = B.map f2_8) :
    IsUnit B.det ∧ (B⁻¹).permanent = (A⁻¹).permanent := by
  -- Induct on the number of pairs (i, j) with i ≤ j where A i j ≠ B i j
  let diffSet (X Y : Matrix (Fin n) (Fin n) (ZMod 8)) : Finset (Fin n × Fin n) :=
    Finset.univ.filter fun p => p.1 ≤ p.2 ∧ X p.1 p.2 ≠ Y p.1 p.2
  have hmain : ∀ m : ℕ, ∀ X : Matrix (Fin n) (Fin n) (ZMod 8),
      (diffSet X B).card = m → X.IsSymm → (∀ i, X i i = 0 ∨ X i i = 4) →
      IsUnit X.det → X.map f2_8 = B.map f2_8 →
      IsUnit B.det ∧ (B⁻¹).permanent = (X⁻¹).permanent := by
    intro m
    induction m with
    | zero =>
      intro X hm hXsym _ hX _
      have hXB : X = B := by
        ext i j
        have hempty : diffSet X B = ∅ := Finset.card_eq_zero.mp hm
        rcases le_total i j with hij | hji
        · by_contra hne
          have hmem : (i, j) ∈ diffSet X B := mem_filter.mpr ⟨mem_univ _, hij, hne⟩
          rw [hempty] at hmem; exact Finset.notMem_empty _ hmem
        · by_contra hne
          have hne' : X j i ≠ B j i := by rwa [hXsym.apply i j, hBsym.apply i j]
          have hmem : (j, i) ∈ diffSet X B := mem_filter.mpr ⟨mem_univ _, hji, hne'⟩
          rw [hempty] at hmem; exact Finset.notMem_empty _ hmem
      subst hXB; exact ⟨hX, rfl⟩
    | succ m ih =>
      intro X hm hXsym hXdiag hX hXmod
      have hne : (diffSet X B).Nonempty := Finset.card_pos.mp (by omega)
      obtain ⟨⟨u, v⟩, huv_mem⟩ := hne
      have huv_le : u ≤ v := (mem_filter.mp huv_mem).2.1
      have huv_ne_val : X u v ≠ B u v := (mem_filter.mp huv_mem).2.2
      have hXdiag2 : ∀ i, f2_8 (X i i) = 0 := by
        intro i; rcases hXdiag i with h | h <;> rw [h] <;> decide
      by_cases huv : u = v
      · subst huv
        let X' := X + (4 : ZMod 8) • Matrix.single u u (1 : ZMod 8)
        have hstep := perm_inv_add_four_diag_zmod8 X hXsym hXdiag2 hX u
        have hX'u : X' u u = B u u := by
          simp only [X', Matrix.add_apply, Matrix.smul_apply, Matrix.single_apply, smul_eq_mul,
            and_self, ↓reduceIte, mul_one]
          rcases hXdiag u with h1 | h1 <;> rcases hBdiag u with h2 | h2
          · exact (huv_ne_val (h1.trans h2.symm)).elim
          · rw [h1, h2]; decide
          · rw [h1, h2]; decide
          · exact (huv_ne_val (h1.trans h2.symm)).elim
        have hX'sym : X'.IsSymm := by
          ext i j; simp only [X', Matrix.transpose_apply, Matrix.add_apply, Matrix.smul_apply,
            Matrix.single_apply, smul_eq_mul, hXsym.apply i j, and_comm]
        have hX'diag : ∀ i, X' i i = 0 ∨ X' i i = 4 := by
          intro i
          by_cases hi : i = u
          · rw [hi, hX'u]; exact hBdiag u
          · simp [X', Ne.symm hi, hXdiag i]
        have hX'mod : X'.map f2_8 = B.map f2_8 := by
          rw [← hXmod]; ext i j
          simp only [X', Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, map_add, map_mul]
          have : f2_8 4 = 0 := by decide
          rw [this, zero_mul, add_zero]
        have hdiff_eq : diffSet X' B = (diffSet X B).erase (u, u) := by
          ext ⟨i, j⟩
          simp only [diffSet, mem_filter, mem_univ, true_and, mem_erase]
          by_cases hij : i = u ∧ j = u
          · rcases hij with ⟨rfl, rfl⟩; simp [hX'u]
          · have hnot : ¬(u = i ∧ u = j) := fun ⟨h1, h2⟩ => hij ⟨h1.symm, h2.symm⟩
            have hne : (i, j) ≠ (u, u) := fun h => hij (Prod.mk.inj h)
            simp [X', hnot, hne]
        have hcard : (diffSet X' B).card = m := by
          rw [hdiff_eq, Finset.card_erase_of_mem huv_mem, hm]; omega
        have hres := ih X' hcard hX'sym hX'diag hstep.1 hX'mod
        exact ⟨hres.1, hres.2.trans hstep.2⟩
      · have hcast_eq : f2_8 (X u v) = f2_8 (B u v) := by
          have := congrFun (congrFun hXmod u) v
          simpa using this
        have hexk : ∃ k : ℕ, X u v + ((2 * k : ℕ) : ZMod 8) = B u v := by
          have hgen : ∀ a b : ZMod 8, f2_8 a = f2_8 b → ∃ k < 4, a + ((2 * k : ℕ) : ZMod 8) = b := by
            decide
          obtain ⟨k, _, hk⟩ := hgen (X u v) (B u v) hcast_eq
          exact ⟨k, hk⟩
        obtain ⟨k, hk⟩ := hexk
        let X' := X + ((2 * k : ℕ) : ZMod 8) • (Matrix.single u v (1 : ZMod 8) + Matrix.single v u 1)
        have hstep := perm_inv_add_two_mul_offdiag_zmod8 k X hXsym hXdiag2 hX huv
        have hX'uv : X' u v = B u v := by
          simpa [X', huv, Ne.symm huv] using hk
        have hX'sym : X'.IsSymm := by
          ext i j; simp only [X', Matrix.transpose_apply, Matrix.add_apply, Matrix.smul_apply,
            Matrix.single_apply, smul_eq_mul, hXsym.apply i j]
          by_cases h1 : i = u <;> by_cases h2 : j = v <;> by_cases h3 : i = v <;> by_cases h4 : j = u <;>
            simp [h1, h2, h3, h4, Ne.symm, eq_comm, add_comm]
        have hX'diag : ∀ i, X' i i = 0 ∨ X' i i = 4 := by
          intro i
          have h1 : ¬(u = i ∧ v = i) := fun ⟨h1, h2⟩ => huv (h1.trans h2.symm)
          have h2 : ¬(v = i ∧ u = i) := fun ⟨h1, h2⟩ => huv (h2.trans h1.symm)
          simp [X', h1, h2, hXdiag i]
        have hX'mod : X'.map f2_8 = B.map f2_8 := by
          rw [← hXmod]; ext i j
          simp only [X', Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul,
            map_add, map_mul, Nat.cast_mul, Nat.cast_ofNat]
          have : f2_8 2 = 0 := by decide
          rw [this, zero_mul, zero_mul, add_zero]
        have hdiff_eq : diffSet X' B = (diffSet X B).erase (u, v) := by
          ext ⟨i, j⟩
          simp only [diffSet, mem_filter, mem_univ, true_and, mem_erase]
          by_cases hij : i = u ∧ j = v
          · rcases hij with ⟨rfl, rfl⟩; simp [hX'uv]
          · have hnot1 : ¬(u = i ∧ v = j) := fun ⟨h1, h2⟩ => hij ⟨h1.symm, h2.symm⟩
            have hnot2 : i ≤ j → ¬(v = i ∧ u = j) := fun hle ⟨h1, h2⟩ => by
              subst h1 h2; exact huv (le_antisymm huv_le hle)
            have hne : (i, j) ≠ (u, v) := fun h => hij (Prod.mk.inj h)
            constructor
            · rintro ⟨hle, hne'⟩
              refine ⟨hne, hle, ?_⟩
              simpa [X', hnot1, hnot2 hle] using hne'
            · rintro ⟨_, hle, hne'⟩
              refine ⟨hle, ?_⟩
              simpa [X', hnot1, hnot2 hle] using hne'
        have hcard : (diffSet X' B).card = m := by
          rw [hdiff_eq, Finset.card_erase_of_mem huv_mem, hm]; omega
        have hres := ih X' hcard hX'sym hX'diag hstep.1 hX'mod
        exact ⟨hres.1, hres.2.trans hstep.2⟩
  exact hmain (diffSet A B).card A rfl hAsym hAdiag hA hmod2

/-! #### Shear invariance (`perm((Eᵀ A E)⁻¹) = perm(A⁻¹)` when `2 ∣ A r s`) -/

private lemma permanent_updateRow_add {n : ℕ} {R : Type*} [CommSemiring R]
    (M : Matrix (Fin n) (Fin n) R) (s : Fin n) (u v : Fin n → R) :
    (M.updateRow s (u + v)).permanent =
      (M.updateRow s u).permanent + (M.updateRow s v).permanent := by
  simp only [Matrix.permanent, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun σ _ => ?_
  have hmem : σ⁻¹ s ∈ (Finset.univ : Finset (Fin n)) := mem_univ _
  rw [← Finset.mul_prod_erase _ _ hmem, ← Finset.mul_prod_erase _ _ hmem,
    ← Finset.mul_prod_erase _ _ hmem]
  have hss : σ (σ⁻¹ s) = s := Equiv.apply_symm_apply σ s
  have hrest : ∀ i ∈ Finset.univ.erase (σ⁻¹ s),
      (M.updateRow s (u + v)) (σ i) i = M (σ i) i ∧
      (M.updateRow s u) (σ i) i = M (σ i) i ∧
      (M.updateRow s v) (σ i) i = M (σ i) i := by
    intro i hi
    have hne : σ i ≠ s := fun h => (mem_erase.mp hi).1 (by
      have hinv : σ⁻¹ (σ i) = i := Equiv.symm_apply_apply σ i
      rw [← hinv, h])
    simp [Matrix.updateRow_ne hne]
  rw [Finset.prod_congr rfl (fun i hi => (hrest i hi).1),
    Finset.prod_congr rfl (fun i hi => (hrest i hi).2.1),
    Finset.prod_congr rfl (fun i hi => (hrest i hi).2.2),
    hss, Matrix.updateRow_self, Matrix.updateRow_self, Matrix.updateRow_self,
    Pi.add_apply, add_mul]

private lemma permanent_updateCol_add {n : ℕ} {R : Type*} [CommSemiring R]
    (M : Matrix (Fin n) (Fin n) R) (s : Fin n) (u v : Fin n → R) :
    (M.updateCol s (u + v)).permanent =
      (M.updateCol s u).permanent + (M.updateCol s v).permanent := by
  have hT : ∀ w : Fin n → R, (M.updateCol s w)ᵀ = Mᵀ.updateRow s w := fun w => by
    ext i j; by_cases h : i = s <;> simp [h]
  rw [← Matrix.permanent_transpose, hT (u + v), permanent_updateRow_add,
    ← hT u, ← hT v, Matrix.permanent_transpose, Matrix.permanent_transpose]

private lemma det_four_alt_zmod2 :
    ∀ a02 a03 a12 a13 a23 : ZMod 2,
      (Matrix.of ![![(0 : ZMod 2), 0, a02, a03],
                   ![0, 0, a12, a13],
                   ![a02, a12, 0, a23],
                   ![a03, a13, a23, 0]]).det = a02 * a13 + a03 * a12 := by
  intro a02 a03 a12 a13 a23
  rw [Matrix.det_succ_row_zero, Fin.sum_univ_four]
  simp [Matrix.det_fin_three, Fin.succAbove]
  revert a02 a03 a12 a13 a23; decide

private lemma det_skew_odd_zmod2 {k : ℕ} (M : Matrix (Fin k) (Fin k) (ZMod 2))
    (hSym : M.IsSymm) (hDiag : ∀ i, M i i = 0) (hodd : Odd k) : M.det = 0 := by
  by_contra hne
  have h1 : M.det = 1 := by
    generalize M.det = d at hne ⊢
    revert d hne; decide
  let B : Matrix (Fin k) (Fin k) (ZMod 4) := Matrix.of fun i j =>
    if i < j then (if M i j = 0 then 0 else 1)
    else if j < i then (if M i j = 0 then 0 else -1)
    else 0
  have hB_skew : IsSkew B := by
    constructor
    · intro i; simp [B]
    · intro i j
      rcases lt_trichotomy i j with h | rfl | h
      · simp only [B, Matrix.of_apply, h, ↓reduceIte, not_lt_of_gt h, hSym.apply j i]
        split_ifs <;> simp
      · simp [B]
      · simp only [B, Matrix.of_apply, h, ↓reduceIte, not_lt_of_gt h, hSym.apply j i]
        split_ifs <;> simp
  let f2_4 : ZMod 4 →+* ZMod 2 := ZMod.castHom (by norm_num : 2 ∣ 4) (ZMod 2)
  have hmap : B.map f2_4 = M := by
    ext i j
    simp only [B, Matrix.map_apply, Matrix.of_apply]
    rcases lt_trichotomy i j with h | rfl | h
    · simp only [h, ↓reduceIte]
      generalize M i j = y; revert y; decide
    · simp [hDiag i]
    · simp only [not_lt_of_gt h, ↓reduceIte, h]
      generalize M i j = y; revert y; decide
  have hB_unit : IsUnit B.det := by
    apply zmod4_isUnit_of_cast2_eq_one
    rw [← det_map f2_4 B, hmap, h1]
  have hev := even_of_isUnit_det_skew_zmod4 hB_skew hB_unit
  exact (Nat.not_even_iff_odd.mpr hodd) hev

private lemma subtype_ext_val {α : Type*} {p q : α → Prop} {a b : Subtype p}
    {x y : Subtype q} (h : x = y) (ha : a.1 = x.1 := by rfl) (hb : b.1 = y.1 := by rfl) : a = b :=
  Subtype.ext (ha.trans ((congrArg Subtype.val h).trans hb.symm))

private lemma subPerm_compl_row_expansion_zmod2 {n : ℕ}
    (M : Matrix (Fin n) (Fin n) (ZMod 2)) (hSym : M.IsSymm) (hDiag : ∀ i, M i i = 0)
    (heven : Even n) {r s : Fin n} (hrs : r ≠ s) :
    let T := (Finset.univ.erase r).erase s
    ∑ b ∈ T, M r b * subPerm M T (insert r (T.erase b)) = 0 := by
  intro T
  let U : Finset (Fin n) := Finset.univ.erase s
  have hU_eq : U = insert r T := by
    ext x; simp only [U, T, mem_erase, mem_univ, and_true, mem_insert]
    by_cases hxr : x = r
    · subst hxr; simp [hrs]
    · simp [hxr]
  have hrT : r ∉ T := by simp [T]
  have hU_card : U.card = n - 1 := by
    rw [Finset.card_erase_of_mem (mem_univ s), Finset.card_univ, Fintype.card_fin]
  have hU_odd : Odd U.card := by
    rw [hU_card]
    obtain ⟨m, hm⟩ := heven
    have hpos : 0 < n := Fin.pos r
    refine ⟨m - 1, by omega⟩
  have hdet0 : subPerm M U U = 0 := by
    have hcard_eq : Fintype.card {x // x ∈ U} = Fintype.card (Fin U.card) := by simp
    obtain ⟨e⟩ := Fintype.truncEquivOfCardEq hcard_eq
    rw [subPerm_eq_det_zmod2 M U U (Equiv.refl _)]
    dsimp only [Equiv.refl_apply]
    let Msub : Matrix (Fin U.card) (Fin U.card) (ZMod 2) :=
      (Matrix.of fun a b : {x // x ∈ U} => M a.1 b.1).submatrix e.symm e.symm
    have hdet_eq : (Matrix.of fun a b : {x // x ∈ U} => M a.1 b.1).det = Msub.det :=
      (Matrix.det_submatrix_equiv_self e.symm _).symm
    rw [hdet_eq]
    exact det_skew_odd_zmod2 Msub (by ext a b; simp [Msub, hSym.apply]) (fun a => hDiag _) hU_odd
  -- Expand subPerm M U U along row r (which has M r r = 0)
  have hexp : subPerm M U U = ∑ b ∈ T, M r b * subPerm M T (insert r (T.erase b)) := by
    rw [hU_eq]
    unfold subPerm
    -- Every bijection e : insert r T ≃ insert r T maps some b ∈ insert r T to r; if b = r, M r r = 0
    let inv_r : ({x // x ∈ insert r T} ≃ {y // y ∈ insert r T}) → Fin n :=
      fun e => (e.symm ⟨r, mem_insert_self r T⟩).1
    rw [← Finset.sum_fiberwise_of_maps_to (g := inv_r) (t := insert r T)
      (fun e _ => (e.symm ⟨r, mem_insert_self r T⟩).2)]
    rw [Finset.sum_insert hrT]
    have hr0 : ∑ e ∈ Finset.univ.filter (fun e : {x // x ∈ insert r T} ≃ {y // y ∈ insert r T} =>
        inv_r e = r), ∏ x, M (e x).1 x.1 = 0 := by
      refine Finset.sum_eq_zero fun e he => ?_
      have hre : e ⟨r, mem_insert_self r T⟩ = ⟨r, mem_insert_self r T⟩ := by
        have h1 : e.symm ⟨r, mem_insert_self r T⟩ = ⟨r, mem_insert_self r T⟩ :=
          Subtype.ext (mem_filter.mp he).2
        exact (Equiv.eq_symm_apply e).mp h1.symm
      exact Finset.prod_eq_zero (mem_univ ⟨r, mem_insert_self r T⟩) (by rw [hre]; exact hDiag r)
    rw [hr0, zero_add]
    refine Finset.sum_congr rfl fun b hb => ?_
    have hbr : b ≠ r := fun h => hrT (h ▸ hb)
    rw [Finset.mul_sum]
    have hU_erase : (insert r T).erase b = insert r (T.erase b) := by
      ext x; simp only [mem_erase, mem_insert]; constructor
      · rintro ⟨hxb, rfl | hxT⟩
        · exact Or.inl rfl
        · exact Or.inr ⟨hxb, hxT⟩
      · rintro (rfl | ⟨hxb, hxT⟩)
        · exact ⟨hbr.symm, Or.inl rfl⟩
        · exact ⟨hxb, Or.inr hxT⟩
    have hmem_erase : ∀ {z : Fin n}, z ∈ insert r (T.erase b) → z ≠ b ∧ z ∈ insert r T := by
      intro z hz; rw [← hU_erase, mem_erase] at hz; exact hz
    refine Finset.sum_bij'
      (fun e he =>
        { toFun := fun x => ⟨(e ⟨x.1, (hmem_erase x.2).2⟩).1, by
            have hne : (e ⟨x.1, (hmem_erase x.2).2⟩).1 ≠ r := by
              intro h
              have h2 : e ⟨x.1, (hmem_erase x.2).2⟩ = ⟨r, mem_insert_self r T⟩ := Subtype.ext h
              have h3 : (e.symm ⟨r, mem_insert_self r T⟩).1 = x.1 := by
                rw [← h2, Equiv.symm_apply_apply]
              exact (hmem_erase x.2).1 (h3.symm.trans (mem_filter.mp he).2)
            exact (mem_insert.mp (e _).2).resolve_left hne⟩
          invFun := fun y => ⟨(e.symm ⟨y.1, mem_insert_of_mem y.2⟩).1, by
            rw [← hU_erase, mem_erase]
            refine ⟨?_, (e.symm ⟨y.1, mem_insert_of_mem y.2⟩).2⟩
            intro h
            have h2 : e.symm ⟨y.1, mem_insert_of_mem y.2⟩ = e.symm ⟨r, mem_insert_self r T⟩ :=
              Subtype.ext (h.trans (mem_filter.mp he).2.symm)
            have h3 : y.1 = r := congrArg Subtype.val (e.symm.injective h2)
            exact hrT (h3 ▸ y.2)⟩
          left_inv := fun x =>
            subtype_ext_val
              ((congrArg e.symm (Subtype.ext rfl)).trans (Equiv.symm_apply_apply e ⟨x.1, (hmem_erase x.2).2⟩))
          right_inv := fun y =>
            subtype_ext_val
              ((congrArg e (Subtype.ext rfl)).trans (Equiv.apply_symm_apply e ⟨y.1, mem_insert_of_mem y.2⟩)) })
      (fun f _ =>
        { toFun := fun x => if hx : x.1 = b then ⟨r, mem_insert_self r T⟩
            else ⟨(f ⟨x.1, by rw [← hU_erase]; exact mem_erase.mpr ⟨hx, x.2⟩⟩).1,
              mem_insert_of_mem (f _).2⟩
          invFun := fun y => if hy : y.1 = r then ⟨b, mem_insert_of_mem hb⟩
            else ⟨(f.symm ⟨y.1, (mem_insert.mp y.2).resolve_left hy⟩).1,
              (hmem_erase (f.symm ⟨y.1, (mem_insert.mp y.2).resolve_left hy⟩).2).2⟩
          left_inv := fun x => by
            dsimp only
            by_cases hx : x.1 = b
            · simp only [hx, ↓reduceDIte]; exact Subtype.ext hx.symm
            · have hne : (f ⟨x.1, by rw [← hU_erase]; exact mem_erase.mpr ⟨hx, x.2⟩⟩).1 ≠ r :=
                fun h => hrT (h ▸ (f _).2)
              simp only [hx, ↓reduceDIte, hne]
              exact subtype_ext_val
                ((congrArg f.symm (Subtype.ext rfl)).trans
                  (Equiv.symm_apply_apply f ⟨x.1, by rw [← hU_erase]; exact mem_erase.mpr ⟨hx, x.2⟩⟩))
          right_inv := fun y => by
            dsimp only
            by_cases hy : y.1 = r
            · simp only [hy, ↓reduceDIte]; exact Subtype.ext hy.symm
            · have hne : (f.symm ⟨y.1, (mem_insert.mp y.2).resolve_left hy⟩).1 ≠ b :=
                (hmem_erase (f.symm ⟨y.1, (mem_insert.mp y.2).resolve_left hy⟩).2).1
              simp only [hy, ↓reduceDIte, hne]
              exact subtype_ext_val
                ((congrArg f (Subtype.ext rfl)).trans
                  (Equiv.apply_symm_apply f ⟨y.1, (mem_insert.mp y.2).resolve_left hy⟩)) })
      (fun _ _ => mem_univ _)
      (fun f _ => mem_filter.mpr ⟨mem_univ _, by simp [inv_r]⟩)
      (fun e he => by
        refine Equiv.ext fun x => ?_
        dsimp only [Equiv.coe_fn_mk]
        split_ifs with hx
        · have h1 : x = e.symm ⟨r, mem_insert_self r T⟩ := Subtype.ext (hx.trans (mem_filter.mp he).2.symm)
          rw [h1, Equiv.apply_symm_apply]
        · rfl)
      (fun f _ => by
        refine Equiv.ext fun x => ?_
        have hx : x.1 ≠ b := (hmem_erase x.2).1
        simp only [Equiv.coe_fn_mk, hx, ↓reduceDIte])
      (fun e he => by
        let b' : {x // x ∈ insert r T} := ⟨b, mem_insert_of_mem hb⟩
        rw [← Finset.mul_prod_erase _ _ (mem_univ b')]
        have heb : e b' = ⟨r, mem_insert_self r T⟩ := by
          have h1 : b' = e.symm ⟨r, mem_insert_self r T⟩ := Subtype.ext (mem_filter.mp he).2.symm
          rw [h1, Equiv.apply_symm_apply]
        rw [heb]
        congr 1
        refine Finset.prod_bij'
          (fun x hx => ⟨x.1, by rw [← hU_erase]; exact mem_erase.mpr ⟨fun h => (mem_erase.mp hx).1 (Subtype.ext h), x.2⟩⟩)
          (fun x _ => ⟨x.1, (hmem_erase x.2).2⟩)
          (fun _ _ => mem_univ _)
          (fun x _ => mem_erase.mpr ⟨fun h => (hmem_erase x.2).1 (congrArg Subtype.val h), mem_univ _⟩)
          (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl))
  rw [← hexp, hdet0]

private lemma shear_entry_zmod8 {n : ℕ} (A : Matrix (Fin n) (Fin n) (ZMod 8))
    (r s i j : Fin n) :
    let E : Matrix (Fin n) (Fin n) (ZMod 8) := 1 + Matrix.single s r 1
    (Eᵀ * A * E) i j =
      A i j + (if i = r then A s j else 0) + (if j = r then A i s else 0) +
      (if i = r ∧ j = r then A s s else 0) := by
  intro E
  let S : Matrix (Fin n) (Fin n) (ZMod 8) := Matrix.single s r 1
  have hST : Sᵀ = Matrix.single r s 1 := by
    ext a b; simp [S, Matrix.single_apply, and_comm]
  have h1 : ∀ k, (Sᵀ * A) i k = if i = r then A s k else 0 := by
    intro k; rw [hST]; simp only [Matrix.mul_apply, Matrix.single_apply]
    by_cases hir : i = r
    · rw [hir]; simp
    · simp [hir, Ne.symm hir]
  have h2 : (A * S) i j = if j = r then A i s else 0 := by
    simp only [S, Matrix.mul_apply, Matrix.single_apply]
    by_cases hjr : j = r
    · rw [hjr]; simp
    · simp [hjr, Ne.symm hjr]
  have h3 : (Sᵀ * A * S) i j = if i = r ∧ j = r then A s s else 0 := by
    have hmul : (Sᵀ * A * S) i j = ((Sᵀ * A) * S) i j := rfl
    rw [hmul]
    simp only [S, Matrix.mul_apply, Matrix.single_apply]
    by_cases hjr : j = r
    · rw [hjr]; simp only [and_true, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, mem_univ,
        ↓reduceIte]
      exact h1 s
    · simp [hjr, Ne.symm hjr]
  have hexp : Eᵀ * A * E = A + Sᵀ * A + A * S + Sᵀ * A * S := by
    dsimp only [E, S]
    rw [Matrix.transpose_add, Matrix.transpose_one, Matrix.add_mul, Matrix.one_mul,
      Matrix.mul_add, Matrix.mul_one, Matrix.add_mul]
    abel
  rw [hexp]
  simp only [Matrix.add_apply, h1 j, h2, h3]

private lemma subPerm_quad_eq_pair_zmod2 {n : ℕ}
    (A2 : Matrix (Fin n) (Fin n) (ZMod 2)) (hA2sym : A2.IsSymm) (hA2diag : ∀ i, A2 i i = 0)
    {r s j₁ j₂ : Fin n} (hrs : r ≠ s) (hj : j₁ ≠ j₂)
    (hj1r : j₁ ≠ r) (hj1s : j₁ ≠ s) (hj2r : j₂ ≠ r) (hj2s : j₂ ≠ s) (hA2rs : A2 r s = 0) :
    subPerm A2 {r, s, j₁, j₂} {r, s, j₁, j₂} = subPerm A2 {j₁, j₂} {r, s} := by
  let Q : Finset (Fin n) := {r, s, j₁, j₂}
  let v4 : Fin 4 → Fin n := ![r, s, j₁, j₂]
  have hv4_mem : ∀ k : Fin 4, v4 k ∈ Q := by
    intro k; fin_cases k <;> simp [v4, Q]
  let e4 : Fin 4 ≃ {x // x ∈ Q} :=
    { toFun := fun k => ⟨v4 k, hv4_mem k⟩
      invFun := fun ⟨x, _⟩ =>
        if x = r then 0 else if x = s then 1 else if x = j₁ then 2 else 3
      left_inv := fun k => by
        fin_cases k <;> simp [v4, hrs.symm, hj1r, hj1s, hj2r, hj2s, hj.symm]
      right_inv := fun ⟨x, hx⟩ => by
        simp only [Q, mem_insert, mem_singleton] at hx
        rcases hx with rfl | rfl | rfl | rfl <;>
          simp [v4, hrs.symm, hj1r, hj1s, hj2r, hj2s, hj.symm] }
  change subPerm A2 Q Q = subPerm A2 {j₁, j₂} {r, s}
  rw [subPerm_eq_det_zmod2 A2 Q Q (Equiv.refl _), subPerm_pair A2 hj hrs]
  dsimp only [Equiv.refl_apply]
  have hdet4 : (Matrix.of fun a b : {x // x ∈ Q} => A2 a.1 b.1).det =
      (Matrix.of fun a b : Fin 4 => A2 (v4 a) (v4 b)).det := by
    have hsub : (Matrix.of fun a b : {x // x ∈ Q} => A2 a.1 b.1).submatrix e4 e4 =
        Matrix.of fun a b : Fin 4 => A2 (v4 a) (v4 b) := by
      ext a b; rfl
    rw [← hsub, Matrix.det_submatrix_equiv_self]
  rw [hdet4]
  have hmat : (Matrix.of fun a b : Fin 4 => A2 (v4 a) (v4 b)) =
      Matrix.of ![![(0 : ZMod 2), 0, A2 r j₁, A2 r j₂],
                  ![0, 0, A2 s j₁, A2 s j₂],
                  ![A2 r j₁, A2 s j₁, 0, A2 j₁ j₂],
                  ![A2 r j₂, A2 s j₂, A2 j₁ j₂, 0]] := by
    ext a b
    fin_cases a <;> fin_cases b <;>
      simp [v4, hA2diag, hA2rs, hA2sym.apply]
  rw [hmat, det_four_alt_zmod2, hA2sym.apply r j₁, hA2sym.apply r j₂,
    hA2sym.apply s j₁, hA2sym.apply s j₂]
  ring

private lemma perm_inv_shear_zmod8 {n : ℕ}
    (A : Matrix (Fin n) (Fin n) (ZMod 8)) (hSym : A.IsSymm)
    (hDiag : ∀ i, A i i = 0 ∨ A i i = 4) (hA : IsUnit A.det)
    {r s : Fin n} (hrs : r ≠ s) (hArs : f2_8 (A r s) = 0) :
    let E : Matrix (Fin n) (Fin n) (ZMod 8) := 1 + Matrix.single s r 1
    let A' := Eᵀ * A * E
    A'.IsSymm ∧ (∀ i, A' i i = 0 ∨ A' i i = 4) ∧ IsUnit A'.det ∧
      (A'⁻¹).permanent = (A⁻¹).permanent := by
  intro E A'
  have hDiag2 : ∀ i, f2_8 (A i i) = 0 := fun i => by rcases hDiag i with h | h <;> rw [h] <;> decide
  have heven : Even n := even_of_isUnit_det_symm_diag2_zmod8 A hSym hDiag2 hA
  let S : Matrix (Fin n) (Fin n) (ZMod 8) := Matrix.single s r 1
  let Einv : Matrix (Fin n) (Fin n) (ZMod 8) := 1 - S
  have hSsq : S * S = 0 := by
    ext i j
    simp only [S, Matrix.mul_apply, Matrix.single_apply, Matrix.zero_apply]
    refine Finset.sum_eq_zero fun k _ => ?_
    split_ifs with h1 h2
    · exact (hrs (h1.2.trans h2.1.symm)).elim
    · simp
    · simp
    · simp
  have hEEinv : E * Einv = 1 := by
    change (1 + S) * (1 - S) = 1
    rw [Matrix.add_mul, Matrix.mul_sub, Matrix.mul_sub, Matrix.one_mul, Matrix.one_mul,
      Matrix.mul_one, hSsq]
    abel
  have hEinvE : Einv * E = 1 := by
    change (1 - S) * (1 + S) = 1
    rw [Matrix.sub_mul, Matrix.mul_add, Matrix.mul_add, Matrix.one_mul, Matrix.one_mul,
      Matrix.mul_one, hSsq]
    abel
  have hA'_sym : A'.IsSymm := by
    rw [Matrix.IsSymm]
    dsimp only [A']
    rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, hSym, Matrix.mul_assoc]
  have hA'_entry : ∀ i j : Fin n, A' i j = A i j + (if i = r then A s j else 0) +
      (if j = r then A i s else 0) + (if i = r ∧ j = r then A s s else 0) :=
    fun i j => shear_entry_zmod8 A r s i j
  have hA'_diag : ∀ i : Fin n, A' i i = 0 ∨ A' i i = 4 := by
    intro i
    rw [hA'_entry]
    by_cases hir : i = r
    · rw [hir]
      simp only [↓reduceIte, and_self]
      have h2Asr : (2 : ZMod 8) * A s r = 0 ∨ (2 : ZMod 8) * A s r = 4 := by
        have hsr : f2_8 (A s r) = 0 := by rw [hSym.apply r s]; exact hArs
        generalize A s r = x at hsr
        revert x hsr; decide
      have heq : A r r + A s r + A r s + A s s = A r r + A s s + 2 * A s r := by
        rw [hSym.apply r s]; ring
      rw [heq]
      rcases hDiag r with hr | hr <;> rcases hDiag s with hs | hs <;> rcases h2Asr with h2 | h2 <;>
        rw [hr, hs, h2] <;> decide
    · simp [hir, hDiag i]
  let M : Matrix (Fin n) (Fin n) (ZMod 8) := A⁻¹
  have hAM : A * M = 1 := Matrix.mul_nonsing_inv A hA
  have hMA : M * A = 1 := Matrix.nonsing_inv_mul A hA
  have hMsym : M.IsSymm := by rw [Matrix.IsSymm, Matrix.transpose_nonsing_inv, hSym]
  have hMdiag : ∀ i, f2_8 (M i i) = 0 := inv_diag_cast2_zero_zmod8 A hSym hDiag2 hA
  let M' : Matrix (Fin n) (Fin n) (ZMod 8) := Einv * M * Einvᵀ
  have hA'M' : A' * M' = 1 := by
    calc A' * M' = Eᵀ * A * (E * Einv) * M * Einvᵀ := by simp only [A', M', Matrix.mul_assoc]
      _ = Eᵀ * (A * M) * Einvᵀ := by rw [hEEinv, Matrix.mul_one]; simp only [Matrix.mul_assoc]
      _ = (Einv * E)ᵀ := by rw [hAM, Matrix.mul_one, Matrix.transpose_mul]
      _ = 1 := by rw [hEinvE, Matrix.transpose_one]
  have hA'_unit : IsUnit A'.det :=
    isUnit_iff_exists_inv.mpr ⟨M'.det, by rw [← Matrix.det_mul, hA'M', Matrix.det_one]⟩
  have hA'_inv : A'⁻¹ = M' := by
    have h1 := congrArg (fun X => A'⁻¹ * X) hA'M'
    rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul A' hA'_unit, Matrix.one_mul, Matrix.mul_one] at h1
    exact h1.symm
  refine ⟨hA'_sym, hA'_diag, hA'_unit, ?_⟩
  rw [hA'_inv]
  -- Expand M'.permanent = M.permanent - 2 * M_row.permanent + M_both.permanent
  let M1 : Matrix (Fin n) (Fin n) (ZMod 8) := M.updateRow s (M s + (-M r))
  let M_row : Matrix (Fin n) (Fin n) (ZMod 8) := M.updateRow s (M r)
  let M_col : Matrix (Fin n) (Fin n) (ZMod 8) := M.updateCol s (fun i => M i r)
  let M_both : Matrix (Fin n) (Fin n) (ZMod 8) := M_row.updateCol s (fun i => M_row i r)
  have hM1_eq : Einv * M = M1 := by
    ext i j
    simp only [Einv, S, M1, Matrix.mul_apply, Matrix.sub_apply, Matrix.one_apply, Matrix.single_apply,
      sub_mul, Finset.sum_sub_distrib, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, mem_univ,
      ↓reduceIte]
    by_cases his : i = s
    · subst his; simp [Matrix.updateRow_self, sub_eq_add_neg]
    · simp [Matrix.updateRow_ne his, Ne.symm his]
  have hM'_eq : M' = M1.updateCol s ((fun i => M1 i s) + (fun i => -M1 i r)) := by
    ext i j
    dsimp only [M']
    rw [hM1_eq]
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Einv, S, Matrix.sub_apply, Matrix.one_apply,
      Matrix.single_apply, mul_sub, Finset.sum_sub_distrib, mul_ite, mul_one, mul_zero]
    by_cases hjs : j = s
    · subst hjs; simp [Matrix.updateCol_self, sub_eq_add_neg]
    · simp [Matrix.updateCol_ne hjs, Ne.symm hjs]
  have hM_col_perm : M_col.permanent = M_row.permanent := by
    have hT : M_col = M_rowᵀ := by
      ext i j
      by_cases hjs : j = s
      · subst hjs; simp [M_col, M_row, Matrix.updateCol_self, Matrix.updateRow_self, hMsym.apply i r]
      · simp [M_col, M_row, Matrix.updateCol_ne hjs, Matrix.updateRow_ne hjs, hMsym.apply i j]
    rw [hT, Matrix.permanent_transpose]
  have hM'_perm : M'.permanent = M.permanent - 2 * M_row.permanent + M_both.permanent := by
    rw [hM'_eq, permanent_updateCol_add]
    have hleft : M1.updateCol s (fun i => M1 i s) = M1 := by
      ext i j; by_cases h : j = s <;> simp [h]
    have hright : M1.updateCol s (fun i => -M1 i r) =
        M1.updateCol s ((-1 : ZMod 8) • fun i => M1 i r) := by
      congr 1; ext i; simp
    have hM1_upd_col : M1.updateCol s (fun i => M1 i r) =
        M_col.updateRow s (M_col s + (-M_col r)) := by
      ext i j
      by_cases his : i = s <;> by_cases hjs : j = s
      · subst his hjs
        simp [M1, M_col, Matrix.updateRow_self, Matrix.updateCol_self]
      · subst his
        simp [M1, M_col, hjs, Matrix.updateRow_self]
      · subst hjs
        simp [M1, M_col, his, Matrix.updateCol_self]
      · simp [M1, M_col, his, hjs]
    have hM1_r_eq : M_col.updateRow s (M_col r) = M_both := by
      ext i j
      by_cases his : i = s <;> by_cases hjs : j = s
      · subst his hjs; simp [M_col, M_both, M_row]
      · subst his; simp [M_col, M_both, M_row, hjs]
      · subst hjs; simp [M_col, M_both, M_row, his]
      · simp [M_col, M_both, M_row, his, hjs]
    have hM1_perm : M1.permanent = M.permanent - M_row.permanent := by
      dsimp only [M1]
      rw [permanent_updateRow_add]
      have h0 : M.updateRow s (M s) = M := by ext i j; by_cases h : i = s <;> simp [h]
      have hneg : M.updateRow s (-M r) = M.updateRow s ((-1 : ZMod 8) • M r) := by
        congr 1; ext j; simp
      rw [h0, hneg, Matrix.permanent_updateRow_smul]; ring
    have hM1c_perm : (M1.updateCol s (fun i => M1 i r)).permanent =
        M_col.permanent - M_both.permanent := by
      rw [hM1_upd_col, permanent_updateRow_add]
      have h0 : M_col.updateRow s (M_col s) = M_col := by ext i j; by_cases h : i = s <;> simp [h]
      have hneg : M_col.updateRow s (-M_col r) = M_col.updateRow s ((-1 : ZMod 8) • M_col r) := by
        congr 1; ext j; simp
      rw [h0, hneg, Matrix.permanent_updateRow_smul, hM1_r_eq]; ring
    rw [hleft, hright, Matrix.permanent_updateCol_smul, hM1_perm, hM1c_perm, hM_col_perm]
    ring
  rw [hM'_perm]
  suffices hdiff : M_both.permanent - 2 * M_row.permanent = 0 by linear_combination hdiff
  let T : Finset (Fin n) := (Finset.univ.erase r).erase s
  have hT_eq : ({r, s} : Finset (Fin n))ᶜ = T := by
    ext x; simp [T, and_comm]
  have hMrow_exp : (2 : ZMod 8) * M_row.permanent =
      4 * ∑ J ∈ Finset.powersetCard 2 (Finset.univ : Finset (Fin n)),
        (∏ j ∈ J, M r j) * subPerm M T Jᶜ := by
    rw [← Matrix.permanent_transpose]
    have h1 : M_rowᵀ.permanent =
        ∑ σ : Equiv.Perm (Fin n), (∏ j ∈ ({r, s} : Finset (Fin n)), M_rowᵀ (σ j) j) *
          (∏ j ∈ ({r, s} : Finset (Fin n))ᶜ, M_rowᵀ (σ j) j) := by
      rw [Matrix.permanent]
      refine Finset.sum_congr rfl fun σ _ => ?_
      exact (Finset.prod_mul_prod_compl ({r, s} : Finset (Fin n)) (fun j => M_rowᵀ (σ j) j)).symm
    rw [h1, sum_perm_prod_compl ({r, s} : Finset (Fin n)) M_rowᵀ M_rowᵀ, Finset.card_pair hrs,
      Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun J hJ => ?_
    obtain ⟨j₁, j₂, hj, rfl⟩ := Finset.card_eq_two.mp (Finset.mem_powersetCard.mp hJ).2
    have hsub1 : subPerm M_rowᵀ {j₁, j₂} {r, s} = 2 * (∏ j ∈ ({j₁, j₂} : Finset (Fin n)), M r j) := by
      rw [subPerm_pair M_rowᵀ hj hrs, Finset.prod_pair hj]
      simp [M_row, Matrix.updateRow_ne hrs, Matrix.updateRow_self]; ring
    have hsub2 : subPerm M_rowᵀ ({j₁, j₂}ᶜ) ({r, s}ᶜ) = subPerm M T ({j₁, j₂}ᶜ) := by
      rw [hT_eq, ← subPerm_symm hMsym]
      unfold subPerm
      refine Finset.sum_congr rfl fun e _ => Finset.prod_congr rfl fun x _ => ?_
      have hxne : x.1 ≠ s := (mem_erase.mp x.2).1
      simp [M_row, Matrix.updateRow_ne hxne, hMsym.apply]
    rw [hsub1, hsub2]; ring
  have hMboth_exp : M_both.permanent =
      4 * ∑ J ∈ Finset.powersetCard 2 T,
        ∑ I ∈ Finset.powersetCard 2 T,
          (∏ j ∈ J, M r j) * (∏ i ∈ I, M r i) * subPerm M (T \ I) (T \ J) := by
    rw [← Matrix.permanent_transpose]
    have h1 : M_bothᵀ.permanent =
        ∑ σ : Equiv.Perm (Fin n), (∏ j ∈ ({r, s} : Finset (Fin n)), M_bothᵀ (σ j) j) *
          (∏ j ∈ ({r, s} : Finset (Fin n))ᶜ, M_bothᵀ (σ j) j) := by
      rw [Matrix.permanent]
      refine Finset.sum_congr rfl fun σ _ => ?_
      exact (Finset.prod_mul_prod_compl ({r, s} : Finset (Fin n)) (fun j => M_bothᵀ (σ j) j)).symm
    rw [h1, sum_perm_prod_compl ({r, s} : Finset (Fin n)) M_bothᵀ M_bothᵀ, Finset.card_pair hrs]
    -- Split J ∈ powersetCard 2 univ into: J ⊆ T, J = {r, s}, or |J ∩ {r, s}| = 1
    have hMboth_r : ∀ j, M_both r j = if j = s then M r r else M r j := by
      intro j; by_cases hjs : j = s <;> simp [M_both, M_row, hjs, hrs]
    have hMboth_s : ∀ j, M_both s j = if j = s then M r r else M r j := by
      intro j; by_cases hjs : j = s <;> simp [M_both, M_row, hjs]
    have hMboth_col_r : ∀ i, M_both i s = M_both i r := by
      intro i; simp [M_both, Matrix.updateCol_self, Matrix.updateCol_ne hrs]
    have hJ_rs : subPerm M_bothᵀ {r, s} {r, s} * subPerm M_bothᵀ ({r, s}ᶜ) ({r, s}ᶜ) = 0 := by
      rw [subPerm_pair M_bothᵀ hrs hrs]
      simp only [Matrix.transpose_apply, hMboth_r, hMboth_s, ↓reduceIte, ite_self]
      have h2sq : (2 : ZMod 8) * (M r r * M r r) = 0 := by
        have hm := hMdiag r
        generalize M r r = x at hm
        revert x hm; decide
      have : M r r * M r r + M r r * M r r = 2 * (M r r * M r r) := by ring
      rw [this, h2sq, zero_mul]
    -- Split sum over J ∈ powersetCard 2 univ into J ⊆ T vs not (J ⊆ T)
    have hsubT : Finset.powersetCard 2 T ⊆ Finset.powersetCard 2 (Finset.univ : Finset (Fin n)) :=
      Finset.powersetCard_mono (Finset.subset_univ T)
    rw [← Finset.sum_sdiff hsubT]
    have hnotT_zero : ∑ J ∈ Finset.powersetCard 2 Finset.univ \ Finset.powersetCard 2 T,
        subPerm M_bothᵀ J {r, s} * subPerm M_bothᵀ Jᶜ ({r, s}ᶜ) = 0 := by
      -- For J not in powersetCard 2 T: either J = {r, s} (zero!) or J = {r, b} / {s, b} (pair them!)
      let pairJ : Finset (Fin n) → Finset (Fin n) := fun J => J.image (Equiv.swap r s)
      refine Finset.sum_involution (fun J _ => pairJ J) ?_ ?_ ?_ ?_
      · intro J hJ
        obtain ⟨j₁, j₂, hj, rfl⟩ := Finset.card_eq_two.mp
          (Finset.mem_powersetCard.mp (Finset.mem_sdiff.mp hJ).1).2
        have hnot : ¬ ({j₁, j₂} ⊆ T) := fun h =>
          (Finset.mem_sdiff.mp hJ).2 (Finset.mem_powersetCard.mpr ⟨h, Finset.card_pair hj⟩)
        by_cases hJrs : ({j₁, j₂} : Finset (Fin n)) = {r, s}
        · rw [hJrs]
          have hpair_rs : pairJ {r, s} = {r, s} := by
            ext x; simp only [pairJ, mem_image, mem_insert, mem_singleton]
            constructor
            · rintro ⟨y, rfl | rfl, rfl⟩ <;> simp
            · rintro (rfl | rfl)
              · exact ⟨s, Or.inr rfl, by simp⟩
              · exact ⟨r, Or.inl rfl, by simp⟩
          rw [hpair_rs, hJ_rs, add_zero]
        · -- Exactly one of r, s is in {j₁, j₂}
          have h4mul : subPerm M_bothᵀ {j₁, j₂} {r, s} = 2 * M r r * M r (if j₁ = r ∨ j₁ = s then j₂ else j₁) := by
            rw [subPerm_pair M_bothᵀ hj hrs]
            simp only [Matrix.transpose_apply, hMboth_r, hMboth_s]
            by_cases h1 : j₁ = r ∨ j₁ = s
            · have h2 : ¬(j₂ = r ∨ j₂ = s) := by
                rintro (h2r | h2s)
                · rcases h1 with h1r | h1s
                  · exact hj (h1r.trans h2r.symm)
                  · exact hJrs (by rw [h1s, h2r, Finset.pair_comm])
                · rcases h1 with h1r | h1s
                  · exact hJrs (by rw [h1r, h2s])
                  · exact hj (h1s.trans h2s.symm)
              push Not at h2
              rcases h1 with h1 | h1 <;> simp [h1, hrs, h2.2] <;> ring
            · have h2 : j₂ = r ∨ j₂ = s := by
                by_contra h2'
                push Not at h1 h2'
                apply hnot
                intro x hx
                rcases mem_insert.mp hx with rfl | hx2
                · simp [T, h1.1, h1.2]
                · rw [mem_singleton.mp hx2]; simp [T, h2'.1, h2'.2]
              push Not at h1
              rcases h2 with h2 | h2 <;> simp [h2, hrs, h1.1, h1.2] <;> ring
          have hsame_compl : subPerm M_bothᵀ (pairJ {j₁, j₂})ᶜ ({r, s}ᶜ) =
              subPerm M_bothᵀ ({j₁, j₂}ᶜ) ({r, s}ᶜ) := by
            unfold subPerm
            let sw := Equiv.swap r s
            let φ : ({x // x ∈ ({r, s} : Finset (Fin n))ᶜ} ≃ {y // y ∈ (pairJ {j₁, j₂})ᶜ}) ≃
                ({x // x ∈ ({r, s} : Finset (Fin n))ᶜ} ≃ {y // y ∈ ({j₁, j₂}ᶜ : Finset (Fin n))}) :=
              Equiv.equivCongr (Equiv.refl _)
                { toFun := fun y => ⟨sw y.1, by
                    rw [Finset.mem_compl]; intro hm
                    have : y.1 ∈ pairJ {j₁, j₂} := by
                      dsimp only [pairJ]; rw [mem_image]; exact ⟨sw y.1, hm, by simp [sw]⟩
                    exact (Finset.mem_compl.mp y.2) this⟩
                  invFun := fun y => ⟨sw y.1, by
                    rw [Finset.mem_compl]; intro hm
                    dsimp only [pairJ] at hm; rw [mem_image] at hm
                    obtain ⟨z, hz, hzy⟩ := hm
                    have : y.1 = z := (sw.injective hzy).symm
                    exact (Finset.mem_compl.mp y.2) (this ▸ hz)⟩
                  left_inv := fun y => by ext; simp [sw]
                  right_inv := fun y => by ext; simp [sw] }
            refine Fintype.sum_equiv φ _ _ fun e => Finset.prod_congr rfl fun x _ => ?_
            change M_both x.1 (e x).1 = M_both x.1 (sw (e x).1)
            by_cases h1 : (e x).1 = r
            · rw [h1, Equiv.swap_apply_left, hMboth_col_r]
            · by_cases h2 : (e x).1 = s
              · rw [h2, Equiv.swap_apply_right, hMboth_col_r]
              · rw [Equiv.swap_apply_of_ne_of_ne h1 h2]
          have hsame_pair : subPerm M_bothᵀ (pairJ {j₁, j₂}) {r, s} = subPerm M_bothᵀ {j₁, j₂} {r, s} := by
            have hsw_ne : Equiv.swap r s j₁ ≠ Equiv.swap r s j₂ := fun h => hj ((Equiv.swap r s).injective h)
            have hpeq : pairJ {j₁, j₂} = {Equiv.swap r s j₁, Equiv.swap r s j₂} := by
              simp [pairJ, Finset.image_insert, Finset.image_singleton]
            rw [hpeq, subPerm_pair M_bothᵀ hsw_ne hrs, subPerm_pair M_bothᵀ hj hrs]
            simp only [Matrix.transpose_apply]
            have hcol : ∀ a, M_both r (Equiv.swap r s a) = M_both r a ∧
                M_both s (Equiv.swap r s a) = M_both s a := by
              intro a
              by_cases h1 : a = r
              · subst h1; simp [hMboth_col_r]
              · by_cases h2 : a = s
                · subst h2; simp [hMboth_col_r]
                · simp [Equiv.swap_apply_of_ne_of_ne h1 h2]
            rw [(hcol j₁).1, (hcol j₁).2, (hcol j₂).1, (hcol j₂).2]
          rw [hsame_pair, hsame_compl, ← two_mul, h4mul, ← mul_assoc, ← mul_assoc]
          have h4m : (2 : ZMod 8) * (2 * M r r) = 0 := by
            have : (2 : ZMod 8) * (2 * M r r) = 4 * M r r := by ring
            rw [this]; exact zmod8_four_mul_eq_zero_of_cast2 _ (hMdiag r)
          rw [h4m, zero_mul, zero_mul]
      · intro J hJ hne0 heq
        obtain ⟨j₁, j₂, hj, rfl⟩ := Finset.card_eq_two.mp
          (Finset.mem_powersetCard.mp (Finset.mem_sdiff.mp hJ).1).2
        by_cases hJrs : ({j₁, j₂} : Finset (Fin n)) = {r, s}
        · exact hne0 (by rw [hJrs]; exact hJ_rs)
        · have hnot : ¬ ({j₁, j₂} ⊆ T) := fun h =>
            (Finset.mem_sdiff.mp hJ).2 (Finset.mem_powersetCard.mpr ⟨h, Finset.card_pair hj⟩)
          have h1 : (r ∈ ({j₁, j₂} : Finset (Fin n)) ∧ s ∉ ({j₁, j₂} : Finset (Fin n))) ∨
              (s ∈ ({j₁, j₂} : Finset (Fin n)) ∧ r ∉ ({j₁, j₂} : Finset (Fin n))) := by
            by_cases hr : r ∈ ({j₁, j₂} : Finset (Fin n)) <;> by_cases hs : s ∈ ({j₁, j₂} : Finset (Fin n))
            · exfalso; apply hJrs
              refine (Finset.eq_of_subset_of_card_le ?_ (by rw [Finset.card_pair hj, Finset.card_pair hrs])).symm
              intro x hx; rcases mem_insert.mp hx with rfl | hx2
              · exact hr
              · rw [mem_singleton.mp hx2]; exact hs
            · exact Or.inl ⟨hr, hs⟩
            · exact Or.inr ⟨hs, hr⟩
            · exfalso; apply hnot; intro x hx
              simp only [T, mem_erase, mem_univ, and_true]
              exact ⟨fun h => hs (h ▸ hx), fun h => hr (h ▸ hx)⟩
          rcases h1 with ⟨hr, hs⟩ | ⟨hs, hr⟩
          · have : s ∈ pairJ {j₁, j₂} := by dsimp only [pairJ]; rw [mem_image]; exact ⟨r, hr, by simp⟩
            rw [heq] at this; exact hs this
          · have : r ∈ pairJ {j₁, j₂} := by dsimp only [pairJ]; rw [mem_image]; exact ⟨s, hs, by simp⟩
            rw [heq] at this; exact hr this
      · intro J hJ
        rw [Finset.mem_sdiff, Finset.mem_powersetCard] at hJ ⊢
        refine ⟨⟨Finset.subset_univ _, ?_⟩, ?_⟩
        · dsimp only [pairJ]; rw [Finset.card_image_of_injective _ (Equiv.swap r s).injective, hJ.1.2]
        · intro hmem
          apply hJ.2
          rw [Finset.mem_powersetCard] at hmem ⊢
          refine ⟨?_, hJ.1.2⟩
          intro x hx
          have hsw : Equiv.swap r s x ∈ T := hmem.1 (mem_image_of_mem _ hx)
          have hx_ne_r : x ≠ r := fun h => by rw [h, Equiv.swap_apply_left] at hsw; simp [T] at hsw
          have hx_ne_s : x ≠ s := fun h => by rw [h, Equiv.swap_apply_right] at hsw; simp [T] at hsw
          simp [T, hx_ne_r, hx_ne_s]
      · intro J _
        ext x; simp only [pairJ, mem_image]
        constructor
        · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩; simpa using hy
        · intro hx; exact ⟨Equiv.swap r s x, ⟨x, hx, rfl⟩, by simp⟩
    rw [hnotT_zero, zero_add, Finset.mul_sum]
    refine Finset.sum_congr rfl fun J hJ => ?_
    have hJT : J ⊆ T := (Finset.mem_powersetCard.mp hJ).1
    obtain ⟨j₁, j₂, hj, rfl⟩ := Finset.card_eq_two.mp (Finset.mem_powersetCard.mp hJ).2
    have hj₁_ne_s : j₁ ≠ s := (mem_erase.mp (hJT (by simp))).1
    have hj₂_ne_s : j₂ ≠ s := (mem_erase.mp (hJT (by simp))).1
    have hsub1 : subPerm M_bothᵀ {j₁, j₂} {r, s} = 2 * (∏ j ∈ ({j₁, j₂} : Finset (Fin n)), M r j) := by
      rw [subPerm_pair M_bothᵀ hj hrs, Finset.prod_pair hj]
      simp [hMboth_r, hMboth_s, hj₁_ne_s, hj₂_ne_s]; ring
    -- Now expand subPerm M_bothᵀ ({j₁, j₂}ᶜ) T along columns {r, s} ⊆ {j₁, j₂}ᶜ
    have hsub2 : subPerm M_bothᵀ ({j₁, j₂}ᶜ) ({r, s}ᶜ) =
        2 * ∑ I ∈ Finset.powersetCard 2 T, (∏ i ∈ I, M r i) * subPerm M (T \ I) (T \ {j₁, j₂}) := by
      rw [hT_eq]
      have hrs_sub : ({r, s} : Finset (Fin n)) ⊆ {j₁, j₂}ᶜ := by
        intro x hx
        rw [Finset.mem_compl]
        intro hm
        have hxT := hJT hm
        rcases mem_insert.mp hx with rfl | hx2
        · simp [T] at hxT
        · rw [mem_singleton.mp hx2] at hxT; simp [T] at hxT
      -- Group bijections e : T ≃ {j₁, j₂}ᶜ by I = e⁻¹({r, s}) ⊆ T
      change (∑ e : {x // x ∈ T} ≃ {y // y ∈ ({j₁, j₂}ᶜ : Finset (Fin n))}, ∏ x, M_bothᵀ (e x).1 x.1) = _
      let preRS : ({x // x ∈ T} ≃ {y // y ∈ ({j₁, j₂}ᶜ : Finset (Fin n))}) → Finset (Fin n) :=
        fun e => ({r, s} : Finset (Fin n)).attach.image (fun y => (e.symm ⟨y.1, hrs_sub y.2⟩).1)
      have hmaps : ∀ e : {x // x ∈ T} ≃ {y // y ∈ ({j₁, j₂}ᶜ : Finset (Fin n))},
          preRS e ∈ Finset.powersetCard 2 T := by
        intro e
        rw [Finset.mem_powersetCard]
        refine ⟨?_, ?_⟩
        · intro x hx
          obtain ⟨y, _, rfl⟩ := mem_image.mp hx
          exact (e.symm _).2
        · dsimp only [preRS]; rw [Finset.card_image_of_injective]
          · rw [Finset.card_attach, Finset.card_pair hrs]
          · intro y₁ y₂ h
            have h1 : e.symm ⟨y₁.1, hrs_sub y₁.2⟩ = e.symm ⟨y₂.1, hrs_sub y₂.2⟩ := Subtype.ext h
            exact subtype_ext_val (e.symm.injective h1)
      rw [← Finset.sum_fiberwise_of_maps_to (g := preRS) (t := Finset.powersetCard 2 T) (fun e _ => hmaps e),
        Finset.mul_sum]
      refine Finset.sum_congr rfl fun I hI => ?_
      have hIT : I ⊆ T := (Finset.mem_powersetCard.mp hI).1
      obtain ⟨i₁, i₂, hi, rfl⟩ := Finset.card_eq_two.mp (Finset.mem_powersetCard.mp hI).2
      have hJcompl_sdiff : ({j₁, j₂}ᶜ : Finset (Fin n)) \ {r, s} = T \ {j₁, j₂} := by
        ext x; simp [T, not_or]; tauto
      have hmem_sdiff : ∀ {z : Fin n}, z ∈ T \ {j₁, j₂} →
          z ∈ ({j₁, j₂}ᶜ : Finset (Fin n)) ∧ z ∉ ({r, s} : Finset (Fin n)) := by
        intro z hz; rw [← hJcompl_sdiff, mem_sdiff] at hz; exact hz
      -- Biject fiber over I with ({i₁, i₂} ≃ {r, s}) × (T \ {i₁, i₂} ≃ T \ {j₁, j₂})
      have hfib : ∑ e ∈ Finset.univ.filter (fun e : {x // x ∈ T} ≃ {y // y ∈ ({j₁, j₂}ᶜ : Finset (Fin n))} =>
          preRS e = {i₁, i₂}), ∏ x, M_bothᵀ (e x).1 x.1 =
          subPerm M_bothᵀ {r, s} {i₁, i₂} * subPerm M (T \ {i₁, i₂}) (T \ {j₁, j₂}) := by
        unfold subPerm
        rw [Finset.sum_mul_sum, ← Finset.sum_product']
        refine Finset.sum_bij'
          (fun e he =>
            ( { toFun := fun x => ⟨(e ⟨x.1, hIT x.2⟩).1, by
                  have hmem : x.1 ∈ preRS e := (mem_filter.mp he).2.symm ▸ x.2
                  obtain ⟨y, _, hy⟩ := mem_image.mp hmem
                  have h2 : e ⟨x.1, hIT x.2⟩ = ⟨y.1, hrs_sub y.2⟩ := by
                    have : (⟨x.1, hIT x.2⟩ : {z // z ∈ T}) = e.symm ⟨y.1, hrs_sub y.2⟩ := Subtype.ext hy.symm
                    rw [this, Equiv.apply_symm_apply]
                  rw [h2]; exact y.2⟩
                invFun := fun y => ⟨(e.symm ⟨y.1, hrs_sub y.2⟩).1, by
                  rw [← (mem_filter.mp he).2]; dsimp only [preRS]; rw [mem_image]
                  exact ⟨⟨y.1, y.2⟩, mem_attach _ _, rfl⟩⟩
                left_inv := fun x =>
                  subtype_ext_val
                    ((congrArg e.symm (Subtype.ext rfl)).trans (Equiv.symm_apply_apply e ⟨x.1, hIT x.2⟩))
                right_inv := fun y =>
                  subtype_ext_val
                    ((congrArg e (Subtype.ext rfl)).trans (Equiv.apply_symm_apply e ⟨y.1, hrs_sub y.2⟩)) },
              { toFun := fun y => ⟨(e.symm ⟨y.1, (hmem_sdiff y.2).1⟩).1, by
                  rw [mem_sdiff]
                  refine ⟨(e.symm _).2, ?_⟩
                  intro hmem
                  rw [← (mem_filter.mp he).2] at hmem; dsimp only [preRS] at hmem; rw [mem_image] at hmem
                  obtain ⟨z, _, hz⟩ := hmem
                  have h2 := e.symm.injective (Subtype.ext hz)
                  exact (hmem_sdiff y.2).2 ((congrArg Subtype.val h2).symm ▸ z.2)⟩
                invFun := fun x => ⟨(e ⟨x.1, (mem_sdiff.mp x.2).1⟩).1, by
                  rw [← hJcompl_sdiff, mem_sdiff]
                  refine ⟨(e _).2, ?_⟩
                  intro hmem
                  have hmem' : x.1 ∈ preRS e := by
                    dsimp only [preRS]; rw [mem_image]
                    exact ⟨⟨(e ⟨x.1, (mem_sdiff.mp x.2).1⟩).1, hmem⟩, mem_attach _ _,
                      congrArg Subtype.val (Equiv.symm_apply_apply e _)⟩
                  rw [(mem_filter.mp he).2] at hmem'
                  exact (mem_sdiff.mp x.2).2 hmem'⟩
                left_inv := fun y =>
                  subtype_ext_val
                    ((congrArg e (Subtype.ext rfl)).trans (Equiv.apply_symm_apply e ⟨y.1, (hmem_sdiff y.2).1⟩))
                right_inv := fun x =>
                  subtype_ext_val
                    ((congrArg e.symm (Subtype.ext rfl)).trans (Equiv.symm_apply_apply e ⟨x.1, (mem_sdiff.mp x.2).1⟩)) } ))
          (fun p _ =>
            { toFun := fun x => if hx : x.1 ∈ ({i₁, i₂} : Finset (Fin n))
                then ⟨(p.1 ⟨x.1, hx⟩).1, hrs_sub (p.1 ⟨x.1, hx⟩).2⟩
                else ⟨(p.2.symm ⟨x.1, mem_sdiff.mpr ⟨x.2, hx⟩⟩).1,
                  (hmem_sdiff (p.2.symm ⟨x.1, mem_sdiff.mpr ⟨x.2, hx⟩⟩).2).1⟩
              invFun := fun y => if hy : y.1 ∈ ({r, s} : Finset (Fin n))
                then ⟨(p.1.symm ⟨y.1, hy⟩).1, hIT (p.1.symm ⟨y.1, hy⟩).2⟩
                else ⟨(p.2 ⟨y.1, hJcompl_sdiff ▸ mem_sdiff.mpr ⟨y.2, hy⟩⟩).1,
                  (mem_sdiff.mp (p.2 _).2).1⟩
              left_inv := fun x => by
                dsimp only
                by_cases hx : x.1 ∈ ({i₁, i₂} : Finset (Fin n))
                · simp only [hx, ↓reduceDIte, (p.1 ⟨x.1, hx⟩).2]
                  exact subtype_ext_val
                    ((congrArg p.1.symm (Subtype.ext rfl)).trans (Equiv.symm_apply_apply p.1 ⟨x.1, hx⟩))
                · have hnot : (p.2.symm ⟨x.1, mem_sdiff.mpr ⟨x.2, hx⟩⟩).1 ∉ ({r, s} : Finset (Fin n)) :=
                    (hmem_sdiff (p.2.symm ⟨x.1, mem_sdiff.mpr ⟨x.2, hx⟩⟩).2).2
                  simp only [hx, ↓reduceDIte, hnot]
                  exact subtype_ext_val
                    ((congrArg p.2 (Subtype.ext rfl)).trans
                      (Equiv.apply_symm_apply p.2 ⟨x.1, mem_sdiff.mpr ⟨x.2, hx⟩⟩))
              right_inv := fun y => by
                dsimp only
                by_cases hy : y.1 ∈ ({r, s} : Finset (Fin n))
                · simp only [hy, ↓reduceDIte, (p.1.symm ⟨y.1, hy⟩).2]
                  exact subtype_ext_val
                    ((congrArg p.1 (Subtype.ext rfl)).trans (Equiv.apply_symm_apply p.1 ⟨y.1, hy⟩))
                · have hnot : (p.2 ⟨y.1, hJcompl_sdiff ▸ mem_sdiff.mpr ⟨y.2, hy⟩⟩).1 ∉ ({i₁, i₂} : Finset (Fin n)) :=
                    (mem_sdiff.mp (p.2 _).2).2
                  simp only [hy, ↓reduceDIte, hnot]
                  exact subtype_ext_val
                    ((congrArg p.2.symm (Subtype.ext rfl)).trans
                      (Equiv.symm_apply_apply p.2 ⟨y.1, hJcompl_sdiff ▸ mem_sdiff.mpr ⟨y.2, hy⟩⟩)) })
          (fun _ _ => mem_univ _)
          (fun p _ => by
            refine mem_filter.mpr ⟨mem_univ _, ?_⟩
            ext x; simp only [preRS, mem_image, mem_attach, true_and, Subtype.exists]
            constructor
            · rintro ⟨y, hy, rfl⟩
              simp only [Equiv.coe_fn_symm_mk, hy, ↓reduceDIte]
              exact (p.1.symm ⟨y, hy⟩).2
            · intro hx
              refine ⟨(p.1 ⟨x, hx⟩).1, (p.1 ⟨x, hx⟩).2, ?_⟩
              simp only [Equiv.coe_fn_symm_mk, (p.1 ⟨x, hx⟩).2, ↓reduceDIte]
              exact congrArg Subtype.val
                ((congrArg p.1.symm (Subtype.ext rfl)).trans (Equiv.symm_apply_apply p.1 ⟨x, hx⟩)))
          (fun e he => by
            refine Equiv.ext fun x => ?_; dsimp only [Equiv.coe_fn_mk]
            split_ifs <;> exact Subtype.ext rfl)
          (fun p _ => by
            refine Prod.ext (Equiv.ext fun x => ?_) (Equiv.ext fun x => ?_)
            · simp only [Equiv.coe_fn_mk, x.2, ↓reduceDIte]
            · have hnot : x.1 ∉ ({r, s} : Finset (Fin n)) := (hmem_sdiff x.2).2
              simp only [Equiv.coe_fn_mk, Equiv.coe_fn_symm_mk, hnot, ↓reduceDIte])
          (fun e he => by
            dsimp only [Equiv.coe_fn_mk]
            have hpart' : (∏ x : {x // x ∈ T}, M_bothᵀ (e x).1 x.1) =
                (∏ x : {x // x ∈ ({i₁, i₂} : Finset (Fin n))}, M_bothᵀ (e ⟨x.1, hIT x.2⟩).1 x.1) *
                (∏ y : {y // y ∈ T \ {j₁, j₂}},
                  M (e.symm ⟨y.1, (hmem_sdiff y.2).1⟩).1 y.1) := by
              rw [← Finset.prod_filter_mul_prod_filter_not Finset.univ
                (fun x : {x // x ∈ T} => x.1 ∈ ({i₁, i₂} : Finset (Fin n)))]
              congr 1
              · refine Finset.prod_bij'
                  (fun x hx => ⟨x.1, (mem_filter.mp hx).2⟩)
                  (fun x _ => ⟨x.1, hIT x.2⟩)
                  (fun _ _ => mem_univ _)
                  (fun x _ => mem_filter.mpr ⟨mem_univ _, x.2⟩)
                  (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
              · refine Finset.prod_bij'
                  (fun x hx => ⟨(e x).1, by
                    rw [← hJcompl_sdiff, mem_sdiff]
                    refine ⟨(e x).2, ?_⟩
                    intro hmem
                    have hm : x.1 ∈ preRS e := by
                      dsimp only [preRS]; rw [mem_image]
                      exact ⟨⟨(e x).1, hmem⟩, mem_attach _ _, congrArg Subtype.val (Equiv.symm_apply_apply e x)⟩
                    rw [(mem_filter.mp he).2] at hm
                    exact (mem_filter.mp hx).2 hm⟩)
                  (fun y _ => e.symm ⟨y.1, (hmem_sdiff y.2).1⟩)
                  (fun _ _ => mem_univ _)
                  (fun y _ => mem_filter.mpr ⟨mem_univ _, fun hmem => by
                    rw [← (mem_filter.mp he).2] at hmem; dsimp only [preRS] at hmem; rw [mem_image] at hmem
                    obtain ⟨z, _, hz⟩ := hmem
                    have h2 := e.symm.injective (Subtype.ext hz)
                    exact (hmem_sdiff y.2).2 ((congrArg Subtype.val h2).symm ▸ z.2)⟩)
                  (fun x _ => Equiv.symm_apply_apply e x)
                  (fun y _ => subtype_ext_val (Equiv.apply_symm_apply e ⟨y.1, (hmem_sdiff y.2).1⟩))
                  (fun x hx => by
                    have hxne : x.1 ≠ s := (mem_erase.mp x.2).1
                    have hene : (e x).1 ≠ s := by
                      intro h
                      have hm : x.1 ∈ preRS e := by
                        dsimp only [preRS]; rw [mem_image]
                        exact ⟨⟨s, by simp⟩, mem_attach _ _, by
                          have : e x = ⟨s, hrs_sub (by simp)⟩ := Subtype.ext h
                          rw [← this, Equiv.symm_apply_apply]⟩
                      rw [(mem_filter.mp he).2] at hm
                      exact (mem_filter.mp hx).2 hm
                    have hback : (e.symm ⟨(e x).1, _⟩).1 = x.1 :=
                      congrArg Subtype.val (Equiv.symm_apply_apply e x)
                    rw [hback]
                    simp [M_both, M_row, Matrix.updateCol_ne hene, Matrix.updateRow_ne hxne])
            exact hpart')
      rw [hfib]
      have hi₁_ne_s : i₁ ≠ s := (mem_erase.mp (hIT (by simp))).1
      have hi₂_ne_s : i₂ ≠ s := (mem_erase.mp (hIT (by simp))).1
      have hpair_rs : subPerm M_bothᵀ {r, s} {i₁, i₂} = 2 * (∏ i ∈ ({i₁, i₂} : Finset (Fin n)), M r i) := by
        rw [subPerm_pair M_bothᵀ hrs hi, Finset.prod_pair hi]
        simp only [Matrix.transpose_apply, hMboth_col_r]
        have hmb1 : M_both i₁ r = M r i₁ := by
          simp [M_both, M_row, hrs, Matrix.updateRow_ne hi₁_ne_s, hMsym.apply]
        have hmb2 : M_both i₂ r = M r i₂ := by
          simp [M_both, M_row, hrs, Matrix.updateRow_ne hi₂_ne_s, hMsym.apply]
        rw [hmb1, hmb2]; ring
      rw [hpair_rs]; ring
    rw [hsub1, hsub2, ← mul_assoc, Finset.mul_sum]
    have h22 : (2 : ZMod 8) * (∏ j ∈ ({j₁, j₂} : Finset (Fin n)), M r j) * 2 =
        4 * (∏ j ∈ ({j₁, j₂} : Finset (Fin n)), M r j) := by ring
    rw [h22, Finset.mul_sum]
    refine Finset.sum_congr rfl fun I _ => by ring
  -- Now prove M_both.permanent - 2 * M_row.permanent = 0 by dropping 4 * (...) to ZMod 2!
  rw [hMboth_exp, hMrow_exp, ← mul_sub]
  refine zmod8_four_mul_eq_zero_of_cast2 _ ?_
  let A2 := A.map f2_8
  let M2 := M.map f2_8
  have hM2A2 : M2 * A2 = 1 := by
    rw [← Matrix.map_mul, hMA, Matrix.map_one f2_8 (map_zero f2_8) (map_one f2_8)]
  have hM2sym : M2.IsSymm := by ext a b; simp [M2, hMsym.apply a b]
  have hA2sym : A2.IsSymm := by ext a b; simp [A2, hSym.apply a b]
  have hA2diag : ∀ i, A2 i i = 0 := hDiag2
  have hM2diag : ∀ i, M2 i i = 0 := hMdiag
  have hA2rs : A2 r s = 0 := hArs
  rw [map_sub]
  -- Simplify first sum in ZMod 2: off-diagonal I ≠ J cancels by symmetry!
  have hS_both2 : f2_8 (∑ J ∈ Finset.powersetCard 2 T, ∑ I ∈ Finset.powersetCard 2 T,
      (∏ j ∈ J, M r j) * (∏ i ∈ I, M r i) * subPerm M (T \ I) (T \ J)) =
      ∑ J ∈ Finset.powersetCard 2 T, (∏ j ∈ J, M2 r j) * subPerm M2 (T \ J) (T \ J) := by
    simp only [map_sum, map_mul, map_prod, ← subPerm_map f2_8 M]
    have hsplit_diag :
        ∑ J ∈ Finset.powersetCard 2 T, ∑ I ∈ Finset.powersetCard 2 T,
          (∏ j ∈ J, M2 r j) * (∏ i ∈ I, M2 r i) * subPerm M2 (T \ I) (T \ J) =
        (∑ J ∈ Finset.powersetCard 2 T,
          (∏ j ∈ J, M2 r j) * (∏ i ∈ J, M2 r i) * subPerm M2 (T \ J) (T \ J)) +
        ∑ p ∈ (Finset.powersetCard 2 T ×ˢ Finset.powersetCard 2 T).filter (fun p => p.1 ≠ p.2),
          (∏ j ∈ p.1, M2 r j) * (∏ i ∈ p.2, M2 r i) * subPerm M2 (T \ p.2) (T \ p.1) := by
      rw [← Finset.sum_product']
      rw [← Finset.sum_filter_add_sum_filter_not (Finset.powersetCard 2 T ×ˢ Finset.powersetCard 2 T)
        (fun p => p.1 = p.2)]
      congr 1
      refine Finset.sum_bij' (fun p _ => p.1) (fun J _ => (J, J))
        (fun p hp => (mem_product.mp (mem_filter.mp hp).1).1)
        (fun J hJ => mem_filter.mpr ⟨mem_product.mpr ⟨hJ, hJ⟩, rfl⟩)
        (fun p hp => Prod.ext rfl (mem_filter.mp hp).2)
        (fun _ _ => rfl)
        (fun p hp => by rw [(mem_filter.mp hp).2])
    change (∑ J ∈ Finset.powersetCard 2 T, ∑ I ∈ Finset.powersetCard 2 T,
        (∏ j ∈ J, M2 r j) * (∏ i ∈ I, M2 r i) * subPerm M2 (T \ I) (T \ J)) = _
    rw [hsplit_diag]
    have hoff0 : ∑ p ∈ (Finset.powersetCard 2 T ×ˢ Finset.powersetCard 2 T).filter (fun p => p.1 ≠ p.2),
        (∏ j ∈ p.1, M2 r j) * (∏ i ∈ p.2, M2 r i) * subPerm M2 (T \ p.2) (T \ p.1) = 0 := by
      refine Finset.sum_involution (fun p _ => (p.2, p.1)) ?_ ?_ ?_ ?_
      · intro p _
        dsimp only
        rw [subPerm_symm hM2sym (T \ p.1) (T \ p.2), mul_comm (∏ j ∈ p.2, M2 r j)]
        exact zmod2_add_self _
      · intro p hp _ heq
        exact (mem_filter.mp hp).2 (congrArg Prod.fst heq).symm
      · intro p hp
        simp only [mem_filter, mem_product] at hp ⊢
        exact ⟨⟨hp.1.2, hp.1.1⟩, hp.2.symm⟩
      · intro p _; rfl
    rw [hoff0, add_zero]
    refine Finset.sum_congr rfl fun J _ => by rw [zmod2_sq]
  -- Simplify second sum in ZMod 2: split J ⊆ T vs r ∈ J (zero!) vs s ∈ J, r ∉ J (odd det = 0!)
  have hS_row2 : f2_8 (∑ J ∈ Finset.powersetCard 2 (Finset.univ : Finset (Fin n)),
      (∏ j ∈ J, M r j) * subPerm M T Jᶜ) =
      ∑ J ∈ Finset.powersetCard 2 T, (∏ j ∈ J, M2 r j) * subPerm M2 T Jᶜ := by
    simp only [map_sum, map_mul, map_prod, ← subPerm_map f2_8 M]
    change (∑ J ∈ Finset.powersetCard 2 (Finset.univ : Finset (Fin n)),
        (∏ j ∈ J, M2 r j) * subPerm M2 T Jᶜ) = _
    have hsubT : Finset.powersetCard 2 T ⊆ Finset.powersetCard 2 (Finset.univ : Finset (Fin n)) :=
      Finset.powersetCard_mono (Finset.subset_univ T)
    rw [← Finset.sum_sdiff hsubT]
    have hrest0 : ∑ J ∈ Finset.powersetCard 2 Finset.univ \ Finset.powersetCard 2 T,
        (∏ j ∈ J, M2 r j) * subPerm M2 T Jᶜ = 0 := by
      rw [← Finset.sum_filter_add_sum_filter_not _ (fun J : Finset (Fin n) => r ∈ J)]
      have hr0 : ∑ J ∈ (Finset.powersetCard 2 Finset.univ \ Finset.powersetCard 2 T).filter (fun J => r ∈ J),
          (∏ j ∈ J, M2 r j) * subPerm M2 T Jᶜ = 0 := by
        refine Finset.sum_eq_zero fun J hJ => ?_
        have hrJ : r ∈ J := (mem_filter.mp hJ).2
        rw [Finset.prod_eq_zero hrJ (hM2diag r), zero_mul]
      rw [hr0, zero_add]
      -- Remaining J have s ∈ J and r ∉ J, so J = {s, b} with b ∈ T
      have hbij : ∑ J ∈ (Finset.powersetCard 2 Finset.univ \ Finset.powersetCard 2 T).filter (fun J => r ∉ J),
          (∏ j ∈ J, M2 r j) * subPerm M2 T Jᶜ =
          M2 r s * ∑ b ∈ T, M2 r b * subPerm M2 T (insert r (T.erase b)) := by
        rw [Finset.mul_sum]
        refine Finset.sum_bij'
          (fun J hJ => (J.erase s).min' (Finset.card_pos.mp (by
            have hJ2 := (Finset.mem_powersetCard.mp (Finset.mem_sdiff.mp (mem_filter.mp hJ).1).1).2
            have hsJ : s ∈ J := by
              by_contra hns
              apply (Finset.mem_sdiff.mp (mem_filter.mp hJ).1).2
              rw [Finset.mem_powersetCard]
              refine ⟨fun x hx => ?_, hJ2⟩
              simp only [T, mem_erase, mem_univ, and_true]
              exact ⟨fun h => hns (h ▸ hx), fun h => (mem_filter.mp hJ).2 (h ▸ hx)⟩
            rw [Finset.card_erase_of_mem hsJ, hJ2]; decide)))
          (fun b _ => {s, b})
          (fun J hJ => by
            have hJ2 := (Finset.mem_powersetCard.mp (Finset.mem_sdiff.mp (mem_filter.mp hJ).1).1).2
            have hsJ : s ∈ J := by
              by_contra hns
              apply (Finset.mem_sdiff.mp (mem_filter.mp hJ).1).2
              rw [Finset.mem_powersetCard]
              refine ⟨fun x hx => ?_, hJ2⟩
              simp only [T, mem_erase, mem_univ, and_true]
              exact ⟨fun h => hns (h ▸ hx), fun h => (mem_filter.mp hJ).2 (h ▸ hx)⟩
            have hmem := Finset.min'_mem (J.erase s) (Finset.card_pos.mp (by rw [Finset.card_erase_of_mem hsJ, hJ2]; decide))
            simp only [T, mem_erase, mem_univ, and_true]
            exact ⟨(mem_erase.mp hmem).1, fun h => (mem_filter.mp hJ).2 (h ▸ (mem_erase.mp hmem).2)⟩)
          (fun b hb => by
            have hbs : b ≠ s := (mem_erase.mp hb).1
            have hbr : b ≠ r := (mem_erase.mp (mem_erase.mp hb).2).1
            refine mem_filter.mpr ⟨Finset.mem_sdiff.mpr ⟨Finset.mem_powersetCard.mpr
              ⟨Finset.subset_univ _, Finset.card_pair hbs.symm⟩, ?_⟩, ?_⟩
            · intro hm; have := (Finset.mem_powersetCard.mp hm).1 (mem_insert_self s {b}); simp [T] at this
            · simp [hrs, hbr.symm])
          (fun J hJ => by
            have hJ2 := (Finset.mem_powersetCard.mp (Finset.mem_sdiff.mp (mem_filter.mp hJ).1).1).2
            have hsJ : s ∈ J := by
              by_contra hns
              apply (Finset.mem_sdiff.mp (mem_filter.mp hJ).1).2
              rw [Finset.mem_powersetCard]
              refine ⟨fun x hx => ?_, hJ2⟩
              simp only [T, mem_erase, mem_univ, and_true]
              exact ⟨fun h => hns (h ▸ hx), fun h => (mem_filter.mp hJ).2 (h ▸ hx)⟩
            have hcard1 : (J.erase s).card = 1 := by rw [Finset.card_erase_of_mem hsJ, hJ2]
            obtain ⟨b, hb_eq⟩ := Finset.card_eq_one.mp hcard1
            have hmin : (J.erase s).min' (Finset.card_pos.mp (by rw [hcard1]; decide)) = b := by simp [hb_eq]
            rw [hmin]
            ext x; constructor
            · intro hx; rcases mem_insert.mp hx with rfl | hx2
              · exact hsJ
              · rw [mem_singleton.mp hx2]; have : b ∈ J.erase s := by rw [hb_eq]; simp
                exact (mem_erase.mp this).2
            · intro hx; by_cases hxs : x = s
              · simp [hxs]
              · have : x ∈ J.erase s := mem_erase.mpr ⟨hxs, hx⟩
                rw [hb_eq, mem_singleton] at this; simp [this])
          (fun b hb => by
            have hbs : b ≠ s := (mem_erase.mp hb).1
            have her : ({s, b} : Finset (Fin n)).erase s = {b} := by
              ext x; simp only [mem_erase, mem_insert, mem_singleton]
              constructor
              · rintro ⟨h1, rfl | rfl⟩
                · exact (h1 rfl).elim
                · rfl
              · rintro rfl; exact ⟨hbs, Or.inr rfl⟩
            simp [her])
          (fun J hJ => by
            have hJ2 := (Finset.mem_powersetCard.mp (Finset.mem_sdiff.mp (mem_filter.mp hJ).1).1).2
            have hsJ : s ∈ J := by
              by_contra hns
              apply (Finset.mem_sdiff.mp (mem_filter.mp hJ).1).2
              rw [Finset.mem_powersetCard]
              refine ⟨fun x hx => ?_, hJ2⟩
              simp only [T, mem_erase, mem_univ, and_true]
              exact ⟨fun h => hns (h ▸ hx), fun h => (mem_filter.mp hJ).2 (h ▸ hx)⟩
            have hcard1 : (J.erase s).card = 1 := by rw [Finset.card_erase_of_mem hsJ, hJ2]
            obtain ⟨b, hb_eq⟩ := Finset.card_eq_one.mp hcard1
            have hmin : (J.erase s).min' (Finset.card_pos.mp (by rw [hcard1]; decide)) = b := by simp [hb_eq]
            rw [hmin]
            have hJeq : J = {s, b} := by
              ext x; constructor
              · intro hx; by_cases hxs : x = s
                · simp [hxs]
                · have : x ∈ J.erase s := mem_erase.mpr ⟨hxs, hx⟩
                  rw [hb_eq, mem_singleton] at this; simp [this]
              · intro hx; rcases mem_insert.mp hx with rfl | hx2
                · exact hsJ
                · rw [mem_singleton.mp hx2]; have : b ∈ J.erase s := by rw [hb_eq]; simp
                  exact (mem_erase.mp this).2
            have hbs : s ≠ b := by
              intro h; have : b ∈ J.erase s := by rw [hb_eq]; simp
              exact (mem_erase.mp this).1 h.symm
            have hcompl_eq : Jᶜ = insert r (T.erase b) := by
              rw [hJeq]; ext x
              simp only [Finset.mem_compl, mem_insert, mem_singleton, not_or, T, mem_erase, mem_univ, and_true]
              by_cases hxr : x = r
              · rw [hxr]
                have hrb : r ≠ b := fun h => (mem_filter.mp hJ).2 (by rw [hJeq, h]; simp)
                simp [hrs, hrb]
              · simp [hxr]; tauto
            rw [hcompl_eq, hJeq, Finset.prod_pair hbs]; ring)
      rw [hbij, subPerm_compl_row_expansion_zmod2 M2 hM2sym hM2diag heven hrs, mul_zero]
    rw [hrest0, zero_add]
  rw [hS_both2, hS_row2, ← Finset.sum_sub_distrib]
  refine Finset.sum_eq_zero fun J hJ => ?_
  rw [← mul_sub]
  -- Show subPerm M2 (T \ J) (T \ J) = subPerm M2 T Jᶜ term-by-term!
  have hJT : J ⊆ T := (Finset.mem_powersetCard.mp hJ).1
  obtain ⟨j₁, j₂, hj, rfl⟩ := Finset.card_eq_two.mp (Finset.mem_powersetCard.mp hJ).2
  have h1 : subPerm M2 T ({j₁, j₂}ᶜ) = subPerm A2 {j₁, j₂} {r, s} := by
    rw [← hT_eq]
    exact jacobi_minor_zmod2 M2 A2 hM2A2 {r, s} {j₁, j₂} (by rw [Finset.card_pair hrs, Finset.card_pair hj])
  let Q : Finset (Fin n) := {r, s, j₁, j₂}
  have hQ_compl : Qᶜ = T \ {j₁, j₂} := by
    ext x; simp [Q, T, not_or]; tauto
  have h2 : subPerm M2 (T \ {j₁, j₂}) (T \ {j₁, j₂}) = subPerm A2 Q Q := by
    rw [← hQ_compl]
    exact jacobi_minor_zmod2 M2 A2 hM2A2 Q Q rfl
  have h3 : subPerm A2 Q Q = subPerm A2 {j₁, j₂} {r, s} := by
    have hj1r : j₁ ≠ r := (mem_erase.mp (mem_erase.mp (hJT (by simp))).2).1
    have hj1s : j₁ ≠ s := (mem_erase.mp (hJT (by simp))).1
    have hj2r : j₂ ≠ r := (mem_erase.mp (mem_erase.mp (hJT (by simp))).2).1
    have hj2s : j₂ ≠ s := (mem_erase.mp (hJT (by simp))).1
    exact subPerm_quad_eq_pair_zmod2 A2 hA2sym hA2diag hrs hj hj1r hj1s hj2r hj2s hA2rs
  rw [h1, h2, h3, sub_self, mul_zero]

/-! ### Section 5: Cliques `K_{2m}`, block-diagonal permanents, and graph reduction -/

private lemma perm_fromBlocks_zero {a b : ℕ} {R : Type*} [CommSemiring R]
    (A : Matrix (Fin a) (Fin a) R) (B : Matrix (Fin b) (Fin b) R) :
    (Matrix.fromBlocks A 0 0 B).permanent = A.permanent * B.permanent := by
  rw [Matrix.permanent, Matrix.permanent, Matrix.permanent, Finset.sum_mul_sum, ← Finset.sum_product']
  let S : Finset (Equiv.Perm (Fin a ⊕ Fin b)) :=
    Finset.univ.filter fun σ => (∀ x : Fin a, ∃ y : Fin a, σ (Sum.inl x) = Sum.inl y)
  have hzero : ∀ σ : Equiv.Perm (Fin a ⊕ Fin b), σ ∉ S →
      ∏ i : Fin a ⊕ Fin b, Matrix.fromBlocks A 0 0 B (σ i) i = 0 := by
    intro σ hσ
    simp only [S, mem_filter, mem_univ, true_and] at hσ
    push Not at hσ
    obtain ⟨x, hx⟩ := hσ
    cases h : σ (Sum.inl x) with
    | inl y => exact (hx y h).elim
    | inr y =>
      refine Finset.prod_eq_zero (mem_univ (Sum.inl x)) ?_
      rw [h]; simp
  rw [← Finset.sum_subset (Finset.subset_univ S) (fun σ _ hσ => hzero σ hσ)]
  let leftP (σ : Equiv.Perm (Fin a ⊕ Fin b)) (x : Fin a) : Fin a :=
    match σ (Sum.inl x) with | Sum.inl y => y | Sum.inr _ => x
  let rightP (σ : Equiv.Perm (Fin a ⊕ Fin b)) (x : Fin b) : Fin b :=
    match σ (Sum.inr x) with | Sum.inr y => y | Sum.inl _ => x
  have hleft_spec : ∀ σ ∈ S, ∀ x : Fin a, σ (Sum.inl x) = Sum.inl (leftP σ x) := by
    intro σ hσ x
    obtain ⟨y, hy⟩ := (mem_filter.mp hσ).2 x
    dsimp only [leftP]; rw [hy]
  have hleft_inj : ∀ σ ∈ S, Function.Injective (leftP σ) := by
    intro σ hσ x₁ x₂ h
    have h1 := hleft_spec σ hσ x₁
    have h2 := hleft_spec σ hσ x₂
    rw [h, ← h2] at h1
    exact Sum.inl.inj (σ.injective h1)
  have hright_spec : ∀ σ ∈ S, ∀ x : Fin b, σ (Sum.inr x) = Sum.inr (rightP σ x) := by
    intro σ hσ x
    cases h : σ (Sum.inr x) with
    | inr y => dsimp only [rightP]; rw [h]
    | inl y =>
      exfalso
      have hcard_img : ((Finset.univ : Finset (Fin a)).image (leftP σ)).card = Fintype.card (Fin a) := by
        rw [Finset.card_image_of_injective _ (hleft_inj σ hσ), Finset.card_univ]
      have hfull : (Finset.univ : Finset (Fin a)).image (leftP σ) = Finset.univ :=
        Finset.eq_univ_of_card _ hcard_img
      obtain ⟨z, _, hz⟩ := mem_image.mp (hfull.symm ▸ mem_univ y)
      exact Sum.inl_ne_inr (σ.injective (by rw [hleft_spec σ hσ z, hz, h]))
  have hright_inj : ∀ σ ∈ S, Function.Injective (rightP σ) := by
    intro σ hσ x₁ x₂ h
    have h1 := hright_spec σ hσ x₁
    have h2 := hright_spec σ hσ x₂
    rw [h, ← h2] at h1
    exact Sum.inr.inj (σ.injective h1)
  refine Finset.sum_bij'
    (fun σ hσ =>
      (Equiv.ofBijective (leftP σ) (Finite.injective_iff_bijective.mp (hleft_inj σ hσ)),
       Equiv.ofBijective (rightP σ) (Finite.injective_iff_bijective.mp (hright_inj σ hσ))))
    (fun p _ => Equiv.sumCongr p.1 p.2)
    (fun _ _ => mem_univ _)
    (fun p _ => mem_filter.mpr ⟨mem_univ _, fun x => ⟨p.1 x, rfl⟩⟩)
    (fun σ hσ => by
      ext z; rcases z with x | x
      · exact (hleft_spec σ hσ x).symm
      · exact (hright_spec σ hσ x).symm)
    (fun p _ => Prod.ext (Equiv.ext fun _ => rfl) (Equiv.ext fun _ => rfl))
    (fun σ hσ => by
      rw [Fintype.prod_sum_type]
      congr 1
      · refine Finset.prod_congr rfl fun x _ => ?_
        rw [hleft_spec σ hσ x]; rfl
      · refine Finset.prod_congr rfl fun x _ => ?_
        rw [hright_spec σ hσ x]; rfl)

private lemma perm_inv_clique_zmod8 (m : ℕ) (hm : 1 ≤ m) :
    let K : Matrix (Fin (2 * m)) (Fin (2 * m)) (ZMod 8) := Matrix.of fun i j => if i = j then 0 else 1
    IsUnit K.det ∧ (K⁻¹).permanent = 1 := by
  intro K
  have hodd' : IsUnit ((2 * m - 1 : ℕ) : ZMod 8) := by
    apply zmod8_isUnit_of_cast2_eq_one
    have h1 : f2_8 ((2 * m - 1 : ℕ) : ZMod 8) = ((2 * m - 1 : ℕ) : ZMod 2) := by
      rw [map_natCast]
    rw [h1, ← ZMod.natCast_mod, show (2 * m - 1) % 2 = 1 by omega]; rfl
  obtain ⟨u, hu⟩ := hodd'
  let a : ZMod 8 := (u⁻¹ : (ZMod 8)ˣ).val
  have ha : ((2 * m - 1 : ℕ) : ZMod 8) * a = 1 := by rw [← hu]; exact Units.mul_inv u
  let M : Matrix (Fin (2 * m)) (Fin (2 * m)) (ZMod 8) :=
    Matrix.of fun i j => if i = j then a - 1 else a
  have hKM : K * M = 1 := by
    ext i j
    simp only [K, M, Matrix.mul_apply, Matrix.of_apply, Matrix.one_apply]
    have hsum : ∑ k : Fin (2 * m), (if i = k then (0 : ZMod 8) else 1) * (if k = j then a - 1 else a) =
        ∑ k ∈ Finset.univ.erase i, (if k = j then a - 1 else a) := by
      rw [← Finset.add_sum_erase _ _ (mem_univ i)]
      simp only [↓reduceIte, zero_mul, zero_add]
      refine Finset.sum_congr rfl fun k hk => by simp [(mem_erase.mp hk).1.symm]
    rw [hsum]
    by_cases hij : i = j
    · subst hij
      have h1 : ∀ k ∈ Finset.univ.erase i, (if k = i then a - 1 else a) = a :=
        fun k hk => if_neg (mem_erase.mp hk).1
      rw [Finset.sum_congr rfl h1, Finset.sum_const, Finset.card_erase_of_mem (mem_univ i),
        Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, ha, if_pos rfl]
    · have hj_mem : j ∈ Finset.univ.erase i := mem_erase.mpr ⟨Ne.symm hij, mem_univ j⟩
      rw [← Finset.add_sum_erase _ _ hj_mem, if_pos rfl]
      have h1 : ∀ k ∈ (Finset.univ.erase i).erase j, (if k = j then a - 1 else a) = a :=
        fun k hk => if_neg (mem_erase.mp hk).1
      rw [Finset.sum_congr rfl h1, Finset.sum_const, Finset.card_erase_of_mem hj_mem,
        Finset.card_erase_of_mem (mem_univ i), Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      have hcard : ((2 * m - 1 - 1 : ℕ) : ZMod 8) = ((2 * m - 1 : ℕ) : ZMod 8) - 1 := by
        rw [Nat.cast_sub (by omega), Nat.cast_one]
      rw [hcard, if_neg hij]
      linear_combination ha
  have hK_unit : IsUnit K.det :=
    isUnit_iff_exists_inv.mpr ⟨M.det, by rw [← Matrix.det_mul, hKM, Matrix.det_one]⟩
  have hK_inv : K⁻¹ = M := by
    have h1 := congrArg (fun X => K⁻¹ * X) hKM
    rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul K hK_unit, Matrix.one_mul, Matrix.mul_one] at h1
    exact h1.symm
  refine ⟨hK_unit, ?_⟩
  rw [hK_inv, Matrix.permanent]
  -- Expand ∏ i, (a + (if σ i = i then -1 else 0)) via Finset.prod_add
  have hexp : ∑ σ : Equiv.Perm (Fin (2 * m)), ∏ i : Fin (2 * m), M (σ i) i =
      ∑ S : Finset (Fin (2 * m)),
        a ^ S.card * (-1 : ZMod 8) ^ (2 * m - S.card) * (Nat.factorial S.card : ZMod 8) := by
    have hprod : ∀ σ : Equiv.Perm (Fin (2 * m)),
        ∏ i : Fin (2 * m), M (σ i) i =
        ∑ S : Finset (Fin (2 * m)),
          (∏ _i ∈ S, a) * (∏ i ∈ Sᶜ, (if σ i = i then (-1 : ZMod 8) else 0)) := by
      intro σ
      have h1 : ∀ i : Fin (2 * m), M (σ i) i = a + (if σ i = i then (-1 : ZMod 8) else 0) := by
        intro i; simp only [M, Matrix.of_apply]; split_ifs <;> ring
      simp_rw [h1]
      rw [Finset.prod_add]
      have hp : (Finset.univ : Finset (Fin (2 * m))).powerset = Finset.univ := by ext S; simp
      rw [hp]
      refine Finset.sum_congr rfl fun S _ => ?_
      have hc : Finset.univ \ S = Sᶜ := by ext x; simp
      rw [hc]
    simp_rw [hprod]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun S _ => ?_
    simp_rw [Finset.prod_const, ← Finset.mul_sum]
    rw [mul_assoc]
    congr 1
    have hfix : ∀ σ : Equiv.Perm (Fin (2 * m)),
        (∏ i ∈ Sᶜ, (if σ i = i then (-1 : ZMod 8) else 0)) =
        if ∀ i ∈ Sᶜ, σ i = i then (-1 : ZMod 8) ^ (2 * m - S.card) else 0 := by
      intro σ
      by_cases h : ∀ i ∈ Sᶜ, σ i = i
      · rw [if_pos h]
        rw [Finset.prod_congr rfl (fun i hi => if_pos (h i hi)), Finset.prod_const,
          Finset.card_compl, Fintype.card_fin]
      · rw [if_neg h]
        push Not at h
        obtain ⟨i0, hi0, hne⟩ := h
        exact Finset.prod_eq_zero hi0 (if_neg hne)
    simp_rw [hfix, Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul]
    rw [mul_comm]
    congr 1
    have hcard_fix : (Finset.univ.filter (fun σ : Equiv.Perm (Fin (2 * m)) => ∀ i ∈ Sᶜ, σ i = i)).card =
        Nat.factorial S.card := by
      have hbij : Fintype.card {σ : Equiv.Perm (Fin (2 * m)) // ∀ i ∈ Sᶜ, σ i = i} =
          Fintype.card (Equiv.Perm {x // x ∈ S}) := by
        refine Fintype.card_congr
          { toFun := fun ⟨σ, hσ⟩ =>
              { toFun := fun x => ⟨σ x.1, by
                  by_contra hnot
                  have h1 : σ (σ x.1) = σ x.1 := hσ (σ x.1) (Finset.mem_compl.mpr hnot)
                  have h2 : σ x.1 = x.1 := σ.injective h1
                  exact hnot (h2.symm ▸ x.2)⟩
                invFun := fun y => ⟨σ⁻¹ y.1, by
                  by_contra hnot
                  have h1 : σ (σ⁻¹ y.1) = σ⁻¹ y.1 := hσ (σ⁻¹ y.1) (Finset.mem_compl.mpr hnot)
                  have hinv_a : σ (σ⁻¹ y.1) = y.1 := Equiv.apply_symm_apply σ y.1
                  rw [hinv_a] at h1
                  exact hnot (h1 ▸ y.2)⟩
                left_inv := fun x => Subtype.ext (Equiv.symm_apply_apply σ x.1)
                right_inv := fun y => Subtype.ext (Equiv.apply_symm_apply σ y.1) }
            invFun := fun τ =>
              ⟨{ toFun := fun x => if hx : x ∈ S then (τ ⟨x, hx⟩).1 else x
                 invFun := fun y => if hy : y ∈ S then (τ.symm ⟨y, hy⟩).1 else y
                 left_inv := fun x => by
                   dsimp only; by_cases hx : x ∈ S
                   · simp [hx, (τ ⟨x, hx⟩).2]
                   · simp [hx]
                 right_inv := fun y => by
                   dsimp only; by_cases hy : y ∈ S
                   · simp [hy, (τ.symm ⟨y, hy⟩).2]
                   · simp [hy] },
               fun i hi => by
                 have hnot : i ∉ S := Finset.mem_compl.mp hi
                 simp [hnot]⟩
            left_inv := fun ⟨σ, hσ⟩ => by
              ext x; dsimp only [Equiv.coe_fn_mk]
              by_cases hx : x ∈ S
              · simp [hx]
              · simp [hx, hσ x (Finset.mem_compl.mpr hx)]
            right_inv := fun τ => Equiv.ext fun x => Subtype.ext (by simp) }
      rw [← Fintype.card_subtype, hbij, Fintype.card_perm, Fintype.card_coe]
    rw [hcard_fix]
  rw [hexp]
  -- Group by j = S.card ∈ range (2 * m + 1)
  rw [← Finset.sum_fiberwise_of_maps_to (g := Finset.card) (t := Finset.range (2 * m + 1))
    (fun S _ => Finset.mem_range.mpr (Nat.lt_succ_of_le (by simpa using Finset.card_le_univ S)))]
  have hgroup : ∀ j ∈ Finset.range (2 * m + 1),
      (∑ S ∈ Finset.univ.filter (fun S : Finset (Fin (2 * m)) => S.card = j),
        a ^ S.card * (-1 : ZMod 8) ^ (2 * m - S.card) * (Nat.factorial S.card : ZMod 8)) =
      ((2 * m).choose j : ZMod 8) * a ^ j * (-1 : ZMod 8) ^ (2 * m - j) * (Nat.factorial j : ZMod 8) := by
    intro j _
    rw [Finset.sum_congr rfl (fun S hS => by rw [(mem_filter.mp hS).2]), Finset.sum_const, nsmul_eq_mul]
    have hcard_j : (Finset.univ.filter (fun S : Finset (Fin (2 * m)) => S.card = j)).card = (2 * m).choose j := by
      have heq : Finset.univ.filter (fun S : Finset (Fin (2 * m)) => S.card = j) =
          Finset.powersetCard j Finset.univ := by ext S; simp [Finset.mem_powersetCard]
      rw [heq, Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]
    rw [hcard_j]; ring
  rw [Finset.sum_congr rfl hgroup]
  have hge4 : ∀ j ∈ Finset.range (2 * m + 1), 4 ≤ j →
      ((2 * m).choose j : ZMod 8) * a ^ j * (-1 : ZMod 8) ^ (2 * m - j) * (Nat.factorial j : ZMod 8) = 0 := by
    intro j _ hj
    have hdvd : 8 ∣ Nat.factorial j := dvd_trans (by decide : 8 ∣ Nat.factorial 4) (Nat.factorial_dvd_factorial hj)
    have h0 : (Nat.factorial j : ZMod 8) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr hdvd
    rw [h0, mul_zero]
  by_cases hm1 : m = 1
  · subst hm1
    simp only [Nat.mul_one, Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
    have ha1 : a = 1 := by
      have : ((2 * 1 - 1 : ℕ) : ZMod 8) = 1 := rfl
      rw [this, one_mul] at ha; exact ha
    rw [ha1]; decide
  · have hm2 : 2 ≤ m := by omega
    have hsub : Finset.range 4 ⊆ Finset.range (2 * m + 1) := Finset.range_mono (by omega)
    rw [← Finset.sum_subset hsub (fun j hj hnot => hge4 j hj (by simp at hnot; omega))]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
    have h2m_even : (-1 : ZMod 8) ^ (2 * m) = 1 := Even.neg_one_pow ⟨m, by omega⟩
    have h2m1_odd : (-1 : ZMod 8) ^ (2 * m - 1) = -1 := Odd.neg_one_pow ⟨m - 1, by omega⟩
    have h2m2_even : (-1 : ZMod 8) ^ (2 * m - 2) = 1 := Even.neg_one_pow ⟨m - 1, by omega⟩
    have h2m3_odd : (-1 : ZMod 8) ^ (2 * m - 3) = -1 := Odd.neg_one_pow ⟨m - 2, by omega⟩
    have hc0 : (2 * m).choose 0 = 1 := Nat.choose_zero_right _
    have hc1 : (2 * m).choose 1 = 2 * m := Nat.choose_one_right _
    have hc2 : (2 * m).choose 2 * 2 = 2 * m * (2 * m - 1) := by
      rw [Nat.choose_two_right]; exact Nat.div_mul_cancel (Nat.even_mul_pred_self (2 * m)).two_dvd
    have hc3 : (2 * m).choose 3 * 6 = 2 * m * (2 * m - 1) * (2 * m - 2) := by
      have hdesc := Nat.descFactorial_eq_factorial_mul_choose (2 * m) 3
      rw [Nat.descFactorial_succ, Nat.descFactorial_succ, Nat.descFactorial_succ,
        Nat.descFactorial_zero] at hdesc
      have hf3 : Nat.factorial 3 = 6 := by decide
      rw [hf3] at hdesc
      calc (2 * m).choose 3 * 6 = 6 * (2 * m).choose 3 := mul_comm _ _
        _ = (2 * m - 2) * ((2 * m - 1) * (2 * m * 1)) := hdesc.symm
        _ = 2 * m * (2 * m - 1) * (2 * m - 2) := by ring
    have ht0 : ((2 * m).choose 0 : ZMod 8) * a ^ 0 * (-1 : ZMod 8) ^ (2 * m - 0) * (Nat.factorial 0 : ZMod 8) = 1 := by
      simp [hc0, h2m_even]
    have ht1 : ((2 * m).choose 1 : ZMod 8) * a ^ 1 * (-1 : ZMod 8) ^ (2 * m - 1) * (Nat.factorial 1 : ZMod 8) =
        -(2 * m : ZMod 8) * a := by
      simp [hc1, h2m1_odd]
    have ht2 : ((2 * m).choose 2 : ZMod 8) * a ^ 2 * (-1 : ZMod 8) ^ (2 * m - 2) * (Nat.factorial 2 : ZMod 8) =
        (2 * m : ZMod 8) * a := by
      have hcast : ((2 * m).choose 2 : ZMod 8) * (Nat.factorial 2 : ZMod 8) =
          (2 * m : ZMod 8) * ((2 * m - 1 : ℕ) : ZMod 8) := by
        have := congrArg (Nat.cast : ℕ → ZMod 8) hc2
        simpa [Nat.factorial] using this
      rw [h2m2_even, mul_one]
      calc ((2 * m).choose 2 : ZMod 8) * a ^ 2 * (Nat.factorial 2 : ZMod 8)
          = (((2 * m).choose 2 : ZMod 8) * (Nat.factorial 2 : ZMod 8)) * a * a := by ring
        _ = (2 * m : ZMod 8) * (((2 * m - 1 : ℕ) : ZMod 8) * a) * a := by rw [hcast]; ring
        _ = (2 * m : ZMod 8) * a := by rw [ha, mul_one]
    have ht3 : ((2 * m).choose 3 : ZMod 8) * a ^ 3 * (-1 : ZMod 8) ^ (2 * m - 3) * (Nat.factorial 3 : ZMod 8) = 0 := by
      have hcast : ((2 * m).choose 3 : ZMod 8) * (Nat.factorial 3 : ZMod 8) =
          (2 * m : ZMod 8) * ((2 * m - 1 : ℕ) : ZMod 8) * ((2 * m - 2 : ℕ) : ZMod 8) := by
        have := congrArg (Nat.cast : ℕ → ZMod 8) hc3
        simpa [Nat.factorial] using this
      have h8dvd : 8 ∣ (2 * m) * (2 * m - 2) := by
        have heq : 2 * m * (2 * m - 2) = 4 * (m * (m - 1)) := by
          have : 2 * m - 2 = 2 * (m - 1) := by omega
          rw [this]; ring
        rw [heq]
        obtain ⟨k, hk⟩ := Nat.even_mul_pred_self m
        exact ⟨k, by omega⟩
      have h0 : ((2 * m * (2 * m - 2) : ℕ) : ZMod 8) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr h8dvd
      have h0' : (2 * m : ZMod 8) * ((2 * m - 2 : ℕ) : ZMod 8) = 0 := by
        simpa [Nat.cast_mul] using h0
      calc ((2 * m).choose 3 : ZMod 8) * a ^ 3 * (-1 : ZMod 8) ^ (2 * m - 3) * (Nat.factorial 3 : ZMod 8)
          = ((2 * m).choose 3 : ZMod 8) * (Nat.factorial 3 : ZMod 8) * a ^ 3 * (-1 : ZMod 8) ^ (2 * m - 3) := by ring
        _ = ((2 * m : ZMod 8) * ((2 * m - 2 : ℕ) : ZMod 8)) * (((2 * m - 1 : ℕ) : ZMod 8) * a ^ 3 * (-1 : ZMod 8) ^ (2 * m - 3)) := by
            rw [hcast]; ring
        _ = 0 := by rw [h0', zero_mul]
    rw [ht0, ht1, ht2, ht3]; ring

private lemma perm_inv_zmod8_of_symm_diag4 : ∀ n : ℕ,
    ∀ A : Matrix (Fin n) (Fin n) (ZMod 8),
      A.IsSymm → (∀ i, A i i = 0 ∨ A i i = 4) → IsUnit A.det → (A⁻¹).permanent = 1 := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro A hSym hDiag hA
    rcases n with _ | n'
    · exact Matrix.permanent_isEmpty
    · have hDiag2 : ∀ i, f2_8 (A i i) = 0 := fun i => by rcases hDiag i with h | h <;> rw [h] <;> decide
      have heven : Even (n' + 1) := even_of_isUnit_det_symm_diag2_zmod8 A hSym hDiag2 hA
      have hn2 : 2 ≤ n' + 1 := by obtain ⟨m, hm⟩ := heven; omega
      -- Pick an edge (u, v) with f2_8 (A u v) = 1
      have hex_edge : ∃ u v : Fin (n' + 1), u ≠ v ∧ f2_8 (A u v) = 1 := by
        by_contra hno
        push Not at hno
        have h0 : A.map f2_8 = 0 := by
          ext i j
          by_cases hij : i = j
          · subst hij; simp [hDiag2 i]
          · have hne1 := hno i j hij
            simp only [Matrix.map_apply, Matrix.zero_apply]
            generalize f2_8 (A i j) = y at hne1 ⊢
            revert y hne1; decide
        have hd0 : f2_8 A.det = 0 := by
          rw [← det_map f2_8 A, h0, Matrix.det_zero]
        exact absurd (hd0.symm.trans (zmod8_cast2_eq_one_of_isUnit A.det hA)) (by decide)
      obtain ⟨u, v, huv, huv1⟩ := hex_edge
      -- Step A/B helper: clear all vertices with (f2_8 (A u w), f2_8 (A v w)) ∈ {(1,0), (0,1)}
      -- without increasing W = {w | w ≠ u ∧ w ≠ v ∧ f2_8 (A u w) = 1 ∧ f2_8 (A v w) = 1}
      let badSet (X : Matrix (Fin (n' + 1)) (Fin (n' + 1)) (ZMod 8)) : Finset (Fin (n' + 1)) :=
        Finset.univ.filter fun w => w ≠ u ∧ w ≠ v ∧ f2_8 (X u w) ≠ f2_8 (X v w)
      let WSet (X : Matrix (Fin (n' + 1)) (Fin (n' + 1)) (ZMod 8)) : Finset (Fin (n' + 1)) :=
        Finset.univ.filter fun w => w ≠ u ∧ w ≠ v ∧ f2_8 (X u w) = 1 ∧ f2_8 (X v w) = 1
      have hclear_bad : ∀ k : ℕ, ∀ X : Matrix (Fin (n' + 1)) (Fin (n' + 1)) (ZMod 8),
          (badSet X).card = k → X.IsSymm → (∀ i, X i i = 0 ∨ X i i = 4) → IsUnit X.det →
          f2_8 (X u v) = 1 →
          ∃ Y : Matrix (Fin (n' + 1)) (Fin (n' + 1)) (ZMod 8),
            Y.IsSymm ∧ (∀ i, Y i i = 0 ∨ Y i i = 4) ∧ IsUnit Y.det ∧
            f2_8 (Y u v) = 1 ∧ badSet Y = ∅ ∧ WSet Y = WSet X ∧
            (Y⁻¹).permanent = (X⁻¹).permanent := by
        intro k
        induction k with
        | zero =>
          intro X hk hXsym hXdiag hX hXuv
          exact ⟨X, hXsym, hXdiag, hX, hXuv, Finset.card_eq_zero.mp hk, rfl, rfl⟩
        | succ k ihk =>
          intro X hk hXsym hXdiag hX hXuv
          obtain ⟨w, hw⟩ := Finset.card_pos.mp (by omega : 0 < (badSet X).card)
          have hwu : w ≠ u := (mem_filter.mp hw).2.1
          have hwv : w ≠ v := (mem_filter.mp hw).2.2.1
          have hdiff : f2_8 (X u w) ≠ f2_8 (X v w) := (mem_filter.mp hw).2.2.2
          have hXdiag2 : ∀ i, f2_8 (X i i) = 0 := fun i => by rcases hXdiag i with h | h <;> rw [h] <;> decide
          have hcases : (f2_8 (X u w) = 1 ∧ f2_8 (X v w) = 0) ∨ (f2_8 (X u w) = 0 ∧ f2_8 (X v w) = 1) := by
            generalize f2_8 (X u w) = a at hdiff; generalize f2_8 (X v w) = b at hdiff
            revert a b hdiff; decide
          rcases hcases with ⟨huw1, hvw0⟩ | ⟨huw0, hvw1⟩
          · -- Shear v -> w (adds row/col v to row/col w, allowed since f2_8 (X w v) = 0)
            have hwv0 : f2_8 (X w v) = 0 := by rw [hXsym.apply v w]; exact hvw0
            let E : Matrix (Fin (n' + 1)) (Fin (n' + 1)) (ZMod 8) := 1 + Matrix.single v w 1
            let X1 := Eᵀ * X * E
            have hsh := perm_inv_shear_zmod8 X hXsym hXdiag hX hwv hwv0
            have hX1_entry : ∀ i j, f2_8 (X1 i j) = f2_8 (X i j) +
                (if i = w then f2_8 (X v j) else 0) + (if j = w then f2_8 (X i v) else 0) := by
              intro i j
              dsimp only [X1, E]
              rw [shear_entry_zmod8]
              simp only [map_add, apply_ite f2_8, map_zero]
              by_cases h1 : i = w <;> by_cases h2 : j = w <;> simp [h1, h2, hXdiag2]
            have hX1uv : f2_8 (X1 u v) = 1 := by simp [hX1_entry, hwu.symm, hwv.symm, hXuv]
            have hX1uw : f2_8 (X1 u w) = 0 := by simp [hX1_entry, hwu.symm, huw1, hXuv]; decide
            have hX1vw : f2_8 (X1 v w) = 0 := by simp [hX1_entry, hwv.symm, hvw0, hXdiag2]
            have hX1_other : ∀ z, z ≠ w → f2_8 (X1 u z) = f2_8 (X u z) ∧ f2_8 (X1 v z) = f2_8 (X v z) := by
              intro z hz; simp [hX1_entry, hwu.symm, hwv.symm, hz]
            have hbad_eq : badSet X1 = (badSet X).erase w := by
              ext z; simp only [badSet, mem_filter, mem_univ, true_and, mem_erase]
              by_cases hzw : z = w
              · subst hzw; simp [hX1uw, hX1vw]
              · simp [hzw, hX1_other z hzw]
            have hW_eq : WSet X1 = WSet X := by
              ext z; simp only [WSet, mem_filter, mem_univ, true_and]
              by_cases hzw : z = w
              · subst hzw; simp [hX1uw, hvw0]
              · simp [hX1_other z hzw]
            have hcard1 : (badSet X1).card = k := by
              rw [hbad_eq, Finset.card_erase_of_mem hw, hk]; omega
            obtain ⟨Y, h1, h2, h3, h4, h5, h6, h7⟩ := ihk X1 hcard1 hsh.1 hsh.2.1 hsh.2.2.1 hX1uv
            exact ⟨Y, h1, h2, h3, h4, h5, h6.trans hW_eq, h7.trans hsh.2.2.2⟩
          · -- Shear u -> w (allowed since f2_8 (X w u) = 0)
            have hwu0 : f2_8 (X w u) = 0 := by rw [hXsym.apply u w]; exact huw0
            let E : Matrix (Fin (n' + 1)) (Fin (n' + 1)) (ZMod 8) := 1 + Matrix.single u w 1
            let X1 := Eᵀ * X * E
            have hsh := perm_inv_shear_zmod8 X hXsym hXdiag hX hwu hwu0
            have hX1_entry : ∀ i j, f2_8 (X1 i j) = f2_8 (X i j) +
                (if i = w then f2_8 (X u j) else 0) + (if j = w then f2_8 (X i u) else 0) := by
              intro i j
              dsimp only [X1, E]
              rw [shear_entry_zmod8]
              simp only [map_add, apply_ite f2_8, map_zero]
              by_cases h1 : i = w <;> by_cases h2 : j = w <;> simp [h1, h2, hXdiag2]
            have hX1uv : f2_8 (X1 u v) = 1 := by simp [hX1_entry, hwu.symm, hwv.symm, hXuv]
            have hX1uw : f2_8 (X1 u w) = 0 := by simp [hX1_entry, hwu.symm, huw0, hXdiag2]
            have hX1vw : f2_8 (X1 v w) = 0 := by
              simp [hX1_entry, hwv.symm, hvw1, hXsym.apply u v, hXuv]; decide
            have hX1_other : ∀ z, z ≠ w → f2_8 (X1 u z) = f2_8 (X u z) ∧ f2_8 (X1 v z) = f2_8 (X v z) := by
              intro z hz; simp [hX1_entry, hwu.symm, hwv.symm, hz]
            have hbad_eq : badSet X1 = (badSet X).erase w := by
              ext z; simp only [badSet, mem_filter, mem_univ, true_and, mem_erase]
              by_cases hzw : z = w
              · subst hzw; simp [hX1uw, hX1vw]
              · simp [hzw, hX1_other z hzw]
            have hW_eq : WSet X1 = WSet X := by
              ext z; simp only [WSet, mem_filter, mem_univ, true_and]
              by_cases hzw : z = w
              · subst hzw; simp [hX1uw, huw0]
              · simp [hX1_other z hzw]
            have hcard1 : (badSet X1).card = k := by
              rw [hbad_eq, Finset.card_erase_of_mem hw, hk]; omega
            obtain ⟨Y, h1, h2, h3, h4, h5, h6, h7⟩ := ihk X1 hcard1 hsh.1 hsh.2.1 hsh.2.2.1 hX1uv
            exact ⟨Y, h1, h2, h3, h4, h5, h6.trans hW_eq, h7.trans hsh.2.2.2⟩
      -- Now strong induction on (WSet X).card to reduce to a split-off clique!
      have hW_ind : ∀ wcard : ℕ, ∀ X : Matrix (Fin (n' + 1)) (Fin (n' + 1)) (ZMod 8),
          (WSet X).card = wcard → X.IsSymm → (∀ i, X i i = 0 ∨ X i i = 4) → IsUnit X.det →
          f2_8 (X u v) = 1 → (X⁻¹).permanent = 1 := by
        intro wcard
        induction wcard using Nat.strong_induction_on with
        | h wcard ihw =>
          intro X hwc hXsym hXdiag hX hXuv
          obtain ⟨Y, hYsym, hYdiag, hY, hYuv, hYbad, hYW, hYperm⟩ :=
            hclear_bad (badSet X).card X rfl hXsym hXdiag hX hXuv
          rw [← hYperm]
          have hYdiag2 : ∀ i, f2_8 (Y i i) = 0 := fun i => by rcases hYdiag i with h | h <;> rw [h] <;> decide
          have hYwc : (WSet Y).card = wcard := by rw [hYW, hwc]
          let C : Finset (Fin (n' + 1)) := insert u (insert v (WSet Y))
          let Z : Finset (Fin (n' + 1)) := Cᶜ
          have hZ_zero : ∀ z ∈ Z, f2_8 (Y u z) = 0 ∧ f2_8 (Y v z) = 0 := by
            intro z hz
            have hnotC : z ∉ C := Finset.mem_compl.mp hz
            simp only [C, mem_insert, WSet, mem_filter, mem_univ, true_and, not_or] at hnotC
            have hzu : z ≠ u := hnotC.1
            have hzv : z ≠ v := hnotC.2.1
            have hnotW : ¬(f2_8 (Y u z) = 1 ∧ f2_8 (Y v z) = 1) := fun h => hnotC.2.2 ⟨hzu, hzv, h⟩
            have hnotbad : z ∉ badSet Y := by rw [hYbad]; exact Finset.notMem_empty z
            simp only [badSet, mem_filter, mem_univ, true_and] at hnotbad
            have heq : f2_8 (Y u z) = f2_8 (Y v z) := by
              by_contra hne; exact hnotbad ⟨hzu, hzv, hne⟩
            generalize f2_8 (Y u z) = a at heq hnotW ⊢
            generalize f2_8 (Y v z) = b at heq hnotW ⊢
            revert a b heq hnotW; decide
          -- Case 1: non-edge inside WSet Y
          by_cases hnonedge : ∃ w₁ ∈ WSet Y, ∃ w₂ ∈ WSet Y, w₁ ≠ w₂ ∧ f2_8 (Y w₁ w₂) = 0
          · obtain ⟨w₁, hw₁, w₂, hw₂, hne12, h012⟩ := hnonedge
            have hw₁u : w₁ ≠ u := (mem_filter.mp hw₁).2.1
            have hw₁v : w₁ ≠ v := (mem_filter.mp hw₁).2.2.1
            have hw₂u : w₂ ≠ u := (mem_filter.mp hw₂).2.1
            have hw₂v : w₂ ≠ v := (mem_filter.mp hw₂).2.2.1
            have hw₁u1 : f2_8 (Y u w₁) = 1 := (mem_filter.mp hw₁).2.2.2.1
            have hw₂u1 : f2_8 (Y u w₂) = 1 := (mem_filter.mp hw₂).2.2.2.1
            -- Shear w₁ -> w₂ (adds row/col w₁ to row/col w₂)
            have h21_0 : f2_8 (Y w₂ w₁) = 0 := by rw [hYsym.apply w₁ w₂]; exact h012
            let E : Matrix (Fin (n' + 1)) (Fin (n' + 1)) (ZMod 8) := 1 + Matrix.single w₁ w₂ 1
            let Y1 := Eᵀ * Y * E
            have hsh := perm_inv_shear_zmod8 Y hYsym hYdiag hY hne12.symm h21_0
            have hY1_entry : ∀ i j, f2_8 (Y1 i j) = f2_8 (Y i j) +
                (if i = w₂ then f2_8 (Y w₁ j) else 0) + (if j = w₂ then f2_8 (Y i w₁) else 0) := by
              intro i j
              dsimp only [Y1, E]
              rw [shear_entry_zmod8]
              simp only [map_add, apply_ite f2_8, map_zero]
              by_cases h1 : i = w₂ <;> by_cases h2 : j = w₂ <;> simp [h1, h2, hYdiag2]
            have hY1uv : f2_8 (Y1 u v) = 1 := by simp [hY1_entry, hw₂u.symm, hw₂v.symm, hYuv]
            have hY1uw2 : f2_8 (Y1 u w₂) = 0 := by
              simp [hY1_entry, hw₂u.symm, hw₂u1, hw₁u1]; decide
            have hW1_eq : WSet Y1 = (WSet Y).erase w₂ := by
              ext z; simp only [WSet, mem_filter, mem_univ, true_and, mem_erase]
              by_cases hzw : z = w₂
              · subst hzw; simp [hY1uw2]
              · simp [hzw, hY1_entry, hw₂u.symm, hw₂v.symm]
            have hcard1 : (WSet Y1).card < wcard := by
              rw [hW1_eq, ← hYwc]; exact Finset.card_erase_lt_of_mem hw₂
            rw [← hsh.2.2.2]
            exact ihw (WSet Y1).card hcard1 Y1 rfl hsh.1 hsh.2.1 hsh.2.2.1 hY1uv
          · -- Case 2: edge between WSet Y and Z
            by_cases hbridge : ∃ w ∈ WSet Y, ∃ z ∈ Z, f2_8 (Y w z) = 1
            · obtain ⟨w, hw, z, hz, hwz1⟩ := hbridge
              have hzu : z ≠ u := fun h => by
                have : u ∉ C := h ▸ Finset.mem_compl.mp hz
                exact this (mem_insert_self u _)
              have hzv : z ≠ v := fun h => by
                have : v ∉ C := h ▸ Finset.mem_compl.mp hz
                exact this (mem_insert_of_mem (mem_insert_self v _))
              have hYuz0 : f2_8 (Y u z) = 0 := (hZ_zero z hz).1
              have hYvz0 : f2_8 (Y v z) = 0 := (hZ_zero z hz).2
              -- Shear z -> u (adds row/col z to row/col u, allowed since f2_8 (Y u z) = 0)
              let E : Matrix (Fin (n' + 1)) (Fin (n' + 1)) (ZMod 8) := 1 + Matrix.single z u 1
              let Y1 := Eᵀ * Y * E
              have hsh := perm_inv_shear_zmod8 Y hYsym hYdiag hY hzu.symm hYuz0
              have hY1_entry : ∀ i j, f2_8 (Y1 i j) = f2_8 (Y i j) +
                  (if i = u then f2_8 (Y z j) else 0) + (if j = u then f2_8 (Y i z) else 0) := by
                intro i j
                dsimp only [Y1, E]
                rw [shear_entry_zmod8]
                simp only [map_add, apply_ite f2_8, map_zero]
                by_cases h1 : i = u <;> by_cases h2 : j = u <;> simp [h1, h2, hYdiag2]
              have hY1uv : f2_8 (Y1 u v) = 1 := by
                simp [hY1_entry, huv.symm, hYuv, hYsym.apply v z, hYvz0]
              have hY1v : ∀ x, x ≠ u → f2_8 (Y1 v x) = f2_8 (Y v x) := by
                intro x hxu; simp [hY1_entry, huv.symm, hxu]
              have hW1_sub : WSet Y1 ⊆ (WSet Y).erase w := by
                intro x hx
                simp only [WSet, mem_filter, mem_univ, true_and] at hx
                have hYx_v : f2_8 (Y v x) = 1 := by rw [← hY1v x hx.1]; exact hx.2.2.2
                have hxW : x ∈ WSet Y := by
                  by_contra hnotW
                  have hxC : x ∉ C := by simp [C, hx.1, hx.2.1, hnotW]
                  have hxZ : x ∈ Z := Finset.mem_compl.mpr hxC
                  have := (hZ_zero x hxZ).2
                  rw [hYx_v] at this; exact absurd this (by decide)
                refine mem_erase.mpr ⟨?_, hxW⟩
                intro hxw
                subst hxw
                have hYuw1 : f2_8 (Y u x) = 1 := (mem_filter.mp hw).2.2.2.1
                have hY1ux : f2_8 (Y1 u x) = 0 := by
                  simp [hY1_entry, hx.1, hYuw1, hYsym.apply x z, hwz1]; decide
                rw [hY1ux] at hx; exact absurd hx.2.2.1 (by decide)
              have hcard1 : (WSet Y1).card < wcard := by
                rw [← hYwc]
                exact lt_of_le_of_lt (Finset.card_le_card hW1_sub) (Finset.card_erase_lt_of_mem hw)
              rw [← hsh.2.2.2]
              exact ihw (WSet Y1).card hcard1 Y1 rfl hsh.1 hsh.2.1 hsh.2.2.1 hY1uv
            · -- Case 3: C is an isolated clique mod 2!
              push Not at hnonedge hbridge
              have hC_clique : ∀ a ∈ C, ∀ b ∈ C, a ≠ b → f2_8 (Y a b) = 1 := by
                intro a ha b hb hab
                simp only [C, mem_insert] at ha hb
                rcases ha with hau | hav | haW <;> rcases hb with hbu | hbv | hbW
                · exact (hab (hau.trans hbu.symm)).elim
                · rw [hau, hbv]; exact hYuv
                · rw [hau]; exact (mem_filter.mp hbW).2.2.2.1
                · rw [hav, hbu, hYsym.apply u v]; exact hYuv
                · exact (hab (hav.trans hbv.symm)).elim
                · rw [hav]; exact (mem_filter.mp hbW).2.2.2.2
                · rw [hbu, hYsym.apply u a]; exact (mem_filter.mp haW).2.2.2.1
                · rw [hbv, hYsym.apply v a]; exact (mem_filter.mp haW).2.2.2.2
                · have hne0 := hnonedge a haW b hbW hab
                  generalize f2_8 (Y a b) = x at hne0 ⊢
                  revert x hne0; decide
              have hCZ_zero : ∀ a ∈ C, ∀ z ∈ Z, f2_8 (Y a z) = 0 := by
                intro a ha z hz
                simp only [C, mem_insert] at ha
                rcases ha with rfl | rfl | haW
                · exact (hZ_zero z hz).1
                · exact (hZ_zero z hz).2
                · have hne1 := hbridge a haW z hz
                  generalize f2_8 (Y a z) = x at hne1 ⊢
                  revert x hne1; decide
              -- Reindex Fin (n'+1) ≃ Fin C.card ⊕ Fin Z.card
              let c := C.card
              let zc := Z.card
              have hc_ge2 : 2 ≤ c := by
                have : ({u, v} : Finset (Fin (n' + 1))) ⊆ C := by
                  intro x hx; rcases mem_insert.mp hx with rfl | hx2
                  · simp [C]
                  · rw [mem_singleton.mp hx2]; simp [C]
                calc 2 = ({u, v} : Finset (Fin (n' + 1))).card := (Finset.card_pair huv).symm
                  _ ≤ C.card := Finset.card_le_card this
              have hcz : c + zc = n' + 1 := by
                dsimp only [c, zc, Z]
                rw [Finset.card_compl, Fintype.card_fin]
                exact Nat.add_sub_of_le (by simpa using Finset.card_le_univ C)
              obtain ⟨eC⟩ := Fintype.truncEquivOfCardEq (show Fintype.card (Fin c) = Fintype.card {x // x ∈ C} by simp [c])
              obtain ⟨eZ⟩ := Fintype.truncEquivOfCardEq (show Fintype.card (Fin zc) = Fintype.card {x // x ∈ Z} by simp [zc])
              let eSum : Fin c ⊕ Fin zc ≃ Fin (n' + 1) :=
                { toFun := Sum.elim (fun a => (eC a).1) (fun b => (eZ b).1)
                  invFun := fun x => if h : x ∈ C then Sum.inl (eC.symm ⟨x, h⟩) else Sum.inr (eZ.symm ⟨x, Finset.mem_compl.mpr h⟩)
                  left_inv := fun x => by
                    rcases x with a | b
                    · simp [(eC a).2]
                    · have hnot : (eZ b).1 ∉ C := Finset.mem_compl.mp (eZ b).2
                      simp [hnot]
                  right_inv := fun x => by dsimp; split_ifs <;> simp }
              -- Build exact block-diagonal matrix B_blk on Fin (n'+1) matching Y mod 2!
              let Kc : Matrix (Fin c) (Fin c) (ZMod 8) := Matrix.of fun i j => if i = j then 0 else 1
              let YZ : Matrix (Fin zc) (Fin zc) (ZMod 8) := Matrix.of fun i j => Y (eZ i).1 (eZ j).1
              let B_blk : Matrix (Fin c ⊕ Fin zc) (Fin c ⊕ Fin zc) (ZMod 8) := Matrix.fromBlocks Kc 0 0 YZ
              let B : Matrix (Fin (n' + 1)) (Fin (n' + 1)) (ZMod 8) := B_blk.submatrix eSum.symm eSum.symm
              have hB_sym : B.IsSymm := by
                have hblk_sym : B_blk.IsSymm := by
                  ext x y; rcases x with i | i <;> rcases y with j | j
                  · simp [B_blk, Kc, eq_comm]
                  · simp [B_blk]
                  · simp [B_blk]
                  · simp [B_blk, YZ, hYsym.apply]
                ext i j; exact hblk_sym.apply (eSum.symm i) (eSum.symm j)
              have hB_diag : ∀ i, B i i = 0 ∨ B i i = 4 := by
                intro i
                dsimp only [B, Matrix.submatrix_apply]
                cases h : eSum.symm i with
                | inl a => left; simp [B_blk, Kc]
                | inr b => exact hYdiag (eZ b).1
              have hY_mod2_B : Y.map f2_8 = B.map f2_8 := by
                ext i j
                let x := eSum.symm i
                let y := eSum.symm j
                have hi : i = eSum x := (Equiv.apply_symm_apply eSum i).symm
                have hj : j = eSum y := (Equiv.apply_symm_apply eSum j).symm
                change f2_8 (Y i j) = f2_8 (B_blk x y)
                rw [hi, hj]
                rcases x with a | a <;> rcases y with b | b
                · simp only [B_blk, Matrix.fromBlocks_apply₁₁, Kc, Matrix.of_apply, eSum,
                    Equiv.coe_fn_mk, Sum.elim_inl]
                  by_cases hab : a = b
                  · subst hab; simp [hYdiag2]
                  · have hne : (eC a).1 ≠ (eC b).1 := fun h => hab (eC.injective (Subtype.ext h))
                    simp [hab, hC_clique _ (eC a).2 _ (eC b).2 hne]
                · simp only [B_blk, Matrix.fromBlocks_apply₁₂, Matrix.zero_apply, map_zero, eSum,
                    Equiv.coe_fn_mk, Sum.elim_inl, Sum.elim_inr]
                  exact hCZ_zero _ (eC a).2 _ (eZ b).2
                · simp only [B_blk, Matrix.fromBlocks_apply₂₁, Matrix.zero_apply, map_zero, eSum,
                    Equiv.coe_fn_mk, Sum.elim_inl, Sum.elim_inr]
                  rw [hYsym.apply (eC b).1 (eZ a).1]
                  exact hCZ_zero _ (eC b).2 _ (eZ a).2
                · simp [B_blk, YZ, eSum]
              have hlift := perm_inv_eq_of_cast2_eq Y B hYsym hB_sym hYdiag hB_diag hY hY_mod2_B
              rw [← hlift.2]
              have hB_blk_unit : IsUnit B_blk.det := by
                have hdet : B.det = B_blk.det := Matrix.det_submatrix_equiv_self eSum.symm B_blk
                exact hdet ▸ hlift.1
              have hdet_mul : B_blk.det = Kc.det * YZ.det := Matrix.det_fromBlocks_zero₁₂ Kc 0 YZ
              have hKc_unit : IsUnit Kc.det := isUnit_of_mul_isUnit_left (hdet_mul ▸ hB_blk_unit)
              have hYZ_unit : IsUnit YZ.det := isUnit_of_mul_isUnit_right (hdet_mul ▸ hB_blk_unit)
              have hKc_sym : Kc.IsSymm := by ext a b; simp [Kc, eq_comm]
              have hKc_diag2 : ∀ i, f2_8 (Kc i i) = 0 := fun i => by simp [Kc]
              have hc_even : Even c := even_of_isUnit_det_symm_diag2_zmod8 Kc hKc_sym hKc_diag2 hKc_unit
              obtain ⟨m, hm⟩ := hc_even
              have hm1 : 1 ≤ m := by omega
              have hcm : c = 2 * m := by omega
              have hKc_perm : (Kc⁻¹).permanent = 1 := by
                let eM : Fin c ≃ Fin (2 * m) := finCongr hcm
                let Km : Matrix (Fin (2 * m)) (Fin (2 * m)) (ZMod 8) :=
                  Matrix.of fun i j => if i = j then 0 else 1
                have hK_eq : Kc = Km.submatrix eM eM := by ext i j; simp [Kc, Km, eM]
                have hKm := perm_inv_clique_zmod8 m hm1
                have hinv_eq : Kc⁻¹ = (Km⁻¹).submatrix eM eM := by
                  have hmul : Kc * (Km⁻¹).submatrix eM eM = 1 := by
                    rw [hK_eq]; ext i j
                    simp only [Matrix.mul_apply, Matrix.submatrix_apply, Matrix.one_apply]
                    rw [Fintype.sum_equiv eM
                      (fun k => Km (eM i) (eM k) * Km⁻¹ (eM k) (eM j))
                      (fun k => Km (eM i) k * Km⁻¹ k (eM j)) (fun _ => rfl)]
                    have := congrFun (congrFun (Matrix.mul_nonsing_inv Km hKm.1) (eM i)) (eM j)
                    simpa [Matrix.mul_apply, Matrix.one_apply] using this
                  have h1 := congrArg (fun X => Kc⁻¹ * X) hmul
                  rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul Kc hKc_unit, Matrix.one_mul,
                    Matrix.mul_one] at h1
                  exact h1.symm
                rw [hinv_eq]
                unfold Matrix.permanent
                refine (Fintype.sum_equiv (Equiv.permCongr eM) _ _ fun σ => ?_).trans hKm.2
                refine Fintype.prod_equiv eM _ _ fun i => ?_
                simp [Km]
              have hYZ_perm : (YZ⁻¹).permanent = 1 := by
                have hzc_lt : zc < n' + 1 := by omega
                exact ih zc hzc_lt YZ (by ext a b; simp [YZ, hYsym.apply])
                  (fun a => hYdiag (eZ a).1) hYZ_unit
              have hB_blk_inv : B_blk⁻¹ = Matrix.fromBlocks Kc⁻¹ 0 0 YZ⁻¹ := by
                have hmul : B_blk * Matrix.fromBlocks Kc⁻¹ 0 0 YZ⁻¹ = 1 := by
                  dsimp only [B_blk]
                  rw [Matrix.fromBlocks_multiply]
                  simp [Matrix.mul_nonsing_inv Kc hKc_unit, Matrix.mul_nonsing_inv YZ hYZ_unit,
                    Matrix.fromBlocks_one]
                have h1 := congrArg (fun X => B_blk⁻¹ * X) hmul
                rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul B_blk hB_blk_unit, Matrix.one_mul,
                  Matrix.mul_one] at h1
                exact h1.symm
              have hB_inv : B⁻¹ = (B_blk⁻¹).submatrix eSum.symm eSum.symm := by
                have hmul : B * (B_blk⁻¹).submatrix eSum.symm eSum.symm = 1 := by
                  ext i j
                  simp only [B, Matrix.mul_apply, Matrix.submatrix_apply, Matrix.one_apply]
                  rw [Fintype.sum_equiv eSum.symm
                    (fun k => B_blk (eSum.symm i) (eSum.symm k) * B_blk⁻¹ (eSum.symm k) (eSum.symm j))
                    (fun k => B_blk (eSum.symm i) k * B_blk⁻¹ k (eSum.symm j)) (fun _ => rfl)]
                  have := congrFun (congrFun (Matrix.mul_nonsing_inv B_blk hB_blk_unit) (eSum.symm i)) (eSum.symm j)
                  simpa [Matrix.mul_apply, Matrix.one_apply] using this
                have h1 := congrArg (fun X => B⁻¹ * X) hmul
                rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul B hlift.1, Matrix.one_mul, Matrix.mul_one] at h1
                exact h1.symm
              have hperm_reidx : ((B_blk⁻¹).submatrix eSum.symm eSum.symm).permanent = (B_blk⁻¹).permanent := by
                unfold Matrix.permanent
                let φ : Equiv.Perm (Fin (n' + 1)) ≃ Equiv.Perm (Fin c ⊕ Fin zc) :=
                  Equiv.permCongr eSum.symm
                refine Fintype.sum_equiv φ _ _ fun σ => ?_
                refine Fintype.prod_equiv eSum.symm _ _ fun i => ?_
                simp [φ]
              rw [hB_inv, hperm_reidx, hB_blk_inv, perm_fromBlocks_zero, hKc_perm, hYZ_perm, mul_one]
      exact hW_ind (WSet A).card A rfl hSym hDiag hA huv1

end OMA.MO513259

theorem OMA.solution : type_of% @OMA.S_mo_513259.main := by
  constructor
  · intro n A hG hA
    exact OMA.MO513259.perm_inv_zmod8_of_symm_diag4 n A hG.1 (fun i => Or.inl (hG.2.1 i)) hA
  · intro n A hG hA
    apply OMA.MO513259.eq_zero_zmod24_of_casts
    · let f8 : ZMod 24 →+* ZMod 8 := ZMod.castHom (by norm_num : 8 ∣ 24) (ZMod 8)
      let f4 : ZMod 8 →+* ZMod 4 := ZMod.castHom (by norm_num : 4 ∣ 8) (ZMod 4)
      let A8 : Matrix (Fin n) (Fin n) (ZMod 8) := A.map f8
      have hA8_unit : IsUnit A8.det := by
        rw [OMA.MO513259.det_map]; exact hA.map f8
      have hA8_sym : A8.IsSymm := by ext i j; simp [A8, hG.1.apply i j]
      have hA8_diag : ∀ i, A8 i i = 0 ∨ A8 i i = 4 := fun i => Or.inl (by simp [A8, hG.2.1 i])
      have hinv8 : (A8⁻¹).permanent = 1 :=
        OMA.MO513259.perm_inv_zmod8_of_symm_diag4 n A8 hA8_sym hA8_diag hA8_unit
      let A4 : Matrix (Fin n) (Fin n) (ZMod 4) := A8.map f4
      have hA4_unit : IsUnit A4.det := by
        rw [OMA.MO513259.det_map]; exact hA8_unit.map f4
      have hA4_sym : A4.IsSymm := by ext i j; simp [A4, hA8_sym.apply i j]
      have hA4_diag : ∀ i, A4 i i = 0 ∨ A4 i i = 2 := fun i => Or.inl (by simp [A4, A8, hG.2.1 i])
      have hperm4 : A4.permanent = 1 :=
        OMA.MO513259.perm_symm_eq_one_zmod4 A4 hA4_sym hA4_diag hA4_unit
      have h2perm8 : (2 : ZMod 8) * A8.permanent = 2 := by
        have hcast4 : f4 A8.permanent = 1 := by
          rw [← OMA.MO513259.permanent_map f4 A8]; exact hperm4
        have hlem : ∀ x : ZMod 8, f4 x = 1 → (2 : ZMod 8) * x = 2 := by decide
        exact hlem A8.permanent hcast4
      simp only [map_sub, map_add, map_mul, map_ofNat]
      rw [← OMA.MO513259.permanent_map f8 A, ← OMA.MO513259.permanent_map f8 A⁻¹,
        ← OMA.MO513259.inv_map_of_isUnit f8 A hA]
      change (2 : ZMod 8) * A8.permanent + (A8⁻¹).permanent - 3 = 0
      rw [h2perm8, hinv8]
      decide
    · let f3 : ZMod 24 →+* ZMod 3 := ZMod.castHom (by norm_num : 3 ∣ 24) (ZMod 3)
      let A3 : Matrix (Fin n) (Fin n) (ZMod 3) := A.map f3
      have hA3_unit : IsUnit A3.det := by
        rw [OMA.MO513259.det_map]; exact hA.map f3
      have hinv3 : (A3⁻¹).permanent = A3.permanent :=
        OMA.MO513259.perm_inv_eq_perm_zmod3 A3 hA3_unit
      simp only [map_sub, map_add, map_mul, map_ofNat]
      rw [← OMA.MO513259.permanent_map f3 A, ← OMA.MO513259.permanent_map f3 A⁻¹,
        ← OMA.MO513259.inv_map_of_isUnit f3 A hA]
      change (2 : ZMod 3) * A3.permanent + (A3⁻¹).permanent - 3 = 0
      rw [hinv3]
      have h3 : (2 : ZMod 3) * A3.permanent + A3.permanent = 3 * A3.permanent := by ring
      rw [h3]
      have h30 : (3 : ZMod 3) = 0 := rfl
      rw [h30, zero_mul, sub_zero]

