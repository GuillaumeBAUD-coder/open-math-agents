import OMAStatements.S_arxiv_2602_07467

open Polynomial Matrix
open OMA.S_arxiv_2602_07467

namespace OMA.P_arxiv_2602_07467

private abbrev M3 (p : ℕ) := Matrix (Fin 3) (Fin 3) (ZMod p)
private abbrev V3 (p : ℕ) := Fin 3 → ZMod p

private instance instFiniteUCCGVert (p : ℕ) [Fact p.Prime] : Finite (UCCGVert p) :=
  Finite.of_injective (fun v : UCCGVert p => (v.val : Set (M3 p)))
    (fun _ _ h => Subtype.ext (SetLike.coe_injective h))

private lemma subring_map_closure {R S : Type*} [Ring R] [Ring S] (f : R →+* S) (s : Set R) :
    (Subring.closure s).map f = Subring.closure (f '' s) := by
  apply le_antisymm
  · rw [Subring.map_le_iff_le_comap]
    exact Subring.closure_le.mpr (fun x hx => Subring.subset_closure ⟨x, hx, rfl⟩)
  · exact Subring.closure_le.mpr (by rintro _ ⟨x, hx, rfl⟩; exact ⟨x, Subring.subset_closure hx, rfl⟩)

private lemma pow_eq_zero {R : Type*} [MonoidWithZero R] [NoZeroDivisors R] {a : R} {n : ℕ}
    (h : a ^ n = 0) : a = 0 := eq_zero_of_pow_eq_zero h

private lemma not_irreducible_mul {R : Type*} [Monoid R] {a b : R} (ha : ¬ IsUnit a) (hb : ¬ IsUnit b) :
    ¬ Irreducible (a * b) := fun h => (h.isUnit_or_isUnit rfl).elim ha hb

private lemma isIntegral_m3 {p : ℕ} [Fact p.Prime] (A : M3 p) : IsIntegral (ZMod p) A :=
  ⟨A.charpoly, Matrix.charpoly_monic A, Matrix.aeval_self_charpoly A⟩

private lemma finrank_span_singleton_le {p : ℕ} [Fact p.Prime] (v : V3 p) :
    Module.finrank (ZMod p) (Submodule.span (ZMod p) ({v} : Set (V3 p))) ≤ 1 := by
  by_cases hv : v = 0
  · subst hv; rw [Submodule.span_zero_singleton, finrank_bot]; exact Nat.zero_le 1
  · rw [finrank_span_singleton hv]

private lemma commute_aeval_self {p : ℕ} [Fact p.Prime] (A : M3 p) (f : (ZMod p)[X]) :
    Commute (aeval A f) A := by
  induction f using Polynomial.induction_on' with
  | add g h hg hh => rw [map_add]; exact hg.add_left hh
  | monomial n r =>
    rw [aeval_monomial, Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul]
    exact (Commute.pow_left (Commute.refl A) n).smul_left r

private lemma card_adjoin_of_deg2 {p : ℕ} [Fact p.Prime] (A : M3 p) (a0 a1 : ZMod p)
    (hA2 : A * A = a1 • A + a0 • (1 : M3 p))
    (hinj : ∀ r0 r1 : ZMod p, r0 • (1 : M3 p) + r1 • A = 0 → r0 = 0 ∧ r1 = 0) :
    Nat.card (Algebra.adjoin (ZMod p) ({A} : Set (M3 p))) = p ^ 2 := by
  classical
  have hmem : ∀ x : M3 p, x ∈ Algebra.adjoin (ZMod p) ({A} : Set (M3 p)) ↔
      ∃ r0 r1 : ZMod p, x = r0 • (1 : M3 p) + r1 • A := by
    intro x; constructor
    · intro hx; induction hx using Algebra.adjoin_induction with
      | mem y hy => rw [Set.mem_singleton_iff.mp hy]; exact ⟨0, 1, by simp⟩
      | algebraMap r => exact ⟨r, 0, by simp [Algebra.algebraMap_eq_smul_one]⟩
      | add _ _ _ _ h1 h2 =>
        rcases h1 with ⟨r0, r1, rfl⟩; rcases h2 with ⟨s0, s1, rfl⟩
        exact ⟨r0 + s0, r1 + s1, by simp only [add_smul]; abel⟩
      | mul _ _ _ _ h1 h2 =>
        rcases h1 with ⟨r0, r1, rfl⟩; rcases h2 with ⟨s0, s1, rfl⟩
        refine ⟨r0 * s0 + r1 * s1 * a0, r0 * s1 + r1 * s0 + r1 * s1 * a1, ?_⟩
        rw [add_mul, mul_add, mul_add, smul_mul_assoc, mul_smul_comm, smul_mul_assoc, mul_smul_comm,
            smul_mul_assoc, mul_smul_comm, smul_mul_assoc, mul_smul_comm]
        simp only [one_mul, mul_one, hA2, smul_add]
        ext i j; simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]; ring
    · rintro ⟨r0, r1, rfl⟩
      have h0 : r0 • (1 : M3 p) ∈ Algebra.adjoin (ZMod p) ({A} : Set (M3 p)) := by
        rw [← Algebra.algebraMap_eq_smul_one]; exact algebraMap_mem _ r0
      have h1 : r1 • A ∈ Algebra.adjoin (ZMod p) ({A} : Set (M3 p)) := by
        rw [Algebra.smul_def]; exact mul_mem (algebraMap_mem _ r1) (Algebra.subset_adjoin rfl)
      exact add_mem h0 h1
  have e : ZMod p × ZMod p ≃ Algebra.adjoin (ZMod p) ({A} : Set (M3 p)) :=
    Equiv.ofBijective (fun r => ⟨r.1 • (1 : M3 p) + r.2 • A, (hmem _).mpr ⟨r.1, r.2, rfl⟩⟩)
      ⟨fun r s h => by
        have hv := sub_eq_zero.mpr (congrArg Subtype.val h)
        dsimp only at hv
        have h0 : (r.1 - s.1) • (1 : M3 p) + (r.2 - s.2) • A = 0 := by simp only [sub_smul]; rw [← hv]; abel
        obtain ⟨h1, h2⟩ := hinj _ _ h0
        exact Prod.ext (sub_eq_zero.mp h1) (sub_eq_zero.mp h2),
       fun x => by obtain ⟨r0, r1, hr⟩ := (hmem x.val).mp x.prop; exact ⟨(r0, r1), Subtype.ext hr.symm⟩⟩
  rw [Nat.card_eq_fintype_card, ← Fintype.card_congr e, Fintype.card_prod, ZMod.card, sq]

private lemma card_adjoin_of_deg3 {p : ℕ} [Fact p.Prime] (A : M3 p) (a0 a1 a2 : ZMod p)
    (hA3 : A * (A * A) = a2 • (A * A) + a1 • A + a0 • (1 : M3 p))
    (hinj : ∀ r0 r1 r2 : ZMod p, r0 • (1 : M3 p) + r1 • A + r2 • (A * A) = 0 → r0 = 0 ∧ r1 = 0 ∧ r2 = 0) :
    Nat.card (Algebra.adjoin (ZMod p) ({A} : Set (M3 p))) = p ^ 3 := by
  classical
  have hA4 : (A * A) * (A * A) = (a2 * a2 + a1) • (A * A) + (a2 * a1 + a0) • A + (a2 * a0) • (1 : M3 p) := by
    calc (A * A) * (A * A) = A * (A * (A * A)) := by rw [mul_assoc]
      _ = A * (a2 • (A * A) + a1 • A + a0 • (1 : M3 p)) := by rw [hA3]
      _ = a2 • (A * (A * A)) + a1 • (A * A) + a0 • A := by simp only [mul_add, mul_smul_comm, mul_one]
      _ = a2 • (a2 • (A * A) + a1 • A + a0 • (1 : M3 p)) + a1 • (A * A) + a0 • A := by rw [hA3]
      _ = (a2 * a2 + a1) • (A * A) + (a2 * a1 + a0) • A + (a2 * a0) • (1 : M3 p) := by
          simp only [smul_add, smul_smul, add_smul]; abel
  have hA3' : (A * A) * A = a2 • (A * A) + a1 • A + a0 • (1 : M3 p) := by rw [mul_assoc, hA3]
  have hmem : ∀ x : M3 p, x ∈ Algebra.adjoin (ZMod p) ({A} : Set (M3 p)) ↔
      ∃ r0 r1 r2 : ZMod p, x = r0 • (1 : M3 p) + r1 • A + r2 • (A * A) := by
    intro x; constructor
    · intro hx; induction hx using Algebra.adjoin_induction with
      | mem y hy => rw [Set.mem_singleton_iff.mp hy]; exact ⟨0, 1, 0, by simp⟩
      | algebraMap r => exact ⟨r, 0, 0, by simp [Algebra.algebraMap_eq_smul_one]⟩
      | add _ _ _ _ h1 h2 =>
        rcases h1 with ⟨r0, r1, r2, rfl⟩; rcases h2 with ⟨s0, s1, s2, rfl⟩
        exact ⟨r0 + s0, r1 + s1, r2 + s2, by simp only [add_smul]; abel⟩
      | mul _ _ _ _ h1 h2 =>
        rcases h1 with ⟨r0, r1, r2, rfl⟩; rcases h2 with ⟨s0, s1, s2, rfl⟩
        refine ⟨r0 * s0 + (r1 * s2 + r2 * s1) * a0 + r2 * s2 * (a2 * a0),
                r0 * s1 + r1 * s0 + (r1 * s2 + r2 * s1) * a1 + r2 * s2 * (a2 * a1 + a0),
                r0 * s2 + r1 * s1 + r2 * s0 + (r1 * s2 + r2 * s1) * a2 + r2 * s2 * (a2 * a2 + a1), ?_⟩
        simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, one_mul, mul_one, hA3, hA3', hA4, smul_add]
        ext i j; simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]; ring
    · rintro ⟨r0, r1, r2, rfl⟩
      have hA_in : A ∈ Algebra.adjoin (ZMod p) ({A} : Set (M3 p)) := Algebra.subset_adjoin rfl
      exact add_mem (add_mem (Subalgebra.smul_mem _ (one_mem _) r0) (Subalgebra.smul_mem _ hA_in r1))
        (Subalgebra.smul_mem _ (mul_mem hA_in hA_in) r2)
  have e : ZMod p × ZMod p × ZMod p ≃ Algebra.adjoin (ZMod p) ({A} : Set (M3 p)) :=
    Equiv.ofBijective (fun r => ⟨r.1 • (1 : M3 p) + r.2.1 • A + r.2.2 • (A * A), (hmem _).mpr ⟨r.1, r.2.1, r.2.2, rfl⟩⟩)
      ⟨fun r s h => by
        have hv := sub_eq_zero.mpr (congrArg Subtype.val h)
        dsimp only at hv
        have h0 : (r.1 - s.1) • (1 : M3 p) + (r.2.1 - s.2.1) • A + (r.2.2 - s.2.2) • (A * A) = 0 := by
          simp only [sub_smul]; rw [← hv]; abel
        obtain ⟨h1, h2, h3⟩ := hinj _ _ _ h0
        exact Prod.ext (sub_eq_zero.mp h1) (Prod.ext (sub_eq_zero.mp h2) (sub_eq_zero.mp h3)),
       fun x => by obtain ⟨r0, r1, r2, hr⟩ := (hmem x.val).mp x.prop; exact ⟨(r0, r1, r2), Subtype.ext hr.symm⟩⟩
  rw [Nat.card_eq_fintype_card, ← Fintype.card_congr e, Fintype.card_prod, Fintype.card_prod, ZMod.card]; ring

private lemma finrank_adjoin_singleton_m3 {p : ℕ} [Fact p.Prime] (A : M3 p) :
    Module.finrank (ZMod p) (Algebra.adjoin (ZMod p) ({A} : Set (M3 p))) =
      (minpoly (ZMod p) A).natDegree := by
  classical
  have hint : IsIntegral (ZMod p) A := isIntegral_m3 A
  have hm_mon : (minpoly (ZMod p) A).Monic := minpoly.monic hint
  have hpos : 1 ≤ (minpoly (ZMod p) A).natDegree := minpoly.natDegree_pos hint
  have hle3 : (minpoly (ZMod p) A).natDegree ≤ 3 := by
    have hdvd := minpoly.dvd (ZMod p) A (Matrix.aeval_self_charpoly A)
    have h := Polynomial.natDegree_le_of_dvd hdvd (Matrix.charpoly_monic A).ne_zero
    rwa [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin] at h
  have hcard_eq : ∀ d : ℕ, Nat.card (Algebra.adjoin (ZMod p) ({A} : Set (M3 p))) = p ^ d →
      Module.finrank (ZMod p) (Algebra.adjoin (ZMod p) ({A} : Set (M3 p))) = d := fun d hcard => by
    have hcard2 : Nat.card (Algebra.adjoin (ZMod p) ({A} : Set (M3 p))) =
        p ^ Module.finrank (ZMod p) (Algebra.adjoin (ZMod p) ({A} : Set (M3 p))) := by
      rw [Nat.card_eq_fintype_card, Module.card_eq_pow_finrank (K := ZMod p), ZMod.card]
    exact Nat.pow_right_injective (Fact.out : p.Prime).two_le (hcard2.symm.trans hcard)
  have hdeg_eval : ∀ (f : (ZMod p)[X]), f ≠ 0 → f.natDegree < (minpoly (ZMod p) A).natDegree → aeval A f ≠ 0 :=
    fun f hf hlt h0 => by
      have := Polynomial.natDegree_le_of_dvd (minpoly.dvd (ZMod p) A h0) hf; omega
  interval_cases hd : (minpoly (ZMod p) A).natDegree
  · -- d = 1: `A = c • 1`
    have hm1 : minpoly (ZMod p) A = X - C (-(minpoly (ZMod p) A).coeff 0) := by
      ext k
      by_cases hk : k ≤ 1
      · interval_cases k
        · simp [Polynomial.coeff_X, Polynomial.coeff_C]
        · simpa [Polynomial.Monic, Polynomial.leadingCoeff, hd] using hm_mon
      · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)]
        simp [Polynomial.coeff_X, Polynomial.coeff_C, show 1 ≠ k by omega, show k ≠ 0 by omega]
    set c := -(minpoly (ZMod p) A).coeff 0
    have hA1 : A = c • (1 : M3 p) := by
      have h0 := minpoly.aeval (ZMod p) A
      rw [hm1, map_sub, aeval_X, aeval_C, Algebra.algebraMap_eq_smul_one, sub_eq_zero] at h0; exact h0
    have hmem : ∀ x : M3 p, x ∈ Algebra.adjoin (ZMod p) ({A} : Set (M3 p)) ↔ ∃ r : ZMod p, x = r • (1 : M3 p) := by
      intro x; constructor
      · intro hx; induction hx using Algebra.adjoin_induction with
        | mem y hy => rw [Set.mem_singleton_iff.mp hy]; exact ⟨c, hA1⟩
        | algebraMap r => exact ⟨r, Algebra.algebraMap_eq_smul_one r⟩
        | add _ _ _ _ h1 h2 => rcases h1 with ⟨r1, rfl⟩; rcases h2 with ⟨r2, rfl⟩; exact ⟨r1 + r2, by rw [add_smul]⟩
        | mul _ _ _ _ h1 h2 => rcases h1 with ⟨r1, rfl⟩; rcases h2 with ⟨r2, rfl⟩; exact ⟨r1 * r2, by rw [smul_mul_smul_comm, mul_one]⟩
      · rintro ⟨r, rfl⟩; exact Subalgebra.smul_mem _ (one_mem _) r
    refine hcard_eq 1 ?_
    have e : ZMod p ≃ Algebra.adjoin (ZMod p) ({A} : Set (M3 p)) :=
      Equiv.ofBijective (fun r => ⟨r • (1 : M3 p), (hmem _).mpr ⟨r, rfl⟩⟩)
        ⟨fun r1 r2 h => by simpa using congrArg (fun z => z.val 0 0) h,
         fun x => by obtain ⟨r, hr⟩ := (hmem x.val).mp x.prop; exact ⟨r, Subtype.ext hr.symm⟩⟩
    rw [Nat.card_eq_fintype_card, ← Fintype.card_congr e, ZMod.card, pow_one]
  · -- d = 2: `A^2 = a1 • A + a0 • 1`
    let a1 : ZMod p := -(minpoly (ZMod p) A).coeff 1
    let a0 : ZMod p := -(minpoly (ZMod p) A).coeff 0
    have hA2 : A * A = a1 • A + a0 • (1 : M3 p) := by
      have hm2 : minpoly (ZMod p) A = X ^ 2 + C (-a1) * X + C (-a0) := by
        ext k
        by_cases hk : k ≤ 2
        · interval_cases k
          · simp [a0, Polynomial.coeff_C, Polynomial.coeff_X_pow]
          · simp [a1, Polynomial.coeff_C, Polynomial.coeff_X_pow]
          · simpa [Polynomial.Monic, Polynomial.leadingCoeff, hd] using hm_mon
        · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)]
          simp [Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_C,
                show k ≠ 2 by omega, show 1 ≠ k by omega, show k ≠ 0 by omega]
      have h0 := minpoly.aeval (ZMod p) A
      rw [hm2] at h0
      simp only [map_add, map_mul, aeval_X, aeval_C, Algebra.algebraMap_eq_smul_one,
        neg_smul, neg_mul, smul_mul_assoc, one_mul, sq] at h0
      exact eq_of_sub_eq_zero (by rw [← h0]; abel)
    have hinj : ∀ r0 r1 : ZMod p, r0 • (1 : M3 p) + r1 • A = 0 → r0 = 0 ∧ r1 = 0 := by
      intro r0 r1 h0
      let f : (ZMod p)[X] := C r1 * X + C r0
      have hfa : aeval A f = 0 := by
        simp only [f, map_add, map_mul, aeval_C, aeval_X, Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul]
        rw [add_comm]; exact h0
      have hf0 : f = 0 := by
        by_contra hne
        have hlt : f.natDegree < 2 := by
          refine lt_of_le_of_lt (Polynomial.natDegree_add_le _ _) (max_lt ?_ ?_)
          · refine lt_of_le_of_lt Polynomial.natDegree_mul_le ?_; simp
          · simp
        exact hdeg_eval f hne (hd ▸ hlt) hfa
      have hc0 := congrArg (fun g : (ZMod p)[X] => g.coeff 0) hf0
      have hc1 := congrArg (fun g : (ZMod p)[X] => g.coeff 1) hf0
      simp [f, Polynomial.coeff_X, Polynomial.coeff_C] at hc0 hc1
      exact ⟨hc0, hc1⟩
    exact hcard_eq 2 (card_adjoin_of_deg2 A a0 a1 hA2 hinj)
  · -- d = 3: `A^3 = a2 • A^2 + a1 • A + a0 • 1`
    let a2 : ZMod p := -(minpoly (ZMod p) A).coeff 2
    let a1 : ZMod p := -(minpoly (ZMod p) A).coeff 1
    let a0 : ZMod p := -(minpoly (ZMod p) A).coeff 0
    have hA3 : A * (A * A) = a2 • (A * A) + a1 • A + a0 • (1 : M3 p) := by
      have hm3 : minpoly (ZMod p) A = X ^ 3 + C (-a2) * X ^ 2 + C (-a1) * X + C (-a0) := by
        ext k
        by_cases hk : k ≤ 3
        · interval_cases k
          · simp [a0, Polynomial.coeff_C, Polynomial.coeff_X_pow]
          · simp [a1, Polynomial.coeff_C, Polynomial.coeff_X_pow]
          · simp [a2, Polynomial.coeff_X_pow]
          · simpa [Polynomial.Monic, Polynomial.leadingCoeff, hd] using hm_mon
        · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)]
          simp [Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_C,
                show k ≠ 3 by omega, show k ≠ 2 by omega, show 1 ≠ k by omega, show k ≠ 0 by omega]
      have h0 := minpoly.aeval (ZMod p) A
      rw [hm3] at h0
      simp only [map_add, map_mul, map_pow, aeval_X, aeval_C, Algebra.algebraMap_eq_smul_one,
        neg_smul, neg_mul, smul_mul_assoc, one_mul,
        show A ^ 3 = A * (A * A) by rw [pow_succ, sq, mul_assoc], sq] at h0
      exact eq_of_sub_eq_zero (by rw [← h0]; abel)
    have hinj : ∀ r0 r1 r2 : ZMod p, r0 • (1 : M3 p) + r1 • A + r2 • (A * A) = 0 → r0 = 0 ∧ r1 = 0 ∧ r2 = 0 := by
      intro r0 r1 r2 h0
      let f : (ZMod p)[X] := C r2 * X ^ 2 + C r1 * X + C r0
      have hfa : aeval A f = 0 := by
        simp only [f, map_add, map_mul, aeval_C, aeval_X, Algebra.algebraMap_eq_smul_one,
          smul_mul_assoc, one_mul, sq]
        rw [← h0]; abel
      have hf0 : f = 0 := by
        by_contra hne
        have hlt : f.natDegree < 3 := by
          refine lt_of_le_of_lt (Polynomial.natDegree_add_le _ _) (max_lt ?_ (by simp))
          refine lt_of_le_of_lt (Polynomial.natDegree_add_le _ _) (max_lt ?_ ?_)
          · refine lt_of_le_of_lt Polynomial.natDegree_mul_le ?_; simp
          · refine lt_of_le_of_lt Polynomial.natDegree_mul_le ?_; simp
        exact hdeg_eval f hne (hd ▸ hlt) hfa
      have hc0 := congrArg (fun g : (ZMod p)[X] => g.coeff 0) hf0
      have hc1 := congrArg (fun g : (ZMod p)[X] => g.coeff 1) hf0
      have hc2 := congrArg (fun g : (ZMod p)[X] => g.coeff 2) hf0
      simp [f, Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_C] at hc0 hc1 hc2
      exact ⟨hc0, hc1, hc2⟩
    exact hcard_eq 3 (card_adjoin_of_deg3 A a0 a1 a2 hA3 hinj)

/-! ### Section 1: Subrings, Polynomials, and Conjugation in `M_3(ZMod p)` -/

private lemma subring_closure_eq_adjoin {p : ℕ} [Fact p.Prime] (A : M3 p) :
    Subring.closure ({A} : Set (M3 p)) = (Algebra.adjoin (ZMod p) ({A} : Set (M3 p))).toSubring := by
  apply le_antisymm
  · exact Subring.closure_le.mpr (Set.singleton_subset_iff.mpr (Algebra.subset_adjoin rfl))
  · intro B hB
    induction hB using Algebra.adjoin_induction with
    | mem x hx => exact Subring.subset_closure hx
    | algebraMap r =>
      have hr : algebraMap (ZMod p) (M3 p) r = ((r.val : ℕ) : M3 p) := by
        conv_lhs => rw [← ZMod.natCast_zmod_val r]
        rw [map_natCast]
      rw [hr]
      exact natCast_mem _ _
    | add x y _ _ hx hy => exact add_mem hx hy
    | mul x y _ _ hx hy => exact mul_mem hx hy

private lemma mem_subring_closure_iff_aeval {p : ℕ} [Fact p.Prime] (A B : M3 p) :
    B ∈ Subring.closure ({A} : Set (M3 p)) ↔ ∃ f : (ZMod p)[X], aeval A f = B := by
  rw [subring_closure_eq_adjoin A]
  change B ∈ Algebra.adjoin (ZMod p) ({A} : Set (M3 p)) ↔ _
  rw [Algebra.adjoin_singleton_eq_range_aeval]
  rfl

private lemma aeval_mem_subring_closure {p : ℕ} [Fact p.Prime] (A : M3 p) (f : (ZMod p)[X]) :
    aeval A f ∈ Subring.closure ({A} : Set (M3 p)) :=
  (mem_subring_closure_iff_aeval A _).mpr ⟨f, rfl⟩

private lemma smul_one_mem_subring {p : ℕ} [Fact p.Prime] (S : Subring (M3 p)) (c : ZMod p) :
    c • (1 : M3 p) ∈ S := by
  have hc : c • (1 : M3 p) = (c.val : M3 p) := by
    conv_lhs => rw [← ZMod.natCast_zmod_val c]
    rw [Nat.cast_smul_eq_nsmul, nsmul_eq_mul, mul_one]
  rw [hc]
  exact natCast_mem S c.val

private lemma smul_mem_subring {p : ℕ} [Fact p.Prime] (S : Subring (M3 p)) (c : ZMod p)
    {A : M3 p} (hA : A ∈ S) : c • A ∈ S := by
  have : c • A = (c • (1 : M3 p)) * A := by simp
  rw [this]
  exact mul_mem (smul_one_mem_subring S c) hA

private lemma uccgAdj_iff_comm {p : ℕ} [Fact p.Prime] {v₁ v₂ : UCCGVert p}
    {A₁ A₂ : M3 p} (h₁ : A₁ ∈ SingleGens v₁) (h₂ : A₂ ∈ SingleGens v₂) :
    UCCGAdj v₁ v₂ ↔ A₁ * A₂ = A₂ * A₁ := by
  constructor
  · intro hadj
    exact hadj A₁ (h₁ ▸ Subring.subset_closure rfl) A₂ (h₂ ▸ Subring.subset_closure rfl)
  · intro hcomm X hX Y hY
    rw [← h₁] at hX; rw [← h₂] at hY
    obtain ⟨f, rfl⟩ := (mem_subring_closure_iff_aeval A₁ X).mp hX
    obtain ⟨g, rfl⟩ := (mem_subring_closure_iff_aeval A₂ Y).mp hY
    have hcomm' : Commute A₁ A₂ := hcomm
    have h1 : ∀ h : (ZMod p)[X], Commute (aeval A₁ h) A₂ := fun h => by
      induction h using Polynomial.induction_on' with
      | add p1 p2 hp1 hp2 => rw [map_add]; exact hp1.add_left hp2
      | monomial n c =>
        rw [aeval_monomial, Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul]
        exact (hcomm'.pow_left n).smul_left c
    have h2 : Commute (aeval A₁ f) A₂ := h1 f
    have h3 : ∀ k : (ZMod p)[X], Commute (aeval A₁ f) (aeval A₂ k) := fun k => by
      induction k using Polynomial.induction_on' with
      | add p1 p2 hp1 hp2 => rw [map_add]; exact hp1.add_right hp2
      | monomial n c =>
        rw [aeval_monomial, Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul]
        exact (h2.pow_right n).smul_right c
    exact h3 g

private def conjAlgEquiv {p : ℕ} [Fact p.Prime] (S : GL (Fin 3) (ZMod p)) :
    M3 p ≃ₐ[ZMod p] M3 p where
  toFun A := S.val * A * (↑S⁻¹ : M3 p)
  invFun A := (↑S⁻¹ : M3 p) * A * S.val
  left_inv A := by
    calc (↑S⁻¹ : M3 p) * (S.val * A * (↑S⁻¹ : M3 p)) * S.val
        = ((↑S⁻¹ : M3 p) * S.val) * A * ((↑S⁻¹ : M3 p) * S.val) := by simp only [mul_assoc]
      _ = A := by rw [Units.inv_mul, one_mul, mul_one]
  right_inv A := by
    calc S.val * ((↑S⁻¹ : M3 p) * A * S.val) * (↑S⁻¹ : M3 p)
        = (S.val * (↑S⁻¹ : M3 p)) * A * (S.val * (↑S⁻¹ : M3 p)) := by simp only [mul_assoc]
      _ = A := by rw [Units.mul_inv, one_mul, mul_one]
  map_mul' A B := by
    calc S.val * (A * B) * (↑S⁻¹ : M3 p)
        = S.val * A * (1 * B) * (↑S⁻¹ : M3 p) := by simp only [one_mul, mul_assoc]
      _ = S.val * A * (((↑S⁻¹ : M3 p) * S.val) * B) * (↑S⁻¹ : M3 p) := by rw [Units.inv_mul]
      _ = (S.val * A * (↑S⁻¹ : M3 p)) * (S.val * B * (↑S⁻¹ : M3 p)) := by simp only [mul_assoc]
  map_add' A B := by rw [mul_add, add_mul]
  commutes' c := by
    simp only [Algebra.algebraMap_eq_smul_one, mul_smul_comm, smul_mul_assoc, mul_one, Units.mul_inv]

private lemma charpoly_conj {p : ℕ} [Fact p.Prime] (S : GL (Fin 3) (ZMod p)) (A : M3 p) :
    (conjAlgEquiv S A).charpoly = A.charpoly := by
  change (S.val * A * (↑S⁻¹ : M3 p)).charpoly = A.charpoly
  rw [Matrix.charpoly_mul_comm, ← mul_assoc, Units.inv_mul, one_mul]

private lemma minpoly_conj {p : ℕ} [Fact p.Prime] (S : GL (Fin 3) (ZMod p)) (A : M3 p) :
    minpoly (ZMod p) (conjAlgEquiv S A) = minpoly (ZMod p) A :=
  minpoly.algEquiv_eq (conjAlgEquiv S) A

private lemma hasM3Type_conj {p : ℕ} [Fact p.Prime] (S : GL (Fin 3) (ZMod p)) (A : M3 p) (t : M3Type) :
    HasM3Type (conjAlgEquiv S A) t ↔ HasM3Type A t := by
  cases t <;> simp only [HasM3Type, charpoly_conj, minpoly_conj]

private lemma subring_closure_conj {p : ℕ} [Fact p.Prime] (S : GL (Fin 3) (ZMod p)) (A : M3 p) :
    Subring.closure ({conjAlgEquiv S A} : Set (M3 p)) =
      (Subring.closure ({A} : Set (M3 p))).map (conjAlgEquiv S).toRingHom := by
  rw [subring_map_closure, Set.image_singleton]; rfl

private lemma charpoly_eval_eq_det {p : ℕ} [Fact p.Prime] (A : M3 p) (l : ZMod p) :
    A.charpoly.eval l = (l • (1 : M3 p) - A).det := by
  rw [Matrix.charpoly, ← Polynomial.coe_evalRingHom, RingHom.map_det]
  congr 1
  ext i j
  simp [Matrix.charmatrix, Matrix.diagonal_apply, Matrix.one_apply]
  by_cases h : i = j <;> simp [h]

private lemma isRoot_charpoly_iff_eigvec {p : ℕ} [Fact p.Prime] (A : M3 p) (l : ZMod p) :
    A.charpoly.IsRoot l ↔ ∃ v : V3 p, v ≠ 0 ∧ A *ᵥ v = l • v := by
  rw [Polynomial.IsRoot, charpoly_eval_eq_det, Matrix.exists_mulVec_eq_zero_iff.symm]
  constructor <;> rintro ⟨v, hv, h⟩ <;> refine ⟨v, hv, ?_⟩
  · have h1 : (l • (1 : M3 p)) *ᵥ v - A *ᵥ v = 0 := by simpa [sub_mulVec] using h
    rw [Matrix.smul_mulVec, Matrix.one_mulVec, sub_eq_zero] at h1
    exact h1.symm
  · rw [sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, h, sub_self]

private lemma aeval_mulVec_of_eigvec {p : ℕ} [Fact p.Prime] {A : M3 p} {l : ZMod p} {v : V3 p}
    (hv : A *ᵥ v = l • v) (f : (ZMod p)[X]) :
    (aeval A f) *ᵥ v = (f.eval l) • v := by
  induction f using Polynomial.induction_on' with
  | add f g hf hg =>
    rw [map_add, Polynomial.eval_add, Matrix.add_mulVec, hf, hg, add_smul]
  | monomial n c =>
    rw [aeval_monomial, Polynomial.eval_monomial, Algebra.algebraMap_eq_smul_one,
      smul_mul_assoc, one_mul, Matrix.smul_mulVec]
    have hpow : ∀ k : ℕ, (A ^ k) *ᵥ v = (l ^ k) • v := by
      intro k
      induction k with
      | zero => simp
      | succ k ih =>
        rw [pow_succ', ← Matrix.mulVec_mulVec, ih, Matrix.mulVec_smul, hv, smul_smul, pow_succ', mul_comm]
    rw [hpow n, smul_smul]

private lemma isRoot_minpoly_iff_charpoly {p : ℕ} [Fact p.Prime] (A : M3 p) (l : ZMod p) :
    (minpoly (ZMod p) A).IsRoot l ↔ A.charpoly.IsRoot l := by
  constructor
  · intro h
    obtain ⟨g, hg⟩ := minpoly.dvd (ZMod p) A (Matrix.aeval_self_charpoly A)
    rw [Polynomial.IsRoot, hg, Polynomial.eval_mul, h.eq_zero, zero_mul]
  · intro h
    obtain ⟨v, hv0, hv⟩ := (isRoot_charpoly_iff_eigvec A l).mp h
    have h0 := aeval_mulVec_of_eigvec hv (minpoly (ZMod p) A)
    rw [minpoly.aeval, Matrix.zero_mulVec] at h0
    by_contra hne
    have : v = 0 := by
      have := congrArg (fun w => ((minpoly (ZMod p) A).eval l)⁻¹ • w) h0.symm
      simpa [smul_smul, inv_mul_cancel₀ hne] using this
    exact hv0 this

private lemma minpoly_natDegree_pos {p : ℕ} [Fact p.Prime] (A : M3 p) :
    1 ≤ (minpoly (ZMod p) A).natDegree := by
  have hint : IsIntegral (ZMod p) A := ⟨A.charpoly, Matrix.charpoly_monic A, Matrix.aeval_self_charpoly A⟩
  exact minpoly.natDegree_pos hint

private lemma minpoly_natDegree_le_three {p : ℕ} [Fact p.Prime] (A : M3 p) :
    (minpoly (ZMod p) A).natDegree ≤ 3 := by
  have hdvd := minpoly.dvd (ZMod p) A (Matrix.aeval_self_charpoly A)
  have hne : A.charpoly ≠ 0 := (Matrix.charpoly_monic A).ne_zero
  have hdeg : A.charpoly.natDegree = 3 := by rw [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]
  have hle := Polynomial.natDegree_le_of_dvd hdvd hne
  omega

private lemma charpoly_smul_one {p : ℕ} [Fact p.Prime] (l : ZMod p) :
    (l • (1 : M3 p)).charpoly = (X - C l) ^ 3 := by
  rw [Matrix.charpoly, Matrix.det_fin_three]
  simp [Matrix.charmatrix]
  ring

private lemma minpoly_smul_one {p : ℕ} [Fact p.Prime] (l : ZMod p) :
    minpoly (ZMod p) (l • (1 : M3 p)) = X - C l := by
  have hmon : (X - C l).Monic := Polynomial.monic_X_sub_C l
  have haev : aeval (l • (1 : M3 p)) (X - C l) = 0 := by
    simp [Algebra.algebraMap_eq_smul_one]
  have hdvd := minpoly.dvd (ZMod p) (l • (1 : M3 p)) haev
  have hdeg_le : (minpoly (ZMod p) (l • (1 : M3 p))).natDegree ≤ 1 := by
    simpa [Polynomial.natDegree_X_sub_C] using Polynomial.natDegree_le_of_dvd hdvd hmon.ne_zero
  have hdeg_pos := minpoly_natDegree_pos (l • (1 : M3 p))
  have hdeg_eq : (minpoly (ZMod p) (l • (1 : M3 p))).natDegree = (X - C l).natDegree := by
    rw [Polynomial.natDegree_X_sub_C]; omega
  exact (Polynomial.eq_of_monic_of_dvd_of_natDegree_le
    (minpoly.monic (isIntegral_m3 (l • (1 : M3 p)))) hmon hdvd (le_of_eq hdeg_eq.symm)).symm

/-! ### Section 2: Classification of all `3 × 3` matrices into Types `(A)`–`(H)` & Proposition 3.1 -/

private lemma irred_of_no_root_deg_le_three {K : Type*} [Field K] (P : K[X])
    (hdeg2 : 2 ≤ P.natDegree) (hdeg3 : P.natDegree ≤ 3) (hno : ∀ a : K, ¬ P.IsRoot a) :
    Irreducible P := by
  have hPne : P ≠ 0 := fun h => by subst h; simp at hdeg2
  refine ⟨fun hu => by have := Polynomial.natDegree_eq_zero_of_isUnit hu; omega, ?_⟩
  intro A B hAB
  have hAne : A ≠ 0 := fun h => by rw [h, zero_mul] at hAB; exact hPne hAB
  have hBne : B ≠ 0 := fun h => by rw [h, mul_zero] at hAB; exact hPne hAB
  have hsum : P.natDegree = A.natDegree + B.natDegree := by
    rw [hAB, Polynomial.natDegree_mul hAne hBne]
  by_cases hA0 : A.natDegree = 0
  · left; exact Polynomial.isUnit_iff_degree_eq_zero.mpr (by rw [Polynomial.degree_eq_natDegree hAne, hA0]; rfl)
  · by_cases hB0 : B.natDegree = 0
    · right; exact Polynomial.isUnit_iff_degree_eq_zero.mpr (by rw [Polynomial.degree_eq_natDegree hBne, hB0]; rfl)
    · exfalso
      have hmin : A.natDegree = 1 ∨ B.natDegree = 1 := by omega
      rcases hmin with h1 | h1
      · obtain ⟨a, ha⟩ : ∃ a : K, A.IsRoot a := by
          set r : K := -(A.coeff 0) / A.coeff 1
          refine ⟨r, ?_⟩
          have hlc : A.coeff 1 ≠ 0 := by
            have := Polynomial.leadingCoeff_ne_zero.mpr hAne
            rwa [Polynomial.leadingCoeff, h1] at this
          have hAeq : A = C (A.coeff 1) * X + C (A.coeff 0) :=
            Polynomial.eq_X_add_C_of_degree_le_one (Polynomial.degree_le_of_natDegree_le (le_of_eq h1))
          rw [Polynomial.IsRoot, hAeq]
          simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
          dsimp only [r]; rw [mul_div_cancel₀ _ hlc]; ring
        exact hno a (by rw [Polynomial.IsRoot, hAB, Polynomial.eval_mul, ha.eq_zero, zero_mul])
      · obtain ⟨a, ha⟩ : ∃ a : K, B.IsRoot a := by
          set r : K := -(B.coeff 0) / B.coeff 1
          refine ⟨r, ?_⟩
          have hlc : B.coeff 1 ≠ 0 := by
            have := Polynomial.leadingCoeff_ne_zero.mpr hBne
            rwa [Polynomial.leadingCoeff, h1] at this
          have hBeq : B = C (B.coeff 1) * X + C (B.coeff 0) :=
            Polynomial.eq_X_add_C_of_degree_le_one (Polynomial.degree_le_of_natDegree_le (le_of_eq h1))
          rw [Polynomial.IsRoot, hBeq]
          simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
          dsimp only [r]; rw [mul_div_cancel₀ _ hlc]; ring
        exact hno a (by rw [Polynomial.IsRoot, hAB, Polynomial.eval_mul, ha.eq_zero, mul_zero])

private lemma poly_deg2_cases {p : ℕ} [Fact p.Prime] (Q : (ZMod p)[X]) (hmon : Q.Monic) (hdeg : Q.natDegree = 2) :
    Irreducible Q ∨ ∃ a b : ZMod p, Q = (X - C a) * (X - C b) := by
  by_cases hr : ∃ a : ZMod p, Q.IsRoot a
  · right
    obtain ⟨a, ha⟩ := hr
    obtain ⟨R, hR⟩ := Polynomial.dvd_iff_isRoot.mpr ha
    have hRne : R ≠ 0 := fun h => by rw [h, mul_zero] at hR; exact hmon.ne_zero hR
    have hRdeg : R.natDegree = 1 := by
      have := congrArg Polynomial.natDegree hR
      rw [hdeg, Polynomial.natDegree_mul (Polynomial.monic_X_sub_C a).ne_zero hRne,
          Polynomial.natDegree_X_sub_C] at this
      omega
    have hRmon : R.Monic :=
      (Polynomial.monic_X_sub_C a).of_mul_monic_left (hR ▸ hmon)
    have hReq : R = X - C (-R.coeff 0) := by
      rw [Polynomial.eq_X_add_C_of_degree_le_one (Polynomial.degree_le_of_natDegree_le (le_of_eq hRdeg))]
      have hlc : R.coeff 1 = 1 := by simpa [Polynomial.Monic, Polynomial.leadingCoeff, hRdeg] using hRmon
      simp [hlc, sub_eq_add_neg]
    exact ⟨a, -R.coeff 0, by rw [hR]; conv_lhs => rw [hReq]⟩
  · left
    push Not at hr
    exact irred_of_no_root_deg_le_three Q (by omega) (by omega) hr

private lemma charpoly_deg3_cases {p : ℕ} [Fact p.Prime] (P : (ZMod p)[X]) (hmon : P.Monic) (hdeg : P.natDegree = 3) :
    Irreducible P ∨
    (∃ (l : ZMod p) (Q : (ZMod p)[X]), Q.Monic ∧ Q.natDegree = 2 ∧ Irreducible Q ∧ P = (X - C l) * Q) ∨
    (∃ a b c : ZMod p, P = (X - C a) * (X - C b) * (X - C c)) := by
  by_cases hr : ∃ l : ZMod p, P.IsRoot l
  · obtain ⟨l, hl⟩ := hr
    obtain ⟨Q, hQ⟩ := Polynomial.dvd_iff_isRoot.mpr hl
    have hQne : Q ≠ 0 := fun h => by rw [h, mul_zero] at hQ; exact hmon.ne_zero hQ
    have hQdeg : Q.natDegree = 2 := by
      have := congrArg Polynomial.natDegree hQ
      rw [hdeg, Polynomial.natDegree_mul (Polynomial.monic_X_sub_C l).ne_zero hQne,
          Polynomial.natDegree_X_sub_C] at this
      omega
    have hQmon : Q.Monic := (Polynomial.monic_X_sub_C l).of_mul_monic_left (hQ ▸ hmon)
    rcases poly_deg2_cases Q hQmon hQdeg with hirr | ⟨b, c, hbc⟩
    · exact Or.inr (Or.inl ⟨l, Q, hQmon, hQdeg, hirr, hQ⟩)
    · exact Or.inr (Or.inr ⟨l, b, c, by rw [hQ, hbc, mul_assoc]⟩)
  · push Not at hr
    exact Or.inl (irred_of_no_root_deg_le_three P (by omega) (by omega) hr)

private lemma exists_hasM3Type {p : ℕ} [Fact p.Prime] (A : M3 p) :
    ∃ t : M3Type, HasM3Type A t := by
  have hPmon : A.charpoly.Monic := Matrix.charpoly_monic A
  have hPdeg : A.charpoly.natDegree = 3 := by rw [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]
  have hint : IsIntegral (ZMod p) A := ⟨A.charpoly, hPmon, Matrix.aeval_self_charpoly A⟩
  have hm_mon : (minpoly (ZMod p) A).Monic := minpoly.monic hint
  have hm_dvd : minpoly (ZMod p) A ∣ A.charpoly := minpoly.dvd (ZMod p) A (Matrix.aeval_self_charpoly A)
  have hm_pos : 1 ≤ (minpoly (ZMod p) A).natDegree := minpoly_natDegree_pos A
  have hm_le : (minpoly (ZMod p) A).natDegree ≤ 3 := minpoly_natDegree_le_three A
  have hm_eq_of_deg3 : (minpoly (ZMod p) A).natDegree = 3 → minpoly (ZMod p) A = A.charpoly := fun h =>
    (Polynomial.eq_of_monic_of_dvd_of_natDegree_le hm_mon hPmon hm_dvd (by omega)).symm
  rcases charpoly_deg3_cases A.charpoly hPmon hPdeg with hirr | ⟨l, Q, hQmon, hQdeg, hQirr, hPQ⟩ | ⟨a, b, c, hPabc⟩
  · -- Type G
    refine ⟨.G, hirr, ?_⟩
    obtain ⟨R, hR⟩ := hm_dvd
    rcases hirr.isUnit_or_isUnit hR with hu | hu
    · exfalso; have := Polynomial.natDegree_eq_zero_of_isUnit hu; omega
    · exact hm_eq_of_deg3 (by
        have hR0 := Polynomial.natDegree_eq_zero_of_isUnit hu
        have hRne : R ≠ 0 := hu.ne_zero
        have := congrArg Polynomial.natDegree hR
        rw [hPdeg, Polynomial.natDegree_mul hm_mon.ne_zero hRne, hR0, add_zero] at this
        omega)
  · -- Type H
    refine ⟨.H, l, Q, hQmon, hQdeg, hQirr, hPQ, ?_⟩
    have hl_root : (minpoly (ZMod p) A).IsRoot l :=
      (isRoot_minpoly_iff_charpoly A l).mpr (by rw [Polynomial.IsRoot, hPQ]; simp)
    obtain ⟨M1, hM1⟩ := Polynomial.dvd_iff_isRoot.mpr hl_root
    have hM1_dvd_Q : M1 ∣ Q := by
      obtain ⟨R, hR⟩ := hm_dvd
      rw [hPQ, hM1, mul_assoc] at hR
      exact ⟨R, mul_left_cancel₀ (Polynomial.monic_X_sub_C l).ne_zero hR⟩
    obtain ⟨R, hR⟩ := hM1_dvd_Q
    rcases hQirr.isUnit_or_isUnit hR with hu | hu
    · -- M1 is unit => minpoly = X - C l => A = l • 1 => charpoly = (X - C l)^3 => Q has root l!
      exfalso
      have hM1deg : M1.natDegree = 0 := Polynomial.natDegree_eq_zero_of_isUnit hu
      have hmdeg1 : (minpoly (ZMod p) A).natDegree = 1 := by
        rw [hM1, Polynomial.natDegree_mul (Polynomial.monic_X_sub_C l).ne_zero hu.ne_zero,
            Polynomial.natDegree_X_sub_C, hM1deg]
      have hmeq : minpoly (ZMod p) A = X - C l :=
        Polynomial.eq_of_monic_of_dvd_of_natDegree_le (Polynomial.monic_X_sub_C l) hm_mon
          (by rw [Polynomial.dvd_iff_isRoot]; exact hl_root) (by rw [Polynomial.natDegree_X_sub_C]; omega)
      have hA_eq : A = l • (1 : M3 p) := by
        have := minpoly.aeval (ZMod p) A
        rw [hmeq, map_sub, aeval_X, aeval_C, Algebra.algebraMap_eq_smul_one, sub_eq_zero] at this
        exact this
      have hch : A.charpoly = (X - C l) ^ 3 := hA_eq ▸ charpoly_smul_one l
      rw [hch] at hPQ
      have hQeq : Q = (X - C l) ^ 2 := mul_left_cancel₀ (Polynomial.monic_X_sub_C l).ne_zero
        (by rw [← hPQ]; ring)
      have hQred : ¬ Irreducible Q := by
        rw [hQeq, sq]
        exact not_irreducible_mul (Polynomial.not_isUnit_X_sub_C l) (Polynomial.not_isUnit_X_sub_C l)
      exact hQred hQirr
    · have hR0 := Polynomial.natDegree_eq_zero_of_isUnit hu
      have hM1deg : M1.natDegree = 2 := by
        have := congrArg Polynomial.natDegree hR
        rw [hQdeg, Polynomial.natDegree_mul (by rintro rfl; simp at hR; exact hQmon.ne_zero hR) hu.ne_zero, hR0] at this
        omega
      have hmdeg3 : (minpoly (ZMod p) A).natDegree = 3 := by
        rw [hM1, Polynomial.natDegree_mul (Polynomial.monic_X_sub_C l).ne_zero
          (by rintro rfl; simp at hM1deg), Polynomial.natDegree_X_sub_C, hM1deg]
      exact hm_eq_of_deg3 hmdeg3
  · -- Split into 3 linear factors `(X - C a) * (X - C b) * (X - C c)`
    by_cases hab : a = b
    · subst hab
      by_cases hac : a = c
      · subst hac
        have hP3 : A.charpoly = (X - C a) ^ 3 := by rw [hPabc]; ring
        have ha_r : (minpoly (ZMod p) A).IsRoot a :=
          (isRoot_minpoly_iff_charpoly A a).mpr (by rw [Polynomial.IsRoot, hP3]; simp)
        have hdeg_cases : (minpoly (ZMod p) A).natDegree = 1 ∨
            (minpoly (ZMod p) A).natDegree = 2 ∨ (minpoly (ZMod p) A).natDegree = 3 := by omega
        rcases hdeg_cases with hd1 | hd2 | hd3
        · refine ⟨.A, a, hP3, ?_⟩
          exact Polynomial.eq_of_monic_of_dvd_of_natDegree_le (Polynomial.monic_X_sub_C a) hm_mon
            (Polynomial.dvd_iff_isRoot.mpr ha_r) (by rw [Polynomial.natDegree_X_sub_C]; omega)
        · refine ⟨.E, a, hP3, ?_⟩
          -- `minpoly` divides `(X - C a)^3`, monic, deg 2 => `minpoly = (X - C a)^2`
          obtain ⟨M1, hM1⟩ := Polynomial.dvd_iff_isRoot.mpr ha_r
          have hM1ne : M1 ≠ 0 := fun h => by rw [h, mul_zero] at hM1; exact hm_mon.ne_zero hM1
          have hM1deg : M1.natDegree = 1 := by
            have := congrArg Polynomial.natDegree hM1
            rw [hd2, Polynomial.natDegree_mul (Polynomial.monic_X_sub_C a).ne_zero hM1ne,
                Polynomial.natDegree_X_sub_C] at this; omega
          have hM1mon : M1.Monic := (Polynomial.monic_X_sub_C a).of_mul_monic_left (hM1 ▸ hm_mon)
          have hM1dvd : M1 ∣ (X - C a) ^ 2 := by
            obtain ⟨R, hR⟩ := hm_dvd
            rw [hP3, hM1, mul_assoc] at hR
            exact ⟨R, mul_left_cancel₀ (Polynomial.monic_X_sub_C a).ne_zero (by rw [← hR]; ring)⟩
          have hM1eq : M1 = X - C a := by
            have hroot : M1.IsRoot (-M1.coeff 0) := by
              rw [Polynomial.IsRoot, Polynomial.eq_X_add_C_of_degree_le_one
                (Polynomial.degree_le_of_natDegree_le (le_of_eq hM1deg))]
              have hlc : M1.coeff 1 = 1 := by simpa [Polynomial.Monic, Polynomial.leadingCoeff, hM1deg] using hM1mon
              simp [hlc]
            obtain ⟨R, hR⟩ := hM1dvd
            have hr2 : ((X - C a) ^ 2).eval (-M1.coeff 0) = 0 := by rw [hR, Polynomial.eval_mul, hroot.eq_zero, zero_mul]
            have heq : -M1.coeff 0 = a := by
              have : (-M1.coeff 0 - a) ^ 2 = 0 := by simpa using hr2
              exact sub_eq_zero.mp (pow_eq_zero this)
            have h1 : M1 = X + C (M1.coeff 0) := by
              rw [Polynomial.eq_X_add_C_of_degree_le_one (Polynomial.degree_le_of_natDegree_le (le_of_eq hM1deg))]
              have hlc : M1.coeff 1 = 1 := by simpa [Polynomial.Monic, Polynomial.leadingCoeff, hM1deg] using hM1mon
              simp [hlc]
            rw [h1, show M1.coeff 0 = -a by rw [← heq, neg_neg], map_neg, sub_eq_add_neg]
          rw [hM1, hM1eq, sq]
        · exact ⟨.D, a, hP3, hP3 ▸ hm_eq_of_deg3 hd3⟩
      · -- `a = b ≠ c`: `charpoly = (X - C a)^2 * (X - C c)` -> Type B or Type F
        have hP2 : A.charpoly = (X - C a) ^ 2 * (X - C c) := by rw [hPabc]; ring
        have ha_r : (minpoly (ZMod p) A).IsRoot a :=
          (isRoot_minpoly_iff_charpoly A a).mpr (by rw [Polynomial.IsRoot, hP2]; simp)
        have hc_r : (minpoly (ZMod p) A).IsRoot c :=
          (isRoot_minpoly_iff_charpoly A c).mpr (by rw [Polynomial.IsRoot, hP2]; simp)
        have hdvd2 : (X - C c) * (X - C a) ∣ minpoly (ZMod p) A := by
          obtain ⟨M1, hM1⟩ := Polynomial.dvd_iff_isRoot.mpr hc_r
          have haM1 : M1.IsRoot a := by
            have := ha_r
            rw [Polynomial.IsRoot, hM1, Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C] at this
            exact (mul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr hac)
          obtain ⟨M2, hM2⟩ := Polynomial.dvd_iff_isRoot.mpr haM1
          exact ⟨M2, by rw [hM1, hM2, mul_assoc]⟩
        have hm_ge2 : 2 ≤ (minpoly (ZMod p) A).natDegree := by
          have h2 : ((X - C c) * (X - C a)).natDegree = 2 := by
            rw [Polynomial.natDegree_mul (Polynomial.monic_X_sub_C c).ne_zero (Polynomial.monic_X_sub_C a).ne_zero,
                Polynomial.natDegree_X_sub_C, Polynomial.natDegree_X_sub_C]
          exact h2 ▸ Polynomial.natDegree_le_of_dvd hdvd2 hm_mon.ne_zero
        by_cases hd2 : (minpoly (ZMod p) A).natDegree = 2
        · refine ⟨.B, c, a, Ne.symm hac, by rw [hP2, mul_comm], ?_⟩
          exact Polynomial.eq_of_monic_of_dvd_of_natDegree_le
            ((Polynomial.monic_X_sub_C c).mul (Polynomial.monic_X_sub_C a)) hm_mon hdvd2
            (by rw [hd2, Polynomial.natDegree_mul (Polynomial.monic_X_sub_C c).ne_zero
              (Polynomial.monic_X_sub_C a).ne_zero, Polynomial.natDegree_X_sub_C, Polynomial.natDegree_X_sub_C])
        · exact ⟨.F, a, c, hac, hP2, hm_eq_of_deg3 (by omega)⟩
    · by_cases hac : a = c
      · subst hac
        have hP2 : A.charpoly = (X - C a) ^ 2 * (X - C b) := by rw [hPabc]; ring
        have ha_r : (minpoly (ZMod p) A).IsRoot a :=
          (isRoot_minpoly_iff_charpoly A a).mpr (by rw [Polynomial.IsRoot, hP2]; simp)
        have hb_r : (minpoly (ZMod p) A).IsRoot b :=
          (isRoot_minpoly_iff_charpoly A b).mpr (by rw [Polynomial.IsRoot, hP2]; simp)
        have hdvd2 : (X - C b) * (X - C a) ∣ minpoly (ZMod p) A := by
          obtain ⟨M1, hM1⟩ := Polynomial.dvd_iff_isRoot.mpr hb_r
          have haM1 : M1.IsRoot a := by
            have := ha_r
            rw [Polynomial.IsRoot, hM1, Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C] at this
            exact (mul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr hab)
          obtain ⟨M2, hM2⟩ := Polynomial.dvd_iff_isRoot.mpr haM1
          exact ⟨M2, by rw [hM1, hM2, mul_assoc]⟩
        have hm_ge2 : 2 ≤ (minpoly (ZMod p) A).natDegree := by
          have h2 : ((X - C b) * (X - C a)).natDegree = 2 := by
            rw [Polynomial.natDegree_mul (Polynomial.monic_X_sub_C b).ne_zero (Polynomial.monic_X_sub_C a).ne_zero,
                Polynomial.natDegree_X_sub_C, Polynomial.natDegree_X_sub_C]
          exact h2 ▸ Polynomial.natDegree_le_of_dvd hdvd2 hm_mon.ne_zero
        by_cases hd2 : (minpoly (ZMod p) A).natDegree = 2
        · refine ⟨.B, b, a, Ne.symm hab, by rw [hP2, mul_comm], ?_⟩
          exact Polynomial.eq_of_monic_of_dvd_of_natDegree_le
            ((Polynomial.monic_X_sub_C b).mul (Polynomial.monic_X_sub_C a)) hm_mon hdvd2
            (by rw [hd2, Polynomial.natDegree_mul (Polynomial.monic_X_sub_C b).ne_zero
              (Polynomial.monic_X_sub_C a).ne_zero, Polynomial.natDegree_X_sub_C, Polynomial.natDegree_X_sub_C])
        · exact ⟨.F, a, b, hab, hP2, hm_eq_of_deg3 (by omega)⟩
      · by_cases hbc : b = c
        · subst hbc
          have hP2 : A.charpoly = (X - C b) ^ 2 * (X - C a) := by rw [hPabc]; ring
          have ha_r : (minpoly (ZMod p) A).IsRoot a :=
            (isRoot_minpoly_iff_charpoly A a).mpr (by rw [Polynomial.IsRoot, hP2]; simp)
          have hb_r : (minpoly (ZMod p) A).IsRoot b :=
            (isRoot_minpoly_iff_charpoly A b).mpr (by rw [Polynomial.IsRoot, hP2]; simp)
          have hdvd2 : (X - C a) * (X - C b) ∣ minpoly (ZMod p) A := by
            obtain ⟨M1, hM1⟩ := Polynomial.dvd_iff_isRoot.mpr ha_r
            have hbM1 : M1.IsRoot b := by
              have := hb_r
              rw [Polynomial.IsRoot, hM1, Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C] at this
              exact (mul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr (Ne.symm hab))
            obtain ⟨M2, hM2⟩ := Polynomial.dvd_iff_isRoot.mpr hbM1
            exact ⟨M2, by rw [hM1, hM2, mul_assoc]⟩
          have hm_ge2 : 2 ≤ (minpoly (ZMod p) A).natDegree := by
            have h2 : ((X - C a) * (X - C b)).natDegree = 2 := by
              rw [Polynomial.natDegree_mul (Polynomial.monic_X_sub_C a).ne_zero (Polynomial.monic_X_sub_C b).ne_zero,
                  Polynomial.natDegree_X_sub_C, Polynomial.natDegree_X_sub_C]
            exact h2 ▸ Polynomial.natDegree_le_of_dvd hdvd2 hm_mon.ne_zero
          by_cases hd2 : (minpoly (ZMod p) A).natDegree = 2
          · refine ⟨.B, a, b, hab, by rw [hP2, mul_comm], ?_⟩
            exact Polynomial.eq_of_monic_of_dvd_of_natDegree_le
              ((Polynomial.monic_X_sub_C a).mul (Polynomial.monic_X_sub_C b)) hm_mon hdvd2
              (by rw [hd2, Polynomial.natDegree_mul (Polynomial.monic_X_sub_C a).ne_zero
                (Polynomial.monic_X_sub_C b).ne_zero, Polynomial.natDegree_X_sub_C, Polynomial.natDegree_X_sub_C])
          · exact ⟨.F, b, a, Ne.symm hab, hP2, hm_eq_of_deg3 (by omega)⟩
        · -- All three distinct -> Type C!
          refine ⟨.C, a, b, c, hab, hac, hbc, hPabc, ?_⟩
          have ha_r : (minpoly (ZMod p) A).IsRoot a :=
            (isRoot_minpoly_iff_charpoly A a).mpr (by rw [Polynomial.IsRoot, hPabc]; simp)
          have hb_r : (minpoly (ZMod p) A).IsRoot b :=
            (isRoot_minpoly_iff_charpoly A b).mpr (by rw [Polynomial.IsRoot, hPabc]; simp)
          have hc_r : (minpoly (ZMod p) A).IsRoot c :=
            (isRoot_minpoly_iff_charpoly A c).mpr (by rw [Polynomial.IsRoot, hPabc]; simp)
          obtain ⟨M1, hM1⟩ := Polynomial.dvd_iff_isRoot.mpr ha_r
          have hbM1 : M1.IsRoot b := by
            have := hb_r; rw [Polynomial.IsRoot, hM1, Polynomial.eval_mul] at this
            exact (mul_eq_zero.mp this).resolve_left (by simp [sub_eq_zero, Ne.symm hab])
          obtain ⟨M2, hM2⟩ := Polynomial.dvd_iff_isRoot.mpr hbM1
          have hcM2 : M2.IsRoot c := by
            have := hc_r; rw [Polynomial.IsRoot, hM1, hM2, Polynomial.eval_mul, Polynomial.eval_mul] at this
            have h1 := (mul_eq_zero.mp this).resolve_left (by simp [sub_eq_zero, Ne.symm hac])
            exact (mul_eq_zero.mp h1).resolve_left (by simp [sub_eq_zero, Ne.symm hbc])
          obtain ⟨M3, hM3⟩ := Polynomial.dvd_iff_isRoot.mpr hcM2
          have hdvd3 : A.charpoly ∣ minpoly (ZMod p) A := ⟨M3, by rw [hM1, hM2, hM3, hPabc]; ring⟩
          exact Polynomial.eq_of_monic_of_dvd_of_natDegree_le hPmon hm_mon hdvd3
            (Polynomial.natDegree_le_of_dvd hm_dvd hPmon.ne_zero)

/-- Characterization invariants of each type: `(deg minpoly, # distinct eigenvalues in GF(p), isD)`. -/
private lemma hasM3Type_invariants {p : ℕ} [Fact p.Prime] {A : M3 p} {t : M3Type} (ht : HasM3Type A t) :
    (minpoly (ZMod p) A).natDegree = (match t with | .A => 1 | .B | .E => 2 | _ => 3) ∧
    (Finset.univ.filter fun l : ZMod p => A.charpoly.IsRoot l).card =
      (match t with | .G => 0 | .A | .D | .E | .H => 1 | .B | .F => 2 | .C => 3) ∧
    (t = .D → ∃ l : ZMod p, (A - l • 1) ^ 3 = 0) ∧
    (t = .H → ∀ l : ZMod p, (A - l • 1) ^ 3 ≠ 0) := by
  classical
  have hcard_one : ∀ l : ZMod p, (Finset.univ.filter fun x : ZMod p => x = l).card = 1 := fun l => by
    have : Finset.univ.filter (fun x : ZMod p => x = l) = {l} := by ext x; simp
    rw [this, Finset.card_singleton]
  have hcard_two : ∀ {l m : ZMod p}, l ≠ m →
      (Finset.univ.filter fun x : ZMod p => x = l ∨ x = m).card = 2 := fun {l m} hne => by
    have : Finset.univ.filter (fun x : ZMod p => x = l ∨ x = m) = {l, m} := by ext x; simp
    rw [this, Finset.card_pair hne]
  have hcard_three : ∀ {l m n : ZMod p}, l ≠ m → l ≠ n → m ≠ n →
      (Finset.univ.filter fun x : ZMod p => x = l ∨ x = m ∨ x = n).card = 3 := fun {l m n} h1 h2 h3 => by
    have : Finset.univ.filter (fun x : ZMod p => x = l ∨ x = m ∨ x = n) = {l, m, n} := by ext x; simp
    rw [this, Finset.card_insert_of_notMem (by simp [h1, h2]), Finset.card_pair h3]
  cases t with
  | A =>
    dsimp only
    rcases ht with ⟨l, hch, hm⟩
    refine ⟨by rw [hm, Polynomial.natDegree_X_sub_C], ?_, fun h => M3Type.noConfusion h, fun h => M3Type.noConfusion h⟩
    convert hcard_one l using 2; ext x; simp [Polynomial.IsRoot, hch, sub_eq_zero]
  | B =>
    dsimp only
    rcases ht with ⟨l, m, hlm, hch, hm⟩
    refine ⟨?_, ?_, fun h => M3Type.noConfusion h, fun h => M3Type.noConfusion h⟩
    · rw [hm, Polynomial.natDegree_mul (Polynomial.monic_X_sub_C l).ne_zero (Polynomial.monic_X_sub_C m).ne_zero,
          Polynomial.natDegree_X_sub_C, Polynomial.natDegree_X_sub_C]
    · convert hcard_two hlm using 2; ext x; simp [Polynomial.IsRoot, hch, sub_eq_zero]
  | C =>
    dsimp only
    rcases ht with ⟨l, m, n, h1, h2, h3, hch, hm⟩
    have hdeg3 : A.charpoly.natDegree = 3 := by rw [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]
    refine ⟨by rw [hm, hdeg3], ?_, fun h => M3Type.noConfusion h, fun h => M3Type.noConfusion h⟩
    convert hcard_three h1 h2 h3 using 2; ext x; simp [Polynomial.IsRoot, hch, sub_eq_zero, or_assoc]
  | D =>
    dsimp only
    rcases ht with ⟨l, hch, hm⟩
    have hdeg3 : A.charpoly.natDegree = 3 := by rw [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]
    refine ⟨by rw [hm, ← hch, hdeg3], ?_, fun _ => ⟨l, ?_⟩, fun h => M3Type.noConfusion h⟩
    · convert hcard_one l using 2; ext x; simp [Polynomial.IsRoot, hch, sub_eq_zero]
    · have := Matrix.aeval_self_charpoly A
      rw [hch, map_pow, map_sub, aeval_X, aeval_C, Algebra.algebraMap_eq_smul_one] at this
      exact this
  | E =>
    dsimp only
    rcases ht with ⟨l, hch, hm⟩
    refine ⟨by rw [hm, Polynomial.natDegree_pow, Polynomial.natDegree_X_sub_C], ?_,
      fun h => M3Type.noConfusion h, fun h => M3Type.noConfusion h⟩
    convert hcard_one l using 2; ext x; simp [Polynomial.IsRoot, hch, sub_eq_zero]
  | F =>
    dsimp only
    rcases ht with ⟨l, m, hlm, hch, hm⟩
    have hdeg3 : A.charpoly.natDegree = 3 := by rw [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]
    refine ⟨by rw [hm, hdeg3], ?_, fun h => M3Type.noConfusion h, fun h => M3Type.noConfusion h⟩
    convert hcard_two hlm using 2; ext x; simp [Polynomial.IsRoot, hch, sub_eq_zero]
  | G =>
    dsimp only
    rcases ht with ⟨hirr, hm⟩
    have hdeg3 : A.charpoly.natDegree = 3 := by rw [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]
    refine ⟨by rw [hm, hdeg3], ?_, fun h => M3Type.noConfusion h, fun h => M3Type.noConfusion h⟩
    have hno : ∀ x : ZMod p, ¬ A.charpoly.IsRoot x := fun x hx => by
      obtain ⟨Q, hQ⟩ := Polynomial.dvd_iff_isRoot.mpr hx
      rcases hirr.isUnit_or_isUnit hQ with hu | hu
      · exact Polynomial.not_isUnit_X_sub_C x hu
      · have hQ0 := Polynomial.natDegree_eq_zero_of_isUnit hu
        have := congrArg Polynomial.natDegree hQ
        rw [hdeg3, Polynomial.natDegree_mul (Polynomial.monic_X_sub_C x).ne_zero hu.ne_zero,
            Polynomial.natDegree_X_sub_C, hQ0] at this; omega
    have : Finset.univ.filter (fun x : ZMod p => A.charpoly.IsRoot x) = ∅ := by
      ext x; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
      exact hno x
    rw [this, Finset.card_empty]
  | H =>
    dsimp only
    rcases ht with ⟨l, Q, hQmon, hQdeg, hQirr, hch, hm⟩
    have hdeg3 : A.charpoly.natDegree = 3 := by rw [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]
    have hQno : ∀ x : ZMod p, ¬ Q.IsRoot x := fun x hx => by
      obtain ⟨R, hR⟩ := Polynomial.dvd_iff_isRoot.mpr hx
      rcases hQirr.isUnit_or_isUnit hR with hu | hu
      · exact Polynomial.not_isUnit_X_sub_C x hu
      · have hR0 := Polynomial.natDegree_eq_zero_of_isUnit hu
        have := congrArg Polynomial.natDegree hR
        rw [hQdeg, Polynomial.natDegree_mul (Polynomial.monic_X_sub_C x).ne_zero hu.ne_zero,
            Polynomial.natDegree_X_sub_C, hR0] at this; omega
    refine ⟨by rw [hm, hdeg3], ?_, fun h => M3Type.noConfusion h, fun _ c hc => ?_⟩
    · convert hcard_one l using 2; ext x
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Polynomial.IsRoot, hch,
        Polynomial.eval_mul, mul_eq_zero, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C,
        sub_eq_zero]
      exact ⟨fun h => h.resolve_right (hQno x), Or.inl⟩
    · have haev : aeval A ((X - C c) ^ 3) = 0 := by
        simpa [Algebra.algebraMap_eq_smul_one] using hc
      have hdvd : minpoly (ZMod p) A ∣ (X - C c) ^ 3 := minpoly.dvd (ZMod p) A haev
      rw [hm, hch] at hdvd
      have hQdvd : Q ∣ (X - C c) ^ 3 := dvd_trans (dvd_mul_left Q (X - C l)) hdvd
      have hprime : Prime Q := hQirr.prime
      have hQdvd1 : Q ∣ (X - C c) := hprime.dvd_of_dvd_pow hQdvd
      have hle := Polynomial.natDegree_le_of_dvd hQdvd1 (Polynomial.monic_X_sub_C c).ne_zero
      rw [Polynomial.natDegree_X_sub_C] at hle; omega

private lemma hasM3Type_unique {p : ℕ} [Fact p.Prime] {A : M3 p} {t₁ t₂ : M3Type}
    (h1 : HasM3Type A t₁) (h2 : HasM3Type A t₂) : t₁ = t₂ := by
  have i1 := hasM3Type_invariants h1
  have i2 := hasM3Type_invariants h2
  cases t₁ <;> cases t₂ <;> dsimp only at i1 i2 <;>
    first | rfl | (exfalso; omega) | (exfalso; rcases i1.2.2.1 rfl with ⟨l, hl⟩; exact i2.2.2.2 rfl l hl) | (exfalso; rcases i2.2.2.1 rfl with ⟨l, hl⟩; exact i1.2.2.2 rfl l hl)

private lemma existsUnique_hasM3Type {p : ℕ} [Fact p.Prime] (A : M3 p) :
    ∃! t : M3Type, HasM3Type A t := by
  obtain ⟨t, ht⟩ := exists_hasM3Type A
  exact ⟨t, ht, fun t' ht' => hasM3Type_unique ht' ht⟩

/-- Proposition 3.1: Matrices generating the same unital subring have the same type. -/
private lemma same_type_of_subring_eq {p : ℕ} [Fact p.Prime] {A B : M3 p}
    (hAB : Subring.closure ({A} : Set (M3 p)) = Subring.closure ({B} : Set (M3 p))) :
    ∀ t : M3Type, HasM3Type A t ↔ HasM3Type B t := by
  classical
  obtain ⟨tA, htA⟩ := exists_hasM3Type A
  obtain ⟨tB, htB⟩ := exists_hasM3Type B
  suffices hEq : tA = tB by
    intro t; constructor <;> intro ht
    · rw [hasM3Type_unique ht htA, hEq]; exact htB
    · rw [hasM3Type_unique ht htB, ← hEq]; exact htA
  have iA := hasM3Type_invariants htA
  have iB := hasM3Type_invariants htB
  -- 1. Equal `minpoly.natDegree` via `finrank` of `Algebra.adjoin (ZMod p) {A}`
  have hadj_eq : Algebra.adjoin (ZMod p) ({A} : Set (M3 p)) = Algebra.adjoin (ZMod p) ({B} : Set (M3 p)) := by
    ext X
    change X ∈ (Algebra.adjoin (ZMod p) ({A} : Set (M3 p))).toSubring ↔
           X ∈ (Algebra.adjoin (ZMod p) ({B} : Set (M3 p))).toSubring
    rw [← subring_closure_eq_adjoin A, ← subring_closure_eq_adjoin B, hAB]
  have hdeg_eq : (minpoly (ZMod p) A).natDegree = (minpoly (ZMod p) B).natDegree := by
    rw [← finrank_adjoin_singleton_m3 A, ← finrank_adjoin_singleton_m3 B, hadj_eq]
  -- 2. Equal number of distinct eigenvalues in `ZMod p` via `f, g` with `B = f(A), A = g(B)`
  obtain ⟨f, hf⟩ := (mem_subring_closure_iff_aeval A B).mp (hAB ▸ Subring.subset_closure rfl)
  obtain ⟨g, hg⟩ := (mem_subring_closure_iff_aeval B A).mp (hAB.symm ▸ Subring.subset_closure rfl)
  have hroots_eq : (Finset.univ.filter fun l : ZMod p => A.charpoly.IsRoot l).card =
      (Finset.univ.filter fun l : ZMod p => B.charpoly.IsRoot l).card := by
    refine Finset.card_bij (fun l _ => f.eval l) ?_ ?_ ?_
    · intro l hl
      have hl' := (Finset.mem_filter.mp hl).2
      obtain ⟨v, hv0, hv⟩ := (isRoot_charpoly_iff_eigvec A l).mp hl'
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, (isRoot_charpoly_iff_eigvec B _).mpr ⟨v, hv0, ?_⟩⟩
      rw [← hf]; exact aeval_mulVec_of_eigvec hv f
    · intro l₁ hl₁ l₂ hl₂ hfeq
      obtain ⟨v₁, hv10, hv₁⟩ := (isRoot_charpoly_iff_eigvec A l₁).mp (Finset.mem_filter.mp hl₁).2
      obtain ⟨v₂, hv20, hv₂⟩ := (isRoot_charpoly_iff_eigvec A l₂).mp (Finset.mem_filter.mp hl₂).2
      have h1 : g.eval (f.eval l₁) = l₁ := by
        have hB1 : B *ᵥ v₁ = (f.eval l₁) • v₁ := by rw [← hf]; exact aeval_mulVec_of_eigvec hv₁ f
        have hA1 : A *ᵥ v₁ = (g.eval (f.eval l₁)) • v₁ := by rw [← hg]; exact aeval_mulVec_of_eigvec hB1 g
        have hsub : (g.eval (f.eval l₁) - l₁) • v₁ = 0 := by rw [sub_smul, ← hA1, ← hv₁, sub_self]
        by_contra hne
        have h0 := congrArg (fun w => (g.eval (f.eval l₁) - l₁)⁻¹ • w) hsub
        rw [smul_smul, inv_mul_cancel₀ (sub_ne_zero.mpr hne), one_smul, smul_zero] at h0
        exact hv10 h0
      have h2 : g.eval (f.eval l₂) = l₂ := by
        have hB2 : B *ᵥ v₂ = (f.eval l₂) • v₂ := by rw [← hf]; exact aeval_mulVec_of_eigvec hv₂ f
        have hA2 : A *ᵥ v₂ = (g.eval (f.eval l₂)) • v₂ := by rw [← hg]; exact aeval_mulVec_of_eigvec hB2 g
        have hsub : (g.eval (f.eval l₂) - l₂) • v₂ = 0 := by rw [sub_smul, ← hA2, ← hv₂, sub_self]
        by_contra hne
        have h0 := congrArg (fun w => (g.eval (f.eval l₂) - l₂)⁻¹ • w) hsub
        rw [smul_smul, inv_mul_cancel₀ (sub_ne_zero.mpr hne), one_smul, smul_zero] at h0
        exact hv20 h0
      rw [← h1, ← h2, hfeq]
    · intro m hm
      obtain ⟨v, hv0, hv⟩ := (isRoot_charpoly_iff_eigvec B m).mp (Finset.mem_filter.mp hm).2
      have hA : A *ᵥ v = (g.eval m) • v := by rw [← hg]; exact aeval_mulVec_of_eigvec hv g
      have hB : B *ᵥ v = (f.eval (g.eval m)) • v := by rw [← hf]; exact aeval_mulVec_of_eigvec hA f
      have hfg : f.eval (g.eval m) = m := by
        have hsub : (f.eval (g.eval m) - m) • v = 0 := by rw [sub_smul, ← hB, ← hv, sub_self]
        by_contra hne
        have h0 := congrArg (fun w => (f.eval (g.eval m) - m)⁻¹ • w) hsub
        rw [smul_smul, inv_mul_cancel₀ (sub_ne_zero.mpr hne), one_smul, smul_zero] at h0
        exact hv0 h0
      exact ⟨g.eval m, Finset.mem_filter.mpr ⟨Finset.mem_univ _, (isRoot_charpoly_iff_eigvec A _).mpr ⟨v, hv0, hA⟩⟩, hfg⟩
  -- 3. Distinguish Type D vs Type H: if `(A - l•1)^3 = 0` then `(f(A) - f(l)•1)^3 = 0`!
  have hnilp : ∀ {X Y : M3 p} {h : (ZMod p)[X]}, aeval X h = Y →
      (∃ l : ZMod p, (X - l • 1) ^ 3 = 0) → (∃ m : ZMod p, (Y - m • 1) ^ 3 = 0) := by
    intro X Y h hXY ⟨l, hl⟩
    refine ⟨h.eval l, ?_⟩
    obtain ⟨q, hq⟩ := Polynomial.dvd_iff_isRoot.mpr (show (h - C (h.eval l)).IsRoot l by simp [Polynomial.IsRoot])
    have hdiff : Y - (h.eval l) • (1 : M3 p) = (X - l • 1) * aeval X q := by
      have := congrArg (aeval X) hq
      simpa [hXY, Algebra.algebraMap_eq_smul_one] using this
    rw [hdiff, Commute.mul_pow (Commute.sub_left (commute_aeval_self X q).symm (Commute.smul_left (Commute.one_left _) l)),
        hl, zero_mul]
  cases tA <;> cases tB <;> dsimp only at iA iB <;> first
    | rfl
    | (exfalso; omega)
    | (exfalso; exact iB.2.2.2 rfl _ (hnilp hf (iA.2.2.1 rfl)).choose_spec)
    | (exfalso; exact iA.2.2.2 rfl _ (hnilp hg (iB.2.2.1 rfl)).choose_spec)

/-! ### Section 3: Explicit Canonical Forms & Generators for All 8 Types -/

private lemma vertHasType_iff_all {p : ℕ} [Fact p.Prime] {v : UCCGVert p} {t : M3Type} :
    VertHasType v t ↔ ∀ A ∈ SingleGens v, HasM3Type A t := by
  constructor
  · rintro ⟨A, hA, htA⟩ B hB
    exact (same_type_of_subring_eq (hA.trans hB.symm) t).mp htA
  · intro h
    obtain ⟨A, hA⟩ := v.prop
    exact ⟨A, hA.symm, h A hA.symm⟩

private lemma vertHasType_unique {p : ℕ} [Fact p.Prime] {v : UCCGVert p} {t₁ t₂ : M3Type}
    (h1 : VertHasType v t₁) (h2 : VertHasType v t₂) : t₁ = t₂ := by
  obtain ⟨A, hA, ht1⟩ := h1
  exact hasM3Type_unique ht1 ((vertHasType_iff_all.mp h2) A hA)

/-- Build `S ∈ GL (Fin 3) (ZMod p)` from 3 linearly independent column vectors `v0, v1, v2`. -/
private noncomputable def glOfCols {p : ℕ} [Fact p.Prime] (v0 v1 v2 : V3 p)
    (hli : LinearIndependent (ZMod p) ![v0, v1, v2]) : GL (Fin 3) (ZMod p) :=
  let M : M3 p := Matrix.of fun i j => ![v0, v1, v2] j i
  have hdet : IsUnit M.det := by
    rw [isUnit_iff_ne_zero]
    intro h0
    obtain ⟨c, hc0, hMc⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h0
    have hlin : ∑ j : Fin 3, c j • ![v0, v1, v2] j = 0 := by
      ext i
      have hi := congrFun hMc i
      simpa [M, Matrix.mulVec, dotProduct, mul_comm] using hi
    have hc_all : ∀ j, c j = 0 := Fintype.linearIndependent_iff.mp hli c hlin
    exact hc0 (funext hc_all)
  Matrix.nonsingInvUnit M hdet

private lemma glOfCols_mul_eq {p : ℕ} [Fact p.Prime] {v0 v1 v2 : V3 p}
    (hli : LinearIndependent (ZMod p) ![v0, v1, v2]) (A B : M3 p)
    (h0 : A *ᵥ v0 = B 0 0 • v0 + B 1 0 • v1 + B 2 0 • v2)
    (h1 : A *ᵥ v1 = B 0 1 • v0 + B 1 1 • v1 + B 2 1 • v2)
    (h2 : A *ᵥ v2 = B 0 2 • v0 + B 1 2 • v1 + B 2 2 • v2) :
    conjAlgEquiv (glOfCols v0 v1 v2 hli)⁻¹ A = B := by
  set S := glOfCols v0 v1 v2 hli
  change (↑S⁻¹ : M3 p) * A * S.val = B
  have hSval : S.val = Matrix.of fun i j => ![v0, v1, v2] j i := rfl
  have hAS : A * S.val = S.val * B := by
    ext i j
    have hcol : ∀ k : Fin 3, (A * S.val) i k = (A *ᵥ ![v0, v1, v2] k) i := fun k => by
      rw [hSval]; simp [Matrix.mul_apply, Matrix.mulVec, dotProduct]
    have hSB : ∀ k : Fin 3, (S.val * B) i k =
        (B 0 k • v0 + B 1 k • v1 + B 2 k • v2) i := fun k => by
      rw [hSval]; simp [Matrix.mul_apply, Fin.sum_univ_three, mul_comm]
    rw [hcol j, hSB j]
    fin_cases j
    · exact congrFun h0 i
    · exact congrFun h1 i
    · exact congrFun h2 i
  rw [mul_assoc, hAS, ← mul_assoc, Units.inv_mul, one_mul]

private lemma linearIndependent_three_iff {p : ℕ} [Fact p.Prime] (v0 v1 v2 : V3 p) :
    LinearIndependent (ZMod p) ![v0, v1, v2] ↔
      ∀ c0 c1 c2 : ZMod p, c0 • v0 + c1 • v1 + c2 • v2 = 0 → c0 = 0 ∧ c1 = 0 ∧ c2 = 0 := by
  rw [Fintype.linearIndependent_iff]
  constructor
  · intro h c0 c1 c2 hsum
    have h0 := h ![c0, c1, c2] (by simpa [Fin.sum_univ_three] using hsum)
    exact ⟨h0 0, h0 1, h0 2⟩
  · intro h c hsum
    have h' : c 0 • v0 + c 1 • v1 + c 2 • v2 = 0 := by simpa [Fin.sum_univ_three] using hsum
    obtain ⟨h0, h1, h2⟩ := h (c 0) (c 1) (c 2) h'
    intro j; fin_cases j <;> assumption

private def matE01 (p : ℕ) : M3 p := !![0, 1, 0; 0, 0, 0; 0, 0, 0]
private def matB0 (p : ℕ) : M3 p := !![1, 0, 0; 0, 0, 0; 0, 0, 0]
private def matD0 (p : ℕ) : M3 p := !![0, 1, 0; 0, 0, 1; 0, 0, 0]
private def matF0 (p : ℕ) : M3 p := !![0, 1, 0; 0, 0, 0; 0, 0, 1]
private def matComp3 {p : ℕ} (q : (ZMod p)[X]) : M3 p :=
  !![0, 0, -q.coeff 0; 1, 0, -q.coeff 1; 0, 1, -q.coeff 2]
private def matH0 {p : ℕ} (l : ZMod p) (q : (ZMod p)[X]) : M3 p :=
  !![l, 0, 0; 0, 0, -q.coeff 0; 0, 1, -q.coeff 1]

/-- Any two matrices `A` and `a • A + b • 1` with `a ≠ 0` generate the same unital subring. -/
private lemma subring_closure_affine {p : ℕ} [Fact p.Prime] (A : M3 p) {a : ZMod p} (ha : a ≠ 0) (b : ZMod p) :
    Subring.closure ({a • A + b • (1 : M3 p)} : Set (M3 p)) = Subring.closure ({A} : Set (M3 p)) := by
  apply le_antisymm
  · rw [Subring.closure_le, Set.singleton_subset_iff]
    exact add_mem (smul_mem_subring _ a (Subring.subset_closure rfl)) (smul_one_mem_subring _ b)
  · rw [Subring.closure_le, Set.singleton_subset_iff]
    set S := Subring.closure ({a • A + b • (1 : M3 p)} : Set (M3 p))
    have hEq : A = a⁻¹ • (a • A + b • (1 : M3 p)) + (-a⁻¹ * b) • (1 : M3 p) := by
      rw [smul_add, smul_smul, inv_mul_cancel₀ ha, one_smul, smul_smul, add_assoc, ← add_smul]
      simp
    rw [hEq]
    exact add_mem (smul_mem_subring S a⁻¹ (Subring.subset_closure rfl)) (smul_one_mem_subring S (-a⁻¹ * b))

/-- Helper: `Subring.closure {A}` is equal to `Subring.closure {B}` iff `B ∈ ⟨A⟩` and `A ∈ ⟨B⟩`. -/
private lemma subring_closure_eq_iff {p : ℕ} (A B : M3 p) :
    Subring.closure ({A} : Set (M3 p)) = Subring.closure ({B} : Set (M3 p)) ↔
      B ∈ Subring.closure ({A} : Set (M3 p)) ∧ A ∈ Subring.closure ({B} : Set (M3 p)) := by
  constructor
  · intro h; exact ⟨h ▸ Subring.subset_closure rfl, h.symm ▸ Subring.subset_closure rfl⟩
  · rintro ⟨hBA, hAB⟩
    exact le_antisymm (Subring.closure_le.mpr (Set.singleton_subset_iff.mpr hAB))
      (Subring.closure_le.mpr (Set.singleton_subset_iff.mpr hBA))

/-- Helper: if `N^2 = 0` and `N ≠ 0`, then `N` is conjugate to `matE01 p`! -/
private lemma exists_conj_matE01 {p : ℕ} [Fact p.Prime] {N : M3 p} (hN0 : N ≠ 0) (hN2 : N ^ 2 = 0) :
    ∃ S : GL (Fin 3) (ZMod p), conjAlgEquiv S N = matE01 p := by
  classical
  -- Pick `v1` with `N *ᵥ v1 ≠ 0`, set `v0 := N *ᵥ v1`, so `N *ᵥ v0 = 0`
  have hex_v1 : ∃ v1 : V3 p, N *ᵥ v1 ≠ 0 := by
    by_contra hall; push Not at hall
    apply hN0; ext i j
    have := congrFun (hall (Pi.single j 1)) i
    simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_three, Pi.single_apply] using this
  obtain ⟨v1, hv1⟩ := hex_v1
  set v0 := N *ᵥ v1
  have hNv0 : N *ᵥ v0 = 0 := by
    show N *ᵥ (N *ᵥ v1) = 0
    rw [Matrix.mulVec_mulVec, ← sq, hN2, Matrix.zero_mulVec]
  -- `ker N` has dimension ≥ 2 because `range N ≤ ker N` and `rank + nullity = 3`;
  -- in fact we just pick any `v2 ∈ ker N` not in `span {v0}`!
  have hker_dim : 2 ≤ Module.finrank (ZMod p) (LinearMap.ker (Matrix.toLin' N)) := by
    have hle : LinearMap.range (Matrix.toLin' N) ≤ LinearMap.ker (Matrix.toLin' N) := by
      rintro _ ⟨x, rfl⟩
      show N *ᵥ (N *ᵥ x) = 0
      rw [Matrix.mulVec_mulVec, ← sq, hN2, Matrix.zero_mulVec]
    have hsum := LinearMap.finrank_range_add_finrank_ker (Matrix.toLin' N)
    rw [Module.finrank_fin_fun] at hsum
    have h1 := Submodule.finrank_mono hle
    omega
  have hex_v2 : ∃ v2 : V3 p, N *ᵥ v2 = 0 ∧ ∀ c : ZMod p, v2 ≠ c • v0 := by
    by_contra hall; push Not at hall
    have hsub : LinearMap.ker (Matrix.toLin' N) ≤ Submodule.span (ZMod p) {v0} := by
      intro x hx
      obtain ⟨c, rfl⟩ := hall x hx
      exact Submodule.smul_mem _ c (Submodule.subset_span rfl)
    have hle1 : Module.finrank (ZMod p) (LinearMap.ker (Matrix.toLin' N)) ≤ 1 :=
      le_trans (Submodule.finrank_mono hsub) (finrank_span_singleton_le v0)
    omega
  obtain ⟨v2, hNv2, hv2_ind⟩ := hex_v2
  have hli : LinearIndependent (ZMod p) ![v0, v1, v2] := by
    rw [linearIndependent_three_iff]
    intro c0 c1 c2 hsum
    have hNsum := congrArg (N *ᵥ ·) hsum
    simp only [Matrix.mulVec_add, Matrix.mulVec_smul, hNv0, hNv2, Matrix.mulVec_zero,
      smul_zero, zero_add, add_zero] at hNsum
    have hc1 : c1 = 0 := by
      by_contra hne
      exact hv1 (by simpa [smul_smul, inv_mul_cancel₀ hne] using congrArg (c1⁻¹ • ·) hNsum)
    subst hc1; simp only [zero_smul, add_zero] at hsum
    have hc2 : c2 = 0 := by
      by_contra hne
      have : v2 = (-c2⁻¹ * c0) • v0 := by
        have := congrArg (c2⁻¹ • ·) hsum
        rw [smul_add, smul_smul, smul_smul, inv_mul_cancel₀ hne, one_smul, smul_zero] at this
        have h1 := eq_neg_of_add_eq_zero_right this
        simpa [neg_mul, neg_smul] using h1
      exact hv2_ind (-c2⁻¹ * c0) this
    subst hc2; simp only [zero_smul, add_zero] at hsum
    have hc0 : c0 = 0 := by
      by_contra hne
      exact hv1 (by simpa [smul_smul, inv_mul_cancel₀ hne] using congrArg (c0⁻¹ • ·) hsum)
    exact ⟨hc0, rfl, rfl⟩
  refine ⟨(glOfCols v0 v1 v2 hli)⁻¹, glOfCols_mul_eq hli N (matE01 p) ?_ ?_ ?_⟩
  · simp [matE01, hNv0]
  · simp [matE01, v0]
  · simp [matE01, hNv2]

/-- Helper: if `P^2 = P` and `charpoly P = (X - 1) * X^2`, then `P` is conjugate to `matB0 p`! -/
private lemma exists_conj_matB0 {p : ℕ} [Fact p.Prime] {P : M3 p}
    (hPch : P.charpoly = (X - C 1) * X ^ 2) (hP2 : P ^ 2 = P) :
    ∃ S : GL (Fin 3) (ZMod p), conjAlgEquiv S P = matB0 p := by
  classical
  -- `1` is an eigenvalue -> pick `v0 ≠ 0` with `P *ᵥ v0 = v0`
  have h1r : P.charpoly.IsRoot 1 := by rw [Polynomial.IsRoot, hPch]; simp
  obtain ⟨v0, hv0_ne, hv0⟩ := (isRoot_charpoly_iff_eigvec P 1).mp h1r
  rw [one_smul] at hv0
  -- `ker P` has dimension 2! (If `dim (range P) ≥ 2`, since `P = id` on `range P`, then `dim (ker (P - I)) ≥ 2`,
  -- so `(X - 1)^2 ∣ charpoly P`, contradicting `charpoly P = (X - 1) * X^2`!)
  -- Even simpler: pick `v1 ≠ 0` in `ker P` (since `0` is a root of `charpoly P`).
  have h0r : P.charpoly.IsRoot 0 := by rw [Polynomial.IsRoot, hPch]; simp
  obtain ⟨v1, hv1_ne, hv1⟩ := (isRoot_charpoly_iff_eigvec P 0).mp h0r
  rw [zero_smul] at hv1
  -- Show `dim (ker P) ≥ 2`: if `dim (ker P) ≤ 1`, then `dim (range P) ≥ 2`, so `P` is identity on a 2D subspace `W`,
  -- pick independent `u1, u2 ∈ W` and `v1 ∈ ker P` -> in basis `u1, u2, v1`, `P = diag(1, 1, 0)` -> `charpoly = (X - 1)^2 * X`!
  have hker2 : 2 ≤ Module.finrank (ZMod p) (LinearMap.ker (Matrix.toLin' P)) := by
    by_contra hlt
    have hsum := LinearMap.finrank_range_add_finrank_ker (Matrix.toLin' P)
    rw [Module.finrank_fin_fun] at hsum
    have hran2 : 2 ≤ Module.finrank (ZMod p) (LinearMap.range (Matrix.toLin' P)) := by omega
    -- Pick `u0 ∈ range P` (`v0 = P *ᵥ v0 ∈ range P`) and `u1 ∈ range P` independent of `v0`!
    have hex_u1 : ∃ u1 : V3 p, P *ᵥ u1 = u1 ∧ ∀ c : ZMod p, u1 ≠ c • v0 := by
      by_contra hall; push Not at hall
      have hsub : LinearMap.range (Matrix.toLin' P) ≤ Submodule.span (ZMod p) {v0} := by
        rintro _ ⟨x, rfl⟩
        have hfix : P *ᵥ (P *ᵥ x) = P *ᵥ x := by rw [Matrix.mulVec_mulVec, ← sq, hP2]
        obtain ⟨c, hc⟩ := hall (P *ᵥ x) hfix
        change P *ᵥ x ∈ _
        rw [hc]; exact Submodule.smul_mem _ c (Submodule.subset_span rfl)
      have hle1 : Module.finrank (ZMod p) (LinearMap.range (Matrix.toLin' P)) ≤ 1 :=
        le_trans (Submodule.finrank_mono hsub) (finrank_span_singleton_le v0)
      omega
    obtain ⟨u1, hu1, hu1_ind⟩ := hex_u1
    have hli : LinearIndependent (ZMod p) ![v0, u1, v1] := by
      rw [linearIndependent_three_iff]
      intro c0 c1 c2 hsum
      have hP := congrArg (P *ᵥ ·) hsum
      simp only [Matrix.mulVec_add, Matrix.mulVec_smul, hv0, hu1, hv1, Matrix.mulVec_zero,
        smul_zero, add_zero] at hP
      have hc1 : c1 = 0 := by
        by_contra hne
        exact hu1_ind (-c1⁻¹ * c0) (by
          have := congrArg (c1⁻¹ • ·) hP
          rw [smul_add, smul_smul, smul_smul, inv_mul_cancel₀ hne, one_smul, smul_zero] at this
          simpa [neg_mul, neg_smul] using eq_neg_of_add_eq_zero_right this)
      subst hc1; simp only [zero_smul, add_zero] at hP hsum
      have hc0 : c0 = 0 := by
        by_contra hne
        exact hv0_ne (by simpa [smul_smul, inv_mul_cancel₀ hne] using congrArg (c0⁻¹ • ·) hP)
      subst hc0; simp only [zero_smul, zero_add] at hsum
      have hc2 : c2 = 0 := by
        by_contra hne
        exact hv1_ne (by simpa [smul_smul, inv_mul_cancel₀ hne] using congrArg (c2⁻¹ • ·) hsum)
      exact ⟨rfl, rfl, hc2⟩
    have hconj := glOfCols_mul_eq hli P (!![1, 0, 0; 0, 1, 0; 0, 0, 0])
      (by simp [hv0]) (by simp [hu1]) (by simp [hv1])
    have hch_eq : P.charpoly = (!![(1 : ZMod p), 0, 0; 0, 1, 0; 0, 0, 0]).charpoly := by
      rw [← hconj, charpoly_conj]
    have hch_calc : (!![(1 : ZMod p), 0, 0; 0, 1, 0; 0, 0, 0]).charpoly = (X - C 1) ^ 2 * X := by
      rw [Matrix.charpoly, Matrix.det_fin_three]
      simp [Matrix.charmatrix]; ring
    rw [hPch, hch_calc] at hch_eq
    have hcoeff := congrArg (fun f : (ZMod p)[X] => f.coeff 1) hch_eq
    simp [sq, mul_sub, sub_mul, Polynomial.coeff_X] at hcoeff
  have hex_v2 : ∃ v2 : V3 p, P *ᵥ v2 = 0 ∧ ∀ c : ZMod p, v2 ≠ c • v1 := by
    by_contra hall; push Not at hall
    have hsub : LinearMap.ker (Matrix.toLin' P) ≤ Submodule.span (ZMod p) {v1} := by
      intro x hx
      obtain ⟨c, hc⟩ := hall x hx
      rw [hc]; exact Submodule.smul_mem _ c (Submodule.subset_span rfl)
    have hle1 : Module.finrank (ZMod p) (LinearMap.ker (Matrix.toLin' P)) ≤ 1 :=
      le_trans (Submodule.finrank_mono hsub) (finrank_span_singleton_le v1)
    omega
  obtain ⟨v2, hv2, hv2_ind⟩ := hex_v2
  have hli : LinearIndependent (ZMod p) ![v0, v1, v2] := by
    rw [linearIndependent_three_iff]
    intro c0 c1 c2 hsum
    have hP := congrArg (P *ᵥ ·) hsum
    simp only [Matrix.mulVec_add, Matrix.mulVec_smul, hv0, hv1, hv2, Matrix.mulVec_zero,
      smul_zero, add_zero] at hP
    have hc0 : c0 = 0 := by
      by_contra hne
      exact hv0_ne (by simpa [smul_smul, inv_mul_cancel₀ hne] using congrArg (c0⁻¹ • ·) hP)
    subst hc0; simp only [zero_smul, zero_add] at hsum
    have hc2 : c2 = 0 := by
      by_contra hne
      exact hv2_ind (-c2⁻¹ * c1) (by
        have := congrArg (c2⁻¹ • ·) hsum
        rw [smul_add, smul_smul, smul_smul, inv_mul_cancel₀ hne, one_smul, smul_zero] at this
        simpa [neg_mul, neg_smul] using eq_neg_of_add_eq_zero_right this)
    subst hc2; simp only [zero_smul, add_zero] at hsum
    have hc1 : c1 = 0 := by
      by_contra hne
      exact hv1_ne (by simpa [smul_smul, inv_mul_cancel₀ hne] using congrArg (c1⁻¹ • ·) hsum)
    exact ⟨rfl, hc1, rfl⟩
  refine ⟨(glOfCols v0 v1 v2 hli)⁻¹, glOfCols_mul_eq hli P (matB0 p) ?_ ?_ ?_⟩
  · simp [matB0, hv0]
  · simp [matB0, hv1]
  · simp [matB0, hv2]

/-- Canonical form for every Type B matrix: `∃ S, conj S A = l • matB0 + m • (1 - matB0)` (in fact its subring is conj to `⟨matB0⟩`). -/
private lemma canonical_B {p : ℕ} [Fact p.Prime] {A : M3 p} (hB : HasM3Type A .B) :
    ∃ S : GL (Fin 3) (ZMod p),
      Subring.closure ({conjAlgEquiv S A} : Set (M3 p)) = Subring.closure ({matB0 p} : Set (M3 p)) := by
  rcases hB with ⟨l, m, hlm, hch, hm⟩
  set P : M3 p := (l - m)⁻¹ • (A - m • (1 : M3 p))
  have hlm' : l - m ≠ 0 := sub_ne_zero.mpr hlm
  have hA_eq : A = (l - m) • P + m • (1 : M3 p) := by
    simp [P, smul_smul, mul_inv_cancel₀ hlm']
  have hP2 : P ^ 2 = P := by
    have hmin := minpoly.aeval (ZMod p) A
    rw [hm, map_mul, map_sub, map_sub, aeval_X, aeval_C, aeval_C,
        Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one] at hmin
    have h1 : (A - l • (1 : M3 p)) = (A - m • (1 : M3 p)) - (l - m) • (1 : M3 p) := by
      rw [sub_smul]; abel
    rw [h1, sub_mul] at hmin
    have h2 : (A - m • (1 : M3 p)) * (A - m • (1 : M3 p)) = (l - m) • (A - m • (1 : M3 p)) := by
      have := sub_eq_zero.mp hmin
      simpa [smul_mul_assoc, one_mul] using this
    calc P ^ 2 = ((l - m)⁻¹ * (l - m)⁻¹) • ((A - m • (1 : M3 p)) * (A - m • (1 : M3 p))) := by
            rw [sq, smul_mul_smul_comm]
      _ = ((l - m)⁻¹ * (l - m)⁻¹ * (l - m)) • (A - m • (1 : M3 p)) := by rw [h2, smul_smul]
      _ = P := by simp [P, mul_assoc, inv_mul_cancel₀ hlm']
  have hPch : P.charpoly = (X - C 1) * X ^ 2 := by
    have hmat : ∀ t : (ZMod p)[X],
        (Matrix.scalar (Fin 3) t - P.map C) =
          C (l - m)⁻¹ • (Matrix.scalar (Fin 3) (C (l - m) * t + C m) - A.map C) := by
      intro t; apply Matrix.ext; intro i j
      simp only [Matrix.sub_apply, Matrix.scalar_apply, Matrix.diagonal_apply, Matrix.map_apply,
        Matrix.smul_apply, smul_eq_mul, P, Matrix.one_apply]
      by_cases hij : i = j
      · subst hij; simp only [ite_true, map_mul, map_sub, mul_one]
        have : C (l - m)⁻¹ * C (l - m) = (1 : (ZMod p)[X]) := by rw [← map_mul, inv_mul_cancel₀ hlm', map_one]
        calc t - C (l - m)⁻¹ * (C (A i i) - C m)
            = (C (l - m)⁻¹ * C (l - m)) * t + C (l - m)⁻¹ * C m - C (l - m)⁻¹ * C (A i i) := by rw [this]; ring
          _ = C (l - m)⁻¹ * ((C l - C m) * t + C m - C (A i i)) := by rw [← map_sub]; ring
      · simp [hij, map_mul]
    have hdet := congrArg Matrix.det (hmat X)
    rw [Matrix.det_smul, Fintype.card_fin] at hdet
    change P.charpoly = _ at hdet
    have hcomp : (Matrix.scalar (Fin 3) (C (l - m) * X + C m) - A.map C).det =
        A.charpoly.comp (C (l - m) * X + C m) := by
      rw [Matrix.charpoly]
      have h := RingHom.map_det (Polynomial.compRingHom (C (l - m) * X + C m)) (Matrix.charmatrix A)
      change _ = (Polynomial.compRingHom (C (l - m) * X + C m)) (Matrix.charmatrix A).det
      rw [h]; congr 1; apply Matrix.ext; intro i j
      by_cases hij : i = j
      · subst hij; simp [Matrix.charmatrix, Polynomial.compRingHom]
      · simp [hij, Matrix.charmatrix, Polynomial.compRingHom]
    rw [hcomp, hch] at hdet
    simp only [Polynomial.mul_comp, Polynomial.pow_comp, Polynomial.sub_comp, Polynomial.X_comp,
      Polynomial.C_comp] at hdet
    have h1 : C (l - m) * X + C m - C l = C (l - m) * (X - C 1) := by
      rw [mul_sub, map_one, mul_one, map_sub]; ring
    have h2 : C (l - m) * X + C m - C m = C (l - m) * X := by ring
    rw [h1, h2] at hdet
    have hinv : C (l - m)⁻¹ ^ 3 * C (l - m) ^ 3 = (1 : (ZMod p)[X]) := by
      rw [← mul_pow, ← map_mul, inv_mul_cancel₀ hlm', map_one, one_pow]
    calc P.charpoly = C (l - m)⁻¹ ^ 3 * (C (l - m) * (X - C 1) * (C (l - m) * X) ^ 2) := hdet
      _ = (C (l - m)⁻¹ ^ 3 * C (l - m) ^ 3) * ((X - C 1) * X ^ 2) := by ring
      _ = (X - C 1) * X ^ 2 := by rw [hinv, one_mul]
  obtain ⟨S, hS⟩ := exists_conj_matB0 hPch hP2
  refine ⟨S, ?_⟩
  have h1 : conjAlgEquiv S A = (l - m) • matB0 p + m • (1 : M3 p) := by
    rw [hA_eq, map_add, map_smul, hS, map_smul, map_one]
  rw [h1, subring_closure_affine _ hlm' m]

/-- Canonical form for every Type E matrix: `∃ S, ⟨conj S A⟩ = ⟨matE01 p⟩`. -/
private lemma canonical_E {p : ℕ} [Fact p.Prime] {A : M3 p} (hE : HasM3Type A .E) :
    ∃ S : GL (Fin 3) (ZMod p),
      Subring.closure ({conjAlgEquiv S A} : Set (M3 p)) = Subring.closure ({matE01 p} : Set (M3 p)) := by
  rcases hE with ⟨l, _, hm⟩
  set N : M3 p := A - l • (1 : M3 p)
  have hN2 : N ^ 2 = 0 := by
    have := minpoly.aeval (ZMod p) A
    rw [hm, map_pow, map_sub, aeval_X, aeval_C, Algebra.algebraMap_eq_smul_one] at this
    exact this
  have hN0 : N ≠ 0 := by
    intro h0
    have hA : A = l • (1 : M3 p) := sub_eq_zero.mp h0
    have := minpoly_smul_one l
    rw [← hA, hm] at this
    have := congrArg Polynomial.natDegree this
    simp [Polynomial.natDegree_pow] at this
  obtain ⟨S, hS⟩ := exists_conj_matE01 hN0 hN2
  refine ⟨S, ?_⟩
  have h1 : conjAlgEquiv S A = (1 : ZMod p) • matE01 p + l • (1 : M3 p) := by
    have hA : A = N + l • (1 : M3 p) := (sub_add_cancel A _).symm
    rw [hA, map_add, map_smul, map_one, hS, one_smul]
  rw [h1, subring_closure_affine _ one_ne_zero l]

/-- Canonical form for every Type D matrix: `∃ S, ⟨conj S A⟩ = ⟨matD0 p⟩`. -/
private lemma canonical_D {p : ℕ} [Fact p.Prime] {A : M3 p} (hD : HasM3Type A .D) :
    ∃ S : GL (Fin 3) (ZMod p),
      Subring.closure ({conjAlgEquiv S A} : Set (M3 p)) = Subring.closure ({matD0 p} : Set (M3 p)) := by
  rcases hD with ⟨l, _, hm⟩
  set N : M3 p := A - l • (1 : M3 p)
  have hN3 : N ^ 3 = 0 := by
    have := minpoly.aeval (ZMod p) A
    rw [hm, map_pow, map_sub, aeval_X, aeval_C, Algebra.algebraMap_eq_smul_one] at this
    exact this
  have hN2_ne : N ^ 2 ≠ 0 := by
    intro h2
    have haev : aeval A ((X - C l) ^ 2) = 0 := by simpa [N, Algebra.algebraMap_eq_smul_one] using h2
    have hdvd := minpoly.dvd (ZMod p) A haev
    have hle := Polynomial.natDegree_le_of_dvd hdvd ((Polynomial.monic_X_sub_C l).pow 2).ne_zero
    rw [hm, Polynomial.natDegree_pow, Polynomial.natDegree_pow, Polynomial.natDegree_X_sub_C] at hle
    omega
  have hex_v2 : ∃ v2 : V3 p, (N ^ 2) *ᵥ v2 ≠ 0 := by
    by_contra hall; push Not at hall
    apply hN2_ne; ext i j
    have := congrFun (hall (Pi.single j 1)) i
    simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_three, Pi.single_apply] using this
  obtain ⟨v2, hv2⟩ := hex_v2
  set v1 := N *ᵥ v2
  set v0 := N *ᵥ v1
  have hv0_eq : v0 = (N ^ 2) *ᵥ v2 := by rw [sq, ← Matrix.mulVec_mulVec]
  have hv0_ne : v0 ≠ 0 := hv0_eq ▸ hv2
  have hNv0 : N *ᵥ v0 = 0 := by
    rw [hv0_eq, Matrix.mulVec_mulVec, ← pow_succ', hN3, Matrix.zero_mulVec]
  have hli : LinearIndependent (ZMod p) ![v0, v1, v2] := by
    rw [linearIndependent_three_iff]
    intro c0 c1 c2 hsum
    have h2 := congrArg ((N ^ 2) *ᵥ ·) hsum
    have hN2v0 : (N ^ 2) *ᵥ v0 = 0 := by rw [sq, ← Matrix.mulVec_mulVec, hNv0, Matrix.mulVec_zero]
    have hN2v1 : (N ^ 2) *ᵥ v1 = 0 := by
      show (N ^ 2) *ᵥ (N *ᵥ v2) = 0
      rw [Matrix.mulVec_mulVec, ← pow_succ, hN3, Matrix.zero_mulVec]
    simp only [Matrix.mulVec_add, Matrix.mulVec_smul, hN2v0, hN2v1, ← hv0_eq, Matrix.mulVec_zero,
      smul_zero, zero_add] at h2
    have hc2 : c2 = 0 := by
      by_contra hne
      exact hv0_ne (by simpa [smul_smul, inv_mul_cancel₀ hne] using congrArg (c2⁻¹ • ·) h2)
    subst hc2; simp only [zero_smul, add_zero] at hsum
    have h1 := congrArg (N *ᵥ ·) hsum
    simp only [Matrix.mulVec_add, Matrix.mulVec_smul, hNv0, Matrix.mulVec_zero, smul_zero, zero_add] at h1
    have hc1 : c1 = 0 := by
      by_contra hne
      exact hv0_ne (by simpa [smul_smul, inv_mul_cancel₀ hne] using congrArg (c1⁻¹ • ·) h1)
    subst hc1; simp only [zero_smul, add_zero] at hsum
    have hc0 : c0 = 0 := by
      by_contra hne
      exact hv0_ne (by simpa [smul_smul, inv_mul_cancel₀ hne] using congrArg (c0⁻¹ • ·) hsum)
    exact ⟨hc0, rfl, rfl⟩
  have hconj := glOfCols_mul_eq hli N (matD0 p) (by simp [matD0, hNv0]) (by simp [matD0, v0]) (by simp [matD0, v1])
  refine ⟨(glOfCols v0 v1 v2 hli)⁻¹, ?_⟩
  have hA : A = N + l • (1 : M3 p) := (sub_add_cancel A _).symm
  have h1 : conjAlgEquiv (glOfCols v0 v1 v2 hli)⁻¹ A = (1 : ZMod p) • matD0 p + l • (1 : M3 p) := by
    rw [hA, map_add, map_smul, map_one, hconj, one_smul]
  rw [h1, subring_closure_affine _ one_ne_zero l]

/-- Canonical form for every Type F matrix: `∃ S, ⟨conj S A⟩ = ⟨matF0 p⟩`. -/
private lemma canonical_F {p : ℕ} [Fact p.Prime] {A : M3 p} (hF : HasM3Type A .F) :
    ∃ S : GL (Fin 3) (ZMod p),
      Subring.closure ({conjAlgEquiv S A} : Set (M3 p)) = Subring.closure ({matF0 p} : Set (M3 p)) := by
  rcases hF with ⟨l, m, hlm, hch, hm⟩
  set N : M3 p := A - l • (1 : M3 p)
  set M : M3 p := A - m • (1 : M3 p)
  have hNM : N * M ≠ 0 := by
    intro h0
    have haev : aeval A ((X - C l) * (X - C m)) = 0 := by
      simpa [N, M, Algebra.algebraMap_eq_smul_one] using h0
    have hdvd := minpoly.dvd (ZMod p) A haev
    have hle := Polynomial.natDegree_le_of_dvd hdvd
      ((Polynomial.monic_X_sub_C l).mul (Polynomial.monic_X_sub_C m)).ne_zero
    have hdeg3 : A.charpoly.natDegree = 3 := by rw [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]
    rw [hm, hdeg3, Polynomial.natDegree_mul (Polynomial.monic_X_sub_C l).ne_zero
        (Polynomial.monic_X_sub_C m).ne_zero, Polynomial.natDegree_X_sub_C, Polynomial.natDegree_X_sub_C] at hle
    omega
  have hN2M : N ^ 2 * M = 0 := by
    have := Matrix.aeval_self_charpoly A
    rw [hch, map_mul, map_pow, map_sub, map_sub, aeval_X, aeval_C, aeval_C,
        Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one] at this
    exact this
  have hex_u : ∃ u : V3 p, (N * M) *ᵥ u ≠ 0 := by
    by_contra hall; push Not at hall
    apply hNM; ext i j
    have := congrFun (hall (Pi.single j 1)) i
    simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_three, Pi.single_apply] using this
  obtain ⟨u, hu⟩ := hex_u
  set v1 := M *ᵥ u
  set v0 := N *ᵥ v1
  have hv0_ne : v0 ≠ 0 := by simpa [v0, v1, Matrix.mulVec_mulVec] using hu
  have hNv0 : N *ᵥ v0 = 0 := by
    show N *ᵥ (N *ᵥ (M *ᵥ u)) = 0
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← sq, hN2M, Matrix.zero_mulVec]
  have hAv0 : A *ᵥ v0 = l • v0 := by
    have : A *ᵥ v0 - l • v0 = 0 := by simpa [N, sub_mulVec, Matrix.smul_mulVec] using hNv0
    exact sub_eq_zero.mp this
  have hAv1 : A *ᵥ v1 = v0 + l • v1 := by
    have : A *ᵥ v1 - l • v1 = v0 := by
      change A *ᵥ v1 - l • v1 = (A - l • (1 : M3 p)) *ᵥ v1
      rw [sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec]
    exact eq_add_of_sub_eq this
  obtain ⟨v2, hv2_ne, hAv2⟩ := (isRoot_charpoly_iff_eigvec A m).mp (by rw [Polynomial.IsRoot, hch]; simp)
  have hli : LinearIndependent (ZMod p) ![v0, v1, v2] := by
    rw [linearIndependent_three_iff]
    intro c0 c1 c2 hsum
    have hN2v0 : (N ^ 2) *ᵥ v0 = 0 := by rw [sq, ← Matrix.mulVec_mulVec, hNv0, Matrix.mulVec_zero]
    have hN2v1 : (N ^ 2) *ᵥ v1 = 0 := by
      show (N ^ 2) *ᵥ (M *ᵥ u) = 0
      rw [Matrix.mulVec_mulVec, hN2M, Matrix.zero_mulVec]
    have hN2v2 : (N ^ 2) *ᵥ v2 = ((m - l) ^ 2) • v2 := by
      have := aeval_mulVec_of_eigvec hAv2 ((X - C l) ^ 2)
      simpa [N, Algebra.algebraMap_eq_smul_one] using this
    have h2 := congrArg ((N ^ 2) *ᵥ ·) hsum
    simp only [Matrix.mulVec_add, Matrix.mulVec_smul, hN2v0, hN2v1, hN2v2, Matrix.mulVec_zero,
      smul_zero, zero_add] at h2
    have hml2 : (m - l) ^ 2 ≠ 0 := pow_ne_zero 2 (sub_ne_zero.mpr (Ne.symm hlm))
    have hc2 : c2 = 0 := by
      by_contra hne
      have hmul : c2 * (m - l) ^ 2 ≠ 0 := mul_ne_zero hne hml2
      rw [smul_smul] at h2
      have h2' := congrArg ((c2 * (m - l) ^ 2)⁻¹ • ·) h2
      rw [smul_smul, inv_mul_cancel₀ hmul, one_smul, smul_zero] at h2'
      exact hv2_ne h2'
    subst hc2; simp only [zero_smul, add_zero] at hsum
    have h1 := congrArg (N *ᵥ ·) hsum
    simp only [Matrix.mulVec_add, Matrix.mulVec_smul, hNv0, Matrix.mulVec_zero, smul_zero, zero_add] at h1
    have hc1 : c1 = 0 := by
      by_contra hne
      exact hv0_ne (by simpa [smul_smul, inv_mul_cancel₀ hne] using congrArg (c1⁻¹ • ·) h1)
    subst hc1; simp only [zero_smul, add_zero] at hsum
    have hc0 : c0 = 0 := by
      by_contra hne
      exact hv0_ne (by simpa [smul_smul, inv_mul_cancel₀ hne] using congrArg (c0⁻¹ • ·) hsum)
    exact ⟨hc0, rfl, rfl⟩
  -- Scale `v1` by `(m - l)` so `A` transforms to `l • 1 + (m - l) • matF0 p`!
  have hml : m - l ≠ 0 := sub_ne_zero.mpr (Ne.symm hlm)
  have hli' : LinearIndependent (ZMod p) ![v0, (m - l) • v1, v2] := by
    rw [linearIndependent_three_iff]
    intro c0 c1 c2 hsum
    rw [smul_smul] at hsum
    obtain ⟨h0, h1, h2⟩ := (linearIndependent_three_iff v0 v1 v2).mp hli c0 (c1 * (m - l)) c2 hsum
    exact ⟨h0, (mul_eq_zero.mp h1).resolve_right hml, h2⟩
  have hconj := glOfCols_mul_eq hli' A ((m - l) • matF0 p + l • (1 : M3 p))
    (by simp [matF0, hAv0])
    (by
      rw [Matrix.mulVec_smul, hAv1, smul_add, smul_smul, mul_comm (m - l) l, ← smul_smul]
      simp [matF0, add_comm])
    (by simp [matF0, hAv2, sub_add_cancel])
  refine ⟨(glOfCols v0 ((m - l) • v1) v2 hli')⁻¹, ?_⟩
  rw [hconj, subring_closure_affine _ hml l]

/-- Canonical form for every Type C matrix: `∃ S l m n, l ≠ m ∧ l ≠ n ∧ m ≠ n ∧ conj S A = diagonal ![l, m, n]`. -/
private lemma canonical_C {p : ℕ} [Fact p.Prime] {A : M3 p} (hC : HasM3Type A .C) :
    ∃ (S : GL (Fin 3) (ZMod p)) (l m n : ZMod p), l ≠ m ∧ l ≠ n ∧ m ≠ n ∧
      conjAlgEquiv S A = Matrix.diagonal ![l, m, n] := by
  rcases hC with ⟨l, m, n, hlm, hln, hmn, hch, _⟩
  obtain ⟨v0, hv0_ne, hv0⟩ := (isRoot_charpoly_iff_eigvec A l).mp (by rw [Polynomial.IsRoot, hch]; simp)
  obtain ⟨v1, hv1_ne, hv1⟩ := (isRoot_charpoly_iff_eigvec A m).mp (by rw [Polynomial.IsRoot, hch]; simp)
  obtain ⟨v2, hv2_ne, hv2⟩ := (isRoot_charpoly_iff_eigvec A n).mp (by rw [Polynomial.IsRoot, hch]; simp)
  have hli : LinearIndependent (ZMod p) ![v0, v1, v2] := by
    rw [linearIndependent_three_iff]
    intro c0 c1 c2 hsum
    have hf : ∀ (a b d : ZMod p) (va vb vd : V3 p),
        a ≠ b → a ≠ d → A *ᵥ va = a • va → A *ᵥ vb = b • vb → A *ᵥ vd = d • vd →
        va ≠ 0 → ∀ x y z : ZMod p, x • va + y • vb + z • vd = 0 → x = 0 := by
      intro a b d va vb vd hab had ha hb hd hva x y z hs
      have h1 := congrArg (fun w => (aeval A ((X - C b) * (X - C d))) *ᵥ w) hs
      simp only [Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_zero,
        aeval_mulVec_of_eigvec ha, aeval_mulVec_of_eigvec hb, aeval_mulVec_of_eigvec hd,
        Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C,
        sub_self, zero_mul, mul_zero, zero_smul, smul_zero, add_zero] at h1
      have hne : (a - b) * (a - d) ≠ 0 := mul_ne_zero (sub_ne_zero.mpr hab) (sub_ne_zero.mpr had)
      rw [smul_smul] at h1
      by_contra hx
      have h1' := congrArg ((x * ((a - b) * (a - d)))⁻¹ • ·) h1
      rw [smul_smul, inv_mul_cancel₀ (mul_ne_zero hx hne), one_smul, smul_zero] at h1'
      exact hva h1'
    refine ⟨hf l m n v0 v1 v2 hlm hln hv0 hv1 hv2 hv0_ne c0 c1 c2 hsum,
            hf m l n v1 v0 v2 (Ne.symm hlm) hmn hv1 hv0 hv2 hv1_ne c1 c0 c2 (by rw [← hsum]; abel),
            hf n l m v2 v0 v1 (Ne.symm hln) (Ne.symm hmn) hv2 hv0 hv1 hv2_ne c2 c0 c1 (by rw [← hsum]; abel)⟩
  refine ⟨(glOfCols v0 v1 v2 hli)⁻¹, l, m, n, hlm, hln, hmn,
    glOfCols_mul_eq hli A (Matrix.diagonal ![l, m, n]) ?_ ?_ ?_⟩
  · simp [hv0]
  · simp [hv1]
  · simp [hv2]

/-- Canonical form for every Type G matrix: `∃ S, conj S A = matComp3 A.charpoly`. -/
private lemma canonical_G {p : ℕ} [Fact p.Prime] {A : M3 p} (hG : HasM3Type A .G) :
    ∃ S : GL (Fin 3) (ZMod p), conjAlgEquiv S A = matComp3 A.charpoly := by
  rcases hG with ⟨hirr, hm⟩
  have hPmon : A.charpoly.Monic := Matrix.charpoly_monic A
  have hPdeg : A.charpoly.natDegree = 3 := by rw [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]
  set v0 : V3 p := Pi.single 0 1
  have hv0_ne : v0 ≠ 0 := by intro h; have := congrFun h 0; simp [v0] at this
  set v1 := A *ᵥ v0
  set v2 := A *ᵥ v1
  have hli : LinearIndependent (ZMod p) ![v0, v1, v2] := by
    rw [linearIndependent_three_iff]
    intro c0 c1 c2 hsum
    let f : (ZMod p)[X] := C c0 + C c1 * X + C c2 * X ^ 2
    have hfv0 : (aeval A f) *ᵥ v0 = 0 := by
      have h1 : (aeval A f) *ᵥ v0 = c0 • v0 + c1 • v1 + c2 • v2 := by
        simp only [f, map_add, map_mul, aeval_C, aeval_X, Algebra.algebraMap_eq_smul_one,
          Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, smul_mul_assoc, one_mul,
          sq, ← Matrix.mulVec_mulVec, v1, v2]
      rw [h1, hsum]
    have hf0 : f = 0 := by
      by_contra hfne
      have hfdeg : f.natDegree ≤ 2 := by
        refine le_trans (Polynomial.natDegree_add_le _ _) (max_le ?_ ?_)
        · refine le_trans (Polynomial.natDegree_add_le _ _) (max_le (by simp) ?_)
          exact le_trans (Polynomial.natDegree_mul_le) (by simp)
        · exact le_trans (Polynomial.natDegree_mul_le) (by simp)
      have hndvd : ¬ A.charpoly ∣ f := fun hdvd => by
        have := Polynomial.natDegree_le_of_dvd hdvd hfne; omega
      have hcop : IsCoprime A.charpoly f :=
        (hirr.coprime_iff_not_dvd.mpr hndvd)
      obtain ⟨u, w, huw⟩ := hcop
      have h1 : (aeval A (u * A.charpoly + w * f)) *ᵥ v0 = v0 := by
        rw [huw, map_one, Matrix.one_mulVec]
      rw [map_add, map_mul, map_mul, Matrix.aeval_self_charpoly, mul_zero, zero_add,
          ← Matrix.mulVec_mulVec, hfv0, Matrix.mulVec_zero] at h1
      exact hv0_ne h1.symm
    have h0 : c0 = 0 := by have := congrArg (fun g : (ZMod p)[X] => g.coeff 0) hf0; simpa [f] using this
    have h1 : c1 = 0 := by have := congrArg (fun g : (ZMod p)[X] => g.coeff 1) hf0; simpa [f] using this
    have h2 : c2 = 0 := by have := congrArg (fun g : (ZMod p)[X] => g.coeff 2) hf0; simpa [f] using this
    exact ⟨h0, h1, h2⟩
  have hP_exp : A.charpoly = X ^ 3 + C (A.charpoly.coeff 2) * X ^ 2 +
      C (A.charpoly.coeff 1) * X + C (A.charpoly.coeff 0) := by
    ext k
    by_cases hk : k ≤ 3
    · interval_cases k <;> simp [Polynomial.coeff_X, Polynomial.coeff_C, Polynomial.coeff_X_pow]
      · have : A.charpoly.coeff 3 = 1 := by simpa [Polynomial.Monic, Polynomial.leadingCoeff, hPdeg] using hPmon
        exact this
    · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)]
      simp [Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_C, show k ≠ 3 by omega,
            show k ≠ 2 by omega, show 1 ≠ k by omega, show k ≠ 0 by omega]
  have hAv2 : A *ᵥ v2 = (-A.charpoly.coeff 0) • v0 + (-A.charpoly.coeff 1) • v1 + (-A.charpoly.coeff 2) • v2 := by
    have haev := congrArg (· *ᵥ v0) (Matrix.aeval_self_charpoly A)
    rw [hP_exp] at haev
    simp only [map_add, map_mul, map_one, aeval_X, aeval_C, Algebra.algebraMap_eq_smul_one,
      Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, Matrix.zero_mulVec,
      smul_mul_assoc, one_mul, pow_succ', pow_zero, ← Matrix.mulVec_mulVec] at haev
    change A *ᵥ v2 + A.charpoly.coeff 2 • v2 + A.charpoly.coeff 1 • v1 + A.charpoly.coeff 0 • v0 = 0 at haev
    have := eq_neg_of_add_eq_zero_left haev
    ext i
    have hi := congrFun haev i
    simp only [Pi.add_apply, Pi.smul_apply, Pi.zero_apply, smul_eq_mul] at hi ⊢
    linear_combination hi
  refine ⟨(glOfCols v0 v1 v2 hli)⁻¹, glOfCols_mul_eq hli A (matComp3 A.charpoly) ?_ ?_ ?_⟩
  · simp [matComp3, v1]
  · simp [matComp3, v2]
  · simpa [matComp3] using hAv2

/-- Canonical form for every Type H matrix: `∃ S l q, q.Monic ∧ q.natDegree = 2 ∧ Irreducible q ∧ conj S A = matH0 l q`. -/
private lemma canonical_H {p : ℕ} [Fact p.Prime] {A : M3 p} (hH : HasM3Type A .H) :
    ∃ (S : GL (Fin 3) (ZMod p)) (l : ZMod p) (q : (ZMod p)[X]),
      q.Monic ∧ q.natDegree = 2 ∧ Irreducible q ∧ conjAlgEquiv S A = matH0 l q := by
  rcases hH with ⟨l, q, hqmon, hqdeg, hqirr, hch, _⟩
  obtain ⟨v0, hv0_ne, hv0⟩ := (isRoot_charpoly_iff_eigvec A l).mp (by rw [Polynomial.IsRoot, hch]; simp)
  have hAl_ne : A - l • (1 : M3 p) ≠ 0 := by
    intro h0
    have hA : A = l • (1 : M3 p) := sub_eq_zero.mp h0
    have := charpoly_smul_one l
    rw [← hA, hch] at this
    have hqeq : q = (X - C l) ^ 2 := mul_left_cancel₀ (Polynomial.monic_X_sub_C l).ne_zero (by rw [this]; ring)
    rw [hqeq, sq] at hqirr
    exact not_irreducible_mul (Polynomial.not_isUnit_X_sub_C l) (Polynomial.not_isUnit_X_sub_C l) hqirr
  have hex_u : ∃ u : V3 p, (A - l • (1 : M3 p)) *ᵥ u ≠ 0 := by
    by_contra hall; push Not at hall
    apply hAl_ne; ext i j
    have := congrFun (hall (Pi.single j 1)) i
    simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_three, Pi.single_apply] using this
  obtain ⟨u, hu⟩ := hex_u
  set v1 := (A - l • (1 : M3 p)) *ᵥ u
  set v2 := A *ᵥ v1
  have hqv1 : (aeval A q) *ᵥ v1 = 0 := by
    have haev := Matrix.aeval_self_charpoly A
    rw [hch, mul_comm, map_mul, map_sub, aeval_X, aeval_C, Algebra.algebraMap_eq_smul_one] at haev
    rw [Matrix.mulVec_mulVec, haev, Matrix.zero_mulVec]
  have hqno : ∀ x : ZMod p, ¬ q.IsRoot x := fun x hx => by
    obtain ⟨R, hR⟩ := Polynomial.dvd_iff_isRoot.mpr hx
    rcases hqirr.isUnit_or_isUnit hR with hu | hu
    · exact Polynomial.not_isUnit_X_sub_C x hu
    · have := congrArg Polynomial.natDegree hR
      rw [hqdeg, Polynomial.natDegree_mul (Polynomial.monic_X_sub_C x).ne_zero hu.ne_zero,
          Polynomial.natDegree_X_sub_C, Polynomial.natDegree_eq_zero_of_isUnit hu] at this
      omega
  have hli : LinearIndependent (ZMod p) ![v0, v1, v2] := by
    rw [linearIndependent_three_iff]
    intro c0 c1 c2 hsum
    have hq_sum := congrArg ((aeval A q) *ᵥ ·) hsum
    have hqv2 : (aeval A q) *ᵥ v2 = 0 := by
      have hcomm : aeval A q * A = A * aeval A q := (commute_aeval_self A q).eq
      rw [Matrix.mulVec_mulVec, hcomm, ← Matrix.mulVec_mulVec, hqv1, Matrix.mulVec_zero]
    simp only [Matrix.mulVec_add, Matrix.mulVec_smul, aeval_mulVec_of_eigvec hv0, hqv1, hqv2,
      Matrix.mulVec_zero, smul_zero, add_zero] at hq_sum
    have hql_ne : q.eval l ≠ 0 := hqno l
    have hc0 : c0 = 0 := by
      by_contra hne
      rw [smul_smul] at hq_sum
      have h0 := congrArg ((c0 * q.eval l)⁻¹ • ·) hq_sum
      rw [smul_smul, inv_mul_cancel₀ (mul_ne_zero hne hql_ne), one_smul, smul_zero] at h0
      exact hv0_ne h0
    subst hc0; simp only [zero_smul, zero_add] at hsum
    have hc2 : c2 = 0 := by
      by_contra hne
      have hAv1 : A *ᵥ v1 = (-c2⁻¹ * c1) • v1 := by
        have := congrArg (c2⁻¹ • ·) hsum
        rw [smul_add, smul_smul, smul_smul, inv_mul_cancel₀ hne, one_smul, smul_zero] at this
        simpa [neg_mul, neg_smul] using eq_neg_of_add_eq_zero_right this
      have hqev := aeval_mulVec_of_eigvec hAv1 q
      rw [hqv1] at hqev
      have h0 := congrArg ((q.eval (-c2⁻¹ * c1))⁻¹ • ·) hqev.symm
      rw [smul_smul, inv_mul_cancel₀ (hqno (-c2⁻¹ * c1)), one_smul, smul_zero] at h0
      exact hu h0
    subst hc2; simp only [zero_smul, add_zero] at hsum
    have hc1 : c1 = 0 := by
      by_contra hne
      exact hu (by simpa [smul_smul, inv_mul_cancel₀ hne] using congrArg (c1⁻¹ • ·) hsum)
    exact ⟨rfl, hc1, rfl⟩
  have hq_exp : q = X ^ 2 + C (q.coeff 1) * X + C (q.coeff 0) := by
    ext k
    by_cases hk : k ≤ 2
    · interval_cases k <;> simp [Polynomial.coeff_X, Polynomial.coeff_C, Polynomial.coeff_X_pow]
      · simpa [Polynomial.Monic, Polynomial.leadingCoeff, hqdeg] using hqmon
    · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)]
      simp [Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_C,
            show k ≠ 2 by omega, show 1 ≠ k by omega, show k ≠ 0 by omega]
  have hAv2 : A *ᵥ v2 = (-q.coeff 0) • v1 + (-q.coeff 1) • v2 := by
    have h1 := hqv1
    rw [hq_exp] at h1
    simp only [map_add, map_mul, aeval_X, aeval_C, Algebra.algebraMap_eq_smul_one,
      Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, smul_mul_assoc, one_mul,
      sq, ← Matrix.mulVec_mulVec] at h1
    change A *ᵥ v2 + q.coeff 1 • v2 + q.coeff 0 • v1 = 0 at h1
    ext i
    have hi := congrFun h1 i
    simp only [Pi.add_apply, Pi.smul_apply, Pi.zero_apply, smul_eq_mul] at hi ⊢
    linear_combination hi
  refine ⟨(glOfCols v0 v1 v2 hli)⁻¹, l, q, hqmon, hqdeg, hqirr,
    glOfCols_mul_eq hli A (matH0 l q) ?_ ?_ ?_⟩
  · simp [matH0, hv0]
  · simp [matH0, v2]
  · simp [matH0, hAv2]

/-! ### Section 4: Single Generator Counts `gen_(X)` for All 8 Types -/

private lemma card_singleGens_conj {p : ℕ} [Fact p.Prime] (S : GL (Fin 3) (ZMod p)) (A : M3 p) :
    Nat.card (SingleGens ⟨Subring.closure ({conjAlgEquiv S A} : Set (M3 p)), ⟨_, rfl⟩⟩) =
      Nat.card (SingleGens ⟨Subring.closure ({A} : Set (M3 p)), ⟨_, rfl⟩⟩) := by
  classical
  refine Nat.card_congr ?_
  refine Equiv.ofBijective (fun X => ⟨(conjAlgEquiv S).symm X.val, ?_⟩) ⟨?_, ?_⟩
  · have hX : Subring.closure ({X.val} : Set (M3 p)) = Subring.closure ({conjAlgEquiv S A} : Set (M3 p)) := X.prop
    have h1 := congrArg (Subring.map (conjAlgEquiv S).symm.toRingHom) hX
    rw [subring_map_closure, subring_map_closure, Set.image_singleton, Set.image_singleton] at h1
    change Subring.closure ({(conjAlgEquiv S).symm X.val} : Set (M3 p)) =
      Subring.closure ({(conjAlgEquiv S).symm (conjAlgEquiv S A)} : Set (M3 p)) at h1
    rw [AlgEquiv.symm_apply_apply] at h1
    exact h1
  · intro X Y h; exact Subtype.ext ((conjAlgEquiv S).symm.injective (congrArg Subtype.val h))
  · intro Y
    refine ⟨⟨conjAlgEquiv S Y.val, ?_⟩, Subtype.ext (by simp)⟩
    have hY : Subring.closure ({Y.val} : Set (M3 p)) = Subring.closure ({A} : Set (M3 p)) := Y.prop
    have h1 := congrArg (Subring.map (conjAlgEquiv S).toRingHom) hY
    rw [subring_map_closure, subring_map_closure, Set.image_singleton, Set.image_singleton] at h1
    exact h1

/-- Elements of `Subring.closure {A}` when `minpoly` has degree `d` are uniquely `∑_{i < d} c_i A^i`. -/
private lemma mem_closure_deg2 {p : ℕ} [Fact p.Prime] {A : M3 p} {a b : ZMod p}
    (h2 : A ^ 2 = a • A + b • (1 : M3 p)) :
    ∀ B : M3 p, B ∈ Subring.closure ({A} : Set (M3 p)) ↔ ∃ c0 c1 : ZMod p, B = c0 • (1 : M3 p) + c1 • A := by
  intro B
  constructor
  · intro hB
    obtain ⟨f, rfl⟩ := (mem_subring_closure_iff_aeval A B).mp hB
    clear hB
    induction f using Polynomial.induction_on' with
    | add f g hf hg =>
      obtain ⟨c0, c1, hc⟩ := hf
      obtain ⟨d0, d1, hd⟩ := hg
      refine ⟨c0 + d0, c1 + d1, ?_⟩
      rw [map_add, hc, hd, add_smul, add_smul]; abel
    | monomial n r =>
      have hpow : ∀ k : ℕ, ∃ c0 c1 : ZMod p, A ^ k = c0 • (1 : M3 p) + c1 • A := by
        intro k
        induction k with
        | zero => exact ⟨1, 0, by simp⟩
        | succ k ih =>
          obtain ⟨c0, c1, hc⟩ := ih
          refine ⟨c1 * b, c0 + c1 * a, ?_⟩
          rw [pow_succ, hc, add_mul, smul_mul_assoc, one_mul, smul_mul_assoc, ← sq, h2,
              smul_add, smul_smul, smul_smul, add_smul]
          abel
      obtain ⟨c0, c1, hc⟩ := hpow n
      refine ⟨r * c0, r * c1, ?_⟩
      rw [aeval_monomial, Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul, hc,
          smul_add, smul_smul, smul_smul]
  · rintro ⟨c0, c1, rfl⟩
    exact add_mem (smul_one_mem_subring _ c0) (smul_mem_subring _ c1 (Subring.subset_closure rfl))

private lemma mem_closure_deg3 {p : ℕ} [Fact p.Prime] {A : M3 p} {a b c : ZMod p}
    (h3 : A ^ 3 = a • A ^ 2 + b • A + c • (1 : M3 p)) :
    ∀ B : M3 p, B ∈ Subring.closure ({A} : Set (M3 p)) ↔
      ∃ c0 c1 c2 : ZMod p, B = c0 • (1 : M3 p) + c1 • A + c2 • A ^ 2 := by
  intro B
  constructor
  · intro hB
    obtain ⟨f, rfl⟩ := (mem_subring_closure_iff_aeval A B).mp hB
    clear hB
    induction f using Polynomial.induction_on' with
    | add f g hf hg =>
      obtain ⟨c0, c1, c2, hc⟩ := hf
      obtain ⟨d0, d1, d2, hd⟩ := hg
      refine ⟨c0 + d0, c1 + d1, c2 + d2, ?_⟩
      rw [map_add, hc, hd, add_smul, add_smul, add_smul]; abel
    | monomial n r =>
      have hpow : ∀ k : ℕ, ∃ c0 c1 c2 : ZMod p, A ^ k = c0 • (1 : M3 p) + c1 • A + c2 • A ^ 2 := by
        intro k
        induction k with
        | zero => exact ⟨1, 0, 0, by simp⟩
        | succ k ih =>
          obtain ⟨c0, c1, c2, hc⟩ := ih
          refine ⟨c2 * c, c0 + c2 * b, c1 + c2 * a, ?_⟩
          rw [pow_succ, hc, add_mul, add_mul, smul_mul_assoc, one_mul, smul_mul_assoc, ← sq,
              smul_mul_assoc, ← pow_succ, h3, smul_add, smul_add, smul_smul, smul_smul, smul_smul,
              add_smul, add_smul]
          abel
      obtain ⟨c0, c1, c2, hc⟩ := hpow n
      refine ⟨r * c0, r * c1, r * c2, ?_⟩
      rw [aeval_monomial, Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul, hc,
          smul_add, smul_add, smul_smul, smul_smul, smul_smul]
  · rintro ⟨c0, c1, c2, rfl⟩
    set S := Subring.closure ({A} : Set (M3 p))
    have hA : A ∈ S := Subring.subset_closure rfl
    have hA2 : A ^ 2 ∈ S := by rw [sq]; exact mul_mem hA hA
    exact add_mem (add_mem (smul_one_mem_subring S c0) (smul_mem_subring S c1 hA))
      (smul_mem_subring S c2 hA2)

private lemma card_singleGens_A {p : ℕ} [Fact p.Prime] {A : M3 p} (htA : HasM3Type A .A) :
    Nat.card (SingleGens ⟨Subring.closure ({A} : Set (M3 p)), ⟨A, rfl⟩⟩) = expectedGenCount p .A := by
  classical
  rcases htA with ⟨l, _, hm⟩
  have hA_eq : A = l • (1 : M3 p) := by
    have := minpoly.aeval (ZMod p) A
    rw [hm, map_sub, aeval_X, aeval_C, Algebra.algebraMap_eq_smul_one, sub_eq_zero] at this
    exact this
  have hcl : Subring.closure ({A} : Set (M3 p)) = Subring.closure ({(0 : M3 p)} : Set (M3 p)) := by
    rw [subring_closure_eq_iff]
    refine ⟨zero_mem _, ?_⟩
    rw [hA_eq]; exact smul_one_mem_subring _ l
  have hmem : ∀ B : M3 p, B ∈ Subring.closure ({(0 : M3 p)} : Set (M3 p)) ↔ ∃ c : ZMod p, B = c • (1 : M3 p) := by
    intro B; constructor
    · intro hB
      obtain ⟨f, rfl⟩ := (mem_subring_closure_iff_aeval (0 : M3 p) B).mp hB
      clear hB
      refine ⟨f.coeff 0, ?_⟩
      induction f using Polynomial.induction_on' with
      | add g h hg hh => rw [map_add, hg, hh, Polynomial.coeff_add, add_smul]
      | monomial n r =>
        cases n with
        | zero => simp [Algebra.algebraMap_eq_smul_one]
        | succ n => simp [pow_succ]
    · rintro ⟨c, rfl⟩; exact smul_one_mem_subring _ c
  have hbij : SingleGens ⟨Subring.closure ({A} : Set (M3 p)), ⟨A, rfl⟩⟩ ≃ ZMod p :=
    (Equiv.ofBijective (fun c : ZMod p => (⟨c • (1 : M3 p), by
      show Subring.closure ({c • (1 : M3 p)} : Set (M3 p)) = Subring.closure ({A} : Set (M3 p))
      rw [hcl, subring_closure_eq_iff]
      exact ⟨zero_mem _, smul_one_mem_subring _ c⟩⟩ : SingleGens ⟨Subring.closure ({A} : Set (M3 p)), ⟨A, rfl⟩⟩))
      ⟨fun c₁ c₂ h => by
        have := congrArg (fun x => x.val 0 0) h; simpa using this,
       fun B => by
        have hBp : Subring.closure ({B.val} : Set (M3 p)) = Subring.closure ({A} : Set (M3 p)) := B.prop
        have hB : B.val ∈ Subring.closure ({(0 : M3 p)} : Set (M3 p)) :=
          (SetLike.ext_iff.mp (hBp.trans hcl) B.val).mp (Subring.subset_closure rfl)
        obtain ⟨c, hc⟩ := (hmem B.val).mp hB
        exact ⟨c, Subtype.ext hc.symm⟩⟩).symm
  rw [Nat.card_congr hbij, Nat.card_zmod]; rfl

private lemma card_singleGens_B {p : ℕ} [Fact p.Prime] {A : M3 p} (htA : HasM3Type A .B) :
    Nat.card (SingleGens ⟨Subring.closure ({A} : Set (M3 p)), ⟨A, rfl⟩⟩) = expectedGenCount p .B := by
  classical
  obtain ⟨S, hS⟩ := canonical_B htA
  rw [← card_singleGens_conj S A]
  have hveq : (⟨Subring.closure ({conjAlgEquiv S A} : Set (M3 p)), ⟨_, rfl⟩⟩ : UCCGVert p) =
      ⟨Subring.closure ({matB0 p} : Set (M3 p)), ⟨_, rfl⟩⟩ := Subtype.ext hS
  rw [hveq]
  have hsq : matB0 p ^ 2 = (1 : ZMod p) • matB0 p + (0 : ZMod p) • (1 : M3 p) := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [matB0, sq, Matrix.mul_apply, Fin.sum_univ_three]
  have hbij : SingleGens ⟨Subring.closure ({matB0 p} : Set (M3 p)), ⟨_, rfl⟩⟩ ≃
      ZMod p × { a : ZMod p // a ≠ 0 } :=
    (Equiv.ofBijective (fun x : ZMod p × { a : ZMod p // a ≠ 0 } =>
      (⟨x.2.val • matB0 p + x.1 • (1 : M3 p), subring_closure_affine (matB0 p) x.2.prop x.1⟩ :
        SingleGens ⟨Subring.closure ({matB0 p} : Set (M3 p)), ⟨_, rfl⟩⟩))
      ⟨fun x y h => by
        have h00 := congrArg (fun z => z.val 0 0) h
        have h11 := congrArg (fun z => z.val 1 1) h
        simp [matB0] at h00 h11
        exact Prod.ext h11 (Subtype.ext (by linear_combination h00 - h11)),
       fun B => by
        have hBp : Subring.closure ({B.val} : Set (M3 p)) = Subring.closure ({matB0 p} : Set (M3 p)) := B.prop
        have hB : B.val ∈ Subring.closure ({matB0 p} : Set (M3 p)) :=
          (SetLike.ext_iff.mp hBp B.val).mp (Subring.subset_closure rfl)
        obtain ⟨c0, c1, hc⟩ := (mem_closure_deg2 hsq B.val).mp hB
        have hc1 : c1 ≠ 0 := by
          intro h0; subst h0; simp only [zero_smul, add_zero] at hc
          have hB_A : HasM3Type B.val .A := ⟨c0, hc ▸ charpoly_smul_one c0, hc ▸ minpoly_smul_one c0⟩
          have hmatB : HasM3Type (matB0 p) .B :=
            (same_type_of_subring_eq hS .B).mp ((hasM3Type_conj S A .B).mpr htA)
          have hB_B := (same_type_of_subring_eq hBp .B).mpr hmatB
          exact M3Type.noConfusion (hasM3Type_unique hB_A hB_B)
        exact ⟨(c0, ⟨c1, hc1⟩), Subtype.ext (by rw [hc, add_comm])⟩⟩).symm
  rw [Nat.card_congr hbij, Nat.card_prod, Nat.card_zmod]
  have hne0 : Nat.card { a : ZMod p // a ≠ 0 } = p - 1 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype_compl, ZMod.card, Fintype.card_unique]
  rw [hne0]; rfl

private lemma card_singleGens_E {p : ℕ} [Fact p.Prime] {A : M3 p} (htA : HasM3Type A .E) :
    Nat.card (SingleGens ⟨Subring.closure ({A} : Set (M3 p)), ⟨A, rfl⟩⟩) = expectedGenCount p .E := by
  classical
  obtain ⟨S, hS⟩ := canonical_E htA
  rw [← card_singleGens_conj S A]
  have hveq : (⟨Subring.closure ({conjAlgEquiv S A} : Set (M3 p)), ⟨_, rfl⟩⟩ : UCCGVert p) =
      ⟨Subring.closure ({matE01 p} : Set (M3 p)), ⟨_, rfl⟩⟩ := Subtype.ext hS
  rw [hveq]
  have hsq : matE01 p ^ 2 = (0 : ZMod p) • matE01 p + (0 : ZMod p) • (1 : M3 p) := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [matE01, sq, Matrix.mul_apply, Fin.sum_univ_three]
  have hbij : SingleGens ⟨Subring.closure ({matE01 p} : Set (M3 p)), ⟨_, rfl⟩⟩ ≃
      ZMod p × { a : ZMod p // a ≠ 0 } :=
    (Equiv.ofBijective (fun x : ZMod p × { a : ZMod p // a ≠ 0 } =>
      (⟨x.2.val • matE01 p + x.1 • (1 : M3 p), subring_closure_affine (matE01 p) x.2.prop x.1⟩ :
        SingleGens ⟨Subring.closure ({matE01 p} : Set (M3 p)), ⟨_, rfl⟩⟩))
      ⟨fun x y h => by
        have h00 := congrArg (fun z => z.val 0 0) h
        have h01 := congrArg (fun z => z.val 0 1) h
        simp [matE01] at h00 h01
        exact Prod.ext h00 (Subtype.ext h01),
       fun B => by
        have hBp : Subring.closure ({B.val} : Set (M3 p)) = Subring.closure ({matE01 p} : Set (M3 p)) := B.prop
        have hB : B.val ∈ Subring.closure ({matE01 p} : Set (M3 p)) :=
          (SetLike.ext_iff.mp hBp B.val).mp (Subring.subset_closure rfl)
        obtain ⟨c0, c1, hc⟩ := (mem_closure_deg2 hsq B.val).mp hB
        have hc1 : c1 ≠ 0 := by
          intro h0; subst h0; simp only [zero_smul, add_zero] at hc
          have hB_A : HasM3Type B.val .A := ⟨c0, hc ▸ charpoly_smul_one c0, hc ▸ minpoly_smul_one c0⟩
          have hmatE : HasM3Type (matE01 p) .E := (same_type_of_subring_eq hS .E).mp ((hasM3Type_conj S A .E).mpr htA)
          have hB_E := (same_type_of_subring_eq hBp .E).mpr hmatE
          exact M3Type.noConfusion (hasM3Type_unique hB_A hB_E)
        exact ⟨(c0, ⟨c1, hc1⟩), Subtype.ext (by rw [hc, add_comm])⟩⟩).symm
  rw [Nat.card_congr hbij, Nat.card_prod, Nat.card_zmod]
  have hne0 : Nat.card { a : ZMod p // a ≠ 0 } = p - 1 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype_compl, ZMod.card, Fintype.card_unique]
  rw [hne0]; rfl

private lemma card_singleGens_C {p : ℕ} [Fact p.Prime] {A : M3 p} (htA : HasM3Type A .C) :
    Nat.card (SingleGens ⟨Subring.closure ({A} : Set (M3 p)), ⟨A, rfl⟩⟩) = expectedGenCount p .C := by
  classical
  obtain ⟨S, l, m, n, hlm, hln, hmn, hS⟩ := canonical_C htA
  rw [← card_singleGens_conj S A]
  have hveq : (⟨Subring.closure ({conjAlgEquiv S A} : Set (M3 p)), ⟨_, rfl⟩⟩ : UCCGVert p) =
      ⟨Subring.closure ({Matrix.diagonal ![l, m, n]} : Set (M3 p)), ⟨_, rfl⟩⟩ := Subtype.ext (by rw [hS])
  rw [hveq]
  have hdiag_mem : ∀ a b c : ZMod p, Matrix.diagonal ![a, b, c] ∈ Subring.closure ({Matrix.diagonal ![l, m, n]} : Set (M3 p)) := by
    intro a b c
    let f : (ZMod p)[X] :=
      C (a * ((l - m) * (l - n))⁻¹) * ((X - C m) * (X - C n)) +
      C (b * ((m - l) * (m - n))⁻¹) * ((X - C l) * (X - C n)) +
      C (c * ((n - l) * (n - m))⁻¹) * ((X - C l) * (X - C m))
    have haev : aeval (Matrix.diagonal ![l, m, n]) f = Matrix.diagonal ![a, b, c] := by
      have hdiag_aeval : ∀ g : (ZMod p)[X], aeval (Matrix.diagonal ![l, m, n]) g =
          Matrix.diagonal ![g.eval l, g.eval m, g.eval n] := fun g => by
        induction g using Polynomial.induction_on' with
        | add g1 g2 h1 h2 =>
          rw [map_add, h1, h2]; ext i j; fin_cases i <;> fin_cases j <;> simp
        | monomial k r =>
          rw [aeval_monomial, Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul, Matrix.diagonal_pow]
          ext i j; fin_cases i <;> fin_cases j <;> simp [Polynomial.eval_monomial]
      rw [hdiag_aeval]
      have hlm' : l - m ≠ 0 := sub_ne_zero.mpr hlm
      have hln' : l - n ≠ 0 := sub_ne_zero.mpr hln
      have hmn' : m - n ≠ 0 := sub_ne_zero.mpr hmn
      have hml' : m - l ≠ 0 := sub_ne_zero.mpr (Ne.symm hlm)
      have hnl' : n - l ≠ 0 := sub_ne_zero.mpr (Ne.symm hln)
      have hnm' : n - m ≠ 0 := sub_ne_zero.mpr (Ne.symm hmn)
      ext i j; fin_cases i <;> fin_cases j <;> (simp [f]; try field_simp [hlm', hln', hmn', hml', hnl', hnm'])
    exact (mem_subring_closure_iff_aeval _ _).mpr ⟨f, haev⟩
  have hmem_diag : ∀ B : M3 p, B ∈ Subring.closure ({Matrix.diagonal ![l, m, n]} : Set (M3 p)) ↔
      ∃ a b c : ZMod p, B = Matrix.diagonal ![a, b, c] := by
    intro B; constructor
    · intro hB
      obtain ⟨f, rfl⟩ := (mem_subring_closure_iff_aeval _ B).mp hB
      clear hB
      refine ⟨f.eval l, f.eval m, f.eval n, ?_⟩
      induction f using Polynomial.induction_on' with
      | add g1 g2 h1 h2 => rw [map_add, h1, h2]; ext i j; fin_cases i <;> fin_cases j <;> simp
      | monomial k r =>
        rw [aeval_monomial, Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul, Matrix.diagonal_pow]
        ext i j; fin_cases i <;> fin_cases j <;> simp [Polynomial.eval_monomial]
    · rintro ⟨a, b, c, rfl⟩; exact hdiag_mem a b c
  have hgen_iff : ∀ a b c : ZMod p,
      Subring.closure ({Matrix.diagonal ![a, b, c]} : Set (M3 p)) =
        Subring.closure ({Matrix.diagonal ![l, m, n]} : Set (M3 p)) ↔ a ≠ b ∧ a ≠ c ∧ b ≠ c := by
    intro a b c; constructor
    · intro hEq
      have hC : HasM3Type (Matrix.diagonal ![a, b, c]) .C :=
        (same_type_of_subring_eq hEq .C).mpr (hS ▸ (hasM3Type_conj S A .C).mpr htA)
      have hch : (Matrix.diagonal ![a, b, c]).charpoly = (X - C a) * (X - C b) * (X - C c) := by
        rw [Matrix.charpoly, Matrix.det_fin_three]
        simp [Matrix.charmatrix]
      have h3 := (hasM3Type_invariants hC).2.1
      dsimp only at h3
      rw [hch] at h3
      have hfilt : (Finset.univ.filter fun x : ZMod p => ((X - C a) * (X - C b) * (X - C c)).IsRoot x) = {a, b, c} := by
        ext x; simp [Polynomial.IsRoot, sub_eq_zero, or_assoc]
      rw [hfilt] at h3
      refine ⟨?_, ?_, ?_⟩
      · intro hab; subst hab
        have : ({a, a, c} : Finset (ZMod p)) = {a, c} := by ext x; simp
        rw [this] at h3; have := Finset.card_le_two (a := a) (b := c); omega
      · intro hac; subst hac
        have : ({a, b, a} : Finset (ZMod p)) = {a, b} := by ext x; simp [or_comm]
        rw [this] at h3; have := Finset.card_le_two (a := a) (b := b); omega
      · intro hbc; subst hbc
        have : ({a, b, b} : Finset (ZMod p)) = {a, b} := by ext x; simp
        rw [this] at h3; have := Finset.card_le_two (a := a) (b := b); omega
    · rintro ⟨hab, hac, hbc⟩
      rw [subring_closure_eq_iff]
      refine ⟨?_, hdiag_mem a b c⟩
      let f : (ZMod p)[X] :=
        C (l * ((a - b) * (a - c))⁻¹) * ((X - C b) * (X - C c)) +
        C (m * ((b - a) * (b - c))⁻¹) * ((X - C a) * (X - C c)) +
        C (n * ((c - a) * (c - b))⁻¹) * ((X - C a) * (X - C b))
      refine (mem_subring_closure_iff_aeval _ _).mpr ⟨f, ?_⟩
      have hdiag_aeval : ∀ g : (ZMod p)[X], aeval (Matrix.diagonal ![a, b, c]) g =
          Matrix.diagonal ![g.eval a, g.eval b, g.eval c] := fun g => by
        induction g using Polynomial.induction_on' with
        | add g1 g2 h1 h2 => rw [map_add, h1, h2]; ext i j; fin_cases i <;> fin_cases j <;> simp
        | monomial k r =>
          rw [aeval_monomial, Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul, Matrix.diagonal_pow]
          ext i j; fin_cases i <;> fin_cases j <;> simp [Polynomial.eval_monomial]
      rw [hdiag_aeval]
      have hab' : a - b ≠ 0 := sub_ne_zero.mpr hab
      have hac' : a - c ≠ 0 := sub_ne_zero.mpr hac
      have hbc' : b - c ≠ 0 := sub_ne_zero.mpr hbc
      have hba' : b - a ≠ 0 := sub_ne_zero.mpr (Ne.symm hab)
      have hca' : c - a ≠ 0 := sub_ne_zero.mpr (Ne.symm hac)
      have hcb' : c - b ≠ 0 := sub_ne_zero.mpr (Ne.symm hbc)
      ext i j; fin_cases i <;> fin_cases j <;> (simp [f]; try field_simp [hab', hac', hbc', hba', hca', hcb'])
  let T3 := { x : ZMod p × ZMod p × ZMod p // x.1 ≠ x.2.1 ∧ x.1 ≠ x.2.2 ∧ x.2.1 ≠ x.2.2 }
  have hbij : SingleGens ⟨Subring.closure ({Matrix.diagonal ![l, m, n]} : Set (M3 p)), ⟨_, rfl⟩⟩ ≃ T3 :=
    (Equiv.ofBijective (fun x : T3 =>
      (⟨Matrix.diagonal ![x.val.1, x.val.2.1, x.val.2.2], (hgen_iff _ _ _).mpr x.prop⟩ :
        SingleGens ⟨Subring.closure ({Matrix.diagonal ![l, m, n]} : Set (M3 p)), ⟨_, rfl⟩⟩))
      ⟨fun x y h => by
        have h0 := congrArg (fun z => z.val 0 0) h
        have h1 := congrArg (fun z => z.val 1 1) h
        have h2 := congrArg (fun z => z.val 2 2) h
        simp at h0 h1 h2
        exact Subtype.ext (Prod.ext h0 (Prod.ext h1 h2)),
       fun B => by
        have hBp : Subring.closure ({B.val} : Set (M3 p)) = Subring.closure ({Matrix.diagonal ![l, m, n]} : Set (M3 p)) := B.prop
        have hB : B.val ∈ Subring.closure ({Matrix.diagonal ![l, m, n]} : Set (M3 p)) :=
          (SetLike.ext_iff.mp hBp B.val).mp (Subring.subset_closure rfl)
        obtain ⟨a, b, c, hc⟩ := (hmem_diag B.val).mp hB
        have hne := (hgen_iff a b c).mp (hc ▸ hBp)
        exact ⟨⟨(a, b, c), hne⟩, Subtype.ext hc.symm⟩⟩).symm
  rw [Nat.card_congr hbij, Nat.card_eq_fintype_card]
  have hcardT3 : Fintype.card T3 = p * (p - 1) * (p - 2) := by
    have h1 : Fintype.card T3 = ∑ a : ZMod p, ∑ b : ZMod p, ∑ c : ZMod p,
        if a ≠ b ∧ a ≠ c ∧ b ≠ c then 1 else 0 := by
      rw [Fintype.card_subtype]
      simp only [Finset.card_filter, Fintype.sum_prod_type]
    rw [h1]
    have hinner : ∀ a b : ZMod p, a ≠ b →
        (∑ c : ZMod p, if a ≠ b ∧ a ≠ c ∧ b ≠ c then 1 else 0) = p - 2 := fun a b hab => by
      have : (∑ c : ZMod p, if a ≠ b ∧ a ≠ c ∧ b ≠ c then 1 else 0) =
          (Finset.univ.filter fun c : ZMod p => c ≠ a ∧ c ≠ b).card := by
        rw [Finset.card_filter]; refine Finset.sum_congr rfl fun c _ => ?_
        by_cases hca : c = a
        · subst hca; simp
        · by_cases hcb : c = b
          · subst hcb; simp
          · simp [hab, hca, hcb, Ne.symm hca, Ne.symm hcb]
      rw [this]
      have hsub : Finset.univ.filter (fun c : ZMod p => c ≠ a ∧ c ≠ b) = Finset.univ \ {a, b} := by
        ext c; simp
      rw [hsub, Finset.card_sdiff, Finset.inter_univ, Finset.card_univ, ZMod.card, Finset.card_pair hab]
    have hmid : ∀ a : ZMod p,
        (∑ b : ZMod p, ∑ c : ZMod p, if a ≠ b ∧ a ≠ c ∧ b ≠ c then 1 else 0) = (p - 1) * (p - 2) := fun a => by
      have : (∑ b : ZMod p, ∑ c : ZMod p, if a ≠ b ∧ a ≠ c ∧ b ≠ c then 1 else 0) =
          ∑ b ∈ Finset.univ.erase a, (p - 2) := by
        rw [← Finset.sum_erase_add _ _ (Finset.mem_univ a)]
        have h0 : (∑ c : ZMod p, if a ≠ a ∧ a ≠ c ∧ a ≠ c then 1 else 0) = 0 := by simp
        rw [h0, add_zero]
        refine Finset.sum_congr rfl fun b hb => hinner a b (Ne.symm (Finset.ne_of_mem_erase hb))
      rw [this, Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ a),
          Finset.card_univ, ZMod.card, smul_eq_mul]
    simp_rw [hmid]
    rw [Finset.sum_const, Finset.card_univ, ZMod.card, smul_eq_mul]; ring
  exact hcardT3

private lemma card_singleGens_D {p : ℕ} [Fact p.Prime] {A : M3 p} (htA : HasM3Type A .D) :
    Nat.card (SingleGens ⟨Subring.closure ({A} : Set (M3 p)), ⟨A, rfl⟩⟩) = expectedGenCount p .D := by
  classical
  obtain ⟨S, hS⟩ := canonical_D htA
  rw [← card_singleGens_conj S A]
  have hveq : (⟨Subring.closure ({conjAlgEquiv S A} : Set (M3 p)), ⟨_, rfl⟩⟩ : UCCGVert p) =
      ⟨Subring.closure ({matD0 p} : Set (M3 p)), ⟨_, rfl⟩⟩ := Subtype.ext hS
  rw [hveq]
  have hcub : matD0 p ^ 3 = (0 : ZMod p) • matD0 p ^ 2 + (0 : ZMod p) • matD0 p + (0 : ZMod p) • (1 : M3 p) := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [matD0, pow_succ, Matrix.mul_apply, Fin.sum_univ_three]
  have hD2 : matD0 p ^ 2 = !![0, 0, 1; 0, 0, 0; 0, 0, 0] := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [matD0, sq, Matrix.mul_apply, Fin.sum_univ_three]
  have hgen_iff : ∀ c0 c1 c2 : ZMod p,
      Subring.closure ({c0 • (1 : M3 p) + c1 • matD0 p + c2 • matD0 p ^ 2} : Set (M3 p)) =
        Subring.closure ({matD0 p} : Set (M3 p)) ↔ c1 ≠ 0 := by
    intro c0 c1 c2
    set B := c0 • (1 : M3 p) + c1 • matD0 p + c2 • matD0 p ^ 2
    constructor
    · intro hEq hc1; subst hc1
      have hB2 : (B - c0 • (1 : M3 p)) ^ 2 = 0 := by
        have : B - c0 • (1 : M3 p) = c2 • matD0 p ^ 2 := by dsimp [B]; simp
        rw [this, _root_.smul_pow, ← pow_mul]
        ext i j; fin_cases i <;> fin_cases j <;> simp [matD0, pow_succ]
      have hdeg_le2 : (minpoly (ZMod p) B).natDegree ≤ 2 := by
        have hdvd := minpoly.dvd (ZMod p) B (show aeval B ((X - C c0) ^ 2) = 0 by
          simpa [Algebra.algebraMap_eq_smul_one] using hB2)
        have h := Polynomial.natDegree_le_of_dvd hdvd ((Polynomial.monic_X_sub_C c0).pow 2).ne_zero
        simpa [Polynomial.natDegree_pow, Polynomial.natDegree_X_sub_C] using h
      have hD : HasM3Type B .D := (same_type_of_subring_eq hEq .D).mpr
        ((same_type_of_subring_eq hS .D).mp ((hasM3Type_conj S A .D).mpr htA))
      have h3 := (hasM3Type_invariants hD).1
      dsimp only at h3
      omega
    · intro hc1
      rw [subring_closure_eq_iff]
      refine ⟨?_, (mem_closure_deg3 hcub B).mpr ⟨c0, c1, c2, rfl⟩⟩
      set SB := Subring.closure ({B} : Set (M3 p))
      have hBsub : B - c0 • (1 : M3 p) ∈ SB :=
        sub_mem (Subring.subset_closure rfl) (smul_one_mem_subring SB c0)
      have hsqB : (B - c0 • (1 : M3 p)) ^ 2 = (c1 ^ 2) • matD0 p ^ 2 := by
        have hdiff : B - c0 • (1 : M3 p) = c1 • matD0 p + c2 • matD0 p ^ 2 := by dsimp [B]; abel
        rw [hdiff, hD2]; ext i j; fin_cases i <;> fin_cases j <;>
          simp [matD0, sq, Matrix.mul_apply, Fin.sum_univ_three]
      have hD2_mem : matD0 p ^ 2 ∈ SB := by
        have h1 : (c1 ^ 2)⁻¹ • ((B - c0 • (1 : M3 p)) ^ 2) = matD0 p ^ 2 := by
          rw [hsqB, smul_smul, inv_mul_cancel₀ (pow_ne_zero 2 hc1), one_smul]
        rw [← h1]
        exact smul_mem_subring SB _ (pow_mem hBsub 2)
      have hD_eq : matD0 p = c1⁻¹ • ((B - c0 • (1 : M3 p)) - c2 • matD0 p ^ 2) := by
        have : (B - c0 • (1 : M3 p)) - c2 • matD0 p ^ 2 = c1 • matD0 p := by dsimp [B]; abel
        rw [this, smul_smul, inv_mul_cancel₀ hc1, one_smul]
      rw [hD_eq]
      exact smul_mem_subring SB _ (sub_mem hBsub (smul_mem_subring SB _ hD2_mem))
  let TD := ZMod p × { a : ZMod p // a ≠ 0 } × ZMod p
  have hbij : SingleGens ⟨Subring.closure ({matD0 p} : Set (M3 p)), ⟨_, rfl⟩⟩ ≃ TD :=
    (Equiv.ofBijective (fun x : TD =>
      (⟨x.1 • (1 : M3 p) + x.2.1.val • matD0 p + x.2.2 • matD0 p ^ 2,
        (hgen_iff x.1 x.2.1.val x.2.2).mpr x.2.1.prop⟩ :
        SingleGens ⟨Subring.closure ({matD0 p} : Set (M3 p)), ⟨_, rfl⟩⟩))
      ⟨fun x y h => by
        have h00 := congrArg (fun z => z.val 0 0) h
        have h01 := congrArg (fun z => z.val 0 1) h
        have h02 := congrArg (fun z => z.val 0 2) h
        dsimp only at h00 h01 h02
        rw [hD2] at h00 h01 h02
        simp [matD0] at h00 h01 h02
        exact Prod.ext h00 (Prod.ext (Subtype.ext h01) h02),
       fun B => by
        have hBp : Subring.closure ({B.val} : Set (M3 p)) = Subring.closure ({matD0 p} : Set (M3 p)) := B.prop
        have hB : B.val ∈ Subring.closure ({matD0 p} : Set (M3 p)) :=
          (SetLike.ext_iff.mp hBp B.val).mp (Subring.subset_closure rfl)
        obtain ⟨c0, c1, c2, hc⟩ := (mem_closure_deg3 hcub B.val).mp hB
        have hc1 := (hgen_iff c0 c1 c2).mp (hc ▸ hBp)
        exact ⟨(c0, ⟨c1, hc1⟩, c2), Subtype.ext hc.symm⟩⟩).symm
  rw [Nat.card_congr hbij, Nat.card_prod, Nat.card_prod, Nat.card_zmod]
  have hne0 : Nat.card { a : ZMod p // a ≠ 0 } = p - 1 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype_compl, ZMod.card, Fintype.card_unique]
  rw [hne0]; dsimp only [expectedGenCount]; ring

private lemma card_singleGens_F {p : ℕ} [Fact p.Prime] {A : M3 p} (htA : HasM3Type A .F) :
    Nat.card (SingleGens ⟨Subring.closure ({A} : Set (M3 p)), ⟨A, rfl⟩⟩) = expectedGenCount p .F := by
  classical
  obtain ⟨S, hS⟩ := canonical_F htA
  rw [← card_singleGens_conj S A]
  have hveq : (⟨Subring.closure ({conjAlgEquiv S A} : Set (M3 p)), ⟨_, rfl⟩⟩ : UCCGVert p) =
      ⟨Subring.closure ({matF0 p} : Set (M3 p)), ⟨_, rfl⟩⟩ := Subtype.ext hS
  rw [hveq]
  have hF2 : matF0 p ^ 2 = !![0, 0, 0; 0, 0, 0; 0, 0, 1] := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [matF0, sq, Matrix.mul_apply, Fin.sum_univ_three]
  have hcub : matF0 p ^ 3 = (1 : ZMod p) • matF0 p ^ 2 + (0 : ZMod p) • matF0 p + (0 : ZMod p) • (1 : M3 p) := by
    rw [pow_succ, hF2]; ext i j; fin_cases i <;> fin_cases j <;> simp [matF0, Matrix.mul_apply, Fin.sum_univ_three]
  have hgen_iff : ∀ c0 c1 c2 : ZMod p,
      Subring.closure ({c0 • (1 : M3 p) + c1 • matF0 p + c2 • matF0 p ^ 2} : Set (M3 p)) =
        Subring.closure ({matF0 p} : Set (M3 p)) ↔ c1 ≠ 0 ∧ c1 + c2 ≠ 0 := by
    intro c0 c1 c2
    set B := c0 • (1 : M3 p) + c1 • matF0 p + c2 • matF0 p ^ 2
    have hBval : B = !![c0, c1, 0; 0, c0, 0; 0, 0, c0 + c1 + c2] := by
      dsimp only [B]; rw [hF2]; ext i j; fin_cases i <;> fin_cases j <;> simp [matF0]; try ring
    constructor
    · intro hEq
      have hF : HasM3Type B .F := (same_type_of_subring_eq hEq .F).mpr
        ((same_type_of_subring_eq hS .F).mp ((hasM3Type_conj S A .F).mpr htA))
      have hinv := hasM3Type_invariants hF
      dsimp only at hinv
      constructor
      · intro hc1
        have hB2 : (B - c0 • (1 : M3 p)) * (B - (c0 + c1 + c2) • (1 : M3 p)) = 0 := by
          rw [hBval, hc1]; ext i j; fin_cases i <;> fin_cases j <;>
            simp [Matrix.mul_apply, Fin.sum_univ_three]
        have hdvd := minpoly.dvd (ZMod p) B (show aeval B ((X - C c0) * (X - C (c0 + c1 + c2))) = 0 by
          simpa [Algebra.algebraMap_eq_smul_one, add_smul] using hB2)
        have hle := Polynomial.natDegree_le_of_dvd hdvd
          ((Polynomial.monic_X_sub_C c0).mul (Polynomial.monic_X_sub_C (c0 + c1 + c2))).ne_zero
        rw [Polynomial.natDegree_mul (Polynomial.monic_X_sub_C c0).ne_zero
            (Polynomial.monic_X_sub_C _).ne_zero, Polynomial.natDegree_X_sub_C, Polynomial.natDegree_X_sub_C] at hle
        have h3 := hinv.1; omega
      · intro hc12
        have hch : B.charpoly = (X - C c0) ^ 3 := by
          rw [hBval, Matrix.charpoly, Matrix.det_fin_three]
          have : c0 + c1 + c2 = c0 := by linear_combination hc12
          rw [this]; simp [Matrix.charmatrix]; ring
        have h1 : (Finset.univ.filter fun x : ZMod p => B.charpoly.IsRoot x).card = 1 := by
          rw [hch]
          have : (Finset.univ.filter fun x : ZMod p => ((X - C c0) ^ 3).IsRoot x) = {c0} := by
            ext x; simp [Polynomial.IsRoot, sub_eq_zero]
          rw [this, Finset.card_singleton]
        have h2 := hinv.2.1; omega
    · rintro ⟨hc1, hc12⟩
      rw [subring_closure_eq_iff]
      refine ⟨?_, (mem_closure_deg3 hcub B).mpr ⟨c0, c1, c2, rfl⟩⟩
      set SB := Subring.closure ({B} : Set (M3 p))
      have hBsub : B - c0 • (1 : M3 p) ∈ SB :=
        sub_mem (Subring.subset_closure rfl) (smul_one_mem_subring SB c0)
      have hsqB : (B - c0 • (1 : M3 p)) ^ 2 = ((c1 + c2) ^ 2) • matF0 p ^ 2 := by
        rw [hBval, hF2]; ext i j; fin_cases i <;> fin_cases j <;>
          (simp [sq, Matrix.mul_apply, Fin.sum_univ_three]; try ring)
      have hF2_mem : matF0 p ^ 2 ∈ SB := by
        have h1 : ((c1 + c2) ^ 2)⁻¹ • ((B - c0 • (1 : M3 p)) ^ 2) = matF0 p ^ 2 := by
          rw [hsqB, smul_smul, inv_mul_cancel₀ (pow_ne_zero 2 hc12), one_smul]
        rw [← h1]; exact smul_mem_subring SB _ (pow_mem hBsub 2)
      have hF_eq : matF0 p = c1⁻¹ • ((B - c0 • (1 : M3 p)) - c2 • matF0 p ^ 2) := by
        have : (B - c0 • (1 : M3 p)) - c2 • matF0 p ^ 2 = c1 • matF0 p := by dsimp [B]; abel
        rw [this, smul_smul, inv_mul_cancel₀ hc1, one_smul]
      rw [hF_eq]; exact smul_mem_subring SB _ (sub_mem hBsub (smul_mem_subring SB _ hF2_mem))
  let TF := ZMod p × { a : ZMod p // a ≠ 0 } × { d : ZMod p // d ≠ 0 }
  have hbij : SingleGens ⟨Subring.closure ({matF0 p} : Set (M3 p)), ⟨_, rfl⟩⟩ ≃ TF :=
    (Equiv.ofBijective (fun x : TF =>
      (⟨x.1 • (1 : M3 p) + x.2.1.val • matF0 p + (x.2.2.val - x.2.1.val) • matF0 p ^ 2,
        (hgen_iff _ _ _).mpr ⟨x.2.1.prop, by simpa using x.2.2.prop⟩⟩ :
        SingleGens ⟨Subring.closure ({matF0 p} : Set (M3 p)), ⟨_, rfl⟩⟩))
      ⟨fun x y h => by
        have h00 := congrArg (fun z => z.val 0 0) h
        have h01 := congrArg (fun z => z.val 0 1) h
        have h22 := congrArg (fun z => z.val 2 2) h
        dsimp only at h00 h01 h22
        rw [hF2] at h00 h01 h22
        simp [matF0] at h00 h01 h22
        exact Prod.ext h00 (Prod.ext (Subtype.ext h01) (Subtype.ext (by linear_combination h22 - h00))),
       fun B => by
        have hBp : Subring.closure ({B.val} : Set (M3 p)) = Subring.closure ({matF0 p} : Set (M3 p)) := B.prop
        have hB : B.val ∈ Subring.closure ({matF0 p} : Set (M3 p)) :=
          (SetLike.ext_iff.mp hBp B.val).mp (Subring.subset_closure rfl)
        obtain ⟨c0, c1, c2, hc⟩ := (mem_closure_deg3 hcub B.val).mp hB
        obtain ⟨hc1, hc12⟩ := (hgen_iff c0 c1 c2).mp (hc ▸ hBp)
        exact ⟨(c0, ⟨c1, hc1⟩, ⟨c1 + c2, hc12⟩), Subtype.ext (by simp [hc])⟩⟩).symm
  rw [Nat.card_congr hbij, Nat.card_prod, Nat.card_prod, Nat.card_zmod]
  have hne0 : Nat.card { a : ZMod p // a ≠ 0 } = p - 1 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype_compl, ZMod.card, Fintype.card_unique]
  rw [hne0]; dsimp only [expectedGenCount]; ring

private lemma card_singleGens_G {p : ℕ} [Fact p.Prime] {A : M3 p} (htA : HasM3Type A .G) :
  Nat.card (SingleGens ⟨Subring.closure ({A} : Set (M3 p)), ⟨A, rfl⟩⟩) = expectedGenCount p .G := by
  classical
  have : Fintype (UCCGVert p) := Fintype.ofFinite _
  have hp2 : 2 ≤ p := (Fact.out : p.Prime).two_le
  rcases htA with ⟨hirr, hm⟩
  have hPmon : A.charpoly.Monic := Matrix.charpoly_monic A
  have hPdeg : A.charpoly.natDegree = 3 := by rw [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]
  have hint : IsIntegral (ZMod p) A := ⟨A.charpoly, hPmon, Matrix.aeval_self_charpoly A⟩
  have hcub : A ^ 3 = (-A.charpoly.coeff 2) • A ^ 2 + (-A.charpoly.coeff 1) • A + (-A.charpoly.coeff 0) • (1 : M3 p) := by
    have hP_exp : A.charpoly = X ^ 3 + C (A.charpoly.coeff 2) * X ^ 2 +
        C (A.charpoly.coeff 1) * X + C (A.charpoly.coeff 0) := by
      ext k
      by_cases hk : k ≤ 3
      · interval_cases k <;> simp [Polynomial.coeff_X, Polynomial.coeff_C, Polynomial.coeff_X_pow]
        · simpa [Polynomial.Monic, Polynomial.leadingCoeff, hPdeg] using hPmon
      · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)]
        simp [Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_C,
              show k ≠ 3 by omega, show k ≠ 2 by omega, show 1 ≠ k by omega, show k ≠ 0 by omega]
    have haev := Matrix.aeval_self_charpoly A
    rw [hP_exp] at haev
    simp only [map_add, map_mul, map_pow, aeval_X, aeval_C, Algebra.algebraMap_eq_smul_one,
      smul_mul_assoc, one_mul] at haev
    ext i j
    have hij := congrArg (fun M : M3 p => M i j) haev
    simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.zero_apply, smul_eq_mul] at hij ⊢
    linear_combination hij
  -- Uniqueness of `(c0, c1, c2)`: `1, A, A^2` are linearly independent since `deg(minpoly A) = 3`!
  have hlin_uniq : ∀ c0 c1 c2 : ZMod p, c0 • (1 : M3 p) + c1 • A + c2 • A ^ 2 = 0 →
      c0 = 0 ∧ c1 = 0 ∧ c2 = 0 := by
    intro c0 c1 c2 h0
    let f : (ZMod p)[X] := C c0 + C c1 * X + C c2 * X ^ 2
    have hf : aeval A f = 0 := by simpa [f, Algebra.algebraMap_eq_smul_one] using h0
    have hdvd := minpoly.dvd (ZMod p) A hf
    have hf0 : f = 0 := by
      by_contra hne
      have hfdeg : f.natDegree ≤ 2 := by
        refine le_trans (Polynomial.natDegree_add_le _ _) (max_le ?_ ?_)
        · refine le_trans (Polynomial.natDegree_add_le _ _) (max_le (by simp) (le_trans Polynomial.natDegree_mul_le (by simp)))
        · exact le_trans Polynomial.natDegree_mul_le (by simp)
      have hle := Polynomial.natDegree_le_of_dvd hdvd hne
      rw [hm, hPdeg] at hle; omega
    exact ⟨by simpa [f] using congrArg (fun g : (ZMod p)[X] => g.coeff 0) hf0,
           by simpa [f] using congrArg (fun g : (ZMod p)[X] => g.coeff 1) hf0,
           by simpa [f] using congrArg (fun g : (ZMod p)[X] => g.coeff 2) hf0⟩
  -- Every nonzero `B ∈ ⟨A⟩` is invertible in `⟨A⟩` (since `gcd(f, charpoly) = 1`),
  -- and every non-scalar `B ∈ ⟨A⟩` has `deg(minpoly B) = 3`, hence generates `⟨A⟩`!
  have hgen_iff : ∀ c0 c1 c2 : ZMod p,
      Subring.closure ({c0 • (1 : M3 p) + c1 • A + c2 • A ^ 2} : Set (M3 p)) =
        Subring.closure ({A} : Set (M3 p)) ↔ c1 ≠ 0 ∨ c2 ≠ 0 := by
    intro c0 c1 c2
    set B := c0 • (1 : M3 p) + c1 • A + c2 • A ^ 2
    have hBmem : B ∈ Subring.closure ({A} : Set (M3 p)) := (mem_closure_deg3 hcub B).mpr ⟨c0, c1, c2, rfl⟩
    constructor
    · intro hEq
      by_contra hall; push Not at hall
      rcases hall with ⟨rfl, rfl⟩
      have hB_eq : B = c0 • (1 : M3 p) := by dsimp [B]; simp
      have hBA : HasM3Type B .A := ⟨c0, hB_eq ▸ charpoly_smul_one c0, hB_eq ▸ minpoly_smul_one c0⟩
      have hBG : HasM3Type B .G := (same_type_of_subring_eq hEq .G).mpr ⟨hirr, hm⟩
      exact M3Type.noConfusion (hasM3Type_unique hBA hBG)
    · intro hne
      -- Show `1, B, B^2` are linearly independent over `ZMod p`!
      -- Because `Subring.closure {A}` is an integral domain (in fact a field: if `f(A)*g(A) = 0` then `charpoly ∣ f*g`,
      -- so `charpoly ∣ f` or `charpoly ∣ g` by irreducibility of `charpoly`!).
      -- If `B` had a quadratic annihilator `q(B) = 0` (`deg q = 2`), then either `q` has a root `r` (so `(B - r•1)(B - s•1) = 0`,
      -- forcing `B = r•1` or `B = s•1` since `⟨A⟩` is a domain -> contradicts `hne`!), OR `q` is irreducible of degree 2
      -- (then `1, B` span a 2D subfield of the 3D field `⟨A⟩` -> `2 ∣ 3`, impossible!!).
      have hdom : ∀ X Y : M3 p, X ∈ Subring.closure ({A} : Set (M3 p)) → Y ∈ Subring.closure ({A} : Set (M3 p)) →
          X * Y = 0 → X = 0 ∨ Y = 0 := by
        intro X Y hX hY hXY
        obtain ⟨f, rfl⟩ := (mem_subring_closure_iff_aeval A X).mp hX
        obtain ⟨g, rfl⟩ := (mem_subring_closure_iff_aeval A Y).mp hY
        have hfg : aeval A (f * g) = 0 := by rw [map_mul, hXY]
        have hdvd : A.charpoly ∣ f * g := hm ▸ minpoly.dvd (ZMod p) A hfg
        rcases hirr.prime.dvd_or_dvd hdvd with h1 | h2
        · left; obtain ⟨k, rfl⟩ := h1; rw [map_mul, Matrix.aeval_self_charpoly, zero_mul]
        · right; obtain ⟨k, rfl⟩ := h2; rw [map_mul, Matrix.aeval_self_charpoly, zero_mul]
      -- Also every nonzero `X ∈ ⟨A⟩` has an inverse in `⟨A⟩`!
      have hinv : ∀ X : M3 p, X ∈ Subring.closure ({A} : Set (M3 p)) → X ≠ 0 →
          ∃ Y ∈ Subring.closure ({A} : Set (M3 p)), X * Y = 1 := by
        intro X hX hX0
        obtain ⟨f, rfl⟩ := (mem_subring_closure_iff_aeval A X).mp hX
        have hndvd : ¬ A.charpoly ∣ f := fun ⟨k, hk⟩ => hX0 (by rw [hk, map_mul, Matrix.aeval_self_charpoly, zero_mul])
        obtain ⟨u, w, huw⟩ := hirr.coprime_iff_not_dvd.mpr hndvd
        rw [mul_comm w f] at huw
        refine ⟨aeval A w, aeval_mem_subring_closure A w, ?_⟩
        have := congrArg (aeval A) huw
        rw [map_add, map_mul, map_mul, Matrix.aeval_self_charpoly, mul_zero, zero_add, map_one] at this
        exact this
      -- Show `B` is not scalar:
      have hB_nsc : ∀ r : ZMod p, B ≠ r • (1 : M3 p) := by
        intro r hr
        have h0 : (c0 - r) • (1 : M3 p) + c1 • A + c2 • A ^ 2 = 0 := by
          rw [sub_smul]; calc c0 • (1 : M3 p) - r • (1 : M3 p) + c1 • A + c2 • A ^ 2
              = B - r • (1 : M3 p) := by simp [B]; abel
            _ = 0 := sub_eq_zero.mpr hr
        obtain ⟨_, h1, h2⟩ := hlin_uniq (c0 - r) c1 c2 h0
        rcases hne with h | h <;> contradiction
      -- Show `deg (minpoly B) = 3`:
      have hBdeg3 : (minpoly (ZMod p) B).natDegree = 3 := by
        have hpos := minpoly_natDegree_pos B
        have hle := minpoly_natDegree_le_three B
        have hne1 : (minpoly (ZMod p) B).natDegree ≠ 1 := by
          intro h1
          have hmB := minpoly.monic (⟨B.charpoly, Matrix.charpoly_monic B, Matrix.aeval_self_charpoly B⟩ : IsIntegral (ZMod p) B)
          have hlin : minpoly (ZMod p) B = X + C ((minpoly (ZMod p) B).coeff 0) := by
            rw [Polynomial.eq_X_add_C_of_degree_le_one (Polynomial.degree_le_of_natDegree_le (le_of_eq h1))]
            have hlc : (minpoly (ZMod p) B).coeff 1 = 1 := by simpa [Polynomial.Monic, Polynomial.leadingCoeff, h1] using hmB
            simp [hlc]
          have haev := minpoly.aeval (ZMod p) B
          rw [hlin, map_add, aeval_X, aeval_C, Algebra.algebraMap_eq_smul_one] at haev
          exact hB_nsc (-(minpoly (ZMod p) B).coeff 0) (by rw [neg_smul]; exact eq_neg_of_add_eq_zero_left haev)
        have hne2 : (minpoly (ZMod p) B).natDegree ≠ 2 := by
          intro h2
          -- `S_B := Algebra.adjoin (ZMod p) {B}` is a 2D subspace of the 3D space `S_A := Algebra.adjoin (ZMod p) {A}`!
          -- Moreover, `S_B` is closed under multiplication, and for any `X ∈ S_A \ S_B`, `S_B ∩ (X * S_B) = {0}`
          -- (if `X * b1 = b2` with `b1 ≠ 0`, since `b1⁻¹ ∈ S_B`? Even simpler: `b1 ∈ S_B \ {0}` has `b1⁻¹ ∈ S_B`
          -- because `b1` satisfies a degree ≤ 2 monic polynomial with nonzero constant term!).
          -- Thus `S_B + X * S_B` has dimension `2 + 2 = 4 ≤ 3 = dim S_A`, CONTRADICTION!!
          have hSB_sub : Algebra.adjoin (ZMod p) ({B} : Set (M3 p)) ≤ Algebra.adjoin (ZMod p) ({A} : Set (M3 p)) := by
            rw [Algebra.adjoin_le_iff, Set.singleton_subset_iff]
            change B ∈ (Algebra.adjoin (ZMod p) ({A} : Set (M3 p))).toSubring
            rwa [← subring_closure_eq_adjoin A]
          have hdimA : Module.finrank (ZMod p) (Algebra.adjoin (ZMod p) ({A} : Set (M3 p))) = 3 := by
            rw [finrank_adjoin_singleton_m3, hm, hPdeg]
          have hintB : IsIntegral (ZMod p) B := ⟨B.charpoly, Matrix.charpoly_monic B, Matrix.aeval_self_charpoly B⟩
          have hdimB : Module.finrank (ZMod p) (Algebra.adjoin (ZMod p) ({B} : Set (M3 p))) = 2 := by
            rw [finrank_adjoin_singleton_m3, h2]
          -- Pick `X ∈ S_A \ S_B`
          have hexX : ∃ X : M3 p, X ∈ Algebra.adjoin (ZMod p) ({A} : Set (M3 p)) ∧
              X ∉ Algebra.adjoin (ZMod p) ({B} : Set (M3 p)) := by
            by_contra hall; push Not at hall
            have heq : Algebra.adjoin (ZMod p) ({A} : Set (M3 p)) = Algebra.adjoin (ZMod p) ({B} : Set (M3 p)) :=
              le_antisymm (fun x hx => hall x hx) hSB_sub
            rw [heq, hdimB] at hdimA; omega
          obtain ⟨X, hXA, hXnotB⟩ := hexX
          -- Show `1, B, X, X * B` are linearly independent in `S_A`, contradicting `dim S_A = 3`!
          -- Wait: if `c0 • 1 + c1 • B + c2 • X + c3 • (X * B) = 0`, then `X * (c2 • 1 + c3 • B) = -(c0 • 1 + c1 • B)`.
          -- If `c2 • 1 + c3 • B ≠ 0`, show `(c2 • 1 + c3 • B)⁻¹ ∈ S_B`:
          -- Let `u := c2 • 1 + c3 • B ∈ S_B \ {0}`. Since `B^2 = a•B + b•1`, `u * (a'•1 - c3•B) = norm • 1` with `norm ≠ 0`!
          have hmB := minpoly.monic hintB
          have hB_eq : B ^ 2 = (-(minpoly (ZMod p) B).coeff 1) • B + (-(minpoly (ZMod p) B).coeff 0) • (1 : M3 p) := by
            have hP2 : minpoly (ZMod p) B = Polynomial.X ^ 2 + C ((minpoly (ZMod p) B).coeff 1) * Polynomial.X + C ((minpoly (ZMod p) B).coeff 0) := by
              ext k
              by_cases hk : k ≤ 2
              · interval_cases k <;> simp [Polynomial.coeff_X, Polynomial.coeff_C, Polynomial.coeff_X_pow]
                · simpa [Polynomial.Monic, Polynomial.leadingCoeff, h2] using hmB
              · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)]
                simp [Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_C,
                      show k ≠ 2 by omega, show 1 ≠ k by omega, show k ≠ 0 by omega]
            have haev := minpoly.aeval (ZMod p) B
            rw [hP2] at haev
            simp only [map_add, map_mul, map_pow, aeval_X, aeval_C, Algebra.algebraMap_eq_smul_one,
              smul_mul_assoc, one_mul] at haev
            ext i j
            have hij := congrArg (fun M : M3 p => M i j) haev
            simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.zero_apply, smul_eq_mul] at hij ⊢
            linear_combination hij
          set a1 := -(minpoly (ZMod p) B).coeff 1
          set a0 := -(minpoly (ZMod p) B).coeff 0
          -- Now `S_A` has card `p^3`, while `{c0•1 + c1•B + c2•X + c3•(X*B)}` has `p^4` distinct elements!
          have hinj4 : Function.Injective (fun t : ZMod p × ZMod p × ZMod p × ZMod p =>
              (⟨t.1 • (1 : M3 p) + t.2.1 • B + t.2.2.1 • X + t.2.2.2 • (X * B), by
                have h1 : (1 : M3 p) ∈ Algebra.adjoin (ZMod p) ({A} : Set (M3 p)) := one_mem _
                have hB' : B ∈ Algebra.adjoin (ZMod p) ({A} : Set (M3 p)) := hSB_sub (Algebra.subset_adjoin rfl)
                exact add_mem (add_mem (add_mem (Subalgebra.smul_mem _ h1 _) (Subalgebra.smul_mem _ hB' _))
                  (Subalgebra.smul_mem _ hXA _)) (Subalgebra.smul_mem _ (mul_mem hXA hB') _)⟩ :
                Algebra.adjoin (ZMod p) ({A} : Set (M3 p)))) := by
            intro t1 t2 heq
            have hval := congrArg Subtype.val heq
            dsimp only at hval
            set d0 := t1.1 - t2.1; set d1 := t1.2.1 - t2.2.1
            set d2 := t1.2.2.1 - t2.2.2.1; set d3 := t1.2.2.2 - t2.2.2.2
            have hdiff : d0 • (1 : M3 p) + d1 • B + X * (d2 • (1 : M3 p) + d3 • B) = 0 := by
              have hsub : (t1.1 • (1 : M3 p) + t1.2.1 • B + t1.2.2.1 • X + t1.2.2.2 • (X * B)) -
                  (t2.1 • (1 : M3 p) + t2.2.1 • B + t2.2.2.1 • X + t2.2.2.2 • (X * B)) = 0 := sub_eq_zero.mpr hval
              rw [mul_add, mul_smul_comm, mul_one, mul_smul_comm]
              simp only [d0, d1, d2, d3, sub_smul]
              rw [← hsub]; abel
            set u := d2 • (1 : M3 p) + d3 • B
            have hu0 : u = 0 := by
              by_contra hune
              set v := (d2 + d3 * a1) • (1 : M3 p) - d3 • B
              have huv : u * v = (d2 * (d2 + d3 * a1) - d3 * d3 * a0) • (1 : M3 p) := by
                have h1 : u * v = (d2 * (d2 + d3 * a1)) • (1 : M3 p) - (d2 * d3) • B +
                    (d3 * (d2 + d3 * a1)) • B - (d3 * d3) • B ^ 2 := by
                  simp only [u, v, add_mul, mul_sub, smul_mul_smul_comm, one_mul, mul_one, sq]
                  abel
                rw [h1, hB_eq, smul_add (d3 * d3), smul_smul, smul_smul]
                ext i j; simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]; ring
              have hu_mem : u ∈ Subring.closure ({A} : Set (M3 p)) := by
                rw [subring_closure_eq_adjoin]; exact add_mem (Subalgebra.smul_mem _ (one_mem _) _)
                  (Subalgebra.smul_mem _ (hSB_sub (Algebra.subset_adjoin rfl)) _)
              have hv_mem : v ∈ Subring.closure ({A} : Set (M3 p)) := by
                rw [subring_closure_eq_adjoin]; exact sub_mem (Subalgebra.smul_mem _ (one_mem _) _)
                  (Subalgebra.smul_mem _ (hSB_sub (Algebra.subset_adjoin rfl)) _)
              have hvne : v ≠ 0 := by
                intro hv0
                by_cases hd3 : d3 = 0
                · dsimp only [v] at hv0
                  rw [hd3, zero_mul, add_zero, zero_smul, sub_zero] at hv0
                  have hd2 : d2 = 0 := by simpa using congrArg (fun M : M3 p => M 0 0) hv0
                  exact hune (by simp [u, hd2, hd3])
                · exact hB_nsc (d3⁻¹ * (d2 + d3 * a1)) (by
                    have h1 : d3 • B = (d2 + d3 * a1) • (1 : M3 p) := (sub_eq_zero.mp hv0).symm
                    have h2 := congrArg (d3⁻¹ • ·) h1
                    simpa [smul_smul, inv_mul_cancel₀ hd3] using h2)
              have hnorm_ne : d2 * (d2 + d3 * a1) - d3 * d3 * a0 ≠ 0 := by
                intro hn0
                rw [hn0, zero_smul] at huv
                rcases hdom u v hu_mem hv_mem huv with h | h <;> contradiction
              have hXv : X * (u * v) = -(d0 • (1 : M3 p) + d1 • B) * v := by
                have h1 : X * u = -(d0 • (1 : M3 p) + d1 • B) := eq_neg_of_add_eq_zero_right hdiff
                rw [← mul_assoc, h1]
              rw [huv, mul_smul_comm, mul_one] at hXv
              have hX_eq : X = (d2 * (d2 + d3 * a1) - d3 * d3 * a0)⁻¹ • (-(d0 • (1 : M3 p) + d1 • B) * v) := by
                have := congrArg ((d2 * (d2 + d3 * a1) - d3 * d3 * a0)⁻¹ • ·) hXv
                simpa [smul_smul, inv_mul_cancel₀ hnorm_ne] using this
              apply hXnotB; rw [hX_eq]
              have hB_in : B ∈ Algebra.adjoin (ZMod p) ({B} : Set (M3 p)) := Algebra.subset_adjoin rfl
              have hv_in : v ∈ Algebra.adjoin (ZMod p) ({B} : Set (M3 p)) :=
                sub_mem (Subalgebra.smul_mem _ (one_mem _) _) (Subalgebra.smul_mem _ hB_in _)
              have hw_in : -(d0 • (1 : M3 p) + d1 • B) ∈ Algebra.adjoin (ZMod p) ({B} : Set (M3 p)) :=
                neg_mem (add_mem (Subalgebra.smul_mem _ (one_mem _) _) (Subalgebra.smul_mem _ hB_in _))
              exact Subalgebra.smul_mem _ (mul_mem hw_in hv_in) _
            have hd3 : d3 = 0 := by
              by_contra hne3
              exact hB_nsc (-d3⁻¹ * d2) (by
                have h1 : d3 • B = -(d2 • (1 : M3 p)) := eq_neg_of_add_eq_zero_right hu0
                have h2 := congrArg (d3⁻¹ • ·) h1
                simpa [smul_smul, inv_mul_cancel₀ hne3, neg_mul, neg_smul] using h2)
            have hd2 : d2 = 0 := by
              have hu0' : d2 • (1 : M3 p) + d3 • B = 0 := hu0
              rw [hd3, zero_smul, add_zero] at hu0'
              simpa using congrArg (fun M : M3 p => M 0 0) hu0'
            rw [hu0, mul_zero, add_zero] at hdiff
            have hd1 : d1 = 0 := by
              by_contra hne1
              exact hB_nsc (-d1⁻¹ * d0) (by
                have h1 : d1 • B = -(d0 • (1 : M3 p)) := eq_neg_of_add_eq_zero_right hdiff
                have h2 := congrArg (d1⁻¹ • ·) h1
                simpa [smul_smul, inv_mul_cancel₀ hne1, neg_mul, neg_smul] using h2)
            have hd0 : d0 = 0 := by
              rw [hd1, zero_smul, add_zero] at hdiff
              simpa using congrArg (fun M : M3 p => M 0 0) hdiff
            exact Prod.ext (sub_eq_zero.mp hd0) (Prod.ext (sub_eq_zero.mp hd1)
              (Prod.ext (sub_eq_zero.mp hd2) (sub_eq_zero.mp hd3)))
          have hle4 := Fintype.card_le_of_injective _ hinj4
          have hcardA : Fintype.card (Algebra.adjoin (ZMod p) ({A} : Set (M3 p))) = p ^ 3 := by
            rw [Module.card_eq_pow_finrank (K := ZMod p), ZMod.card, hdimA]
          simp only [Fintype.card_prod, ZMod.card, hcardA] at hle4
          have : p ^ 4 ≤ p ^ 3 := by convert hle4 using 1; ring
          have : p ^ 3 < p ^ 4 := Nat.pow_lt_pow_right (by omega) (by omega)
          omega
        omega
      -- Now `Algebra.adjoin (ZMod p) {B} ≤ Algebra.adjoin (ZMod p) {A}` and both have `finrank = 3` => equal!
      have hSB_sub : Algebra.adjoin (ZMod p) ({B} : Set (M3 p)) ≤ Algebra.adjoin (ZMod p) ({A} : Set (M3 p)) := by
        rw [Algebra.adjoin_le_iff, Set.singleton_subset_iff]
        change B ∈ (Algebra.adjoin (ZMod p) ({A} : Set (M3 p))).toSubring
        rwa [← subring_closure_eq_adjoin A]
      have hdimA : Module.finrank (ZMod p) (Algebra.adjoin (ZMod p) ({A} : Set (M3 p))) = 3 := by
        rw [finrank_adjoin_singleton_m3, hm, hPdeg]
      have hdimB : Module.finrank (ZMod p) (Algebra.adjoin (ZMod p) ({B} : Set (M3 p))) = 3 := by
        rw [finrank_adjoin_singleton_m3, hBdeg3]
      have heq_sub : (Algebra.adjoin (ZMod p) ({B} : Set (M3 p))).toSubmodule =
          (Algebra.adjoin (ZMod p) ({A} : Set (M3 p))).toSubmodule :=
        Submodule.eq_of_le_of_finrank_eq hSB_sub (by
          change Module.finrank (ZMod p) (Algebra.adjoin (ZMod p) ({B} : Set (M3 p))) =
            Module.finrank (ZMod p) (Algebra.adjoin (ZMod p) ({A} : Set (M3 p)))
          rw [hdimB, hdimA])
      rw [subring_closure_eq_adjoin B, subring_closure_eq_adjoin A]
      ext X
      exact SetLike.ext_iff.mp heq_sub X
  let TG := { x : ZMod p × ZMod p × ZMod p // x.2.1 ≠ 0 ∨ x.2.2 ≠ 0 }
  have hbij : SingleGens ⟨Subring.closure ({A} : Set (M3 p)), ⟨A, rfl⟩⟩ ≃ TG :=
    (Equiv.ofBijective (fun x : TG =>
      (⟨x.val.1 • (1 : M3 p) + x.val.2.1 • A + x.val.2.2 • A ^ 2,
        (hgen_iff x.val.1 x.val.2.1 x.val.2.2).mpr x.prop⟩ :
        SingleGens ⟨Subring.closure ({A} : Set (M3 p)), ⟨A, rfl⟩⟩))
      ⟨fun x y h => by
        have h0 : (x.val.1 - y.val.1) • (1 : M3 p) + (x.val.2.1 - y.val.2.1) • A +
            (x.val.2.2 - y.val.2.2) • A ^ 2 = 0 := by
          have hv := sub_eq_zero.mpr (congrArg Subtype.val h)
          dsimp only at hv
          simp only [sub_smul]; rw [← hv]; abel
        obtain ⟨h1, h2, h3⟩ := hlin_uniq _ _ _ h0
        exact Subtype.ext (Prod.ext (sub_eq_zero.mp h1) (Prod.ext (sub_eq_zero.mp h2) (sub_eq_zero.mp h3))),
       fun B => by
        have hBp : Subring.closure ({B.val} : Set (M3 p)) = Subring.closure ({A} : Set (M3 p)) := B.prop
        have hB : B.val ∈ Subring.closure ({A} : Set (M3 p)) :=
          (SetLike.ext_iff.mp hBp B.val).mp (Subring.subset_closure rfl)
        obtain ⟨c0, c1, c2, hc⟩ := (mem_closure_deg3 hcub B.val).mp hB
        have hne := (hgen_iff c0 c1 c2).mp (hc ▸ hBp)
        exact ⟨⟨(c0, c1, c2), hne⟩, Subtype.ext hc.symm⟩⟩).symm
  rw [Nat.card_congr hbij, Nat.card_eq_fintype_card]
  have hcardTG : Fintype.card TG = p ^ 3 - p := by
    have heq : TG ≃ { x : ZMod p × ZMod p × ZMod p // ¬ (x.2.1 = 0 ∧ x.2.2 = 0) } :=
      Equiv.subtypeEquivRight fun x => by tauto
    rw [Fintype.card_congr heq, Fintype.card_subtype_compl]
    have htot : Fintype.card (ZMod p × ZMod p × ZMod p) = p ^ 3 := by
      simp [Fintype.card_prod, ZMod.card]; ring
    have hsc : Fintype.card { x : ZMod p × ZMod p × ZMod p // x.2.1 = 0 ∧ x.2.2 = 0 } = p := by
      have e2 : { x : ZMod p × ZMod p × ZMod p // x.2.1 = 0 ∧ x.2.2 = 0 } ≃ ZMod p :=
        { toFun := fun x => x.val.1
          invFun := fun c => ⟨(c, 0, 0), rfl, rfl⟩
          left_inv := fun ⟨⟨_, _, _⟩, hb, hc⟩ => Subtype.ext (Prod.ext rfl (Prod.ext hb.symm hc.symm))
          right_inv := fun _ => rfl }
      rw [Fintype.card_congr e2, ZMod.card]
    rw [htot, hsc]
  exact hcardTG

private lemma mem_closure_matH0 {p : ℕ} [Fact p.Prime] {l : ZMod p} {q : (ZMod p)[X]}
    (hqmon : q.Monic) (hqdeg : q.natDegree = 2) (hqirr : Irreducible q) (B : M3 p) :
    B ∈ Subring.closure ({matH0 l q} : Set (M3 p)) ↔
      ∃ a b c : ZMod p, B = !![a, 0, 0; 0, b, -c * q.coeff 0; 0, c, b - c * q.coeff 1] := by
  set M := matH0 l q
  have hqno : ∀ x : ZMod p, ¬ q.IsRoot x := fun x hx => by
    obtain ⟨R, hR⟩ := Polynomial.dvd_iff_isRoot.mpr hx
    rcases hqirr.isUnit_or_isUnit hR with hu | hu
    · exact Polynomial.not_isUnit_X_sub_C x hu
    · have := congrArg Polynomial.natDegree hR
      rw [hqdeg, Polynomial.natDegree_mul (Polynomial.monic_X_sub_C x).ne_zero hu.ne_zero,
          Polynomial.natDegree_X_sub_C, Polynomial.natDegree_eq_zero_of_isUnit hu] at this; omega
  constructor
  · intro hB
    let S0 : Subring (M3 p) :=
      { carrier := { X | ∃ a b c : ZMod p, X = !![a, 0, 0; 0, b, -c * q.coeff 0; 0, c, b - c * q.coeff 1] }
        mul_mem' := by
          rintro _ _ ⟨a1, b1, c1, rfl⟩ ⟨a2, b2, c2, rfl⟩
          refine ⟨a1 * a2, b1 * b2 - c1 * c2 * q.coeff 0, b1 * c2 + c1 * b2 - c1 * c2 * q.coeff 1, ?_⟩
          ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three] <;> ring
        one_mem' := ⟨1, 1, 0, by ext i j; fin_cases i <;> fin_cases j <;> simp⟩
        add_mem' := by
          rintro _ _ ⟨a1, b1, c1, rfl⟩ ⟨a2, b2, c2, rfl⟩
          refine ⟨a1 + a2, b1 + b2, c1 + c2, ?_⟩
          ext i j; fin_cases i <;> fin_cases j <;> simp <;> ring
        zero_mem' := ⟨0, 0, 0, by ext i j; fin_cases i <;> fin_cases j <;> simp⟩
        neg_mem' := by
          rintro _ ⟨a1, b1, c1, rfl⟩
          refine ⟨-a1, -b1, -c1, ?_⟩
          ext i j; fin_cases i <;> fin_cases j <;> (simp; try ring) }
    have hle : Subring.closure ({M} : Set (M3 p)) ≤ S0 :=
      Subring.closure_le.mpr (Set.singleton_subset_iff.mpr ⟨l, 0, 1, by
        ext i j; fin_cases i <;> fin_cases j <;> simp [M, matH0]⟩)
    exact hle hB
  · rintro ⟨a, b, c, rfl⟩
    have hqM : aeval M q = (q.eval l) • matB0 p := by
      have hq_exp : q = X ^ 2 + C (q.coeff 1) * X + C (q.coeff 0) := by
        ext k
        by_cases hk : k ≤ 2
        · interval_cases k <;> simp [Polynomial.coeff_X, Polynomial.coeff_C, Polynomial.coeff_X_pow]
          · simpa [Polynomial.Monic, Polynomial.leadingCoeff, hqdeg] using hqmon
        · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)]
          simp [Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_C,
                show k ≠ 2 by omega, show 1 ≠ k by omega, show k ≠ 0 by omega]
      rw [hq_exp]
      simp only [map_add, map_mul, map_pow, aeval_X, aeval_C, Algebra.algebraMap_eq_smul_one,
        smul_mul_assoc, one_mul, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow,
        Polynomial.eval_X, Polynomial.eval_C]
      ext i j; fin_cases i <;> fin_cases j <;> (simp [M, matH0, matB0, sq]; try ring)
    have hE00 : matB0 p ∈ Subring.closure ({M} : Set (M3 p)) := by
      have h1 : (q.eval l)⁻¹ • aeval M q = matB0 p := by
        rw [hqM, smul_smul, inv_mul_cancel₀ (hqno l), one_smul]
      rw [← h1]; exact smul_mem_subring _ _ (aeval_mem_subring_closure M q)
    have hEq : !![a, 0, 0; 0, b, -c * q.coeff 0; 0, c, b - c * q.coeff 1] =
        (a - b - c * l) • matB0 p + b • (1 : M3 p) + c • M := by
      ext i j; fin_cases i <;> fin_cases j <;> simp [M, matH0, matB0] <;> ring
    rw [hEq]
    exact add_mem (add_mem (smul_mem_subring _ _ hE00) (smul_one_mem_subring _ b))
      (smul_mem_subring _ c (Subring.subset_closure rfl))

private lemma gen_matH0_iff {p : ℕ} [Fact p.Prime] {l : ZMod p} {q : (ZMod p)[X]}
    (hqmon : q.Monic) (hqdeg : q.natDegree = 2) (hqirr : Irreducible q)
    (htM : HasM3Type (matH0 l q) .H) (a b c : ZMod p) :
    Subring.closure ({!![a, 0, 0; 0, b, -c * q.coeff 0; 0, c, b - c * q.coeff 1]} : Set (M3 p)) =
      Subring.closure ({matH0 l q} : Set (M3 p)) ↔ c ≠ 0 := by
  set M := matH0 l q
  set B := !![a, 0, 0; 0, b, -c * q.coeff 0; 0, c, b - c * q.coeff 1]
  have hqno : ∀ x : ZMod p, ¬ q.IsRoot x := fun x hx => by
    obtain ⟨R, hR⟩ := Polynomial.dvd_iff_isRoot.mpr hx
    rcases hqirr.isUnit_or_isUnit hR with hu | hu
    · exact Polynomial.not_isUnit_X_sub_C x hu
    · have := congrArg Polynomial.natDegree hR
      rw [hqdeg, Polynomial.natDegree_mul (Polynomial.monic_X_sub_C x).ne_zero hu.ne_zero,
          Polynomial.natDegree_X_sub_C, Polynomial.natDegree_eq_zero_of_isUnit hu] at this; omega
  constructor
  · intro hEq hc0; subst hc0
    have hBdiag : B = (a - b) • matB0 p + b • (1 : M3 p) := by
      ext i j; fin_cases i <;> fin_cases j <;> simp [B, matB0]
    have hdeg2 : (minpoly (ZMod p) B).natDegree ≤ 2 := by
      have hsq : (B - b • (1 : M3 p)) * (B - a • (1 : M3 p)) = 0 := by
        rw [hBdiag]; ext i j; fin_cases i <;> fin_cases j <;>
          simp [matB0, Matrix.mul_apply, Fin.sum_univ_three]
      have hdvd := minpoly.dvd (ZMod p) B (show aeval B ((X - C b) * (X - C a)) = 0 by
        simpa [Algebra.algebraMap_eq_smul_one] using hsq)
      have hle := Polynomial.natDegree_le_of_dvd hdvd
        ((Polynomial.monic_X_sub_C b).mul (Polynomial.monic_X_sub_C a)).ne_zero
      rw [Polynomial.natDegree_mul (Polynomial.monic_X_sub_C b).ne_zero
          (Polynomial.monic_X_sub_C a).ne_zero, Polynomial.natDegree_X_sub_C, Polynomial.natDegree_X_sub_C] at hle
      omega
    have hBH : HasM3Type B .H := (same_type_of_subring_eq hEq .H).mpr htM
    have h3 := (hasM3Type_invariants hBH).1
    dsimp only at h3
    omega
  · intro hc
    rw [subring_closure_eq_iff]
    refine ⟨?_, (mem_closure_matH0 hqmon hqdeg hqirr B).mpr ⟨a, b, c, rfl⟩⟩
    let q' : (ZMod p)[X] := X ^ 2 + C (c * q.coeff 1 - 2 * b) * X + C (b ^ 2 - b * c * q.coeff 1 + c ^ 2 * q.coeff 0)
    have hq'a_ne : q'.eval a ≠ 0 := by
      intro h0
      have hval : q.eval (c⁻¹ * (a - b)) = 0 := by
        have hq_exp : q = X ^ 2 + C (q.coeff 1) * X + C (q.coeff 0) := by
          ext k
          by_cases hk : k ≤ 2
          · interval_cases k <;> simp [Polynomial.coeff_X, Polynomial.coeff_C, Polynomial.coeff_X_pow]
            · simpa [Polynomial.Monic, Polynomial.leadingCoeff, hqdeg] using hqmon
          · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)]
            simp [Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_C,
                  show k ≠ 2 by omega, show 1 ≠ k by omega, show k ≠ 0 by omega]
        rw [hq_exp]
        simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C]
        simp only [q', Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C] at h0
        have hmul : c ^ 2 * ((c⁻¹ * (a - b)) ^ 2 + q.coeff 1 * (c⁻¹ * (a - b)) + q.coeff 0) =
            a ^ 2 + (c * q.coeff 1 - 2 * b) * a + (b ^ 2 - b * c * q.coeff 1 + c ^ 2 * q.coeff 0) := by
          have hci : c * c⁻¹ = 1 := mul_inv_cancel₀ hc
          calc c ^ 2 * ((c⁻¹ * (a - b)) ^ 2 + q.coeff 1 * (c⁻¹ * (a - b)) + q.coeff 0)
              = (c * c⁻¹) ^ 2 * (a - b) ^ 2 + c * (c * c⁻¹) * q.coeff 1 * (a - b) + c ^ 2 * q.coeff 0 := by ring
            _ = (a - b) ^ 2 + c * q.coeff 1 * (a - b) + c ^ 2 * q.coeff 0 := by rw [hci]; ring
            _ = a ^ 2 + (c * q.coeff 1 - 2 * b) * a + (b ^ 2 - b * c * q.coeff 1 + c ^ 2 * q.coeff 0) := by ring
        have h0' : c ^ 2 * ((c⁻¹ * (a - b)) ^ 2 + q.coeff 1 * (c⁻¹ * (a - b)) + q.coeff 0) = 0 := by rw [hmul, h0]
        exact (mul_eq_zero.mp h0').resolve_left (pow_ne_zero 2 hc)
      exact hqno (c⁻¹ * (a - b)) hval
    have hq'B : aeval B q' = (q'.eval a) • matB0 p := by
      simp only [q', map_add, map_mul, map_pow, aeval_X, aeval_C, Algebra.algebraMap_eq_smul_one,
        smul_mul_assoc, one_mul, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow,
        Polynomial.eval_X, Polynomial.eval_C]
      ext i j; fin_cases i <;> fin_cases j <;> simp [B, matB0, sq] <;> ring
    have hE00 : matB0 p ∈ Subring.closure ({B} : Set (M3 p)) := by
      have h1 : (q'.eval a)⁻¹ • aeval B q' = matB0 p := by
        rw [hq'B, smul_smul, inv_mul_cancel₀ hq'a_ne, one_smul]
      rw [← h1]; exact smul_mem_subring (Subring.closure ({B} : Set (M3 p))) _ (aeval_mem_subring_closure B q')
    have hcM_eq : c • M = (c * l - a + b) • matB0 p + (-b) • (1 : M3 p) + B := by
      ext i j; fin_cases i <;> fin_cases j <;> (simp [M, matH0, matB0, B]; try ring)
    have hM_eq : M = c⁻¹ • ((c * l - a + b) • matB0 p + (-b) • (1 : M3 p) + B) := by
      rw [← hcM_eq, smul_smul, inv_mul_cancel₀ hc, one_smul]
    rw [hM_eq]
    set SB := Subring.closure ({B} : Set (M3 p))
    exact smul_mem_subring SB c⁻¹ (add_mem (add_mem (smul_mem_subring SB _ hE00) (smul_one_mem_subring SB _))
      (Subring.subset_closure rfl))

private lemma card_singleGens_H {p : ℕ} [Fact p.Prime] {A : M3 p} (htA : HasM3Type A .H) :
  Nat.card (SingleGens ⟨Subring.closure ({A} : Set (M3 p)), ⟨A, rfl⟩⟩) = expectedGenCount p .H := by
  classical
  obtain ⟨S, l, q, hqmon, hqdeg, hqirr, hS⟩ := canonical_H htA
  rw [← card_singleGens_conj S A]
  have hveq : (⟨Subring.closure ({conjAlgEquiv S A} : Set (M3 p)), ⟨_, rfl⟩⟩ : UCCGVert p) =
      ⟨Subring.closure ({matH0 l q} : Set (M3 p)), ⟨_, rfl⟩⟩ := Subtype.ext (by rw [hS])
  rw [hveq]
  set M := matH0 l q
  have htM : HasM3Type M .H := hS ▸ (hasM3Type_conj S A .H).mpr htA
  let TH := ZMod p × ZMod p × { c : ZMod p // c ≠ 0 }
  have hbij : SingleGens ⟨Subring.closure ({M} : Set (M3 p)), ⟨_, rfl⟩⟩ ≃ TH :=
    (Equiv.ofBijective (fun x : TH =>
      (⟨!![x.1, 0, 0; 0, x.2.1, -x.2.2.val * q.coeff 0; 0, x.2.2.val, x.2.1 - x.2.2.val * q.coeff 1],
        (gen_matH0_iff hqmon hqdeg hqirr htM x.1 x.2.1 x.2.2.val).mpr x.2.2.prop⟩ :
        SingleGens ⟨Subring.closure ({M} : Set (M3 p)), ⟨_, rfl⟩⟩))
      ⟨fun x y h => by
        have h00 := congrArg (fun z => z.val 0 0) h
        have h11 := congrArg (fun z => z.val 1 1) h
        have h21 := congrArg (fun z => z.val 2 1) h
        simp at h00 h11 h21
        exact Prod.ext h00 (Prod.ext h11 (Subtype.ext h21)),
       fun B => by
        have hBp : Subring.closure ({B.val} : Set (M3 p)) = Subring.closure ({M} : Set (M3 p)) := B.prop
        have hB : B.val ∈ Subring.closure ({M} : Set (M3 p)) :=
          (SetLike.ext_iff.mp hBp B.val).mp (Subring.subset_closure rfl)
        obtain ⟨a, b, c, hc⟩ := (mem_closure_matH0 hqmon hqdeg hqirr B.val).mp hB
        have hcne := (gen_matH0_iff hqmon hqdeg hqirr htM a b c).mp (hc ▸ hBp)
        exact ⟨(a, b, ⟨c, hcne⟩), Subtype.ext hc.symm⟩⟩).symm
  rw [Nat.card_congr hbij, Nat.card_prod, Nat.card_prod, Nat.card_zmod]
  have hne0 : Nat.card { c : ZMod p // c ≠ 0 } = p - 1 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype_compl, ZMod.card, Fintype.card_unique]
  rw [hne0]; dsimp only [expectedGenCount]; ring

private lemma card_singleGens_of_type {p : ℕ} [Fact p.Prime] (t : M3Type)
    (v : UCCGVert p) (hv : v ∈ VertsOfType p t) :
    Nat.card (SingleGens v) = expectedGenCount p t := by
  obtain ⟨A, hAv, htA⟩ := hv
  have hv_eq : v = ⟨Subring.closure ({A} : Set (M3 p)), ⟨A, rfl⟩⟩ := Subtype.ext hAv.symm
  rw [hv_eq]
  cases t with
  | A => exact card_singleGens_A htA
  | B => exact card_singleGens_B htA
  | C => exact card_singleGens_C htA
  | D => exact card_singleGens_D htA
  | E => exact card_singleGens_E htA
  | F => exact card_singleGens_F htA
  | G => exact card_singleGens_G htA
  | H => exact card_singleGens_H htA

/-! ### Section 5: Projective Plane `PG(2, p)`, Rank-1 Matrices, Bijection `Φ`, and Theorem 4.1 -/

private lemma dotProduct_single_left {p : ℕ} (i : Fin 3) (c : ZMod p) (u : V3 p) :
    dotProduct (Pi.single i c) u = c * u i := by
  rw [dotProduct, Finset.sum_eq_single i]
  · simp
  · intro j _ hji; simp [Pi.single_eq_of_ne hji]
  · intro hi; exact absurd (Finset.mem_univ i) hi

private lemma finite_pgPoint {p : ℕ} [Fact p.Prime] : Finite (PGPoint p) :=
  Finite.of_injective (fun P : PGPoint p => (P.val : Set (V3 p)))
    (fun _ _ h => Subtype.ext (SetLike.coe_injective h))

private lemma finite_pgLine {p : ℕ} [Fact p.Prime] : Finite (PGLine p) :=
  Finite.of_injective (fun L : PGLine p => (L.val : Set (V3 p)))
    (fun _ _ h => Subtype.ext (SetLike.coe_injective h))

private lemma card_pgPoint {p : ℕ} [Fact p.Prime] :
    Nat.card (PGPoint p) = p ^ 2 + p + 1 := by
  classical
  have : Finite (PGPoint p) := finite_pgPoint
  let : Fintype (PGPoint p) := Fintype.ofFinite _
  have hp2 : 2 ≤ p := (Fact.out : p.Prime).two_le
  -- Map each nonzero `v : V3 p` to `span {v} ∈ PGPoint p`; each fiber has size `p - 1`.
  let NZ := { v : V3 p // v ≠ 0 }
  let toPt : NZ → PGPoint p := fun v =>
    ⟨Submodule.span (ZMod p) ({v.val} : Set (V3 p)), finrank_span_singleton v.prop⟩
  have hfiber : ∀ P : PGPoint p, (Finset.univ.filter fun v : NZ => toPt v = P).card = p - 1 := by
    intro P
    obtain ⟨u, hu0, hspan⟩ : ∃ u : V3 p, u ≠ 0 ∧ P.val = Submodule.span (ZMod p) ({u} : Set (V3 p)) := by
      have hne : P.val ≠ ⊥ := fun h => by have := P.prop; rw [h, finrank_bot] at this; omega
      obtain ⟨u, huP, hu0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
      have hle : Submodule.span (ZMod p) ({u} : Set (V3 p)) ≤ P.val :=
        Submodule.span_le.mpr (Set.singleton_subset_iff.mpr huP)
      have heq := Submodule.eq_of_le_of_finrank_eq hle (by rw [finrank_span_singleton hu0, P.prop])
      exact ⟨u, hu0, heq.symm⟩
    have hEq : (Finset.univ.filter fun v : NZ => toPt v = P) =
        (Finset.univ : Finset { c : ZMod p // c ≠ 0 }).image fun c => ⟨c.val • u, smul_ne_zero c.prop hu0⟩ := by
      ext v
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
      constructor
      · intro hv
        have hvP : v.val ∈ P.val := by
          have : v.val ∈ (toPt v).val := Submodule.subset_span rfl
          rwa [hv] at this
        rw [hspan, Submodule.mem_span_singleton] at hvP
        obtain ⟨c, hc⟩ := hvP
        have hc0 : c ≠ 0 := fun h => v.prop (by rw [← hc, h, zero_smul])
        exact ⟨⟨c, hc0⟩, Subtype.ext hc⟩
      · rintro ⟨⟨c, hc0⟩, rfl⟩
        apply Subtype.ext; dsimp only [toPt]; rw [hspan]
        apply Submodule.eq_of_le_of_finrank_eq
        · rw [Submodule.span_le, Set.singleton_subset_iff]
          exact Submodule.smul_mem _ c (Submodule.subset_span rfl)
        · rw [finrank_span_singleton (smul_ne_zero hc0 hu0), finrank_span_singleton hu0]
    rw [hEq, Finset.card_image_of_injective _ (fun a b h => by
      have h1 : (a.val - b.val) • u = 0 := by
        rw [sub_smul]; exact sub_eq_zero.mpr (congrArg Subtype.val h)
      exact Subtype.ext (sub_eq_zero.mp ((smul_eq_zero.mp h1).resolve_right hu0)))]
    rw [Finset.card_univ, Fintype.card_subtype_compl, ZMod.card, Fintype.card_unique]
  have hsum : Fintype.card NZ = ∑ P : PGPoint p, (Finset.univ.filter fun v : NZ => toPt v = P).card := by
    rw [← Finset.card_biUnion]
    · have : Finset.univ.biUnion (fun P : PGPoint p => Finset.univ.filter fun v : NZ => toPt v = P) = Finset.univ := by
        ext v; simp
      rw [this, Finset.card_univ]
    · intro P1 _ P2 _ hne
      change Disjoint _ _
      rw [Finset.disjoint_left]
      intro v h1 h2
      exact hne (((Finset.mem_filter.mp h1).2).symm.trans (Finset.mem_filter.mp h2).2)
  simp_rw [hfiber] at hsum
  rw [Finset.sum_const, Finset.card_univ, smul_eq_mul] at hsum
  have hNZ : Fintype.card NZ = p ^ 3 - 1 := by
    rw [Fintype.card_subtype_compl, Fintype.card_fun, ZMod.card, Fintype.card_fin, Fintype.card_unique]
  rw [hNZ] at hsum
  have hmul : (p ^ 2 + p + 1) * (p - 1) = p ^ 3 - 1 := by
    have : p ^ 3 = (p ^ 2 + p + 1) * (p - 1) + 1 := by
      zify [show 1 ≤ p by omega]; ring
    omega
  rw [Nat.card_eq_fintype_card]
  exact Nat.eq_of_mul_eq_mul_right (show 0 < p - 1 by omega) (hsum.symm.trans hmul.symm)

private def orthoSub {p : ℕ} [Fact p.Prime] (W : Submodule (ZMod p) (V3 p)) : Submodule (ZMod p) (V3 p) where
  carrier := { v | ∀ w ∈ W, dotProduct v w = 0 }
  add_mem' ha hb w hw := by rw [add_dotProduct, ha w hw, hb w hw, add_zero]
  zero_mem' w _ := zero_dotProduct w
  smul_mem' c x hx w hw := by rw [smul_dotProduct, hx w hw, smul_zero]

private lemma finrank_orthoSub_point {p : ℕ} [Fact p.Prime] (P : PGPoint p) :
    Module.finrank (ZMod p) (orthoSub P.val) = 2 := by
  classical
  have hne : P.val ≠ ⊥ := fun h => by have := P.prop; rw [h, finrank_bot] at this; omega
  obtain ⟨u, huP, hu0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  have hspan : P.val = Submodule.span (ZMod p) ({u} : Set (V3 p)) :=
    (Submodule.eq_of_le_of_finrank_eq (Submodule.span_le.mpr (Set.singleton_subset_iff.mpr huP))
      (by rw [finrank_span_singleton hu0, P.prop])).symm
  let φ : (V3 p) →ₗ[ZMod p] ZMod p :=
    { toFun := fun v => dotProduct v u
      map_add' := fun x y => add_dotProduct x y u
      map_smul' := fun c x => smul_dotProduct c x u }
  have hker : orthoSub P.val = LinearMap.ker φ := by
    ext v
    change (∀ w ∈ P.val, dotProduct v w = 0) ↔ dotProduct v u = 0
    rw [hspan]
    constructor
    · intro h; exact h u (Submodule.subset_span rfl)
    · intro h w hw
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hw
      rw [dotProduct_smul, h, smul_zero]
  have hsurj : LinearMap.range φ = ⊤ := by
    rw [eq_top_iff]; intro r _
    have hex : ∃ i : Fin 3, u i ≠ 0 := by
      by_contra hall; push Not at hall; exact hu0 (funext hall)
    obtain ⟨i, hi⟩ := hex
    refine ⟨Pi.single i (r * (u i)⁻¹), ?_⟩
    change dotProduct (Pi.single i (r * (u i)⁻¹)) u = r
    rw [dotProduct_single_left, mul_assoc, inv_mul_cancel₀ hi, mul_one]
  have hsum := LinearMap.finrank_range_add_finrank_ker φ
  rw [hsurj, finrank_top, Module.finrank_self, Module.finrank_fin_fun, ← hker] at hsum
  omega

private lemma finrank_orthoSub_span_singleton {p : ℕ} [Fact p.Prime] {w : V3 p} (hw : w ≠ 0) :
    Module.finrank (ZMod p) (orthoSub (Submodule.span (ZMod p) ({w} : Set (V3 p)))) = 2 :=
  finrank_orthoSub_point ⟨Submodule.span (ZMod p) ({w} : Set (V3 p)), finrank_span_singleton hw⟩

private lemma finrank_orthoSub_line {p : ℕ} [Fact p.Prime] (L : PGLine p) :
    Module.finrank (ZMod p) (orthoSub L.val) = 1 := by
  classical
  -- `L` has basis `v1, v2`, so `orthoSub L` is `ker (w ↦ (dotProduct w v1, dotProduct w v2))`!
  let b := Module.finBasis (ZMod p) L.val
  have h2 : Module.finrank (ZMod p) L.val = 2 := L.prop
  let u0 : V3 p := (b ⟨0, by omega⟩).val
  let u1 : V3 p := (b ⟨1, by omega⟩).val
  let φ : (V3 p) →ₗ[ZMod p] (Fin 2 → ZMod p) :=
    { toFun := fun v => ![dotProduct v u0, dotProduct v u1]
      map_add' := fun x y => by ext j; fin_cases j <;> simp [add_dotProduct]
      map_smul' := fun c x => by ext j; fin_cases j <;> simp [smul_dotProduct] }
  have hker : orthoSub L.val = LinearMap.ker φ := by
    ext v
    change (∀ w ∈ L.val, dotProduct v w = 0) ↔ ![dotProduct v u0, dotProduct v u1] = 0
    constructor
    · intro h; ext j; fin_cases j
      · exact h u0 (b ⟨0, by omega⟩).prop
      · exact h u1 (b ⟨1, by omega⟩).prop
    · intro h w hw
      have h0 : dotProduct v u0 = 0 := by simpa using congrFun h 0
      have h1 : dotProduct v u1 = 0 := by simpa using congrFun h 1
      have hrep := b.sum_repr ⟨w, hw⟩
      have hw_eq : w = (b.repr ⟨w, hw⟩ ⟨0, by omega⟩) • u0 + (b.repr ⟨w, hw⟩ ⟨1, by omega⟩) • u1 := by
        have hv := congrArg Subtype.val hrep
        rw [AddSubmonoidClass.coe_finsetSum] at hv
        simp only [SetLike.val_smul] at hv
        have hsum2 : ∑ i : Fin (Module.finrank (ZMod p) L.val), (b.repr ⟨w, hw⟩ i) • (b i).val =
            (b.repr ⟨w, hw⟩ ⟨0, by omega⟩) • u0 + (b.repr ⟨w, hw⟩ ⟨1, by omega⟩) • u1 := by
          rw [Fintype.sum_equiv (finCongr h2) _
            (fun j : Fin 2 => (b.repr ⟨w, hw⟩ ((finCongr h2).symm j)) • (b ((finCongr h2).symm j)).val)
            (fun i => by simp)]
          simp only [Fin.sum_univ_two, u0, u1]; rfl
        simpa [hsum2] using hv.symm
      rw [hw_eq, dotProduct_add, dotProduct_smul, dotProduct_smul, h0, h1, smul_zero, smul_zero, add_zero]
  -- Show `φ` is surjective (equivalently `u0, u1` linearly independent => the `2 × 3` matrix has rank 2!):
  have hsurj : LinearMap.range φ = ⊤ := by
    -- If `range φ ≠ ⊤`, `finrank (range φ) ≤ 1`, so `∃ (a, b) ≠ (0, 0)` with `∀ v, a*(v·u0) + b*(v·u1) = 0`,
    -- giving `a • u0 + b • u1 = 0`, contradicting linear independence of `b`!
    by_contra hntop
    have hlt : Module.finrank (ZMod p) (LinearMap.range φ) < 2 := by
      have hle : Module.finrank (ZMod p) (LinearMap.range φ) ≤ 2 := by
        simpa using Submodule.finrank_le (LinearMap.range φ)
      have hne : Module.finrank (ZMod p) (LinearMap.range φ) ≠ 2 := fun heq =>
        hntop (Submodule.eq_top_of_finrank_eq (by simpa using heq))
      omega
    -- Pick nonzero `(a, b) : Fin 2 → ZMod p` orthogonal to `range φ`
    have hex_ab : ∃ a b : ZMod p, (a ≠ 0 ∨ b ≠ 0) ∧ ∀ y ∈ LinearMap.range φ, a * y 0 + b * y 1 = 0 := by
      by_cases h0 : LinearMap.range φ = ⊥
      · exact ⟨1, 0, Or.inl one_ne_zero, fun y hy => by rw [h0] at hy; simp at hy; simp [hy]⟩
      · obtain ⟨y0, hy0, hy0_ne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h0
        have hge1 : 1 ≤ Module.finrank (ZMod p) (LinearMap.range φ) := by
          have := Submodule.finrank_mono (Submodule.span_le.mpr (Set.singleton_subset_iff.mpr hy0))
          rw [finrank_span_singleton hy0_ne] at this; exact this
        have hsp : LinearMap.range φ = Submodule.span (ZMod p) ({y0} : Set (Fin 2 → ZMod p)) :=
          (Submodule.eq_of_le_of_finrank_eq (Submodule.span_le.mpr (Set.singleton_subset_iff.mpr hy0))
            (by rw [finrank_span_singleton hy0_ne]; omega)).symm
        refine ⟨-y0 1, y0 0, ?_, fun y hy => ?_⟩
        · by_contra hall; push Not at hall
          apply hy0_ne; ext j; fin_cases j
          · exact hall.2
          · exact neg_eq_zero.mp hall.1
        · rw [hsp, Submodule.mem_span_singleton] at hy
          obtain ⟨c, rfl⟩ := hy; simp; ring
    obtain ⟨a, b', hab, horth⟩ := hex_ab
    have hcomb : a • u0 + b' • u1 = 0 := by
      ext i
      have hi := horth (φ (Pi.single i 1)) ⟨Pi.single i 1, rfl⟩
      simp only [φ, LinearMap.coe_mk, AddHom.coe_mk, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_fin_one, dotProduct_single_left, one_mul] at hi
      simpa using hi
    have hlin : (a • b ⟨0, by omega⟩ + b' • b ⟨1, by omega⟩ : L.val) = 0 := Subtype.ext hcomb
    have hrepr0 := congrArg (fun x => b.repr x ⟨0, by omega⟩) hlin
    have hrepr1 := congrArg (fun x => b.repr x ⟨1, by omega⟩) hlin
    simp only [map_add, map_smul, map_zero, Module.Basis.repr_self, Finsupp.add_apply, Finsupp.smul_apply,
      Finsupp.zero_apply, Finsupp.single_apply, smul_eq_mul] at hrepr0 hrepr1
    have h01 : (⟨0, by omega⟩ : Fin (Module.finrank (ZMod p) L.val)) ≠ ⟨1, by omega⟩ := by
      intro h; have := congrArg Fin.val h; simp at this
    simp [h01, h01.symm] at hrepr0 hrepr1
    rcases hab with ha | hb <;> contradiction
  have hsum := LinearMap.finrank_range_add_finrank_ker φ
  rw [hsurj, finrank_top, Module.finrank_fin_fun, Module.finrank_fin_fun, ← hker] at hsum
  omega

private lemma orthoSub_orthoSub {p : ℕ} [Fact p.Prime] (W : Submodule (ZMod p) (V3 p))
    (hW : Module.finrank (ZMod p) W = 1 ∨ Module.finrank (ZMod p) W = 2) :
    orthoSub (orthoSub W) = W := by
  have hle : W ≤ orthoSub (orthoSub W) := fun w hw v hv => by
    rw [dotProduct_comm]; exact hv w hw
  rcases hW with h1 | h2
  · have hd1 : Module.finrank (ZMod p) (orthoSub W) = 2 := finrank_orthoSub_point ⟨W, h1⟩
    have hd2 : Module.finrank (ZMod p) (orthoSub (orthoSub W)) = 1 := finrank_orthoSub_line ⟨orthoSub W, hd1⟩
    exact (Submodule.eq_of_le_of_finrank_eq hle (by omega)).symm
  · have hd1 : Module.finrank (ZMod p) (orthoSub W) = 1 := finrank_orthoSub_line ⟨W, h2⟩
    have hd2 : Module.finrank (ZMod p) (orthoSub (orthoSub W)) = 2 := finrank_orthoSub_point ⟨orthoSub W, hd1⟩
    exact (Submodule.eq_of_le_of_finrank_eq hle (by omega)).symm

private lemma card_pgLine {p : ℕ} [Fact p.Prime] :
    Nat.card (PGLine p) = p ^ 2 + p + 1 := by
  let e : PGLine p ≃ PGPoint p :=
    { toFun := fun L => ⟨orthoSub L.val, finrank_orthoSub_line L⟩
      invFun := fun P => ⟨orthoSub P.val, finrank_orthoSub_point P⟩
      left_inv := fun L => Subtype.ext (orthoSub_orthoSub L.val (Or.inr L.prop))
      right_inv := fun P => Subtype.ext (orthoSub_orthoSub P.val (Or.inl P.prop)) }
  rw [Nat.card_congr e, card_pgPoint]

private lemma card_points_on_line {p : ℕ} [Fact p.Prime] (L : PGLine p) :
    Nat.card { P : PGPoint p // P.val ≤ L.val } = p + 1 := by
  classical
  have : Finite (PGPoint p) := finite_pgPoint
  let : Fintype { P : PGPoint p // P.val ≤ L.val } := Fintype.ofFinite _
  have hp2 : 2 ≤ p := (Fact.out : p.Prime).two_le
  let NZL := { v : V3 p // v ∈ L.val ∧ v ≠ 0 }
  let toPt : NZL → { P : PGPoint p // P.val ≤ L.val } := fun v =>
    ⟨⟨Submodule.span (ZMod p) ({v.val} : Set (V3 p)), finrank_span_singleton v.prop.2⟩,
      Submodule.span_le.mpr (Set.singleton_subset_iff.mpr v.prop.1)⟩
  have hfiber : ∀ P : { P : PGPoint p // P.val ≤ L.val },
      (Finset.univ.filter fun v : NZL => toPt v = P).card = p - 1 := by
    intro P
    have hne : P.val.val ≠ ⊥ := fun h => by have := P.val.prop; rw [h, finrank_bot] at this; omega
    obtain ⟨u, huP, hu0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
    have hspan : P.val.val = Submodule.span (ZMod p) ({u} : Set (V3 p)) :=
      (Submodule.eq_of_le_of_finrank_eq (Submodule.span_le.mpr (Set.singleton_subset_iff.mpr huP))
        (by rw [finrank_span_singleton hu0, P.val.prop])).symm
    have hEq : (Finset.univ.filter fun v : NZL => toPt v = P) =
        (Finset.univ : Finset { c : ZMod p // c ≠ 0 }).image fun c =>
          ⟨c.val • u, Submodule.smul_mem _ c.val (P.prop huP), smul_ne_zero c.prop hu0⟩ := by
      ext v
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
      constructor
      · intro hv
        have hvP : v.val ∈ P.val.val := by
          have : v.val ∈ (toPt v).val.val := Submodule.subset_span rfl
          rwa [hv] at this
        rw [hspan, Submodule.mem_span_singleton] at hvP
        obtain ⟨c, hc⟩ := hvP
        have hc0 : c ≠ 0 := fun h => v.prop.2 (by rw [← hc, h, zero_smul])
        exact ⟨⟨c, hc0⟩, Subtype.ext hc⟩
      · rintro ⟨⟨c, hc0⟩, rfl⟩
        apply Subtype.ext; apply Subtype.ext; dsimp only [toPt]; rw [hspan]
        apply Submodule.eq_of_le_of_finrank_eq
        · rw [Submodule.span_le, Set.singleton_subset_iff]
          exact Submodule.smul_mem _ c (Submodule.subset_span rfl)
        · rw [finrank_span_singleton (smul_ne_zero hc0 hu0), finrank_span_singleton hu0]
    rw [hEq, Finset.card_image_of_injective _ (fun a b h => by
      have h1 : (a.val - b.val) • u = 0 := by rw [sub_smul]; exact sub_eq_zero.mpr (congrArg Subtype.val h)
      exact Subtype.ext (sub_eq_zero.mp ((smul_eq_zero.mp h1).resolve_right hu0)))]
    rw [Finset.card_univ, Fintype.card_subtype_compl, ZMod.card, Fintype.card_unique]
  have hsum : Fintype.card NZL = ∑ P : { P : PGPoint p // P.val ≤ L.val },
      (Finset.univ.filter fun v : NZL => toPt v = P).card := by
    rw [← Finset.card_biUnion]
    · have : Finset.univ.biUnion (fun P : { P : PGPoint p // P.val ≤ L.val } =>
          Finset.univ.filter fun v : NZL => toPt v = P) = Finset.univ := by ext v; simp
      rw [this, Finset.card_univ]
    · intro P1 _ P2 _ hne; change Disjoint _ _; rw [Finset.disjoint_left]
      intro v h1 h2; exact hne (((Finset.mem_filter.mp h1).2).symm.trans (Finset.mem_filter.mp h2).2)
  simp_rw [hfiber] at hsum
  rw [Finset.sum_const, Finset.card_univ, smul_eq_mul] at hsum
  have hNZL : Fintype.card NZL = p ^ 2 - 1 := by
    have hLcard : Fintype.card L.val = p ^ 2 := by
      rw [Module.card_eq_pow_finrank (K := ZMod p), ZMod.card, L.prop]
    have heq : NZL ≃ { x : L.val // x ≠ 0 } :=
      { toFun := fun v => ⟨⟨v.val, v.prop.1⟩, fun h => v.prop.2 (congrArg Subtype.val h)⟩
        invFun := fun x => ⟨x.val.val, x.val.prop, fun h => x.prop (Subtype.ext h)⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    rw [Fintype.card_congr heq, Fintype.card_subtype_compl, hLcard, Fintype.card_unique]
  rw [hNZL] at hsum
  have hmul : (p + 1) * (p - 1) = p ^ 2 - 1 := by
    have : p ^ 2 = (p + 1) * (p - 1) + 1 := by zify [show 1 ≤ p by omega]; ring
    omega
  rw [Nat.card_eq_fintype_card]
  exact Nat.eq_of_mul_eq_mul_right (show 0 < p - 1 by omega) (hsum.symm.trans hmul.symm)

/-! ### Section 5B: Rank-1 Matrices, Bijection `Φ : V_(B) ∪ V_(E) ≃ PG(2, p) × PG(2, p)^*`, Theorem 4.1, and `|V_(B)|, |V_(E)|` -/

private lemma rank1_eq_vecMulVec {p : ℕ} [Fact p.Prime] {A : M3 p}
    (h1 : Module.finrank (ZMod p) (LinearMap.range (Matrix.toLin' A)) = 1) :
    ∃ u w : V3 p, u ≠ 0 ∧ w ≠ 0 ∧ A = Matrix.vecMulVec u w := by
  classical
  have hne : LinearMap.range (Matrix.toLin' A) ≠ ⊥ := fun h => by rw [h, finrank_bot] at h1; omega
  obtain ⟨u, huR, hu0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  have hspan : LinearMap.range (Matrix.toLin' A) = Submodule.span (ZMod p) ({u} : Set (V3 p)) :=
    (Submodule.eq_of_le_of_finrank_eq (Submodule.span_le.mpr (Set.singleton_subset_iff.mpr huR))
      (by rw [finrank_span_singleton hu0, h1])).symm
  -- Each column `j` of `A` is in `range A = span {u}`, so `col j = w j • u`!
  have hcol : ∀ j : Fin 3, ∃ c : ZMod p, A *ᵥ Pi.single j 1 = c • u := fun j => by
    have hmem : A *ᵥ Pi.single j 1 ∈ Submodule.span (ZMod p) ({u} : Set (V3 p)) :=
      hspan ▸ ⟨Pi.single j 1, rfl⟩
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hmem
    exact ⟨c, hc.symm⟩
  let w : V3 p := fun j => Classical.choose (hcol j)
  have hAeq : A = Matrix.vecMulVec u w := by
    ext i j
    have hj := congrFun (Classical.choose_spec (hcol j)) i
    change dotProduct (A i) (Pi.single j 1) = w j * u i at hj
    rw [dotProduct_comm, dotProduct_single_left, one_mul] at hj
    rw [hj, Matrix.vecMulVec_apply, mul_comm]
  have hw0 : w ≠ 0 := by
    intro h0
    have hA0 : A = 0 := by ext i j; rw [hAeq, h0]; simp [Matrix.vecMulVec_apply]
    apply hne; rw [hA0]; ext x; simp
  exact ⟨u, w, hu0, hw0, hAeq⟩

private lemma vecMulVec_mulVec {p : ℕ} (u w x : V3 p) :
    (Matrix.vecMulVec u w) *ᵥ x = (dotProduct w x) • u := by
  ext i
  simp only [Matrix.mulVec, dotProduct, Matrix.vecMulVec_apply, Pi.smul_apply, smul_eq_mul,
    Finset.sum_mul]
  refine Finset.sum_congr rfl fun j _ => by ring

private lemma vecMulVec_mul_vecMulVec {p : ℕ} (u₁ w₁ u₂ w₂ : V3 p) :
    Matrix.vecMulVec u₁ w₁ * Matrix.vecMulVec u₂ w₂ = (dotProduct w₁ u₂) • Matrix.vecMulVec u₁ w₂ := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.vecMulVec_apply, Matrix.smul_apply, smul_eq_mul, dotProduct,
    Finset.sum_mul]
  refine Finset.sum_congr rfl fun k _ => by ring

private lemma range_vecMulVec {p : ℕ} [Fact p.Prime] {u w : V3 p} (_hu : u ≠ 0) (hw : w ≠ 0) :
    LinearMap.range (Matrix.toLin' (Matrix.vecMulVec u w)) = Submodule.span (ZMod p) ({u} : Set (V3 p)) := by
  ext x
  simp only [LinearMap.mem_range, Matrix.toLin'_apply, vecMulVec_mulVec, Submodule.mem_span_singleton]
  constructor
  · rintro ⟨y, rfl⟩; exact ⟨dotProduct w y, rfl⟩
  · rintro ⟨c, rfl⟩
    have hex : ∃ j : Fin 3, w j ≠ 0 := by
      by_contra hall; push Not at hall; exact hw (funext hall)
    obtain ⟨j, hj⟩ := hex
    refine ⟨Pi.single j (c * (w j)⁻¹), ?_⟩
    have hdot : dotProduct w (Pi.single j (c * (w j)⁻¹)) = c := by
      rw [dotProduct_comm, dotProduct_single_left, mul_assoc, inv_mul_cancel₀ hj, mul_one]
    rw [hdot]

private lemma ker_vecMulVec {p : ℕ} [Fact p.Prime] {u w : V3 p} (hu : u ≠ 0) :
    LinearMap.ker (Matrix.toLin' (Matrix.vecMulVec u w)) = orthoSub (Submodule.span (ZMod p) ({w} : Set (V3 p))) := by
  ext x
  simp only [LinearMap.mem_ker, Matrix.toLin'_apply, vecMulVec_mulVec]
  change (dotProduct w x) • u = 0 ↔ ∀ y ∈ Submodule.span (ZMod p) ({w} : Set (V3 p)), dotProduct x y = 0
  rw [smul_eq_zero]
  constructor
  · intro h y hy
    have hwx : dotProduct w x = 0 := h.resolve_right hu
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hy
    rw [dotProduct_smul, dotProduct_comm, hwx, smul_zero]
  · intro h
    left; rw [dotProduct_comm]; exact h w (Submodule.subset_span rfl)

private lemma vecMulVec_eq_iff {p : ℕ} [Fact p.Prime] {u₁ w₁ u₂ w₂ : V3 p}
    (hu₁ : u₁ ≠ 0) (hw₁ : w₁ ≠ 0) (hu₂ : u₂ ≠ 0) (hw₂ : w₂ ≠ 0) :
    (∃ c : ZMod p, c ≠ 0 ∧ Matrix.vecMulVec u₁ w₁ = c • Matrix.vecMulVec u₂ w₂) ↔
      Submodule.span (ZMod p) ({u₁} : Set (V3 p)) = Submodule.span (ZMod p) ({u₂} : Set (V3 p)) ∧
      orthoSub (Submodule.span (ZMod p) ({w₁} : Set (V3 p))) = orthoSub (Submodule.span (ZMod p) ({w₂} : Set (V3 p))) := by
  constructor
  · rintro ⟨c, hc, hEq⟩
    have h1 : LinearMap.range (Matrix.toLin' (Matrix.vecMulVec u₁ w₁)) =
        LinearMap.range (Matrix.toLin' (Matrix.vecMulVec u₂ w₂)) := by
      rw [hEq]; ext x
      simp only [LinearMap.mem_range, Matrix.toLin'_apply, Matrix.smul_mulVec]
      constructor
      · rintro ⟨y, rfl⟩; exact ⟨c • y, by rw [Matrix.mulVec_smul]⟩
      · rintro ⟨y, rfl⟩; exact ⟨c⁻¹ • y, by rw [Matrix.mulVec_smul, smul_smul, mul_inv_cancel₀ hc, one_smul]⟩
    have h2 : LinearMap.ker (Matrix.toLin' (Matrix.vecMulVec u₁ w₁)) =
        LinearMap.ker (Matrix.toLin' (Matrix.vecMulVec u₂ w₂)) := by
      rw [hEq]; ext x
      simp only [LinearMap.mem_ker, Matrix.toLin'_apply, Matrix.smul_mulVec, smul_eq_zero, hc, false_or]
    rw [range_vecMulVec hu₁ hw₁, range_vecMulVec hu₂ hw₂] at h1
    rw [ker_vecMulVec hu₁, ker_vecMulVec hu₂] at h2
    exact ⟨h1, h2⟩
  · rintro ⟨hU, hL⟩
    have hu1_in : u₁ ∈ Submodule.span (ZMod p) ({u₂} : Set (V3 p)) := hU ▸ Submodule.subset_span rfl
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hu1_in
    have ha0 : a ≠ 0 := fun h => hu₁ (by rw [← ha, h, zero_smul])
    have hW : Submodule.span (ZMod p) ({w₁} : Set (V3 p)) = Submodule.span (ZMod p) ({w₂} : Set (V3 p)) := by
      have h1 := orthoSub_orthoSub (Submodule.span (ZMod p) ({w₁} : Set (V3 p))) (Or.inl (finrank_span_singleton hw₁))
      have h2 := orthoSub_orthoSub (Submodule.span (ZMod p) ({w₂} : Set (V3 p))) (Or.inl (finrank_span_singleton hw₂))
      rw [← h1, ← h2, hL]
    have hw1_in : w₁ ∈ Submodule.span (ZMod p) ({w₂} : Set (V3 p)) := hW ▸ Submodule.subset_span rfl
    obtain ⟨b, hb⟩ := Submodule.mem_span_singleton.mp hw1_in
    have hb0 : b ≠ 0 := fun h => hw₁ (by rw [← hb, h, zero_smul])
    refine ⟨a * b, mul_ne_zero ha0 hb0, ?_⟩
    ext i j; rw [← ha, ← hb]; simp [Matrix.vecMulVec_apply]; ring

/-- Every `v ∈ V_(B)` has a unique rank-1 idempotent generator `P` (`P^2 = P`, `rank P = 1`).
    Every `v ∈ V_(E)` has a rank-1 nilpotent generator `N` (`N^2 = 0`, `rank N = 1`), unique up to nonzero scalar. -/
private lemma exists_rank1_gen_B {p : ℕ} [Fact p.Prime] {v : UCCGVert p} (hv : VertHasType v .B) :
    ∃ A : M3 p, A ∈ SingleGens v ∧ A ^ 2 = A ∧
      Module.finrank (ZMod p) (LinearMap.range (Matrix.toLin' A)) = 1 ∧
      Module.finrank (ZMod p) (LinearMap.ker (Matrix.toLin' A)) = 2 ∧
      ¬ LinearMap.range (Matrix.toLin' A) ≤ LinearMap.ker (Matrix.toLin' A) := by
  obtain ⟨M, hMv, hMB⟩ := hv
  obtain ⟨S, hS⟩ := canonical_B hMB
  set A := (conjAlgEquiv S).symm (matB0 p)
  have hAv : A ∈ SingleGens v := by
    show Subring.closure ({A} : Set (M3 p)) = v.val
    rw [← hMv]
    have h1 := congrArg (Subring.map (conjAlgEquiv S).symm.toRingHom) hS
    rw [subring_map_closure, subring_map_closure, Set.image_singleton, Set.image_singleton] at h1
    simpa [A] using h1.symm
  have hB0_sq : matB0 p ^ 2 = matB0 p := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [matB0, sq, Matrix.mul_apply, Fin.sum_univ_three]
  have hA2 : A ^ 2 = A := by
    show (conjAlgEquiv S).symm (matB0 p) ^ 2 = (conjAlgEquiv S).symm (matB0 p)
    rw [← map_pow, hB0_sq]
  -- Also `A = vecMulVec (S⁻¹ *ᵥ e0) (e0 ᵥ* S)` so `rank A = 1`!
  have hmatB0_vec : matB0 p = Matrix.vecMulVec (Pi.single 0 1) (Pi.single 0 1) := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [matB0, Matrix.vecMulVec_apply]
  have hAvec : A = Matrix.vecMulVec ((↑S⁻¹ : M3 p) *ᵥ Pi.single 0 1) ((Pi.single 0 1) ᵥ* S.val) := by
    change (↑S⁻¹ : M3 p) * matB0 p * S.val = _
    rw [hmatB0_vec]
    ext i j
    simp only [Matrix.mul_apply, Matrix.vecMulVec_apply, Matrix.mulVec, Matrix.vecMul, dotProduct,
      Fin.sum_univ_three, Pi.single_apply]
    simp
  have hu0 : ((↑S⁻¹ : M3 p) *ᵥ Pi.single 0 1) ≠ 0 := by
    intro h0
    have h1 := congrArg (S.val *ᵥ ·) h0
    rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec, Matrix.mulVec_zero] at h1
    have := congrFun h1 0; simp at this
  have hw0 : ((Pi.single 0 1) ᵥ* S.val) ≠ 0 := by
    intro h0
    have h1 := congrArg (· ᵥ* (↑S⁻¹ : M3 p)) h0
    rw [Matrix.vecMul_vecMul, Units.mul_inv, Matrix.vecMul_one, Matrix.zero_vecMul] at h1
    have := congrFun h1 0; simp at this
  have hran : LinearMap.range (Matrix.toLin' A) = Submodule.span (ZMod p) ({(↑S⁻¹ : M3 p) *ᵥ Pi.single 0 1} : Set (V3 p)) :=
    hAvec ▸ range_vecMulVec hu0 hw0
  have hker : LinearMap.ker (Matrix.toLin' A) = orthoSub (Submodule.span (ZMod p) ({(Pi.single 0 1) ᵥ* S.val} : Set (V3 p))) :=
    hAvec ▸ ker_vecMulVec hu0
  have hdot1 : dotProduct ((Pi.single 0 1) ᵥ* S.val) ((↑S⁻¹ : M3 p) *ᵥ Pi.single 0 1) = 1 := by
    rw [Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul, Units.mul_inv, Matrix.vecMul_one,
      dotProduct_single_left, one_mul, Pi.single_eq_same]
  refine ⟨A, hAv, hA2, ?_, ?_, ?_⟩
  · rw [hran, finrank_span_singleton hu0]
  · rw [hker]; exact finrank_orthoSub_span_singleton hw0
  · intro hle
    have hmem : ((↑S⁻¹ : M3 p) *ᵥ Pi.single 0 1) ∈ LinearMap.ker (Matrix.toLin' A) :=
      hle (hran ▸ Submodule.subset_span rfl)
    rw [hker] at hmem
    have h0 := hmem ((Pi.single 0 1) ᵥ* S.val) (Submodule.subset_span rfl)
    rw [dotProduct_comm, hdot1] at h0
    exact one_ne_zero h0

private lemma exists_rank1_gen_E {p : ℕ} [Fact p.Prime] {v : UCCGVert p} (hv : VertHasType v .E) :
    ∃ A : M3 p, A ∈ SingleGens v ∧ A ^ 2 = 0 ∧
      Module.finrank (ZMod p) (LinearMap.range (Matrix.toLin' A)) = 1 ∧
      Module.finrank (ZMod p) (LinearMap.ker (Matrix.toLin' A)) = 2 ∧
      LinearMap.range (Matrix.toLin' A) ≤ LinearMap.ker (Matrix.toLin' A) := by
  obtain ⟨M, hMv, hME⟩ := hv
  obtain ⟨S, hS⟩ := canonical_E hME
  set A := (conjAlgEquiv S).symm (matE01 p)
  have hAv : A ∈ SingleGens v := by
    show Subring.closure ({A} : Set (M3 p)) = v.val
    rw [← hMv]
    have h1 := congrArg (Subring.map (conjAlgEquiv S).symm.toRingHom) hS
    rw [subring_map_closure, subring_map_closure, Set.image_singleton, Set.image_singleton] at h1
    simpa [A] using h1.symm
  have hE_sq : matE01 p ^ 2 = 0 := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [matE01, sq, Matrix.mul_apply, Fin.sum_univ_three]
  have hA2 : A ^ 2 = 0 := by
    show (conjAlgEquiv S).symm (matE01 p) ^ 2 = 0
    rw [← map_pow, hE_sq, map_zero]
  have hmatE_vec : matE01 p = Matrix.vecMulVec (Pi.single 0 1) (Pi.single 1 1) := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [matE01, Matrix.vecMulVec_apply]
  have hAvec : A = Matrix.vecMulVec ((↑S⁻¹ : M3 p) *ᵥ Pi.single 0 1) ((Pi.single 1 1) ᵥ* S.val) := by
    change (↑S⁻¹ : M3 p) * matE01 p * S.val = _
    rw [hmatE_vec]
    ext i j
    simp only [Matrix.mul_apply, Matrix.vecMulVec_apply, Matrix.mulVec, Matrix.vecMul, dotProduct,
      Fin.sum_univ_three, Pi.single_apply]
    simp
  have hu0 : ((↑S⁻¹ : M3 p) *ᵥ Pi.single 0 1) ≠ 0 := by
    intro h0
    have h1 := congrArg (S.val *ᵥ ·) h0
    rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec, Matrix.mulVec_zero] at h1
    have := congrFun h1 0; simp at this
  have hw0 : ((Pi.single 1 1) ᵥ* S.val) ≠ 0 := by
    intro h0
    have h1 := congrArg (· ᵥ* (↑S⁻¹ : M3 p)) h0
    rw [Matrix.vecMul_vecMul, Units.mul_inv, Matrix.vecMul_one, Matrix.zero_vecMul] at h1
    have := congrFun h1 1; simp at this
  refine ⟨A, hAv, hA2, ?_, ?_, ?_⟩
  · rw [hAvec, range_vecMulVec hu0 hw0, finrank_span_singleton hu0]
  · rw [hAvec, ker_vecMulVec hu0]; exact finrank_orthoSub_span_singleton hw0
  · rintro _ ⟨x, rfl⟩
    show A *ᵥ (A *ᵥ x) = 0
    rw [Matrix.mulVec_mulVec, ← sq, hA2, Matrix.zero_mulVec]

private lemma hasM3Type_matE01 (p : ℕ) [Fact p.Prime] : HasM3Type (matE01 p) .E := by
  refine ⟨0, ?_, ?_⟩
  · rw [Matrix.charpoly, Matrix.det_fin_three]
    simp [matE01, Matrix.charmatrix]; ring
  · have hsq : (matE01 p) ^ 2 = 0 := by
      ext i j; fin_cases i <;> fin_cases j <;> simp [matE01, sq, Matrix.mul_apply, Fin.sum_univ_three]
    have hdvd : minpoly (ZMod p) (matE01 p) ∣ (X - C (0 : ZMod p)) ^ 2 :=
      minpoly.dvd (ZMod p) _ (by simpa [Algebra.algebraMap_eq_smul_one] using hsq)
    have hpos := minpoly_natDegree_pos (matE01 p)
    have hle := Polynomial.natDegree_le_of_dvd hdvd ((Polynomial.monic_X_sub_C (0 : ZMod p)).pow 2).ne_zero
    rw [Polynomial.natDegree_pow, Polynomial.natDegree_X_sub_C] at hle
    have hne1 : (minpoly (ZMod p) (matE01 p)).natDegree ≠ 1 := by
      intro h1
      have h0r : (minpoly (ZMod p) (matE01 p)).IsRoot 0 :=
        (isRoot_minpoly_iff_charpoly (matE01 p) 0).mpr (by
          rw [Polynomial.IsRoot, Matrix.charpoly, Matrix.det_fin_three]
          simp [matE01, Matrix.charmatrix])
      have hm0 : minpoly (ZMod p) (matE01 p) = X - C (0 : ZMod p) :=
        Polynomial.eq_of_monic_of_dvd_of_natDegree_le
          (Polynomial.monic_X_sub_C (0 : ZMod p))
          (minpoly.monic (isIntegral_m3 (matE01 p)))
          (Polynomial.dvd_iff_isRoot.mpr h0r)
          (by rw [Polynomial.natDegree_X_sub_C]; omega)
      have hzero := minpoly.aeval (ZMod p) (matE01 p)
      rw [hm0] at hzero; simp at hzero
      have := congrArg (fun M : M3 p => M 0 1) hzero; simp [matE01] at this
    exact (Polynomial.eq_of_monic_of_dvd_of_natDegree_le
      (minpoly.monic (isIntegral_m3 (matE01 p)))
      ((Polynomial.monic_X_sub_C (0 : ZMod p)).pow 2) hdvd
      (by rw [Polynomial.natDegree_pow, Polynomial.natDegree_X_sub_C]; omega)).symm

private lemma hasM3Type_matB0 (p : ℕ) [Fact p.Prime] : HasM3Type (matB0 p) .B := by
  refine ⟨1, 0, one_ne_zero, ?_, ?_⟩
  · rw [Matrix.charpoly, Matrix.det_fin_three]
    simp [matB0, Matrix.charmatrix]; ring
  · have hsq : (matB0 p - 1 • (1 : M3 p)) * (matB0 p - 0 • (1 : M3 p)) = 0 := by
      ext i j; fin_cases i <;> fin_cases j <;> simp [matB0, Matrix.mul_apply, Fin.sum_univ_three]
    have hdvd := minpoly.dvd (ZMod p) (matB0 p)
      (show aeval (matB0 p) ((X - C (1 : ZMod p)) * (X - C (0 : ZMod p))) = 0 by
        simpa [Algebra.algebraMap_eq_smul_one] using hsq)
    have h1r : (minpoly (ZMod p) (matB0 p)).IsRoot 1 :=
      (isRoot_minpoly_iff_charpoly (matB0 p) 1).mpr (by
        rw [Polynomial.IsRoot, Matrix.charpoly, Matrix.det_fin_three]
        simp [matB0, Matrix.charmatrix])
    have h0r : (minpoly (ZMod p) (matB0 p)).IsRoot 0 :=
      (isRoot_minpoly_iff_charpoly (matB0 p) 0).mpr (by
        rw [Polynomial.IsRoot, Matrix.charpoly, Matrix.det_fin_three]
        simp [matB0, Matrix.charmatrix])
    obtain ⟨M1, hM1⟩ := Polynomial.dvd_iff_isRoot.mpr h1r
    have h0M1 : M1.IsRoot 0 := by
      rw [Polynomial.IsRoot, hM1, Polynomial.eval_mul] at h0r
      exact (mul_eq_zero.mp h0r).resolve_left (by simp)
    obtain ⟨M2, hM2⟩ := Polynomial.dvd_iff_isRoot.mpr h0M1
    have hdvd2 : (X - C (1 : ZMod p)) * (X - C (0 : ZMod p)) ∣ minpoly (ZMod p) (matB0 p) :=
      ⟨M2, by rw [hM1, hM2, mul_assoc]⟩
    exact (Polynomial.eq_of_monic_of_dvd_of_natDegree_le
      (minpoly.monic (isIntegral_m3 (matB0 p)))
      ((Polynomial.monic_X_sub_C (1 : ZMod p)).mul (Polynomial.monic_X_sub_C (0 : ZMod p))) hdvd
      (Polynomial.natDegree_le_of_dvd hdvd2 (minpoly.monic (isIntegral_m3 (matB0 p))).ne_zero)).symm

/-- Construct the canonical rank-1 matrix for any `(P, L) ∈ PGPoint p × PGLine p`:
    if `¬ P ≤ L`, it's a Type B idempotent; if `P ≤ L`, it's a Type E nilpotent! -/
private lemma exists_rank1_of_point_line {p : ℕ} [Fact p.Prime] (P : PGPoint p) (L : PGLine p) :
    ∃ A : M3 p,
      LinearMap.range (Matrix.toLin' A) = P.val ∧
      LinearMap.ker (Matrix.toLin' A) = L.val ∧
      (¬ P.val ≤ L.val → HasM3Type A .B ∧ A ^ 2 = A) ∧
      (P.val ≤ L.val → HasM3Type A .E ∧ A ^ 2 = 0) := by
  classical
  have hPne : P.val ≠ ⊥ := fun h => by have := P.prop; rw [h, finrank_bot] at this; omega
  obtain ⟨u, huP, hu0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hPne
  have hPspan : P.val = Submodule.span (ZMod p) ({u} : Set (V3 p)) :=
    (Submodule.eq_of_le_of_finrank_eq (Submodule.span_le.mpr (Set.singleton_subset_iff.mpr huP))
      (by rw [finrank_span_singleton hu0, P.prop])).symm
  have hLo1 : Module.finrank (ZMod p) (orthoSub L.val) = 1 := finrank_orthoSub_line L
  have hLone : orthoSub L.val ≠ ⊥ := fun h => by rw [h, finrank_bot] at hLo1; omega
  obtain ⟨w, hwL, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hLone
  have hLospan : orthoSub L.val = Submodule.span (ZMod p) ({w} : Set (V3 p)) :=
    (Submodule.eq_of_le_of_finrank_eq (Submodule.span_le.mpr (Set.singleton_subset_iff.mpr hwL))
      (by rw [finrank_span_singleton hw0, hLo1])).symm
  have hLker : orthoSub (Submodule.span (ZMod p) ({w} : Set (V3 p))) = L.val := by
    rw [← hLospan]; exact orthoSub_orthoSub L.val (Or.inr L.prop)
  by_cases hinc : P.val ≤ L.val
  · set A := Matrix.vecMulVec u w
    have hdot0 : dotProduct w u = 0 := hwL u (hinc huP)
    have hA2 : A ^ 2 = 0 := by rw [sq, vecMulVec_mul_vecMulVec, hdot0, zero_smul]
    have hA0 : A ≠ 0 := by
      intro h0
      have : LinearMap.range (Matrix.toLin' A) = ⊥ := by rw [h0]; ext x; simp
      rw [range_vecMulVec hu0 hw0, ← hPspan] at this; exact hPne this
    obtain ⟨S, hS⟩ := exists_conj_matE01 hA0 hA2
    refine ⟨A, (range_vecMulVec hu0 hw0).trans hPspan.symm, (ker_vecMulVec hu0).trans hLker,
      fun hn => absurd hinc hn, fun _ => ⟨(hasM3Type_conj S A .E).mp (hS ▸ hasM3Type_matE01 p), hA2⟩⟩
  · have hdot_ne : dotProduct w u ≠ 0 := by
      intro h0
      apply hinc; rw [hPspan, Submodule.span_le, Set.singleton_subset_iff, ← hLker]
      intro y hy
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hy
      rw [dotProduct_smul, dotProduct_comm, h0, smul_zero]
    set w' := (dotProduct w u)⁻¹ • w
    have hw'0 : w' ≠ 0 := smul_ne_zero (inv_ne_zero hdot_ne) hw0
    set A := Matrix.vecMulVec u w'
    have hdot1 : dotProduct w' u = 1 := by
      simp [w', smul_dotProduct, inv_mul_cancel₀ hdot_ne]
    have hA2 : A ^ 2 = A := by
      rw [sq, vecMulVec_mul_vecMulVec, hdot1, one_smul]
    have hker' : LinearMap.ker (Matrix.toLin' A) = L.val := by
      rw [ker_vecMulVec hu0, ← hLker]
      congr 1; apply Submodule.eq_of_le_of_finrank_eq
      · rw [Submodule.span_le, Set.singleton_subset_iff]
        exact Submodule.smul_mem _ _ (Submodule.subset_span rfl)
      · rw [finrank_span_singleton hw'0, finrank_span_singleton hw0]
    have hLne : L.val ≠ ⊥ := fun h => by have := L.prop; rw [h, finrank_bot] at this; omega
    obtain ⟨v1, hv1L, hv1_ne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hLne
    have hex_v2 : ∃ v2 : V3 p, v2 ∈ L.val ∧ ∀ c : ZMod p, v2 ≠ c • v1 := by
      by_contra hall; push Not at hall
      have hsub : L.val ≤ Submodule.span (ZMod p) ({v1} : Set (V3 p)) := fun x hx => by
        obtain ⟨c, hc⟩ := hall x hx; rw [hc]; exact Submodule.smul_mem _ c (Submodule.subset_span rfl)
      have h12 : Module.finrank (ZMod p) L.val ≤ 1 :=
        le_trans (Submodule.finrank_mono hsub) (finrank_span_singleton_le v1)
      rw [L.prop] at h12; omega
    obtain ⟨v2, hv2L, hv2_ind⟩ := hex_v2
    have hAu : A *ᵥ u = u := by rw [vecMulVec_mulVec, hdot1, one_smul]
    have hAv1 : A *ᵥ v1 = 0 := by have : v1 ∈ LinearMap.ker (Matrix.toLin' A) := hker'.symm ▸ hv1L; exact this
    have hAv2 : A *ᵥ v2 = 0 := by have : v2 ∈ LinearMap.ker (Matrix.toLin' A) := hker'.symm ▸ hv2L; exact this
    have hli : LinearIndependent (ZMod p) ![u, v1, v2] := by
      rw [linearIndependent_three_iff]
      intro c0 c1 c2 hsum
      have hA := congrArg (A *ᵥ ·) hsum
      simp only [Matrix.mulVec_add, Matrix.mulVec_smul, hAu, hAv1, hAv2, Matrix.mulVec_zero, smul_zero, add_zero] at hA
      have hc0 : c0 = 0 := by
        by_contra hne; exact hu0 (by simpa [smul_smul, inv_mul_cancel₀ hne] using congrArg (c0⁻¹ • ·) hA)
      subst hc0; simp only [zero_smul, zero_add] at hsum
      have hc2 : c2 = 0 := by
        by_contra hne
        exact hv2_ind (-c2⁻¹ * c1) (by
          have := congrArg (c2⁻¹ • ·) hsum
          rw [smul_add, smul_smul, smul_smul, inv_mul_cancel₀ hne, one_smul, smul_zero] at this
          simpa [neg_mul, neg_smul] using eq_neg_of_add_eq_zero_right this)
      subst hc2; simp only [zero_smul, add_zero] at hsum
      have hc1 : c1 = 0 := by
        by_contra hne; exact hv1_ne (by simpa [smul_smul, inv_mul_cancel₀ hne] using congrArg (c1⁻¹ • ·) hsum)
      exact ⟨rfl, hc1, rfl⟩
    have hconj := glOfCols_mul_eq hli A (matB0 p) (by simp [matB0, hAu]) (by simp [matB0, hAv1]) (by simp [matB0, hAv2])
    refine ⟨A, (range_vecMulVec hu0 hw'0).trans hPspan.symm, hker',
      fun _ => ⟨(hasM3Type_conj _ A .B).mp (hconj ▸ hasM3Type_matB0 p), hA2⟩, fun h => absurd h hinc⟩

/-- Theorem 4.1: The graph isomorphism `Φ : (V_(B) ∪ V_(E)) ≃ PGPoint p × PGLine p`! -/
private lemma theorem_4_1 (p : ℕ) [Fact p.Prime] :
    ∃ Φ : { v : UCCGVert p // VertHasType v .B ∨ VertHasType v .E } ≃ PGPoint p × PGLine p,
      (∀ v, VertHasType v.val .B ↔ ¬ (Φ v).1.val ≤ (Φ v).2.val) ∧
      (∀ v, VertHasType v.val .E ↔ (Φ v).1.val ≤ (Φ v).2.val) ∧
      (∀ v₁ v₂, UCCGAdj v₁.val v₂.val ↔ DeltaAdj (Φ v₁) (Φ v₂)) := by
  classical
  -- Map `Ψ : PGPoint p × PGLine p → (V_B ∪ V_E)` sending `(P, L)` to `⟨A_{P, L}⟩`!
  let genPL (x : PGPoint p × PGLine p) : M3 p := Classical.choose (exists_rank1_of_point_line x.1 x.2)
  have hgenPL : ∀ x : PGPoint p × PGLine p,
      LinearMap.range (Matrix.toLin' (genPL x)) = x.1.val ∧
      LinearMap.ker (Matrix.toLin' (genPL x)) = x.2.val ∧
      (¬ x.1.val ≤ x.2.val → HasM3Type (genPL x) .B ∧ (genPL x) ^ 2 = genPL x) ∧
      (x.1.val ≤ x.2.val → HasM3Type (genPL x) .E ∧ (genPL x) ^ 2 = 0) :=
    fun x => Classical.choose_spec (exists_rank1_of_point_line x.1 x.2)
  let Ψ : PGPoint p × PGLine p → { v : UCCGVert p // VertHasType v .B ∨ VertHasType v .E } :=
    fun x => ⟨⟨Subring.closure ({genPL x} : Set (M3 p)), ⟨genPL x, rfl⟩⟩, by
      by_cases hinc : x.1.val ≤ x.2.val
      · exact Or.inr ⟨genPL x, rfl, ((hgenPL x).2.2.2 hinc).1⟩
      · exact Or.inl ⟨genPL x, rfl, ((hgenPL x).2.2.1 hinc).1⟩⟩
  -- Key helper: `genPL x = vecMulVec u w` for some `u, w ≠ 0` with `span {u} = x.1`, `orthoSub (span {w}) = x.2`!
  have hgenPL_vec : ∀ x : PGPoint p × PGLine p,
      ∃ u w : V3 p, u ≠ 0 ∧ w ≠ 0 ∧ genPL x = Matrix.vecMulVec u w ∧
        Submodule.span (ZMod p) ({u} : Set (V3 p)) = x.1.val ∧
        orthoSub (Submodule.span (ZMod p) ({w} : Set (V3 p))) = x.2.val := fun x => by
    obtain ⟨u, w, hu, hw, hvec⟩ := rank1_eq_vecMulVec (by rw [(hgenPL x).1, x.1.prop])
    refine ⟨u, w, hu, hw, hvec, ?_, ?_⟩
    · rw [← range_vecMulVec hu hw, ← hvec, (hgenPL x).1]
    · rw [← ker_vecMulVec hu, ← hvec, (hgenPL x).2.1]
  -- Prove `Ψ` is bijective!
  have hΨ_inj : Function.Injective Ψ := by
    intro x₁ x₂ hEq
    have hcl : Subring.closure ({genPL x₁} : Set (M3 p)) = Subring.closure ({genPL x₂} : Set (M3 p)) :=
      congrArg (fun z => z.val.val) hEq
    obtain ⟨u₁, w₁, hu1, hw1, hv1, hP1, hL1⟩ := hgenPL_vec x₁
    obtain ⟨u₂, w₂, hu2, hw2, hv2, hP2, hL2⟩ := hgenPL_vec x₂
    -- `genPL x₂` has `sq = genPL x₂` or `0`, so `genPL x₁ = c0 • 1 + c1 • genPL x₂` with `c1 ≠ 0`!
    have hsq2 : ∃ a : ZMod p, genPL x₂ ^ 2 = a • genPL x₂ + (0 : ZMod p) • (1 : M3 p) := by
      by_cases hinc : x₂.1.val ≤ x₂.2.val
      · exact ⟨0, by rw [((hgenPL x₂).2.2.2 hinc).2]; simp⟩
      · exact ⟨1, by rw [((hgenPL x₂).2.2.1 hinc).2]; simp⟩
    obtain ⟨a, ha⟩ := hsq2
    obtain ⟨c0, c1, hc⟩ := (mem_closure_deg2 ha (genPL x₁)).mp (hcl ▸ Subring.subset_closure rfl)
    -- Show `c0 = 0`! Since `ker (genPL x₁)` and `ker (genPL x₂)` are 2D subspaces of `V3 p`, their intersection is nonzero!
    have hc0 : c0 = 0 := by
      set L1 : Submodule (ZMod p) (V3 p) := x₁.2.val
      set L2 : Submodule (ZMod p) (V3 p) := x₂.2.val
      have hsum := Submodule.finrank_sup_add_finrank_inf_eq L1 L2
      have hsup : Module.finrank (ZMod p) ↥(L1 ⊔ L2) ≤ 3 := by
        simpa using Submodule.finrank_le (L1 ⊔ L2)
      have hinf_pos : 0 < Module.finrank (ZMod p) ↥(L1 ⊓ L2) := by rw [x₁.2.prop, x₂.2.prop] at hsum; omega
      have hne : L1 ⊓ L2 ≠ ⊥ := fun h => by rw [h, finrank_bot] at hinf_pos; omega
      obtain ⟨z, ⟨hz1, hz2⟩, hz0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
      have h1z : genPL x₁ *ᵥ z = 0 := by
        show z ∈ LinearMap.ker (Matrix.toLin' (genPL x₁))
        rw [(hgenPL x₁).2.1]; exact hz1
      have h2z : genPL x₂ *ᵥ z = 0 := by
        show z ∈ LinearMap.ker (Matrix.toLin' (genPL x₂))
        rw [(hgenPL x₂).2.1]; exact hz2
      have hcz := congrArg (· *ᵥ z) hc
      simp only [h1z, Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, h2z, smul_zero, add_zero] at hcz
      exact (smul_eq_zero.mp hcz.symm).resolve_right hz0
    subst hc0; simp only [zero_smul, zero_add] at hc
    have hc1 : c1 ≠ 0 := by
      intro h0; subst h0; simp only [zero_smul] at hc
      have hbot : LinearMap.range (Matrix.toLin' (genPL x₁)) = ⊥ := by rw [hc]; ext y; simp
      rw [(hgenPL x₁).1] at hbot
      have hfr := x₁.1.prop; rw [hbot, finrank_bot] at hfr; omega
    rw [hv1, hv2] at hc
    obtain ⟨hPeq, hLeq⟩ := (vecMulVec_eq_iff hu1 hw1 hu2 hw2).mp ⟨c1, hc1, hc⟩
    exact Prod.ext (Subtype.ext (hP1.symm.trans (hPeq.trans hP2))) (Subtype.ext (hL1.symm.trans (hLeq.trans hL2)))
  have hΨ_surj : Function.Surjective Ψ := by
    intro v
    rcases v.prop with hvB | hvE
    · obtain ⟨A, hAv, hA2, hAr, hAk, hAnle⟩ := exists_rank1_gen_B hvB
      let P : PGPoint p := ⟨LinearMap.range (Matrix.toLin' A), hAr⟩
      let L : PGLine p := ⟨LinearMap.ker (Matrix.toLin' A), hAk⟩
      refine ⟨(P, L), Subtype.ext (Subtype.ext ?_)⟩
      show Subring.closure ({genPL (P, L)} : Set (M3 p)) = v.val.val
      rw [← hAv]
      obtain ⟨u₁, w₁, hu1, hw1, hv1, hP1, hL1⟩ := hgenPL_vec (P, L)
      obtain ⟨u₂, w₂, hu2, hw2, hv2⟩ := rank1_eq_vecMulVec hAr
      have hP2 : Submodule.span (ZMod p) ({u₂} : Set (V3 p)) = P.val := by rw [← range_vecMulVec hu2 hw2, ← hv2]
      have hL2 : orthoSub (Submodule.span (ZMod p) ({w₂} : Set (V3 p))) = L.val := by rw [← ker_vecMulVec hu2, ← hv2]
      obtain ⟨c, hc, hEq⟩ := (vecMulVec_eq_iff hu1 hw1 hu2 hw2).mpr ⟨hP1.trans hP2.symm, hL1.trans hL2.symm⟩
      rw [← hv1, ← hv2] at hEq
      have : genPL (P, L) = c • A + (0 : ZMod p) • (1 : M3 p) := by simp [hEq]
      rw [this, subring_closure_affine A hc 0]
    · obtain ⟨A, hAv, hA2, hAr, hAk, hAle⟩ := exists_rank1_gen_E hvE
      let P : PGPoint p := ⟨LinearMap.range (Matrix.toLin' A), hAr⟩
      let L : PGLine p := ⟨LinearMap.ker (Matrix.toLin' A), hAk⟩
      refine ⟨(P, L), Subtype.ext (Subtype.ext ?_)⟩
      show Subring.closure ({genPL (P, L)} : Set (M3 p)) = v.val.val
      rw [← hAv]
      obtain ⟨u₁, w₁, hu1, hw1, hv1, hP1, hL1⟩ := hgenPL_vec (P, L)
      obtain ⟨u₂, w₂, hu2, hw2, hv2⟩ := rank1_eq_vecMulVec hAr
      have hP2 : Submodule.span (ZMod p) ({u₂} : Set (V3 p)) = P.val := by rw [← range_vecMulVec hu2 hw2, ← hv2]
      have hL2 : orthoSub (Submodule.span (ZMod p) ({w₂} : Set (V3 p))) = L.val := by rw [← ker_vecMulVec hu2, ← hv2]
      obtain ⟨c, hc, hEq⟩ := (vecMulVec_eq_iff hu1 hw1 hu2 hw2).mpr ⟨hP1.trans hP2.symm, hL1.trans hL2.symm⟩
      rw [← hv1, ← hv2] at hEq
      have : genPL (P, L) = c • A + (0 : ZMod p) • (1 : M3 p) := by simp [hEq]
      rw [this, subring_closure_affine A hc 0]
  let Φ := (Equiv.ofBijective Ψ ⟨hΨ_inj, hΨ_surj⟩).symm
  have hΦ_inv : ∀ x, Φ (Ψ x) = x := fun x => (Equiv.ofBijective Ψ ⟨hΨ_inj, hΨ_surj⟩).left_inv x
  have hΨ_Φ : ∀ v, Ψ (Φ v) = v := fun v => (Equiv.ofBijective Ψ ⟨hΨ_inj, hΨ_surj⟩).right_inv v
  refine ⟨Φ, ?_, ?_, ?_⟩
  · intro v
    have hv := hΨ_Φ v
    by_cases hinc : (Φ v).1.val ≤ (Φ v).2.val
    · have hE : VertHasType v.val .E := by
        rw [← hv]; exact ⟨genPL (Φ v), rfl, ((hgenPL (Φ v)).2.2.2 hinc).1⟩
      exact ⟨fun hB => M3Type.noConfusion (vertHasType_unique hB hE), fun hn => absurd hinc hn⟩
    · have hB : VertHasType v.val .B := by
        rw [← hv]; exact ⟨genPL (Φ v), rfl, ((hgenPL (Φ v)).2.2.1 hinc).1⟩
      exact ⟨fun _ => hinc, fun _ => hB⟩
  · intro v
    have hv := hΨ_Φ v
    by_cases hinc : (Φ v).1.val ≤ (Φ v).2.val
    · have hE : VertHasType v.val .E := by
        rw [← hv]; exact ⟨genPL (Φ v), rfl, ((hgenPL (Φ v)).2.2.2 hinc).1⟩
      exact ⟨fun _ => hinc, fun _ => hE⟩
    · have hB : VertHasType v.val .B := by
        rw [← hv]; exact ⟨genPL (Φ v), rfl, ((hgenPL (Φ v)).2.2.1 hinc).1⟩
      exact ⟨fun hE => M3Type.noConfusion (vertHasType_unique hB hE), fun h => absurd h hinc⟩
  · -- Graph isomorphism `UCCGAdj v₁ v₂ ↔ DeltaAdj (Φ v₁) (Φ v₂)`!
    intro v₁ v₂
    set x₁ := Φ v₁; set x₂ := Φ v₂
    have hv1 : v₁ = Ψ x₁ := (hΨ_Φ v₁).symm
    have hv2 : v₂ = Ψ x₂ := (hΨ_Φ v₂).symm
    rw [hv1, hv2, uccgAdj_iff_comm (A₁ := genPL x₁) (A₂ := genPL x₂)
      (show genPL x₁ ∈ SingleGens (Ψ x₁).val from rfl) (show genPL x₂ ∈ SingleGens (Ψ x₂).val from rfl)]
    obtain ⟨u₁, w₁, hu1, hw1, heq1, hP1, hL1⟩ := hgenPL_vec x₁
    obtain ⟨u₂, w₂, hu2, hw2, heq2, hP2, hL2⟩ := hgenPL_vec x₂
    -- `P_i ≤ L_j ↔ dotProduct w_j u_i = 0`!
    have hinc_iff : ∀ (u w : V3 p) (P : PGPoint p) (L : PGLine p),
        Submodule.span (ZMod p) ({u} : Set (V3 p)) = P.val →
        orthoSub (Submodule.span (ZMod p) ({w} : Set (V3 p))) = L.val →
        (P.val ≤ L.val ↔ dotProduct w u = 0) := by
      intro u w P L hP hL
      rw [← hP, ← hL, Submodule.span_le, Set.singleton_subset_iff]
      change (∀ y ∈ Submodule.span (ZMod p) ({w} : Set (V3 p)), dotProduct u y = 0) ↔ dotProduct w u = 0
      constructor
      · intro h; rw [dotProduct_comm]; exact h w (Submodule.subset_span rfl)
      · intro h y hy; obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hy
        rw [dotProduct_smul, dotProduct_comm, h, smul_zero]
    have h21 : x₂.1.val ≤ x₁.2.val ↔ dotProduct w₁ u₂ = 0 := hinc_iff u₂ w₁ x₂.1 x₁.2 hP2 hL1
    have h12 : x₁.1.val ≤ x₂.2.val ↔ dotProduct w₂ u₁ = 0 := hinc_iff u₁ w₂ x₁.1 x₂.2 hP1 hL2
    -- Prove `genPL x₁ * genPL x₂ = genPL x₂ * genPL x₁ ↔ (x₁ = x₂) ∨ (P₂ ≤ L₁ ∧ P₁ ≤ L₂)`
    have hcomm_iff : genPL x₁ * genPL x₂ = genPL x₂ * genPL x₁ ↔
        (x₁.1.val = x₂.1.val ∧ x₁.2.val = x₂.2.val) ∨ (x₂.1.val ≤ x₁.2.val ∧ x₁.1.val ≤ x₂.2.val) := by
      rw [heq1, heq2, vecMulVec_mul_vecMulVec, vecMulVec_mul_vecMulVec, h21, h12]
      constructor
      · intro hcomm
        by_cases hd1 : dotProduct w₁ u₂ = 0
        · right; refine ⟨hd1, ?_⟩
          rw [hd1, zero_smul] at hcomm
          by_contra hd2
          have h0 : Matrix.vecMulVec u₂ w₁ = 0 := by
            have := congrArg ((dotProduct w₂ u₁)⁻¹ • ·) hcomm.symm
            simpa [smul_smul, inv_mul_cancel₀ hd2] using this
          have hex_u : ∃ i, u₂ i ≠ 0 := by by_contra h; push Not at h; exact hu2 (funext h)
          have hex_w : ∃ j, w₁ j ≠ 0 := by by_contra h; push Not at h; exact hw1 (funext h)
          obtain ⟨i, hi⟩ := hex_u; obtain ⟨j, hj⟩ := hex_w
          have := congrArg (fun M : M3 p => M i j) h0
          simp [Matrix.vecMulVec_apply] at this
          rcases this with h | h <;> contradiction
        · left
          have hd2 : dotProduct w₂ u₁ ≠ 0 := by
            intro h0; rw [h0, zero_smul] at hcomm
            have hM0 : Matrix.vecMulVec u₁ w₂ = 0 := by
              have := congrArg ((dotProduct w₁ u₂)⁻¹ • ·) hcomm
              simpa [smul_smul, inv_mul_cancel₀ hd1] using this
            have hex_u : ∃ i, u₁ i ≠ 0 := by by_contra h; push Not at h; exact hu1 (funext h)
            have hex_w : ∃ j, w₂ j ≠ 0 := by by_contra h; push Not at h; exact hw2 (funext h)
            obtain ⟨i, hi⟩ := hex_u; obtain ⟨j, hj⟩ := hex_w
            have := congrArg (fun M : M3 p => M i j) hM0
            simp [Matrix.vecMulVec_apply] at this
            rcases this with h | h <;> contradiction
          -- `vecMulVec u₁ w₂ = c • vecMulVec u₂ w₁` (`c ≠ 0`) => `span{u₁} = span{u₂}` and `ortho{w₂} = ortho{w₁}`!
          have hsc : Matrix.vecMulVec u₁ w₂ = ((dotProduct w₁ u₂)⁻¹ * dotProduct w₂ u₁) • Matrix.vecMulVec u₂ w₁ := by
            have := congrArg ((dotProduct w₁ u₂)⁻¹ • ·) hcomm
            simpa [smul_smul, inv_mul_cancel₀ hd1] using this
          obtain ⟨hU, hW⟩ := (vecMulVec_eq_iff hu1 hw2 hu2 hw1).mp ⟨_, mul_ne_zero (inv_ne_zero hd1) hd2, hsc⟩
          exact ⟨hP1.symm.trans (hU.trans hP2), hL1.symm.trans (hW.symm.trans hL2)⟩
      · rintro (⟨hPeq, hLeq⟩ | ⟨hd1, hd2⟩)
        · have hx : x₁ = x₂ := Prod.ext (Subtype.ext hPeq) (Subtype.ext hLeq)
          rw [← vecMulVec_mul_vecMulVec, ← vecMulVec_mul_vecMulVec, ← heq1, ← heq2, hx]
        · rw [hd1, hd2, zero_smul, zero_smul]
    rw [hcomm_iff]
    -- Finally, `(P₁ = P₂ ∧ L₁ = L₂) ∨ (P₂ ≤ L₁ ∧ P₁ ≤ L₂) ↔ DeltaAdj x₁ x₂` (exact 4-case split of Theorem 4.1!)
    dsimp only [DeltaAdj]
    constructor
    · rintro (⟨hP, hL⟩ | ⟨h21', h12'⟩)
      · exact Or.inl ⟨hP, hL⟩
      · by_cases h11 : x₁.1.val ≤ x₁.2.val
        · by_cases h22 : x₂.1.val ≤ x₂.2.val
          · -- Two distinct points cannot lie on two distinct lines in `PG(2, p)`!
            by_cases hPeq : x₁.1.val = x₂.1.val
            · exact Or.inr (Or.inl ⟨h11, h22, Or.inl hPeq⟩)
            · by_cases hLeq : x₁.2.val = x₂.2.val
              · exact Or.inr (Or.inl ⟨h11, h22, Or.inr hLeq⟩)
              · exfalso
                set P1 : Submodule (ZMod p) (V3 p) := x₁.1.val
                set P2 : Submodule (ZMod p) (V3 p) := x₂.1.val
                set L1 : Submodule (ZMod p) (V3 p) := x₁.2.val
                set L2 : Submodule (ZMod p) (V3 p) := x₂.2.val
                have hsup : P1 ⊔ P2 ≤ L1 ⊓ L2 := sup_le (le_inf h11 h12') (le_inf h21' h22)
                have hinf_bot : P1 ⊓ P2 = ⊥ := by
                  by_contra hne
                  have hle1 : Module.finrank (ZMod p) ↥(P1 ⊓ P2) ≤ 1 := by
                    have := Submodule.finrank_mono (inf_le_left : P1 ⊓ P2 ≤ P1)
                    rw [x₁.1.prop] at this; exact this
                  have hpos : 0 < Module.finrank (ZMod p) ↥(P1 ⊓ P2) := by
                    by_contra h0; exact hne (Submodule.finrank_eq_zero.mp (by omega))
                  have he1 : P1 ⊓ P2 = P1 := Submodule.eq_of_le_of_finrank_eq inf_le_left (by rw [x₁.1.prop]; omega)
                  have he2 : P1 ⊓ P2 = P2 := Submodule.eq_of_le_of_finrank_eq inf_le_right (by rw [x₂.1.prop]; omega)
                  exact hPeq (he1.symm.trans he2)
                have hfr_sup : Module.finrank (ZMod p) ↥(P1 ⊔ P2) = 2 := by
                  have h := Submodule.finrank_sup_add_finrank_inf_eq P1 P2
                  rw [hinf_bot, finrank_bot, add_zero, x₁.1.prop, x₂.1.prop] at h; exact h
                have hfr_inf : Module.finrank (ZMod p) ↥(L1 ⊓ L2) = 2 := by
                  have hge := Submodule.finrank_mono hsup
                  have hle := Submodule.finrank_mono (inf_le_left : L1 ⊓ L2 ≤ L1)
                  rw [hfr_sup] at hge; rw [x₁.2.prop] at hle; omega
                have he1 := Submodule.eq_of_le_of_finrank_eq (inf_le_left : L1 ⊓ L2 ≤ L1)
                  (by rw [hfr_inf, x₁.2.prop])
                have he2 := Submodule.eq_of_le_of_finrank_eq (inf_le_right : L1 ⊓ L2 ≤ L2)
                  (by rw [hfr_inf, x₂.2.prop])
                exact hLeq (he1.symm.trans he2)
          · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨fun h => h22 (h ▸ h12'), fun h => h22 (h ▸ h21'), ⟨h11, h12'⟩, ⟨h21', h22⟩⟩)))
        · by_cases h22 : x₂.1.val ≤ x₂.2.val
          · exact Or.inr (Or.inr (Or.inl ⟨fun h => h11 (h.symm ▸ h21'), fun h => h11 (h.symm ▸ h12'), ⟨h21', h22⟩, ⟨h12', h11⟩⟩))
          · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨fun h => h11 (h ▸ h21'), fun h => h11 (h ▸ h12'), ⟨h12', h11⟩, ⟨h21', h22⟩⟩)))
    · rintro (⟨hP, hL⟩ | ⟨h11, h22, hP | hL⟩ | ⟨_, _, ⟨h21', _⟩, ⟨h12', _⟩⟩ | ⟨_, _, ⟨_, h12'⟩, ⟨h21', _⟩⟩ | ⟨_, _, ⟨h12', _⟩, ⟨h21', _⟩⟩)
      · exact Or.inl ⟨hP, hL⟩
      · exact Or.inr ⟨hP ▸ h11, hP.symm ▸ h22⟩
      · exact Or.inr ⟨hL ▸ h22, hL.symm ▸ h11⟩
      · exact Or.inr ⟨h21', h12'⟩
      · exact Or.inr ⟨h21', h12'⟩
      · exact Or.inr ⟨h21', h12'⟩

private lemma card_verts_B_E (p : ℕ) [Fact p.Prime] :
    Nat.card (VertsOfType p .B) = (p ^ 2 + p + 1) * p ^ 2 ∧
    Nat.card (VertsOfType p .E) = (p ^ 2 + p + 1) * (p + 1) := by
  classical
  have : Finite (PGPoint p) := finite_pgPoint
  have : Finite (PGLine p) := finite_pgLine
  let : Fintype (PGPoint p) := Fintype.ofFinite _
  let : Fintype (PGLine p) := Fintype.ofFinite _
  obtain ⟨Φ, hΦB, hΦE, _⟩ := theorem_4_1 p
  have hE_eq : Nat.card (VertsOfType p .E) = Nat.card { x : PGPoint p × PGLine p // x.1.val ≤ x.2.val } := by
    refine Nat.card_congr ?_
    refine Equiv.ofBijective (fun v : VertsOfType p .E =>
      ⟨Φ ⟨v.val, Or.inr v.prop⟩, (hΦE ⟨v.val, Or.inr v.prop⟩).mp v.prop⟩) ⟨?_, ?_⟩
    · intro a b h
      have h1 := Φ.injective (congrArg Subtype.val h)
      exact Subtype.ext (congrArg (fun z => z.val) h1)
    · intro y
      let v := Φ.symm y.val
      have hvE : VertHasType v.val .E := (hΦE v).mpr (by simpa [v] using y.prop)
      exact ⟨⟨v.val, hvE⟩, Subtype.ext (by simp [v])⟩
  have hB_eq : Nat.card (VertsOfType p .B) = Nat.card { x : PGPoint p × PGLine p // ¬ x.1.val ≤ x.2.val } := by
    refine Nat.card_congr ?_
    refine Equiv.ofBijective (fun v : VertsOfType p .B =>
      ⟨Φ ⟨v.val, Or.inl v.prop⟩, (hΦB ⟨v.val, Or.inl v.prop⟩).mp v.prop⟩) ⟨?_, ?_⟩
    · intro a b h
      have h1 := Φ.injective (congrArg Subtype.val h)
      exact Subtype.ext (congrArg (fun z => z.val) h1)
    · intro y
      let v := Φ.symm y.val
      have hvB : VertHasType v.val .B := (hΦB v).mpr (by simpa [v] using y.prop)
      exact ⟨⟨v.val, hvB⟩, Subtype.ext (by simp [v])⟩
  have hcard_inc : Nat.card { x : PGPoint p × PGLine p // x.1.val ≤ x.2.val } = (p ^ 2 + p + 1) * (p + 1) := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    have hsum : (Finset.univ.filter fun x : PGPoint p × PGLine p => x.1.val ≤ x.2.val).card =
        ∑ L : PGLine p, (Finset.univ.filter fun P : PGPoint p => P.val ≤ L.val).card := by
      rw [Finset.card_filter, Fintype.sum_prod_type_right]
      refine Finset.sum_congr rfl fun L _ => (Finset.card_filter _ _).symm
    rw [hsum]
    have hterm : ∀ L : PGLine p, (Finset.univ.filter fun P : PGPoint p => P.val ≤ L.val).card = p + 1 := fun L => by
      have := card_points_on_line L
      rwa [Nat.card_eq_fintype_card, Fintype.card_subtype] at this
    simp_rw [hterm]
    rw [Finset.sum_const, Finset.card_univ, smul_eq_mul, ← Nat.card_eq_fintype_card, card_pgLine]
  have hcard_ninc : Nat.card { x : PGPoint p × PGLine p // ¬ x.1.val ≤ x.2.val } = (p ^ 2 + p + 1) * p ^ 2 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype_compl, Fintype.card_prod,
        ← Nat.card_eq_fintype_card (α := PGPoint p), ← Nat.card_eq_fintype_card (α := PGLine p),
        card_pgPoint, card_pgLine, ← Nat.card_eq_fintype_card, hcard_inc]
    have : (p ^ 2 + p + 1) * (p ^ 2 + p + 1) = (p ^ 2 + p + 1) * p ^ 2 + (p ^ 2 + p + 1) * (p + 1) := by ring
    omega
  exact ⟨hB_eq.trans hcard_ninc, hE_eq.trans hcard_inc⟩

/-! ### Section 6: Centralizers of Non-Derogatory Matrices & Section 5 Attachments -/

/-- Helper: `v ∈ V_(A)` iff `v.val = Subring.closure {0}`. -/
private lemma vertHasType_A_iff {p : ℕ} [Fact p.Prime] (v : UCCGVert p) :
    VertHasType v .A ↔ v.val = Subring.closure ({(0 : M3 p)} : Set (M3 p)) := by
  constructor
  · rintro ⟨A, hAv, l, _, hm⟩
    have hA : A = l • (1 : M3 p) := by
      have := minpoly.aeval (ZMod p) A
      rw [hm, map_sub, aeval_X, aeval_C, Algebra.algebraMap_eq_smul_one, sub_eq_zero] at this
      exact this
    rw [← hAv, subring_closure_eq_iff]
    exact ⟨zero_mem _, hA ▸ smul_one_mem_subring _ l⟩
  · intro hv
    exact ⟨0, hv.symm, 0, by simp, by simp⟩

private lemma card_verts_A (p : ℕ) [Fact p.Prime] : Nat.card (VertsOfType p .A) = 1 := by
  have huniq : Unique (VertsOfType p .A) :=
    { default := ⟨⟨Subring.closure ({(0 : M3 p)} : Set (M3 p)), ⟨0, rfl⟩⟩, (vertHasType_A_iff _).mpr rfl⟩
      uniq := fun v => Subtype.ext (Subtype.ext ((vertHasType_A_iff v.val).mp v.prop)) }
  exact Nat.card_unique

private lemma adj_of_type_A {p : ℕ} [Fact p.Prime] {v : UCCGVert p} (hv : VertHasType v .A) (w : UCCGVert p) :
    UCCGAdj v w := by
  obtain ⟨B, hBw⟩ := w.prop
  have h0 : (0 : M3 p) ∈ SingleGens v := ((vertHasType_A_iff v).mp hv).symm
  exact (uccgAdj_iff_comm h0 hBw.symm).mpr (by simp)

private lemma commute_aeval_left {p : ℕ} [Fact p.Prime] {A B : M3 p}
    (h : A * B = B * A) (f : (ZMod p)[X]) : aeval A f * B = B * aeval A f := by
  have hcomm : Commute A B := h
  induction f using Polynomial.induction_on' with
  | add p1 p2 hp1 hp2 => rw [map_add]; exact Commute.add_left hp1 hp2
  | monomial n c =>
    rw [aeval_monomial, Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul]
    exact (hcomm.pow_left n).smul_left c

/-- For every non-derogatory matrix `A` (Types `C, D, F, G, H`), its centralizer equals `Subring.closure {A}`! -/
private lemma centralizer_eq_closure_nonderog {p : ℕ} [Fact p.Prime] {A B : M3 p}
    (hnd : HasM3Type A .C ∨ HasM3Type A .D ∨ HasM3Type A .F ∨ HasM3Type A .G ∨ HasM3Type A .H)
    (hcomm : A * B = B * A) : B ∈ Subring.closure ({A} : Set (M3 p)) := by
  -- Transport `B ∈ Subring.closure {A}` via `conjAlgEquiv S`!
  have hconj_mem : ∀ (S : GL (Fin 3) (ZMod p)),
      conjAlgEquiv S B ∈ Subring.closure ({conjAlgEquiv S A} : Set (M3 p)) →
      B ∈ Subring.closure ({A} : Set (M3 p)) := fun S hmem => by
    rw [subring_closure_conj] at hmem
    rcases hmem with ⟨X, hX, hSX⟩
    have : X = B := (conjAlgEquiv S).injective hSX
    rwa [← this]
  have hconj_comm : ∀ (S : GL (Fin 3) (ZMod p)),
      conjAlgEquiv S A * conjAlgEquiv S B = conjAlgEquiv S B * conjAlgEquiv S A := fun S => by
    rw [← map_mul, ← map_mul, hcomm]
  rcases hnd with hC | hD | hF | hG | hH
  · obtain ⟨S, l, m, n, hlm, hln, hmn, hS⟩ := canonical_C hC
    apply hconj_mem S; rw [hS]
    set Y := conjAlgEquiv S B
    have hc : Matrix.diagonal ![l, m, n] * Y = Y * Matrix.diagonal ![l, m, n] := hS ▸ hconj_comm S
    have hoff : ∀ i j : Fin 3, i ≠ j → Y i j = 0 := by
      intro i j hij
      have h := congrArg (fun M : M3 p => M i j) hc
      simp only [Matrix.diagonal_mul, Matrix.mul_diagonal] at h
      have hd : ![l, m, n] i ≠ ![l, m, n] j := by fin_cases i <;> fin_cases j <;> simp_all [Ne.symm]
      have hsub : (![l, m, n] i - ![l, m, n] j) * Y i j = 0 := by linear_combination h
      exact (mul_eq_zero.mp hsub).resolve_left (sub_ne_zero.mpr hd)
    have hXdiag : Y = Matrix.diagonal ![Y 0 0, Y 1 1, Y 2 2] := by
      ext i j; fin_cases i <;> fin_cases j <;> simp [hoff]
    rw [hXdiag]
    let f : (ZMod p)[X] :=
      C (Y 0 0 * ((l - m) * (l - n))⁻¹) * ((Polynomial.X - C m) * (Polynomial.X - C n)) +
      C (Y 1 1 * ((m - l) * (m - n))⁻¹) * ((Polynomial.X - C l) * (Polynomial.X - C n)) +
      C (Y 2 2 * ((n - l) * (n - m))⁻¹) * ((Polynomial.X - C l) * (Polynomial.X - C m))
    refine (mem_subring_closure_iff_aeval _ _).mpr ⟨f, ?_⟩
    have hdiag_aeval : ∀ g : (ZMod p)[X], aeval (Matrix.diagonal ![l, m, n]) g =
        Matrix.diagonal ![g.eval l, g.eval m, g.eval n] := fun g => by
      induction g using Polynomial.induction_on' with
      | add g1 g2 h1 h2 => rw [map_add, h1, h2]; ext i j; fin_cases i <;> fin_cases j <;> simp
      | monomial k r =>
        rw [aeval_monomial, Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul, Matrix.diagonal_pow]
        ext i j; fin_cases i <;> fin_cases j <;> simp [Polynomial.eval_monomial]
    rw [hdiag_aeval]
    have h1 : (l - m) * (l - n) ≠ 0 := mul_ne_zero (sub_ne_zero.mpr hlm) (sub_ne_zero.mpr hln)
    have h2 : (m - l) * (m - n) ≠ 0 := mul_ne_zero (sub_ne_zero.mpr (Ne.symm hlm)) (sub_ne_zero.mpr hmn)
    have h3 : (n - l) * (n - m) ≠ 0 := mul_ne_zero (sub_ne_zero.mpr (Ne.symm hln)) (sub_ne_zero.mpr (Ne.symm hmn))
    have hfl : f.eval l = Y 0 0 := by
      simp only [f, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_C,
        Polynomial.eval_X, sub_self, mul_zero, zero_mul, add_zero]
      rw [mul_assoc, inv_mul_cancel₀ h1, mul_one]
    have hfm : f.eval m = Y 1 1 := by
      simp only [f, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_C,
        Polynomial.eval_X, sub_self, mul_zero, zero_mul, add_zero, zero_add]
      rw [mul_assoc, inv_mul_cancel₀ h2, mul_one]
    have hfn : f.eval n = Y 2 2 := by
      simp only [f, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_C,
        Polynomial.eval_X, sub_self, mul_zero, add_zero, zero_add]
      rw [mul_assoc, inv_mul_cancel₀ h3, mul_one]
    rw [hfl, hfm, hfn]
  · obtain ⟨S, hS⟩ := canonical_D hD
    apply hconj_mem S; rw [hS]
    set Y := conjAlgEquiv S B
    have hc : matD0 p * Y = Y * matD0 p := by
      have hm : matD0 p ∈ Subring.closure ({conjAlgEquiv S A} : Set (M3 p)) := hS ▸ Subring.subset_closure rfl
      obtain ⟨f, hf⟩ := (mem_subring_closure_iff_aeval _ _).mp hm
      rw [← hf]; exact commute_aeval_left (hconj_comm S) f
    have h10 : Y 1 0 = 0 := by have := congrArg (fun M : M3 p => M 0 0) hc; simp [matD0, Matrix.mul_apply, Fin.sum_univ_three] at this; exact this
    have h20 : Y 2 0 = 0 := by have := congrArg (fun M : M3 p => M 1 0) hc; simp [matD0, Matrix.mul_apply, Fin.sum_univ_three] at this; exact this
    have h21 : Y 2 1 = 0 := by have := congrArg (fun M : M3 p => M 2 2) hc; simp [matD0, Matrix.mul_apply, Fin.sum_univ_three] at this; exact this.symm
    have h00_11 : Y 1 1 = Y 0 0 := by have := congrArg (fun M : M3 p => M 0 1) hc; simp [matD0, Matrix.mul_apply, Fin.sum_univ_three] at this; exact this
    have h11_22 : Y 2 2 = Y 1 1 := by have := congrArg (fun M : M3 p => M 1 2) hc; simp [matD0, Matrix.mul_apply, Fin.sum_univ_three] at this; exact this
    have h01_12 : Y 1 2 = Y 0 1 := by have := congrArg (fun M : M3 p => M 0 2) hc; simp [matD0, Matrix.mul_apply, Fin.sum_univ_three] at this; exact this
    have hD2 : matD0 p ^ 2 = !![0, 0, 1; 0, 0, 0; 0, 0, 0] := by
      ext i j; fin_cases i <;> fin_cases j <;> simp [matD0, sq, Matrix.mul_apply, Fin.sum_univ_three]
    have hXeq : Y = Y 0 0 • (1 : M3 p) + Y 0 1 • matD0 p + Y 0 2 • matD0 p ^ 2 := by
      rw [hD2]; ext i j; fin_cases i <;> fin_cases j <;> simp [matD0, h10, h20, h21, h00_11, h11_22, h01_12]
    rw [hXeq]
    set SD := Subring.closure ({matD0 p} : Set (M3 p))
    have hD_in : matD0 p ∈ SD := Subring.subset_closure rfl
    exact add_mem (add_mem (smul_one_mem_subring SD _) (smul_mem_subring SD _ hD_in))
      (smul_mem_subring SD _ (sq (matD0 p) ▸ mul_mem hD_in hD_in))
  · obtain ⟨S, hS⟩ := canonical_F hF
    apply hconj_mem S; rw [hS]
    set Y := conjAlgEquiv S B
    have hc : matF0 p * Y = Y * matF0 p := by
      have hm : matF0 p ∈ Subring.closure ({conjAlgEquiv S A} : Set (M3 p)) := hS ▸ Subring.subset_closure rfl
      obtain ⟨f, hf⟩ := (mem_subring_closure_iff_aeval _ _).mp hm
      rw [← hf]; exact commute_aeval_left (hconj_comm S) f
    have h10 : Y 1 0 = 0 := by have := congrArg (fun M : M3 p => M 0 0) hc; simp [matF0, Matrix.mul_apply, Fin.sum_univ_three] at this; exact this
    have h20 : Y 2 0 = 0 := by have := congrArg (fun M : M3 p => M 2 0) hc; simp [matF0, Matrix.mul_apply, Fin.sum_univ_three] at this; exact this
    have h21 : Y 2 1 = 0 := by have := congrArg (fun M : M3 p => M 2 1) hc; simp [matF0, Matrix.mul_apply, Fin.sum_univ_three, h20] at this; exact this
    have h12 : Y 1 2 = 0 := by have := congrArg (fun M : M3 p => M 1 2) hc; simp [matF0, Matrix.mul_apply, Fin.sum_univ_three] at this; exact this.symm
    have h02 : Y 0 2 = 0 := by have := congrArg (fun M : M3 p => M 0 2) hc; simp [matF0, Matrix.mul_apply, Fin.sum_univ_three, h12] at this; exact this.symm
    have h00_11 : Y 1 1 = Y 0 0 := by have := congrArg (fun M : M3 p => M 0 1) hc; simp [matF0, Matrix.mul_apply, Fin.sum_univ_three] at this; exact this
    have hF2 : matF0 p ^ 2 = !![0, 0, 0; 0, 0, 0; 0, 0, 1] := by
      ext i j; fin_cases i <;> fin_cases j <;> simp [matF0, sq, Matrix.mul_apply, Fin.sum_univ_three]
    have hXeq : Y = Y 0 0 • (1 : M3 p) + Y 0 1 • matF0 p + (Y 2 2 - Y 0 0 - Y 0 1) • matF0 p ^ 2 := by
      rw [hF2]; ext i j; fin_cases i <;> fin_cases j <;> simp [matF0, h10, h20, h21, h12, h02, h00_11]
    rw [hXeq]
    set SF := Subring.closure ({matF0 p} : Set (M3 p))
    have hF_in : matF0 p ∈ SF := Subring.subset_closure rfl
    exact add_mem (add_mem (smul_one_mem_subring SF _) (smul_mem_subring SF _ hF_in))
      (smul_mem_subring SF _ (sq (matF0 p) ▸ mul_mem hF_in hF_in))
  · obtain ⟨S, hS⟩ := canonical_G hG
    apply hconj_mem S; rw [hS]
    set C := matComp3 A.charpoly
    set Y0 := conjAlgEquiv S B
    have hc : C * Y0 = Y0 * C := hS ▸ hconj_comm S
    -- `Y0` agrees with `Y0 0 0 • 1 + Y0 1 0 • C + Y0 2 0 • C^2` on `e0, e1 = C e0, e2 = C^2 e0`!
    set Y : M3 p := Y0 0 0 • (1 : M3 p) + Y0 1 0 • C + Y0 2 0 • C ^ 2
    have hC0 : C *ᵥ Pi.single 0 1 = Pi.single 1 1 := by
      ext i; fin_cases i <;> simp [C, matComp3, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
    have hC1 : C *ᵥ Pi.single 1 1 = Pi.single 2 1 := by
      ext i; fin_cases i <;> simp [C, matComp3, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
    have hXe0 : Y0 *ᵥ Pi.single 0 1 = Y *ᵥ Pi.single 0 1 := by
      ext i
      have h1 : (C ^ 2) *ᵥ Pi.single 0 1 = Pi.single 2 1 := by
        rw [sq, ← Matrix.mulVec_mulVec, hC0, hC1]
      simp only [Y, Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, hC0, h1]
      fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three]
    have hCY : C * Y = Y * C := by
      simp only [Y, mul_add, add_mul, mul_smul_comm, smul_mul_assoc, mul_one, one_mul, sq, mul_assoc]
    have hXe1 : Y0 *ᵥ Pi.single 1 1 = Y *ᵥ Pi.single 1 1 := by
      rw [← hC0, Matrix.mulVec_mulVec, ← hc, ← Matrix.mulVec_mulVec, hXe0,
          Matrix.mulVec_mulVec, hCY, ← Matrix.mulVec_mulVec]
    have hXe2 : Y0 *ᵥ Pi.single 2 1 = Y *ᵥ Pi.single 2 1 := by
      rw [← hC1, Matrix.mulVec_mulVec, ← hc, ← Matrix.mulVec_mulVec, hXe1,
          Matrix.mulVec_mulVec, hCY, ← Matrix.mulVec_mulVec]
    have hXY : Y0 = Y := by
      ext i j
      have hcol : ∀ k : Fin 3, Y0 *ᵥ Pi.single k 1 = Y *ᵥ Pi.single k 1 := fun k => by
        fin_cases k; exact hXe0; exact hXe1; exact hXe2
      have hji := congrFun (hcol j) i
      change dotProduct (Y0 i) (Pi.single j 1) = dotProduct (Y i) (Pi.single j 1) at hji
      rwa [dotProduct_comm, dotProduct_single_left, dotProduct_comm, dotProduct_single_left, one_mul, one_mul] at hji
    rw [hXY]
    set SC := Subring.closure ({C} : Set (M3 p))
    have hC_in : C ∈ SC := Subring.subset_closure rfl
    exact add_mem (add_mem (smul_one_mem_subring SC _) (smul_mem_subring SC _ hC_in))
      (smul_mem_subring SC _ (sq C ▸ mul_mem hC_in hC_in))
  · obtain ⟨S, l, q, hqmon, hqdeg, hqirr, hS⟩ := canonical_H hH
    apply hconj_mem S; rw [hS]
    set M := matH0 l q
    set X := conjAlgEquiv S B
    have hc : M * X = X * M := hS ▸ hconj_comm S
    have hqno : ∀ x : ZMod p, ¬ q.IsRoot x := fun x hx => by
      obtain ⟨R, hR⟩ := Polynomial.dvd_iff_isRoot.mpr hx
      rcases hqirr.isUnit_or_isUnit hR with hu | hu
      · exact Polynomial.not_isUnit_X_sub_C x hu
      · have := congrArg Polynomial.natDegree hR
        rw [hqdeg, Polynomial.natDegree_mul (Polynomial.monic_X_sub_C x).ne_zero hu.ne_zero,
            Polynomial.natDegree_X_sub_C, Polynomial.natDegree_eq_zero_of_isUnit hu] at this; omega
    have hq_exp : q = Polynomial.X ^ 2 + C (q.coeff 1) * Polynomial.X + C (q.coeff 0) := by
      ext k
      by_cases hk : k ≤ 2
      · interval_cases k <;> simp [Polynomial.coeff_X, Polynomial.coeff_C, Polynomial.coeff_X_pow]
        · simpa [Polynomial.Monic, Polynomial.leadingCoeff, hqdeg] using hqmon
      · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)]
        simp [Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_C,
              show k ≠ 2 by omega, show 1 ≠ k by omega, show k ≠ 0 by omega]
    have hqM : aeval M q = (q.eval l) • matB0 p := by
      rw [hq_exp]
      simp only [map_add, map_mul, map_pow, aeval_X, aeval_C, Algebra.algebraMap_eq_smul_one,
        smul_mul_assoc, one_mul, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow,
        Polynomial.eval_X, Polynomial.eval_C]
      ext i j; fin_cases i <;> fin_cases j <;> (simp [M, matH0, matB0, sq]; try ring)
    have hE00_mem : matB0 p ∈ Subring.closure ({M} : Set (M3 p)) := by
      have h1 : (q.eval l)⁻¹ • aeval M q = matB0 p := by rw [hqM, smul_smul, inv_mul_cancel₀ (hqno l), one_smul]
      rw [← h1]; exact smul_mem_subring _ _ (aeval_mem_subring_closure M q)
    have hE00_comm : matB0 p * X = X * matB0 p := by
      have h1 : aeval M q * X = X * aeval M q := commute_aeval_left hc q
      rw [hqM, smul_mul_assoc, mul_smul_comm] at h1
      have h2 := congrArg ((q.eval l)⁻¹ • ·) h1
      simpa [smul_smul, inv_mul_cancel₀ (hqno l)] using h2
    have h01 : X 0 1 = 0 := by have := congrArg (fun T : M3 p => T 0 1) hE00_comm; simp [matB0, Matrix.mul_apply, Fin.sum_univ_three] at this; exact this
    have h02 : X 0 2 = 0 := by have := congrArg (fun T : M3 p => T 0 2) hE00_comm; simp [matB0, Matrix.mul_apply, Fin.sum_univ_three] at this; exact this
    have h10 : X 1 0 = 0 := by have := congrArg (fun T : M3 p => T 1 0) hE00_comm; simp [matB0, Matrix.mul_apply, Fin.sum_univ_three] at this; exact this.symm
    have h20 : X 2 0 = 0 := by have := congrArg (fun T : M3 p => T 2 0) hE00_comm; simp [matB0, Matrix.mul_apply, Fin.sum_univ_three] at this; exact this.symm
    have h12 : X 1 2 = -X 2 1 * q.coeff 0 := by
      have := congrArg (fun T : M3 p => T 1 1) hc
      simp [M, matH0, Matrix.mul_apply, Fin.sum_univ_three, h01, h10] at this; linear_combination -this
    have h22 : X 2 2 = X 1 1 - X 2 1 * q.coeff 1 := by
      have := congrArg (fun T : M3 p => T 2 1) hc
      simp [M, matH0, Matrix.mul_apply, Fin.sum_univ_three, h01, h20] at this; linear_combination -this
    have hXeq : X = (X 0 0 - X 1 1 - X 2 1 * l) • matB0 p + X 1 1 • (1 : M3 p) + X 2 1 • M := by
      ext i j; fin_cases i <;> fin_cases j <;>
        simp [M, matH0, matB0, h01, h02, h10, h20, h12, h22] <;> ring
    rw [hXeq]
    exact add_mem (add_mem (smul_mem_subring _ _ hE00_mem) (smul_one_mem_subring _ _))
      (smul_mem_subring _ _ (Subring.subset_closure rfl))

private lemma le_of_adj_nonderog {p : ℕ} [Fact p.Prime] {v w : UCCGVert p}
    (hv : VertHasType v .C ∨ VertHasType v .D ∨ VertHasType v .F ∨ VertHasType v .G ∨ VertHasType v .H)
    (hadj : UCCGAdj v w) : w.val ≤ v.val := by
  obtain ⟨A, hAv⟩ := v.prop
  obtain ⟨B, hBw⟩ := w.prop
  have hnd : HasM3Type A .C ∨ HasM3Type A .D ∨ HasM3Type A .F ∨ HasM3Type A .G ∨ HasM3Type A .H := by
    rcases hv with h | h | h | h | h
    · exact Or.inl ((vertHasType_iff_all.mp h) A hAv.symm)
    · exact Or.inr (Or.inl ((vertHasType_iff_all.mp h) A hAv.symm))
    · exact Or.inr (Or.inr (Or.inl ((vertHasType_iff_all.mp h) A hAv.symm)))
    · exact Or.inr (Or.inr (Or.inr (Or.inl ((vertHasType_iff_all.mp h) A hAv.symm))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr ((vertHasType_iff_all.mp h) A hAv.symm))))
  have hcomm : A * B = B * A := (uccgAdj_iff_comm hAv.symm hBw.symm).mp hadj
  have hBmem : B ∈ v.val := hAv ▸ centralizer_eq_closure_nonderog hnd hcomm
  rw [hBw]; exact Subring.closure_le.mpr (Set.singleton_subset_iff.mpr hBmem)

private lemma nonderog_no_cross_edges {p : ℕ} [Fact p.Prime] {v₁ v₂ : UCCGVert p} (hne : v₁ ≠ v₂)
    (h1 : VertHasType v₁ .C ∨ VertHasType v₁ .D ∨ VertHasType v₁ .F ∨ VertHasType v₁ .G ∨ VertHasType v₁ .H)
    (h2 : VertHasType v₂ .C ∨ VertHasType v₂ .D ∨ VertHasType v₂ .F ∨ VertHasType v₂ .G ∨ VertHasType v₂ .H) :
    ¬ UCCGAdj v₁ v₂ := by
  intro hadj
  have hadj' : UCCGAdj v₂ v₁ := fun A hA B hB => (hadj B hB A hA).symm
  exact hne (Subtype.ext (le_antisymm (le_of_adj_nonderog h2 hadj') (le_of_adj_nonderog h1 hadj)))

private lemma adj_G_iff {p : ℕ} [Fact p.Prime] {v : UCCGVert p} (hv : VertHasType v .G) (w : UCCGVert p) :
    UCCGAdj v w ↔ w = v ∨ VertHasType w .A := by
  constructor
  · intro hadj
    have hle : w.val ≤ v.val := le_of_adj_nonderog (Or.inr (Or.inr (Or.inr (Or.inl hv)))) hadj
    obtain ⟨B, hBw⟩ := w.prop
    obtain ⟨A, hAv, hAG⟩ := hv
    have hB_in : B ∈ Subring.closure ({A} : Set (M3 p)) := by
      have : B ∈ v.val := hle (hBw ▸ Subring.subset_closure rfl)
      rwa [← hAv] at this
    by_cases hsc : ∃ c : ZMod p, B = c • (1 : M3 p)
    · right; obtain ⟨c, rfl⟩ := hsc
      exact ⟨c • (1 : M3 p), hBw.symm, c, charpoly_smul_one c, minpoly_smul_one c⟩
    · left
      -- Since `A` has Type G, every non-scalar element of `⟨A⟩` generates `⟨A⟩`!
      -- We already proved `deg(minpoly B) = 3` for non-scalar `B ∈ ⟨A⟩` in `card_singleGens_of_type` —
      -- even simpler: `SingleGens v` has size `p^3 - p`, scalar subring has size `p`, total `|v| = p^3`,
      -- so EVERY non-scalar element of `v` MUST be in `SingleGens v`!!
      classical
      have hcard_v : Nat.card v.val = p ^ 3 := by
        have hvA : v.val = (Algebra.adjoin (ZMod p) ({A} : Set (M3 p))).toSubring := by
          rw [← hAv, subring_closure_eq_adjoin]
        have hdim : Module.finrank (ZMod p) (Algebra.adjoin (ZMod p) ({A} : Set (M3 p))) = 3 := by
          rw [finrank_adjoin_singleton_m3, hAG.2, Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]
        rw [hvA, Nat.card_eq_fintype_card]
        change Fintype.card (Algebra.adjoin (ZMod p) ({A} : Set (M3 p))) = p ^ 3
        rw [Module.card_eq_pow_finrank (K := ZMod p), ZMod.card, hdim]
      let Sgens : Finset (M3 p) := Finset.univ.filter fun X => X ∈ SingleGens v
      let Sscal : Finset (M3 p) := Finset.univ.filter fun X => ∃ c : ZMod p, X = c • (1 : M3 p)
      let Sv : Finset (M3 p) := Finset.univ.filter fun X => X ∈ v.val
      have hdisj : Disjoint Sgens Sscal := by
        rw [Finset.disjoint_left]; intro X h1 h2
        obtain ⟨c, rfl⟩ := (Finset.mem_filter.mp h2).2
        have hXG : HasM3Type (c • (1 : M3 p)) .G := (vertHasType_iff_all.mp ⟨A, hAv, hAG⟩) _ (Finset.mem_filter.mp h1).2
        have hXA : HasM3Type (c • (1 : M3 p)) .A := ⟨c, charpoly_smul_one c, minpoly_smul_one c⟩
        exact M3Type.noConfusion (hasM3Type_unique hXG hXA)
      have hsub : Sgens ∪ Sscal ⊆ Sv := by
        intro X hX; refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
        rcases Finset.mem_union.mp hX with h1 | h2
        · exact (Finset.mem_filter.mp h1).2 ▸ Subring.subset_closure rfl
        · obtain ⟨c, rfl⟩ := (Finset.mem_filter.mp h2).2; exact smul_one_mem_subring _ c
      have hcard_gens : Sgens.card = p ^ 3 - p := by
        have h1 := card_singleGens_of_type .G v ⟨A, hAv, hAG⟩
        rwa [Nat.card_eq_fintype_card, Fintype.card_subtype] at h1
      have hcard_scal : Sscal.card = p := by
        have hEq : Sscal = Finset.univ.image (fun c : ZMod p => c • (1 : M3 p)) := by
          ext X; simp [Sscal, eq_comm]
        rw [hEq, Finset.card_image_of_injective _ (fun a b h => by simpa using congrArg (fun M : M3 p => M 0 0) h),
            Finset.card_univ, ZMod.card]
      have hcard_Sv : Sv.card = p ^ 3 := by
        rwa [Nat.card_eq_fintype_card, Fintype.card_subtype] at hcard_v
      have hp2 : 2 ≤ p := (Fact.out : p.Prime).two_le
      have hle_p : p ≤ p ^ 3 := Nat.le_self_pow (by omega) p
      have heq_fin : Sgens ∪ Sscal = Sv := Finset.eq_of_subset_of_card_le hsub (by
        rw [Finset.card_union_of_disjoint hdisj, hcard_gens, hcard_scal, hcard_Sv]; omega)
      have hB_Sv : B ∈ Sv := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hAv ▸ hB_in⟩
      rw [← heq_fin, Finset.mem_union] at hB_Sv
      have hB_gen : B ∈ SingleGens v := (Finset.mem_filter.mp (hB_Sv.resolve_right (by simpa [Sscal] using hsc))).2
      exact Subtype.ext (hBw.trans hB_gen)
  · rintro (rfl | hwA)
    · obtain ⟨A, hAv, _⟩ := hv
      exact (uccgAdj_iff_comm hAv hAv).mpr rfl
    · exact fun X hX Y hY => (adj_of_type_A hwA v Y hY X hX).symm

/-! ### Section 6B: Attachments & Vertex Counts for Types `(D), (F), (H), (C), (G)` -/

private lemma hasM3Type_matD0 (p : ℕ) [Fact p.Prime] : HasM3Type (matD0 p) .D := by
  refine ⟨0, ?_, ?_⟩
  · rw [Matrix.charpoly, Matrix.det_fin_three]
    simp [matD0, Matrix.charmatrix]; ring
  · have hch : (matD0 p).charpoly = (X - C (0 : ZMod p)) ^ 3 := by
      rw [Matrix.charpoly, Matrix.det_fin_three]
      simp [matD0, Matrix.charmatrix]; ring
    have hdvd := minpoly.dvd (ZMod p) (matD0 p) (Matrix.aeval_self_charpoly (matD0 p))
    rw [hch] at hdvd
    have hle3 := minpoly_natDegree_le_three (matD0 p)
    have hdeg_ge3 : 3 ≤ (minpoly (ZMod p) (matD0 p)).natDegree := by
      by_contra hlt
      have hle2 : (minpoly (ZMod p) (matD0 p)).natDegree ≤ 2 := by omega
      have h0r : (minpoly (ZMod p) (matD0 p)).IsRoot 0 :=
        (isRoot_minpoly_iff_charpoly (matD0 p) 0).mpr (by rw [Polynomial.IsRoot, hch]; simp)
      have hpos := minpoly_natDegree_pos (matD0 p)
      have hmon := minpoly.monic (isIntegral_m3 (matD0 p))
      have hdvd2 : minpoly (ZMod p) (matD0 p) ∣ (X - C (0 : ZMod p)) ^ 2 := by
        obtain ⟨M1, hM1⟩ := Polynomial.dvd_iff_isRoot.mpr h0r
        by_cases h1 : (minpoly (ZMod p) (matD0 p)).natDegree = 1
        · have hEq : minpoly (ZMod p) (matD0 p) = X - C (0 : ZMod p) :=
            Polynomial.eq_of_monic_of_dvd_of_natDegree_le (Polynomial.monic_X_sub_C (0 : ZMod p)) hmon
              (Polynomial.dvd_iff_isRoot.mpr h0r) (by rw [Polynomial.natDegree_X_sub_C]; omega)
          rw [hEq, sq]; exact dvd_mul_right _ _
        · have h2 : (minpoly (ZMod p) (matD0 p)).natDegree = 2 := by omega
          have hM1ne : M1 ≠ 0 := fun h => by rw [h, mul_zero] at hM1; exact hmon.ne_zero hM1
          have hM1deg : M1.natDegree = 1 := by
            have := congrArg Polynomial.natDegree hM1
            rw [h2, Polynomial.natDegree_mul (Polynomial.monic_X_sub_C (0 : ZMod p)).ne_zero hM1ne,
                Polynomial.natDegree_X_sub_C] at this; omega
          have hM1mon : M1.Monic :=
            Polynomial.Monic.of_mul_monic_left (Polynomial.monic_X_sub_C (0 : ZMod p)) (hM1 ▸ hmon)
          have hM1dvd : M1 ∣ (X - C (0 : ZMod p)) ^ 2 := by
            obtain ⟨R, hR⟩ := hdvd; rw [hM1, mul_assoc] at hR
            exact ⟨R, mul_left_cancel₀ (Polynomial.monic_X_sub_C (0 : ZMod p)).ne_zero (by rw [← hR]; ring)⟩
          have hM1eq : M1 = X - C (0 : ZMod p) := by
            have hr : M1.IsRoot (-M1.coeff 0) := by
              rw [Polynomial.IsRoot, Polynomial.eq_X_add_C_of_degree_le_one (Polynomial.degree_le_of_natDegree_le (le_of_eq hM1deg))]
              have hlc : M1.coeff 1 = 1 := by simpa [Polynomial.Monic, Polynomial.leadingCoeff, hM1deg] using hM1mon
              simp [hlc]
            obtain ⟨R, hR⟩ := hM1dvd
            have hr2 : ((-M1.coeff 0 - 0) : ZMod p) ^ 2 = 0 := by
              have := congrArg (Polynomial.eval (-M1.coeff 0)) hR
              simpa [hr.eq_zero] using this
            have hc0 : M1.coeff 0 = 0 := by
              have := sub_eq_zero.mp (pow_eq_zero hr2); simpa using this
            rw [Polynomial.eq_X_add_C_of_degree_le_one (Polynomial.degree_le_of_natDegree_le (le_of_eq hM1deg))]
            have hlc : M1.coeff 1 = 1 := by simpa [Polynomial.Monic, Polynomial.leadingCoeff, hM1deg] using hM1mon
            simp [hlc, hc0]
          rw [hM1, hM1eq, sq]
      obtain ⟨R, hR⟩ := hdvd2
      have hsq0 : (matD0 p) ^ 2 = 0 := by
        have := congrArg (aeval (matD0 p)) hR
        rw [map_mul, minpoly.aeval, zero_mul] at this
        simpa using this
      have := congrArg (fun M : M3 p => M 0 2) hsq0
      simp [matD0, sq, Matrix.mul_apply, Fin.sum_univ_three] at this
    exact (Polynomial.eq_of_monic_of_dvd_of_natDegree_le
      (minpoly.monic (isIntegral_m3 (matD0 p)))
      ((Polynomial.monic_X_sub_C (0 : ZMod p)).pow 3) hdvd
      (by rw [Polynomial.natDegree_pow, Polynomial.natDegree_X_sub_C]; omega)).symm

/-- Helper: every Type D vertex has a unique `(E)` neighbor and no `(B)` neighbor;
    and every `e ∈ V_(E)` has exactly `p - 1` neighbors in `V_(D)`. -/
private lemma section5_D (p : ℕ) [Fact p.Prime] :
    (∀ v ∈ VertsOfType p .D,
      (∃! e : UCCGVert p, VertHasType e .E ∧ UCCGAdj v e) ∧
      (∀ b ∈ VertsOfType p .B, ¬ UCCGAdj v b)) ∧
    (∀ e ∈ VertsOfType p .E,
      Nat.card { d : UCCGVert p // VertHasType d .D ∧ UCCGAdj e d } = p - 1) ∧
    Nat.card (VertsOfType p .D) = (p ^ 3 - 1) * (p + 1) := by
  classical
  have : Fintype (UCCGVert p) := Fintype.ofFinite _
  have hp2 : 2 ≤ p := (Fact.out : p.Prime).two_le
  have hD0_D : HasM3Type (matD0 p) .D := hasM3Type_matD0 p
  have hD_part1 : ∀ v ∈ VertsOfType p .D,
      (∃! e : UCCGVert p, VertHasType e .E ∧ UCCGAdj v e) ∧
      (∀ b ∈ VertsOfType p .B, ¬ UCCGAdj v b) := by
    intro v hv
    obtain ⟨A, hAv, hAD⟩ := hv
    obtain ⟨S, hS⟩ := canonical_D hAD
    let e0 : UCCGVert p := ⟨Subring.closure ({(conjAlgEquiv S).symm (matD0 p ^ 2)} : Set (M3 p)), ⟨_, rfl⟩⟩
    have hD2_E : HasM3Type (matD0 p ^ 2) .E := by
      have hsq0 : (matD0 p ^ 2) ^ 2 = 0 := by
        ext i j; fin_cases i <;> fin_cases j <;> simp [matD0, sq, Matrix.mul_apply, Fin.sum_univ_three]
      have hne0 : matD0 p ^ 2 ≠ 0 := by
        intro h; have := congrArg (fun M : M3 p => M 0 2) h
        simp [matD0, sq, Matrix.mul_apply, Fin.sum_univ_three] at this
      obtain ⟨T, hT⟩ := exists_conj_matE01 hne0 hsq0
      exact (hasM3Type_conj T _ .E).mp (hT ▸ hasM3Type_matE01 p)
    have hD_cub : matD0 p ^ 3 = (0 : ZMod p) • matD0 p ^ 2 + (0 : ZMod p) • matD0 p + (0 : ZMod p) • (1 : M3 p) := by
      ext i j; fin_cases i <;> fin_cases j <;> simp [matD0, pow_succ, Matrix.mul_apply, Fin.sum_univ_three]
    have hD2_val : matD0 p ^ 2 = !![0, 0, 1; 0, 0, 0; 0, 0, 0] := by
      ext i j; fin_cases i <;> fin_cases j <;> simp [matD0, sq, Matrix.mul_apply, Fin.sum_univ_three]
    have hmem_v : ∀ X : M3 p, X ∈ v.val ↔ ∃ c0 c1 c2 : ZMod p,
        conjAlgEquiv S X = c0 • (1 : M3 p) + c1 • matD0 p + c2 • matD0 p ^ 2 := by
      intro X
      have hv_map : v.val = (Subring.closure ({matD0 p} : Set (M3 p))).map (conjAlgEquiv S).symm.toRingHom := by
        rw [← hAv]
        ext Y; simp only [Subring.mem_map]
        constructor
        · intro hY
          refine ⟨conjAlgEquiv S Y, ?_, by simp⟩
          rw [← hS, subring_closure_conj]; exact ⟨Y, hY, rfl⟩
        · rintro ⟨Z, hZ, rfl⟩
          rw [← hS, subring_closure_conj] at hZ
          rcases hZ with ⟨W, hW, hSW⟩
          have : (conjAlgEquiv S).symm Z = W := by rw [← hSW]; simp
          change (conjAlgEquiv S).symm Z ∈ Subring.closure {A}
          rwa [this]
      rw [hv_map]
      constructor
      · rintro ⟨Y, hY, rfl⟩
        simpa using (mem_closure_deg3 hD_cub Y).mp hY
      · rintro ⟨c0, c1, c2, hEq⟩
        exact ⟨conjAlgEquiv S X, (mem_closure_deg3 hD_cub _).mpr ⟨c0, c1, c2, hEq⟩, by simp⟩
    -- Any element `X ∈ v.val` has `charpoly = (X - c0)^3`, so NEVER Type B!
    -- And `X ∈ v.val` has Type E iff `c1 = 0 ∧ c2 ≠ 0`, which generates `e0`!
    constructor
    · refine ⟨e0, ⟨⟨_, rfl, (hasM3Type_conj S _ .E).mp (by simpa using hD2_E)⟩, ?_⟩, ?_⟩
      · have hcomm : conjAlgEquiv S A * matD0 p ^ 2 = matD0 p ^ 2 * conjAlgEquiv S A := by
          have hm : matD0 p ^ 2 ∈ Subring.closure ({conjAlgEquiv S A} : Set (M3 p)) :=
            hS ▸ (sq (matD0 p) ▸ mul_mem (Subring.subset_closure rfl) (Subring.subset_closure rfl))
          obtain ⟨f, hf⟩ := (mem_subring_closure_iff_aeval _ _).mp hm
          rw [← hf]; exact (commute_aeval_self (conjAlgEquiv S A) f).symm
        refine (uccgAdj_iff_comm hAv rfl).mpr ?_
        apply (conjAlgEquiv S).injective
        simpa [map_mul] using hcomm
      · rintro e ⟨heE, hadj⟩
        have hle : e.val ≤ v.val := le_of_adj_nonderog (Or.inr (Or.inl ⟨A, hAv, hAD⟩)) hadj
        obtain ⟨X, hXe, hXE⟩ := heE
        have hXv : X ∈ v.val := hle (hXe ▸ Subring.subset_closure rfl)
        obtain ⟨c0, c1, c2, hc⟩ := (hmem_v X).mp hXv
        have hXE' : HasM3Type (conjAlgEquiv S X) .E := (hasM3Type_conj S X .E).mpr hXE
        have hc1 : c1 = 0 := by
          by_contra hne
          -- Then `conj S X` has Type D (same subring as `matD0`), contradicting Type E!
          have hsq : (conjAlgEquiv S X - c0 • (1 : M3 p)) ^ 2 = (c1 ^ 2) • matD0 p ^ 2 := by
            rw [hc, hD2_val]; ext i j; fin_cases i <;> fin_cases j <;>
              simp [matD0, sq, Matrix.mul_apply, Fin.sum_univ_three]
          have hch : (conjAlgEquiv S X).charpoly = (Polynomial.X - C c0) ^ 3 := by
            rw [hc, hD2_val, Matrix.charpoly, Matrix.det_fin_three]
            simp [matD0, Matrix.charmatrix]; ring
          rcases hXE' with ⟨l, hchl, hml⟩
          have hl : l = c0 := by
            have := congrArg (fun f : (ZMod p)[X] => f.IsRoot c0) (hch.symm.trans hchl)
            have htrue : ((Polynomial.X - C c0) ^ 3).IsRoot c0 := by simp [Polynomial.IsRoot]
            have h1 := this.mp htrue
            simp [Polynomial.IsRoot, sub_eq_zero] at h1; exact h1.symm
          subst hl
          have h0 := minpoly.aeval (ZMod p) (conjAlgEquiv S X)
          rw [hml, map_pow, map_sub, aeval_X, aeval_C, Algebra.algebraMap_eq_smul_one, hsq] at h0
          have h02 := congrArg (fun M : M3 p => M 0 2) h0
          simp [hD2_val] at h02
          exact hne h02
        subst hc1; simp only [zero_smul, add_zero] at hc
        have hc2 : c2 ≠ 0 := by
          intro h0; subst h0; simp only [zero_smul, add_zero] at hc
          have hXA : HasM3Type (conjAlgEquiv S X) .A := ⟨c0, hc ▸ charpoly_smul_one c0, hc ▸ minpoly_smul_one c0⟩
          exact M3Type.noConfusion (hasM3Type_unique hXA hXE')
        have hcl_S : Subring.closure ({conjAlgEquiv S X} : Set (M3 p)) = Subring.closure ({matD0 p ^ 2} : Set (M3 p)) := by
          rw [hc, add_comm, subring_closure_affine _ hc2 c0]
        apply Subtype.ext; rw [← hXe]
        have h1 := congrArg (Subring.map (conjAlgEquiv S).symm.toRingHom) hcl_S
        rw [subring_map_closure, subring_map_closure, Set.image_singleton, Set.image_singleton] at h1
        simpa [e0] using h1
    · intro b hb hadj
      have hle : b.val ≤ v.val := le_of_adj_nonderog (Or.inr (Or.inl ⟨A, hAv, hAD⟩)) hadj
      obtain ⟨X, hXb, hXB⟩ := hb
      obtain ⟨c0, c1, c2, hc⟩ := (hmem_v X).mp (hle (hXb ▸ Subring.subset_closure rfl))
      have hch : (conjAlgEquiv S X).charpoly = (Polynomial.X - C c0) ^ 3 := by
        rw [hc, hD2_val, Matrix.charpoly, Matrix.det_fin_three]
        simp [matD0, Matrix.charmatrix]; ring
      have h1 := (hasM3Type_invariants ((hasM3Type_conj S X .B).mpr hXB)).2.1
      dsimp only at h1
      rw [hch] at h1
      have hfilt : (Finset.univ.filter fun x : ZMod p => ((Polynomial.X - C c0) ^ 3).IsRoot x) = {c0} := by
        ext x; simp [Polynomial.IsRoot, sub_eq_zero]
      rw [hfilt, Finset.card_singleton] at h1; omega
  -- Part 2: Every `e ∈ V_(E)` has `p - 1` neighbors in `V_(D)`!
  have hD_part2 : ∀ e ∈ VertsOfType p .E,
      Nat.card { d : UCCGVert p // VertHasType d .D ∧ UCCGAdj e d } = p - 1 := by
    intro e he
    obtain ⟨A, hAe, hAE⟩ := he
    obtain ⟨S, hS⟩ := canonical_E hAE
    -- Transport via `conjAlgEquiv S` so `e` becomes `e0 = ⟨matE01 p⟩`!
    let e0 : UCCGVert p := ⟨Subring.closure ({matE01 p} : Set (M3 p)), ⟨_, rfl⟩⟩
    have heq_card : Nat.card { d : UCCGVert p // VertHasType d .D ∧ UCCGAdj e d } =
        Nat.card { d : UCCGVert p // VertHasType d .D ∧ UCCGAdj e0 d } := by
      refine Nat.card_congr ?_
      let mapV (d : UCCGVert p) : UCCGVert p :=
        ⟨d.val.map (conjAlgEquiv S).toRingHom, by
          obtain ⟨M, hMd⟩ := d.prop
          exact ⟨conjAlgEquiv S M, by rw [hMd, subring_map_closure, Set.image_singleton]; rfl⟩⟩
      let invV (d : UCCGVert p) : UCCGVert p :=
        ⟨d.val.map (conjAlgEquiv S).symm.toRingHom, by
          obtain ⟨M, hMd⟩ := d.prop
          exact ⟨(conjAlgEquiv S).symm M, by rw [hMd, subring_map_closure, Set.image_singleton]; rfl⟩⟩
      have hmap_type : ∀ d, VertHasType (mapV d) .D ↔ VertHasType d .D := fun d => by
        obtain ⟨M, hMd⟩ := d.prop
        have hM1 : conjAlgEquiv S M ∈ SingleGens (mapV d) := by
          show Subring.closure ({conjAlgEquiv S M} : Set (M3 p)) = d.val.map (conjAlgEquiv S).toRingHom
          rw [hMd, subring_map_closure, Set.image_singleton]; rfl
        constructor
        · intro h; exact ⟨M, hMd.symm, (hasM3Type_conj S M .D).mp ((vertHasType_iff_all.mp h) _ hM1)⟩
        · intro h; exact ⟨conjAlgEquiv S M, hM1, (hasM3Type_conj S M .D).mpr ((vertHasType_iff_all.mp h) M hMd.symm)⟩
      have hmap_adj : ∀ d, UCCGAdj e0 (mapV d) ↔ UCCGAdj e d := fun d => by
        obtain ⟨M, hMd⟩ := d.prop
        have hM1 : conjAlgEquiv S M ∈ SingleGens (mapV d) := by
          show Subring.closure ({conjAlgEquiv S M} : Set (M3 p)) = d.val.map (conjAlgEquiv S).toRingHom
          rw [hMd, subring_map_closure, Set.image_singleton]; rfl
        have hA1 : conjAlgEquiv S A ∈ SingleGens e0 := hS
        rw [uccgAdj_iff_comm hA1 hM1, uccgAdj_iff_comm hAe hMd.symm, ← map_mul, ← map_mul]
        exact (conjAlgEquiv S).injective.eq_iff
      refine Equiv.ofBijective (fun d => ⟨mapV d.val, (hmap_type d.val).mpr d.prop.1, (hmap_adj d.val).mpr d.prop.2⟩) ⟨?_, ?_⟩
      · intro d1 d2 h
        apply Subtype.ext; apply Subtype.ext
        have h1 := congrArg (fun z => z.val.val.map (conjAlgEquiv S).symm.toRingHom) h
        have hcancel : ∀ T : Subring (M3 p), (T.map (conjAlgEquiv S).toRingHom).map (conjAlgEquiv S).symm.toRingHom = T := fun T => by
          ext X; simp only [Subring.mem_map]; constructor
          · rintro ⟨_, ⟨Y, hY, rfl⟩, hEq⟩
            have hYX : Y = X := by simpa using hEq
            exact hYX ▸ hY
          · intro hX; exact ⟨conjAlgEquiv S X, ⟨X, hX, rfl⟩, by simp⟩
        change (d1.val.val.map (conjAlgEquiv S).toRingHom).map (conjAlgEquiv S).symm.toRingHom =
          (d2.val.val.map (conjAlgEquiv S).toRingHom).map (conjAlgEquiv S).symm.toRingHom at h1
        rw [hcancel, hcancel] at h1; exact h1
      · intro d
        have hcancel : mapV (invV d.val) = d.val := by
          apply Subtype.ext; ext X; simp only [mapV, invV, Subring.mem_map]; constructor
          · rintro ⟨_, ⟨Y, hY, rfl⟩, hEq⟩
            have hYX : Y = X := by simpa using hEq
            exact hYX ▸ hY
          · intro hX; exact ⟨(conjAlgEquiv S).symm X, ⟨X, hX, rfl⟩, by simp⟩
        refine ⟨⟨invV d.val, (hmap_type _).mp (hcancel.symm ▸ d.prop.1), (hmap_adj _).mp (hcancel.symm ▸ d.prop.2)⟩,
          Subtype.ext hcancel⟩
    rw [heq_card]
    -- Now parametrize `{d | VertHasType d .D ∧ UCCGAdj e0 d}` by `r ∈ {r : ZMod p // r ≠ 0}` via
    -- `D_r := !![0, 0, 1; 0, 0, 0; 0, r, 0]`!
    -- Check: `D_r * matE01 = 0 = matE01 * D_r` AND `D_r^2 = r • matE01` (`≠ 0`), `D_r^3 = 0`!!
    let Dr (r : ZMod p) : M3 p := !![0, 0, 1; 0, 0, 0; 0, r, 0]
    have hDr_sq : ∀ r : ZMod p, Dr r ^ 2 = r • matE01 p := fun r => by
      ext i j; fin_cases i <;> fin_cases j <;> simp [Dr, matE01, sq, Matrix.mul_apply, Fin.sum_univ_three]
    have hDr_cub : ∀ r : ZMod p, Dr r ^ 3 = (0 : ZMod p) • Dr r ^ 2 + (0 : ZMod p) • Dr r + (0 : ZMod p) • (1 : M3 p) := fun r => by
      ext i j; fin_cases i <;> fin_cases j <;> simp [Dr, pow_succ, Matrix.mul_apply, Fin.sum_univ_three]
    have hDr_D : ∀ {r : ZMod p}, r ≠ 0 → HasM3Type (Dr r) .D := fun {r} hr => by
      have hli' : LinearIndependent (ZMod p) ![(Pi.single 0 1 : V3 p), Pi.single 2 1, r⁻¹ • Pi.single 1 1] := by
        rw [linearIndependent_three_iff]; intro c0 c1 c2 h
        have h0 := congrFun h 0; have h1 := congrFun h 1; have h2 := congrFun h 2
        simp at h0 h1 h2
        exact ⟨h0, h2, h1.resolve_right hr⟩
      have hconj' := glOfCols_mul_eq hli' (Dr r) (matD0 p)
        (by ext i; fin_cases i <;> simp [Dr, matD0, Matrix.mulVec, dotProduct, Fin.sum_univ_three])
        (by ext i; fin_cases i <;> simp [Dr, matD0, Matrix.mulVec, dotProduct, Fin.sum_univ_three])
        (by ext i; fin_cases i <;> simp [Dr, matD0, Matrix.mulVec, dotProduct, Fin.sum_univ_three, mul_inv_cancel₀ hr])
      exact (hasM3Type_conj _ (Dr r) .D).mp (hconj' ▸ hD0_D)
    have hDr_adj : ∀ r : ZMod p, UCCGAdj e0 ⟨Subring.closure ({Dr r} : Set (M3 p)), ⟨_, rfl⟩⟩ := fun r =>
      (uccgAdj_iff_comm rfl rfl).mpr (by
        ext i j; fin_cases i <;> fin_cases j <;> simp [Dr, matE01, Matrix.mul_apply, Fin.sum_univ_three])
    let NZ := { r : ZMod p // r ≠ 0 }
    have hbij : NZ ≃ { d : UCCGVert p // VertHasType d .D ∧ UCCGAdj e0 d } :=
      Equiv.ofBijective (fun r : NZ =>
        ⟨⟨Subring.closure ({Dr r.val} : Set (M3 p)), ⟨_, rfl⟩⟩, ⟨Dr r.val, rfl, hDr_D r.prop⟩, hDr_adj r.val⟩)
        ⟨fun r1 r2 hEq => by
          have hmem : Dr r1.val ∈ Subring.closure ({Dr r2.val} : Set (M3 p)) := by
            have hcl : Subring.closure ({Dr r1.val} : Set (M3 p)) = Subring.closure ({Dr r2.val} : Set (M3 p)) :=
              congrArg (fun z => z.val.val) hEq
            rw [← hcl]; exact Subring.subset_closure rfl
          obtain ⟨c0, c1, c2, hc⟩ := (mem_closure_deg3 (hDr_cub r2.val) _).mp hmem
          rw [hDr_sq r2.val] at hc
          have h02 := congrArg (fun M : M3 p => M 0 2) hc
          have h21 := congrArg (fun M : M3 p => M 2 1) hc
          simp [Dr, matE01] at h02 h21
          exact Subtype.ext (by rw [h21, ← h02, one_mul]),
         fun d => by
          obtain ⟨M, hMd, hMD⟩ := d.prop.1
          have hcomm : matE01 p * M = M * matE01 p := (uccgAdj_iff_comm rfl hMd).mp d.prop.2
          have h10 : M 1 0 = 0 := by have := congrArg (fun T : M3 p => T 0 0) hcomm; simp [matE01, Matrix.mul_apply, Fin.sum_univ_three] at this; exact this
          have h12 : M 1 2 = 0 := by have := congrArg (fun T : M3 p => T 0 2) hcomm; simp [matE01, Matrix.mul_apply, Fin.sum_univ_three] at this; exact this
          have h20 : M 2 0 = 0 := by have := congrArg (fun T : M3 p => T 2 1) hcomm; simp [matE01, Matrix.mul_apply, Fin.sum_univ_three] at this; exact this.symm
          have h00_11 : M 1 1 = M 0 0 := by have := congrArg (fun T : M3 p => T 0 1) hcomm; simp [matE01, Matrix.mul_apply, Fin.sum_univ_three] at this; exact this
          -- `M.charpoly = (X - M 0 0)^2 * (X - M 2 2)`! Since `M` has Type D, `M 2 2 = M 0 0` and `(M - M 0 0•1)^2 ≠ 0`!
          have hchM : M.charpoly = (Polynomial.X - C (M 0 0)) ^ 2 * (Polynomial.X - C (M 2 2)) := by
            rw [Matrix.charpoly, Matrix.det_fin_three]
            simp [Matrix.charmatrix, h10, h12, h20, h00_11, sq]
          have h22 : M 2 2 = M 0 0 := by
            have h1 := (hasM3Type_invariants hMD).2.1
            dsimp only at h1
            rw [hchM] at h1
            by_contra hne
            have hfilt : (Finset.univ.filter fun x : ZMod p => ((Polynomial.X - C (M 0 0)) ^ 2 * (Polynomial.X - C (M 2 2))).IsRoot x) = {M 0 0, M 2 2} := by
              ext x; simp [Polynomial.IsRoot, sub_eq_zero]
            rw [hfilt, Finset.card_pair (Ne.symm hne)] at h1; omega
          have hsqM : (M - M 0 0 • (1 : M3 p)) ^ 2 = (M 0 2 * M 2 1) • matE01 p := by
            ext i j; fin_cases i <;> fin_cases j <;>
              simp [matE01, sq, Matrix.mul_apply, Fin.sum_univ_three, h10, h12, h20, h00_11, h22]
          have hprod_ne : M 0 2 * M 2 1 ≠ 0 := by
            intro h0; rw [h0, zero_smul] at hsqM
            have hdvd := minpoly.dvd (ZMod p) M (show aeval M ((Polynomial.X - C (M 0 0)) ^ 2) = 0 by
              simpa [Algebra.algebraMap_eq_smul_one] using hsqM)
            have hle := Polynomial.natDegree_le_of_dvd hdvd ((Polynomial.monic_X_sub_C (M 0 0)).pow 2).ne_zero
            rw [Polynomial.natDegree_pow, Polynomial.natDegree_X_sub_C] at hle
            have h3 := (hasM3Type_invariants hMD).1; dsimp only at h3; omega
          have h02_ne : M 0 2 ≠ 0 := left_ne_zero_of_mul hprod_ne
          have h21_ne : M 2 1 ≠ 0 := right_ne_zero_of_mul hprod_ne
          set r := (M 0 2)⁻¹ * M 2 1
          have hr_ne : r ≠ 0 := mul_ne_zero (inv_ne_zero h02_ne) h21_ne
          refine ⟨⟨r, hr_ne⟩, Subtype.ext (Subtype.ext ?_)⟩
          show Subring.closure ({Dr r} : Set (M3 p)) = d.val.val
          rw [← hMd, subring_closure_eq_iff]
          have hM_eq : M = M 0 0 • (1 : M3 p) + M 0 2 • Dr r + (r⁻¹ * M 0 1) • Dr r ^ 2 := by
            rw [hDr_sq r]
            ext i j; fin_cases i <;> fin_cases j <;>
              simp [Dr, matE01, h10, h12, h20, h00_11, h22, r]
            · field_simp [h02_ne, h21_ne]
            · rw [← mul_assoc, mul_inv_cancel₀ h02_ne, one_mul]
          refine ⟨(mem_closure_deg3 (hDr_cub r) M).mpr ⟨M 0 0, M 0 2, r⁻¹ * M 0 1, hM_eq⟩, ?_⟩
          -- `Dr r ∈ ⟨M⟩`: first `matE01 ∈ ⟨M⟩` via `(M - M 0 0•1)^2 = (M 0 2 * M 2 1) • matE01`, then `Dr r`!
          have hMsub : M - M 0 0 • (1 : M3 p) ∈ Subring.closure ({M} : Set (M3 p)) :=
            sub_mem (Subring.subset_closure rfl) (smul_one_mem_subring _ _)
          have hE01_mem : matE01 p ∈ Subring.closure ({M} : Set (M3 p)) := by
            have h1 : (M 0 2 * M 2 1)⁻¹ • ((M - M 0 0 • (1 : M3 p)) ^ 2) = matE01 p := by
              rw [hsqM, smul_smul, inv_mul_cancel₀ hprod_ne, one_smul]
            rw [← h1]; exact smul_mem_subring _ _ (sq (M - M 0 0 • (1 : M3 p)) ▸ mul_mem hMsub hMsub)
          have hDr_eq : Dr r = (M 0 2)⁻¹ • ((M - M 0 0 • (1 : M3 p)) - M 0 1 • matE01 p) := by
            ext i j; fin_cases i <;> fin_cases j <;>
              simp [Dr, matE01, h10, h12, h20, h00_11, h22, r, inv_mul_cancel₀ h02_ne]
          rw [hDr_eq]
          exact smul_mem_subring _ _ (sub_mem hMsub (smul_mem_subring _ _ hE01_mem))⟩
    rw [← Nat.card_congr hbij, Nat.card_eq_fintype_card, Fintype.card_subtype_compl, ZMod.card, Fintype.card_unique]
  -- Part 3: `|V_(D)| = |V_(E)| * (p - 1) = (p^3 - 1) * (p + 1)`!
  have hD_card : Nat.card (VertsOfType p .D) = (p ^ 3 - 1) * (p + 1) := by
    let : Fintype (VertsOfType p .D) := Fintype.ofFinite _
    let : Fintype (VertsOfType p .E) := Fintype.ofFinite _
    let toE : VertsOfType p .D → VertsOfType p .E := fun d =>
      ⟨Classical.choose (hD_part1 d.val d.prop).1, (Classical.choose_spec (hD_part1 d.val d.prop).1).1.1⟩
    have hsum : Fintype.card (VertsOfType p .D) =
        ∑ e : VertsOfType p .E, (Finset.univ.filter fun d : VertsOfType p .D => toE d = e).card := by
      rw [← Finset.card_biUnion]
      · have : Finset.univ.biUnion (fun e : VertsOfType p .E =>
            Finset.univ.filter fun d : VertsOfType p .D => toE d = e) = Finset.univ := by ext d; simp
        rw [this, Finset.card_univ]
      · intro e1 _ e2 _ hne; change Disjoint _ _; rw [Finset.disjoint_left]
        intro d h1 h2; exact hne (((Finset.mem_filter.mp h1).2).symm.trans (Finset.mem_filter.mp h2).2)
    have hfib : ∀ e : VertsOfType p .E,
        (Finset.univ.filter fun d : VertsOfType p .D => toE d = e).card = p - 1 := fun e => by
      let : Fintype { d : UCCGVert p // VertHasType d .D ∧ UCCGAdj e.val d } := Fintype.ofFinite _
      have heq : { d : VertsOfType p .D // toE d = e } ≃ { d : UCCGVert p // VertHasType d .D ∧ UCCGAdj e.val d } :=
        { toFun := fun d => ⟨d.val.val, d.val.prop, fun X hX Y hY =>
            ((Classical.choose_spec (hD_part1 d.val.val d.val.prop).1).1.2 Y hY X (by
              have h1 : Classical.choose (hD_part1 d.val.val d.val.prop).1 = e.val := congrArg Subtype.val d.prop
              rwa [h1])).symm⟩
          invFun := fun d => ⟨⟨d.val, d.prop.1⟩, Subtype.ext ((Classical.choose_spec (hD_part1 d.val d.prop.1).1).2 e.val
            ⟨e.prop, fun X hX Y hY => (d.prop.2 Y hY X hX).symm⟩).symm⟩
          left_inv := fun _ => rfl
          right_inv := fun _ => rfl }
      rw [← Fintype.card_subtype, Fintype.card_congr heq, ← Nat.card_eq_fintype_card]
      exact hD_part2 e.val e.prop
    simp_rw [hfib] at hsum
    rw [Finset.sum_const, Finset.card_univ, smul_eq_mul, ← Nat.card_eq_fintype_card,
        ← Nat.card_eq_fintype_card, (card_verts_B_E p).2] at hsum
    rw [hsum]
    have hp3 : 1 ≤ p ^ 3 := Nat.one_le_pow 3 p (by omega)
    have : (p ^ 2 + p + 1) * (p + 1) * (p - 1) = (p ^ 3 - 1) * (p + 1) := by
      zify [show 1 ≤ p by omega, hp3]; ring
    exact this
  exact ⟨hD_part1, hD_part2, hD_card⟩

/-- Helper: Number of adjacent `(B, E)` pairs equals `(p^2 + p + 1) * p^2 * (p + 1)`. -/
private lemma card_BE_edges (p : ℕ) [Fact p.Prime] :
    Nat.card { pair : VertsOfType p .B × VertsOfType p .E // UCCGAdj pair.1.val pair.2.val } =
      (p ^ 2 + p + 1) * p ^ 2 * (p + 1) := by
  classical
  let : Fintype (VertsOfType p .B) := Fintype.ofFinite _
  let : Fintype (VertsOfType p .E) := Fintype.ofFinite _
  obtain ⟨Φ, hΦB, hΦE, hΦadj⟩ := theorem_4_1 p
  have hE_nbrs : ∀ b : VertsOfType p .B,
      (Finset.univ.filter fun e : VertsOfType p .E => UCCGAdj b.val e.val).card = p + 1 := by
    intro b
    set xb := Φ ⟨b.val, Or.inl b.prop⟩
    have hxb_ninc : ¬ xb.1.val ≤ xb.2.val := (hΦB ⟨b.val, Or.inl b.prop⟩).mp b.prop
    let toP : { e : VertsOfType p .E // UCCGAdj b.val e.val } → { P : PGPoint p // P.val ≤ xb.2.val } := fun e =>
      ⟨(Φ ⟨e.val.val, Or.inr e.val.prop⟩).1, by
        have hadj := (hΦadj ⟨b.val, Or.inl b.prop⟩ ⟨e.val.val, Or.inr e.val.prop⟩).mp e.prop
        have he_inc : (Φ ⟨e.val.val, Or.inr e.val.prop⟩).1.val ≤ (Φ ⟨e.val.val, Or.inr e.val.prop⟩).2.val :=
          (hΦE ⟨e.val.val, Or.inr e.val.prop⟩).mp e.val.prop
        rcases hadj with ⟨hP, hL⟩ | ⟨h1, _, _⟩ | ⟨_, _, ⟨h21, _⟩, _⟩ | ⟨_, _, ⟨h1, _⟩, _⟩ | ⟨_, _, _, ⟨_, h2⟩⟩
        · exact absurd (hP ▸ hL ▸ he_inc) hxb_ninc
        · exact absurd h1 hxb_ninc
        · exact h21
        · exact absurd h1 hxb_ninc
        · exact absurd he_inc h2⟩
    have htoP_bij : Function.Bijective toP := by
      constructor
      · intro e1 e2 hEq
        have hPeq : (Φ ⟨e1.val.val, Or.inr e1.val.prop⟩).1 = (Φ ⟨e2.val.val, Or.inr e2.val.prop⟩).1 :=
          congrArg Subtype.val hEq
        have hline : ∀ e : { e : VertsOfType p .E // UCCGAdj b.val e.val },
            (Φ ⟨e.val.val, Or.inr e.val.prop⟩).2.val = xb.1.val ⊔ (toP e).val.val := fun e => by
          have hadj := (hΦadj ⟨b.val, Or.inl b.prop⟩ ⟨e.val.val, Or.inr e.val.prop⟩).mp e.prop
          have he_inc := (hΦE ⟨e.val.val, Or.inr e.val.prop⟩).mp e.val.prop
          have h12 : xb.1.val ≤ (Φ ⟨e.val.val, Or.inr e.val.prop⟩).2.val := by
            rcases hadj with ⟨hP, hL⟩ | ⟨h1, _, _⟩ | ⟨_, _, _, ⟨h12, _⟩⟩ | ⟨_, _, ⟨h1, _⟩, _⟩ | ⟨_, _, _, ⟨_, h2⟩⟩
            · exact absurd (hP ▸ hL ▸ he_inc) hxb_ninc
            · exact absurd h1 hxb_ninc
            · exact h12
            · exact absurd h1 hxb_ninc
            · exact absurd he_inc h2
          have hle : xb.1.val ⊔ (toP e).val.val ≤ (Φ ⟨e.val.val, Or.inr e.val.prop⟩).2.val := sup_le h12 he_inc
          have hneP : xb.1.val ≠ (toP e).val.val := fun h => hxb_ninc (h ▸ (toP e).prop)
          set P1 : Submodule (ZMod p) (V3 p) := xb.1.val
          set P2 : Submodule (ZMod p) (V3 p) := (toP e).val.val
          have hP1 : Module.finrank (ZMod p) ↥P1 = 1 := xb.1.prop
          have hP2 : Module.finrank (ZMod p) ↥P2 = 1 := (toP e).val.prop
          have hinf : P1 ⊓ P2 = ⊥ := by
            by_contra hne
            have hle1 : Module.finrank (ZMod p) ↥(P1 ⊓ P2) ≤ 1 := by
              have := Submodule.finrank_mono (inf_le_left : P1 ⊓ P2 ≤ P1)
              rw [hP1] at this; exact this
            have hpos : 0 < Module.finrank (ZMod p) ↥(P1 ⊓ P2) := by
              by_contra h0; exact hne (Submodule.finrank_eq_zero.mp (by omega))
            have h1 := Submodule.eq_of_le_of_finrank_eq (inf_le_left : P1 ⊓ P2 ≤ P1) (by omega)
            have h2 := Submodule.eq_of_le_of_finrank_eq (inf_le_right : P1 ⊓ P2 ≤ P2) (by omega)
            exact hneP (h1.symm.trans h2)
          have hfr : Module.finrank (ZMod p) ↥(P1 ⊔ P2) = 2 := by
            have h := Submodule.finrank_sup_add_finrank_inf_eq P1 P2
            rw [hinf, finrank_bot, add_zero, hP1, hP2] at h; exact h
          exact (Submodule.eq_of_le_of_finrank_eq hle (by rw [hfr, (Φ _).2.prop])).symm
        have hLeq : (Φ ⟨e1.val.val, Or.inr e1.val.prop⟩).2 = (Φ ⟨e2.val.val, Or.inr e2.val.prop⟩).2 :=
          Subtype.ext ((hline e1).trans (by rw [hEq]; exact (hline e2).symm))
        have hΦeq := Φ.injective (Prod.ext hPeq hLeq)
        exact Subtype.ext (Subtype.ext (congrArg (Subtype.val : { w : UCCGVert p // VertHasType w .B ∨ VertHasType w .E } → UCCGVert p) hΦeq))
      · intro P
        have hneP : xb.1.val ≠ P.val.val := fun h => hxb_ninc (h ▸ P.prop)
        set P1 : Submodule (ZMod p) (V3 p) := xb.1.val
        set P2 : Submodule (ZMod p) (V3 p) := P.val.val
        have hP1 : Module.finrank (ZMod p) ↥P1 = 1 := xb.1.prop
        have hP2 : Module.finrank (ZMod p) ↥P2 = 1 := P.val.prop
        have hinf : P1 ⊓ P2 = ⊥ := by
          by_contra hne
          have hle1 : Module.finrank (ZMod p) ↥(P1 ⊓ P2) ≤ 1 := by
            have := Submodule.finrank_mono (inf_le_left : P1 ⊓ P2 ≤ P1)
            rw [hP1] at this; exact this
          have hpos : 0 < Module.finrank (ZMod p) ↥(P1 ⊓ P2) := by
            by_contra h0; exact hne (Submodule.finrank_eq_zero.mp (by omega))
          have h1 := Submodule.eq_of_le_of_finrank_eq (inf_le_left : P1 ⊓ P2 ≤ P1) (by omega)
          have h2 := Submodule.eq_of_le_of_finrank_eq (inf_le_right : P1 ⊓ P2 ≤ P2) (by omega)
          exact hneP (h1.symm.trans h2)
        have hfr : Module.finrank (ZMod p) ↥(P1 ⊔ P2) = 2 := by
          have h := Submodule.finrank_sup_add_finrank_inf_eq P1 P2
          rw [hinf, finrank_bot, add_zero, hP1, hP2] at h; exact h
        let L : PGLine p := ⟨xb.1.val ⊔ P.val.val, hfr⟩
        let v := Φ.symm (P.val, L)
        have hvE : VertHasType v.val .E := (hΦE v).mpr (by
          show (Φ v).1.val ≤ (Φ v).2.val
          rw [Φ.apply_symm_apply]; exact le_sup_right)
        have hadj : UCCGAdj b.val v.val := (hΦadj ⟨b.val, Or.inl b.prop⟩ v).mpr (by
          have hΦv : Φ v = (P.val, L) := Φ.apply_symm_apply (P.val, L)
          rw [hΦv]
          exact Or.inr (Or.inr (Or.inl ⟨hneP, fun h => hxb_ninc (h ▸ le_sup_left),
            ⟨P.prop, le_sup_right⟩, ⟨le_sup_left, hxb_ninc⟩⟩)))
        refine ⟨⟨⟨v.val, hvE⟩, hadj⟩, Subtype.ext ?_⟩
        show (Φ ⟨v.val, Or.inr hvE⟩).1 = P.val
        have hv_eq : (⟨v.val, Or.inr hvE⟩ : { w : UCCGVert p // VertHasType w .B ∨ VertHasType w .E }) = v := Subtype.ext rfl
        rw [hv_eq, Φ.apply_symm_apply]
    have hcard_e : (Finset.univ.filter fun e : VertsOfType p .E => UCCGAdj b.val e.val).card =
        Fintype.card { e : VertsOfType p .E // UCCGAdj b.val e.val } := (Fintype.card_subtype _).symm
    let : Finite (PGPoint p) :=
      Finite.of_injective (fun P : PGPoint p => (P.val : Set (V3 p))) (fun _ _ h => Subtype.ext (SetLike.coe_injective h))
    let : Fintype { P : PGPoint p // P.val ≤ xb.2.val } := Fintype.ofFinite _
    rw [hcard_e, Fintype.card_congr (Equiv.ofBijective toP htoP_bij),
        ← Nat.card_eq_fintype_card, card_points_on_line xb.2]
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  have hsum : (Finset.univ.filter fun pair : VertsOfType p .B × VertsOfType p .E => UCCGAdj pair.1.val pair.2.val).card =
      ∑ b : VertsOfType p .B, (Finset.univ.filter fun e : VertsOfType p .E => UCCGAdj b.val e.val).card := by
    rw [Finset.card_filter, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun b _ => (Finset.card_filter _ _).symm
  rw [hsum]; simp_rw [hE_nbrs]
  rw [Finset.sum_const, Finset.card_univ, smul_eq_mul, ← Nat.card_eq_fintype_card, (card_verts_B_E p).1]

/-- Helper: Section 5(F) — bijection `ψF : V_(F) ≃ {(b, e) ∈ V_(B) × V_(E) | UCCGAdj b e}` and `|V_(F)|`! -/
private lemma section5_F (p : ℕ) [Fact p.Prime] :
    (∃ ψF : VertsOfType p .F ≃
        { pair : VertsOfType p .B × VertsOfType p .E // UCCGAdj pair.1.val pair.2.val },
      ∀ v,
        (∀ b ∈ VertsOfType p .B, UCCGAdj v.val b ↔ b = (ψF v).val.1.val) ∧
        (∀ e ∈ VertsOfType p .E, UCCGAdj v.val e ↔ e = (ψF v).val.2.val)) ∧
    Nat.card (VertsOfType p .F) = (p ^ 2 + p + 1) * p ^ 2 * (p + 1) := by
  classical
  have hF0_F : HasM3Type (matF0 p) .F := by
    have hch : (matF0 p).charpoly = (Polynomial.X - C (0 : ZMod p)) ^ 2 * (Polynomial.X - C (1 : ZMod p)) := by
      rw [Matrix.charpoly, Matrix.det_fin_three]
      simp [matF0, Matrix.charmatrix, sq]
    refine ⟨0, 1, zero_ne_one, hch, ?_⟩
    have hdvd := minpoly.dvd (ZMod p) (matF0 p) (Matrix.aeval_self_charpoly (matF0 p))
    have h0r : (minpoly (ZMod p) (matF0 p)).IsRoot 0 := (isRoot_minpoly_iff_charpoly _ 0).mpr (by rw [Polynomial.IsRoot, hch]; simp)
    have h1r : (minpoly (ZMod p) (matF0 p)).IsRoot 1 := (isRoot_minpoly_iff_charpoly _ 1).mpr (by rw [Polynomial.IsRoot, hch]; simp)
    obtain ⟨M1, hM1⟩ := Polynomial.dvd_iff_isRoot.mpr h0r
    have h1M1 : M1.IsRoot 1 := by
      rw [Polynomial.IsRoot, hM1, Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C] at h1r
      exact (mul_eq_zero.mp h1r).resolve_left (by simp)
    obtain ⟨M2, hM2⟩ := Polynomial.dvd_iff_isRoot.mpr h1M1
    have hdvd2 : (X - C (0 : ZMod p)) * (X - C (1 : ZMod p)) ∣ minpoly (ZMod p) (matF0 p) :=
      ⟨M2, by rw [hM1, hM2, mul_assoc]⟩
    have hmon := minpoly.monic (isIntegral_m3 (matF0 p))
    have hge2 : 2 ≤ (minpoly (ZMod p) (matF0 p)).natDegree := by
      have := Polynomial.natDegree_le_of_dvd hdvd2 hmon.ne_zero
      rw [Polynomial.natDegree_mul (Polynomial.monic_X_sub_C (0 : ZMod p)).ne_zero (Polynomial.monic_X_sub_C (1 : ZMod p)).ne_zero,
          Polynomial.natDegree_X_sub_C, Polynomial.natDegree_X_sub_C] at this; exact this
    have hne2 : (minpoly (ZMod p) (matF0 p)).natDegree ≠ 2 := by
      intro h2
      have hEq : minpoly (ZMod p) (matF0 p) = (X - C (0 : ZMod p)) * (X - C (1 : ZMod p)) :=
        Polynomial.eq_of_monic_of_dvd_of_natDegree_le
          ((Polynomial.monic_X_sub_C (0 : ZMod p)).mul (Polynomial.monic_X_sub_C (1 : ZMod p))) hmon hdvd2
          (by rw [h2, Polynomial.natDegree_mul (Polynomial.monic_X_sub_C (0 : ZMod p)).ne_zero
              (Polynomial.monic_X_sub_C (1 : ZMod p)).ne_zero, Polynomial.natDegree_X_sub_C, Polynomial.natDegree_X_sub_C])
      have haev := minpoly.aeval (ZMod p) (matF0 p)
      rw [hEq, map_mul, map_sub, map_sub, aeval_X, aeval_C, aeval_C,
          Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one] at haev
      have h01 := congrArg (fun M : M3 p => M 0 1) haev
      simp [matF0, Matrix.mul_apply, Fin.sum_univ_three] at h01
    have hle3 := minpoly_natDegree_le_three (matF0 p)
    exact (Polynomial.eq_of_monic_of_dvd_of_natDegree_le hmon (Matrix.charpoly_monic _) hdvd
      (by rw [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]; omega)).symm
  have hF2 : matF0 p ^ 2 = !![0, 0, 0; 0, 0, 0; 0, 0, 1] := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [matF0, sq, Matrix.mul_apply, Fin.sum_univ_three]
  have hFcub : matF0 p ^ 3 = (1 : ZMod p) • matF0 p ^ 2 + (0 : ZMod p) • matF0 p + (0 : ZMod p) • (1 : M3 p) := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [matF0, pow_succ, Matrix.mul_apply, Fin.sum_univ_three]
  -- For every `(b, e) ∈ V_B × V_E` with `UCCGAdj b e`, construct the unique `v ∈ V_F` adjacent to both!
  have hBE_canon : ∀ (b : VertsOfType p .B) (e : VertsOfType p .E), UCCGAdj b.val e.val →
      ∃ S : GL (Fin 3) (ZMod p),
        Subring.closure ({(conjAlgEquiv S).symm (matF0 p ^ 2)} : Set (M3 p)) = b.val.val ∧
        Subring.closure ({(conjAlgEquiv S).symm (matE01 p)} : Set (M3 p)) = e.val.val := by
    intro b e hadj
    obtain ⟨P, hPb, hP2, hPr, hPk, hPnle⟩ := exists_rank1_gen_B b.prop
    obtain ⟨N, hNe, hN2, hNr, hNk, hNle⟩ := exists_rank1_gen_E e.prop
    have hcomm : P * N = N * P := (uccgAdj_iff_comm hPb hNe).mp hadj
    -- Since `P ≠ N` (different types `B` vs `E`), `P * N = 0` and `N * P = 0`!
    obtain ⟨uP, wP, huP, hwP, hPvec⟩ := rank1_eq_vecMulVec hPr
    obtain ⟨uN, wN, huN, hwN, hNvec⟩ := rank1_eq_vecMulVec hNr
    have hPN0 : P * N = 0 ∧ N * P = 0 := by
      -- If `dotProduct wP uN ≠ 0`, then as in Theorem 4.1, `(span{uP}, ker P) = (span{uN}, ker N)`,
      -- contradicting `¬ range P ≤ ker P` vs `range N ≤ ker N`!
      have hd1 : dotProduct wP uN = 0 := by
        by_contra hne
        rw [hPvec, hNvec, vecMulVec_mul_vecMulVec, vecMulVec_mul_vecMulVec] at hcomm
        have hd2 : dotProduct wN uP ≠ 0 := by
          intro h0; rw [h0, zero_smul] at hcomm
          have h0' : Matrix.vecMulVec uP wN = 0 := by
            have := congrArg ((dotProduct wP uN)⁻¹ • ·) hcomm
            simpa [smul_smul, inv_mul_cancel₀ hne] using this
          have hex_u : ∃ i, uP i ≠ 0 := by by_contra h; push Not at h; exact huP (funext h)
          have hex_w : ∃ j, wN j ≠ 0 := by by_contra h; push Not at h; exact hwN (funext h)
          obtain ⟨i, hi⟩ := hex_u; obtain ⟨j, hj⟩ := hex_w
          have := congrArg (fun M : M3 p => M i j) h0'; simp [Matrix.vecMulVec_apply] at this
          rcases this with h | h <;> contradiction
        have hsc : Matrix.vecMulVec uP wN = ((dotProduct wP uN)⁻¹ * dotProduct wN uP) • Matrix.vecMulVec uN wP := by
          have := congrArg ((dotProduct wP uN)⁻¹ • ·) hcomm
          simpa [smul_smul, inv_mul_cancel₀ hne] using this
        obtain ⟨hU, hW⟩ := (vecMulVec_eq_iff huP hwN huN hwP).mp ⟨_, mul_ne_zero (inv_ne_zero hne) hd2, hsc⟩
        have hreq : LinearMap.range (Matrix.toLin' P) = LinearMap.range (Matrix.toLin' N) := by
          rw [hPvec, hNvec, range_vecMulVec huP hwP, range_vecMulVec huN hwN, hU]
        have hkeq : LinearMap.ker (Matrix.toLin' P) = LinearMap.ker (Matrix.toLin' N) := by
          rw [hPvec, hNvec, ker_vecMulVec huP, ker_vecMulVec huN, hW.symm]
        exact hPnle (by rw [hreq, hkeq]; exact hNle)
      have hd2 : dotProduct wN uP = 0 := by
        rw [hPvec, hNvec, vecMulVec_mul_vecMulVec, vecMulVec_mul_vecMulVec, hd1, zero_smul] at hcomm
        by_contra hne
        have h0' : Matrix.vecMulVec uN wP = 0 := by
          have := congrArg ((dotProduct wN uP)⁻¹ • ·) hcomm.symm
          simpa [smul_smul, inv_mul_cancel₀ hne] using this
        have hex_u : ∃ i, uN i ≠ 0 := by by_contra h; push Not at h; exact huN (funext h)
        have hex_w : ∃ j, wP j ≠ 0 := by by_contra h; push Not at h; exact hwP (funext h)
        obtain ⟨i, hi⟩ := hex_u; obtain ⟨j, hj⟩ := hex_w
        have := congrArg (fun M : M3 p => M i j) h0'; simp [Matrix.vecMulVec_apply] at this
        rcases this with h | h <;> contradiction
      exact ⟨by rw [hPvec, hNvec, vecMulVec_mul_vecMulVec, hd1, zero_smul],
             by rw [hPvec, hNvec, vecMulVec_mul_vecMulVec, hd2, zero_smul]⟩
    -- Pick `v1` with `N *ᵥ v1 ≠ 0`; set `v1' := v1 - P *ᵥ v1` (so `P *ᵥ v1' = 0` and `N *ᵥ v1' = N *ᵥ v1 ≠ 0`!),
    -- `v0 := N *ᵥ v1'`, and `v2 := uP` (so `P *ᵥ v2 = v2`, `N *ᵥ v2 = 0`)!
    have hex_v1 : ∃ v1 : V3 p, N *ᵥ v1 ≠ 0 := by
      by_contra hall; push Not at hall
      have hN0 : N = 0 := by
        ext i j
        have hij := congrFun (hall (Pi.single j 1)) i
        change dotProduct (N i) (Pi.single j 1) = 0 at hij
        rwa [dotProduct_comm, dotProduct_single_left, one_mul] at hij
      have : LinearMap.range (Matrix.toLin' N) = ⊥ := by rw [hN0]; ext x; simp
      rw [this, finrank_bot] at hNr; omega
    obtain ⟨v1_raw, hv1_raw⟩ := hex_v1
    set v1 := v1_raw - P *ᵥ v1_raw
    have hPv1 : P *ᵥ v1 = 0 := by
      rw [Matrix.mulVec_sub, Matrix.mulVec_mulVec, ← sq, hP2, sub_self]
    have hNv1 : N *ᵥ v1 = N *ᵥ v1_raw := by
      rw [Matrix.mulVec_sub, Matrix.mulVec_mulVec, hPN0.2, Matrix.zero_mulVec, sub_zero]
    set v0 := N *ᵥ v1
    have hv0_ne : v0 ≠ 0 := hNv1.symm ▸ hv1_raw
    have hNv0 : N *ᵥ v0 = 0 := by rw [Matrix.mulVec_mulVec, ← sq, hN2, Matrix.zero_mulVec]
    have hPv0 : P *ᵥ v0 = 0 := by rw [Matrix.mulVec_mulVec, hPN0.1, Matrix.zero_mulVec]
    have hPv2 : P *ᵥ uP = uP := by
      have h1 : P *ᵥ (P *ᵥ uP) = P *ᵥ uP := by rw [Matrix.mulVec_mulVec, ← sq, hP2]
      have huP_in : uP ∈ LinearMap.range (Matrix.toLin' P) := by
        rw [hPvec, range_vecMulVec huP hwP]; exact Submodule.subset_span rfl
      obtain ⟨x, rfl⟩ := huP_in
      show P *ᵥ (P *ᵥ x) = P *ᵥ x; rw [Matrix.mulVec_mulVec, ← sq, hP2]
    have hNv2 : N *ᵥ uP = 0 := by
      rw [← hPv2, Matrix.mulVec_mulVec, hPN0.2, Matrix.zero_mulVec]
    have hli : LinearIndependent (ZMod p) ![v0, v1, uP] := by
      rw [linearIndependent_three_iff]; intro c0 c1 c2 hsum
      have hP := congrArg (P *ᵥ ·) hsum
      simp only [Matrix.mulVec_add, Matrix.mulVec_smul, hPv0, hPv1, hPv2, Matrix.mulVec_zero, smul_zero, zero_add] at hP
      have hc2 : c2 = 0 := by
        by_contra hne; exact huP (by simpa [smul_smul, inv_mul_cancel₀ hne] using congrArg (c2⁻¹ • ·) hP)
      subst hc2; simp only [zero_smul, add_zero] at hsum
      have hN := congrArg (N *ᵥ ·) hsum
      simp only [Matrix.mulVec_add, Matrix.mulVec_smul, hNv0, Matrix.mulVec_zero, smul_zero, zero_add] at hN
      have hc1 : c1 = 0 := by
        by_contra hne; exact hv0_ne (by simpa [smul_smul, inv_mul_cancel₀ hne] using congrArg (c1⁻¹ • ·) hN)
      subst hc1; simp only [zero_smul, add_zero] at hsum
      have hc0 : c0 = 0 := by
        by_contra hne; exact hv0_ne (by simpa [smul_smul, inv_mul_cancel₀ hne] using congrArg (c0⁻¹ • ·) hsum)
      exact ⟨hc0, rfl, rfl⟩
    set S := (glOfCols v0 v1 uP hli)⁻¹
    have hSP : conjAlgEquiv S P = matF0 p ^ 2 := by
      rw [hF2]; exact glOfCols_mul_eq hli P _ (by simp [hPv0]) (by simp [hPv1]) (by simp [hPv2])
    have hSN : conjAlgEquiv S N = matE01 p :=
      glOfCols_mul_eq hli N _ (by simp [matE01, hNv0]) (by simp [matE01, v0]) (by simp [matE01, hNv2])
    refine ⟨S, ?_, ?_⟩
    · rw [← hSP]; simp only [AlgEquiv.symm_apply_apply]; exact hPb
    · rw [← hSN]; simp only [AlgEquiv.symm_apply_apply]; exact hNe
  -- For any `v ∈ V_F`, show it has a unique `(B)` neighbor and a unique `(E)` neighbor!
  have hF_uniq : ∀ v : VertsOfType p .F,
      ∃ (b : VertsOfType p .B) (e : VertsOfType p .E), UCCGAdj b.val e.val ∧
        (∀ b' ∈ VertsOfType p .B, UCCGAdj v.val b' ↔ b' = b.val) ∧
        (∀ e' ∈ VertsOfType p .E, UCCGAdj v.val e' ↔ e' = e.val) := by
    intro v
    obtain ⟨A, hAv, hAF⟩ := v.prop
    obtain ⟨S, hS⟩ := canonical_F hAF
    let b0 : UCCGVert p := ⟨Subring.closure ({(conjAlgEquiv S).symm (matF0 p ^ 2)} : Set (M3 p)), ⟨_, rfl⟩⟩
    let e0 : UCCGVert p := ⟨Subring.closure ({(conjAlgEquiv S).symm (matE01 p)} : Set (M3 p)), ⟨_, rfl⟩⟩
    have hF2_B : HasM3Type (matF0 p ^ 2) .B := by
      have hli : LinearIndependent (ZMod p) ![(Pi.single 2 1 : V3 p), Pi.single 1 1, Pi.single 0 1] := by
        rw [linearIndependent_three_iff]; intro c0 c1 c2 h
        exact ⟨by simpa using congrFun h 2, by simpa using congrFun h 1, by simpa using congrFun h 0⟩
      have hconj := glOfCols_mul_eq hli (matF0 p ^ 2) (matB0 p)
        (by ext i; fin_cases i <;> simp [hF2, matB0, Matrix.mulVec, dotProduct, Fin.sum_univ_three])
        (by ext i; fin_cases i <;> simp [hF2, matB0, Matrix.mulVec, dotProduct, Fin.sum_univ_three])
        (by ext i; fin_cases i <;> simp [hF2, matB0, Matrix.mulVec, dotProduct, Fin.sum_univ_three])
      exact (hasM3Type_conj _ _ .B).mp (hconj ▸ hasM3Type_matB0 p)
    have hE01_E : HasM3Type (matE01 p) .E := hasM3Type_matE01 p
    have hb0_B : VertHasType b0 .B := ⟨_, rfl, (hasM3Type_conj S _ .B).mp (by simpa using hF2_B)⟩
    have he0_E : VertHasType e0 .E := ⟨_, rfl, (hasM3Type_conj S _ .E).mp (by simpa using hE01_E)⟩
    have hbe_adj : UCCGAdj b0 e0 := by
      refine (uccgAdj_iff_comm rfl rfl).mpr ?_
      apply (conjAlgEquiv S).injective; simp only [map_mul, AlgEquiv.apply_symm_apply]
      rw [hF2]; ext i j; fin_cases i <;> fin_cases j <;> simp [matE01, Matrix.mul_apply, Fin.sum_univ_three]
    have hmem_v : ∀ X : M3 p, X ∈ v.val.val ↔ ∃ c0 c1 c2 : ZMod p,
        conjAlgEquiv S X = c0 • (1 : M3 p) + c1 • matF0 p + c2 • matF0 p ^ 2 := by
      intro X
      have hv_map : v.val.val = (Subring.closure ({matF0 p} : Set (M3 p))).map (conjAlgEquiv S).symm.toRingHom := by
        rw [← hAv]
        ext Y; simp only [Subring.mem_map]
        constructor
        · intro hY
          refine ⟨conjAlgEquiv S Y, ?_, by simp⟩
          rw [← hS, subring_closure_conj]; exact ⟨Y, hY, rfl⟩
        · rintro ⟨Z, hZ, rfl⟩
          rw [← hS, subring_closure_conj] at hZ
          rcases hZ with ⟨W, hW, hSW⟩
          have : (conjAlgEquiv S).symm Z = W := by rw [← hSW]; simp
          change (conjAlgEquiv S).symm Z ∈ Subring.closure {A}
          rwa [this]
      rw [hv_map]; constructor
      · rintro ⟨Y, hY, rfl⟩; simpa using (mem_closure_deg3 hFcub Y).mp hY
      · rintro ⟨c0, c1, c2, hEq⟩; exact ⟨conjAlgEquiv S X, (mem_closure_deg3 hFcub _).mpr ⟨c0, c1, c2, hEq⟩, by simp⟩
    have hE01_eq : matE01 p = matF0 p - matF0 p ^ 2 := by
      rw [hF2]; ext i j; fin_cases i <;> fin_cases j <;> simp [matE01, matF0]
    refine ⟨⟨b0, hb0_B⟩, ⟨e0, he0_E⟩, hbe_adj, ?_, ?_⟩
    · intro b' hb'
      constructor
      · intro hadj
        have hle := le_of_adj_nonderog (Or.inr (Or.inr (Or.inl v.prop))) hadj
        obtain ⟨X, hXb, hXB⟩ := hb'
        obtain ⟨c0, c1, c2, hc⟩ := (hmem_v X).mp (hle (hXb ▸ Subring.subset_closure rfl))
        have hXB' := (hasM3Type_conj S X .B).mpr hXB
        have hc1 : c1 = 0 := by
          -- If `c1 ≠ 0`, `conj S X` has either `c1 + c2 = 0` (Type E) or `c1 + c2 ≠ 0` (Type F), never Type B!
          by_contra hc1_ne
          have hval : conjAlgEquiv S X = !![c0, c1, 0; 0, c0, 0; 0, 0, c0 + c1 + c2] := by
            rw [hc, hF2]; ext i j; fin_cases i <;> fin_cases j <;> simp [matF0, add_assoc]
          have hch : (conjAlgEquiv S X).charpoly = (Polynomial.X - C c0) ^ 2 * (Polynomial.X - C (c0 + c1 + c2)) := by
            rw [hval, Matrix.charpoly, Matrix.det_fin_three]
            simp [Matrix.charmatrix, -mul_eq_mul_right_iff, -mul_eq_mul_left_iff]; ring
          rcases hXB' with ⟨l, m, hlm, hchl, hml⟩
          -- `conj S X` satisfies `(X - l)(X - m) = 0`, so `(X - c0)(X - (c0+c1+c2)) = 0`!
          have hroots : {l, m} = ({c0, c0 + c1 + c2} : Finset (ZMod p)) := by
            ext x
            have h := congrArg (fun f : (ZMod p)[X] => f.IsRoot x) (hchl.symm.trans hch)
            simp only [Polynomial.IsRoot, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_sub,
              Polynomial.eval_X, Polynomial.eval_C, mul_eq_zero, sq_eq_zero_iff, sub_eq_zero] at h
            simp only [Finset.mem_insert, Finset.mem_singleton]
            exact h.to_iff
          have hprod0 : (conjAlgEquiv S X - c0 • (1 : M3 p)) * (conjAlgEquiv S X - (c0 + c1 + c2) • (1 : M3 p)) = 0 := by
            have hmin := minpoly.aeval (ZMod p) (conjAlgEquiv S X)
            rw [hml, map_mul, map_sub, map_sub, aeval_X, aeval_C, aeval_C,
                Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one] at hmin
            have hpair : (l = c0 ∧ m = c0 + c1 + c2) ∨ (l = c0 + c1 + c2 ∧ m = c0) := by
              have h1 : l ∈ ({c0, c0 + c1 + c2} : Finset (ZMod p)) := hroots ▸ Finset.mem_insert_self l {m}
              have h2 : m ∈ ({c0, c0 + c1 + c2} : Finset (ZMod p)) := hroots ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self m)
              simp only [Finset.mem_insert, Finset.mem_singleton] at h1 h2
              rcases h1 with rfl | rfl <;> rcases h2 with rfl | rfl
              · exact absurd rfl hlm
              · exact Or.inl ⟨rfl, rfl⟩
              · exact Or.inr ⟨rfl, rfl⟩
              · exact absurd rfl hlm
            rcases hpair with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
            · exact hmin
            · rw [← hmin]; rw [hval]; ext i j; fin_cases i <;> fin_cases j <;>
                simp [Matrix.mul_apply, Fin.sum_univ_three]; ring
          have h01 := congrArg (fun M : M3 p => M 0 1) hprod0
          rw [hval] at h01; simp [Matrix.mul_apply, Fin.sum_univ_three] at h01
          have hne_c12 : c1 + c2 ≠ 0 := by
            intro h0
            have : c0 + c1 + c2 = c0 := by linear_combination h0
            rw [this] at hroots
            have hcard := congrArg Finset.card hroots
            rw [Finset.card_pair hlm] at hcard; simp at hcard
          rcases h01 with h | h
          · exact hc1_ne h
          · exact hne_c12 (by linear_combination -h)
        subst hc1; simp only [zero_smul, add_zero] at hc
        have hc2 : c2 ≠ 0 := by
          intro h0; subst h0; simp only [zero_smul, add_zero] at hc
          exact M3Type.noConfusion (hasM3Type_unique
            (show HasM3Type (conjAlgEquiv S X) .A from ⟨c0, hc ▸ charpoly_smul_one c0, hc ▸ minpoly_smul_one c0⟩) hXB')
        have hcl_S : Subring.closure ({conjAlgEquiv S X} : Set (M3 p)) = Subring.closure ({matF0 p ^ 2} : Set (M3 p)) := by
          rw [hc, add_comm, subring_closure_affine _ hc2 c0]
        apply Subtype.ext; rw [← hXb]
        have h1 := congrArg (Subring.map (conjAlgEquiv S).symm.toRingHom) hcl_S
        rw [subring_map_closure, subring_map_closure, Set.image_singleton, Set.image_singleton] at h1
        simpa [b0] using h1
      · rintro rfl
        refine (uccgAdj_iff_comm hAv rfl).mpr ?_
        apply (conjAlgEquiv S).injective; simp only [map_mul, AlgEquiv.apply_symm_apply]
        have hm : matF0 p ^ 2 ∈ Subring.closure ({conjAlgEquiv S A} : Set (M3 p)) :=
          hS ▸ (sq (matF0 p) ▸ mul_mem (Subring.subset_closure rfl) (Subring.subset_closure rfl))
        obtain ⟨f, hf⟩ := (mem_subring_closure_iff_aeval _ _).mp hm
        rw [← hf]; exact (commute_aeval_self _ f).symm
    · intro e' he'
      constructor
      · intro hadj
        have hle := le_of_adj_nonderog (Or.inr (Or.inr (Or.inl v.prop))) hadj
        obtain ⟨X, hXe, hXE⟩ := he'
        obtain ⟨c0, c1, c2, hc⟩ := (hmem_v X).mp (hle (hXe ▸ Subring.subset_closure rfl))
        have hXE' := (hasM3Type_conj S X .E).mpr hXE
        have hval : conjAlgEquiv S X = !![c0, c1, 0; 0, c0, 0; 0, 0, c0 + c1 + c2] := by
          rw [hc, hF2]; ext i j; fin_cases i <;> fin_cases j <;> simp [matF0, add_assoc]
        have hch : (conjAlgEquiv S X).charpoly = (Polynomial.X - C c0) ^ 2 * (Polynomial.X - C (c0 + c1 + c2)) := by
          rw [hval, Matrix.charpoly, Matrix.det_fin_three]
          simp [Matrix.charmatrix, -mul_eq_mul_right_iff, -mul_eq_mul_left_iff]; ring
        have hc12 : c1 + c2 = 0 := by
          have h1 := (hasM3Type_invariants hXE').2.1
          dsimp only at h1
          rw [hch] at h1
          by_contra hne
          have hne' : c0 ≠ c0 + c1 + c2 := fun h => hne (by linear_combination -h)
          have hfilt : (Finset.univ.filter fun x : ZMod p => ((Polynomial.X - C c0) ^ 2 * (Polynomial.X - C (c0 + c1 + c2))).IsRoot x) =
              {c0, c0 + c1 + c2} := by ext x; simp [Polynomial.IsRoot, sub_eq_zero]
          rw [hfilt, Finset.card_pair hne'] at h1; omega
        have hc1 : c1 ≠ 0 := by
          intro h0; subst h0; simp only [zero_add] at hc12; subst hc12; simp only [zero_smul, add_zero] at hc
          exact M3Type.noConfusion (hasM3Type_unique
            (show HasM3Type (conjAlgEquiv S X) .A from ⟨c0, hc ▸ charpoly_smul_one c0, hc ▸ minpoly_smul_one c0⟩) hXE')
        have hXeq : conjAlgEquiv S X = c1 • matE01 p + c0 • (1 : M3 p) := by
          rw [hval]; ext i j; fin_cases i <;> fin_cases j <;> simp [matE01]; linear_combination hc12
        have hcl_S : Subring.closure ({conjAlgEquiv S X} : Set (M3 p)) = Subring.closure ({matE01 p} : Set (M3 p)) := by
          rw [hXeq, subring_closure_affine _ hc1 c0]
        apply Subtype.ext; rw [← hXe]
        have h1 := congrArg (Subring.map (conjAlgEquiv S).symm.toRingHom) hcl_S
        rw [subring_map_closure, subring_map_closure, Set.image_singleton, Set.image_singleton] at h1
        simpa [e0] using h1
      · rintro rfl
        refine (uccgAdj_iff_comm hAv rfl).mpr ?_
        apply (conjAlgEquiv S).injective; simp only [map_mul, AlgEquiv.apply_symm_apply]
        have hm : matE01 p ∈ Subring.closure ({conjAlgEquiv S A} : Set (M3 p)) := by
          rw [hS, hE01_eq]; exact sub_mem (Subring.subset_closure rfl)
            (sq (matF0 p) ▸ mul_mem (Subring.subset_closure rfl) (Subring.subset_closure rfl))
        obtain ⟨f, hf⟩ := (mem_subring_closure_iff_aeval _ _).mp hm
        rw [← hf]; exact (commute_aeval_self _ f).symm
  -- Build `ψF`!
  let toPair : VertsOfType p .F → { pair : VertsOfType p .B × VertsOfType p .E // UCCGAdj pair.1.val pair.2.val } :=
    fun v => ⟨(Classical.choose (hF_uniq v), Classical.choose (Classical.choose_spec (hF_uniq v))),
      (Classical.choose_spec (Classical.choose_spec (hF_uniq v))).1⟩
  have htoPair_spec : ∀ v : VertsOfType p .F,
      (∀ b ∈ VertsOfType p .B, UCCGAdj v.val b ↔ b = (toPair v).val.1.val) ∧
      (∀ e ∈ VertsOfType p .E, UCCGAdj v.val e ↔ e = (toPair v).val.2.val) :=
    fun v => (Classical.choose_spec (Classical.choose_spec (hF_uniq v))).2
  have htoPair_bij : Function.Bijective toPair := by
    constructor
    · intro v1 v2 hEq
      set pair := toPair v1
      obtain ⟨S, hSb, hSe⟩ := hBE_canon pair.val.1 pair.val.2 pair.prop
      -- Any `v ∈ V_F` adjacent to both `pair.1` and `pair.2` MUST equal `⟨(conj S).symm (matF0 p)⟩`!
      have hmust : ∀ v : VertsOfType p .F, toPair v = pair →
          v.val.val = Subring.closure ({(conjAlgEquiv S).symm (matF0 p)} : Set (M3 p)) := by
        intro v hv
        have hb : UCCGAdj v.val pair.val.1.val := (htoPair_spec v).1 _ pair.val.1.prop |>.mpr (by rw [hv])
        have he : UCCGAdj v.val pair.val.2.val := (htoPair_spec v).2 _ pair.val.2.prop |>.mpr (by rw [hv])
        have hle_b := le_of_adj_nonderog (Or.inr (Or.inr (Or.inl v.prop))) hb
        have hle_e := le_of_adj_nonderog (Or.inr (Or.inr (Or.inl v.prop))) he
        have hb_in : (conjAlgEquiv S).symm (matF0 p ^ 2) ∈ v.val.val := hle_b (hSb ▸ Subring.subset_closure rfl)
        have he_in : (conjAlgEquiv S).symm (matE01 p) ∈ v.val.val := hle_e (hSe ▸ Subring.subset_closure rfl)
        have hsum_eq : (conjAlgEquiv S).symm (matF0 p) =
            (conjAlgEquiv S).symm (matF0 p ^ 2) + (conjAlgEquiv S).symm (matE01 p) := by
          rw [← map_add]; congr 1; rw [hF2]; ext i j; fin_cases i <;> fin_cases j <;> simp [matF0, matE01]
        have hf_in : (conjAlgEquiv S).symm (matF0 p) ∈ v.val.val := hsum_eq ▸ add_mem hb_in he_in
        have hf_F : HasM3Type ((conjAlgEquiv S).symm (matF0 p)) .F := (hasM3Type_conj S _ .F).mp (by simpa using hF0_F)
        have hadj_vf : UCCGAdj v.val ⟨Subring.closure ({(conjAlgEquiv S).symm (matF0 p)} : Set (M3 p)), ⟨_, rfl⟩⟩ := by
          obtain ⟨A, hAv, _⟩ := v.prop
          refine (uccgAdj_iff_comm hAv rfl).mpr ?_
          obtain ⟨g, hg⟩ := (mem_subring_closure_iff_aeval A _).mp (hAv.symm ▸ hf_in)
          rw [← hg]; exact (commute_aeval_self A g).symm
        by_contra hne
        exact nonderog_no_cross_edges (fun h => hne (congrArg Subtype.val h))
          (Or.inr (Or.inr (Or.inl v.prop))) (Or.inr (Or.inr (Or.inl ⟨_, rfl, hf_F⟩))) hadj_vf
      exact Subtype.ext (Subtype.ext ((hmust v1 rfl).trans (hmust v2 hEq.symm).symm))
    · intro pair
      obtain ⟨S, hSb, hSe⟩ := hBE_canon pair.val.1 pair.val.2 pair.prop
      let v : VertsOfType p .F :=
        ⟨⟨Subring.closure ({(conjAlgEquiv S).symm (matF0 p)} : Set (M3 p)), ⟨_, rfl⟩⟩,
          ⟨_, rfl, (hasM3Type_conj S _ .F).mp (by simpa using hF0_F)⟩⟩
      refine ⟨v, ?_⟩
      have hb : UCCGAdj v.val pair.val.1.val := by
        refine (uccgAdj_iff_comm rfl hSb).mpr ?_
        apply (conjAlgEquiv S).injective; simp only [map_mul, AlgEquiv.apply_symm_apply]
        rw [hF2]; ext i j; fin_cases i <;> fin_cases j <;> simp [matF0, Matrix.mul_apply, Fin.sum_univ_three]
      have he : UCCGAdj v.val pair.val.2.val := by
        refine (uccgAdj_iff_comm rfl hSe).mpr ?_
        apply (conjAlgEquiv S).injective; simp only [map_mul, AlgEquiv.apply_symm_apply]
        ext i j; fin_cases i <;> fin_cases j <;> simp [matF0, matE01, Matrix.mul_apply, Fin.sum_univ_three]
      exact Subtype.ext (Prod.ext (Subtype.ext (((htoPair_spec v).1 _ pair.val.1.prop).mp hb).symm)
        (Subtype.ext (((htoPair_spec v).2 _ pair.val.2.prop).mp he).symm))
  let ψF := Equiv.ofBijective toPair htoPair_bij
  -- Count `|V_(F)| = |BE edges| = |V_(B)| * (p + 1)` using `card_BE_edges`!
  have hF_card : Nat.card (VertsOfType p .F) = (p ^ 2 + p + 1) * p ^ 2 * (p + 1) := by
    rw [Nat.card_congr ψF]
    exact card_BE_edges p
  exact ⟨⟨ψF, htoPair_spec⟩, hF_card⟩

/-- Fast direct proof that `matB0 p` has Type B (avoids expensive `orthoSub` unification in `section5_H`/`section5_C`). -/
private lemma matB0_hasType (p : ℕ) [Fact p.Prime] : HasM3Type (matB0 p) .B := by
  have hch : (matB0 p).charpoly = (Polynomial.X - C 1) * (Polynomial.X - C 0) ^ 2 := by
    rw [Matrix.charpoly, Matrix.det_fin_three]
    simp [matB0, Matrix.charmatrix, -mul_eq_mul_right_iff, -mul_eq_mul_left_iff]; ring
  have hB2 : matB0 p * matB0 p = matB0 p := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [matB0, Matrix.mul_apply, Fin.sum_univ_three]
  have hmin : minpoly (ZMod p) (matB0 p) = (Polynomial.X - C 1) * (Polynomial.X - C 0) := by
    have hmon : ((Polynomial.X - C (1 : ZMod p)) * (Polynomial.X - C 0)).Monic :=
      (Polynomial.monic_X_sub_C 1).mul (Polynomial.monic_X_sub_C 0)
    have haev : aeval (matB0 p) ((Polynomial.X - C (1 : ZMod p)) * (Polynomial.X - C 0)) = 0 := by
      simp [sub_mul, hB2]
    have hdvd : minpoly (ZMod p) (matB0 p) ∣ (Polynomial.X - C 1) * (Polynomial.X - C 0) :=
      minpoly.dvd _ _ haev
    have hdeg_ge : 2 ≤ (minpoly (ZMod p) (matB0 p)).natDegree := by
      by_contra hlt
      have h1 : (minpoly (ZMod p) (matB0 p)).natDegree = 1 := by
        have := minpoly.natDegree_pos (isIntegral_m3 (matB0 p)); omega
      have hlin := Polynomial.eq_X_add_C_of_natDegree_le_one (le_of_eq h1)
      have hlc : (minpoly (ZMod p) (matB0 p)).coeff 1 = 1 := by
        rw [← h1]; exact (minpoly.monic (isIntegral_m3 (matB0 p))).leadingCoeff
      rw [hlc, map_one, one_mul] at hlin
      have h0 := minpoly.aeval (ZMod p) (matB0 p)
      rw [hlin, map_add, aeval_X, aeval_C, Algebra.algebraMap_eq_smul_one] at h0
      have h00 := congrArg (fun M : M3 p => M 0 0) h0
      have h22 := congrArg (fun M : M3 p => M 2 2) h0
      simp [matB0] at h00 h22
      rw [h22, add_zero] at h00; exact one_ne_zero h00
    have hdeg2 : ((Polynomial.X - C (1 : ZMod p)) * (Polynomial.X - C 0)).natDegree = 2 := by compute_degree!
    exact (Polynomial.eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic (isIntegral_m3 (matB0 p))) hmon hdvd
      (by rw [hdeg2]; exact hdeg_ge)).symm
  exact ⟨1, 0, one_ne_zero, hch, hmin⟩

/-- Helper: Section 5(H) Part 1 — each `v ∈ V_(H)` has unique `(B)` neighbor and no `(E)` neighbor. -/
private lemma section5_H_part1 (p : ℕ) [Fact p.Prime] :
    ∀ v ∈ VertsOfType p .H,
      (∃! b : UCCGVert p, VertHasType b .B ∧ UCCGAdj v b) ∧
      (∀ e ∈ VertsOfType p .E, ¬ UCCGAdj v e) := by
  classical
  have hB0_B : HasM3Type (matB0 p) .B := matB0_hasType p
  intro v hv
  obtain ⟨A, hAv, hAH⟩ := hv
  obtain ⟨S, l, q, hqmon, hqdeg, hqirr, hS⟩ := canonical_H hAH
  set M := matH0 l q
  have hqno : ∀ x : ZMod p, ¬ q.IsRoot x := fun x hx => by
    obtain ⟨R, hR⟩ := Polynomial.dvd_iff_isRoot.mpr hx
    rcases hqirr.isUnit_or_isUnit hR with hu | hu
    · exact Polynomial.not_isUnit_X_sub_C x hu
    · have := congrArg Polynomial.natDegree hR
      rw [hqdeg, Polynomial.natDegree_mul (Polynomial.monic_X_sub_C x).ne_zero hu.ne_zero,
          Polynomial.natDegree_X_sub_C, Polynomial.natDegree_eq_zero_of_isUnit hu] at this; omega
  have hq_exp : q = Polynomial.X ^ 2 + C (q.coeff 1) * Polynomial.X + C (q.coeff 0) := by
    ext k
    by_cases hk : k ≤ 2
    · interval_cases k <;> simp [Polynomial.coeff_X, Polynomial.coeff_C, Polynomial.coeff_X_pow]
      · simpa [Polynomial.Monic, Polynomial.leadingCoeff, hqdeg] using hqmon
    · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)]
      simp [Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_C,
            show k ≠ 2 by omega, show 1 ≠ k by omega, show k ≠ 0 by omega]
  have hqM : aeval M q = (q.eval l) • matB0 p := by
    rw [hq_exp]
    simp only [map_add, map_mul, map_pow, aeval_X, aeval_C, Algebra.algebraMap_eq_smul_one,
      smul_mul_assoc, one_mul, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow,
      Polynomial.eval_X, Polynomial.eval_C]
    ext i j; fin_cases i <;> fin_cases j <;>
      (simp [M, matH0, matB0, sq]; try ring)
  have hE00_in : matB0 p ∈ Subring.closure ({M} : Set (M3 p)) := by
    have h1 : (q.eval l)⁻¹ • aeval M q = matB0 p := by rw [hqM, smul_smul, inv_mul_cancel₀ (hqno l), one_smul]
    rw [← h1]; exact smul_mem_subring _ _ (aeval_mem_subring_closure M q)
  let b0 : UCCGVert p := ⟨Subring.closure ({(conjAlgEquiv S).symm (matB0 p)} : Set (M3 p)), ⟨_, rfl⟩⟩
  have hmem_v : ∀ X : M3 p, X ∈ v.val ↔ ∃ a b c : ZMod p,
      conjAlgEquiv S X = !![a, 0, 0; 0, b, -c * q.coeff 0; 0, c, b - c * q.coeff 1] := by
    intro X
    have hv_map : v.val = (Subring.closure ({M} : Set (M3 p))).map (conjAlgEquiv S).symm.toRingHom := by
      rw [← hAv]
      ext Y; simp only [Subring.mem_map]
      constructor
      · intro hY
        refine ⟨conjAlgEquiv S Y, ?_, by simp⟩
        rw [← hS, subring_closure_conj]; exact ⟨Y, hY, rfl⟩
      · rintro ⟨Z, hZ, rfl⟩
        rw [← hS, subring_closure_conj] at hZ
        rcases hZ with ⟨W, hW, hSW⟩
        have : (conjAlgEquiv S).symm Z = W := by rw [← hSW]; simp
        change (conjAlgEquiv S).symm Z ∈ Subring.closure {A}
        rwa [this]
    rw [hv_map]
    constructor
    · rintro ⟨Y, hY, rfl⟩
      let S0 : Subring (M3 p) :=
        { carrier := { T | ∃ a b c : ZMod p, T = !![a, 0, 0; 0, b, -c * q.coeff 0; 0, c, b - c * q.coeff 1] }
          mul_mem' := by
            rintro _ _ ⟨a1, b1, c1, rfl⟩ ⟨a2, b2, c2, rfl⟩
            refine ⟨a1 * a2, b1 * b2 - c1 * c2 * q.coeff 0, b1 * c2 + c1 * b2 - c1 * c2 * q.coeff 1, ?_⟩
            ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three] <;> ring
          one_mem' := ⟨1, 1, 0, by ext i j; fin_cases i <;> fin_cases j <;> simp⟩
          add_mem' := by
            rintro _ _ ⟨a1, b1, c1, rfl⟩ ⟨a2, b2, c2, rfl⟩
            refine ⟨a1 + a2, b1 + b2, c1 + c2, ?_⟩
            ext i j; fin_cases i <;> fin_cases j <;> simp <;> ring
          zero_mem' := ⟨0, 0, 0, by ext i j; fin_cases i <;> fin_cases j <;> simp⟩
          neg_mem' := by
            rintro _ ⟨a1, b1, c1, rfl⟩
            refine ⟨-a1, -b1, -c1, ?_⟩
            ext i j; fin_cases i <;> fin_cases j <;> (simp; try ring) }
      have hle : Subring.closure ({M} : Set (M3 p)) ≤ S0 :=
        Subring.closure_le.mpr (Set.singleton_subset_iff.mpr ⟨l, 0, 1, by
          ext i j; fin_cases i <;> fin_cases j <;> simp [M, matH0]⟩)
      have hY' : Y ∈ S0 := hle hY
      change ∃ a b c, Y = !![a, 0, 0; 0, b, -c * q.coeff 0; 0, c, b - c * q.coeff 1] at hY'
      simpa using hY'
    · rintro ⟨a, b, c, hEq⟩
      refine ⟨conjAlgEquiv S X, ?_, by simp⟩
      have hEq' : conjAlgEquiv S X = (a - b - c * l) • matB0 p + b • (1 : M3 p) + c • M := by
        rw [hEq]; ext i j; fin_cases i <;> fin_cases j <;> (simp [M, matH0, matB0]; try ring)
      rw [hEq']
      exact add_mem (add_mem (smul_mem_subring _ _ hE00_in) (smul_one_mem_subring _ b))
        (smul_mem_subring _ c (Subring.subset_closure rfl))
  have hc0_of_not_H : ∀ {X : M3 p}, X ∈ v.val → ¬ HasM3Type X .H →
      ∃ a b : ZMod p, conjAlgEquiv S X = (a - b) • matB0 p + b • (1 : M3 p) := by
    intro X hXv hnotH
    obtain ⟨a, b, c, hc⟩ := (hmem_v X).mp hXv
    have hc0 : c = 0 := by
      by_contra hne
      let q' : (ZMod p)[X] := Polynomial.X ^ 2 + C (c * q.coeff 1 - 2 * b) * Polynomial.X + C (b ^ 2 - b * c * q.coeff 1 + c ^ 2 * q.coeff 0)
      have hq'deg : q'.natDegree = 2 := by dsimp [q']; compute_degree!
      have hq'mon : q'.Monic := by
        rw [Polynomial.Monic, Polynomial.leadingCoeff, hq'deg]
        simp only [q', Polynomial.coeff_add, Polynomial.coeff_X_pow, Polynomial.coeff_C_mul_X, Polynomial.coeff_C]
        norm_num
      have hq'irr : Irreducible q' := by
        refine irred_of_no_root_deg_le_three q' (by omega) (by omega) fun x hx => ?_
        have hval : q.eval (c⁻¹ * (x - b)) = 0 := by
          rw [hq_exp]
          simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C]
          simp only [Polynomial.IsRoot, q', Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C] at hx
          have hci : c * c⁻¹ = 1 := mul_inv_cancel₀ hne
          have hmul : c ^ 2 * ((c⁻¹ * (x - b)) ^ 2 + q.coeff 1 * (c⁻¹ * (x - b)) + q.coeff 0) =
              x ^ 2 + (c * q.coeff 1 - 2 * b) * x + (b ^ 2 - b * c * q.coeff 1 + c ^ 2 * q.coeff 0) := by
            calc c ^ 2 * ((c⁻¹ * (x - b)) ^ 2 + q.coeff 1 * (c⁻¹ * (x - b)) + q.coeff 0)
                = (c * c⁻¹) ^ 2 * (x - b) ^ 2 + c * (c * c⁻¹) * q.coeff 1 * (x - b) + c ^ 2 * q.coeff 0 := by ring
              _ = (x - b) ^ 2 + c * q.coeff 1 * (x - b) + c ^ 2 * q.coeff 0 := by rw [hci]; ring
              _ = x ^ 2 + (c * q.coeff 1 - 2 * b) * x + (b ^ 2 - b * c * q.coeff 1 + c ^ 2 * q.coeff 0) := by ring
          have h0' : c ^ 2 * ((c⁻¹ * (x - b)) ^ 2 + q.coeff 1 * (c⁻¹ * (x - b)) + q.coeff 0) = 0 := by rw [hmul, hx]
          exact (mul_eq_zero.mp h0').resolve_left (pow_ne_zero 2 hne)
        exact hqno (c⁻¹ * (x - b)) hval
      have hch : (conjAlgEquiv S X).charpoly = (Polynomial.X - C a) * q' := by
        rw [hc, Matrix.charpoly, Matrix.det_fin_three]
        simp [q', Matrix.charmatrix, map_ofNat, -mul_eq_mul_right_iff, -mul_eq_mul_left_iff]; ring
      obtain ⟨tX, htX⟩ := exists_hasM3Type (conjAlgEquiv S X)
      have hinv := hasM3Type_invariants htX
      have h1 : (Finset.univ.filter fun x : ZMod p => (conjAlgEquiv S X).charpoly.IsRoot x).card = 1 := by
        rw [hch]
        have hq'no : ∀ x : ZMod p, ¬ q'.IsRoot x := fun x hx => by
          obtain ⟨R, hR⟩ := Polynomial.dvd_iff_isRoot.mpr hx
          rcases hq'irr.isUnit_or_isUnit hR with hu | hu
          · exact Polynomial.not_isUnit_X_sub_C x hu
          · have := congrArg Polynomial.natDegree hR
            rw [hq'deg, Polynomial.natDegree_mul (Polynomial.monic_X_sub_C x).ne_zero hu.ne_zero,
                Polynomial.natDegree_X_sub_C, Polynomial.natDegree_eq_zero_of_isUnit hu] at this; omega
        have hfilt : (Finset.univ.filter fun x : ZMod p => ((Polynomial.X - C a) * q').IsRoot x) = {a} := by
          ext x; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton,
            Polynomial.IsRoot, Polynomial.eval_mul, mul_eq_zero, Polynomial.eval_sub, Polynomial.eval_X,
            Polynomial.eval_C, sub_eq_zero]
          exact ⟨fun h => h.resolve_right (hq'no x), Or.inl⟩
        rw [hfilt, Finset.card_singleton]
      have hnot_cube : ∀ r : ZMod p, (conjAlgEquiv S X).charpoly ≠ (Polynomial.X - C r) ^ 3 := fun r hr => by
        have hQdvd : q' ∣ (Polynomial.X - C r) ^ 3 := ⟨Polynomial.X - C a, by rw [← hr, hch, mul_comm]⟩
        have hQdvd1 : q' ∣ Polynomial.X - C r := hq'irr.prime.dvd_of_dvd_pow hQdvd
        have := Polynomial.natDegree_le_of_dvd hQdvd1 (Polynomial.monic_X_sub_C r).ne_zero
        rw [Polynomial.natDegree_X_sub_C] at this; omega
      have htH : tX = .H := by
        cases tX with
        | H => rfl
        | A => exfalso; rcases htX with ⟨r, hcr, _⟩; exact hnot_cube r hcr
        | E => exfalso; rcases htX with ⟨r, hcr, _⟩; exact hnot_cube r hcr
        | D => exfalso; rcases htX with ⟨r, hcr, _⟩; exact hnot_cube r hcr
        | B => exfalso; have h1' := hinv.2.1; dsimp only at h1'; rw [h1] at h1'; omega
        | C => exfalso; have h1' := hinv.2.1; dsimp only at h1'; rw [h1] at h1'; omega
        | F => exfalso; have h1' := hinv.2.1; dsimp only at h1'; rw [h1] at h1'; omega
        | G => exfalso; have h1' := hinv.2.1; dsimp only at h1'; rw [h1] at h1'; omega
      exact hnotH ((hasM3Type_conj S X .H).mp (htH ▸ htX))
    subst hc0
    refine ⟨a, b, ?_⟩
    rw [hc]; ext i j; fin_cases i <;> fin_cases j <;> simp [matB0]
  constructor
  · refine ⟨b0, ⟨⟨_, rfl, (hasM3Type_conj S _ .B).mp (by simpa using hB0_B)⟩, ?_⟩, ?_⟩
    · refine (uccgAdj_iff_comm hAv rfl).mpr ?_
      apply (conjAlgEquiv S).injective; simp only [map_mul, AlgEquiv.apply_symm_apply, hS]
      ext i j; fin_cases i <;> fin_cases j <;> simp [M, matH0, matB0, Matrix.mul_apply, Fin.sum_univ_three]
    · rintro b' ⟨hb'B, hadj⟩
      have hle := le_of_adj_nonderog (Or.inr (Or.inr (Or.inr (Or.inr ⟨A, hAv, hAH⟩)))) hadj
      obtain ⟨X, hXb, hXB⟩ := hb'B
      obtain ⟨a, b, hab⟩ := hc0_of_not_H (hle (hXb ▸ Subring.subset_closure rfl))
        (fun hH => M3Type.noConfusion (hasM3Type_unique hXB hH))
      have hab_ne : a - b ≠ 0 := by
        intro h0; rw [h0, zero_smul, zero_add] at hab
        exact M3Type.noConfusion (hasM3Type_unique
          (show HasM3Type (conjAlgEquiv S X) .A from ⟨b, hab ▸ charpoly_smul_one b, hab ▸ minpoly_smul_one b⟩)
          ((hasM3Type_conj S X .B).mpr hXB))
      have hcl_S : Subring.closure ({conjAlgEquiv S X} : Set (M3 p)) = Subring.closure ({matB0 p} : Set (M3 p)) := by
        rw [hab, subring_closure_affine _ hab_ne b]
      apply Subtype.ext; rw [← hXb]
      have h1 := congrArg (Subring.map (conjAlgEquiv S).symm.toRingHom) hcl_S
      rw [subring_map_closure, subring_map_closure, Set.image_singleton, Set.image_singleton] at h1
      simpa [b0] using h1
  · intro e he hadj
    have hle := le_of_adj_nonderog (Or.inr (Or.inr (Or.inr (Or.inr ⟨A, hAv, hAH⟩)))) hadj
    obtain ⟨X, hXe, hXE⟩ := he
    obtain ⟨a, b, hab⟩ := hc0_of_not_H (hle (hXe ▸ Subring.subset_closure rfl))
      (fun hH => M3Type.noConfusion (hasM3Type_unique hXE hH))
    by_cases hab0 : a - b = 0
    · rw [hab0, zero_smul, zero_add] at hab
      exact M3Type.noConfusion (hasM3Type_unique
        (show HasM3Type (conjAlgEquiv S X) .A from ⟨b, hab ▸ charpoly_smul_one b, hab ▸ minpoly_smul_one b⟩)
        ((hasM3Type_conj S X .E).mpr hXE))
    · have hcl_S : Subring.closure ({conjAlgEquiv S X} : Set (M3 p)) = Subring.closure ({matB0 p} : Set (M3 p)) := by
        rw [hab, subring_closure_affine _ hab0 b]
      have hXB := (same_type_of_subring_eq hcl_S .B).mpr hB0_B
      exact M3Type.noConfusion (hasM3Type_unique hXB ((hasM3Type_conj S X .E).mpr hXE))

/-- Helper: Section 5(H) — each `v ∈ V_(H)` has unique `(B)` neighbor & no `(E)` neighbor;
    each `b ∈ V_(B)` has `p*(p-1)/2` neighbors in `V_(H)`; and `|V_(H)| = (p^3 - 1) * p^3 / 2`! -/
private lemma section5_H (p : ℕ) [Fact p.Prime] :
    (∀ v ∈ VertsOfType p .H,
      (∃! b : UCCGVert p, VertHasType b .B ∧ UCCGAdj v b) ∧
      (∀ e ∈ VertsOfType p .E, ¬ UCCGAdj v e)) ∧
    (∀ b ∈ VertsOfType p .B,
      Nat.card { h : UCCGVert p // VertHasType h .H ∧ UCCGAdj b h } = p * (p - 1) / 2) ∧
    Nat.card (VertsOfType p .H) = (p ^ 3 - 1) * p ^ 3 / 2 := by
  classical
  have : Fintype (UCCGVert p) := Fintype.ofFinite _
  have hp2 : 2 ≤ p := (Fact.out : p.Prime).two_le
  have hH_part1 := section5_H_part1 p
  -- Part 2: Every `b ∈ V_(B)` has `p*(p-1)/2` neighbors in `V_(H)`!
  have hH_part2 : ∀ b ∈ VertsOfType p .B,
      Nat.card { h : UCCGVert p // VertHasType h .H ∧ UCCGAdj b h } = p * (p - 1) / 2 := by
    intro b hb
    obtain ⟨A, hAb, hAB⟩ := hb
    obtain ⟨S, hS⟩ := canonical_B hAB
    let b0 : UCCGVert p := ⟨Subring.closure ({matB0 p} : Set (M3 p)), ⟨_, rfl⟩⟩
    have heq_card : Nat.card { h : UCCGVert p // VertHasType h .H ∧ UCCGAdj b h } =
        Nat.card { h : UCCGVert p // VertHasType h .H ∧ UCCGAdj b0 h } := by
      refine Nat.card_congr ?_
      let mapV (d : UCCGVert p) : UCCGVert p :=
        ⟨d.val.map (conjAlgEquiv S).toRingHom, by
          obtain ⟨M, hMd⟩ := d.prop
          exact ⟨conjAlgEquiv S M, by rw [hMd, subring_map_closure, Set.image_singleton]; rfl⟩⟩
      let invV (d : UCCGVert p) : UCCGVert p :=
        ⟨d.val.map (conjAlgEquiv S).symm.toRingHom, by
          obtain ⟨M, hMd⟩ := d.prop
          exact ⟨(conjAlgEquiv S).symm M, by rw [hMd, subring_map_closure, Set.image_singleton]; rfl⟩⟩
      have hmap_type : ∀ d, VertHasType (mapV d) .H ↔ VertHasType d .H := fun d => by
        obtain ⟨M, hMd⟩ := d.prop
        have hM1 : conjAlgEquiv S M ∈ SingleGens (mapV d) := by
          show Subring.closure ({conjAlgEquiv S M} : Set (M3 p)) = d.val.map (conjAlgEquiv S).toRingHom
          rw [hMd, subring_map_closure, Set.image_singleton]; rfl
        constructor
        · intro h; exact ⟨M, hMd.symm, (hasM3Type_conj S M .H).mp ((vertHasType_iff_all.mp h) _ hM1)⟩
        · intro h; exact ⟨conjAlgEquiv S M, hM1, (hasM3Type_conj S M .H).mpr ((vertHasType_iff_all.mp h) M hMd.symm)⟩
      have hmap_adj : ∀ d, UCCGAdj b0 (mapV d) ↔ UCCGAdj b d := fun d => by
        obtain ⟨M, hMd⟩ := d.prop
        have hM1 : conjAlgEquiv S M ∈ SingleGens (mapV d) := by
          show Subring.closure ({conjAlgEquiv S M} : Set (M3 p)) = d.val.map (conjAlgEquiv S).toRingHom
          rw [hMd, subring_map_closure, Set.image_singleton]; rfl
        rw [uccgAdj_iff_comm hS hM1, uccgAdj_iff_comm hAb hMd.symm, ← map_mul, ← map_mul]
        exact (conjAlgEquiv S).injective.eq_iff
      refine Equiv.ofBijective (fun d => ⟨mapV d.val, (hmap_type d.val).mpr d.prop.1, (hmap_adj d.val).mpr d.prop.2⟩) ⟨?_, ?_⟩
      · intro d1 d2 h
        apply Subtype.ext; apply Subtype.ext
        have h1 := congrArg (fun z => z.val.val.map (conjAlgEquiv S).symm.toRingHom) h
        have hcancel : ∀ T : Subring (M3 p), (T.map (conjAlgEquiv S).toRingHom).map (conjAlgEquiv S).symm.toRingHom = T := fun T => by
          ext X; simp only [Subring.mem_map]; constructor
          · rintro ⟨_, ⟨Y, hY, rfl⟩, hEq⟩
            have hYX : Y = X := by simpa using hEq
            rwa [← hYX]
          · intro hX; exact ⟨conjAlgEquiv S X, ⟨X, hX, rfl⟩, by simp⟩
        dsimp only [mapV] at h1
        rw [hcancel, hcancel] at h1
        exact h1
      · intro d
        have hcancel : mapV (invV d.val) = d.val := by
          apply Subtype.ext; ext X; simp only [mapV, invV, Subring.mem_map]; constructor
          · rintro ⟨_, ⟨Y, hY, rfl⟩, hEq⟩
            have hYX : Y = X := by simpa using hEq
            rwa [← hYX]
          · intro hX; exact ⟨(conjAlgEquiv S).symm X, ⟨X, hX, rfl⟩, by simp⟩
        refine ⟨⟨invV d.val, (hmap_type _).mp (hcancel.symm ▸ d.prop.1), (hmap_adj _).mp (hcancel.symm ▸ d.prop.2)⟩,
          Subtype.ext hcancel⟩
    rw [heq_card]
    -- Double-count the set `MH := {M : M3 p | HasM3Type M .H ∧ matB0 p * M = M * matB0 p}`!
    -- On one hand, `|MH| = |{h ∈ V_H | b0 ~ h}| * gen_H = |{h ∈ V_H | b0 ~ h}| * (p^2 * (p - 1))`.
    -- On the other hand, `M ∈ MH` iff `M = !![a, 0, 0; 0, d, e; 0, f, g]` where `X^2 - (d+g)X + (dg-ef)` is irreducible!
    -- Such `(a, d, e, f, g)` has `e ≠ 0`, and bijects with `(a, d, e, (s, t))` where `X^2 + sX + t` is irreducible (`p(p-1)/2` choices)!
    let MH := Finset.univ.filter fun M : M3 p => HasM3Type M .H ∧ matB0 p * M = M * matB0 p
    let HN := { h : UCCGVert p // VertHasType h .H ∧ UCCGAdj b0 h }
    let : Fintype HN := Fintype.ofFinite _
    have hMH_sum : MH.card = Fintype.card HN * (p ^ 2 * (p - 1)) := by
      have hpart : MH = Finset.univ.biUnion (fun h : HN => Finset.univ.filter fun M : M3 p => M ∈ SingleGens h.val) := by
        ext M; simp only [MH, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_biUnion]
        constructor
        · rintro ⟨hMH, hcomm⟩
          let hV : UCCGVert p := ⟨Subring.closure ({M} : Set (M3 p)), ⟨M, rfl⟩⟩
          exact ⟨⟨hV, ⟨M, rfl, hMH⟩, (uccgAdj_iff_comm rfl rfl).mpr hcomm⟩, rfl⟩
        · rintro ⟨h, hM⟩
          exact ⟨(vertHasType_iff_all.mp h.prop.1) M hM, (uccgAdj_iff_comm rfl hM).mp h.prop.2⟩
      rw [hpart, Finset.card_biUnion]
      · have hfib : ∀ h : HN, (Finset.univ.filter fun M : M3 p => M ∈ SingleGens h.val).card = p ^ 2 * (p - 1) := fun h => by
          have := card_singleGens_of_type .H h.val h.prop.1
          rwa [Nat.card_eq_fintype_card, Fintype.card_subtype] at this
        simp_rw [hfib]; rw [Finset.sum_const, Finset.card_univ, smul_eq_mul]
      · intro h1 _ h2 _ hne; change Disjoint _ _; rw [Finset.disjoint_left]
        intro M hm1 hm2
        exact hne (Subtype.ext (Subtype.ext ((Finset.mem_filter.mp hm1).2.symm.trans (Finset.mem_filter.mp hm2).2)))
    -- Count irreducible monic quadratics `Iq := {(s, t) : ZMod p × ZMod p | ∀ x, x^2 + s*x + t ≠ 0}`!
    let Iq := Finset.univ.filter fun st : ZMod p × ZMod p => ∀ x : ZMod p, x ^ 2 + st.1 * x + st.2 ≠ 0
    have hIq_card : Iq.card = p * (p - 1) / 2 := by
      let red := Finset.univ.filter fun st : ZMod p × ZMod p => ∃ x : ZMod p, x ^ 2 + st.1 * x + st.2 = 0
      have htot : Iq.card + red.card = p ^ 2 := by
        have h1 := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (ZMod p × ZMod p)))
          (fun st => ∀ x : ZMod p, x ^ 2 + st.1 * x + st.2 ≠ 0)
        have h2 : (Finset.univ.filter fun st : ZMod p × ZMod p => ¬ ∀ x : ZMod p, x ^ 2 + st.1 * x + st.2 ≠ 0) = red := by
          ext st; simp [red]
        rw [h2, Finset.card_univ, Fintype.card_prod, ZMod.card] at h1; rw [sq]; exact h1
      let redD := Finset.univ.image fun a : ZMod p => (-2 * a, a ^ 2)
      let redO := (Finset.univ.filter fun ab : ZMod p × ZMod p => ab.1 ≠ ab.2).image fun ab => (-(ab.1 + ab.2), ab.1 * ab.2)
      have hred_eq : red = redD ∪ redO := by
        ext ⟨s, t⟩
        simp only [red, redD, redO, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
        constructor
        · rintro ⟨a, ha⟩
          let b := -s - a
          have hab : -(a + b) = s ∧ a * b = t := ⟨by dsimp [b]; ring, by dsimp [b]; linear_combination -ha⟩
          by_cases heq : a = b
          · left; refine ⟨a, Prod.ext (by rw [← hab.1, ← heq]; ring) (by rw [← hab.2, ← heq, sq])⟩
          · right; exact ⟨(a, b), heq, Prod.ext hab.1 hab.2⟩
        · rintro (⟨a, h⟩ | ⟨⟨a, b⟩, _, h⟩)
          · rcases Prod.mk.inj h with ⟨rfl, rfl⟩; exact ⟨a, by ring⟩
          · rcases Prod.mk.inj h with ⟨rfl, rfl⟩; exact ⟨a, by ring⟩
      have hdisjDO : Disjoint redD redO := by
        rw [Finset.disjoint_left]; rintro ⟨s, t⟩ h1 h2
        obtain ⟨a, _, ha⟩ := Finset.mem_image.mp h1
        obtain ⟨⟨u, v⟩, huv, h2'⟩ := Finset.mem_image.mp h2
        have hne : u ≠ v := (Finset.mem_filter.mp huv).2
        rcases Prod.mk.inj (ha.trans h2'.symm) with ⟨hsum, hprod⟩
        have hsq0 : (u - v) ^ 2 = 0 := by
          have : (u + v) ^ 2 = 4 * (u * v) := by
            calc (u + v) ^ 2 = (-(u + v)) ^ 2 := by ring
              _ = (-2 * a) ^ 2 := by rw [← hsum]
              _ = 4 * a ^ 2 := by ring
              _ = 4 * (u * v) := by rw [hprod]
          linear_combination this
        exact hne (sub_eq_zero.mp (pow_eq_zero hsq0))
      have hcardD : redD.card = p := by
        rw [Finset.card_image_of_injective _ (fun a b h => by
          rcases Prod.mk.inj h with ⟨h1, h2⟩
          by_cases h2z : (2 : ZMod p) = 0
          · have hsq : (a - b) ^ 2 = 0 := by
              have : (a - b) ^ 2 = a ^ 2 - (2 : ZMod p) * a * b + b ^ 2 := by ring
              rw [this, h2z, zero_mul, zero_mul, sub_zero, h2]
              have : b ^ 2 + b ^ 2 = (2 : ZMod p) * b ^ 2 := by ring
              rw [this, h2z, zero_mul]
            exact sub_eq_zero.mp (pow_eq_zero hsq)
          · have : (2 : ZMod p) * (a - b) = 0 := by linear_combination -h1
            exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_left h2z)), Finset.card_univ, ZMod.card]
      have hcardO : 2 * redO.card = p * (p - 1) := by
        let O := Finset.univ.filter fun ab : ZMod p × ZMod p => ab.1 ≠ ab.2
        have hOcard : O.card = p * (p - 1) := by
          have h1 : O.card + (Finset.univ.filter fun ab : ZMod p × ZMod p => ab.1 = ab.2).card = p * p := by
            have h := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (ZMod p × ZMod p))) (fun ab => ab.1 = ab.2)
            rw [Finset.card_univ, Fintype.card_prod, ZMod.card] at h; rw [add_comm]; exact h
          have hdiag : (Finset.univ.filter fun ab : ZMod p × ZMod p => ab.1 = ab.2).card = p := by
            have hEq : (Finset.univ.filter fun ab : ZMod p × ZMod p => ab.1 = ab.2) =
                Finset.univ.image fun a : ZMod p => (a, a) := by ext ⟨a, b⟩; simp [eq_comm]
            rw [hEq, Finset.card_image_of_injective _ (fun a b h => (Prod.mk.inj h).1), Finset.card_univ, ZMod.card]
          rw [hdiag] at h1
          have : p * p = p * (p - 1) + p := by zify [show 1 ≤ p by omega]; ring
          omega
        have hfib2 : ∀ st ∈ redO, (O.filter fun ab => (-(ab.1 + ab.2), ab.1 * ab.2) = st).card = 2 := by
          intro st hst
          obtain ⟨⟨u, v⟩, huv, rfl⟩ := Finset.mem_image.mp hst
          have hne : u ≠ v := (Finset.mem_filter.mp huv).2
          have hEq : (O.filter fun ab => (-(ab.1 + ab.2), ab.1 * ab.2) = (-(u + v), u * v)) = {(u, v), (v, u)} := by
            ext ⟨a, b⟩
            simp only [O, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq]
            constructor
            · rintro ⟨_, hsum, hprod⟩
              have hfac : (a - u) * (a - v) = 0 := by
                have h1 : a + b = u + v := by linear_combination -hsum
                have hb : b = u + v - a := by linear_combination h1
                rw [hb] at hprod; linear_combination -hprod
              rcases mul_eq_zero.mp hfac with hau | hav
              · left; have hu : a = u := sub_eq_zero.mp hau
                exact ⟨hu, by linear_combination -hsum - hu⟩
              · right; have hv : a = v := sub_eq_zero.mp hav
                exact ⟨hv, by linear_combination -hsum - hv⟩
            · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
              · exact ⟨hne, rfl, rfl⟩
              · exact ⟨hne.symm, by ring, by ring⟩
          rw [hEq, Finset.card_pair (fun h => hne (Prod.mk.inj h).1)]
        have hsum : O.card = ∑ st ∈ redO, (O.filter fun ab => (-(ab.1 + ab.2), ab.1 * ab.2) = st).card := by
          rw [← Finset.card_biUnion]
          · congr 1; ext ab; simp only [Finset.mem_biUnion, Finset.mem_filter, redO, Finset.mem_image]
            constructor
            · intro hab; exact ⟨(-(ab.1 + ab.2), ab.1 * ab.2), ⟨ab, Finset.mem_filter.mp hab, rfl⟩, hab, rfl⟩
            · rintro ⟨_, _, hab, _⟩; exact hab
          · intro s1 _ s2 _ hne; change Disjoint _ _; rw [Finset.disjoint_left]
            intro ab h1 h2; exact hne (((Finset.mem_filter.mp h1).2).symm.trans (Finset.mem_filter.mp h2).2)
        rw [Finset.sum_congr rfl hfib2, Finset.sum_const, smul_eq_mul, mul_comm] at hsum
        rw [← hsum, hOcard]
      rw [hred_eq, Finset.card_union_of_disjoint hdisjDO, hcardD] at htot
      have h2Iq : 2 * Iq.card = p * (p - 1) := by
        have : 2 * p ^ 2 = 2 * p + p * (p - 1) + p * (p - 1) := by zify [show 1 ≤ p by omega]; ring
        omega
      omega
    -- Bijection between `MH` and `ZMod p × ZMod p × {e : ZMod p // e ≠ 0} × Iq`!
    let ParamH := ZMod p × ZMod p × { e : ZMod p // e ≠ 0 } × { st : ZMod p × ZMod p // st ∈ Iq }
    let toMH_mat (x : ParamH) : M3 p :=
      let a := x.1; let d := x.2.1; let e := x.2.2.1.val; let s := x.2.2.2.val.1; let t := x.2.2.2.val.2
      let g := -s - d; let f := e⁻¹ * (d * g - t)
      !![a, 0, 0; 0, d, e; 0, f, g]
    have htoMH_H : ∀ x : ParamH, HasM3Type (toMH_mat x) .H := fun x => by
      have he : x.2.2.1.val ≠ 0 := x.2.2.1.prop
      have hst : ∀ z : ZMod p, z ^ 2 + x.2.2.2.val.1 * z + x.2.2.2.val.2 ≠ 0 := (Finset.mem_filter.mp x.2.2.2.prop).2
      let q : (ZMod p)[X] := Polynomial.X ^ 2 + C x.2.2.2.val.1 * Polynomial.X + C x.2.2.2.val.2
      have hqdeg : q.natDegree = 2 := by dsimp [q]; compute_degree!
      have hqmon : q.Monic := by
        rw [Polynomial.Monic, Polynomial.leadingCoeff, hqdeg]
        simp only [q, Polynomial.coeff_add, Polynomial.coeff_X_pow, Polynomial.coeff_C_mul_X, Polynomial.coeff_C]
        norm_num
      have hqirr : Irreducible q := irred_of_no_root_deg_le_three q (by omega) (by omega) (fun z hz => hst z (by simpa [Polynomial.IsRoot, q] using hz))
      have hch : (toMH_mat x).charpoly = (Polynomial.X - C x.1) * q := by
        dsimp only [toMH_mat]
        rw [Matrix.charpoly, Matrix.det_fin_three]
        simp [q, Matrix.charmatrix, -mul_eq_mul_right_iff, -mul_eq_mul_left_iff]
        have h1 : C x.2.2.1.val * C (x.2.2.1.val⁻¹) = 1 := by rw [← map_mul, mul_inv_cancel₀ he, map_one]
        have h2 : (Polynomial.X - C x.1) * (C x.2.2.1.val * C (x.2.2.1.val⁻¹) * (C x.2.1 * (-C x.2.2.2.val.1 - C x.2.1) - C x.2.2.2.val.2)) =
            (Polynomial.X - C x.1) * (C x.2.1 * (-C x.2.2.2.val.1 - C x.2.1) - C x.2.2.2.val.2) := by rw [h1, one_mul]
        linear_combination -h2
      refine ⟨x.1, q, hqmon, hqdeg, hqirr, hch, ?_⟩
      set M0 : M3 p := toMH_mat x
      have ha_r : (minpoly (ZMod p) M0).IsRoot x.1 := (isRoot_minpoly_iff_charpoly M0 x.1).mpr (by rw [Polynomial.IsRoot, hch]; simp)
      obtain ⟨M1, hM1⟩ := Polynomial.dvd_iff_isRoot.mpr ha_r
      obtain ⟨R, hR⟩ := minpoly.dvd (ZMod p) M0 (Matrix.aeval_self_charpoly M0)
      rw [hch, hM1] at hR
      have hM1dvd : M1 ∣ q := ⟨R, mul_left_cancel₀ (Polynomial.monic_X_sub_C x.1).ne_zero (by rw [hR, mul_assoc])⟩
      obtain ⟨R2, hR2⟩ := hM1dvd
      rcases hqirr.isUnit_or_isUnit hR2 with hu | hu
      · exfalso
        have hmdeg1 : (minpoly (ZMod p) M0).natDegree = 1 := by
          rw [hM1, Polynomial.natDegree_mul (Polynomial.monic_X_sub_C x.1).ne_zero hu.ne_zero,
              Polynomial.natDegree_X_sub_C, Polynomial.natDegree_eq_zero_of_isUnit hu]
        have hmeq : minpoly (ZMod p) M0 = Polynomial.X - C x.1 :=
          Polynomial.eq_of_monic_of_dvd_of_natDegree_le
            (Polynomial.monic_X_sub_C x.1) (minpoly.monic (isIntegral_m3 M0))
            (Polynomial.dvd_iff_isRoot.mpr ha_r) (by rw [Polynomial.natDegree_X_sub_C]; omega)
        have h0 := minpoly.aeval (ZMod p) M0
        rw [hmeq, map_sub, aeval_X, aeval_C, Algebra.algebraMap_eq_smul_one, sub_eq_zero] at h0
        have := congrArg (fun T : M3 p => T 1 2) h0; simp [M0, toMH_mat] at this; exact he this
      · have hM1ne : M1 ≠ 0 := fun h => by rw [h, zero_mul] at hR2; exact hqmon.ne_zero hR2
        have hM1deg : M1.natDegree = 2 := by
          have := congrArg Polynomial.natDegree hR2
          rw [hqdeg, Polynomial.natDegree_mul hM1ne hu.ne_zero, Polynomial.natDegree_eq_zero_of_isUnit hu] at this; omega
        have hmdeg3 : (minpoly (ZMod p) M0).natDegree = 3 := by
          rw [hM1, Polynomial.natDegree_mul (Polynomial.monic_X_sub_C x.1).ne_zero hM1ne,
              Polynomial.natDegree_X_sub_C, hM1deg]
        exact (Polynomial.eq_of_monic_of_dvd_of_natDegree_le
          (minpoly.monic (isIntegral_m3 M0))
          (Matrix.charpoly_monic M0) (minpoly.dvd (ZMod p) M0 (Matrix.aeval_self_charpoly M0))
          (by rw [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]; omega)).symm
    let toMH : ParamH → { M : M3 p // M ∈ MH } := fun x =>
      ⟨toMH_mat x, Finset.mem_filter.mpr ⟨Finset.mem_univ _, htoMH_H x, by
        ext i j; fin_cases i <;> fin_cases j <;> simp [toMH_mat, matB0, Matrix.mul_apply, Fin.sum_univ_three]⟩⟩
    have hMH_bij : ParamH ≃ { M : M3 p // M ∈ MH } := Equiv.ofBijective toMH ⟨by
      intro x y h
      have h00 := congrArg (fun z => z.val 0 0) h
      have h11 := congrArg (fun z => z.val 1 1) h
      have h12 := congrArg (fun z => z.val 1 2) h
      have h21 := congrArg (fun z => z.val 2 1) h
      have h22 := congrArg (fun z => z.val 2 2) h
      simp [toMH, toMH_mat] at h00 h11 h12 h21 h22
      have hs : x.2.2.2.val.1 = y.2.2.2.val.1 := by linear_combination -h22 - h11
      have ht : x.2.2.2.val.2 = y.2.2.2.val.2 := by
        have hmul := congrArg (x.2.2.1.val * ·) h21
        rw [← mul_assoc, mul_inv_cancel₀ x.2.2.1.prop, one_mul, h12, ← mul_assoc, mul_inv_cancel₀ y.2.2.1.prop, one_mul,
            h11, hs] at hmul
        linear_combination -hmul
      exact Prod.ext h00 (Prod.ext h11 (Prod.ext (Subtype.ext h12) (Subtype.ext (Prod.ext hs ht)))), by
      intro M
      obtain ⟨hMH, hcomm⟩ := (Finset.mem_filter.mp M.prop).2
      have h01 : M.val 0 1 = 0 := by have := congrArg (fun T : M3 p => T 0 1) hcomm; simp [matB0, Matrix.mul_apply, Fin.sum_univ_three] at this; exact this
      have h02 : M.val 0 2 = 0 := by have := congrArg (fun T : M3 p => T 0 2) hcomm; simp [matB0, Matrix.mul_apply, Fin.sum_univ_three] at this; exact this
      have h10 : M.val 1 0 = 0 := by have := congrArg (fun T : M3 p => T 1 0) hcomm; simp [matB0, Matrix.mul_apply, Fin.sum_univ_three] at this; exact this.symm
      have h20 : M.val 2 0 = 0 := by have := congrArg (fun T : M3 p => T 2 0) hcomm; simp [matB0, Matrix.mul_apply, Fin.sum_univ_three] at this; exact this.symm
      set s := -(M.val 1 1 + M.val 2 2)
      set t := M.val 1 1 * M.val 2 2 - M.val 1 2 * M.val 2 1
      have hch : M.val.charpoly = (Polynomial.X - C (M.val 0 0)) * (Polynomial.X ^ 2 + C s * Polynomial.X + C t) := by
        rw [Matrix.charpoly, Matrix.det_fin_three]
        simp [s, t, Matrix.charmatrix, h01, h02, h10, h20, -mul_eq_mul_right_iff, -mul_eq_mul_left_iff]; ring
      have hno : ∀ z : ZMod p, z ^ 2 + s * z + t ≠ 0 := by
        intro z hz
        rcases hMH with ⟨l, q, hqmon, hqdeg, hqirr, hchl, _⟩
        have hqno : ∀ x : ZMod p, ¬ q.IsRoot x := fun x hx => by
          obtain ⟨R, hR⟩ := Polynomial.dvd_iff_isRoot.mpr hx
          rcases hqirr.isUnit_or_isUnit hR with hu | hu
          · exact Polynomial.not_isUnit_X_sub_C x hu
          · have := congrArg Polynomial.natDegree hR
            rw [hqdeg, Polynomial.natDegree_mul (Polynomial.monic_X_sub_C x).ne_zero hu.ne_zero,
                Polynomial.natDegree_X_sub_C, Polynomial.natDegree_eq_zero_of_isUnit hu] at this; omega
        have hl : l = M.val 0 0 := by
          have hrt : ((Polynomial.X - C l) * q).IsRoot (M.val 0 0) := by
            rw [← hchl, hch]; simp [Polynomial.IsRoot]
          simp only [Polynomial.IsRoot, Polynomial.eval_mul, mul_eq_zero, Polynomial.eval_sub,
            Polynomial.eval_X, Polynomial.eval_C, sub_eq_zero] at hrt
          exact (hrt.resolve_right (hqno _)).symm
        subst hl
        have hqeq : q = Polynomial.X ^ 2 + C s * Polynomial.X + C t :=
          mul_left_cancel₀ (Polynomial.monic_X_sub_C (M.val 0 0)).ne_zero (hchl.symm.trans hch)
        exact hqno z (by rw [Polynomial.IsRoot, hqeq]; simpa using hz)
      have he12 : M.val 1 2 ≠ 0 := fun h0 => by
        have := hno (M.val 1 1); apply this; simp [s, t, h0]; ring
      refine ⟨(M.val 0 0, M.val 1 1, ⟨M.val 1 2, he12⟩, ⟨(s, t), Finset.mem_filter.mpr ⟨Finset.mem_univ _, hno⟩⟩), Subtype.ext ?_⟩
      ext i j; fin_cases i <;> fin_cases j <;> simp [toMH, toMH_mat, h01, h02, h10, h20, s, t]
      rw [← mul_assoc, inv_mul_cancel₀ he12, one_mul]⟩
    have hMH_card : MH.card = p ^ 2 * (p - 1) * (p * (p - 1) / 2) := by
      have h1 : MH.card = Fintype.card ParamH := by
        rw [← Fintype.card_coe MH, ← Fintype.card_congr hMH_bij]
      have hne0 : Fintype.card { e : ZMod p // e ≠ 0 } = p - 1 := by
        have h2 : Fintype.card { e : ZMod p // e ≠ 0 } = Fintype.card { e : ZMod p // ¬ e = 0 } := rfl
        rw [h2, Fintype.card_subtype_compl, ZMod.card, Fintype.card_unique]
      rw [h1, Fintype.card_prod, Fintype.card_prod, Fintype.card_prod, ZMod.card,
          hne0, Fintype.card_coe, hIq_card]
      ring
    rw [hMH_card] at hMH_sum
    rw [Nat.card_eq_fintype_card]
    have hpos : 0 < p ^ 2 * (p - 1) := by
      have : 0 < p - 1 := by omega
      positivity
    exact Nat.eq_of_mul_eq_mul_right hpos (by rw [← hMH_sum, mul_comm])
  -- Part 3: `|V_(H)| = |V_(B)| * (p * (p - 1) / 2) = (p^3 - 1) * p^3 / 2`!
  have hH_card : Nat.card (VertsOfType p .H) = (p ^ 3 - 1) * p ^ 3 / 2 := by
    let : Fintype (VertsOfType p .H) := Fintype.ofFinite _
    let : Fintype (VertsOfType p .B) := Fintype.ofFinite _
    let toB : VertsOfType p .H → VertsOfType p .B := fun h =>
      ⟨Classical.choose (hH_part1 h.val h.prop).1, (Classical.choose_spec (hH_part1 h.val h.prop).1).1.1⟩
    have hsum : Fintype.card (VertsOfType p .H) =
        ∑ b : VertsOfType p .B, (Finset.univ.filter fun h : VertsOfType p .H => toB h = b).card := by
      rw [← Finset.card_biUnion]
      · have : Finset.univ.biUnion (fun b : VertsOfType p .B =>
            Finset.univ.filter fun h : VertsOfType p .H => toB h = b) = Finset.univ := by ext h; simp
        rw [this, Finset.card_univ]
      · intro b1 _ b2 _ hne; change Disjoint _ _; rw [Finset.disjoint_left]
        intro h h1 h2; exact hne (((Finset.mem_filter.mp h1).2).symm.trans (Finset.mem_filter.mp h2).2)
    have hfib : ∀ b : VertsOfType p .B,
        (Finset.univ.filter fun h : VertsOfType p .H => toB h = b).card = p * (p - 1) / 2 := fun b => by
      let : Fintype { h : UCCGVert p // VertHasType h .H ∧ UCCGAdj b.val h } := Fintype.ofFinite _
      have heq : { h : VertsOfType p .H // toB h = b } ≃ { h : UCCGVert p // VertHasType h .H ∧ UCCGAdj b.val h } :=
        { toFun := fun h => ⟨h.val.val, h.val.prop, fun X hX Y hY =>
            ((Classical.choose_spec (hH_part1 h.val.val h.val.prop).1).1.2 Y hY X (by
              have h1 : Classical.choose (hH_part1 h.val.val h.val.prop).1 = b.val := congrArg Subtype.val h.prop
              rwa [h1])).symm⟩
          invFun := fun h => ⟨⟨h.val, h.prop.1⟩, Subtype.ext ((Classical.choose_spec (hH_part1 h.val h.prop.1).1).2 b.val
            ⟨b.prop, fun X hX Y hY => (h.prop.2 Y hY X hX).symm⟩).symm⟩
          left_inv := fun _ => rfl
          right_inv := fun _ => rfl }
      rw [← Fintype.card_subtype, Fintype.card_congr heq, ← Nat.card_eq_fintype_card]
      exact hH_part2 b.val b.prop
    simp_rw [hfib] at hsum
    rw [Finset.sum_const, Finset.card_univ, smul_eq_mul, ← Nat.card_eq_fintype_card,
        ← Nat.card_eq_fintype_card, (card_verts_B_E p).1] at hsum
    rw [hsum]
    have heven : 2 ∣ p * (p - 1) := by
      rcases Nat.even_or_odd p with ⟨k, rfl⟩ | ⟨k, rfl⟩
      · exact ⟨k * (2 * k - 1), by ring⟩
      · exact ⟨(2 * k + 1) * k, by zify [show 1 ≤ 2 * k + 1 by omega]; ring⟩
    obtain ⟨m, hm⟩ := heven
    have hdiv1 : p * (p - 1) / 2 = m := by omega
    have hmul : (p ^ 3 - 1) * p ^ 3 = 2 * ((p ^ 2 + p + 1) * p ^ 2 * m) := by
      have h1 : (p ^ 2 + p + 1) * p ^ 2 * (p * (p - 1)) = (p ^ 3 - 1) * p ^ 3 := by
        zify [show 1 ≤ p by omega, Nat.one_le_pow 3 p (by omega)]; ring
      rw [← h1, hm]; ring
    rw [hdiv1, hmul, Nat.mul_div_cancel_left _ (by omega)]
  exact ⟨hH_part1, hH_part2, hH_card⟩

/-- Helper: diagonal polynomial evaluation on `Matrix.diagonal ![l, m, n]`. -/
private lemma aeval_diag3 {p : ℕ} [Fact p.Prime] (l m n : ZMod p) (g : (ZMod p)[X]) :
    aeval (Matrix.diagonal ![l, m, n]) g = Matrix.diagonal ![g.eval l, g.eval m, g.eval n] := by
  induction g using Polynomial.induction_on' with
  | add g1 g2 h1 h2 => rw [map_add, h1, h2]; ext i j; fin_cases i <;> fin_cases j <;> simp
  | monomial k r =>
    rw [aeval_monomial, Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul, Matrix.diagonal_pow]
    ext i j; fin_cases i <;> fin_cases j <;> simp [Polynomial.eval_monomial]

/-- Helper: Section 5(C) Part 0 — `hdiag_B`, `hC_noE`, and canonicalization of `(B)`-triangles. -/
private lemma section5_C_helpers (p : ℕ) [Fact p.Prime] :
    (∀ k : Fin 3, HasM3Type (Matrix.diagonal (Pi.single k (1 : ZMod p))) .B) ∧
    (∀ v ∈ VertsOfType p .C, ∀ e ∈ VertsOfType p .E, ¬ UCCGAdj v e) ∧
    (∀ T : { T : Finset (UCCGVert p) // T.card = 3 ∧
        (∀ b ∈ T, VertHasType b .B) ∧ (∀ b₁ ∈ T, ∀ b₂ ∈ T, UCCGAdj b₁ b₂) },
      ∃ S : GL (Fin 3) (ZMod p),
        ∀ b : UCCGVert p, b ∈ T.val ↔
          b = ⟨Subring.closure ({(conjAlgEquiv S).symm (Matrix.diagonal (Pi.single 0 1))} : Set (M3 p)), ⟨_, rfl⟩⟩ ∨
          b = ⟨Subring.closure ({(conjAlgEquiv S).symm (Matrix.diagonal (Pi.single 1 1))} : Set (M3 p)), ⟨_, rfl⟩⟩ ∨
          b = ⟨Subring.closure ({(conjAlgEquiv S).symm (Matrix.diagonal (Pi.single 2 1))} : Set (M3 p)), ⟨_, rfl⟩⟩) := by
  classical
  have hB0_B : HasM3Type (matB0 p) .B := matB0_hasType p
  have hdiag_B : ∀ k : Fin 3, HasM3Type (Matrix.diagonal (Pi.single k (1 : ZMod p))) .B := fun k => by
    let σ : Equiv.Perm (Fin 3) := Equiv.swap 0 k
    have hli : LinearIndependent (ZMod p) ![(Pi.single (σ 0) 1 : V3 p), Pi.single (σ 1) 1, Pi.single (σ 2) 1] := by
      rw [linearIndependent_three_iff]; intro c0 c1 c2 h
      have h0 := congrFun h (σ 0); have h1 := congrFun h (σ 1); have h2 := congrFun h (σ 2)
      have h01 : σ 0 ≠ σ 1 := fun e => by have := σ.injective e; simp at this
      have h02 : σ 0 ≠ σ 2 := fun e => by have := σ.injective e; simp at this
      have h12 : σ 1 ≠ σ 2 := fun e => by have := σ.injective e; simp at this
      simp [h01, h02, h12, h01.symm, h02.symm, h12.symm] at h0 h1 h2
      exact ⟨h0, h1, h2⟩
    have hconj := glOfCols_mul_eq hli (Matrix.diagonal (Pi.single k (1 : ZMod p))) (matB0 p)
      (by ext i; fin_cases i <;> simp [matB0, σ, Matrix.mulVec_diagonal, Pi.single_apply])
      (by
        have h10 : σ 1 ≠ k := fun e => by
          have : σ 1 = σ 0 := by simpa [σ] using e
          have := σ.injective this; simp at this
        ext i; simp [matB0, Matrix.mulVec_diagonal, Pi.single_apply]
        by_cases hi : i = σ 1
        · subst hi; simp [h10]
        · simp [hi])
      (by
        have h20 : σ 2 ≠ k := fun e => by
          have : σ 2 = σ 0 := by simpa [σ] using e
          have := σ.injective this; simp at this
        ext i; simp [matB0, Matrix.mulVec_diagonal, Pi.single_apply]
        by_cases hi : i = σ 2
        · subst hi; simp [h20]
        · simp [hi])
    exact (hasM3Type_conj _ _ .B).mp (hconj ▸ hB0_B)
  have hdiag_not_E : ∀ (a b c : ZMod p), ¬ HasM3Type (Matrix.diagonal ![a, b, c]) .E := by
    rintro a b c ⟨l, hch, hm⟩
    have h0 := minpoly.aeval (ZMod p) (Matrix.diagonal ![a, b, c])
    rw [hm, map_pow, map_sub, aeval_X, aeval_C, Algebra.algebraMap_eq_smul_one] at h0
    have ha : (a - l) ^ 2 = 0 := by simpa [sq, Matrix.mul_apply, Fin.sum_univ_three] using congrArg (fun M : M3 p => M 0 0) h0
    have hb : (b - l) ^ 2 = 0 := by simpa [sq, Matrix.mul_apply, Fin.sum_univ_three] using congrArg (fun M : M3 p => M 1 1) h0
    have hc : (c - l) ^ 2 = 0 := by simpa [sq, Matrix.mul_apply, Fin.sum_univ_three] using congrArg (fun M : M3 p => M 2 2) h0
    have hEq : Matrix.diagonal ![a, b, c] = l • (1 : M3 p) := by
      have ha' := sub_eq_zero.mp (pow_eq_zero ha)
      have hb' := sub_eq_zero.mp (pow_eq_zero hb)
      have hc' := sub_eq_zero.mp (pow_eq_zero hc)
      ext i j; fin_cases i <;> fin_cases j <;> simp [ha', hb', hc']
    have hA : HasM3Type (Matrix.diagonal ![a, b, c]) .A := ⟨l, hEq ▸ charpoly_smul_one l, hEq ▸ minpoly_smul_one l⟩
    exact M3Type.noConfusion (hasM3Type_unique hA (show HasM3Type (Matrix.diagonal ![a, b, c]) .E from ⟨l, hch, hm⟩))
  have hC_noE : ∀ v ∈ VertsOfType p .C, ∀ e ∈ VertsOfType p .E, ¬ UCCGAdj v e := by
    intro v hv e he hadj
    have hle := le_of_adj_nonderog (Or.inl hv) hadj
    obtain ⟨A, hAv, hAC⟩ := hv
    obtain ⟨S, l, m, n, hlm, hln, hmn, hS⟩ := canonical_C hAC
    obtain ⟨X, hXe, hXE⟩ := he
    have hX_in : conjAlgEquiv S X ∈ Subring.closure ({Matrix.diagonal ![l, m, n]} : Set (M3 p)) := by
      rw [← hS, subring_closure_conj]; exact ⟨X, hAv ▸ hle (hXe ▸ Subring.subset_closure rfl), rfl⟩
    obtain ⟨f, hf⟩ := (mem_subring_closure_iff_aeval _ _).mp hX_in
    have hdiag : conjAlgEquiv S X = Matrix.diagonal ![f.eval l, f.eval m, f.eval n] := hf ▸ aeval_diag3 l m n f
    exact hdiag_not_E _ _ _ (hdiag ▸ (hasM3Type_conj S X .E).mpr hXE)
  let Tri := { T : Finset (UCCGVert p) // T.card = 3 ∧
      (∀ b ∈ T, VertHasType b .B) ∧ (∀ b₁ ∈ T, ∀ b₂ ∈ T, UCCGAdj b₁ b₂) }
  have hTri_canon : ∀ T : Tri, ∃ S : GL (Fin 3) (ZMod p),
      ∀ b : UCCGVert p, b ∈ T.val ↔
        b = ⟨Subring.closure ({(conjAlgEquiv S).symm (Matrix.diagonal (Pi.single 0 1))} : Set (M3 p)), ⟨_, rfl⟩⟩ ∨
        b = ⟨Subring.closure ({(conjAlgEquiv S).symm (Matrix.diagonal (Pi.single 1 1))} : Set (M3 p)), ⟨_, rfl⟩⟩ ∨
        b = ⟨Subring.closure ({(conjAlgEquiv S).symm (Matrix.diagonal (Pi.single 2 1))} : Set (M3 p)), ⟨_, rfl⟩⟩ := by
    intro T
    obtain ⟨b0, b1, b2, hb0, hb1, hb2, h01, h02, h12, hTeq⟩ :
        ∃ b0 b1 b2 : UCCGVert p, b0 ∈ T.val ∧ b1 ∈ T.val ∧ b2 ∈ T.val ∧
          b0 ≠ b1 ∧ b0 ≠ b2 ∧ b1 ≠ b2 ∧ T.val = {b0, b1, b2} := by
      obtain ⟨b0, hb0⟩ := Finset.card_pos.mp (by omega : 0 < T.val.card)
      have hc1 : (T.val.erase b0).card = 2 := by rw [Finset.card_erase_of_mem hb0, T.prop.1]
      obtain ⟨b1, hb1'⟩ := Finset.card_pos.mp (by omega : 0 < (T.val.erase b0).card)
      have h01 : b0 ≠ b1 := (Finset.ne_of_mem_erase hb1').symm
      have hb1 : b1 ∈ T.val := Finset.mem_of_mem_erase hb1'
      have hc2 : ((T.val.erase b0).erase b1).card = 1 := by rw [Finset.card_erase_of_mem hb1', hc1]
      obtain ⟨b2, hb2eq⟩ := Finset.card_eq_one.mp hc2
      have hb2'' : b2 ∈ (T.val.erase b0).erase b1 := by rw [hb2eq]; exact Finset.mem_singleton_self b2
      have h12 : b1 ≠ b2 := (Finset.ne_of_mem_erase hb2'').symm
      have hb2' : b2 ∈ T.val.erase b0 := Finset.mem_of_mem_erase hb2''
      have h02 : b0 ≠ b2 := (Finset.ne_of_mem_erase hb2').symm
      have hb2 : b2 ∈ T.val := Finset.mem_of_mem_erase hb2'
      refine ⟨b0, b1, b2, hb0, hb1, hb2, h01, h02, h12, ?_⟩
      ext x; constructor
      · intro hx
        by_cases hx0 : x = b0
        · simp [hx0]
        · by_cases hx1 : x = b1
          · simp [hx1]
          · have : x ∈ (T.val.erase b0).erase b1 := Finset.mem_erase.mpr ⟨hx1, Finset.mem_erase.mpr ⟨hx0, hx⟩⟩
            rw [hb2eq, Finset.mem_singleton] at this; simp [this]
      · intro hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl | rfl <;> assumption
    obtain ⟨P0, hP0b, hP0_2, hP0r, _, hP0n⟩ := exists_rank1_gen_B (T.prop.2.1 b0 hb0)
    obtain ⟨P1, hP1b, hP1_2, hP1r, _, hP1n⟩ := exists_rank1_gen_B (T.prop.2.1 b1 hb1)
    obtain ⟨P2, hP2b, hP2_2, hP2r, _, hP2n⟩ := exists_rank1_gen_B (T.prop.2.1 b2 hb2)
    have horth : ∀ {bi bj : UCCGVert p} {Pi Pj : M3 p}, bi ≠ bj →
        Pi ∈ SingleGens bi → Pj ∈ SingleGens bj →
        Module.finrank (ZMod p) (LinearMap.range (Matrix.toLin' Pi)) = 1 →
        Module.finrank (ZMod p) (LinearMap.range (Matrix.toLin' Pj)) = 1 →
        Pi * Pj = Pj * Pi → Pi * Pj = 0 := by
      intro bi bj Pi Pj hne hPi hPj hri hrj hcomm
      obtain ⟨ui, wi, hui, hwi, hvec_i⟩ := rank1_eq_vecMulVec hri
      obtain ⟨uj, wj, huj, hwj, hvec_j⟩ := rank1_eq_vecMulVec hrj
      rw [hvec_i, hvec_j, vecMulVec_mul_vecMulVec] at hcomm ⊢
      rw [vecMulVec_mul_vecMulVec] at hcomm
      have hd : dotProduct wi uj = 0 := by
        by_contra hdn
        have hdj : dotProduct wj ui ≠ 0 := by
          intro h0; rw [h0, zero_smul] at hcomm
          have h0' : Matrix.vecMulVec ui wj = 0 := by
            simpa [smul_smul, inv_mul_cancel₀ hdn] using congrArg ((dotProduct wi uj)⁻¹ • ·) hcomm
          have hex_u : ∃ i, ui i ≠ 0 := by by_contra h; push Not at h; exact hui (funext h)
          have hex_w : ∃ j, wj j ≠ 0 := by by_contra h; push Not at h; exact hwj (funext h)
          obtain ⟨i, hi⟩ := hex_u; obtain ⟨j, hj⟩ := hex_w
          have := congrArg (fun M : M3 p => M i j) h0'; simp [Matrix.vecMulVec_apply] at this
          rcases this with h | h <;> contradiction
        have hsc : Matrix.vecMulVec ui wj = ((dotProduct wi uj)⁻¹ * dotProduct wj ui) • Matrix.vecMulVec uj wi := by
          simpa [smul_smul, inv_mul_cancel₀ hdn] using congrArg ((dotProduct wi uj)⁻¹ • ·) hcomm
        obtain ⟨hU, hW⟩ := (vecMulVec_eq_iff hui hwj huj hwi).mp ⟨_, mul_ne_zero (inv_ne_zero hdn) hdj, hsc⟩
        obtain ⟨c, hc, hEq⟩ := (vecMulVec_eq_iff hui hwi huj hwj).mpr ⟨hU, hW.symm⟩
        rw [← hvec_i, ← hvec_j] at hEq
        have hcl : Subring.closure ({Pi} : Set (M3 p)) = Subring.closure ({Pj} : Set (M3 p)) := by
          have : Pi = c • Pj + (0 : ZMod p) • (1 : M3 p) := by simp [hEq]
          rw [this, subring_closure_affine Pj hc 0]
        exact hne (Subtype.ext (hPi.symm.trans (hcl.trans hPj)))
      rw [hd, zero_smul]
    have h01_0 : P0 * P1 = 0 := horth h01 hP0b hP1b hP0r hP1r ((uccgAdj_iff_comm hP0b hP1b).mp (T.prop.2.2 b0 hb0 b1 hb1))
    have h10_0 : P1 * P0 = 0 := horth h01.symm hP1b hP0b hP1r hP0r ((uccgAdj_iff_comm hP1b hP0b).mp (T.prop.2.2 b1 hb1 b0 hb0))
    have h02_0 : P0 * P2 = 0 := horth h02 hP0b hP2b hP0r hP2r ((uccgAdj_iff_comm hP0b hP2b).mp (T.prop.2.2 b0 hb0 b2 hb2))
    have h20_0 : P2 * P0 = 0 := horth h02.symm hP2b hP0b hP2r hP0r ((uccgAdj_iff_comm hP2b hP0b).mp (T.prop.2.2 b2 hb2 b0 hb0))
    have h12_0 : P1 * P2 = 0 := horth h12 hP1b hP2b hP1r hP2r ((uccgAdj_iff_comm hP1b hP2b).mp (T.prop.2.2 b1 hb1 b2 hb2))
    have h21_0 : P2 * P1 = 0 := horth h12.symm hP2b hP1b hP2r hP1r ((uccgAdj_iff_comm hP2b hP1b).mp (T.prop.2.2 b2 hb2 b1 hb1))
    have hex_v : ∀ {P : M3 p}, P ^ 2 = P → Module.finrank (ZMod p) (LinearMap.range (Matrix.toLin' P)) = 1 →
        ∃ v : V3 p, v ≠ 0 ∧ P *ᵥ v = v := by
      intro P hP2 hPr
      have hne : LinearMap.range (Matrix.toLin' P) ≠ ⊥ := fun h => by rw [h, finrank_bot] at hPr; omega
      obtain ⟨v, ⟨x, rfl⟩, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
      exact ⟨P *ᵥ x, hv0, by rw [Matrix.mulVec_mulVec, ← sq, hP2]⟩
    obtain ⟨v0, hv0_ne, hv0⟩ := hex_v hP0_2 hP0r
    obtain ⟨v1, hv1_ne, hv1⟩ := hex_v hP1_2 hP1r
    obtain ⟨v2, hv2_ne, hv2⟩ := hex_v hP2_2 hP2r
    have hP0v1 : P0 *ᵥ v1 = 0 := by rw [← hv1, Matrix.mulVec_mulVec, h01_0, Matrix.zero_mulVec]
    have hP0v2 : P0 *ᵥ v2 = 0 := by rw [← hv2, Matrix.mulVec_mulVec, h02_0, Matrix.zero_mulVec]
    have hP1v0 : P1 *ᵥ v0 = 0 := by rw [← hv0, Matrix.mulVec_mulVec, h10_0, Matrix.zero_mulVec]
    have hP1v2 : P1 *ᵥ v2 = 0 := by rw [← hv2, Matrix.mulVec_mulVec, h12_0, Matrix.zero_mulVec]
    have hP2v0 : P2 *ᵥ v0 = 0 := by rw [← hv0, Matrix.mulVec_mulVec, h20_0, Matrix.zero_mulVec]
    have hP2v1 : P2 *ᵥ v1 = 0 := by rw [← hv1, Matrix.mulVec_mulVec, h21_0, Matrix.zero_mulVec]
    have hli : LinearIndependent (ZMod p) ![v0, v1, v2] := by
      rw [linearIndependent_three_iff]; intro c0 c1 c2 hsum
      have hc0 : c0 = 0 := by
        have h := congrArg (P0 *ᵥ ·) hsum
        simp only [Matrix.mulVec_add, Matrix.mulVec_smul, hv0, hP0v1, hP0v2, Matrix.mulVec_zero, smul_zero, add_zero] at h
        by_contra hne; exact hv0_ne (by simpa [smul_smul, inv_mul_cancel₀ hne] using congrArg (c0⁻¹ • ·) h)
      have hc1 : c1 = 0 := by
        have h := congrArg (P1 *ᵥ ·) hsum
        simp only [Matrix.mulVec_add, Matrix.mulVec_smul, hP1v0, hv1, hP1v2, Matrix.mulVec_zero, smul_zero, zero_add, add_zero] at h
        by_contra hne; exact hv1_ne (by simpa [smul_smul, inv_mul_cancel₀ hne] using congrArg (c1⁻¹ • ·) h)
      have hc2 : c2 = 0 := by
        have h := congrArg (P2 *ᵥ ·) hsum
        simp only [Matrix.mulVec_add, Matrix.mulVec_smul, hP2v0, hP2v1, hv2, Matrix.mulVec_zero, smul_zero, zero_add] at h
        by_contra hne; exact hv2_ne (by simpa [smul_smul, inv_mul_cancel₀ hne] using congrArg (c2⁻¹ • ·) h)
      exact ⟨hc0, hc1, hc2⟩
    set S := (glOfCols v0 v1 v2 hli)⁻¹
    have hSP0 : conjAlgEquiv S P0 = Matrix.diagonal (Pi.single 0 1) :=
      glOfCols_mul_eq hli P0 _ (by simp [hv0]) (by simp [hP0v1]) (by simp [hP0v2])
    have hSP1 : conjAlgEquiv S P1 = Matrix.diagonal (Pi.single 1 1) :=
      glOfCols_mul_eq hli P1 _ (by simp [hP1v0]) (by simp [hv1]) (by simp [hP1v2])
    have hSP2 : conjAlgEquiv S P2 = Matrix.diagonal (Pi.single 2 1) :=
      glOfCols_mul_eq hli P2 _ (by simp [hP2v0]) (by simp [hP2v1]) (by simp [hv2])
    refine ⟨S, fun b => ?_⟩
    rw [hTeq]
    have hb0_eq : b0 = ⟨Subring.closure ({(conjAlgEquiv S).symm (Matrix.diagonal (Pi.single 0 1))} : Set (M3 p)), ⟨_, rfl⟩⟩ :=
      Subtype.ext (by rw [← hSP0, AlgEquiv.symm_apply_apply]; exact hP0b.symm)
    have hb1_eq : b1 = ⟨Subring.closure ({(conjAlgEquiv S).symm (Matrix.diagonal (Pi.single 1 1))} : Set (M3 p)), ⟨_, rfl⟩⟩ :=
      Subtype.ext (by rw [← hSP1, AlgEquiv.symm_apply_apply]; exact hP1b.symm)
    have hb2_eq : b2 = ⟨Subring.closure ({(conjAlgEquiv S).symm (Matrix.diagonal (Pi.single 2 1))} : Set (M3 p)), ⟨_, rfl⟩⟩ :=
      Subtype.ext (by rw [← hSP2, AlgEquiv.symm_apply_apply]; exact hP2b.symm)
    simp only [Finset.mem_insert, Finset.mem_singleton]
    rw [hb0_eq, hb1_eq, hb2_eq]
  exact ⟨hdiag_B, hC_noE, hTri_canon⟩

/-- Helper: Section 5(C) Part 1 — no `(E)` neighbors and bijection `ψC` with `(B)`-triangles for `p ≥ 3`. -/
private lemma section5_C_bij (p : ℕ) [Fact p.Prime] :
    (∀ v ∈ VertsOfType p .C, ∀ e ∈ VertsOfType p .E, ¬ UCCGAdj v e) ∧
    (3 ≤ p →
      ∃ ψC : VertsOfType p .C ≃
        { T : Finset (UCCGVert p) // T.card = 3 ∧
            (∀ b ∈ T, VertHasType b .B) ∧ (∀ b₁ ∈ T, ∀ b₂ ∈ T, UCCGAdj b₁ b₂) },
      ∀ v b, b ∈ (ψC v).val ↔ (VertHasType b .B ∧ UCCGAdj v.val b)) := by
  classical
  have : Fintype (UCCGVert p) := Fintype.ofFinite _
  obtain ⟨hdiag_B, hC_noE, hTri_canon⟩ := section5_C_helpers p
  let Tri := { T : Finset (UCCGVert p) // T.card = 3 ∧
      (∀ b ∈ T, VertHasType b .B) ∧ (∀ b₁ ∈ T, ∀ b₂ ∈ T, UCCGAdj b₁ b₂) }
  -- Bijection `ψC` for `3 ≤ p`!
  have hC_bij : 3 ≤ p →
      ∃ ψC : VertsOfType p .C ≃ Tri,
        ∀ v b, b ∈ (ψC v).val ↔ (VertHasType b .B ∧ UCCGAdj v.val b) := by
    intro hp3
    -- Map `v ∈ V_C` to its Finset of Type B neighbors!
    let nbrB (v : VertsOfType p .C) : Finset (UCCGVert p) :=
      Finset.univ.filter fun b : UCCGVert p => VertHasType b .B ∧ UCCGAdj v.val b
    have hnbrB_prop : ∀ v : VertsOfType p .C,
        (nbrB v).card = 3 ∧ (∀ b ∈ nbrB v, VertHasType b .B) ∧ (∀ b₁ ∈ nbrB v, ∀ b₂ ∈ nbrB v, UCCGAdj b₁ b₂) := by
      intro v
      obtain ⟨A, hAv, hAC⟩ := v.prop
      obtain ⟨S, l, m, n, hlm, hln, hmn, hS⟩ := canonical_C hAC
      let e0 : UCCGVert p := ⟨Subring.closure ({(conjAlgEquiv S).symm (Matrix.diagonal (Pi.single 0 1))} : Set (M3 p)), ⟨_, rfl⟩⟩
      let e1 : UCCGVert p := ⟨Subring.closure ({(conjAlgEquiv S).symm (Matrix.diagonal (Pi.single 1 1))} : Set (M3 p)), ⟨_, rfl⟩⟩
      let e2 : UCCGVert p := ⟨Subring.closure ({(conjAlgEquiv S).symm (Matrix.diagonal (Pi.single 2 1))} : Set (M3 p)), ⟨_, rfl⟩⟩
      have hEq : nbrB v = {e0, e1, e2} := by
        ext b
        simp only [nbrB, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Finset.mem_singleton]
        constructor
        · rintro ⟨hbB, hadj⟩
          have hle := le_of_adj_nonderog (Or.inl v.prop) hadj
          obtain ⟨X, hXb, hXB⟩ := hbB
          have hX_in : conjAlgEquiv S X ∈ Subring.closure ({Matrix.diagonal ![l, m, n]} : Set (M3 p)) := by
            rw [← hS, subring_closure_conj]; exact ⟨X, hAv ▸ hle (hXb ▸ Subring.subset_closure rfl), rfl⟩
          obtain ⟨f, hf⟩ := (mem_subring_closure_iff_aeval _ _).mp hX_in
          set a0 := f.eval l; set a1 := f.eval m; set a2 := f.eval n
          have hdiag : conjAlgEquiv S X = Matrix.diagonal ![a0, a1, a2] := hf ▸ aeval_diag3 l m n f
          have h2 := (hasM3Type_invariants ((hasM3Type_conj S X .B).mpr hXB)).2.1
          dsimp only at h2
          have hch : (conjAlgEquiv S X).charpoly = (Polynomial.X - C a0) * (Polynomial.X - C a1) * (Polynomial.X - C a2) := by
            rw [hdiag, Matrix.charpoly, Matrix.det_fin_three]
            simp [Matrix.charmatrix]
          rw [hch] at h2
          have hfilt : (Finset.univ.filter fun x : ZMod p => ((Polynomial.X - C a0) * (Polynomial.X - C a1) * (Polynomial.X - C a2)).IsRoot x) =
              {a0, a1, a2} := by ext x; simp [Polynomial.IsRoot, sub_eq_zero, or_assoc]
          rw [hfilt] at h2
          have hcases : (a1 = a2 ∧ a0 ≠ a1) ∨ (a0 = a2 ∧ a1 ≠ a0) ∨ (a0 = a1 ∧ a2 ≠ a0) := by
            by_cases h01 : a0 = a1
            · by_cases h02 : a0 = a2
              · rw [← h01, ← h02] at h2; simp at h2
              · exact Or.inr (Or.inr ⟨h01, Ne.symm h02⟩)
            · by_cases h02 : a0 = a2
              · exact Or.inr (Or.inl ⟨h02, Ne.symm h01⟩)
              · by_cases h12 : a1 = a2
                · exact Or.inl ⟨h12, h01⟩
                · rw [Finset.card_insert_of_notMem (by simp [h01, h02]), Finset.card_pair h12] at h2; omega
          have hmk : ∀ (k : Fin 3) (c d : ZMod p), c ≠ 0 →
              conjAlgEquiv S X = c • Matrix.diagonal (Pi.single k 1) + d • (1 : M3 p) →
              b = ⟨Subring.closure ({(conjAlgEquiv S).symm (Matrix.diagonal (Pi.single k 1))} : Set (M3 p)), ⟨_, rfl⟩⟩ := by
            intro k c d hc hXk
            have hcl_S : Subring.closure ({conjAlgEquiv S X} : Set (M3 p)) =
                Subring.closure ({Matrix.diagonal (Pi.single k 1)} : Set (M3 p)) := by
              rw [hXk, subring_closure_affine _ hc d]
            apply Subtype.ext; rw [← hXb]
            have h1 := congrArg (Subring.map (conjAlgEquiv S).symm.toRingHom) hcl_S
            rw [subring_map_closure, subring_map_closure, Set.image_singleton, Set.image_singleton] at h1
            simpa using h1
          rcases hcases with ⟨h12, h01⟩ | ⟨h02, h10⟩ | ⟨h01, h20⟩
          · left; exact hmk 0 (a0 - a1) a1 (sub_ne_zero.mpr h01) (by rw [hdiag, h12]; ext i j; fin_cases i <;> fin_cases j <;> simp)
          · right; left; exact hmk 1 (a1 - a0) a0 (sub_ne_zero.mpr h10) (by rw [hdiag, h02]; ext i j; fin_cases i <;> fin_cases j <;> simp)
          · right; right; exact hmk 2 (a2 - a0) a0 (sub_ne_zero.mpr h20) (by rw [hdiag, h01]; ext i j; fin_cases i <;> fin_cases j <;> simp)
        · rintro (rfl | rfl | rfl)
          · refine ⟨⟨_, rfl, (hasM3Type_conj S _ .B).mp (by simpa using hdiag_B 0)⟩, (uccgAdj_iff_comm hAv rfl).mpr ?_⟩
            apply (conjAlgEquiv S).injective; simp only [map_mul, AlgEquiv.apply_symm_apply, hS]
            ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]
          · refine ⟨⟨_, rfl, (hasM3Type_conj S _ .B).mp (by simpa using hdiag_B 1)⟩, (uccgAdj_iff_comm hAv rfl).mpr ?_⟩
            apply (conjAlgEquiv S).injective; simp only [map_mul, AlgEquiv.apply_symm_apply, hS]
            ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]
          · refine ⟨⟨_, rfl, (hasM3Type_conj S _ .B).mp (by simpa using hdiag_B 2)⟩, (uccgAdj_iff_comm hAv rfl).mpr ?_⟩
            apply (conjAlgEquiv S).injective; simp only [map_mul, AlgEquiv.apply_symm_apply, hS]
            ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]
      have hne_ek : ∀ k₁ k₂ : Fin 3, k₁ ≠ k₂ →
          Subring.closure ({Matrix.diagonal (Pi.single k₁ (1 : ZMod p))} : Set (M3 p)) ≠
          Subring.closure ({Matrix.diagonal (Pi.single k₂ (1 : ZMod p))} : Set (M3 p)) := by
        intro k₁ k₂ hne hcl
        have hsq : Matrix.diagonal (Pi.single k₂ (1 : ZMod p)) ^ 2 =
            (1 : ZMod p) • Matrix.diagonal (Pi.single k₂ (1 : ZMod p)) + (0 : ZMod p) • (1 : M3 p) := by
          ext i j; fin_cases i <;> fin_cases j <;> fin_cases k₂ <;> simp [sq, Matrix.mul_apply, Fin.sum_univ_three]
        obtain ⟨c0, c1, hc⟩ := (mem_closure_deg2 hsq (Matrix.diagonal (Pi.single k₁ (1 : ZMod p)))).mp
          (hcl ▸ Subring.subset_closure rfl)
        -- Look at the third index `k₃ ∉ {k₁, k₂}` -> `c0 = 0`, then at `k₁` -> `1 = 0`, contradiction!
        have hex3 : ∃ k₃ : Fin 3, k₃ ≠ k₁ ∧ k₃ ≠ k₂ := by
          fin_cases k₁ <;> fin_cases k₂ <;> first | exact absurd rfl hne | exact ⟨0, by decide, by decide⟩ | exact ⟨1, by decide, by decide⟩ | exact ⟨2, by decide, by decide⟩
        obtain ⟨k₃, h31, h32⟩ := hex3
        have hc0 : c0 = 0 := by have := congrArg (fun M : M3 p => M k₃ k₃) hc; simp [h31, h32] at this; exact this.symm
        have h10 : (1 : ZMod p) = 0 := by have := congrArg (fun M : M3 p => M k₁ k₁) hc; simp [hc0, hne] at this
        exact one_ne_zero h10
      have he01 : e0 ≠ e1 := fun h => hne_ek 0 1 (by decide) (by
        have h1 := congrArg (fun z : UCCGVert p => z.val.map (conjAlgEquiv S).toRingHom) h
        simp only [e0, e1, subring_map_closure, Set.image_singleton] at h1; simpa using h1)
      have he02 : e0 ≠ e2 := fun h => hne_ek 0 2 (by decide) (by
        have h1 := congrArg (fun z : UCCGVert p => z.val.map (conjAlgEquiv S).toRingHom) h
        simp only [e0, e2, subring_map_closure, Set.image_singleton] at h1; simpa using h1)
      have he12 : e1 ≠ e2 := fun h => hne_ek 1 2 (by decide) (by
        have h1 := congrArg (fun z : UCCGVert p => z.val.map (conjAlgEquiv S).toRingHom) h
        simp only [e1, e2, subring_map_closure, Set.image_singleton] at h1; simpa using h1)
      refine ⟨?_, fun b hb => (Finset.mem_filter.mp hb).2.1, fun b1 hb1 b2 hb2 => ?_⟩
      · rw [hEq, Finset.card_insert_of_notMem (by simp [he01, he02]), Finset.card_pair he12]
      · have hle1 := le_of_adj_nonderog (Or.inl v.prop) (Finset.mem_filter.mp hb1).2.2
        have hle2 := le_of_adj_nonderog (Or.inl v.prop) (Finset.mem_filter.mp hb2).2.2
        intro X hX Y hY
        have hX' := hle1 hX; have hY' := hle2 hY
        exact (uccgAdj_iff_comm hAv hAv).mpr rfl X hX' Y hY'
    let toTri : VertsOfType p .C → Tri := fun v => ⟨nbrB v, hnbrB_prop v⟩
    -- Prove `toTri` is bijective!
    have h01_p : (0 : ZMod p) ≠ 1 := zero_ne_one
    have h2v : (2 : ZMod p).val = 2 := by
      have : ((2 : ℕ) : ZMod p).val = 2 := ZMod.val_natCast_of_lt (by omega)
      simpa using this
    have h02_p : (0 : ZMod p) ≠ 2 := fun h => by
      have := congrArg ZMod.val h; rw [ZMod.val_zero, h2v] at this; omega
    have h12_p : (1 : ZMod p) ≠ 2 := fun h => by
      have := congrArg ZMod.val h; rw [ZMod.val_one, h2v] at this; omega
    have hdiag012_C : HasM3Type (Matrix.diagonal ![(0 : ZMod p), 1, 2]) .C := by
      have hch : (Matrix.diagonal ![(0 : ZMod p), 1, 2]).charpoly = (Polynomial.X - C 0) * (Polynomial.X - C 1) * (Polynomial.X - C 2) := by
        rw [Matrix.charpoly, Matrix.det_fin_three]
        simp [Matrix.charmatrix]
      refine ⟨0, 1, 2, h01_p, h02_p, h12_p, hch, ?_⟩
      obtain ⟨t, ht⟩ := exists_hasM3Type (Matrix.diagonal ![(0 : ZMod p), 1, 2])
      have h3 : (Finset.univ.filter fun x : ZMod p => (Matrix.diagonal ![(0 : ZMod p), 1, 2]).charpoly.IsRoot x).card = 3 := by
        rw [hch]
        have : (Finset.univ.filter fun x : ZMod p => (((Polynomial.X - C (0 : ZMod p)) * (Polynomial.X - C 1) * (Polynomial.X - C 2)) : (ZMod p)[X]).IsRoot x) = {0, 1, 2} := by
          ext x; simp [Polynomial.IsRoot, sub_eq_zero, or_assoc]
        rw [this, Finset.card_insert_of_notMem (by simp [h01_p, h02_p]), Finset.card_pair h12_p]
      have hinv := (hasM3Type_invariants ht).2.1
      rw [h3] at hinv
      have htC : t = .C := by cases t <;> (dsimp only at hinv; first | rfl | omega)
      subst htC; exact ht.choose_spec.choose_spec.choose_spec.2.2.2.2
    have htoTri_bij : Function.Bijective toTri := by
      constructor
      · intro v1 v2 hEq
        set T := toTri v1
        obtain ⟨S, hST⟩ := hTri_canon T
        -- Any `v ∈ V_C` with `toTri v = T` contains `(conj S)⁻¹ E00`, `E11`, `E22`, hence contains `(conj S)⁻¹ diag(0, 1, 2)`!
        have hmust : ∀ v : VertsOfType p .C, toTri v = T →
            v.val.val = Subring.closure ({(conjAlgEquiv S).symm (Matrix.diagonal ![(0 : ZMod p), 1, 2])} : Set (M3 p)) := by
          intro v hv
          have hmem_k : ∀ k : Fin 3, (conjAlgEquiv S).symm (Matrix.diagonal (Pi.single k 1)) ∈ v.val.val := fun k => by
            let ek : UCCGVert p := ⟨Subring.closure ({(conjAlgEquiv S).symm (Matrix.diagonal (Pi.single k 1))} : Set (M3 p)), ⟨_, rfl⟩⟩
            have hek_in : ek ∈ (toTri v).val := by
              rw [hv, hST]
              fin_cases k
              · exact Or.inl rfl
              · exact Or.inr (Or.inl rfl)
              · exact Or.inr (Or.inr rfl)
            have hadj : UCCGAdj v.val ek := (Finset.mem_filter.mp hek_in).2.2
            exact le_of_adj_nonderog (Or.inl v.prop) hadj (Subring.subset_closure rfl)
          have h012_eq : (conjAlgEquiv S).symm (Matrix.diagonal ![(0 : ZMod p), 1, 2]) =
              (1 : ZMod p) • (conjAlgEquiv S).symm (Matrix.diagonal (Pi.single 1 1)) +
              (2 : ZMod p) • (conjAlgEquiv S).symm (Matrix.diagonal (Pi.single 2 1)) := by
            rw [← map_smul, ← map_smul, ← map_add]; congr 1
            ext i j; fin_cases i <;> fin_cases j <;> simp
          have h012_in : (conjAlgEquiv S).symm (Matrix.diagonal ![(0 : ZMod p), 1, 2]) ∈ v.val.val :=
            h012_eq ▸ add_mem (smul_mem_subring _ _ (hmem_k 1)) (smul_mem_subring _ _ (hmem_k 2))
          have hC012 : HasM3Type ((conjAlgEquiv S).symm (Matrix.diagonal ![(0 : ZMod p), 1, 2])) .C :=
            (hasM3Type_conj S _ .C).mp (by simpa using hdiag012_C)
          obtain ⟨A, hAv, _⟩ := v.prop
          have hadj : UCCGAdj v.val ⟨Subring.closure ({(conjAlgEquiv S).symm (Matrix.diagonal ![(0 : ZMod p), 1, 2])} : Set (M3 p)), ⟨_, rfl⟩⟩ := by
            refine (uccgAdj_iff_comm hAv rfl).mpr ?_
            obtain ⟨g, hg⟩ := (mem_subring_closure_iff_aeval A _).mp (hAv.symm ▸ h012_in)
            rw [← hg]; exact (commute_aeval_self A g).symm
          by_contra hne
          exact nonderog_no_cross_edges (fun h => hne (congrArg Subtype.val h))
            (Or.inl v.prop) (Or.inl ⟨_, rfl, hC012⟩) hadj
        exact Subtype.ext (Subtype.ext ((hmust v1 rfl).trans (hmust v2 hEq.symm).symm))
      · intro T
        obtain ⟨S, hST⟩ := hTri_canon T
        let v : VertsOfType p .C :=
          ⟨⟨Subring.closure ({(conjAlgEquiv S).symm (Matrix.diagonal ![(0 : ZMod p), 1, 2])} : Set (M3 p)), ⟨_, rfl⟩⟩,
            ⟨_, rfl, (hasM3Type_conj S _ .C).mp (by simpa using hdiag012_C)⟩⟩
        refine ⟨v, Subtype.ext ?_⟩
        -- Both `(toTri v).val` and `T.val` have card 3, and `T.val ⊆ (toTri v).val`!
        have hcomm_k : ∀ k : Fin 3,
            Matrix.diagonal ![(0 : ZMod p), 1, 2] * Matrix.diagonal (Pi.single k 1) =
            Matrix.diagonal (Pi.single k 1) * Matrix.diagonal ![(0 : ZMod p), 1, 2] := fun k => by
          rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]; congr 1; ext i; ring
        have hsub : T.val ⊆ (toTri v).val := by
          intro b hb
          let ek (k : Fin 3) : UCCGVert p :=
            ⟨Subring.closure ({(conjAlgEquiv S).symm (Matrix.diagonal (Pi.single k 1))} : Set (M3 p)),
              ⟨(conjAlgEquiv S).symm (Matrix.diagonal (Pi.single k 1)), rfl⟩⟩
          have hmem : ∀ k : Fin 3, ek k ∈ (toTri v).val := fun k =>
            Finset.mem_filter.mpr ⟨Finset.mem_univ _,
              ⟨_, rfl, (hasM3Type_conj S _ .B).mp (by simpa using hdiag_B k)⟩,
              (uccgAdj_iff_comm rfl rfl).mpr ((conjAlgEquiv S).injective (by
                simp only [map_mul, AlgEquiv.apply_symm_apply]; exact hcomm_k k))⟩
          rcases (hST b).mp hb with rfl | rfl | rfl
          · exact hmem 0
          · exact hmem 1
          · exact hmem 2
        exact (Finset.eq_of_subset_of_card_le hsub (by rw [(toTri v).prop.1, T.prop.1])).symm
    exact ⟨Equiv.ofBijective toTri htoTri_bij, fun v b => by simp [toTri, nbrB]⟩
  exact ⟨hC_noE, hC_bij⟩

/-- Helper: Section 5(C) — no `(E)` neighbors, bijection `ψC` with `(B)`-triangles for `p ≥ 3`,
    and `|V_(C)| = expectedVertCount p .C`! -/
private lemma section5_C (p : ℕ) [Fact p.Prime] :
    (∀ v ∈ VertsOfType p .C, ∀ e ∈ VertsOfType p .E, ¬ UCCGAdj v e) ∧
    (3 ≤ p →
      ∃ ψC : VertsOfType p .C ≃
        { T : Finset (UCCGVert p) // T.card = 3 ∧
            (∀ b ∈ T, VertHasType b .B) ∧ (∀ b₁ ∈ T, ∀ b₂ ∈ T, UCCGAdj b₁ b₂) },
      ∀ v b, b ∈ (ψC v).val ↔ (VertHasType b .B ∧ UCCGAdj v.val b)) ∧
    Nat.card (VertsOfType p .C) = expectedVertCount p .C := by
  classical
  have : Fintype (UCCGVert p) := Fintype.ofFinite _
  have hp2 : 2 ≤ p := (Fact.out : p.Prime).two_le
  obtain ⟨hC_noE, hC_bij⟩ := section5_C_bij p
  let Tri := { T : Finset (UCCGVert p) // T.card = 3 ∧
      (∀ b ∈ T, VertHasType b .B) ∧ (∀ b₁ ∈ T, ∀ b₂ ∈ T, UCCGAdj b₁ b₂) }
  have : Fintype Tri := Fintype.ofFinite _
  have : Fintype (VertsOfType p .B) := Fintype.ofFinite _
  -- Count `|V_(C)|`: 0 if `p = 2`; `(p^2 + p + 1) * p^3 * (p + 1) / 6` if `p ≥ 3`!
  have hC_card : Nat.card (VertsOfType p .C) = expectedVertCount p .C := by
    by_cases hp2eq : p = 2
    · subst hp2eq
      dsimp only [expectedVertCount]; rw [if_pos rfl]
      have hemp : IsEmpty (VertsOfType 2 .C) := ⟨fun v => by
        obtain ⟨A, _, l, m, n, hlm, hln, hmn, _, _⟩ := v.prop
        fin_cases l <;> fin_cases m <;> fin_cases n <;>
          first | exact hlm rfl | exact hln rfl | exact hmn rfl⟩
      exact Nat.card_eq_zero.mpr (Or.inl hemp)
    · have hp3 : 3 ≤ p := by omega
      dsimp only [expectedVertCount]; rw [if_neg hp2eq]
      obtain ⟨ψC, _⟩ := hC_bij hp3
      rw [Nat.card_congr ψC]
      -- Count ordered triples `(b0, b1, b2)` of distinct pairwise adjacent Type B vertices = `6 * |Tri|`!
      let OrdTri := { x : VertsOfType p .B × VertsOfType p .B × VertsOfType p .B //
          x.1 ≠ x.2.1 ∧ x.1 ≠ x.2.2 ∧ x.2.1 ≠ x.2.2 ∧
          UCCGAdj x.1.val x.2.1.val ∧ UCCGAdj x.1.val x.2.2.val ∧ UCCGAdj x.2.1.val x.2.2.val }
      have : Fintype OrdTri := Fintype.ofFinite _
      -- 1. `|OrdTri| = 6 * |Tri|` (map `(b0, b1, b2) ↦ {b0, b1, b2}` has every fiber of size `6 = |Perm (Fin 3)|`!)
      let toT : OrdTri → Tri := fun x =>
        ⟨{x.val.1.val, x.val.2.1.val, x.val.2.2.val},
          by rw [Finset.card_insert_of_notMem (by
                   simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
                   exact ⟨fun h => x.prop.1 (Subtype.ext h), fun h => x.prop.2.1 (Subtype.ext h)⟩),
                 Finset.card_pair (fun h => x.prop.2.2.1 (Subtype.ext h))],
          fun b hb => by simp only [Finset.mem_insert, Finset.mem_singleton] at hb; rcases hb with rfl | rfl | rfl; exact x.val.1.prop; exact x.val.2.1.prop; exact x.val.2.2.prop,
          fun b1 hb1 b2 hb2 => by
            have hsym : ∀ u w : UCCGVert p, UCCGAdj u w → UCCGAdj w u := fun u w h X hX Y hY => (h Y hY X hX).symm
            have hrefl : ∀ u : UCCGVert p, UCCGAdj u u := fun u => by obtain ⟨A, hA⟩ := u.prop; exact (uccgAdj_iff_comm hA.symm hA.symm).mpr rfl
            simp only [Finset.mem_insert, Finset.mem_singleton] at hb1 hb2
            rcases hb1 with rfl | rfl | rfl <;> rcases hb2 with rfl | rfl | rfl
            · exact hrefl _
            · exact x.prop.2.2.2.1
            · exact x.prop.2.2.2.2.1
            · exact hsym _ _ x.prop.2.2.2.1
            · exact hrefl _
            · exact x.prop.2.2.2.2.2
            · exact hsym _ _ x.prop.2.2.2.2.1
            · exact hsym _ _ x.prop.2.2.2.2.2
            · exact hrefl _⟩
      have hfib6 : ∀ T : Tri, (Finset.univ.filter fun x : OrdTri => toT x = T).card = 6 := by
        intro T
        obtain ⟨b0, hb0⟩ := Finset.card_pos.mp (by omega : 0 < T.val.card)
        have hc1 : (T.val.erase b0).card = 2 := by rw [Finset.card_erase_of_mem hb0, T.prop.1]
        obtain ⟨b1, hb1'⟩ := Finset.card_pos.mp (by omega : 0 < (T.val.erase b0).card)
        have h01 : b0 ≠ b1 := (Finset.ne_of_mem_erase hb1').symm
        have hb1 : b1 ∈ T.val := Finset.mem_of_mem_erase hb1'
        have hc2 : ((T.val.erase b0).erase b1).card = 1 := by rw [Finset.card_erase_of_mem hb1', hc1]
        obtain ⟨b2, hb2eq⟩ := Finset.card_eq_one.mp hc2
        have hb2'' : b2 ∈ (T.val.erase b0).erase b1 := by rw [hb2eq]; exact Finset.mem_singleton_self b2
        have h12 : b1 ≠ b2 := (Finset.ne_of_mem_erase hb2'').symm
        have hb2' : b2 ∈ T.val.erase b0 := Finset.mem_of_mem_erase hb2''
        have h02 : b0 ≠ b2 := (Finset.ne_of_mem_erase hb2').symm
        have hb2 : b2 ∈ T.val := Finset.mem_of_mem_erase hb2'
        have hTeq : T.val = {b0, b1, b2} := by
          ext x; constructor
          · intro hx; by_cases hx0 : x = b0
            · simp [hx0]
            · by_cases hx1 : x = b1
              · simp [hx1]
              · have : x ∈ (T.val.erase b0).erase b1 := Finset.mem_erase.mpr ⟨hx1, Finset.mem_erase.mpr ⟨hx0, hx⟩⟩
                rw [hb2eq, Finset.mem_singleton] at this; simp [this]
          · intro hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx
            rcases hx with rfl | rfl | rfl <;> assumption
        let arr : Fin 3 → VertsOfType p .B := ![⟨b0, T.prop.2.1 b0 hb0⟩, ⟨b1, T.prop.2.1 b1 hb1⟩, ⟨b2, T.prop.2.1 b2 hb2⟩]
        have harr_inj : Function.Injective arr := by
          intro i j hij
          have hval : (arr i).val = (arr j).val := congrArg Subtype.val hij
          fin_cases i <;> fin_cases j <;> simp [arr] at hval
          all_goals first | rfl | exact absurd hval h01 | exact absurd hval h02 | exact absurd hval h12 |
                            exact absurd hval h01.symm | exact absurd hval h02.symm | exact absurd hval h12.symm
        have harr_mem : ∀ i : Fin 3, (arr i).val ∈ T.val := fun i => by fin_cases i <;> assumption
        have hbij6 : Equiv.Perm (Fin 3) ≃ { x : OrdTri // toT x = T } :=
          Equiv.ofBijective (fun σ : Equiv.Perm (Fin 3) =>
            let xσ : OrdTri := ⟨(arr (σ 0), arr (σ 1), arr (σ 2)),
              fun h => by have := σ.injective (harr_inj h); simp at this,
              fun h => by have := σ.injective (harr_inj h); simp at this,
              fun h => by have := σ.injective (harr_inj h); simp at this,
              T.prop.2.2 _ (harr_mem _) _ (harr_mem _),
              T.prop.2.2 _ (harr_mem _) _ (harr_mem _),
              T.prop.2.2 _ (harr_mem _) _ (harr_mem _)⟩
            ⟨xσ,
             Subtype.ext (by
               apply Finset.eq_of_subset_of_card_le
               · intro w hw; simp only [toT, xσ, Finset.mem_insert, Finset.mem_singleton] at hw
                 rcases hw with rfl | rfl | rfl <;> exact harr_mem _
               · have hT3 : T.val.card = 3 := T.prop.1
                 have hto3 : (toT xσ).val.card = 3 := (toT xσ).prop.1
                 omega)⟩)
            ⟨fun σ1 σ2 h => by
              have h0' : σ1 0 = σ2 0 := harr_inj (congrArg (fun z => z.val.val.1) h)
              have h1' : σ1 1 = σ2 1 := harr_inj (congrArg (fun z => z.val.val.2.1) h)
              have h2' : σ1 2 = σ2 2 := harr_inj (congrArg (fun z => z.val.val.2.2) h)
              refine Equiv.ext fun i => ?_
              fin_cases i; exact h0'; exact h1'; exact h2',
             fun x => by
              have hsub : ∀ w ∈ ({x.val.val.1.val, x.val.val.2.1.val, x.val.val.2.2.val} : Finset (UCCGVert p)),
                  ∃ i : Fin 3, (arr i).val = w := fun w hw => by
                have hwT : w ∈ T.val := by rw [← x.prop]; exact hw
                rw [hTeq] at hwT; simp only [Finset.mem_insert, Finset.mem_singleton] at hwT
                rcases hwT with rfl | rfl | rfl
                · exact ⟨0, rfl⟩
                · exact ⟨1, rfl⟩
                · exact ⟨2, rfl⟩
              obtain ⟨i0, hi0⟩ := hsub _ (Finset.mem_insert_self _ _)
              obtain ⟨i1, hi1⟩ := hsub _ (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
              obtain ⟨i2, hi2⟩ := hsub _ (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_singleton_self _)))
              have hi01 : i0 ≠ i1 := fun h => x.val.prop.1 (Subtype.ext (hi0.symm.trans (h ▸ hi1)))
              have hi02 : i0 ≠ i2 := fun h => x.val.prop.2.1 (Subtype.ext (hi0.symm.trans (h ▸ hi2)))
              have hi12 : i1 ≠ i2 := fun h => x.val.prop.2.2.1 (Subtype.ext (hi1.symm.trans (h ▸ hi2)))
              let f : Fin 3 → Fin 3 := ![i0, i1, i2]
              have hf_inj : Function.Injective f := by
                intro a b hab; fin_cases a <;> fin_cases b <;> simp [f] at hab ⊢
                all_goals first | rfl | exact absurd hab hi01 | exact absurd hab hi02 | exact absurd hab hi12 |
                                  exact absurd hab hi01.symm | exact absurd hab hi02.symm | exact absurd hab hi12.symm
              refine ⟨Equiv.ofBijective f (Finite.injective_iff_bijective.mp hf_inj),
                Subtype.ext (Subtype.ext (Prod.ext (Subtype.ext hi0) (Prod.ext (Subtype.ext hi1) (Subtype.ext hi2))))⟩⟩
        rw [← Fintype.card_subtype, ← Fintype.card_congr hbij6, Fintype.card_perm, Fintype.card_fin]; decide
      have h6Tri : Fintype.card OrdTri = 6 * Fintype.card Tri := by
        have hsum : Fintype.card OrdTri = ∑ T : Tri, (Finset.univ.filter fun x : OrdTri => toT x = T).card := by
          rw [← Finset.card_biUnion]
          · have : Finset.univ.biUnion (fun T : Tri => Finset.univ.filter fun x : OrdTri => toT x = T) = Finset.univ := by ext x; simp
            rw [this, Finset.card_univ]
          · intro T1 _ T2 _ hne; change Disjoint _ _; rw [Finset.disjoint_left]
            intro x h1 h2; exact hne (((Finset.mem_filter.mp h1).2).symm.trans (Finset.mem_filter.mp h2).2)
        simp_rw [hfib6] at hsum
        rw [Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_comm] at hsum; exact hsum
      -- 2. Count `|OrdTri| = |V_(B)| * p * (p + 1)` via Theorem 4.1 (`PG(2, p)`)!
      -- Given `(b0, b1)` distinct adjacent in `V_B`, there is a UNIQUE `b2 ∈ V_B` completing the triangle!
      -- And given `b0 = (P0, L0)` (`¬ P0 ≤ L0`), `b1 = (P1, L1)` is distinct & adjacent iff
      -- `P1 ≤ L0` (`p + 1` points!) AND `P0 ≤ L1` AND `¬ P1 ≤ L1` (`p` lines through `P0` not containing `P1`!)!
      obtain ⟨Φ, hΦB, _, hΦadj⟩ := theorem_4_1 p
      let OrdPair := { x : VertsOfType p .B × VertsOfType p .B // x.1 ≠ x.2 ∧ UCCGAdj x.1.val x.2.val }
      have : Fintype OrdPair := Fintype.ofFinite _
      have hPair_to_Tri : OrdTri ≃ OrdPair := by
        -- Drop `b2`: for any `(b0, b1) ∈ OrdPair`, `b2` is UNIQUE (`I - P0 - P1`)!
        let proj : OrdTri → OrdPair := fun x => ⟨(x.val.1, x.val.2.1), x.prop.1, x.prop.2.2.2.1⟩
        refine Equiv.ofBijective proj ⟨?_, ?_⟩
        · intro x y hEq
          have hb0 : x.val.1 = y.val.1 := congrArg (fun z => z.val.1) hEq
          have hb1 : x.val.2.1 = y.val.2.1 := congrArg (fun z => z.val.2) hEq
          -- Both `x.2.2` and `y.2.2` have `(P2, L2)` with `P2 = L0 ∩ L1` and `L2 = P0 ⊔ P1`!
          have hP2_eq : ∀ z : OrdTri,
              (Φ ⟨z.val.2.2.val, Or.inl z.val.2.2.prop⟩).1.val =
                (Φ ⟨z.val.1.val, Or.inl z.val.1.prop⟩).2.val ⊓ (Φ ⟨z.val.2.1.val, Or.inl z.val.2.1.prop⟩).2.val ∧
              (Φ ⟨z.val.2.2.val, Or.inl z.val.2.2.prop⟩).2.val =
                (Φ ⟨z.val.1.val, Or.inl z.val.1.prop⟩).1.val ⊔ (Φ ⟨z.val.2.1.val, Or.inl z.val.2.1.prop⟩).1.val := by
            intro z
            set x0 := Φ ⟨z.val.1.val, Or.inl z.val.1.prop⟩
            set x1 := Φ ⟨z.val.2.1.val, Or.inl z.val.2.1.prop⟩
            set x2 := Φ ⟨z.val.2.2.val, Or.inl z.val.2.2.prop⟩
            have hn0 := (hΦB ⟨z.val.1.val, Or.inl z.val.1.prop⟩).mp z.val.1.prop
            have hn1 := (hΦB ⟨z.val.2.1.val, Or.inl z.val.2.1.prop⟩).mp z.val.2.1.prop
            have hn2 := (hΦB ⟨z.val.2.2.val, Or.inl z.val.2.2.prop⟩).mp z.val.2.2.prop
            have hstep : ∀ {a b : VertsOfType p .B}, a ≠ b → UCCGAdj a.val b.val →
                (Φ ⟨a.val, Or.inl a.prop⟩).1.val ≠ (Φ ⟨b.val, Or.inl b.prop⟩).1.val ∧
                (Φ ⟨a.val, Or.inl a.prop⟩).2.val ≠ (Φ ⟨b.val, Or.inl b.prop⟩).2.val ∧
                (Φ ⟨a.val, Or.inl a.prop⟩).1.val ≤ (Φ ⟨b.val, Or.inl b.prop⟩).2.val ∧
                (Φ ⟨b.val, Or.inl b.prop⟩).1.val ≤ (Φ ⟨a.val, Or.inl a.prop⟩).2.val := by
              intro a b hab hadj
              have hna := (hΦB ⟨a.val, Or.inl a.prop⟩).mp a.prop
              have hnb := (hΦB ⟨b.val, Or.inl b.prop⟩).mp b.prop
              have hd := (hΦadj ⟨a.val, Or.inl a.prop⟩ ⟨b.val, Or.inl b.prop⟩).mp hadj
              rcases hd with ⟨hP, hL⟩ | ⟨h1, _, _⟩ | ⟨_, _, ⟨_, h2⟩, _⟩ | ⟨_, _, ⟨h1, _⟩, _⟩ | ⟨hP, hL, ⟨h12, _⟩, ⟨h21, _⟩⟩
              · have hval : a.val = b.val := congrArg (fun z : { w : UCCGVert p // VertHasType w .B ∨ VertHasType w .E } => z.val)
                  (Φ.injective (Prod.ext (Subtype.ext hP) (Subtype.ext hL)))
                exact absurd (Subtype.ext hval) hab
              · exact absurd h1 hna
              · exact absurd h2 hnb
              · exact absurd h1 hna
              · exact ⟨hP, hL, h12, h21⟩
            obtain ⟨hP01, hL01, h01, h10⟩ := hstep z.prop.1 z.prop.2.2.2.1
            obtain ⟨_, _, h02, h20⟩ := hstep z.prop.2.1 z.prop.2.2.2.2.1
            obtain ⟨_, _, h12, h21⟩ := hstep z.prop.2.2.1 z.prop.2.2.2.2.2
            constructor
            · have hle : x2.1.val ≤ x0.2.val ⊓ x1.2.val := le_inf h20 h21
              have hfr_inf : Module.finrank (ZMod p) ↥(x0.2.val ⊓ x1.2.val) = 1 := by
                have hsum := Submodule.finrank_sup_add_finrank_inf_eq x0.2.val x1.2.val
                have hsup_le : Module.finrank (ZMod p) ↥(x0.2.val ⊔ x1.2.val) ≤ 3 :=
                  (Submodule.finrank_le _).trans (by simp)
                have hne_sup : Module.finrank (ZMod p) ↥(x0.2.val ⊔ x1.2.val) ≠ 2 := fun h2 => by
                  have he1 := Submodule.eq_of_le_of_finrank_eq (le_sup_left : x0.2.val ≤ x0.2.val ⊔ x1.2.val) (by rw [x0.2.prop, h2])
                  have he2 := Submodule.eq_of_le_of_finrank_eq (le_sup_right : x1.2.val ≤ x0.2.val ⊔ x1.2.val) (by rw [x1.2.prop, h2])
                  exact hL01 (he1.trans he2.symm)
                have hge2 : 2 ≤ Module.finrank (ZMod p) ↥(x0.2.val ⊔ x1.2.val) := by
                  have := Submodule.finrank_mono (le_sup_left : x0.2.val ≤ x0.2.val ⊔ x1.2.val); rw [x0.2.prop] at this; exact this
                rw [x0.2.prop, x1.2.prop] at hsum; omega
              exact Submodule.eq_of_le_of_finrank_eq hle (by rw [x2.1.prop, hfr_inf])
            · have hle : x0.1.val ⊔ x1.1.val ≤ x2.2.val := sup_le h02 h12
              have hinf_bot : x0.1.val ⊓ x1.1.val = ⊥ := by
                by_contra hne
                obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
                have he1 : Submodule.span (ZMod p) ({v} : Set (V3 p)) = x0.1.val :=
                  Submodule.eq_of_le_of_finrank_eq (Submodule.span_le.mpr (Set.singleton_subset_iff.mpr hv.1)) (by rw [finrank_span_singleton hv0, x0.1.prop])
                have he2 : Submodule.span (ZMod p) ({v} : Set (V3 p)) = x1.1.val :=
                  Submodule.eq_of_le_of_finrank_eq (Submodule.span_le.mpr (Set.singleton_subset_iff.mpr hv.2)) (by rw [finrank_span_singleton hv0, x1.1.prop])
                exact hP01 (he1.symm.trans he2)
              have hfr_sup : Module.finrank (ZMod p) ↥(x0.1.val ⊔ x1.1.val) = 2 := by
                have hsum := Submodule.finrank_sup_add_finrank_inf_eq x0.1.val x1.1.val
                rw [hinf_bot, finrank_bot, add_zero, x0.1.prop, x1.1.prop] at hsum; exact hsum
              exact (Submodule.eq_of_le_of_finrank_eq hle (by rw [hfr_sup, x2.2.prop])).symm
          obtain ⟨hxP, hxL⟩ := hP2_eq x
          obtain ⟨hyP, hyL⟩ := hP2_eq y
          have hΦeq : Φ ⟨x.val.2.2.val, Or.inl x.val.2.2.prop⟩ = Φ ⟨y.val.2.2.val, Or.inl y.val.2.2.prop⟩ :=
            Prod.ext (Subtype.ext (hxP.trans (by rw [hb0, hb1]; exact hyP.symm)))
              (Subtype.ext (hxL.trans (by rw [hb0, hb1]; exact hyL.symm)))
          have hb2 : x.val.2.2 = y.val.2.2 := Subtype.ext (congrArg (fun z : { w : UCCGVert p // VertHasType w .B ∨ VertHasType w .E } => z.val) (Φ.injective hΦeq))
          exact Subtype.ext (Prod.ext hb0 (Prod.ext hb1 hb2))
        · intro pair
          set x0 := Φ ⟨pair.val.1.val, Or.inl pair.val.1.prop⟩
          set x1 := Φ ⟨pair.val.2.val, Or.inl pair.val.2.prop⟩
          have hn0 := (hΦB ⟨pair.val.1.val, Or.inl pair.val.1.prop⟩).mp pair.val.1.prop
          have hn1 := (hΦB ⟨pair.val.2.val, Or.inl pair.val.2.prop⟩).mp pair.val.2.prop
          have hd := (hΦadj ⟨pair.val.1.val, Or.inl pair.val.1.prop⟩ ⟨pair.val.2.val, Or.inl pair.val.2.prop⟩).mp pair.prop.2
          have ⟨hP01, hL01, h01, h10⟩ : x0.1.val ≠ x1.1.val ∧ x0.2.val ≠ x1.2.val ∧ x0.1.val ≤ x1.2.val ∧ x1.1.val ≤ x0.2.val := by
            rcases hd with ⟨hP, hL⟩ | ⟨h1, _, _⟩ | ⟨_, _, ⟨_, h2⟩, _⟩ | ⟨_, _, ⟨h1, _⟩, _⟩ | ⟨hP, hL, ⟨h12, _⟩, ⟨h21, _⟩⟩
            · have hval : pair.val.1.val = pair.val.2.val := congrArg (fun z : { w : UCCGVert p // VertHasType w .B ∨ VertHasType w .E } => z.val)
                (Φ.injective (Prod.ext (Subtype.ext hP) (Subtype.ext hL)))
              exact absurd (Subtype.ext hval) pair.prop.1
            · exact absurd h1 hn0
            · exact absurd h2 hn1
            · exact absurd h1 hn0
            · exact ⟨hP, hL, h12, h21⟩
          have hfr_inf : Module.finrank (ZMod p) ↥(x0.2.val ⊓ x1.2.val) = 1 := by
            have hsum := Submodule.finrank_sup_add_finrank_inf_eq x0.2.val x1.2.val
            have hsup_le : Module.finrank (ZMod p) ↥(x0.2.val ⊔ x1.2.val) ≤ 3 :=
              (Submodule.finrank_le _).trans (by simp)
            have hne_sup : Module.finrank (ZMod p) ↥(x0.2.val ⊔ x1.2.val) ≠ 2 := fun h2 => by
              have he1 := Submodule.eq_of_le_of_finrank_eq (le_sup_left : x0.2.val ≤ x0.2.val ⊔ x1.2.val) (by rw [x0.2.prop, h2])
              have he2 := Submodule.eq_of_le_of_finrank_eq (le_sup_right : x1.2.val ≤ x0.2.val ⊔ x1.2.val) (by rw [x1.2.prop, h2])
              exact hL01 (he1.trans he2.symm)
            have hge2 : 2 ≤ Module.finrank (ZMod p) ↥(x0.2.val ⊔ x1.2.val) := by
              have := Submodule.finrank_mono (le_sup_left : x0.2.val ≤ x0.2.val ⊔ x1.2.val); rw [x0.2.prop] at this; exact this
            rw [x0.2.prop, x1.2.prop] at hsum; omega
          have hinf_bot : x0.1.val ⊓ x1.1.val = ⊥ := by
            by_contra hne
            obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
            have he1 : Submodule.span (ZMod p) ({v} : Set (V3 p)) = x0.1.val :=
              Submodule.eq_of_le_of_finrank_eq (Submodule.span_le.mpr (Set.singleton_subset_iff.mpr hv.1)) (by rw [finrank_span_singleton hv0, x0.1.prop])
            have he2 : Submodule.span (ZMod p) ({v} : Set (V3 p)) = x1.1.val :=
              Submodule.eq_of_le_of_finrank_eq (Submodule.span_le.mpr (Set.singleton_subset_iff.mpr hv.2)) (by rw [finrank_span_singleton hv0, x1.1.prop])
            exact hP01 (he1.symm.trans he2)
          have hfr_sup : Module.finrank (ZMod p) ↥(x0.1.val ⊔ x1.1.val) = 2 := by
            have hsum := Submodule.finrank_sup_add_finrank_inf_eq x0.1.val x1.1.val
            rw [hinf_bot, finrank_bot, add_zero, x0.1.prop, x1.1.prop] at hsum; exact hsum
          let P2 : PGPoint p := ⟨x0.2.val ⊓ x1.2.val, hfr_inf⟩
          let L2 : PGLine p := ⟨x0.1.val ⊔ x1.1.val, hfr_sup⟩
          have hn2 : ¬ P2.val ≤ L2.val := by
            intro hle
            -- If `x0.2 ⊓ x1.2 ≤ x0.1 ⊔ x1.1`, pick nonzero `z ∈ x0.2 ⊓ x1.2`: `z = v0 + v1` with `v0 ∈ x0.1, v1 ∈ x1.1`.
            -- Since `z ∈ x0.2` and `v1 ∈ x1.1 ≤ x0.2`, `v0 = z - v1 ∈ x0.2`, so `v0 = 0` (since `¬ x0.1 ≤ x0.2`)!
            -- Similarly `v1 = 0`, contradicting `z ≠ 0`!
            have hne : P2.val ≠ ⊥ := fun h => by have := P2.prop; rw [h, finrank_bot] at this; omega
            obtain ⟨z, hz, hz0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
            have hz_sup : z ∈ x0.1.val ⊔ x1.1.val := hle hz
            obtain ⟨v0, hv0, v1, hv1, rfl⟩ := Submodule.mem_sup.mp hz_sup
            have hv0_in : v0 ∈ x0.2.val := by
              have : v0 = (v0 + v1) - v1 := by abel
              rw [this]; exact Submodule.sub_mem _ hz.1 (h10 hv1)
            have hv0_0 : v0 = 0 := by
              by_contra hne0
              apply hn0
              have hsp : x0.1.val = Submodule.span (ZMod p) ({v0} : Set (V3 p)) :=
                (Submodule.eq_of_le_of_finrank_eq (Submodule.span_le.mpr (Set.singleton_subset_iff.mpr hv0))
                  (by rw [finrank_span_singleton hne0, x0.1.prop])).symm
              rw [hsp, Submodule.span_le, Set.singleton_subset_iff]; exact hv0_in
            have hv1_in : v1 ∈ x1.2.val := by
              have : v1 = (v0 + v1) - v0 := by abel
              rw [this]; exact Submodule.sub_mem _ hz.2 (h01 hv0)
            have hv1_0 : v1 = 0 := by
              by_contra hne1
              apply hn1
              have hsp : x1.1.val = Submodule.span (ZMod p) ({v1} : Set (V3 p)) :=
                (Submodule.eq_of_le_of_finrank_eq (Submodule.span_le.mpr (Set.singleton_subset_iff.mpr hv1))
                  (by rw [finrank_span_singleton hne1, x1.1.prop])).symm
              rw [hsp, Submodule.span_le, Set.singleton_subset_iff]; exact hv1_in
            exact hz0 (by rw [hv0_0, hv1_0, add_zero])
          let v2 := Φ.symm (P2, L2)
          have hv2B : VertHasType v2.val .B := (hΦB v2).mpr (by simpa [v2] using hn2)
          have hadj02 : UCCGAdj pair.val.1.val v2.val := (hΦadj ⟨pair.val.1.val, Or.inl pair.val.1.prop⟩ v2).mpr (by
            rw [Φ.apply_symm_apply]
            exact Or.inr (Or.inr (Or.inr (Or.inr ⟨fun h => hn0 (h ▸ inf_le_left), fun h => hn0 (h ▸ le_sup_left),
              ⟨le_sup_left, hn0⟩, ⟨inf_le_left, hn2⟩⟩))))
          have hadj12 : UCCGAdj pair.val.2.val v2.val := (hΦadj ⟨pair.val.2.val, Or.inl pair.val.2.prop⟩ v2).mpr (by
            rw [Φ.apply_symm_apply]
            exact Or.inr (Or.inr (Or.inr (Or.inr ⟨fun h => hn1 (h ▸ inf_le_right), fun h => hn1 (h ▸ le_sup_right),
              ⟨le_sup_right, hn1⟩, ⟨inf_le_right, hn2⟩⟩))))
          have hne02 : pair.val.1 ≠ ⟨v2.val, hv2B⟩ := fun h => hn0 (by
            have h1 : x0 = (P2, L2) := by
              have : (⟨pair.val.1.val, Or.inl pair.val.1.prop⟩ : { w : UCCGVert p // VertHasType w .B ∨ VertHasType w .E }) = v2 :=
                Subtype.ext (congrArg (fun z : VertsOfType p .B => z.val) h)
              rw [show x0 = Φ ⟨pair.val.1.val, Or.inl pair.val.1.prop⟩ from rfl, this, Φ.apply_symm_apply]
            have := congrArg (fun z : PGPoint p × PGLine p => z.1.val) h1
            dsimp only [P2] at this; rw [this]; exact inf_le_left)
          have hne12 : pair.val.2 ≠ ⟨v2.val, hv2B⟩ := fun h => hn1 (by
            have h1 : x1 = (P2, L2) := by
              have : (⟨pair.val.2.val, Or.inl pair.val.2.prop⟩ : { w : UCCGVert p // VertHasType w .B ∨ VertHasType w .E }) = v2 :=
                Subtype.ext (congrArg (fun z : VertsOfType p .B => z.val) h)
              rw [show x1 = Φ ⟨pair.val.2.val, Or.inl pair.val.2.prop⟩ from rfl, this, Φ.apply_symm_apply]
            have := congrArg (fun z : PGPoint p × PGLine p => z.1.val) h1
            dsimp only [P2] at this; rw [this]; exact inf_le_right)
          exact ⟨⟨(pair.val.1, pair.val.2, ⟨v2.val, hv2B⟩), pair.prop.1, hne02, hne12, pair.prop.2, hadj02, hadj12⟩, rfl⟩
      -- 3. Count `|OrdPair| = |V_(B)| * (p + 1) * p`!
      have hB_nbrs : ∀ b0 : VertsOfType p .B,
          (Finset.univ.filter fun b1 : VertsOfType p .B => b0 ≠ b1 ∧ UCCGAdj b0.val b1.val).card = (p + 1) * p := by
        intro b0
        set x0 := Φ ⟨b0.val, Or.inl b0.prop⟩
        have hn0 := (hΦB ⟨b0.val, Or.inl b0.prop⟩).mp b0.prop
        -- Bijects with `{(P1, L1) | P1 ≤ x0.2 ∧ x0.1 ≤ L1 ∧ ¬ P1 ≤ L1}`!
        have : Finite (PGPoint p × PGLine p) := Finite.of_equiv _ Φ
        have : Finite (PGPoint p) := Finite.of_injective (fun P => (P, x0.2)) (fun _ _ h => congrArg Prod.fst h)
        have : Finite (PGLine p) := Finite.of_injective (fun L => (x0.1, L)) (fun _ _ h => congrArg Prod.snd h)
        have : Fintype (PGPoint p) := Fintype.ofFinite _
        have : Fintype (PGLine p) := Fintype.ofFinite _
        let S := { x1 : PGPoint p × PGLine p // x1.1.val ≤ x0.2.val ∧ x0.1.val ≤ x1.2.val ∧ ¬ x1.1.val ≤ x1.2.val }
        have hbij : { b1 : VertsOfType p .B // b0 ≠ b1 ∧ UCCGAdj b0.val b1.val } ≃ S :=
          Equiv.ofBijective (fun b1 =>
            ⟨Φ ⟨b1.val.val, Or.inl b1.val.prop⟩, by
              have hn1 := (hΦB ⟨b1.val.val, Or.inl b1.val.prop⟩).mp b1.val.prop
              have hd := (hΦadj ⟨b0.val, Or.inl b0.prop⟩ ⟨b1.val.val, Or.inl b1.val.prop⟩).mp b1.prop.2
              rcases hd with ⟨hP, hL⟩ | ⟨h1, _, _⟩ | ⟨_, _, ⟨_, h2⟩, _⟩ | ⟨_, _, ⟨h1, _⟩, _⟩ | ⟨_, _, ⟨h12, _⟩, ⟨h21, _⟩⟩
              · have hval : b0.val = b1.val.val := congrArg (fun z : { w : UCCGVert p // VertHasType w .B ∨ VertHasType w .E } => z.val)
                  (Φ.injective (Prod.ext (Subtype.ext hP) (Subtype.ext hL)))
                exact absurd (Subtype.ext hval) b1.prop.1
              · exact absurd h1 hn0
              · exact absurd h2 hn1
              · exact absurd h1 hn0
              · exact ⟨h21, h12, hn1⟩⟩)
            ⟨fun a b h => Subtype.ext (Subtype.ext (congrArg (fun z : { w : UCCGVert p // VertHasType w .B ∨ VertHasType w .E } => z.val)
                (Φ.injective (congrArg Subtype.val h)))),
             fun x1 => by
              let v1 := Φ.symm x1.val
              have hv1B : VertHasType v1.val .B := (hΦB v1).mpr (by simpa [v1] using x1.prop.2.2)
              have hne : b0 ≠ ⟨v1.val, hv1B⟩ := fun h => hn0 (by
                have h1 : Φ ⟨b0.val, Or.inl b0.prop⟩ = x1.val := by
                  have hsub : (⟨b0.val, Or.inl b0.prop⟩ : { w : UCCGVert p // VertHasType w .B ∨ VertHasType w .E }) = v1 :=
                    Subtype.ext (congrArg (fun z : VertsOfType p .B => z.val) h)
                  rw [hsub, Φ.apply_symm_apply]
                have h2 : x0.1.val = x1.val.1.val := congrArg (fun z : PGPoint p × PGLine p => z.1.val) h1
                rw [h2]; exact x1.prop.1)
              have hadj : UCCGAdj b0.val v1.val := (hΦadj ⟨b0.val, Or.inl b0.prop⟩ v1).mpr (by
                rw [Φ.apply_symm_apply]
                exact Or.inr (Or.inr (Or.inr (Or.inr ⟨fun h => hn0 (h ▸ x1.prop.1), fun h => hn0 (h ▸ x1.prop.2.1),
                  ⟨x1.prop.2.1, hn0⟩, ⟨x1.prop.1, x1.prop.2.2⟩⟩))))
              refine ⟨⟨⟨v1.val, hv1B⟩, hne, hadj⟩, Subtype.ext ?_⟩
              dsimp only
              have hv_eq : (⟨v1.val, Or.inl hv1B⟩ : { w : UCCGVert p // VertHasType w .B ∨ VertHasType w .E }) = v1 := Subtype.ext rfl
              rw [hv_eq, Φ.apply_symm_apply]⟩
        rw [← Fintype.card_subtype, Fintype.card_congr hbij, Fintype.card_subtype]
        have hsum : (Finset.univ.filter fun x1 : PGPoint p × PGLine p =>
            x1.1.val ≤ x0.2.val ∧ x0.1.val ≤ x1.2.val ∧ ¬ x1.1.val ≤ x1.2.val).card =
            ∑ P1 ∈ Finset.univ.filter (fun P1 : PGPoint p => P1.val ≤ x0.2.val),
              (Finset.univ.filter fun L1 : PGLine p => x0.1.val ≤ L1.val ∧ ¬ P1.val ≤ L1.val).card := by
          rw [Finset.card_filter, Fintype.sum_prod_type]
          rw [Finset.sum_filter]
          refine Finset.sum_congr rfl fun P1 _ => ?_
          by_cases hP : P1.val ≤ x0.2.val
          · rw [if_pos hP, Finset.card_filter]
            refine Finset.sum_congr rfl fun L1 _ => by simp [hP]
          · simp [hP]
        rw [hsum]
        have hlines_through : ∀ P : PGPoint p, (Finset.univ.filter fun L : PGLine p => P.val ≤ L.val).card = p + 1 := fun P => by
          -- Duality `L ↦ orthoSub L`: `P ≤ L ↔ orthoSub L ≤ orthoSub P`!
          let Ldual : PGLine p := ⟨orthoSub P.val, finrank_orthoSub_point P⟩
          have hbijL : { L : PGLine p // P.val ≤ L.val } ≃ { Q : PGPoint p // Q.val ≤ Ldual.val } :=
            { toFun := fun L => ⟨⟨orthoSub L.val.val, finrank_orthoSub_line L.val⟩, fun v hv w hw => hv w (L.prop hw)⟩
              invFun := fun Q => ⟨⟨orthoSub Q.val.val, finrank_orthoSub_point Q.val⟩, fun w hw v hv => by
                rw [dotProduct_comm]; exact Q.prop hv w hw⟩
              left_inv := fun L => Subtype.ext (Subtype.ext (orthoSub_orthoSub L.val.val (Or.inr L.val.prop)))
              right_inv := fun Q => Subtype.ext (Subtype.ext (orthoSub_orthoSub Q.val.val (Or.inl Q.val.prop))) }
          rw [← Fintype.card_subtype, Fintype.card_congr hbijL, ← Nat.card_eq_fintype_card, card_points_on_line Ldual]
        have hinner : ∀ P1 ∈ Finset.univ.filter (fun P1 : PGPoint p => P1.val ≤ x0.2.val),
            (Finset.univ.filter fun L1 : PGLine p => x0.1.val ≤ L1.val ∧ ¬ P1.val ≤ L1.val).card = p := by
          intro P1 hP1
          have hP1le : P1.val ≤ x0.2.val := (Finset.mem_filter.mp hP1).2
          have hneP : x0.1.val ≠ P1.val := fun h => hn0 (h ▸ hP1le)
          have hinf : x0.1.val ⊓ P1.val = ⊥ := by
            by_contra hne
            obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
            have h1 : Submodule.span (ZMod p) ({v} : Set (V3 p)) = x0.1.val :=
              Submodule.eq_of_le_of_finrank_eq (Submodule.span_le.mpr (Set.singleton_subset_iff.mpr hv.1)) (by rw [finrank_span_singleton hv0, x0.1.prop])
            have h2 : Submodule.span (ZMod p) ({v} : Set (V3 p)) = P1.val :=
              Submodule.eq_of_le_of_finrank_eq (Submodule.span_le.mpr (Set.singleton_subset_iff.mpr hv.2)) (by rw [finrank_span_singleton hv0, P1.prop])
            exact hneP (h1.symm.trans h2)
          have hfr : Module.finrank (ZMod p) ↥(x0.1.val ⊔ P1.val) = 2 := by
            have h := Submodule.finrank_sup_add_finrank_inf_eq x0.1.val P1.val
            rw [hinf, finrank_bot, add_zero, x0.1.prop, P1.prop] at h; exact h
          let Ljoin : PGLine p := ⟨x0.1.val ⊔ P1.val, hfr⟩
          have hEq : (Finset.univ.filter fun L1 : PGLine p => x0.1.val ≤ L1.val ∧ ¬ P1.val ≤ L1.val) =
              (Finset.univ.filter fun L1 : PGLine p => x0.1.val ≤ L1.val).erase Ljoin := by
            ext L1; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase]
            constructor
            · rintro ⟨h1, h2⟩; exact ⟨fun h => h2 (h ▸ le_sup_right), h1⟩
            · rintro ⟨hneL, h1⟩
              refine ⟨h1, fun h2 => hneL (Subtype.ext ?_)⟩
              exact (Submodule.eq_of_le_of_finrank_eq (sup_le h1 h2) (by rw [hfr, L1.prop])).symm
          have hLjoin_mem : Ljoin ∈ Finset.univ.filter (fun L1 : PGLine p => x0.1.val ≤ L1.val) :=
            Finset.mem_filter.mpr ⟨Finset.mem_univ Ljoin, le_sup_left⟩
          rw [hEq, Finset.card_erase_of_mem hLjoin_mem, hlines_through x0.1]; omega
        rw [Finset.sum_congr rfl hinner, Finset.sum_const, smul_eq_mul]
        have hP_card : (Finset.univ.filter fun P1 : PGPoint p => P1.val ≤ x0.2.val).card = p + 1 := by
          have := card_points_on_line x0.2
          rwa [Nat.card_eq_fintype_card, Fintype.card_subtype] at this
        rw [hP_card]
      have hOrdPair_card : Fintype.card OrdPair = (p ^ 2 + p + 1) * p ^ 2 * ((p + 1) * p) := by
        rw [Fintype.card_subtype]
        have hsum : (Finset.univ.filter fun x : VertsOfType p .B × VertsOfType p .B => x.1 ≠ x.2 ∧ UCCGAdj x.1.val x.2.val).card =
            ∑ b0 : VertsOfType p .B, (Finset.univ.filter fun b1 : VertsOfType p .B => b0 ≠ b1 ∧ UCCGAdj b0.val b1.val).card := by
          rw [Finset.card_filter, Fintype.sum_prod_type]
          refine Finset.sum_congr rfl fun b0 _ => (Finset.card_filter _ _).symm
        rw [hsum]; simp_rw [hB_nbrs]
        rw [Finset.sum_const, Finset.card_univ, smul_eq_mul, ← Nat.card_eq_fintype_card, (card_verts_B_E p).1]
      rw [Nat.card_eq_fintype_card]
      have h6eq : 6 * Fintype.card Tri = (p ^ 2 + p + 1) * p ^ 3 * (p + 1) := by
        rw [← h6Tri, Fintype.card_congr hPair_to_Tri, hOrdPair_card]; ring
      rw [← h6eq, Nat.mul_div_cancel_left _ (by omega)]
  exact ⟨hC_noE, hC_bij, hC_card⟩

/-- Count `|V_(G)|` by subtracting all other 7 types from `|M_3(ZMod p)| = p^9`! -/
private lemma card_verts_G (p : ℕ) [Fact p.Prime] :
    Nat.card (VertsOfType p .G) = (p ^ 3 - p) * (p ^ 3 - p ^ 2) / 3 := by
  classical
  have : Fintype (UCCGVert p) := Fintype.ofFinite _
  have hp2 : 2 ≤ p := (Fact.out : p.Prime).two_le
  -- Partition `M3 p` by vertex `v` and then by type `t : M3Type`!
  have hsum_all : p ^ 9 = ∑ t : M3Type, Nat.card (VertsOfType p t) * expectedGenCount p t := by
    have hM3 : Fintype.card (M3 p) = p ^ 9 := by
      change Fintype.card (Fin 3 → Fin 3 → ZMod p) = p ^ 9
      simp [ZMod.card]; ring
    have hpart_v : Fintype.card (M3 p) = ∑ v : UCCGVert p, Nat.card (SingleGens v) := by
      rw [← Finset.card_univ]
      have hbi : (Finset.univ : Finset (M3 p)) =
          Finset.univ.biUnion (fun v : UCCGVert p => Finset.univ.filter fun A : M3 p => A ∈ SingleGens v) := by
        ext A; simp only [Finset.mem_univ, Finset.mem_biUnion, Finset.mem_filter, true_and, true_iff]
        exact ⟨⟨Subring.closure ({A} : Set (M3 p)), ⟨A, rfl⟩⟩, rfl⟩
      rw [hbi, Finset.card_biUnion]
      · refine Finset.sum_congr rfl fun v _ => ?_
        rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
      · intro v1 _ v2 _ hne; change Disjoint _ _; rw [Finset.disjoint_left]
        intro A h1 h2; exact hne (Subtype.ext (((Finset.mem_filter.mp h1).2).symm.trans (Finset.mem_filter.mp h2).2))
    have hpart_t : (∑ v : UCCGVert p, Nat.card (SingleGens v)) =
        ∑ t : M3Type, ∑ v ∈ Finset.univ.filter (fun v : UCCGVert p => VertHasType v t), Nat.card (SingleGens v) := by
      rw [← Finset.sum_biUnion]
      · congr 1; ext v; simp only [Finset.mem_univ, Finset.mem_biUnion, Finset.mem_filter, true_and, true_iff]
        obtain ⟨A, hAv⟩ := v.prop
        obtain ⟨t, ht⟩ := exists_hasM3Type A
        exact ⟨t, A, hAv.symm, ht⟩
      · intro t1 _ t2 _ hne; change Disjoint _ _; rw [Finset.disjoint_left]
        intro v h1 h2; exact hne (vertHasType_unique (Finset.mem_filter.mp h1).2 (Finset.mem_filter.mp h2).2)
    rw [← hM3, hpart_v, hpart_t]
    refine Finset.sum_congr rfl fun t _ => ?_
    have hconst : ∀ v ∈ Finset.univ.filter (fun v : UCCGVert p => VertHasType v t),
        Nat.card (SingleGens v) = expectedGenCount p t := fun v hv =>
      card_singleGens_of_type t v (Finset.mem_filter.mp hv).2
    rw [Finset.sum_congr rfl hconst, Finset.sum_const, smul_eq_mul, ← Fintype.card_subtype, ← Nat.card_eq_fintype_card]
    rfl
  have hsum_expand : (∑ t : M3Type, Nat.card (VertsOfType p t) * expectedGenCount p t) =
      Nat.card (VertsOfType p .A) * expectedGenCount p .A +
      Nat.card (VertsOfType p .B) * expectedGenCount p .B +
      Nat.card (VertsOfType p .C) * expectedGenCount p .C +
      Nat.card (VertsOfType p .D) * expectedGenCount p .D +
      Nat.card (VertsOfType p .E) * expectedGenCount p .E +
      Nat.card (VertsOfType p .F) * expectedGenCount p .F +
      Nat.card (VertsOfType p .G) * expectedGenCount p .G +
      Nat.card (VertsOfType p .H) * expectedGenCount p .H := by
    have huniv : (Finset.univ : Finset M3Type) = {.A, .B, .C, .D, .E, .F, .G, .H} := by
      ext t; cases t <;> simp
    rw [huniv]
    simp [Finset.sum_insert, add_assoc]
  rw [hsum_expand, card_verts_A p, (card_verts_B_E p).1, (card_verts_B_E p).2,
      (section5_C p).2.2, (section5_D p).2.2, (section5_F p).2, (section5_H p).2.2] at hsum_all
  -- Algebraic identity in `ℤ` (valid for both `p = 2` and `p ≥ 3`)!
  have hdiv6 : 6 ∣ (p ^ 2 + p + 1) * p ^ 3 * (p + 1) := by
    have h2 : 2 ∣ p * (p + 1) := by rcases Nat.even_or_odd p with ⟨k, rfl⟩ | ⟨k, rfl⟩ <;> [exact ⟨k * (2*k+1), by ring⟩; exact ⟨(2*k+1)*(k+1), by ring⟩]
    have h3 : 3 ∣ (p ^ 2 + p + 1) * p * (p + 1) := by
      have hm : p % 3 = 0 ∨ p % 3 = 1 ∨ p % 3 = 2 := by omega
      rcases hm with h | h | h
      · exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_right (Nat.dvd_of_mod_eq_zero h) _) _
      · have : 3 ∣ p ^ 2 + p + 1 := by
          obtain ⟨q, rfl⟩ : ∃ q, p = 3 * q + 1 := ⟨p / 3, by omega⟩
          exact ⟨3 * q ^ 2 + 3 * q + 1, by ring⟩
        exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left this _) _
      · have : 3 ∣ p + 1 := by omega
        exact dvd_mul_of_dvd_right this _
    have h2' : 2 ∣ (p ^ 2 + p + 1) * p ^ 3 * (p + 1) := by
      obtain ⟨k, hk⟩ := h2
      exact ⟨(p ^ 2 + p + 1) * p ^ 2 * k, by calc (p ^ 2 + p + 1) * p ^ 3 * (p + 1) = (p ^ 2 + p + 1) * p ^ 2 * (p * (p + 1)) := by ring
        _ = 2 * ((p ^ 2 + p + 1) * p ^ 2 * k) := by rw [hk]; ring⟩
    have h3' : 3 ∣ (p ^ 2 + p + 1) * p ^ 3 * (p + 1) := by
      obtain ⟨k, hk⟩ := h3
      exact ⟨p ^ 2 * k, by calc (p ^ 2 + p + 1) * p ^ 3 * (p + 1) = p ^ 2 * ((p ^ 2 + p + 1) * p * (p + 1)) := by ring
        _ = 3 * (p ^ 2 * k) := by rw [hk]; ring⟩
    exact Nat.Coprime.mul_dvd_of_dvd_of_dvd (by decide) h2' h3'
  have hdiv2 : 2 ∣ (p ^ 3 - 1) * p ^ 3 := by
    rcases Nat.even_or_odd p with ⟨k, rfl⟩ | ⟨k, rfl⟩
    · have hk1 : 1 ≤ (2 * k) ^ 3 := Nat.one_le_pow 3 (2 * k) (by omega)
      exact ⟨(8 * k ^ 3 - 1) * 4 * k ^ 3, by zify [hk1]; ring⟩
    · have : 2 ∣ (2 * k + 1) ^ 3 - 1 := by
        refine ⟨4 * k ^ 3 + 6 * k ^ 2 + 3 * k, ?_⟩
        zify [Nat.one_le_pow 3 (2 * k + 1) (by omega)]; ring
      exact dvd_mul_of_dvd_left this _
  have hdiv3 : 3 ∣ (p ^ 3 - p) * (p ^ 3 - p ^ 2) := by
    have : 3 ∣ p ^ 3 - p := by
      have hm : p % 3 = 0 ∨ p % 3 = 1 ∨ p % 3 = 2 := by omega
      have h1 : p ^ 3 - p = p * (p - 1) * (p + 1) := by zify [show 1 ≤ p by omega, show p ≤ p ^ 3 by exact Nat.le_self_pow (by omega) p]; ring
      rw [h1]
      rcases hm with h | h | h
      · exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (Nat.dvd_of_mod_eq_zero h) _) _
      · exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_right (by omega) _) _
      · exact dvd_mul_of_dvd_right (by omega) _
    exact dvd_mul_of_dvd_left this _
  have hC_term : expectedVertCount p .C * expectedGenCount p .C =
      ((p ^ 2 + p + 1) * p ^ 3 * (p + 1) / 6) * (p * (p - 1) * (p - 2)) := by
    dsimp only [expectedVertCount, expectedGenCount]
    by_cases h2 : p = 2
    · subst h2; simp
    · simp [h2]
  have hG_mul' : Nat.card (VertsOfType p .G) * (p ^ 3 - p) =
      ((p ^ 3 - p) * (p ^ 3 - p ^ 2) / 3) * (p ^ 3 - p) := by
    rw [hC_term] at hsum_all
    dsimp only [expectedGenCount] at hsum_all
    obtain ⟨c6, hc6⟩ := hdiv6
    obtain ⟨c2, hc2⟩ := hdiv2
    obtain ⟨c3, hc3⟩ := hdiv3
    have h6q : (p ^ 2 + p + 1) * p ^ 3 * (p + 1) / 6 = c6 := by rw [hc6, Nat.mul_div_cancel_left _ (by omega)]
    have h2q : (p ^ 3 - 1) * p ^ 3 / 2 = c2 := by rw [hc2, Nat.mul_div_cancel_left _ (by omega)]
    have h3q : (p ^ 3 - p) * (p ^ 3 - p ^ 2) / 3 = c3 := by rw [hc3, Nat.mul_div_cancel_left _ (by omega)]
    rw [h6q, h2q] at hsum_all
    rw [h3q]
    have hle_p3 : p ≤ p ^ 3 := Nat.le_self_pow (by omega) p
    have hle_p23 : p ^ 2 ≤ p ^ 3 := Nat.pow_le_pow_right (by omega) (by omega)
    have hle_13 : 1 ≤ p ^ 3 := Nat.one_le_pow 3 p (by omega)
    have h6z : 6 * (Nat.card (VertsOfType p .G) * (p ^ 3 - p) : ℤ) = 6 * (c3 * (p ^ 3 - p) : ℤ) := by
      zify [show 1 ≤ p by omega, show 2 ≤ p by omega, hle_p3, hle_p23, hle_13] at hsum_all hc6 hc2 hc3 ⊢
      linear_combination -6 * hsum_all + (p : ℤ) * ((p : ℤ) - 1) * ((p : ℤ) - 2) * hc6 +
        3 * (p : ℤ) ^ 2 * ((p : ℤ) - 1) * hc2 + 2 * ((p : ℤ) ^ 3 - (p : ℤ)) * hc3
    have hz : (Nat.card (VertsOfType p .G) * (p ^ 3 - p) : ℤ) = (c3 * (p ^ 3 - p) : ℤ) := by omega
    exact_mod_cast hz
  have hpos : 0 < p ^ 3 - p := by
    have : p < p ^ 3 := lt_of_lt_of_le (show p < p * p by nlinarith) (by nlinarith)
    omega
  exact Nat.eq_of_mul_eq_mul_right hpos hG_mul'

/-! ### Section 7: Ordinary Commuting Graph `Γ(M_3(GF(p)))` Blow-Up & Main Theorem -/

private lemma central_iff_type_A {p : ℕ} [Fact p.Prime] (A : M3 p) :
    (∀ B : M3 p, A * B = B * A) ↔ HasM3Type A .A := by
  constructor
  · intro hcen
    -- Commuting with `matB0 p` and `E_{11}` forces `A` diagonal; commuting with `E_{01}, E_{12}` forces scalar!
    have h01 : A 0 1 = 0 := by have := congrArg (fun M : M3 p => M 0 1) (hcen (matB0 p)); simp [matB0, Matrix.mul_apply, Fin.sum_univ_three] at this; exact this.symm
    have h02 : A 0 2 = 0 := by have := congrArg (fun M : M3 p => M 0 2) (hcen (matB0 p)); simp [matB0, Matrix.mul_apply, Fin.sum_univ_three] at this; exact this.symm
    have h10 : A 1 0 = 0 := by have := congrArg (fun M : M3 p => M 1 0) (hcen (matB0 p)); simp [matB0, Matrix.mul_apply, Fin.sum_univ_three] at this; exact this
    have h20 : A 2 0 = 0 := by have := congrArg (fun M : M3 p => M 2 0) (hcen (matB0 p)); simp [matB0, Matrix.mul_apply, Fin.sum_univ_three] at this; exact this
    have h12 : A 1 2 = 0 := by
      have := congrArg (fun M : M3 p => M 1 2) (hcen !![0, 0, 0; 0, 1, 0; 0, 0, 0])
      simp [Matrix.mul_apply, Fin.sum_univ_three] at this; exact this.symm
    have h21 : A 2 1 = 0 := by
      have := congrArg (fun M : M3 p => M 2 1) (hcen !![0, 0, 0; 0, 1, 0; 0, 0, 0])
      simp [Matrix.mul_apply, Fin.sum_univ_three] at this; exact this
    have h00_11 : A 0 0 = A 1 1 := by
      have := congrArg (fun M : M3 p => M 0 1) (hcen (matE01 p))
      simp [matE01, Matrix.mul_apply, Fin.sum_univ_three] at this; exact this
    have h11_22 : A 1 1 = A 2 2 := by
      have := congrArg (fun M : M3 p => M 1 2) (hcen !![0, 0, 0; 0, 0, 1; 0, 0, 0])
      simp [Matrix.mul_apply, Fin.sum_univ_three] at this; exact this
    set c := A 0 0
    have hA_eq : A = c • (1 : M3 p) := by
      ext i j; fin_cases i <;> fin_cases j <;> simp [c, h01, h02, h10, h20, h12, h21, h00_11, h11_22]
    exact ⟨c, hA_eq ▸ charpoly_smul_one c, hA_eq ▸ minpoly_smul_one c⟩
  · rintro ⟨l, _, hm⟩ B
    have hA : A = l • (1 : M3 p) := by
      have := minpoly.aeval (ZMod p) A
      rw [hm, map_sub, aeval_X, aeval_C, Algebra.algebraMap_eq_smul_one, sub_eq_zero] at this
      exact this
    rw [hA, smul_mul_assoc, mul_smul_comm, one_mul, mul_one]

theorem main_proof : type_of% @OMA.S_arxiv_2602_07467.main := by
  intro p _
  refine ⟨⟨existsUnique_hasM3Type, fun A B hAB => same_type_of_subring_eq hAB, ?_, card_singleGens_of_type⟩,
    theorem_4_1 p, ?_, ?_⟩
  · intro t
    cases t with
    | A => exact card_verts_A p
    | B => exact (card_verts_B_E p).1
    | C => exact (section5_C p).2.2
    | D => exact (section5_D p).2.2
    | E => exact (card_verts_B_E p).2
    | F => exact (section5_F p).2
    | G => exact card_verts_G p
    | H => exact (section5_H p).2.2
  · exact ⟨fun v hv => adj_of_type_A hv,
      fun v₁ v₂ hne h1 h2 => nonderog_no_cross_edges hne h1 h2,
      fun v hv => adj_G_iff hv,
      (section5_C p).1, (section5_C p).2.1,
      (section5_F p).1,
      (section5_H p).1, (section5_H p).2.1,
      (section5_D p).1, (section5_D p).2.1⟩
  · refine ⟨central_iff_type_A, ?_, ?_⟩
    · intro A B
      simp only [CommAdj]
      rw [uccgAdj_iff_comm (v₁ := ⟨Subring.closure {A.val}, ⟨A.val, rfl⟩⟩)
            (v₂ := ⟨Subring.closure {B.val}, ⟨B.val, rfl⟩⟩) rfl rfl]
    · intro v hv A B hAv hAB
      have hadj : UCCGAdj v ⟨Subring.closure {B.val}, ⟨B.val, rfl⟩⟩ :=
        (uccgAdj_iff_comm hAv rfl).mpr hAB.2
      rcases (adj_G_iff hv _).mp hadj with hEq | hBA
      · exact congrArg Subtype.val hEq
      · exfalso
        have hBA' : HasM3Type B.val .A := (vertHasType_iff_all.mp hBA) B.val rfl
        exact B.prop ((central_iff_type_A B.val).mpr hBA')

end OMA.P_arxiv_2602_07467

theorem OMA.solution : type_of% @OMA.S_arxiv_2602_07467.main :=
  OMA.P_arxiv_2602_07467.main_proof
