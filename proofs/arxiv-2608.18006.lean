import OMAStatements.S_arxiv_2608_18006
import Mathlib

namespace OMA.P_arxiv_2608_18006

open OMA.S_arxiv_2608_18006

/-! ### General homogeneous degree-2 coefficient extraction -/

private def mdeg {n : ℕ} (d : Fin n →₀ ℕ) : ℕ :=
  d.sum (fun _ k => k)

private lemma mdeg_add {n : ℕ} (a b : Fin n →₀ ℕ) : mdeg (a + b) = mdeg a + mdeg b := by
  unfold mdeg
  exact Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl)

private lemma mdeg_eq_zero_iff {n : ℕ} (a : Fin n →₀ ℕ) : mdeg a = 0 ↔ a = 0 := by
  constructor
  · intro h
    ext j
    have hj : a j ≤ mdeg a := by
      by_cases hmem : j ∈ a.support
      · exact Finset.single_le_sum (f := fun i => a i) (fun _ _ => Nat.zero_le _) hmem
      · simp [Finsupp.notMem_support_iff.mp hmem]
    simp only [Finsupp.zero_apply]
    omega
  · intro h; subst h; simp [mdeg]

private lemma mdeg_single {n : ℕ} (j : Fin n) (k : ℕ) : mdeg (Finsupp.single j k) = k := by
  unfold mdeg
  exact Finsupp.sum_single_index rfl

private lemma coeff_mul_of_deg_ge {n : ℕ} (q g : MvPolynomial (Fin n) ℂ) (d0 : Fin n →₀ ℕ)
    (hd0 : mdeg d0 = 2) (hg : ∀ d ∈ g.support, 2 ≤ mdeg d) :
    MvPolynomial.coeff d0 (q * g) = MvPolynomial.coeff 0 q * MvPolynomial.coeff d0 g := by
  rw [MvPolynomial.coeff_mul]
  rw [Finset.sum_eq_single ((0 : Fin n →₀ ℕ), d0)]
  · rintro ⟨a, b⟩ hab hne
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hab
    by_cases hbg : b ∈ g.support
    · have hb2 : 2 ≤ mdeg b := hg b hbg
      have hsum : mdeg a + mdeg b = 2 := by rw [← mdeg_add, hab, hd0]
      have ha0 : a = 0 := (mdeg_eq_zero_iff a).mp (by omega)
      subst ha0
      rw [zero_add] at hab
      subst hab
      exact absurd rfl hne
    · rw [MvPolynomial.notMem_support_iff.mp hbg, mul_zero]
  · intro hnot
    exfalso
    exact hnot (Finset.HasAntidiagonal.mem_antidiagonal.mpr (zero_add d0))

private lemma monom_eq_monomial {n : ℕ} (S : Finset (Fin n)) :
    monom S = MvPolynomial.monomial (∑ j ∈ S, Finsupp.single j 1) (1 : ℂ) := by
  unfold monom
  induction S using Finset.cons_induction with
  | empty => simp [MvPolynomial.monomial_zero']
  | cons a s ha ih =>
    rw [Finset.prod_cons, Finset.sum_cons, ih, MvPolynomial.X, MvPolynomial.monomial_mul, one_mul]

private lemma mdeg_sum_single {n : ℕ} (S : Finset (Fin n)) :
    mdeg (∑ j ∈ S, Finsupp.single j 1) = S.card := by
  induction S using Finset.cons_induction with
  | empty => simp [mdeg]
  | cons a s ha ih =>
    rw [Finset.sum_cons, mdeg_add, mdeg_single, ih, Finset.card_cons]; omega

private lemma mdeg_monom_ge {n : ℕ} (S : Finset (Fin n)) (k : ℕ) (hk : k ≤ S.card) :
    ∀ d ∈ (monom S).support, k ≤ mdeg d := by
  rw [monom_eq_monomial]
  intro d hd
  have hdeq : d = ∑ j ∈ S, Finsupp.single j 1 := by
    by_contra hne
    have : MvPolynomial.coeff d (MvPolynomial.monomial (∑ j ∈ S, Finsupp.single j 1) (1 : ℂ)) = 0 := by
      rw [MvPolynomial.coeff_monomial, if_neg (Ne.symm hne)]
    exact (MvPolynomial.mem_support_iff.mp hd) this
  rw [hdeq, mdeg_sum_single]
  exact hk

private lemma linear_mul_monom_deg_ge {n : ℕ} (c : Fin n → ℂ) (S : Finset (Fin n))
    (k : ℕ) (hk : k ≤ S.card) :
    ∀ d ∈ ((∑ j : Fin n, c j • MvPolynomial.X j) * monom S).support, k + 1 ≤ mdeg d := by
  intro d hd
  rw [MvPolynomial.mem_support_iff, Finset.sum_mul, MvPolynomial.coeff_sum] at hd
  have hex : ∃ j : Fin n, MvPolynomial.coeff d ((c j • MvPolynomial.X j) * monom S) ≠ 0 := by
    by_contra hall
    push Not at hall
    exact hd (Finset.sum_eq_zero (fun j _ => hall j))
  obtain ⟨j, hj⟩ := hex
  rw [smul_mul_assoc, MvPolynomial.coeff_smul, smul_eq_mul] at hj
  have hj' : MvPolynomial.coeff d (MvPolynomial.X j * monom S) ≠ 0 :=
    right_ne_zero_of_mul hj
  rw [monom_eq_monomial, MvPolynomial.X, MvPolynomial.monomial_mul, one_mul,
    MvPolynomial.coeff_monomial] at hj'
  split_ifs at hj' with hdeq
  · rw [← hdeq, mdeg_add, mdeg_single, mdeg_sum_single]
    omega
  · exact absurd rfl hj'

private lemma linear_form_vanish_ideal {n : ℕ}
    (φ : MvPolynomial (Fin n) ℂ →ₗ[ℂ] ℂ)
    (hdeg2 : ∀ (q g : MvPolynomial (Fin n) ℂ),
      (∀ d ∈ g.support, 2 ≤ mdeg d) → φ (q * g) = MvPolynomial.coeff 0 q * φ g)
    (S : Set (MvPolynomial (Fin n) ℂ))
    (hS : ∀ g ∈ S, (∀ d ∈ g.support, 2 ≤ mdeg d) ∧ φ g = 0) :
    ∀ p ∈ Ideal.span S, φ p = 0 := by
  intro p hp
  have hall : ∀ q : MvPolynomial (Fin n) ℂ, φ (q * p) = 0 := by
    refine Submodule.span_induction (p := fun x _ => ∀ q, φ (q * x) = 0) ?_ ?_ ?_ ?_ hp
    · intro g hg q
      rw [hdeg2 q g (hS g hg).1, (hS g hg).2, mul_zero]
    · intro q; rw [mul_zero, map_zero]
    · intro x y _ _ hx hy q; rw [mul_add, map_add, hx q, hy q, add_zero]
    · intro a x _ ih q
      change φ (q * (a * x)) = 0
      rw [← mul_assoc]
      exact ih (q * a)
  simpa using hall 1

/-! ### Part 1: Lattice rank 1 ordered counterexample (Theorem 6.1 of arXiv:2608.18006) -/

private def A1 : Matrix (Fin 4) (Fin 5) ℤ :=
  ![![1, 1, 1, 1, 1],
    ![2, 1, 0, 0, 0],
    ![2, 0, 1, 0, 0],
    ![-1, 0, 0, 1, 0]]

private def B1 : Matrix (Fin 5) (Fin 1) ℤ :=
  ![![1], ![-2], ![-2], ![1], ![2]]

private def w1 : Fin 5 → ℝ :=
  ![1, 0, 0, 0, 0]

private def v1 : Fin 5 → ℤ :=
  ![-2, -2, 0, -1, 0]

private def N1 : Set (Finset (Fin 5)) :=
  {({0, 1, 3} : Finset (Fin 5)), ({1, 2} : Finset (Fin 5))}

private lemma B1_mulVec (z : Fin 1 → ℤ) :
    B1.mulVec z = ![z 0, -2 * z 0, -2 * z 0, z 0, 2 * z 0] := by
  ext j; fin_cases j <;> simp [B1, Matrix.mulVec, dotProduct]

private lemma w1_dot_B1 (z : Fin 1 → ℤ) :
    ∑ j : Fin 5, w1 j * ((B1.mulVec z j : ℤ) : ℝ) = (z 0 : ℝ) := by
  rw [B1_mulVec]
  simp [w1, Fin.sum_univ_five]

private lemma A1_homog : IsHomogeneousConfig A1 := by
  refine ⟨![1, 0, 0, 0], fun j => ?_⟩
  fin_cases j <;> simp [A1, Fin.sum_univ_four]

private lemma A1_B1_basis : HasLatticeBasis A1 B1 := by
  constructor
  · intro z
    rw [B1_mulVec]
    ext i
    fin_cases i
    · simp [A1, Matrix.mulVec, dotProduct, Fin.sum_univ_five]; ring
    · simp [A1, Matrix.mulVec, dotProduct, Fin.sum_univ_five]
    · simp [A1, Matrix.mulVec, dotProduct, Fin.sum_univ_five]
    · simp [A1, Matrix.mulVec, dotProduct, Fin.sum_univ_five]
  · intro u hu
    have h0 := congrFun hu 0
    have h1 := congrFun hu 1
    have h2 := congrFun hu 2
    have h3 := congrFun hu 3
    simp [A1, Matrix.mulVec, dotProduct, Fin.sum_univ_five] at h0 h1 h2 h3
    refine ⟨![u 0], ?_, ?_⟩
    · dsimp only
      rw [B1_mulVec]
      ext j; fin_cases j <;> dsimp <;> omega
    · intro z hz
      ext i; fin_cases i
      have := congrFun hz 0
      rw [B1_mulVec] at this
      simpa using this

private lemma w1_generic : IsGenericWeight B1 w1 := by
  intro z hz
  rw [w1_dot_B1]
  have h0 : z 0 ≠ 0 := by
    intro h
    apply hz
    ext i; fin_cases i; exact h
  exact_mod_cast h0

private lemma v1_fake : IsFakeExponent B1 w1 v1 := by
  intro z hw
  rw [w1_dot_B1] at hw
  have hz : 1 ≤ z 0 := by
    have : (0 : ℤ) < z 0 := by exact_mod_cast hw
    omega
  refine ⟨4, ?_, ?_⟩
  · simp [v1]
  · rw [B1_mulVec]; simp [v1]; omega

private lemma nsupp_v1_shift (z : Fin 1 → ℤ) :
    nsupp (fun j => v1 j + B1.mulVec z j) =
      if z 0 ≤ -1 then ({0, 3, 4} : Finset (Fin 5))
      else if z 0 = 0 then ({0, 1, 3} : Finset (Fin 5))
      else if z 0 = 1 then ({0, 1, 2} : Finset (Fin 5))
      else ({1, 2} : Finset (Fin 5)) := by
  rw [B1_mulVec]
  by_cases hm1 : z 0 ≤ -1
  · rw [if_pos hm1]
    ext j; fin_cases j <;> simp [nsupp, v1] <;> omega
  · rw [if_neg hm1]
    by_cases h0 : z 0 = 0
    · rw [if_pos h0]
      ext j; fin_cases j <;> simp [nsupp, v1, h0]
    · rw [if_neg h0]
      by_cases h1 : z 0 = 1
      · rw [if_pos h1]
        ext j; fin_cases j <;> simp [nsupp, v1, h1]
      · rw [if_neg h1]
        ext j; fin_cases j <;> simp [nsupp, v1] <;> omega

private lemma realizedSupports_B1_v1 (I : Finset (Fin 5)) :
    I ∈ realizedSupports B1 v1 ↔
      I = {0, 3, 4} ∨ I = {0, 1, 3} ∨ I = {0, 1, 2} ∨ I = {1, 2} := by
  constructor
  · rintro ⟨z, rfl⟩
    rw [nsupp_v1_shift]
    split_ifs <;> simp
  · rintro (rfl | rfl | rfl | rfl)
    · refine ⟨![-1], ?_⟩; rw [nsupp_v1_shift]; simp
    · refine ⟨![0], ?_⟩; rw [nsupp_v1_shift]; simp
    · refine ⟨![1], ?_⟩; rw [nsupp_v1_shift]; simp
    · refine ⟨![2], ?_⟩; rw [nsupp_v1_shift]; simp

private lemma nsupp_v1_eq : nsupp v1 = ({0, 1, 3} : Finset (Fin 5)) := by decide

private lemma N1_ordered : IsOrderedNegSupportFamily B1 w1 v1 N1 := by
  refine ⟨?_, ?_, ?_⟩
  · rw [nsupp_v1_eq]; exact Or.inl rfl
  · intro I hI
    rcases hI with rfl | rfl
    · refine ⟨(realizedSupports_B1_v1 _).mpr (Or.inr (Or.inl rfl)), fun z hz => ?_⟩
      rw [w1_dot_B1]
      rw [nsupp_v1_shift] at hz
      split_ifs at hz with h1 h2 h3
      · exfalso; exact absurd hz (by decide)
      · rw [h2]; norm_num
      · exfalso; exact absurd hz (by decide)
      · exfalso; exact absurd hz (by decide)
    · refine ⟨(realizedSupports_B1_v1 _).mpr (Or.inr (Or.inr (Or.inr rfl))), fun z hz => ?_⟩
      rw [w1_dot_B1]
      rw [nsupp_v1_shift] at hz
      split_ifs at hz with h1 h2 h3
      · exfalso; exact absurd hz (by decide)
      · exfalso; exact absurd hz (by decide)
      · exfalso; exact absurd hz (by decide)
      · have : (0 : ℤ) ≤ z 0 := by omega
        exact_mod_cast this
  · intro I hI J hJ hsub
    rw [realizedSupports_B1_v1] at hJ
    rcases hI with rfl | rfl <;> rcases hJ with rfl | rfl | rfl | rfl
    · exfalso; exact absurd hsub (by decide)
    · exact Or.inl rfl
    · exfalso; exact absurd hsub (by decide)
    · exfalso; exact absurd hsub (by decide)
    · exfalso; exact absurd hsub (by decide)
    · exfalso; exact absurd hsub (by decide)
    · exfalso; exact absurd hsub (by decide)
    · exact Or.inr rfl

private lemma commonNegSupport_N1 : commonNegSupport N1 = ({1} : Finset (Fin 5)) := by
  ext j; fin_cases j <;> simp [commonNegSupport, N1]

private lemma N1_obstruction : HasNonzeroObstruction A1 B1 v1 N1 := by
  dsimp only [HasNonzeroObstruction]
  have he_eq : monom (nsupp v1 \ commonNegSupport N1) =
      MvPolynomial.X (0 : Fin 5) * MvPolynomial.X (3 : Fin 5) := by
    rw [nsupp_v1_eq, commonNegSupport_N1]
    have hset : ({0, 1, 3} : Finset (Fin 5)) \ {1} = {0, 3} := by decide
    rw [hset]; simp [monom]
  refine ⟨1, ?_, ?_⟩
  · rw [mul_one, he_eq]
    have hθ2 : (2 : ℂ) • MvPolynomial.X (0 : Fin 5) + MvPolynomial.X (2 : Fin 5) ∈ eulerIdeal A1 := by
      apply Ideal.subset_span
      refine ⟨2, ?_⟩
      simp [A1, Fin.sum_univ_five]
    have hθ3 : (-1 : ℂ) • MvPolynomial.X (0 : Fin 5) + MvPolynomial.X (3 : Fin 5) ∈ eulerIdeal A1 := by
      apply Ideal.subset_span
      refine ⟨3, ?_⟩
      simp [A1, Fin.sum_univ_five]
    have hP02 : MvPolynomial.X (0 : Fin 5) * MvPolynomial.X (2 : Fin 5) ∈ boundaryIdeal B1 v1 N1 := by
      apply Ideal.subset_span
      refine ⟨{1, 2}, Or.inr rfl, {0, 1, 2}, (realizedSupports_B1_v1 _).mpr (Or.inr (Or.inr (Or.inl rfl))),
        ?_, ?_⟩
      · intro h; rcases h with h | h <;> exact absurd h (by decide)
      · rw [commonNegSupport_N1]
        have hset : (({1, 2} : Finset (Fin 5)) ∪ {0, 1, 2}) \ {1} = {0, 2} := by decide
        rw [hset]; simp [monom]
    have hU : MvPolynomial.X (0 : Fin 5) * ((-1 : ℂ) • MvPolynomial.X 0 + MvPolynomial.X 3) +
        ((1 / 2 : ℂ) • MvPolynomial.X 0) * ((2 : ℂ) • MvPolynomial.X 0 + MvPolynomial.X 2) ∈
        eulerIdeal A1 :=
      Ideal.add_mem _ (Ideal.mul_mem_left _ _ hθ3) (Ideal.mul_mem_left _ _ hθ2)
    have hP : (-(1 / 2 : ℂ)) • (MvPolynomial.X (0 : Fin 5) * MvPolynomial.X (2 : Fin 5)) ∈
        boundaryIdeal B1 v1 N1 := by
      rw [Algebra.smul_def]
      exact Ideal.mul_mem_left _ _ hP02
    have hsum_mem := Submodule.add_mem_sup hU hP
    have hid : (MvPolynomial.X (0 : Fin 5) * ((-1 : ℂ) • MvPolynomial.X 0 + MvPolynomial.X 3) +
        ((1 / 2 : ℂ) • MvPolynomial.X 0) * ((2 : ℂ) • MvPolynomial.X 0 + MvPolynomial.X 2)) +
        (-(1 / 2 : ℂ)) • (MvPolynomial.X (0 : Fin 5) * MvPolynomial.X (2 : Fin 5)) =
        (MvPolynomial.X (0 : Fin 5) * MvPolynomial.X (3 : Fin 5) : MvPolynomial (Fin 5) ℂ) := by
      have h12 : (algebraMap ℂ (MvPolynomial (Fin 5) ℂ)) (1 / 2 : ℂ) * 2 = 1 := by
        rw [← map_ofNat (algebraMap ℂ (MvPolynomial (Fin 5) ℂ)) 2, ← map_mul]
        norm_num
      simp only [Algebra.smul_def, map_neg, map_one, map_ofNat]
      linear_combination MvPolynomial.X (0 : Fin 5) ^ 2 * h12
    rwa [hid] at hsum_mem
  · rw [mul_one, he_eq]
    intro hmem
    set d03 : Fin 5 →₀ ℕ := Finsupp.single 0 1 + Finsupp.single 3 1
    have hd03 : mdeg d03 = 2 := by simp [d03, mdeg_add, mdeg_single]
    let φ1 : MvPolynomial (Fin 5) ℂ →ₗ[ℂ] ℂ := MvPolynomial.lcoeff ℂ d03
    have hφ1_deg : ∀ (q g : MvPolynomial (Fin 5) ℂ),
        (∀ d ∈ g.support, 2 ≤ mdeg d) → φ1 (q * g) = MvPolynomial.coeff 0 q * φ1 g :=
      fun q g hg => coeff_mul_of_deg_ge q g d03 hd03 hg
    have hUM : ∀ u ∈ eulerIdeal A1 * supportIdeal N1, φ1 u = 0 := by
      unfold eulerIdeal supportIdeal
      rw [Ideal.span_mul_span']
      refine linear_form_vanish_ideal φ1 hφ1_deg _ ?_
      rintro _ ⟨_, ⟨i, rfl⟩, _, ⟨I, hI, rfl⟩, rfl⟩
      rw [commonNegSupport_N1]
      rcases hI with rfl | rfl
      · have hcard : 2 ≤ (({0, 1, 3} : Finset (Fin 5)) \ {1}).card := by decide
        have h3 := linear_mul_monom_deg_ge (fun j => (A1 i j : ℂ)) _ 2 hcard
        refine ⟨fun d hd => by have := h3 d hd; omega, ?_⟩
        by_contra hne
        have := h3 d03 (MvPolynomial.mem_support_iff.mpr hne)
        omega
      · have hcard : 1 ≤ (({1, 2} : Finset (Fin 5)) \ {1}).card := by decide
        have h2 := linear_mul_monom_deg_ge (fun j => (A1 i j : ℂ)) _ 1 hcard
        refine ⟨fun d hd => by have := h2 d hd; omega, ?_⟩
        have hset : ({1, 2} : Finset (Fin 5)) \ {1} = {2} := by decide
        rw [hset]
        have hmon2 : monom ({2} : Finset (Fin 5)) = MvPolynomial.X 2 := by simp [monom]
        change MvPolynomial.coeff d03 _ = 0
        rw [hmon2, MvPolynomial.coeff_mul]
        refine Finset.sum_eq_zero (fun ab hab => ?_)
        rcases ab with ⟨a, b⟩
        rw [Finset.HasAntidiagonal.mem_antidiagonal] at hab
        by_cases hb : b = Finsupp.single 2 1
        · subst hb
          have h2eq := congrFun (congrArg DFunLike.coe hab) 2
          simp [d03] at h2eq
        · rw [MvPolynomial.X, MvPolynomial.coeff_monomial, if_neg (Ne.symm hb), mul_zero]
    have hP : ∀ u ∈ boundaryIdeal B1 v1 N1, φ1 u = 0 := by
      unfold boundaryIdeal
      refine linear_form_vanish_ideal φ1 hφ1_deg _ ?_
      rintro _ ⟨I, hI, J, hJ, hJnot, rfl⟩
      rw [commonNegSupport_N1]
      rw [realizedSupports_B1_v1] at hJ
      have hne_03 : ((I ∪ J) \ {1}) ≠ {0, 3} ∧ 2 ≤ ((I ∪ J) \ {1}).card := by
        rcases hI with rfl | rfl <;> rcases hJ with rfl | rfl | rfl | rfl
        · decide
        · exfalso; exact hJnot (Or.inl rfl)
        · decide
        · exfalso; exact hJnot (Or.inr rfl)
        · decide
        · exfalso; exact hJnot (Or.inl rfl)
        · decide
        · exfalso; exact hJnot (Or.inr rfl)
      refine ⟨mdeg_monom_ge _ 2 hne_03.2, ?_⟩
      change MvPolynomial.coeff d03 (monom ((I ∪ J) \ {1})) = 0
      rw [monom_eq_monomial, MvPolynomial.coeff_monomial, if_neg]
      intro hsum
      apply hne_03.1
      ext j
      have hj := congrFun (congrArg DFunLike.coe hsum) j
      simp only [Finsupp.finsetSum_apply, Finsupp.single_apply, Finset.sum_ite_eq',
        Finsupp.coe_add, Pi.add_apply, d03, Finset.mem_insert, Finset.mem_singleton] at hj ⊢
      by_cases hm : j ∈ (I ∪ J) \ {1}
      · simp only [hm, ↓reduceIte, true_iff] at hj ⊢
        fin_cases j <;> simp at hj ⊢
      · simp only [hm, ↓reduceIte, false_iff] at hj ⊢
        fin_cases j <;> simp at hj ⊢
    rcases Submodule.mem_sup.mp hmem with ⟨u, hu, v, hv, huv⟩
    have h0 : φ1 (MvPolynomial.X (0 : Fin 5) * MvPolynomial.X (3 : Fin 5)) = 0 := by
      rw [← huv, map_add, hUM u hu, hP v hv, add_zero]
    have h1 : φ1 (MvPolynomial.X (0 : Fin 5) * MvPolynomial.X (3 : Fin 5)) = 1 := by
      change MvPolynomial.coeff d03 (MvPolynomial.X (0 : Fin 5) * MvPolynomial.X (3 : Fin 5)) = 1
      rw [MvPolynomial.X, MvPolynomial.X, MvPolynomial.monomial_mul, one_mul,
        MvPolynomial.coeff_monomial, if_pos rfl]
    rw [h1] at h0
    exact one_ne_zero h0

/-! ### Part 2: Lattice rank 2 ordered distinguished collection counterexample (Theorem 6.10) -/

private def A2 : Matrix (Fin 3) (Fin 5) ℤ :=
  ![![20, -5, 3, 0, 0],
    ![-3, 2, -1, 1, 0],
    ![-16, 4, -1, 0, 1]]

private def B2 : Matrix (Fin 5) (Fin 2) ℤ :=
  ![![0, -1],
    ![3, -4],
    ![5, 0],
    ![-1, 5],
    ![-7, 0]]

private noncomputable def theta2 : ℝ :=
  15 + Real.sqrt 2 / 100

private noncomputable def w2 : Fin 5 → ℝ :=
  ![theta2 - 4, 1, 0, 0, 0]

private def v2 : Fin 5 → ℤ :=
  ![0, 1, 0, -2, -3]

private lemma B2_mulVec (z : Fin 2 → ℤ) :
    B2.mulVec z = ![-z 1, 3 * z 0 - 4 * z 1, 5 * z 0, -z 0 + 5 * z 1, -7 * z 0] := by
  ext j
  fin_cases j <;> simp [B2, Matrix.mulVec, dotProduct, Fin.sum_univ_two, sub_eq_add_neg]

private lemma w2_dot_B2 (z : Fin 2 → ℤ) :
    ∑ j : Fin 5, w2 j * ((B2.mulVec z j : ℤ) : ℝ) =
      3 * (z 0 : ℝ) - theta2 * (z 1 : ℝ) := by
  rw [B2_mulVec]
  simp [w2, Fin.sum_univ_five]
  ring

private lemma theta2_gt_15 : (15 : ℝ) < theta2 := by
  unfold theta2
  have h : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  linarith

private lemma A2_homog : IsHomogeneousConfig A2 := by
  refine ⟨![1, 1, 1], fun j => ?_⟩
  fin_cases j <;> simp [A2, Fin.sum_univ_three] <;> norm_num

private lemma A2_B2_basis : HasLatticeBasis A2 B2 := by
  constructor
  · intro z
    rw [B2_mulVec]
    ext i; fin_cases i <;> simp [A2, Matrix.mulVec, dotProduct, Fin.sum_univ_five] <;> ring
  · intro u hu
    have h0 := congrFun hu 0
    have h1 := congrFun hu 1
    have h2 := congrFun hu 2
    simp [A2, Matrix.mulVec, dotProduct, Fin.sum_univ_five] at h0 h1 h2
    refine ⟨![-(u 3 + 5 * u 0), -u 0], ?_, ?_⟩
    · dsimp only
      rw [B2_mulVec]
      ext j; fin_cases j <;> dsimp <;> omega
    · intro z hz
      have hz0 := congrFun hz 0
      have hz3 := congrFun hz 3
      rw [B2_mulVec] at hz0 hz3
      dsimp at hz0 hz3
      ext i; fin_cases i <;> dsimp <;> omega

private lemma w2_generic : IsGenericWeight B2 w2 := by
  intro z hz hdot
  rw [w2_dot_B2] at hdot
  by_cases h1 : z 1 = 0
  · rw [h1, Int.cast_zero, mul_zero, sub_zero] at hdot
    have h0 : z 0 = 0 := by
      have : (z 0 : ℝ) = 0 := by linarith
      exact_mod_cast this
    apply hz
    ext i; fin_cases i
    · exact h0
    · exact h1
  · have h1r : (z 1 : ℝ) ≠ 0 := by exact_mod_cast h1
    have hsq2 : Real.sqrt 2 = ((100 * (3 * (z 0 : ℚ) - 15 * (z 1 : ℚ)) / (z 1 : ℚ) : ℚ) : ℝ) := by
      push_cast
      unfold theta2 at hdot
      field_simp [h1r]
      linarith
    exact irrational_sqrt_two ⟨100 * (3 * (z 0 : ℚ) - 15 * (z 1 : ℚ)) / (z 1 : ℚ), hsq2.symm⟩

private lemma v2_fake : IsFakeExponent B2 w2 v2 := by
  intro z hw
  rw [w2_dot_B2] at hw
  have hth := theta2_gt_15
  by_cases hq : z 1 ≤ -1
  · refine ⟨0, by simp [v2], ?_⟩
    rw [B2_mulVec]; simp [v2]; omega
  · by_cases hp : 1 ≤ z 0
    · refine ⟨2, by simp [v2], ?_⟩
      rw [B2_mulVec]; simp [v2]; omega
    · exfalso
      have hp0 : (z 0 : ℝ) ≤ 0 := by exact_mod_cast (show z 0 ≤ 0 by omega)
      have hq0 : (0 : ℝ) ≤ (z 1 : ℝ) := by exact_mod_cast (show 0 ≤ z 1 by omega)
      nlinarith

private lemma nsupp_v2_iff (z : Fin 2 → ℤ) :
    (0 ∈ nsupp (fun j => v2 j + B2.mulVec z j) ↔ 1 ≤ z 1) ∧
    (1 ∈ nsupp (fun j => v2 j + B2.mulVec z j) ↔ 3 * z 0 - 4 * z 1 ≤ -2) ∧
    (2 ∈ nsupp (fun j => v2 j + B2.mulVec z j) ↔ z 0 ≤ -1) ∧
    (3 ∈ nsupp (fun j => v2 j + B2.mulVec z j) ↔ -z 0 + 5 * z 1 ≤ 1) ∧
    (4 ∈ nsupp (fun j => v2 j + B2.mulVec z j) ↔ 0 ≤ z 0) := by
  rw [B2_mulVec]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> simp [nsupp, v2] <;> omega

private lemma realizedSupports_B2_v2 (I : Finset (Fin 5)) :
    I ∈ realizedSupports B2 v2 ↔
      I = {2, 3} ∨ I = {3, 4} ∨ I = {0, 1, 2} ∨ I = {1, 2, 3} ∨
      I = {1, 2} ∨ I = {0, 4} ∨ I = {0, 1, 4} ∨ I = {0, 3, 4} := by
  constructor
  · rintro ⟨z, rfl⟩
    by_cases hp : z 0 ≤ -1
    · by_cases hq : 1 ≤ z 1
      · right; right; left
        ext j; fin_cases j <;> simp [nsupp, v2, B2_mulVec] <;> omega
      · by_cases h1 : 3 * z 0 - 4 * z 1 ≤ -2
        · by_cases h3 : -z 0 + 5 * z 1 ≤ 1
          · right; right; right; left
            ext j; fin_cases j <;> simp [nsupp, v2, B2_mulVec] <;> omega
          · right; right; right; right; left
            ext j; fin_cases j <;> simp [nsupp, v2, B2_mulVec] <;> omega
        · left
          ext j; fin_cases j <;> simp [nsupp, v2, B2_mulVec] <;> omega
    · by_cases hq : 1 ≤ z 1
      · by_cases h1 : 3 * z 0 - 4 * z 1 ≤ -2
        · right; right; right; right; right; right; left
          ext j; fin_cases j <;> simp [nsupp, v2, B2_mulVec] <;> omega
        · by_cases h3 : -z 0 + 5 * z 1 ≤ 1
          · right; right; right; right; right; right; right
            ext j; fin_cases j <;> simp [nsupp, v2, B2_mulVec] <;> omega
          · right; right; right; right; right; left
            ext j; fin_cases j <;> simp [nsupp, v2, B2_mulVec] <;> omega
      · right; left
        ext j; fin_cases j <;> simp [nsupp, v2, B2_mulVec] <;> omega
  · rintro (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
    · refine ⟨![-1, -1], ?_⟩; ext j; fin_cases j <;> simp [nsupp, v2, B2_mulVec]
    · refine ⟨![0, 0], ?_⟩; ext j; fin_cases j <;> simp [nsupp, v2, B2_mulVec]
    · refine ⟨![-1, 1], ?_⟩; ext j; fin_cases j <;> simp [nsupp, v2, B2_mulVec]
    · refine ⟨![-1, 0], ?_⟩; ext j; fin_cases j <;> simp [nsupp, v2, B2_mulVec]
    · refine ⟨![-2, 0], ?_⟩; ext j; fin_cases j <;> simp [nsupp, v2, B2_mulVec]
    · refine ⟨![2, 1], ?_⟩; ext j; fin_cases j <;> simp [nsupp, v2, B2_mulVec]
    · refine ⟨![0, 1], ?_⟩; ext j; fin_cases j <;> simp [nsupp, v2, B2_mulVec]
    · refine ⟨![4, 1], ?_⟩; ext j; fin_cases j <;> simp [nsupp, v2, B2_mulVec]

private lemma distinguished_B2_v2 (I : Finset (Fin 5)) :
    I ∈ distinguishedCollection B2 w2 v2 ↔ I = {2, 3} ∨ I = {3, 4} := by
  have hth := theta2_gt_15
  constructor
  · rintro ⟨hreal, hnn⟩
    rw [realizedSupports_B2_v2] at hreal
    rcases hreal with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr rfl
    · exfalso
      have hw := hnn ![-1, 1] (by ext j; fin_cases j <;> simp [nsupp, v2, B2_mulVec])
      rw [w2_dot_B2] at hw; simp at hw; linarith
    · exfalso
      have hw := hnn ![-1, 0] (by ext j; fin_cases j <;> simp [nsupp, v2, B2_mulVec])
      rw [w2_dot_B2] at hw; simp at hw; linarith
    · exfalso
      have hw := hnn ![-2, 0] (by ext j; fin_cases j <;> simp [nsupp, v2, B2_mulVec])
      rw [w2_dot_B2] at hw; simp at hw; linarith
    · exfalso
      have hw := hnn ![2, 1] (by ext j; fin_cases j <;> simp [nsupp, v2, B2_mulVec])
      rw [w2_dot_B2] at hw; simp at hw; linarith
    · exfalso
      have hw := hnn ![0, 1] (by ext j; fin_cases j <;> simp [nsupp, v2, B2_mulVec])
      rw [w2_dot_B2] at hw; simp at hw; linarith
    · exfalso
      have hw := hnn ![4, 1] (by ext j; fin_cases j <;> simp [nsupp, v2, B2_mulVec])
      rw [w2_dot_B2] at hw; simp at hw; linarith
  · rintro (rfl | rfl)
    · refine ⟨(realizedSupports_B2_v2 _).mpr (Or.inl rfl), fun z hz => ?_⟩
      rw [w2_dot_B2]
      have hiff := nsupp_v2_iff z
      have h0 : ¬ 1 ≤ z 1 := by rw [← hiff.1, hz]; decide
      have h1 : ¬ 3 * z 0 - 4 * z 1 ≤ -2 := by rw [← hiff.2.1, hz]; decide
      have h2 : z 0 ≤ -1 := by rw [← hiff.2.2.1, hz]; decide
      have hq1 : (z 1 : ℝ) ≤ -1 := by exact_mod_cast (show z 1 ≤ -1 by omega)
      have h3p : 4 * (z 1 : ℝ) - 1 ≤ 3 * (z 0 : ℝ) := by
        exact_mod_cast (show 4 * z 1 - 1 ≤ 3 * z 0 by omega)
      nlinarith
    · refine ⟨(realizedSupports_B2_v2 _).mpr (Or.inr (Or.inl rfl)), fun z hz => ?_⟩
      rw [w2_dot_B2]
      have hiff := nsupp_v2_iff z
      have h0 : ¬ 1 ≤ z 1 := by rw [← hiff.1, hz]; decide
      have h4 : 0 ≤ z 0 := by rw [← hiff.2.2.2.2, hz]; decide
      have hq0 : (z 1 : ℝ) ≤ 0 := by exact_mod_cast (show z 1 ≤ 0 by omega)
      have hp0 : (0 : ℝ) ≤ (z 0 : ℝ) := by exact_mod_cast h4
      nlinarith

private lemma nsupp_v2_eq : nsupp v2 = ({3, 4} : Finset (Fin 5)) := by decide

private lemma N2_ordered :
    IsOrderedNegSupportFamily B2 w2 v2 (distinguishedCollection B2 w2 v2) := by
  refine ⟨?_, Set.Subset.rfl, ?_⟩
  · rw [distinguished_B2_v2, nsupp_v2_eq]; exact Or.inr rfl
  · intro I hI J hJ hsub
    rw [distinguished_B2_v2] at hI ⊢
    rw [realizedSupports_B2_v2] at hJ
    rcases hI with rfl | rfl <;>
      rcases hJ with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact Or.inl rfl
    · exfalso; exact absurd hsub (by decide)
    · exfalso; exact absurd hsub (by decide)
    · exfalso; exact absurd hsub (by decide)
    · exfalso; exact absurd hsub (by decide)
    · exfalso; exact absurd hsub (by decide)
    · exfalso; exact absurd hsub (by decide)
    · exfalso; exact absurd hsub (by decide)
    · exfalso; exact absurd hsub (by decide)
    · exact Or.inr rfl
    · exfalso; exact absurd hsub (by decide)
    · exfalso; exact absurd hsub (by decide)
    · exfalso; exact absurd hsub (by decide)
    · exfalso; exact absurd hsub (by decide)
    · exfalso; exact absurd hsub (by decide)
    · exfalso; exact absurd hsub (by decide)

private lemma commonNegSupport_N2 :
    commonNegSupport (distinguishedCollection B2 w2 v2) = ({3} : Finset (Fin 5)) := by
  ext j; fin_cases j <;> simp [commonNegSupport, distinguished_B2_v2]

private noncomputable def phi2 : MvPolynomial (Fin 5) ℂ →ₗ[ℂ] ℂ :=
  (1 : ℂ) • MvPolynomial.lcoeff ℂ (Finsupp.single 2 1 + Finsupp.single 4 1) +
  (3 / 28 : ℂ) • MvPolynomial.lcoeff ℂ (Finsupp.single 0 1 + Finsupp.single 2 1) +
  (-(5 / 7 : ℂ)) • MvPolynomial.lcoeff ℂ (Finsupp.single 2 1 + Finsupp.single 2 1) +
  (3 / 5 : ℂ) • MvPolynomial.lcoeff ℂ (Finsupp.single 1 1 + Finsupp.single 4 1) +
  (-(7 / 5 : ℂ)) • MvPolynomial.lcoeff ℂ (Finsupp.single 4 1 + Finsupp.single 4 1) +
  (-(11 / 28 : ℂ)) • MvPolynomial.lcoeff ℂ (Finsupp.single 2 1 + Finsupp.single 3 1) +
  (-(1 / 5 : ℂ)) • MvPolynomial.lcoeff ℂ (Finsupp.single 3 1 + Finsupp.single 4 1)

private lemma phi2_mul_of_deg_ge (q g : MvPolynomial (Fin 5) ℂ)
    (hg : ∀ d ∈ g.support, 2 ≤ mdeg d) :
    phi2 (q * g) = MvPolynomial.coeff 0 q * phi2 g := by
  have hd24 : mdeg (Finsupp.single (2 : Fin 5) 1 + Finsupp.single 4 1) = 2 := by
    simp [mdeg_add, mdeg_single]
  have hd02 : mdeg (Finsupp.single (0 : Fin 5) 1 + Finsupp.single 2 1) = 2 := by
    simp [mdeg_add, mdeg_single]
  have hd22 : mdeg (Finsupp.single (2 : Fin 5) 1 + Finsupp.single 2 1) = 2 := by
    simp [mdeg_add, mdeg_single]
  have hd14 : mdeg (Finsupp.single (1 : Fin 5) 1 + Finsupp.single 4 1) = 2 := by
    simp [mdeg_add, mdeg_single]
  have hd44 : mdeg (Finsupp.single (4 : Fin 5) 1 + Finsupp.single 4 1) = 2 := by
    simp [mdeg_add, mdeg_single]
  have hd23 : mdeg (Finsupp.single (2 : Fin 5) 1 + Finsupp.single 3 1) = 2 := by
    simp [mdeg_add, mdeg_single]
  have hd34 : mdeg (Finsupp.single (3 : Fin 5) 1 + Finsupp.single 4 1) = 2 := by
    simp [mdeg_add, mdeg_single]
  simp only [phi2, LinearMap.add_apply, LinearMap.smul_apply, MvPolynomial.lcoeff_apply,
    smul_eq_mul]
  rw [coeff_mul_of_deg_ge q g _ hd24 hg,
      coeff_mul_of_deg_ge q g _ hd02 hg,
      coeff_mul_of_deg_ge q g _ hd22 hg,
      coeff_mul_of_deg_ge q g _ hd14 hg,
      coeff_mul_of_deg_ge q g _ hd44 hg,
      coeff_mul_of_deg_ge q g _ hd23 hg,
      coeff_mul_of_deg_ge q g _ hd34 hg]
  ring

private lemma single_add_single_eq_iff {α : Type*} [DecidableEq α] (k l i j : α) :
    Finsupp.single k (1 : ℕ) + Finsupp.single l 1 = Finsupp.single i 1 + Finsupp.single j 1 ↔
      (k = i ∧ l = j) ∨ (k = j ∧ l = i) := by
  constructor
  · intro h
    have hk := congrFun (congrArg DFunLike.coe h) k
    simp only [Finsupp.coe_add, Pi.add_apply, Finsupp.single_apply, ↓reduceIte] at hk
    by_cases hki : i = k
    · subst hki
      have hlj : Finsupp.single l (1 : ℕ) = Finsupp.single j 1 := add_left_cancel h
      have hl := congrFun (congrArg DFunLike.coe hlj) l
      simp only [Finsupp.single_apply, ↓reduceIte] at hl
      by_cases hjl : j = l
      · exact Or.inl ⟨rfl, hjl.symm⟩
      · rw [if_neg hjl] at hl; omega
    · rw [if_neg hki] at hk
      by_cases hkj : j = k
      · subst hkj
        rw [add_comm (Finsupp.single i (1 : ℕ))] at h
        have hli : Finsupp.single l (1 : ℕ) = Finsupp.single i 1 := add_left_cancel h
        have hl := congrFun (congrArg DFunLike.coe hli) l
        simp only [Finsupp.single_apply, ↓reduceIte] at hl
        by_cases hil : i = l
        · exact Or.inr ⟨rfl, hil.symm⟩
        · rw [if_neg hil] at hl; omega
      · rw [if_neg hkj] at hk; omega
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · rfl
    · exact add_comm _ _

private lemma coeff_X_mul_X (i j k l : Fin 5) :
    MvPolynomial.coeff (Finsupp.single i 1 + Finsupp.single j 1)
      (MvPolynomial.X k * MvPolynomial.X l : MvPolynomial (Fin 5) ℂ) =
      if (k = i ∧ l = j) ∨ (k = j ∧ l = i) then 1 else 0 := by
  rw [MvPolynomial.X, MvPolynomial.X, MvPolynomial.monomial_mul, one_mul,
    MvPolynomial.coeff_monomial]
  have hiff := single_add_single_eq_iff k l i j
  by_cases h1 : Finsupp.single k 1 + Finsupp.single l 1 = Finsupp.single i 1 + Finsupp.single j 1
  · rw [if_pos h1, if_pos (hiff.mp h1)]
  · rw [if_neg h1, if_neg (fun h2 => h1 (hiff.mpr h2))]

private lemma phi2_X_mul_X (k l : Fin 5) :
    phi2 (MvPolynomial.X k * MvPolynomial.X l) =
      if (k = 2 ∧ l = 4) ∨ (k = 4 ∧ l = 2) then (1 : ℂ)
      else if (k = 0 ∧ l = 2) ∨ (k = 2 ∧ l = 0) then (3 / 28 : ℂ)
      else if k = 2 ∧ l = 2 then (-(5 / 7 : ℂ))
      else if (k = 1 ∧ l = 4) ∨ (k = 4 ∧ l = 1) then (3 / 5 : ℂ)
      else if k = 4 ∧ l = 4 then (-(7 / 5 : ℂ))
      else if (k = 2 ∧ l = 3) ∨ (k = 3 ∧ l = 2) then (-(11 / 28 : ℂ))
      else if (k = 3 ∧ l = 4) ∨ (k = 4 ∧ l = 3) then (-(1 / 5 : ℂ))
      else 0 := by
  simp only [phi2, LinearMap.add_apply, LinearMap.smul_apply, MvPolynomial.lcoeff_apply,
    smul_eq_mul, coeff_X_mul_X]
  fin_cases k <;> fin_cases l <;> (simp; try norm_num)

private lemma N2_obstruction :
    HasNonzeroObstruction A2 B2 v2 (distinguishedCollection B2 w2 v2) := by
  dsimp only [HasNonzeroObstruction]
  have he_eq : monom (nsupp v2 \ commonNegSupport (distinguishedCollection B2 w2 v2)) =
      MvPolynomial.X (4 : Fin 5) := by
    rw [nsupp_v2_eq, commonNegSupport_N2]
    have hset : ({3, 4} : Finset (Fin 5)) \ {3} = {4} := by decide
    rw [hset]; simp [monom]
  refine ⟨MvPolynomial.X (2 : Fin 5), ?_, ?_⟩
  · rw [he_eq]
    have hθ0 : (20 : ℂ) • MvPolynomial.X (0 : Fin 5) + (-5 : ℂ) • MvPolynomial.X 1 +
        (3 : ℂ) • MvPolynomial.X 2 ∈ eulerIdeal A2 := by
      apply Ideal.subset_span
      refine ⟨0, ?_⟩
      simp [A2, Fin.sum_univ_five]
    have hθ2 : (-16 : ℂ) • MvPolynomial.X (0 : Fin 5) + (4 : ℂ) • MvPolynomial.X 1 +
        (-1 : ℂ) • MvPolynomial.X 2 + MvPolynomial.X 4 ∈ eulerIdeal A2 := by
      apply Ideal.subset_span
      refine ⟨2, ?_⟩
      simp [A2, Fin.sum_univ_five]
    have hP12 : MvPolynomial.X (1 : Fin 5) * MvPolynomial.X (2 : Fin 5) ∈
        boundaryIdeal B2 v2 (distinguishedCollection B2 w2 v2) := by
      apply Ideal.subset_span
      refine ⟨{2, 3}, (distinguished_B2_v2 _).mpr (Or.inl rfl),
        {1, 2}, (realizedSupports_B2_v2 _).mpr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))),
        ?_, ?_⟩
      · rw [distinguished_B2_v2]; decide
      · rw [commonNegSupport_N2]
        have hset : (({2, 3} : Finset (Fin 5)) ∪ {1, 2}) \ {3} = {1, 2} := by decide
        rw [hset]; simp [monom]
    have hP04 : MvPolynomial.X (0 : Fin 5) * MvPolynomial.X (4 : Fin 5) ∈
        boundaryIdeal B2 v2 (distinguishedCollection B2 w2 v2) := by
      apply Ideal.subset_span
      refine ⟨{3, 4}, (distinguished_B2_v2 _).mpr (Or.inr rfl),
        {0, 4}, (realizedSupports_B2_v2 _).mpr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))),
        ?_, ?_⟩
      · rw [distinguished_B2_v2]; decide
      · rw [commonNegSupport_N2]
        have hset : (({3, 4} : Finset (Fin 5)) ∪ {0, 4}) \ {3} = {0, 4} := by decide
        rw [hset]; simp [monom]
    have hU : (1 / 3 : ℂ) • ((MvPolynomial.X 4 + (4 : ℂ) • MvPolynomial.X 1) *
          ((20 : ℂ) • MvPolynomial.X 0 + (-5 : ℂ) • MvPolynomial.X 1 + (3 : ℂ) • MvPolynomial.X 2) +
          ((5 : ℂ) • MvPolynomial.X 1) *
          ((-16 : ℂ) • MvPolynomial.X 0 + (4 : ℂ) • MvPolynomial.X 1 + (-1 : ℂ) • MvPolynomial.X 2 +
            MvPolynomial.X 4)) ∈ eulerIdeal A2 := by
      rw [Algebra.smul_def]
      exact Ideal.mul_mem_left _ _
        (Ideal.add_mem _ (Ideal.mul_mem_left _ _ hθ0) (Ideal.mul_mem_left _ _ hθ2))
    have hP : (-(7 / 3 : ℂ)) • (MvPolynomial.X 1 * MvPolynomial.X 2) +
        (-(20 / 3 : ℂ)) • (MvPolynomial.X 0 * MvPolynomial.X 4) ∈
        boundaryIdeal B2 v2 (distinguishedCollection B2 w2 v2) := by
      rw [Algebra.smul_def, Algebra.smul_def]
      exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ hP12) (Ideal.mul_mem_left _ _ hP04)
    have hsum_mem := Submodule.add_mem_sup hU hP
    have hid : (1 / 3 : ℂ) • ((MvPolynomial.X (4 : Fin 5) + (4 : ℂ) • MvPolynomial.X 1) *
          ((20 : ℂ) • MvPolynomial.X 0 + (-5 : ℂ) • MvPolynomial.X 1 + (3 : ℂ) • MvPolynomial.X 2) +
          ((5 : ℂ) • MvPolynomial.X 1) *
          ((-16 : ℂ) • MvPolynomial.X 0 + (4 : ℂ) • MvPolynomial.X 1 + (-1 : ℂ) • MvPolynomial.X 2 +
            MvPolynomial.X 4)) +
        ((-(7 / 3 : ℂ)) • (MvPolynomial.X 1 * MvPolynomial.X 2) +
        (-(20 / 3 : ℂ)) • (MvPolynomial.X 0 * MvPolynomial.X 4)) =
        (MvPolynomial.X (4 : Fin 5) * MvPolynomial.X (2 : Fin 5) : MvPolynomial (Fin 5) ℂ) := by
      have h13 : (algebraMap ℂ (MvPolynomial (Fin 5) ℂ)) (1 / 3 : ℂ) * 3 = 1 := by
        rw [← map_ofNat (algebraMap ℂ (MvPolynomial (Fin 5) ℂ)) 3, ← map_mul]; norm_num
      have h73 : (algebraMap ℂ (MvPolynomial (Fin 5) ℂ)) (7 / 3 : ℂ) =
          7 * (algebraMap ℂ (MvPolynomial (Fin 5) ℂ)) (1 / 3 : ℂ) := by
        rw [← map_ofNat (algebraMap ℂ (MvPolynomial (Fin 5) ℂ)) 7, ← map_mul]; norm_num
      have h203 : (algebraMap ℂ (MvPolynomial (Fin 5) ℂ)) (20 / 3 : ℂ) =
          20 * (algebraMap ℂ (MvPolynomial (Fin 5) ℂ)) (1 / 3 : ℂ) := by
        rw [← map_ofNat (algebraMap ℂ (MvPolynomial (Fin 5) ℂ)) 20, ← map_mul]; norm_num
      simp only [Algebra.smul_def, map_neg, map_one, map_ofNat, h73, h203]
      linear_combination MvPolynomial.X (4 : Fin 5) * MvPolynomial.X (2 : Fin 5) * h13
    rwa [hid] at hsum_mem
  · rw [he_eq]
    intro hmem
    have hUM : ∀ u ∈ eulerIdeal A2 * supportIdeal (distinguishedCollection B2 w2 v2), phi2 u = 0 := by
      unfold eulerIdeal supportIdeal
      rw [Ideal.span_mul_span']
      refine linear_form_vanish_ideal phi2 phi2_mul_of_deg_ge _ ?_
      rintro _ ⟨_, ⟨i, rfl⟩, _, ⟨I, hI, rfl⟩, rfl⟩
      rw [commonNegSupport_N2]
      rw [distinguished_B2_v2] at hI
      rcases hI with rfl | rfl
      · have hset : ({2, 3} : Finset (Fin 5)) \ {3} = {2} := by decide
        have hcard : 1 ≤ (({2, 3} : Finset (Fin 5)) \ {3}).card := by decide
        have h2 := linear_mul_monom_deg_ge (fun j => (A2 i j : ℂ)) _ 1 hcard
        refine ⟨fun d hd => by have := h2 d hd; omega, ?_⟩
        rw [hset]
        have hmon2 : monom ({2} : Finset (Fin 5)) = MvPolynomial.X 2 := by simp [monom]
        change phi2 ((∑ j : Fin 5, (A2 i j : ℂ) • MvPolynomial.X j) * monom {2}) = 0
        rw [hmon2, Finset.sum_mul, map_sum]
        simp only [smul_mul_assoc, map_smul, smul_eq_mul]
        fin_cases i <;>
          (simp [A2, Fin.sum_univ_five, phi2_X_mul_X]; norm_num)
      · have hset : ({3, 4} : Finset (Fin 5)) \ {3} = {4} := by decide
        have hcard : 1 ≤ (({3, 4} : Finset (Fin 5)) \ {3}).card := by decide
        have h2 := linear_mul_monom_deg_ge (fun j => (A2 i j : ℂ)) _ 1 hcard
        refine ⟨fun d hd => by have := h2 d hd; omega, ?_⟩
        rw [hset]
        have hmon4 : monom ({4} : Finset (Fin 5)) = MvPolynomial.X 4 := by simp [monom]
        change phi2 ((∑ j : Fin 5, (A2 i j : ℂ) • MvPolynomial.X j) * monom {4}) = 0
        rw [hmon4, Finset.sum_mul, map_sum]
        simp only [smul_mul_assoc, map_smul, smul_eq_mul]
        fin_cases i <;>
          (simp [A2, Fin.sum_univ_five, phi2_X_mul_X]; norm_num)
    have hP : ∀ u ∈ boundaryIdeal B2 v2 (distinguishedCollection B2 w2 v2), phi2 u = 0 := by
      unfold boundaryIdeal
      refine linear_form_vanish_ideal phi2 phi2_mul_of_deg_ge _ ?_
      rintro _ ⟨I, hI, J, hJ, hJnot, rfl⟩
      rw [commonNegSupport_N2]
      rw [distinguished_B2_v2] at hI
      rw [realizedSupports_B2_v2] at hJ
      have hcase : ((I ∪ J) \ {3}) = {1, 2} ∨ ((I ∪ J) \ {3}) = {0, 4} ∨
          3 ≤ ((I ∪ J) \ {3}).card := by
        rcases hI with rfl | rfl <;>
          rcases hJ with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
        · exfalso; exact hJnot ((distinguished_B2_v2 _).mpr (Or.inl rfl))
        · exfalso; exact hJnot ((distinguished_B2_v2 _).mpr (Or.inr rfl))
        · right; right; decide
        · left; decide
        · left; decide
        · right; right; decide
        · right; right; decide
        · right; right; decide
        · exfalso; exact hJnot ((distinguished_B2_v2 _).mpr (Or.inl rfl))
        · exfalso; exact hJnot ((distinguished_B2_v2 _).mpr (Or.inr rfl))
        · right; right; decide
        · right; right; decide
        · right; right; decide
        · right; left; decide
        · right; right; decide
        · right; left; decide
      rcases hcase with heq | heq | hge3
      · rw [heq]
        refine ⟨mdeg_monom_ge _ 2 (by decide), ?_⟩
        have hmon : monom ({1, 2} : Finset (Fin 5)) = MvPolynomial.X 1 * MvPolynomial.X 2 := by
          simp [monom]
        rw [hmon, phi2_X_mul_X]; simp
      · rw [heq]
        refine ⟨mdeg_monom_ge _ 2 (by decide), ?_⟩
        have hmon : monom ({0, 4} : Finset (Fin 5)) = MvPolynomial.X 0 * MvPolynomial.X 4 := by
          simp [monom]
        rw [hmon, phi2_X_mul_X]; simp
      · have h3 := mdeg_monom_ge ((I ∪ J) \ {3}) 3 hge3
        refine ⟨fun d hd => by have := h3 d hd; omega, ?_⟩
        have hzero : ∀ d0 : Fin 5 →₀ ℕ, mdeg d0 = 2 →
            MvPolynomial.coeff d0 (monom ((I ∪ J) \ {3})) = 0 := by
          intro d0 hd0
          by_contra hne
          have := h3 d0 (MvPolynomial.mem_support_iff.mpr hne)
          omega
        simp only [phi2, LinearMap.add_apply, LinearMap.smul_apply, MvPolynomial.lcoeff_apply,
          smul_eq_mul]
        rw [hzero _ (by simp [mdeg_add, mdeg_single]),
            hzero _ (by simp [mdeg_add, mdeg_single]),
            hzero _ (by simp [mdeg_add, mdeg_single]),
            hzero _ (by simp [mdeg_add, mdeg_single]),
            hzero _ (by simp [mdeg_add, mdeg_single]),
            hzero _ (by simp [mdeg_add, mdeg_single]),
            hzero _ (by simp [mdeg_add, mdeg_single])]
        ring
    rcases Submodule.mem_sup.mp hmem with ⟨u, hu, v, hv, huv⟩
    have h0 : phi2 (MvPolynomial.X (4 : Fin 5) * MvPolynomial.X (2 : Fin 5)) = 0 := by
      rw [← huv, map_add, hUM u hu, hP v hv, add_zero]
    have h1 : phi2 (MvPolynomial.X (4 : Fin 5) * MvPolynomial.X (2 : Fin 5)) = 1 := by
      rw [phi2_X_mul_X]; simp
    rw [h1] at h0
    exact one_ne_zero h0

theorem main_proof :
    (∃ (d n : ℕ) (A : Matrix (Fin d) (Fin n) ℤ) (B : Matrix (Fin n) (Fin 1) ℤ)
      (w : Fin n → ℝ) (v : Fin n → ℤ) (N : Set (Finset (Fin n))),
      IsHomogeneousConfig A ∧
      HasLatticeBasis A B ∧
      IsGenericWeight B w ∧
      IsFakeExponent B w v ∧
      IsOrderedNegSupportFamily B w v N ∧
      HasNonzeroObstruction A B v N) ∧
    (∃ (d n : ℕ) (A : Matrix (Fin d) (Fin n) ℤ) (B : Matrix (Fin n) (Fin 2) ℤ)
      (w : Fin n → ℝ) (v : Fin n → ℤ),
      IsHomogeneousConfig A ∧
      HasLatticeBasis A B ∧
      IsGenericWeight B w ∧
      IsFakeExponent B w v ∧
      IsOrderedNegSupportFamily B w v (distinguishedCollection B w v) ∧
      HasNonzeroObstruction A B v (distinguishedCollection B w v)) :=
  ⟨⟨4, 5, A1, B1, w1, v1, N1, A1_homog, A1_B1_basis, w1_generic, v1_fake, N1_ordered, N1_obstruction⟩,
   ⟨3, 5, A2, B2, w2, v2, A2_homog, A2_B2_basis, w2_generic, v2_fake, N2_ordered, N2_obstruction⟩⟩

end OMA.P_arxiv_2608_18006

theorem OMA.solution : type_of% @OMA.S_arxiv_2608_18006.main :=
  OMA.P_arxiv_2608_18006.main_proof
