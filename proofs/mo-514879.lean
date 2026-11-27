import OMAStatements.S_mo_514879
import Mathlib

namespace MO514879Proof

open Polynomial Finset

noncomputable section

/-! ### Step 0: Primitives on `rootsOfUnity n ℂ` -/

private lemma card_rootsOfUnity_eq (n : ℕ) [NeZero n] [Fintype (rootsOfUnity n ℂ)] :
    Fintype.card (rootsOfUnity n ℂ) = n := by
  have hn : n ≠ 0 := NeZero.ne n
  let ω : ℂ := Complex.exp (2 * Real.pi * Complex.I / n)
  have hω : IsPrimitiveRoot ω n := Complex.isPrimitiveRoot_exp n hn
  have hω_ne : ω ≠ 0 := hω.ne_zero hn
  let f : Fin n → rootsOfUnity n ℂ := fun j =>
    ⟨Units.mk0 (ω ^ j.val) (pow_ne_zero _ hω_ne), by
      rw [mem_rootsOfUnity]
      ext
      simp only [Units.val_pow_eq_pow_val, Units.val_mk0, Units.val_one]
      rw [← pow_mul, mul_comm, pow_mul, hω.pow_eq_one, one_pow]⟩
  have hbij : Function.Bijective f := by
    constructor
    · intro a b hab
      have hval : ω ^ a.val = ω ^ b.val := by
        have := congrArg (fun u : rootsOfUnity n ℂ => (u.val : ℂ)) hab
        simpa [f] using this
      exact Fin.ext (hω.injOn_pow (Finset.mem_coe.mpr (Finset.mem_range.mpr a.isLt))
        (Finset.mem_coe.mpr (Finset.mem_range.mpr b.isLt)) hval)
    · intro u
      have hu : ((u.val : ℂ)) ^ n = 1 := by
        have h1 := (mem_rootsOfUnity n u.val).mp u.property
        have h2 := congrArg (fun x : ℂˣ => (x : ℂ)) h1
        simpa using h2
      obtain ⟨j, hj, hju⟩ := hω.eq_pow_of_pow_eq_one hu
      refine ⟨⟨j, hj⟩, ?_⟩
      ext
      simpa [f] using hju
  rw [← Fintype.card_of_bijective hbij, Fintype.card_fin]

private lemma norm_rootsOfUnity {n : ℕ} [NeZero n] (u : rootsOfUnity n ℂ) :
    ‖(u.val : ℂ)‖ = 1 := by
  have hn : n ≠ 0 := NeZero.ne n
  have hu : ((u.val : ℂ)) ^ n = 1 := by
    have h1 := (mem_rootsOfUnity n u.val).mp u.property
    have h2 := congrArg (fun x : ℂˣ => (x : ℂ)) h1
    simpa using h2
  have hnorm : ‖(u.val : ℂ)‖ ^ n = 1 ^ n := by
    rw [← norm_pow, hu, norm_one, one_pow]
  exact pow_left_inj₀ (norm_nonneg _) zero_le_one hn |>.mp hnorm

/-! ### Step 1: Construction of `G ∈ ℂ[Y][T]` via multivariate evenness -/

private lemma mvpoly_coeff_signFlip {U : Type*} [DecidableEq U] {R : Type*} [CommRing R]
    (j : U) (P : MvPolynomial U R) (e : U →₀ ℕ) :
    MvPolynomial.coeff e
        (MvPolynomial.aeval (R := R)
          (fun i : U => if i = j then (-MvPolynomial.X i : MvPolynomial U R) else MvPolynomial.X i) P) =
      (-1 : R) ^ (e j) * MvPolynomial.coeff e P := by
  let τ : MvPolynomial U R →ₐ[R] MvPolynomial U R :=
    MvPolynomial.aeval (fun i : U => if i = j then -MvPolynomial.X i else MvPolynomial.X i)
  have hmono : ∀ (d : U →₀ ℕ) (c : R),
      τ (MvPolynomial.monomial d c) = MvPolynomial.monomial d ((-1 : R) ^ (d j) * c) := by
    intro d c
    rw [MvPolynomial.monomial_eq, map_mul, show τ (MvPolynomial.C c) = MvPolynomial.C c from by
      dsimp only [τ]; rw [MvPolynomial.aeval_C, MvPolynomial.algebraMap_eq]]
    rw [Finsupp.prod, map_prod]
    have hterm : ∀ i ∈ d.support,
        τ (MvPolynomial.X i ^ d i) =
          MvPolynomial.C (if i = j then (-1 : R) ^ (d i) else 1) * MvPolynomial.X i ^ d i := by
      intro i _
      rw [map_pow]
      dsimp only [τ]
      rw [MvPolynomial.aeval_X]
      split_ifs with hij
      · rw [neg_eq_neg_one_mul, mul_pow, ← map_one MvPolynomial.C, ← map_neg, ← map_pow]
      · rw [map_one, one_mul]
    rw [Finset.prod_congr rfl hterm, Finset.prod_mul_distrib, ← map_prod]
    have hprod_c : (∏ i ∈ d.support, if i = j then (-1 : R) ^ (d i) else (1 : R)) = (-1 : R) ^ (d j) := by
      by_cases hj : j ∈ d.support
      · rw [Finset.prod_eq_single j]
        · simp
        · intro i _ hij; simp [hij]
        · intro h; exact absurd hj h
      · have hdj : d j = 0 := Finsupp.notMem_support_iff.mp hj
        rw [hdj, pow_zero]
        apply Finset.prod_eq_one
        intro i hi
        have hij : i ≠ j := fun h => hj (h ▸ hi)
        simp [hij]
    rw [hprod_c, ← mul_assoc, ← map_mul, mul_comm c, MvPolynomial.monomial_eq]
    rfl
  change MvPolynomial.coeff e (τ P) = _
  conv_lhs => rw [P.as_sum]
  rw [map_sum, MvPolynomial.coeff_sum]
  simp_rw [hmono, MvPolynomial.coeff_monomial]
  by_cases he : e ∈ P.support
  · rw [Finset.sum_eq_single e]
    · simp
    · intro d _ hde; simp [hde]
    · intro h; exact absurd he h
  · have hc0 : MvPolynomial.coeff e P = 0 := MvPolynomial.notMem_support_iff.mp he
    rw [hc0, mul_zero]
    apply Finset.sum_eq_zero
    intro d hd
    have hde : d ≠ e := fun h => he (h ▸ hd)
    simp [hde]

private lemma exists_poly_G (n : ℕ) [NeZero n] [Fintype (rootsOfUnity n ℂ)] :
    ∃ G : Polynomial (Polynomial ℂ),
      ∀ (t y : ℂ) (r : rootsOfUnity n ℂ → ℂ),
        (∀ i, r i ^ 2 = t ^ 2 - (i.val : ℂ)) →
        G.eval₂ (evalRingHom y) t =
          ∏ s : Finset (rootsOfUnity n ℂ),
            (y - ∏ i, if i ∈ s then t - r i else t + r i) := by
  classical
  let U := rootsOfUnity n ℂ
  let R := Polynomial (Polynomial ℂ)
  let TR : R := Polynomial.X
  let YR : R := Polynomial.C Polynomial.X
  let Φ : MvPolynomial U R :=
    ∏ s : Finset U,
      (MvPolynomial.C YR -
        ∏ i : U, if i ∈ s then MvPolynomial.C TR - MvPolynomial.X i
                 else MvPolynomial.C TR + MvPolynomial.X i)
  have hinv : ∀ j : U,
      MvPolynomial.aeval (R := R)
        (fun i : U => if i = j then (-MvPolynomial.X i : MvPolynomial U R) else MvPolynomial.X i) Φ = Φ := by
    intro j
    let τ : MvPolynomial U R →ₐ[R] MvPolynomial U R :=
      MvPolynomial.aeval (fun i : U => if i = j then -MvPolynomial.X i else MvPolynomial.X i)
    show τ Φ = Φ
    dsimp only [Φ]
    rw [map_prod]
    let eFlip : Finset U ≃ Finset U :=
      { toFun := fun s => symmDiff s {j}
        invFun := fun s => symmDiff s {j}
        left_inv := fun s => by ext x; simp
        right_inv := fun s => by ext x; simp }
    have hτC : ∀ c : R, τ (MvPolynomial.C c) = MvPolynomial.C c := fun c => by
      dsimp only [τ]; rw [MvPolynomial.aeval_C, MvPolynomial.algebraMap_eq]
    refine Fintype.prod_equiv eFlip _ _ fun s => ?_
    rw [map_sub, hτC, map_prod]
    congr 1
    refine Finset.prod_congr rfl fun i _ => ?_
    by_cases hij : i = j
    · subst hij
      by_cases hi : i ∈ s
      · have hni : i ∉ eFlip s := by simp [eFlip, Finset.mem_symmDiff, hi]
        simp only [if_pos hi, if_neg hni, map_sub, hτC, τ, MvPolynomial.aeval_X, ↓reduceIte,
          sub_neg_eq_add]
      · have hni : i ∈ eFlip s := by simp [eFlip, Finset.mem_symmDiff, hi]
        simp only [if_neg hi, if_pos hni, map_add, hτC, τ, MvPolynomial.aeval_X, ↓reduceIte,
          ← sub_eq_add_neg]
    · have hiff : i ∈ eFlip s ↔ i ∈ s := by simp [eFlip, Finset.mem_symmDiff, hij]
      by_cases hi : i ∈ s
      · simp only [if_pos hi, if_pos (hiff.mpr hi), map_sub, hτC, τ, MvPolynomial.aeval_X,
          if_neg hij]
      · simp only [if_neg hi, if_neg (mt hiff.mp hi), map_add, hτC, τ, MvPolynomial.aeval_X,
          if_neg hij]
  have heven : ∀ e ∈ Φ.support, ∀ j : U, Even (e j) := by
    intro e he j
    by_contra hnot
    have hodd : Odd (e j) := Nat.not_even_iff_odd.mp hnot
    have hcoeff := mvpoly_coeff_signFlip j Φ e
    have hneg : (-1 : R) ^ (e j) = -1 := by
      obtain ⟨m, hm⟩ := hodd
      rw [hm, pow_add, pow_mul, show (-1 : R) ^ 2 = 1 by ring, one_pow, one_mul, pow_one]
    rw [hinv j, hneg] at hcoeff
    have h2 : (2 : R) * MvPolynomial.coeff e Φ = 0 := by
      linear_combination hcoeff
    have h2ne : (2 : R) ≠ 0 := two_ne_zero
    have hc0 : MvPolynomial.coeff e Φ = 0 := (mul_eq_zero.mp h2).resolve_left h2ne
    exact MvPolynomial.mem_support_iff.mp he hc0
  let G : R :=
    ∑ e ∈ Φ.support,
      MvPolynomial.coeff e Φ * ∏ i : U, (TR ^ 2 - Polynomial.C (Polynomial.C (i.val : ℂ))) ^ (e i / 2)
  refine ⟨G, fun t y r hr => ?_⟩
  let ψ : R →+* ℂ := Polynomial.eval₂RingHom (evalRingHom y) t
  change ψ G = _
  have hψ_TR : ψ TR = t := Polynomial.eval₂_X _ _
  have hψ_YR : ψ YR = y := by
    change (Polynomial.C Polynomial.X).eval₂ (evalRingHom y) t = y
    rw [Polynomial.eval₂_C]; simp
  have hψ_CC : ∀ c : ℂ, ψ (Polynomial.C (Polynomial.C c)) = c := fun c => by
    change (Polynomial.C (Polynomial.C c)).eval₂ (evalRingHom y) t = c
    rw [Polynomial.eval₂_C]; simp
  have hG_eval : ψ G = MvPolynomial.eval₂ ψ r Φ := by
    dsimp only [G]
    rw [map_sum, MvPolynomial.eval₂_eq']
    refine Finset.sum_congr rfl fun e he => ?_
    rw [map_mul, map_prod]
    congr 1
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [map_pow, map_sub, map_pow, hψ_TR, hψ_CC, ← hr i, ← pow_mul]
    obtain ⟨m, hm⟩ := heven e he i
    have hdiv : 2 * (e i / 2) = e i := by omega
    rw [hdiv]
  rw [hG_eval]
  dsimp only [Φ]
  rw [MvPolynomial.eval₂_prod]
  refine Finset.prod_congr rfl fun s _ => ?_
  rw [MvPolynomial.eval₂_sub, MvPolynomial.eval₂_C, hψ_YR, MvPolynomial.eval₂_prod]
  congr 1
  refine Finset.prod_congr rfl fun i _ => ?_
  split_ifs
  · rw [MvPolynomial.eval₂_sub, MvPolynomial.eval₂_C, MvPolynomial.eval₂_X, hψ_TR]
  · rw [MvPolynomial.eval₂_add, MvPolynomial.eval₂_C, MvPolynomial.eval₂_X, hψ_TR]

/-! ### Step 2: Rotational invariance and extraction of `F ∈ ℂ[Y][X]` -/

private lemma coeff_comp_C_mul_X {K : Type*} [CommRing K] (p : Polynomial K) (a : K) (d : ℕ) :
    (p.comp (Polynomial.C a * Polynomial.X)).coeff d = a ^ d * p.coeff d := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
      rw [Polynomial.add_comp, Polynomial.coeff_add, Polynomial.coeff_add, hp, hq, mul_add]
  | monomial m c =>
      rw [Polynomial.monomial_comp, mul_pow, ← map_pow, Polynomial.C_mul',
        Polynomial.coeff_smul, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
        Polynomial.coeff_monomial, smul_eq_mul]
      by_cases h : d = m
      · subst h; simp [mul_comm]
      · simp [h, Ne.symm h]

private lemma coeff_comp_X_pow {K : Type*} [CommRing K] (p : Polynomial K) {n : ℕ} (hn : 0 < n) (d : ℕ) :
    (p.comp (Polynomial.X ^ n)).coeff d = if n ∣ d then p.coeff (d / n) else 0 := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
      rw [Polynomial.add_comp, Polynomial.coeff_add, hp, hq]
      split_ifs <;> simp
  | monomial m c =>
      rw [Polynomial.monomial_comp, ← pow_mul, Polynomial.C_mul_X_pow_eq_monomial,
        Polynomial.coeff_monomial, Polynomial.coeff_monomial]
      by_cases h : n * m = d
      · have hdvd : n ∣ d := ⟨m, h.symm⟩
        have hdiv : d / n = m := by rw [← h, Nat.mul_div_right _ hn]
        simp [h, hdvd, hdiv]
      · simp only [if_neg h]
        split_ifs with hdvd heq
        · exfalso; exact h (by rw [heq, Nat.mul_div_cancel' hdvd])
        · rfl
        · rfl

private lemma exists_poly_F_of_rot_inv (n : ℕ) [NeZero n] [Fintype (rootsOfUnity n ℂ)]
    (G : Polynomial (Polynomial ℂ))
    (hG : ∀ (t y : ℂ) (r : rootsOfUnity n ℂ → ℂ),
      (∀ i, r i ^ 2 = t ^ 2 - (i.val : ℂ)) →
      G.eval₂ (evalRingHom y) t =
        ∏ s : Finset (rootsOfUnity n ℂ),
          (y - ∏ i, if i ∈ s then t - r i else t + r i)) :
    ∃ F : Polynomial (Polynomial ℂ),
      F.comp (Polynomial.X ^ n) = G ∧
      G.natDegree = F.natDegree * n ∧
      ∀ (t y : ℂ) (r : rootsOfUnity n ℂ → ℂ),
        (∀ i, r i ^ 2 = t ^ 2 - (i.val : ℂ)) →
        F.eval₂ (evalRingHom y) (t ^ n) =
          ∏ s : Finset (rootsOfUnity n ℂ),
            (y - ∏ i, if i ∈ s then t - r i else t + r i) := by
  classical
  have hn_ne : n ≠ 0 := NeZero.ne n
  have hn_pos : 0 < n := Nat.pos_of_ne_zero hn_ne
  let U := rootsOfUnity n ℂ
  let ω : ℂ := Complex.exp (2 * Real.pi * Complex.I / n)
  have hω : IsPrimitiveRoot ω n := Complex.isPrimitiveRoot_exp n hn_ne
  have hω_ne : ω ≠ 0 := hω.ne_zero hn_ne
  let uω : U := ⟨Units.mk0 ω hω_ne, by
    rw [mem_rootsOfUnity]; ext; simpa using hω.pow_eq_one⟩
  have huω_val : (uω.val : ℂ) = ω := rfl
  -- Step 2.1: G(ω * t, y) = G(t, y) for all t, y ∈ ℂ
  have hrot : ∀ t y : ℂ, G.eval₂ (evalRingHom y) (ω * t) = G.eval₂ (evalRingHom y) t := by
    intro t y
    have hex : ∀ i : U, ∃ w : ℂ, w ^ 2 = t ^ 2 - (i.val : ℂ) := fun i =>
      IsAlgClosed.exists_pow_nat_eq (t ^ 2 - (i.val : ℂ)) (by norm_num)
    choose r hr using hex
    let σ : U ≃ U := Equiv.mulLeft (uω⁻¹ ^ 2)
    let r' : U → ℂ := fun i => ω * r (σ i)
    have hr' : ∀ i : U, r' i ^ 2 = (ω * t) ^ 2 - (i.val : ℂ) := by
      intro i
      have hσ_eq : σ i = uω⁻¹ ^ 2 * i := rfl
      dsimp only [r']
      rw [mul_pow, hr, hσ_eq]
      have hσ_val : (((uω⁻¹ ^ 2 * i).val : ℂ)) = ω⁻¹ ^ 2 * (i.val : ℂ) := by
        simp [huω_val]
      rw [hσ_val, mul_sub, mul_pow, ← mul_assoc, ← mul_pow ω ω⁻¹, mul_inv_cancel₀ hω_ne, one_pow, one_mul]
    rw [hG (ω * t) y r' hr', hG t y r hr]
    let eSet : Finset U ≃ Finset U :=
      { toFun := fun s => s.map σ.toEmbedding
        invFun := fun s => s.map σ.symm.toEmbedding
        left_inv := fun s => by ext x; simp
        right_inv := fun s => by ext x; simp }
    refine Fintype.prod_equiv eSet _ _ fun s => ?_
    congr 1
    have hpull : ∀ i : U,
        (if i ∈ s then ω * t - r' i else ω * t + r' i) =
          ω * (if σ i ∈ eSet s then t - r (σ i) else t + r (σ i)) := by
      intro i
      have hiff : σ i ∈ eSet s ↔ i ∈ s := by simp [eSet]
      dsimp only [r']
      by_cases hi : i ∈ s
      · simp only [if_pos hi, if_pos (hiff.mpr hi)]; ring
      · simp only [if_neg hi, if_neg (mt hiff.mp hi)]; ring
    simp_rw [hpull]
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, card_rootsOfUnity_eq n,
      hω.pow_eq_one, one_mul]
    exact Fintype.prod_equiv σ _ _ (fun _ => rfl)
  -- Step 2.2: G.coeff d = 0 whenever ¬ n ∣ d
  have hcoeff_zero : ∀ d : ℕ, ¬ n ∣ d → G.coeff d = 0 := by
    intro d hndvd
    apply Polynomial.funext
    intro y
    rw [Polynomial.eval_zero]
    let gy : Polynomial ℂ := G.map (evalRingHom y)
    have hcomp : gy.comp (Polynomial.C ω * Polynomial.X) = gy := by
      apply Polynomial.funext
      intro t
      rw [Polynomial.eval_comp, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X,
        Polynomial.eval_map, Polynomial.eval_map]
      exact hrot t y
    have hcd := congrArg (fun p : Polynomial ℂ => p.coeff d) hcomp
    rw [coeff_comp_C_mul_X] at hcd
    have hsub : (ω ^ d - 1) * gy.coeff d = 0 := by linear_combination hcd
    have hne : ω ^ d - 1 ≠ 0 := by
      intro h0
      have h1 : ω ^ d = 1 := sub_eq_zero.mp h0
      exact hndvd (hω.dvd_of_pow_eq_one d h1)
    have hgy0 : gy.coeff d = 0 := (mul_eq_zero.mp hsub).resolve_left hne
    simpa [gy, Polynomial.coeff_map] using hgy0
  -- Step 2.3: Construct F
  let F : Polynomial (Polynomial ℂ) :=
    ∑ j ∈ Finset.range (G.natDegree / n + 1), Polynomial.monomial j (G.coeff (n * j))
  have hF_coeff : ∀ j : ℕ, F.coeff j = G.coeff (n * j) := by
    intro j
    dsimp only [F]
    rw [Polynomial.finsetSum_coeff]
    simp_rw [Polynomial.coeff_monomial]
    by_cases hj : j ∈ Finset.range (G.natDegree / n + 1)
    · rw [Finset.sum_eq_single j]
      · simp
      · intro b _ hbj; simp [hbj]
      · intro h; exact absurd hj h
    · have hgt : G.natDegree < n * j := by
        simp only [Finset.mem_range, not_lt] at hj
        rw [mul_comm]
        exact (Nat.div_lt_iff_lt_mul hn_pos).mp (Nat.lt_of_succ_le hj)
      rw [Polynomial.coeff_eq_zero_of_natDegree_lt hgt]
      apply Finset.sum_eq_zero
      intro b hb
      have hbj : b ≠ j := fun h => hj (h ▸ hb)
      simp [hbj]
  have hFG : F.comp (Polynomial.X ^ n) = G := by
    apply Polynomial.ext
    intro d
    rw [coeff_comp_X_pow F hn_pos d]
    split_ifs with hdvd
    · rw [hF_coeff, Nat.mul_div_cancel' hdvd]
    · exact (hcoeff_zero d hdvd).symm
  refine ⟨F, hFG, ?_, ?_⟩
  · rw [← hFG, Polynomial.natDegree_comp, Polynomial.natDegree_X_pow]
  · intro t y r hr
    have heval : F.eval₂ (evalRingHom y) (t ^ n) = G.eval₂ (evalRingHom y) t := by
      rw [← hFG, ← Polynomial.eval_map, ← Polynomial.eval_map, Polynomial.map_comp,
        Polynomial.map_pow, Polynomial.map_X, Polynomial.eval_comp, Polynomial.eval_pow,
        Polynomial.eval_X]
    rw [heval]
    exact hG t y r hr

/-! ### Step 3: Exact telescoping binomial sum -/

private lemma binomial_sum_step (k m : ℕ) (hm : m ≤ k) :
    ∑ j ∈ Finset.range (m + 1), (2 * k + 1).choose j * (2 * k + 1 - 2 * j) =
      (2 * k + 1) * (2 * k).choose m := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [Finset.sum_range_succ, ih (Nat.le_of_succ_le hm)]
      have hpascal : (2 * k + 1).choose (m + 1) = (2 * k).choose m + (2 * k).choose (m + 1) :=
        Nat.choose_succ_succ (2 * k) m
      have hratio : (2 * k).choose (m + 1) * (m + 1) = (2 * k).choose m * (2 * k - m) := by
        have h := Nat.choose_succ_right_eq (2 * k) m
        linarith
      zify [show 2 * (m + 1) ≤ 2 * k + 1 by omega, show m ≤ 2 * k by omega] at hpascal hratio ⊢
      rw [hpascal]
      linear_combination -2 * hratio

private lemma subset_deg_sum (k : ℕ) [Fintype (rootsOfUnity (2 * k + 1) ℂ)] :
    ∑ s : Finset (rootsOfUnity (2 * k + 1) ℂ),
        (if s.card ≤ k then (2 * k + 1) - 2 * s.card else 0) =
      (2 * k + 1) * (2 * k).choose k := by
  classical
  let U := rootsOfUnity (2 * k + 1) ℂ
  have hcardU : Fintype.card U = 2 * k + 1 := card_rootsOfUnity_eq (2 * k + 1)
  rw [← Finset.sum_filter]
  have hpart :
      (Finset.univ.filter fun s : Finset U => s.card ≤ k) =
        (Finset.range (k + 1)).biUnion (fun j => Finset.powersetCard j (Finset.univ : Finset U)) := by
    ext s
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_biUnion,
      Finset.mem_range, Finset.mem_powersetCard, Finset.subset_univ, true_and]
    constructor
    · intro h; exact ⟨s.card, Nat.lt_succ_of_le h, rfl⟩
    · rintro ⟨j, hj, rfl⟩; exact Nat.lt_succ_iff.mp hj
  rw [hpart, Finset.sum_biUnion]
  · have hterm : ∀ j ∈ Finset.range (k + 1),
        (∑ s ∈ Finset.powersetCard j (Finset.univ : Finset U), (2 * k + 1 - 2 * s.card)) =
          (2 * k + 1).choose j * (2 * k + 1 - 2 * j) := by
      intro j _
      have hcongr : ∀ s ∈ Finset.powersetCard j (Finset.univ : Finset U),
          2 * k + 1 - 2 * s.card = 2 * k + 1 - 2 * j := fun s hs => by
        rw [(Finset.mem_powersetCard.mp hs).2]
      rw [Finset.sum_congr rfl hcongr, Finset.sum_const, Finset.card_powersetCard,
        Finset.card_univ, hcardU, smul_eq_mul]
    rw [Finset.sum_congr rfl hterm]
    exact binomial_sum_step k k le_rfl
  · intro i _ j _ hij
    change Disjoint _ _
    rw [Finset.disjoint_left]
    intro s hsi hsj
    exact hij ((Finset.mem_powersetCard.mp hsi).2.symm.trans (Finset.mem_powersetCard.mp hsj).2)

/-! ### Step 4: Generic polynomial degree bounds from large real `t` and norm estimates -/

private lemma natDegree_le_of_norm_bound (p : Polynomial ℂ) (D : ℕ) (C T₀ : ℝ)
    (hC : 0 ≤ C) (hT₀ : 1 ≤ T₀)
    (hbd : ∀ t : ℝ, T₀ ≤ t → ‖p.eval (t : ℂ)‖ ≤ C * t ^ D) :
    p.natDegree ≤ D := by
  by_contra hgt
  push Not at hgt
  set d := p.natDegree
  have hp0 : p ≠ 0 := by
    intro h0; dsimp [d] at hgt; rw [h0, Polynomial.natDegree_zero] at hgt; omega
  have hlc_pos : 0 < ‖p.leadingCoeff‖ := norm_pos_iff.mpr (Polynomial.leadingCoeff_ne_zero.mpr hp0)
  have hd_ge1 : 1 ≤ d := by omega
  let B : ℝ := ∑ j ∈ Finset.range d, ‖p.coeff j‖
  have hB_nn : 0 ≤ B := Finset.sum_nonneg fun _ _ => norm_nonneg _
  set t : ℝ := max T₀ ((B + C + 1) / ‖p.leadingCoeff‖)
  have ht_T0 : T₀ ≤ t := le_max_left _ _
  have ht_1 : 1 ≤ t := le_trans hT₀ ht_T0
  have ht_pos : 0 < t := lt_of_lt_of_le zero_lt_one ht_1
  have htail : ‖p.eval (t : ℂ) - p.leadingCoeff * (t : ℂ) ^ d‖ ≤ B * t ^ (d - 1) := by
    have heval : p.eval (t : ℂ) =
        (∑ j ∈ Finset.range d, p.coeff j * (t : ℂ) ^ j) + p.leadingCoeff * (t : ℂ) ^ d := by
      rw [Polynomial.eval_eq_sum_range, Finset.sum_range_succ, Polynomial.coeff_natDegree]
    rw [heval, add_sub_cancel_right]
    calc ‖∑ j ∈ Finset.range d, p.coeff j * (t : ℂ) ^ j‖
        ≤ ∑ j ∈ Finset.range d, ‖p.coeff j * (t : ℂ) ^ j‖ := norm_sum_le _ _
      _ ≤ ∑ j ∈ Finset.range d, ‖p.coeff j‖ * t ^ (d - 1) := by
          refine Finset.sum_le_sum fun j hj => ?_
          rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht_pos]
          have hj_le : j ≤ d - 1 := by
            have := Finset.mem_range.mp hj; omega
          exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ ht_1 hj_le) (norm_nonneg _)
      _ = B * t ^ (d - 1) := by rw [← Finset.sum_mul]
  have hmain : ‖p.leadingCoeff‖ * t ^ d - B * t ^ (d - 1) ≤ ‖p.eval (t : ℂ)‖ := by
    have hnorm_lead : ‖p.leadingCoeff * (t : ℂ) ^ d‖ = ‖p.leadingCoeff‖ * t ^ d := by
      rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht_pos]
    have htri : ‖p.leadingCoeff * (t : ℂ) ^ d‖ - ‖p.eval (t : ℂ)‖ ≤
        ‖p.leadingCoeff * (t : ℂ) ^ d - p.eval (t : ℂ)‖ := norm_sub_norm_le _ _
    rw [norm_sub_rev, hnorm_lead] at htri
    linarith
  have hup : ‖p.eval (t : ℂ)‖ ≤ C * t ^ (d - 1) := by
    calc ‖p.eval (t : ℂ)‖ ≤ C * t ^ D := hbd t ht_T0
      _ ≤ C * t ^ (d - 1) := mul_le_mul_of_nonneg_left (pow_le_pow_right₀ ht_1 (by omega)) hC
  have htd_eq : t ^ d = t * t ^ (d - 1) := by
    conv_lhs => rw [show d = (d - 1) + 1 by omega, pow_succ, mul_comm]
  have htd1_pos : 0 < t ^ (d - 1) := pow_pos ht_pos _
  have hineq : ‖p.leadingCoeff‖ * t * t ^ (d - 1) ≤ (B + C) * t ^ (d - 1) := by
    rw [mul_assoc, ← htd_eq]; linarith
  have hlin : ‖p.leadingCoeff‖ * t ≤ B + C := le_of_mul_le_mul_right hineq htd1_pos
  have ht_big : (B + C + 1) / ‖p.leadingCoeff‖ ≤ t := le_max_right _ _
  have hcontra : B + C + 1 ≤ ‖p.leadingCoeff‖ * t := by
    have := mul_le_mul_of_nonneg_left ht_big hlc_pos.le
    rwa [mul_div_cancel₀ _ hlc_pos.ne'] at this
  linarith

private lemma le_natDegree_of_norm_bound (p : Polynomial ℂ) (D : ℕ) (c₀ T₀ : ℝ)
    (hc₀ : 0 < c₀) (hT₀ : 1 ≤ T₀)
    (hbd : ∀ t : ℝ, T₀ ≤ t → c₀ * t ^ D ≤ ‖p.eval (t : ℂ)‖) :
    D ≤ p.natDegree := by
  by_contra hlt
  push Not at hlt
  set d := p.natDegree
  let B : ℝ := ∑ j ∈ Finset.range (d + 1), ‖p.coeff j‖
  have hB_nn : 0 ≤ B := Finset.sum_nonneg fun _ _ => norm_nonneg _
  set t : ℝ := max T₀ ((B + 1) / c₀)
  have ht_T0 : T₀ ≤ t := le_max_left _ _
  have ht_1 : 1 ≤ t := le_trans hT₀ ht_T0
  have ht_pos : 0 < t := lt_of_lt_of_le zero_lt_one ht_1
  have hup : ‖p.eval (t : ℂ)‖ ≤ B * t ^ d := by
    rw [Polynomial.eval_eq_sum_range]
    calc ‖∑ j ∈ Finset.range (d + 1), p.coeff j * (t : ℂ) ^ j‖
        ≤ ∑ j ∈ Finset.range (d + 1), ‖p.coeff j * (t : ℂ) ^ j‖ := norm_sum_le _ _
      _ ≤ ∑ j ∈ Finset.range (d + 1), ‖p.coeff j‖ * t ^ d := by
          refine Finset.sum_le_sum fun j hj => ?_
          rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht_pos]
          have hj_le : j ≤ d := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
          exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ ht_1 hj_le) (norm_nonneg _)
      _ = B * t ^ d := by rw [← Finset.sum_mul]
  have hlo : c₀ * t ^ (d + 1) ≤ ‖p.eval (t : ℂ)‖ := by
    calc c₀ * t ^ (d + 1) ≤ c₀ * t ^ D :=
          mul_le_mul_of_nonneg_left (pow_le_pow_right₀ ht_1 (by omega)) hc₀.le
      _ ≤ ‖p.eval (t : ℂ)‖ := hbd t ht_T0
  have htd_pos : 0 < t ^ d := pow_pos ht_pos _
  have hineq : c₀ * t * t ^ d ≤ B * t ^ d := by
    rw [mul_assoc, mul_comm t, ← pow_succ]; linarith
  have hlin : c₀ * t ≤ B := le_of_mul_le_mul_right hineq htd_pos
  have ht_big : (B + 1) / c₀ ≤ t := le_max_right _ _
  have hcontra : B + 1 ≤ c₀ * t := by
    have := mul_le_mul_of_nonneg_left ht_big hc₀.le
    rwa [mul_div_cancel₀ _ hc₀.ne'] at this
  linarith

private lemma exists_good_sqrt {n : ℕ} [NeZero n] (t : ℝ) (ht : 4 ≤ t) (i : rootsOfUnity n ℂ) :
    ∃ r : ℂ, r ^ 2 = (t : ℂ) ^ 2 - (i.val : ℂ) ∧
      t ≤ ‖(t : ℂ) + r‖ ∧ ‖(t : ℂ) + r‖ ≤ 3 * t ∧
      (3 * t)⁻¹ ≤ ‖(t : ℂ) - r‖ ∧ ‖(t : ℂ) - r‖ ≤ t⁻¹ := by
  obtain ⟨r₀, hr₀⟩ := IsAlgClosed.exists_pow_nat_eq ((t : ℂ) ^ 2 - (i.val : ℂ)) (by norm_num : 0 < 2)
  let r : ℂ := if 0 ≤ r₀.re then r₀ else -r₀
  have hr_sq : r ^ 2 = (t : ℂ) ^ 2 - (i.val : ℂ) := by
    dsimp only [r]; split_ifs <;> simp [hr₀]
  have hr_re : 0 ≤ r.re := by
    dsimp only [r]; split_ifs with h
    · exact h
    · simp only [Complex.neg_re]; linarith
  have ht_pos : 0 < t := by linarith
  have hplus_ge : t ≤ ‖(t : ℂ) + r‖ := by
    have hre : ((t : ℂ) + r).re = t + r.re := by simp
    have h1 := Complex.re_le_norm ((t : ℂ) + r)
    linarith
  have hplus_pos : 0 < ‖(t : ℂ) + r‖ := lt_of_lt_of_le ht_pos hplus_ge
  have hprod : ((t : ℂ) - r) * ((t : ℂ) + r) = (i.val : ℂ) := by
    linear_combination -hr_sq
  have hnorm_prod : ‖(t : ℂ) - r‖ * ‖(t : ℂ) + r‖ = 1 := by
    rw [← norm_mul, hprod, norm_rootsOfUnity]
  have hminus_eq : ‖(t : ℂ) - r‖ = ‖(t : ℂ) + r‖⁻¹ :=
    eq_inv_of_mul_eq_one_left hnorm_prod
  have hminus_le : ‖(t : ℂ) - r‖ ≤ t⁻¹ := by
    rw [hminus_eq]
    exact inv_anti₀ ht_pos hplus_ge
  have hplus_le : ‖(t : ℂ) + r‖ ≤ 3 * t := by
    have heq : (t : ℂ) + r = (2 * t : ℝ) - ((t : ℂ) - r) := by push_cast; ring
    have htri : ‖(t : ℂ) + r‖ ≤ ‖((2 * t : ℝ) : ℂ)‖ + ‖(t : ℂ) - r‖ := by
      rw [heq]; exact norm_sub_le _ _
    have h2t : ‖((2 * t : ℝ) : ℂ)‖ = 2 * t := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]
    have hinv_le : t⁻¹ ≤ t := by
      have h1 : t⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by linarith)
      linarith
    linarith
  have hminus_ge : (3 * t)⁻¹ ≤ ‖(t : ℂ) - r‖ := by
    rw [hminus_eq]
    exact inv_anti₀ hplus_pos hplus_le
  exact ⟨r, hr_sq, hplus_ge, hplus_le, hminus_ge, hminus_le⟩

private lemma natDegree_G_eq (k : ℕ) [Fintype (rootsOfUnity (2 * k + 1) ℂ)]
    (G : Polynomial (Polynomial ℂ))
    (hG : ∀ (t y : ℂ) (r : rootsOfUnity (2 * k + 1) ℂ → ℂ),
      (∀ i, r i ^ 2 = t ^ 2 - (i.val : ℂ)) →
      G.eval₂ (evalRingHom y) t =
        ∏ s : Finset (rootsOfUnity (2 * k + 1) ℂ),
          (y - ∏ i, if i ∈ s then t - r i else t + r i)) :
    G.natDegree = (2 * k + 1) * (2 * k).choose k := by
  classical
  let n := 2 * k + 1
  let D := n * (2 * k).choose k
  let U := rootsOfUnity (2 * k + 1) ℂ
  have hcardU : Fintype.card U = n := card_rootsOfUnity_eq (2 * k + 1)
  let e : Finset U → ℕ := fun s => if s.card ≤ k then n - 2 * s.card else 0
  have hsum_e : ∑ s : Finset U, e s = D := subset_deg_sum k
  -- Helper: bounds on subset product α s for real t ≥ 4
  have hsubset_bds : ∀ (t : ℝ), 4 ≤ t →
      ∃ r : U → ℂ, (∀ i, r i ^ 2 = (t : ℂ) ^ 2 - (i.val : ℂ)) ∧
        ∀ s : Finset U,
          let α := ∏ i : U, if i ∈ s then (t : ℂ) - r i else (t : ℂ) + r i
          (s.card ≤ k → ((3 : ℝ) ^ n)⁻¹ * t ^ (n - 2 * s.card) ≤ ‖α‖ ∧
            ‖α‖ ≤ (3 : ℝ) ^ n * t ^ (n - 2 * s.card)) ∧
          (k < s.card → ‖α‖ ≤ (3 : ℝ) ^ n * t⁻¹) := by
    intro t ht
    have ht_pos : 0 < t := by linarith
    have ht_1 : 1 ≤ t := by linarith
    choose r hr_sq hp_ge hp_le hm_ge hm_le using fun i : U => exists_good_sqrt t ht i
    refine ⟨r, hr_sq, fun s => ?_⟩
    set m := s.card
    have hm_le_n : m ≤ n := by
      calc m = s.card := rfl
        _ ≤ Fintype.card U := Finset.card_le_univ s
        _ = n := hcardU
    have hcompl : (Finset.univ \ s).card = n - m := by
      rw [Finset.card_sdiff, Finset.inter_univ, Finset.card_univ, hcardU]
    have hsplit : (∏ i : U, ‖if i ∈ s then (t : ℂ) - r i else (t : ℂ) + r i‖) =
        (∏ i ∈ s, ‖(t : ℂ) - r i‖) * (∏ i ∈ Finset.univ \ s, ‖(t : ℂ) + r i‖) := by
      have hunion : (Finset.univ : Finset U) = s ∪ (Finset.univ \ s) :=
        (Finset.union_sdiff_of_subset (Finset.subset_univ s)).symm
      conv_lhs => rw [hunion]
      rw [Finset.prod_union disjoint_sdiff_self_right]
      congr 1
      · refine Finset.prod_congr rfl fun i hi => by simp [hi]
      · refine Finset.prod_congr rfl fun i hi => by
          have hni : i ∉ s := (Finset.mem_sdiff.mp hi).2
          simp [hni]
    have hnorm_α : ‖∏ i : U, if i ∈ s then (t : ℂ) - r i else (t : ℂ) + r i‖ =
        (∏ i ∈ s, ‖(t : ℂ) - r i‖) * (∏ i ∈ Finset.univ \ s, ‖(t : ℂ) + r i‖) := by
      rw [norm_prod, hsplit]
    have hα_up : ‖∏ i : U, if i ∈ s then (t : ℂ) - r i else (t : ℂ) + r i‖ ≤
        (t⁻¹) ^ m * (3 * t) ^ (n - m) := by
      rw [hnorm_α]
      refine mul_le_mul ?_ ?_ (Finset.prod_nonneg fun _ _ => norm_nonneg _) (by positivity)
      · calc ∏ i ∈ s, ‖(t : ℂ) - r i‖ ≤ ∏ _i ∈ s, t⁻¹ :=
              Finset.prod_le_prod (fun _ _ => norm_nonneg _) (fun i _ => hm_le i)
          _ = (t⁻¹) ^ m := by rw [Finset.prod_const]
      · calc ∏ i ∈ Finset.univ \ s, ‖(t : ℂ) + r i‖ ≤ ∏ _i ∈ Finset.univ \ s, (3 * t) :=
              Finset.prod_le_prod (fun _ _ => norm_nonneg _) (fun i _ => hp_le i)
          _ = (3 * t) ^ (n - m) := by rw [Finset.prod_const, hcompl]
    have hα_lo : ((3 * t)⁻¹) ^ m * t ^ (n - m) ≤
        ‖∏ i : U, if i ∈ s then (t : ℂ) - r i else (t : ℂ) + r i‖ := by
      rw [hnorm_α]
      refine mul_le_mul ?_ ?_ (by positivity) (Finset.prod_nonneg fun _ _ => norm_nonneg _)
      · calc ((3 * t)⁻¹) ^ m = ∏ _i ∈ s, (3 * t)⁻¹ := by rw [Finset.prod_const]
          _ ≤ ∏ i ∈ s, ‖(t : ℂ) - r i‖ :=
              Finset.prod_le_prod (fun _ _ => by positivity) (fun i _ => hm_ge i)
      · calc t ^ (n - m) = ∏ _i ∈ Finset.univ \ s, t := by rw [Finset.prod_const, hcompl]
          _ ≤ ∏ i ∈ Finset.univ \ s, ‖(t : ℂ) + r i‖ :=
              Finset.prod_le_prod (fun _ _ => by positivity) (fun i _ => hp_ge i)
    constructor
    · intro hmk
      have h2m : 2 * m ≤ n := by omega
      have hpow_split : t ^ (n - m) = t ^ m * t ^ (n - 2 * m) := by
        rw [← pow_add, show m + (n - 2 * m) = n - m by omega]
      constructor
      · have hsimp : ((3 * t)⁻¹) ^ m * t ^ (n - m) = ((3 : ℝ) ^ m)⁻¹ * t ^ (n - 2 * m) := by
          rw [mul_inv, mul_pow, inv_pow, inv_pow, hpow_split]
          have htm : (t ^ m)⁻¹ * t ^ m = 1 := inv_mul_cancel₀ (pow_pos ht_pos m).ne'
          calc ((3 : ℝ) ^ m)⁻¹ * (t ^ m)⁻¹ * (t ^ m * t ^ (n - 2 * m))
              = ((3 : ℝ) ^ m)⁻¹ * ((t ^ m)⁻¹ * t ^ m) * t ^ (n - 2 * m) := by ring
            _ = ((3 : ℝ) ^ m)⁻¹ * t ^ (n - 2 * m) := by rw [htm, mul_one]
        have h3le : ((3 : ℝ) ^ n)⁻¹ ≤ ((3 : ℝ) ^ m)⁻¹ :=
          inv_anti₀ (by positivity) (pow_le_pow_right₀ (by norm_num) hm_le_n)
        calc ((3 : ℝ) ^ n)⁻¹ * t ^ (n - 2 * m)
            ≤ ((3 : ℝ) ^ m)⁻¹ * t ^ (n - 2 * m) := mul_le_mul_of_nonneg_right h3le (by positivity)
          _ = ((3 * t)⁻¹) ^ m * t ^ (n - m) := hsimp.symm
          _ ≤ _ := hα_lo
      · have hsimp : (t⁻¹) ^ m * (3 * t) ^ (n - m) = (3 : ℝ) ^ (n - m) * t ^ (n - 2 * m) := by
          rw [inv_pow, mul_pow, hpow_split]
          have htm : (t ^ m)⁻¹ * t ^ m = 1 := inv_mul_cancel₀ (pow_pos ht_pos m).ne'
          calc (t ^ m)⁻¹ * ((3 : ℝ) ^ (n - m) * (t ^ m * t ^ (n - 2 * m)))
              = (3 : ℝ) ^ (n - m) * ((t ^ m)⁻¹ * t ^ m) * t ^ (n - 2 * m) := by ring
            _ = (3 : ℝ) ^ (n - m) * t ^ (n - 2 * m) := by rw [htm, mul_one]
        have h3le : (3 : ℝ) ^ (n - m) ≤ (3 : ℝ) ^ n :=
          pow_le_pow_right₀ (by norm_num) (Nat.sub_le n m)
        calc _ ≤ (t⁻¹) ^ m * (3 * t) ^ (n - m) := hα_up
          _ = (3 : ℝ) ^ (n - m) * t ^ (n - 2 * m) := hsimp
          _ ≤ (3 : ℝ) ^ n * t ^ (n - 2 * m) := mul_le_mul_of_nonneg_right h3le (by positivity)
    · intro hmk
      have h2m : n + 1 ≤ 2 * m := by omega
      have hpow_split : (t⁻¹) ^ m = (t⁻¹) ^ (n - m) * (t⁻¹) ^ (2 * m - n) := by
        rw [← pow_add, show (n - m) + (2 * m - n) = m by omega]
      have hsimp : (t⁻¹) ^ m * (3 * t) ^ (n - m) = (3 : ℝ) ^ (n - m) * (t⁻¹) ^ (2 * m - n) := by
        rw [hpow_split, mul_pow, inv_pow]
        have htnm : (t ^ (n - m))⁻¹ * t ^ (n - m) = 1 := inv_mul_cancel₀ (pow_pos ht_pos _).ne'
        calc (t ^ (n - m))⁻¹ * (t⁻¹) ^ (2 * m - n) * ((3 : ℝ) ^ (n - m) * t ^ (n - m))
            = (3 : ℝ) ^ (n - m) * ((t ^ (n - m))⁻¹ * t ^ (n - m)) * (t⁻¹) ^ (2 * m - n) := by ring
          _ = (3 : ℝ) ^ (n - m) * (t⁻¹) ^ (2 * m - n) := by rw [htnm, mul_one]
      have h3le : (3 : ℝ) ^ (n - m) ≤ (3 : ℝ) ^ n :=
        pow_le_pow_right₀ (by norm_num) (Nat.sub_le n m)
      have hinv_le : (t⁻¹) ^ (2 * m - n) ≤ t⁻¹ := by
        have hle1 : t⁻¹ ≤ 1 := inv_le_one_of_one_le₀ ht_1
        calc (t⁻¹) ^ (2 * m - n) ≤ (t⁻¹) ^ 1 :=
              pow_le_pow_of_le_one (by positivity) hle1 (by omega)
          _ = t⁻¹ := pow_one _
      calc _ ≤ (t⁻¹) ^ m * (3 * t) ^ (n - m) := hα_up
        _ = (3 : ℝ) ^ (n - m) * (t⁻¹) ^ (2 * m - n) := hsimp
        _ ≤ (3 : ℝ) ^ n * t⁻¹ := mul_le_mul h3le hinv_le (by positivity) (by positivity)
  apply le_antisymm
  · -- Upper bound: G.natDegree ≤ D
    apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
    intro d hd
    apply Polynomial.funext
    intro y
    rw [Polynomial.eval_zero]
    let gy : Polynomial ℂ := G.map (evalRingHom y)
    have hgy_deg : gy.natDegree ≤ D := by
      refine natDegree_le_of_norm_bound gy D ((‖y‖ + (3 : ℝ) ^ n) ^ Fintype.card (Finset U)) 4
        (by positivity) (by norm_num) fun t ht => ?_
      have ht_1 : 1 ≤ t := by linarith
      obtain ⟨r, hr_sq, hbds⟩ := hsubset_bds t ht
      rw [Polynomial.eval_map, hG (t : ℂ) y r hr_sq, norm_prod]
      have hfac : ∀ s : Finset U,
          ‖y - ∏ i : U, if i ∈ s then (t : ℂ) - r i else (t : ℂ) + r i‖ ≤
            (‖y‖ + (3 : ℝ) ^ n) * t ^ e s := by
        intro s
        obtain ⟨hlo_hi, hgt_hi⟩ := hbds s
        have htri := norm_sub_le y (∏ i : U, if i ∈ s then (t : ℂ) - r i else (t : ℂ) + r i)
        by_cases hsk : s.card ≤ k
        · have h1 := (hlo_hi hsk).2
          have hpow1 : 1 ≤ t ^ (n - 2 * s.card) := one_le_pow₀ ht_1
          have h2 : ‖y‖ ≤ ‖y‖ * t ^ (n - 2 * s.card) :=
            le_mul_of_one_le_right (norm_nonneg y) hpow1
          simp only [e, if_pos hsk]
          linarith
        · have hsk' : k < s.card := Nat.lt_of_not_ge hsk
          have h1 := hgt_hi hsk'
          have hinv1 : t⁻¹ ≤ 1 := inv_le_one_of_one_le₀ ht_1
          have h2 : (3 : ℝ) ^ n * t⁻¹ ≤ (3 : ℝ) ^ n :=
            mul_le_of_le_one_right (by positivity) hinv1
          simp only [e, if_neg hsk, pow_zero, mul_one]
          linarith
      calc ∏ s : Finset U, ‖y - ∏ i : U, if i ∈ s then (t : ℂ) - r i else (t : ℂ) + r i‖
          ≤ ∏ s : Finset U, ((‖y‖ + (3 : ℝ) ^ n) * t ^ e s) :=
            Finset.prod_le_prod (fun _ _ => norm_nonneg _) (fun s _ => hfac s)
        _ = (‖y‖ + (3 : ℝ) ^ n) ^ Fintype.card (Finset U) * t ^ (∑ s : Finset U, e s) := by
            rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Finset.prod_pow_eq_pow_sum]
        _ = (‖y‖ + (3 : ℝ) ^ n) ^ Fintype.card (Finset U) * t ^ D := by rw [hsum_e]
    have hcoeff0 : gy.coeff d = 0 := Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hgy_deg hd)
    simpa [gy, Polynomial.coeff_map] using hcoeff0
  · -- Lower bound: D ≤ G.natDegree via y = 1
    let g1 : Polynomial ℂ := G.map (evalRingHom (1 : ℂ))
    have hg1_deg : D ≤ g1.natDegree := by
      let c₀ : ℝ := ((2 * (3 : ℝ) ^ n)⁻¹) ^ Fintype.card (Finset U)
      let T₀ : ℝ := 2 * (3 : ℝ) ^ n + 4
      refine le_natDegree_of_norm_bound g1 D c₀ T₀ (by positivity) (by
        have : (1 : ℝ) ≤ (3 : ℝ) ^ n := one_le_pow₀ (by norm_num)
        dsimp [T₀]; linarith) fun t ht => ?_
      have ht4 : 4 ≤ t := by
        have : (0 : ℝ) ≤ 2 * (3 : ℝ) ^ n := by positivity
        dsimp [T₀] at ht; linarith
      have ht_pos : 0 < t := by linarith
      have ht_1 : 1 ≤ t := by linarith
      have ht_big : 2 * (3 : ℝ) ^ n ≤ t := by dsimp [T₀] at ht; linarith
      obtain ⟨r, hr_sq, hbds⟩ := hsubset_bds t ht4
      rw [Polynomial.eval_map, hG (t : ℂ) 1 r hr_sq, norm_prod]
      have hfac : ∀ s : Finset U,
          (2 * (3 : ℝ) ^ n)⁻¹ * t ^ e s ≤
            ‖(1 : ℂ) - ∏ i : U, if i ∈ s then (t : ℂ) - r i else (t : ℂ) + r i‖ := by
        intro s
        obtain ⟨hlo_hi, hgt_hi⟩ := hbds s
        set α := ∏ i : U, if i ∈ s then (t : ℂ) - r i else (t : ℂ) + r i
        by_cases hsk : s.card ≤ k
        · have h1 := (hlo_hi hsk).1
          have hpow_ge : t ≤ t ^ (n - 2 * s.card) := by
            calc t = t ^ 1 := (pow_one t).symm
              _ ≤ t ^ (n - 2 * s.card) := pow_le_pow_right₀ ht_1 (by omega)
          have h2le : (2 : ℝ) ≤ ((3 : ℝ) ^ n)⁻¹ * t ^ (n - 2 * s.card) := by
            have h3p : (0 : ℝ) < (3 : ℝ) ^ n := by positivity
            have := mul_le_mul_of_nonneg_left (le_trans ht_big hpow_ge) (inv_nonneg.mpr h3p.le)
            rw [mul_comm (2 : ℝ), ← mul_assoc, inv_mul_cancel₀ h3p.ne', one_mul] at this
            exact this
          have hrev : ‖α‖ - 1 ≤ ‖(1 : ℂ) - α‖ := by
            have h := norm_sub_norm_le α 1
            rw [norm_one, norm_sub_rev] at h
            exact h
          have hhalf : (2 * (3 : ℝ) ^ n)⁻¹ * t ^ (n - 2 * s.card) =
              (1 / 2 : ℝ) * (((3 : ℝ) ^ n)⁻¹ * t ^ (n - 2 * s.card)) := by
            rw [mul_inv]; ring
          simp only [e, if_pos hsk]
          linarith
        · have hsk' : k < s.card := Nat.lt_of_not_ge hsk
          have h1 := hgt_hi hsk'
          have hhalf_ub : (3 : ℝ) ^ n * t⁻¹ ≤ 1 / 2 := by
            rw [← div_eq_mul_inv, div_le_iff₀ ht_pos]
            linarith
          have hrev : 1 - ‖α‖ ≤ ‖(1 : ℂ) - α‖ := by
            have h := norm_sub_norm_le (1 : ℂ) α
            rwa [norm_one] at h
          have h3ge1 : (1 : ℝ) ≤ (3 : ℝ) ^ n := one_le_pow₀ (by norm_num)
          have hinv_le : (2 * (3 : ℝ) ^ n)⁻¹ ≤ 1 / 2 := by
            rw [one_div]
            exact inv_anti₀ (by norm_num) (by linarith)
          simp only [e, if_neg hsk, pow_zero, mul_one]
          linarith
      calc c₀ * t ^ D
          = ((2 * (3 : ℝ) ^ n)⁻¹) ^ Fintype.card (Finset U) * t ^ (∑ s : Finset U, e s) := by
            rw [hsum_e]
        _ = ∏ s : Finset U, ((2 * (3 : ℝ) ^ n)⁻¹ * t ^ e s) := by
            rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Finset.prod_pow_eq_pow_sum]
        _ ≤ ∏ s : Finset U, ‖(1 : ℂ) - ∏ i : U, if i ∈ s then (t : ℂ) - r i else (t : ℂ) + r i‖ :=
            Finset.prod_le_prod (fun _ _ => by positivity) (fun s _ => hfac s)
    exact le_trans hg1_deg Polynomial.natDegree_map_le

/-! ### Step 5: Main theorem -/

lemma main_proof (k : ℕ) [Fintype (rootsOfUnity (2 * k + 1) ℂ)] :
    ∃ F : Polynomial (Polynomial ℂ),
      F.natDegree = (2 * k).choose k ∧
      ∀ (t y : ℂ) (r : rootsOfUnity (2 * k + 1) ℂ → ℂ),
        (∀ i, r i ^ 2 = t ^ 2 - (i.val : ℂ)) →
        F.eval₂ (evalRingHom y) (t ^ (2 * k + 1)) =
          ∏ s : Finset (rootsOfUnity (2 * k + 1) ℂ),
            (y - ∏ i, if i ∈ s then t - r i else t + r i) := by
  obtain ⟨G, hG⟩ := exists_poly_G (2 * k + 1)
  obtain ⟨F, _, hdeg_rel, hF_eval⟩ := exists_poly_F_of_rot_inv (2 * k + 1) G hG
  have hdegG : G.natDegree = (2 * k + 1) * (2 * k).choose k := natDegree_G_eq k G hG
  have hdegF : F.natDegree = (2 * k).choose k := by
    have hmul : F.natDegree * (2 * k + 1) = (2 * k).choose k * (2 * k + 1) := by
      rw [← hdeg_rel, hdegG, mul_comm]
    exact Nat.eq_of_mul_eq_mul_right (Nat.succ_pos (2 * k)) hmul
  exact ⟨F, hdegF, hF_eval⟩

end
end MO514879Proof

theorem OMA.solution : type_of% @OMA.S_mo_514879.main := fun k =>
  @MO514879Proof.main_proof k (Fintype.ofFinite _)
