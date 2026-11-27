import OMAReductions.R_PfisterPythagorasNumber_pfister_problem_variants_lower_bound_R1

/-!
# Proof of PfisterPythagorasNumber.pfister_problem.variants.lower_bound.R1.H2 (Cassels 1964)

We prove Cassels' 1964 variable-adjunction theorem: if `f ∈ ℝ[X_0, ..., X_{k-1}]` is not a sum
of `m` squares in `ℝ(X_0, ..., X_{k-1})`, then `f + X_k^2` is not a sum of `m + 1` squares in
`ℝ(X_0, ..., X_k)`.

The proof has four self-contained parts:
1. `K = MvRatFunc (Fin k) ℝ` is formally real (sums of squares vanish only trivially).
2. Canonical embedding `MvRatFunc (Fin (k + 1)) ℝ →+* RatFunc K` sending `X_k ↦ X`.
3. Cassels' polynomial descent theorem in `K[X]`: if `P ∈ K[X]` is a sum of `n` squares in
   `RatFunc K`, then `P` is already a sum of `n` squares in `K[X]`.
4. Degree-1 extraction and Householder reflection in `K^{m+1}` showing `C a + X^2 = ∑ g_i^2`
   forces `a` to be a sum of `m` squares in `K`.
-/

-- Proof of step PfisterPythagorasNumber.pfister_problem.variants.lower_bound.R1.H2
-- Credit: @mvanhorn

section Cassels1964

open scoped Polynomial

private lemma isSumSqOfLength_map {R S : Type*} [Semiring R] [Semiring S] (φ : R →+* S)
    {n : ℕ} {x : R} (hx : IsSumSqOfLength n x) : IsSumSqOfLength n (φ x) := by
  rcases hx with ⟨g, hg⟩
  refine ⟨fun i => φ (g i), ?_⟩
  rw [hg, map_sum]
  exact Finset.sum_congr rfl fun i _ => map_mul φ (g i) (g i)

private lemma mvPoly_eq_zero_of_eval_eq_zero :
    ∀ (k : ℕ) (p : MvPolynomial (Fin k) ℝ),
      (∀ x : Fin k → ℝ, MvPolynomial.eval x p = 0) → p = 0 := by
  intro k
  induction k with
  | zero =>
    intro p hp
    ext m
    have hm : m = 0 := Subsingleton.elim m 0
    subst hm
    have hzero : (0 : Fin 0 → ℝ) = Fin.elim0 := Subsingleton.elim _ _
    rw [MvPolynomial.coeff_zero, ← MvPolynomial.constantCoeff_eq, ← MvPolynomial.eval_zero,
      hzero, hp Fin.elim0]
  | succ k ih =>
    intro p hp
    let e := MvPolynomial.finSuccEquiv ℝ k
    apply e.injective
    rw [map_zero]
    apply Polynomial.ext
    intro d
    rw [Polynomial.coeff_zero]
    apply ih
    intro x
    have hpoly : (Polynomial.map (MvPolynomial.eval x) (e p)) = 0 := by
      apply Polynomial.eq_zero_of_infinite_isRoot
      refine Set.infinite_univ.mono ?_
      intro t _
      change Polynomial.eval t (Polynomial.map (MvPolynomial.eval x) (e p)) = 0
      rw [← MvPolynomial.eval_eq_eval_mv_eval']
      exact hp (Fin.cons t x)
    have hcoeff := congr_arg (fun q => Polynomial.coeff q d) hpoly
    simpa [Polynomial.coeff_map] using hcoeff

private lemma mvRatFunc_sum_sq_eq_zero (k n : ℕ) (g : Fin n → MvRatFunc (Fin k) ℝ)
    (hg : ∑ i, g i * g i = 0) : ∀ i, g i = 0 := by
  let R := MvPolynomial (Fin k) ℝ
  let K := MvRatFunc (Fin k) ℝ
  let M := nonZeroDivisors R
  let sec := fun i => IsLocalization.sec M (g i)
  let D : R := ∏ i : Fin n, ((sec i).2 : R)
  have hD_mem : D ∈ M := prod_mem fun i _ => (sec i).2.2
  have hD_ne : algebraMap R K D ≠ 0 := by
    intro h0
    have hD0 : D = 0 := IsFractionRing.injective R K (by simpa using h0)
    exact (nonZeroDivisors.ne_zero hD_mem) hD0
  let h : Fin n → R := fun i =>
    (sec i).1 * ∏ j ∈ Finset.univ.erase i, ((sec j).2 : R)
  have hh_spec : ∀ i, algebraMap R K (h i) = algebraMap R K D * g i := by
    intro i
    have hprod : D = ((sec i).2 : R) * ∏ j ∈ Finset.univ.erase i, ((sec j).2 : R) := by
      dsimp [D]
      exact (Finset.mul_prod_erase Finset.univ (fun j => ((sec j).2 : R)) (Finset.mem_univ i)).symm
    have hsec : algebraMap R K ((sec i).2 : R) * g i = algebraMap R K (sec i).1 := by
      simpa [mul_comm] using IsLocalization.sec_spec M (g i)
    calc algebraMap R K (h i)
        = algebraMap R K (sec i).1 *
            algebraMap R K (∏ j ∈ Finset.univ.erase i, ((sec j).2 : R)) := by
          dsimp [h]; exact map_mul _ _ _
      _ = (algebraMap R K ((sec i).2 : R) * g i) *
            algebraMap R K (∏ j ∈ Finset.univ.erase i, ((sec j).2 : R)) := by
          rw [hsec]
      _ = (algebraMap R K ((sec i).2 : R) *
            algebraMap R K (∏ j ∈ Finset.univ.erase i, ((sec j).2 : R))) * g i := by
          ring
      _ = algebraMap R K D * g i := by
          rw [← map_mul, ← hprod]
  have hsum_K : algebraMap R K (∑ i, h i * h i) = 0 := by
    rw [map_sum]
    calc ∑ i, algebraMap R K (h i * h i)
        = ∑ i, (algebraMap R K D * g i) * (algebraMap R K D * g i) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [map_mul, hh_spec i]
      _ = (algebraMap R K D * algebraMap R K D) * ∑ i, g i * g i := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun i _ => by ring
      _ = 0 := by rw [hg, mul_zero]
  have hsum_R : ∑ i, h i * h i = 0 :=
    IsFractionRing.injective R K (by simpa using hsum_K)
  have hh_zero : ∀ i, h i = 0 := by
    intro i
    apply mvPoly_eq_zero_of_eval_eq_zero
    intro x
    have hev : ∑ j : Fin n, MvPolynomial.eval x (h j) * MvPolynomial.eval x (h j) = 0 := by
      have h0 := congr_arg (MvPolynomial.eval x) hsum_R
      simpa [map_sum, map_mul] using h0
    have hterm : MvPolynomial.eval x (h i) * MvPolynomial.eval x (h i) = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => mul_self_nonneg _)).mp hev i (Finset.mem_univ i)
    exact mul_self_eq_zero.mp hterm
  intro i
  have h0 : algebraMap R K D * g i = 0 := by
    rw [← hh_spec i, hh_zero i, map_zero]
  exact (mul_eq_zero.mp h0).resolve_left hD_ne

private lemma poly_sum_sq_coeff_top {K : Type*} [Field K] {n : ℕ}
    (p : Fin n → Polynomial K) (d : ℕ) (hd : ∀ i, (p i).natDegree ≤ d) :
    (∑ i, p i * p i).coeff (2 * d) = ∑ i, (p i).coeff d * (p i).coeff d := by
  rw [Polynomial.finsetSum_coeff]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Polynomial.coeff_mul]
  apply Finset.sum_eq_single (d, d)
  · rintro ⟨a, b⟩ hab hne
    have hab' : a + b = 2 * d := by simpa using hab
    by_cases ha : d < a
    · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt (hd i) ha), zero_mul]
    · have hb : d < b := by
        have : a ≠ d ∨ b ≠ d := by
          by_contra h
          push Not at h
          exact hne (Prod.ext h.1 h.2)
        omega
      rw [Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt (hd i) hb), mul_zero]
  · intro hmem
    exfalso
    exact hmem (by simp; omega)

private lemma poly_sum_sq_eq_zero {K : Type*} [Field K]
    (hreal : ∀ (n : ℕ) (c : Fin n → K), ∑ i, c i * c i = 0 → ∀ i, c i = 0)
    {n : ℕ} (p : Fin n → Polynomial K) (hp : ∑ i, p i * p i = 0) :
    ∀ i, p i = 0 := by
  classical
  by_contra hne
  push Not at hne
  rcases hne with ⟨i0, hi0⟩
  let S : Finset (Fin n) := Finset.univ.filter fun i => p i ≠ 0
  have hS : S.Nonempty := ⟨i0, Finset.mem_filter.mpr ⟨Finset.mem_univ i0, hi0⟩⟩
  obtain ⟨imax, himax_mem, himax_eq⟩ := Finset.exists_mem_eq_sup S hS (fun i => (p i).natDegree)
  set d : ℕ := S.sup (fun i => (p i).natDegree)
  have hd : ∀ i, (p i).natDegree ≤ d := by
    intro i
    by_cases hi : p i = 0
    · simp [hi]
    · exact Finset.le_sup (f := fun i => (p i).natDegree)
        (Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩)
  have htop : ∑ i, (p i).coeff d * (p i).coeff d = 0 := by
    rw [← poly_sum_sq_coeff_top p d hd, hp, Polynomial.coeff_zero]
  have hcoeff0 := hreal n (fun i => (p i).coeff d) htop imax
  have himax_ne : p imax ≠ 0 := (Finset.mem_filter.mp himax_mem).2
  have hlead : (p imax).coeff d = (p imax).leadingCoeff := by
    rw [Polynomial.leadingCoeff, himax_eq]
  rw [hlead] at hcoeff0
  exact himax_ne (Polynomial.leadingCoeff_eq_zero.mp hcoeff0)

private lemma poly_sum_sq_natDegree_le {K : Type*} [Field K]
    (hreal : ∀ (n : ℕ) (c : Fin n → K), ∑ i, c i * c i = 0 → ∀ i, c i = 0)
    {n : ℕ} (p : Fin n → Polynomial K) (P : Polynomial K)
    (hp : ∑ i, p i * p i = P) (m : ℕ) (hP : P.natDegree ≤ 2 * m) :
    ∀ i, (p i).natDegree ≤ m := by
  classical
  by_contra hgt
  push Not at hgt
  rcases hgt with ⟨i0, hi0⟩
  let S : Finset (Fin n) := Finset.univ.filter fun i => p i ≠ 0
  have hi0_ne : p i0 ≠ 0 := by
    intro h0; simp [h0] at hi0
  have hS : S.Nonempty := ⟨i0, Finset.mem_filter.mpr ⟨Finset.mem_univ i0, hi0_ne⟩⟩
  obtain ⟨imax, himax_mem, himax_eq⟩ := Finset.exists_mem_eq_sup S hS (fun i => (p i).natDegree)
  set d : ℕ := S.sup (fun i => (p i).natDegree)
  have hd : ∀ i, (p i).natDegree ≤ d := by
    intro i
    by_cases hi : p i = 0
    · simp [hi]
    · exact Finset.le_sup (f := fun i => (p i).natDegree)
        (Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩)
  have hdm : m < d := lt_of_lt_of_le hi0 (hd i0)
  have hP0 : P.coeff (2 * d) = 0 :=
    Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
  have htop : ∑ i, (p i).coeff d * (p i).coeff d = 0 := by
    rw [← poly_sum_sq_coeff_top p d hd, hp, hP0]
  have hcoeff0 := hreal n (fun i => (p i).coeff d) htop imax
  have himax_ne : p imax ≠ 0 := (Finset.mem_filter.mp himax_mem).2
  have hlead : (p imax).coeff d = (p imax).leadingCoeff := by
    rw [Polynomial.leadingCoeff, himax_eq]
  rw [hlead] at hcoeff0
  exact himax_ne (Polynomial.leadingCoeff_eq_zero.mp hcoeff0)

private lemma cassels_poly_descent {K : Type*} [Field K]
    (hreal : ∀ (n : ℕ) (c : Fin n → K), ∑ i, c i * c i = 0 → ∀ i, c i = 0)
    {n : ℕ} (P : Polynomial K) :
    ∀ (d : ℕ) (p0 : Polynomial K) (p : Fin n → Polynomial K),
      p0 ≠ 0 → p0.natDegree = d → p0 ^ 2 * P = ∑ i, p i * p i →
      ∃ q : Fin n → Polynomial K, P = ∑ i, q i * q i := by
  intro d
  induction d using Nat.strong_induction_on with
  | h d ih =>
    intro p0 p hp0 hdeg hrep
    by_cases hd0 : d = 0
    · have hp0_deg : p0.natDegree = 0 := hdeg.trans hd0
      set c0 : K := p0.coeff 0
      have hc_eq : p0 = Polynomial.C c0 := Polynomial.eq_C_of_natDegree_eq_zero hp0_deg
      have hc_ne : c0 ≠ 0 := by
        intro hc0; exact hp0 (by rw [hc_eq, hc0, map_zero])
      refine ⟨fun i => Polynomial.C c0⁻¹ * p i, ?_⟩
      have hmul : Polynomial.C c0⁻¹ ^ 2 * (p0 ^ 2 * P) = P := by
        rw [hc_eq, ← mul_assoc, ← mul_pow, ← map_mul, inv_mul_cancel₀ hc_ne, map_one, one_pow, one_mul]
      rw [← hmul, hrep, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => by ring
    · let q : Fin n → Polynomial K := fun i => p i / p0
      let r : Fin n → Polynomial K := fun i => p i % p0
      have hdiv : ∀ i, p i = p0 * q i + r i := fun i => (EuclideanDomain.div_add_mod (p i) p0).symm
      by_cases hall : ∀ i, r i = 0
      · refine ⟨q, ?_⟩
        have hsq_ne : p0 ^ 2 ≠ 0 := pow_ne_zero 2 hp0
        apply mul_left_cancel₀ hsq_ne
        rw [hrep, Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [hdiv i, hall i, add_zero]
        ring
      · have hS_ne : ∑ i, r i * r i ≠ 0 := by
          intro hS0
          exact hall (poly_sum_sq_eq_zero hreal r hS0)
        set Qq : Polynomial K := P - ∑ i, q i * q i
        set Bpq : Polynomial K := P * p0 - ∑ i, p i * q i
        set p0' : Polynomial K := Qq * p0 - 2 * Bpq
        let p' : Fin n → Polynomial K := fun i => Qq * p i - 2 * Bpq * q i
        have hrep' : p0' ^ 2 * P = ∑ i, p' i * p' i := by
          have hsum_p' : ∑ i, p' i * p' i =
              Qq ^ 2 * (∑ i, p i * p i) - 4 * Qq * Bpq * (∑ i, p i * q i) +
                4 * Bpq ^ 2 * (∑ i, q i * q i) := by
            have hterm : ∀ i, p' i * p' i =
                Qq ^ 2 * (p i * p i) - 4 * Qq * Bpq * (p i * q i) + 4 * Bpq ^ 2 * (q i * q i) := by
              intro i; dsimp [p']; ring
            simp_rw [hterm, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
          rw [hsum_p', ← hrep]
          have h1 : ∑ i, q i * q i = P - Qq := by dsimp [Qq]; ring
          have h2 : ∑ i, p i * q i = P * p0 - Bpq := by dsimp [Bpq]; ring
          rw [h1, h2]
          dsimp [p0']
          ring
        have hprod : p0 * p0' = -(∑ i, r i * r i) := by
          have hsum_p2 : ∑ i, p i * p i =
              p0 ^ 2 * (∑ i, q i * q i) + 2 * p0 * (∑ i, q i * r i) + ∑ i, r i * r i := by
            have hterm : ∀ i, p i * p i =
                p0 ^ 2 * (q i * q i) + 2 * p0 * (q i * r i) + r i * r i := by
              intro i; rw [hdiv i]; ring
            simp_rw [hterm, Finset.sum_add_distrib, ← Finset.mul_sum]
          have hsum_pq : ∑ i, p i * q i = p0 * (∑ i, q i * q i) + ∑ i, q i * r i := by
            have hterm : ∀ i, p i * q i = p0 * (q i * q i) + q i * r i := by
              intro i; rw [hdiv i]; ring
            simp_rw [hterm, Finset.sum_add_distrib, ← Finset.mul_sum]
          have hB : Bpq = p0 * Qq - ∑ i, q i * r i := by
            dsimp [Bpq, Qq]
            rw [hsum_pq]
            ring
          have hQ : p0 ^ 2 * Qq = 2 * p0 * (∑ i, q i * r i) + ∑ i, r i * r i := by
            dsimp [Qq]
            rw [mul_sub, hrep, hsum_p2]
            ring
          calc p0 * p0' = p0 * (Qq * p0 - 2 * Bpq) := rfl
            _ = p0 * (Qq * p0 - 2 * (p0 * Qq - ∑ i, q i * r i)) := by rw [hB]
            _ = -(p0 ^ 2 * Qq - 2 * p0 * (∑ i, q i * r i)) := by ring
            _ = -(∑ i, r i * r i) := by rw [hQ]; ring
        have hp0'_ne : p0' ≠ 0 := by
          intro h0
          rw [h0, mul_zero] at hprod
          exact hS_ne (neg_eq_zero.mp hprod.symm)
        have hr_deg : ∀ i, (r i * r i).natDegree < 2 * d := by
          intro i
          by_cases hri : r i = 0
          · simp [hri]; omega
          · have hlt : (r i).degree < p0.degree := Polynomial.degree_mod_lt (p i) hp0
            have hnat : (r i).natDegree < p0.natDegree := by
              rw [Polynomial.degree_eq_natDegree hri, Polynomial.degree_eq_natDegree hp0] at hlt
              exact Nat.cast_lt.mp hlt
            have hsq : (r i * r i).natDegree = (r i).natDegree + (r i).natDegree :=
              Polynomial.natDegree_mul hri hri
            omega
        have hS_deg : (∑ i, r i * r i).natDegree < 2 * d := by
          by_cases hne_n : n = 0
          · subst hne_n; exfalso; exact hS_ne (by simp)
          · have hle : (∑ i, r i * r i).natDegree ≤
                Finset.univ.sup (fun i => (r i * r i).natDegree) :=
              Polynomial.natDegree_sum_le _ _
            have hsup : Finset.univ.sup (fun i => (r i * r i).natDegree) < 2 * d := by
              rw [Finset.sup_lt_iff (by omega : 0 < 2 * d)]
              intro i _
              exact hr_deg i
            exact lt_of_le_of_lt hle hsup
        have hdeg' : p0'.natDegree < d := by
          have hmul_deg : (p0 * p0').natDegree = p0.natDegree + p0'.natDegree :=
            Polynomial.natDegree_mul hp0 hp0'_ne
          rw [hprod, Polynomial.natDegree_neg] at hmul_deg
          omega
        exact ih p0'.natDegree hdeg' p0' p' hp0'_ne rfl hrep'

private lemma cassels_ratFunc_to_poly {K : Type*} [Field K]
    (hreal : ∀ (n : ℕ) (c : Fin n → K), ∑ i, c i * c i = 0 → ∀ i, c i = 0)
    {n : ℕ} (P : Polynomial K)
    (hsq : IsSumSqOfLength n (algebraMap (Polynomial K) (RatFunc K) P)) :
    ∃ q : Fin n → Polynomial K, P = ∑ i, q i * q i := by
  rcases hsq with ⟨g, hg⟩
  let M := nonZeroDivisors (Polynomial K)
  let sec := fun i => IsLocalization.sec M (g i)
  let p0 : Polynomial K := ∏ i : Fin n, ((sec i).2 : Polynomial K)
  have hp0_mem : p0 ∈ M := prod_mem fun i _ => (sec i).2.2
  have hp0_ne : p0 ≠ 0 := nonZeroDivisors.ne_zero hp0_mem
  let p : Fin n → Polynomial K := fun i =>
    (sec i).1 * ∏ j ∈ Finset.univ.erase i, ((sec j).2 : Polynomial K)
  have hp_spec : ∀ i, algebraMap (Polynomial K) (RatFunc K) (p i) =
      algebraMap (Polynomial K) (RatFunc K) p0 * g i := by
    intro i
    have hprod : p0 = ((sec i).2 : Polynomial K) *
        ∏ j ∈ Finset.univ.erase i, ((sec j).2 : Polynomial K) := by
      dsimp [p0]
      exact (Finset.mul_prod_erase Finset.univ (fun j => ((sec j).2 : Polynomial K))
        (Finset.mem_univ i)).symm
    have hsec : algebraMap (Polynomial K) (RatFunc K) ((sec i).2 : Polynomial K) * g i =
        algebraMap (Polynomial K) (RatFunc K) (sec i).1 := by
      simpa [mul_comm] using IsLocalization.sec_spec M (g i)
    calc algebraMap (Polynomial K) (RatFunc K) (p i)
        = algebraMap (Polynomial K) (RatFunc K) (sec i).1 *
            algebraMap (Polynomial K) (RatFunc K)
              (∏ j ∈ Finset.univ.erase i, ((sec j).2 : Polynomial K)) := by
          dsimp [p]; exact map_mul _ _ _
      _ = (algebraMap (Polynomial K) (RatFunc K) ((sec i).2 : Polynomial K) * g i) *
            algebraMap (Polynomial K) (RatFunc K)
              (∏ j ∈ Finset.univ.erase i, ((sec j).2 : Polynomial K)) := by
          rw [hsec]
      _ = (algebraMap (Polynomial K) (RatFunc K) ((sec i).2 : Polynomial K) *
            algebraMap (Polynomial K) (RatFunc K)
              (∏ j ∈ Finset.univ.erase i, ((sec j).2 : Polynomial K))) * g i := by
          ring
      _ = algebraMap (Polynomial K) (RatFunc K) p0 * g i := by
          rw [← map_mul, ← hprod]
  have hrep_rf : algebraMap (Polynomial K) (RatFunc K) (p0 ^ 2 * P) =
      algebraMap (Polynomial K) (RatFunc K) (∑ i, p i * p i) := by
    rw [map_mul, map_pow, hg, map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul, hp_spec i]
    ring
  have hrep : p0 ^ 2 * P = ∑ i, p i * p i :=
    IsFractionRing.injective (Polynomial K) (RatFunc K) hrep_rf
  exact cassels_poly_descent hreal P p0.natDegree p0 p hp0_ne rfl hrep

private lemma cassels_add_sq_step {K : Type*} [Field K]
    (hreal : ∀ (n : ℕ) (c : Fin n → K), ∑ i, c i * c i = 0 → ∀ i, c i = 0)
    (h2 : (2 : K) ≠ 0) (m : ℕ) (a : K)
    (hsq : IsSumSqOfLength (m + 1)
      (algebraMap (Polynomial K) (RatFunc K) (Polynomial.C a + Polynomial.X ^ 2))) :
    IsSumSqOfLength m a := by
  obtain ⟨g, hg⟩ := cassels_ratFunc_to_poly hreal (Polynomial.C a + Polynomial.X ^ 2) hsq
  have hP_deg : (Polynomial.C a + Polynomial.X ^ 2 : Polynomial K).natDegree ≤ 2 := by
    calc (Polynomial.C a + Polynomial.X ^ 2 : Polynomial K).natDegree
        ≤ max (Polynomial.C a).natDegree (Polynomial.X ^ 2 : Polynomial K).natDegree :=
          Polynomial.natDegree_add_le _ _
      _ ≤ 2 := by simp
  have hg_deg : ∀ i, (g i).natDegree ≤ 1 :=
    poly_sum_sq_natDegree_le hreal g (Polynomial.C a + Polynomial.X ^ 2) hg.symm 1 hP_deg
  let b : Fin (m + 1) → K := fun i => (g i).coeff 0
  let c : Fin (m + 1) → K := fun i => (g i).coeff 1
  have hg_lin : ∀ i, g i = Polynomial.C (b i) + Polynomial.C (c i) * Polynomial.X := by
    intro i
    ext d
    rcases d with _ | _ | d
    · simp [b]
    · simp [c]
    · simp [Polynomial.coeff_eq_zero_of_natDegree_lt (by have := hg_deg i; omega : (g i).natDegree < d + 2)]
  have hsum_lin : Polynomial.C a + Polynomial.X ^ 2 =
      Polynomial.C (∑ i, b i * b i) +
      Polynomial.C (2 * ∑ i, b i * c i) * Polynomial.X +
      Polynomial.C (∑ i, c i * c i) * Polynomial.X ^ 2 := by
    rw [hg]
    have hterm : ∀ i, g i * g i =
        Polynomial.C (b i * b i) +
        Polynomial.C (2 * (b i * c i)) * Polynomial.X +
        Polynomial.C (c i * c i) * Polynomial.X ^ 2 := by
      intro i
      rw [hg_lin i]
      simp only [map_mul, map_ofNat]
      ring
    simp_rw [hterm, Finset.sum_add_distrib, ← Finset.sum_mul, ← map_sum, ← Finset.mul_sum]
  have ha_eq : ∑ i, b i * b i = a := by
    have h0 := congr_arg (fun q => Polynomial.coeff q 0) hsum_lin
    simp only [Polynomial.coeff_add, Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_C_mul_X,
      Polynomial.coeff_C, Polynomial.coeff_X_pow] at h0
    simpa using h0.symm
  have hbc_eq : ∑ i, b i * c i = 0 := by
    have h1 := congr_arg (fun q => Polynomial.coeff q 1) hsum_lin
    simp only [Polynomial.coeff_add, Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_C_mul_X,
      Polynomial.coeff_C, Polynomial.coeff_X_pow] at h1
    have h2bc : 2 * ∑ i, b i * c i = 0 := by simpa using h1.symm
    exact (mul_eq_zero.mp h2bc).resolve_left h2
  have hc_eq : ∑ i, c i * c i = 1 := by
    have h2c := congr_arg (fun q => Polynomial.coeff q 2) hsum_lin
    simp only [Polynomial.coeff_add, Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_C_mul_X,
      Polynomial.coeff_C, Polynomial.coeff_X_pow] at h2c
    simpa using h2c.symm
  by_cases hc0 : c 0 = 1
  · have htail_c : ∑ i : Fin m, c i.succ * c i.succ = 0 := by
      rw [Fin.sum_univ_succ, hc0, one_mul] at hc_eq
      exact add_left_cancel (hc_eq.trans (add_zero 1).symm)
    have hc_zero : ∀ i : Fin m, c i.succ = 0 := hreal m (fun i => c i.succ) htail_c
    have hb0 : b 0 = 0 := by
      rw [Fin.sum_univ_succ, hc0, mul_one] at hbc_eq
      have htail_bc : ∑ i : Fin m, b i.succ * c i.succ = 0 :=
        Finset.sum_eq_zero fun i _ => by rw [hc_zero i, mul_zero]
      rw [htail_bc, add_zero] at hbc_eq
      exact hbc_eq
    refine ⟨fun i => b i.succ, ?_⟩
    rw [← ha_eq, Fin.sum_univ_succ, hb0, zero_mul, zero_add]
  · have hden : (1 - c 0 : K) ≠ 0 := sub_ne_zero.mpr (Ne.symm hc0)
    let w : Fin (m + 1) → K := Fin.cons (c 0 - 1) (fun i => c i.succ)
    let lam : K := b 0 / (1 - c 0)
    let b' : Fin (m + 1) → K := fun i => b i + lam * w i
    have hw_sq : ∑ i, w i * w i = 2 * (1 - c 0) := by
      rw [Fin.sum_univ_succ]
      simp only [w, Fin.cons_zero, Fin.cons_succ]
      rw [Fin.sum_univ_succ] at hc_eq
      have htail : ∑ i : Fin m, c i.succ * c i.succ = 1 - c 0 * c 0 := by
        exact eq_sub_of_add_eq' hc_eq
      rw [htail]
      ring
    have hbw : ∑ i, b i * w i = -b 0 := by
      rw [Fin.sum_univ_succ]
      simp only [w, Fin.cons_zero, Fin.cons_succ]
      rw [Fin.sum_univ_succ] at hbc_eq
      have htail : ∑ i : Fin m, b i.succ * c i.succ = -(b 0 * c 0) :=
        eq_neg_of_add_eq_zero_right hbc_eq
      rw [htail]
      ring
    have hb'0 : b' 0 = 0 := by
      dsimp [b', lam, w]
      rw [Fin.cons_zero]
      field_simp [hden]
      ring
    have hb'_sum : ∑ i, b' i * b' i = a := by
      have hexp : ∑ i, b' i * b' i =
          (∑ i, b i * b i) + 2 * lam * (∑ i, b i * w i) + lam ^ 2 * (∑ i, w i * w i) := by
        have hterm : ∀ i, b' i * b' i =
            b i * b i + 2 * lam * (b i * w i) + lam ^ 2 * (w i * w i) := by
          intro i; dsimp [b']; ring
        simp_rw [hterm, Finset.sum_add_distrib, ← Finset.mul_sum]
      rw [hexp, ha_eq, hbw, hw_sq]
      dsimp [lam]
      field_simp [hden]
      ring
    refine ⟨fun i => b' i.succ, ?_⟩
    rw [← hb'_sum, Fin.sum_univ_succ, hb'0, zero_mul, zero_add]

private lemma mvRatFunc_to_ratFunc_embed (k : ℕ) :
    ∃ Φ : MvRatFunc (Fin (k + 1)) ℝ →+* RatFunc (MvRatFunc (Fin k) ℝ),
      ∀ (f : MvPolynomial (Fin k) ℝ),
        Φ (algebraMap (MvPolynomial (Fin (k + 1)) ℝ) (MvRatFunc (Fin (k + 1)) ℝ)
          (MvPolynomial.rename Fin.castSucc f + MvPolynomial.X (Fin.last k) ^ 2)) =
        algebraMap (Polynomial (MvRatFunc (Fin k) ℝ)) (RatFunc (MvRatFunc (Fin k) ℝ))
          (Polynomial.C (algebraMap (MvPolynomial (Fin k) ℝ) (MvRatFunc (Fin k) ℝ) f) +
            Polynomial.X ^ 2) := by
  let K := MvRatFunc (Fin k) ℝ
  let e1 : Fin (k + 1) ≃ Option (Fin k) := finSuccEquivLast
  let ePoly : MvPolynomial (Fin (k + 1)) ℝ ≃+* Polynomial (MvPolynomial (Fin k) ℝ) :=
    (MvPolynomial.renameEquiv ℝ e1).toRingEquiv.trans (MvPolynomial.optionEquivLeft ℝ (Fin k)).toRingEquiv
  let φPoly : MvPolynomial (Fin (k + 1)) ℝ →+* Polynomial K :=
    (Polynomial.mapRingHom (algebraMap (MvPolynomial (Fin k) ℝ) K)).comp ePoly.toRingHom
  have hφ_inj : Function.Injective φPoly := by
    exact (Polynomial.map_injective _ (IsFractionRing.injective (MvPolynomial (Fin k) ℝ) K)).comp
      ePoly.injective
  let ψ : MvPolynomial (Fin (k + 1)) ℝ →+* RatFunc K :=
    (algebraMap (Polynomial K) (RatFunc K)).comp φPoly
  have hψ_inj : Function.Injective ψ :=
    (IsFractionRing.injective (Polynomial K) (RatFunc K)).comp hφ_inj
  let Φ : MvRatFunc (Fin (k + 1)) ℝ →+* RatFunc K :=
    IsFractionRing.lift hψ_inj
  refine ⟨Φ, fun f => ?_⟩
  have hlift : Φ (algebraMap (MvPolynomial (Fin (k + 1)) ℝ) (MvRatFunc (Fin (k + 1)) ℝ)
      (MvPolynomial.rename Fin.castSucc f + MvPolynomial.X (Fin.last k) ^ 2)) =
      ψ (MvPolynomial.rename Fin.castSucc f + MvPolynomial.X (Fin.last k) ^ 2) :=
    IsFractionRing.lift_algebraMap hψ_inj _
  rw [hlift]
  change algebraMap (Polynomial K) (RatFunc K)
    (φPoly (MvPolynomial.rename Fin.castSucc f + MvPolynomial.X (Fin.last k) ^ 2)) = _
  congr 1
  rw [map_add, map_pow]
  have hX : φPoly (MvPolynomial.X (Fin.last k)) = Polynomial.X := by
    change Polynomial.map (algebraMap (MvPolynomial (Fin k) ℝ) K)
      (MvPolynomial.optionEquivLeft ℝ (Fin k)
        (MvPolynomial.rename e1 (MvPolynomial.X (Fin.last k)))) = Polynomial.X
    rw [MvPolynomial.rename_X]
    have hlast : e1 (Fin.last k) = none := finSuccEquivLast_last
    rw [hlast, MvPolynomial.optionEquivLeft_X_none, Polynomial.map_X]
  have hren : φPoly (MvPolynomial.rename Fin.castSucc f) =
      Polynomial.C (algebraMap (MvPolynomial (Fin k) ℝ) K f) := by
    change Polynomial.map (algebraMap (MvPolynomial (Fin k) ℝ) K)
      (MvPolynomial.optionEquivLeft ℝ (Fin k)
        (MvPolynomial.rename e1 (MvPolynomial.rename Fin.castSucc f))) =
      Polynomial.C (algebraMap (MvPolynomial (Fin k) ℝ) K f)
    rw [MvPolynomial.rename_rename]
    have hcomp : e1 ∘ Fin.castSucc = Option.some := by
      funext i
      exact finSuccEquivLast_castSucc i
    rw [hcomp]
    have hopt : MvPolynomial.optionEquivLeft ℝ (Fin k) (MvPolynomial.rename Option.some f) =
        Polynomial.C f := by
      clear hlift
      induction f using MvPolynomial.induction_on with
      | C r => simp
      | add p q hp hq => simp [map_add, hp, hq]
      | mul_X p i hp => simp [map_mul, hp]
    rw [hopt, Polynomial.map_C]
  rw [hX, hren]

end Cassels1964

theorem OMA.solution :
    OMA.R_PfisterPythagorasNumber_pfister_problem_variants_lower_bound_R1.H2 := by
  intro k m f hnot hsq
  obtain ⟨Φ, hΦ⟩ := mvRatFunc_to_ratFunc_embed k
  have hsq_rf : IsSumSqOfLength (m + 1)
      (algebraMap (Polynomial (MvRatFunc (Fin k) ℝ)) (RatFunc (MvRatFunc (Fin k) ℝ))
        (Polynomial.C (algebraMap (MvPolynomial (Fin k) ℝ) (MvRatFunc (Fin k) ℝ) f) +
          Polynomial.X ^ 2)) := by
    rw [← hΦ f]
    exact isSumSqOfLength_map Φ hsq
  have h2 : (2 : MvRatFunc (Fin k) ℝ) ≠ 0 := by
    intro h0
    have h0' : (2 : MvPolynomial (Fin k) ℝ) = 0 :=
      IsFractionRing.injective (MvPolynomial (Fin k) ℝ) (MvRatFunc (Fin k) ℝ)
        (by rw [map_ofNat, map_zero]; exact h0)
    have hev := congr_arg (MvPolynomial.eval (fun _ : Fin k => (0 : ℝ))) h0'
    rw [map_ofNat, map_zero] at hev
    norm_num at hev
  exact hnot (cassels_add_sq_step (mvRatFunc_sum_sq_eq_zero k) h2 m
    (algebraMap (MvPolynomial (Fin k) ℝ) (MvRatFunc (Fin k) ℝ) f) hsq_rf)
