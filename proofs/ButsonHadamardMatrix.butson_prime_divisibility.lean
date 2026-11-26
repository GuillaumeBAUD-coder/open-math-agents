import FormalConjectures.Wikipedia.ButsonHadamardMatrix

/-!
# Proof of Butson's prime divisibility theorem

For a prime `p` and `n ≥ 2`, any Butson-type Hadamard matrix `H(p, n)` has two distinct
orthogonal rows whose entrywise products with conjugates are `p`-th roots of unity summing to `0`.
Grouping by powers of a primitive `p`-th root of unity gives a rational polynomial of degree at
most `p - 1` divisible by the `p`-th cyclotomic polynomial `∑_{r < p} X^r`, forcing all
multiplicities to be equal and hence `p ∣ n`.
-/

-- Problem: Butson's prime divisibility theorem
-- Upstream: formal-conjectures FormalConjectures/Wikipedia/ButsonHadamardMatrix.lean:104 (declaration ButsonHadamardMatrix.butson_prime_divisibility)
-- Credit: @TheWaler (the owner of the agent is credited as the solver)

open scoped Polynomial

theorem OMA.solution : type_of% @ButsonHadamardMatrix.butson_prime_divisibility := by
  intro p n hp hn hex
  rcases hex with ⟨M, _, hpow, horth⟩
  have hr01 : (⟨0, by omega⟩ : Fin n) ≠ ⟨1, by omega⟩ := by simp
  have hsum_zero : ∑ j : Fin n, M ⟨0, by omega⟩ j * star (M ⟨1, by omega⟩ j) = 0 := by
    have h01 := congr_fun (congr_fun horth ⟨0, by omega⟩) ⟨1, by omega⟩
    simpa [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply, hr01] using h01
  set a : Fin n → ℂ := fun j => M ⟨0, by omega⟩ j * star (M ⟨1, by omega⟩ j)
  have ha_pow : ∀ j : Fin n, a j ^ p = 1 := by
    intro j
    change (M ⟨0, by omega⟩ j * star (M ⟨1, by omega⟩ j)) ^ p = 1
    rw [mul_pow, ← star_pow, hpow ⟨0, by omega⟩ j, hpow ⟨1, by omega⟩ j, star_one, one_mul]
  set ζ : ℂ := Complex.exp (2 * Real.pi * Complex.I / p)
  have hζ : IsPrimitiveRoot ζ p := Complex.isPrimitiveRoot_exp p hp.ne_zero
  have : NeZero p := ⟨hp.ne_zero⟩
  have hex_exp : ∀ j : Fin n, ∃ r < p, ζ ^ r = a j :=
    fun j => hζ.eq_pow_of_pow_eq_one (ha_pow j)
  choose f hf_lt hf_eq using hex_exp
  set c : ℕ → ℕ := fun r => (Finset.univ.filter (fun j : Fin n => f j = r)).card
  have hcard_sum : ∑ r ∈ Finset.range p, c r = n := by
    have h := Finset.sum_card_fiberwise_eq_card_filter (s := (Finset.univ : Finset (Fin n)))
      (t := Finset.range p) (g := f)
    have hfilter : (Finset.univ.filter (fun j : Fin n => f j ∈ Finset.range p)) = Finset.univ := by
      ext j
      simp [hf_lt j]
    rw [hfilter, Finset.card_univ, Fintype.card_fin] at h
    exact h
  have hζ_sum : ∑ r ∈ Finset.range p, (c r : ℂ) * ζ ^ r = 0 := by
    have hmaps : ∀ j ∈ (Finset.univ : Finset (Fin n)), f j ∈ Finset.range p :=
      fun j _ => Finset.mem_range.mpr (hf_lt j)
    have hfib := Finset.sum_fiberwise_of_maps_to (s := (Finset.univ : Finset (Fin n)))
      (t := Finset.range p) (g := f) (f := a) hmaps
    rw [hsum_zero] at hfib
    rw [← hfib]
    refine Finset.sum_congr rfl ?_
    intro r _
    have hterm : ∑ j ∈ Finset.univ.filter (fun j : Fin n => f j = r), a j =
        ∑ _j ∈ Finset.univ.filter (fun j : Fin n => f j = r), ζ ^ r := by
      refine Finset.sum_congr rfl ?_
      intro j hj
      rw [← hf_eq j, (Finset.mem_filter.mp hj).2]
    rw [hterm, Finset.sum_const, nsmul_eq_mul]
  set P : ℚ[X] := ∑ r ∈ Finset.range p, Polynomial.C (c r : ℚ) * Polynomial.X ^ r
  have hP_eval : Polynomial.aeval ζ P = 0 := by
    simp only [P, map_sum, map_mul, map_pow, Polynomial.aeval_X, map_natCast]
    exact hζ_sum
  have : Fact p.Prime := ⟨hp⟩
  have hcycl_eq : Polynomial.cyclotomic p ℚ = ∑ i ∈ Finset.range p, Polynomial.X ^ i :=
    Polynomial.cyclotomic_prime ℚ p
  have hcycl_eval : Polynomial.aeval ζ (Polynomial.cyclotomic p ℚ) = 0 := by
    rw [hcycl_eq, map_sum]
    simp only [map_pow, Polynomial.aeval_X]
    have hmul := geom_sum_mul ζ p
    rw [hζ.pow_eq_one, sub_self] at hmul
    have hne : ζ - 1 ≠ 0 := sub_ne_zero.mpr (hζ.ne_one hp.one_lt)
    exact (mul_eq_zero.mp hmul).resolve_right hne
  have hmin : minpoly ℚ ζ = Polynomial.cyclotomic p ℚ :=
    (minpoly.eq_of_irreducible_of_monic (Polynomial.cyclotomic.irreducible_rat hp.pos)
      hcycl_eval (Polynomial.cyclotomic.monic p ℚ)).symm
  have hdvd : Polynomial.cyclotomic p ℚ ∣ P := by
    rw [← hmin]
    exact minpoly.dvd ℚ ζ hP_eval
  rcases hdvd with ⟨Q, hPQ⟩
  have hP_coeff : ∀ k : ℕ, P.coeff k = if k < p then (c k : ℚ) else 0 := by
    intro k
    simp only [P, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
      mul_ite, mul_one, mul_zero]
    by_cases hk : k < p
    · rw [if_pos hk, Finset.sum_eq_single k]
      · simp
      · intro r _ hr
        simp [Ne.symm hr]
      · intro hnot
        exact absurd (Finset.mem_range.mpr hk) hnot
    · rw [if_neg hk]
      refine Finset.sum_eq_zero ?_
      intro r hr
      have hrlt : r < p := Finset.mem_range.mp hr
      have hkr : k ≠ r := by omega
      simp [hkr]
  have hP_deg : P.natDegree ≤ p - 1 := by
    rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
    intro k hk
    rw [hP_coeff k, if_neg]
    have hp1 : 1 ≤ p := hp.one_lt.le
    omega
  have hQ_deg : Q.natDegree = 0 := by
    by_cases hQ : Q = 0
    · simp [hQ]
    · have hmul := Polynomial.natDegree_mul (Polynomial.cyclotomic_ne_zero p ℚ) hQ
      rw [← hPQ, Polynomial.natDegree_cyclotomic, Nat.totient_prime hp] at hmul
      omega
  have hQ_eq : Q = Polynomial.C (Q.coeff 0) := Polynomial.eq_C_of_natDegree_eq_zero hQ_deg
  have hcoeff_eq : ∀ r < p, (c r : ℚ) = Q.coeff 0 := by
    intro r hr
    have h1 : P.coeff r = (c r : ℚ) := by rw [hP_coeff r, if_pos hr]
    have h2 : P.coeff r = Q.coeff 0 := by
      rw [hPQ, hcycl_eq, hQ_eq, Polynomial.coeff_mul_C, Polynomial.finsetSum_coeff]
      simp only [Polynomial.coeff_X_pow]
      rw [Finset.sum_eq_single r]
      · simp
      · intro i _ hi
        simp [Ne.symm hi]
      · intro hnot
        exact absurd (Finset.mem_range.mpr hr) hnot
    linarith
  have hc_const : ∀ r ∈ Finset.range p, c r = c 0 := by
    intro r hr
    have hq : (c r : ℚ) = (c 0 : ℚ) := by
      rw [hcoeff_eq r (Finset.mem_range.mp hr), hcoeff_eq 0 hp.pos]
    exact Nat.cast_injective hq
  refine ⟨c 0, ?_⟩
  rw [← hcard_sum, Finset.sum_congr rfl hc_const, Finset.sum_const, Finset.card_range, smul_eq_mul]
