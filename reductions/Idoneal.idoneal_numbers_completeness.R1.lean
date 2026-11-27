import FormalConjectures.Wikipedia.IdonealCompleteness

-- Reduction Idoneal.idoneal_numbers_completeness.R1 of Idoneal numbers completeness conjecture
-- Credit: @senamakel
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.
--
-- Route (no class number formula, no genus theory): n = ab + bc + ca iff n + a^2 = (a+b)(a+c),
-- so an idoneal n has -n a non-residue mod every odd prime p not dividing n with p^2 < n.
-- With x = floor(sqrt n) and psi the primitive character inducing the Kronecker character of
-- Q(sqrt(-n)), the weighted prime sum over primes p < x where psi(p) = 1 is then at most
-- 2 #P log x for a small set P, while the explicit bounds H3 and H4 (consequences of GRH,
-- H1) force it to be about x/2. These contradict for n >= 10^8. Below 10^8 the finite
-- check H2 applies.
--
-- H1: GRH for Dirichlet L-functions (the statement DirichletLNonvanishingRightOfHalf of
--     leanprover-community/riemann-hypothesis, src/Statements.lean, inlined).
-- H2: the finite check below 10^8: every n < 10^8 outside the 65 has a representation.
-- H3: under GRH, the explicit bound for the weighted prime sum of a primitive non-trivial
--     Dirichlet character of any modulus N (Bach 1997, Lemma 2.1; McGown, Trevino and
--     Trudgian 2016, Lemma 1, with the constants of the erdos-985 toolkit).
-- H4: under GRH, the principal part of the same bound (the same references).

namespace OMA.R_Idoneal_idoneal_numbers_completeness_R1

open ArithmeticFunction Finset Idoneal

/-- GRH for Dirichlet L-functions. -/
def H1 : Prop :=
  ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (s : ℂ),
    1 / 2 < s.re → (χ ≠ 1 ∨ s ≠ 1) → DirichletCharacter.LFunction χ s ≠ 0

/-- The finite check: every `0 < n < 10^8` outside Euler's 65 is `ab + bc + ca`
with `0 < a < b < c`. -/
def H2 : Prop :=
  ∀ n : ℕ, 0 < n → n < 10 ^ 8 → n ∉ Idoneal.knownIdonealNumbers →
    ∃ a b c : ℕ, 0 < a ∧ a < b ∧ b < c ∧ n = a * b + b * c + a * c

/-- Under GRH, the explicit bound for `Σ_{m<x} Λ(m) χ(m) (1 - m/x)` for a primitive
non-trivial character `χ` mod `N`. -/
def H3 : Prop :=
  (∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (s : ℂ),
      1 / 2 < s.re → (χ ≠ 1 ∨ s ≠ 1) → DirichletCharacter.LFunction χ s ≠ 0) →
    ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), χ.IsPrimitive → χ ≠ 1 →
      ∀ x : ℕ, 1 ≤ x →
        ‖∑ m ∈ Finset.range x, (ArithmeticFunction.vonMangoldt m : ℂ) * χ m * (1 - (m : ℂ) / x)‖
          ≤ (Real.sqrt x + 2 + 3 / x) * ((2 / 3) * (Real.log N + 5 / 3))
            + (Real.log x + 1) + 0.6

/-- Under GRH, `|Σ_{m<x} Λ(m) (1 - m/x) - x/2| ≤ √x/20 + 3`. -/
def H4 : Prop :=
  (∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (s : ℂ),
      1 / 2 < s.re → (χ ≠ 1 ∨ s ≠ 1) → DirichletCharacter.LFunction χ s ≠ 0) →
    ∀ x : ℕ, 1 ≤ x →
      |∑ m ∈ Finset.range x, (ArithmeticFunction.vonMangoldt m : ℝ) * (1 - (m : ℝ) / x)
          - (x : ℝ) / 2| ≤ Real.sqrt x / 20 + 3

/-! ### The elementary reduction -/

/-- A factorisation `n + a² = u · v` with `0 < a`, `2a < u`, `u² < n + a²` makes `n` non-idoneal. -/
theorem not_isIdoneal_of_witness {n a u : ℕ} (ha : 0 < a) (hau : 2 * a < u)
    (hdvd : u ∣ n + a * a) (hlt : u * u < n + a * a) : ¬ IsIdoneal n := by
  rintro ⟨-, hno⟩
  obtain ⟨v, hv⟩ := hdvd
  have huv : u < v := by
    by_contra h
    replace h := not_lt.mp h
    have : u * v ≤ u * u := Nat.mul_le_mul_left u h
    omega
  obtain ⟨b, rfl⟩ : ∃ b, u = a + b := ⟨u - a, by omega⟩
  obtain ⟨c, rfl⟩ : ∃ c, v = a + c := ⟨v - a, by omega⟩
  refine hno ⟨a, b, c, ha, by omega, by omega, ?_⟩
  have : n + a * a = a * a + (a * b + b * c + a * c) := by rw [hv]; ring
  omega

/-- For an idoneal `n` and an odd prime `p ∤ n` with `p² < n`, `−n` is not a square mod `p`. -/
theorem not_isSquare_of_isIdoneal {n p : ℕ} (hn : IsIdoneal n) (hp : p.Prime) (hp2 : p ≠ 2)
    (hpn : ¬ p ∣ n) (hpp : p * p < n) : ¬ IsSquare (-(n : ZMod p)) := by
  have := Fact.mk hp
  rintro ⟨r, hr⟩
  set a : ℕ := (r : ZMod p).valMinAbs.natAbs with ha_def
  have hsq : ((a : ℤ) : ZMod p) ^ 2 = r ^ 2 := by
    have : ((a : ℤ)) = |r.valMinAbs| := by simp [ha_def]
    rw [this]
    rcases abs_choice r.valMinAbs with h | h <;> rw [h] <;> simp [ZMod.coe_valMinAbs]
  have hale : 2 * a ≤ p := by
    have := ZMod.natAbs_valMinAbs_le r
    omega
  have hodd : p % 2 = 1 := Nat.odd_iff.mp (hp.odd_of_ne_two hp2)
  have hdvd : p ∣ n + a * a := by
    rw [← ZMod.natCast_eq_zero_iff]
    push_cast
    have h1 : ((a : ℤ) : ZMod p) = (a : ZMod p) := by simp
    rw [h1] at hsq
    rw [show (a : ZMod p) * a = (a : ZMod p) ^ 2 by ring, hsq, sq, ← hr]
    ring
  have ha0 : 0 < a := by
    rcases Nat.eq_zero_or_pos a with h | h
    · exfalso
      rw [h] at hdvd
      simp at hdvd
      exact hpn hdvd
    · exact h
  exact not_isIdoneal_of_witness ha0 (by omega) hdvd (by nlinarith) hn

/-! ### The Kronecker character of `ℚ(√−n)` as a Dirichlet character mod `4n` -/

lemma odd_of_coprime_four_mul (n : ℕ) {b : ℕ} (h : Nat.Coprime b (4 * n)) : Odd b := by
  rw [Nat.odd_iff]
  by_contra h2
  have : 2 ∣ Nat.gcd b (4 * n) := Nat.dvd_gcd (by omega) (Dvd.intro (2 * n) (by ring))
  rw [h] at this
  omega

lemma gcd_neg_eq_one_of_coprime (n : ℕ) {b : ℕ} (h : Nat.Coprime b (4 * n)) :
    (-(n : ℤ)).gcd b = 1 := by
  rw [Int.neg_gcd, Int.gcd_natCast_natCast]
  exact (Nat.Coprime.coprime_dvd_right (Dvd.intro_left 4 rfl) h).symm

lemma jacobi_isUnit (n : ℕ) (u : (ZMod (4 * n))ˣ) :
    IsUnit (jacobiSym (-(n : ℤ)) (u : ZMod (4 * n)).val) :=
  Int.isUnit_iff.mpr (jacobiSym.eq_one_or_neg_one
    (gcd_neg_eq_one_of_coprime n (ZMod.val_coe_unit_coprime u)))

/-- `u ↦ J(−n | u)` is a homomorphism on units mod `4n`. -/
lemma exists_jacobiHom (n : ℕ) [NeZero n] :
    ∃ f : (ZMod (4 * n))ˣ →* ℤˣ, ∀ u, (f u : ℤ) = jacobiSym (-(n : ℤ)) (u : ZMod (4 * n)).val := by
  refine ⟨{ toFun := fun u => (jacobi_isUnit n u).unit, map_one' := ?_, map_mul' := ?_ }, ?_⟩
  · ext
    have h1 : (1 : ZMod (4 * n)).val = 1 := ZMod.val_one'' (by have := NeZero.ne n; omega)
    simp [h1, jacobiSym.one_right]
  · intro u v
    ext
    simp only [IsUnit.unit_spec, Units.val_mul]
    have hu := ZMod.val_coe_unit_coprime u
    have hv := ZMod.val_coe_unit_coprime v
    have hou := odd_of_coprime_four_mul n hu
    have hov := odd_of_coprime_four_mul n hv
    rw [ZMod.val_mul]
    have hmod := jacobiSym.mod_right (-(n : ℤ)) (hou.mul hov)
    rw [show (-(n : ℤ)).natAbs = n by simp] at hmod
    rw [← hmod, jacobiSym.mul_right' _ hou.pos.ne' hov.pos.ne']
  · intro u
    rfl

/-- The Dirichlet character `χ_{−4n}` mod `4n`: at an odd prime `p ∤ n` it is `(−n / p)`. -/
lemma exists_kroneckerChar (n : ℕ) [NeZero n] :
    ∃ χ : DirichletCharacter ℂ (4 * n), ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → ¬ p ∣ n →
      χ p = (legendreSym p (-(n : ℤ)) : ℂ) := by
  obtain ⟨f, hf⟩ := exists_jacobiHom n
  refine ⟨MulChar.ofUnitHom ((Units.map (Int.castRingHom ℂ).toMonoidHom).comp f), ?_⟩
  intro p _ hp2 hpn
  have hp : p.Prime := Fact.out
  have hcop : Nat.Coprime p (4 * n) := by
    refine Nat.Coprime.mul_right ?_ ((Nat.Prime.coprime_iff_not_dvd hp).2 hpn)
    rw [show (4 : ℕ) = 2 ^ 2 by norm_num]
    exact Nat.Coprime.pow_right _ ((Nat.coprime_primes hp Nat.prime_two).2 hp2)
  set u := ZMod.unitOfCoprime p hcop
  have hu : (u : ZMod (4 * n)) = (p : ZMod (4 * n)) := rfl
  rw [← hu, MulChar.ofUnitHom_coe]
  simp only [MonoidHom.coe_comp, Function.comp_apply, Units.coe_map]
  have hfu := hf u
  simp only [MonoidHom.coe_coe, RingHom.toMonoidHom_eq_coe]
  rw [show ((Int.castRingHom ℂ) (f u : ℤ)) = ((f u : ℤ) : ℂ) from rfl, hfu, hu,
    ZMod.val_natCast, jacobiSym.legendreSym.to_jacobiSym]
  have hodd : Odd p := hp.odd_of_ne_two hp2
  have hmod := jacobiSym.mod_right (-(n : ℤ)) hodd
  rw [show (-(n : ℤ)).natAbs = n by simp] at hmod
  rw [← hmod]

/-! ### The prime-sum upper bound -/

/-- The powers of a prime `p` below `x` carry total von Mangoldt weight at most `log x`. -/
theorem sum_vonMangoldt_dvd_le {p : ℕ} (hp : p.Prime) {x : ℕ} (hx : 1 ≤ x) :
    ∑ m ∈ range x, (if p ∣ m then (Λ m : ℝ) else 0) ≤ Real.log x := by
  set K := Nat.log p x
  rw [← Finset.sum_filter]
  have hsub : ((range x).filter (fun m => p ∣ m)).filter (fun m => (Λ m : ℝ) ≠ 0)
      ⊆ (p ^ K).divisors := by
    intro m hm
    simp only [mem_filter, mem_range] at hm
    obtain ⟨⟨hmx, hpm⟩, hΛ⟩ := hm
    have hpp : IsPrimePow m := by
      by_contra h
      exact hΛ (by simp [vonMangoldt_apply, h])
    obtain ⟨q, k, hq, hk, rfl⟩ := hpp
    have hq' := hq.nat_prime
    have hpq : p = q := (Nat.prime_dvd_prime_iff_eq hp hq').1 (hp.dvd_of_dvd_pow hpm)
    subst hpq
    rw [Nat.mem_divisors]
    refine ⟨pow_dvd_pow p (Nat.le_log_of_pow_le hp.one_lt hmx.le), pow_ne_zero _ hp.ne_zero⟩
  calc ∑ m ∈ (range x).filter (fun m => p ∣ m), (Λ m : ℝ)
      = ∑ m ∈ ((range x).filter (fun m => p ∣ m)).filter (fun m => (Λ m : ℝ) ≠ 0), (Λ m : ℝ) :=
        (Finset.sum_filter_ne_zero _).symm
    _ ≤ ∑ m ∈ (p ^ K).divisors, (Λ m : ℝ) :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => vonMangoldt_nonneg)
    _ = Real.log (p ^ K : ℕ) := by
        rw [vonMangoldt_sum]
    _ ≤ Real.log x := by
        apply Real.log_le_log (by exact_mod_cast pow_pos hp.pos K)
        exact_mod_cast Nat.pow_log_le_self p (by omega)

/-- The sieve bound for `Σ_{m<x} Λ(m)(1 − m/x)(1 + Re ψ(m))`. `P` must contain every prime
`p < x` with `p * p < x`, and `ψ` must be `−1` at every prime `p < x` not in `P`. -/
theorem splitSum_le {N : ℕ} (ψ : DirichletCharacter ℂ N) {x : ℕ} (hx : 1 ≤ x) (P : Finset ℕ)
    (hPp : ∀ p ∈ P, p.Prime)
    (hsq : ∀ p, p.Prime → p < x → p * p < x → p ∈ P)
    (hval : ∀ p, p.Prime → p < x → p ∉ P → ψ p = -1) :
    ∑ m ∈ range x, (Λ m : ℝ) * (1 - (m : ℝ) / x) * (1 + (ψ m).re)
      ≤ 2 * P.card * Real.log x := by
  have hpt : ∀ m ∈ range x, (Λ m : ℝ) * (1 - (m : ℝ) / x) * (1 + (ψ m).re)
      ≤ 2 * ∑ p ∈ P, (if p ∣ m then (Λ m : ℝ) else 0) := by
    intro m hm
    rw [mem_range] at hm
    have hxR : (0 : ℝ) < x := by exact_mod_cast hx
    have hw0 : 0 ≤ 1 - (m : ℝ) / x := by
      rw [sub_nonneg, div_le_one hxR]; exact_mod_cast hm.le
    have hw1 : 1 - (m : ℝ) / x ≤ 1 := by
      have : 0 ≤ (m : ℝ) / x := by positivity
      linarith
    have hre : (ψ m).re ≤ 1 := by
      have h1 := Complex.re_le_norm (ψ m)
      have h2 : ‖ψ m‖ ≤ 1 := DirichletCharacter.norm_le_one ψ m
      linarith
    have hre' : -1 ≤ (ψ m).re := by
      have h1 := Complex.abs_re_le_norm (ψ m)
      have h2 : ‖ψ m‖ ≤ 1 := DirichletCharacter.norm_le_one ψ m
      have := neg_abs_le (ψ m).re
      linarith
    have hΛ0 : (0 : ℝ) ≤ Λ m := vonMangoldt_nonneg
    have hRHS0 : 0 ≤ ∑ p ∈ P, (if p ∣ m then (Λ m : ℝ) else 0) :=
      Finset.sum_nonneg fun p _ => by split_ifs <;> simp [hΛ0]
    by_cases hpp : IsPrimePow m
    · set p := m.minFac
      have hm1 : m ≠ 1 := hpp.ne_one
      have hpr : p.Prime := Nat.minFac_prime hm1
      have hpm : p ∣ m := Nat.minFac_dvd m
      by_cases hP : p ∈ P
      · have : (Λ m : ℝ) ≤ ∑ p ∈ P, (if p ∣ m then (Λ m : ℝ) else 0) := by
          have := Finset.single_le_sum (f := fun q => if q ∣ m then (Λ m : ℝ) else 0)
            (fun q _ => by split_ifs <;> simp [hΛ0]) hP
          simpa [hpm] using this
        have h2 : (Λ m : ℝ) * (1 - (m : ℝ) / x) * (1 + (ψ m).re) ≤ (Λ m : ℝ) * 1 * 2 := by
          apply mul_le_mul (mul_le_mul_of_nonneg_left hw1 hΛ0) (by linarith) (by linarith)
          positivity
        linarith
      · have hmpos : 0 < m := hpp.pos
        have hpx : p < x := lt_of_le_of_lt (Nat.minFac_le hmpos) hm
        have hmp : m = p := by
          have he := hpp.minFac_pow_factorization_eq
          set e := m.factorization p
          have he0 : e ≠ 0 := by
            intro h0; rw [h0, pow_zero] at he; exact hm1 he.symm
          by_contra hne
          have he2 : 2 ≤ e := by
            rcases Nat.lt_or_ge e 2 with h | h
            · exfalso; have : e = 1 := by omega
              rw [this, pow_one] at he; exact hne he.symm
            · exact h
          have : p * p ∣ m := by
            rw [← he, ← pow_two]; exact pow_dvd_pow p he2
          have hle := Nat.le_of_dvd hmpos this
          exact hP (hsq p hpr hpx (by omega))
        have hψ := hval p hpr hpx hP
        have h0 : (Λ m : ℝ) * (1 - (m : ℝ) / x) * (1 + (ψ m).re) = 0 := by
          rw [hmp, hψ]
          simp only [Complex.neg_re, Complex.one_re, add_neg_cancel, mul_zero]
        rw [h0]; linarith
    · have : (Λ m : ℝ) = 0 := by simp [vonMangoldt_apply, hpp]
      have h0 : (Λ m : ℝ) * (1 - (m : ℝ) / x) * (1 + (ψ m).re) = 0 := by
        rw [this]; simp only [zero_mul]
      rw [h0]; linarith
  calc ∑ m ∈ range x, (Λ m : ℝ) * (1 - (m : ℝ) / x) * (1 + (ψ m).re)
        ≤ ∑ m ∈ range x, 2 * ∑ p ∈ P, (if p ∣ m then (Λ m : ℝ) else 0) :=
        Finset.sum_le_sum hpt
    _ = 2 * ∑ p ∈ P, ∑ m ∈ range x, (if p ∣ m then (Λ m : ℝ) else 0) := by
        rw [← Finset.mul_sum, Finset.sum_comm]
    _ ≤ 2 * ∑ p ∈ P, Real.log x := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        exact Finset.sum_le_sum fun p hp => sum_vonMangoldt_dvd_le (hPp p hp) hx
    _ = 2 * P.card * Real.log x := by
        rw [Finset.sum_const, nsmul_eq_mul]; ring

/-- `2 ^ ω(m) ≤ m`. -/
theorem two_pow_card_primeFactors_le {m : ℕ} (hm : m ≠ 0) : 2 ^ m.primeFactors.card ≤ m := by
  calc 2 ^ m.primeFactors.card ≤ ∏ p ∈ m.primeFactors, p :=
        Finset.pow_card_le_prod _ _ _ fun p hp => (Nat.prime_of_mem_primeFactors hp).two_le
    _ ≤ m := Nat.le_of_dvd (Nat.pos_of_ne_zero hm) (Nat.prod_primeFactors_dvd m)

/-! ### The numerical contradiction for `n ≥ 10^8` -/

/-- `log s ≤ s/100 + 3.8521` for `s > 0`. -/
lemma log_le_linear {s : ℝ} (hs : 0 < s) : Real.log s ≤ s / 100 + 3.8521 := by
  have h1 : Real.log (s / 100) ≤ s / 100 - 1 := Real.log_le_sub_one_of_pos (by positivity)
  rw [Real.log_div hs.ne' (by norm_num)] at h1
  have h2 : Real.log 100 < 4.8521 := by
    have : Real.log 100 < Real.log 128 := Real.log_lt_log (by norm_num) (by norm_num)
    have h7 : Real.log 128 = 7 * Real.log 2 := by
      rw [show (128 : ℝ) = 2 ^ 7 by norm_num, Real.log_pow]; norm_num
    have := Real.log_two_lt_d9
    linarith
  linarith

theorem numerics {x N n ω : ℝ} (hx : 10 ^ 4 ≤ x) (hN1 : 1 ≤ N) (hN : N ≤ 4 * n)
    (hn : n < (x + 1) ^ 2) (hn0 : 0 < n) (hω0 : 0 ≤ ω) (hω : ω * Real.log 2 ≤ Real.log (2 * n)) :
    2 * (Real.sqrt x + 1 + ω) * Real.log x
      < x / 2 - Real.sqrt x / 20 - 3
        - ((Real.sqrt x + 2 + 3 / x) * ((2 / 3) * (Real.log N + 5 / 3))
          + (Real.log x + 1) + 0.6) := by
  set s := Real.sqrt x with hs_def
  have hx0 : 0 < x := by linarith
  have hs100 : 100 ≤ s := by
    rw [hs_def, show (100 : ℝ) = Real.sqrt (10 ^ 4) by
      rw [show (10 : ℝ) ^ 4 = 100 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt hx
  have hxs : x = s ^ 2 := (Real.sq_sqrt hx0.le).symm
  set L := Real.log s with hL_def
  have hlogx : Real.log x = 2 * L := by
    rw [hxs, Real.log_pow]; push_cast; ring
  have hL0 : 0 ≤ L := Real.log_nonneg (by linarith)
  have hLle : L ≤ s / 100 + 3.8521 := log_le_linear (by linarith)
  have hl2a := Real.log_two_gt_d9
  have hl2b := Real.log_two_lt_d9
  have hNx : N ≤ 5 * s ^ 4 := by
    have : 4 * (x + 1) ^ 2 ≤ 5 * x ^ 2 := by nlinarith
    rw [hxs] at this; nlinarith
  have hlogN : Real.log N ≤ 2.0795 + 4 * L := by
    have h1 : Real.log N ≤ Real.log (5 * s ^ 4) := Real.log_le_log (by linarith) hNx
    rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow] at h1
    have h5 : Real.log 5 < Real.log 8 := Real.log_lt_log (by norm_num) (by norm_num)
    have h8 : Real.log 8 = 3 * Real.log 2 := by
      rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]; norm_num
    push_cast at h1
    linarith
  have hlog2n : Real.log (2 * n) ≤ 1.3863 + 4 * L := by
    have h2n : 2 * n ≤ 3 * s ^ 4 := by
      have : 2 * (x + 1) ^ 2 ≤ 3 * x ^ 2 := by nlinarith
      rw [hxs] at this hn; nlinarith
    have h1 : Real.log (2 * n) ≤ Real.log (3 * s ^ 4) := Real.log_le_log (by linarith) h2n
    rw [Real.log_mul (x := 3) (by norm_num) (by positivity), Real.log_pow] at h1
    have h3 : Real.log 3 < Real.log 4 := Real.log_lt_log (by norm_num) (by norm_num)
    have h4 : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
    push_cast at h1
    linarith
  have hωL : ω * L * 0.6931 ≤ (1.3863 + 4 * L) * L := by
    have : ω * 0.6931 ≤ 1.3863 + 4 * L := by nlinarith
    nlinarith
  have h3x : 3 / x ≤ 0.0003 := by
    rw [div_le_iff₀ hx0]; nlinarith
  rw [hlogx]
  have hA : (s + 2 + 3 / x) * ((2 / 3) * (Real.log N + 5 / 3))
      ≤ (s + 2.0003) * ((2 / 3) * (2.0795 + 4 * L + 5 / 3)) := by
    have hlN0 : 0 ≤ Real.log N := Real.log_nonneg hN1
    apply mul_le_mul (by linarith) (by linarith) (by positivity) (by linarith)
  have hxs' : x / 2 = s ^ 2 / 2 := by rw [hxs]
  rw [hxs']
  have key : 0.6931 * (2 * (s + 1 + ω) * (2 * L)) + 0.6931 * ((s + 2.0003) * ((2 / 3) * (2.0795 + 4 * L + 5 / 3))
      + (2 * L + 1) + 0.6 + s / 20 + 3) < 0.6931 * (s ^ 2 / 2) := by
    have e1 : 0.6931 * (2 * (s + 1 + ω) * (2 * L)) = 4 * 0.6931 * (s + 1) * L + 4 * (ω * L * 0.6931) := by ring
    rw [e1]
    have hsL : s * L ≤ s * (s / 100 + 3.8521) := mul_le_mul_of_nonneg_left hLle (by linarith)
    have hLL : L * L ≤ (s / 100 + 3.8521) * (s / 100 + 3.8521) := mul_self_le_mul_self hL0 hLle
    nlinarith
  nlinarith

/-! ### Under GRH, no `n ≥ 10^8` is idoneal -/

/-- The split-prime sum is the principal sum plus the real part of the character sum. -/
theorem splitSum_eq {N : ℕ} (ψ : DirichletCharacter ℂ N) (x : ℕ) :
    ∑ m ∈ range x, (Λ m : ℝ) * (1 - (m : ℝ) / x) * (1 + (ψ m).re)
      = ∑ m ∈ range x, (Λ m : ℝ) * (1 - (m : ℝ) / x)
        + (∑ m ∈ range x, (Λ m : ℂ) * ψ m * (1 - (m : ℂ) / x)).re := by
  rw [Complex.re_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun m _ => ?_
  have : (Λ m : ℂ) * ψ m * (1 - (m : ℂ) / x) = (((Λ m : ℝ) * (1 - (m : ℝ) / x) : ℝ) : ℂ) * ψ m := by
    push_cast; ring
  rw [this, Complex.re_ofReal_mul]
  ring

theorem splitSum_one (x : ℕ) :
    ∑ m ∈ range x, (Λ m : ℝ) * (1 - (m : ℝ) / x) * (1 + ((1 : DirichletCharacter ℂ 1) m).re)
      = 2 * ∑ m ∈ range x, (Λ m : ℝ) * (1 - (m : ℝ) / x) := by
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  have : (1 : DirichletCharacter ℂ 1) m = 1 := MulChar.one_apply (isUnit_of_subsingleton _)
  rw [this]; simp only [Complex.one_re]; ring

/-- Given H1, H3, H4: every `n ≥ 10^8` has an odd prime `p ∤ n` with `p² < n` at which `−n`
is a square mod `p` (a prime that splits in `ℚ(√−n)`). -/
theorem exists_split_prime (h1 : H1) (h3 : H3) (h4 : H4) {n : ℕ} (hn : 10 ^ 8 ≤ n) :
    ∃ p, p.Prime ∧ p ≠ 2 ∧ ¬ p ∣ n ∧ p * p < n ∧ IsSquare (-(n : ZMod p)) := by
  by_contra hcon
  have hns : ∀ p, p.Prime → p ≠ 2 → ¬ p ∣ n → p * p < n → ¬ IsSquare (-(n : ZMod p)) :=
    fun p hp hp2 hpn hpp hsq => hcon ⟨p, hp, hp2, hpn, hpp, hsq⟩
  have hn0 : 0 < n := by omega
  haveI : NeZero n := ⟨by omega⟩
  set x := Nat.sqrt n with hx_def
  have hxx : x * x ≤ n := Nat.sqrt_le n
  have hnx : n < (x + 1) * (x + 1) := Nat.lt_succ_sqrt n
  have hx4 : 10 ^ 4 ≤ x := Nat.le_sqrt.2 (by norm_num; omega)
  have hx1 : 1 ≤ x := by omega
  obtain ⟨χ, hχ⟩ := exists_kroneckerChar n
  set ψ := χ.primitiveCharacter
  haveI : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  set P : Finset ℕ := (range x).filter (fun p => p.Prime ∧ (p * p < x ∨ p ∣ 2 * n)) with hP_def
  have hPp : ∀ p ∈ P, p.Prime := fun p hp => (mem_filter.1 hp).2.1
  have hsq : ∀ p, p.Prime → p < x → p * p < x → p ∈ P := fun p hp hpx hpp =>
    mem_filter.2 ⟨mem_range.2 hpx, hp, Or.inl hpp⟩
  have hgood : ∀ p, p.Prime → p < x → p ∉ P → χ p = -1 ∧ ψ p = -1 := by
    intro p hp hpx hpP
    have hn2 : ¬ p ∣ 2 * n := fun h => hpP (mem_filter.2 ⟨mem_range.2 hpx, hp, Or.inr h⟩)
    have hp2 : p ≠ 2 := by rintro rfl; exact hn2 (dvd_mul_right 2 n)
    have hpn : ¬ p ∣ n := fun h => hn2 (Dvd.dvd.mul_left h 2)
    have hpp : p * p < n := lt_of_lt_of_le (Nat.mul_self_lt_mul_self hpx) hxx
    haveI := Fact.mk hp
    have hns := hns p hp hp2 hpn hpp
    have hleg : legendreSym p (-(n : ℤ)) = -1 := by
      rw [legendreSym.eq_neg_one_iff]; push_cast; exact hns
    have hχp : χ p = -1 := by
      rw [hχ p hp2 hpn, hleg]; simp
    have hcop : Nat.Coprime p (4 * n) := by
      refine Nat.Coprime.mul_right ?_ ((Nat.Prime.coprime_iff_not_dvd hp).2 hpn)
      rw [show (4 : ℕ) = 2 ^ 2 by norm_num]
      exact Nat.Coprime.pow_right _ ((Nat.coprime_primes hp Nat.prime_two).2 hp2)
    have hψp : ψ p = χ p := by
      have := DirichletCharacter.primitiveCharacter_apply_of_isCoprime χ (a := (p : ℤ))
        (by exact_mod_cast Nat.isCoprime_iff_coprime.2 hcop)
      simpa using this
    exact ⟨hχp, hψp.trans hχp⟩
  set ω := (2 * n).primeFactors.card
  have hPcard : (P.card : ℝ) ≤ Real.sqrt (x : ℝ) + 1 + ω := by
    have hsub : P ⊆ range (Nat.sqrt x + 1) ∪ (2 * n).primeFactors := by
      intro p hp
      obtain ⟨-, hpr, h⟩ := mem_filter.1 hp
      rcases h with h | h
      · exact mem_union_left _ (mem_range.2 (Nat.lt_succ_of_le (Nat.le_sqrt.2 h.le)))
      · exact mem_union_right _ (Nat.mem_primeFactors.2 ⟨hpr, h, by omega⟩)
    have h1 := (card_le_card hsub).trans (card_union_le _ _)
    rw [card_range] at h1
    have h2 : (P.card : ℝ) ≤ (Nat.sqrt x : ℝ) + 1 + ω := by exact_mod_cast h1
    have h3 := Real.nat_sqrt_le_real_sqrt (a := x)
    linarith
  have hω : (ω : ℝ) * Real.log 2 ≤ Real.log (2 * n) := by
    have h := two_pow_card_primeFactors_le (m := 2 * n) (by omega)
    have : Real.log ((2 : ℝ) ^ ω) ≤ Real.log (2 * n) :=
      Real.log_le_log (by positivity) (by exact_mod_cast h)
    rwa [Real.log_pow] at this
  have hxR : (10 : ℝ) ^ 4 ≤ x := by exact_mod_cast hx4
  have hnR : (n : ℝ) < ((x : ℝ) + 1) ^ 2 := by
    have : (n : ℝ) < ((x + 1) * (x + 1) : ℕ) := by exact_mod_cast hnx
    push_cast at this; nlinarith
  have hlogx : 0 ≤ Real.log x := Real.log_nonneg (by exact_mod_cast hx1)
  have hprin := h4 h1 x hx1
  set S₀ := ∑ m ∈ range x, (Λ m : ℝ) * (1 - (m : ℝ) / x)
  have hS₀ : (x : ℝ) / 2 - Real.sqrt (x : ℝ) / 20 - 3 ≤ S₀ := by
    have := (abs_le.mp hprin).1; linarith
  have hN1 : (1 : ℝ) ≤ χ.conductor := by
    have := Nat.pos_of_ne_zero χ.conductor_ne_zero; exact_mod_cast this
  have hN : (χ.conductor : ℝ) ≤ 4 * n := by
    have := Nat.le_of_dvd (by omega) χ.conductor_dvd_level; exact_mod_cast this
  have hnum := numerics hxR hN1 hN hnR (by exact_mod_cast hn0) (by positivity) hω
  by_cases hex : ∃ p, p.Prime ∧ p < x ∧ p ∉ P
  · obtain ⟨p, hp, hpx, hpP⟩ := hex
    have hψ1 : ψ ≠ 1 := by
      intro h1
      have hval := (hgood p hp hpx hpP).2
      have hunit : IsUnit (p : ZMod χ.conductor) := by
        rw [ZMod.isUnit_iff_coprime]
        have hpn : ¬ p ∣ 2 * n := fun h => hpP (mem_filter.2 ⟨mem_range.2 hpx, hp, Or.inr h⟩)
        refine Nat.Coprime.coprime_dvd_right χ.conductor_dvd_level ?_
        have hp2 : p ≠ 2 := by rintro rfl; exact hpn (dvd_mul_right 2 n)
        have hpn' : ¬ p ∣ n := fun h => hpn (Dvd.dvd.mul_left h 2)
        refine Nat.Coprime.mul_right ?_ ((Nat.Prime.coprime_iff_not_dvd hp).2 hpn')
        rw [show (4 : ℕ) = 2 ^ 2 by norm_num]
        exact Nat.Coprime.pow_right _ ((Nat.coprime_primes hp Nat.prime_two).2 hp2)
      rw [h1, MulChar.one_apply hunit] at hval
      norm_num at hval
    have hbach := h3 h1 χ.conductor ψ (χ.primitiveCharacter_isPrimitive) hψ1 x hx1
    have hsplit := splitSum_le ψ hx1 P hPp hsq (fun p hp hpx hpP => (hgood p hp hpx hpP).2)
    rw [splitSum_eq] at hsplit
    set B := ∑ m ∈ range x, (Λ m : ℂ) * ψ m * (1 - (m : ℂ) / x)
    have hre : -‖B‖ ≤ B.re := by
      have := Complex.abs_re_le_norm B
      have := neg_abs_le B.re
      linarith
    have : 2 * (P.card : ℝ) * Real.log x ≤ 2 * (Real.sqrt (x : ℝ) + 1 + ω) * Real.log x := by
      have := mul_le_mul_of_nonneg_right hPcard hlogx; nlinarith
    linarith
  · push_neg at hex
    have hsplit := splitSum_le (1 : DirichletCharacter ℂ 1) hx1 P hPp hsq
      (fun p hp hpx hpP => absurd (hex p hp hpx) hpP)
    rw [splitSum_one] at hsplit
    have : 2 * (P.card : ℝ) * Real.log x ≤ 2 * (Real.sqrt (x : ℝ) + 1 + ω) * Real.log x := by
      have := mul_le_mul_of_nonneg_right hPcard hlogx; nlinarith
    have hsx : 0 ≤ Real.sqrt (x : ℝ) := Real.sqrt_nonneg _
    have hω0 : (0 : ℝ) ≤ ω := by positivity
    have hB0 : 0 ≤ (Real.sqrt (x : ℝ) + 2 + 3 / x) * ((2 / 3) * (Real.log χ.conductor + 5 / 3))
        + (Real.log x + 1) + 0.6 := by
      have : 0 ≤ Real.log χ.conductor := Real.log_nonneg hN1
      positivity
    nlinarith

theorem main : H1 → H2 → H3 → H4 → type_of% @Idoneal.idoneal_numbers_completeness := by
  intro h1 h2 h3 h4 n hn
  by_cases hlt : n < 10 ^ 8
  · by_contra hk
    exact hn.2 (h2 n hn.1 hlt hk)
  · obtain ⟨p, hp, hp2, hpn, hpp, hsq⟩ := exists_split_prime h1 h3 h4 (not_lt.mp hlt)
    exact absurd hsq (not_isSquare_of_isIdoneal hn hp hp2 hpn hpp)

end OMA.R_Idoneal_idoneal_numbers_completeness_R1
