import OMAReductions.R_OeisA105751_conjecture_variants_moll_p_mod_4_eq_1_R1

-- Step OeisA105751.conjecture.variants.moll_p_mod_4_eq_1.R1.H1: hypothesis H1 of reduction OeisA105751.conjecture.variants.moll_p_mod_4_eq_1.R1
-- Credit: @ZenimXD
--
-- Proof. Let q = p^e with e = ν_p(n!). Since p ≡ 1 (mod 4), -1 is a square mod p, and Hensel's
-- lemma lifts it to ι ∈ ZMod q with ι² = -1. The two ring maps ℤ[i] → ZMod q sending i to ι and
-- to -ι send P = ∏_{k ≤ n} (1 + k i) to ι^(n+1) ∏ (k - ι) and (-ι)^(n+1) ∏ (k + ι); both
-- products are products of n+1 consecutive residues, so they are images of (n+1)!·(...) and vanish
-- because q ∣ n!. Their difference is 2·Im(P)·ι, and 2 and ι are units mod q, so q ∣ Im(P) = a(n).

open Finset

namespace OMAStepA105751H1

/-- `a n` is the imaginary part of the Gaussian-integer product `∏_{k ≤ n} (1 + k i)`. -/
lemma a_eq_im (n : ℕ) :
    OeisA105751.a n = (∏ k ∈ range (n + 1), (⟨1, (k : ℤ)⟩ : GaussianInt)).im := by
  have h : (∏ k ∈ range (n + 1), (1 + (k : ℂ) * Complex.I)) =
      GaussianInt.toComplex (∏ k ∈ range (n + 1), (⟨1, (k : ℤ)⟩ : GaussianInt)) := by
    rw [map_prod]
    refine prod_congr rfl (fun k _ => ?_)
    rw [GaussianInt.toComplex_def']
    push_cast
    ring
  show ⌊(∏ k ∈ range (n + 1), (1 + (k : ℂ) * Complex.I)).im⌋ = _
  rw [h]
  have him : (GaussianInt.toComplex (∏ k ∈ range (n + 1), (⟨1, (k : ℤ)⟩ : GaussianInt))).im =
      ((∏ k ∈ range (n + 1), (⟨1, (k : ℤ)⟩ : GaussianInt)).im : ℝ) := by
    rw [GaussianInt.toComplex_def]
    simp
  rw [him, Int.floor_intCast]

/-- For `p ≡ 1 (mod 4)`, `-1` has a square root modulo every power of `p`. -/
lemma exists_sqrt_neg_one (p : ℕ) (hp : p.Prime) (hmod : p % 4 = 1) (e : ℕ) :
    ∃ ι : ZMod (p ^ e), ι * ι = -1 := by
  have hF : Fact p.Prime := ⟨hp⟩
  obtain ⟨y, hy⟩ := ZMod.exists_sq_eq_neg_one_iff.2 (by omega : p % 4 ≠ 3)
  set c : ℤ := (y.val : ℤ) with hc_def
  have hc : (p : ℤ) ∣ c ^ 2 + 1 := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    have : ((c : ℤ) : ZMod p) = y := by
      rw [hc_def, Int.cast_natCast, ZMod.natCast_zmod_val]
    push_cast
    rw [this, sq, ← hy]
    ring
  have hpz : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have hp5 : 5 ≤ p := by
    have := hp.two_le
    omega
  have h2c : ¬ (p : ℤ) ∣ 2 * c := by
    intro h
    have hp2 : ¬ (p : ℤ) ∣ 2 := by
      intro h2
      have := Int.le_of_dvd (by norm_num) h2
      omega
    have hpc : (p : ℤ) ∣ c := (hpz.dvd_or_dvd h).resolve_left hp2
    have h3 : (p : ℤ) ∣ c ^ 2 := dvd_pow hpc two_ne_zero
    have h1 : (p : ℤ) ∣ 1 := (dvd_add_right h3).mp hc
    have := Int.le_of_dvd (by norm_num) h1
    omega
  let F : Polynomial ℤ := Polynomial.X ^ 2 + 1
  have e1 : F.aeval (c : ℤ_[p]) = ((c ^ 2 + 1 : ℤ) : ℤ_[p]) := by
    simp [F]
  have e2 : F.derivative.aeval (c : ℤ_[p]) = ((2 * c : ℤ) : ℤ_[p]) := by
    first
      | simp [F, map_ofNat]
      | (simp [F]; left; exact map_ofNat _ 2)
  have hnorm : ‖F.aeval (c : ℤ_[p])‖ < ‖F.derivative.aeval (c : ℤ_[p])‖ ^ 2 := by
    rw [e1, e2]
    have n1 : ‖((c ^ 2 + 1 : ℤ) : ℤ_[p])‖ < 1 := (PadicInt.norm_int_lt_one_iff_dvd _).2 hc
    have n2 : ‖((2 * c : ℤ) : ℤ_[p])‖ = 1 := by
      have hle := PadicInt.norm_le_one ((2 * c : ℤ) : ℤ_[p])
      have hnlt : ¬ ‖((2 * c : ℤ) : ℤ_[p])‖ < 1 :=
        fun h => h2c ((PadicInt.norm_int_lt_one_iff_dvd _).1 h)
      linarith [not_lt.mp hnlt]
    rw [n2, one_pow]
    exact n1
  obtain ⟨z, hz, -⟩ := hensels_lemma hnorm
  have hz' : z * z = -1 := by
    simp [F] at hz
    linear_combination hz
  refine ⟨PadicInt.toZModPow e z, ?_⟩
  rw [← map_mul, hz', map_neg, map_one]

/-- A product of `n + 1` consecutive residues vanishes modulo any `q ∣ n!`. -/
lemma prod_consecutive_eq_zero (n q : ℕ) [NeZero q] (hq : q ∣ n.factorial) (y : ZMod q) :
    ∏ k ∈ range (n + 1), ((k : ZMod q) + y) = 0 := by
  have h : ∏ k ∈ range (n + 1), ((k : ZMod q) + y) = ((y.val.ascFactorial (n + 1) : ℕ) : ZMod q) := by
    rw [Nat.ascFactorial_eq_prod_range, Nat.cast_prod]
    refine prod_congr rfl (fun k _ => ?_)
    push_cast
    rw [ZMod.natCast_zmod_val]
    ring
  rw [h, CharP.cast_eq_zero_iff (ZMod q) q]
  exact hq.trans ((Nat.factorial_dvd_factorial (Nat.le_succ n)).trans
    (Nat.factorial_dvd_ascFactorial _ _))

end OMAStepA105751H1

open OMAStepA105751H1 in
theorem OMA.solution : OMA.R_OeisA105751_conjecture_variants_moll_p_mod_4_eq_1_R1.H1 := by
  intro p hp hmod n
  set e := padicValNat p n.factorial
  have hq0 : p ^ e ≠ 0 := pow_ne_zero _ hp.ne_zero
  have : NeZero (p ^ e) := ⟨hq0⟩
  have hq : p ^ e ∣ n.factorial := pow_padicValNat_dvd
  obtain ⟨ι, hι⟩ := exists_sqrt_neg_one p hp hmod e
  have hd1 : ι * ι = ((-1 : ℤ) : ZMod (p ^ e)) := by rw [hι]; push_cast; rfl
  have hd2 : (-ι) * (-ι) = ((-1 : ℤ) : ZMod (p ^ e)) := by rw [neg_mul_neg, hι]; push_cast; rfl
  let ψp : GaussianInt →+* ZMod (p ^ e) := Zsqrtd.lift ⟨ι, hd1⟩
  let ψm : GaussianInt →+* ZMod (p ^ e) := Zsqrtd.lift ⟨-ι, hd2⟩
  set P := ∏ k ∈ range (n + 1), (⟨1, (k : ℤ)⟩ : GaussianInt) with hP
  have hpz : ψp P = 0 := by
    rw [hP, map_prod]
    have hk : ∀ k ∈ range (n + 1), ψp ⟨1, (k : ℤ)⟩ = ι * ((k : ZMod (p ^ e)) + (-ι)) := by
      intro k _
      simp only [ψp, Zsqrtd.lift_apply_apply]
      push_cast
      linear_combination hι
    rw [prod_congr rfl hk, prod_mul_distrib, prod_consecutive_eq_zero n (p ^ e) hq, mul_zero]
  have hmz : ψm P = 0 := by
    rw [hP, map_prod]
    have hk : ∀ k ∈ range (n + 1), ψm ⟨1, (k : ℤ)⟩ = (-ι) * ((k : ZMod (p ^ e)) + ι) := by
      intro k _
      simp only [ψm, Zsqrtd.lift_apply_apply]
      push_cast
      linear_combination hι
    rw [prod_congr rfl hk, prod_mul_distrib, prod_consecutive_eq_zero n (p ^ e) hq, mul_zero]
  have hdiff : ψp P - ψm P = (2 * ι) * (P.im : ZMod (p ^ e)) := by
    simp only [ψp, ψm, Zsqrtd.lift_apply_apply]
    ring
  rw [hpz, hmz, sub_zero] at hdiff
  have h2 : IsUnit (2 : ZMod (p ^ e)) := by
    have hcop : Nat.Coprime 2 (p ^ e) := by
      apply Nat.Coprime.pow_right
      exact (Nat.coprime_primes Nat.prime_two hp).2 (by omega)
    exact_mod_cast (ZMod.isUnit_iff_coprime 2 (p ^ e)).2 hcop
  have hιu : IsUnit ι := ⟨⟨ι, -ι, by rw [mul_neg, hι, neg_neg], by rw [neg_mul, hι, neg_neg]⟩, rfl⟩
  have him : (P.im : ZMod (p ^ e)) = 0 := ((h2.mul hιu).mul_right_eq_zero).1 hdiff.symm
  rw [a_eq_im, ← hP]
  have := (ZMod.intCast_zmod_eq_zero_iff_dvd P.im (p ^ e)).1 him
  exact_mod_cast this
