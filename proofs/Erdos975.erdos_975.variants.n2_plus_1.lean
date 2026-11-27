import FormalConjectures.ErdosProblems.«975»

/-!
# Proof of Erdős Problem 975 (`Erdos975.erdos_975.variants.n2_plus_1`)

We prove that there exists `c > 0` such that
`Erdos975Sum (X ^ 2 + 1) x / (x * log x) → c` as `x → ∞`.

By divisor symmetry `τ(n^2 + 1) = 2 * #{1 ≤ d ≤ n : d ∣ n^2 + 1}` for `n ≥ 1`, summing over `n ≤ N`
and swapping the order of summation reduces the problem to estimating `∑_{d ≤ N} ρ(d) / d`,
where `ρ(d) = #{a ∈ ZMod d : a^2 + 1 = 0}`. Using the exact multiplicative identity
`ρ = μ_sq * (χ₄ * ζ)`, hyperbola summation for `χ₄ * ζ` (with Leibniz's series for `π / 4`),
and Abel summation gives `c = (π / 2) * ∑_{u ≥ 1} μ(u) / u^2 > 0`.
-/

-- Credit: @green-notes

open Filter Real Polynomial Finset
open scoped ArithmeticFunction.sigma ArithmeticFunction.zeta ArithmeticFunction.Moebius Topology

namespace Erdos975Proof

section RhoAndMultiplicative

private noncomputable def rho (d : ℕ) : ℕ :=
  if hd : d = 0 then 0 else
    letI : NeZero d := ⟨hd⟩
    ((Finset.univ : Finset (ZMod d)).filter (fun a ↦ a ^ 2 + 1 = 0)).card

private lemma rho_zero : rho 0 = 0 := by simp [rho]

private lemma rho_one : rho 1 = 1 := by
  simp only [rho, one_ne_zero, ↓reduceDIte]
  rw [Finset.filter_eq_self.mpr (fun a _ ↦ Subsingleton.elim _ _), Finset.card_univ, ZMod.card]

private lemma rho_pos_eq {d : ℕ} [NeZero d] :
    rho d = ((Finset.univ : Finset (ZMod d)).filter (fun a ↦ a ^ 2 + 1 = 0)).card := by
  simp only [rho, NeZero.ne d, ↓reduceDIte]

private lemma rho_mul_of_coprime {m n : ℕ} (h : m.Coprime n) :
    rho (m * n) = rho m * rho n := by
  by_cases hm : m = 0
  · subst hm; simp [rho_zero]
  by_cases hn : n = 0
  · subst hn; simp [rho_zero]
  have hmn : m * n ≠ 0 := mul_ne_zero hm hn
  have : NeZero (m * n) := ⟨hmn⟩
  have : NeZero m := ⟨hm⟩
  have : NeZero n := ⟨hn⟩
  rw [rho_pos_eq, rho_pos_eq, rho_pos_eq]
  let e := ZMod.chineseRemainder h
  let S := (Finset.univ : Finset (ZMod (m * n))).filter (fun a ↦ a ^ 2 + 1 = 0)
  let S₁ := (Finset.univ : Finset (ZMod m)).filter (fun a ↦ a ^ 2 + 1 = 0)
  let S₂ := (Finset.univ : Finset (ZMod n)).filter (fun a ↦ a ^ 2 + 1 = 0)
  change S.card = S₁.card * S₂.card
  rw [← Finset.card_product]
  refine Finset.card_bij (fun a _ ↦ e a) (fun a ha ↦ ?_) (fun a₁ _ a₂ _ h12 ↦ e.injective h12)
    (fun ⟨x, y⟩ hxy ↦ ?_)
  · have ha0 : a ^ 2 + 1 = 0 := (Finset.mem_filter.mp ha).2
    have he0 : e (a ^ 2 + 1) = 0 := by rw [ha0, map_zero]
    rw [map_add, map_pow, map_one] at he0
    rw [Finset.mem_product, Finset.mem_filter, Finset.mem_filter]
    exact ⟨⟨Finset.mem_univ _, congrArg Prod.fst he0⟩,
      ⟨Finset.mem_univ _, congrArg Prod.snd he0⟩⟩
  · rw [Finset.mem_product, Finset.mem_filter, Finset.mem_filter] at hxy
    refine ⟨e.symm (x, y), Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, e.apply_symm_apply _⟩
    apply e.injective
    rw [map_add, map_pow, map_one, map_zero, e.apply_symm_apply]
    ext
    · exact hxy.1.2
    · exact hxy.2.2

private noncomputable def rhoAF : ArithmeticFunction ℤ where
  toFun d := (rho d : ℤ)
  map_zero' := by simp [rho_zero]

private lemma rhoAF_isMultiplicative : rhoAF.IsMultiplicative := by
  rw [ArithmeticFunction.IsMultiplicative.iff_ne_zero]
  refine ⟨by simp [rhoAF, rho_one], fun {m n} _ _ h ↦ ?_⟩
  simp only [rhoAF, ArithmeticFunction.coe_mk, rho_mul_of_coprime h, Nat.cast_mul]

private def chi4Fun (n : ℕ) : ℤ :=
  if n % 4 = 1 then 1 else if n % 4 = 3 then -1 else 0

private lemma chi4Fun_zero : chi4Fun 0 = 0 := by simp [chi4Fun]

private lemma chi4Fun_one : chi4Fun 1 = 1 := by simp [chi4Fun]

private lemma chi4Fun_mul (m n : ℕ) : chi4Fun (m * n) = chi4Fun m * chi4Fun n := by
  have hmod : (m * n) % 4 = ((m % 4) * (n % 4)) % 4 := Nat.mul_mod m n 4
  have hm : m % 4 < 4 := Nat.mod_lt m (by omega)
  have hn : n % 4 < 4 := Nat.mod_lt n (by omega)
  simp only [chi4Fun]
  rw [hmod]
  interval_cases h1 : m % 4 <;> interval_cases h2 : n % 4 <;> decide

private def chi4 : ArithmeticFunction ℤ where
  toFun := chi4Fun
  map_zero' := chi4Fun_zero

private lemma chi4_isMultiplicative : chi4.IsMultiplicative := by
  rw [ArithmeticFunction.IsMultiplicative.iff_ne_zero]
  exact ⟨chi4Fun_one, fun {m n} _ _ _ ↦ chi4Fun_mul m n⟩

private lemma abs_chi4_le_one (k : ℕ) : |(chi4 k : ℝ)| ≤ 1 := by
  simp only [chi4, ArithmeticFunction.coe_mk, chi4Fun]
  split_ifs <;> norm_num

private lemma isSquare_mul_iff_of_coprime {m n : ℕ} (h : m.Coprime n) :
    IsSquare (m * n) ↔ IsSquare m ∧ IsSquare n := by
  constructor
  · rintro ⟨k, hk⟩
    by_cases hm : m = 0
    · subst hm; exact ⟨⟨0, rfl⟩, by simp at h; subst h; exact ⟨1, rfl⟩⟩
    by_cases hn : n = 0
    · subst hn; exact ⟨by simp at h; subst h; exact ⟨1, rfl⟩, ⟨0, rfl⟩⟩
    have hk0 : k ≠ 0 := fun h0 ↦ mul_ne_zero hm hn (by simp [hk, h0])
    have hfac : ∀ p : ℕ, Even (m.factorization p) ∧ Even (n.factorization p) := by
      intro p
      have hsum : m.factorization p + n.factorization p = 2 * k.factorization p := by
        have h1 := congrArg (fun t ↦ Nat.factorization t p) hk
        rw [Nat.factorization_mul hm hn, Finsupp.add_apply,
          Nat.factorization_mul hk0 hk0, Finsupp.add_apply] at h1
        omega
      have hdisj := h.disjoint_primeFactors
      by_cases hpm : p ∈ m.primeFactors
      · have hpn : p ∉ n.primeFactors := Finset.disjoint_left.mp hdisj hpm
        have hn0 : n.factorization p = 0 := Finsupp.notMem_support_iff.mp hpn
        rw [hn0, add_zero] at hsum
        exact ⟨⟨k.factorization p, by omega⟩, ⟨0, by omega⟩⟩
      · have hm0 : m.factorization p = 0 := Finsupp.notMem_support_iff.mp hpm
        rw [hm0, zero_add] at hsum
        exact ⟨⟨0, by omega⟩, ⟨k.factorization p, by omega⟩⟩
    have sq_of_even : ∀ a : ℕ, a ≠ 0 → (∀ p : ℕ, Even (a.factorization p)) → IsSquare a := by
      intro a ha hev
      refine ⟨∏ p ∈ a.primeFactors, p ^ (a.factorization p / 2), ?_⟩
      conv_lhs => rw [← Nat.prod_factorization_pow_eq_self ha]
      rw [← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun p _ ↦ ?_
      obtain ⟨r, hr⟩ := hev p
      rw [hr, show (r + r) / 2 = r by omega, ← pow_add]
    exact ⟨sq_of_even m hm (fun p ↦ (hfac p).1), sq_of_even n hn (fun p ↦ (hfac p).2)⟩
  · rintro ⟨⟨a, rfl⟩, ⟨b, rfl⟩⟩
    exact ⟨a * b, by ring⟩

private def muSq : ArithmeticFunction ℤ where
  toFun n := if IsSquare n then μ (Nat.sqrt n) else 0
  map_zero' := by simp

private lemma muSq_isMultiplicative : muSq.IsMultiplicative := by
  rw [ArithmeticFunction.IsMultiplicative.iff_ne_zero]
  refine ⟨by simp [muSq], fun {m n} hm hn h ↦ ?_⟩
  simp only [muSq, ArithmeticFunction.coe_mk, isSquare_mul_iff_of_coprime h]
  by_cases hsq : IsSquare m ∧ IsSquare n
  · obtain ⟨⟨a, rfl⟩, ⟨b, rfl⟩⟩ := hsq
    have hcop_ab : a.Coprime b :=
      Nat.Coprime.coprime_dvd_left (dvd_mul_left a a)
        (Nat.Coprime.coprime_dvd_right (dvd_mul_left b b) h)
    have hs1 : Nat.sqrt (a * a) = a := Nat.sqrt_eq a
    have hs2 : Nat.sqrt (b * b) = b := Nat.sqrt_eq b
    have hs12 : Nat.sqrt ((a * a) * (b * b)) = a * b := by
      rw [show (a * a) * (b * b) = (a * b) * (a * b) by ring, Nat.sqrt_eq]
    simp only [IsSquare.mul_self, and_self, ↓reduceIte, hs1, hs2, hs12]
    exact ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hcop_ab
  · by_cases hsm : IsSquare m
    · have hsn : ¬ IsSquare n := fun hn' ↦ hsq ⟨hsm, hn'⟩
      simp [hsm, hsn]
    · simp [hsm]

private lemma rho_two_pow {e : ℕ} (he : 1 ≤ e) :
    rho (2 ^ e) = if e = 1 then 1 else 0 := by
  rcases eq_or_lt_of_le he with rfl | he2
  · simp only [↓reduceIte]
    rw [rho_pos_eq, Finset.card_eq_one]
    refine ⟨1, ?_⟩
    ext a
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    constructor
    · intro ha
      have hv : a.val < 2 := by simpa using a.val_lt
      have hval0 : a.val ≠ 0 := by
        intro h0
        have : a = 0 := by rw [← ZMod.natCast_zmod_val a, h0, Nat.cast_zero]
        rw [this] at ha
        have hnot : (2 ^ 1 : ℕ) ∣ 1 := by
          rw [← ZMod.natCast_eq_zero_iff]
          simp at ha
        exact absurd hnot (by decide)
      have hval1 : a.val = 1 := by omega
      rw [← ZMod.natCast_zmod_val a, hval1, Nat.cast_one]
    · rintro rfl
      rw [one_pow, one_add_one_eq_two, ← Nat.cast_two]
      exact (ZMod.natCast_eq_zero_iff 2 (2 ^ 1)).mpr (by decide)
  · have he2' : 2 ≤ e := he2
    have : NeZero (2 ^ e) := ⟨by positivity⟩
    rw [rho_pos_eq, if_neg (by omega), Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro a _ ha
    have h2e_dvd : 2 ^ e ∣ a.val ^ 2 + 1 := by
      rw [← ZMod.natCast_eq_zero_iff]
      push_cast
      simpa [ZMod.natCast_zmod_val] using ha
    have h4_dvd : 4 ∣ a.val ^ 2 + 1 :=
      (show 4 ∣ 2 ^ e from (by decide : 4 = 2 ^ 2) ▸ Nat.pow_dvd_pow 2 he2').trans h2e_dvd
    have hmod : (a.val ^ 2 + 1) % 4 = 0 := Nat.dvd_iff_mod_eq_zero.mp h4_dvd
    have hval : a.val = 4 * (a.val / 4) + a.val % 4 := (Nat.div_add_mod a.val 4).symm
    have ha4 : a.val % 4 < 4 := Nat.mod_lt _ (by omega)
    have hsq4 : (a.val ^ 2 + 1) % 4 = ((a.val % 4) ^ 2 + 1) % 4 := by
      have : a.val ^ 2 + 1 =
          4 * (4 * (a.val / 4) ^ 2 + 2 * (a.val / 4) * (a.val % 4)) + ((a.val % 4) ^ 2 + 1) := by
        conv_lhs => rw [hval]
        ring
      rw [this, Nat.mul_add_mod]
    rw [hsq4] at hmod
    interval_cases a.val % 4 <;> norm_num at hmod

private lemma rho_prime_mod4_three {p e : ℕ} (hp : p.Prime) (hp3 : p % 4 = 3) (he : 1 ≤ e) :
    rho (p ^ e) = 0 := by
  have hpe : p ^ e ≠ 0 := pow_ne_zero e hp.ne_zero
  have : NeZero (p ^ e) := ⟨hpe⟩
  rw [rho_pos_eq, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro a _ ha
  have hdvd : p ^ e ∣ a.val ^ 2 + 1 := by
    rw [← ZMod.natCast_eq_zero_iff]
    push_cast
    simpa [ZMod.natCast_zmod_val] using ha
  have hp_dvd : p ∣ a.val ^ 2 + 1 := (dvd_pow_self p (by omega)).trans hdvd
  have hsq : IsSquare (-1 : ZMod p) := by
    refine ⟨(a.val : ZMod p), ?_⟩
    have hz : ((a.val ^ 2 + 1 : ℕ) : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr hp_dvd
    push_cast at hz
    linear_combination -hz
  have : Fact p.Prime := ⟨hp⟩
  rw [ZMod.exists_sq_eq_neg_one_iff] at hsq
  exact hsq hp3

private lemma exists_sq_neg_one_prime_pow {p : ℕ} (hp : p.Prime) (hp1 : p % 4 = 1) :
    ∀ e : ℕ, 1 ≤ e → ∃ r : ZMod (p ^ e), r ^ 2 + 1 = 0 := by
  have : Fact p.Prime := ⟨hp⟩
  intro e he
  induction e, he using Nat.le_induction with
  | base =>
    obtain ⟨r, hr⟩ := ZMod.exists_sq_eq_neg_one_iff.mpr (by omega : p % 4 ≠ 3)
    have hdvd : p ∣ r.val ^ 2 + 1 := by
      rw [← ZMod.natCast_eq_zero_iff]
      push_cast
      rw [ZMod.natCast_zmod_val, sq, ← hr]
      ring
    refine ⟨(r.val : ZMod (p ^ 1)), ?_⟩
    have hz : ((r.val ^ 2 + 1 : ℕ) : ZMod (p ^ 1)) = 0 :=
      (ZMod.natCast_eq_zero_iff _ _).mpr (by simpa [pow_one] using hdvd)
    push_cast at hz
    exact hz
  | succ k hk ih =>
    obtain ⟨r, hr⟩ := ih
    have hdvd : p ^ k ∣ r.val ^ 2 + 1 := by
      rw [← ZMod.natCast_eq_zero_iff]
      push_cast
      simpa [ZMod.natCast_zmod_val] using hr
    obtain ⟨m, hm⟩ := hdvd
    have hndvd_r : ¬ p ∣ r.val := by
      intro hpr
      have hp1' : p ∣ 1 :=
        (Nat.dvd_add_right (dvd_pow hpr (by omega))).mp ((dvd_pow_self p (by omega)).trans ⟨m, hm⟩)
      exact hp.not_dvd_one hp1'
    have hndvd_2r : ¬ p ∣ 2 * r.val := by
      intro h2r
      rcases hp.dvd_mul.mp h2r with h2 | hr'
      · have hle := Nat.le_of_dvd (by omega) h2
        have := hp.two_le
        omega
      · exact hndvd_r hr'
    have h2r_ne : ((2 * r.val : ℕ) : ZMod p) ≠ 0 := by
      rw [Ne, ZMod.natCast_eq_zero_iff]
      exact hndvd_2r
    let tz : ZMod p := -(m : ZMod p) * ((2 * r.val : ℕ) : ZMod p)⁻¹
    let t := tz.val
    have ht_eq : ((2 * r.val * t + m : ℕ) : ZMod p) = 0 := by
      push_cast
      simp only [t, ZMod.natCast_zmod_val, tz]
      rw [show (2 : ZMod p) * (r.val : ZMod p) * (-(m : ZMod p) * ((2 * r.val : ℕ) : ZMod p)⁻¹) +
          (m : ZMod p) = -(m : ZMod p) * (((2 * r.val : ℕ) : ZMod p) *
          ((2 * r.val : ℕ) : ZMod p)⁻¹) + (m : ZMod p) by push_cast; ring]
      rw [mul_inv_cancel₀ h2r_ne]
      ring
    obtain ⟨q, hq⟩ := (ZMod.natCast_eq_zero_iff _ _).mp ht_eq
    let u := r.val + t * p ^ k
    have hu_dvd : p ^ (k + 1) ∣ u ^ 2 + 1 := by
      refine ⟨q + t ^ 2 * p ^ (k - 1), ?_⟩
      have hpow2 : p ^ k * p ^ k = p ^ (k + 1) * p ^ (k - 1) := by
        calc p ^ k * p ^ k = p ^ (k + k) := (pow_add p k k).symm
          _ = p ^ ((k + 1) + (k - 1)) := by congr 1; omega
          _ = p ^ (k + 1) * p ^ (k - 1) := pow_add p (k + 1) (k - 1)
      calc u ^ 2 + 1
          = (r.val ^ 2 + 1) + 2 * r.val * t * p ^ k + t ^ 2 * (p ^ k * p ^ k) := by
            dsimp [u]; ring
        _ = p ^ k * m + (2 * r.val * t) * p ^ k + t ^ 2 * (p ^ (k + 1) * p ^ (k - 1)) := by
            rw [hm, hpow2]
        _ = p ^ k * (2 * r.val * t + m) + p ^ (k + 1) * (t ^ 2 * p ^ (k - 1)) := by ring
        _ = p ^ k * (p * q) + p ^ (k + 1) * (t ^ 2 * p ^ (k - 1)) := by rw [hq]
        _ = p ^ (k + 1) * (q + t ^ 2 * p ^ (k - 1)) := by rw [pow_succ]; ring
    refine ⟨(u : ZMod (p ^ (k + 1))), ?_⟩
    have hz : ((u ^ 2 + 1 : ℕ) : ZMod (p ^ (k + 1))) = 0 :=
      (ZMod.natCast_eq_zero_iff _ _).mpr hu_dvd
    push_cast at hz
    exact hz

private lemma rho_prime_mod4_one {p e : ℕ} (hp : p.Prime) (hp1 : p % 4 = 1) (he : 1 ≤ e) :
    rho (p ^ e) = 2 := by
  have hpe : p ^ e ≠ 0 := pow_ne_zero e hp.ne_zero
  have : NeZero (p ^ e) := ⟨hpe⟩
  rw [rho_pos_eq]
  obtain ⟨r, hr⟩ := exists_sq_neg_one_prime_pow hp hp1 e he
  have hp_dvd_r : p ^ e ∣ r.val ^ 2 + 1 := by
    rw [← ZMod.natCast_eq_zero_iff]
    push_cast
    simpa [ZMod.natCast_zmod_val] using hr
  have hndvd_2r : ¬ p ∣ 2 * r.val := by
    intro h2r
    rcases hp.dvd_mul.mp h2r with h2 | hr'
    · have hle := Nat.le_of_dvd (by omega) h2
      have := hp.two_le
      omega
    · have hp1' : p ∣ 1 :=
        (Nat.dvd_add_right (dvd_pow hr' (by omega))).mp ((dvd_pow_self p (by omega)).trans hp_dvd_r)
      exact hp.not_dvd_one hp1'
  have hne : r ≠ -r := by
    intro heq
    have h2r0 : (2 * r.val : ZMod (p ^ e)) = 0 := by
      have : (2 : ZMod (p ^ e)) * r = 0 := by
        calc (2 : ZMod (p ^ e)) * r = r + r := two_mul r
          _ = r + (-r) := by rw [← heq]
          _ = 0 := add_neg_cancel r
      rwa [← ZMod.natCast_zmod_val r] at this
    rw [← Nat.cast_two, ← Nat.cast_mul, ZMod.natCast_eq_zero_iff] at h2r0
    exact hndvd_2r ((dvd_pow_self p (by omega)).trans h2r0)
  have hset : (Finset.univ : Finset (ZMod (p ^ e))).filter (fun a ↦ a ^ 2 + 1 = 0) = {r, -r} := by
    ext a
    simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · intro ha
      have ha_dvd : (p ^ e : ℤ) ∣ (a.val : ℤ) ^ 2 + 1 := by
        have ha_nat : p ^ e ∣ a.val ^ 2 + 1 := by
          rw [← ZMod.natCast_eq_zero_iff]
          push_cast
          simpa [ZMod.natCast_zmod_val] using ha.2
        exact_mod_cast ha_nat
      have hr_dvd : (p ^ e : ℤ) ∣ (r.val : ℤ) ^ 2 + 1 := by exact_mod_cast hp_dvd_r
      have hdiff : (p ^ e : ℤ) ∣ ((a.val : ℤ) - (r.val : ℤ)) * ((a.val : ℤ) + (r.val : ℤ)) := by
        have hsub := dvd_sub ha_dvd hr_dvd
        have hsq : (a.val : ℤ) ^ 2 + 1 - ((r.val : ℤ) ^ 2 + 1) =
            ((a.val : ℤ) - (r.val : ℤ)) * ((a.val : ℤ) + (r.val : ℤ)) := by ring
        rwa [hsq] at hsub
      have hnot_both : ¬ ((p : ℤ) ∣ (a.val : ℤ) - (r.val : ℤ) ∧
          (p : ℤ) ∣ (a.val : ℤ) + (r.val : ℤ)) := by
        rintro ⟨h1, h2⟩
        have h2r : (p : ℤ) ∣ (2 * r.val : ℕ) := by
          have hs := dvd_sub h2 h1
          have : (a.val : ℤ) + (r.val : ℤ) - ((a.val : ℤ) - (r.val : ℤ)) =
              ((2 * r.val : ℕ) : ℤ) := by push_cast; ring
          rwa [this] at hs
        exact hndvd_2r (Int.natCast_dvd_natCast.mp h2r)
      have hcop_or : IsCoprime (p ^ e : ℤ) ((a.val : ℤ) - (r.val : ℤ)) ∨
          IsCoprime (p ^ e : ℤ) ((a.val : ℤ) + (r.val : ℤ)) := by
        have hprime_int : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
        rcases not_and_or.mp hnot_both with h1 | h2
        · left; exact (hprime_int.coprime_iff_not_dvd.mpr h1).pow_left
        · right; exact (hprime_int.coprime_iff_not_dvd.mpr h2).pow_left
      rcases hcop_or with hc1 | hc2
      · right
        have hd : (p ^ e : ℤ) ∣ (a.val : ℤ) + (r.val : ℤ) := hc1.dvd_of_dvd_mul_left hdiff
        have hz := (ZMod.intCast_zmod_eq_zero_iff_dvd ((a.val : ℤ) + (r.val : ℤ)) (p ^ e)).mpr hd
        have hz' : (a.val : ZMod (p ^ e)) + (r.val : ZMod (p ^ e)) = 0 := by exact_mod_cast hz
        rw [ZMod.natCast_zmod_val, ZMod.natCast_zmod_val] at hz'
        exact eq_neg_of_add_eq_zero_left hz'
      · left
        have hd : (p ^ e : ℤ) ∣ (a.val : ℤ) - (r.val : ℤ) := hc2.dvd_of_dvd_mul_right hdiff
        have hz := (ZMod.intCast_zmod_eq_zero_iff_dvd ((a.val : ℤ) - (r.val : ℤ)) (p ^ e)).mpr hd
        have hz' : (a.val : ZMod (p ^ e)) - (r.val : ZMod (p ^ e)) = 0 := by exact_mod_cast hz
        rw [ZMod.natCast_zmod_val, ZMod.natCast_zmod_val] at hz'
        exact sub_eq_zero.mp hz'
    · rintro (rfl | rfl)
      · exact ⟨Finset.mem_univ _, hr⟩
      · exact ⟨Finset.mem_univ _, by simpa [neg_sq] using hr⟩
  rw [hset, Finset.card_pair hne]

private lemma sum_divisorsAntidiagonal_eq {R : Type*} [AddCommMonoid R] {d : ℕ} (hd0 : d ≠ 0)
    (F : ℕ → ℕ → R) :
    ∑ x ∈ d.divisorsAntidiagonal, F x.1 x.2 = ∑ u ∈ d.divisors, F u (d / u) := by
  refine Finset.sum_bij (fun x _ ↦ x.1) (fun x hx ↦ ?_) (fun x₁ hx₁ x₂ hx₂ h12 ↦ ?_)
    (fun u hu ↦ ?_) (fun x hx ↦ ?_)
  · obtain ⟨hprod, hne⟩ := Nat.mem_divisorsAntidiagonal.mp hx
    exact Nat.mem_divisors.mpr ⟨⟨x.2, hprod.symm⟩, hne⟩
  · obtain ⟨hp1, _⟩ := Nat.mem_divisorsAntidiagonal.mp hx₁
    obtain ⟨hp2, _⟩ := Nat.mem_divisorsAntidiagonal.mp hx₂
    have hx1_pos : 0 < x₁.1 := Nat.pos_of_dvd_of_pos ⟨x₁.2, hp1.symm⟩ (Nat.pos_of_ne_zero hd0)
    have hx2_eq : x₁.2 = x₂.2 := by
      calc x₁.2 = (x₁.1 * x₁.2) / x₁.1 := (Nat.mul_div_cancel_left _ hx1_pos).symm
        _ = d / x₁.1 := by rw [hp1]
        _ = d / x₂.1 := by rw [h12]
        _ = (x₂.1 * x₂.2) / x₂.1 := by rw [hp2]
        _ = x₂.2 := Nat.mul_div_cancel_left _ (h12 ▸ hx1_pos)
    exact Prod.ext h12 hx2_eq
  · have hu_dvd := Nat.dvd_of_mem_divisors hu
    exact ⟨(u, d / u), Nat.mem_divisorsAntidiagonal.mpr ⟨Nat.mul_div_cancel' hu_dvd, hd0⟩, rfl⟩
  · obtain ⟨hprod, _⟩ := Nat.mem_divisorsAntidiagonal.mp hx
    have hx1_pos : 0 < x.1 := Nat.pos_of_dvd_of_pos ⟨x.2, hprod.symm⟩ (Nat.pos_of_ne_zero hd0)
    have hdiv : d / x.1 = x.2 := by rw [← hprod, Nat.mul_div_cancel_left _ hx1_pos]
    rw [hdiv]

private lemma rhoAF_eq_muSq_mul_chi4_mul_zeta :
    rhoAF = muSq * (chi4 * ζ) := by
  refine (ArithmeticFunction.IsMultiplicative.eq_iff_eq_on_prime_powers
    rhoAF rhoAF_isMultiplicative (muSq * (chi4 * ζ))
    (muSq_isMultiplicative.mul
      (chi4_isMultiplicative.mul ArithmeticFunction.isMultiplicative_zeta.natCast))).mpr ?_
  intro p e hp
  by_cases he0 : e = 0
  · subst he0
    simp [rhoAF_isMultiplicative.map_one,
      (muSq_isMultiplicative.mul (chi4_isMultiplicative.mul ArithmeticFunction.isMultiplicative_zeta.natCast)).map_one]
  have he1 : 1 ≤ e := Nat.pos_of_ne_zero he0
  have hpe0 : p ^ e ≠ 0 := pow_ne_zero e hp.ne_zero
  have hconv : ∀ m : ℕ, (chi4 * (ζ : ArithmeticFunction ℤ)) (p ^ m) =
      ∑ i ∈ Finset.range (m + 1), chi4 (p ^ i) := by
    intro m
    rw [ArithmeticFunction.coe_mul_zeta_apply, Nat.sum_divisors_prime_pow hp]
  have hmu : (muSq * (chi4 * (ζ : ArithmeticFunction ℤ))) (p ^ e) =
      if e = 1 then (chi4 * (ζ : ArithmeticFunction ℤ)) (p ^ e)
      else (chi4 * (ζ : ArithmeticFunction ℤ)) (p ^ e) -
        (chi4 * (ζ : ArithmeticFunction ℤ)) (p ^ (e - 2)) := by
    rw [ArithmeticFunction.mul_apply,
      sum_divisorsAntidiagonal_eq hpe0 (fun x y ↦ muSq x * (chi4 * (ζ : ArithmeticFunction ℤ)) y),
      Nat.sum_divisors_prime_pow hp]
    have hdiv_pow : ∀ x ∈ Finset.range (e + 1),
        muSq (p ^ x) * (chi4 * (ζ : ArithmeticFunction ℤ)) (p ^ e / p ^ x) =
          muSq (p ^ x) * (chi4 * (ζ : ArithmeticFunction ℤ)) (p ^ (e - x)) := by
      intro x hx
      rw [Finset.mem_range] at hx
      rw [Nat.pow_div (by omega) hp.pos]
    rw [Finset.sum_congr rfl hdiv_pow]
    rcases eq_or_lt_of_le he1 with rfl | he2
    · simp [Finset.sum_range_succ, muSq, hp.not_isSquare]
    · have he2' : 2 ≤ e := he2
      rw [if_neg (by omega)]
      have hterm : ∀ x ∈ Finset.range (e + 1),
          muSq (p ^ x) * (chi4 * (ζ : ArithmeticFunction ℤ)) (p ^ (e - x)) =
            if x = 0 then (chi4 * (ζ : ArithmeticFunction ℤ)) (p ^ e)
            else if x = 2 then -(chi4 * (ζ : ArithmeticFunction ℤ)) (p ^ (e - 2))
            else 0 := by
        intro x _
        rcases eq_or_ne x 0 with rfl | hx0
        · simp [muSq]
        rcases eq_or_ne x 2 with rfl | hx2
        · have hsq : IsSquare (p ^ 2) := ⟨p, by ring⟩
          simp [muSq, hsq, ArithmeticFunction.moebius_apply_prime hp]
        · rw [if_neg hx0, if_neg hx2]
          by_cases hsq : IsSquare (p ^ x)
          · have hx_even : Even x := by
              obtain ⟨k, hk⟩ := hsq
              have hpx0 : p ^ x ≠ 0 := pow_ne_zero x hp.ne_zero
              have hk0 : k ≠ 0 := fun h0 ↦ hpx0 (by simp [hk, h0])
              have hfac := congrArg (fun t ↦ Nat.factorization t p) hk
              rw [Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul, hp.factorization_self,
                mul_one, Nat.factorization_mul hk0 hk0, Finsupp.add_apply, ← two_mul] at hfac
              exact ⟨k.factorization p, by omega⟩
            obtain ⟨m, hm⟩ := hx_even
            have hm2 : 2 ≤ m := by omega
            have hsqrt : Nat.sqrt (p ^ x) = p ^ m := by
              rw [hm, show m + m = 2 * m by omega, mul_comm, pow_mul, sq, Nat.sqrt_eq]
            simp only [muSq, ArithmeticFunction.coe_mk, hsq, ↓reduceIte, hsqrt]
            rw [ArithmeticFunction.moebius_apply_prime_pow hp (by omega), if_neg (by omega), zero_mul]
          · simp [muSq, hsq]
      rw [Finset.sum_congr rfl hterm, Finset.sum_ite, Finset.sum_ite]
      have hfilt0 : (Finset.range (e + 1)).filter (· = 0) = {0} := by
        ext x; simp
      have hfilt2 : ((Finset.range (e + 1)).filter (· ≠ 0)).filter (· = 2) = {2} := by
        ext x; simp [Finset.mem_range]
        omega
      rw [hfilt0, hfilt2, Finset.sum_singleton, Finset.sum_singleton]
      simp [sub_eq_add_neg]
  simp only [rhoAF, ArithmeticFunction.coe_mk]
  rcases hp.eq_two_or_odd with rfl | hp_odd
  · rw [rho_two_pow he1, hmu]
    have hchi2 : ∀ m : ℕ, (chi4 * (ζ : ArithmeticFunction ℤ)) (2 ^ m) = 1 := by
      intro m
      rw [hconv m, Finset.sum_range_succ']
      have h0 : ∀ i ∈ Finset.range m, chi4 (2 ^ (i + 1)) = 0 := by
        intro i _
        simp only [chi4, ArithmeticFunction.coe_mk, chi4Fun]
        have h2d : 2 ∣ 2 ^ (i + 1) := dvd_pow_self 2 (by omega)
        have : (2 ^ (i + 1)) % 2 = 0 := Nat.dvd_iff_mod_eq_zero.mp h2d
        have : (2 ^ (i + 1)) % 4 = 0 ∨ (2 ^ (i + 1)) % 4 = 2 := by omega
        rcases this with h4 | h4 <;> simp [h4]
      rw [Finset.sum_congr rfl h0, Finset.sum_const_zero, zero_add]
      simp [chi4, chi4Fun]
    split_ifs with he1' <;> simp [hchi2]
  · have hp4 : p % 4 = 1 ∨ p % 4 = 3 := by omega
    rcases hp4 with hp1 | hp3
    · rw [rho_prime_mod4_one hp hp1 he1, hmu]
      have hpow1 : ∀ i : ℕ, (p ^ i) % 4 = 1 := by
        intro i
        induction i with
        | zero => simp
        | succ j ih => rw [pow_succ, Nat.mul_mod, ih, hp1]
      have hchip : ∀ m : ℕ, (chi4 * (ζ : ArithmeticFunction ℤ)) (p ^ m) = (m : ℤ) + 1 := by
        intro m
        rw [hconv m]
        have h1 : ∀ i ∈ Finset.range (m + 1), chi4 (p ^ i) = 1 := by
          intro i _
          simp [chi4, chi4Fun, hpow1 i]
        rw [Finset.sum_congr rfl h1, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
        omega
      split_ifs with he1'
      · subst he1'
        rw [hchip 1]
        norm_num
      · rw [hchip e, hchip (e - 2)]
        omega
    · rw [rho_prime_mod4_three hp hp3 he1, hmu]
      have hpow_mod : ∀ i : ℕ, p ^ i % 4 = if Even i then 1 else 3 := by
        intro i
        induction i with
        | zero => simp
        | succ k ih =>
          rw [pow_succ, Nat.mul_mod, ih, hp3]
          by_cases hk : Even k
          · have hk1 : ¬ Even (k + 1) := by simpa [Nat.even_add_one] using hk
            simp [hk, hk1]
          · have hk1 : Even (k + 1) := by simpa [Nat.even_add_one] using hk
            simp [hk, hk1]
      have hchip : ∀ m : ℕ, (chi4 * (ζ : ArithmeticFunction ℤ)) (p ^ m) =
          if Even m then 1 else 0 := by
        intro m
        rw [hconv m]
        have hpow : ∀ i : ℕ, chi4 (p ^ i) = (-1 : ℤ) ^ i := by
          intro i
          simp only [chi4, ArithmeticFunction.coe_mk, chi4Fun, hpow_mod i]
          by_cases hi : Even i
          · rw [if_pos hi, if_pos rfl, hi.neg_one_pow]
          · rw [if_neg hi, if_neg (by decide), if_pos rfl, (Nat.not_even_iff_odd.mp hi).neg_one_pow]
        have hsum_alt : ∀ n : ℕ, ∑ i ∈ Finset.range n, (-1 : ℤ) ^ i = if Even n then 0 else 1 := by
          intro n
          induction n with
          | zero => simp
          | succ k ih =>
            rw [Finset.sum_range_succ, ih]
            by_cases hk : Even k
            · have hk1 : ¬ Even (k + 1) := by simpa [Nat.even_add_one] using hk
              rw [if_pos hk, if_neg hk1, hk.neg_one_pow, zero_add]
            · have hk1 : Even (k + 1) := by simpa [Nat.even_add_one] using hk
              have hk' : Odd k := Nat.not_even_iff_odd.mp hk
              rw [if_neg hk, if_pos hk1, hk'.neg_one_pow]
              ring
        simp_rw [hpow]
        rw [hsum_alt (m + 1)]
        by_cases hm : Even m
        · have hm1 : ¬ Even (m + 1) := by simpa [Nat.even_add_one] using hm
          simp [hm, hm1]
        · have hm1 : Even (m + 1) := by simpa [Nat.even_add_one] using hm
          simp [hm, hm1]
      split_ifs with he1'
      · subst he1'
        rw [hchip 1]
        simp
      · rw [hchip e, hchip (e - 2)]
        have hev : Even e ↔ Even (e - 2) := by
          rw [show e = (e - 2) + 2 by omega, Nat.even_add]
          simp
        by_cases he_ev : Even e
        · simp [he_ev, hev.mp he_ev]
        · have hne2 : ¬ Even (e - 2) := fun h ↦ he_ev (hev.mpr h)
          simp [he_ev, hne2]

private def hChi (m : ℕ) : ℝ :=
  ∑ k ∈ m.divisors, (chi4 k : ℝ)

private lemma rho_eq_sum_mu_hChi {d : ℕ} (hd : 1 ≤ d) :
    (rho d : ℝ) = ∑ u ∈ (Finset.Icc 1 (Nat.sqrt d)).filter (fun u ↦ u ^ 2 ∣ d),
      (μ u : ℝ) * hChi (d / u ^ 2) := by
  have hd0 : d ≠ 0 := by omega
  have hid : (rho d : ℝ) = ∑ x ∈ d.divisorsAntidiagonal,
      (muSq x.1 : ℝ) * (((chi4 * (ζ : ArithmeticFunction ℤ)) x.2 : ℤ) : ℝ) := by
    have h1 := congrArg (fun f : ArithmeticFunction ℤ ↦ (f d : ℝ)) rhoAF_eq_muSq_mul_chi4_mul_zeta
    rw [ArithmeticFunction.mul_apply, Int.cast_sum] at h1
    simpa [rhoAF, Int.cast_mul] using h1
  rw [hid, sum_divisorsAntidiagonal_eq hd0
    (fun x y ↦ (muSq x : ℝ) * (((chi4 * (ζ : ArithmeticFunction ℤ)) y : ℤ) : ℝ))]
  have hterm : ∀ x ∈ d.divisors,
      (muSq x : ℝ) * ((chi4 * (ζ : ArithmeticFunction ℤ)) (d / x) : ℝ) =
        if IsSquare x then (μ (Nat.sqrt x) : ℝ) * hChi (d / x) else 0 := by
    intro x _
    simp only [muSq, ArithmeticFunction.coe_mk]
    by_cases hsq : IsSquare x
    · rw [if_pos hsq, if_pos hsq, ArithmeticFunction.coe_mul_zeta_apply, Int.cast_sum]
      rfl
    · simp [hsq]
  rw [Finset.sum_congr rfl hterm, ← Finset.sum_filter]
  refine Finset.sum_bij' (fun x _ ↦ Nat.sqrt x) (fun u _ ↦ u ^ 2) ?_ ?_ ?_ ?_ ?_
  · intro x hx
    have hsq : IsSquare x := (Finset.mem_filter.mp hx).2
    have hx_dvd : x ∣ d := Nat.dvd_of_mem_divisors (Finset.mem_filter.mp hx).1
    have hx_pos : 0 < x := Nat.pos_of_mem_divisors (Finset.mem_filter.mp hx).1
    have hx_le : x ≤ d := Nat.le_of_dvd (by omega) hx_dvd
    obtain ⟨u, rfl⟩ := hsq
    rw [Nat.sqrt_eq u]
    refine Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨?_, Nat.le_sqrt.mpr ?_⟩, ?_⟩
    · nlinarith
    · nlinarith
    · simpa [sq] using hx_dvd
  · intro u hu
    obtain ⟨hu_icc, hud⟩ := Finset.mem_filter.mp hu
    rw [Finset.mem_Icc] at hu_icc
    exact Finset.mem_filter.mpr ⟨Nat.mem_divisors.mpr ⟨hud, hd0⟩, ⟨u, by ring⟩⟩
  · intro x hx
    obtain ⟨u, rfl⟩ := (Finset.mem_filter.mp hx).2
    rw [Nat.sqrt_eq u, sq]
  · intro u _
    rw [sq, Nat.sqrt_eq u]
  · intro x hx
    obtain ⟨u, rfl⟩ := (Finset.mem_filter.mp hx).2
    rw [Nat.sqrt_eq u, sq]

end RhoAndMultiplicative

section HyperbolaHChi

private def HChi (Y : ℕ) : ℝ :=
  ∑ m ∈ Finset.Icc 1 Y, hChi m

private lemma card_Icc_filter_dvd (Y k : ℕ) (hk : 1 ≤ k) :
    ((Finset.Icc 1 Y).filter (fun m ↦ k ∣ m)).card = Y / k := by
  rw [← show (Finset.Icc 1 (Y / k)).card = Y / k by
    rw [Nat.card_Icc]; exact Nat.add_sub_cancel (Y / k) 1]
  symm
  refine Finset.card_bij (fun j _ ↦ k * j) (fun j hj ↦ ?_) (fun j₁ _ j₂ _ h12 ↦ ?_)
    (fun m hm ↦ ?_)
  · rw [Finset.mem_Icc] at hj
    refine Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨by nlinarith, ?_⟩, dvd_mul_right k j⟩
    exact (mul_comm k j).trans_le ((Nat.le_div_iff_mul_le hk).mp hj.2)
  · exact Nat.mul_left_cancel hk h12
  · obtain ⟨hm_icc, hkm⟩ := Finset.mem_filter.mp hm
    rw [Finset.mem_Icc] at hm_icc
    obtain ⟨j, rfl⟩ := hkm
    refine ⟨j, Finset.mem_Icc.mpr ⟨?_, (Nat.le_div_iff_mul_le hk).mpr (by linarith)⟩, rfl⟩
    by_contra hj0
    have : j = 0 := by omega
    subst this
    omega

private lemma HChi_eq_sum_floor (Y : ℕ) :
    HChi Y = ∑ k ∈ Finset.Icc 1 Y, (chi4 k : ℝ) * ((Y / k : ℕ) : ℝ) := by
  unfold HChi hChi
  have h1 : ∀ m ∈ Finset.Icc 1 Y,
      ∑ k ∈ m.divisors, (chi4 k : ℝ) =
        ∑ k ∈ Finset.Icc 1 Y, if k ∣ m then (chi4 k : ℝ) else 0 := by
    intro m hm
    rw [Finset.mem_Icc] at hm
    rw [← Finset.sum_filter]
    refine Finset.sum_congr ?_ (fun _ _ ↦ rfl)
    ext k
    simp only [Nat.mem_divisors, Finset.mem_filter, Finset.mem_Icc]
    constructor
    · rintro ⟨hkd, hm0⟩
      exact ⟨⟨Nat.pos_of_dvd_of_pos hkd (by omega), Nat.le_trans (Nat.le_of_dvd (by omega) hkd) hm.2⟩, hkd⟩
    · rintro ⟨_, hkd⟩
      exact ⟨hkd, by omega⟩
  rw [Finset.sum_congr rfl h1, Finset.sum_comm]
  refine Finset.sum_congr rfl fun k hk ↦ ?_
  rw [Finset.mem_Icc] at hk
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_comm, card_Icc_filter_dvd Y k hk.1]

private lemma sum_range_chi4_mem (n : ℕ) :
    ∑ k ∈ Finset.range n, (chi4 k : ℝ) = 0 ∨ ∑ k ∈ Finset.range n, (chi4 k : ℝ) = 1 := by
  have hmod : ∀ m : ℕ, ∑ k ∈ Finset.range m, (chi4 k : ℝ) =
      if m % 4 = 2 ∨ m % 4 = 3 then 1 else 0 := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      rw [Finset.sum_range_succ, ih]
      have hm4 : m % 4 < 4 := Nat.mod_lt m (by omega)
      simp only [chi4, ArithmeticFunction.coe_mk, chi4Fun]
      interval_cases h : m % 4
      · have h1 : (m + 1) % 4 = 1 := by omega
        simp [h1]
      · have h1 : (m + 1) % 4 = 2 := by omega
        simp [h1]
      · have h1 : (m + 1) % 4 = 3 := by omega
        simp [h1]
      · have h1 : (m + 1) % 4 = 0 := by omega
        simp [h1]
  rw [hmod]
  split_ifs <;> simp

private lemma abs_sum_Icc_chi4_le_one (a b : ℕ) :
    |∑ k ∈ Finset.Icc a b, (chi4 k : ℝ)| ≤ 1 := by
  by_cases hab : a ≤ b
  · have hsplit : ∑ k ∈ Finset.Icc a b, (chi4 k : ℝ) =
        (∑ k ∈ Finset.range (b + 1), (chi4 k : ℝ)) - ∑ k ∈ Finset.range a, (chi4 k : ℝ) := by
      have h_eq : Finset.Icc a b = Finset.Ico a (b + 1) := rfl
      rw [h_eq, ← Finset.sum_range_add_sum_Ico (fun k ↦ (chi4 k : ℝ)) (by omega : a ≤ b + 1)]
      ring
    rw [hsplit]
    rcases sum_range_chi4_mem (b + 1) with hb | hb <;>
      rcases sum_range_chi4_mem a with ha | ha <;>
      rw [hb, ha] <;> norm_num
  · have hmt : Finset.Icc a b = ∅ := Finset.Icc_eq_empty (by omega)
    rw [hmt, Finset.sum_empty, abs_zero]
    norm_num

private lemma sum_Icc_chi4_div_eq (B : ℕ) :
    ∑ k ∈ Finset.Icc 1 B, (chi4 k : ℝ) / (k : ℝ) =
      ∑ i ∈ Finset.range ((B + 1) / 2), (-1 : ℝ) ^ i / (2 * (i : ℝ) + 1) := by
  have heven : ∀ k : ℕ, Even k → (chi4 k : ℝ) / (k : ℝ) = 0 := by
    intro k hk
    obtain ⟨m, rfl⟩ := hk
    simp only [chi4, ArithmeticFunction.coe_mk, chi4Fun]
    have h4 : (m + m) % 4 = 0 ∨ (m + m) % 4 = 2 := by omega
    rcases h4 with h4 | h4 <;> simp [h4]
  have hodd : ∀ i : ℕ, (chi4 (2 * i + 1) : ℝ) = (-1 : ℝ) ^ i := by
    intro i
    simp only [chi4, ArithmeticFunction.coe_mk, chi4Fun]
    rcases Nat.even_or_odd i with hi | hi
    · obtain ⟨j, rfl⟩ := hi
      have h4 : (2 * (j + j) + 1) % 4 = 1 := by omega
      rw [h4, if_pos rfl, show j + j = 2 * j by ring, pow_mul]
      norm_num
    · obtain ⟨j, rfl⟩ := hi
      have h4 : (2 * (2 * j + 1) + 1) % 4 = 3 := by omega
      rw [h4, if_neg (by omega), if_pos rfl, pow_add, pow_mul, pow_one]
      norm_num
  have hfilt : ∑ k ∈ Finset.Icc 1 B, (chi4 k : ℝ) / (k : ℝ) =
      ∑ k ∈ (Finset.Icc 1 B).filter Odd, (chi4 k : ℝ) / (k : ℝ) := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    by_cases hk : Odd k
    · rw [if_pos hk]
    · rw [if_neg hk, heven k (Nat.not_odd_iff_even.mp hk)]
  rw [hfilt]
  symm
  refine Finset.sum_bij (fun i _ ↦ 2 * i + 1) (fun i hi ↦ ?_) (fun i₁ _ i₂ _ h12 ↦ by omega)
    (fun k hk ↦ ?_) (fun i _ ↦ ?_)
  · rw [Finset.mem_range] at hi
    exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨by omega, by omega⟩, ⟨i, rfl⟩⟩
  · obtain ⟨hk_icc, hk_odd⟩ := Finset.mem_filter.mp hk
    rw [Finset.mem_Icc] at hk_icc
    obtain ⟨i, rfl⟩ := hk_odd
    exact ⟨i, Finset.mem_range.mpr (by omega), rfl⟩
  · rw [hodd i]
    push_cast
    rfl

private lemma abs_leibniz_sub_pi_div_four (n : ℕ) :
    |∑ i ∈ Finset.range n, (-1 : ℝ) ^ i / (2 * (i : ℝ) + 1) - π / 4| ≤ 1 / (2 * (n : ℝ) + 1) := by
  let f : ℕ → ℝ := fun i ↦ (2 * (i : ℝ) + 1)⁻¹
  have hfa : Antitone f := antitone_iff_forall_lt.mpr fun a b hab ↦ by
    dsimp [f]
    gcongr
  have hfl : Tendsto (fun k ↦ ∑ i ∈ Finset.range k, (-1 : ℝ) ^ i * f i) atTop (𝓝 (π / 4)) := by
    simpa only [f, div_eq_mul_inv] using Real.tendsto_sum_pi_div_four
  have upper := hfa.alternating_series_le_tendsto hfl
  have lower := hfa.tendsto_le_alternating_series hfl
  have heq : ∑ i ∈ Finset.range n, (-1 : ℝ) ^ i / (2 * (i : ℝ) + 1) =
      ∑ i ∈ Finset.range n, (-1 : ℝ) ^ i * f i := by
    refine Finset.sum_congr rfl fun i _ ↦ by simp [f, div_eq_mul_inv]
  rw [heq, abs_sub_le_iff]
  rcases Nat.even_or_odd n with ⟨m, rfl⟩ | ⟨m, rfl⟩
  · rw [show m + m = 2 * m by omega]
    have h1 := upper m
    have h2 := lower m
    rw [Finset.sum_range_succ, show (-1 : ℝ) ^ (2 * m) = 1 by simp, one_mul] at h2
    have hf_nn : 0 ≤ f (2 * m) := by dsimp [f]; positivity
    have hf_eq : f (2 * m) = 1 / (2 * ((2 * m : ℕ) : ℝ) + 1) := by
      dsimp [f]; push_cast; rw [one_div]
    rw [← hf_eq]
    constructor <;> linarith
  · have h1 := upper (m + 1)
    have h2 := lower m
    have hneg1 : (-1 : ℝ) ^ (2 * m + 1) = -1 := by
      rw [pow_add, pow_mul]; norm_num
    rw [show 2 * (m + 1) = 2 * m + 1 + 1 by omega, Finset.sum_range_succ,
      hneg1, neg_one_mul] at h1
    have hf_nn : 0 ≤ f (2 * m + 1) := by dsimp [f]; positivity
    have hf_eq : f (2 * m + 1) = 1 / (2 * ((2 * m + 1 : ℕ) : ℝ) + 1) := by
      dsimp [f]; push_cast; rw [one_div]
    rw [← hf_eq]
    constructor <;> linarith

private lemma HChi_approx (Y : ℕ) :
    |HChi Y - (π / 4) * (Y : ℝ)| ≤ 3 * Real.sqrt (Y : ℝ) + 2 := by
  by_cases hY0 : Y = 0
  · subst hY0
    simp [HChi]
  have hY1 : 1 ≤ Y := Nat.pos_of_ne_zero hY0
  rw [HChi_eq_sum_floor]
  let B := Nat.sqrt Y
  have hB1 : 1 ≤ B := Nat.sqrt_pos.mpr hY1
  have hBY : B ≤ Y := Nat.sqrt_le_self Y
  have hsplit : Finset.Icc 1 Y = Finset.Icc 1 B ∪ Finset.Icc (B + 1) Y := by
    ext k
    simp only [Finset.mem_union, Finset.mem_Icc]
    omega
  have hdisj : Disjoint (Finset.Icc 1 B) (Finset.Icc (B + 1) Y) := by
    rw [Finset.disjoint_left]
    intro k hk1 hk2
    rw [Finset.mem_Icc] at hk1 hk2
    omega
  rw [hsplit, Finset.sum_union hdisj]
  have hpart1_floor :
      |∑ k ∈ Finset.Icc 1 B, (chi4 k : ℝ) * ((Y / k : ℕ) : ℝ) -
        (Y : ℝ) * ∑ k ∈ Finset.Icc 1 B, (chi4 k : ℝ) / (k : ℝ)| ≤ (B : ℝ) := by
    rw [Finset.mul_sum]
    have heq : ∑ k ∈ Finset.Icc 1 B, (Y : ℝ) * ((chi4 k : ℝ) / (k : ℝ)) =
        ∑ k ∈ Finset.Icc 1 B, (chi4 k : ℝ) * ((Y : ℝ) / (k : ℝ)) := by
      refine Finset.sum_congr rfl fun k _ ↦ by ring
    rw [heq, ← Finset.sum_sub_distrib]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ k ∈ Finset.Icc 1 B,
          |(chi4 k : ℝ) * ((Y / k : ℕ) : ℝ) - (chi4 k : ℝ) * ((Y : ℝ) / (k : ℝ))|
        ≤ ∑ _k ∈ Finset.Icc 1 B, (1 : ℝ) := by
          refine Finset.sum_le_sum fun k hk ↦ ?_
          rw [Finset.mem_Icc] at hk
          have hk0 : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
          rw [← mul_sub, abs_mul]
          have hfl1 : ((Y / k : ℕ) : ℝ) ≤ (Y : ℝ) / (k : ℝ) := by
            rw [le_div_iff₀ hk0]
            exact_mod_cast Nat.div_mul_le_self Y k
          have hfl2 : (Y : ℝ) / (k : ℝ) - 1 < ((Y / k : ℕ) : ℝ) := by
            rw [sub_lt_iff_lt_add, div_lt_iff₀ hk0]
            have hlt : Y < (Y / k + 1) * k := by
              rw [add_mul, one_mul]
              exact Nat.lt_div_mul_add (by omega : 0 < k) (a := Y)
            have hcast : (Y : ℝ) < (((Y / k + 1) * k : ℕ) : ℝ) := by exact_mod_cast hlt
            push_cast at hcast
            linarith
          have habs : |((Y / k : ℕ) : ℝ) - (Y : ℝ) / (k : ℝ)| ≤ 1 := by
            rw [abs_sub_le_iff]
            constructor <;> linarith
          calc |(chi4 k : ℝ)| * |((Y / k : ℕ) : ℝ) - (Y : ℝ) / (k : ℝ)|
              ≤ 1 * 1 := mul_le_mul (abs_chi4_le_one k) habs (abs_nonneg _) zero_le_one
            _ = 1 := one_mul 1
      _ = (B : ℝ) := by simp
  have hpart1_pi :
      |(Y : ℝ) * ∑ k ∈ Finset.Icc 1 B, (chi4 k : ℝ) / (k : ℝ) - (π / 4) * (Y : ℝ)| ≤
        Real.sqrt (Y : ℝ) + 1 := by
    rw [sum_Icc_chi4_div_eq, show (π / 4) * (Y : ℝ) = (Y : ℝ) * (π / 4) by ring, ← mul_sub,
      abs_mul, abs_of_nonneg (by positivity)]
    have hleb := abs_leibniz_sub_pi_div_four ((B + 1) / 2)
    have hden : (B : ℝ) + 1 ≤ 2 * (((B + 1) / 2 : ℕ) : ℝ) + 1 := by
      exact_mod_cast (by omega : B + 1 ≤ 2 * ((B + 1) / 2) + 1)
    have hinv : 1 / (2 * (((B + 1) / 2 : ℕ) : ℝ) + 1) ≤ 1 / ((B : ℝ) + 1) :=
      div_le_div_of_nonneg_left zero_le_one (by positivity) hden
    have hY_lt : (Y : ℝ) < ((B + 1 : ℕ) : ℝ) ^ 2 := by
      have hlt : Y < (B + 1) ^ 2 := by
        rw [sq]
        exact Nat.lt_succ_sqrt Y
      exact_mod_cast hlt
    have hYB : (Y : ℝ) / ((B : ℝ) + 1) ≤ (B : ℝ) + 1 := by
      rw [div_le_iff₀ (by positivity)]
      push_cast at hY_lt
      linarith
    have hB_sqrt : (B : ℝ) ≤ Real.sqrt (Y : ℝ) := by
      refine Real.le_sqrt_of_sq_le ?_
      have hle : B ^ 2 ≤ Y := by rw [sq]; exact Nat.sqrt_le Y
      exact_mod_cast hle
    calc (Y : ℝ) * |∑ i ∈ Finset.range ((B + 1) / 2), (-1 : ℝ) ^ i / (2 * (i : ℝ) + 1) - π / 4|
        ≤ (Y : ℝ) * (1 / ((B : ℝ) + 1)) := mul_le_mul_of_nonneg_left (hleb.trans hinv) (by positivity)
      _ = (Y : ℝ) / ((B : ℝ) + 1) := by ring
      _ ≤ (B : ℝ) + 1 := hYB
      _ ≤ Real.sqrt (Y : ℝ) + 1 := by linarith
  have hpart2 :
      |∑ k ∈ Finset.Icc (B + 1) Y, (chi4 k : ℝ) * ((Y / k : ℕ) : ℝ)| ≤ (B : ℝ) := by
    let Q := Y / (B + 1)
    have hQ_le : Q ≤ B := by
      have hlt : Y < (B + 1) * (B + 1) := Nat.lt_succ_sqrt Y
      have hqlt : Y / (B + 1) < B + 1 := (Nat.div_lt_iff_lt_mul (by omega)).mpr hlt
      exact Nat.le_of_lt_succ hqlt
    have hswap : ∀ k ∈ Finset.Icc (B + 1) Y,
        (chi4 k : ℝ) * ((Y / k : ℕ) : ℝ) =
          ∑ a ∈ Finset.Icc 1 Q, if k ≤ Y / a then (chi4 k : ℝ) else 0 := by
      intro k hk
      rw [Finset.mem_Icc] at hk
      have hk_pos : 0 < k := by omega
      have hYk_le : Y / k ≤ Q := Nat.div_le_div_left hk.1 (by omega)
      have hfilt : (Finset.Icc 1 Q).filter (fun a ↦ k ≤ Y / a) = Finset.Icc 1 (Y / k) := by
        ext a
        simp only [Finset.mem_filter, Finset.mem_Icc]
        constructor
        · rintro ⟨⟨ha1, _⟩, hka⟩
          exact ⟨ha1, (Nat.le_div_iff_mul_le hk_pos).mpr ((mul_comm a k).symm ▸
            (Nat.le_div_iff_mul_le (by omega)).mp hka)⟩
        · rintro ⟨ha1, haY⟩
          refine ⟨⟨ha1, haY.trans hYk_le⟩, (Nat.le_div_iff_mul_le (by omega)).mpr ?_⟩
          rw [mul_comm k a]
          exact (Nat.le_div_iff_mul_le hk_pos).mp haY
      rw [← Finset.sum_filter, hfilt, Finset.sum_const, Nat.card_Icc,
        Nat.add_sub_cancel (Y / k) 1, nsmul_eq_mul, mul_comm]
    rw [Finset.sum_congr rfl hswap, Finset.sum_comm]
    have hinner : ∀ a ∈ Finset.Icc 1 Q,
        |∑ k ∈ Finset.Icc (B + 1) Y, if k ≤ Y / a then (chi4 k : ℝ) else 0| ≤ 1 := by
      intro a ha
      rw [Finset.mem_Icc] at ha
      rw [← Finset.sum_filter]
      have hfilt : (Finset.Icc (B + 1) Y).filter (fun k ↦ k ≤ Y / a) =
          Finset.Icc (B + 1) (min Y (Y / a)) := by
        ext k
        simp only [Finset.mem_filter, Finset.mem_Icc]
        omega
      rw [hfilt]
      exact abs_sum_Icc_chi4_le_one (B + 1) (min Y (Y / a))
    calc |∑ a ∈ Finset.Icc 1 Q, ∑ k ∈ Finset.Icc (B + 1) Y, if k ≤ Y / a then (chi4 k : ℝ) else 0|
        ≤ ∑ a ∈ Finset.Icc 1 Q,
            |∑ k ∈ Finset.Icc (B + 1) Y, if k ≤ Y / a then (chi4 k : ℝ) else 0| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _a ∈ Finset.Icc 1 Q, (1 : ℝ) := Finset.sum_le_sum hinner
      _ = (Q : ℝ) := by simp
      _ ≤ (B : ℝ) := by exact_mod_cast hQ_le
  have hB_sqrt : (B : ℝ) ≤ Real.sqrt (Y : ℝ) := by
    refine Real.le_sqrt_of_sq_le ?_
    have hle : B ^ 2 ≤ Y := by rw [sq]; exact Nat.sqrt_le Y
    exact_mod_cast hle
  have htri1 := abs_add_le
    ((∑ k ∈ Finset.Icc 1 B, (chi4 k : ℝ) * ((Y / k : ℕ) : ℝ) -
        (Y : ℝ) * ∑ k ∈ Finset.Icc 1 B, (chi4 k : ℝ) / (k : ℝ)) +
      ((Y : ℝ) * ∑ k ∈ Finset.Icc 1 B, (chi4 k : ℝ) / (k : ℝ) - (π / 4) * (Y : ℝ)))
    (∑ k ∈ Finset.Icc (B + 1) Y, (chi4 k : ℝ) * ((Y / k : ℕ) : ℝ))
  have htri2 := abs_add_le
    (∑ k ∈ Finset.Icc 1 B, (chi4 k : ℝ) * ((Y / k : ℕ) : ℝ) -
      (Y : ℝ) * ∑ k ∈ Finset.Icc 1 B, (chi4 k : ℝ) / (k : ℝ))
    ((Y : ℝ) * ∑ k ∈ Finset.Icc 1 B, (chi4 k : ℝ) / (k : ℝ) - (π / 4) * (Y : ℝ))
  have heq_main : (∑ k ∈ Finset.Icc 1 B, (chi4 k : ℝ) * ((Y / k : ℕ) : ℝ) +
      ∑ k ∈ Finset.Icc (B + 1) Y, (chi4 k : ℝ) * ((Y / k : ℕ) : ℝ)) -
    (π / 4) * (Y : ℝ) =
    ((∑ k ∈ Finset.Icc 1 B, (chi4 k : ℝ) * ((Y / k : ℕ) : ℝ) -
      (Y : ℝ) * ∑ k ∈ Finset.Icc 1 B, (chi4 k : ℝ) / (k : ℝ)) +
    ((Y : ℝ) * ∑ k ∈ Finset.Icc 1 B, (chi4 k : ℝ) / (k : ℝ) - (π / 4) * (Y : ℝ))) +
    ∑ k ∈ Finset.Icc (B + 1) Y, (chi4 k : ℝ) * ((Y / k : ℕ) : ℝ) := by ring
  rw [heq_main]
  linarith

end HyperbolaHChi

section SumRho

private noncomputable def muTerm (u : ℕ) : ℝ :=
  if u = 0 then 0 else (μ u : ℝ) / (u : ℝ) ^ 2

private noncomputable def LConst : ℝ :=
  ∑' u : ℕ, muTerm u

private lemma summable_inv_sq : Summable (fun u : ℕ ↦ (1 : ℝ) / (u : ℝ) ^ 2) := by
  exact Real.summable_one_div_nat_pow.mpr (by norm_num)

private lemma summable_muTerm : Summable muTerm := by
  refine Summable.of_norm_bounded summable_inv_sq fun u ↦ ?_
  rw [Real.norm_eq_abs]
  by_cases hu : u = 0
  · subst hu; simp [muTerm]
  · simp only [muTerm, hu, ↓reduceIte, abs_div, abs_pow, Nat.abs_cast]
    have hmu : |(μ u : ℝ)| ≤ 1 := by exact_mod_cast ArithmeticFunction.abs_moebius_le_one
    exact div_le_div_of_nonneg_right hmu (by positivity)

private lemma sum_Ico_inv_sq_le (a b : ℕ) (ha : 2 ≤ a) (hab : a ≤ b) :
    ∑ u ∈ Finset.Ico a b, (1 : ℝ) / (u : ℝ) ^ 2 ≤ 1 / ((a : ℝ) - 1) := by
  have hterm : ∀ u ∈ Finset.Ico a b,
      (1 : ℝ) / (u : ℝ) ^ 2 ≤ 1 / ((u : ℝ) - 1) - 1 / (u : ℝ) := by
    intro u hu
    rw [Finset.mem_Ico] at hu
    have hu2 : (2 : ℝ) ≤ (u : ℝ) := by exact_mod_cast (by omega : 2 ≤ u)
    have hu0 : (u : ℝ) ≠ 0 := by linarith
    have hu1 : (u : ℝ) - 1 ≠ 0 := by linarith
    have hsub : 1 / ((u : ℝ) - 1) - 1 / (u : ℝ) = 1 / ((u : ℝ) * ((u : ℝ) - 1)) := by
      field_simp [hu0, hu1]
      ring
    rw [hsub]
    refine div_le_div_of_nonneg_left zero_le_one (by nlinarith) (by nlinarith)
  have htel : ∑ u ∈ Finset.Ico a b, (1 / ((u : ℝ) - 1) - 1 / (u : ℝ)) =
      1 / ((a : ℝ) - 1) - 1 / ((b : ℝ) - 1) := by
    clear hterm
    induction b, hab using Nat.le_induction with
    | base => simp
    | succ k hk ih =>
      rw [Finset.sum_Ico_succ_top hk, ih]
      push_cast
      ring
  have ha2 : (2 : ℝ) ≤ (a : ℝ) := by exact_mod_cast ha
  have hb2 : (2 : ℝ) ≤ (b : ℝ) := by exact_mod_cast (ha.trans hab)
  have hb_nonneg : 0 ≤ 1 / ((b : ℝ) - 1) := div_nonneg zero_le_one (by linarith)
  calc ∑ u ∈ Finset.Ico a b, (1 : ℝ) / (u : ℝ) ^ 2
      ≤ ∑ u ∈ Finset.Ico a b, (1 / ((u : ℝ) - 1) - 1 / (u : ℝ)) := Finset.sum_le_sum hterm
    _ = 1 / ((a : ℝ) - 1) - 1 / ((b : ℝ) - 1) := htel
    _ ≤ 1 / ((a : ℝ) - 1) := by linarith

private lemma LConst_pos : 0 < LConst := by
  have htend := summable_muTerm.tendsto_sum_tsum_nat
  have hge : ∀ M : ℕ, 4 ≤ M → (1 / 4 : ℝ) ≤ ∑ u ∈ Finset.range M, muTerm u := by
    intro M hM
    have hsplit : Finset.range M = {0, 1, 2} ∪ Finset.Ico 3 M := by
      ext u
      simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton, Finset.mem_Ico,
        Finset.mem_range]
      omega
    have hdisj : Disjoint ({0, 1, 2} : Finset ℕ) (Finset.Ico 3 M) := by
      rw [Finset.disjoint_left]
      intro u hu1 hu2
      simp only [Finset.mem_insert, Finset.mem_singleton] at hu1
      rw [Finset.mem_Ico] at hu2
      omega
    rw [hsplit, Finset.sum_union hdisj]
    have h012 : ∑ u ∈ ({0, 1, 2} : Finset ℕ), muTerm u = 3 / 4 := by
      have h01 : (0 : ℕ) ∉ ({1, 2} : Finset ℕ) := by decide
      have h12 : (1 : ℕ) ∉ ({2} : Finset ℕ) := by decide
      rw [Finset.sum_insert h01, Finset.sum_insert h12, Finset.sum_singleton]
      simp only [muTerm, ↓reduceIte, one_ne_zero, ArithmeticFunction.moebius_apply_one,
        Int.cast_one, Nat.cast_one, one_pow, div_one, OfNat.ofNat_ne_zero,
        ArithmeticFunction.moebius_apply_prime Nat.prime_two, Int.cast_neg, Nat.cast_ofNat]
      norm_num
    have htail : -(1 / 2 : ℝ) ≤ ∑ u ∈ Finset.Ico 3 M, muTerm u := by
      have habs : |∑ u ∈ Finset.Ico 3 M, muTerm u| ≤ 1 / 2 := by
        calc |∑ u ∈ Finset.Ico 3 M, muTerm u|
            ≤ ∑ u ∈ Finset.Ico 3 M, |muTerm u| := Finset.abs_sum_le_sum_abs _ _
          _ ≤ ∑ u ∈ Finset.Ico 3 M, (1 : ℝ) / (u : ℝ) ^ 2 := by
              refine Finset.sum_le_sum fun u hu ↦ ?_
              rw [Finset.mem_Ico] at hu
              have hu0 : u ≠ 0 := by omega
              simp only [muTerm, hu0, ↓reduceIte, abs_div, abs_pow, Nat.abs_cast]
              have hmu : |(μ u : ℝ)| ≤ 1 := by exact_mod_cast ArithmeticFunction.abs_moebius_le_one
              exact div_le_div_of_nonneg_right hmu (by positivity)
          _ ≤ 1 / ((3 : ℝ) - 1) := sum_Ico_inv_sq_le 3 M (by omega) (by omega)
          _ = 1 / 2 := by norm_num
      linarith [(abs_le.mp habs).1]
    linarith
  have hlim : (1 / 4 : ℝ) ≤ LConst :=
    ge_of_tendsto htend (eventually_atTop.mpr ⟨4, hge⟩)
  linarith

private lemma abs_sum_Icc_muTerm_sub_LConst (K : ℕ) (hK : 1 ≤ K) :
    |∑ u ∈ Finset.Icc 1 K, muTerm u - LConst| ≤ 1 / (K : ℝ) := by
  have hrange : ∑ u ∈ Finset.Icc 1 K, muTerm u = ∑ u ∈ Finset.range (K + 1), muTerm u := by
    have h0 : (0 : ℕ) ∉ Finset.Icc 1 K := by simp
    have hunion : Finset.range (K + 1) = insert 0 (Finset.Icc 1 K) := by
      ext u; simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]; omega
    rw [hunion, Finset.sum_insert h0, show muTerm 0 = 0 by simp [muTerm], zero_add]
  rw [hrange]
  have hlim : Tendsto (fun M ↦ |∑ u ∈ Finset.range (K + 1), muTerm u - ∑ u ∈ Finset.range M, muTerm u|)
      atTop (𝓝 |∑ u ∈ Finset.range (K + 1), muTerm u - LConst|) :=
    (tendsto_const_nhds.sub summable_muTerm.tendsto_sum_tsum_nat).abs
  refine le_of_tendsto hlim ?_
  rw [eventually_atTop]
  refine ⟨K + 1, fun M hM ↦ ?_⟩
  have hsub : ∑ u ∈ Finset.range M, muTerm u - ∑ u ∈ Finset.range (K + 1), muTerm u =
      ∑ u ∈ Finset.Ico (K + 1) M, muTerm u := by
    rw [← Finset.sum_range_add_sum_Ico muTerm hM]
    ring
  rw [abs_sub_comm, hsub]
  calc |∑ u ∈ Finset.Ico (K + 1) M, muTerm u|
      ≤ ∑ u ∈ Finset.Ico (K + 1) M, |muTerm u| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ u ∈ Finset.Ico (K + 1) M, (1 : ℝ) / (u : ℝ) ^ 2 := by
        refine Finset.sum_le_sum fun u hu ↦ ?_
        rw [Finset.mem_Ico] at hu
        have hu0 : u ≠ 0 := by omega
        simp only [muTerm, hu0, ↓reduceIte, abs_div, abs_pow, Nat.abs_cast]
        have hmu : |(μ u : ℝ)| ≤ 1 := by exact_mod_cast ArithmeticFunction.abs_moebius_le_one
        exact div_le_div_of_nonneg_right hmu (by positivity)
    _ ≤ 1 / (((K + 1 : ℕ) : ℝ) - 1) := sum_Ico_inv_sq_le (K + 1) M (by omega) hM
    _ = 1 / (K : ℝ) := by push_cast; ring

private noncomputable def R_rho (N : ℕ) : ℝ :=
  ∑ d ∈ Finset.Icc 1 N, (rho d : ℝ)

private lemma R_rho_nonneg (N : ℕ) : 0 ≤ R_rho N :=
  Finset.sum_nonneg fun _ _ ↦ Nat.cast_nonneg _

private lemma R_rho_eq (N : ℕ) :
    R_rho N = ∑ u ∈ Finset.Icc 1 (Nat.sqrt N), (μ u : ℝ) * HChi (N / u ^ 2) := by
  unfold R_rho
  have hinner : ∀ d ∈ Finset.Icc 1 N,
      (rho d : ℝ) = ∑ u ∈ Finset.Icc 1 (Nat.sqrt N),
        if u ^ 2 ∣ d then (μ u : ℝ) * hChi (d / u ^ 2) else 0 := by
    intro d hd
    rw [Finset.mem_Icc] at hd
    rw [rho_eq_sum_mu_hChi hd.1, Finset.sum_filter]
    refine Finset.sum_subset (Finset.Icc_subset_Icc_right (Nat.sqrt_le_sqrt hd.2)) ?_
    intro u hu hnu
    rw [Finset.mem_Icc] at hu hnu
    have hndvd : ¬ u ^ 2 ∣ d := by
      intro hdvd
      have hle : u ^ 2 ≤ d := Nat.le_of_dvd hd.1 hdvd
      have : u ≤ Nat.sqrt d := Nat.le_sqrt.mpr (by simpa [sq] using hle)
      omega
    simp [hndvd]
  rw [Finset.sum_congr rfl hinner, Finset.sum_comm]
  refine Finset.sum_congr rfl fun u hu ↦ ?_
  rw [Finset.mem_Icc] at hu
  have hu0 : 0 < u := by omega
  have hu2 : 0 < u ^ 2 := by positivity
  rw [← Finset.sum_filter]
  unfold HChi
  rw [Finset.mul_sum]
  refine Finset.sum_bij (fun d _ ↦ d / u ^ 2) (fun d hd ↦ ?_) (fun d₁ hd₁ d₂ hd₂ h12 ↦ ?_)
    (fun m hm ↦ ?_) (fun _ _ ↦ rfl)
  · obtain ⟨hd_icc, hud⟩ := Finset.mem_filter.mp hd
    rw [Finset.mem_Icc] at hd_icc ⊢
    exact ⟨Nat.div_pos (Nat.le_of_dvd hd_icc.1 hud) hu2, Nat.div_le_div_right hd_icc.2⟩
  · obtain ⟨_, hud₁⟩ := Finset.mem_filter.mp hd₁
    obtain ⟨_, hud₂⟩ := Finset.mem_filter.mp hd₂
    rw [← Nat.mul_div_cancel' hud₁, ← Nat.mul_div_cancel' hud₂, h12]
  · rw [Finset.mem_Icc] at hm
    refine ⟨u ^ 2 * m, Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨by nlinarith, ?_⟩,
      dvd_mul_right _ _⟩, Nat.mul_div_cancel_left m hu2⟩
    rw [mul_comm]
    exact (Nat.le_div_iff_mul_le hu2).mp hm.2

private lemma R_rho_approx (N : ℕ) (hN : 1 ≤ N) :
    |R_rho N - (π / 4 * LConst) * (N : ℝ)| ≤
      3 * Real.sqrt (N : ℝ) * (1 + Real.log (N : ℝ)) + 5 * Real.sqrt (N : ℝ) := by
  rw [R_rho_eq]
  let K := Nat.sqrt N
  have hK1 : 1 ≤ K := Nat.sqrt_pos.mpr hN
  have hK_le_N : K ≤ N := Nat.sqrt_le_self N
  have hK_sqrt : (K : ℝ) ≤ Real.sqrt (N : ℝ) := by
    refine Real.le_sqrt_of_sq_le ?_
    have hle : K ^ 2 ≤ N := by rw [sq]; exact Nat.sqrt_le N
    exact_mod_cast hle
  have hN_lt_K1 : (N : ℝ) < ((K + 1 : ℕ) : ℝ) ^ 2 := by
    have hlt : N < (K + 1) ^ 2 := by rw [sq]; exact Nat.lt_succ_sqrt N
    exact_mod_cast hlt
  have hsqrt_le_2K : Real.sqrt (N : ℝ) ≤ 2 * (K : ℝ) := by
    have h1 : Real.sqrt (N : ℝ) ≤ (K : ℝ) + 1 := by
      refine Real.sqrt_le_iff.mpr ⟨by positivity, ?_⟩
      push_cast at hN_lt_K1
      exact hN_lt_K1.le
    have hK1_r : (1 : ℝ) ≤ (K : ℝ) := by exact_mod_cast hK1
    linarith
  let T1 := ∑ u ∈ Finset.Icc 1 K,
    (μ u : ℝ) * (HChi (N / u ^ 2) - (π / 4) * ((N / u ^ 2 : ℕ) : ℝ))
  let T2 := ∑ u ∈ Finset.Icc 1 K,
    (μ u : ℝ) * ((π / 4) * ((N / u ^ 2 : ℕ) : ℝ) - (π / 4) * ((N : ℝ) / (u : ℝ) ^ 2))
  let T3 := (π / 4) * (N : ℝ) * ((∑ u ∈ Finset.Icc 1 K, muTerm u) - LConst)
  have hdecomp :
      ∑ u ∈ Finset.Icc 1 K, (μ u : ℝ) * HChi (N / u ^ 2) - (π / 4 * LConst) * (N : ℝ) =
        T1 + T2 + T3 := by
    have hsum_mu : ∑ u ∈ Finset.Icc 1 K, (μ u : ℝ) * ((π / 4) * ((N : ℝ) / (u : ℝ) ^ 2)) =
        (π / 4) * (N : ℝ) * ∑ u ∈ Finset.Icc 1 K, muTerm u := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun u hu ↦ ?_
      rw [Finset.mem_Icc] at hu
      have hu0 : u ≠ 0 := by omega
      simp only [muTerm, hu0, ↓reduceIte]
      ring
    dsimp [T1, T2, T3]
    simp only [mul_sub, Finset.sum_sub_distrib]
    rw [hsum_mu]
    ring
  have hT1 : |T1| ≤ 3 * Real.sqrt (N : ℝ) * (1 + Real.log (N : ℝ)) + 2 * Real.sqrt (N : ℝ) := by
    calc |T1|
        ≤ ∑ u ∈ Finset.Icc 1 K,
            |(μ u : ℝ) * (HChi (N / u ^ 2) - (π / 4) * ((N / u ^ 2 : ℕ) : ℝ))| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ u ∈ Finset.Icc 1 K, (3 * Real.sqrt (N : ℝ) * (u : ℝ)⁻¹ + 2) := by
          refine Finset.sum_le_sum fun u hu ↦ ?_
          rw [Finset.mem_Icc] at hu
          have hu_pos : (0 : ℝ) < u := by exact_mod_cast (by omega : 0 < u)
          rw [abs_mul]
          have hmu : |(μ u : ℝ)| ≤ 1 := by exact_mod_cast ArithmeticFunction.abs_moebius_le_one
          have hhc := HChi_approx (N / u ^ 2)
          have hsq_le : Real.sqrt ((N / u ^ 2 : ℕ) : ℝ) ≤ Real.sqrt (N : ℝ) * (u : ℝ)⁻¹ := by
            have hle : ((N / u ^ 2 : ℕ) : ℝ) ≤ (N : ℝ) / (u : ℝ) ^ 2 := by
              rw [le_div_iff₀ (by positivity)]
              exact_mod_cast Nat.div_mul_le_self N (u ^ 2)
            calc Real.sqrt ((N / u ^ 2 : ℕ) : ℝ)
                ≤ Real.sqrt ((N : ℝ) / (u : ℝ) ^ 2) := Real.sqrt_le_sqrt hle
              _ = Real.sqrt (N : ℝ) / Real.sqrt ((u : ℝ) ^ 2) := Real.sqrt_div (by positivity) _
              _ = Real.sqrt (N : ℝ) / (u : ℝ) := by rw [Real.sqrt_sq hu_pos.le]
              _ = Real.sqrt (N : ℝ) * (u : ℝ)⁻¹ := div_eq_mul_inv _ _
          calc |(μ u : ℝ)| * |HChi (N / u ^ 2) - (π / 4) * ((N / u ^ 2 : ℕ) : ℝ)|
              ≤ 1 * (3 * Real.sqrt ((N / u ^ 2 : ℕ) : ℝ) + 2) :=
                mul_le_mul hmu hhc (abs_nonneg _) zero_le_one
            _ ≤ 3 * Real.sqrt (N : ℝ) * (u : ℝ)⁻¹ + 2 := by linarith
      _ = 3 * Real.sqrt (N : ℝ) * ∑ u ∈ Finset.Icc 1 K, (u : ℝ)⁻¹ + 2 * (K : ℝ) := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Nat.card_Icc,
            show K + 1 - 1 = K by omega, nsmul_eq_mul]
          ring
      _ = 3 * Real.sqrt (N : ℝ) * (harmonic K : ℝ) + 2 * (K : ℝ) := by
          rw [harmonic_eq_sum_Icc]
          push_cast
          rfl
      _ ≤ 3 * Real.sqrt (N : ℝ) * (1 + Real.log (N : ℝ)) + 2 * Real.sqrt (N : ℝ) := by
          have hharm : (harmonic K : ℝ) ≤ 1 + Real.log (N : ℝ) := by
            have h1 := harmonic_le_one_add_log K
            have h2 : Real.log (K : ℝ) ≤ Real.log (N : ℝ) :=
              Real.log_le_log (by exact_mod_cast hK1) (by exact_mod_cast hK_le_N)
            linarith
          have hsq0 : 0 ≤ 3 * Real.sqrt (N : ℝ) := by positivity
          nlinarith
  have hT2 : |T2| ≤ Real.sqrt (N : ℝ) := by
    calc |T2|
        ≤ ∑ u ∈ Finset.Icc 1 K,
            |(μ u : ℝ) * ((π / 4) * ((N / u ^ 2 : ℕ) : ℝ) - (π / 4) * ((N : ℝ) / (u : ℝ) ^ 2))| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _u ∈ Finset.Icc 1 K, (1 : ℝ) := by
          refine Finset.sum_le_sum fun u hu ↦ ?_
          rw [Finset.mem_Icc] at hu
          have hu0 : 0 < u := by omega
          have hu0_r : (0 : ℝ) < u := by exact_mod_cast hu0
          have hu2 : 0 < u ^ 2 := by positivity
          have hu2_pos : (0 : ℝ) < (u : ℝ) ^ 2 := by positivity
          rw [abs_mul, ← mul_sub, abs_mul, abs_of_nonneg (by positivity : 0 ≤ π / 4)]
          have hmu : |(μ u : ℝ)| ≤ 1 := by exact_mod_cast ArithmeticFunction.abs_moebius_le_one
          have hfl1 : ((N / u ^ 2 : ℕ) : ℝ) ≤ (N : ℝ) / (u : ℝ) ^ 2 := by
            rw [le_div_iff₀ hu2_pos]
            exact_mod_cast Nat.div_mul_le_self N (u ^ 2)
          have hfl2 : (N : ℝ) / (u : ℝ) ^ 2 - 1 < ((N / u ^ 2 : ℕ) : ℝ) := by
            rw [sub_lt_iff_lt_add, div_lt_iff₀ hu2_pos]
            have hlt : N < (N / u ^ 2 + 1) * u ^ 2 := by
              rw [add_mul, one_mul]
              exact Nat.lt_div_mul_add hu2 (a := N)
            have hcast : (N : ℝ) < (((N / u ^ 2 + 1) * u ^ 2 : ℕ) : ℝ) := by exact_mod_cast hlt
            push_cast at hcast
            linarith
          have habs : |((N / u ^ 2 : ℕ) : ℝ) - (N : ℝ) / (u : ℝ) ^ 2| ≤ 1 := by
            rw [abs_sub_le_iff]; constructor <;> linarith
          have hpi : π / 4 ≤ 1 := by linarith [pi_lt_four]
          calc |(μ u : ℝ)| * (π / 4 * |((N / u ^ 2 : ℕ) : ℝ) - (N : ℝ) / (u : ℝ) ^ 2|)
              ≤ 1 * (1 * 1) := mul_le_mul hmu (mul_le_mul hpi habs (abs_nonneg _) zero_le_one)
                (by positivity) zero_le_one
            _ = 1 := by norm_num
      _ = (K : ℝ) := by simp
      _ ≤ Real.sqrt (N : ℝ) := hK_sqrt
  have hT3 : |T3| ≤ 2 * Real.sqrt (N : ℝ) := by
    dsimp [T3]
    rw [abs_mul, abs_mul, abs_of_nonneg (by positivity), abs_of_nonneg (by positivity)]
    have hpi : π / 4 ≤ 1 := by linarith [pi_lt_four]
    have htail := abs_sum_Icc_muTerm_sub_LConst K hK1
    have hsq_pos : 0 < Real.sqrt (N : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast hN)
    have hK_inv : 1 / (K : ℝ) ≤ 2 / Real.sqrt (N : ℝ) := by
      rw [div_le_div_iff₀ (by positivity) hsq_pos]
      linarith
    have hdiv_sq : (N : ℝ) / Real.sqrt (N : ℝ) = Real.sqrt (N : ℝ) := by
      rw [div_eq_iff hsq_pos.ne']
      exact (Real.mul_self_sqrt (by positivity)).symm
    calc π / 4 * (N : ℝ) * |∑ u ∈ Finset.Icc 1 K, muTerm u - LConst|
        ≤ 1 * (N : ℝ) * (2 / Real.sqrt (N : ℝ)) :=
          mul_le_mul (mul_le_mul_of_nonneg_right hpi (by positivity)) (htail.trans hK_inv)
            (abs_nonneg _) (by positivity)
      _ = 2 * ((N : ℝ) / Real.sqrt (N : ℝ)) := by ring
      _ = 2 * Real.sqrt (N : ℝ) := by rw [hdiv_sq]
  rw [hdecomp]
  have htri1 := abs_add_le (T1 + T2) T3
  have htri2 := abs_add_le T1 T2
  linarith

private lemma tendsto_R_rho_div :
    Tendsto (fun N : ℕ ↦ R_rho N / (N : ℝ)) atTop (𝓝 (π / 4 * LConst)) := by
  have ho : Real.log =o[atTop] (fun x : ℝ ↦ x ^ (1 / 2 : ℝ)) :=
    isLittleO_log_rpow_atTop (by norm_num)
  have htend_log : Tendsto (fun N : ℕ ↦ Real.log (N : ℝ) / Real.sqrt (N : ℝ)) atTop (𝓝 0) := by
    have h0 := ho.tendsto_div_nhds_zero.comp tendsto_natCast_atTop_atTop
    refine h0.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with N _
    simp only [Function.comp_def, Real.sqrt_eq_rpow]
  have htend_inv : Tendsto (fun N : ℕ ↦ (1 : ℝ) / Real.sqrt (N : ℝ)) atTop (𝓝 0) := by
    have h0 := (tendsto_const_nhds (x := (1 : ℝ))).div_atTop
      (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)
    simpa [Function.comp_def] using h0
  have hbound : Tendsto (fun N : ℕ ↦
      3 * (Real.log (N : ℝ) / Real.sqrt (N : ℝ)) + 8 * (1 / Real.sqrt (N : ℝ))) atTop (𝓝 0) := by
    simpa using (htend_log.const_mul 3).add (htend_inv.const_mul 8)
  refine tendsto_iff_norm_sub_tendsto_zero.mpr ?_
  refine squeeze_zero' (Eventually.of_forall fun _ ↦ norm_nonneg _) ?_ hbound
  filter_upwards [eventually_ge_atTop 1] with N hN
  rw [Real.norm_eq_abs]
  have hN_pos : (0 : ℝ) < N := by exact_mod_cast hN
  have hsq_pos : 0 < Real.sqrt (N : ℝ) := Real.sqrt_pos.mpr hN_pos
  have hdiv : R_rho N / (N : ℝ) - π / 4 * LConst =
      (R_rho N - (π / 4 * LConst) * (N : ℝ)) / (N : ℝ) := by
    field_simp
  rw [hdiv, abs_div, abs_of_pos hN_pos]
  have hr := R_rho_approx N hN
  have hsq_div : Real.sqrt (N : ℝ) / (N : ℝ) = 1 / Real.sqrt (N : ℝ) := by
    rw [div_eq_div_iff hN_pos.ne' hsq_pos.ne', one_mul, Real.mul_self_sqrt hN_pos.le]
  calc |R_rho N - π / 4 * LConst * (N : ℝ)| / (N : ℝ)
      ≤ (3 * Real.sqrt (N : ℝ) * (1 + Real.log (N : ℝ)) + 5 * Real.sqrt (N : ℝ)) / (N : ℝ) :=
        div_le_div_of_nonneg_right hr hN_pos.le
    _ = 3 * (Real.log (N : ℝ) * (Real.sqrt (N : ℝ) / (N : ℝ))) +
          8 * (Real.sqrt (N : ℝ) / (N : ℝ)) := by ring
    _ = 3 * (Real.log (N : ℝ) / Real.sqrt (N : ℝ)) + 8 * (1 / Real.sqrt (N : ℝ)) := by
        rw [hsq_div]
        ring

end SumRho

section AbelAndFinal

private noncomputable def S_rho (N : ℕ) : ℝ :=
  ∑ d ∈ Finset.Icc 1 N, (rho d : ℝ) / (d : ℝ)

private lemma S_rho_abel (N : ℕ) (hN : 1 ≤ N) :
    S_rho N = R_rho N / (N : ℝ) +
      ∑ d ∈ Finset.Icc 1 (N - 1), (R_rho d / (d : ℝ)) * (1 / ((d + 1 : ℕ) : ℝ)) := by
  induction N, hN using Nat.le_induction with
  | base =>
    simp [S_rho, R_rho]
  | succ k hk ih =>
    have hsplit : Finset.Icc 1 (k + 1) = insert (k + 1) (Finset.Icc 1 k) := by
      ext d; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
    have hnot : k + 1 ∉ Finset.Icc 1 k := by simp
    have hS_succ : S_rho (k + 1) = S_rho k + (rho (k + 1) : ℝ) / ((k + 1 : ℕ) : ℝ) := by
      unfold S_rho
      rw [hsplit, Finset.sum_insert hnot, add_comm]
    have hR_succ : R_rho (k + 1) = R_rho k + (rho (k + 1) : ℝ) := by
      unfold R_rho
      rw [hsplit, Finset.sum_insert hnot, add_comm]
    have hk_pos : (0 : ℝ) < k := by exact_mod_cast hk
    have hk1_pos : (0 : ℝ) < ((k + 1 : ℕ) : ℝ) := by positivity
    have hsplit2 : Finset.Icc 1 k = insert k (Finset.Icc 1 (k - 1)) := by
      ext d; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
    have hnot2 : k ∉ Finset.Icc 1 (k - 1) := by simp; omega
    simp only [Nat.add_sub_cancel]
    rw [hS_succ, ih, hsplit2, Finset.sum_insert hnot2, hR_succ]
    have hdiff : R_rho k / (k : ℝ) - R_rho k / ((k + 1 : ℕ) : ℝ) =
        (R_rho k / (k : ℝ)) * (1 / ((k + 1 : ℕ) : ℝ)) := by
      push_cast
      field_simp
      ring
    have hsplit_div : (R_rho k + (rho (k + 1) : ℝ)) / ((k + 1 : ℕ) : ℝ) =
        R_rho k / ((k + 1 : ℕ) : ℝ) + (rho (k + 1) : ℝ) / ((k + 1 : ℕ) : ℝ) := add_div _ _ _
    linarith

private lemma tendsto_harmonic_div_log :
    Tendsto (fun N : ℕ ↦ (harmonic N : ℝ) / Real.log (N : ℝ)) atTop (𝓝 1) := by
  have h_inv_log : Tendsto (fun N : ℕ ↦ 1 / Real.log (N : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  have h_up : Tendsto (fun N : ℕ ↦ 1 + 1 / Real.log (N : ℝ)) atTop (𝓝 1) := by
    simpa using tendsto_const_nhds.add h_inv_log
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h_up ?_ ?_
  · filter_upwards [eventually_ge_atTop 2] with N hN
    have hlog_pos : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < N))
    have hlog_le : Real.log (N : ℝ) ≤ Real.log ((N + 1 : ℕ) : ℝ) :=
      Real.log_le_log (by exact_mod_cast (by omega : 0 < N)) (by exact_mod_cast (by omega : N ≤ N + 1))
    rw [one_le_div hlog_pos]
    exact hlog_le.trans (log_add_one_le_harmonic N)
  · filter_upwards [eventually_ge_atTop 2] with N hN
    have hlog_pos : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < N))
    rw [div_le_iff₀ hlog_pos]
    have := harmonic_le_one_add_log N
    calc (harmonic N : ℝ) ≤ 1 + Real.log (N : ℝ) := this
      _ = (1 + 1 / Real.log (N : ℝ)) * Real.log (N : ℝ) := by field_simp; ring

private lemma sum_Icc_inv_succ_eq_harmonic_sub (N : ℕ) (hN : 1 ≤ N) :
    ∑ d ∈ Finset.Icc 1 (N - 1), (1 / ((d + 1 : ℕ) : ℝ)) = (harmonic N : ℝ) - 1 := by
  induction N, hN using Nat.le_induction with
  | base => simp
  | succ k hk ih =>
    have hsplit : Finset.Icc 1 k = insert k (Finset.Icc 1 (k - 1)) := by
      ext d; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
    have hnot : k ∉ Finset.Icc 1 (k - 1) := by simp; omega
    have hharm_succ : (harmonic (k + 1) : ℝ) = (harmonic k : ℝ) + 1 / ((k + 1 : ℕ) : ℝ) := by
      simp only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
      have hsplit2 : Finset.Icc 1 (k + 1) = insert (k + 1) (Finset.Icc 1 k) := by
        ext d; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
      have hnot2 : k + 1 ∉ Finset.Icc 1 k := by simp
      rw [hsplit2, Finset.sum_insert hnot2, one_div]
      ring
    simp only [Nat.add_sub_cancel]
    rw [hsplit, Finset.sum_insert hnot, ih, hharm_succ]
    ring

private lemma tendsto_S_rho_div_log :
    Tendsto (fun N : ℕ ↦ S_rho N / Real.log (N : ℝ)) atTop (𝓝 (π / 4 * LConst)) := by
  let c₁ := π / 4 * LConst
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨D₀, hD₀⟩ := Metric.tendsto_atTop.mp tendsto_R_rho_div (ε / 8) (by positivity)
  let D := max D₀ 2
  have hD2 : 2 ≤ D := le_max_right _ _
  let C_head : ℝ := ∑ d ∈ Finset.Icc 1 (D - 1),
    |R_rho d / (d : ℝ) - c₁| * (1 / ((d + 1 : ℕ) : ℝ))
  have hev : ∀ᶠ N : ℕ in atTop,
      2 ≤ N ∧
      D + 1 ≤ N ∧
      |(R_rho N / (N : ℝ)) / Real.log (N : ℝ)| < ε / 5 ∧
      |c₁ * ((harmonic N : ℝ) / Real.log (N : ℝ) - 1)| < ε / 5 ∧
      |c₁ / Real.log (N : ℝ)| < ε / 5 ∧
      C_head / Real.log (N : ℝ) < ε / 5 ∧
      (harmonic N : ℝ) / Real.log (N : ℝ) ≤ 8 / 5 := by
    have h1 : ∀ᶠ N : ℕ in atTop, 2 ≤ N := eventually_ge_atTop 2
    have h2 : ∀ᶠ N : ℕ in atTop, D + 1 ≤ N := eventually_ge_atTop (D + 1)
    have h3 : ∀ᶠ N : ℕ in atTop, |(R_rho N / (N : ℝ)) / Real.log (N : ℝ)| < ε / 5 := by
      have ht := (tendsto_R_rho_div.div_atTop
        (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)).abs
      rw [abs_zero] at ht
      exact ht.eventually (eventually_lt_nhds (by positivity))
    have h4 : ∀ᶠ N : ℕ in atTop, |c₁ * ((harmonic N : ℝ) / Real.log (N : ℝ) - 1)| < ε / 5 := by
      have ht : Tendsto (fun N : ℕ ↦ |c₁ * ((harmonic N : ℝ) / Real.log (N : ℝ) - 1)|) atTop (𝓝 0) := by
        have hsub : Tendsto (fun N : ℕ ↦ (harmonic N : ℝ) / Real.log (N : ℝ) - 1) atTop (𝓝 0) := by
          simpa using tendsto_harmonic_div_log.sub (tendsto_const_nhds (x := (1 : ℝ)))
        simpa using (hsub.const_mul c₁).abs
      exact ht.eventually (eventually_lt_nhds (by positivity))
    have h5 : ∀ᶠ N : ℕ in atTop, |c₁ / Real.log (N : ℝ)| < ε / 5 := by
      have ht := ((tendsto_const_nhds (x := c₁)).div_atTop
        (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)).abs
      rw [abs_zero] at ht
      exact ht.eventually (eventually_lt_nhds (by positivity))
    have h6 : ∀ᶠ N : ℕ in atTop, C_head / Real.log (N : ℝ) < ε / 5 := by
      have ht := (tendsto_const_nhds (x := C_head)).div_atTop
        (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
      exact ht.eventually (eventually_lt_nhds (by positivity))
    have h7 : ∀ᶠ N : ℕ in atTop, (harmonic N : ℝ) / Real.log (N : ℝ) ≤ 8 / 5 :=
      tendsto_harmonic_div_log.eventually (eventually_le_nhds (by norm_num))
    exact h1.and (h2.and (h3.and (h4.and (h5.and (h6.and h7)))))
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp hev
  refine ⟨N₀, fun N hN ↦ ?_⟩
  obtain ⟨hN2, hND, h3, h4, h5, h6, h7⟩ := hN₀ N hN
  have hlog_pos : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < N))
  have hharm_sum := sum_Icc_inv_succ_eq_harmonic_sub N (by omega)
  have htail_bound :
      |∑ d ∈ Finset.Icc 1 (N - 1), (R_rho d / (d : ℝ) - c₁) * (1 / ((d + 1 : ℕ) : ℝ))| ≤
        C_head + (ε / 8) * (harmonic N : ℝ) := by
    have hsplit : Finset.Icc 1 (N - 1) = Finset.Icc 1 (D - 1) ∪ Finset.Icc D (N - 1) := by
      ext d; simp only [Finset.mem_union, Finset.mem_Icc]; omega
    have hdisj : Disjoint (Finset.Icc 1 (D - 1)) (Finset.Icc D (N - 1)) := by
      rw [Finset.disjoint_left]
      intro d h1 h2
      rw [Finset.mem_Icc] at h1 h2
      omega
    rw [hsplit, Finset.sum_union hdisj]
    have hhead_le : |∑ d ∈ Finset.Icc 1 (D - 1), (R_rho d / (d : ℝ) - c₁) * (1 / ((d + 1 : ℕ) : ℝ))| ≤
        C_head := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      refine Finset.sum_le_sum fun d _ ↦ ?_
      rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 1 / ((d + 1 : ℕ) : ℝ))]
    have htail_le : |∑ d ∈ Finset.Icc D (N - 1), (R_rho d / (d : ℝ) - c₁) * (1 / ((d + 1 : ℕ) : ℝ))| ≤
        (ε / 8) * (harmonic N : ℝ) := by
      calc |∑ d ∈ Finset.Icc D (N - 1), (R_rho d / (d : ℝ) - c₁) * (1 / ((d + 1 : ℕ) : ℝ))|
          ≤ ∑ d ∈ Finset.Icc D (N - 1), |(R_rho d / (d : ℝ) - c₁) * (1 / ((d + 1 : ℕ) : ℝ))| :=
            Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ d ∈ Finset.Icc D (N - 1), (ε / 8) * (1 / ((d + 1 : ℕ) : ℝ)) := by
            refine Finset.sum_le_sum fun d hd ↦ ?_
            rw [Finset.mem_Icc] at hd
            rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 1 / ((d + 1 : ℕ) : ℝ))]
            have hd0 : |R_rho d / (d : ℝ) - c₁| ≤ ε / 8 := by
              rw [← Real.dist_eq]
              exact (hD₀ d ((le_max_left D₀ 2).trans hd.1)).le
            exact mul_le_mul_of_nonneg_right hd0 (by positivity)
        _ = (ε / 8) * ∑ d ∈ Finset.Icc D (N - 1), (1 / ((d + 1 : ℕ) : ℝ)) :=
            (Finset.mul_sum _ _ _).symm
        _ ≤ (ε / 8) * ∑ d ∈ Finset.Icc 1 (N - 1), (1 / ((d + 1 : ℕ) : ℝ)) := by
            refine mul_le_mul_of_nonneg_left ?_ (by positivity)
            exact Finset.sum_le_sum_of_subset_of_nonneg
              (Finset.Icc_subset_Icc (by omega) le_rfl) fun _ _ _ ↦ by positivity
        _ = (ε / 8) * ((harmonic N : ℝ) - 1) := by rw [hharm_sum]
        _ ≤ (ε / 8) * (harmonic N : ℝ) := by
            refine mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    exact (abs_add_le _ _).trans (add_le_add hhead_le htail_le)
  have hS_decomp : S_rho N / Real.log (N : ℝ) - c₁ =
      (R_rho N / (N : ℝ)) / Real.log (N : ℝ) +
      (∑ d ∈ Finset.Icc 1 (N - 1), (R_rho d / (d : ℝ) - c₁) * (1 / ((d + 1 : ℕ) : ℝ))) /
        Real.log (N : ℝ) +
      c₁ * ((harmonic N : ℝ) / Real.log (N : ℝ) - 1) - c₁ / Real.log (N : ℝ) := by
    rw [S_rho_abel N (by omega)]
    have hsplit_s : ∑ d ∈ Finset.Icc 1 (N - 1), (R_rho d / (d : ℝ)) * (1 / ((d + 1 : ℕ) : ℝ)) =
        ∑ d ∈ Finset.Icc 1 (N - 1), (R_rho d / (d : ℝ) - c₁) * (1 / ((d + 1 : ℕ) : ℝ)) +
          c₁ * ((harmonic N : ℝ) - 1) := by
      rw [← hharm_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun d _ ↦ by ring
    rw [hsplit_s]
    field_simp
    ring
  rw [Real.dist_eq, hS_decomp]
  have hsum_div :
      |(∑ d ∈ Finset.Icc 1 (N - 1), (R_rho d / (d : ℝ) - c₁) * (1 / ((d + 1 : ℕ) : ℝ))) /
          Real.log (N : ℝ)| <
        ε / 5 + ε / 5 := by
    rw [abs_div, abs_of_pos hlog_pos]
    have hmul : (ε / 8) * ((harmonic N : ℝ) / Real.log (N : ℝ)) ≤ (ε / 8) * (8 / 5) :=
      mul_le_mul_of_nonneg_left h7 (by positivity)
    calc |∑ d ∈ Finset.Icc 1 (N - 1), (R_rho d / (d : ℝ) - c₁) * (1 / ((d + 1 : ℕ) : ℝ))| /
          Real.log (N : ℝ)
        ≤ (C_head + (ε / 8) * (harmonic N : ℝ)) / Real.log (N : ℝ) :=
          div_le_div_of_nonneg_right htail_bound hlog_pos.le
      _ = C_head / Real.log (N : ℝ) + (ε / 8) * ((harmonic N : ℝ) / Real.log (N : ℝ)) := by ring
      _ < ε / 5 + (ε / 8) * (8 / 5) := by linarith
      _ = ε / 5 + ε / 5 := by ring
  have htri1 := abs_sub ((R_rho N / (N : ℝ)) / Real.log (N : ℝ) +
    (∑ d ∈ Finset.Icc 1 (N - 1), (R_rho d / (d : ℝ) - c₁) * (1 / ((d + 1 : ℕ) : ℝ))) /
      Real.log (N : ℝ) +
    c₁ * ((harmonic N : ℝ) / Real.log (N : ℝ) - 1)) (c₁ / Real.log (N : ℝ))
  have htri2 := abs_add_le ((R_rho N / (N : ℝ)) / Real.log (N : ℝ) +
    (∑ d ∈ Finset.Icc 1 (N - 1), (R_rho d / (d : ℝ) - c₁) * (1 / ((d + 1 : ℕ) : ℝ))) /
      Real.log (N : ℝ))
    (c₁ * ((harmonic N : ℝ) / Real.log (N : ℝ) - 1))
  have htri3 := abs_add_le ((R_rho N / (N : ℝ)) / Real.log (N : ℝ))
    ((∑ d ∈ Finset.Icc 1 (N - 1), (R_rho d / (d : ℝ) - c₁) * (1 / ((d + 1 : ℕ) : ℝ))) /
      Real.log (N : ℝ))
  linarith

private lemma div_symm_n2_plus_1 (n : ℕ) (hn : 1 ≤ n) :
    (σ 0 (n ^ 2 + 1) : ℝ) = 2 * (((Finset.Icc 1 n).filter (fun d ↦ d ∣ n ^ 2 + 1)).card : ℝ) := by
  rw [ArithmeticFunction.sigma_zero_apply]
  let S := (n ^ 2 + 1).divisors
  let S₁ := S.filter (· ≤ n)
  let S₂ := S.filter (n < ·)
  have hpart : S = S₁ ∪ S₂ := by
    ext d
    simp only [S₁, S₂, Finset.mem_union, Finset.mem_filter]
    by_cases hdS : d ∈ S <;> simp [hdS]
    omega
  have hdisj : Disjoint S₁ S₂ := by
    rw [Finset.disjoint_left]
    intro d h1 h2
    simp only [S₁, S₂, Finset.mem_filter] at h1 h2
    omega
  have hbij : S₁.card = S₂.card := by
    refine Finset.card_bij (fun d _ ↦ (n ^ 2 + 1) / d) (fun d hd ↦ ?_) (fun d₁ hd₁ d₂ hd₂ h12 ↦ ?_)
      (fun d' hd' ↦ ?_)
    · simp only [S₁, S, Finset.mem_filter, Nat.mem_divisors] at hd
      obtain ⟨⟨hd_dvd, hm0⟩, hdn⟩ := hd
      have hd_pos : 0 < d := Nat.pos_of_dvd_of_pos hd_dvd (by positivity)
      have hdiv_dvd : (n ^ 2 + 1) / d ∣ n ^ 2 + 1 := Nat.div_dvd_of_dvd hd_dvd
      refine Finset.mem_filter.mpr ⟨Nat.mem_divisors.mpr ⟨hdiv_dvd, hm0⟩, ?_⟩
      by_contra! hle
      have hmul : d * ((n ^ 2 + 1) / d) ≤ n * n := Nat.mul_le_mul hdn hle
      rw [Nat.mul_div_cancel' hd_dvd] at hmul
      nlinarith
    · simp only [S₁, S, Finset.mem_filter, Nat.mem_divisors] at hd₁ hd₂
      have hm0 : n ^ 2 + 1 ≠ 0 := by positivity
      have hdiv1 := Nat.div_div_self hd₁.1.1 hm0
      have hdiv2 := Nat.div_div_self hd₂.1.1 hm0
      rw [← hdiv1, ← hdiv2, h12]
    · simp only [S₂, S, Finset.mem_filter, Nat.mem_divisors] at hd'
      obtain ⟨⟨hd'_dvd, hm0⟩, hnd'⟩ := hd'
      refine ⟨(n ^ 2 + 1) / d', Finset.mem_filter.mpr ⟨Nat.mem_divisors.mpr
        ⟨Nat.div_dvd_of_dvd hd'_dvd, hm0⟩, ?_⟩, Nat.div_div_self hd'_dvd hm0⟩
      by_contra! hgt
      have hmul : (n + 1) * (n + 1) ≤ d' * ((n ^ 2 + 1) / d') := Nat.mul_le_mul hnd' hgt
      rw [Nat.mul_div_cancel' hd'_dvd] at hmul
      nlinarith
  have hS1 : S₁ = (Finset.Icc 1 n).filter (fun d ↦ d ∣ n ^ 2 + 1) := by
    ext d
    simp only [S₁, S, Finset.mem_filter, Nat.mem_divisors, Finset.mem_Icc]
    constructor
    · rintro ⟨⟨hd_dvd, _⟩, hdn⟩
      exact ⟨⟨Nat.pos_of_dvd_of_pos hd_dvd (by positivity), hdn⟩, hd_dvd⟩
    · rintro ⟨⟨_, hdn⟩, hd_dvd⟩
      exact ⟨⟨hd_dvd, by positivity⟩, hdn⟩
  have hcard : S.card = 2 * S₁.card := by
    rw [hpart, Finset.card_union_of_disjoint hdisj, ← hbij, two_mul]
  rw [hcard, hS1]
  push_cast
  rfl

private lemma block_count_eq_rho (k d : ℕ) (hd : 1 ≤ d) :
    ((Finset.Ico k (k + d)).filter (fun n ↦ d ∣ n ^ 2 + 1)).card = rho d := by
  have hd0 : d ≠ 0 := by omega
  have : NeZero d := ⟨hd0⟩
  rw [rho_pos_eq]
  refine Finset.card_bij (fun n _ ↦ (n : ZMod d)) (fun n hn ↦ ?_)
    (fun n₁ hn₁ n₂ hn₂ h12 ↦ ?_) (fun a ha ↦ ?_)
  · obtain ⟨_, hdn⟩ := Finset.mem_filter.mp hn
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    have hz := (ZMod.natCast_eq_zero_iff (n ^ 2 + 1) d).mpr hdn
    push_cast at hz
    exact hz
  · rw [Finset.mem_filter, Finset.mem_Ico] at hn₁ hn₂
    wlog hle : n₁ ≤ n₂ generalizing n₁ n₂
    · exact (this n₂ hn₂ n₁ hn₁ h12.symm (by omega)).symm
    have hdiff_z : ((n₂ - n₁ : ℕ) : ZMod d) = 0 := by
      rw [Nat.cast_sub hle, h12, sub_self]
    have hdvd := (ZMod.natCast_eq_zero_iff (n₂ - n₁) d).mp hdiff_z
    have hlt : n₂ - n₁ < d := by omega
    have h0 : n₂ - n₁ = 0 := Nat.eq_zero_of_dvd_of_lt hdvd hlt
    omega
  · have ha0 : a ^ 2 + 1 = 0 := (Finset.mem_filter.mp ha).2
    let r := (a - (k : ZMod d)).val
    have hr : r < d := ZMod.val_lt _
    refine ⟨k + r, Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr ⟨by omega, by omega⟩, ?_⟩, ?_⟩
    · rw [← ZMod.natCast_eq_zero_iff]
      push_cast
      simp only [r, ZMod.natCast_zmod_val, add_sub_cancel]
      exact ha0
    · push_cast
      simp only [r, ZMod.natCast_zmod_val, add_sub_cancel]

private lemma interval_count_approx (d N : ℕ) (hd : 1 ≤ d) :
    |(((Finset.Icc d N).filter (fun n ↦ d ∣ n ^ 2 + 1)).card : ℝ) -
      (N : ℝ) / (d : ℝ) * (rho d : ℝ)| ≤ 2 * (rho d : ℝ) := by
  by_cases hdN : N < d
  · have hmt : (Finset.Icc d N).filter (fun n ↦ d ∣ n ^ 2 + 1) = ∅ := by
      rw [Finset.Icc_eq_empty (by omega), Finset.filter_empty]
    rw [hmt, Finset.card_empty, Nat.cast_zero, zero_sub, abs_neg,
      abs_of_nonneg (by positivity)]
    have hNd : (N : ℝ) / (d : ℝ) ≤ 1 := (div_le_one (by exact_mod_cast hd)).mpr (by exact_mod_cast hdN.le)
    nlinarith [show (0 : ℝ) ≤ rho d by positivity]
  have hdN' : d ≤ N := not_lt.mp hdN
  let q := (N + 1 - d) / d
  let blocks := (Finset.range q).biUnion (fun j ↦ Finset.Ico (d + j * d) (d + (j + 1) * d))
  let rem := Finset.Ico (d + q * d) (N + 1)
  have hq_mul : d + q * d ≤ N + 1 := by
    have hdiv := Nat.div_mul_le_self (N + 1 - d) d
    change q * d ≤ N + 1 - d at hdiv
    omega
  have hN_lt_q1 : N + 1 < d + (q + 1) * d := by
    have hlt := Nat.lt_div_mul_add (by omega : 0 < d) (a := N + 1 - d)
    change N + 1 - d < q * d + d at hlt
    rw [add_mul, one_mul]
    omega
  have hpart : Finset.Icc d N = blocks ∪ rem := by
    ext n
    simp only [Finset.mem_Icc, Finset.mem_union, blocks, Finset.mem_biUnion, Finset.mem_range,
      Finset.mem_Ico, rem]
    constructor
    · rintro ⟨hdn, hnN⟩
      by_cases hn_rem : d + q * d ≤ n
      · right; omega
      · left
        let j := (n - d) / d
        refine ⟨j, ?_, ?_, ?_⟩
        · have h1 : n - d < q * d := by omega
          exact (Nat.div_lt_iff_lt_mul hd).mpr h1
        · have hdiv := Nat.div_mul_le_self (n - d) d
          change j * d ≤ n - d at hdiv
          omega
        · have hlt := Nat.lt_div_mul_add hd (a := n - d)
          change n - d < j * d + d at hlt
          rw [add_mul, one_mul]
          omega
    · rintro (⟨j, hjq, h1, h2⟩ | ⟨h1, h2⟩)
      · have hle : d + (j + 1) * d ≤ d + q * d := by nlinarith
        omega
      · omega
  have hdisj_rem : Disjoint blocks rem := by
    rw [Finset.disjoint_left]
    intro n h1 h2
    simp only [blocks, Finset.mem_biUnion, Finset.mem_range, Finset.mem_Ico] at h1
    simp only [rem, Finset.mem_Ico] at h2
    obtain ⟨j, hjq, _, hjn⟩ := h1
    have hle : d + (j + 1) * d ≤ d + q * d := by nlinarith
    omega
  have hpair : ((Finset.range q : Set ℕ).PairwiseDisjoint
      (fun j ↦ Finset.Ico (d + j * d) (d + (j + 1) * d))) := by
    intro i _ j _ hij
    rw [Function.onFun, Finset.disjoint_left]
    intro n hi hj
    rw [Finset.mem_Ico] at hi hj
    rcases lt_or_gt_of_ne hij with hlt | hgt
    · have : d + (i + 1) * d ≤ d + j * d := by nlinarith
      omega
    · have : d + (j + 1) * d ≤ d + i * d := by nlinarith
      omega
  let P : ℕ → Prop := fun n ↦ d ∣ n ^ 2 + 1
  have hcnt_eq : ((Finset.Icc d N).filter P).card =
      q * rho d + (rem.filter P).card := by
    rw [hpart, Finset.filter_union, Finset.card_union_of_disjoint
      (Finset.disjoint_filter_filter hdisj_rem)]
    congr 1
    rw [Finset.filter_biUnion, Finset.card_biUnion]
    · calc ∑ j ∈ Finset.range q, ((Finset.Ico (d + j * d) (d + (j + 1) * d)).filter P).card
          = ∑ _j ∈ Finset.range q, rho d := by
            refine Finset.sum_congr rfl fun j _ ↦ ?_
            rw [show d + (j + 1) * d = (d + j * d) + d by ring]
            exact block_count_eq_rho (d + j * d) d hd
        _ = q * rho d := by simp
    · intro i hi j hj hij
      exact Finset.disjoint_filter_filter (hpair hi hj hij)
  have hrem_le : (rem.filter P).card ≤ rho d := by
    have hsub : rem.filter P ⊆ (Finset.Ico (d + q * d) ((d + q * d) + d)).filter P := by
      intro n hn
      obtain ⟨hn_rem, hP⟩ := Finset.mem_filter.mp hn
      rw [Finset.mem_Ico] at hn_rem
      exact Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr ⟨hn_rem.1, by linarith⟩, hP⟩
    exact (Finset.card_le_card hsub).trans_eq (block_count_eq_rho (d + q * d) d hd)
  have hd_pos : (0 : ℝ) < d := by exact_mod_cast hd
  have hq_ub : (q : ℝ) ≤ (N : ℝ) / (d : ℝ) := by
    rw [le_div_iff₀ hd_pos]
    exact_mod_cast (show q * d ≤ N by omega)
  have hq_lb : (N : ℝ) / (d : ℝ) - 2 ≤ (q : ℝ) := by
    rw [sub_le_iff_le_add, div_le_iff₀ hd_pos]
    have : N + 1 < d + (q + 1) * d := hN_lt_q1
    have hcast : (N : ℝ) ≤ (q : ℝ) * (d : ℝ) + 2 * (d : ℝ) := by
      exact_mod_cast (by nlinarith : N ≤ q * d + 2 * d)
    linarith
  have hcnt_r : (((Finset.Icc d N).filter P).card : ℝ) =
      (q : ℝ) * (rho d : ℝ) + ((rem.filter P).card : ℝ) := by exact_mod_cast hcnt_eq
  have hrem_r : ((rem.filter P).card : ℝ) ≤ (rho d : ℝ) := by exact_mod_cast hrem_le
  have hrho_nn : (0 : ℝ) ≤ (rho d : ℝ) := Nat.cast_nonneg _
  rw [hcnt_r, abs_sub_le_iff]
  constructor <;> nlinarith

private lemma Erdos975Sum_approx (x : ℝ) (hx : 1 ≤ x) :
    |Erdos975.Erdos975Sum (X ^ 2 + 1) x - 2 * (⌊x⌋₊ : ℝ) * S_rho ⌊x⌋₊| ≤
      1 + 4 * R_rho ⌊x⌋₊ := by
  let N := ⌊x⌋₊
  have hN1 : 1 ≤ N := Nat.le_floor (by exact_mod_cast hx)
  have hsum_eq : Erdos975.Erdos975Sum (X ^ 2 + 1) x =
      1 + 2 * ∑ d ∈ Finset.Icc 1 N,
        (((Finset.Icc d N).filter (fun n ↦ d ∣ n ^ 2 + 1)).card : ℝ) := by
    unfold Erdos975.Erdos975Sum
    change ∑ n ∈ Finset.Iic N, (σ 0 ⌊((X ^ 2 + 1 : ℤ[X]).eval (n : ℤ))⌋₊ : ℝ) = _
    have h0 : (0 : ℕ) ∉ Finset.Icc 1 N := by simp
    have hIic : Finset.Iic N = insert 0 (Finset.Icc 1 N) := by
      ext n; simp only [Finset.mem_Iic, Finset.mem_insert, Finset.mem_Icc]; omega
    rw [hIic, Finset.sum_insert h0]
    have h0val : (σ 0 ⌊((X ^ 2 + 1 : ℤ[X]).eval ((0 : ℕ) : ℤ))⌋₊ : ℝ) = 1 := by
      simp [Polynomial.eval_add, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_one]
    rw [h0val]
    congr 1
    have hterm : ∀ n ∈ Finset.Icc 1 N,
        (σ 0 ⌊((X ^ 2 + 1 : ℤ[X]).eval (n : ℤ))⌋₊ : ℝ) =
          2 * ∑ d ∈ Finset.Icc 1 N, if d ≤ n ∧ d ∣ n ^ 2 + 1 then (1 : ℝ) else 0 := by
      intro n hn
      rw [Finset.mem_Icc] at hn
      have heval : ⌊((X ^ 2 + 1 : ℤ[X]).eval (n : ℤ))⌋₊ = n ^ 2 + 1 := by
        simp only [Polynomial.eval_add, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_one]
        exact_mod_cast Nat.floor_natCast (R := ℤ) (n ^ 2 + 1)
      rw [heval, div_symm_n2_plus_1 n hn.1, ← Finset.sum_filter]
      congr 1
      rw [Finset.sum_const, nsmul_eq_mul, mul_one]
      congr 2
      ext d
      simp only [Finset.mem_filter, Finset.mem_Icc]
      omega
    rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum, Finset.sum_comm]
    congr 1
    refine Finset.sum_congr rfl fun d hd ↦ ?_
    rw [Finset.mem_Icc] at hd
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one]
    congr 2
    ext n
    simp only [Finset.mem_filter, Finset.mem_Icc]
    omega
  rw [hsum_eq]
  have hS_eq : 2 * (N : ℝ) * S_rho N =
      2 * ∑ d ∈ Finset.Icc 1 N, (N : ℝ) / (d : ℝ) * (rho d : ℝ) := by
    unfold S_rho
    rw [mul_assoc, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun d _ ↦ by ring
  rw [hS_eq]
  have hdiff : (1 + 2 * ∑ d ∈ Finset.Icc 1 N,
      (((Finset.Icc d N).filter (fun n ↦ d ∣ n ^ 2 + 1)).card : ℝ)) -
      2 * ∑ d ∈ Finset.Icc 1 N, (N : ℝ) / (d : ℝ) * (rho d : ℝ) =
      1 + 2 * ∑ d ∈ Finset.Icc 1 N,
        ((((Finset.Icc d N).filter (fun n ↦ d ∣ n ^ 2 + 1)).card : ℝ) -
          (N : ℝ) / (d : ℝ) * (rho d : ℝ)) := by
    rw [Finset.sum_sub_distrib]
    ring
  rw [hdiff]
  refine (abs_add_le _ _).trans ?_
  rw [abs_one, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
  have hsum_abs : |∑ d ∈ Finset.Icc 1 N,
      ((((Finset.Icc d N).filter (fun n ↦ d ∣ n ^ 2 + 1)).card : ℝ) -
        (N : ℝ) / (d : ℝ) * (rho d : ℝ))| ≤ 2 * R_rho N := by
    calc |∑ d ∈ Finset.Icc 1 N,
          ((((Finset.Icc d N).filter (fun n ↦ d ∣ n ^ 2 + 1)).card : ℝ) -
            (N : ℝ) / (d : ℝ) * (rho d : ℝ))|
        ≤ ∑ d ∈ Finset.Icc 1 N,
            |(((Finset.Icc d N).filter (fun n ↦ d ∣ n ^ 2 + 1)).card : ℝ) -
              (N : ℝ) / (d : ℝ) * (rho d : ℝ)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ d ∈ Finset.Icc 1 N, 2 * (rho d : ℝ) := by
          refine Finset.sum_le_sum fun d hd ↦ ?_
          rw [Finset.mem_Icc] at hd
          exact interval_count_approx d N hd.1
      _ = 2 * R_rho N := by rw [← Finset.mul_sum]; rfl
  linarith

end AbelAndFinal

theorem solution_main :
    ∃ c > (0 : ℝ), Tendsto (fun x ↦ Erdos975.Erdos975Sum (X ^ 2 + 1) x / (x * log x)) atTop (𝓝 c) := by
  let c₁ := π / 4 * LConst
  refine ⟨2 * c₁, by have := LConst_pos; positivity, ?_⟩
  have htend_floor : Tendsto (fun x : ℝ ↦ ⌊x⌋₊) atTop atTop :=
    tendsto_atTop.mpr fun b ↦ (eventually_ge_atTop (b : ℝ)).mono fun _ hx ↦ Nat.le_floor hx
  have htend_floor_div : Tendsto (fun x : ℝ ↦ (⌊x⌋₊ : ℝ) / x) atTop (𝓝 1) := by
    have h1 : Tendsto (fun x : ℝ ↦ 1 - 1 / x) atTop (𝓝 1) := by
      simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub
        ((tendsto_const_nhds (x := (1 : ℝ))).div_atTop tendsto_id)
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' h1 tendsto_const_nhds ?_ ?_
    · filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
      have hfl := Nat.sub_one_lt_floor x
      rw [sub_le_iff_le_add, ← add_div, le_div_iff₀ (by linarith)]
      linarith
    · filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
      rw [div_le_one (by linarith)]
      exact Nat.floor_le (by linarith)
  have htend_log_div : Tendsto (fun x : ℝ ↦ Real.log (⌊x⌋₊ : ℝ) / Real.log x) atTop (𝓝 1) := by
    have hcomp : Tendsto (fun x : ℝ ↦ 1 + Real.log ((⌊x⌋₊ : ℝ) / x) / Real.log x) atTop (𝓝 1) := by
      have hlog1 : Tendsto (fun x : ℝ ↦ Real.log ((⌊x⌋₊ : ℝ) / x)) atTop (𝓝 0) := by
        simpa [Function.comp_def, Real.log_one] using
          (Real.continuousAt_log one_ne_zero).tendsto.comp htend_floor_div
      simpa using (tendsto_const_nhds (x := (1 : ℝ))).add (hlog1.div_atTop Real.tendsto_log_atTop)
    refine hcomp.congr' ?_
    filter_upwards [eventually_ge_atTop (2 : ℝ)] with x hx
    have hfl_ge1 : 1 ≤ ⌊x⌋₊ := Nat.le_floor (by norm_num; linarith)
    have hfl_pos : (0 : ℝ) < (⌊x⌋₊ : ℝ) := by exact_mod_cast hfl_ge1
    have hlog_ne : Real.log x ≠ 0 := (Real.log_pos (by linarith)).ne'
    rw [Real.log_div hfl_pos.ne' (by linarith)]
    field_simp
    ring
  have htend_main : Tendsto
      (fun x : ℝ ↦ (2 * (⌊x⌋₊ : ℝ) * S_rho ⌊x⌋₊) / (x * Real.log x)) atTop (𝓝 (2 * c₁)) := by
    have hprod : Tendsto (fun x : ℝ ↦
        2 * ((⌊x⌋₊ : ℝ) / x) * (S_rho ⌊x⌋₊ / Real.log (⌊x⌋₊ : ℝ)) *
          (Real.log (⌊x⌋₊ : ℝ) / Real.log x)) atTop (𝓝 (2 * 1 * c₁ * 1)) :=
      (((tendsto_const_nhds.mul htend_floor_div).mul
        (tendsto_S_rho_div_log.comp htend_floor)).mul htend_log_div)
    rw [mul_one, mul_one] at hprod
    refine hprod.congr' ?_
    filter_upwards [eventually_ge_atTop (2 : ℝ)] with x hx
    have hfl2 : 2 ≤ ⌊x⌋₊ := Nat.le_floor (by norm_num; linarith)
    have hlog_fl : Real.log (⌊x⌋₊ : ℝ) ≠ 0 :=
      (Real.log_pos (by exact_mod_cast (by omega : 1 < ⌊x⌋₊))).ne'
    have hlog_x : Real.log x ≠ 0 := (Real.log_pos (by linarith)).ne'
    have hx0 : x ≠ 0 := by linarith
    field_simp
  have htend_err : Tendsto
      (fun x : ℝ ↦ (Erdos975.Erdos975Sum (X ^ 2 + 1) x - 2 * (⌊x⌋₊ : ℝ) * S_rho ⌊x⌋₊) /
        (x * Real.log x)) atTop (𝓝 0) := by
    have hbound : Tendsto (fun x : ℝ ↦
        (1 + 4 * R_rho ⌊x⌋₊) / (x * Real.log x)) atTop (𝓝 0) := by
      have h1 : Tendsto (fun x : ℝ ↦ 1 / (x * Real.log x)) atTop (𝓝 0) :=
        tendsto_const_nhds.div_atTop (tendsto_id.atTop_mul_atTop₀ Real.tendsto_log_atTop)
      have h2 : Tendsto (fun x : ℝ ↦
          4 * (R_rho ⌊x⌋₊ / (⌊x⌋₊ : ℝ)) * ((⌊x⌋₊ : ℝ) / x) / Real.log x) atTop (𝓝 0) := by
        have hnum : Tendsto (fun x : ℝ ↦ 4 * (R_rho ⌊x⌋₊ / (⌊x⌋₊ : ℝ)) * ((⌊x⌋₊ : ℝ) / x))
            atTop (𝓝 (4 * c₁ * 1)) :=
          ((tendsto_const_nhds.mul (tendsto_R_rho_div.comp htend_floor)).mul htend_floor_div)
        exact hnum.div_atTop Real.tendsto_log_atTop
      have hadd : Tendsto (fun x : ℝ ↦
          1 / (x * Real.log x) + 4 * (R_rho ⌊x⌋₊ / (⌊x⌋₊ : ℝ)) * ((⌊x⌋₊ : ℝ) / x) / Real.log x)
          atTop (𝓝 0) := by
        simpa using h1.add h2
      refine hadd.congr' ?_
      filter_upwards [eventually_ge_atTop (2 : ℝ)] with x hx
      have hfl2 : 2 ≤ ⌊x⌋₊ := Nat.le_floor (by norm_num; linarith)
      have hfl_ne : (⌊x⌋₊ : ℝ) ≠ 0 := by exact_mod_cast (by omega : ⌊x⌋₊ ≠ 0)
      have hx_ne : x ≠ 0 := by linarith
      have hlog_ne : Real.log x ≠ 0 := (Real.log_pos (by linarith)).ne'
      field_simp
    refine tendsto_iff_norm_sub_tendsto_zero.mpr ?_
    refine squeeze_zero' (Eventually.of_forall fun _ ↦ norm_nonneg _) ?_ hbound
    filter_upwards [eventually_ge_atTop (2 : ℝ)] with x hx
    rw [sub_zero, Real.norm_eq_abs, abs_div]
    have hden_pos : 0 < x * Real.log x := mul_pos (by linarith) (Real.log_pos (by linarith))
    rw [abs_of_pos hden_pos]
    exact div_le_div_of_nonneg_right (Erdos975Sum_approx x (by linarith)) hden_pos.le
  have hsum := htend_main.add htend_err
  rw [add_zero] at hsum
  refine hsum.congr' ?_
  filter_upwards [eventually_ge_atTop (2 : ℝ)] with x _
  ring

end Erdos975Proof

theorem OMA.solution : type_of% @Erdos975.erdos_975.variants.n2_plus_1 :=
  Erdos975Proof.solution_main
