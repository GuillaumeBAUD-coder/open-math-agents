import FormalConjectures.Wikipedia.ArtinPrimitiveRootsConjecture

-- Reduction ArtinPrimitiveRootsConjecture.conditional_artin_primitive_roots.parts.i.R1 of Artin's Conjecture on Primitive Roots
-- Credit: @senamakel
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.
--
-- Route (Hooley 1967): a prime p not dividing a has a as a primitive root iff no prime q
-- has q | p - 1 and a^((p-1)/q) = 1 mod p, that is iff p splits completely in no Kummer
-- field K_q = Q(zeta_q, a^(1/q)). Inclusion-exclusion over the primes q below
-- xi1 = (log x)/6 with H1 for the small squarefree k, Brun-Titchmarsh (H2) for the primes
-- q in (sqrt x / log^2 x, sqrt x log x], H1 again for the medium primes, and a direct
-- count for the huge primes q > sqrt x log x, show that the proportion of primes below x
-- with a as a primitive root tends to delta(a) = sum over k of mu(k) / [K_k : Q].
-- H3 makes the series converge and H4 makes delta(a) positive. main proves this sieve
-- half in full; the analytic input and the Kummer theory are the hypotheses.
--
-- H1: effective Chebotarev for the Kummer fields under Hooley's hypothesis (RH for the
--     Dedekind zeta functions of K_k, as HooleyHypothesis states it): the number of
--     primes p < x splitting completely in K_k is pi(x) / [K_k : Q] + O(sqrt x log(kx)),
--     uniformly in squarefree k (Hooley 1967, section 3; Lagarias-Odlyzko 1977).
-- H2: Brun-Titchmarsh for the progression 1 mod q, with the constant 20000.
-- H3: Kummer degrees: k phi(k) is at most c [K_k : Q] for squarefree k, a not 0, 1, -1.
-- H4: Kummer theory: Artin's density delta(a) is positive for a not a square, a not -1.
--
-- Hooley's hypothesis is the premise of the target itself, so it is not one of the H's.

open scoped Classical

namespace OMA.R_ArtinPrimitiveRootsConjecture_conditional_artin_primitive_roots_parts_i_R1

/-- Effective Chebotarev for the Kummer fields of `a` under Hooley's hypothesis. -/
def H1 : Prop :=
  ∀ a : ℤ, a ≠ 0 → ArtinPrimitiveRootsConjecture.HooleyHypothesis a →
    ∃ C : ℝ, ∀ k x : ℕ, Squarefree k → 2 ≤ x →
      |((((Finset.range x).filter fun p : ℕ => p.Prime ∧ ¬ (p : ℤ) ∣ a ∧ k ∣ p - 1 ∧
            (a : ZMod p) ^ ((p - 1) / k) = 1).card : ℕ) : ℝ) -
          (Nat.primeCounting x : ℝ) /
            ((Module.finrank ℚ (Polynomial.X ^ k - Polynomial.C (a : ℚ)).SplittingField : ℕ) : ℝ)|
        ≤ C * Real.sqrt x * Real.log (k * x)

/-- Brun–Titchmarsh: `π(x; q, 1) ≤ 20000 x / (φ(q) log(x/q))` for `1 ≤ q < x`. -/
def H2 : Prop :=
  ∀ q : ℕ, 1 ≤ q → ∀ x : ℝ, (q : ℝ) < x →
    ((((Finset.range (⌊x⌋₊ + 1)).filter fun p => p.Prime ∧ p ≡ 1 [MOD q]).card : ℕ) : ℝ) ≤
      20000 * x / (q.totient * Real.log (x / q))

/-- The Kummer degrees grow like `k φ(k)`. -/
def H3 : Prop :=
  ∀ a : ℤ, a ≠ 0 → a ≠ 1 → a ≠ -1 → ∃ c : ℝ, 0 < c ∧ ∀ k : ℕ, Squarefree k → 0 < k →
    (k : ℝ) * (Nat.totient k : ℝ) ≤
      c * ((Module.finrank ℚ (Polynomial.X ^ k - Polynomial.C (a : ℚ)).SplittingField : ℕ) : ℝ)

/-- Artin's density `Σ_k μ(k) / [ℚ(ζ_k, a^{1/k}) : ℚ]` is positive. -/
def H4 : Prop :=
  ∀ a : ℤ, ¬ IsSquare a → a ≠ -1 →
    0 < ∑' k : ℕ, (ArithmeticFunction.moebius k : ℝ) /
      ((Module.finrank ℚ (Polynomial.X ^ k - Polynomial.C (a : ℚ)).SplittingField : ℕ) : ℝ)


section

namespace Artin

open ArtinPrimitiveRootsConjecture Polynomial

end Artin

end

section

namespace Artin

open scoped ArithmeticFunction.Moebius

end Artin

end

section

namespace Artin

open ArtinPrimitiveRootsConjecture Finset
open scoped ArithmeticFunction.Moebius

lemma intCast_zmod_ne_zero {p : ℕ} {a : ℤ} (ha : ¬ (p : ℤ) ∣ a) : (a : ZMod p) ≠ 0 := by
  rwa [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]

lemma pow_sub_one_eq_one {p : ℕ} (hp : p.Prime) {a : ℤ} (ha : ¬ (p : ℤ) ∣ a) :
    (a : ZMod p) ^ (p - 1) = 1 := by
  have := Fact.mk hp
  exact ZMod.pow_card_sub_one_eq_one (intCast_zmod_ne_zero ha)

theorem orderOf_eq_sub_one_iff {p : ℕ} (hp : p.Prime) {a : ℤ} (ha : ¬ (p : ℤ) ∣ a) :
    orderOf (a : ZMod p) = p - 1 ↔
      ∀ q : ℕ, q.Prime → q ∣ p - 1 → (a : ZMod p) ^ ((p - 1) / q) ≠ 1 := by
  constructor
  · intro h q hq hqd heq
    have hdvd := orderOf_dvd_of_pow_eq_one heq
    rw [h] at hdvd
    have hpos : 0 < p - 1 := Nat.sub_pos_of_lt hp.one_lt
    have h1 := Nat.le_of_dvd (Nat.div_pos (Nat.le_of_dvd hpos hqd) hq.pos) hdvd
    have h2 := Nat.div_lt_self hpos hq.one_lt
    omega
  · intro h
    exact orderOf_eq_of_pow_and_pow_div_prime (Nat.sub_pos_of_lt hp.one_lt) (pow_sub_one_eq_one hp ha) h

lemma orderOf_dvd_sub_one {p : ℕ} (hp : p.Prime) {a : ℤ} (ha : ¬ (p : ℤ) ∣ a) :
    orderOf (a : ZMod p) ∣ p - 1 :=
  orderOf_dvd_of_pow_eq_one (pow_sub_one_eq_one hp ha)

lemma orderOf_pos' {p : ℕ} (hp : p.Prime) {a : ℤ} (ha : ¬ (p : ℤ) ∣ a) :
    0 < orderOf (a : ZMod p) := by
  rcases Nat.eq_zero_or_pos (orderOf (a : ZMod p)) with h | h
  · have := orderOf_dvd_sub_one hp ha
    rw [h, zero_dvd_iff] at this
    have := hp.one_lt
    omega
  · exact h

theorem kummer_cond_iff {p : ℕ} (hp : p.Prime) {a : ℤ} (ha : ¬ (p : ℤ) ∣ a) (k : ℕ) :
    (k ∣ p - 1 ∧ (a : ZMod p) ^ ((p - 1) / k) = 1) ↔
      k ∣ (p - 1) / orderOf (a : ZMod p) := by
  set d := orderOf (a : ZMod p) with hd
  have hdpos : 0 < d := orderOf_pos' hp ha
  obtain ⟨m, hm⟩ := orderOf_dvd_sub_one hp ha
  rw [← hd] at hm
  have hm' : (p - 1) / d = m := by rw [hm, Nat.mul_div_cancel_left _ hdpos]
  rw [hm', hm]
  constructor
  · rintro ⟨⟨j, hj⟩, hpow⟩
    have hk0 : 0 < k := by
      rcases Nat.eq_zero_or_pos k with h | h
      · subst h
        have h1 := hp.one_lt
        have : d * m ≠ 0 := by omega
        simp at hj; exact absurd hj (by simpa using this)
      · exact h
    rw [hj, Nat.mul_div_cancel_left _ hk0] at hpow
    obtain ⟨i, hi⟩ := orderOf_dvd_of_pow_eq_one hpow
    rw [← hd] at hi
    refine ⟨i, ?_⟩
    have : d * m = d * (k * i) := by rw [hj, hi]; ring
    exact Nat.eq_of_mul_eq_mul_left hdpos this
  · intro hk
    refine ⟨Dvd.dvd.mul_left hk d, ?_⟩
    rw [Nat.mul_div_assoc d hk, pow_mul, hd, pow_orderOf_eq_one, one_pow]

theorem sum_moebius_divisors (n : ℕ) :
    ∑ d ∈ n.divisors, (μ d : ℤ) = if n = 1 then 1 else 0 := by
  rw [← ArithmeticFunction.coe_mul_zeta_apply, ArithmeticFunction.moebius_mul_coe_zeta,
    ArithmeticFunction.one_apply]

theorem sum_moebius_kummerCount (a : ℤ) (Q : Finset ℕ) (hQ : ∀ q ∈ Q, q.Prime) (x : ℕ) :
    ∑ k ∈ (∏ q ∈ Q, q).divisors, (μ k : ℤ) * ((((Finset.range (x : ℕ)).filter fun pK : ℕ => pK.Prime ∧ ¬ (pK : ℤ) ∣ (a : ℤ) ∧ (k : ℕ) ∣ pK - 1 ∧ ((a : ℤ) : ZMod pK) ^ ((pK - 1) / (k : ℕ)) = 1).card : ℕ)) = ((((Finset.range (x : ℕ)).filter fun pK : ℕ => pK.Prime ∧ ¬ (pK : ℤ) ∣ (a : ℤ) ∧ ∀ qK ∈ (Q : Finset ℕ), ¬ (qK ∣ pK - 1 ∧ ((a : ℤ) : ZMod pK) ^ ((pK - 1) / qK) = 1)).card : ℕ)) := by
  classical
  set P := ∏ q ∈ Q, q with hPdef
  have hP : P ≠ 0 := Finset.prod_ne_zero_iff.mpr fun q hq => (hQ q hq).ne_zero
  set A := (range x).filter fun p : ℕ => p.Prime ∧ ¬ (p : ℤ) ∣ a with hA
  set m : ℕ → ℕ := fun p => (p - 1) / orderOf (a : ZMod p) with hm
  
  have hK : ∀ k, (((((Finset.range (x : ℕ)).filter fun pK : ℕ => pK.Prime ∧ ¬ (pK : ℤ) ∣ (a : ℤ) ∧ (k : ℕ) ∣ pK - 1 ∧ ((a : ℤ) : ZMod pK) ^ ((pK - 1) / (k : ℕ)) = 1).card : ℕ)) : ℤ) = ∑ p ∈ A, if k ∣ m p then (1 : ℤ) else 0 := by
    intro k
    rw [Finset.card_filter, hA, Finset.sum_filter]
    push_cast
    refine Finset.sum_congr rfl fun p _ => ?_
    by_cases h : p.Prime ∧ ¬ (p : ℤ) ∣ a
    · have := kummer_cond_iff h.1 h.2 k
      simp only [h, not_false_eq_true, true_and, ite_true]
      by_cases h' : k ∣ m p
      · simp [h', this.mpr h']
      · have h3 : ¬ (k ∣ p - 1 ∧ (a : ZMod p) ^ ((p - 1) / k) = 1) := fun h'' => h' (this.mp h'')
        simp only [h', h3, ite_false]
    · have h2 : ¬ (p.Prime ∧ ¬ (p : ℤ) ∣ a ∧ k ∣ p - 1 ∧ (a : ZMod p) ^ ((p - 1) / k) = 1) :=
        fun h'' => h ⟨h''.1, h''.2.1⟩
      simp only [h, h2, ite_false]
  
  have hinner : ∀ p, (∑ k ∈ P.divisors, (μ k : ℤ) * if k ∣ m p then (1 : ℤ) else 0) =
      if Nat.gcd P (m p) = 1 then 1 else 0 := by
    intro p
    rw [← sum_moebius_divisors]
    simp only [mul_ite, mul_one, mul_zero]
    rw [← Finset.sum_filter]
    congr 1
    ext k
    simp only [Finset.mem_filter, Nat.mem_divisors, Nat.dvd_gcd_iff]
    have : Nat.gcd P (m p) ≠ 0 := Nat.gcd_ne_zero_left hP
    tauto
  have hcop : ∀ p ∈ A, (Nat.gcd P (m p) = 1 ↔
      ∀ q ∈ Q, ¬ (q ∣ p - 1 ∧ (a : ZMod p) ^ ((p - 1) / q) = 1)) := by
    intro p hpA
    rw [hA, Finset.mem_filter] at hpA
    rw [← Nat.Coprime, hPdef, Nat.coprime_prod_left_iff]
    refine forall₂_congr fun q hq => ?_
    rw [Nat.Prime.coprime_iff_not_dvd (hQ q hq), kummer_cond_iff hpA.2.1 hpA.2.2]
  calc ∑ k ∈ P.divisors, (μ k : ℤ) * ((((Finset.range (x : ℕ)).filter fun pK : ℕ => pK.Prime ∧ ¬ (pK : ℤ) ∣ (a : ℤ) ∧ (k : ℕ) ∣ pK - 1 ∧ ((a : ℤ) : ZMod pK) ^ ((pK - 1) / (k : ℕ)) = 1).card : ℕ))
      = ∑ k ∈ P.divisors, ∑ p ∈ A, (μ k : ℤ) * if k ∣ m p then (1 : ℤ) else 0 := by
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [hK, Finset.mul_sum]
    _ = ∑ p ∈ A, ∑ k ∈ P.divisors, (μ k : ℤ) * if k ∣ m p then (1 : ℤ) else 0 :=
        Finset.sum_comm
    _ = ∑ p ∈ A, if Nat.gcd P (m p) = 1 then (1 : ℤ) else 0 :=
        Finset.sum_congr rfl fun p _ => hinner p
    _ = ((A.filter fun p => Nat.gcd P (m p) = 1).card : ℤ) := by
        rw [Finset.card_filter]; push_cast; rfl
    _ = ((((Finset.range (x : ℕ)).filter fun pK : ℕ => pK.Prime ∧ ¬ (pK : ℤ) ∣ (a : ℤ) ∧ ∀ qK ∈ (Q : Finset ℕ), ¬ (qK ∣ pK - 1 ∧ ((a : ℤ) : ZMod pK) ^ ((pK - 1) / qK) = 1)).card : ℕ)) := by
        beta_reduce
        congr 2
        rw [hA, Finset.filter_filter]
        refine Finset.filter_congr fun p hp => ?_
        constructor
        · rintro ⟨⟨h1, h2⟩, h3⟩
          exact ⟨h1, h2, (hcop p (by simp [hA, hp, h1, h2])).mp h3⟩
        · rintro ⟨h1, h2, h3⟩
          exact ⟨⟨h1, h2⟩, (hcop p (by simp [hA, hp, h1, h2])).mpr h3⟩

lemma not_dvd_of_orderOf_eq {p : ℕ} (hp : p.Prime) {a : ℤ}
    (h : orderOf (a : ZMod p) = p - 1) : ¬ (p : ℤ) ∣ a := by
  intro hdvd
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd] at hdvd
  rw [hdvd, orderOf_eq_zero_iff'.mpr] at h
  · have := hp.one_lt; omega
  · intro n hn h0
    have := Fact.mk hp
    rw [zero_pow hn.ne'] at h0
    exact zero_ne_one h0

lemma not_kummer_of_orderOf_eq {p : ℕ} (hp : p.Prime) {a : ℤ}
    (h : orderOf (a : ZMod p) = p - 1) (q : ℕ) (hq : q.Prime) :
    ¬ (q ∣ p - 1 ∧ (a : ZMod p) ^ ((p - 1) / q) = 1) := fun hc =>
  (orderOf_eq_sub_one_iff hp (not_dvd_of_orderOf_eq hp h)).mp h q hq hc.1 hc.2

theorem primRootCount_eq_sum_moebius (a : ℤ) (Q : Finset ℕ) (hQ : ∀ q ∈ Q, q.Prime) (x : ℕ)
    (hQx : ∀ q : ℕ, q.Prime → q < x → q ∈ Q) :
    (((((Finset.range (x : ℕ)).filter fun pK : ℕ => pK.Prime ∧ orderOf ((a : ℤ) : ZMod pK) = pK - 1).card : ℕ)) : ℤ) =
      ∑ k ∈ (∏ q ∈ Q, q).divisors, (μ k : ℤ) * ((((Finset.range (x : ℕ)).filter fun pK : ℕ => pK.Prime ∧ ¬ (pK : ℤ) ∣ (a : ℤ) ∧ (k : ℕ) ∣ pK - 1 ∧ ((a : ℤ) : ZMod pK) ^ ((pK - 1) / (k : ℕ)) = 1).card : ℕ)) := by
  rw [sum_moebius_kummerCount a Q hQ x]
  congr 2
  refine Finset.filter_congr fun p hp => ?_
  rw [Finset.mem_range] at hp
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, not_dvd_of_orderOf_eq h1 h2, fun q hq => not_kummer_of_orderOf_eq h1 h2 q (hQ q hq)⟩
  · rintro ⟨h1, h2, h3⟩
    refine ⟨h1, (orderOf_eq_sub_one_iff h1 h2).mpr fun q hq hqd heq => h3 q ?_ ⟨hqd, heq⟩⟩
    refine hQx q hq ?_
    have := Nat.le_of_dvd (Nat.sub_pos_of_lt h1.one_lt) hqd
    omega

theorem primRootCount_le_sum_moebius (a : ℤ) (ξ x : ℕ) :
    (((((Finset.range (x : ℕ)).filter fun pK : ℕ => pK.Prime ∧ orderOf ((a : ℤ) : ZMod pK) = pK - 1).card : ℕ)) : ℤ) ≤
      ∑ k ∈ (∏ q ∈ Nat.primesLE ξ, q).divisors, (μ k : ℤ) * ((((Finset.range (x : ℕ)).filter fun pK : ℕ => pK.Prime ∧ ¬ (pK : ℤ) ∣ (a : ℤ) ∧ (k : ℕ) ∣ pK - 1 ∧ ((a : ℤ) : ZMod pK) ^ ((pK - 1) / (k : ℕ)) = 1).card : ℕ)) := by
  rw [sum_moebius_kummerCount a _ (fun q hq => (Nat.mem_primesLE.mp hq).2) x]
  exact Nat.cast_le.mpr (Finset.card_le_card fun p hp => by
    simp only [Finset.mem_filter] at hp ⊢
    exact ⟨hp.1, hp.2.1, not_dvd_of_orderOf_eq hp.2.1 hp.2.2, fun q hq =>
      not_kummer_of_orderOf_eq hp.2.1 hp.2.2 q (Nat.mem_primesLE.mp hq).2⟩)

theorem sum_moebius_sub_le_primRootCount (a : ℤ) (ξ x : ℕ) :
    ∑ k ∈ (∏ q ∈ Nat.primesLE ξ, q).divisors, (μ k : ℤ) * ((((Finset.range (x : ℕ)).filter fun pK : ℕ => pK.Prime ∧ ¬ (pK : ℤ) ∣ (a : ℤ) ∧ (k : ℕ) ∣ pK - 1 ∧ ((a : ℤ) : ZMod pK) ^ ((pK - 1) / (k : ℕ)) = 1).card : ℕ)) -
        ∑ q ∈ (range x).filter (fun q => q.Prime ∧ ξ < q), (((((Finset.range (x : ℕ)).filter fun pK : ℕ => pK.Prime ∧ ¬ (pK : ℤ) ∣ (a : ℤ) ∧ (q : ℕ) ∣ pK - 1 ∧ ((a : ℤ) : ZMod pK) ^ ((pK - 1) / (q : ℕ)) = 1).card : ℕ)) : ℤ) ≤
      ((((Finset.range (x : ℕ)).filter fun pK : ℕ => pK.Prime ∧ orderOf ((a : ℤ) : ZMod pK) = pK - 1).card : ℕ)) := by
  classical
  rw [sub_le_iff_le_add, sum_moebius_kummerCount a _ (fun q hq => (Nat.mem_primesLE.mp hq).2) x]
  have key : ((range x).filter fun p : ℕ => p.Prime ∧ ¬ (p : ℤ) ∣ a ∧
      ∀ q ∈ Nat.primesLE ξ, ¬ (q ∣ p - 1 ∧ (a : ZMod p) ^ ((p - 1) / q) = 1)) ⊆
      ((range x).filter fun p : ℕ => p.Prime ∧ orderOf (a : ZMod p) = p - 1) ∪
        ((range x).filter (fun q => q.Prime ∧ ξ < q)).biUnion fun q =>
          (range x).filter fun p : ℕ => p.Prime ∧ ¬ (p : ℤ) ∣ a ∧ q ∣ p - 1 ∧
            (a : ZMod p) ^ ((p - 1) / q) = 1 := by
    intro p hp
    simp only [Finset.mem_filter, Finset.mem_range] at hp
    obtain ⟨hpx, hp, hpa, hsift⟩ := hp
    by_cases hord : orderOf (a : ZMod p) = p - 1
    · exact Finset.mem_union_left _ (by simp [hpx, hp, hord])
    · refine Finset.mem_union_right _ ?_
      have := mt (orderOf_eq_sub_one_iff hp hpa).mpr hord
      push Not at this
      obtain ⟨q, hq, hqd, heq⟩ := this
      have hqp := Nat.le_of_dvd (Nat.sub_pos_of_lt hp.one_lt) hqd
      have hξq : ξ < q := by
        by_contra hle
        exact hsift q (Nat.mem_primesLE.mpr ⟨by omega, hq⟩) ⟨hqd, heq⟩
      simp only [Finset.mem_biUnion, Finset.mem_filter, Finset.mem_range]
      exact ⟨q, ⟨by omega, hq, hξq⟩, hpx, hp, hpa, hqd, heq⟩
  have := (Finset.card_le_card key).trans
    ((Finset.card_union_le _ _).trans (Nat.add_le_add_left Finset.card_biUnion_le _))
  beta_reduce
  beta_reduce
  exact_mod_cast this

end Artin

end

section

namespace Artin

open ArtinPrimitiveRootsConjecture Filter Finset
open scoped Topology

lemma partialDensity_S_eq (a : ℤ) (b : ℕ) :
    (S a).partialDensity {p | p.Prime} b =
      (((((Finset.range (b : ℕ)).filter fun pK : ℕ => pK.Prime ∧ orderOf ((a : ℤ) : ZMod pK) = pK - 1).card : ℕ)) : ℝ) / (Nat.primeCounting' b : ℝ) := by
  classical
  have h1 : (S a ∩ {p | p.Prime}) ∩ Set.Iio b =
      ↑((range b).filter fun p : ℕ => p.Prime ∧ orderOf (a : ZMod p) = p - 1) := by
    ext p
    simp only [S, Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_Iio, coe_filter, mem_range]
    tauto
  have h2 : {p : ℕ | p.Prime} ∩ Set.Iio b = ↑(Nat.primesBelow b) := by
    ext p
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_Iio, Nat.primesBelow, coe_filter,
      mem_range]
    tauto
  rw [Set.partialDensity, h1, h2, Set.ncard_coe_finset, Set.ncard_coe_finset, Nat.primesBelow_card_eq_primeCounting']

lemma primeCounting_le_primeCounting'_add_one (b : ℕ) :
    Nat.primeCounting b ≤ Nat.primeCounting' b + 1 := by
  rw [Nat.primeCounting_eq_primeCounting'_succ]
  unfold Nat.primeCounting'
  rw [Nat.count_succ]
  split_ifs <;> omega

lemma tendsto_primeCounting_div_primeCounting' :
    Tendsto (fun b : ℕ => (Nat.primeCounting b : ℝ) / Nat.primeCounting' b) atTop (𝓝 1) := by
  have hinv : Tendsto (fun b : ℕ => ((Nat.primeCounting' b : ℝ))⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp
      (tendsto_natCast_atTop_atTop.comp Nat.tendsto_primeCounting')
  have hupper : Tendsto (fun b : ℕ => 1 + ((Nat.primeCounting' b : ℝ))⁻¹) atTop (𝓝 1) := by
    simpa using hinv.const_add 1
  have hpos : ∀ᶠ b : ℕ in atTop, 0 < (Nat.primeCounting' b : ℝ) := by
    filter_upwards [Nat.tendsto_primeCounting'.eventually_gt_atTop 0] with b hb
    exact_mod_cast hb
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hupper ?_ ?_
  · filter_upwards [hpos] with b hb
    rw [le_div_iff₀ hb, one_mul]
    exact_mod_cast Nat.monotone_primeCounting' (Nat.le_succ b)
  · filter_upwards [hpos] with b hb
    rw [div_le_iff₀ hb, add_mul, one_mul, inv_mul_cancel₀ hb.ne']
    exact_mod_cast primeCounting_le_primeCounting'_add_one b

theorem hasDensity_of_tendsto (a : ℤ) (δ : ℝ)
    (h : Tendsto (fun x : ℕ => (((((Finset.range (x : ℕ)).filter fun pK : ℕ => pK.Prime ∧ orderOf ((a : ℤ) : ZMod pK) = pK - 1).card : ℕ)) : ℝ) / Nat.primeCounting x) atTop (𝓝 δ)) :
    (S a).HasDensity δ {p | p.Prime} := by
  unfold Set.HasDensity
  have hlim := h.mul tendsto_primeCounting_div_primeCounting'
  rw [mul_one] at hlim
  refine hlim.congr' ?_
  filter_upwards [Nat.tendsto_primeCounting.eventually_gt_atTop 0] with b hb
  rw [partialDensity_S_eq]
  have hb' : (Nat.primeCounting b : ℝ) ≠ 0 := by exact_mod_cast hb.ne'
  field_simp

theorem hasDensity_of_tendsto_of_bounded (a : ℤ) (δ : ℝ) (N : ℕ → ℝ) (C : ℝ)
    (hN : ∀ᶠ x : ℕ in atTop, |N x - ((((Finset.range (x : ℕ)).filter fun pK : ℕ => pK.Prime ∧ orderOf ((a : ℤ) : ZMod pK) = pK - 1).card : ℕ))| ≤ C)
    (h : Tendsto (fun x : ℕ => N x / Nat.primeCounting x) atTop (𝓝 δ)) :
    (S a).HasDensity δ {p | p.Prime} := by
  refine hasDensity_of_tendsto a δ ?_
  have hinv : Tendsto (fun b : ℕ => C * ((Nat.primeCounting b : ℝ))⁻¹) atTop (𝓝 0) := by
    simpa using (tendsto_inv_atTop_zero.comp
      (tendsto_natCast_atTop_atTop.comp Nat.tendsto_primeCounting)).const_mul C
  have hdiff : Tendsto (fun x : ℕ => ((((((Finset.range (x : ℕ)).filter fun pK : ℕ => pK.Prime ∧ orderOf ((a : ℤ) : ZMod pK) = pK - 1).card : ℕ)) : ℝ) - N x) / Nat.primeCounting x)
      atTop (𝓝 0) := by
    refine squeeze_zero_norm' ?_ hinv
    filter_upwards [hN, Nat.tendsto_primeCounting.eventually_gt_atTop 0] with x hx hpos
    have hposR : (0 : ℝ) < Nat.primeCounting x := by exact_mod_cast hpos
    rw [Real.norm_eq_abs, abs_div, abs_of_pos hposR, abs_sub_comm, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right hx (inv_nonneg.mpr hposR.le)
  have := h.add hdiff
  rw [add_zero] at this
  refine this.congr fun x => ?_
  rw [← add_div]
  ring_nf

end Artin

end

section

namespace Artin

open Finset

open Classical in

lemma pow_add_one_le_add_one_pow (c : ℕ) {m : ℕ} (hm : 1 ≤ m) : c ^ m + 1 ≤ (c + 1) ^ m := by
  induction m, hm using Nat.le_induction with
  | base => simp
  | succ m hm ih =>
    rw [pow_succ, pow_succ]
    nlinarith [Nat.zero_le (c ^ m), Nat.zero_le c]

lemma card_primeFactors_le_of_le_pow {n B m : ℕ} (hn : n ≠ 0) (h : n ≤ B ^ m) :
    n.primeFactors.card ≤ B * m := by
  have h1 : 2 ^ n.primeFactors.card ≤ n :=
    (Finset.pow_card_le_prod _ id 2 fun p hp => (Nat.prime_of_mem_primeFactors hp).two_le).trans
      (Nat.le_of_dvd (Nat.pos_of_ne_zero hn) (Nat.prod_primeFactors_dvd n))
  have h2 : B ^ m ≤ 2 ^ (B * m) := by
    rw [pow_mul]
    exact Nat.pow_le_pow_left (Nat.lt_two_pow_self).le m
  exact (Nat.pow_le_pow_iff_right (by norm_num)).mp (h1.trans (h.trans h2))

lemma natAbs_pow_sub_one {a : ℤ} (ha : 2 ≤ a.natAbs) {m : ℕ} (hm : 1 ≤ m) :
    (a ^ m - 1).natAbs ≠ 0 ∧ (a ^ m - 1).natAbs ≤ (a.natAbs + 1) ^ m := by
  constructor
  · intro h
    rw [Int.natAbs_eq_zero, sub_eq_zero] at h
    have := congrArg Int.natAbs h
    rw [Int.natAbs_pow, Int.natAbs_one] at this
    have h2 : 2 ^ m ≤ a.natAbs ^ m := Nat.pow_le_pow_left ha m
    have h3 : 2 ≤ 2 ^ m := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
    omega
  · calc (a ^ m - 1).natAbs ≤ (a ^ m).natAbs + (1 : ℤ).natAbs := Int.natAbs_sub_le _ _
      _ = a.natAbs ^ m + 1 := by rw [Int.natAbs_pow, Int.natAbs_one]
      _ ≤ (a.natAbs + 1) ^ m := pow_add_one_le_add_one_pow _ hm

theorem hugePrimeCount_le (a : ℤ) (ha0 : a ≠ 0) (ha1 : a ≠ 1) (ha2 : a ≠ -1) (x : ℕ)
    (hx : 2 ≤ x) :
    (((((Finset.range (x : ℕ)).filter fun pK : ℕ => pK.Prime ∧ ¬ (pK : ℤ) ∣ (a : ℤ) ∧ ∃ qK : ℕ, qK.Prime ∧ Real.sqrt (x : ℕ) * Real.log (x : ℕ) < qK ∧ qK ∣ pK - 1 ∧ ((a : ℤ) : ZMod pK) ^ ((pK - 1) / qK) = 1).card : ℕ)) : ℝ) ≤ (a.natAbs + 1 : ℝ) * x / Real.log x ^ 2 := by
  classical
  have ha : 2 ≤ a.natAbs := by
    rcases Int.natAbs_eq a with h | h <;> omega
  set B := a.natAbs + 1 with hB
  have hxR : (2 : ℝ) ≤ x := by exact_mod_cast hx
  have hlog : 0 < Real.log x := Real.log_pos (by linarith)
  have hsqrt : 0 < Real.sqrt x := Real.sqrt_pos.mpr (by linarith)
  set M : ℝ := Real.sqrt x / Real.log x with hM
  have hM0 : 0 ≤ M := div_nonneg hsqrt.le hlog.le
  set M' := ⌊M⌋₊ with hM'
  
  have hsub : ((range x).filter fun p : ℕ => p.Prime ∧ ¬ (p : ℤ) ∣ a ∧
      ∃ q : ℕ, q.Prime ∧ Real.sqrt x * Real.log x < q ∧ q ∣ p - 1 ∧
        (a : ZMod p) ^ ((p - 1) / q) = 1) ⊆
      (Icc 1 M').biUnion fun m => (a ^ m - 1).natAbs.primeFactors := by
    intro p hp
    simp only [Finset.mem_filter, Finset.mem_range] at hp
    obtain ⟨hpx, hp, -, q, hq, hqbig, hqd, hpow⟩ := hp
    set m := (p - 1) / q with hmdef
    have hqm : q * m = p - 1 := Nat.mul_div_cancel' hqd
    have hp1 := hp.one_lt
    have hm1 : 1 ≤ m := by
      rcases Nat.eq_zero_or_pos m with h | h
      · rw [h, mul_zero] at hqm; omega
      · exact h
    have hmM : m ≤ M' := by
      refine Nat.le_floor ?_
      rw [hM, le_div_iff₀ hlog]
      have hqmR : (q : ℝ) * m < x := by
        have : q * m < x := by omega
        exact_mod_cast this
      have hmR : (0 : ℝ) < m := by exact_mod_cast hm1
      have h1 : (m : ℝ) * (Real.sqrt x * Real.log x) < Real.sqrt x * Real.sqrt x := by
        rw [Real.mul_self_sqrt (by linarith)]
        calc (m : ℝ) * (Real.sqrt x * Real.log x) < m * q := mul_lt_mul_of_pos_left hqbig hmR
          _ = q * m := mul_comm _ _
          _ < x := hqmR
      have h2 : Real.sqrt x * ((m : ℝ) * Real.log x) < Real.sqrt x * Real.sqrt x := by
        linarith
      exact (lt_of_mul_lt_mul_left h2 hsqrt.le).le
    simp only [Finset.mem_biUnion, Finset.mem_Icc]
    refine ⟨m, ⟨hm1, hmM⟩, ?_⟩
    obtain ⟨hne, -⟩ := natAbs_pow_sub_one ha hm1
    refine Nat.mem_primeFactors.mpr ⟨hp, ?_, hne⟩
    rw [← Int.natCast_dvd, ← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    rw [hpow, sub_self]
  
  have hcard : ((range x).filter fun p : ℕ => p.Prime ∧ ¬ (p : ℤ) ∣ a ∧
      ∃ q : ℕ, q.Prime ∧ Real.sqrt x * Real.log x < q ∧ q ∣ p - 1 ∧
        (a : ZMod p) ^ ((p - 1) / q) = 1).card ≤ B * (M' * M') := by
    refine (Finset.card_le_card hsub).trans (Finset.card_biUnion_le.trans ?_)
    calc ∑ m ∈ Icc 1 M', (a ^ m - 1).natAbs.primeFactors.card
        ≤ ∑ _m ∈ Icc 1 M', B * M' := by
          refine Finset.sum_le_sum fun m hm => ?_
          rw [Finset.mem_Icc] at hm
          obtain ⟨hne, hle⟩ := natAbs_pow_sub_one ha hm.1
          exact (card_primeFactors_le_of_le_pow hne hle).trans (Nat.mul_le_mul_left _ hm.2)
      _ = B * (M' * M') := by
          rw [Finset.sum_const, Nat.card_Icc, smul_eq_mul]
          simp only [Nat.add_sub_cancel]
          ring
  have hM'R : (M' : ℝ) ≤ M := Nat.floor_le hM0
  have hMsq : M ^ 2 = x / Real.log x ^ 2 := by
    rw [hM, div_pow, Real.sq_sqrt (by linarith)]
  have hBR : (0 : ℝ) ≤ B := by positivity
  calc (((((Finset.range (x : ℕ)).filter fun pK : ℕ => pK.Prime ∧ ¬ (pK : ℤ) ∣ (a : ℤ) ∧ ∃ qK : ℕ, qK.Prime ∧ Real.sqrt (x : ℕ) * Real.log (x : ℕ) < qK ∧ qK ∣ pK - 1 ∧ ((a : ℤ) : ZMod pK) ^ ((pK - 1) / qK) = 1).card : ℕ)) : ℝ) ≤ (B * (M' * M') : ℕ) := by
        beta_reduce; exact_mod_cast hcard
    _ = (B : ℝ) * (M' : ℝ) ^ 2 := by push_cast; ring
    _ ≤ (B : ℝ) * M ^ 2 := by
        gcongr
    _ = (a.natAbs + 1 : ℝ) * x / Real.log x ^ 2 := by
        rw [hMsq, hB]; push_cast; ring

end Artin

end

section

end

section

namespace Artin

open Finset Real Filter Asymptotics

lemma sum_inv_primes_dyadic_le {B : ℝ} (hB : 2 ≤ B) :
    ∑ q ∈ (Ioc ⌊B⌋₊ ⌊2 * B⌋₊).filter Nat.Prime, (q : ℝ)⁻¹ ≤ 2 * Real.log 4 / Real.log B := by
  have hB0 : 0 < B := by linarith
  have hlogB : 0 < Real.log B := Real.log_pos (by linarith)
  set Q := (Ioc ⌊B⌋₊ ⌊2 * B⌋₊).filter Nat.Prime with hQ
  have hgt : ∀ q ∈ Q, B < q := fun q hq => by
    simp only [hQ, mem_filter, mem_Ioc] at hq
    exact (Nat.floor_lt hB0.le).mp hq.1.1
  
  have hcard : (Q.card : ℝ) * Real.log B ≤ 2 * B * Real.log 4 := by
    have hθ : ∑ q ∈ Q, Real.log q ≤ Chebyshev.theta (2 * B) := by
      rw [Chebyshev.theta]
      apply sum_le_sum_of_subset_of_nonneg
      · intro q hq
        simp only [hQ, mem_filter, mem_Ioc] at hq ⊢
        exact ⟨⟨by omega, hq.1.2⟩, hq.2⟩
      · intro q _ _
        exact Real.log_natCast_nonneg q
    have hle : (Q.card : ℝ) * Real.log B ≤ ∑ q ∈ Q, Real.log q := by
      rw [← nsmul_eq_mul, ← sum_const]
      exact sum_le_sum fun q hq => Real.log_le_log hB0 (hgt q hq).le
    have := Chebyshev.theta_le_log4_mul_x (x := 2 * B) (by linarith)
    linarith
  calc ∑ q ∈ Q, (q : ℝ)⁻¹ ≤ ∑ _q ∈ Q, B⁻¹ :=
        sum_le_sum fun q hq => inv_anti₀ hB0 (hgt q hq).le
    _ = Q.card * B⁻¹ := by rw [sum_const, nsmul_eq_mul]
    _ ≤ 2 * Real.log 4 / Real.log B := by
        rw [le_div_iff₀ hlogB]
        calc (Q.card : ℝ) * B⁻¹ * Real.log B = (Q.card * Real.log B) * B⁻¹ := by ring
          _ ≤ (2 * B * Real.log 4) * B⁻¹ := by gcongr
          _ = 2 * Real.log 4 := by field_simp

lemma sum_inv_primes_le {A : ℝ} (hA : 2 ≤ A) (J : ℕ) :
    ∑ q ∈ (Ioc ⌊A⌋₊ ⌊A * 2 ^ J⌋₊).filter Nat.Prime, (q : ℝ)⁻¹ ≤
      J * (2 * Real.log 4 / Real.log A) := by
  have hlogA : 0 < Real.log A := Real.log_pos (by linarith)
  induction J with
  | zero => simp
  | succ J ih =>
    have hAJ : A ≤ A * 2 ^ J := le_mul_of_one_le_right (by linarith) (one_le_pow₀ (by norm_num))
    have hmono1 : ⌊A⌋₊ ≤ ⌊A * 2 ^ J⌋₊ := Nat.floor_mono hAJ
    have hmono2 : ⌊A * 2 ^ J⌋₊ ≤ ⌊A * 2 ^ (J + 1)⌋₊ := Nat.floor_mono (by
      rw [pow_succ]; nlinarith [pow_pos (show (0:ℝ) < 2 by norm_num) J])
    rw [sum_filter, ← sum_Ioc_consecutive _ hmono1 hmono2, ← sum_filter, ← sum_filter]
    have hblock := sum_inv_primes_dyadic_le (B := A * 2 ^ J) (by linarith)
    have h2 : 2 * (A * 2 ^ J) = A * 2 ^ (J + 1) := by ring
    rw [h2] at hblock
    have hlog : 2 * Real.log 4 / Real.log (A * 2 ^ J) ≤ 2 * Real.log 4 / Real.log A := by
      have h4 : 0 ≤ 2 * Real.log 4 := by positivity
      exact div_le_div_of_nonneg_left h4 hlogA (Real.log_le_log (by linarith) hAJ)
    push_cast
    linarith

section Estimates

variable {x : ℝ} (hx : Real.exp 256 ≤ x)
include hx

lemma xpos_of_large : 0 < x := lt_of_lt_of_le (Real.exp_pos _) hx

lemma log_ge_of_large : 256 ≤ Real.log x := by
  rw [← Real.log_exp 256]; exact Real.log_le_log (Real.exp_pos _) hx

lemma loglog_le_of_large : Real.log (Real.log x) ≤ Real.log x / 8 := by
  have hL := log_ge_of_large hx
  have hL0 : 0 ≤ Real.log x := by linarith
  have h1 := Real.log_le_rpow_div hL0 (show (0:ℝ) < 1 / 2 by norm_num)
  rw [← Real.sqrt_eq_rpow] at h1
  have hs : 16 ≤ Real.sqrt (Real.log x) := by
    rw [Real.le_sqrt (by norm_num) hL0]; linarith
  have hss : Real.sqrt (Real.log x) * Real.sqrt (Real.log x) = Real.log x :=
    Real.mul_self_sqrt hL0
  have : Real.sqrt (Real.log x) / (1 / 2) ≤ Real.log x / 8 := by nlinarith
  linarith

lemma one_le_loglog_of_large : 1 ≤ Real.log (Real.log x) := by
  have hL := log_ge_of_large hx
  rw [← Real.log_exp 1]
  apply Real.log_le_log (Real.exp_pos _)
  have := Real.exp_one_lt_d9
  linarith

lemma log_div_sqrt_log_of_large :
    Real.log x / 4 ≤ Real.log (Real.sqrt x / Real.log x) := by
  have hx0 := xpos_of_large hx
  have hL := log_ge_of_large hx
  rw [Real.log_div (Real.sqrt_pos.mpr hx0).ne' (by linarith), Real.log_sqrt hx0.le]
  linarith [loglog_le_of_large hx]

lemma log_xi2_of_large : Real.log x / 4 ≤ Real.log (((Real.sqrt (x : ℝ) / Real.log (x : ℝ) ^ 2 : ℝ))) := by
  have hx0 := xpos_of_large hx
  have hL := log_ge_of_large hx
  rw [Real.log_div (Real.sqrt_pos.mpr hx0).ne' (by positivity), Real.log_sqrt hx0.le, Real.log_pow]
  push_cast
  linarith [loglog_le_of_large hx]

lemma two_le_xi2_of_large : 2 ≤ ((Real.sqrt (x : ℝ) / Real.log (x : ℝ) ^ 2 : ℝ)) := by
  have hx0 := xpos_of_large hx
  have hL := log_ge_of_large hx
  have hpos : 0 < ((Real.sqrt (x : ℝ) / Real.log (x : ℝ) ^ 2 : ℝ)) := by beta_reduce; positivity
  have h := log_xi2_of_large hx
  have hlog2 : Real.log 2 < 1 := by
    have := Real.log_two_lt_d9; linarith
  rw [← Real.log_le_log_iff (by norm_num) hpos]
  linarith

end Estimates

lemma primeCountAP_le_of_le_xi3 (hBT : ∀ q : ℕ, 1 ≤ q → ∀ x : ℝ, (q : ℝ) < x → ((((Finset.range (⌊x⌋₊ + 1)).filter fun p => p.Prime ∧ p ≡ 1 [MOD q]).card : ℕ) : ℝ) ≤ 20000 * x / (q.totient * Real.log (x / q))) {x : ℝ} (hx : Real.exp 256 ≤ x) {q : ℕ} (hq : q.Prime)
    (hq3 : (q : ℝ) ≤ ((Real.sqrt (x : ℝ) * Real.log (x : ℝ) : ℝ))) :
    (((((Finset.range (⌊(x : ℝ)⌋₊ + 1)).filter fun pK => pK.Prime ∧ pK ≡ 1 [MOD (q : ℕ)]).card : ℕ)) : ℝ) ≤ 160000 * x / (q * Real.log x) := by
  have hx0 := xpos_of_large hx
  have hL := log_ge_of_large hx
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq.pos
  have hq2 : (2 : ℝ) ≤ q := by exact_mod_cast hq.two_le
  
  have hxq : Real.sqrt x / Real.log x ≤ x / q := by
    rw [div_le_div_iff₀ (by linarith) hq0]
    have hxx : Real.sqrt x * Real.sqrt x = x := Real.mul_self_sqrt hx0.le
    have : Real.sqrt x * q ≤ Real.sqrt x * (Real.sqrt x * Real.log x) :=
      mul_le_mul_of_nonneg_left hq3 (Real.sqrt_nonneg x)
    nlinarith
  have hlogxq : Real.log x / 4 ≤ Real.log (x / q) :=
    (log_div_sqrt_log_of_large hx).trans
      (Real.log_le_log (div_pos (Real.sqrt_pos.mpr hx0) (by linarith)) hxq)
  have hqx : (q : ℝ) < x := by
    have : 0 < Real.log (x / q) := by linarith
    have := (Real.log_pos_iff (by positivity)).mp this
    rwa [one_lt_div hq0] at this
  have hbt := hBT q hq.one_lt.le x hqx
  have htot : (q : ℝ) / 2 ≤ q.totient := by
    rw [Nat.totient_prime hq, Nat.cast_sub hq.one_lt.le]
    push_cast
    linarith
  calc (((((Finset.range (⌊(x : ℝ)⌋₊ + 1)).filter fun pK => pK.Prime ∧ pK ≡ 1 [MOD (q : ℕ)]).card : ℕ)) : ℝ) ≤ 20000 * x / (q.totient * Real.log (x / q)) := hbt
    _ ≤ 20000 * x / ((q / 2) * (Real.log x / 4)) := by
        apply div_le_div_of_nonneg_left (by positivity) (by positivity)
        exact mul_le_mul htot hlogxq (by positivity) (by positivity)
    _ = 160000 * x / (q * Real.log x) := by
        field_simp
        ring

lemma sum_inv_largePrimes_le {x : ℝ} (hx : Real.exp 256 ≤ x) :
    ∑ q ∈ (((Finset.Ioc ⌊((Real.sqrt ((x : ℝ) : ℝ) / Real.log ((x : ℝ) : ℝ) ^ 2 : ℝ))⌋₊ ⌊((Real.sqrt ((x : ℝ) : ℝ) * Real.log ((x : ℝ) : ℝ) : ℝ))⌋₊).filter Nat.Prime : Finset ℕ)), (q : ℝ)⁻¹ ≤ 144 * Real.log (Real.log x) / Real.log x := by
  have hx0 := xpos_of_large hx
  have hL := log_ge_of_large hx
  have hl1 := one_le_loglog_of_large hx
  set L := Real.log x with hLdef
  set l := Real.log L with hldef
  have hA := two_le_xi2_of_large hx
  have hlogA := log_xi2_of_large hx
  have hlog2 := Real.log_two_gt_d9
  set J := ⌈3 * l / Real.log 2⌉₊ with hJ
  
  have hJ1 : 3 * l / Real.log 2 ≤ J := Nat.le_ceil _
  have hpowJ : L ^ 3 ≤ (2 : ℝ) ^ J := by
    have h1 : L ^ 3 = Real.exp (3 * l) := by
      rw [hldef, mul_comm, Real.exp_mul, Real.exp_log (by linarith)]
      norm_cast
    have h2 : (2 : ℝ) ^ J = Real.exp (Real.log 2 * J) := by
      rw [← Real.rpow_natCast, Real.rpow_def_of_pos (by norm_num)]
    rw [h1, h2, Real.exp_le_exp]
    rw [div_le_iff₀ (by linarith)] at hJ1
    linarith
  have hcover : ((Real.sqrt (x : ℝ) * Real.log (x : ℝ) : ℝ)) ≤ ((Real.sqrt (x : ℝ) / Real.log (x : ℝ) ^ 2 : ℝ)) * 2 ^ J := by
    beta_reduce
    have hL2 : 0 < L ^ 2 := by positivity
    rw [div_mul_eq_mul_div, le_div_iff₀ hL2]
    have : Real.sqrt x * L * L ^ 2 = Real.sqrt x * L ^ 3 := by ring
    rw [this]
    exact mul_le_mul_of_nonneg_left hpowJ (Real.sqrt_nonneg x)
  have hsub : (((Finset.Ioc ⌊((Real.sqrt ((x : ℝ) : ℝ) / Real.log ((x : ℝ) : ℝ) ^ 2 : ℝ))⌋₊ ⌊((Real.sqrt ((x : ℝ) : ℝ) * Real.log ((x : ℝ) : ℝ) : ℝ))⌋₊).filter Nat.Prime : Finset ℕ)) ⊆ (Ioc ⌊((Real.sqrt (x : ℝ) / Real.log (x : ℝ) ^ 2 : ℝ))⌋₊ ⌊((Real.sqrt (x : ℝ) / Real.log (x : ℝ) ^ 2 : ℝ)) * 2 ^ J⌋₊).filter Nat.Prime := by
    intro q hq
    simp only [mem_filter, mem_Ioc] at hq ⊢
    exact ⟨⟨hq.1.1, hq.1.2.trans (Nat.floor_mono hcover)⟩, hq.2⟩
  have hJle : (J : ℝ) ≤ 6 * l := by
    have := Nat.ceil_lt_add_one (show 0 ≤ 3 * l / Real.log 2 by positivity)
    rw [← hJ] at this
    have h5 : 3 * l / Real.log 2 ≤ 5 * l := by
      rw [div_le_iff₀ (by linarith)]; nlinarith
    linarith
  have hlog4 : Real.log 4 ≤ 3 := by
    have := Real.log_le_sub_one_of_pos (show (0:ℝ) < 4 by norm_num); linarith
  calc ∑ q ∈ (((Finset.Ioc ⌊((Real.sqrt ((x : ℝ) : ℝ) / Real.log ((x : ℝ) : ℝ) ^ 2 : ℝ))⌋₊ ⌊((Real.sqrt ((x : ℝ) : ℝ) * Real.log ((x : ℝ) : ℝ) : ℝ))⌋₊).filter Nat.Prime : Finset ℕ)), (q : ℝ)⁻¹
      ≤ ∑ q ∈ (Ioc ⌊((Real.sqrt (x : ℝ) / Real.log (x : ℝ) ^ 2 : ℝ))⌋₊ ⌊((Real.sqrt (x : ℝ) / Real.log (x : ℝ) ^ 2 : ℝ)) * 2 ^ J⌋₊).filter Nat.Prime, (q : ℝ)⁻¹ :=
        sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => by positivity
    _ ≤ J * (2 * Real.log 4 / Real.log (((Real.sqrt (x : ℝ) / Real.log (x : ℝ) ^ 2 : ℝ)))) := sum_inv_primes_le hA J
    _ ≤ (6 * l) * (2 * 3 / (L / 4)) := by
        gcongr
        have : 0 < Real.log (((Real.sqrt (x : ℝ) / Real.log (x : ℝ) ^ 2 : ℝ))) := by linarith
        positivity
    _ = 144 * l / L := by
        have : L ≠ 0 := by linarith
        field_simp
        ring

theorem largePrimesSum_le (hBT : ∀ q : ℕ, 1 ≤ q → ∀ x : ℝ, (q : ℝ) < x → ((((Finset.range (⌊x⌋₊ + 1)).filter fun p => p.Prime ∧ p ≡ 1 [MOD q]).card : ℕ) : ℝ) ≤ 20000 * x / (q.totient * Real.log (x / q))) {x : ℝ} (hx : Real.exp 256 ≤ x) :
    (((∑ qK ∈ (((Finset.Ioc ⌊((Real.sqrt (((x : ℝ) : ℝ) : ℝ) / Real.log (((x : ℝ) : ℝ) : ℝ) ^ 2 : ℝ))⌋₊ ⌊((Real.sqrt (((x : ℝ) : ℝ) : ℝ) * Real.log (((x : ℝ) : ℝ) : ℝ) : ℝ))⌋₊).filter Nat.Prime : Finset ℕ)), ((((Finset.range (⌊((x : ℝ) : ℝ)⌋₊ + 1)).filter fun pK => pK.Prime ∧ pK ≡ 1 [MOD (qK : ℕ)]).card : ℕ)) : ℕ)) : ℝ) ≤ 23040000 * x * Real.log (Real.log x) / Real.log x ^ 2 := by
  have hx0 := xpos_of_large hx
  have hL := log_ge_of_large hx
  have hL0 : 0 < Real.log x := by linarith
  rw [Nat.cast_sum]
  calc ∑ q ∈ (((Finset.Ioc ⌊((Real.sqrt ((x : ℝ) : ℝ) / Real.log ((x : ℝ) : ℝ) ^ 2 : ℝ))⌋₊ ⌊((Real.sqrt ((x : ℝ) : ℝ) * Real.log ((x : ℝ) : ℝ) : ℝ))⌋₊).filter Nat.Prime : Finset ℕ)), (((((Finset.range (⌊(x : ℝ)⌋₊ + 1)).filter fun pK => pK.Prime ∧ pK ≡ 1 [MOD (q : ℕ)]).card : ℕ)) : ℝ)
      ≤ ∑ q ∈ (((Finset.Ioc ⌊((Real.sqrt ((x : ℝ) : ℝ) / Real.log ((x : ℝ) : ℝ) ^ 2 : ℝ))⌋₊ ⌊((Real.sqrt ((x : ℝ) : ℝ) * Real.log ((x : ℝ) : ℝ) : ℝ))⌋₊).filter Nat.Prime : Finset ℕ)), 160000 * x / Real.log x * (q : ℝ)⁻¹ := by
        refine sum_le_sum fun q hq => ?_
        simp only [mem_filter, mem_Ioc] at hq
        have hq3 : (q : ℝ) ≤ ((Real.sqrt (x : ℝ) * Real.log (x : ℝ) : ℝ)) := by
          have hxi3 : 0 ≤ ((Real.sqrt (x : ℝ) * Real.log (x : ℝ) : ℝ)) := by beta_reduce; positivity
          exact (Nat.le_floor_iff hxi3).mp hq.1.2
        calc (((((Finset.range (⌊(x : ℝ)⌋₊ + 1)).filter fun pK => pK.Prime ∧ pK ≡ 1 [MOD (q : ℕ)]).card : ℕ)) : ℝ) ≤ 160000 * x / (q * Real.log x) :=
              primeCountAP_le_of_le_xi3 hBT hx hq.2 hq3
          _ = 160000 * x / Real.log x * (q : ℝ)⁻¹ := by
              have : (q : ℝ) ≠ 0 := by exact_mod_cast hq.2.ne_zero
              field_simp
    _ = 160000 * x / Real.log x * ∑ q ∈ (((Finset.Ioc ⌊((Real.sqrt ((x : ℝ) : ℝ) / Real.log ((x : ℝ) : ℝ) ^ 2 : ℝ))⌋₊ ⌊((Real.sqrt ((x : ℝ) : ℝ) * Real.log ((x : ℝ) : ℝ) : ℝ))⌋₊).filter Nat.Prime : Finset ℕ)), (q : ℝ)⁻¹ := by rw [mul_sum]
    _ ≤ 160000 * x / Real.log x * (144 * Real.log (Real.log x) / Real.log x) := by
        gcongr
        exact sum_inv_largePrimes_le hx
    _ = 23040000 * x * Real.log (Real.log x) / Real.log x ^ 2 := by
        field_simp
        ring

lemma div_log_le_primeCounting {x : ℝ} (hx : 64 ≤ x) :
    x / Real.log x ≤ 4 / Real.log 2 * (Nat.primeCounting ⌊x⌋₊ : ℝ) := by
  have hn : 64 ≤ ⌊x⌋₊ := Nat.le_floor (by exact_mod_cast hx)
  have hn4 : (64 : ℝ) ≤ ⌊x⌋₊ := by exact_mod_cast hn
  set n : ℝ := (⌊x⌋₊ : ℝ) with hndef
  have hlogn : 0 < Real.log n := Real.log_pos (by linarith)
  have hlogx : Real.log n ≤ Real.log x := Real.log_le_log (by linarith) (Nat.floor_le (by linarith))
  have hfl : x ≤ 2 * n := by linarith [Nat.lt_floor_add_one x]
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog2' : 0.6931471803 < Real.log 2 := Real.log_two_gt_d9
  have hpsi := Chebyshev.psi_ge ⌊x⌋₊
  have hpsi2 := Chebyshev.psi_le_primeCounting_mul_log ⌊x⌋₊
  
  have hl1 : Real.log (n + 1) ≤ Real.sqrt (n + 1) / (1 / 2) := by
    rw [Real.sqrt_eq_rpow]
    exact Real.log_le_rpow_div (by positivity) (by norm_num)
  have hs0 : 0 ≤ Real.sqrt (n + 1) := Real.sqrt_nonneg _
  have hss : Real.sqrt (n + 1) * Real.sqrt (n + 1) = n + 1 := Real.mul_self_sqrt (by positivity)
  have hs : Real.sqrt (n + 1) ≤ n * Real.log 2 / 4 := by
    have hl2sq : (0.48 : ℝ) ≤ Real.log 2 ^ 2 := by nlinarith
    have hsq : n + 1 ≤ (n * Real.log 2 / 4) ^ 2 := by
      have h1 : (n * Real.log 2 / 4) ^ 2 = n * n * Real.log 2 ^ 2 / 16 := by ring
      have h2 : n * 64 ≤ n * n := mul_le_mul_of_nonneg_left hn4 (by linarith)
      have h3 : n * n * 0.48 ≤ n * n * Real.log 2 ^ 2 :=
        mul_le_mul_of_nonneg_left hl2sq (by positivity)
      rw [h1]
      linarith
    rw [show n * Real.log 2 / 4 = Real.sqrt ((n * Real.log 2 / 4) ^ 2) from
      (Real.sqrt_sq (by positivity)).symm]
    exact Real.sqrt_le_sqrt hsq
  have hpi : n * Real.log 2 / 2 ≤ (Nat.primeCounting ⌊x⌋₊ : ℝ) * Real.log n := by
    have : (↑⌊x⌋₊ : ℝ) * Real.log 2 - Real.log (↑⌊x⌋₊ + 1) ≤
        (Nat.primeCounting ⌊x⌋₊ : ℝ) * Real.log ↑⌊x⌋₊ := hpsi.trans hpsi2
    rw [← hndef] at this
    linarith
  calc x / Real.log x ≤ 2 * n / Real.log n := by
        apply div_le_div₀ (by positivity) hfl hlogn hlogx
    _ ≤ 4 / Real.log 2 * (Nat.primeCounting ⌊x⌋₊ : ℝ) := by
        rw [div_le_iff₀ hlogn]
        calc 2 * n = 4 / Real.log 2 * (n * Real.log 2 / 2) := by field_simp; ring
          _ ≤ 4 / Real.log 2 * ((Nat.primeCounting ⌊x⌋₊ : ℝ) * Real.log n) := by gcongr
          _ = _ := by ring

lemma isLittleO_loglog_div_log_sq :
    (fun x : ℝ => x * Real.log (Real.log x) / Real.log x ^ 2) =o[atTop]
      fun x => x / Real.log x := by
  have h := (Real.isLittleO_log_id_atTop.comp_tendsto Real.tendsto_log_atTop).mul_isBigO
    (isBigO_refl (fun x : ℝ => x / Real.log x ^ 2) atTop)
  refine h.congr' (Eventually.of_forall fun x => ?_) ?_
  · simp only [Function.comp_apply]; ring
  · filter_upwards [eventually_gt_atTop 1] with x hx
    have : Real.log x ≠ 0 := (Real.log_pos hx).ne'
    simp only [Function.comp_apply, id]
    field_simp

theorem largePrimesSum_isLittleO (hBT : ∀ q : ℕ, 1 ≤ q → ∀ x : ℝ, (q : ℝ) < x → ((((Finset.range (⌊x⌋₊ + 1)).filter fun p => p.Prime ∧ p ≡ 1 [MOD q]).card : ℕ) : ℝ) ≤ 20000 * x / (q.totient * Real.log (x / q))) :
    (fun x : ℝ => (((∑ qK ∈ (((Finset.Ioc ⌊((Real.sqrt (((x : ℝ) : ℝ) : ℝ) / Real.log (((x : ℝ) : ℝ) : ℝ) ^ 2 : ℝ))⌋₊ ⌊((Real.sqrt (((x : ℝ) : ℝ) : ℝ) * Real.log (((x : ℝ) : ℝ) : ℝ) : ℝ))⌋₊).filter Nat.Prime : Finset ℕ)), ((((Finset.range (⌊((x : ℝ) : ℝ)⌋₊ + 1)).filter fun pK => pK.Prime ∧ pK ≡ 1 [MOD (qK : ℕ)]).card : ℕ)) : ℕ)) : ℝ)) =o[atTop]
      fun x => (Nat.primeCounting ⌊x⌋₊ : ℝ) := by
  have h1 : (fun x : ℝ => (((∑ qK ∈ (((Finset.Ioc ⌊((Real.sqrt (((x : ℝ) : ℝ) : ℝ) / Real.log (((x : ℝ) : ℝ) : ℝ) ^ 2 : ℝ))⌋₊ ⌊((Real.sqrt (((x : ℝ) : ℝ) : ℝ) * Real.log (((x : ℝ) : ℝ) : ℝ) : ℝ))⌋₊).filter Nat.Prime : Finset ℕ)), ((((Finset.range (⌊((x : ℝ) : ℝ)⌋₊ + 1)).filter fun pK => pK.Prime ∧ pK ≡ 1 [MOD (qK : ℕ)]).card : ℕ)) : ℕ)) : ℝ)) =O[atTop]
      fun x => x * Real.log (Real.log x) / Real.log x ^ 2 := by
    refine IsBigO.of_bound 23040000 ?_
    filter_upwards [eventually_ge_atTop (Real.exp 256)] with x hx
    have hx0 := xpos_of_large hx
    have hL := log_ge_of_large hx
    have hl := one_le_loglog_of_large hx
    rw [Real.norm_of_nonneg (Nat.cast_nonneg _), Real.norm_of_nonneg (by positivity)]
    have := largePrimesSum_le hBT hx
    calc (((∑ qK ∈ (((Finset.Ioc ⌊((Real.sqrt (((x : ℝ) : ℝ) : ℝ) / Real.log (((x : ℝ) : ℝ) : ℝ) ^ 2 : ℝ))⌋₊ ⌊((Real.sqrt (((x : ℝ) : ℝ) : ℝ) * Real.log (((x : ℝ) : ℝ) : ℝ) : ℝ))⌋₊).filter Nat.Prime : Finset ℕ)), ((((Finset.range (⌊((x : ℝ) : ℝ)⌋₊ + 1)).filter fun pK => pK.Prime ∧ pK ≡ 1 [MOD (qK : ℕ)]).card : ℕ)) : ℕ)) : ℝ) ≤ 23040000 * x * Real.log (Real.log x) / Real.log x ^ 2 := this
      _ = _ := by ring
  have h3 : (fun x : ℝ => x / Real.log x) =O[atTop]
      fun x => (Nat.primeCounting ⌊x⌋₊ : ℝ) := by
    refine IsBigO.of_bound (4 / Real.log 2) ?_
    filter_upwards [eventually_ge_atTop 64] with x hx
    have hlogx : 0 < Real.log x := Real.log_pos (by linarith)
    rw [Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (Nat.cast_nonneg _)]
    exact div_log_le_primeCounting hx
  exact h1.trans_isLittleO (isLittleO_loglog_div_log_sq.trans_isBigO h3)

open Classical in

lemma largePrimeCount_le_largePrimesSum (a : ℤ) (x : ℕ) :
    ((((Finset.range (x : ℕ)).filter fun pK : ℕ => pK.Prime ∧ ¬ (pK : ℤ) ∣ (a : ℤ) ∧ ∃ qK : ℕ, qK.Prime ∧ ((Real.sqrt ((x : ℕ) : ℝ) / Real.log ((x : ℕ) : ℝ) ^ 2 : ℝ)) < qK ∧ (qK : ℝ) ≤ ((Real.sqrt ((x : ℕ) : ℝ) * Real.log ((x : ℕ) : ℝ) : ℝ)) ∧ qK ∣ pK - 1 ∧ ((a : ℤ) : ZMod pK) ^ ((pK - 1) / qK) = 1).card : ℕ)) ≤ ((∑ qK ∈ (((Finset.Ioc ⌊((Real.sqrt (((x : ℝ) : ℝ) : ℝ) / Real.log (((x : ℝ) : ℝ) : ℝ) ^ 2 : ℝ))⌋₊ ⌊((Real.sqrt (((x : ℝ) : ℝ) : ℝ) * Real.log (((x : ℝ) : ℝ) : ℝ) : ℝ))⌋₊).filter Nat.Prime : Finset ℕ)), ((((Finset.range (⌊((x : ℝ) : ℝ)⌋₊ + 1)).filter fun pK => pK.Prime ∧ pK ≡ 1 [MOD (qK : ℕ)]).card : ℕ)) : ℕ)) := by
  classical
  beta_reduce
  refine (card_le_card ?_).trans card_biUnion_le
  intro p hp
  simp only [mem_filter, mem_range] at hp
  obtain ⟨hpx, hp, -, q, hq, hq2, hq3, hqd, -⟩ := hp
  simp only [mem_biUnion, mem_filter, mem_Ioc, mem_range, Nat.floor_natCast]
  have hxi2 : 0 ≤ ((Real.sqrt (x : ℝ) / Real.log (x : ℝ) ^ 2 : ℝ)) := by beta_reduce; positivity
  have hxi3 : 0 ≤ ((Real.sqrt (x : ℝ) * Real.log (x : ℝ) : ℝ)) := le_trans (Nat.cast_nonneg q) hq3
  refine ⟨q, ⟨⟨(Nat.floor_lt hxi2).mpr hq2, Nat.le_floor hq3⟩, hq⟩, by omega, hp, ?_⟩
  exact ((Nat.modEq_iff_dvd' hp.one_lt.le).mpr hqd).symm

theorem largePrimeCount_le (hBT : ∀ q : ℕ, 1 ≤ q → ∀ x : ℝ, (q : ℝ) < x → ((((Finset.range (⌊x⌋₊ + 1)).filter fun p => p.Prime ∧ p ≡ 1 [MOD q]).card : ℕ) : ℝ) ≤ 20000 * x / (q.totient * Real.log (x / q))) (a : ℤ) {x : ℕ} (hx : Real.exp 256 ≤ x) :
    (((((Finset.range (x : ℕ)).filter fun pK : ℕ => pK.Prime ∧ ¬ (pK : ℤ) ∣ (a : ℤ) ∧ ∃ qK : ℕ, qK.Prime ∧ ((Real.sqrt ((x : ℕ) : ℝ) / Real.log ((x : ℕ) : ℝ) ^ 2 : ℝ)) < qK ∧ (qK : ℝ) ≤ ((Real.sqrt ((x : ℕ) : ℝ) * Real.log ((x : ℕ) : ℝ) : ℝ)) ∧ qK ∣ pK - 1 ∧ ((a : ℤ) : ZMod pK) ^ ((pK - 1) / qK) = 1).card : ℕ)) : ℝ) ≤ 23040000 * x * Real.log (Real.log x) / Real.log x ^ 2 :=
  (Nat.cast_le.mpr (largePrimeCount_le_largePrimesSum a x)).trans (largePrimesSum_le hBT hx)

theorem largePrimeCount_isLittleO (hBT : ∀ q : ℕ, 1 ≤ q → ∀ x : ℝ, (q : ℝ) < x → ((((Finset.range (⌊x⌋₊ + 1)).filter fun p => p.Prime ∧ p ≡ 1 [MOD q]).card : ℕ) : ℝ) ≤ 20000 * x / (q.totient * Real.log (x / q))) (a : ℤ) :
    (fun x : ℕ => (((((Finset.range (x : ℕ)).filter fun pK : ℕ => pK.Prime ∧ ¬ (pK : ℤ) ∣ (a : ℤ) ∧ ∃ qK : ℕ, qK.Prime ∧ ((Real.sqrt ((x : ℕ) : ℝ) / Real.log ((x : ℕ) : ℝ) ^ 2 : ℝ)) < qK ∧ (qK : ℝ) ≤ ((Real.sqrt ((x : ℕ) : ℝ) * Real.log ((x : ℕ) : ℝ) : ℝ)) ∧ qK ∣ pK - 1 ∧ ((a : ℤ) : ZMod pK) ^ ((pK - 1) / qK) = 1).card : ℕ)) : ℝ)) =o[atTop]
      fun x => (Nat.primeCounting x : ℝ) := by
  have h := (largePrimesSum_isLittleO hBT).comp_tendsto tendsto_natCast_atTop_atTop
  simp only [Function.comp_def, Nat.floor_natCast] at h
  refine IsBigO.trans_isLittleO (IsBigO.of_bound 1 (Eventually.of_forall fun x => ?_)) h
  rw [Real.norm_of_nonneg (Nat.cast_nonneg _), Real.norm_of_nonneg (Nat.cast_nonneg _), one_mul]
  have hle := largePrimeCount_le_largePrimesSum a x
  simp only [Nat.floor_natCast] at hle
  exact_mod_cast hle

end Artin

end

section

namespace Artin

open ArtinPrimitiveRootsConjecture Finset Filter Asymptotics
open scoped ArithmeticFunction.Moebius Topology

lemma totient_sq_aux (n : ℕ) :
    n ≤ 2 * Nat.totient n ^ 2 ∧ (n % 2 = 1 → n ≤ Nat.totient n ^ 2) := by
  induction n using Nat.recOnPosPrimePosCoprime with
  | prime_pow p k hp hk =>
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    rw [Nat.totient_prime_pow_succ hp]
    have ht : 1 ≤ p ^ j := Nat.one_le_pow _ _ hp.pos
    rcases hp.eq_two_or_odd' with rfl | hodd
    · refine ⟨?_, fun h => ?_⟩
      · rw [pow_succ]
        norm_num
        nlinarith
      · have : 2 ^ (j + 1) % 2 = 0 := by rw [pow_succ]; simp
        omega
    · have hp3 : 3 ≤ p := by
        obtain ⟨m, hm⟩ := hodd
        have := hp.two_le
        omega
      obtain ⟨r, rfl⟩ : ∃ r, p = r + 1 := ⟨p - 1, by omega⟩
      simp only [Nat.add_sub_cancel]
      have key : (r + 1) ^ (j + 1) ≤ ((r + 1) ^ j * r) ^ 2 := by
        have h1 : r + 1 ≤ r * r := by nlinarith
        calc (r + 1) ^ (j + 1) = (r + 1) ^ j * (r + 1) := pow_succ _ _
          _ ≤ (r + 1) ^ j * (r * r) := Nat.mul_le_mul_left _ h1
          _ ≤ ((r + 1) ^ j * (r + 1) ^ j) * (r * r) :=
              Nat.mul_le_mul_right _ (Nat.le_mul_of_pos_right _ ht)
          _ = ((r + 1) ^ j * r) ^ 2 := by ring
      exact ⟨key.trans (by omega), fun _ => key⟩
  | zero => simp
  | one => simp
  | coprime a b ha hb hab iha ihb =>
    rw [Nat.totient_mul hab, mul_pow]
    have hmod := Nat.mul_mod a b 2
    have hnot : ¬ (a % 2 = 0 ∧ b % 2 = 0) := by
      rintro ⟨h1, h2⟩
      have := Nat.dvd_gcd (Nat.dvd_of_mod_eq_zero h1) (Nat.dvd_of_mod_eq_zero h2)
      rw [Nat.Coprime.gcd_eq_one hab] at this
      exact absurd (Nat.dvd_one.mp this) (by norm_num)
    rcases Nat.mod_two_eq_zero_or_one a with ha2 | ha2 <;>
      rcases Nat.mod_two_eq_zero_or_one b with hb2 | hb2
    · exact absurd ⟨ha2, hb2⟩ hnot
    · refine ⟨?_, fun h => ?_⟩
      · calc a * b ≤ (2 * Nat.totient a ^ 2) * Nat.totient b ^ 2 :=
            Nat.mul_le_mul iha.1 (ihb.2 hb2)
          _ = _ := by ring
      · rw [hmod, ha2] at h; simp at h
    · refine ⟨?_, fun h => ?_⟩
      · calc a * b ≤ Nat.totient a ^ 2 * (2 * Nat.totient b ^ 2) :=
            Nat.mul_le_mul (iha.2 ha2) ihb.1
          _ = _ := by ring
      · rw [hmod, hb2] at h; simp at h
    · have h := Nat.mul_le_mul (iha.2 ha2) (ihb.2 hb2)
      exact ⟨h.trans (by omega), fun _ => h⟩

lemma le_two_mul_totient_sq (n : ℕ) : n ≤ 2 * Nat.totient n ^ 2 := (totient_sq_aux n).1

lemma invKTot_nonneg (k : ℕ) : 0 ≤ ((1 / (((k : ℕ) : ℝ) * Nat.totient (k : ℕ)) : ℝ)) := by beta_reduce; positivity

lemma invKTot_le (k : ℕ) : ((1 / (((k : ℕ) : ℝ) * Nat.totient (k : ℕ)) : ℝ)) ≤ 2 * ((k : ℝ) ^ (3 / 2 : ℝ))⁻¹ := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have htR : (0 : ℝ) < Nat.totient k := by exact_mod_cast Nat.totient_pos.mpr hk
  have h32 : (k : ℝ) ^ (3 / 2 : ℝ) = k * Real.sqrt k := by
    rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add hkR, Real.rpow_one,
      Real.sqrt_eq_rpow]
  have hcast : (k : ℝ) ≤ 2 * (Nat.totient k : ℝ) ^ 2 := by
    exact_mod_cast le_two_mul_totient_sq k
  have hsq : Real.sqrt k ≤ 2 * Nat.totient k :=
    Real.sqrt_le_iff.mpr ⟨by positivity, by nlinarith⟩
  rw [h32, ← div_eq_mul_inv, div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [mul_le_mul_of_nonneg_left hsq hkR.le]

lemma summable_invKTot : Summable (fun (kF : ℕ) => ((1 / ((kF : ℝ) * Nat.totient kF) : ℝ))) :=
  Summable.of_nonneg_of_le invKTot_nonneg invKTot_le
    ((Real.summable_nat_rpow_inv.mpr (by norm_num)).mul_left 2)

lemma inv_kummerDegree_le {a : ℤ} {c : ℝ} (hc : 0 < c)
    (hK : ∀ k : ℕ, Squarefree k → 0 < k →
      ((k : ℝ) * (Nat.totient k : ℝ)) ≤ c * ((Module.finrank ℚ (Polynomial.X ^ (k : ℕ) - Polynomial.C ((a : ℤ) : ℚ)).SplittingField : ℕ) : ℝ))
    {k : ℕ} (hsq : Squarefree k) (hk : 0 < k) :
    0 < ((Module.finrank ℚ (Polynomial.X ^ (k : ℕ) - Polynomial.C ((a : ℤ) : ℚ)).SplittingField : ℕ) : ℝ) ∧ 1 / ((Module.finrank ℚ (Polynomial.X ^ (k : ℕ) - Polynomial.C ((a : ℤ) : ℚ)).SplittingField : ℕ) : ℝ) ≤ c * ((1 / (((k : ℕ) : ℝ) * Nat.totient (k : ℕ)) : ℝ)) := by
  have hkt : (0 : ℝ) < k * Nat.totient k := by
    have : (0 : ℝ) < k := by exact_mod_cast hk
    have : (0 : ℝ) < Nat.totient k := by exact_mod_cast Nat.totient_pos.mpr hk
    positivity
  have hD := hK k hsq hk
  have hDpos : (0 : ℝ) < (Module.finrank ℚ (Polynomial.X ^ (k : ℕ) - Polynomial.C ((a : ℤ) : ℚ)).SplittingField : ℕ) := by
    by_contra hneg
    push Not at hneg
    nlinarith
  refine ⟨hDpos, ?_⟩
  rw [mul_one_div, div_le_div_iff₀ hDpos hkt]
  linarith

theorem summable_moebius_div_kummerDegree (a : ℤ) (hK1 : (∃ c : ℝ, 0 < c ∧ ∀ kK : ℕ, Squarefree kK → 0 < kK → ((kK : ℝ) * (Nat.totient kK : ℝ)) ≤ c * ((Module.finrank ℚ (Polynomial.X ^ (kK : ℕ) - Polynomial.C (((a : ℤ) : ℤ) : ℚ)).SplittingField : ℕ) : ℝ))) :
    Summable fun k : ℕ => (μ k : ℝ) / ((Module.finrank ℚ (Polynomial.X ^ (k : ℕ) - Polynomial.C ((a : ℤ) : ℚ)).SplittingField : ℕ) : ℝ) := by
  obtain ⟨c, hc, hK⟩ := hK1
  refine Summable.of_norm_bounded (summable_invKTot.mul_left c) fun k => ?_
  rw [Real.norm_eq_abs]
  beta_reduce
  by_cases hsq : Squarefree k
  · rcases Nat.eq_zero_or_pos k with hk0 | hk
    · have hmu0 : (μ k : ℝ) = 0 := by rw [hk0]; simp
      rw [hmu0, zero_div, abs_zero]
      exact mul_nonneg hc.le (invKTot_nonneg k)
    obtain ⟨hDpos, hle⟩ := inv_kummerDegree_le hc hK hsq hk
    have hmu : |(μ k : ℝ)| ≤ 1 := by exact_mod_cast ArithmeticFunction.abs_moebius_le_one
    rw [abs_div, abs_of_pos hDpos]
    exact le_trans (div_le_div_of_nonneg_right hmu hDpos.le) hle
  · rw [ArithmeticFunction.moebius_eq_zero_of_not_squarefree hsq, Int.cast_zero, zero_div,
      abs_zero]
    exact mul_nonneg hc.le (invKTot_nonneg k)

lemma tendsto_tailInvKTot : Tendsto (fun (nF : ℕ) => ((∑' kK : ℕ, ((1 / (((kK : ℕ) : ℝ) * Nat.totient (kK : ℕ)) : ℝ)) - ∑ kK ∈ Finset.range nF, ((1 / (((kK : ℕ) : ℝ) * Nat.totient (kK : ℕ)) : ℝ)) : ℝ))) atTop (𝓝 0) := by
  have h := (tendsto_const_nhds (x := ∑' k, ((1 / (((k : ℕ) : ℝ) * Nat.totient (k : ℕ)) : ℝ)))).sub
    summable_invKTot.hasSum.tendsto_sum_nat
  rw [sub_self] at h
  exact h

lemma sum_le_tailInvKTot (s : Finset ℕ) (n : ℕ) (hs : ∀ k ∈ s, n ≤ k) :
    ∑ k ∈ s, ((1 / (((k : ℕ) : ℝ) * Nat.totient (k : ℕ)) : ℝ)) ≤ ((∑' kK : ℕ, ((1 / (((kK : ℕ) : ℝ) * Nat.totient (kK : ℕ)) : ℝ)) - ∑ kK ∈ Finset.range (n : ℕ), ((1 / (((kK : ℕ) : ℝ) * Nat.totient (kK : ℕ)) : ℝ)) : ℝ)) := by
  have hdisj : Disjoint s (range n) := by
    rw [Finset.disjoint_left]
    intro k hk hk'
    have := hs k hk
    rw [mem_range] at hk'
    omega
  have := summable_invKTot.sum_le_tsum (s ∪ range n) (fun k _ => invKTot_nonneg k)
  rw [sum_union hdisj] at this
  beta_reduce
  linarith

lemma tendsto_sum_divisors_primorial {f : ℕ → ℝ} (hf : Summable f)
    (hf0 : ∀ k, ¬ Squarefree k → f k = 0) (hf00 : f 0 = 0) :
    Tendsto (fun ξ : ℕ => ∑ k ∈ (primorial ξ).divisors, f k) atTop (𝓝 (∑' k, f k)) := by
  have hT : Tendsto (fun ξ : ℕ => (primorial ξ).divisors ∪ range ξ) atTop atTop :=
    tendsto_atTop_mono (fun ξ => subset_union_right) tendsto_finset_range
  have hS : Tendsto (fun s : Finset ℕ => ∑ k ∈ s, f k) atTop (𝓝 (∑' k, f k)) := hf.hasSum
  refine (hS.comp hT).congr fun ξ => ?_
  simp only [Function.comp]
  refine (sum_subset subset_union_left fun k hk hk' => ?_).symm
  have hkξ : k < ξ := by
    rcases mem_union.mp hk with h | h
    · exact absurd h hk'
    · exact mem_range.mp h
  rcases Nat.eq_zero_or_pos k with rfl | hk0
  · exact hf00
  by_cases hsq : Squarefree k
  · exfalso
    refine hk' (Nat.mem_divisors.mpr ⟨?_, primorial_ne_zero _⟩)
    exact hsq.dvd_primorial.trans (primorial_dvd_primorial hkξ.le)
  · exact hf0 k hsq

theorem siftedCount_le (a : ℤ) (ξ x : ℕ) :
    ((((Finset.range (x : ℕ)).filter fun pK : ℕ => pK.Prime ∧ ¬ (pK : ℤ) ∣ (a : ℤ) ∧ ∀ qK ∈ ((Nat.primesLE ξ) : Finset ℕ), ¬ (qK ∣ pK - 1 ∧ ((a : ℤ) : ZMod pK) ^ ((pK - 1) / qK) = 1)).card : ℕ)) ≤ ((((Finset.range (x : ℕ)).filter fun pK : ℕ => pK.Prime ∧ orderOf ((a : ℤ) : ZMod pK) = pK - 1).card : ℕ)) +
      ∑ q ∈ (((Finset.Ioc (ξ : ℕ) ⌊((Real.sqrt ((x : ℕ) : ℝ) / Real.log ((x : ℕ) : ℝ) ^ 2 : ℝ))⌋₊).filter Nat.Prime : Finset ℕ)), ((((Finset.range (x : ℕ)).filter fun pK : ℕ => pK.Prime ∧ ¬ (pK : ℤ) ∣ (a : ℤ) ∧ (q : ℕ) ∣ pK - 1 ∧ ((a : ℤ) : ZMod pK) ^ ((pK - 1) / (q : ℕ)) = 1).card : ℕ)) + ((((Finset.range (x : ℕ)).filter fun pK : ℕ => pK.Prime ∧ ¬ (pK : ℤ) ∣ (a : ℤ) ∧ ∃ qK : ℕ, qK.Prime ∧ ((Real.sqrt ((x : ℕ) : ℝ) / Real.log ((x : ℕ) : ℝ) ^ 2 : ℝ)) < qK ∧ (qK : ℝ) ≤ ((Real.sqrt ((x : ℕ) : ℝ) * Real.log ((x : ℕ) : ℝ) : ℝ)) ∧ qK ∣ pK - 1 ∧ ((a : ℤ) : ZMod pK) ^ ((pK - 1) / qK) = 1).card : ℕ)) + ((((Finset.range (x : ℕ)).filter fun pK : ℕ => pK.Prime ∧ ¬ (pK : ℤ) ∣ (a : ℤ) ∧ ∃ qK : ℕ, qK.Prime ∧ Real.sqrt (x : ℕ) * Real.log (x : ℕ) < qK ∧ qK ∣ pK - 1 ∧ ((a : ℤ) : ZMod pK) ^ ((pK - 1) / qK) = 1).card : ℕ)) := by
  classical
  set A := (range x).filter fun p : ℕ => p.Prime ∧ orderOf (a : ZMod p) = p - 1
  set B := ((((Finset.Ioc (ξ : ℕ) ⌊((Real.sqrt ((x : ℕ) : ℝ) / Real.log ((x : ℕ) : ℝ) ^ 2 : ℝ))⌋₊).filter Nat.Prime : Finset ℕ))).biUnion fun q =>
    (range x).filter fun p : ℕ => p.Prime ∧ ¬ (p : ℤ) ∣ a ∧ q ∣ p - 1 ∧
      (a : ZMod p) ^ ((p - 1) / q) = 1
  set Cs := (range x).filter fun p : ℕ => p.Prime ∧ ¬ (p : ℤ) ∣ a ∧
    ∃ q : ℕ, q.Prime ∧ ((Real.sqrt (x : ℝ) / Real.log (x : ℝ) ^ 2 : ℝ)) < q ∧ (q : ℝ) ≤ ((Real.sqrt (x : ℝ) * Real.log (x : ℝ) : ℝ)) ∧ q ∣ p - 1 ∧
      (a : ZMod p) ^ ((p - 1) / q) = 1
  set D := (range x).filter fun p : ℕ => p.Prime ∧ ¬ (p : ℤ) ∣ a ∧
    ∃ q : ℕ, q.Prime ∧ Real.sqrt x * Real.log x < q ∧ q ∣ p - 1 ∧
      (a : ZMod p) ^ ((p - 1) / q) = 1
  have key : ((range x).filter fun p : ℕ => p.Prime ∧ ¬ (p : ℤ) ∣ a ∧
      ∀ q ∈ Nat.primesLE ξ, ¬ (q ∣ p - 1 ∧ (a : ZMod p) ^ ((p - 1) / q) = 1)) ⊆
      A ∪ B ∪ Cs ∪ D := by
    intro p hp
    simp only [Finset.mem_filter, Finset.mem_range] at hp
    obtain ⟨hpx, hp, hpa, hsift⟩ := hp
    by_cases hord : orderOf (a : ZMod p) = p - 1
    · refine mem_union_left _ (mem_union_left _ (mem_union_left _ ?_))
      simp [A, hpx, hp, hord]
    · have := mt (orderOf_eq_sub_one_iff hp hpa).mpr hord
      push Not at this
      obtain ⟨q, hq, hqd, heq⟩ := this
      have hqp := Nat.le_of_dvd (Nat.sub_pos_of_lt hp.one_lt) hqd
      have hξq : ξ < q := by
        by_contra hle
        exact hsift q (Nat.mem_primesLE.mpr ⟨by omega, hq⟩) ⟨hqd, heq⟩
      by_cases h2 : (q : ℝ) ≤ ((Real.sqrt (x : ℝ) / Real.log (x : ℝ) ^ 2 : ℝ))
      · refine mem_union_left _ (mem_union_left _ (mem_union_right _ ?_))
        simp only [B, mem_biUnion, mem_filter, mem_Ioc, mem_range]
        exact ⟨q, ⟨⟨hξq, Nat.le_floor h2⟩, hq⟩, hpx, hp, hpa, hqd, heq⟩
      · push Not at h2
        by_cases h3 : (q : ℝ) ≤ ((Real.sqrt (x : ℝ) * Real.log (x : ℝ) : ℝ))
        · refine mem_union_left _ (mem_union_right _ ?_)
          simp only [Cs, mem_filter, mem_range]
          exact ⟨hpx, hp, hpa, q, hq, h2, h3, hqd, heq⟩
        · push Not at h3
          refine mem_union_right _ ?_
          simp only [D, mem_filter, mem_range]
          exact ⟨hpx, hp, hpa, q, hq, h3, hqd, heq⟩
  have hB : B.card ≤ ∑ q ∈ (((Finset.Ioc (ξ : ℕ) ⌊((Real.sqrt ((x : ℕ) : ℝ) / Real.log ((x : ℕ) : ℝ) ^ 2 : ℝ))⌋₊).filter Nat.Prime : Finset ℕ)), ((((Finset.range (x : ℕ)).filter fun pK : ℕ => pK.Prime ∧ ¬ (pK : ℤ) ∣ (a : ℤ) ∧ (q : ℕ) ∣ pK - 1 ∧ ((a : ℤ) : ZMod pK) ^ ((pK - 1) / (q : ℕ)) = 1).card : ℕ)) := by
    refine card_biUnion_le.trans (le_of_eq ?_)
    rfl
  have hC : Cs.card = ((((Finset.range (x : ℕ)).filter fun pK : ℕ => pK.Prime ∧ ¬ (pK : ℤ) ∣ (a : ℤ) ∧ ∃ qK : ℕ, qK.Prime ∧ ((Real.sqrt ((x : ℕ) : ℝ) / Real.log ((x : ℕ) : ℝ) ^ 2 : ℝ)) < qK ∧ (qK : ℝ) ≤ ((Real.sqrt ((x : ℕ) : ℝ) * Real.log ((x : ℕ) : ℝ) : ℝ)) ∧ qK ∣ pK - 1 ∧ ((a : ℤ) : ZMod pK) ^ ((pK - 1) / qK) = 1).card : ℕ)) := by
    rfl
  have hD : D.card = ((((Finset.range (x : ℕ)).filter fun pK : ℕ => pK.Prime ∧ ¬ (pK : ℤ) ∣ (a : ℤ) ∧ ∃ qK : ℕ, qK.Prime ∧ Real.sqrt (x : ℕ) * Real.log (x : ℕ) < qK ∧ qK ∣ pK - 1 ∧ ((a : ℤ) : ZMod pK) ^ ((pK - 1) / qK) = 1).card : ℕ)) := by
    rfl
  beta_reduce
  calc _ ≤ (A ∪ B ∪ Cs ∪ D).card := card_le_card key
    _ ≤ A.card + B.card + Cs.card + D.card := by
        refine (card_union_le _ _).trans (Nat.add_le_add_right ?_ _)
        refine (card_union_le _ _).trans (Nat.add_le_add_right ?_ _)
        exact card_union_le _ _
    _ ≤ _ := by
        rw [hC, hD]
        have hA : A.card = ((((Finset.range (x : ℕ)).filter fun pK : ℕ => pK.Prime ∧ orderOf ((a : ℤ) : ZMod pK) = pK - 1).card : ℕ)) := rfl
        omega

lemma abs_primRootCount_sub_le (a : ℤ) (ξ x : ℕ) :
    |(((((Finset.range (x : ℕ)).filter fun pK : ℕ => pK.Prime ∧ orderOf ((a : ℤ) : ZMod pK) = pK - 1).card : ℕ)) : ℝ) - ∑ k ∈ (primorial ξ).divisors, (μ k : ℝ) * ((((Finset.range (x : ℕ)).filter fun pK : ℕ => pK.Prime ∧ ¬ (pK : ℤ) ∣ (a : ℤ) ∧ (k : ℕ) ∣ pK - 1 ∧ ((a : ℤ) : ZMod pK) ^ ((pK - 1) / (k : ℕ)) = 1).card : ℕ))| ≤
      (∑ q ∈ (((Finset.Ioc (ξ : ℕ) ⌊((Real.sqrt ((x : ℕ) : ℝ) / Real.log ((x : ℕ) : ℝ) ^ 2 : ℝ))⌋₊).filter Nat.Prime : Finset ℕ)), (((((Finset.range (x : ℕ)).filter fun pK : ℕ => pK.Prime ∧ ¬ (pK : ℤ) ∣ (a : ℤ) ∧ (q : ℕ) ∣ pK - 1 ∧ ((a : ℤ) : ZMod pK) ^ ((pK - 1) / (q : ℕ)) = 1).card : ℕ)) : ℝ)) + ((((Finset.range (x : ℕ)).filter fun pK : ℕ => pK.Prime ∧ ¬ (pK : ℤ) ∣ (a : ℤ) ∧ ∃ qK : ℕ, qK.Prime ∧ ((Real.sqrt ((x : ℕ) : ℝ) / Real.log ((x : ℕ) : ℝ) ^ 2 : ℝ)) < qK ∧ (qK : ℝ) ≤ ((Real.sqrt ((x : ℕ) : ℝ) * Real.log ((x : ℕ) : ℝ) : ℝ)) ∧ qK ∣ pK - 1 ∧ ((a : ℤ) : ZMod pK) ^ ((pK - 1) / qK) = 1).card : ℕ)) +
        ((((Finset.range (x : ℕ)).filter fun pK : ℕ => pK.Prime ∧ ¬ (pK : ℤ) ∣ (a : ℤ) ∧ ∃ qK : ℕ, qK.Prime ∧ Real.sqrt (x : ℕ) * Real.log (x : ℕ) < qK ∧ qK ∣ pK - 1 ∧ ((a : ℤ) : ZMod pK) ^ ((pK - 1) / qK) = 1).card : ℕ)) := by
  have h1 := primRootCount_le_sum_moebius a ξ x
  have h2 := sum_moebius_kummerCount a (Nat.primesLE ξ)
    (fun q hq => (Nat.mem_primesLE.mp hq).2) x
  have h3 := siftedCount_le a ξ x
  rw [← primorial_eq_prod_primesLE] at h1 h2
  have h1' : (((((Finset.range (x : ℕ)).filter fun pK : ℕ => pK.Prime ∧ orderOf ((a : ℤ) : ZMod pK) = pK - 1).card : ℕ)) : ℝ) ≤
      ∑ k ∈ (primorial ξ).divisors, (μ k : ℝ) * ((((Finset.range (x : ℕ)).filter fun pK : ℕ => pK.Prime ∧ ¬ (pK : ℤ) ∣ (a : ℤ) ∧ (k : ℕ) ∣ pK - 1 ∧ ((a : ℤ) : ZMod pK) ^ ((pK - 1) / (k : ℕ)) = 1).card : ℕ)) := by
    have := (Int.cast_le (R := ℝ)).mpr h1
    push_cast at this
    exact this
  have h2' : ∑ k ∈ (primorial ξ).divisors, (μ k : ℝ) * ((((Finset.range (x : ℕ)).filter fun pK : ℕ => pK.Prime ∧ ¬ (pK : ℤ) ∣ (a : ℤ) ∧ (k : ℕ) ∣ pK - 1 ∧ ((a : ℤ) : ZMod pK) ^ ((pK - 1) / (k : ℕ)) = 1).card : ℕ)) =
      ((((Finset.range (x : ℕ)).filter fun pK : ℕ => pK.Prime ∧ ¬ (pK : ℤ) ∣ (a : ℤ) ∧ ∀ qK ∈ ((Nat.primesLE ξ) : Finset ℕ), ¬ (qK ∣ pK - 1 ∧ ((a : ℤ) : ZMod pK) ^ ((pK - 1) / qK) = 1)).card : ℕ)) := by
    have := congrArg (Int.cast (R := ℝ)) h2
    push_cast at this
    exact this
  have h3' : (((((Finset.range (x : ℕ)).filter fun pK : ℕ => pK.Prime ∧ ¬ (pK : ℤ) ∣ (a : ℤ) ∧ ∀ qK ∈ ((Nat.primesLE ξ) : Finset ℕ), ¬ (qK ∣ pK - 1 ∧ ((a : ℤ) : ZMod pK) ^ ((pK - 1) / qK) = 1)).card : ℕ)) : ℝ) ≤ ((((Finset.range (x : ℕ)).filter fun pK : ℕ => pK.Prime ∧ orderOf ((a : ℤ) : ZMod pK) = pK - 1).card : ℕ)) +
      (∑ q ∈ (((Finset.Ioc (ξ : ℕ) ⌊((Real.sqrt ((x : ℕ) : ℝ) / Real.log ((x : ℕ) : ℝ) ^ 2 : ℝ))⌋₊).filter Nat.Prime : Finset ℕ)), (((((Finset.range (x : ℕ)).filter fun pK : ℕ => pK.Prime ∧ ¬ (pK : ℤ) ∣ (a : ℤ) ∧ (q : ℕ) ∣ pK - 1 ∧ ((a : ℤ) : ZMod pK) ^ ((pK - 1) / (q : ℕ)) = 1).card : ℕ)) : ℝ)) + ((((Finset.range (x : ℕ)).filter fun pK : ℕ => pK.Prime ∧ ¬ (pK : ℤ) ∣ (a : ℤ) ∧ ∃ qK : ℕ, qK.Prime ∧ ((Real.sqrt ((x : ℕ) : ℝ) / Real.log ((x : ℕ) : ℝ) ^ 2 : ℝ)) < qK ∧ (qK : ℝ) ≤ ((Real.sqrt ((x : ℕ) : ℝ) * Real.log ((x : ℕ) : ℝ) : ℝ)) ∧ qK ∣ pK - 1 ∧ ((a : ℤ) : ZMod pK) ^ ((pK - 1) / qK) = 1).card : ℕ)) +
        ((((Finset.range (x : ℕ)).filter fun pK : ℕ => pK.Prime ∧ ¬ (pK : ℤ) ∣ (a : ℤ) ∧ ∃ qK : ℕ, qK.Prime ∧ Real.sqrt (x : ℕ) * Real.log (x : ℕ) < qK ∧ qK ∣ pK - 1 ∧ ((a : ℤ) : ZMod pK) ^ ((pK - 1) / qK) = 1).card : ℕ)) := by
    have h3r := (Nat.cast_le (α := ℝ)).mpr h3
    rw [Nat.cast_add, Nat.cast_add, Nat.cast_add, Nat.cast_sum] at h3r
    exact h3r
  have h0 : (0 : ℝ) ≤ (∑ q ∈ (((Finset.Ioc (ξ : ℕ) ⌊((Real.sqrt ((x : ℕ) : ℝ) / Real.log ((x : ℕ) : ℝ) ^ 2 : ℝ))⌋₊).filter Nat.Prime : Finset ℕ)), (((((Finset.range (x : ℕ)).filter fun pK : ℕ => pK.Prime ∧ ¬ (pK : ℤ) ∣ (a : ℤ) ∧ (q : ℕ) ∣ pK - 1 ∧ ((a : ℤ) : ZMod pK) ^ ((pK - 1) / (q : ℕ)) = 1).card : ℕ)) : ℝ)) + ((((Finset.range (x : ℕ)).filter fun pK : ℕ => pK.Prime ∧ ¬ (pK : ℤ) ∣ (a : ℤ) ∧ ∃ qK : ℕ, qK.Prime ∧ ((Real.sqrt ((x : ℕ) : ℝ) / Real.log ((x : ℕ) : ℝ) ^ 2 : ℝ)) < qK ∧ (qK : ℝ) ≤ ((Real.sqrt ((x : ℕ) : ℝ) * Real.log ((x : ℕ) : ℝ) : ℝ)) ∧ qK ∣ pK - 1 ∧ ((a : ℤ) : ZMod pK) ^ ((pK - 1) / qK) = 1).card : ℕ)) +
      ((((Finset.range (x : ℕ)).filter fun pK : ℕ => pK.Prime ∧ ¬ (pK : ℤ) ∣ (a : ℤ) ∧ ∃ qK : ℕ, qK.Prime ∧ Real.sqrt (x : ℕ) * Real.log (x : ℕ) < qK ∧ qK ∣ pK - 1 ∧ ((a : ℤ) : ZMod pK) ^ ((pK - 1) / qK) = 1).card : ℕ)) := add_nonneg (add_nonneg (Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _) (Nat.cast_nonneg _)) (Nat.cast_nonneg _)
  rw [abs_le]
  constructor <;> linarith

lemma abs_sum_moebius_sub_le (a : ℤ) {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ k x : ℕ, Squarefree k → 2 ≤ x →
      |(((((Finset.range (x : ℕ)).filter fun pK : ℕ => pK.Prime ∧ ¬ (pK : ℤ) ∣ (a : ℤ) ∧ (k : ℕ) ∣ pK - 1 ∧ ((a : ℤ) : ZMod pK) ^ ((pK - 1) / (k : ℕ)) = 1).card : ℕ)) : ℝ) - (Nat.primeCounting x : ℝ) / (Module.finrank ℚ (Polynomial.X ^ (k : ℕ) - Polynomial.C ((a : ℤ) : ℚ)).SplittingField : ℕ)|
        ≤ C * Real.sqrt x * Real.log (k * x))
    (P x : ℕ) (hP : P ≠ 0) (hx : 2 ≤ x) :
    |∑ k ∈ P.divisors, (μ k : ℝ) * ((((Finset.range (x : ℕ)).filter fun pK : ℕ => pK.Prime ∧ ¬ (pK : ℤ) ∣ (a : ℤ) ∧ (k : ℕ) ∣ pK - 1 ∧ ((a : ℤ) : ZMod pK) ^ ((pK - 1) / (k : ℕ)) = 1).card : ℕ)) -
        (Nat.primeCounting x : ℝ) * ∑ k ∈ P.divisors, (μ k : ℝ) / (Module.finrank ℚ (Polynomial.X ^ (k : ℕ) - Polynomial.C ((a : ℤ) : ℚ)).SplittingField : ℕ)| ≤
      P * (C * Real.sqrt x * Real.log (P * x)) := by
  rw [mul_sum, ← sum_sub_distrib]
  have hxR : (2 : ℝ) ≤ x := by exact_mod_cast hx
  have hPR : (1 : ℝ) ≤ P := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hP
  have hlogP : 0 ≤ Real.log (P * x) := Real.log_nonneg (by nlinarith)
  have hCs : 0 ≤ C * Real.sqrt x := mul_nonneg hC (Real.sqrt_nonneg _)
  have hid : ∀ u v w z : ℝ, u * v - w * (u / z) = u * (v - w / z) := fun u v w z => by ring
  refine (abs_sum_le_sum_abs _ _).trans ?_
  refine (sum_le_sum (g := fun _ => C * Real.sqrt x * Real.log (P * x)) fun k hk => ?_).trans ?_
  · have hkP := Nat.divisor_le hk
    have hk0 : 0 < k := Nat.pos_of_mem_divisors hk
    rw [hid, abs_mul]
    by_cases hsq : Squarefree k
    · have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk0
      have hkPR : (k : ℝ) ≤ P := by exact_mod_cast hkP
      have hlog : Real.log (k * x) ≤ Real.log (P * x) :=
        Real.log_le_log (by positivity) (by nlinarith)
      have hmu : |(μ k : ℝ)| ≤ 1 := by exact_mod_cast ArithmeticFunction.abs_moebius_le_one
      refine (mul_le_mul hmu (h k x hsq hx) (abs_nonneg _) zero_le_one).trans ?_
      rw [one_mul]; exact mul_le_mul_of_nonneg_left hlog hCs
    · rw [ArithmeticFunction.moebius_eq_zero_of_not_squarefree hsq, Int.cast_zero,
        abs_zero, zero_mul]
      exact mul_nonneg hCs hlogP
  · rw [sum_const, nsmul_eq_mul]
    refine mul_le_mul_of_nonneg_right ?_ (mul_nonneg hCs hlogP)
    exact_mod_cast Nat.card_divisors_le_self P

lemma primorial_le_four_pow (n : ℕ) : primorial n ≤ 4 ^ n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · exact (primorial_lt_four_pow n hn.ne').le

lemma log_four_lt_two : Real.log 4 < 2 := by
  have h : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
  have := Real.log_two_lt_d9
  linarith

lemma primorial_xi1_le {x : ℕ} (hx : 1 ≤ x) :
    (primorial (((⌊Real.log (x : ℕ) / 6⌋₊ : ℕ))) : ℝ) ≤ Real.exp (Real.log x / 3) := by
  have hL : 0 ≤ Real.log x := Real.log_nonneg (by exact_mod_cast hx)
  have hξ : (((⌊Real.log (x : ℕ) / 6⌋₊ : ℕ)) : ℝ) ≤ Real.log x / 6 := Nat.floor_le (by positivity)
  have h0 : (0 : ℝ) ≤ ((⌊Real.log (x : ℕ) / 6⌋₊ : ℕ)) := Nat.cast_nonneg _
  have h4 := log_four_lt_two
  calc (primorial (((⌊Real.log (x : ℕ) / 6⌋₊ : ℕ))) : ℝ) ≤ (4 : ℝ) ^ ((⌊Real.log (x : ℕ) / 6⌋₊ : ℕ)) := by exact_mod_cast primorial_le_four_pow _
    _ = Real.exp (((⌊Real.log (x : ℕ) / 6⌋₊ : ℕ)) * Real.log 4) := by rw [Real.exp_nat_mul, Real.exp_log (by norm_num)]
    _ ≤ Real.exp (Real.log x / 3) := by
        apply Real.exp_le_exp.mpr
        nlinarith

lemma div_primeCounting_le {x : ℕ} (hx : 64 ≤ x) {Y : ℝ} (hY : 0 ≤ Y) :
    Y / Nat.primeCounting x ≤ 4 / Real.log 2 * Y * Real.log x / x := by
  have hxR : (64 : ℝ) ≤ x := by exact_mod_cast hx
  have h := div_log_le_primeCounting hxR
  rw [Nat.floor_natCast] at h
  have hL : 0 < Real.log x := Real.log_pos (by linarith)
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h' : (x : ℝ) ≤ 4 / Real.log 2 * Nat.primeCounting x * Real.log x := by
    rwa [div_le_iff₀ hL] at h
  have hπ : (0 : ℝ) < Nat.primeCounting x := by
    rcases (Nat.cast_nonneg (α := ℝ) (Nat.primeCounting x)).eq_or_lt with h0 | h0
    · rw [← h0] at h'; simp at h'; linarith
    · exact h0
  rw [div_le_div_iff₀ hπ (by linarith)]
  nlinarith [mul_le_mul_of_nonneg_left h' hY]

lemma error_ratio_le {C : ℝ} (hC : 0 ≤ C) {x : ℕ} (hx : 64 ≤ x) :
    (primorial (((⌊Real.log (x : ℕ) / 6⌋₊ : ℕ))) : ℝ) * (C * Real.sqrt x * Real.log (primorial (((⌊Real.log (x : ℕ) / 6⌋₊ : ℕ))) * x)) /
        Nat.primeCounting x ≤
      8 * C / Real.log 2 * (Real.log x ^ 2 * Real.exp (-(Real.log x / 6))) := by
  have hxR : (64 : ℝ) ≤ x := by exact_mod_cast hx
  have hx0 : (0 : ℝ) < x := by linarith
  set L := Real.log x with hLdef
  have hL : 0 < L := Real.log_pos (by linarith)
  have hP := primorial_xi1_le (by omega : 1 ≤ x)
  have hP1 : (1 : ℝ) ≤ primorial (((⌊Real.log (x : ℕ) / 6⌋₊ : ℕ))) := by exact_mod_cast primorial_pos _
  have hP0 : (0 : ℝ) < primorial (((⌊Real.log (x : ℕ) / 6⌋₊ : ℕ))) := by linarith
  have hlogP : Real.log (primorial (((⌊Real.log (x : ℕ) / 6⌋₊ : ℕ)))) ≤ L / 3 := by
    calc _ ≤ Real.log (Real.exp (L / 3)) := Real.log_le_log hP0 hP
      _ = L / 3 := Real.log_exp _
  have hlogPx : Real.log (primorial (((⌊Real.log (x : ℕ) / 6⌋₊ : ℕ))) * x) ≤ 2 * L := by
    rw [Real.log_mul hP0.ne' hx0.ne']; linarith
  have hlogPx0 : 0 ≤ Real.log (primorial (((⌊Real.log (x : ℕ) / 6⌋₊ : ℕ))) * x) := Real.log_nonneg (by nlinarith)
  have hsqrt : Real.sqrt x = Real.exp (L / 2) := by
    rw [Real.sqrt_eq_iff_mul_self_eq_of_pos (Real.exp_pos _), ← Real.exp_add, add_halves,
      hLdef, Real.exp_log hx0]
  have hxe : (x : ℝ) = Real.exp L := by rw [hLdef, Real.exp_log hx0]
  have hY : 0 ≤ (primorial (((⌊Real.log (x : ℕ) / 6⌋₊ : ℕ))) : ℝ) *
      (C * Real.sqrt x * Real.log (primorial (((⌊Real.log (x : ℕ) / 6⌋₊ : ℕ))) * x)) := by positivity
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine (div_primeCounting_le hx hY).trans ?_
  rw [hsqrt]
  calc 4 / Real.log 2 * ((primorial (((⌊Real.log (x : ℕ) / 6⌋₊ : ℕ))) : ℝ) *
        (C * Real.exp (L / 2) * Real.log (primorial (((⌊Real.log (x : ℕ) / 6⌋₊ : ℕ))) * x))) * L / x
      ≤ 4 / Real.log 2 * (Real.exp (L / 3) * (C * Real.exp (L / 2) * (2 * L))) * L / x := by
        gcongr
    _ = 8 * C / Real.log 2 * (L ^ 2 * Real.exp (-(L / 6))) := by
        rw [hxe, show -(L / 6) = L / 3 + L / 2 - L by ring, Real.exp_sub, Real.exp_add]
        field_simp
        ring

lemma tendsto_xi2 : Tendsto (fun (xF : ℝ) => ((Real.sqrt xF / Real.log xF ^ 2 : ℝ))) atTop atTop := by
  have h : Tendsto (fun x : ℝ => Real.exp (Real.log x / 4)) atTop atTop :=
    Real.tendsto_exp_atTop.comp (Real.tendsto_log_atTop.atTop_div_const (by norm_num))
  refine tendsto_atTop_mono' atTop ?_ h
  filter_upwards [eventually_ge_atTop (Real.exp 256)] with x hx
  have hpos : 0 < ((Real.sqrt (x : ℝ) / Real.log (x : ℝ) ^ 2 : ℝ)) := by have := two_le_xi2_of_large hx; linarith
  calc Real.exp (Real.log x / 4) ≤ Real.exp (Real.log (((Real.sqrt (x : ℝ) / Real.log (x : ℝ) ^ 2 : ℝ)))) :=
        Real.exp_le_exp.mpr (log_xi2_of_large hx)
    _ = ((Real.sqrt (x : ℝ) / Real.log (x : ℝ) ^ 2 : ℝ)) := Real.exp_log hpos

lemma eventually_primeCounting_xi2_le : ∀ᶠ x : ℕ in atTop,
    (Nat.primeCounting ⌊((Real.sqrt (x : ℝ) / Real.log (x : ℝ) ^ 2 : ℝ))⌋₊ : ℝ) ≤ (Real.log 4 + 1) * ((Real.sqrt (x : ℝ) / Real.log (x : ℝ) ^ 2 : ℝ)) / Real.log (((Real.sqrt (x : ℝ) / Real.log (x : ℝ) ^ 2 : ℝ))) :=
  (tendsto_xi2.comp tendsto_natCast_atTop_atTop).eventually
    (Chebyshev.eventually_primeCounting_le one_pos)

lemma medium_le (a : ℤ) {C c : ℝ} (hC : 0 ≤ C) (hc : 0 < c)
    (hK : ∀ k : ℕ, Squarefree k → 0 < k →
      ((k : ℝ) * (Nat.totient k : ℝ)) ≤ c * ((Module.finrank ℚ (Polynomial.X ^ (k : ℕ) - Polynomial.C ((a : ℤ) : ℚ)).SplittingField : ℕ) : ℝ))
    (h : ∀ k x : ℕ, Squarefree k → 2 ≤ x →
      |(((((Finset.range (x : ℕ)).filter fun pK : ℕ => pK.Prime ∧ ¬ (pK : ℤ) ∣ (a : ℤ) ∧ (k : ℕ) ∣ pK - 1 ∧ ((a : ℤ) : ZMod pK) ^ ((pK - 1) / (k : ℕ)) = 1).card : ℕ)) : ℝ) - (Nat.primeCounting x : ℝ) / (Module.finrank ℚ (Polynomial.X ^ (k : ℕ) - Polynomial.C ((a : ℤ) : ℚ)).SplittingField : ℕ)|
        ≤ C * Real.sqrt x * Real.log (k * x))
    (ξ x : ℕ) (hx : Real.exp 256 ≤ x)
    (hcheb : (Nat.primeCounting ⌊((Real.sqrt (x : ℝ) / Real.log (x : ℝ) ^ 2 : ℝ))⌋₊ : ℝ) ≤ (Real.log 4 + 1) * ((Real.sqrt (x : ℝ) / Real.log (x : ℝ) ^ 2 : ℝ)) / Real.log (((Real.sqrt (x : ℝ) / Real.log (x : ℝ) ^ 2 : ℝ)))) :
    ∑ q ∈ (((Finset.Ioc (ξ : ℕ) ⌊((Real.sqrt ((x : ℕ) : ℝ) / Real.log ((x : ℕ) : ℝ) ^ 2 : ℝ))⌋₊).filter Nat.Prime : Finset ℕ)), (((((Finset.range (x : ℕ)).filter fun pK : ℕ => pK.Prime ∧ ¬ (pK : ℤ) ∣ (a : ℤ) ∧ (q : ℕ) ∣ pK - 1 ∧ ((a : ℤ) : ZMod pK) ^ ((pK - 1) / (q : ℕ)) = 1).card : ℕ)) : ℝ) ≤
      c * Nat.primeCounting x * ((∑' kK : ℕ, ((1 / (((kK : ℕ) : ℝ) * Nat.totient (kK : ℕ)) : ℝ)) - ∑ kK ∈ Finset.range ((ξ + 1) : ℕ), ((1 / (((kK : ℕ) : ℝ) * Nat.totient (kK : ℕ)) : ℝ)) : ℝ)) +
        8 * (Real.log 4 + 1) * C * x / Real.log x ^ 2 := by
  have hx0 : (0 : ℝ) < x := xpos_of_large hx
  have hLb := log_ge_of_large hx
  set L := Real.log (x : ℝ) with hLdef
  have hL : 0 < L := by linarith
  have hx1 : (1 : ℝ) ≤ x := by
    have := Real.add_one_le_exp 256; linarith
  have hx2 : 2 ≤ x := by
    have : (2 : ℝ) ≤ x := by have := Real.add_one_le_exp 256; linarith
    exact_mod_cast this
  have hxi2pos : 0 < ((Real.sqrt (x : ℝ) / Real.log (x : ℝ) ^ 2 : ℝ)) := by have := two_le_xi2_of_large hx; linarith
  have hlogxi2 : L / 4 ≤ Real.log (((Real.sqrt (x : ℝ) / Real.log (x : ℝ) ^ 2 : ℝ))) := log_xi2_of_large hx
  have hsx : Real.sqrt x * Real.sqrt x = x := Real.mul_self_sqrt hx0.le
  have hs0 : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx0
  have hxi2x : ((Real.sqrt (x : ℝ) / Real.log (x : ℝ) ^ 2 : ℝ)) ≤ x := by
    have hsle : Real.sqrt x ≤ x := by nlinarith [Real.sqrt_nonneg (x : ℝ)]
    have : ((Real.sqrt (x : ℝ) / Real.log (x : ℝ) ^ 2 : ℝ)) ≤ Real.sqrt x := by
      rw [div_le_iff₀ (by positivity)]
      have h1 : (1 : ℝ) ≤ Real.log (x : ℝ) ^ 2 := by rw [← hLdef]; nlinarith
      nlinarith
    linarith
  have hπ0 : (0 : ℝ) ≤ Nat.primeCounting x := Nat.cast_nonneg _
  
  have hterm : ∀ q ∈ (((Finset.Ioc (ξ : ℕ) ⌊((Real.sqrt ((x : ℕ) : ℝ) / Real.log ((x : ℕ) : ℝ) ^ 2 : ℝ))⌋₊).filter Nat.Prime : Finset ℕ)), (((((Finset.range (x : ℕ)).filter fun pK : ℕ => pK.Prime ∧ ¬ (pK : ℤ) ∣ (a : ℤ) ∧ (q : ℕ) ∣ pK - 1 ∧ ((a : ℤ) : ZMod pK) ^ ((pK - 1) / (q : ℕ)) = 1).card : ℕ)) : ℝ) ≤
      c * Nat.primeCounting x * ((1 / (((q : ℕ) : ℝ) * Nat.totient (q : ℕ)) : ℝ)) + 2 * C * Real.sqrt x * L := by
    intro q hq
    simp only [mem_filter, mem_Ioc] at hq
    obtain ⟨⟨-, hq2⟩, hqp⟩ := hq
    have hqR : (q : ℝ) ≤ x := by
      have : (q : ℝ) ≤ ⌊((Real.sqrt (x : ℝ) / Real.log (x : ℝ) ^ 2 : ℝ))⌋₊ := by exact_mod_cast hq2
      linarith [Nat.floor_le hxi2pos.le]
    have hq0 : (0 : ℝ) < q := by exact_mod_cast hqp.pos
    obtain ⟨hDpos, hle⟩ := inv_kummerDegree_le hc hK hqp.squarefree hqp.pos
    have habs := h q x hqp.squarefree hx2
    have hlog : Real.log (q * x) ≤ 2 * L := by
      rw [Real.log_mul hq0.ne' hx0.ne']
      linarith [Real.log_le_log hq0 hqR]
    have h1 : (Nat.primeCounting x : ℝ) / (Module.finrank ℚ (Polynomial.X ^ (q : ℕ) - Polynomial.C ((a : ℤ) : ℚ)).SplittingField : ℕ) ≤
        c * Nat.primeCounting x * ((1 / (((q : ℕ) : ℝ) * Nat.totient (q : ℕ)) : ℝ)) := by
      rw [div_eq_mul_one_div]
      nlinarith
    have h2 : C * Real.sqrt x * Real.log (q * x) ≤ 2 * C * Real.sqrt x * L := by
      have := mul_le_mul_of_nonneg_left hlog (mul_nonneg hC hs0.le)
      linarith
    have := (abs_le.mp habs).2
    linarith
  have hcard : (((((Finset.Ioc (ξ : ℕ) ⌊((Real.sqrt ((x : ℕ) : ℝ) / Real.log ((x : ℕ) : ℝ) ^ 2 : ℝ))⌋₊).filter Nat.Prime : Finset ℕ))).card : ℝ) ≤ Nat.primeCounting ⌊((Real.sqrt (x : ℝ) / Real.log (x : ℝ) ^ 2 : ℝ))⌋₊ := by
    rw [← Nat.primesLE_card_eq_primeCounting]
    refine Nat.cast_le.mpr (card_le_card fun q hq => ?_)
    simp only [mem_filter, mem_Ioc] at hq
    exact Nat.mem_primesLE.mpr ⟨hq.1.2, hq.2⟩
  have hsum : ∑ q ∈ (((Finset.Ioc (ξ : ℕ) ⌊((Real.sqrt ((x : ℕ) : ℝ) / Real.log ((x : ℕ) : ℝ) ^ 2 : ℝ))⌋₊).filter Nat.Prime : Finset ℕ)), ((1 / (((q : ℕ) : ℝ) * Nat.totient (q : ℕ)) : ℝ)) ≤ ((∑' kK : ℕ, ((1 / (((kK : ℕ) : ℝ) * Nat.totient (kK : ℕ)) : ℝ)) - ∑ kK ∈ Finset.range ((ξ + 1) : ℕ), ((1 / (((kK : ℕ) : ℝ) * Nat.totient (kK : ℕ)) : ℝ)) : ℝ)) := by
    refine sum_le_tailInvKTot _ _ fun q hq => ?_
    simp only [mem_filter, mem_Ioc] at hq
    omega
  have hcount : (Nat.primeCounting ⌊((Real.sqrt (x : ℝ) / Real.log (x : ℝ) ^ 2 : ℝ))⌋₊ : ℝ) ≤ 4 * (Real.log 4 + 1) * Real.sqrt x / L ^ 3 := by
    refine hcheb.trans ?_
    have hl4 : 0 < Real.log 4 + 1 := by positivity
    calc (Real.log 4 + 1) * ((Real.sqrt (x : ℝ) / Real.log (x : ℝ) ^ 2 : ℝ)) / Real.log (((Real.sqrt (x : ℝ) / Real.log (x : ℝ) ^ 2 : ℝ)))
        ≤ (Real.log 4 + 1) * ((Real.sqrt (x : ℝ) / Real.log (x : ℝ) ^ 2 : ℝ)) / (L / 4) :=
          div_le_div_of_nonneg_left (by positivity) (by positivity) hlogxi2
      _ = 4 * (Real.log 4 + 1) * Real.sqrt x / L ^ 3 := by
          rw [← hLdef]
          field_simp
  calc ∑ q ∈ (((Finset.Ioc (ξ : ℕ) ⌊((Real.sqrt ((x : ℕ) : ℝ) / Real.log ((x : ℕ) : ℝ) ^ 2 : ℝ))⌋₊).filter Nat.Prime : Finset ℕ)), (((((Finset.range (x : ℕ)).filter fun pK : ℕ => pK.Prime ∧ ¬ (pK : ℤ) ∣ (a : ℤ) ∧ (q : ℕ) ∣ pK - 1 ∧ ((a : ℤ) : ZMod pK) ^ ((pK - 1) / (q : ℕ)) = 1).card : ℕ)) : ℝ)
      ≤ ∑ q ∈ (((Finset.Ioc (ξ : ℕ) ⌊((Real.sqrt ((x : ℕ) : ℝ) / Real.log ((x : ℕ) : ℝ) ^ 2 : ℝ))⌋₊).filter Nat.Prime : Finset ℕ)), (c * Nat.primeCounting x * ((1 / (((q : ℕ) : ℝ) * Nat.totient (q : ℕ)) : ℝ)) + 2 * C * Real.sqrt x * L) :=
        sum_le_sum hterm
    _ = c * Nat.primeCounting x * ∑ q ∈ (((Finset.Ioc (ξ : ℕ) ⌊((Real.sqrt ((x : ℕ) : ℝ) / Real.log ((x : ℕ) : ℝ) ^ 2 : ℝ))⌋₊).filter Nat.Prime : Finset ℕ)), ((1 / (((q : ℕ) : ℝ) * Nat.totient (q : ℕ)) : ℝ)) +
          ((((Finset.Ioc (ξ : ℕ) ⌊((Real.sqrt ((x : ℕ) : ℝ) / Real.log ((x : ℕ) : ℝ) ^ 2 : ℝ))⌋₊).filter Nat.Prime : Finset ℕ))).card * (2 * C * Real.sqrt x * L) := by
        rw [sum_add_distrib, ← mul_sum, sum_const, nsmul_eq_mul]
    _ ≤ c * Nat.primeCounting x * ((∑' kK : ℕ, ((1 / (((kK : ℕ) : ℝ) * Nat.totient (kK : ℕ)) : ℝ)) - ∑ kK ∈ Finset.range ((ξ + 1) : ℕ), ((1 / (((kK : ℕ) : ℝ) * Nat.totient (kK : ℕ)) : ℝ)) : ℝ)) +
          (4 * (Real.log 4 + 1) * Real.sqrt x / L ^ 3) * (2 * C * Real.sqrt x * L) := by
        gcongr
        exact hcard.trans hcount
    _ = c * Nat.primeCounting x * ((∑' kK : ℕ, ((1 / (((kK : ℕ) : ℝ) * Nat.totient (kK : ℕ)) : ℝ)) - ∑ kK ∈ Finset.range ((ξ + 1) : ℕ), ((1 / (((kK : ℕ) : ℝ) * Nat.totient (kK : ℕ)) : ℝ)) : ℝ)) +
          8 * (Real.log 4 + 1) * C * x / L ^ 2 := by
        have e : (4 * (Real.log 4 + 1) * Real.sqrt x / L ^ 3) * (2 * C * Real.sqrt x * L) =
            8 * (Real.log 4 + 1) * C * (Real.sqrt x * Real.sqrt x) / L ^ 2 := by
          field_simp
          ring
        rw [e, hsx]

lemma abs_div_sub_le {N M π S δ med lg hg E : ℝ} (hπ : 0 < π) (e1 : |N - M| ≤ med + lg + hg)
    (e2 : |M - π * S| ≤ E) :
    |N / π - δ| ≤ med / π + lg / π + hg / π + E / π + |S - δ| := by
  have hsplit : N / π - δ = (N - M) / π + (M - π * S) / π + (S - δ) := by
    field_simp
    ring
  rw [hsplit]
  calc |(N - M) / π + (M - π * S) / π + (S - δ)|
      ≤ |(N - M) / π| + |(M - π * S) / π| + |S - δ| :=
        (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) (le_refl _))
    _ = |N - M| / π + |M - π * S| / π + |S - δ| := by
        rw [abs_div, abs_div, abs_of_pos hπ]
    _ ≤ (med + lg + hg) / π + E / π + |S - δ| := by
        gcongr
    _ = med / π + lg / π + hg / π + E / π + |S - δ| := by
        rw [add_div, add_div]

theorem tendsto_primRootCount_div (hBT : ∀ q : ℕ, 1 ≤ q → ∀ x : ℝ, (q : ℝ) < x → ((((Finset.range (⌊x⌋₊ + 1)).filter fun p => p.Prime ∧ p ≡ 1 [MOD q]).card : ℕ) : ℝ) ≤ 20000 * x / (q.totient * Real.log (x / q))) (a : ℤ) (ha : ¬IsSquare a) (ha' : a ≠ -1)
    (hK1 : (∃ c : ℝ, 0 < c ∧ ∀ kK : ℕ, Squarefree kK → 0 < kK → ((kK : ℝ) * (Nat.totient kK : ℝ)) ≤ c * ((Module.finrank ℚ (Polynomial.X ^ (kK : ℕ) - Polynomial.C (((a : ℤ) : ℤ) : ℚ)).SplittingField : ℕ) : ℝ))) (h : (∃ C : ℝ, ∀ kK xK : ℕ, Squarefree kK → 2 ≤ xK → |(((((Finset.range (xK : ℕ)).filter fun pK : ℕ => pK.Prime ∧ ¬ (pK : ℤ) ∣ ((a : ℤ) : ℤ) ∧ (kK : ℕ) ∣ pK - 1 ∧ (((a : ℤ) : ℤ) : ZMod pK) ^ ((pK - 1) / (kK : ℕ)) = 1).card : ℕ)) : ℝ) - (Nat.primeCounting xK : ℝ) / (Module.finrank ℚ (Polynomial.X ^ (kK : ℕ) - Polynomial.C (((a : ℤ) : ℤ) : ℚ)).SplittingField : ℕ)| ≤ C * Real.sqrt xK * Real.log (kK * xK))) :
    Tendsto (fun x : ℕ => (((((Finset.range (x : ℕ)).filter fun pK : ℕ => pK.Prime ∧ orderOf ((a : ℤ) : ZMod pK) = pK - 1).card : ℕ)) : ℝ) / Nat.primeCounting x) atTop
      (𝓝 (∑' k : ℕ, (μ k : ℝ) / ((Module.finrank ℚ (Polynomial.X ^ (k : ℕ) - Polynomial.C ((a : ℤ) : ℚ)).SplittingField : ℕ) : ℝ))) := by
  have ha0 : a ≠ 0 := by rintro rfl; exact ha ⟨0, by simp⟩
  have ha1 : a ≠ 1 := by rintro rfl; exact ha ⟨1, by simp⟩
  have hf : Summable fun k : ℕ => (μ k : ℝ) / ((Module.finrank ℚ (Polynomial.X ^ (k : ℕ) - Polynomial.C ((a : ℤ) : ℚ)).SplittingField : ℕ) : ℝ) :=
    summable_moebius_div_kummerDegree a hK1
  obtain ⟨c, hc, hK⟩ := hK1
  obtain ⟨C, hC⟩ := h
  have hC0 : 0 ≤ C := by
    have h13 := hC 1 3 squarefree_one (by norm_num)
    have hpos : 0 < Real.sqrt ((3 : ℕ) : ℝ) * Real.log ((1 : ℕ) * ((3 : ℕ) : ℝ)) := by
      have : (1 : ℝ) < (1 : ℕ) * ((3 : ℕ) : ℝ) := by norm_num
      have := Real.log_pos this
      positivity
    by_contra hneg
    push Not at hneg
    have : C * Real.sqrt ((3 : ℕ) : ℝ) * Real.log ((1 : ℕ) * ((3 : ℕ) : ℝ)) < 0 := by
      rw [mul_assoc]; exact mul_neg_of_neg_of_pos hneg hpos
    have := (abs_nonneg _).trans h13
    linarith
  set δ := ∑' k : ℕ, (μ k : ℝ) / ((Module.finrank ℚ (Polynomial.X ^ (k : ℕ) - Polynomial.C ((a : ℤ) : ℚ)).SplittingField : ℕ) : ℝ) with hδ
  set f : ℕ → ℝ := fun k => (μ k : ℝ) / ((Module.finrank ℚ (Polynomial.X ^ (k : ℕ) - Polynomial.C ((a : ℤ) : ℚ)).SplittingField : ℕ) : ℝ) with hfdef
  
  have hlog : Tendsto (fun x : ℕ => Real.log x) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hξ : Tendsto (fun (xF : ℕ) => ((⌊Real.log xF / 6⌋₊ : ℕ))) atTop atTop :=
    tendsto_nat_floor_atTop.comp (hlog.atTop_div_const (by norm_num))
  
  have hSP : Tendsto (fun x : ℕ => ∑ k ∈ (primorial (((⌊Real.log (x : ℕ) / 6⌋₊ : ℕ)))).divisors, f k) atTop (𝓝 δ) :=
    (tendsto_sum_divisors_primorial hf
      (fun k hk => by
        simp [hfdef, ArithmeticFunction.moebius_eq_zero_of_not_squarefree hk])
      (by simp [hfdef])).comp hξ
  
  set K1 : ℝ := 4 / Real.log 2 * (8 * (Real.log 4 + 1) * C)
  set K2 : ℝ := 4 / Real.log 2 * (a.natAbs + 1 : ℝ)
  set B : ℕ → ℝ := fun x =>
    |∑ k ∈ (primorial (((⌊Real.log (x : ℕ) / 6⌋₊ : ℕ)))).divisors, f k - δ| +
      8 * C / Real.log 2 * (Real.log x ^ 2 * Real.exp (-(Real.log x / 6))) +
      c * ((∑' kK : ℕ, ((1 / (((kK : ℕ) : ℝ) * Nat.totient (kK : ℕ)) : ℝ)) - ∑ kK ∈ Finset.range ((((⌊Real.log (x : ℕ) / 6⌋₊ : ℕ)) + 1) : ℕ), ((1 / (((kK : ℕ) : ℝ) * Nat.totient (kK : ℕ)) : ℝ)) : ℝ)) + K1 / Real.log x +
      (((((Finset.range (x : ℕ)).filter fun pK : ℕ => pK.Prime ∧ ¬ (pK : ℤ) ∣ (a : ℤ) ∧ ∃ qK : ℕ, qK.Prime ∧ ((Real.sqrt ((x : ℕ) : ℝ) / Real.log ((x : ℕ) : ℝ) ^ 2 : ℝ)) < qK ∧ (qK : ℝ) ≤ ((Real.sqrt ((x : ℕ) : ℝ) * Real.log ((x : ℕ) : ℝ) : ℝ)) ∧ qK ∣ pK - 1 ∧ ((a : ℤ) : ZMod pK) ^ ((pK - 1) / qK) = 1).card : ℕ)) : ℝ) / Nat.primeCounting x + K2 / Real.log x with hBdef
  have hB : Tendsto B atTop (𝓝 0) := by
    have t1 : Tendsto (fun x : ℕ => |∑ k ∈ (primorial (((⌊Real.log (x : ℕ) / 6⌋₊ : ℕ)))).divisors, f k - δ|) atTop
        (𝓝 0) := by
      have := (hSP.sub_const δ).abs
      rwa [sub_self, abs_zero] at this
    have t2 : Tendsto (fun x : ℕ => Real.log x ^ 2 * Real.exp (-(Real.log x / 6))) atTop
        (𝓝 0) := by
      have := ((Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 2).comp
        (hlog.atTop_div_const (by norm_num : (0 : ℝ) < 6))).const_mul 36
      rw [mul_zero] at this
      refine this.congr fun x => ?_
      simp only [Function.comp]
      ring
    have t3 : Tendsto (fun x : ℕ => ((∑' kK : ℕ, ((1 / (((kK : ℕ) : ℝ) * Nat.totient (kK : ℕ)) : ℝ)) - ∑ kK ∈ Finset.range ((((⌊Real.log (x : ℕ) / 6⌋₊ : ℕ)) + 1) : ℕ), ((1 / (((kK : ℕ) : ℝ) * Nat.totient (kK : ℕ)) : ℝ)) : ℝ))) atTop (𝓝 0) :=
      tendsto_tailInvKTot.comp ((tendsto_add_atTop_nat 1).comp hξ)
    have t4 : Tendsto (fun x : ℕ => K1 / Real.log x) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop hlog
    have t5 : Tendsto (fun x : ℕ => (((((Finset.range (x : ℕ)).filter fun pK : ℕ => pK.Prime ∧ ¬ (pK : ℤ) ∣ (a : ℤ) ∧ ∃ qK : ℕ, qK.Prime ∧ ((Real.sqrt ((x : ℕ) : ℝ) / Real.log ((x : ℕ) : ℝ) ^ 2 : ℝ)) < qK ∧ (qK : ℝ) ≤ ((Real.sqrt ((x : ℕ) : ℝ) * Real.log ((x : ℕ) : ℝ) : ℝ)) ∧ qK ∣ pK - 1 ∧ ((a : ℤ) : ZMod pK) ^ ((pK - 1) / qK) = 1).card : ℕ)) : ℝ) / Nat.primeCounting x) atTop
        (𝓝 0) :=
      (largePrimeCount_isLittleO hBT a).tendsto_div_nhds_zero
    have t6 : Tendsto (fun x : ℕ => K2 / Real.log x) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop hlog
    have := ((((t1.add (t2.const_mul (8 * C / Real.log 2))).add (t3.const_mul c)).add t4).add
      t5).add t6
    have hz : (0 : ℝ) + 8 * C / Real.log 2 * 0 + c * 0 + 0 + 0 + 0 = 0 := by ring
    rw [hz] at this
    exact this
  rw [← tendsto_sub_nhds_zero_iff]
  refine squeeze_zero_norm' ?_ hB
  filter_upwards [eventually_ge_atTop ⌈Real.exp 256⌉₊, eventually_primeCounting_xi2_le]
    with x hx hcheb
  have hxe : Real.exp 256 ≤ x := Nat.ceil_le.mp hx
  have hx4R : (64 : ℝ) ≤ x := by have := Real.add_one_le_exp 256; linarith
  have hx4 : 64 ≤ x := by exact_mod_cast hx4R
  have hL : 0 < Real.log x := Real.log_pos (by linarith)
  have hπ : (0 : ℝ) < Nat.primeCounting x := by
    have h' := div_log_le_primeCounting hx4R
    rw [Nat.floor_natCast] at h'
    have : 0 < (x : ℝ) / Real.log x := by positivity
    have hl2 : 0 < 4 / Real.log 2 := div_pos (by norm_num) (Real.log_pos (by norm_num))
    by_contra hneg
    push Not at hneg
    nlinarith
  have e1 := abs_primRootCount_sub_le a (((⌊Real.log (x : ℕ) / 6⌋₊ : ℕ))) x
  have e2 := abs_sum_moebius_sub_le a hC0 hC (primorial (((⌊Real.log (x : ℕ) / 6⌋₊ : ℕ)))) x (primorial_ne_zero _)
    (by omega)
  have e3 := error_ratio_le hC0 hx4
  have e4 := medium_le a hC0 hc hK hC (((⌊Real.log (x : ℕ) / 6⌋₊ : ℕ))) x hxe hcheb
  have e5 := hugePrimeCount_le a ha0 ha1 ha' x (by omega)
  have r4 : (∑ q ∈ (((Finset.Ioc ((((⌊Real.log (x : ℕ) / 6⌋₊ : ℕ))) : ℕ) ⌊((Real.sqrt ((x : ℕ) : ℝ) / Real.log ((x : ℕ) : ℝ) ^ 2 : ℝ))⌋₊).filter Nat.Prime : Finset ℕ)), (((((Finset.range (x : ℕ)).filter fun pK : ℕ => pK.Prime ∧ ¬ (pK : ℤ) ∣ (a : ℤ) ∧ (q : ℕ) ∣ pK - 1 ∧ ((a : ℤ) : ZMod pK) ^ ((pK - 1) / (q : ℕ)) = 1).card : ℕ)) : ℝ)) / Nat.primeCounting x ≤
      c * ((∑' kK : ℕ, ((1 / (((kK : ℕ) : ℝ) * Nat.totient (kK : ℕ)) : ℝ)) - ∑ kK ∈ Finset.range ((((⌊Real.log (x : ℕ) / 6⌋₊ : ℕ)) + 1) : ℕ), ((1 / (((kK : ℕ) : ℝ) * Nat.totient (kK : ℕ)) : ℝ)) : ℝ)) + K1 / Real.log x := by
    have hY : 0 ≤ 8 * (Real.log 4 + 1) * C * x / Real.log x ^ 2 := by positivity
    have h8 := div_primeCounting_le hx4 hY
    have hsplit : (c * Nat.primeCounting x * ((∑' kK : ℕ, ((1 / (((kK : ℕ) : ℝ) * Nat.totient (kK : ℕ)) : ℝ)) - ∑ kK ∈ Finset.range ((((⌊Real.log (x : ℕ) / 6⌋₊ : ℕ)) + 1) : ℕ), ((1 / (((kK : ℕ) : ℝ) * Nat.totient (kK : ℕ)) : ℝ)) : ℝ)) +
          8 * (Real.log 4 + 1) * C * x / Real.log x ^ 2) / Nat.primeCounting x =
        c * ((∑' kK : ℕ, ((1 / (((kK : ℕ) : ℝ) * Nat.totient (kK : ℕ)) : ℝ)) - ∑ kK ∈ Finset.range ((((⌊Real.log (x : ℕ) / 6⌋₊ : ℕ)) + 1) : ℕ), ((1 / (((kK : ℕ) : ℝ) * Nat.totient (kK : ℕ)) : ℝ)) : ℝ)) +
          (8 * (Real.log 4 + 1) * C * x / Real.log x ^ 2) / Nat.primeCounting x := by
      rw [add_div]; congr 1; field_simp
    have hK1eq : 4 / Real.log 2 * (8 * (Real.log 4 + 1) * C * x / Real.log x ^ 2) *
        Real.log x / x = K1 / Real.log x := by
      have : (x : ℝ) ≠ 0 := by positivity
      simp only [K1]
      field_simp
    have := div_le_div_of_nonneg_right e4 hπ.le
    rw [hsplit] at this
    linarith
  have r5 : (((((Finset.range (x : ℕ)).filter fun pK : ℕ => pK.Prime ∧ ¬ (pK : ℤ) ∣ (a : ℤ) ∧ ∃ qK : ℕ, qK.Prime ∧ Real.sqrt (x : ℕ) * Real.log (x : ℕ) < qK ∧ qK ∣ pK - 1 ∧ ((a : ℤ) : ZMod pK) ^ ((pK - 1) / qK) = 1).card : ℕ)) : ℝ) / Nat.primeCounting x ≤ K2 / Real.log x := by
    have hY : 0 ≤ (a.natAbs + 1 : ℝ) * x / Real.log x ^ 2 := by positivity
    have h8 := div_primeCounting_le hx4 hY
    have hK2eq : 4 / Real.log 2 * ((a.natAbs + 1 : ℝ) * x / Real.log x ^ 2) * Real.log x / x =
        K2 / Real.log x := by
      have : (x : ℝ) ≠ 0 := by positivity
      simp only [K2]
      field_simp
    have := div_le_div_of_nonneg_right e5 hπ.le
    linarith
  have key := abs_div_sub_le (δ := δ) hπ e1 e2
  rw [Real.norm_eq_abs]
  refine key.trans ?_
  simp only [hBdef]
  linarith

theorem artin_of_effectiveKummerChebotarev_of_kummer (hBT : ∀ q : ℕ, 1 ≤ q → ∀ x : ℝ, (q : ℝ) < x → ((((Finset.range (⌊x⌋₊ + 1)).filter fun p => p.Prime ∧ p ≡ 1 [MOD q]).card : ℕ) : ℝ) ≤ 20000 * x / (q.totient * Real.log (x / q))) (a : ℤ) (ha : ¬IsSquare a)
    (ha' : a ≠ -1) (hK1 : (∃ c : ℝ, 0 < c ∧ ∀ kK : ℕ, Squarefree kK → 0 < kK → ((kK : ℝ) * (Nat.totient kK : ℝ)) ≤ c * ((Module.finrank ℚ (Polynomial.X ^ (kK : ℕ) - Polynomial.C (((a : ℤ) : ℤ) : ℚ)).SplittingField : ℕ) : ℝ))) (hK2 : (0 < ∑' kK : ℕ, (ArithmeticFunction.moebius kK : ℝ) / ((Module.finrank ℚ (Polynomial.X ^ (kK : ℕ) - Polynomial.C (((a : ℤ) : ℤ) : ℚ)).SplittingField : ℕ) : ℝ)))
    (h : (∃ C : ℝ, ∀ kK xK : ℕ, Squarefree kK → 2 ≤ xK → |(((((Finset.range (xK : ℕ)).filter fun pK : ℕ => pK.Prime ∧ ¬ (pK : ℤ) ∣ ((a : ℤ) : ℤ) ∧ (kK : ℕ) ∣ pK - 1 ∧ (((a : ℤ) : ℤ) : ZMod pK) ^ ((pK - 1) / (kK : ℕ)) = 1).card : ℕ)) : ℝ) - (Nat.primeCounting xK : ℝ) / (Module.finrank ℚ (Polynomial.X ^ (kK : ℕ) - Polynomial.C (((a : ℤ) : ℤ) : ℚ)).SplittingField : ℕ)| ≤ C * Real.sqrt xK * Real.log (kK * xK))) :
    ∃ x > 0, (S a).HasDensity x {p | p.Prime} :=
  ⟨_, hK2, hasDensity_of_tendsto a _ (tendsto_primRootCount_div hBT a ha ha' hK1 h)⟩

end Artin

end


theorem main : H1 → H2 → H3 → H4 →
    type_of% @ArtinPrimitiveRootsConjecture.conditional_artin_primitive_roots.parts.i := by
  intro h1 h2 h3 h4 a ha ha' h
  have ha0 : a ≠ 0 := by rintro rfl; exact ha ⟨0, by simp⟩
  have ha1 : a ≠ 1 := by rintro rfl; exact ha ⟨1, by simp⟩
  exact Artin.artin_of_effectiveKummerChebotarev_of_kummer h2 a ha ha' (h3 a ha0 ha1 ha')
    (h4 a ha ha') (h1 a ha0 h)

end OMA.R_ArtinPrimitiveRootsConjecture_conditional_artin_primitive_roots_parts_i_R1
