import FormalConjectures.Wikipedia.AgohGiuga

/-!
# Proof of `AgohGiuga.isStrongGiuga_iff`

For a composite integer `a`, we prove
`IsStrongGiuga a ↔ IsCarmichael a ∧ ∃ n : ℕ, ∑ p ∈ a.primeFactors, (1 / p : ℚ) - 1 / a = n`
by showing both sides are equivalent to
`Squarefree a ∧ ∀ p ∈ a.primeFactors, (p - 1) ∣ (a - 1) ∧ p ∣ (a / p - 1)`:
1. For every prime `p ∣ a`, block reduction mod `p` gives
   `1 + ∑_{i=1}^{a-1} i^{a-1} ≡ 1 + (a / p) * ∑_{r < p} r^{a-1} (mod p)`.
   The inner `ZMod p` power sum equals `-1` if `p - 1 ∣ a - 1` (Fermat's little theorem) and `0`
   otherwise (via a cyclic generator of `(ZMod p)ˣ`), so `p` divides `1 + ∑ i^{a-1}` iff
   `(p - 1) ∣ (a - 1) ∧ p ∣ (a / p - 1)`.
2. Combining `korselts_criterion` with the rational-sum characterization
   `(∃ n : ℕ, ∑_{p ∣ a} 1/p - 1/a = n) ↔ Squarefree a ∧ ∀ p ∈ a.primeFactors, p ∣ a / p - 1`
   completes the equivalence.
-/

-- Problem: Agoh-Giuga conjecture — isStrongGiuga iff
-- Upstream: formal-conjectures FormalConjectures/Wikipedia/AgohGiuga.lean:262 (declaration AgohGiuga.isStrongGiuga_iff)
-- Credit: @TheWaler (the owner of the agent is credited as the solver)

namespace AgohGiugaStrongProof

open AgohGiuga
open scoped Nat

private lemma prod_primeFactors_of_squarefree {n : ℕ} (hn0 : n ≠ 0) (hsq : Squarefree n) :
    ∏ p ∈ n.primeFactors, p = n := by
  have h1 : ∀ p ∈ n.primeFactors, n.factorization p = 1 := by
    intro p hp
    have hp_prime : p.Prime := Nat.prime_of_mem_primeFactors hp
    have hge1 : 1 ≤ n.factorization p :=
      (hp_prime.dvd_iff_one_le_factorization hn0).mp (Nat.dvd_of_mem_primeFactors hp)
    have hle1 : n.factorization p ≤ 1 := by
      by_contra hgt
      have h2 : 2 ≤ n.factorization p := by omega
      have hsq_dvd : p * p ∣ n := by
        rw [← sq]
        exact (pow_dvd_pow p h2).trans (n.ordProj_dvd p)
      exact (Nat.squarefree_iff_prime_squarefree.mp hsq p hp_prime) hsq_dvd
    omega
  conv_rhs => rw [← Nat.prod_factorization_pow_eq_self hn0, Finsupp.prod, Nat.support_factorization]
  refine Finset.prod_congr rfl fun p hp => ?_
  rw [h1 p hp, pow_one]

private lemma dvd_of_squarefree_forall_primeFactors_dvd {n m : ℕ} (hn0 : n ≠ 0) (hsq : Squarefree n)
    (h : ∀ p ∈ n.primeFactors, p ∣ m) : n ∣ m := by
  rw [← prod_primeFactors_of_squarefree hn0 hsq]
  have haux : ∀ s : Finset ℕ, (∀ p ∈ s, p.Prime ∧ p ∣ m) → ∏ p ∈ s, p ∣ m := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      intro _
      simp
    | @insert a s ha ih =>
      intro hs
      rw [Finset.prod_insert ha]
      have ha_p : a.Prime := (hs a (Finset.mem_insert_self a s)).1
      have ha_d : a ∣ m := (hs a (Finset.mem_insert_self a s)).2
      have hs_d : ∏ p ∈ s, p ∣ m := ih fun p hp => hs p (Finset.mem_insert_of_mem hp)
      have hcop : Nat.Coprime a (∏ p ∈ s, p) := Nat.Coprime.prod_right fun p hp =>
        (Nat.coprime_primes ha_p (hs p (Finset.mem_insert_of_mem hp)).1).mpr
          (fun hEq => ha (hEq ▸ hp))
      exact hcop.mul_dvd_of_dvd_of_dvd ha_d hs_d
  exact haux n.primeFactors fun p hp => ⟨Nat.prime_of_mem_primeFactors hp, h p hp⟩

private lemma squarefree_of_forall_primeFactors_dvd_div_sub_one {n : ℕ} (hn0 : n ≠ 0)
    (h : ∀ p ∈ n.primeFactors, p ∣ n / p - 1) : Squarefree n := by
  rw [Nat.squarefree_iff_prime_squarefree]
  intro p hp hpp
  have hpn : p ∣ n := dvd_trans (dvd_mul_right p p) hpp
  have hmem : p ∈ n.primeFactors := Nat.mem_primeFactors.mpr ⟨hp, hpn, hn0⟩
  have hdvd1 : p ∣ n / p - 1 := h p hmem
  rcases hpp with ⟨k, hk⟩
  have hdiv : n / p = p * k := by
    rw [hk, mul_assoc, Nat.mul_div_cancel_left _ hp.pos]
  have hdvd2 : p ∣ n / p := ⟨k, hdiv⟩
  have hge1 : 1 ≤ n / p := Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hn0) hpn) hp.pos
  have h1 : p ∣ 1 := by
    have hadd : n / p - 1 + 1 = n / p := Nat.sub_add_cancel hge1
    exact (Nat.dvd_add_right hdvd1).mp (hadd.symm ▸ hdvd2)
  exact hp.not_dvd_one h1

private lemma sum_range_pow_zmod_mul (q d k : ℕ) :
    ((∑ i ∈ Finset.range (q * d), i ^ k : ℕ) : ZMod d) =
      (q : ZMod d) * ∑ r ∈ Finset.range d, (r : ZMod d) ^ k := by
  induction q with
  | zero =>
    simp
  | succ q ih =>
    rw [add_mul, one_mul, Finset.sum_range_add, Nat.cast_add, ih]
    have hblock : ((∑ r ∈ Finset.range d, (q * d + r) ^ k : ℕ) : ZMod d) =
        ∑ r ∈ Finset.range d, (r : ZMod d) ^ k := by
      push_cast
      refine Finset.sum_congr rfl fun r _ => ?_
      simp
    rw [hblock]
    push_cast
    ring

private lemma sum_Ioo_eq_sum_range {n k : ℕ} (hk : 0 < k) :
    ∑ i ∈ Finset.Ioo 0 n, i ^ k = ∑ i ∈ Finset.range n, i ^ k := by
  by_cases hn : n = 0
  · subst hn; simp
  have hrange : Finset.range n = insert 0 (Finset.Ioo 0 n) := by
    ext x
    simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Ioo]
    omega
  rw [hrange, Finset.sum_insert (by simp), zero_pow hk.ne', zero_add]

private lemma sum_range_pow_zmod_eq_neg_one_of_dvd {p k : ℕ} (hp : p.Prime)
    (hk_pos : 0 < k) (hdvd : p - 1 ∣ k) :
    ∑ r ∈ Finset.range p, (r : ZMod p) ^ k = -1 := by
  have : Fact p.Prime := ⟨hp⟩
  rcases hdvd with ⟨c, hc⟩
  rw [← Nat.Ico_zero_eq_range, Finset.sum_eq_sum_Ico_succ_bot hp.pos]
  have h0 : ((0 : ℕ) : ZMod p) ^ k = 0 := by
    rw [Nat.cast_zero, zero_pow hk_pos.ne']
  rw [h0, zero_add]
  have hones : ∑ r ∈ Finset.Ico 1 p, (r : ZMod p) ^ k = ∑ _r ∈ Finset.Ico 1 p, (1 : ZMod p) := by
    refine Finset.sum_congr rfl fun r hr => ?_
    rcases Finset.mem_Ico.mp hr with ⟨hr1, hrp⟩
    have hr_ne : (r : ZMod p) ≠ 0 := by
      intro h0
      have hpr : p ∣ r := (ZMod.natCast_eq_zero_iff r p).mp h0
      exact absurd (Nat.le_of_dvd (by omega) hpr) (by omega)
    rw [hc, pow_mul, ZMod.pow_card_sub_one_eq_one hr_ne, one_pow]
  rw [hones, Finset.sum_const, Nat.card_Ico, nsmul_eq_mul, mul_one,
    Nat.cast_sub hp.pos, ZMod.natCast_self, Nat.cast_one, zero_sub]

private lemma sum_range_pow_zmod_eq_zero_of_not_dvd {p k : ℕ} (hp : p.Prime)
    (hk : ¬ (p - 1) ∣ k) :
    ∑ r ∈ Finset.range p, (r : ZMod p) ^ k = 0 := by
  have : Fact p.Prime := ⟨hp⟩
  have hrange : ∑ r ∈ Finset.range p, (r : ZMod p) ^ k = ∑ x : ZMod p, x ^ k := by
    refine Finset.sum_nbij (fun r : ℕ => (r : ZMod p)) ?_ ?_ ?_ ?_
    · intro r _
      exact Finset.mem_univ _
    · intro r1 hr1 r2 hr2 heq
      have hval := congr_arg ZMod.val heq
      rwa [ZMod.val_natCast_of_lt (Finset.mem_range.mp hr1),
        ZMod.val_natCast_of_lt (Finset.mem_range.mp hr2)] at hval
    · intro x _
      exact ⟨x.val, Finset.mem_range.mpr (ZMod.val_lt x), ZMod.natCast_zmod_val x⟩
    · intro _ _
      rfl
  rw [hrange]
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := (ZMod p)ˣ)
  have hord : orderOf g = p - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_eq_fintype_card,
      ZMod.card_units_eq_totient, Nat.totient_prime hp]
  have hgk_ne : (g : ZMod p) ^ k ≠ 1 := by
    intro h1
    have hunit : g ^ k = 1 := Units.ext (by simpa [Units.val_pow_eq_pow_val] using h1)
    exact hk (hord ▸ orderOf_dvd_iff_pow_eq_one.mpr hunit)
  have hbij : ∑ x : ZMod p, ((g : ZMod p) * x) ^ k = ∑ x : ZMod p, x ^ k :=
    Equiv.sum_comp (Equiv.mulLeft₀ (g : ZMod p) g.ne_zero) (fun x : ZMod p => x ^ k)
  have hfactor : ∑ x : ZMod p, ((g : ZMod p) * x) ^ k =
      (g : ZMod p) ^ k * ∑ x : ZMod p, x ^ k := by
    simp_rw [mul_pow, ← Finset.mul_sum]
  have hmul : ((g : ZMod p) ^ k - 1) * ∑ x : ZMod p, x ^ k = 0 := by
    rw [sub_mul, one_mul, ← hfactor, hbij, sub_self]
  exact (mul_eq_zero.mp hmul).resolve_left (sub_ne_zero.mpr hgk_ne)

private lemma sum_primeFactors_iff_char {n : ℕ} (hn : n.Composite) :
    (∃ m : ℕ, ∑ p ∈ n.primeFactors, (1 / p : ℚ) - 1 / n = m) ↔
      Squarefree n ∧ ∀ p ∈ n.primeFactors, p ∣ n / p - 1 := by
  have hn1 : 1 < n := hn.1
  have hn0 : n ≠ 0 := by omega
  have hn_q_ne : (n : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hn0
  set S : ℕ := ∑ p ∈ n.primeFactors, n / p
  have hS_ge1 : 1 ≤ S := by
    rcases Nat.nonempty_primeFactors.mpr hn1 with ⟨p0, hp0⟩
    have h1 : 1 ≤ n / p0 := Nat.div_pos (Nat.le_of_dvd (by omega) (Nat.dvd_of_mem_primeFactors hp0))
      (Nat.prime_of_mem_primeFactors hp0).pos
    exact le_trans h1 (Finset.single_le_sum (f := fun p => n / p) (fun _ _ => Nat.zero_le _) hp0)
  have hclear : (n : ℚ) * (∑ p ∈ n.primeFactors, (1 / p : ℚ) - 1 / n) = ((S - 1 : ℕ) : ℚ) := by
    rw [mul_sub, Finset.mul_sum, mul_one_div_cancel hn_q_ne, Nat.cast_sub hS_ge1, Nat.cast_one]
    congr 1
    push_cast [S]
    refine Finset.sum_congr rfl fun p hp => ?_
    have hpn : p ∣ n := Nat.dvd_of_mem_primeFactors hp
    have hp_ne : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.prime_of_mem_primeFactors hp).ne_zero
    have hmul : ((n / p : ℕ) : ℚ) * (p : ℚ) = (n : ℚ) := by
      exact_mod_cast Nat.div_mul_cancel hpn
    rw [mul_one_div, div_eq_iff hp_ne]
    exact hmul.symm
  have hdvd_iff : (∃ m : ℕ, ∑ p ∈ n.primeFactors, (1 / p : ℚ) - 1 / n = m) ↔ n ∣ S - 1 := by
    constructor
    · rintro ⟨m, hm⟩
      refine ⟨m, ?_⟩
      have hq : ((S - 1 : ℕ) : ℚ) = ((n * m : ℕ) : ℚ) := by
        rw [← hclear, hm, Nat.cast_mul]
      exact Nat.cast_injective hq
    · rintro ⟨m, hm⟩
      refine ⟨m, ?_⟩
      apply mul_left_cancel₀ hn_q_ne
      rw [hclear, hm, Nat.cast_mul]
  have hp_sum_iff : ∀ p ∈ n.primeFactors, p ∣ S - 1 ↔ p ∣ n / p - 1 := by
    intro p hp
    have hp_prime : p.Prime := Nat.prime_of_mem_primeFactors hp
    have hpn : p ∣ n := Nat.dvd_of_mem_primeFactors hp
    have hge1 : 1 ≤ n / p := Nat.div_pos (Nat.le_of_dvd (by omega) hpn) hp_prime.pos
    have hsplit : S = n / p + ∑ q ∈ n.primeFactors.erase p, n / q :=
      (Finset.add_sum_erase n.primeFactors (fun q => n / q) hp).symm
    have hsub_eq : S - 1 = (n / p - 1) + ∑ q ∈ n.primeFactors.erase p, n / q := by
      omega
    have herase_dvd : p ∣ ∑ q ∈ n.primeFactors.erase p, n / q := by
      refine Finset.dvd_sum fun q hq => ?_
      rcases Finset.mem_erase.mp hq with ⟨hqp, hq_mem⟩
      have hq_prime : q.Prime := Nat.prime_of_mem_primeFactors hq_mem
      have hqn : q ∣ n := Nat.dvd_of_mem_primeFactors hq_mem
      have hcop : Nat.Coprime p q := (Nat.coprime_primes hp_prime hq_prime).mpr (Ne.symm hqp)
      have hmul : p ∣ (n / q) * q := by rwa [Nat.div_mul_cancel hqn]
      exact hcop.dvd_of_dvd_mul_right hmul
    rw [hsub_eq, Nat.dvd_add_left herase_dvd]
  rw [hdvd_iff]
  constructor
  · intro hdvd
    have hall : ∀ p ∈ n.primeFactors, p ∣ n / p - 1 := fun p hp =>
      (hp_sum_iff p hp).mp (dvd_trans (Nat.dvd_of_mem_primeFactors hp) hdvd)
    exact ⟨squarefree_of_forall_primeFactors_dvd_div_sub_one hn0 hall, hall⟩
  · rintro ⟨hsq, hall⟩
    exact dvd_of_squarefree_forall_primeFactors_dvd hn0 hsq fun p hp =>
      (hp_sum_iff p hp).mpr (hall p hp)

private lemma isStrongGiuga_iff_char {a : ℕ} (ha : a.Composite) :
    IsStrongGiuga a ↔ Squarefree a ∧ ∀ p ∈ a.primeFactors, (p - 1) ∣ (a - 1) ∧ p ∣ a / p - 1 := by
  have ha1 : 1 < a := ha.1
  have ha0 : a ≠ 0 := by omega
  have ha_sub_pos : 0 < a - 1 := by omega
  have hp_iff : ∀ p ∈ a.primeFactors,
      p ∣ 1 + ∑ i ∈ Finset.Ioo 0 a, i ^ (a - 1) ↔ (p - 1) ∣ (a - 1) ∧ p ∣ a / p - 1 := by
    intro p hp_mem
    have hp : p.Prime := Nat.prime_of_mem_primeFactors hp_mem
    have : Fact p.Prime := ⟨hp⟩
    have hpa : p ∣ a := Nat.dvd_of_mem_primeFactors hp_mem
    have hge1 : 1 ≤ a / p := Nat.div_pos (Nat.le_of_dvd (by omega) hpa) hp.pos
    rw [sum_Ioo_eq_sum_range ha_sub_pos, ← ZMod.natCast_eq_zero_iff]
    have hsum_mod : ((∑ i ∈ Finset.range a, i ^ (a - 1) : ℕ) : ZMod p) =
        ((a / p : ℕ) : ZMod p) * ∑ r ∈ Finset.range p, (r : ZMod p) ^ (a - 1) := by
      have h := sum_range_pow_zmod_mul (a / p) p (a - 1)
      rwa [Nat.div_mul_cancel hpa] at h
    rw [Nat.cast_add, Nat.cast_one, hsum_mod]
    by_cases hdvd : p - 1 ∣ a - 1
    · rw [sum_range_pow_zmod_eq_neg_one_of_dvd hp ha_sub_pos hdvd, mul_neg_one,
        ← ZMod.natCast_eq_zero_iff (a / p - 1) p, Nat.cast_sub hge1, Nat.cast_one]
      constructor
      · intro h
        exact ⟨hdvd, by linear_combination -h⟩
      · rintro ⟨_, h⟩
        linear_combination -h
    · rw [sum_range_pow_zmod_eq_zero_of_not_dvd hp hdvd, mul_zero, add_zero]
      exact ⟨fun h => absurd h one_ne_zero, fun h => absurd h.1 hdvd⟩
  constructor
  · rintro ⟨_, hdvd⟩
    have hall : ∀ p ∈ a.primeFactors, (p - 1) ∣ (a - 1) ∧ p ∣ a / p - 1 := fun p hp =>
      (hp_iff p hp).mp (dvd_trans (Nat.dvd_of_mem_primeFactors hp) hdvd)
    exact ⟨squarefree_of_forall_primeFactors_dvd_div_sub_one ha0 fun p hp => (hall p hp).2, hall⟩
  · rintro ⟨hsq, hall⟩
    refine ⟨ha, dvd_of_squarefree_forall_primeFactors_dvd ha0 hsq fun p hp => ?_⟩
    exact (hp_iff p hp).mpr (hall p hp)

end AgohGiugaStrongProof

open AgohGiuga AgohGiugaStrongProof

theorem OMA.solution : type_of% @AgohGiuga.isStrongGiuga_iff := by
  intro a ha
  have ha0 : a ≠ 0 := by have := ha.1; omega
  rw [isStrongGiuga_iff_char ha, korselts_criterion a ha, sum_primeFactors_iff_char ha]
  constructor
  · rintro ⟨hsq, hall⟩
    refine ⟨⟨hsq, fun p hp hpa => (hall p (Nat.mem_primeFactors.mpr ⟨hp, hpa, ha0⟩)).1⟩,
      ⟨hsq, fun p hp => (hall p hp).2⟩⟩
  · rintro ⟨⟨hsq, hcarm⟩, ⟨_, hweak⟩⟩
    exact ⟨hsq, fun p hp =>
      ⟨hcarm p (Nat.prime_of_mem_primeFactors hp) (Nat.dvd_of_mem_primeFactors hp), hweak p hp⟩⟩
