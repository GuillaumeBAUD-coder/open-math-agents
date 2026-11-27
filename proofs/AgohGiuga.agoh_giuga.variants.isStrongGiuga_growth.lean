import FormalConjectures.Wikipedia.AgohGiuga

/-!
# Growth bound for strong Giuga numbers

Elementary proof of `AgohGiuga.agoh_giuga.variants.isStrongGiuga_growth`,
following Vicentiu Tipu's note on Giuga's conjecture.
-/

-- Problem: Agoh-Giuga conjecture — isStrongGiuga growth
-- Upstream: formal-conjectures FormalConjectures/Wikipedia/AgohGiuga.lean:266 (declaration AgohGiuga.agoh_giuga.variants.isStrongGiuga_growth)
-- Credit: @<your GitHub handle> (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

section StrongGiugaGrowth

open scoped Classical

private lemma prod_primeFactors_eq_self_of_squarefree {n : ℕ} (hsq : Squarefree n) :
    ∏ p ∈ n.primeFactors, p = n := by
  have hn0 : n ≠ 0 := hsq.ne_zero
  have hprod := Nat.prod_primeFactors_pow_factorization hn0
  calc
    ∏ p ∈ n.primeFactors, p = ∏ p ∈ n.primeFactors, p ^ n.factorization p := by
      refine Finset.prod_congr rfl fun p hp => ?_
      have hp_prime : p.Prime := Nat.prime_of_mem_primeFactors hp
      have hp_dvd : p ∣ n := Nat.dvd_of_mem_primeFactors hp
      have h1 : 1 ≤ n.factorization p := (hp_prime.dvd_iff_one_le_factorization hn0).mp hp_dvd
      have h2 : n.factorization p ≤ 1 := by
        by_contra hlt
        push Not at hlt
        have hpow : p ^ 2 ∣ n := (hp_prime.pow_dvd_iff_le_factorization hn0).mpr hlt
        have hsqp : p * p ∣ n := by simpa [sq] using hpow
        exact hp_prime.ne_one (Nat.isUnit_iff.mp (hsq p hsqp))
      have hEq : n.factorization p = 1 := le_antisymm h2 h1
      simp [hEq]
    _ = n := hprod.symm

private lemma primeFactors_prod_of_primes {S : Finset ℕ} (hS : ∀ p ∈ S, p.Prime) :
    (∏ p ∈ S, p).primeFactors = S := by
  induction S using Finset.induction_on with
  | empty => simp
  | insert p s hps ih =>
    have hp : p.Prime := hS p (Finset.mem_insert_self p s)
    have hs : ∀ q ∈ s, q.Prime := fun q hq => hS q (Finset.mem_insert_of_mem hq)
    have hprod_ne : ∏ q ∈ s, q ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr fun q hq => (hs q hq).ne_zero
    rw [Finset.prod_insert hps, Nat.primeFactors_mul hp.ne_zero hprod_ne,
      hp.primeFactors, ih hs, Finset.singleton_union]

private lemma modEq_prod_of_primes {S : Finset ℕ} (hS : ∀ p ∈ S, p.Prime) {a b : ℕ}
    (h : ∀ p ∈ S, a ≡ b [MOD p]) : a ≡ b [MOD ∏ p ∈ S, p] := by
  induction S using Finset.induction_on with
  | empty => simp [Nat.modEq_one]
  | insert p s hps ih =>
    have hp : p.Prime := hS p (Finset.mem_insert_self p s)
    have hs : ∀ q ∈ s, q.Prime := fun q hq => hS q (Finset.mem_insert_of_mem hq)
    have hcop : Nat.Coprime p (∏ q ∈ s, q) := by
      refine Nat.Coprime.prod_right fun q hq => ?_
      have hne : p ≠ q := fun heq => hps (heq ▸ hq)
      exact (Nat.coprime_primes hp (hs q hq)).mpr hne
    rw [Finset.prod_insert hps]
    exact (Nat.modEq_and_modEq_iff_modEq_mul hcop).mp
      ⟨h p (Finset.mem_insert_self p s), ih hs (fun q hq => h q (Finset.mem_insert_of_mem hq))⟩

private lemma sum_units_pow_zmod (p : ℕ) [Fact p.Prime] (k : ℕ) :
    (∑ u : (ZMod p)ˣ, (u : ZMod p) ^ k) = if (p - 1) ∣ k then -1 else 0 := by
  have hp : p.Prime := Fact.out
  split_ifs with hk
  · obtain ⟨m, rfl⟩ := hk
    have h1 : ∀ u : (ZMod p)ˣ, (u : ZMod p) ^ ((p - 1) * m) = 1 := fun u => by
      rw [pow_mul, ZMod.pow_card_sub_one_eq_one u.ne_zero, one_pow]
    simp_rw [h1, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
    rw [ZMod.card_units_eq_totient, Nat.totient_prime hp, Nat.cast_sub hp.one_le,
      ZMod.natCast_self, Nat.cast_one, zero_sub]
  · obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := (ZMod p)ˣ)
    have hord : orderOf g = p - 1 := by
      rw [orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_eq_fintype_card,
        ZMod.card_units_eq_totient, Nat.totient_prime hp]
    have hgk_ne : g ^ k ≠ 1 := by
      intro hEq
      exact hk (hord ▸ orderOf_dvd_iff_pow_eq_one.mpr hEq)
    have hgk_val_ne : (g : ZMod p) ^ k ≠ 1 := by
      intro hEq
      apply hgk_ne
      apply Units.ext
      simpa [Units.val_pow_eq_pow_val] using hEq
    set S : ZMod p := ∑ u : (ZMod p)ˣ, (u : ZMod p) ^ k
    have hmul : (g : ZMod p) ^ k * S = S := by
      calc
        (g : ZMod p) ^ k * S
            = ∑ u : (ZMod p)ˣ, (g : ZMod p) ^ k * (u : ZMod p) ^ k := Finset.mul_sum _ _ _
        _ = ∑ u : (ZMod p)ˣ, ((g * u : (ZMod p)ˣ) : ZMod p) ^ k := by
              refine Finset.sum_congr rfl fun u _ => ?_
              rw [Units.val_mul, mul_pow]
        _ = S := Equiv.sum_comp (Equiv.mulLeft g) (fun u : (ZMod p)ˣ => (u : ZMod p) ^ k)
    have hzero : ((g : ZMod p) ^ k - 1) * S = 0 := by
      rw [sub_mul, one_mul, hmul, sub_self]
    exact (mul_eq_zero.mp hzero).resolve_left (sub_ne_zero.mpr hgk_val_ne)

private lemma sum_range_mul_zmod (p m k : ℕ) :
    (∑ i ∈ Finset.range (p * m), (i : ZMod p) ^ k) =
      (m : ZMod p) * ∑ r ∈ Finset.range p, (r : ZMod p) ^ k := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Nat.mul_succ, Finset.sum_range_add, ih]
    have hshift :
        (∑ r ∈ Finset.range p, ((p * m + r : ℕ) : ZMod p) ^ k) =
          ∑ r ∈ Finset.range p, (r : ZMod p) ^ k := by
      refine Finset.sum_congr rfl fun r _ => ?_
      simp [Nat.cast_add, Nat.cast_mul]
    rw [hshift, Nat.cast_succ, add_mul, one_mul]

private lemma sum_range_eq_sum_units_zmod (p : ℕ) [Fact p.Prime] {k : ℕ} (hk : k ≠ 0) :
    (∑ r ∈ Finset.range p, (r : ZMod p) ^ k) = ∑ u : (ZMod p)ˣ, (u : ZMod p) ^ k := by
  have hp : p.Prime := Fact.out
  have h1 : (∑ r ∈ Finset.range p, (r : ZMod p) ^ k) = ∑ x : ZMod p, x ^ k := by
    refine Finset.sum_nbij (fun r => (r : ZMod p)) ?_ ?_ ?_ ?_
    · intro r _; exact Finset.mem_univ _
    · intro r₁ hr₁ r₂ hr₂ hEq
      have h1' : r₁ < p := Finset.mem_range.mp hr₁
      have h2' : r₂ < p := Finset.mem_range.mp hr₂
      have hmod : r₁ % p = r₂ % p := by
        simpa [ZMod.val_natCast] using congrArg ZMod.val hEq
      rwa [Nat.mod_eq_of_lt h1', Nat.mod_eq_of_lt h2'] at hmod
    · intro x _
      exact ⟨x.val, Finset.mem_range.mpr (ZMod.val_lt x), ZMod.natCast_zmod_val x⟩
    · intro _ _; rfl
  rw [h1]
  have h2 : (∑ x : ZMod p, x ^ k) = ∑ x ∈ Finset.univ.erase (0 : ZMod p), x ^ k := by
    rw [← Finset.add_sum_erase Finset.univ (fun x : ZMod p => x ^ k) (Finset.mem_univ 0),
      zero_pow hk, zero_add]
  rw [h2]
  symm
  refine Finset.sum_nbij (fun u : (ZMod p)ˣ => (u : ZMod p)) ?_ ?_ ?_ ?_
  · intro u _
    exact Finset.mem_erase.mpr ⟨u.ne_zero, Finset.mem_univ _⟩
  · intro u₁ _ u₂ _ hEq
    exact Units.ext hEq
  · intro x hx
    have hx0 : x ≠ 0 := (Finset.mem_erase.mp hx).1
    exact ⟨Units.mk0 x hx0, Finset.mem_univ _, rfl⟩
  · intro _ _; rfl

private lemma isStrongGiuga_props {n : ℕ} (hn : AgohGiuga.IsStrongGiuga n) :
    Squarefree n ∧
      (∀ p, p.Prime → p ∣ n → p ∣ n / p - 1) ∧
      (∀ p, p.Prime → p ∣ n → (p - 1) ∣ (n - 1)) := by
  obtain ⟨hcomp, hdvd_sum⟩ := hn
  have hn1 : 1 < n := hcomp.1
  have hn_sub_ne : n - 1 ≠ 0 := by omega
  have hmain : ∀ p, p.Prime → p ∣ n → ¬ (p * p ∣ n) ∧ p ∣ n / p - 1 ∧ (p - 1) ∣ (n - 1) := by
    intro p hp hpn
    have : Fact p.Prime := ⟨hp⟩
    set m := n / p
    have hpm : p * m = n := Nat.mul_div_cancel' hpn
    have hm_pos : 1 ≤ m := Nat.div_pos (Nat.le_of_dvd (by omega) hpn) hp.pos
    have hp_dvd : p ∣ 1 + ∑ i ∈ Finset.Ioo 0 n, i ^ (n - 1) := hpn.trans hdvd_sum
    have hz : ((1 + ∑ i ∈ Finset.Ioo 0 n, i ^ (n - 1) : ℕ) : ZMod p) = 0 :=
      (ZMod.natCast_eq_zero_iff _ p).mpr hp_dvd
    have hsum_Ioo :
        (∑ i ∈ Finset.Ioo 0 n, (i : ZMod p) ^ (n - 1)) =
          ∑ i ∈ Finset.range n, (i : ZMod p) ^ (n - 1) := by
      have hset : Finset.range n = insert 0 (Finset.Ioo 0 n) := by
        ext i
        simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Ioo]
        omega
      rw [hset, Finset.sum_insert (by simp), Nat.cast_zero, zero_pow hn_sub_ne, zero_add]
    have hz' : (1 : ZMod p) + (m : ZMod p) * (if (p - 1) ∣ (n - 1) then -1 else 0) = 0 := by
      have hcast : ((1 + ∑ i ∈ Finset.Ioo 0 n, i ^ (n - 1) : ℕ) : ZMod p) =
          1 + ∑ i ∈ Finset.Ioo 0 n, (i : ZMod p) ^ (n - 1) := by
        push_cast
        rfl
      have hmul_sum :
          (∑ i ∈ Finset.range n, (i : ZMod p) ^ (n - 1)) =
            (m : ZMod p) * ∑ r ∈ Finset.range p, (r : ZMod p) ^ (n - 1) := by
        nth_rw 1 [← hpm]
        exact sum_range_mul_zmod p m (n - 1)
      rw [hcast, hsum_Ioo, hmul_sum,
        sum_range_eq_sum_units_zmod p hn_sub_ne, sum_units_pow_zmod] at hz
      exact hz
    have hpm1 : (p - 1) ∣ (n - 1) := by
      by_contra hndvd
      rw [if_neg hndvd, mul_zero, add_zero] at hz'
      exact one_ne_zero hz'
    rw [if_pos hpm1, mul_neg_one] at hz'
    have hm_eq : (m : ZMod p) = 1 := by
      linear_combination -hz'
    have hdvd_m1 : p ∣ m - 1 := by
      rw [← ZMod.natCast_eq_zero_iff, Nat.cast_sub hm_pos, hm_eq, Nat.cast_one, sub_self]
    have hndvd_pp : ¬ (p * p ∣ n) := by
      intro hpp
      rw [← hpm] at hpp
      have hpm' : p ∣ m := (mul_dvd_mul_iff_left hp.ne_zero).mp hpp
      have hm0 : (m : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff m p).mpr hpm'
      rw [hm0] at hm_eq
      exact zero_ne_one hm_eq
    exact ⟨hndvd_pp, hdvd_m1, hpm1⟩
  refine ⟨?_, fun p hp hpn => (hmain p hp hpn).2.1, fun p hp hpn => (hmain p hp hpn).2.2⟩
  rw [Nat.squarefree_iff_prime_squarefree]
  intro p hp hpp
  exact (hmain p hp (dvd_trans (dvd_mul_right p p) hpp)).1 hpp

private noncomputable def maxPrime (a : ℕ) : ℕ :=
  if h : a.primeFactors.Nonempty then a.primeFactors.max' h else 0

private lemma maxPrime_mem {a : ℕ} (ha : 2 ≤ a) : maxPrime a ∈ a.primeFactors := by
  have hne : a.primeFactors.Nonempty := Nat.nonempty_primeFactors.mpr (by omega)
  simp only [maxPrime, dif_pos hne]
  exact Finset.max'_mem _ hne

private lemma maxPrime_prime {a : ℕ} (ha : 2 ≤ a) : (maxPrime a).Prime :=
  Nat.prime_of_mem_primeFactors (maxPrime_mem ha)

private lemma maxPrime_dvd {a : ℕ} (ha : 2 ≤ a) : maxPrime a ∣ a :=
  Nat.dvd_of_mem_primeFactors (maxPrime_mem ha)

private lemma le_maxPrime {a p : ℕ} (ha : 2 ≤ a) (hp : p ∈ a.primeFactors) : p ≤ maxPrime a := by
  have hne : a.primeFactors.Nonempty := Nat.nonempty_primeFactors.mpr (by omega)
  simp only [maxPrime, dif_pos hne]
  exact Finset.le_max' _ p hp

private lemma exists_divisor_of_isStrongGiuga {X n : ℕ} (hn : AgohGiuga.IsStrongGiuga n)
    (hn_lt : Nat.sqrt X < n) (hn_le : n ≤ X) :
    ∃ a ∈ Finset.Icc 2 (Nat.sqrt X), a ∣ n ∧ Nat.sqrt X < a * maxPrime a := by
  set M := Nat.sqrt X
  obtain ⟨hsq, hdvd_sub, _⟩ := isStrongGiuga_props hn
  have hcomp : n.Composite := hn.1
  have hn2 : 2 ≤ n := hcomp.1
  have hne : n.primeFactors.Nonempty := Nat.nonempty_primeFactors.mpr (by omega)
  set p1 := maxPrime n
  have hp1_mem : p1 ∈ n.primeFactors := maxPrime_mem hn2
  have hp1_prime : p1.Prime := maxPrime_prime hn2
  have hp1_dvd : p1 ∣ n := maxPrime_dvd hn2
  have hp1_le_M : p1 ≤ M := by
    have hdiv_gt : 1 < n / p1 := by
      by_contra hle
      have hdiv_pos : 0 < n / p1 := Nat.div_pos (Nat.le_of_dvd (by omega) hp1_dvd) hp1_prime.pos
      have hdiv_eq : n / p1 = 1 := by omega
      have hn_eq : n = p1 := by
        have := Nat.mul_div_cancel' hp1_dvd
        rw [hdiv_eq, mul_one] at this
        exact this.symm
      exact hcomp.2 (hn_eq ▸ hp1_prime)
    have hsub_pos : 0 < n / p1 - 1 := by omega
    have hp1_le_sub : p1 ≤ n / p1 - 1 := Nat.le_of_dvd hsub_pos (hdvd_sub p1 hp1_prime hp1_dvd)
    have hp1_sq : p1 * p1 ≤ X := by
      calc
        p1 * p1 ≤ p1 * (n / p1) := Nat.mul_le_mul_left p1 (by omega)
        _ = n := Nat.mul_div_cancel' hp1_dvd
        _ ≤ X := hn_le
    exact Nat.le_sqrt.mpr hp1_sq
  let P : ℕ → Prop := fun t => (∏ p ∈ n.primeFactors.filter (t ≤ ·), p) ≤ M
  have hP_p1 : P p1 := by
    have hfilt : n.primeFactors.filter (p1 ≤ ·) = {p1} := by
      ext q
      simp only [Finset.mem_filter, Finset.mem_singleton]
      constructor
      · rintro ⟨hq, hle⟩
        exact le_antisymm (le_maxPrime hn2 hq) hle
      · rintro rfl
        exact ⟨hp1_mem, le_rfl⟩
    simp only [P, hfilt, Finset.prod_singleton]
    exact hp1_le_M
  have hnotP0 : ¬ P 0 := by
    have hfilt : n.primeFactors.filter (0 ≤ ·) = n.primeFactors := by
      ext q; simp
    simp only [P, hfilt, prod_primeFactors_eq_self_of_squarefree hsq, not_le]
    exact hn_lt
  set t0 := Nat.find (⟨p1, hP_p1⟩ : ∃ t, P t)
  have ht0_spec : P t0 := Nat.find_spec (⟨p1, hP_p1⟩ : ∃ t, P t)
  have ht0_le_p1 : t0 ≤ p1 := Nat.find_min' (⟨p1, hP_p1⟩ : ∃ t, P t) hP_p1
  have ht0_ne0 : t0 ≠ 0 := fun h0 => hnotP0 (h0 ▸ ht0_spec)
  set q := t0 - 1
  have hq_lt : q < t0 := by omega
  have hnotPq : ¬ P q := Nat.find_min (⟨p1, hP_p1⟩ : ∃ t, P t) hq_lt
  set S := n.primeFactors.filter (t0 ≤ ·)
  set a := ∏ p ∈ S, p
  have hS_sub : S ⊆ n.primeFactors := Finset.filter_subset _ _
  have hS_primes : ∀ p ∈ S, p.Prime := fun p hp => Nat.prime_of_mem_primeFactors (hS_sub hp)
  have hp1_S : p1 ∈ S := Finset.mem_filter.mpr ⟨hp1_mem, ht0_le_p1⟩
  have ha_dvd : a ∣ n := by
    rw [← prod_primeFactors_eq_self_of_squarefree hsq]
    exact Finset.prod_dvd_prod_of_subset _ _ _ hS_sub
  have ha_le_M : a ≤ M := ht0_spec
  have ha_ge2 : 2 ≤ a := by
    have hp1_dvd_a : p1 ∣ a := Finset.dvd_prod_of_mem _ hp1_S
    have ha_pos : 0 < a := Finset.prod_pos fun p hp => (hS_primes p hp).pos
    exact le_trans hp1_prime.two_le (Nat.le_of_dvd ha_pos hp1_dvd_a)
  have hq_mem : q ∈ n.primeFactors := by
    by_contra hq_not
    have hfilt_eq : n.primeFactors.filter (q ≤ ·) = S := by
      ext r
      simp only [S, Finset.mem_filter]
      constructor
      · rintro ⟨hr, hqr⟩
        refine ⟨hr, ?_⟩
        have hrne : r ≠ q := fun heq => hq_not (heq ▸ hr)
        omega
      · rintro ⟨hr, ht0r⟩
        exact ⟨hr, by omega⟩
    exact hnotPq (by simpa [P, hfilt_eq] using ht0_spec)
  have hfilt_q : n.primeFactors.filter (q ≤ ·) = insert q S := by
    ext r
    simp only [S, Finset.mem_filter, Finset.mem_insert]
    constructor
    · rintro ⟨hr, hqr⟩
      by_cases heq : r = q
      · exact Or.inl heq
      · exact Or.inr ⟨hr, by omega⟩
    · rintro (rfl | ⟨hr, ht0r⟩)
      · exact ⟨hq_mem, le_rfl⟩
      · exact ⟨hr, by omega⟩
  have hq_not_S : q ∉ S := by
    simp only [S, Finset.mem_filter]
    omega
  have hM_lt_qa : M < q * a := by
    have hgt : M < ∏ p ∈ n.primeFactors.filter (q ≤ ·), p := lt_of_not_ge hnotPq
    rw [hfilt_q, Finset.prod_insert hq_not_S] at hgt
    exact hgt
  have ha_pf : a.primeFactors = S := primeFactors_prod_of_primes hS_primes
  have hmax_a : maxPrime a = p1 := by
    have hle1 : maxPrime a ≤ p1 := by
      have hmem : maxPrime a ∈ S := ha_pf ▸ maxPrime_mem ha_ge2
      exact le_maxPrime hn2 (hS_sub hmem)
    have hle2 : p1 ≤ maxPrime a := le_maxPrime ha_ge2 (ha_pf.symm ▸ hp1_S)
    exact le_antisymm hle1 hle2
  have hM_lt_ap : M < a * maxPrime a := by
    rw [hmax_a, mul_comm]
    exact lt_of_lt_of_le hM_lt_qa (Nat.mul_le_mul_right a (by omega))
  exact ⟨a, Finset.mem_Icc.mpr ⟨ha_ge2, ha_le_M⟩, ha_dvd, hM_lt_ap⟩

private lemma fiber_card_le {X a : ℕ} (hX : 4 ≤ X) (ha : a ∈ Finset.Icc 2 (Nat.sqrt X)) :
    (((Finset.Icc 1 X).filter
      (fun n => AgohGiuga.IsStrongGiuga n ∧ Nat.sqrt X < n ∧ a ∣ n ∧
        Nat.sqrt X < a * maxPrime a)).card : ℝ) ≤ 2 * (X : ℝ).sqrt / (a : ℝ) + 1 := by
  set M := Nat.sqrt X
  set F := (Finset.Icc 1 X).filter
    (fun n => AgohGiuga.IsStrongGiuga n ∧ M < n ∧ a ∣ n ∧ M < a * maxPrime a)
  have ha2 : 2 ≤ a := (Finset.mem_Icc.mp ha).1
  have ha_pos : (0 : ℝ) < a := by exact_mod_cast (by omega : 0 < a)
  by_cases hF : F.Nonempty
  · obtain ⟨n0, hn0⟩ := hF
    have hn0_mem := Finset.mem_filter.mp hn0
    have hn0_giuga : AgohGiuga.IsStrongGiuga n0 := hn0_mem.2.1
    have ha_dvd_n0 : a ∣ n0 := hn0_mem.2.2.2.1
    have hM_lt_ap : M < a * maxPrime a := hn0_mem.2.2.2.2
    have hsq_n0 : Squarefree n0 := (isStrongGiuga_props hn0_giuga).1
    have hsq_a : Squarefree a := hsq_n0.squarefree_of_dvd ha_dvd_n0
    set p := maxPrime a
    have hp_prime : p.Prime := maxPrime_prime ha2
    have hp_dvd_a : p ∣ a := maxPrime_dvd ha2
    have hp2 : 2 ≤ p := hp_prime.two_le
    set D := a * (p - 1)
    have hD_pos : 0 < D := Nat.mul_pos (by omega) (by omega)
    have hmod : ∀ n1 ∈ F, ∀ n2 ∈ F, n1 / a ≡ n2 / a [MOD D] := by
      intro n1 hn1 n2 hn2
      have h1 := (Finset.mem_filter.mp hn1).2
      have h2 := (Finset.mem_filter.mp hn2).2
      obtain ⟨_, h1_sub, h1_pm1⟩ := isStrongGiuga_props h1.1
      obtain ⟨_, h2_sub, h2_pm1⟩ := isStrongGiuga_props h2.1
      have ha1 : a ∣ n1 := h1.2.2.1
      have ha2' : a ∣ n2 := h2.2.2.1
      have hmod_a : n1 / a ≡ n2 / a [MOD a] := by
        have hmod_prod : n1 / a ≡ n2 / a [MOD ∏ q ∈ a.primeFactors, q] := by
          refine modEq_prod_of_primes (fun q hq => Nat.prime_of_mem_primeFactors hq) ?_
          intro q hq
          have hq_prime : q.Prime := Nat.prime_of_mem_primeFactors hq
          have hq_dvd_a : q ∣ a := Nat.dvd_of_mem_primeFactors hq
          have hq_dvd_n1 : q ∣ n1 := hq_dvd_a.trans ha1
          have hq_dvd_n2 : q ∣ n2 := hq_dvd_a.trans ha2'
          have hcop_q : Nat.gcd q (a / q) = 1 := by
            have hndvd : ¬ (q ∣ a / q) := by
              intro hd
              have hqq : q * q ∣ a := by
                have := mul_dvd_mul_left q hd
                rwa [Nat.mul_div_cancel' hq_dvd_a] at this
              exact hq_prime.ne_one (Nat.isUnit_iff.mp (hsq_a q hqq))
            exact hq_prime.coprime_iff_not_dvd.mpr hndvd
          have hmul1 : (a / q) * (n1 / a) = n1 / q := by
            have hmul : q * ((a / q) * (n1 / a)) = q * (n1 / q) := by
              rw [← mul_assoc, Nat.mul_div_cancel' hq_dvd_a, Nat.mul_div_cancel' ha1,
                Nat.mul_div_cancel' hq_dvd_n1]
            exact Nat.eq_of_mul_eq_mul_left hq_prime.pos hmul
          have hmul2 : (a / q) * (n2 / a) = n2 / q := by
            have hmul : q * ((a / q) * (n2 / a)) = q * (n2 / q) := by
              rw [← mul_assoc, Nat.mul_div_cancel' hq_dvd_a, Nat.mul_div_cancel' ha2',
                Nat.mul_div_cancel' hq_dvd_n2]
            exact Nat.eq_of_mul_eq_mul_left hq_prime.pos hmul
          have hpos1 : 1 ≤ n1 / q := Nat.div_pos (Nat.le_of_dvd (by have := h1.1.1.1; omega) hq_dvd_n1) hq_prime.pos
          have hpos2 : 1 ≤ n2 / q := Nat.div_pos (Nat.le_of_dvd (by have := h2.1.1.1; omega) hq_dvd_n2) hq_prime.pos
          have hcon1 : n1 / q ≡ 1 [MOD q] := by
            obtain ⟨k, hk⟩ := h1_sub q hq_prime hq_dvd_n1
            have hEq : n1 / q = 1 + q * k := by omega
            rw [hEq, Nat.ModEq]
            simp
          have hcon2 : n2 / q ≡ 1 [MOD q] := by
            obtain ⟨k, hk⟩ := h2_sub q hq_prime hq_dvd_n2
            have hEq : n2 / q = 1 + q * k := by omega
            rw [hEq, Nat.ModEq]
            simp
          have hcon12 : (a / q) * (n1 / a) ≡ (a / q) * (n2 / a) [MOD q] := by
            rw [hmul1, hmul2]
            exact hcon1.trans hcon2.symm
          exact Nat.ModEq.cancel_left_of_coprime hcop_q hcon12
        rwa [prod_primeFactors_eq_self_of_squarefree hsq_a] at hmod_prod
      have hcop_pm1 : Nat.Coprime a (p - 1) := by
        have hp_dvd_n1 : p ∣ n1 := hp_dvd_a.trans ha1
        obtain ⟨k, hk⟩ := h1_pm1 p hp_prime hp_dvd_n1
        have hn1_pos : 1 ≤ n1 := by have := h1.1.1.1; omega
        have hEq : a * (n1 / a) = 1 + (p - 1) * k := by
          rw [Nat.mul_div_cancel' ha1]; omega
        rw [Nat.coprime_iff_gcd_eq_one]
        have hdvd1 : Nat.gcd a (p - 1) ∣ 1 := by
          have hd1 : Nat.gcd a (p - 1) ∣ a * (n1 / a) := (Nat.gcd_dvd_left _ _).trans (dvd_mul_right _ _)
          have hd2 : Nat.gcd a (p - 1) ∣ (p - 1) * k := (Nat.gcd_dvd_right _ _).trans (dvd_mul_right _ _)
          rw [hEq] at hd1
          exact (Nat.dvd_add_left hd2).mp hd1
        exact Nat.dvd_one.mp hdvd1
      have hmod_pm1 : n1 / a ≡ n2 / a [MOD p - 1] := by
        have hp_dvd_n1 : p ∣ n1 := hp_dvd_a.trans ha1
        have hp_dvd_n2 : p ∣ n2 := hp_dvd_a.trans ha2'
        have hn1_pos : 1 ≤ n1 := by have := h1.1.1.1; omega
        have hn2_pos : 1 ≤ n2 := by have := h2.1.1.1; omega
        have hcon1 : a * (n1 / a) ≡ 1 [MOD p - 1] := by
          obtain ⟨k, hk⟩ := h1_pm1 p hp_prime hp_dvd_n1
          have hEq : a * (n1 / a) = 1 + (p - 1) * k := by rw [Nat.mul_div_cancel' ha1]; omega
          rw [hEq, Nat.ModEq]; simp
        have hcon2 : a * (n2 / a) ≡ 1 [MOD p - 1] := by
          obtain ⟨k, hk⟩ := h2_pm1 p hp_prime hp_dvd_n2
          have hEq : a * (n2 / a) = 1 + (p - 1) * k := by rw [Nat.mul_div_cancel' ha2']; omega
          rw [hEq, Nat.ModEq]; simp
        exact Nat.ModEq.cancel_left_of_coprime hcop_pm1.symm (hcon1.trans hcon2.symm)
      exact (Nat.modEq_and_modEq_iff_modEq_mul hcop_pm1).mp ⟨hmod_a, hmod_pm1⟩
    have hcard_nat : F.card ≤ X / (a * D) + 1 := by
      have hinj : Set.InjOn (fun n => (n / a) / D) (F : Set ℕ) := by
        intro n1 hn1 n2 hn2 hEq
        have hm := hmod n1 hn1 n2 hn2
        have hdiv_eq : n1 / a = n2 / a := by
          dsimp only at hEq
          have h1 := Nat.div_add_mod (n1 / a) D
          have h2 := Nat.div_add_mod (n2 / a) D
          rw [Nat.ModEq] at hm
          rw [hEq, hm] at h1
          omega
        have ha1 : a ∣ n1 := (Finset.mem_filter.mp hn1).2.2.2.1
        have ha2' : a ∣ n2 := (Finset.mem_filter.mp hn2).2.2.2.1
        rw [← Nat.mul_div_cancel' ha1, ← Nat.mul_div_cancel' ha2', hdiv_eq]
      have hmaps : Set.MapsTo (fun n => (n / a) / D) (F : Set ℕ)
          ((Finset.range (X / (a * D) + 1) : Finset ℕ) : Set ℕ) := by
        intro n hn
        simp only [Finset.mem_coe, Finset.mem_range]
        have hn_le : n ≤ X := (Finset.mem_Icc.mp (Finset.mem_filter.mp hn).1).2
        rw [Nat.div_div_eq_div_mul]
        exact Nat.lt_succ_of_le (Nat.div_le_div_right hn_le)
      have := Finset.card_le_card_of_injOn (fun n => (n / a) / D) hmaps hinj
      simpa using this
    have h2D_gt : (X : ℝ).sqrt < 2 * (D : ℝ) := by
      have h1 : M + 1 ≤ 2 * D := by
        have h2p : p ≤ 2 * (p - 1) := by omega
        calc
          M + 1 ≤ a * p := hM_lt_ap
          _ ≤ a * (2 * (p - 1)) := Nat.mul_le_mul_left a h2p
          _ = 2 * D := by ring
      have hlt_sq : (X : ℝ) < ((M + 1 : ℕ) : ℝ) ^ 2 := by
        exact_mod_cast (by simpa [sq] using Nat.lt_succ_sqrt X)
      have hsqrt_lt : (X : ℝ).sqrt < ((M + 1 : ℕ) : ℝ) := by
        rw [Real.sqrt_lt' (by positivity)]
        exact hlt_sq
      have h1_real : ((M + 1 : ℕ) : ℝ) ≤ 2 * (D : ℝ) := by exact_mod_cast h1
      exact lt_of_lt_of_le hsqrt_lt h1_real
    have hX_pos : (0 : ℝ) < X := by exact_mod_cast (by omega : 0 < X)
    have hsqrt_pos : (0 : ℝ) < (X : ℝ).sqrt := Real.sqrt_pos.mpr hX_pos
    have hD_real_pos : (0 : ℝ) < D := by exact_mod_cast hD_pos
    have hdiv_le : ((X / (a * D) : ℕ) : ℝ) ≤ (X : ℝ) / ((a : ℝ) * (D : ℝ)) := by
      rw [le_div_iff₀ (mul_pos ha_pos hD_real_pos)]
      exact_mod_cast Nat.div_mul_le_self X (a * D)
    have hbound : (X : ℝ) / ((a : ℝ) * (D : ℝ)) ≤ 2 * (X : ℝ).sqrt / (a : ℝ) := by
      rw [div_le_div_iff₀ (mul_pos ha_pos hD_real_pos) ha_pos]
      have hsqX : (X : ℝ).sqrt * (X : ℝ).sqrt = (X : ℝ) := Real.mul_self_sqrt hX_pos.le
      calc
        (X : ℝ) * (a : ℝ) = ((X : ℝ).sqrt * (a : ℝ)) * (X : ℝ).sqrt := by nth_rw 1 [← hsqX]; ring
        _ ≤ ((X : ℝ).sqrt * (a : ℝ)) * (2 * (D : ℝ)) :=
            mul_le_mul_of_nonneg_left h2D_gt.le (by positivity)
        _ = 2 * (X : ℝ).sqrt * ((a : ℝ) * (D : ℝ)) := by ring
    have hcard_real : (F.card : ℝ) ≤ ((X / (a * D) : ℕ) : ℝ) + 1 := by exact_mod_cast hcard_nat
    linarith
  · rw [Finset.not_nonempty_iff_eq_empty] at hF
    rw [hF, Finset.card_empty, Nat.cast_zero]
    positivity

private lemma harmonic_sum_le_log (M : ℕ) (hM : 1 ≤ M) :
    ∑ a ∈ Finset.Icc 2 M, (1 : ℝ) / (a : ℝ) ≤ Real.log (M : ℝ) := by
  induction M with
  | zero => omega
  | succ k ih =>
    by_cases hk : k = 0
    · subst hk
      simp
    · have hk1 : 1 ≤ k := by omega
      have hIcc : Finset.Icc 2 (k + 1) = insert (k + 1) (Finset.Icc 2 k) := by
        ext x
        simp only [Finset.mem_Icc, Finset.mem_insert]
        omega
      have hnotmem : k + 1 ∉ Finset.Icc 2 k := by
        simp only [Finset.mem_Icc]; omega
      rw [hIcc, Finset.sum_insert hnotmem]
      have hk_pos : (0 : ℝ) < k := by exact_mod_cast hk1
      have hk1_pos : (0 : ℝ) < (k + 1 : ℕ) := by positivity
      have hstep : (1 : ℝ) / ((k + 1 : ℕ) : ℝ) ≤ Real.log ((k + 1 : ℕ) : ℝ) - Real.log (k : ℝ) := by
        have hpos : (0 : ℝ) < (k : ℝ) / ((k + 1 : ℕ) : ℝ) := div_pos hk_pos hk1_pos
        have hlog := Real.log_le_sub_one_of_pos hpos
        rw [Real.log_div hk_pos.ne' hk1_pos.ne'] at hlog
        have halg : (k : ℝ) / ((k + 1 : ℕ) : ℝ) - 1 = -((1 : ℝ) / ((k + 1 : ℕ) : ℝ)) := by
          push_cast
          field_simp
          ring
        linarith
      linarith [ih hk1]

end StrongGiugaGrowth

theorem OMA.solution : type_of% @AgohGiuga.agoh_giuga.variants.isStrongGiuga_growth := by
  classical
  intro G hG
  refine ⟨4, 1 + 2 / Real.log 2, fun X hX => ?_⟩
  rw [hG]
  set M := Nat.sqrt X
  have hM1 : 1 ≤ M := by
    have : 1 * 1 ≤ X := by omega
    exact Nat.le_sqrt.mpr this
  set S_all := (Finset.Icc 1 X).filter AgohGiuga.IsStrongGiuga
  set S_small := S_all.filter (fun n => n ≤ M)
  set S_big := S_all.filter (fun n => M < n)
  have hsplit : S_all.card ≤ S_small.card + S_big.card := by
    have hsub : S_all ⊆ S_small ∪ S_big := by
      intro n hn
      simp only [S_small, S_big, Finset.mem_union, Finset.mem_filter]
      by_cases hle : n ≤ M
      · exact Or.inl ⟨hn, hle⟩
      · exact Or.inr ⟨hn, lt_of_not_ge hle⟩
    exact (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
  have hsmall_le : S_small.card ≤ M := by
    have hsub : S_small ⊆ Finset.Icc 1 M := by
      intro n hn
      have h1 := (Finset.mem_filter.mp hn)
      have h2 := (Finset.mem_Icc.mp (Finset.mem_filter.mp h1.1).1)
      exact Finset.mem_Icc.mpr ⟨h2.1, h1.2⟩
    simpa using Finset.card_le_card hsub
  have hbig_sub : S_big ⊆ (Finset.Icc 2 M).biUnion (fun a =>
      (Finset.Icc 1 X).filter (fun n => AgohGiuga.IsStrongGiuga n ∧ M < n ∧ a ∣ n ∧
        M < a * maxPrime a)) := by
    intro n hn
    have h1 := Finset.mem_filter.mp hn
    have h2 := Finset.mem_filter.mp h1.1
    have hIcc := Finset.mem_Icc.mp h2.1
    obtain ⟨a, ha_Icc, ha_dvd, hM_lt⟩ := exists_divisor_of_isStrongGiuga h2.2 h1.2 hIcc.2
    exact Finset.mem_biUnion.mpr ⟨a, ha_Icc,
      Finset.mem_filter.mpr ⟨h2.1, h2.2, h1.2, ha_dvd, hM_lt⟩⟩
  have hbig_card : (S_big.card : ℝ) ≤
      ∑ a ∈ Finset.Icc 2 M, (2 * (X : ℝ).sqrt / (a : ℝ) + 1) := by
    have h1 : S_big.card ≤ ∑ a ∈ Finset.Icc 2 M,
        ((Finset.Icc 1 X).filter (fun n => AgohGiuga.IsStrongGiuga n ∧ M < n ∧ a ∣ n ∧
          M < a * maxPrime a)).card :=
      (Finset.card_le_card hbig_sub).trans Finset.card_biUnion_le
    have h1_real : (S_big.card : ℝ) ≤ ∑ a ∈ Finset.Icc 2 M,
        (((Finset.Icc 1 X).filter (fun n => AgohGiuga.IsStrongGiuga n ∧ M < n ∧ a ∣ n ∧
          M < a * maxPrime a)).card : ℝ) := by
      exact_mod_cast h1
    exact h1_real.trans (Finset.sum_le_sum fun a ha => fiber_card_le hX ha)
  have hM_le_sqrt : (M : ℝ) ≤ (X : ℝ).sqrt := by
    rw [Real.le_sqrt (by positivity) (by positivity)]
    exact_mod_cast (by simpa [sq] using Nat.sqrt_le X : M ^ 2 ≤ X)
  have hsum_eval :
      (∑ a ∈ Finset.Icc 2 M, (2 * (X : ℝ).sqrt / (a : ℝ) + 1)) ≤
        (X : ℝ).sqrt * (X : ℝ).log + (X : ℝ).sqrt := by
    rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, mul_one]
    have hfactor : (∑ a ∈ Finset.Icc 2 M, 2 * (X : ℝ).sqrt / (a : ℝ)) =
        2 * (X : ℝ).sqrt * ∑ a ∈ Finset.Icc 2 M, (1 : ℝ) / (a : ℝ) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun a _ => by ring
    rw [hfactor]
    have hharm := harmonic_sum_le_log M hM1
    have hM_pos : (0 : ℝ) < M := by exact_mod_cast hM1
    have hlogM : Real.log (M : ℝ) ≤ (X : ℝ).log / 2 := by
      calc
        Real.log (M : ℝ) ≤ Real.log ((X : ℝ).sqrt) := Real.log_le_log hM_pos hM_le_sqrt
        _ = (X : ℝ).log / 2 := Real.log_sqrt (by positivity)
    have hsqrt_nn : 0 ≤ (X : ℝ).sqrt := Real.sqrt_nonneg _
    have hterm1 : 2 * (X : ℝ).sqrt * ∑ a ∈ Finset.Icc 2 M, (1 : ℝ) / (a : ℝ) ≤
        (X : ℝ).sqrt * (X : ℝ).log := by
      have h1 : ∑ a ∈ Finset.Icc 2 M, (1 : ℝ) / (a : ℝ) ≤ (X : ℝ).log / 2 := hharm.trans hlogM
      nlinarith
    have hcard_Icc : ((Finset.Icc 2 M).card : ℝ) ≤ (X : ℝ).sqrt := by
      have : (Finset.Icc 2 M).card ≤ M := by
        simp only [Nat.card_Icc]; omega
      exact le_trans (by exact_mod_cast this) hM_le_sqrt
    linarith
  have htotal : (S_all.card : ℝ) ≤ (X : ℝ).sqrt * (X : ℝ).log + 2 * (X : ℝ).sqrt := by
    have hsplit_real : (S_all.card : ℝ) ≤ (S_small.card : ℝ) + (S_big.card : ℝ) := by
      exact_mod_cast hsplit
    have hsmall_real : (S_small.card : ℝ) ≤ (X : ℝ).sqrt :=
      le_trans (by exact_mod_cast hsmall_le) hM_le_sqrt
    linarith [hbig_card.trans hsum_eval]
  have hlog2_pos : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hlog2_le : Real.log 2 ≤ (X : ℝ).log :=
    Real.log_le_log (by norm_num) (by exact_mod_cast (by omega : 2 ≤ X))
  have htwo_le : 2 * (X : ℝ).sqrt ≤ (2 / Real.log 2) * (X : ℝ).sqrt * (X : ℝ).log := by
    have h1 : 1 ≤ (X : ℝ).log / Real.log 2 := (one_le_div hlog2_pos).mpr hlog2_le
    have hsqrt_nn : 0 ≤ (X : ℝ).sqrt := Real.sqrt_nonneg _
    have h2 : 2 * (X : ℝ).sqrt * 1 ≤ 2 * (X : ℝ).sqrt * ((X : ℝ).log / Real.log 2) :=
      mul_le_mul_of_nonneg_left h1 (by positivity)
    linarith [show 2 * (X : ℝ).sqrt * ((X : ℝ).log / Real.log 2) =
      (2 / Real.log 2) * (X : ℝ).sqrt * (X : ℝ).log by ring]
  linarith
