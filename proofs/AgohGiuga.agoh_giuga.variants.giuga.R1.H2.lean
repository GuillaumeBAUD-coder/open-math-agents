import OMAReductions.R_AgohGiuga_agoh_giuga_variants_giuga_R1

/-!
# Step H2 of Agoh-Giuga reduction R1

Proves that every strong Giuga number satisfies `p ∣ (n / p - 1)` for every prime factor `p` (Giuga 1950).
-/

open scoped Nat

private lemma sum_zmod_pow_of_dvd {p k : ℕ} [Fact p.Prime] (hk : k ≠ 0) (hdvd : p - 1 ∣ k) :
    ∑ x : ZMod p, x ^ k = -1 := by
  have hp : p.Prime := Fact.out
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : ZMod p)), zero_pow hk, zero_add]
  have h1 : ∀ x ∈ Finset.univ.erase (0 : ZMod p), x ^ k = 1 := by
    intro x hx
    have hx0 : x ≠ 0 := Finset.ne_of_mem_erase hx
    obtain ⟨m, rfl⟩ := hdvd
    rw [pow_mul, ZMod.pow_card_sub_one_eq_one hx0, one_pow]
  rw [Finset.sum_congr rfl h1, Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ _),
    Finset.card_univ, ZMod.card, nsmul_eq_mul, mul_one]
  rw [Nat.cast_sub hp.one_le, ZMod.natCast_self, Nat.cast_one, zero_sub]

private lemma sum_zmod_pow_of_not_dvd {p k : ℕ} [Fact p.Prime] (hndvd : ¬ (p - 1 ∣ k)) :
    ∑ x : ZMod p, x ^ k = 0 := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := (ZMod p)ˣ)
  have hord : orderOf g = p - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_eq_fintype_card, ZMod.card_units]
  have hgk_ne : ((g : ZMod p) ^ k) ≠ 1 := by
    intro h
    apply hndvd
    rw [← hord, orderOf_dvd_iff_pow_eq_one]
    ext
    simpa [Units.val_pow_eq_pow_val] using h
  have hmul : (g : ZMod p) ^ k * ∑ x : ZMod p, x ^ k = ∑ x : ZMod p, x ^ k := by
    rw [Finset.mul_sum]
    have hrew : ∀ x : ZMod p, (g : ZMod p) ^ k * x ^ k = ((g : ZMod p) * x) ^ k := fun x =>
      (mul_pow (g : ZMod p) x k).symm
    simp_rw [hrew]
    exact Equiv.sum_comp (Equiv.mulLeft₀ (g : ZMod p) g.ne_zero) (fun x : ZMod p => x ^ k)
  have hzero : ((g : ZMod p) ^ k - 1) * ∑ x : ZMod p, x ^ k = 0 := by
    rw [sub_mul, one_mul, hmul, sub_self]
  exact (mul_eq_zero.mp hzero).resolve_left (sub_ne_zero.mpr hgk_ne)

private lemma sum_range_mul_zmod (p m : ℕ) (f : ZMod p → ZMod p) :
    ∑ i ∈ Finset.range (m * p), f (i : ZMod p) =
      (m : ZMod p) * ∑ j ∈ Finset.range p, f (j : ZMod p) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Nat.succ_mul, Finset.sum_range_add, ih]
    have hshift : ∑ j ∈ Finset.range p, f ((m * p + j : ℕ) : ZMod p) =
        ∑ j ∈ Finset.range p, f (j : ZMod p) := by
      refine Finset.sum_congr rfl fun j _ => ?_
      simp [Nat.cast_add, Nat.cast_mul]
    rw [hshift, Nat.cast_succ, add_mul, one_mul]

private lemma sum_range_eq_sum_zmod {p : ℕ} [Fact p.Prime] (f : ZMod p → ZMod p) :
    ∑ j ∈ Finset.range p, f (j : ZMod p) = ∑ x : ZMod p, f x := by
  have hp : p.Prime := Fact.out
  have : NeZero p := ⟨hp.ne_zero⟩
  symm
  refine Finset.sum_bij (fun x _ => x.val) ?_ ?_ ?_ ?_
  · intro x _
    exact Finset.mem_range.mpr (ZMod.val_lt x)
  · intro x _ y _ h
    exact (ZMod.val_injective p) h
  · intro j hj
    refine ⟨(j : ZMod p), Finset.mem_univ _, ?_⟩
    exact ZMod.val_natCast_of_lt (Finset.mem_range.mp hj)
  · intro x _
    rw [ZMod.natCast_zmod_val]

private lemma sum_Ioo_cast_zmod {a p : ℕ} [Fact p.Prime] (ha : 1 < a) (hpa : p ∣ a) :
    ((∑ i ∈ Finset.Ioo 0 a, i ^ (a - 1) : ℕ) : ZMod p) =
      ((a / p : ℕ) : ZMod p) * ∑ x : ZMod p, x ^ (a - 1) := by
  have ha1 : a - 1 ≠ 0 := by omega
  have hrange : Finset.range a = insert 0 (Finset.Ioo 0 a) := by
    ext x
    simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Ioo]
    omega
  have hsum_eq : ∑ i ∈ Finset.Ioo 0 a, i ^ (a - 1) = ∑ i ∈ Finset.range a, i ^ (a - 1) := by
    rw [hrange, Finset.sum_insert (by simp), zero_pow ha1, zero_add]
  rw [hsum_eq, Nat.cast_sum]
  simp_rw [Nat.cast_pow]
  have hmul : a / p * p = a := Nat.div_mul_cancel hpa
  have hstep : ∑ i ∈ Finset.range a, (i : ZMod p) ^ (a - 1) =
      ∑ i ∈ Finset.range (a / p * p), (i : ZMod p) ^ (a - 1) := by
    rw [hmul]
  rw [hstep, sum_range_mul_zmod p (a / p) (fun x : ZMod p => x ^ (a - 1)),
    sum_range_eq_sum_zmod (fun x : ZMod p => x ^ (a - 1))]

theorem OMA.solution : OMA.R_AgohGiuga_agoh_giuga_variants_giuga_R1.H2 := by
  intro a hsg p hp
  have ha : a.Composite := hsg.1
  have ha1 : 1 < a := ha.1
  have ha_sub_ne : a - 1 ≠ 0 := by omega
  have hdiv : a ∣ 1 + ∑ i ∈ Finset.Ioo 0 a, i ^ (a - 1) := hsg.2
  have hp_prime : p.Prime := Nat.prime_of_mem_primeFactors hp
  have hpa : p ∣ a := Nat.dvd_of_mem_primeFactors hp
  have : Fact p.Prime := ⟨hp_prime⟩
  have hp_div : p ∣ 1 + ∑ i ∈ Finset.Ioo 0 a, i ^ (a - 1) := hpa.trans hdiv
  have hz : ((1 + ∑ i ∈ Finset.Ioo 0 a, i ^ (a - 1) : ℕ) : ZMod p) = 0 :=
    (ZMod.natCast_eq_zero_iff _ p).mpr hp_div
  rw [Nat.cast_add, Nat.cast_one, sum_Ioo_cast_zmod ha1 hpa] at hz
  have hdvd : p - 1 ∣ a - 1 := by
    by_contra hndvd
    rw [sum_zmod_pow_of_not_dvd hndvd, mul_zero, add_zero] at hz
    exact one_ne_zero hz
  rw [sum_zmod_pow_of_dvd ha_sub_ne hdvd, mul_neg_one] at hz
  have hdiv_eq : ((a / p : ℕ) : ZMod p) = 1 := by
    linear_combination -hz
  have hdiv_ge : 1 ≤ a / p := Nat.div_pos (Nat.le_of_dvd (by omega) hpa) hp_prime.pos
  rw [← ZMod.natCast_eq_zero_iff, Nat.cast_sub hdiv_ge, Nat.cast_one, hdiv_eq, sub_self]
