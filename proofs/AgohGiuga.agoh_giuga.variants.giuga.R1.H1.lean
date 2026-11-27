import OMAReductions.R_AgohGiuga_agoh_giuga_variants_giuga_R1

/-!
# Step H1 of Agoh-Giuga Conjecture (Giuga's Formulation)

We prove Giuga's theorem (1950) that every strong Giuga number is a Carmichael number:
`∀ n : ℕ, IsStrongGiuga n → IsCarmichael n`.

For each prime `p ∣ n`, reducing `1 + ∑_{i=1}^{n-1} i^{n-1}` modulo `p` over the `n / p` residue
blocks of length `p` yields `1 + (n / p) * ∑_{r=0}^{p-1} r^{n-1} ≡ 0 (mod p)`.
If `(p - 1) ∤ (n - 1)`, multiplication by a cyclic generator of `(ZMod p)ˣ` shows the inner power
sum vanishes in `ZMod p`, leaving `1 ≡ 0 (mod p)`, impossible. Hence `(p - 1) ∣ (n - 1)`, the inner
sum is `-1`, and `p ∣ (n / p - 1)`. The latter rules out `p^2 ∣ n`, giving `Squarefree n`, so
Korselt's criterion yields `IsCarmichael n`.
-/

-- Step AgohGiuga.agoh_giuga.variants.giuga.R1.H1
-- Credit: @cosformula

namespace OMA.StepAgohGiugaH1

open AgohGiuga

private lemma sum_Ioo_eq_sum_range {n k : ℕ} (hk : 0 < k) :
    ∑ i ∈ Finset.Ioo 0 n, i ^ k = ∑ i ∈ Finset.range n, i ^ k := by
  by_cases hn : n = 0
  · subst hn; simp
  have hrange : Finset.range n = insert 0 (Finset.Ioo 0 n) := by
    ext x
    simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Ioo]
    omega
  rw [hrange, Finset.sum_insert (by simp), zero_pow hk.ne', zero_add]

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

private lemma prime_conditions_of_isStrongGiuga {n p : ℕ} (hn : IsStrongGiuga n)
    (hp : p.Prime) (hpn : p ∣ n) : (p - 1) ∣ (n - 1) ∧ p ∣ n / p - 1 := by
  have : Fact p.Prime := ⟨hp⟩
  have hn1 : 1 < n := hn.1.1
  have hsub_pos : 0 < n - 1 := by omega
  have hge1 : 1 ≤ n / p := Nat.div_pos (Nat.le_of_dvd (by omega) hpn) hp.pos
  have hp_sum : p ∣ 1 + ∑ i ∈ Finset.range n, i ^ (n - 1) := by
    rw [← sum_Ioo_eq_sum_range hsub_pos]
    exact dvd_trans hpn hn.2
  have hzmod : ((1 + ∑ i ∈ Finset.range n, i ^ (n - 1) : ℕ) : ZMod p) = 0 :=
    (ZMod.natCast_eq_zero_iff _ p).mpr hp_sum
  have hsum_mod : ((∑ i ∈ Finset.range n, i ^ (n - 1) : ℕ) : ZMod p) =
      ((n / p : ℕ) : ZMod p) * ∑ r ∈ Finset.range p, (r : ZMod p) ^ (n - 1) := by
    have h := sum_range_pow_zmod_mul (n / p) p (n - 1)
    rwa [Nat.div_mul_cancel hpn] at h
  rw [Nat.cast_add, Nat.cast_one, hsum_mod] at hzmod
  by_cases hdvd : p - 1 ∣ n - 1
  · rw [sum_range_pow_zmod_eq_neg_one_of_dvd hp hsub_pos hdvd, mul_neg_one] at hzmod
    refine ⟨hdvd, ?_⟩
    rw [← ZMod.natCast_eq_zero_iff (n / p - 1) p, Nat.cast_sub hge1, Nat.cast_one]
    linear_combination -hzmod
  · rw [sum_range_pow_zmod_eq_zero_of_not_dvd hp hdvd, mul_zero, add_zero] at hzmod
    exact absurd hzmod one_ne_zero

private lemma squarefree_of_isStrongGiuga {n : ℕ} (hn : IsStrongGiuga n) : Squarefree n := by
  have hn1 : 1 < n := hn.1.1
  rw [Nat.squarefree_iff_prime_squarefree]
  intro p hp hpp
  have hpn : p ∣ n := dvd_trans (dvd_mul_right p p) hpp
  have hdvd1 : p ∣ n / p - 1 := (prime_conditions_of_isStrongGiuga hn hp hpn).2
  rcases hpp with ⟨k, hk⟩
  have hdvd2 : p ∣ n / p := ⟨k, by rw [hk, mul_assoc, Nat.mul_div_cancel_left _ hp.pos]⟩
  have hge1 : 1 ≤ n / p := Nat.div_pos (Nat.le_of_dvd (by omega) hpn) hp.pos
  have h1 : p ∣ 1 := by
    have hadd : n / p - 1 + 1 = n / p := Nat.sub_add_cancel hge1
    exact (Nat.dvd_add_right hdvd1).mp (hadd.symm ▸ hdvd2)
  exact hp.not_dvd_one h1

end OMA.StepAgohGiugaH1

theorem OMA.solution : OMA.R_AgohGiuga_agoh_giuga_variants_giuga_R1.H1 := by
  intro n hn
  exact (AgohGiuga.korselts_criterion n hn.1).mpr
    ⟨OMA.StepAgohGiugaH1.squarefree_of_isStrongGiuga hn,
      fun p hp hpn => (OMA.StepAgohGiugaH1.prime_conditions_of_isStrongGiuga hn hp hpn).1⟩
