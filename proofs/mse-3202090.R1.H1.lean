import OMAReductions.R_mse_3202090_R1

-- Step mse-3202090.R1.H1: hypothesis H1 of reduction mse-3202090.R1
-- Credit: @nnkostov

/-!
Given odd primes `p ≠ q` and exponents `n, m > 1` with `p^n - p = q^m - q`:
`p` divides `q^(m-1) - 1` exactly once (not `p^2`), because `p^n - p = p(p^(n-1) - 1)`
has `p`-adic valuation `1` and `gcd(p, q) = 1`. Working in `(ZMod p)ˣ` with
`d = orderOf (q : ZMod p)`, we have `d ∣ p - 1` and `d ∣ m - 1`, and writing
`q^(p-1) - 1 = (q^d - 1) * S` with `S ≡ (p - 1) / d ≢ 0 (mod p)` shows `¬ p^2 ∣ q^(p-1) - 1`
(otherwise `p^2 ∣ q^d - 1 ∣ q^(m-1) - 1`). Likewise writing `m - 1 = d * k` gives
`q^(m-1) - 1 = (q^d - 1) * S'` with `S' ≡ k (mod p)`, forcing `¬ p ∣ m - 1`.
Applying this symmetrically to `(p, q, n, m)` and `(q, p, m, n)` yields all four claims.
-/

private lemma pow_sub_one_eq_mul_geom_sum (x r : ℕ) (hx : 1 ≤ x) :
    x ^ r - 1 = (x - 1) * ∑ i ∈ Finset.range r, x ^ i := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [Finset.sum_range_succ, mul_add, ← ih]
    have h1 : 1 ≤ x ^ r := Nat.one_le_pow r x (by omega)
    have h2 : 1 ≤ x ^ (r + 1) := Nat.one_le_pow (r + 1) x (by omega)
    zify [hx, h1, h2]
    ring

private lemma obstructions_one (p q n m : ℕ) (hp : p.Prime) (hq : q.Prime) (hne : p ≠ q)
    (hn : 1 < n) (hm : 1 < m) (heq : p ^ n - p = q ^ m - q) :
    (¬ p ^ 2 ∣ q ^ (p - 1) - 1) ∧ (¬ p ∣ m - 1) := by
  let _ : Fact p.Prime := ⟨hp⟩
  have hpn : p ^ n - p = p * (p ^ (n - 1) - 1) := by
    have hpow : p ^ n = p * p ^ (n - 1) := by
      calc
        p ^ n = p ^ ((n - 1) + 1) := by rw [Nat.sub_add_cancel (by omega)]
        _ = p ^ (n - 1) * p := pow_succ p (n - 1)
        _ = p * p ^ (n - 1) := mul_comm _ _
    rw [hpow]
    conv_lhs => rhs; rw [← mul_one p]
    rw [← Nat.mul_sub]
  have hqm : q ^ m - q = q * (q ^ (m - 1) - 1) := by
    have hpow : q ^ m = q * q ^ (m - 1) := by
      calc
        q ^ m = q ^ ((m - 1) + 1) := by rw [Nat.sub_add_cancel (by omega)]
        _ = q ^ (m - 1) * q := pow_succ q (m - 1)
        _ = q * q ^ (m - 1) := mul_comm _ _
    rw [hpow]
    conv_lhs => rhs; rw [← mul_one q]
    rw [← Nat.mul_sub]
  have hp_ndvd_pn : ¬ p ∣ p ^ (n - 1) - 1 := by
    intro h
    have hp_dvd_pow : p ∣ p ^ (n - 1) := dvd_pow_self p (by omega)
    have h1 : 1 ≤ p ^ (n - 1) := Nat.one_le_pow _ _ hp.pos
    have hdiff : p ∣ p ^ (n - 1) - (p ^ (n - 1) - 1) := Nat.dvd_sub hp_dvd_pow h
    have he1 : p ^ (n - 1) - (p ^ (n - 1) - 1) = 1 := by omega
    rw [he1] at hdiff
    exact hp.not_dvd_one hdiff
  have hp2_ndvd_lhs : ¬ p ^ 2 ∣ p ^ n - p := by
    intro h
    rw [hpn, sq] at h
    exact hp_ndvd_pn ((Nat.mul_dvd_mul_iff_left hp.pos).mp h)
  have hp2_ndvd_qm : ¬ p ^ 2 ∣ q ^ (m - 1) - 1 := by
    intro h
    exact hp2_ndvd_lhs (heq ▸ hqm ▸ dvd_mul_of_dvd_right h q)
  have hcop_pq : Nat.Coprime p q := (Nat.coprime_primes hp hq).mpr hne
  have hp_dvd_qm : p ∣ q ^ (m - 1) - 1 := by
    have hp_dvd : p ∣ q * (q ^ (m - 1) - 1) := by
      rw [← hqm, ← heq, hpn]
      exact dvd_mul_right p _
    exact hcop_pq.dvd_of_dvd_mul_left hp_dvd
  have hqm1 : 1 ≤ q ^ (m - 1) := Nat.one_le_pow _ _ hq.pos
  have hqz : (q : ZMod p) ≠ 0 := by
    rw [ne_eq, ZMod.natCast_eq_zero_iff]
    intro hdvd
    exact hne ((hq.dvd_iff_eq hp.ne_one).mp hdvd).symm
  have hqm_z : (q : ZMod p) ^ (m - 1) = 1 := by
    have hz : ((q ^ (m - 1) - 1 : ℕ) : ZMod p) = 0 :=
      (ZMod.natCast_eq_zero_iff _ p).mpr hp_dvd_qm
    rw [Nat.cast_sub hqm1, Nat.cast_pow, Nat.cast_one, sub_eq_zero] at hz
    exact hz
  set d := orderOf (q : ZMod p)
  have hd_m : d ∣ m - 1 := orderOf_dvd_iff_pow_eq_one.mpr hqm_z
  have hd_p : d ∣ p - 1 :=
    orderOf_dvd_iff_pow_eq_one.mpr (ZMod.pow_card_sub_one_eq_one hqz)
  have hp1_pos : 0 < p - 1 := Nat.sub_pos_of_lt hp.one_lt
  have hd_pos : 0 < d := Nat.pos_of_dvd_of_pos hd_p hp1_pos
  have hd_lt : d < p := lt_of_le_of_lt (Nat.le_of_dvd hp1_pos hd_p) (by omega)
  have hqd1 : 1 ≤ q ^ d := Nat.one_le_pow _ _ hq.pos
  have hp_dvd_qd : p ∣ q ^ d - 1 := by
    rw [← ZMod.natCast_eq_zero_iff, Nat.cast_sub hqd1, Nat.cast_pow, Nat.cast_one, sub_eq_zero]
    exact pow_orderOf_eq_one (q : ZMod p)
  have hsum_zmod : ∀ r : ℕ, ((∑ i ∈ Finset.range r, (q ^ d) ^ i : ℕ) : ZMod p) = (r : ZMod p) := by
    intro r
    push_cast
    have hqd_z : (q : ZMod p) ^ d = 1 := pow_orderOf_eq_one (q : ZMod p)
    simp [hqd_z]
  constructor
  · intro hp2_dvd_fermat
    obtain ⟨r, hr_eq⟩ := hd_p
    set S := ∑ i ∈ Finset.range r, (q ^ d) ^ i
    have hfac : q ^ (p - 1) - 1 = (q ^ d - 1) * S := by
      rw [hr_eq, pow_mul]
      exact pow_sub_one_eq_mul_geom_sum (q ^ d) r hqd1
    have hr_pos : 0 < r := by
      by_contra hr0
      have hr0' : r = 0 := by omega
      rw [hr0', mul_zero] at hr_eq
      omega
    have hr_lt : r < p := by
      have hle : r ≤ d * r := Nat.le_mul_of_pos_left r hd_pos
      omega
    have hp_ndvd_r : ¬ p ∣ r := Nat.not_dvd_of_pos_of_lt hr_pos hr_lt
    have hp_ndvd_S : ¬ p ∣ S := by
      rw [← ZMod.natCast_eq_zero_iff, hsum_zmod r, ZMod.natCast_eq_zero_iff]
      exact hp_ndvd_r
    have hcop_p2S : Nat.Coprime (p ^ 2) S := (hp.coprime_iff_not_dvd.mpr hp_ndvd_S).pow_left 2
    rw [hfac] at hp2_dvd_fermat
    have hp2_dvd_qd : p ^ 2 ∣ q ^ d - 1 := hcop_p2S.dvd_of_dvd_mul_right hp2_dvd_fermat
    obtain ⟨k, hk_eq⟩ := hd_m
    have hqd_dvd_qm : q ^ d - 1 ∣ q ^ (m - 1) - 1 := by
      rw [hk_eq, pow_mul, pow_sub_one_eq_mul_geom_sum (q ^ d) k hqd1]
      exact dvd_mul_right _ _
    exact hp2_ndvd_qm (hp2_dvd_qd.trans hqd_dvd_qm)
  · intro hp_dvd_m1
    obtain ⟨k, hk_eq⟩ := hd_m
    have hp_ndvd_d : ¬ p ∣ d := Nat.not_dvd_of_pos_of_lt hd_pos hd_lt
    have hp_dvd_k : p ∣ k := by
      rw [hk_eq] at hp_dvd_m1
      exact hp.dvd_mul.mp hp_dvd_m1 |>.resolve_left hp_ndvd_d
    set S' := ∑ i ∈ Finset.range k, (q ^ d) ^ i
    have hp_dvd_S' : p ∣ S' := by
      rw [← ZMod.natCast_eq_zero_iff, hsum_zmod k, ZMod.natCast_eq_zero_iff]
      exact hp_dvd_k
    have hfac' : q ^ (m - 1) - 1 = (q ^ d - 1) * S' := by
      rw [hk_eq, pow_mul]
      exact pow_sub_one_eq_mul_geom_sum (q ^ d) k hqd1
    exact hp2_ndvd_qm (by rw [hfac', sq]; exact mul_dvd_mul hp_dvd_qd hp_dvd_S')

theorem OMA.solution : OMA.R_mse_3202090_R1.H1 := by
  intro p q n m hp hq _ _ hqp hn hm heq
  have hpq_ne : p ≠ q := ne_of_gt hqp
  have h1 := obstructions_one p q n m hp hq hpq_ne hn hm heq
  have h2 := obstructions_one q p m n hq hp hpq_ne.symm hm hn heq.symm
  exact ⟨h1.1, h2.1, h1.2, h2.2⟩
