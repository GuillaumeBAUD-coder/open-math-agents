import OMAStatements.S_oeis_a384531
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Nat.Factorization.Induction
import Mathlib.Tactic

/-!
Multiplicative + prime-power proof of Schulte's adjacent-gcd sum (OEIS A384531):
the sum over ZMod n is multiplicative by Chinese remainder theorem, and on
prime powers p^e it reduces via coprimality of consecutive gcd terms to
2 * sum_{i < p^e} gcd(i, p^e) - p^e = ((2*e + 1)*p - 2*e) * p^(e - 1).
-/

theorem OMA.solution : type_of% @OMA.S_oeis_a384531.main := by
  let S : ℕ → ℕ := fun n => ∑ i ∈ Finset.range n, (i + 1).gcd n * (i + 2).gcd n
  have hgcd_mod : ∀ a b m : ℕ, a % m = b % m → a.gcd m = b.gcd m := by
    intro a b m h
    rw [Nat.gcd_comm a m, Nat.gcd_rec, h, ← Nat.gcd_rec, Nat.gcd_comm]
  have hgcd_mul_coprime : ∀ k u v : ℕ, u.Coprime v → k.gcd (u * v) = k.gcd u * k.gcd v := by
    intro k u v huv
    refine Nat.dvd_antisymm ?_ ?_
    · have hdvd : k.gcd (u * v) ∣ u * v := Nat.gcd_dvd_right k (u * v)
      have heq := (Nat.gcd_mul_gcd_eq_iff_dvd_mul_of_coprime huv).mpr hdvd
      rw [← heq]
      exact Nat.mul_dvd_mul
        (Nat.dvd_gcd ((Nat.gcd_dvd_left _ _).trans (Nat.gcd_dvd_left k (u * v)))
          (Nat.gcd_dvd_right _ _))
        (Nat.dvd_gcd ((Nat.gcd_dvd_left _ _).trans (Nat.gcd_dvd_left k (u * v)))
          (Nat.gcd_dvd_right _ _))
    · exact Nat.dvd_gcd
        ((huv.gcd_both k k).mul_dvd_of_dvd_of_dvd (k.gcd_dvd_left u) (k.gcd_dvd_left v))
        (Nat.mul_dvd_mul (k.gcd_dvd_right u) (k.gcd_dvd_right v))
  have hS_mul : ∀ u v : ℕ, 1 < u → 1 < v → u.Coprime v → S (u * v) = S u * S v := by
    intro u v hu hv huv
    have hS_eq_SZ : ∀ (n : ℕ) [NeZero n],
        S n = ∑ x : ZMod n, (x.val + 1).gcd n * (x.val + 2).gcd n := by
      intro n hn
      obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (NeZero.ne n)
      exact (Fin.sum_univ_eq_sum_range
        (fun k => (k + 1).gcd (m + 1) * (k + 2).gcd (m + 1)) (m + 1)).symm
    have _ : NeZero u := ⟨by omega⟩
    have _ : NeZero v := ⟨by omega⟩
    have _ : NeZero (u * v) := ⟨Nat.mul_ne_zero (by omega) (by omega)⟩
    let e := ZMod.chineseRemainder huv
    have hsplit : ∀ x : ZMod (u * v),
        (x.val + 1).gcd (u * v) * (x.val + 2).gcd (u * v) =
          (((e x).1.val + 1).gcd u * ((e x).1.val + 2).gcd u) *
          (((e x).2.val + 1).gcd v * ((e x).2.val + 2).gcd v) := by
      intro x
      have hx_cast : e x = ((x.val : ZMod u), (x.val : ZMod v)) := by
        conv_lhs => rw [← ZMod.natCast_zmod_val x]
        rw [map_natCast]
        rfl
      have hy_mod : (e x).1.val % u = x.val % u := by
        have h1 : (((e x).1.val : ℕ) : ZMod u) = (x.val : ZMod u) := by
          rw [ZMod.natCast_zmod_val, hx_cast]
        exact (ZMod.natCast_eq_natCast_iff _ _ u).mp h1
      have hz_mod : (e x).2.val % v = x.val % v := by
        have h1 : (((e x).2.val : ℕ) : ZMod v) = (x.val : ZMod v) := by
          rw [ZMod.natCast_zmod_val, hx_cast]
        exact (ZMod.natCast_eq_natCast_iff _ _ v).mp h1
      have h1u : (x.val + 1).gcd u = ((e x).1.val + 1).gcd u :=
        hgcd_mod _ _ u (by simp [Nat.add_mod, hy_mod])
      have h2u : (x.val + 2).gcd u = ((e x).1.val + 2).gcd u :=
        hgcd_mod _ _ u (by simp [Nat.add_mod, hy_mod])
      have h1v : (x.val + 1).gcd v = ((e x).2.val + 1).gcd v :=
        hgcd_mod _ _ v (by simp [Nat.add_mod, hz_mod])
      have h2v : (x.val + 2).gcd v = ((e x).2.val + 2).gcd v :=
        hgcd_mod _ _ v (by simp [Nat.add_mod, hz_mod])
      rw [hgcd_mul_coprime _ _ _ huv, hgcd_mul_coprime _ _ _ huv, h1u, h2u, h1v, h2v]
      ring
    rw [hS_eq_SZ (u * v), hS_eq_SZ u, hS_eq_SZ v]
    simp_rw [hsplit]
    change ∑ x : ZMod (u * v),
        (((e.toEquiv x).1.val + 1).gcd u * ((e.toEquiv x).1.val + 2).gcd u) *
        (((e.toEquiv x).2.val + 1).gcd v * ((e.toEquiv x).2.val + 2).gcd v) =
      (∑ x : ZMod u, (x.val + 1).gcd u * (x.val + 2).gcd u) *
      (∑ x : ZMod v, (x.val + 1).gcd v * (x.val + 2).gcd v)
    rw [Fintype.sum_equiv e.toEquiv _ (fun p =>
      ((p.1.val + 1).gcd u * (p.1.val + 2).gcd u) *
      ((p.2.val + 1).gcd v * (p.2.val + 2).gcd v)) (fun _ => rfl)]
    rw [Fintype.sum_prod_type]
    simp_rw [← Finset.mul_sum]
    rw [← Finset.sum_mul]
  have hsum_mul : ∀ (g : ℕ → ℕ) (m k : ℕ),
      ∑ i ∈ Finset.range (m * k), g i =
        ∑ q ∈ Finset.range m, ∑ r ∈ Finset.range k, g (q * k + r) := by
    intro g m k
    induction m with
    | zero => simp
    | succ m ih =>
      rw [Nat.succ_mul, Finset.sum_range_add, Finset.sum_range_succ, ih]
  have hH_pow : ∀ p e : ℕ, p.Prime → 0 < e →
      ∑ i ∈ Finset.range (p ^ e), i.gcd (p ^ e) = p ^ e + e * p ^ (e - 1) * (p - 1) := by
    intro p e hp he
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero he.ne'
    induction k with
    | zero =>
      simp only [pow_one, Nat.sub_self, pow_zero, mul_one]
      obtain ⟨q, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hp.ne_zero
      rw [Finset.sum_range_succ']
      simp only [Nat.gcd_zero_left]
      have hones : ∑ i ∈ Finset.range q, (i + 1).gcd (q + 1) = q := by
        have : ∀ i ∈ Finset.range q, (i + 1).gcd (q + 1) = 1 := by
          intro i hi
          rw [Finset.mem_range] at hi
          have hnd : ¬ (q + 1) ∣ i + 1 := Nat.not_dvd_of_pos_of_lt (by omega) (by omega)
          exact (hp.coprime_iff_not_dvd.mpr hnd).symm.gcd_eq_one
        rw [Finset.sum_congr rfl this, Finset.sum_const, Finset.card_range, smul_eq_mul, mul_one]
      rw [hones, add_comm]
      omega
    | succ k ih =>
      have ih' := ih (by omega)
      rw [pow_succ (p : ℕ) (k + 1), hsum_mul]
      have hsplit_r : ∀ q : ℕ,
          ∑ r ∈ Finset.range p, (q * p + r).gcd (p ^ (k + 1) * p) =
            p * q.gcd (p ^ (k + 1)) + (p - 1) := by
        intro q
        obtain ⟨q', hq'⟩ := Nat.exists_eq_succ_of_ne_zero hp.ne_zero
        nth_rw 1 [hq']
        rw [Finset.sum_range_succ']
        have h0 : (q * p + 0).gcd (p ^ (k + 1) * p) = p * q.gcd (p ^ (k + 1)) := by
          rw [Nat.add_zero, Nat.gcd_mul_right, mul_comm]
        have hrest : ∑ r ∈ Finset.range q', (q * p + (r + 1)).gcd (p ^ (k + 1) * p) = p - 1 := by
          have h1 : ∀ r ∈ Finset.range q', (q * p + (r + 1)).gcd (p ^ (k + 1) * p) = 1 := by
            intro r hr
            rw [Finset.mem_range] at hr
            have hnd : ¬ p ∣ r + 1 := Nat.not_dvd_of_pos_of_lt (by omega) (by omega)
            have hcop_p : (q * p + (r + 1)).Coprime p :=
              (Nat.coprime_mul_right_add_left (r + 1) p q).mpr (hp.coprime_iff_not_dvd.mpr hnd).symm
            rw [← pow_succ]
            exact (hcop_p.pow_right (k + 2)).gcd_eq_one
          rw [Finset.sum_congr rfl h1, Finset.sum_const, Finset.card_range, smul_eq_mul, mul_one]
          omega
        rw [h0, hrest, add_comm]
      simp_rw [hsplit_r, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const,
        Finset.card_range, smul_eq_mul, ih']
      have h1 : k.succ - 1 = k := by omega
      have h2 : (k + 1).succ - 1 = k + 1 := by omega
      rw [h1, h2, Nat.mul_add]
      have h3 : p * (k.succ * p ^ k * (p - 1)) = k.succ * (p * p ^ k) * (p - 1) := by ring
      rw [h3, ← pow_succ']
      simp only [Nat.succ_eq_add_one, pow_succ]
      ring
  have ha_mul : ∀ u v : ℕ, 0 < u → 0 < v → u.Coprime v →
      OMA.S_oeis_a384531.a (u * v) = OMA.S_oeis_a384531.a u * OMA.S_oeis_a384531.a v := by
    intro u v hu hv huv
    have hdisj : Disjoint u.primeFactors v.primeFactors := huv.disjoint_primeFactors
    have hpf : (u * v).primeFactors = u.primeFactors ∪ v.primeFactors :=
      Nat.primeFactors_mul hu.ne' hv.ne'
    have hfac_u : ∀ p ∈ u.primeFactors, (u * v).factorization p = u.factorization p := by
      intro p hp
      have hpv : p ∉ v.primeFactors := Finset.disjoint_left.mp hdisj hp
      have hfv0 : v.factorization p = 0 := by
        by_contra hne
        exact hpv (Nat.mem_primeFactors.mpr ⟨Nat.prime_of_mem_primeFactors hp,
          Nat.dvd_of_factorization_pos hne, hv.ne'⟩)
      rw [Nat.factorization_mul_apply_of_coprime huv, hfv0, add_zero]
    have hfac_v : ∀ p ∈ v.primeFactors, (u * v).factorization p = v.factorization p := by
      intro p hp
      have hpu : p ∉ u.primeFactors := Finset.disjoint_right.mp hdisj hp
      have hfu0 : u.factorization p = 0 := by
        by_contra hne
        exact hpu (Nat.mem_primeFactors.mpr ⟨Nat.prime_of_mem_primeFactors hp,
          Nat.dvd_of_factorization_pos hne, hu.ne'⟩)
      rw [Nat.factorization_mul_apply_of_coprime huv, hfu0, zero_add]
    dsimp [OMA.S_oeis_a384531.a]
    rw [hpf, Finset.prod_union hdisj]
    congr 1
    · refine Finset.prod_congr rfl fun p hp => ?_
      rw [hfac_u p hp]
    · refine Finset.prod_congr rfl fun p hp => ?_
      rw [hfac_v p hp]
  intro n
  refine Nat.recOnPosPrimePosCoprime (motive := fun n => 0 < n → OMA.S_oeis_a384531.a n = S n)
    ?_ ?_ ?_ ?_ n
  · intro p e hp he _
    have ha_pe : OMA.S_oeis_a384531.a (p ^ e) = ((2 * e + 1) * p - 2 * e) * p ^ (e - 1) := by
      dsimp [OMA.S_oeis_a384531.a]
      rw [Nat.primeFactors_pow p he.ne', hp.primeFactors, Finset.prod_singleton,
        Nat.factorization_pow_self hp]
    let N := p ^ e
    have hN1 : 1 < N := Nat.one_lt_pow he.ne' hp.one_lt
    have hcop_pair : ∀ i : ℕ, (i + 1).gcd N = 1 ∨ (i + 2).gcd N = 1 := by
      intro i
      by_contra hboth
      push Not at hboth
      obtain ⟨a, _, ha_eq⟩ := (Nat.dvd_prime_pow hp).mp ((i + 1).gcd_dvd_right N)
      obtain ⟨b, _, hb_eq⟩ := (Nat.dvd_prime_pow hp).mp ((i + 2).gcd_dvd_right N)
      have ha0 : a ≠ 0 := fun h => hboth.1 (by rw [ha_eq, h, pow_zero])
      have hb0 : b ≠ 0 := fun h => hboth.2 (by rw [hb_eq, h, pow_zero])
      have hp1 : p ∣ i + 1 := (dvd_pow_self p ha0).trans (ha_eq ▸ (i + 1).gcd_dvd_left N)
      have hp2 : p ∣ i + 2 := (dvd_pow_self p hb0).trans (hb_eq ▸ (i + 2).gcd_dvd_left N)
      have hp_one : p ∣ 1 := by
        have := Nat.dvd_sub hp2 hp1
        simpa [show i + 2 - (i + 1) = 1 by omega] using this
      exact hp.not_dvd_one hp_one
    have hsum_rel : S N + N =
        (∑ i ∈ Finset.range N, (i + 1).gcd N) + (∑ i ∈ Finset.range N, (i + 2).gcd N) := by
      have hterm : ∀ i : ℕ, (i + 1).gcd N * (i + 2).gcd N + 1 = (i + 1).gcd N + (i + 2).gcd N := by
        intro i
        rcases hcop_pair i with h | h <;> rw [h] <;> ring
      calc S N + N
          = ∑ i ∈ Finset.range N, ((i + 1).gcd N * (i + 2).gcd N + 1) := by
            dsimp [S]
            rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, smul_eq_mul, mul_one]
        _ = ∑ i ∈ Finset.range N, ((i + 1).gcd N + (i + 2).gcd N) :=
            Finset.sum_congr rfl fun i _ => hterm i
        _ = (∑ i ∈ Finset.range N, (i + 1).gcd N) + (∑ i ∈ Finset.range N, (i + 2).gcd N) :=
            Finset.sum_add_distrib
    have hshift1 : ∑ i ∈ Finset.range N, (i + 2).gcd N = ∑ i ∈ Finset.range N, (i + 1).gcd N := by
      obtain ⟨M, hM⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : N ≠ 0)
      rw [hM, Finset.sum_range_succ, Finset.sum_range_succ']
      have htop : (M + 2).gcd (M + 1) = 1 := by
        rw [show M + 2 = 1 + (M + 1) by omega, Nat.gcd_add_self_left, Nat.gcd_one_left]
      have hbot : (0 + 1).gcd (M + 1) = 1 := Nat.gcd_one_left (M + 1)
      have hmid : ∑ i ∈ Finset.range M, (i + 2).gcd (M + 1) =
          ∑ i ∈ Finset.range M, (i + 1 + 1).gcd (M + 1) := rfl
      rw [htop, hbot, hmid, add_comm]
    have hshift2 : ∑ i ∈ Finset.range N, (i + 1).gcd N = ∑ i ∈ Finset.range N, i.gcd N := by
      obtain ⟨M, hM⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : N ≠ 0)
      rw [hM, Finset.sum_range_succ, Finset.sum_range_succ']
      simp [add_comm]
    have hS_eq : S N + N = 2 * (N + e * p ^ (e - 1) * (p - 1)) := by
      rw [hsum_rel, hshift1, hshift2, ← two_mul]
      dsimp [N]
      rw [hH_pow p e hp he]
    have hp_ge2 : 2 ≤ p := hp.two_le
    have hmul_pow : p * p ^ (e - 1) = N := by
      dsimp [N]
      obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero he.ne'
      simp [pow_succ']
    have h2e_le : 2 * e ≤ (2 * e + 1) * p := by nlinarith
    have halg : ((2 * e + 1) * p - 2 * e) * p ^ (e - 1) + N =
        2 * (N + e * p ^ (e - 1) * (p - 1)) := by
      zify [h2e_le, show 1 ≤ p by omega]
      have hmul_z : (p : ℤ) * (p ^ (e - 1) : ℤ) = (N : ℤ) := by exact_mod_cast hmul_pow
      linear_combination hmul_z
    rw [← halg, ← ha_pe] at hS_eq
    exact (Nat.add_right_cancel hS_eq).symm
  · intro h; omega
  · intro _
    dsimp [OMA.S_oeis_a384531.a, S]
    simp
  · intro u v hu hv huv ihu ihv _
    rw [ha_mul u v (by omega) (by omega) huv, ihu (by omega), ihv (by omega),
      hS_mul u v hu hv huv]
