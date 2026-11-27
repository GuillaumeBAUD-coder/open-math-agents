import OMAReductions.R_AgohGiuga_agoh_giuga_variants_giuga_R1

-- Step AgohGiuga.agoh_giuga.variants.giuga.R1.H2: hypothesis H2 of reduction
-- AgohGiuga.agoh_giuga.variants.giuga.R1
-- Credit: @ihateSAS
-- H2 := ∀ n : ℕ, IsStrongGiuga n → ∀ p ∈ n.primeFactors, p ∣ (n / p - 1)
--
-- Giuga (1950).  Let `n = p * m` with `p` prime, `d = n - 1`, and work in `ZMod p`.
-- Every integer `i` is congruent modulo `p` to its residue, so the `< p` blocks of
-- `{0, ..., n - 1}` each contribute the same amount:
--   `∑_{i < n} i ^ d ≡ m * ∑_{r ∈ ZMod p} r ^ d  (mod p)`.
-- The left side is `≡ -1`, since `n = p * m ≡ 0`.  For the right side, multiplication by
-- a nonzero `t` permutes `ZMod p`, so `(t ^ d - 1) * ∑ r ^ d = 0`: either
-- `∑ r ^ d = 0`, which contradicts `= -1`, or every unit satisfies `t ^ d = 1`, in which
-- case the sum over nonzero residues is `p - 1 ≡ -1`, forcing `m ≡ 1 (mod p)`.

namespace OMA.AgohGiugaH2

/-- Sums of a `p`-periodic function over `m` complete blocks. -/
theorem sum_range_mul_periodic {R : Type*} [AddCommMonoid R] (p : ℕ)
    (f : ℕ → R) (hf : ∀ i, f (i + p) = f i) (m : ℕ) :
    ∑ i ∈ Finset.range (m * p), f i = m • ∑ i ∈ Finset.range p, f i := by
  induction m with
  | zero => simp
  | succ m ih =>
    have hshift : ∀ k j : ℕ, f (k * p + j) = f j := by
      intro k
      induction k with
      | zero => intro j; simp
      | succ k ihk =>
        intro j
        have e : (k + 1) * p + j = (k * p + j) + p := by ring
        rw [e, hf, ihk j]
    rw [Nat.succ_mul, Finset.sum_range_add, ih]
    have hblock : ∑ x ∈ Finset.range p, f (m * p + x) = ∑ x ∈ Finset.range p, f x := by
      refine Finset.sum_congr rfl (fun x _ => ?_)
      exact hshift m x
    rw [hblock, succ_nsmul]

end OMA.AgohGiugaH2

open AgohGiuga OMA.AgohGiugaH2 in
theorem OMA.solution : OMA.R_AgohGiuga_agoh_giuga_variants_giuga_R1.H2 := by
  intro n hsg p hp_mem
  obtain ⟨hp_prime, hp_dvd, hn_ne⟩ := Nat.mem_primeFactors.mp hp_mem
  haveI : Fact p.Prime := ⟨hp_prime⟩
  obtain ⟨hn_gt, hn_np⟩ := hsg.1
  obtain ⟨k, hk⟩ := hsg.2
  set m := n / p with hm_def
  have hn_eq : n = p * m := by
    have h := Nat.mul_div_cancel' hp_dvd
    rw [hm_def]; exact h.symm
  have hp2 : 2 ≤ p := hp_prime.two_le
  set d := n - 1 with hd_def
  have hd1 : 1 ≤ d := by omega
  -- `n` is `0` in `ZMod p`.
  have hn_zero : (n : ZMod p) = 0 := by
    rw [hn_eq, Nat.cast_mul, ZMod.natCast_self, zero_mul]
  -- Step 1: the Giuga sum is `-1` modulo `p`.
  have hsum1 : ((∑ i ∈ Finset.Ioo 0 n, i ^ d : ℕ) : ZMod p) = -1 := by
    have h1 : ((1 + ∑ i ∈ Finset.Ioo 0 n, i ^ d : ℕ) : ZMod p) = 0 := by
      rw [hk, Nat.cast_mul, hn_zero, zero_mul]
    push_cast at h1 ⊢
    linear_combination h1
  -- Step 2: the sum over `{0, ..., n-1}` is `m` times the sum over one period.
  have hper : ∀ i : ℕ, ((i + p : ℕ) : ZMod p) ^ d = ((i : ℕ) : ZMod p) ^ d := by
    intro i
    have hcast : ((i + p : ℕ) : ZMod p) = ((i : ℕ) : ZMod p) := by
      push_cast [ZMod.natCast_self]
      ring
    rw [hcast]
  have hblock := sum_range_mul_periodic (R := ZMod p) p (fun i => ((i : ℕ) : ZMod p) ^ d) hper m
  rw [nsmul_eq_mul] at hblock
  -- the sum over `range p` is the sum over `ZMod p`
  have himg : (Finset.range p).image (fun i => ((i : ℕ) : ZMod p)) = Finset.univ := by
    refine Finset.eq_univ_of_forall (fun r => ?_)
    exact Finset.mem_image.mpr ⟨r.val, by rw [Finset.mem_range]; exact ZMod.val_lt r,
      by rw [ZMod.natCast_zmod_val]⟩
  have hbij : ∑ i ∈ Finset.range p, ((i : ℕ) : ZMod p) ^ d = ∑ r : ZMod p, r ^ d := by
    conv_rhs => rw [← himg]
    rw [Finset.sum_image]
    intro i hi j hj hij
    rw [Finset.mem_coe, Finset.mem_range] at hi hj
    have h := (ZMod.natCast_eq_natCast_iff' i j p).mp hij
    rw [Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt hj] at h
    exact h
  set F : ZMod p := ∑ r : ZMod p, r ^ d with hF_def
  have hcast' : ((∑ i ∈ Finset.Ioo 0 n, i ^ d : ℕ) : ZMod p)
      = ∑ i ∈ Finset.range (m * p), ((i : ℕ) : ZMod p) ^ d := by
    rw [Nat.cast_sum]
    simp only [Nat.cast_pow]
    have hsub : Finset.Ioo 0 n ⊆ Finset.range (m * p) := by
      intro x hx
      rw [Finset.mem_Ioo] at hx
      rw [Finset.mem_range]
      have h2 : x < p * m := by rw [← hn_eq]; exact hx.2
      rwa [Nat.mul_comm p m] at h2
    refine (Finset.sum_subset hsub (fun x hx hxnot => ?_)).trans (Finset.sum_congr rfl ?_)
    · rw [Finset.mem_range] at hx
      rw [Finset.mem_Ioo] at hxnot
      have hxn : x < n := by
        rw [hn_eq, Nat.mul_comm]; exact hx
      have hx0 : x = 0 := by omega
      rw [hx0, Nat.cast_zero]
      exact zero_pow (by omega)
    · intro x _
      rfl
  -- Step 3: `m * F = -1` in `ZMod p`.
  have hmain : (m : ZMod p) * F = -1 := by
    rw [← hsum1, hcast', hblock, hbij]
  have hFne : F ≠ 0 := by
    intro h
    rw [h, mul_zero] at hmain
    exact (neg_ne_zero.mpr one_ne_zero) hmain.symm
  -- Step 4: multiplication by a unit permutes `ZMod p`, forcing `t ^ d = 1`.
  have hall : ∀ t : (ZMod p)ˣ, ((t : ZMod p)) ^ d = 1 := by
    intro t
    have ht : (t : ZMod p) ≠ 0 := by
      have h := t.ne_zero
      simpa using h
    have hcomp := Equiv.sum_comp (Equiv.mulLeft₀ (t : ZMod p) ht) (fun r : ZMod p => r ^ d)
    have h2 : ∑ r : ZMod p, ((t : ZMod p) * r) ^ d
        = (t : ZMod p) ^ d * ∑ r : ZMod p, r ^ d := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun r _ => mul_pow _ _ _)
    have h4 : (t : ZMod p) ^ d * (∑ r : ZMod p, r ^ d) = ∑ r : ZMod p, r ^ d := by
      rw [← h2]; exact hcomp
    have h3 : ((t : ZMod p) ^ d - 1) * (∑ r : ZMod p, r ^ d) = 0 := by
      rw [sub_mul, one_mul, h4, sub_self]
    rcases mul_eq_zero.mp h3 with h | h
    · linear_combination h
    · exact absurd h hFne
  -- Step 5: the sum over the nonzero residues is `p - 1 = -1`.
  have hFval : F = -1 := by
    have hpt : ∀ r : ZMod p, r ^ d = if r = 0 then 0 else 1 := by
      intro r
      by_cases hr : r = 0
      · rw [hr, if_pos rfl]
        exact zero_pow (by omega)
      · rw [if_neg hr]
        exact hall (Units.mk0 r hr)
    have hstep : F = ∑ r : ZMod p, (if r = 0 then (0 : ZMod p) else 1) := by
      rw [hF_def]
      exact Finset.sum_congr rfl (fun r _ => hpt r)
    have hsplit : (∑ r : ZMod p, (if r = 0 then (0 : ZMod p) else 1))
        = ∑ r ∈ (Finset.univ : Finset (ZMod p)).erase 0, (1 : ZMod p) := by
      rw [← Finset.sum_erase_add _ _ (Finset.mem_univ (0 : ZMod p))]
      rw [show (if (0 : ZMod p) = 0 then (0 : ZMod p) else 1) = 0 by simp, add_zero]
      refine Finset.sum_congr rfl (fun r hr => ?_)
      rw [Finset.mem_erase] at hr
      exact if_neg hr.1
    have hone : ∑ r ∈ (Finset.univ : Finset (ZMod p)).erase 0, (1 : ZMod p)
        = (((Finset.univ : Finset (ZMod p)).erase 0).card : ZMod p) := by simp
    have hcard : ((Finset.univ : Finset (ZMod p)).erase 0).card = p - 1 := by
      rw [Finset.card_erase_of_mem (Finset.mem_univ (0 : ZMod p)), Finset.card_univ,
        ZMod.card]
    rw [hstep, hsplit, hone, hcard, Nat.cast_sub hp_prime.one_le, Nat.cast_one,
      ZMod.natCast_self]
    ring
  -- Step 6: conclude `m ≡ 1 (mod p)`.
  have hm1 : (m : ZMod p) = 1 := by
    rw [hFval] at hmain
    linear_combination -hmain
  have hmod : m % p = 1 % p :=
    (ZMod.natCast_eq_natCast_iff' m 1 p).mp (by rw [hm1]; norm_num)
  have h1p : 1 % p = 1 := Nat.mod_eq_of_lt (by omega)
  rw [h1p] at hmod
  refine ⟨m / p, ?_⟩
  have hdm := Nat.div_add_mod m p
  rw [hmod] at hdm
  omega
