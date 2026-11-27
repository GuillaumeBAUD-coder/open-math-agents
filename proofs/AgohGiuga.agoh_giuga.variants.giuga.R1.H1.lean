import OMAReductions.R_AgohGiuga_agoh_giuga_variants_giuga_R1

-- Step AgohGiuga.agoh_giuga.variants.giuga.R1.H1: hypothesis H1 of reduction AgohGiuga.agoh_giuga.variants.giuga.R1
-- Credit: @jfpvazquez95

/-!
# Every strong Giuga number is a Carmichael number

If `n` is a strong Giuga number (`n.Composite` and `n ∣ 1 + ∑ i ∈ Ioo 0 n, i ^ (n - 1)`),
then for every prime factor `p` of `n` (writing `n = p * m`), reducing modulo `p` gives
`1 + (m : ZMod p) * ∑ x : ZMod p, x ^ (n - 1) = 0`.
Hence `(m : ZMod p) ≠ 0` (so `n` is squarefree) and `S := ∑ x : ZMod p, x ^ (n - 1) ≠ 0`.
Multiplying `S` by `(g : ZMod p) ^ (n - 1)` for a generator `g` of `(ZMod p)ˣ` permutes the summands,
forcing `(g : ZMod p) ^ (n - 1) = 1`, so `(p - 1) ∣ (n - 1)`.
By `AgohGiuga.korselts_criterion`, `n` is a Carmichael number.
-/

namespace OMA.AgohGiugaH1Proof

private lemma sum_range_mul_zmod (p e : ℕ) :
    ∀ k : ℕ, ∑ i ∈ Finset.range (p * k), (i : ZMod p) ^ e =
      (k : ZMod p) * ∑ r ∈ Finset.range p, (r : ZMod p) ^ e
  | 0 => by simp
  | k + 1 => by
    rw [Nat.mul_succ, Finset.sum_range_add, sum_range_mul_zmod p e k]
    have hterm : ∀ r ∈ Finset.range p, (((p * k + r : ℕ) : ZMod p) ^ e) = (r : ZMod p) ^ e := by
      intro r _
      push_cast
      simp
    rw [Finset.sum_congr rfl hterm]
    push_cast
    ring

private lemma sum_range_eq_sum_univ_zmod (p e : ℕ) [NeZero p] :
    ∑ r ∈ Finset.range p, (r : ZMod p) ^ e = ∑ x : ZMod p, x ^ e := by
  rw [← Fin.sum_univ_eq_sum_range (fun r : ℕ => (r : ZMod p) ^ e) p]
  refine Fintype.sum_bijective (fun i : Fin p => (i.val : ZMod p)) ?_ _ _ fun i => rfl
  refine ⟨fun a b hab => ?_, fun x => ⟨⟨x.val, ZMod.val_lt x⟩, ZMod.natCast_zmod_val x⟩⟩
  apply Fin.ext
  have ha := ZMod.val_cast_of_lt a.isLt
  have hb := ZMod.val_cast_of_lt b.isLt
  simpa [ha, hb] using congrArg ZMod.val hab

private lemma strongGiuga_prime_zmod {n p : ℕ} [Fact p.Prime]
    (hcomp : n.Composite)
    (hdvd : n ∣ 1 + ∑ i ∈ Finset.Ioo 0 n, i ^ (n - 1))
    {m : ℕ} (hm : n = p * m) :
    (m : ZMod p) ≠ 0 ∧ (∑ x : ZMod p, x ^ (n - 1)) ≠ 0 := by
  have hn1 : 1 < n := hcomp.1
  have hne : n - 1 ≠ 0 := by omega
  have hp_dvd : p ∣ 1 + ∑ i ∈ Finset.Ioo 0 n, i ^ (n - 1) :=
    dvd_trans ⟨m, hm⟩ hdvd
  have hz : (1 : ZMod p) + ∑ i ∈ Finset.Ioo 0 n, (i : ZMod p) ^ (n - 1) = 0 := by
    have h0 : (((1 + ∑ i ∈ Finset.Ioo 0 n, i ^ (n - 1) : ℕ) : ZMod p)) = 0 :=
      (ZMod.natCast_eq_zero_iff _ p).mpr hp_dvd
    simpa [Nat.cast_add, Nat.cast_sum, Nat.cast_pow] using h0
  have hset : Finset.range n = insert 0 (Finset.Ioo 0 n) := by
    ext x
    simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Ioo]
    omega
  have hrange : Finset.range n = Finset.range (p * m) := congrArg Finset.range hm
  have hsum_eq : ∑ i ∈ Finset.Ioo 0 n, (i : ZMod p) ^ (n - 1) =
      (m : ZMod p) * ∑ x : ZMod p, x ^ (n - 1) := by
    calc ∑ i ∈ Finset.Ioo 0 n, (i : ZMod p) ^ (n - 1)
        = ∑ i ∈ Finset.range n, (i : ZMod p) ^ (n - 1) := by
          rw [hset, Finset.sum_insert (by simp), Nat.cast_zero, zero_pow hne, zero_add]
      _ = ∑ i ∈ Finset.range (p * m), (i : ZMod p) ^ (n - 1) := by rw [hrange]
      _ = (m : ZMod p) * ∑ x : ZMod p, x ^ (n - 1) := by
          rw [sum_range_mul_zmod, sum_range_eq_sum_univ_zmod]
  rw [hsum_eq] at hz
  have hmul : (m : ZMod p) * ∑ x : ZMod p, x ^ (n - 1) ≠ 0 := by
    intro hzero
    rw [hzero, add_zero] at hz
    exact one_ne_zero hz
  exact ⟨left_ne_zero_of_mul hmul, right_ne_zero_of_mul hmul⟩

end OMA.AgohGiugaH1Proof

theorem OMA.solution : OMA.R_AgohGiuga_agoh_giuga_variants_giuga_R1.H1 := by
  intro n ⟨hcomp, hdvd⟩
  refine (AgohGiuga.korselts_criterion n hcomp).mpr ⟨?_, ?_⟩
  · rw [Nat.squarefree_iff_prime_squarefree]
    rintro p hp ⟨m, hm⟩
    have : Fact p.Prime := ⟨hp⟩
    have hm_ne : ((p * m : ℕ) : ZMod p) ≠ 0 :=
      (OMA.AgohGiugaH1Proof.strongGiuga_prime_zmod hcomp hdvd (by rw [hm, mul_assoc])).1
    exact hm_ne (by push_cast; simp)
  · intro p hp ⟨m, hm⟩
    have : Fact p.Prime := ⟨hp⟩
    have hS_ne : (∑ x : ZMod p, x ^ (n - 1)) ≠ 0 :=
      (OMA.AgohGiugaH1Proof.strongGiuga_prime_zmod hcomp hdvd hm).2
    obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := (ZMod p)ˣ)
    have hmul : (g : ZMod p) ^ (n - 1) * ∑ x : ZMod p, x ^ (n - 1) =
        ∑ x : ZMod p, x ^ (n - 1) := by
      rw [Finset.mul_sum]
      simp_rw [← mul_pow]
      exact Equiv.sum_comp (Equiv.mulLeft₀ (g : ZMod p) (Units.ne_zero g))
        (fun x : ZMod p => x ^ (n - 1))
    have hsub : ((g : ZMod p) ^ (n - 1) - 1) * ∑ x : ZMod p, x ^ (n - 1) = 0 := by
      rw [sub_mul, one_mul, hmul, sub_self]
    have hg_zmod : (g : ZMod p) ^ (n - 1) = 1 :=
      sub_eq_zero.mp ((mul_eq_zero.mp hsub).resolve_right hS_ne)
    have hg_pow : g ^ (n - 1) = 1 := Units.ext (by simpa [Units.val_pow_eq_pow_val] using hg_zmod)
    have hord : orderOf g ∣ n - 1 := orderOf_dvd_iff_pow_eq_one.mpr hg_pow
    rwa [orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_eq_fintype_card,
      ZMod.card_units_eq_totient, Nat.totient_prime hp] at hord
