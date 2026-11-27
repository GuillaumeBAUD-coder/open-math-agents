import OMAReductions.R_AgohGiuga_agoh_giuga_variants_giuga_R1

/-! The block decomposition uses the proof of isStrongGiuga_iff in this repository.
The unit indexing follows Mathlib.NumberTheory.Bernoulli. -/

open AgohGiuga Finset

namespace GiugaSteps

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

lemma criterion {n p : ℕ} (hn : IsStrongGiuga n) (hp : p ∈ n.primeFactors) :
    (p - 1) ∣ (n - 1) ∧ p ∣ (n / p - 1) := by
  have hprime := Nat.prime_of_mem_primeFactors hp
  have : Fact p.Prime := ⟨hprime⟩
  have hpn := Nat.dvd_of_mem_primeFactors hp
  have hpos : 1 < n := hn.1.1
  have hd := dvd_trans hpn hn.2
  rw [sum_Ioo_eq_sum_range (by omega), ← ZMod.natCast_eq_zero_iff, Nat.cast_add,
    Nat.cast_one] at hd
  have hblock := sum_range_pow_zmod_mul (n / p) p (n - 1)
  rw [Nat.div_mul_cancel hpn] at hblock
  rw [hblock, ← Nat.Ico_zero_eq_range, Finset.sum_eq_sum_Ico_succ_bot hprime.pos] at hd
  simp only [Nat.cast_zero, zero_pow (show n - 1 ≠ 0 by omega), zero_add] at hd
  have hbij : (∑ v ∈ Ico 1 p, (v : ZMod p) ^ (n - 1)) = ∑ u : (ZMod p)ˣ, (u : ZMod p) ^ (n - 1) :=
    Finset.sum_bij'
      (fun v hv ↦ Units.mk0 (v : ZMod p) (mt (ZMod.natCast_eq_zero_iff v p).mp (by
        exact Nat.not_dvd_of_pos_of_lt (Finset.mem_Ico.mp hv).1 (Finset.mem_Ico.mp hv).2)))
      (fun u _ ↦ (u : ZMod p).val)
      (fun _ _ ↦ Finset.mem_univ _)
      (fun u _ ↦ by grind [u.ne_zero, ZMod.val_ne_zero, ZMod.val_lt])
      (fun v hv ↦ by simp [ZMod.val_cast_of_lt (Finset.mem_Ico.mp hv).2])
      (fun u _ ↦ Units.ext (ZMod.natCast_zmod_val _))
      (fun _ _ ↦ rfl)
  rw [hbij, FiniteField.sum_pow_units, ZMod.card] at hd
  split_ifs at hd with hk
  · refine ⟨hk, (ZMod.natCast_eq_zero_iff _ p).mp ?_⟩
    rw [Nat.cast_sub (Nat.div_pos (Nat.le_of_dvd (by omega) hpn) hprime.pos), Nat.cast_one]
    linear_combination -hd
  · simp at hd

end GiugaSteps

theorem OMA.solution : OMA.R_AgohGiuga_agoh_giuga_variants_giuga_R1.H2 := by
  intro n hn p hp
  exact (GiugaSteps.criterion hn hp).2
