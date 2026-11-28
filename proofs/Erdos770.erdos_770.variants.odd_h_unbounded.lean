import FormalConjectures.ErdosProblems.«770»

open Erdos770 in
theorem OMA.solution : type_of% @Erdos770.erdos_770.variants.odd_h_unbounded := by
  intro a
  let K := a + 2
  have : NeZero (8 * K.factorial) := ⟨by positivity⟩
  obtain ⟨p, hpK, hp, hpa⟩ :=
    Nat.forall_exists_prime_gt_and_eq_mod (q := 8 * K.factorial) isUnit_one.neg K
  have := Fact.mk hp
  have hdvd : 8 * K.factorial ∣ p + 1 := by
    rw [← ZMod.natCast_eq_zero_iff]; push_cast; rw [hpa]; ring
  have h8 : 8 ∣ p + 1 := dvd_trans ⟨_, rfl⟩ hdvd
  let n := p / 2
  have hprime (q : ℕ) (hq : q.Prime) (hqK : q ≤ K) : (q : ZMod p) ^ n = 1 := by
    have := Fact.mk hq
    have hqd : q ∣ p + 1 := (Nat.dvd_factorial hq.pos hqK).trans (dvd_trans ⟨8, mul_comm _ _⟩ hdvd)
    have hpq : (p : ZMod q) = -1 := by
      have h0 : ((p + 1 : ℕ) : ZMod q) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr hqd
      push_cast at h0; exact eq_neg_of_add_eq_zero_left h0
    have hne : (q : ZMod p) ≠ 0 := by
      rw [Ne, ZMod.natCast_eq_zero_iff]; intro h; have := Nat.le_of_dvd hq.pos h; omega
    rw [← ZMod.euler_criterion p hne]
    rcases hq.eq_two_or_odd with rfl | hodd
    · exact (ZMod.exists_sq_eq_two_iff (by omega)).mpr (.inr (by omega))
    · rcases (show q % 4 = 1 ∨ q % 4 = 3 by omega) with h1 | h3
      · exact (ZMod.exists_sq_eq_prime_iff_of_mod_four_eq_one h1 (by omega)).mp
          (hpq ▸ ZMod.exists_sq_eq_neg_one_iff.mpr (by omega))
      · exact (ZMod.exists_sq_eq_prime_iff_of_mod_four_eq_three (by omega) h3 (by omega)).mpr
          fun h => ZMod.exists_sq_eq_neg_one_iff.mp (hpq ▸ h) h3
  have hres (i : ℕ) : 0 < i → i ≤ K → (i : ZMod p) ^ n = 1 := by
    induction i using Nat.recOnMul with
    | zero => omega
    | one => simp
    | prime q hq => exact fun _ => hprime q hq
    | mul u v hu hv =>
      intro huv huvK
      have u0 := Nat.pos_of_mul_pos_right huv
      have v0 := Nat.pos_of_mul_pos_left huv
      push_cast
      rw [mul_pow, hu u0 ((Nat.le_mul_of_pos_right u v0).trans huvK),
        hv v0 ((Nat.le_mul_of_pos_left v u0).trans huvK), one_mul]
  have hn3 : 3 ≤ n := by have := hpK; omega
  let M := 2 ^ n - 1
  have hM : 7 ≤ M := by have := Nat.pow_le_pow_right (by omega : 1 ≤ 2) hn3; omega
  have hmem : (M : ℕ∞) ∈ {m : ℕ∞ | 2 < m ∧
      ((Finset.Icc 2 m.toNat).image fun i => i ^ n - 1).gcd id = 1} := by
    refine ⟨by exact_mod_cast (by omega : 2 < M), ?_⟩
    rw [ENat.toNat_natCast]
    set G := ((Finset.Icc 2 M).image fun j => j ^ n - 1).gcd id
    have hd (i : ℕ) (h1 : 2 ≤ i) (h2 : i ≤ M) : G ∣ i ^ n - 1 :=
      Finset.gcd_dvd (Finset.mem_image_of_mem _ (Finset.mem_Icc.mpr ⟨h1, h2⟩))
    have hd2 := hd 2 le_rfl (by omega)
    have hdM := hd M (by omega) le_rfl
    have h1 : 1 ≤ M ^ n := Nat.one_le_pow n M (by omega)
    exact Nat.dvd_one.mp ((show M ^ n - (M ^ n - 1) = 1 by omega) ▸
      Nat.dvd_sub (dvd_pow hd2 (by omega)) hdM)
  have hge : ((K + 1 : ℕ) : ℕ∞) ≤ h n := le_sInf fun x ⟨_, hgcd⟩ => by
    induction x using ENat.recTopCoe with
    | top => exact le_top
    | coe k =>
      rw [ENat.toNat_natCast] at hgcd
      by_contra hk
      rw [Nat.cast_le] at hk
      have hpG : p ∣ ((Finset.Icc 2 k).image fun i => i ^ n - 1).gcd id :=
        Finset.dvd_gcd fun b hb => by
          obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hb
          rw [Finset.mem_Icc] at hi
          rw [id, ← ZMod.natCast_eq_zero_iff, Nat.cast_sub (Nat.one_le_pow _ _ (by omega))]
          push_cast; rw [hres i (by omega) (by omega), sub_self]
      exact hp.one_lt.ne' (Nat.dvd_one.mp (hgcd ▸ hpG))
  have hne : h n ≠ ⊤ := ne_top_of_le_ne_top (ENat.natCast_ne_top M) (sInf_le hmem)
  refine ⟨(h n).toNat, ⟨h n, ⟨n, Nat.odd_iff.mpr (by omega), rfl⟩, rfl⟩, ?_⟩
  rw [← ENat.natCast_toNat hne, Nat.cast_le] at hge
  omega
