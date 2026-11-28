import OMAStatements.S_oeis_a061002

open OMA.S_oeis_a061002

open Finset

lemma zs {p: ℕ} [Fact p.Prime] (f: ZMod p → ZMod p) (h0: f 0 = 0) :
    ∑ r ∈ Ico 1 p, f r = ∑ x: ZMod p, f x := by
  have h1: ∑ r ∈ range p, f r = ∑ x: ZMod p, f x := by
    refine sum_nbij (fun r: ℕ => (r: ZMod p)) (by simp) ?_ ?_ ?_
    · intro a ha b hb h
      simpa [ZMod.val_natCast_of_lt (mem_range.mp ha), ZMod.val_natCast_of_lt (mem_range.mp hb)]
        using congr_arg ZMod.val h
    · intro x _; exact ⟨x.val, mem_range.mpr x.val_lt, ZMod.natCast_zmod_val x⟩
    · intro a _; rfl
  rw [← h1, ← Nat.Ico_zero_eq_range, sum_eq_sum_Ico_succ_bot (Fact.out: p.Prime).pos]
  simp [h0]

lemma bd {p: ℕ} (hp: p.Prime) (s: Finset ℕ) (b: ℕ → ℕ) (hb: ∀ i ∈ s, ¬p ∣ b i)
    (hS: ∑ i ∈ s, (b i: ZMod p)⁻¹ = 0) :
    ∃ N D: ℕ, ¬p ∣ D ∧ (∑ i ∈ s, (b i: ℚ)⁻¹) * D = N ∧ p ∣ N := by
  haveI: Fact p.Prime := ⟨hp⟩
  refine ⟨∑ i ∈ s, ∏ j ∈ s.erase i, b j, ∏ i ∈ s, b i, ?_, ?_, ?_⟩
  · rintro h
    obtain ⟨i, hi, h⟩ := (hp.prime.dvd_finsetProd_iff _).mp h
    exact hb i hi h
  · rw [sum_mul]
    push_cast
    refine sum_congr rfl fun i hi => ?_
    have hi': (b i: ℚ) ≠ 0 := Nat.cast_ne_zero.mpr fun h0 => hb i hi (h0 ▸ dvd_zero p)
    rw [← mul_prod_erase s (fun j => (b j: ℚ)) hi, inv_mul_cancel_left₀ hi']
  · rw [← ZMod.natCast_eq_zero_iff, Nat.cast_sum]
    have h: ∀ i ∈ s, ((∏ j ∈ s.erase i, b j: ℕ): ZMod p) =
        ((∏ i ∈ s, b i: ℕ): ZMod p) * (b i: ZMod p)⁻¹ := by
      intro i hi
      have hi': (b i: ZMod p) ≠ 0 := by
        rw [Ne, ZMod.natCast_eq_zero_iff]; exact hb i hi
      simp only [Nat.cast_prod]
      rw [← mul_prod_erase s (fun j => (b j: ZMod p)) hi, mul_right_comm,
        mul_inv_cancel₀ hi', one_mul]
    rw [sum_congr rfl h, ← mul_sum, hS, mul_zero]

lemma key: ∀ p: ℕ, p.Prime → 3 < p →
    ((H p / H (p - 1)).den: ℤ) = (p: ℤ) ^ 3 * (H (p - 1) / (p: ℚ) ^ 2).num := by
  rintro p hp hp3
  have hH: ∀ m, H m = harmonic m := fun m => by simp [H, harmonic_eq_sum_Icc]
  simp only [hH]
  set q := harmonic (p - 1) with hq
  haveI: Fact p.Prime := ⟨hp⟩
  set s := Ico 1 p with hs
  have hm: ∀ k ∈ s, 1 ≤ k ∧ k < p := fun k hk => mem_Ico.mp (by rwa [hs] at hk)
  have h1: q = ∑ k ∈ s, (k: ℚ)⁻¹ := by rw [hq, hs, harmonic_eq_sum_Icc]; congr 1
  have h6: ∑ k ∈ s, ((k * (p - k): ℕ): ZMod p)⁻¹ = 0 := by
    have h7: ∀ k ∈ s, ((k * (p - k): ℕ): ZMod p)⁻¹ = -((k: ZMod p) ^ 2)⁻¹ := by
      intro k hk
      rw [Nat.cast_mul, Nat.cast_sub (hm k hk).2.le, ZMod.natCast_self, zero_sub, mul_neg,
        ← sq, inv_neg]
    rw [sum_congr rfl h7, sum_neg_distrib, neg_eq_zero]
    have h8: ∑ x: ZMod p, (x ^ 2)⁻¹ = 0 := by
      rw [show ∑ x: ZMod p, (x ^ 2)⁻¹ = ∑ x: ZMod p, x ^ 2 by
        rw [← Equiv.sum_comp (Equiv.inv (ZMod p)) (fun x: ZMod p => x ^ 2)]; simp [inv_pow]]
      exact FiniteField.sum_pow_lt_card_sub_one (K := ZMod p) 2 (by rw [ZMod.card]; omega)
    rw [hs, zs (fun x: ZMod p => (x ^ 2)⁻¹) (by simp), h8]
  obtain ⟨N, D, hD, hSD, hN⟩ := bd hp s (fun k => k * (p - k)) (fun k hk h => by
    obtain ⟨hk1, hkp⟩ := hm k hk
    rcases hp.dvd_mul.mp h with h' | h' <;>
      exact absurd (Nat.le_of_dvd (by omega) h') (by omega)) h6
  have h2: ∑ k ∈ s, ((p - k: ℕ): ℚ)⁻¹ = ∑ k ∈ s, (k: ℚ)⁻¹ := by
    rw [hs]; simpa using sum_Ico_reflect (fun j: ℕ => (j: ℚ)⁻¹) 1 (Nat.le_succ p)
  have h3: 2 * q * D = (p: ℚ) * N := by
    have h4: 2 * ∑ k ∈ s, (k: ℚ)⁻¹ = ∑ k ∈ s, ((k: ℚ)⁻¹ + ((p - k: ℕ): ℚ)⁻¹) := by
      rw [sum_add_distrib, h2]; ring
    have h5: 2 * q = (p: ℚ) * ∑ k ∈ s, ((k * (p - k): ℕ): ℚ)⁻¹ := by
      rw [h1, h4, mul_sum]
      refine sum_congr rfl fun k hk => ?_
      obtain ⟨hk1, hkp⟩ := hm k hk
      have hk0: ((k: ℚ) + ((p - k: ℕ): ℚ)) = (p: ℚ) := by
        rw [← Nat.cast_add, Nat.add_sub_cancel' hkp.le]
      have hk1': (k: ℚ) ≠ 0 := by positivity
      have hk2': ((p - k: ℕ): ℚ) ≠ 0 := by rw [Nat.cast_ne_zero]; omega
      rw [Nat.cast_mul]; field_simp; linarith
    rw [h5, mul_assoc, hSD]
  have hpD: ¬ p ∣ 2 * D := fun h => (hp.dvd_mul.mp h).elim
    (fun h' => by have := Nat.le_of_dvd (by norm_num) h'; omega) hD
  have hq3: 2 * (q.num: ℤ) * D = ((q.den * p * N: ℕ): ℤ) := by
    rw [show q = (q.num: ℚ) / q.den from (Rat.num_div_den q).symm] at h3
    field_simp at h3
    exact_mod_cast h3
  have hw: (p: ℤ) ^ 2 ∣ q.num := by
    obtain ⟨k, hk⟩ := hN
    have hpN: (p: ℤ) ^ 2 ∣ (p: ℤ) * N := ⟨k, by push_cast [hk]; ring⟩
    have hd: (p: ℤ) ^ 2 ∣ (q.num: ℤ) * ((2 * D: ℕ): ℤ) := by
      rw [show (q.num: ℤ) * ((2 * D: ℕ): ℤ) = 2 * q.num * D by push_cast; ring, hq3,
        show ((q.den * p * N: ℕ): ℤ) = (p: ℤ) * N * q.den by push_cast; ring]
      exact dvd_mul_of_dvd_left hpN _
    exact ((hp.coprime_iff_not_dvd.mpr hpD).isCoprime.pow_left (m := 2)).dvd_of_dvd_mul_right hd
  set a := q.num.natAbs with ha
  set b := q.den with hb
  have hA: (0: ℤ) < q.num := Rat.num_pos.mpr (harmonic_pos (by omega))
  have ha0: 0 < a := Int.natAbs_pos.mpr hA.ne'
  have hb0: 0 < b := q.den_pos
  have hab: q = (a: ℚ) / b := by
    rw [hb, ← show (q.num: ℚ) = (a: ℚ) from by rw [ha, ← Int.cast_natCast, Int.natAbs_of_nonneg hA.le],
      Rat.num_div_den]
  have hred: Nat.Coprime a b := q.reduced
  obtain ⟨Ap, hAp⟩: ∃ Ap, a = p ^ 2 * Ap := by
    obtain ⟨k, hk⟩ := Int.natAbs_dvd_natAbs.mpr hw
    rw [Int.natAbs_pow, Int.natAbs_natCast] at hk
    exact ⟨k, by rw [ha]; exact hk⟩
  have hbp: Nat.Coprime b p := (hred.coprime_dvd_left ⟨p * Ap, by rw [hAp]; ring⟩).symm
  have hc: Nat.Coprime (a * p + b) (a * p) :=
    Nat.coprime_self_add_left.mpr (hred.symm.mul_right hbp)
  have hHp: harmonic p = q + (p: ℚ)⁻¹ := by
    rw [hq, ← Nat.sub_add_cancel hp.pos]
    exact harmonic_succ (p - 1)
  have hden: ((harmonic p / q).den: ℤ) = (a * p: ℕ) := by
    have hf: harmonic p / q = ((a * p + b: ℕ): ℚ) / ((a * p: ℕ): ℚ) := by
      rw [hHp, hab]; push_cast; field_simp
    rw [hf]
    refine Rat.den_div_eq_of_coprime (a := ((a * p + b: ℕ): ℤ)) (b := ((a * p: ℕ): ℤ))
      (by positivity) (by simpa only [Int.natAbs_natCast] using hc)
  have hnum: (q / (p: ℚ) ^ 2).num = (Ap: ℤ) := by
    have hf: q / (p: ℚ) ^ 2 = (Ap: ℚ) / (b: ℚ) := by rw [hab, hAp]; push_cast; field_simp
    rw [hf]
    refine Rat.num_div_eq_of_coprime (a := (Ap: ℤ)) (b := (b: ℤ)) (by positivity)
      (by simpa using hred.coprime_dvd_left ⟨p ^ 2, by rw [hAp]; ring⟩)
  rw [hden, hnum, hAp]
  push_cast
  ring


theorem OMA.solution: type_of% @OMA.S_oeis_a061002.main := key
