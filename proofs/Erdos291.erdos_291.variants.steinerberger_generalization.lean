import FormalConjectures.ErdosProblems.«291»

open Finset

namespace OMA.Harmonic

theorem lcmValLe (p e : ℕ) (s : Finset ℕ) (hn : ∀ j ∈ s, j ≠ 0)
    (hb : ∀ j ∈ s, j.factorization p ≤ e) :
    (s.lcm id).factorization p ≤ e := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert j s hj ih =>
    have hj0 := hn j (mem_insert_self j s)
    have hs0 : s.lcm id ≠ 0 := lcm_ne_zero_iff.mpr (fun t ht => hn t (mem_insert_of_mem ht))
    have hs := ih (fun t ht => hn t (mem_insert_of_mem ht)) (fun t ht => hb t (mem_insert_of_mem ht))
    rw [lcm_insert, id_eq, lcm_eq_nat_lcm, Nat.factorization_lcm hj0 hs0]
    exact max_le (hb j (mem_insert_self j s)) hs

theorem numDvd {p D S : ℕ} (hp : p.Prime) (hD : ¬ p ∣ D) {r : ℚ}
    (hr : r = (S : ℚ) / D) : (p ∣ S) ↔ (p : ℤ) ∣ r.num := by
  have hd : (D : ℤ) ≠ 0 := by
    exact_mod_cast (show D ≠ 0 from fun h => hD (h.symm ▸ dvd_zero p))
  have hr' : r = Rat.divInt (S : ℤ) (D : ℤ) := by simpa [Rat.divInt_eq_div] using hr
  obtain ⟨c, hc, hc'⟩ := Rat.num_den_mk hd hr'
  have hpc : ¬ (p : ℤ) ∣ c := by
    intro h
    apply hD
    exact_mod_cast (show (p : ℤ) ∣ (D : ℤ) from hc'.symm ▸ dvd_mul_of_dvd_left h _)
  have hp' := Nat.prime_iff_prime_int.mp hp
  rw [← Int.natCast_dvd_natCast, hc, hp'.dvd_mul, or_iff_right hpc]

end OMA.Harmonic

open OMA.Harmonic

theorem OMA.solution : type_of% @Erdos291.erdos_291.variants.steinerberger_generalization := by
  intro n p hp hpn
  dsimp
  let e := Nat.log p n
  let b := p ^ e
  let k := n / b
  let I := Icc 1 n
  let J := Icc 1 k
  let L := Erdos291.L n
  let D := L / b
  change p ∣ Nat.gcd (Erdos291.a n) L ↔ (p : ℤ) ∣ (∑ j ∈ J, (1 : ℚ) / j).num
  have hn : n ≠ 0 := (lt_of_lt_of_le hp.pos hpn).ne'
  have hb0 : 0 < b := pow_pos hp.pos _
  have hbn : b ≤ n := Nat.pow_log_le_self p hn
  have hnext : n < p ^ (e + 1) := Nat.lt_pow_succ_log_self hp.one_lt n
  have hlcm (j : ℕ) (hj : j ∈ I) : j ∣ L := Finset.dvd_lcm (f := id) hj
  have hL0 : L ≠ 0 := lcm_ne_zero_iff.mpr (fun j hj => by have := (mem_Icc.mp hj).1; omega)
  have hbd : b ∣ L := hlcm b (mem_Icc.mpr ⟨hb0, hbn⟩)
  have he : L.factorization p = e := by
    apply le_antisymm
    · exact lcmValLe p e I (fun j hj => by have := (mem_Icc.mp hj).1; omega)
        (fun j hj => by
          have hji := mem_Icc.mp hj
          have hj0 : j ≠ 0 := by omega
          by_contra! h
          have h' := (hp.pow_dvd_iff_le_factorization hj0).2 (show e + 1 ≤ j.factorization p by omega)
          exact (not_le_of_gt hnext) ((Nat.le_of_dvd (by omega : 0 < j) h').trans hji.2))
    · exact (hp.pow_dvd_iff_le_factorization hL0).1 hbd
  have hD : ¬ p ∣ D := by
    intro h
    obtain ⟨c, hc⟩ := h
    have heq : L = p ^ (e + 1) * c := by
      calc
        L = D * b := (Nat.div_mul_cancel hbd).symm
        _ = p ^ (e + 1) * c := by rw [hc, pow_succ]; dsimp [b]; ring
    have h' := (hp.pow_dvd_iff_le_factorization hL0).1 (show p ^ (e + 1) ∣ L from ⟨c, heq⟩)
    omega
  have hL (j : ℕ) (hj : j ∈ J) : b * j ∣ L := by
    have hji := mem_Icc.mp hj
    apply hlcm
    exact mem_Icc.mpr ⟨Nat.mul_pos hb0 hji.1,
      by simpa [mul_comm] using (Nat.le_div_iff_mul_le hb0).1 hji.2⟩
  have hDj (j : ℕ) (hj : j ∈ J) : j ∣ D := by
    obtain ⟨c, hc⟩ := hL j hj
    exact ⟨c, by rw [show D = L / b by rfl, hc, mul_assoc, Nat.mul_div_cancel_left _ hb0]⟩
  let B := J.image (b * ·)
  have hBI : B ⊆ I := by
    intro s hs
    obtain ⟨j, hj, rfl⟩ := mem_image.mp hs
    have hji := mem_Icc.mp hj
    exact mem_Icc.mpr ⟨Nat.mul_pos hb0 hji.1,
      by simpa [mul_comm] using (Nat.le_div_iff_mul_le hb0).1 hji.2⟩
  have hB (t : ℕ) (ht : t ∈ I \ B) : ¬ b ∣ t := by
    rintro ⟨j, rfl⟩
    apply (mem_sdiff.mp ht).2
    have h := mem_Icc.mp (mem_sdiff.mp ht).1
    apply mem_image.mpr
    exact ⟨j, mem_Icc.mpr ⟨by by_contra! hn; simp [show j = 0 by omega] at h,
      (Nat.le_div_iff_mul_le hb0).2 (by simpa [mul_comm] using h.2)⟩, rfl⟩
  have hdiv (t : ℕ) (ht : t ∈ I \ B) : p ∣ L / t := by
    have ht0 : t ≠ 0 := by have := (mem_Icc.mp (mem_sdiff.mp ht).1).1; omega
    have hLt := hlcm t (mem_sdiff.mp ht).1
    have hlt : t.factorization p < e := lt_of_not_ge (fun h =>
      hB t ht ((hp.pow_dvd_iff_le_factorization ht0).2 h))
    apply (hp.dvd_iff_one_le_factorization
      (show L / t ≠ 0 by intro hh; exact hL0 (by simpa [hh] using (Nat.div_mul_cancel hLt).symm))).2
    rw [Nat.factorization_div hLt, Finsupp.coe_tsub, Pi.sub_apply, he]
    omega
  let S := ∑ j ∈ J, D / j
  have ha : p ∣ Erdos291.a n ↔ p ∣ S := by
    have hrest : p ∣ ∑ t ∈ I \ B, L / t := Finset.dvd_sum hdiv
    have hsum : (∑ t ∈ B, L / t) = S := by
      rw [show B = J.image (b * ·) by rfl, sum_image]
      · simp only [S, D, Nat.div_div_eq_div_mul]
      · exact fun _ _ _ _ h => Nat.eq_of_mul_eq_mul_left hb0 h
    change p ∣ ∑ t ∈ I, L / t ↔ p ∣ S
    rw [← sum_sdiff hBI, hsum]
    exact (Nat.dvd_add_iff_right hrest).symm
  have hrat : (∑ j ∈ J, (1 : ℚ) / j) = (S : ℚ) / D := by
    have hD0 : (D : ℚ) ≠ 0 := by
      exact_mod_cast (show D ≠ 0 from fun h => hD (h.symm ▸ dvd_zero p))
    apply (eq_div_iff hD0).2
    rw [sum_mul]
    push_cast [S]
    apply sum_congr rfl
    intro j hj
    have hj0 : (j : ℚ) ≠ 0 := by
      exact_mod_cast (show j ≠ 0 by have := (mem_Icc.mp hj).1; omega)
    have hdj : (D / j : ℕ) * j = D := Nat.div_mul_cancel (hDj j hj)
    have hdj' : ((D / j : ℕ) : ℚ) * (j : ℚ) = (D : ℚ) := by exact_mod_cast hdj
    field_simp
    linarith
  have hpL : p ∣ L := hlcm p (mem_Icc.mpr ⟨hp.pos, hpn⟩)
  rw [Nat.dvd_gcd_iff, and_iff_left hpL, ha]
  exact numDvd hp hD hrat
