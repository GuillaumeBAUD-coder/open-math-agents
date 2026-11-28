import OMAReductions.R_oeis_a397683_R1_H2_R1

namespace LiftH

theorem ord_lift (p k d : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (x : ℤ) (hd0 : d ≠ 0)
    (hd : orderOf (x : ZMod p) = d) (hx : ¬ (p : ℤ) ^ 2 ∣ x ^ d - 1) :
    orderOf (x : ZMod (p ^ (k + 1))) = d * p ^ k := by
  have h1 : (p : ℤ) ∣ x ^ d - 1 := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    rw [← hd, pow_orderOf_eq_one, sub_self]
  obtain ⟨a, ha⟩ := h1
  have hna : ¬ (p : ℤ) ∣ a := by
    rintro ⟨b, rfl⟩
    exact hx ⟨b, by rw [ha]; ring⟩
  have hxa : x ^ d = 1 + p * a := by linarith
  have hcast : (x : ZMod (p ^ (k + 1))) ^ d = 1 + p * a := by
    rw [← Int.cast_pow, hxa]; push_cast; ring
  have hord := ZMod.orderOf_one_add_mul_prime hp hp2 a hna k
  rw [← hcast] at hord
  have hdvd : d ∣ orderOf (x : ZMod (p ^ (k + 1))) := by
    have := orderOf_map_dvd
      (ZMod.castHom (dvd_pow_self p (Nat.succ_ne_zero k)) (ZMod p)).toMonoidHom
      (x : ZMod (p ^ (k + 1)))
    simpa [hd] using this
  rw [orderOf_pow_of_dvd hd0 hdvd] at hord
  exact Nat.eq_mul_of_div_eq_right hdvd hord

theorem bad_inj (p d : ℕ) (hp : p.Prime) (hp3 : 3 ≤ p) (y : ℤ) (hy : ¬ (p : ℤ) ∣ y)
    (hd : ¬ (p : ℤ) ∣ (d : ℤ)) (t1 t2 : ℕ) (ht1 : t1 < 3) (ht2 : t2 < 3)
    (hb1 : (p : ℤ) ^ 2 ∣ (y + p * t1) ^ d - 1) (hb2 : (p : ℤ) ^ 2 ∣ (y + p * t2) ^ d - 1) :
    t1 = t2 := by
  have he1 := sq_dvd_add_pow_sub_sub ((p : ℤ) * t1) y d
  have he2 := sq_dvd_add_pow_sub_sub ((p : ℤ) * t2) y d
  have hs1 : (p : ℤ) ^ 2 ∣ ((p : ℤ) * t1) ^ 2 := by
    rw [mul_pow]; exact dvd_mul_right _ _
  have hs2 : (p : ℤ) ^ 2 ∣ ((p : ℤ) * t2) ^ 2 := by
    rw [mul_pow]; exact dvd_mul_right _ _
  have key : (p : ℤ) * p ∣ p * (y ^ (d - 1) * d * ((t1 : ℤ) - t2)) := by
    have := dvd_sub (dvd_sub hb1 (hs1.trans he1)) (dvd_sub hb2 (hs2.trans he2))
    rw [← pow_two]
    have heq : (p : ℤ) * (y ^ (d - 1) * d * ((t1 : ℤ) - t2)) =
        ((y + p * t1) ^ d - 1 - ((y + p * t1) ^ d - y ^ (d - 1) * (p * t1) * d - y ^ d)) -
        ((y + p * t2) ^ d - 1 - ((y + p * t2) ^ d - y ^ (d - 1) * (p * t2) * d - y ^ d)) := by
      ring
    rw [heq]
    exact this
  have hp0 : (p : ℤ) ≠ 0 := by exact_mod_cast hp.ne_zero
  rw [mul_dvd_mul_iff_left hp0] at key
  have hpz : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  rcases hpz.dvd_or_dvd key with h | h
  · rcases hpz.dvd_or_dvd h with h | h
    · exact absurd (hpz.dvd_of_dvd_pow h) hy
    · exact absurd h hd
  · have := Int.eq_zero_of_abs_lt_dvd h (by rw [abs_lt]; constructor <;> omega)
    omega

end LiftH

theorem OMA.solution : OMA.R_oeis_a397683_R1_H2_R1.H2 := by
  intro p n hp hpo hn ⟨v0, hu0, hu1, he, h2⟩
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  have hp2 : p ≠ 2 := by rintro rfl; exact absurd hpo (by decide)
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  have := Fact.mk hp
  set d := orderOf v0 with hd_def
  have hv0 : v0 ≠ 0 := hu0.ne_zero
  have hv1 : v0 + 1 ≠ 0 := hu1.ne_zero
  have hdp : d ∣ p - 1 := orderOf_dvd_of_pow_eq_one (ZMod.pow_card_sub_one_eq_one hv0)
  have hd0 : d ≠ 0 := by rintro h; rw [h, zero_dvd_iff] at hdp; omega
  have hdlt : d < p := by have := Nat.le_of_dvd (by omega) hdp; omega
  have hdz : ¬ (p : ℤ) ∣ (d : ℤ) := by
    rw [Int.natCast_dvd_natCast]; intro h; have := Nat.le_of_dvd (by omega) h; omega
  set c : ℤ := (v0.val : ℤ) with hc_def
  have hc : ((c : ℤ) : ZMod p) = v0 := by simp [hc_def]
  have hcz : ¬ (p : ℤ) ∣ c := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd, hc]; exact hv0
  have hc1z : ¬ (p : ℤ) ∣ (c + 1) := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]; push_cast; rw [hc]; exact hv1
  have hcast0 : ∀ t : ℕ, (((c + p * t : ℤ)) : ZMod p) = v0 := by
    intro t; push_cast; simp [hc]
  have hcast1 : ∀ t : ℕ, (((c + 1 + p * t : ℤ)) : ZMod p) = v0 + 1 := by
    intro t; push_cast; simp [hc]
  obtain ⟨t, ht3, hg0, hg1⟩ : ∃ t : ℕ, t < 3 ∧ ¬ (p : ℤ) ^ 2 ∣ (c + p * t) ^ d - 1 ∧
      ¬ (p : ℤ) ^ 2 ∣ (c + 1 + p * t) ^ d - 1 := by
    by_contra H
    have H' : ∀ t : ℕ, t < 3 → (p : ℤ) ^ 2 ∣ (c + p * t) ^ d - 1 ∨
        (p : ℤ) ^ 2 ∣ (c + 1 + p * t) ^ d - 1 := by
      intro t ht
      by_contra hh
      exact H ⟨t, ht, fun h => hh (Or.inl h), fun h => hh (Or.inr h)⟩
    have i0 := LiftH.bad_inj p d hp hp3 c hcz hdz
    have i1 := LiftH.bad_inj p d hp hp3 (c + 1) hc1z hdz
    rcases H' 0 (by norm_num) with a0 | a0 <;> rcases H' 1 (by norm_num) with a1 | a1 <;>
      rcases H' 2 (by norm_num) with a2 | a2 <;>
      first
      | exact absurd (i0 0 1 (by norm_num) (by norm_num) a0 a1) (by norm_num)
      | exact absurd (i0 0 2 (by norm_num) (by norm_num) a0 a2) (by norm_num)
      | exact absurd (i0 1 2 (by norm_num) (by norm_num) a1 a2) (by norm_num)
      | exact absurd (i1 0 1 (by norm_num) (by norm_num) a0 a1) (by norm_num)
      | exact absurd (i1 0 2 (by norm_num) (by norm_num) a0 a2) (by norm_num)
      | exact absurd (i1 1 2 (by norm_num) (by norm_num) a1 a2) (by norm_num)
  have o0 := LiftH.ord_lift p k d hp hp2 (c + p * t) hd0 (by rw [hcast0]) hg0
  have o1 := LiftH.ord_lift p k d hp hp2 (c + 1 + p * t) hd0 (by rw [hcast1, ← he]) hg1
  have hv : (((c + 1 + p * t : ℤ)) : ZMod (p ^ (k + 1))) =
      (((c + p * t : ℤ)) : ZMod (p ^ (k + 1))) + 1 := by push_cast; ring
  rw [hv] at o1
  have hpos : 0 < d * p ^ k := Nat.pos_of_ne_zero (mul_ne_zero hd0 (pow_ne_zero _ hp.ne_zero))
  refine ⟨((c + p * t : ℤ) : ZMod (p ^ (k + 1))), ?_, ?_, by rw [o0, o1], ?_⟩
  · exact (orderOf_pos_iff.mp (o0 ▸ hpos)).isUnit
  · exact (orderOf_pos_iff.mp (o1 ▸ hpos)).isUnit
  · rw [o0]; exact h2.trans (dvd_mul_right _ _)
