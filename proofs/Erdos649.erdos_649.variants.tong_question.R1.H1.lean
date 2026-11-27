import OMAReductions.R_Erdos649_erdos_649_variants_tong_question_R1

-- Step Erdos649.erdos_649.variants.tong_question.R1.H1: hypothesis H1 of reduction Erdos649.erdos_649.variants.tong_question.R1
-- Credit: @sebastianbachmaier
-- H1 := ∀ p q : ℕ, p.Prime → q.Prime → q < p →     ((∃ e : ℕ, 0 < e ∧ (q ^ e - 1).maxPrimeFac = p) ↔       (q ^ orderOf (q : ZMod p) - 1).maxPrimeFac = p)

namespace OMAErdos649H1

theorem dvd_iff_pow (p q e : ℕ) (hq : 0 < q) :
    p ∣ q ^ e - 1 ↔ (q : ZMod p) ^ e = 1 := by
  have h1 : 1 ≤ q ^ e := Nat.one_le_pow _ _ hq
  rw [← ZMod.natCast_eq_zero_iff, Nat.cast_sub h1]
  push_cast
  exact sub_eq_zero

theorem ne_zero_of_mpf {m p : ℕ} (hp : p.Prime) (h : m.maxPrimeFac = p) : m ≠ 0 := by
  rintro rfl
  have : (0 : ℕ).maxPrimeFac = 0 := Nat.maxPrimeFac_zero
  rw [this] at h
  exact hp.ne_zero h.symm

end OMAErdos649H1

open OMAErdos649H1 in
theorem OMA.solution : OMA.R_Erdos649_erdos_649_variants_tong_question_R1.H1 := by
  intro p q hp hq hqp
  have hq0 : 0 < q := hq.pos
  constructor
  · rintro ⟨e, he, hm⟩
    have hm0 := ne_zero_of_mpf hp hm
    have hpd : p ∣ q ^ e - 1 := hm ▸ Nat.maxPrimeFac_dvd
    have hpow : (q : ZMod p) ^ e = 1 := (dvd_iff_pow p q e hq0).mp hpd
    set o := orderOf (q : ZMod p) with ho
    have hoe : o ∣ e := orderOf_dvd_of_pow_eq_one hpow
    have ho0 : 0 < o := by
      rcases Nat.eq_zero_or_pos o with h | h
      · rw [h, zero_dvd_iff] at hoe; omega
      · exact h
    have hpo : p ∣ q ^ o - 1 := (dvd_iff_pow p q o hq0).mpr (pow_orderOf_eq_one _)
    have hdiv : q ^ o - 1 ∣ q ^ e - 1 := by
      exact Nat.pow_sub_one_dvd_pow_sub_one q hoe
    have ha0 : q ^ o - 1 ≠ 0 := by
      have : q ^ e - 1 ≠ 0 := hm0
      intro h; rw [h, zero_dvd_iff] at hdiv; exact this hdiv
    have hge : p ≤ (q ^ o - 1).maxPrimeFac := Nat.le_maxPrimeFac ha0 hp hpo
    have ha1 : 1 < q ^ o - 1 := by
      have := Nat.le_of_dvd (Nat.pos_of_ne_zero ha0) hpo
      have := hp.two_le
      omega
    have hpr := Nat.prime_maxPrimeFac_of_one_lt _ ha1
    have hle : (q ^ o - 1).maxPrimeFac ≤ (q ^ e - 1).maxPrimeFac :=
      Nat.le_maxPrimeFac hm0 hpr (dvd_trans Nat.maxPrimeFac_dvd hdiv)
    omega
  · intro h
    refine ⟨orderOf (q : ZMod p), ?_, h⟩
    rcases Nat.eq_zero_or_pos (orderOf (q : ZMod p)) with h0 | h0
    · exfalso
      rw [h0] at h
      exact ne_zero_of_mpf hp h (by simp)
    · exact h0
