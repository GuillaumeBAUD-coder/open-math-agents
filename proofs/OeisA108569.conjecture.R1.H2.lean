import OMAReductions.R_OeisA108569_conjecture_R1

/-! Removing one copy of a cubed prime scales both totients by the same factor. -/

namespace OMA.TotientDescent

theorem descend (n : ℕ) (hn : 1 < n) (ho : Odd n) (h : OeisA108569.A n)
    (hc : ∃ p : ℕ, p.Prime ∧ p ^ 3 ∣ n) :
    ∃ m : ℕ, 1 < m ∧ m < n ∧ Odd m ∧ OeisA108569.A m := by
  obtain ⟨p, hp, a, hna⟩ := hc
  let m := p ^ 2 * a
  have hnm : n = p * m := by
    dsimp [m]
    rw [hna]
    ring
  have ha : 0 < a := by
    by_contra! haz
    have : a = 0 := by omega
    simp [this] at hna
    omega
  have hm : 1 < m := by
    have hsq : 1 < p ^ 2 := one_lt_pow₀ hp.one_lt (by decide)
    exact hsq.trans_le (Nat.le_mul_of_pos_right _ ha)
  have hmd : p ∣ m := (dvd_pow_self p (by decide : 2 ≠ 0)).trans (dvd_mul_right _ _)
  have hφp : p ∣ (p ^ 2).totient := by
    rw [Nat.totient_prime_pow_succ hp 1, pow_one]
    exact dvd_mul_right _ _
  have hφm : p ∣ m.totient := hφp.trans (Nat.totient_dvd_of_dvd (dvd_mul_right _ _))
  have hsum : p ∣ m + m.totient := dvd_add hmd hφm
  have hv := h.2
  rw [hnm, Nat.totient_mul_of_prime_of_dvd hp hmd, ← mul_add,
    Nat.totient_mul_of_prime_of_dvd hp hsum] at hv
  refine ⟨m, hm, ?_, ?_, hm.pos, Nat.eq_of_mul_eq_mul_left hp.pos hv⟩
  · rw [hnm]
    exact (Nat.lt_mul_iff_one_lt_left hm.pos).mpr hp.one_lt
  · rw [hnm] at ho
    exact (Nat.odd_mul.mp ho).2

end OMA.TotientDescent

theorem OMA.solution : OMA.R_OeisA108569_conjecture_R1.H2 :=
  OMA.TotientDescent.descend