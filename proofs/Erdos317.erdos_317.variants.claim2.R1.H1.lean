import OMAReductions.R_Erdos317_erdos_317_variants_claim2_R1

-- Step Erdos317.erdos_317.variants.claim2.R1.H1: hypothesis H1 of reduction Erdos317.erdos_317.variants.claim2.R1
-- Credit: @ishaanzee
-- Proof: take u the least prime power above n. lcm(1..m) only changes at prime powers: a
-- non-prime-power m >= 2 is a coprime product of two smaller numbers dividing lcm(1..m-1).

open Finset

namespace E317Aux

/-- `lcm(1..m) = lcm(1..m-1)` when `m ≥ 2` is not a prime power. -/
lemma lcm_step {m : ℕ} (hm : 2 ≤ m) (hpp : ¬ IsPrimePow m) :
    (Icc 1 m).lcm id = (Icc 1 (m - 1)).lcm id := by
  have hins : Icc 1 m = insert m (Icc 1 (m - 1)) := by
    ext x; simp only [mem_Icc, mem_insert]; omega
  rw [hins, Finset.lcm_insert]
  apply (lcm_eq_right_iff _ _ (by simp)).2
  have hsplit : ∃ a b, a * b = m ∧ Nat.Coprime a b ∧ 2 ≤ a ∧ 2 ≤ b := by
    have hpp' : m.minFac.Prime := Nat.minFac_prime (by omega)
    have hab : m.minFac ^ m.factorization m.minFac * (m / m.minFac ^ m.factorization m.minFac) = m :=
      Nat.ordProj_mul_ordCompl_eq_self m m.minFac
    have hcop := (Nat.coprime_ordCompl hpp' (by omega : m ≠ 0)).pow_left (m.factorization m.minFac)
    have hfac : 1 ≤ m.factorization m.minFac :=
      (hpp'.dvd_iff_one_le_factorization (by omega)).1 (Nat.minFac_dvd m)
    have ha2 : 2 ≤ m.minFac ^ m.factorization m.minFac :=
      le_trans hpp'.two_le (Nat.le_self_pow (by omega) _)
    have hbpos : 0 < m / m.minFac ^ m.factorization m.minFac := Nat.ordCompl_pos _ (by omega)
    have hb1 : m / m.minFac ^ m.factorization m.minFac ≠ 1 := by
      intro h1
      apply hpp
      rw [← hab, h1, mul_one]
      exact hpp'.isPrimePow.pow (by omega)
    exact ⟨_, _, hab, hcop, ha2, by omega⟩
  obtain ⟨a, b, hab, hcop, ha2, hb2⟩ := hsplit
  have halt : a < m := by nlinarith
  have hblt : b < m := by nlinarith
  have hdvd : ∀ x, 1 ≤ x → x < m → x ∣ (Icc 1 (m - 1)).lcm id := fun x h1 h2 =>
    Finset.dvd_lcm (s := Icc 1 (m - 1)) (f := id) (mem_Icc.2 ⟨h1, Nat.le_sub_one_of_lt h2⟩)
  rw [show (id m) = a * b by simp [hab]]
  exact hcop.mul_dvd_of_dvd_of_dvd (hdvd a (by omega) halt) (hdvd b (by omega) hblt)

end E317Aux

open E317Aux

theorem OMA.solution : OMA.R_Erdos317_erdos_317_variants_claim2_R1.H1 := by
  unfold OMA.R_Erdos317_erdos_317_variants_claim2_R1.H1
  classical
  intro n hn
  have hex : ∃ u, n < u ∧ IsPrimePow u :=
    ⟨2 ^ (n + 1), lt_trans (Nat.lt_two_pow_self) (Nat.pow_lt_pow_right (by norm_num) (by omega)),
      Nat.prime_two.isPrimePow.pow (by omega)⟩
  let u := Nat.find hex
  have hu : n < u ∧ IsPrimePow u := Nat.find_spec hex
  have hmin : ∀ m, n < m → m < u → ¬ IsPrimePow m := fun m h1 h2 h3 =>
    Nat.find_min hex h2 ⟨h1, h3⟩
  have hstep : ∀ j, n + j < u → (Icc 1 (n + j)).lcm id = (Icc 1 n).lcm id := by
    intro j
    induction j with
    | zero => intro _; rfl
    | succ j ih =>
      intro hj
      rw [lcm_step (by omega) (hmin _ (by omega) hj),
        show n + (j + 1) - 1 = n + j by omega]
      exact ih (by omega)
  refine ⟨u, hu.1, hu.2, ?_⟩
  have := hstep (u - 1 - n) (by omega)
  rw [show n + (u - 1 - n) = u - 1 by omega] at this
  exact this.symm
