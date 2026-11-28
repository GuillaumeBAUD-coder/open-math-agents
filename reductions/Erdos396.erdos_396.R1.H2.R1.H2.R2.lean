import OMAReductions.R_Erdos396_erdos_396_R1_H2_R1
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Data.Nat.Choose.Factorization

-- Credit: @kaleidoKurt

/-!
Split the eighteen consecutive factors into two length-nine windows. For
primes greater than seventeen, each shorter window can be tested at its
own endpoint. A prime dividing the lower window cannot divide a factor of
the upper window. The central binomial recurrence therefore preserves
every copy supplied at the lower endpoint as the window moves up.

The two remaining questions concern different sets of endpoints. One bounds
the frequency of failures at the seven small primes. The other asks for
pairs of successful large-prime windows nine apart with positive upper
density. The counting argument needs no independence assumption.
-/

namespace OMA.R_Erdos396_erdos_396_R1_H2_R1_H2_R2

/-- Small-prime failures among pairs of adjacent windows have density zero. -/
def H1 : Prop := by
  classical
  exact ∀ C : ℕ, ∃ L : ℕ, ∀ N ≥ L,
    C * ((Finset.range N).filter (fun m => ∃ p : ℕ, p.Prime ∧ p ≤ 17 ∧
      (m + 9).centralBinom.factorization p <
        (m.descFactorial 9).factorization p +
        ((m + 9).descFactorial 9).factorization p)).card ≤ N

/-- The set of length-nine windows passing every prime above seventeen
has positive upper density of pairs at distance nine. Each test uses only
the central binomial coefficient at the endpoint of the shorter window. -/
def H2 : Prop := by
  classical
  exact ∃ C : ℕ, ∀ L : ℕ, ∃ N ≥ L,
    N < C * ((Finset.range N).filter (fun m => 9 ≤ m ∧
      ∀ p : ℕ, p.Prime → 17 < p →
        (m.descFactorial 9).factorization p ≤ m.centralBinom.factorization p ∧
        ((m + 9).descFactorial 9).factorization p ≤
          (m + 9).centralBinom.factorization p)).card

theorem split_window (m a b : ℕ) :
    (m + a).descFactorial (a + b) =
      m.descFactorial b * (m + a).descFactorial a := by
  induction b with
  | zero => simp
  | succ b ih =>
    rw [Nat.add_succ, Nat.descFactorial_succ, Nat.descFactorial_succ m, ih,
      show m + a - (a+b) = m-b by omega, Nat.mul_assoc]

theorem prime_has_offset {p m w : ℕ} (hp : p.Prime)
    (h : p ∣ m.descFactorial w) : ∃ i < w, p ∣ m-i := by
  induction w with
  | zero => exact (hp.not_dvd_one (by simpa using h)).elim
  | succ w ih =>
    rw [Nat.descFactorial_succ] at h
    rcases hp.dvd_mul.mp h with last | earlier
    · exact ⟨w, by omega, last⟩
    · obtain ⟨i, hi, hit⟩ := ih earlier
      exact ⟨i, by omega, hit⟩

theorem avoids_shift {p m w : ℕ} (hp : p.Prime) (hw : w ≤ m)
    (hbig : 2*w ≤ p) (hb : p ∣ m.descFactorial w) :
    ∀ j, 0 < j → j ≤ w → ¬ p ∣ m+j := by
  obtain ⟨i, hi, hit⟩ := prime_has_offset hp hb
  intro j hj hjw h
  have hsum : p ∣ (m-i) + (i+j) := by simpa only [show m-i+(i+j) = m+j by omega] using h
  have diff : p ∣ i+j := (Nat.dvd_add_iff_right hit).mpr hsum
  have := Nat.le_of_dvd (show 0 < i+j by omega) diff
  omega

/-- A large prime occurring in the lower block can only gain valuation in
the central binomial coefficient while advancing to the upper endpoint. -/
theorem supply_mono {p m w : ℕ} (hp : p.Prime) (hw : w ≤ m)
    (hbig : 2*w ≤ p) (hb : p ∣ m.descFactorial w) :
    ∀ j ≤ w, m.centralBinom.factorization p ≤ (m+j).centralBinom.factorization p := by
  intro j hj
  induction j with
  | zero => simp
  | succ j ih =>
    have keep := ih (by omega)
    have no := avoids_shift hp hw hbig hb (j+1) (by omega) hj
    have eq := congrArg (fun n : ℕ => n.factorization p)
      (Nat.succ_mul_centralBinom_succ (m+j))
    have hz : ¬ p ∣ m+j+1 := by simpa only [Nat.add_assoc] using no
    simp only [Nat.factorization_mul (show m+j+1 ≠ 0 by omega) (Nat.centralBinom_ne_zero _),
      Nat.factorization_mul (show 2*(2*(m+j)+1) ≠ 0 by positivity) (Nat.centralBinom_ne_zero _),
      Finsupp.coe_add, Pi.add_apply, Nat.factorization_eq_zero_of_not_dvd hz, zero_add] at eq
    change m.centralBinom.factorization p ≤ (m+j+1).centralBinom.factorization p
    omega

theorem join_windows {m : ℕ} (hm : 9 ≤ m)
    (small : ∀ p : ℕ, p.Prime → p ≤ 17 →
      (m.descFactorial 9).factorization p + ((m+9).descFactorial 9).factorization p ≤
        (m+9).centralBinom.factorization p)
    (big : ∀ p : ℕ, p.Prime → 17 < p →
      (m.descFactorial 9).factorization p ≤ m.centralBinom.factorization p ∧
      ((m+9).descFactorial 9).factorization p ≤ (m+9).centralBinom.factorization p) :
    (m+9).descFactorial 18 ∣ (m+9).centralBinom := by
  rw [show 18 = 9 + 9 by decide, split_window]
  have lo := (Nat.descFactorial_pos.mpr hm).ne'
  have hi := (Nat.descFactorial_pos.mpr (show 9 ≤ m+9 by omega)).ne'
  apply (Nat.factorization_le_iff_dvd (mul_ne_zero lo hi) (Nat.centralBinom_ne_zero _)).mp
  intro p
  by_cases hp : p.Prime
  · rw [Nat.factorization_mul lo hi, Finsupp.coe_add, Pi.add_apply]
    by_cases hs : p ≤ 17
    · exact small p hp hs
    · obtain ⟨lower, upper⟩ := big p hp (by omega)
      by_cases hb : p ∣ m.descFactorial 9
      · have hu : ¬ p ∣ (m+9).descFactorial 9 := by
          intro hit
          obtain ⟨i, h, hd⟩ := prime_has_offset hp hit
          apply avoids_shift hp hm (by omega) hb (9-i) (by omega) (by omega)
          simpa only [show m+9-i = m+(9-i) by omega] using hd
        rw [Nat.factorization_eq_zero_of_not_dvd hu, add_zero]
        exact lower.trans (supply_mono hp hm (by omega) hb 9 (by omega))
      · simpa only [Nat.factorization_eq_zero_of_not_dvd hb, zero_add] using upper
  · simp [Nat.factorization_eq_zero_of_not_prime _ hp]

theorem main : H1 → H2 → OMA.R_Erdos396_erdos_396_R1_H2_R1.H2 := by
  classical
  intro scarce pairs
  obtain ⟨C, often⟩ := pairs
  obtain ⟨L, bound⟩ := scarce C
  obtain ⟨N, hN, many⟩ := often L
  let bad := (Finset.range N).filter (fun m => ∃ p : ℕ, p.Prime ∧ p ≤ 17 ∧
    (m+9).centralBinom.factorization p <
      (m.descFactorial 9).factorization p + ((m+9).descFactorial 9).factorization p)
  let good := (Finset.range N).filter (fun m => 9 ≤ m ∧
    ∀ p : ℕ, p.Prime → 17 < p →
      (m.descFactorial 9).factorization p ≤ m.centralBinom.factorization p ∧
      ((m+9).descFactorial 9).factorization p ≤ (m+9).centralBinom.factorization p)
  have outside : ¬ good ⊆ bad := fun incl =>
    (Nat.not_lt_of_ge ((Nat.mul_le_mul_left C (Finset.card_le_card incl)).trans (bound N hN))) many
  obtain ⟨m, hg, hb⟩ := Finset.not_subset.mp outside
  obtain ⟨hr, hm, hlarge⟩ := Finset.mem_filter.mp hg
  refine ⟨m+9, join_windows hm (fun p hp hs => ?_) hlarge⟩
  exact le_of_not_gt (fun h => hb (Finset.mem_filter.mpr ⟨hr, p, hp, hs, h⟩))

end OMA.R_Erdos396_erdos_396_R1_H2_R1_H2_R2
