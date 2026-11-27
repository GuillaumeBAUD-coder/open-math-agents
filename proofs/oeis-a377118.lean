import OMAStatements.S_oeis_a377118
import Mathlib

/-!
# Solution and table correction for OEIS A377118

The general prime-divisibility and eventual-gap claims hold. The full statement
also asserts six explicit gap blocks. For p = 3 its first gap is 3, which is
absent from the printed block in every cyclic phase.

Credit: @thomasfredrickson with Codex. Conjecture: Clark Kimberling.
Source: https://oeis.org/A377118
-/

namespace A377118Proof

open OMA.S_oeis_a377118

/-- The stored coefficients expand the defining power at any cube root of two. -/
theorem expansion {R : Type*} [CommSemiring R] (t : R) (ht : t ^ 3 = 2) (n : ℕ) :
    (t + t ^ 2) ^ n = (coefficients n).1 + (coefficients n).2.1 * t +
      (coefficients n).2.2 * t ^ 2 := by
  induction n with
  | zero => simp [coefficients]
  | succ n ih =>
    rw [pow_succ, ih]
    simp only [coefficients]
    generalize coefficients n = s
    obtain ⟨u, v, w⟩ := s
    push_cast
    ring_nf
    rw [show t ^ 4 = 2 * t by rw [pow_succ t 3, ht], ht]
    ring

theorem recurrence (n : ℕ) : a (n + 3) = 6 * (a n + a (n + 1)) := by
  simp only [a, coefficients]
  ring

private abbrev State (p : ℕ) := ZMod p × ZMod p × ZMod p

private def step {p : ℕ} (s : State p) : State p :=
  (s.2.1, s.2.2, 6 * (s.1 + s.2.1))

private def state (p n : ℕ) : State p := (a n, a (n + 1), a (n + 2))

private theorem state_succ (p n : ℕ) : state p (n + 1) = step (state p n) := by
  simp [state, step, recurrence]

private theorem iterate_state (p n : ℕ) :
    step^[n] (state p 0) = state p n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply', ih, state_succ]

private theorem step_injective {p : ℕ} [Fact p.Prime] (h : (6 : ZMod p) ≠ 0) :
    Function.Injective (step (p := p)) := by
  rintro ⟨x, y, z⟩ ⟨x', y', z'⟩ he
  simp only [step, Prod.mk.injEq] at he ⊢
  obtain ⟨rfl, rfl, he⟩ := he
  exact ⟨add_right_cancel (mul_left_cancel₀ h he), rfl, rfl⟩

/-- A zero in the periodic part, together with a shift preserving all subsequent hits. -/
private theorem periodic_hits (p : ℕ) (hp : p.Prime) :
    ∃ N T : ℕ, 0 < T ∧ p ∣ a N ∧ ∀ n ≥ N, (p ∣ a (n + T) ↔ p ∣ a n) := by
  by_cases h : p ∣ 6
  · have tail (n : ℕ) (hn : 3 ≤ n) : p ∣ a n := by
      obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hn
      rw [Nat.add_comm, recurrence]
      exact dvd_mul_of_dvd_left h _
    exact ⟨3, 1, by decide, tail 3 le_rfl, fun n hn => iff_of_true (tail _ (by omega)) (tail n hn)⟩
  · let : Fact p.Prime := ⟨hp⟩
    have h6 : (6 : ZMod p) ≠ 0 := fun he => h ((ZMod.natCast_eq_zero_iff 6 p).mp he)
    obtain ⟨T, hT, hret⟩ := (step_injective h6).mem_periodicPts (state p 0)
    have h0 : state p T = state p 0 := (iterate_state p T).symm.trans hret.eq
    have every (n : ℕ) : state p (n + T) = state p n := by
      induction n with
      | zero => simpa using h0
      | succ n ih =>
        rw [Nat.succ_add, state_succ, state_succ, ih]
    refine ⟨0, T, hT, dvd_zero _, fun n _ => ?_⟩
    have he := congrArg Prod.fst (every n)
    change (a (n + T) : ZMod p) = (a n : ZMod p) at he
    rw [← ZMod.natCast_eq_zero_iff, ← ZMod.natCast_eq_zero_iff, he]

/-- Difference between consecutive hit indices, enumerated starting at index zero. -/
private noncomputable def hitGap (P : ℕ → Prop) (j : ℕ) : ℕ :=
  Nat.nth P (j + 1) - Nat.nth P j

private theorem gaps_of_periodic_hits (P : ℕ → Prop) [DecidablePred P] (N T : ℕ)
    (hT : 0 < T) (hN : P N) (shift : ∀ n ≥ N, P (n + T) ↔ P n) :
    (Set.ofPred P).Infinite ∧ ∃ d > 0, ∀ j ≥ N, hitGap P (j + d) = hitGap P j := by
  have hits (k : ℕ) : P (N + k * T) := by
    induction k with
    | zero => simpa using hN
    | succ k ih => simpa [Nat.succ_mul, Nat.add_assoc] using (shift (N + k * T) (by omega)).2 ih
  have inf : (Set.ofPred P).Infinite := by
    apply Set.infinite_iff_exists_gt.mpr
    intro k
    exact ⟨N + (k + 1) * T, hits _, by nlinarith⟩
  -- Exactly d hits occur per period once the repeating part begins.
  let d := Nat.count P (N + T) - Nat.count P N
  have more : Nat.count P N < Nat.count P (N + T) := Nat.count_strict_mono hN (by omega)
  have count_shift (n : ℕ) (hn : N ≤ n) : Nat.count P (n + T) = Nat.count P n + d := by
    induction n, hn using Nat.le_induction with
    | base => dsimp [d]; omega
    | succ n hn ih =>
      rw [Nat.succ_add, Nat.count_succ, Nat.count_succ P n, ih, if_congr (shift n hn) rfl rfl]
      omega
  have nth_shift (j : ℕ) (hj : N ≤ j) : Nat.nth P (j + d) = Nat.nth P j + T := by
    have hindex : N ≤ Nat.nth P j := hj.trans (Nat.le_nth fun hf => (inf hf).elim)
    have hit := (shift _ hindex).2 (Nat.nth_mem_of_infinite inf j)
    have hc := count_shift _ hindex
    rw [Nat.count_nth_of_infinite inf] at hc
    rw [← hc, Nat.nth_count hit]
  refine ⟨inf, d, by dsimp [d]; omega, fun j hj => ?_⟩
  dsimp [hitGap]
  rw [show j + d + 1 = j + 1 + d by omega, nth_shift _ (by omega), nth_shift _ hj]
  omega

/-- Every prime hits infinitely often, and the successive gaps are eventually periodic. -/
theorem general_result (p : ℕ) (hp : p.Prime) : generalClaim p := by
  obtain ⟨N, T, hT, hN, shift⟩ := periodic_hits p hp
  obtain ⟨inf, d, hd, hg⟩ := gaps_of_periodic_hits (fun n => p ∣ a n) N T hT hN shift
  exact ⟨inf, d, hd, N, hg⟩

/-- With the OEIS offset zero the indices divisible by 3 are exactly 0, 3, 4, 5, ... . -/
theorem three_dvd_iff (n : ℕ) : 3 ∣ a n ↔ n = 0 ∨ 3 ≤ n := by
  rcases n with _ | _ | _ | n
  · decide
  · decide
  · decide
  · rw [recurrence]
    exact iff_of_true (dvd_mul_of_dvd_left (by decide : 3 ∣ 6) _) (Or.inr (by omega))


private theorem first_gap_three : gap 3 0 = 3 := by
  let P := fun n => 3 ∣ a n
  have first : Nat.nth P 0 = 0 := by
    have he := Nat.nth_count (p := P) (n := 0) (by decide)
    simpa using he
  have second : Nat.nth P 1 = 3 := by
    have he := Nat.nth_count (p := P) (n := 3) (by decide)
    rwa [show Nat.count P 3 = 1 by decide] at he
  change Nat.nth P 1 - Nat.nth P 0 = 3
  rw [first, second]

end A377118Proof

open OMA.S_oeis_a377118

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a377118.main) := by
  intro claim
  obtain ⟨phase, pattern⟩ := ((claim 3 (by decide)).2 [9, 4, 1, 2, 8] (by decide)).1
  have first := pattern 0
  rw [A377118Proof.first_gap_three] at first
  change 3 = [9, 4, 1, 2, 8].getD ((0 + phase) % 5) 0 at first
  have bounded := Nat.mod_lt (0 + phase) (by decide : 0 < 5)
  generalize (0 + phase) % 5 = i at first bounded
  interval_cases i <;> contradiction
