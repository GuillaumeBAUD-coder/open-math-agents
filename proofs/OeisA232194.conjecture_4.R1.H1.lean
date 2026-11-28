import OMAReductions.R_OeisA232194_conjecture_4_R1
import Mathlib

/-!
A kernel search: for each `1 < n ≤ 1000`, `n ≠ 8`, try `x = 1, 2, …` until `n * x ^ 2 + (n - x)`
passes a trial-division primality test (the least such `x` is at most 71).
-/

namespace OMA.A232194

def ptest (n : ℕ) : Bool :=
  decide (2 ≤ n) && (List.range' 2 (Nat.sqrt n - 1)).all (fun d => n % d != 0)

theorem ptest_sound {n : ℕ} (h : ptest n = true) : n.Prime := by
  unfold ptest at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range'_1,
    bne_iff_ne, ne_eq] at h
  obtain ⟨h2, hall⟩ := h
  rw [Nat.prime_def_le_sqrt]
  refine ⟨h2, fun m hm2 hmle hdvd => ?_⟩
  exact hall m ⟨hm2, by omega⟩ (Nat.mod_eq_zero_of_dvd hdvd)

def good (n : ℕ) : Bool := (List.range' 1 (n - 1)).any (fun x => ptest (n * x ^ 2 + (n - x)))

theorem good_sound {n : ℕ} (h : good n = true) :
    ∃ x y : ℕ, 0 < x ∧ 0 < y ∧ x + y = n ∧ (n * x ^ 2 + y).Prime := by
  unfold good at h
  simp only [List.any_eq_true, List.mem_range'_1] at h
  obtain ⟨x, ⟨hx1, hx2⟩, hp⟩ := h
  exact ⟨x, n - x, hx1, by omega, by omega, ptest_sound hp⟩

theorem all_good : (List.range' 2 999).all (fun n => n == 8 || good n) = true := by
  decide +kernel

end OMA.A232194

theorem OMA.solution : OMA.R_OeisA232194_conjecture_4_R1.H1 := by
  intro n hn1 hn2 hn8
  have h := List.all_eq_true.mp OMA.A232194.all_good n (List.mem_range'_1.mpr ⟨hn1, by omega⟩)
  simp only [Bool.or_eq_true, beq_iff_eq] at h
  rcases h with h | h
  · exact absurd h hn8
  · exact OMA.A232194.good_sound h
