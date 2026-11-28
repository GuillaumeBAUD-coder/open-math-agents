import OMAReductions.R_CollatzConjecture_collatz_conjecture_R1_H2_R1_H3_R3

open CollatzConjecture

namespace CollatzH1

def stepB (m : ℕ) : ℕ := if m % 2 = 0 then m / 2 else 3 * m + 1

theorem stepB_eq (m : ℕ) : stepB m = collatzStep m := by
  unfold stepB collatzStep
  by_cases h : m % 2 = 0
  · rw [if_pos h, if_pos (Nat.even_iff.mpr h)]
  · rw [if_neg h, if_neg (fun h' => h (Nat.even_iff.mp h'))]

def drops (n : ℕ) : ℕ → ℕ → Bool
  | 0, _ => false
  | f + 1, m => if m < n then true else drops n f (stepB m)

theorem drops_sound (n : ℕ) : ∀ f m, drops n f m = true → ∃ i, collatzStep^[i] m < n := by
  intro f
  induction f with
  | zero => intro m h; simp [drops] at h
  | succ f ih =>
    intro m h
    unfold drops at h
    by_cases hm : m < n
    · exact ⟨0, hm⟩
    · rw [if_neg hm] at h
      obtain ⟨i, hi⟩ := ih _ h
      refine ⟨i + 1, ?_⟩
      rw [Function.iterate_succ_apply, ← stepB_eq]
      exact hi

def L : List ℕ := [27, 31, 47, 63, 71, 91, 103, 111, 127, 155, 159, 167, 191, 207, 223, 231, 239, 251, 255]

def checkAll : Bool :=
  (List.range 391).all fun q => L.all fun r =>
    decide (256 * q + r < 1000) || decide (100000 ≤ 256 * q + r) || drops (256 * q + r) 300 (256 * q + r)

theorem checkAll_true : checkAll = true := by decide +kernel

end CollatzH1

theorem OMA.solution : OMA.R_CollatzConjecture_collatz_conjecture_R1_H2_R1_H3_R3.H1 := by
  intro n h1 h2 hr
  have hc := CollatzH1.checkAll_true
  unfold CollatzH1.checkAll at hc
  rw [List.all_eq_true] at hc
  have hq := hc (n / 256) (List.mem_range.mpr (by omega))
  rw [List.all_eq_true] at hq
  have hn := hq (n % 256) hr
  have e : 256 * (n / 256) + n % 256 = n := Nat.div_add_mod n 256
  rw [e] at hn
  simp only [Bool.or_eq_true, decide_eq_true_eq] at hn
  rcases hn with (hn | hn) | hn
  · omega
  · omega
  · exact CollatzH1.drops_sound n 300 n hn
