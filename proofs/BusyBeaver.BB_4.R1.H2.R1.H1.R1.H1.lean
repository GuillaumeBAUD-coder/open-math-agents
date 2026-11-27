import OMAReductions.R_BusyBeaver_BB_4_R1_H2_R1_H1_R1

-- Step BusyBeaver.BB_4.R1.H2.R1.H1.R1.H1: hypothesis H1 of reduction BusyBeaver.BB_4.R1.H2.R1.H1.R1
-- Credit: @ishaanzee
-- Proof: a configuration repeated at steps i < j makes the run periodic from i, so every
-- multiStep is some and the machine never halts.

open Turing Turing.BusyBeaver

namespace BBAux

lemma multiStep_add {Γ Λ : Type*} [Inhabited Λ] [Inhabited Γ] (M : Machine Γ Λ)
    (s : Cfg Γ Λ) (a b : ℕ) :
    M.multiStep s (a + b) = (M.multiStep s a).bind (fun c => M.multiStep c b) := by
  induction b with
  | zero => cases h : M.multiStep s a <;> simp [h]
  | succ b ih =>
    rw [← add_assoc, Machine.multiStep_succ, ih]
    cases h : M.multiStep s a <;> simp [h, Machine.multiStep_succ]

end BBAux

open BBAux

theorem OMA.solution : OMA.R_BusyBeaver_BB_4_R1_H2_R1_H1_R1.H1 := by
  unfold OMA.R_BusyBeaver_BB_4_R1_H2_R1_H1_R1.H1
  rintro M - ⟨i, j, hij, -, c, hi, -, hj, -⟩
  have hper : ∀ m, M.multiStep (Machine.init []) (j + m) = M.multiStep (Machine.init []) (i + m) := by
    intro m
    rw [multiStep_add, multiStep_add, hi, hj]
  have hall : ∀ n, (M.multiStep (Machine.init []) n).isSome := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      by_cases hn : n < j
      · rw [Option.isSome_iff_ne_none]
        intro h
        have := Machine.multiStep_eq_none_mono h hn.le
        rw [hj] at this
        exact Option.some_ne_none _ this
      · obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le (not_lt.1 hn)
        rw [hper]
        exact ih _ (by omega)
  intro hH
  obtain ⟨n, hn⟩ := (Machine.isHalting_iff_exists_haltsAt M).1 hH
  have := hall (n + 1)
  rw [Machine.HaltsAfter] at hn
  rw [hn] at this
  exact absurd this (by simp)
