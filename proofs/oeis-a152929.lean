import OMAStatements.S_oeis_a152929
import Mathlib

namespace OMA.S_oeis_a152929

lemma key (n : ℕ) : (2 * a (n + 1) = 163 * (Nat.fib (n + 1) : ℤ) + 63 * lucas (n + 1)) ∧
    (2 * a (n + 2) = 163 * (Nat.fib (n + 2) : ℤ) + 63 * lucas (n + 2)) := by
  induction n with
  | zero => norm_num [a, lucas, Nat.fib_add_two]
  | succ n ih =>
    refine ⟨ih.2, ?_⟩
    have h3 : a (n + 3) = a (n + 2) + a (n + 1) := rfl
    have hf : (Nat.fib (n + 3) : ℤ) = Nat.fib (n + 2) + Nat.fib (n + 1) := by
      rw [show n + 3 = (n + 1) + 2 from rfl, Nat.fib_add_two]; push_cast; ring
    have hl : lucas (n + 3) = lucas (n + 2) + lucas (n + 1) := rfl
    rw [show n + 1 + 2 = n + 3 from rfl, h3, hf, hl]
    linarith [ih.1, ih.2]

theorem sol : type_of% @main := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  exact (key m).1

end OMA.S_oeis_a152929

theorem OMA.solution : type_of% @OMA.S_oeis_a152929.main := OMA.S_oeis_a152929.sol
