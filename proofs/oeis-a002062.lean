import OMAStatements.S_oeis_a002062
import Mathlib

/-
A002062: Fib(n+2) + n + 2 = A006355(n+4) - A066982(n+1), where A006355(m+1) = 2 Fib(m) and
A066982(m) = Lucas(m+1) - (m+1).

luc: Lucas(m+1) = Fib(m+2) + Fib(m), by induction on pairs of consecutive values. The claim then
reduces to Fib(n+3) = Fib(n+1) + Fib(n+2).
-/

namespace OMA.P002062

lemma luc (lucas : ℕ → ℕ) (hl0 : lucas 0 = 2) (hl1 : lucas 1 = 1)
    (hl : ∀ n, lucas (n + 2) = lucas (n + 1) + lucas n) :
    ∀ m, lucas (m + 1) = Nat.fib (m + 2) + Nat.fib m ∧
      lucas (m + 2) = Nat.fib (m + 3) + Nat.fib (m + 1) := by
  intro m
  induction m with
  | zero =>
    refine ⟨by simp [hl1], ?_⟩
    rw [hl, hl1, hl0]
    norm_num [Nat.fib]
  | succ m ih =>
    refine ⟨ih.2, ?_⟩
    rw [hl, ih.2, ih.1, Nat.fib_add_two (n := m + 2), Nat.fib_add_two (n := m)]
    ring

lemma main' (A2 : ℕ → ℕ) (hA2 : ∀ n, A2 n = Nat.fib n + n)
    (A6 : ℕ → ℕ) (hA6 : ∀ n, A6 (n + 1) = 2 * Nat.fib n)
    (lucas : ℕ → ℕ) (hl0 : lucas 0 = 2) (hl1 : lucas 1 = 1)
    (hl : ∀ n, lucas (n + 2) = lucas (n + 1) + lucas n)
    (A9 : ℕ → ℤ) (hA9 : ∀ n, A9 n = (lucas (n + 1) : ℤ) - ((n : ℤ) + 1)) :
    ∀ n : ℕ, (A2 (n + 2) : ℤ) = (A6 (n + 4) : ℤ) - A9 (n + 1) := by
  intro n
  have h := (luc lucas hl0 hl1 hl n).2
  have h3 := Nat.fib_add_two (n := n + 1)
  rw [hA2, hA6, hA9, h]
  push_cast
  rw [show n + 1 + 2 = n + 3 by ring] at h3
  have h3' : (Nat.fib (n + 3) : ℤ) = Nat.fib (n + 1) + Nat.fib (n + 2) := by exact_mod_cast h3
  linear_combination -h3'

end OMA.P002062

theorem OMA.solution : type_of% @OMA.S_oeis_a002062.main :=
  OMA.P002062.main' OMA.S_oeis_a002062.A002062 (fun _ => rfl) OMA.S_oeis_a002062.A006355 (fun _ => rfl)
    OMA.S_oeis_a002062.lucas rfl rfl (fun _ => rfl) OMA.S_oeis_a002062.A066982 (fun _ => rfl)
