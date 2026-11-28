import OMAStatements.S_oeis_a134492
import Mathlib

/-!
# A134492: disproof of the set equality

`Nat.fib 45 = 1134903170 = 10370 * 109441` is the perimeter of the Pythagorean triple
`109441 * (3145, 2928, 4297)`, but `45` is not a multiple of `6`, and `Nat.fib` is injective
on indices `≥ 2`.
-/

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a134492.main) := by
  intro h
  have h45 : Nat.fib 45 = 1134903170 := by norm_num
  have hmem : Nat.fib 45 ∈ {x : ℕ | (∃ j : ℕ, x = Nat.fib j) ∧
      OMA.S_oeis_a134492.IsPythagoreanSum x} := by
    refine ⟨⟨45, rfl⟩, 3145 * 109441, 2928 * 109441, 4297 * 109441, ?_, ?_, ?_, ?_, ?_⟩
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · rw [h45]
  rw [← h] at hmem
  obtain ⟨n, hn, hfib⟩ := hmem
  have hinj := Nat.fib_add_two_strictMono.injective
  have h1 : (fun k => Nat.fib (k + 2)) 43 = (fun k => Nat.fib (k + 2)) (6 * n - 2) := by
    show Nat.fib (43 + 2) = Nat.fib (6 * n - 2 + 2)
    have e : 6 * n - 2 + 2 = 6 * n := by omega
    rw [e]
    exact hfib
  have h2 := hinj h1
  omega
