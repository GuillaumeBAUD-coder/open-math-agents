import OMAReductions.R_Erdos364_erdos_364_R1

-- Reduction Erdos364.erdos_364.R1.H3.R1 of step Erdos364.erdos_364.R1.H3
-- Credit: @MBimrose

/-!
# The three surviving classes of a powerful triple, one step each

A triple `n, n + 1, n + 2` of powerful numbers can only start at `n ≡ 7`, `27` or `35 (mod 36)`
(step `Erdos364.erdos_364.R1.H1` and `...H2` of the parent reduction: one of the three is `2 (mod 4)`
and the multiple of `3` among them must be a multiple of `9`).

This reduction splits the remaining statement into its three residue classes, and records in each
hypothesis the arithmetic feature of that class which a proof has to use:

* `H1`, class `7 (mod 36)`: `n + 1 ≡ 8 (mod 36)` and `n + 2 ≡ 9 (mod 36)`, so `9 ∣ n + 2` and `4 ∣ n + 1`.
* `H2`, class `27 (mod 36)`: `n` itself is the multiple of `3`, and `n ≡ 27 (mod 36)` forces `9 ∣ n`.
* `H3`, class `35 (mod 36)`: the middle term is the multiple of `3`, and `n + 1 ≡ 0 (mod 36)`, so
  `36 ∣ n + 1` while `n` and `n + 2` are both odd.

The divisibility in each hypothesis is a consequence of the residue class, so no hypothesis is
stronger than the class it replaces; `main` discharges it by arithmetic on the residues.
-/

namespace OMA.R_Erdos364_erdos_364_R1_H3_R1

/-- Class `7 (mod 36)`: the smallest term is `7 (mod 9)` and the multiple of `3` is `n + 2`. -/
def H1 : Prop :=
  ∀ n : ℕ, n % 36 = 7 → 9 ∣ n + 2 → 4 ∣ n + 1 →
    ¬ (Nat.Powerful n ∧ Nat.Powerful (n + 1) ∧ Nat.Powerful (n + 2))

/-- Class `27 (mod 36)`: the smallest term is itself divisible by `3`, hence by `9`. -/
def H2 : Prop :=
  ∀ n : ℕ, n % 36 = 27 → 9 ∣ n → 4 ∣ n + 1 →
    ¬ (Nat.Powerful n ∧ Nat.Powerful (n + 1) ∧ Nat.Powerful (n + 2))

/-- Class `35 (mod 36)`: the middle term is divisible by `36`, the outer two are odd. -/
def H3 : Prop :=
  ∀ n : ℕ, n % 36 = 35 → 36 ∣ n + 1 → 4 ∣ n + 1 →
    ¬ (Nat.Powerful n ∧ Nat.Powerful (n + 1) ∧ Nat.Powerful (n + 2))

theorem main : H1 → H2 → H3 → OMA.R_Erdos364_erdos_364_R1.H3 := by
  intro h1 h2 h3 n hn
  rcases hn with h7 | h27 | h35
  · exact h1 n h7 (by omega) (by omega)
  · exact h2 n h27 (by omega) (by omega)
  · exact h3 n h35 (by omega) (by omega)

end OMA.R_Erdos364_erdos_364_R1_H3_R1
