import OMAReductions.R_HardyLittlewood_second_hardy_littlewood_conjecture_R1

-- The second Hardy-Littlewood conjecture when one of x, y is at most 26.
-- Let g(n) = (n + 5) / 6 + (n + 1) / 6, the number of integers in [1, n] coprime to 6. A prime above 3 is
-- coprime to 6, so for x >= 3 the number of primes in (x, x + y] is at most g(x + y) - g(x) (induction on y),
-- and for 2 <= y <= 26 that difference is at most the number of primes up to y (25 cases, by omega).
-- The argument 2 is handled by symmetry. A small verified slice; the inequality is known in a far longer range.

namespace OMA.HL2

theorem pc_succ (n : ℕ) :
    Nat.primeCounting (n + 1) = Nat.primeCounting n + if (n + 1).Prime then 1 else 0 := by
  unfold Nat.primeCounting Nat.primeCounting'
  rw [Nat.count_succ]

theorem prime_mod_six (p : ℕ) (hp : p.Prime) (h : 4 ≤ p) : p % 6 = 1 ∨ p % 6 = 5 := by
  have h2 : ¬ 2 ∣ p := fun hd => by
    rcases (Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp hd with h'
    omega
  have h3 : ¬ 3 ∣ p := fun hd => by
    rcases (Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).mp hd with h'
    omega
  omega

theorem step (n : ℕ) (hn : 3 ≤ n) :
    Nat.primeCounting (n + 1) + ((n + 5) / 6 + (n + 1) / 6) ≤
      Nat.primeCounting n + ((n + 1 + 5) / 6 + (n + 1 + 1) / 6) := by
  rw [pc_succ]
  split_ifs with hp
  · have := prime_mod_six (n + 1) hp (by omega)
    omega
  · omega

theorem window (x : ℕ) (hx : 3 ≤ x) (y : ℕ) :
    Nat.primeCounting (x + y) + ((x + 5) / 6 + (x + 1) / 6) ≤
      Nat.primeCounting x + ((x + y + 5) / 6 + (x + y + 1) / 6) := by
  induction y with
  | zero => simp
  | succ y ih =>
    have h := step (x + y) (by omega)
    have e : x + (y + 1) = x + y + 1 := by ring
    rw [e]
    omega

theorem small_right (x y : ℕ) (hx : 3 ≤ x) (hy : 2 ≤ y) (hy' : y ≤ 26) :
    Nat.primeCounting (x + y) ≤ Nat.primeCounting x + Nat.primeCounting y := by
  have h := window x hx y
  interval_cases y
  all_goals
    first
    | (have e : Nat.primeCounting 2 = 1 := by decide
       omega)
    | (have e : Nat.primeCounting 3 = 2 := by decide
       omega)
    | (have e : Nat.primeCounting 4 = 2 := by decide
       omega)
    | (have e : Nat.primeCounting 5 = 3 := by decide
       omega)
    | (have e : Nat.primeCounting 6 = 3 := by decide
       omega)
    | (have e : Nat.primeCounting 7 = 4 := by decide
       omega)
    | (have e : Nat.primeCounting 8 = 4 := by decide
       omega)
    | (have e : Nat.primeCounting 9 = 4 := by decide
       omega)
    | (have e : Nat.primeCounting 10 = 4 := by decide
       omega)
    | (have e : Nat.primeCounting 11 = 5 := by decide
       omega)
    | (have e : Nat.primeCounting 12 = 5 := by decide
       omega)
    | (have e : Nat.primeCounting 13 = 6 := by decide
       omega)
    | (have e : Nat.primeCounting 14 = 6 := by decide
       omega)
    | (have e : Nat.primeCounting 15 = 6 := by decide
       omega)
    | (have e : Nat.primeCounting 16 = 6 := by decide
       omega)
    | (have e : Nat.primeCounting 17 = 7 := by decide
       omega)
    | (have e : Nat.primeCounting 18 = 7 := by decide
       omega)
    | (have e : Nat.primeCounting 19 = 8 := by decide
       omega)
    | (have e : Nat.primeCounting 20 = 8 := by decide
       omega)
    | (have e : Nat.primeCounting 21 = 8 := by decide
       omega)
    | (have e : Nat.primeCounting 22 = 8 := by decide
       omega)
    | (have e : Nat.primeCounting 23 = 9 := by decide
       omega)
    | (have e : Nat.primeCounting 24 = 9 := by decide
       omega)
    | (have e : Nat.primeCounting 25 = 9 := by decide
       omega)
    | (have e : Nat.primeCounting 26 = 9 := by decide
       omega)

theorem small (x y : ℕ) (hx : 2 ≤ x) (hy : 2 ≤ y) (h : x ≤ 26 ∨ y ≤ 26) :
    Nat.primeCounting (x + y) ≤ Nat.primeCounting x + Nat.primeCounting y := by
  by_cases hx3 : 3 ≤ x
  · by_cases hy3 : 3 ≤ y
    · rcases h with h | h
      · have := small_right y x hy3 hx h
        rw [Nat.add_comm x y]
        omega
      · exact small_right x y hx3 hy h
    · exact small_right x y hx3 hy (by omega)
  · have hx2 : x = 2 := by omega
    subst hx2
    by_cases hy3 : 3 ≤ y
    · have := small_right y 2 hy3 (by norm_num) (by norm_num)
      rw [Nat.add_comm 2 y]
      omega
    · have hy2 : y = 2 := by omega
      subst hy2
      decide

end OMA.HL2

theorem OMA.solution : OMA.R_HardyLittlewood_second_hardy_littlewood_conjecture_R1.H1 := by
  intro x y hx hy h
  exact OMA.HL2.small x y hx hy h
