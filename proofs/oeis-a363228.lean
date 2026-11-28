import OMAStatements.S_oeis_a363228

namespace A363228
open OMA.S_oeis_a363228

lemma exp4_eq (m : ℕ) (hm : m ≠ 0) : exp4 m = padicValNat 2 m / 2 := by
  unfold exp4
  rw [Nat.findGreatest_eq_iff]
  have key : ∀ k, 4 ^ k ∣ m ↔ k ≤ padicValNat 2 m / 2 := by
    intro k
    have : (4 : ℕ) ^ k = 2 ^ (2 * k) := by rw [pow_mul]; norm_num
    rw [this, padicValNat_dvd_iff_le hm]; omega
  refine ⟨?_, ?_, ?_⟩
  · have h1 : 2 ^ padicValNat 2 m ∣ m := pow_padicValNat_dvd
    have h2 := Nat.le_of_dvd (Nat.pos_of_ne_zero hm) h1
    have h3 : padicValNat 2 m < 2 ^ padicValNat 2 m := Nat.lt_two_pow_self ..
    omega
  · intro _; exact (key _).2 le_rfl
  · intro n hn _ h; have := (key n).1 h; omega

lemma val_gen (f : ℕ → ℕ) (hodd : ∀ n, Odd n → f n % 16 = 8)
    (hdbl : ∀ m, 1 ≤ m → ∃ c, f (2 * m) = f m * c ∧ c % 4 = 2) :
    ∀ n, 1 ≤ n → padicValNat 2 (f n) = padicValNat 2 n + 3 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn
    have h2 : padicValNat 2 2 = 1 := padicValNat_self
    rcases Nat.even_or_odd n with he | ho
    · obtain ⟨m, rfl⟩ := he
      have hm : 1 ≤ m := by omega
      obtain ⟨c, hc, hc4⟩ := hdbl m hm
      have ihm := ih m (by omega) hm
      have hfm : f m ≠ 0 := by
        intro h0; rw [h0] at ihm; simp at ihm
      have e : m + m = 2 * m := by ring
      obtain ⟨r, hr⟩ : ∃ r, c = 2 * (2 * r + 1) := ⟨c / 4, by omega⟩
      subst hr
      have b1 : padicValNat 2 (f m * (2 * (2 * r + 1))) =
          padicValNat 2 (f m) + padicValNat 2 (2 * (2 * r + 1)) := padicValNat.mul hfm (by omega)
      have b2 : padicValNat 2 (2 * (2 * r + 1)) = padicValNat 2 2 + padicValNat 2 (2 * r + 1) :=
        padicValNat.mul (by norm_num) (by omega)
      have b3 : padicValNat 2 (2 * m) = padicValNat 2 2 + padicValNat 2 m :=
        padicValNat.mul (by norm_num) (by omega)
      have h3 : padicValNat 2 (2 * r + 1) = 0 := padicValNat.eq_zero_of_not_dvd (by omega)
      rw [e, hc]; omega
    · have h8 := hodd n ho
      obtain ⟨q, hq⟩ : ∃ q, f n = 2 ^ 3 * (2 * q + 1) := ⟨f n / 16, by omega⟩
      have hn2 : padicValNat 2 n = 0 :=
        padicValNat.eq_zero_of_not_dvd (by rcases ho with ⟨k, rfl⟩; omega)
      have a1 : padicValNat 2 (2 ^ 3) = 3 := padicValNat.prime_pow 3
      have a2 : padicValNat 2 (2 * q + 1) = 0 := padicValNat.eq_zero_of_not_dvd (by omega)
      have a3 : padicValNat 2 (2 ^ 3 * (2 * q + 1)) =
          padicValNat 2 (2 ^ 3) + padicValNat 2 (2 * q + 1) :=
        padicValNat.mul (by norm_num) (by omega)
      rw [hq]; omega

lemma fib24 (n : ℕ) : Nat.fib (n + 24) % 16 = Nat.fib n % 16 := by
  have h := Nat.fib_add n 23
  have e23 : Nat.fib 23 = 28657 := by decide
  have e24 : Nat.fib (23 + 1) = 46368 := by decide
  have e : n + 23 + 1 = n + 24 := by ring
  rw [e, e23, e24] at h
  omega

lemma fib6 (k : ℕ) : Nat.fib (6 * k) % 4 = 0 ∧ Nat.fib (6 * k + 1) % 4 = 1 := by
  induction k with
  | zero => exact ⟨by decide, by decide⟩
  | succ k ih =>
    obtain ⟨h0, h1⟩ := ih
    have a := Nat.fib_add (6 * k) 5
    have b := Nat.fib_add (6 * k + 1) 5
    have c : Nat.fib (6 * k + 1 + 1) = Nat.fib (6 * k) + Nat.fib (6 * k + 1) := Nat.fib_add_two
    have e5 : Nat.fib 5 = 5 := by decide
    have e6 : Nat.fib (5 + 1) = 8 := by decide
    rw [e5, e6] at a b
    have x1 : 6 * (k + 1) = 6 * k + 5 + 1 := by ring
    have x2 : 6 * (k + 1) + 1 = 6 * k + 1 + 5 + 1 := by ring
    refine ⟨by rw [x1, a]; omega, by rw [x2, b, c]; omega⟩

lemma fib_odd : ∀ n, Odd n → Nat.fib (6 * n) % 16 = 8 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro ho
    rcases ho with ⟨k, rfl⟩
    rcases k with _ | _ | k
    · decide
    · decide
    · have := ih (2 * k + 1) (by omega) ⟨k, rfl⟩
      have e : 6 * (2 * (k + 1 + 1) + 1) = 6 * (2 * k + 1) + 24 := by ring
      rw [e, fib24]; exact this

lemma fib_dbl : ∀ m, 1 ≤ m → ∃ c, Nat.fib (6 * (2 * m)) = Nat.fib (6 * m) * c ∧ c % 4 = 2 := by
  intro m _
  obtain ⟨h0, h1⟩ := fib6 m
  refine ⟨2 * Nat.fib (6 * m + 1) - Nat.fib (6 * m), ?_, ?_⟩
  · have e : 6 * (2 * m) = 2 * (6 * m) := by ring
    rw [e, Nat.fib_two_mul]
  · have := Nat.fib_le_fib_succ (n := 6 * m)
    omega

lemma pow_odd : ∀ n, Odd n → (9 ^ n - 1) % 16 = 8 := by
  rintro n ⟨k, rfl⟩
  have h : 9 ^ (2 * k + 1) % 16 = 9 := by
    rw [pow_succ, pow_mul, Nat.mul_mod, Nat.pow_mod]; norm_num
  generalize 9 ^ (2 * k + 1) = x at h ⊢
  omega

lemma pow_dbl : ∀ m, 1 ≤ m → ∃ c, 9 ^ (2 * m) - 1 = (9 ^ m - 1) * c ∧ c % 4 = 2 := by
  intro m _
  refine ⟨9 ^ m + 1, ?_, ?_⟩
  · obtain ⟨y, hy⟩ : ∃ y, 9 ^ m = y + 1 :=
      ⟨9 ^ m - 1, by have : 0 < 9 ^ m := by positivity
                     omega⟩
    rw [mul_comm 2 m, pow_mul, hy]
    have : (y + 1) ^ 2 = y * (y + 1 + 1) + 1 := by ring
    rw [this]; simp
  · have : 9 ^ m % 4 = 1 := by rw [Nat.pow_mod]; norm_num
    omega

end A363228

open A363228 OMA.S_oeis_a363228 in
theorem OMA.solution : type_of% @OMA.S_oeis_a363228.main := by
  constructor
  · intro n hn
    have h9 : padicValNat 2 (9 ^ n - 1) = padicValNat 2 n + 3 :=
      val_gen (fun n => 9 ^ n - 1) pow_odd pow_dbl n hn
    have hf : padicValNat 2 (Nat.fib (6 * n)) = padicValNat 2 n + 3 :=
      val_gen (fun n => Nat.fib (6 * n)) fib_odd fib_dbl n hn
    have n9 : 9 ^ n - 1 ≠ 0 := by intro h; rw [h] at h9; simp at h9
    have nf : Nat.fib (6 * n) ≠ 0 := by intro h; rw [h] at hf; simp at hf
    unfold OMA.S_oeis_a363228.a
    rw [exp4_eq _ n9, exp4_eq _ nf, h9, hf]
  · intro m hm h6
    have hm6 : m % 6 ≠ 0 := fun h => h6 (Nat.dvd_of_mod_eq_zero h)
    obtain ⟨h0, h1⟩ := fib6 (m / 6)
    have hfr : ∀ r < 5, Nat.fib (r + 1) % 4 ≠ 0 := by decide
    have hmr : 6 * (m / 6) + (m % 6 - 1) + 1 = m := by omega
    have hr : m % 6 - 1 < 5 := by omega
    have h4 : ¬ 4 ∣ Nat.fib m := by
      intro hd
      rw [← hmr, Nat.fib_add] at hd
      have e1 := Nat.mod_eq_zero_of_dvd hd
      rw [Nat.add_mod, Nat.mul_mod, h0, Nat.mul_mod (Nat.fib (6 * (m / 6) + 1)), h1] at e1
      simp at e1
      exact hfr _ hr (by omega)
    unfold exp4
    rw [Nat.findGreatest_eq_zero_iff]
    intro k hk _ hd
    exact h4 (dvd_trans (dvd_pow_self 4 (by omega)) hd)
