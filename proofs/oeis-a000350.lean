import OMAStatements.S_oeis_a000350

/-! Formalization of the binary Fibonacci suffix argument recorded by Max Alekseyev
on 3 July 2009 in OEIS A000350, answering a conjecture of Ralf Stephan. -/

namespace OMA.A000350Proof

open Nat

/-- After 3·2^k steps the Fibonacci pair returns to (0,1) modulo 2^(k+1). -/
lemma period_pair (k : ℕ) : ∃ u v : ℤ,
    (fib (3 * 2 ^ k) : ℤ) = 2 * 2 ^ k * u ∧
    (fib (3 * 2 ^ k + 1) : ℤ) = 1 + 2 * 2 ^ k * v := by
  induction k with
  | zero => exact ⟨1, 1, by decide, by decide⟩
  | succ k ih =>
    obtain ⟨u, v, hu, hv⟩ := ih
    let t := 3 * 2 ^ k
    change (fib t : ℤ) = _ at hu
    change (fib (t + 1) : ℤ) = _ at hv
    have hs : fib t ≤ 2 * fib (t + 1) := by
      have := fib_le_fib_succ (n := t)
      omega
    rw [show 3 * 2 ^ (k + 1) = 2 * t by dsimp [t]; ring,
      fib_two_mul, fib_two_mul_add_one]
    push_cast [Nat.cast_sub hs]
    refine ⟨u * (1 + 2 * 2 ^ k * v - 2 ^ k * u),
      v + 2 ^ k * (u ^ 2 + v ^ 2), ?_, ?_⟩ <;> rw [hu, hv] <;> ring

lemma period (k : ℕ) : Function.Periodic (fun n => fib n % 2 ^ (k + 1)) (3 * 2 ^ k) := by
  obtain ⟨u,v,hu,hv⟩ := period_pair k
  let t := 3 * 2 ^ k
  let q := 2 ^ (k + 1)
  have h0 : fib 0 ≡ fib t [MOD q] := by
    apply Nat.modEq_iff_dvd.mpr
    refine ⟨u, ?_⟩
    simpa [q,t,pow_succ,mul_comm,mul_left_comm,mul_assoc] using hu
  have h1 : fib 1 ≡ fib (t+1) [MOD q] := by
    apply Nat.modEq_iff_dvd.mpr
    refine ⟨v, ?_⟩
    rw [show (fib 1 : ℤ) = 1 by decide, hv]
    dsimp [q]
    ring
  intro n
  change fib (n+t) ≡ fib n [MOD q]
  induction n using Nat.twoStepInduction with
  | zero => simpa using h0.symm
  | one => simpa [add_comm] using h1.symm
  | more n ih₀ ih₁ =>
    rw [show n+2+t=n+t+2 by omega, fib_add_two, fib_add_two]
    exact ih₀.add (by simpa [Nat.add_right_comm] using ih₁)

lemma lift_fixed {m r : ℕ} (hr : fib r = r) (h₃ : m ≡ r [MOD 3]) (k : ℕ)
    (hm : fib m ≡ m [MOD 2 ^ k]) : m ≡ r [MOD 2 ^ k] := by
  induction k with
  | zero => rw [pow_zero]; exact Nat.modEq_one
  | succ k ih =>
    have hd : 2 ^ k ∣ 2 ^ (k+1) := by simp [pow_succ]
    have hmr := ih (hm.of_dvd hd)
    have hper : m ≡ r [MOD 3 * 2 ^ k] :=
      (Nat.modEq_and_modEq_iff_modEq_mul ((by decide : Nat.Coprime 3 2).pow_right k)).mp ⟨h₃,hmr⟩
    have heq := congrArg (fun n => fib n % 2 ^ (k+1)) (show m % _ = r % _ from hper)
    have hleft := (period k).map_mod_nat m
    have hright := (period k).map_mod_nat r
    change fib (m % _) % _ = fib (r % _) % _ at heq
    change fib (m % _) % _ = fib m % _ at hleft
    change fib (r % _) % _ = fib r % _ at hright
    exact hm.symm.trans (show fib m ≡ r [MOD 2 ^ (k+1)] by
      rw [← hr]; exact hleft.symm.trans (heq.trans hright))

end OMA.A000350Proof

open OMA.S_oeis_a000350 OMA.A000350Proof Nat

theorem OMA.solution : type_of% @OMA.S_oeis_a000350.main := by
  intro m hm
  constructor
  · rintro ⟨front,hfront⟩
    have hd := congrArg List.reverse hfront
    simp only [List.reverse_reverse, List.reverse_append] at hd
    have heq := congrArg (Nat.ofDigits 2) hd
    simp only [Nat.ofDigits_digits, Nat.ofDigits_append] at heq
    let k := (Nat.digits 2 m).length
    have hcong : fib m ≡ m [MOD 2 ^ k] := by
      change _ % _ = _
      rw [heq]
      simp [k]
    have hm' : m < 2 ^ k := Nat.lt_base_pow_length_digits (by decide)
    by_cases hs : m < 5
    · dsimp [k] at hcong
      interval_cases m <;> first | decide | (exfalso; revert hcong; decide)
    obtain ⟨r,hr,h₃⟩ : ∃ r : ℕ, (r = 0 ∨ r = 1 ∨ r = 5) ∧ m ≡ r [MOD 3] := by
      have := Nat.mod_lt m (by decide : 0 < 3)
      rcases (show m%3=0 ∨ m%3=1 ∨ m%3=2 by omega) with h|h|h
      · exact ⟨0, by simp, h⟩
      · exact ⟨1, by simp, h⟩
      · exact ⟨5, by simp, h⟩
    have hfix : fib r = r := by rcases hr with rfl|rfl|rfl <;> decide
    have hsmall : r < 2 ^ k := by rcases hr with rfl|rfl|rfl <;> omega
    have he : m % 2 ^ k = r % 2 ^ k := lift_fixed hfix h₃ k hcong
    rw [Nat.mod_eq_of_lt hm', Nat.mod_eq_of_lt hsmall] at he
    omega
  · rintro (rfl|rfl) <;> exact ⟨[], by decide⟩
