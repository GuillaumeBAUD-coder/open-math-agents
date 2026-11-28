import OMAStatements.S_oeis_a074724
import Mathlib.Data.Nat.Fib.Basic
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.Tactic

namespace OMA.P_oeis_a074724

open OMA.S_oeis_a074724 ArithmeticFunction

/-- Tripling identity for Fibonacci numbers at even indices:
`F(3 * (2 * r)) = F(2 * r) * (5 * F(2 * r) ^ 2 + 3)`. -/
private lemma fib_triple_even (r : ℕ) :
    Nat.fib (3 * (2 * r)) = Nat.fib (2 * r) * (5 * Nat.fib (2 * r) ^ 2 + 3) := by
  have hcass : ∀ k : ℕ, (Nat.fib (k + 1) : ℤ) ^ 2 - (Nat.fib k : ℤ) * (Nat.fib (k + 2) : ℤ) = (-1 : ℤ) ^ k := by
    intro k
    induction k with
    | zero => simp [Nat.fib_zero, Nat.fib_one, Nat.fib_two]
    | succ k ih =>
      have hfib : (Nat.fib (k + 3) : ℤ) = (Nat.fib (k + 1) : ℤ) + (Nat.fib (k + 2) : ℤ) := by
        exact_mod_cast Nat.fib_add_two (n := k + 1)
      have hfib2 : (Nat.fib (k + 2) : ℤ) = (Nat.fib k : ℤ) + (Nat.fib (k + 1) : ℤ) := by
        exact_mod_cast Nat.fib_add_two (n := k)
      rw [show k + 1 + 2 = k + 3 by omega, show k + 1 + 1 = k + 2 by omega, hfib, pow_succ]
      linear_combination -ih + (Nat.fib (k + 2) : ℤ) * hfib2
  have hadd : ∀ a b : ℕ, Nat.fib (a + b + 1) = Nat.fib a * Nat.fib b + Nat.fib (a + 1) * Nat.fib (b + 1) :=
    fun a b => Nat.fib_add a b
  have h2k : ∀ k : ℕ, (Nat.fib (2 * k) : ℤ) = (Nat.fib k : ℤ) * (2 * (Nat.fib (k + 1) : ℤ) - (Nat.fib k : ℤ)) := by
    intro k
    cases k with
    | zero => simp
    | succ m =>
      have h1 := hadd m (m + 1)
      rw [show m + (m + 1) + 1 = 2 * (m + 1) by omega, show m + 1 + 1 = m + 2 by omega] at h1
      have h2 : (Nat.fib (m + 2) : ℤ) = (Nat.fib m : ℤ) + (Nat.fib (m + 1) : ℤ) := by
        exact_mod_cast Nat.fib_add_two (n := m)
      have h1Z : (Nat.fib (2 * (m + 1)) : ℤ) =
          (Nat.fib m : ℤ) * (Nat.fib (m + 1) : ℤ) + (Nat.fib (m + 1) : ℤ) * (Nat.fib (m + 2) : ℤ) := by
        exact_mod_cast h1
      rw [h1Z, h2]; ring
  have h2k1 : ∀ k : ℕ, (Nat.fib (2 * k + 1) : ℤ) = (Nat.fib (k + 1) : ℤ) ^ 2 + (Nat.fib k : ℤ) ^ 2 := by
    intro k
    have h1 := hadd k k
    rw [show k + k + 1 = 2 * k + 1 by omega] at h1
    have h1Z : (Nat.fib (2 * k + 1) : ℤ) =
        (Nat.fib k : ℤ) * (Nat.fib k : ℤ) + (Nat.fib (k + 1) : ℤ) * (Nat.fib (k + 1) : ℤ) := by
      exact_mod_cast h1
    linarith
  have h3k_Z : (Nat.fib (3 * (2 * r)) : ℤ) = (Nat.fib (2 * r) : ℤ) * (5 * (Nat.fib (2 * r) : ℤ) ^ 2 + 3) := by
    cases r with
    | zero => simp
    | succ m =>
      set k : ℕ := 2 * (m + 1)
      have h1 := hadd (k - 1) (2 * k)
      rw [show (k - 1) + 2 * k + 1 = 3 * k by omega, show k - 1 + 1 = k by omega] at h1
      have h1Z : (Nat.fib (3 * k) : ℤ) =
          (Nat.fib (k - 1) : ℤ) * (Nat.fib (2 * k) : ℤ) + (Nat.fib k : ℤ) * (Nat.fib (2 * k + 1) : ℤ) := by
        exact_mod_cast h1
      have hfk : (Nat.fib (k + 1) : ℤ) = (Nat.fib (k - 1) : ℤ) + (Nat.fib k : ℤ) := by
        have h := Nat.fib_add_two (n := k - 1)
        rw [show k - 1 + 2 = k + 1 by omega, show k - 1 + 1 = k by omega] at h
        exact_mod_cast h
      have hc := hcass (k - 1)
      rw [show k - 1 + 1 = k by omega, show k - 1 + 2 = k + 1 by omega] at hc
      have hodd : Odd (k - 1) := ⟨m, by omega⟩
      rw [hodd.neg_one_pow, hfk] at hc
      rw [h1Z, h2k k, h2k1 k, hfk]
      linear_combination -3 * (Nat.fib k : ℤ) * hc
  exact_mod_cast h3k_Z

/-- Periodicity of `Nat.fib k % 9` with period `24`. -/
private lemma fib_mod_nine_add_24 (k : ℕ) :
    Nat.fib (k + 24) % 9 = Nat.fib k % 9 ∧ Nat.fib (k + 25) % 9 = Nat.fib (k + 1) % 9 := by
  induction k with
  | zero => decide
  | succ k ih =>
    refine ⟨ih.2, ?_⟩
    have h1 : Nat.fib (k + 1 + 25) = Nat.fib (k + 24) + Nat.fib (k + 25) := by
      rw [show k + 1 + 25 = (k + 24) + 2 by omega, Nat.fib_add_two]
    have h2 : Nat.fib (k + 1 + 1) = Nat.fib k + Nat.fib (k + 1) := Nat.fib_add_two
    rw [h1, h2, Nat.add_mod, ih.1, ih.2, ← Nat.add_mod]

private lemma fib_mod_nine_mod (k : ℕ) : Nat.fib k % 9 = Nat.fib (k % 24) % 9 := by
  have h : ∀ q r : ℕ, Nat.fib (24 * q + r) % 9 = Nat.fib r % 9 := by
    intro q r
    induction q with
    | zero => simp
    | succ q ih =>
      rw [show 24 * (q + 1) + r = (24 * q + r) + 24 by omega, (fib_mod_nine_add_24 _).1, ih]
  have hdiv : 24 * (k / 24) + k % 24 = k := Nat.div_add_mod k 24
  conv_lhs => rw [← hdiv]
  exact h (k / 24) (k % 24)

private lemma fib_four_mul_mod_nine (m : ℕ) (hm : ¬ 3 ∣ m) :
    3 ∣ Nat.fib (4 * m) ∧ ¬ 9 ∣ Nat.fib (4 * m) := by
  have hmod : Nat.fib (4 * m) % 9 = Nat.fib ((4 * m) % 24) % 9 := fib_mod_nine_mod (4 * m)
  have hrem : (4 * m) % 24 = 4 ∨ (4 * m) % 24 = 8 ∨ (4 * m) % 24 = 16 ∨ (4 * m) % 24 = 20 := by
    omega
  have hval : Nat.fib (4 * m) % 9 = 3 ∨ Nat.fib (4 * m) % 9 = 6 := by
    rcases hrem with h | h | h | h <;> rw [hmod, h] <;> decide
  constructor
  · omega
  · omega

private lemma padicValNat_fib_four_mul (n : ℕ) (hn : 1 ≤ n) :
    padicValNat 3 (Nat.fib (4 * n)) = padicValNat 3 n + 1 := by
  have : Fact (Nat.Prime 3) := ⟨by decide⟩
  set v := padicValNat 3 n
  have h3v_dvd : 3 ^ v ∣ n := pow_padicValNat_dvd
  obtain ⟨m, hm_eq⟩ := h3v_dvd
  have hm_pos : 1 ≤ m := by
    by_contra h0
    have : m = 0 := by omega
    subst this; simp at hm_eq; omega
  have hm_ndvd : ¬ 3 ∣ m := by
    intro hd
    obtain ⟨m', rfl⟩ := hd
    have hdvd : 3 ^ (v + 1) ∣ n := ⟨m', by rw [hm_eq, pow_succ]; ring⟩
    have hle := (padicValNat_dvd_iff_le (by omega : n ≠ 0)).mp hdvd
    omega
  suffices h : ∀ k : ℕ, padicValNat 3 (Nat.fib (4 * (3 ^ k * m))) = k + 1 by
    rw [hm_eq]; exact h v
  intro k
  induction k with
  | zero =>
    rw [pow_zero, one_mul, zero_add]
    obtain ⟨h3, h9⟩ := fib_four_mul_mod_nine m hm_ndvd
    have hne : Nat.fib (4 * m) ≠ 0 := by
      have := Nat.fib_pos.mpr (by omega : 0 < 4 * m); omega
    have hge : 1 ≤ padicValNat 3 (Nat.fib (4 * m)) :=
      (padicValNat_dvd_iff_le hne).mp (by simpa using h3)
    have hlt : padicValNat 3 (Nat.fib (4 * m)) < 2 := by
      by_contra h2
      have hd9 : 3 ^ 2 ∣ Nat.fib (4 * m) :=
        (padicValNat_dvd_iff_le hne).mpr (by omega)
      exact h9 (by simpa using hd9)
    omega
  | succ k ih =>
    have heq : 4 * (3 ^ (k + 1) * m) = 3 * (2 * (2 * (3 ^ k * m))) := by rw [pow_succ]; ring
    have heq2 : 2 * (2 * (3 ^ k * m)) = 4 * (3 ^ k * m) := by ring
    rw [heq, fib_triple_even, heq2]
    set F := Nat.fib (4 * (3 ^ k * m))
    have hF_ne : F ≠ 0 := by
      have hpos : 0 < 4 * (3 ^ k * m) := by positivity
      have := Nat.fib_pos.mpr hpos; omega
    have h3_dvd_F : 3 ∣ F := by
      have : 3 ^ 1 ∣ F := (padicValNat_dvd_iff_le hF_ne).mpr (by omega)
      simpa using this
    have hfac_ne : 5 * F ^ 2 + 3 ≠ 0 := by omega
    rw [padicValNat.mul hF_ne hfac_ne, ih]
    have hfac_val : padicValNat 3 (5 * F ^ 2 + 3) = 1 := by
      obtain ⟨t, ht⟩ := h3_dvd_F
      have hmod9 : (5 * F ^ 2 + 3) % 9 = 3 := by
        have h9 : 5 * F ^ 2 + 3 = 9 * (5 * t ^ 2) + 3 := by rw [ht]; ring
        rw [h9]; omega
      have h3d : 3 ∣ 5 * F ^ 2 + 3 := by omega
      have h9nd : ¬ 9 ∣ 5 * F ^ 2 + 3 := by omega
      have hge : 1 ≤ padicValNat 3 (5 * F ^ 2 + 3) :=
        (padicValNat_dvd_iff_le hfac_ne).mp (by simpa using h3d)
      have hlt : padicValNat 3 (5 * F ^ 2 + 3) < 2 := by
        by_contra h2
        have hd9 : 3 ^ 2 ∣ 5 * F ^ 2 + 3 :=
          (padicValNat_dvd_iff_le hfac_ne).mpr (by omega)
        exact h9nd (by simpa using hd9)
      omega
    omega

private lemma sigma_three_pow (k : ℕ) : 2 * sigma 1 (3 ^ k) = 3 ^ (k + 1) - 1 := by
  have hp : Nat.Prime 3 := by decide
  rw [sigma_one_apply_prime_pow hp]
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ, mul_add, ih]
    have h1 : 1 ≤ 3 ^ (k + 1) := Nat.one_le_pow _ _ (by decide)
    rw [pow_succ 3 (k + 1)]
    omega

private lemma prove_a074724 :
    ∀ n : ℕ, 1 ≤ n →
      a074724 n = 3 ^ (padicValNat 3 n + 1) ∧
      3 * sigma 1 n < sigma 1 (3 * n) ∧
      a074724 n * (sigma 1 (3 * n) - 3 * sigma 1 n) = sigma 1 (3 * n) - sigma 1 n := by
  intro n hn
  have ha : a074724 n = 3 ^ (padicValNat 3 n + 1) := by
    unfold a074724
    rw [padicValNat_fib_four_mul n hn]
  refine ⟨ha, ?_⟩
  have : Fact (Nat.Prime 3) := ⟨by decide⟩
  set v := padicValNat 3 n
  obtain ⟨m, hm_eq⟩ := (pow_padicValNat_dvd : 3 ^ v ∣ n)
  have hm_pos : 1 ≤ m := by
    by_contra h0; have hm0 : m = 0 := by omega
    rw [hm0, mul_zero] at hm_eq; omega
  have hcop : Nat.Coprime (3 ^ v) m := by
    refine Nat.Coprime.pow_left v ?_
    refine (Nat.Prime.coprime_iff_not_dvd (by decide : Nat.Prime 3)).mpr ?_
    intro hd
    obtain ⟨m', rfl⟩ := hd
    have hdvd : 3 ^ (v + 1) ∣ n := ⟨m', by rw [hm_eq, pow_succ]; ring⟩
    have hle := (padicValNat_dvd_iff_le (by omega : n ≠ 0)).mp hdvd
    omega
  have hcop1 : Nat.Coprime (3 ^ (v + 1)) m :=
    Nat.Coprime.pow_left (v + 1) (Nat.Coprime.coprime_dvd_left (dvd_refl 3) (by
      have : Nat.Coprime 3 m := (Nat.Prime.coprime_iff_not_dvd (by decide : Nat.Prime 3)).mpr (by
        intro hd; obtain ⟨m', rfl⟩ := hd
        have hdvd : 3 ^ (v + 1) ∣ n := ⟨m', by rw [hm_eq, pow_succ]; ring⟩
        have hle := (padicValNat_dvd_iff_le (by omega : n ≠ 0)).mp hdvd
        omega)
      exact this))
  have hsn : sigma 1 n = sigma 1 (3 ^ v) * sigma 1 m := by
    rw [hm_eq]; exact isMultiplicative_sigma.map_mul_of_coprime hcop
  have hs3n : sigma 1 (3 * n) = sigma 1 (3 ^ (v + 1)) * sigma 1 m := by
    have h3n : 3 * n = 3 ^ (v + 1) * m := by rw [hm_eq, pow_succ]; ring
    rw [h3n]; exact isMultiplicative_sigma.map_mul_of_coprime hcop1
  have hsm_pos : 1 ≤ sigma 1 m := by
    rw [sigma_one_apply]
    have h1 : 1 ∈ m.divisors := Nat.one_mem_divisors.mpr (by omega)
    exact Finset.single_le_sum (f := fun d : ℕ => d) (fun _ _ => Nat.zero_le _) h1
  have hpow_ge : 1 ≤ 3 ^ (v + 1) := Nat.one_le_pow _ _ (by decide)
  have hdiff1 : sigma 1 (3 ^ (v + 1)) = 3 * sigma 1 (3 ^ v) + 1 := by
    have h1 := sigma_three_pow v
    have h2 := sigma_three_pow (v + 1)
    rw [pow_succ 3 (v + 1)] at h2
    omega
  have hdiff2 : sigma 1 (3 ^ (v + 1)) = sigma 1 (3 ^ v) + 3 ^ (v + 1) := by
    have h1 := sigma_three_pow v
    have h2 := sigma_three_pow (v + 1)
    rw [pow_succ 3 (v + 1)] at h2
    omega
  have hs3n_1 : sigma 1 (3 * n) = 3 * sigma 1 n + sigma 1 m := by
    rw [hs3n, hsn, hdiff1]; ring
  have hs3n_2 : sigma 1 (3 * n) = sigma 1 n + 3 ^ (v + 1) * sigma 1 m := by
    rw [hs3n, hsn, hdiff2]; ring
  refine ⟨by omega, ?_⟩
  rw [ha, hs3n_1, Nat.add_sub_cancel_left]
  omega

end OMA.P_oeis_a074724

theorem OMA.solution : type_of% @OMA.S_oeis_a074724.main :=
  OMA.P_oeis_a074724.prove_a074724
