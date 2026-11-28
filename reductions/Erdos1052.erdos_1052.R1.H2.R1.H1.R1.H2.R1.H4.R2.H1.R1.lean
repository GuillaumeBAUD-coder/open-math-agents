import OMAReductions.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H2_R1_H4_R2

-- Reduction Erdos1052.erdos_1052.R1.H2.R1.H1.R1.H2.R1.H4.R2.H1.R1
-- Credit: @heavydawson
-- For the z = 257, a % 16 = 8, Even (n.factorization 257) branch:
--   1. Proves 64 | n.factorization 257 by killing v2(e) in {1, 2, 3, 4, 5}:
--      d = 2 (5^2 | 257^2 + 1), d = 4 (17 -> 3^2), d = 8 (1601 -> 3^2),
--      d = 16 (97 -> 7^2), d = 32 (65537 -> 3^2).
--   2. Proves a % 48 != 24 (97 | 2^24 + 1 -> 7^2) and a % 400 != 200 (1601 | 2^200 + 1 -> 3^2).
--   3. Proves an infinite quadratic-reciprocity family: for every odd prime q != 257 and every
--      prime r != 257 with q^2 | r + 1 and (r % 8 = 3 or r % 8 = 5), a % (r - 1) != (r - 1) / 2.
--   4. Splits the surviving space into H1 (5 | n) and H2 (not 5 | n).

namespace OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H2_R1_H4_R2_H1_R1

open OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1 hiding H1 H2 H3 main
open OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H2_R1 hiding H1 H2 H3 H4 main
open OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H2_R1_H4_R2 hiding H1 H2 H3 main

def H1 : Prop :=
  ∃ A : ℕ, ∀ n : ℕ, Erdos1052.IsUnitaryPerfect n →
    (∀ p, p.Prime ∧ p ≠ 2 ∧ p ^ 2 ∣ n ↔ p = 257) →
    padicValNat 2 n % 16 = 8 →
    n.factorization 257 % 64 = 0 →
    padicValNat 2 n % 48 ≠ 24 →
    padicValNat 2 n % 400 ≠ 200 →
    (∀ q r : ℕ, q.Prime → q ≠ 2 → q ≠ 257 → r.Prime → r ≠ 257 →
      q ^ 2 ∣ r + 1 → (r % 8 = 3 ∨ r % 8 = 5) →
      padicValNat 2 n % (r - 1) ≠ (r - 1) / 2) →
    5 ∣ n →
    padicValNat 2 n ≤ A

def H2 : Prop :=
  ∃ A : ℕ, ∀ n : ℕ, Erdos1052.IsUnitaryPerfect n →
    (∀ p, p.Prime ∧ p ≠ 2 ∧ p ^ 2 ∣ n ↔ p = 257) →
    padicValNat 2 n % 16 = 8 →
    n.factorization 257 % 64 = 0 →
    padicValNat 2 n % 48 ≠ 24 →
    padicValNat 2 n % 400 ≠ 200 →
    (∀ q r : ℕ, q.Prime → q ≠ 2 → q ≠ 257 → r.Prime → r ≠ 257 →
      q ^ 2 ∣ r + 1 → (r % 8 = 3 ∨ r % 8 = 5) →
      padicValNat 2 n % (r - 1) ≠ (r - 1) / 2) →
    ¬ 5 ∣ n →
    padicValNat 2 n ≤ A

-- Section 1: Balance equation and modular helpers.

theorem balance_257 {n : ℕ} (h : Erdos1052.IsUnitaryPerfect n)
    (hiff : ∀ p, p.Prime ∧ p ≠ 2 ∧ p ^ 2 ∣ n ↔ p = 257) :
    ∃ P : Finset ℕ, (∀ p ∈ P, p.Prime ∧ p ≠ 2) ∧
      (2 ^ padicValNat 2 n + 1) * (1 + 257 ^ n.factorization 257) * ∏ p ∈ P, (p + 1) =
        2 ^ (padicValNat 2 n + 1) * 257 ^ n.factorization 257 * ∏ p ∈ P, p := by
  have hn0 : n ≠ 0 := h.2.ne'
  have hs : ∀ r ∈ n.primeFactors, r ≠ 2 → r ≠ 257 → n.factorization r = 1 := by
    intro r hr hr2 hr257
    have hrp := Nat.prime_of_mem_primeFactors hr
    have hpos := hrp.factorization_pos_of_dvd hn0 (Nat.dvd_of_mem_primeFactors hr)
    have : ¬ 2 ≤ n.factorization r := fun he' =>
      hr257 ((hiff r).mp ⟨hrp, hr2, (hrp.pow_dvd_iff_le_factorization hn0).mpr he'⟩)
    omega
  have h257sq := (hiff 257).mpr rfl
  have h257n : 257 ∣ n := (dvd_pow_self 257 (by norm_num)).trans h257sq.2.2
  have h257pf : 257 ∈ n.primeFactors := Nat.mem_primeFactors.mpr ⟨by norm_num, h257n, hn0⟩
  obtain ⟨hP, E⟩ := kernel_balance_one h h257pf (by norm_num) hs
  rw [Nat.factorization_def n Nat.prime_two] at E
  exact ⟨_, hP, E⟩

theorem dvd_pow_add_one_zmod {p b d : ℕ}
    (h : ((b : ZMod p) ^ d + 1) = 0) : p ∣ 1 + b ^ d := by
  rw [add_comm, ← ZMod.natCast_eq_zero_iff]
  push_cast
  exact h

theorem mod_double_zero {a k k2 : ℕ} (hk : 2 * k = k2) (h1 : a % k = 0) (h2 : a % k2 ≠ k) :
    a % k2 = 0 := by
  subst hk
  obtain ⟨q, rfl⟩ := Nat.dvd_of_mod_eq_zero h1
  have hmul : k * q % (2 * k) = k * (q % 2) := by
    rw [mul_comm 2 k, Nat.mul_mod_mul_left]
  rw [hmul] at h2 ⊢
  rcases Nat.mod_two_eq_zero_or_one q with hq | hq <;> simp [hq] at h2 ⊢

-- Section 2: Eliminating v2(e) in {1, 2, 3, 4, 5}.

theorem kill_e2 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 257 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 257 ^ e * ∏ p ∈ P, p)
    (hmod : e % 4 = 2) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 257 ^ e → c ∈ ({257} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 257 → c ∉ ({257} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  have hd : 1 + 257 ^ 2 ∣ 1 + 257 ^ e := one_add_pow_dvd_of_odd_mul (by omega : e % (2 * 2) = 2)
  exact S_sq hP hK E (c := 5) (by norm_num) (by norm_num) (hnz (by norm_num))
    ((((by norm_num : 5 * 5 ∣ 1 + 257 ^ 2).trans hd).mul_left _).mul_right _)

theorem kill_e4 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 257 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 257 ^ e * ∏ p ∈ P, p)
    (hmod : e % 8 = 4) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 257 ^ e → c ∈ ({257} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 257 → c ∉ ({257} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨-, -, -, -, -, S6, S7, -⟩ := facts hP hK E
  have hd : 1 + 257 ^ 4 ∣ 1 + 257 ^ e := one_add_pow_dvd_of_odd_mul (by omega : e % (2 * 4) = 4)
  have g17 : 17 ∈ P := S7 17 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((dvd_pow_add_one_zmod (by reduce_mod_char)).trans hd)
  exact S6 3 (by norm_num) (by norm_num) (hnz (by norm_num)) 17 g17 (by norm_num)

theorem kill_e8 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 257 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 257 ^ e * ∏ p ∈ P, p)
    (hmod : e % 16 = 8) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 257 ^ e → c ∈ ({257} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 257 → c ∉ ({257} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨-, -, -, -, -, S6, S7, -⟩ := facts hP hK E
  have hd : 1 + 257 ^ 8 ∣ 1 + 257 ^ e := one_add_pow_dvd_of_odd_mul (by omega : e % (2 * 8) = 8)
  have g1601 : 1601 ∈ P := S7 1601 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((dvd_pow_add_one_zmod (by reduce_mod_char)).trans hd)
  exact S6 3 (by norm_num) (by norm_num) (hnz (by norm_num)) 1601 g1601 (by norm_num)

theorem kill_e16 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 257 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 257 ^ e * ∏ p ∈ P, p)
    (hmod : e % 32 = 16) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 257 ^ e → c ∈ ({257} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 257 → c ∉ ({257} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨-, -, -, -, -, S6, S7, -⟩ := facts hP hK E
  have hd : 1 + 257 ^ 16 ∣ 1 + 257 ^ e := one_add_pow_dvd_of_odd_mul (by omega : e % (2 * 16) = 16)
  have g97 : 97 ∈ P := S7 97 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((dvd_pow_add_one_zmod (by reduce_mod_char)).trans hd)
  exact S6 7 (by norm_num) (by norm_num) (hnz (by norm_num)) 97 g97 (by norm_num)

theorem kill_e32 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 257 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 257 ^ e * ∏ p ∈ P, p)
    (hmod : e % 64 = 32) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 257 ^ e → c ∈ ({257} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 257 → c ∉ ({257} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨-, -, -, -, -, S6, S7, -⟩ := facts hP hK E
  have hd : 1 + 257 ^ 32 ∣ 1 + 257 ^ e := one_add_pow_dvd_of_odd_mul (by omega : e % (2 * 32) = 32)
  have g65537 : 65537 ∈ P := S7 65537 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((dvd_pow_add_one_zmod (by reduce_mod_char)).trans hd)
  exact S6 3 (by norm_num) (by norm_num) (hnz (by norm_num)) 65537 g65537 (by norm_num)

-- Section 3: Exclusions on a (d = 24, d = 200, and infinite quadratic-reciprocity family).

theorem kill_a24 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 257 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 257 ^ e * ∏ p ∈ P, p)
    (hmod : m % 48 = 24) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 257 ^ e → c ∈ ({257} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 257 → c ∉ ({257} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨-, S2, -, -, -, S6, -, -⟩ := facts hP hK E
  have hd : 2 ^ 24 + 1 ∣ 2 ^ m + 1 := by
    have h := one_add_pow_dvd_of_odd_mul (z := 2) (e0 := 24) (by omega : m % (2 * 24) = 24)
    rwa [add_comm 1 (2 ^ 24), add_comm 1 (2 ^ m)] at h
  have g97 : 97 ∈ P := S2 97 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 97 ∣ 2 ^ 24 + 1).trans hd)
  exact S6 7 (by norm_num) (by norm_num) (hnz (by norm_num)) 97 g97 (by norm_num)

theorem kill_a200 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 257 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 257 ^ e * ∏ p ∈ P, p)
    (hmod : m % 400 = 200) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 257 ^ e → c ∈ ({257} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 257 → c ∉ ({257} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨-, S2, -, -, -, S6, -, -⟩ := facts hP hK E
  have hd : 2 ^ 200 + 1 ∣ 2 ^ m + 1 := by
    have h := one_add_pow_dvd_of_odd_mul (z := 2) (e0 := 200) (by omega : m % (2 * 200) = 200)
    rwa [add_comm 1 (2 ^ 200), add_comm 1 (2 ^ m)] at h
  have h1601 : 1601 ∣ 2 ^ 200 + 1 := by
    rw [add_comm]
    exact dvd_pow_add_one_zmod (by reduce_mod_char)
  have g1601 : 1601 ∈ P := S2 1601 (by norm_num) (by norm_num) (hnz (by norm_num))
    (h1601.trans hd)
  exact S6 3 (by norm_num) (by norm_num) (hnz (by norm_num)) 1601 g1601 (by norm_num)

theorem dvd_two_pow_half_add_one {r : ℕ} (hr : r.Prime) (h8 : r % 8 = 3 ∨ r % 8 = 5) :
    r ∣ 2 ^ ((r - 1) / 2) + 1 := by
  have : Fact r.Prime := ⟨hr⟩
  have hr2 : r ≠ 2 := by omega
  have hodd : r % 2 = 1 := hr.eq_two_or_odd.resolve_left hr2
  have hdiv : r / 2 = (r - 1) / 2 := by omega
  have hleg : legendreSym r 2 = -1 := by
    rw [legendreSym.at_two hr2]
    have hmod : (r : ZMod 8) = 3 ∨ (r : ZMod 8) = 5 := by
      rcases h8 with h | h
      · left; rw [← ZMod.natCast_mod, h]; rfl
      · right; rw [← ZMod.natCast_mod, h]; rfl
    rcases hmod with h | h <;> rw [h] <;> decide
  have hpow : ((2 : ZMod r) ^ (r / 2)) = (-1 : ZMod r) := by
    have h1 := legendreSym.eq_pow r (2 : ℤ)
    rw [hleg] at h1
    simpa only [Int.cast_neg, Int.cast_one, Int.cast_ofNat] using h1.symm
  rw [← ZMod.natCast_eq_zero_iff]
  push_cast
  rw [← hdiv, hpow]
  ring

theorem excl_a_sq_family {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 257 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 257 ^ e * ∏ p ∈ P, p)
    {q r : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) (hq257 : q ≠ 257)
    (hr : r.Prime) (hr257 : r ≠ 257) (hsq : q ^ 2 ∣ r + 1) (h8 : r % 8 = 3 ∨ r % 8 = 5)
    (hmod : m % (r - 1) = (r - 1) / 2) : False := by
  have hr2 : r ≠ 2 := by omega
  have hK : ∀ c : ℕ, c.Prime → c ∣ 257 ^ e → c ∈ ({257} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 257 → c ∉ ({257} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨-, S2, -, -, -, S6, -, -⟩ := facts hP hK E
  have hd_eq : 2 * ((r - 1) / 2) = r - 1 := by
    have := hr.eq_two_or_odd.resolve_left hr2
    omega
  have hdiv : 2 ^ ((r - 1) / 2) + 1 ∣ 2 ^ m + 1 := by
    have h := one_add_pow_dvd_of_odd_mul (z := 2) (e0 := (r - 1) / 2) (by rw [hd_eq]; exact hmod)
    rwa [add_comm 1 (2 ^ ((r - 1) / 2)), add_comm 1 (2 ^ m)] at h
  have hrP : r ∈ P := S2 r hr hr2 (hnz hr257) ((dvd_two_pow_half_add_one hr h8).trans hdiv)
  exact S6 q hq hq2 (hnz hq257) r hrP (by simpa only [sq] using hsq)

-- Section 4: Main reduction.

theorem main : H1 → H2 →
    OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H2_R1_H4_R2.H1 := by
  rintro ⟨A1, h1⟩ ⟨A2, h2⟩
  refine ⟨max A1 A2, fun n h hiff ha16 heven => ?_⟩
  obtain ⟨P, hP, E⟩ := balance_257 h hiff
  set e := n.factorization 257
  have he2 : e % 2 = 0 := Nat.even_iff.mp heven
  have he4 : e % 4 = 0 := mod_double_zero rfl he2 (fun hm => kill_e2 hP E hm)
  have he8 : e % 8 = 0 := mod_double_zero rfl he4 (fun hm => kill_e4 hP E hm)
  have he16 : e % 16 = 0 := mod_double_zero rfl he8 (fun hm => kill_e8 hP E hm)
  have he32 : e % 32 = 0 := mod_double_zero rfl he16 (fun hm => kill_e16 hP E hm)
  have he64 : e % 64 = 0 := mod_double_zero rfl he32 (fun hm => kill_e32 hP E hm)
  have ha24 : padicValNat 2 n % 48 ≠ 24 := fun hm => kill_a24 hP E hm
  have ha200 : padicValNat 2 n % 400 ≠ 200 := fun hm => kill_a200 hP E hm
  have ha_inf : ∀ q r : ℕ, q.Prime → q ≠ 2 → q ≠ 257 → r.Prime → r ≠ 257 →
      q ^ 2 ∣ r + 1 → (r % 8 = 3 ∨ r % 8 = 5) →
      padicValNat 2 n % (r - 1) ≠ (r - 1) / 2 :=
    fun q r hq hq2 hq257 hr hr257 hsq h8 hm =>
      excl_a_sq_family hP E hq hq2 hq257 hr hr257 hsq h8 hm
  by_cases h5 : 5 ∣ n
  · exact (h1 n h hiff ha16 he64 ha24 ha200 ha_inf h5).trans (le_max_left _ _)
  · exact (h2 n h hiff ha16 he64 ha24 ha200 ha_inf h5).trans (le_max_right _ _)

end OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H2_R1_H4_R2_H1_R1
