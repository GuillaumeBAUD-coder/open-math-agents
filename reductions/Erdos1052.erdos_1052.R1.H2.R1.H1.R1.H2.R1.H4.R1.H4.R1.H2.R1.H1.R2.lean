import OMAReductions.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H2_R1_H4_R1_H4_R1_H2_R1
import Mathlib

-- Reduction Erdos1052.erdos_1052.R1.H2.R1.H1.R1.H2.R1.H4.R1.H4.R1.H2.R1.H1.R2
-- of step Erdos1052.erdos_1052.R1.H2.R1.H1.R1.H2.R1.H4.R1.H4.R1.H2.R1.H1
-- Credit: @DPS0340

/-!
# 32 | e, z in {11, 13, 17, 19}: z = 13 settled completely; a odd and 4 | a settled except z = 17, a = 4 mod 8

Reduces step H1 of Erdos1052.erdos_1052.R1.H2.R1.H1.R1.H2.R1.H4.R1.H4.R1.H2.R1 (unitary perfect number n with
unique repeated odd prime z in {11, 13, 17, 19} and 32 | e = v_z(n); bound a = padicValNat 2 n).

Proved below with no hypothesis:
  (1) a odd, z in {11, 13, 17, 19}: a <= 7, using a uniform weight beta(7) = 64/51 (from 7 <- 13 <- >=103
      or 7 <- >=181) and sharp z-leaf bounds (`zleaves_one` / `zleaves_skip`); totals <= 1.9869 < 2.
  (2) 4 | a, z in {11, 13, 17, 19} except (z = 17, a = 4 mod 8): no positive solution.
      For a != 8 mod 16 (and a != 4 mod 8), the Fermat prime c >= 4097 pins 3 with weight (4/3)(4098/4096),
      totals <= 1.9850 < 2. For z = 11, a = 8 mod 16, F_3 = 257 pins 3 with weight (4/3)(258/256),
      total <= 1.9830 < 2.
  (3) z = 13, a = 2 mod 4: a <= 13, since 13 is not a simple prime; giving kept-parent weights to
      7 (<- 181, 223, or >=307), 31 (<- 61 <- 487 <- >=5843), 103 (<- >=823), and 127 (<- >=3301),
      together with j = 2 splitting on leaf 337, yields total <= 1.9986 < 2 for a >= 14.

Remaining four independent subcases:
  H1: z = 11 and a = 2 mod 4.
  H2: z = 17 and a = 2 mod 4.
  H3: z = 19 and a = 2 mod 4.
  H4: z = 17 and a = 4 mod 8.
-/

namespace OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H2_R1_H4_R1_H4_R1_H2_R1_H1_R2

open OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1 (facts three_dvd_two_pow_add_one kernel_balance_one
  master_gen mersenne_bound zleaf_bound fiber_bound two_pow_of_no_odd_prime
  two_pow_mul_pow_of_odd_primes_eq one_add_le_B B_anti B_nonneg)
open OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H2_R1 (simple_of_unique_repeated)
open OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H2_R1_H4_R1_H4_R1_H2_R1 (exists_fermat_prime
  two_pow_succ_dvd_pred v2_large v2_eq_three ge_4097 ge_eleven kk_le table_close setup5
  far_step nx13_103 fiber_split zleaves_skip zleaves_one odd_ge_nine four_dvd_of_not)

-- H1: a is bounded when z = 11 and a = 2 mod 4.
def H1 : Prop :=
  ∃ A : ℕ, ∀ n : ℕ, Erdos1052.IsUnitaryPerfect n →
    (∀ p, p.Prime ∧ p ≠ 2 ∧ p ^ 2 ∣ n ↔ p = 11) →
    n.factorization 11 % 32 = 0 →
    padicValNat 2 n % 20 ≠ 10 → padicValNat 2 n % 28 ≠ 14 →
    padicValNat 2 n % 4 = 2 →
    padicValNat 2 n ≤ A

-- H2: a is bounded when z = 17 and a = 2 mod 4.
def H2 : Prop :=
  ∃ A : ℕ, ∀ n : ℕ, Erdos1052.IsUnitaryPerfect n →
    (∀ p, p.Prime ∧ p ≠ 2 ∧ p ^ 2 ∣ n ↔ p = 17) →
    n.factorization 17 % 32 = 0 →
    padicValNat 2 n % 20 ≠ 10 → padicValNat 2 n % 28 ≠ 14 →
    padicValNat 2 n % 4 = 2 →
    padicValNat 2 n ≤ A

-- H3: a is bounded when z = 19 and a = 2 mod 4.
def H3 : Prop :=
  ∃ A : ℕ, ∀ n : ℕ, Erdos1052.IsUnitaryPerfect n →
    (∀ p, p.Prime ∧ p ≠ 2 ∧ p ^ 2 ∣ n ↔ p = 19) →
    n.factorization 19 % 32 = 0 →
    padicValNat 2 n % 20 ≠ 10 → padicValNat 2 n % 28 ≠ 14 →
    padicValNat 2 n % 4 = 2 →
    padicValNat 2 n ≤ A

-- H4: a is bounded when z = 17 and a = 4 mod 8.
def H4 : Prop :=
  ∃ A : ℕ, ∀ n : ℕ, Erdos1052.IsUnitaryPerfect n →
    (∀ p, p.Prime ∧ p ≠ 2 ∧ p ^ 2 ∣ n ↔ p = 17) →
    n.factorization 17 % 32 = 0 →
    padicValNat 2 n % 8 = 4 →
    padicValNat 2 n ≤ A

-- ### Section 1: Kept-parent bounds for `z ∈ {11, 13, 17, 19}`

/-- Kept parents of `7` for `z ≥ 11`: `13`, or at least `181`. -/
theorem nx7_small {z p : ℕ} (hz : 11 ≤ z) (hp : p.Prime) (hd : 7 ∣ p + 1) (hsq : ¬ 7 * 7 ∣ p + 1)
    (hl : ∀ c' : ℕ, c'.Prime → c' ≠ 2 → c' ∉ ({z} : Finset ℕ) → c' ∣ p + 1 → 7 ≤ c') :
    p = 13 ∨ 181 ≤ p := by
  have h3z : (3 : ℕ) ∉ ({z} : Finset ℕ) := by rw [Finset.mem_singleton]; omega
  have h5z : (5 : ℕ) ∉ ({z} : Finset ℕ) := by rw [Finset.mem_singleton]; omega
  by_contra hcon
  push Not at hcon
  obtain ⟨k, hk⟩ := hd
  have hk26 : k < 26 := by omega
  obtain rfl : p = 7 * k - 1 := by omega
  interval_cases k <;>
    first
    | omega
    | (norm_num at hp; done)
    | (exact absurd (by decide) hsq; done)
    | (have := hl 3 (by norm_num) (by norm_num) h3z (by decide); omega)
    | (have := hl 5 (by norm_num) (by norm_num) h5z (by decide); omega)

/-- Kept parents of `7` for `z = 13` (excluding `13`): `181`, `223`, or at least `307`. -/
theorem nx7_13 {p : ℕ} (hp : p.Prime) (hp13 : p ≠ 13) (hd : 7 ∣ p + 1) (hsq : ¬ 7 * 7 ∣ p + 1)
    (hl : ∀ c' : ℕ, c'.Prime → c' ≠ 2 → c' ∉ ({13} : Finset ℕ) → c' ∣ p + 1 → 7 ≤ c') :
    p = 181 ∨ p = 223 ∨ 307 ≤ p := by
  have h3z : (3 : ℕ) ∉ ({13} : Finset ℕ) := by simp
  have h5z : (5 : ℕ) ∉ ({13} : Finset ℕ) := by simp
  by_contra hcon
  push Not at hcon
  obtain ⟨k, hk⟩ := hd
  have hk44 : k < 44 := by omega
  obtain rfl : p = 7 * k - 1 := by omega
  interval_cases k <;>
    first
    | omega
    | (norm_num at hp; done)
    | (exact absurd (by decide) hsq; done)
    | (have := hl 3 (by norm_num) (by norm_num) h3z (by decide); omega)
    | (have := hl 5 (by norm_num) (by norm_num) h5z (by decide); omega)

/-- Any prime `p` with `181 ∣ p + 1` is at least `1447`. -/
theorem nx181 {p : ℕ} (hp : p.Prime) (hd : 181 ∣ p + 1) : 1447 ≤ p := by
  by_contra hcon
  push Not at hcon
  obtain ⟨k, hk⟩ := hd
  have hk8 : k < 8 := by omega
  obtain rfl : p = 181 * k - 1 := by omega
  interval_cases k <;> first | omega | (norm_num at hp)

/-- Any prime `p` with `223 ∣ p + 1` is at least `1783`. -/
theorem nx223 {p : ℕ} (hp : p.Prime) (hd : 223 ∣ p + 1) : 1783 ≤ p := by
  by_contra hcon
  push Not at hcon
  obtain ⟨k, hk⟩ := hd
  have hk8 : k < 8 := by omega
  obtain rfl : p = 223 * k - 1 := by omega
  interval_cases k <;> first | omega | (norm_num at hp)

/-- Kept parents of `31` for `z = 13`: `61`, or at least `991`. -/
theorem nx31_13 {p : ℕ} (hp : p.Prime) (hd : 31 ∣ p + 1)
    (hl : ∀ c' : ℕ, c'.Prime → c' ≠ 2 → c' ∉ ({13} : Finset ℕ) → c' ∣ p + 1 → 31 ≤ c') :
    p = 61 ∨ 991 ≤ p := by
  have h3z : (3 : ℕ) ∉ ({13} : Finset ℕ) := by simp
  have h5z : (5 : ℕ) ∉ ({13} : Finset ℕ) := by simp
  have h7z : (7 : ℕ) ∉ ({13} : Finset ℕ) := by simp
  by_contra hcon
  push Not at hcon
  obtain ⟨k, hk⟩ := hd
  have hk32 : k < 32 := by omega
  obtain rfl : p = 31 * k - 1 := by omega
  interval_cases k <;>
    first
    | omega
    | (norm_num at hp; done)
    | (have := hl 3 (by norm_num) (by norm_num) h3z (by decide); omega)
    | (have := hl 5 (by norm_num) (by norm_num) h5z (by decide); omega)
    | (have := hl 7 (by norm_num) (by norm_num) h7z (by decide); omega)

/-- Kept parents of `61` for `z = 13`: `487`, or at least `977`. -/
theorem nx61_13 {p : ℕ} (hp : p.Prime) (hd : 61 ∣ p + 1)
    (hl : ∀ c' : ℕ, c'.Prime → c' ≠ 2 → c' ∉ ({13} : Finset ℕ) → c' ∣ p + 1 → 61 ≤ c') :
    p = 487 ∨ 977 ≤ p := by
  have h7z : (7 : ℕ) ∉ ({13} : Finset ℕ) := by simp
  by_contra hcon
  push Not at hcon
  obtain ⟨k, hk⟩ := hd
  have hk17 : k < 17 := by omega
  obtain rfl : p = 61 * k - 1 := by omega
  interval_cases k <;>
    first
    | omega
    | (norm_num at hp; done)
    | (have := hl 7 (by norm_num) (by norm_num) h7z (by decide); omega)

/-- Any prime `p` with `487 ∣ p + 1` is at least `5843`. -/
theorem nx487 {p : ℕ} (hp : p.Prime) (hd : 487 ∣ p + 1) : 5843 ≤ p := by
  by_contra hcon
  push Not at hcon
  obtain ⟨k, hk⟩ := hd
  have hk12 : k < 12 := by omega
  obtain rfl : p = 487 * k - 1 := by omega
  interval_cases k <;> first | omega | (norm_num at hp)

/-- Kept parents of `103` for `z = 13` are at least `823`. -/
theorem nx103_13 {p : ℕ} (hp : p.Prime) (hd : 103 ∣ p + 1)
    (hl : ∀ c' : ℕ, c'.Prime → c' ≠ 2 → c' ∉ ({13} : Finset ℕ) → c' ∣ p + 1 → 103 ≤ c') :
    823 ≤ p := by
  have h3z : (3 : ℕ) ∉ ({13} : Finset ℕ) := by simp
  by_contra hcon
  push Not at hcon
  obtain ⟨k, hk⟩ := hd
  have hk8 : k < 8 := by omega
  obtain rfl : p = 103 * k - 1 := by omega
  interval_cases k <;>
    first
    | omega
    | (norm_num at hp; done)
    | (have := hl 3 (by norm_num) (by norm_num) h3z (by decide); omega)

/-- Kept parents of `127` for `z = 13` are at least `3301`. -/
theorem nx127_13 {p : ℕ} (hp : p.Prime) (hd : 127 ∣ p + 1)
    (hl : ∀ c' : ℕ, c'.Prime → c' ≠ 2 → c' ∉ ({13} : Finset ℕ) → c' ∣ p + 1 → 127 ≤ c') :
    3301 ≤ p := by
  have h3z : (3 : ℕ) ∉ ({13} : Finset ℕ) := by simp
  have h5z : (5 : ℕ) ∉ ({13} : Finset ℕ) := by simp
  have h7z : (7 : ℕ) ∉ ({13} : Finset ℕ) := by simp
  by_contra hcon
  push Not at hcon
  obtain ⟨k, hk⟩ := hd
  have hk26 : k < 26 := by omega
  obtain rfl : p = 127 * k - 1 := by omega
  interval_cases k <;>
    first
    | omega
    | (norm_num at hp; done)
    | (have := hl 3 (by norm_num) (by norm_num) h3z (by decide); omega)
    | (have := hl 5 (by norm_num) (by norm_num) h5z (by decide); omega)
    | (have := hl 7 (by norm_num) (by norm_num) h7z (by decide); omega)

-- ### Section 2: Uniform `b7 = 64/51` master theorem for `a` odd and `4 ∣ a`

/-- Master weight bound with custom `b3` and sharp `β 7 = 64/51` (via `7 <- 13 <- ≥103` or `7 <- ≥181`),
valid for any `z ≥ 11`. Covers `a` odd (`b3 = 4/3`), `4 ∣ a` pinned by `q ≥ 4097`, and `z = 11, a = 8 mod 16`
pinned by `q = 257`. -/
theorem b3_b7_master {m e z : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (hz : z.Prime)
    (hz11 : 11 ≤ z)
    (E : (2 ^ m + 1) * (1 + z ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * z ^ e * ∏ p ∈ P, p)
    (b3 : ℚ) (hb3lo : 4 / 3 ≤ b3) (hb3hi : b3 ≤ 2)
    (hb3 : ∀ p ∈ P, 3 ∣ p + 1 → (4 / 3 : ℚ) * (((p : ℚ) + 1) / ((p : ℚ) - 1)) ≤ b3) :
    ∃ L : Finset ℕ, L ⊆ P ∧ (∀ x ∈ L, ∀ c : ℕ, c.Prime → c ≠ 2 → c ∣ x + 1 → c = z) ∧
      (2 : ℚ) ≤ (1 + 1 / (2 : ℚ) ^ m) * (((1 + z ^ e : ℕ) : ℚ) / ((z ^ e : ℕ) : ℚ)) *
        ((b3 * (64 / 51) * (16 / 15) * (64 / 63) * (2048 / 2047)) *
          ∏ x ∈ L.filter (fun x => z ∣ x + 1), (((x : ℚ) + 1) / ((x : ℚ) - 1))) := by
  classical
  have hK : ∀ c : ℕ, c.Prime → c ∣ z ^ e → c ∈ ({z} : Finset ℕ) := fun c hc hcd =>
    Finset.mem_singleton.mpr ((Nat.prime_dvd_prime_iff_eq hc hz).mp (hc.dvd_of_dvd_pow hcd))
  obtain ⟨-, -, -, -, -, F6, -, -⟩ := facts hP hK E
  have h7z : (7 : ℕ) ∉ ({z} : Finset ℕ) := by rw [Finset.mem_singleton]; omega
  obtain ⟨β, hβ3, hβ7, hβ13, hβ⟩ : ∃ β : ℕ → ℚ, β 3 = b3 ∧ β 7 = 64 / 51 ∧
      β 13 = 14 / 13 * (104 / 102) ∧
      ∀ x : ℕ, x ≠ 3 → x ≠ 7 → x ≠ 13 → β x = ((x : ℚ) + 1) / ((x : ℚ) - 1) :=
    ⟨fun x => if x = 3 then b3 else if x = 7 then 64 / 51 else if x = 13 then 14 / 13 * (104 / 102)
      else ((x : ℚ) + 1) / ((x : ℚ) - 1), by simp, by simp, by simp,
      fun x h1 h2 h3 => by simp [h1, h2, h3]⟩
  have hBd : ∀ p ∈ P, 1 + 1 / (p : ℚ) ≤ β p ∧ β p ≤ ((p : ℚ) + 1) / ((p : ℚ) - 1) := by
    intro p hp
    by_cases e3 : p = 3
    · subst e3
      rw [hβ3]
      exact ⟨by norm_num; exact hb3lo, by norm_num; exact hb3hi⟩
    by_cases e7 : p = 7
    · subst e7
      rw [hβ7]
      norm_num
    by_cases e13 : p = 13
    · subst e13
      rw [hβ13]
      norm_num
    rw [hβ p e3 e7 e13]
    exact ⟨one_add_le_B (hP p hp).1.two_le, le_refl _⟩
  have hsp : ∀ c : ℕ, β c ≠ ((c : ℚ) + 1) / ((c : ℚ) - 1) → c = 3 ∨ c = 7 ∨ c = 13 := by
    intro c hc
    by_contra hcon
    push Not at hcon
    exact hc (hβ c hcon.1 hcon.2.1 hcon.2.2)
  have h4 : ∀ p ∈ P, ∀ c ∈ P, c ∣ p + 1 →
      (∀ c' : ℕ, c'.Prime → c' ≠ 2 → c' ∉ ({z} : Finset ℕ) → c' ∣ p + 1 → c ≤ c') →
      β c ≠ ((c : ℚ) + 1) / ((c : ℚ) - 1) → (1 + 1 / (c : ℚ)) * β p ≤ β c := by
    intro p hp c hc hd hl _
    have hpp := (hP p hp).1
    have hwp := (hBd p hp).2
    rcases hsp c ‹_› with rfl | rfl | rfl
    · rw [hβ3]
      have hmul : (1 + 1 / ((3 : ℕ) : ℚ)) * β p ≤ (4 / 3 : ℚ) * (((p : ℚ) + 1) / ((p : ℚ) - 1)) := by
        rw [show (1 + 1 / ((3 : ℕ) : ℚ)) = 4 / 3 by norm_num]
        exact mul_le_mul_of_nonneg_left hwp (by norm_num)
      exact hmul.trans (hb3 p hp hd)
    · rw [hβ7]
      rcases nx7_small hz11 hpp hd (F6 7 (by norm_num) (by norm_num) h7z p hp) hl with rfl | hfar
      · rw [hβ13]
        norm_num
      · exact far_step (c := 7) (N := 181) (by norm_num) hfar hwp (by norm_num)
    · rw [hβ13]
      exact far_step (c := 13) (N := 103) (by norm_num) (nx13_103 hpp hd) hwp (by norm_num)
  obtain ⟨L, hLP, hLleaf, hmain⟩ := master_gen hP hK (by positivity) E β hBd h4
  have hleaf : ∀ x ∈ L, ∀ c : ℕ, c.Prime → c ≠ 2 → c ∣ x + 1 → c = z := fun x hx c hc h2 hd =>
    Finset.mem_singleton.mp (hLleaf x hx c hc h2 hd)
  refine ⟨L, hLP, hleaf, ?_⟩
  have hpos : ∀ x ∈ L, 0 < β x := fun x hx =>
    lt_of_lt_of_le (by positivity) (hBd x (hLP hx)).1
  have hBq : ∀ x ∈ L, β x ≤ ((x : ℚ) + 1) / ((x : ℚ) - 1) := fun x hx => (hBd x (hLP hx)).2
  have hd31 := hβ 31 (by norm_num) (by norm_num) (by norm_num)
  have e31 : (((31 : ℕ) : ℚ) + 1) / (((31 : ℕ) : ℚ) - 1) = 16 / 15 := by norm_num
  rw [e31] at hd31
  have hd127 := hβ 127 (by norm_num) (by norm_num) (by norm_num)
  have e127 : (((127 : ℕ) : ℚ) + 1) / (((127 : ℕ) : ℚ) - 1) = 64 / 63 := by norm_num
  rw [e127] at hd127
  have hM : ∏ x ∈ L.filter (fun x => ¬ z ∣ x + 1), β x ≤
      (β 3 * β 7 * β 31 * β 127) * (2048 / 2047) := by
    apply mersenne_bound
    · intro x hx
      exact (hP x (hLP (Finset.mem_filter.mp hx).1)).1
    · intro x hx
      obtain ⟨hxL, hxz⟩ := Finset.mem_filter.mp hx
      exact two_pow_of_no_odd_prime (fun c hc h2 hd => hxz (hleaf x hxL c hc h2 hd ▸ hd))
    · intro x hx
      have hxL := (Finset.mem_filter.mp hx).1
      exact ⟨hpos x hxL, hBq x hxL⟩
    · rw [hβ3, hβ7, hd31, hd127]
      exact ⟨by linarith, by norm_num, by norm_num, by norm_num⟩
  rw [hβ3, hβ7, hd31, hd127] at hM
  have hZ : ∏ x ∈ L.filter (fun x => z ∣ x + 1), β x ≤
      ∏ x ∈ L.filter (fun x => z ∣ x + 1), (((x : ℚ) + 1) / ((x : ℚ) - 1)) :=
    Finset.prod_le_prod (fun x hx => (hpos x (Finset.mem_filter.mp hx).1).le)
      (fun x hx => hBq x (Finset.mem_filter.mp hx).1)
  have hX : ∏ x ∈ L, β x ≤ (b3 * (64 / 51) * (16 / 15) * (64 / 63) * (2048 / 2047)) *
      ∏ x ∈ L.filter (fun x => z ∣ x + 1), (((x : ℚ) + 1) / ((x : ℚ) - 1)) := by
    rw [← Finset.prod_filter_mul_prod_filter_not L (fun x => z ∣ x + 1) β, mul_comm]
    exact mul_le_mul hM hZ (Finset.prod_nonneg fun x hx => (hpos x (Finset.mem_filter.mp hx).1).le)
      (by
        have : (0 : ℚ) ≤ b3 := by linarith
        positivity)
  exact hmain.trans (mul_le_mul_of_nonneg_left hX (by positivity))

/-- Leaf bound helper for `z ∈ {11, 13, 17, 19}`: closes `a` odd (`a ≥ 9`) and `4 ∣ a` (`k ≥ 11`, `q ≥ 4097`). -/
theorem b3_b7_close {m e z a0 : ℕ} {P : Finset ℕ} {b3 Zb : ℚ}
    (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (hz : z.Prime) (hz11 : 11 ≤ z)
    (E : (2 ^ m + 1) * (1 + z ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * z ^ e * ∏ p ∈ P, p)
    (hm : a0 ≤ m) (he4 : 4 ≤ e)
    (hb3lo : 4 / 3 ≤ b3) (hb3hi : b3 ≤ 2)
    (hb3 : ∀ p ∈ P, 3 ∣ p + 1 → (4 / 3 : ℚ) * (((p : ℚ) + 1) / ((p : ℚ) - 1)) ≤ b3)
    (hZ : ∀ L : Finset ℕ, (∀ x ∈ L, x.Prime ∧ x ≠ 2) →
      (∀ x ∈ L, ∀ c : ℕ, c.Prime → c ≠ 2 → c ∣ x + 1 → c = z) →
      ∏ x ∈ L.filter (fun x => z ∣ x + 1), (((x : ℚ) + 1) / ((x : ℚ) - 1)) ≤ Zb)
    (hnum : (1 + 1 / (2 : ℚ) ^ a0) * (((1 + z ^ 4 : ℕ) : ℚ) / ((z ^ 4 : ℕ) : ℚ)) *
      ((b3 * (64 / 51) * (16 / 15) * (64 / 63) * (2048 / 2047)) * Zb) < 2) : False := by
  obtain ⟨L, hLP, hleaf, hmain⟩ := b3_b7_master hP hz hz11 E b3 hb3lo hb3hi hb3
  exact table_close hm hmain (by positivity) (kk_le (by omega) (le_refl z) he4)
    (by have : (0 : ℚ) ≤ b3 := (by linarith); positivity)
    (Finset.prod_nonneg fun x hx =>
      B_nonneg (hP x (hLP (Finset.mem_filter.mp hx).1)).1.one_lt.le)
    (hZ L (fun x hx => hP x (hLP hx)) hleaf) hnum

/-- Uniform leaf bound for `z = 11`: `zleaves_one (s := 5) (q0 := 43)`. -/
theorem zleaves_11 {L : Finset ℕ} (hLp : ∀ x ∈ L, x.Prime ∧ x ≠ 2)
    (hleaf : ∀ x ∈ L, ∀ c : ℕ, c.Prime → c ≠ 2 → c ∣ x + 1 → c = 11) :
    ∏ x ∈ L.filter (fun x => 11 ∣ x + 1), (((x : ℚ) + 1) / ((x : ℚ) - 1)) ≤
      ((11 : ℚ) ^ 2 / ((11 : ℚ) ^ 2 - 3)) *
        ((((43 : ℚ) + 1) / ((43 : ℚ) - 1)) *
          (((2 ^ 5 * 11 : ℕ) : ℚ) / (((2 ^ 5 * 11 : ℕ) : ℚ) - 2))) :=
  zleaves_one (z := 11) (s := 5) (q0 := 43) (by norm_num) (by norm_num) (by norm_num)
    (fun k h1 h2 hp => by
      by_cases hk : k = 2
      · subst hk; norm_num
      · exfalso; interval_cases k <;> first | omega | (norm_num at hp)) hLp hleaf

/-- Uniform leaf bound for `z = 13`: `zleaves_skip (s := 2)`. -/
theorem zleaves_13 {L : Finset ℕ} (hLp : ∀ x ∈ L, x.Prime ∧ x ≠ 2)
    (hleaf : ∀ x ∈ L, ∀ c : ℕ, c.Prime → c ≠ 2 → c ∣ x + 1 → c = 13) :
    ∏ x ∈ L.filter (fun x => 13 ∣ x + 1), (((x : ℚ) + 1) / ((x : ℚ) - 1)) ≤
      ((13 : ℚ) ^ 2 / ((13 : ℚ) ^ 2 - 3)) *
        (((2 ^ 2 * 13 : ℕ) : ℚ) / (((2 ^ 2 * 13 : ℕ) : ℚ) - 2)) :=
  zleaves_skip (z := 13) (s := 2) (by norm_num) (by norm_num)
    (fun k h1 h2 => by interval_cases k <;> norm_num) hLp hleaf

/-- Uniform leaf bound for `z = 17`: `zleaves_skip (s := 1)`. -/
theorem zleaves_17 {L : Finset ℕ} (hLp : ∀ x ∈ L, x.Prime ∧ x ≠ 2)
    (hleaf : ∀ x ∈ L, ∀ c : ℕ, c.Prime → c ≠ 2 → c ∣ x + 1 → c = 17) :
    ∏ x ∈ L.filter (fun x => 17 ∣ x + 1), (((x : ℚ) + 1) / ((x : ℚ) - 1)) ≤
      ((17 : ℚ) ^ 2 / ((17 : ℚ) ^ 2 - 3)) *
        (((2 ^ 1 * 17 : ℕ) : ℚ) / (((2 ^ 1 * 17 : ℕ) : ℚ) - 2)) :=
  zleaves_skip (z := 17) (s := 1) (by norm_num) (by norm_num)
    (fun k h1 h2 => by obtain rfl : k = 1 := (by omega); norm_num) hLp hleaf

/-- Uniform leaf bound for `z = 19`: `zleaves_one (s := 2) (q0 := 37)`. -/
theorem zleaves_19 {L : Finset ℕ} (hLp : ∀ x ∈ L, x.Prime ∧ x ≠ 2)
    (hleaf : ∀ x ∈ L, ∀ c : ℕ, c.Prime → c ≠ 2 → c ∣ x + 1 → c = 19) :
    ∏ x ∈ L.filter (fun x => 19 ∣ x + 1), (((x : ℚ) + 1) / ((x : ℚ) - 1)) ≤
      ((19 : ℚ) ^ 2 / ((19 : ℚ) ^ 2 - 3)) *
        ((((37 : ℚ) + 1) / ((37 : ℚ) - 1)) *
          (((2 ^ 2 * 19 : ℕ) : ℚ) / (((2 ^ 2 * 19 : ℕ) : ℚ) - 2))) :=
  zleaves_one (z := 19) (s := 2) (q0 := 37) (by norm_num) (by norm_num) (by norm_num)
    (fun k h1 h2 hp => by
      by_cases hk : k = 1
      · subst hk; norm_num
      · exfalso; interval_cases k <;> first | omega | (norm_num at hp)) hLp hleaf

/-- Generic `a` odd or `4 ∣ a` (`k ≥ 11`) dead-end for a prime `z ∈ {11, 13, 17, 19}` with `4 ≤ e`. -/
theorem small4_core {n z : ℕ} (h : Erdos1052.IsUnitaryPerfect n) (hz : z.Prime)
    (hz11 : 11 ≤ z) (hz4097 : z < 4097)
    (hS : ∀ p, p.Prime ∧ p ≠ 2 ∧ p ^ 2 ∣ n ↔ p = z) (he4 : 4 ≤ n.factorization z)
    (hna : padicValNat 2 n % 4 ≠ 2)
    (h8 : padicValNat 2 n % 8 ≠ 4) (h16 : padicValNat 2 n % 16 ≠ 8)
    (h32 : padicValNat 2 n % 32 ≠ 16) (h64 : padicValNat 2 n % 64 ≠ 32)
    (h128 : padicValNat 2 n % 128 ≠ 64) (h256 : padicValNat 2 n % 256 ≠ 128)
    (h512 : padicValNat 2 n % 512 ≠ 256) (h1024 : padicValNat 2 n % 1024 ≠ 512)
    (h2048 : padicValNat 2 n % 2048 ≠ 1024) (Zb : ℚ)
    (hZ : ∀ L : Finset ℕ, (∀ x ∈ L, x.Prime ∧ x ≠ 2) →
      (∀ x ∈ L, ∀ c : ℕ, c.Prime → c ≠ 2 → c ∣ x + 1 → c = z) →
      ∏ x ∈ L.filter (fun x => z ∣ x + 1), (((x : ℚ) + 1) / ((x : ℚ) - 1)) ≤ Zb)
    (hodd : (1 + 1 / (2 : ℚ) ^ 9) * (((1 + z ^ 4 : ℕ) : ℚ) / ((z ^ 4 : ℕ) : ℚ)) *
      (((4 / 3) * (64 / 51) * (16 / 15) * (64 / 63) * (2048 / 2047)) * Zb) < 2)
    (hpin : (1 + 1 / (2 : ℚ) ^ 11) * (((1 + z ^ 4 : ℕ) : ℚ) / ((z ^ 4 : ℕ) : ℚ)) *
      (((4 / 3 * (4098 / 4096)) * (64 / 51) * (16 / 15) * (64 / 63) * (2048 / 2047)) * Zb) < 2) :
    padicValNat 2 n ≤ 7 := by
  classical
  by_contra hgt
  obtain ⟨hzn, hs⟩ := simple_of_unique_repeated h.2.ne' hS
  have hz2 : z ≠ 2 := ((hS z).mpr rfl).2.1
  have hzpf : z ∈ n.primeFactors := Nat.mem_primeFactors.mpr ⟨hz, hzn, h.2.ne'⟩
  obtain ⟨hP, E⟩ := kernel_balance_one h hzpf hz2 hs
  rw [Nat.factorization_def n Nat.prime_two] at E
  have hK : ∀ c : ℕ, c.Prime → c ∣ z ^ n.factorization z → c ∈ ({z} : Finset ℕ) :=
    fun c hc hcd =>
      Finset.mem_singleton.mpr ((Nat.prime_dvd_prime_iff_eq hc hz).mp (hc.dvd_of_dvd_pow hcd))
  obtain ⟨-, F2, F3, F4, -, -, -, -⟩ := facts hP hK E
  have h3z : (3 : ℕ) ∉ ({z} : Finset ℕ) := by rw [Finset.mem_singleton]; omega
  by_cases c : padicValNat 2 n % 2 = 1
  · have hno3 := F4 3 Nat.prime_three (by norm_num) h3z (three_dvd_two_pow_add_one c)
    exact b3_b7_close hP hz hz11 E (odd_ge_nine hgt c) he4 (le_refl _) (by norm_num)
      (fun p hp hd => absurd hd (hno3 p hp)) hZ hodd
  · have h4 : padicValNat 2 n % 4 = 0 := four_dvd_of_not c hna
    have hm0 : padicValNat 2 n ≠ 0 := fun h0 => hgt (by rw [h0]; norm_num)
    have hme : Even (padicValNat 2 n) := Nat.even_iff.mpr
      ((Nat.mod_two_eq_zero_or_one (padicValNat 2 n)).resolve_right c)
    obtain ⟨c', k, t, hc, hc2, hc3, hcm, hk, hcF, ht, hmt⟩ := exists_fermat_prime hm0 hme
    have hk11 : 11 ≤ k := v2_large ht hmt h4 h8 h16 h32 h64 h128 h256 h512 h1024 h2048
    have hc4097 : 4097 ≤ c' := ge_4097 hc hk11 (two_pow_succ_dvd_pred hc hcF)
    have hcz : c' ∉ ({z} : Finset ℕ) := by
      rw [Finset.mem_singleton]
      intro hcz'
      exact absurd (hcz' ▸ hc4097) (Nat.not_le.mpr hz4097)
    have hcP := F2 c' hc hc2 hcz hcm
    have h3c : 3 ∣ c' + 1 := Nat.dvd_of_mod_eq_zero (by rw [Nat.add_mod, hc3])
    exact b3_b7_close hP hz hz11 E (ge_eleven hk11 ht hmt) he4 (by norm_num) (by norm_num)
      (fun p hp hd => by
        have hpc : p = c' := F3 3 Nat.prime_three (by norm_num) h3z p hp c' hcP hd h3c
        rw [hpc]
        have hB := B_anti (a := 4097) (b := c') (by norm_num) hc4097
        rw [show (((4097 : ℕ) : ℚ) + 1) / (((4097 : ℕ) : ℚ) - 1) = 4098 / 4096 by norm_num] at hB
        exact mul_le_mul_of_nonneg_left hB (by norm_num)) hZ hpin

/-- `z = 11` and `a = 8 (mod 16)` with `4 ≤ e`: no solution (`F_3 = 257` pins `3`). -/
theorem z11_a16_dead {n : ℕ} (h : Erdos1052.IsUnitaryPerfect n)
    (hS : ∀ p, p.Prime ∧ p ≠ 2 ∧ p ^ 2 ∣ n ↔ p = 11) (he4 : 4 ≤ n.factorization 11)
    (h16 : padicValNat 2 n % 16 = 8) : False := by
  classical
  have hz : Nat.Prime 11 := by norm_num
  obtain ⟨hzn, hs⟩ := simple_of_unique_repeated h.2.ne' hS
  have hzpf : 11 ∈ n.primeFactors := Nat.mem_primeFactors.mpr ⟨hz, hzn, h.2.ne'⟩
  obtain ⟨hP, E⟩ := kernel_balance_one h hzpf (by norm_num) hs
  rw [Nat.factorization_def n Nat.prime_two] at E
  have hm0 : padicValNat 2 n ≠ 0 := by omega
  have hme : Even (padicValNat 2 n) := Nat.even_iff.mpr (by omega)
  obtain ⟨c, k, t, hc, hc2, hc3, hcm, hk, hcF, ht, hmt⟩ := exists_fermat_prime hm0 hme
  have hk3 : k = 3 := v2_eq_three ht hmt h16
  subst hk3
  have hc257 : c = 257 := (Nat.prime_dvd_prime_iff_eq hc (by norm_num)).mp (by simpa using hcF)
  subst hc257
  have hK : ∀ c : ℕ, c.Prime → c ∣ 11 ^ n.factorization 11 → c ∈ ({11} : Finset ℕ) :=
    fun c hc hcd =>
      Finset.mem_singleton.mpr ((Nat.prime_dvd_prime_iff_eq hc hz).mp (hc.dvd_of_dvd_pow hcd))
  obtain ⟨-, F2, F3, -, -, -, -, -⟩ := facts hP hK E
  have hcP := F2 257 hc (by norm_num) (by simp) hcm
  have hm8 : 8 ≤ padicValNat 2 n := by omega
  exact b3_b7_close (b3 := 4 / 3 * (258 / 256)) hP hz (by norm_num) E hm8 he4 (by norm_num) (by norm_num)
    (fun p hp hd => by
      have hp257 : p = 257 := F3 3 Nat.prime_three (by norm_num) (by simp) p hp 257 hcP hd (by norm_num)
      rw [hp257]
      norm_num)
    (fun L hLp hleaf => zleaves_11 hLp hleaf) (by norm_num)

-- ### Section 3: Complete settlement of `z = 13, a = 2 (mod 4)`

/-- Core prime `13`: leaves `x ≠ 103` with `x + 1 = 2 ^ k * 13 ^ j`, `j ≥ 1`, weigh at most
`(2197/2194) * (((338/336) * (2704/2702)) * (832/830))`. -/
theorem thirteen_leaves_no103 {L : Finset ℕ} (hLp : ∀ x ∈ L, x.Prime ∧ x ≠ 2)
    (hleaf : ∀ x ∈ L, ∀ c : ℕ, c.Prime → c ≠ 2 → c ∣ x + 1 → c = 13) :
    ∏ x ∈ (L.filter (fun x => 13 ∣ x + 1)).filter (fun x => ¬ x = 103),
      (((x : ℚ) + 1) / ((x : ℚ) - 1)) ≤
      (2197 / 2194) * (((338 / 336) * (2704 / 2702)) * (832 / 830)) := by
  classical
  have h13pow : ∀ k : ℕ, ¬ 13 ∣ 2 ^ k := fun k h => by
    have := (Nat.prime_dvd_prime_iff_eq (by norm_num : Nat.Prime 13) Nat.prime_two).mp
      ((by norm_num : Nat.Prime 13).dvd_of_dvd_pow h)
    omega
  have hmem : ∀ x ∈ (L.filter (fun x => 13 ∣ x + 1)).filter (fun x => ¬ x = 103),
      x ∈ L ∧ 13 ∣ x + 1 ∧ ¬ x = 103 := fun x hx =>
    ⟨(Finset.mem_filter.mp (Finset.mem_filter.mp hx).1).1,
      (Finset.mem_filter.mp (Finset.mem_filter.mp hx).1).2, (Finset.mem_filter.mp hx).2⟩
  have hform : ∀ x ∈ (L.filter (fun x => 13 ∣ x + 1)).filter (fun x => ¬ x = 103),
      ∃ k j, 1 ≤ k ∧ 1 ≤ j ∧ x + 1 = 2 ^ k * 13 ^ j := by
    intro x hx
    obtain ⟨hxL, hx13, -⟩ := hmem x hx
    obtain ⟨k, j, hkj⟩ := two_pow_mul_pow_of_odd_primes_eq (M := x + 1) (z := 13) (by omega)
      (hleaf x hxL)
    refine ⟨k, j, ?_, ?_, hkj⟩
    · by_contra hk
      have hk0 : k = 0 := by omega
      subst hk0
      have hodd : Odd x := (hLp x hxL).1.odd_of_ne_two (hLp x hxL).2
      have h13 : Odd (13 ^ j) := Odd.pow (by decide)
      rw [pow_zero, one_mul] at hkj
      rw [← hkj] at h13
      rcases hodd with ⟨u, hu⟩
      rcases h13 with ⟨v, hv⟩
      omega
    · by_contra hj
      have hj0 : j = 0 := by omega
      subst hj0
      rw [pow_zero, mul_one] at hkj
      rw [hkj] at hx13
      exact h13pow k hx13
  have hB0 : ∀ x ∈ (L.filter (fun x => 13 ∣ x + 1)).filter (fun x => ¬ x = 103),
      (0 : ℚ) ≤ ((x : ℚ) + 1) / ((x : ℚ) - 1) := fun x hx =>
    B_nonneg (hLp x (hmem x hx).1).1.one_lt.le
  -- j ≥ 3
  have hA : ∏ x ∈ ((L.filter (fun x => 13 ∣ x + 1)).filter (fun x => ¬ x = 103)).filter
      (fun x => 2197 ∣ x + 1), (((x : ℚ) + 1) / ((x : ℚ) - 1)) ≤ 2197 / 2194 := by
    have h := zleaf_bound (z := 13) (by norm_num) 3 (by norm_num)
      (((L.filter (fun x => 13 ∣ x + 1)).filter (fun x => ¬ x = 103)).filter
        (fun x => 2197 ∣ x + 1)) (fun x hx => by
        obtain ⟨hx1, h2197⟩ := Finset.mem_filter.mp hx
        obtain ⟨k, j, hk, hj, hkj⟩ := hform x hx1
        refine ⟨k, j, hk, ?_, hkj⟩
        by_contra hj3
        have hj' : j = 1 ∨ j = 2 := by omega
        rcases hj' with rfl | rfl
        · rw [hkj, pow_one, show (2197 : ℕ) = 169 * 13 by norm_num] at h2197
          exact h13pow k ((by norm_num : (13 : ℕ) ∣ 169).trans
            (Nat.dvd_of_mul_dvd_mul_right (by norm_num) h2197))
        · rw [hkj, show (2197 : ℕ) = 13 * 13 ^ 2 by norm_num] at h2197
          exact h13pow k (Nat.dvd_of_mul_dvd_mul_right (by norm_num) h2197))
    norm_num at h ⊢
    exact h
  -- j = 2
  have hB2 : ∏ x ∈ (((L.filter (fun x => 13 ∣ x + 1)).filter (fun x => ¬ x = 103)).filter
      (fun x => ¬ 2197 ∣ x + 1)).filter (fun x => 169 ∣ x + 1),
      (((x : ℚ) + 1) / ((x : ℚ) - 1)) ≤ (338 / 336) * (2704 / 2702) := by
    have h := fiber_split (u0 := 169) (k0 := 4) (q0 := 337) (by norm_num) (by norm_num)
      ((((L.filter (fun x => 13 ∣ x + 1)).filter (fun x => ¬ x = 103)).filter
        (fun x => ¬ 2197 ∣ x + 1)).filter (fun x => 169 ∣ x + 1)) (fun x hx => by
        obtain ⟨hx2, h169⟩ := Finset.mem_filter.mp hx
        obtain ⟨hx1, h2197⟩ := Finset.mem_filter.mp hx2
        obtain ⟨k, j, hk, hj, hkj⟩ := hform x hx1
        refine ⟨k, hk, ?_⟩
        have hj2 : j = 2 := by
          by_contra hne
          have hj' : j = 1 ∨ 3 ≤ j := by omega
          rcases hj' with rfl | hj3
          · rw [hkj, pow_one, show (169 : ℕ) = 13 * 13 by norm_num] at h169
            exact h13pow k (Nat.dvd_of_mul_dvd_mul_right (by norm_num) h169)
          · apply h2197
            rw [hkj, show (2197 : ℕ) = 13 ^ 3 by norm_num]
            exact Dvd.dvd.mul_left (pow_dvd_pow 13 hj3) _
        rw [hkj, hj2]
        norm_num) (fun x hx k hk hk4 hkx => by
        have hxp := (hLp x (hmem x (Finset.mem_filter.mp (Finset.mem_filter.mp hx).1).1).1).1
        interval_cases k <;> norm_num at hkx <;>
          first
          | omega
          | (have hx' : x = 675 := by omega
             subst hx'; exact absurd hxp (by norm_num))
          | (have hx' : x = 1351 := by omega
             subst hx'; exact absurd hxp (by norm_num))
          | (have hx' : x = 2703 := by omega
             subst hx'; exact absurd hxp (by norm_num)))
    norm_num at h ⊢
    exact h
  -- j = 1 (x ≠ 103, k = 1, 2, 4, 5, 6 all composite, so k ≥ 7, u = 2^6 * 13 = 832)
  have hB1 : ∏ x ∈ (((L.filter (fun x => 13 ∣ x + 1)).filter (fun x => ¬ x = 103)).filter
      (fun x => ¬ 2197 ∣ x + 1)).filter (fun x => ¬ 169 ∣ x + 1),
      (((x : ℚ) + 1) / ((x : ℚ) - 1)) ≤ 832 / 830 := by
    have h := fiber_bound (u := 832) (by norm_num)
      ((((L.filter (fun x => 13 ∣ x + 1)).filter (fun x => ¬ x = 103)).filter
        (fun x => ¬ 2197 ∣ x + 1)).filter (fun x => ¬ 169 ∣ x + 1)) (fun x hx => by
        obtain ⟨hx2, h169⟩ := Finset.mem_filter.mp hx
        obtain ⟨hx1, -⟩ := Finset.mem_filter.mp hx2
        obtain ⟨k, j, hk, hj, hkj⟩ := hform x hx1
        have hj1 : j = 1 := by
          by_contra hne
          apply h169
          rw [hkj, show (169 : ℕ) = 13 ^ 2 by norm_num]
          exact Dvd.dvd.mul_left (pow_dvd_pow 13 (by omega)) _
        rw [hj1, pow_one] at hkj
        have hxp := (hLp x (hmem x hx1).1).1
        have hx103 := (hmem x hx1).2.2
        have hk7 : 7 ≤ k := by
          by_contra hklt
          have hk' : k < 7 := by omega
          interval_cases k <;> norm_num at hkj <;>
            first
            | omega
            | (have hx' : x = 25 := by omega
               subst hx'; exact absurd hxp (by norm_num))
            | (have hx' : x = 51 := by omega
               subst hx'; exact absurd hxp (by norm_num))
            | (have hx' : x = 207 := by omega
               subst hx'; exact absurd hxp (by norm_num))
            | (have hx' : x = 415 := by omega
               subst hx'; exact absurd hxp (by norm_num))
            | (have hx' : x = 831 := by omega
               subst hx'; exact absurd hxp (by norm_num))
        refine ⟨k - 6, by omega, ?_⟩
        rw [hkj, show (832 : ℕ) = 2 ^ 6 * 13 by norm_num, ← mul_assoc, ← pow_add]
        congr 2
        omega)
    norm_num at h ⊢
    exact h
  rw [← Finset.prod_filter_mul_prod_filter_not
    ((L.filter (fun x => 13 ∣ x + 1)).filter (fun x => ¬ x = 103)) (fun x => 2197 ∣ x + 1)]
  refine mul_le_mul hA ?_ (Finset.prod_nonneg fun x hx => hB0 x (Finset.mem_filter.mp hx).1)
    (by norm_num)
  rw [← Finset.prod_filter_mul_prod_filter_not
    (((L.filter (fun x => 13 ∣ x + 1)).filter (fun x => ¬ x = 103)).filter
      (fun x => ¬ 2197 ∣ x + 1)) (fun x => 169 ∣ x + 1)]
  exact mul_le_mul hB2 hB1 (Finset.prod_nonneg fun x hx =>
    hB0 x (Finset.mem_filter.mp (Finset.mem_filter.mp hx).1).1) (by norm_num)

/-- Zero-branching weight bound for `z = 13` and `a = 2 (mod 4)`. -/
theorem thirteen_amod4_master {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 13 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 13 ^ e * ∏ p ∈ P, p)
    (hzP : 13 ∉ P) (h5P : 5 ∈ P) (h5c : ∀ p ∈ P, ¬ 5 ∣ p + 1) :
    ∃ L : Finset ℕ, L ⊆ P ∧ (∀ x ∈ L, ∀ c : ℕ, c.Prime → c ≠ 2 → c ∣ x + 1 → c = 13) ∧
      (2 : ℚ) ≤ (1 + 1 / (2 : ℚ) ^ m) * (((1 + 13 ^ e : ℕ) : ℚ) / ((13 ^ e : ℕ) : ℚ)) *
        ((8 / 5 * (8 / 7 * (182 / 181 * (1448 / 1446))) *
            (32 / 31 * (62 / 61 * (488 / 487 * (5844 / 5842)))) *
            (128 / 127 * (3302 / 3300)) * (2048 / 2047)) *
          ((104 / 103 * (824 / 822)) *
            ∏ x ∈ (L.filter (fun x => 13 ∣ x + 1)).filter (fun x => ¬ x = 103),
              (((x : ℚ) + 1) / ((x : ℚ) - 1)))) := by
  classical
  have hz : Nat.Prime 13 := by norm_num
  have hK : ∀ c : ℕ, c.Prime → c ∣ 13 ^ e → c ∈ ({13} : Finset ℕ) := fun c hc hcd =>
    Finset.mem_singleton.mpr ((Nat.prime_dvd_prime_iff_eq hc hz).mp (hc.dvd_of_dvd_pow hcd))
  obtain ⟨-, -, F3, -, -, F6, -, -⟩ := facts hP hK E
  let b181 : ℚ := 182 / 181 * (1448 / 1446)
  let b223 : ℚ := 224 / 223 * (1784 / 1782)
  let b7 : ℚ := 8 / 7 * b181
  let b487 : ℚ := 488 / 487 * (5844 / 5842)
  let b61 : ℚ := 62 / 61 * b487
  let b31 : ℚ := 32 / 31 * b61
  let b103 : ℚ := 104 / 103 * (824 / 822)
  let b127 : ℚ := 128 / 127 * (3302 / 3300)
  let β : ℕ → ℚ := fun x =>
    if x = 3 then 8 / 5
    else if x = 5 then 6 / 5
    else if x = 7 then b7
    else if x = 181 then b181
    else if x = 223 then b223
    else if x = 31 then b31
    else if x = 61 then b61
    else if x = 487 then b487
    else if x = 103 then b103
    else if x = 127 then b127
    else ((x : ℚ) + 1) / ((x : ℚ) - 1)
  have hβ3 : β 3 = 8 / 5 := by simp [β]
  have hβ5 : β 5 = 6 / 5 := by simp [β]
  have hβ7 : β 7 = b7 := by simp [β]
  have hβ181 : β 181 = b181 := by simp [β]
  have hβ223 : β 223 = b223 := by simp [β]
  have hβ31 : β 31 = b31 := by simp [β]
  have hβ61 : β 61 = b61 := by simp [β]
  have hβ487 : β 487 = b487 := by simp [β]
  have hβ103 : β 103 = b103 := by simp [β]
  have hβ127 : β 127 = b127 := by simp [β]
  have hBd : ∀ p ∈ P, 1 + 1 / (p : ℚ) ≤ β p ∧ β p ≤ ((p : ℚ) + 1) / ((p : ℚ) - 1) := by
    intro p hp
    by_cases e3 : p = 3; · subst e3; simp only [hβ3]; norm_num
    by_cases e5 : p = 5; · subst e5; simp only [hβ5]; norm_num
    by_cases e7 : p = 7; · subst e7; simp only [hβ7, b7, b181]; norm_num
    by_cases e181 : p = 181; · subst e181; simp only [hβ181, b181]; norm_num
    by_cases e223 : p = 223; · subst e223; simp only [hβ223, b223]; norm_num
    by_cases e31 : p = 31; · subst e31; simp only [hβ31, b31, b61, b487]; norm_num
    by_cases e61 : p = 61; · subst e61; simp only [hβ61, b61, b487]; norm_num
    by_cases e487 : p = 487; · subst e487; simp only [hβ487, b487]; norm_num
    by_cases e103 : p = 103; · subst e103; simp only [hβ103, b103]; norm_num
    by_cases e127 : p = 127; · subst e127; simp only [hβ127, b127]; norm_num
    have hdef : β p = ((p : ℚ) + 1) / ((p : ℚ) - 1) := by
      simp [β, e3, e5, e7, e181, e223, e31, e61, e487, e103, e127]
    rw [hdef]
    exact ⟨one_add_le_B (hP p hp).1.two_le, le_refl _⟩
  have h4 : ∀ p ∈ P, ∀ c ∈ P, c ∣ p + 1 →
      (∀ c' : ℕ, c'.Prime → c' ≠ 2 → c' ∉ ({13} : Finset ℕ) → c' ∣ p + 1 → c ≤ c') →
      β c ≠ ((c : ℚ) + 1) / ((c : ℚ) - 1) → (1 + 1 / (c : ℚ)) * β p ≤ β c := by
    intro p hp c hc hd hl hne
    have hpp := (hP p hp).1
    have hwp := (hBd p hp).2
    have hsp : c = 3 ∨ c = 5 ∨ c = 7 ∨ c = 181 ∨ c = 223 ∨ c = 31 ∨ c = 61 ∨ c = 487 ∨ c = 103 ∨ c = 127 := by
      by_contra hcon
      push Not at hcon
      apply hne
      simp [β, hcon]
    rcases hsp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · have hp5 : p = 5 := F3 3 Nat.prime_three (by norm_num) (by simp) p hp 5 h5P hd (by norm_num)
      rw [hp5, hβ5, hβ3]
      norm_num
    · exact absurd hd (h5c p hp)
    · have hp13 : p ≠ 13 := fun h13 => hzP (h13 ▸ hp)
      rw [hβ7]
      rcases nx7_13 hpp hp13 hd (F6 7 (by norm_num) (by norm_num) (by simp) p hp) hl with rfl | rfl | hfar
      · simp only [hβ181, b7, b181]; norm_num
      · simp only [hβ223, b7, b181, b223]; norm_num
      · exact far_step (c := 7) (N := 307) (by norm_num) hfar hwp (by simp only [b7, b181]; norm_num)
    · rw [hβ181]
      exact far_step (c := 181) (N := 1447) (by norm_num) (nx181 hpp hd) hwp
        (by simp only [b181]; norm_num)
    · rw [hβ223]
      exact far_step (c := 223) (N := 1783) (by norm_num) (nx223 hpp hd) hwp
        (by simp only [b223]; norm_num)
    · rw [hβ31]
      rcases nx31_13 hpp hd hl with rfl | hfar
      · simp only [hβ61, b31, b61, b487]; norm_num
      · exact far_step (c := 31) (N := 991) (by norm_num) hfar hwp
          (by simp only [b31, b61, b487]; norm_num)
    · rw [hβ61]
      rcases nx61_13 hpp hd hl with rfl | hfar
      · simp only [hβ487, b61, b487]; norm_num
      · exact far_step (c := 61) (N := 977) (by norm_num) hfar hwp
          (by simp only [b61, b487]; norm_num)
    · rw [hβ487]
      exact far_step (c := 487) (N := 5843) (by norm_num) (nx487 hpp hd) hwp
        (by simp only [b487]; norm_num)
    · rw [hβ103]
      exact far_step (c := 103) (N := 823) (by norm_num) (nx103_13 hpp hd hl) hwp
        (by simp only [b103]; norm_num)
    · rw [hβ127]
      exact far_step (c := 127) (N := 3301) (by norm_num) (nx127_13 hpp hd hl) hwp
        (by simp only [b127]; norm_num)
  obtain ⟨L, hLP, hLleaf, hmain⟩ := master_gen hP hK (by positivity) E β hBd h4
  have hleaf : ∀ x ∈ L, ∀ c : ℕ, c.Prime → c ≠ 2 → c ∣ x + 1 → c = 13 := fun x hx c hc h2 hd =>
    Finset.mem_singleton.mp (hLleaf x hx c hc h2 hd)
  refine ⟨L, hLP, hleaf, ?_⟩
  have hpos : ∀ x ∈ L, 0 < β x := fun x hx =>
    lt_of_lt_of_le (by positivity) (hBd x (hLP hx)).1
  have hBq : ∀ x ∈ L, β x ≤ ((x : ℚ) + 1) / ((x : ℚ) - 1) := fun x hx => (hBd x (hLP hx)).2
  have hM : ∏ x ∈ L.filter (fun x => ¬ 13 ∣ x + 1), β x ≤
      (β 3 * β 7 * β 31 * β 127) * (2048 / 2047) := by
    apply mersenne_bound
    · intro x hx
      exact (hP x (hLP (Finset.mem_filter.mp hx).1)).1
    · intro x hx
      obtain ⟨hxL, hxz⟩ := Finset.mem_filter.mp hx
      exact two_pow_of_no_odd_prime (fun c hc h2 hd => hxz (hleaf x hxL c hc h2 hd ▸ hd))
    · intro x hx
      have hxL := (Finset.mem_filter.mp hx).1
      exact ⟨hpos x hxL, hBq x hxL⟩
    · simp only [hβ3, hβ7, hβ31, hβ127, b7, b181, b31, b61, b487, b127]
      norm_num
  rw [hβ3, hβ7, hβ31, hβ127] at hM
  have h103 : ∏ x ∈ (L.filter (fun x => 13 ∣ x + 1)).filter (fun x => x = 103), β x ≤ b103 := by
    have hsub : (L.filter (fun x => 13 ∣ x + 1)).filter (fun x => x = 103) ⊆ ({103} : Finset ℕ) :=
      fun x hx => by rw [Finset.mem_singleton]; exact (Finset.mem_filter.mp hx).2
    have h := Finset.prod_le_prod_of_subset_of_one_le (f := β) hsub
      (fun x hx => (hpos x (Finset.mem_filter.mp (Finset.mem_filter.mp hx).1).1).le)
      (fun x hx _ => by rw [Finset.mem_singleton.mp hx, hβ103]; simp only [b103]; norm_num)
    rwa [Finset.prod_singleton, hβ103] at h
  have hrest : ∏ x ∈ (L.filter (fun x => 13 ∣ x + 1)).filter (fun x => ¬ x = 103), β x ≤
      ∏ x ∈ (L.filter (fun x => 13 ∣ x + 1)).filter (fun x => ¬ x = 103),
        (((x : ℚ) + 1) / ((x : ℚ) - 1)) :=
    Finset.prod_le_prod
      (fun x hx => (hpos x (Finset.mem_filter.mp (Finset.mem_filter.mp hx).1).1).le)
      (fun x hx => hBq x (Finset.mem_filter.mp (Finset.mem_filter.mp hx).1).1)
  have hZ : ∏ x ∈ L.filter (fun x => 13 ∣ x + 1), β x ≤
      b103 * ∏ x ∈ (L.filter (fun x => 13 ∣ x + 1)).filter (fun x => ¬ x = 103),
        (((x : ℚ) + 1) / ((x : ℚ) - 1)) := by
    rw [← Finset.prod_filter_mul_prod_filter_not (L.filter (fun x => 13 ∣ x + 1)) (fun x => x = 103) β]
    exact mul_le_mul h103 hrest
      (Finset.prod_nonneg fun x hx => (hpos x (Finset.mem_filter.mp (Finset.mem_filter.mp hx).1).1).le)
      (by simp only [b103]; norm_num)
  have hX : ∏ x ∈ L, β x ≤ ((8 / 5 * b7 * b31 * b127 * (2048 / 2047)) *
      (b103 * ∏ x ∈ (L.filter (fun x => 13 ∣ x + 1)).filter (fun x => ¬ x = 103),
        (((x : ℚ) + 1) / ((x : ℚ) - 1)))) := by
    rw [← Finset.prod_filter_mul_prod_filter_not L (fun x => 13 ∣ x + 1) β, mul_comm]
    exact mul_le_mul hM hZ (Finset.prod_nonneg fun x hx => (hpos x (Finset.mem_filter.mp hx).1).le)
      (by simp only [b7, b181, b31, b61, b487, b127]; norm_num)
  exact hmain.trans (mul_le_mul_of_nonneg_left hX (by positivity))

/-- `z = 13`, `a = 2 (mod 4)`, `e ≥ 4`: `a ≤ 13`. Total at most `1.9986 < 2` for `a ≥ 14`. -/
theorem thirteen_amod4_bound {n : ℕ} (h : Erdos1052.IsUnitaryPerfect n)
    (hS : ∀ p, p.Prime ∧ p ≠ 2 ∧ p ^ 2 ∣ n ↔ p = 13) (he4 : 4 ≤ n.factorization 13)
    (hm4 : padicValNat 2 n % 4 = 2) : padicValNat 2 n ≤ 13 := by
  classical
  by_contra hgt
  have hm14 : 14 ≤ padicValNat 2 n := by omega
  have hz : Nat.Prime 13 := by norm_num
  obtain ⟨hzn, hs⟩ := simple_of_unique_repeated h.2.ne' hS
  have hzpf : 13 ∈ n.primeFactors := Nat.mem_primeFactors.mpr ⟨hz, hzn, h.2.ne'⟩
  obtain ⟨hP, E⟩ := kernel_balance_one h hzpf (by norm_num) hs
  rw [Nat.factorization_def n Nat.prime_two] at E
  have hzP : 13 ∉ (n.primeFactors.erase 2).filter (fun r => ¬ r ∈ ({13} : Finset ℕ)) := fun hmem =>
    (Finset.mem_filter.mp hmem).2 (Finset.mem_singleton_self 13)
  obtain ⟨-, h5P, h5c, -⟩ := setup5 hP hz (by norm_num) E hm4
  obtain ⟨L, hLP, hleaf, hmain⟩ := thirteen_amod4_master hP E hzP h5P h5c
  have hZ := thirteen_leaves_no103 (fun x hx => hP x (hLP hx)) hleaf
  refine table_close hm14 hmain (by positivity)
    (kk_le (a := 13) (b := 4) (by norm_num) (le_refl _) he4) (by norm_num)
    (mul_nonneg (by norm_num) (Finset.prod_nonneg fun x hx =>
      B_nonneg (hP x (hLP (Finset.mem_filter.mp (Finset.mem_filter.mp hx).1).1)).1.one_lt.le))
    (mul_le_mul_of_nonneg_left hZ (by norm_num)) ?_
  norm_num

-- ### Section 4: Main reduction

theorem main : H1 → H2 → H3 → H4 → OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H2_R1_H4_R1_H4_R1_H2_R1.H1 := by
  rintro ⟨A1, h1⟩ ⟨A2, h2⟩ ⟨A3, h3⟩ ⟨A4, h4⟩
  refine ⟨max 13 (max A1 (max A2 (max A3 A4))),
    fun n h z hz hzl hS he32 a6 a10 a14 a20 a28 a8 a16 a4096 U R => ?_⟩
  have he2 : 2 ≤ n.factorization z :=
    (hz.pow_dvd_iff_le_factorization h.2.ne').mp ((hS z).mpr rfl).2.2
  have he4 : 4 ≤ n.factorization z := by omega
  simp only [Finset.mem_insert, Finset.mem_singleton] at hzl
  rcases hzl with rfl | rfl | rfl | rfl
  · -- z = 11
    by_cases c2 : padicValNat 2 n % 4 = 2
    · exact (h1 n h hS he32 a20 (a28 (by norm_num)) c2).trans
        ((le_max_left _ _).trans (le_max_right _ _))
    · by_cases c16 : padicValNat 2 n % 16 = 8
      · exact (z11_a16_dead h hS he4 c16).elim
      · exact (small4_core h hz (by norm_num) (by norm_num) hS he4 c2 (a8 (by norm_num)) c16
          (by simpa using R 4 (by simp)) (by simpa using R 5 (by simp))
          (by simpa using R 6 (by simp)) (by simpa using R 7 (by simp))
          (by simpa using R 8 (by simp)) (by simpa using R 9 (by simp))
          (by simpa using R 10 (by simp)) _
          (fun L hLp hleaf => zleaves_11 hLp hleaf) (by norm_num) (by norm_num)).trans
          ((by norm_num : (7 : ℕ) ≤ 13).trans (le_max_left _ _))
  · -- z = 13 (settled completely!)
    by_cases c2 : padicValNat 2 n % 4 = 2
    · exact (thirteen_amod4_bound h hS he4 c2).trans (le_max_left _ _)
    · exact (small4_core h hz (by norm_num) (by norm_num) hS he4 c2 (a8 (by norm_num))
        (a16 (by norm_num) (by norm_num) (by norm_num))
        (by simpa using R 4 (by simp)) (by simpa using R 5 (by simp))
        (by simpa using R 6 (by simp)) (by simpa using R 7 (by simp))
        (by simpa using R 8 (by simp)) (by simpa using R 9 (by simp))
        (by simpa using R 10 (by simp)) _
        (fun L hLp hleaf => zleaves_13 hLp hleaf) (by norm_num) (by norm_num)).trans
        ((by norm_num : (7 : ℕ) ≤ 13).trans (le_max_left _ _))
  · -- z = 17
    by_cases c2 : padicValNat 2 n % 4 = 2
    · exact (h2 n h hS he32 a20 (a28 (by norm_num)) c2).trans
        ((le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _)))
    · by_cases c8 : padicValNat 2 n % 8 = 4
      · exact (h4 n h hS he32 c8).trans
          ((le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))))
      · exact (small4_core h hz (by norm_num) (by norm_num) hS he4 c2 c8
          (a16 (by norm_num) (by norm_num) (by norm_num))
          (by simpa using R 4 (by simp)) (by simpa using R 5 (by simp))
          (by simpa using R 6 (by simp)) (by simpa using R 7 (by simp))
          (by simpa using R 8 (by simp)) (by simpa using R 9 (by simp))
          (by simpa using R 10 (by simp)) _
          (fun L hLp hleaf => zleaves_17 hLp hleaf) (by norm_num) (by norm_num)).trans
          ((by norm_num : (7 : ℕ) ≤ 13).trans (le_max_left _ _))
  · -- z = 19
    by_cases c2 : padicValNat 2 n % 4 = 2
    · exact (h3 n h hS he32 a20 (a28 (by norm_num)) c2).trans
        ((le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))))
    · exact (small4_core h hz (by norm_num) (by norm_num) hS he4 c2 (a8 (by norm_num))
        (a16 (by norm_num) (by norm_num) (by norm_num))
        (by simpa using R 4 (by simp)) (by simpa using R 5 (by simp))
        (by simpa using R 6 (by simp)) (by simpa using R 7 (by simp))
        (by simpa using R 8 (by simp)) (by simpa using R 9 (by simp))
        (by simpa using R 10 (by simp)) _
        (fun L hLp hleaf => zleaves_19 hLp hleaf) (by norm_num) (by norm_num)).trans
        ((by norm_num : (7 : ℕ) ≤ 13).trans (le_max_left _ _))

end OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H2_R1_H4_R1_H4_R1_H2_R1_H1_R2
