import OMAStatements.S_oeis_a373308
import Mathlib

namespace OMA373308
open Polynomial OMA.S_oeis_a373308

lemma E_even (T : Polynomial ℤ) (i : ℕ) : (expand ℤ 2 T).coeff (2 * i) = T.coeff i := by
  rw [coeff_expand (by norm_num)]; simp

lemma E_odd (T : Polynomial ℤ) (i : ℕ) : (expand ℤ 2 T).coeff (2 * i + 1) = 0 := by
  rw [coeff_expand (by norm_num)]
  have : ¬ (2 ∣ 2 * i + 1) := by omega
  simp [this]

lemma split (E : Polynomial ℤ) :
    (1 - X) ^ 3 * E = E - 3 * (X * E) + 3 * (X ^ 2 * E) - X ^ 3 * E := by ring

lemma cm_zero (T : Polynomial ℤ) : ((1 - X) ^ 3 * expand ℤ 2 T).coeff 0 = T.coeff 0 := by
  rw [split]
  simp only [coeff_sub, coeff_add, coeff_ofNat_mul, coeff_X_pow_mul', coeff_X_mul_zero]
  have := E_even T 0
  simp only [mul_zero] at this
  simp [this]

lemma cm_one (T : Polynomial ℤ) : ((1 - X) ^ 3 * expand ℤ 2 T).coeff 1 = -3 * T.coeff 0 := by
  rw [split]
  simp only [coeff_sub, coeff_add, coeff_ofNat_mul, coeff_X_pow_mul']
  have h0 := E_even T 0
  have h1 := E_odd T 0
  simp only [mul_zero, zero_add] at h0 h1
  have h2 : (X * expand ℤ 2 T).coeff 1 = (expand ℤ 2 T).coeff 0 := coeff_X_mul _ 0
  simp [h0, h1, h2]

lemma cm_even (T : Polynomial ℤ) (m : ℕ) :
    ((1 - X) ^ 3 * expand ℤ 2 T).coeff (2 * m + 2) = T.coeff (m + 1) + 3 * T.coeff m := by
  rw [split]
  simp only [coeff_sub, coeff_add, coeff_ofNat_mul]
  rw [show 2 * m + 2 = (2 * m + 1) + 1 by ring, coeff_X_mul, E_odd,
    show 2 * m + 1 + 1 = 2 * m + 2 by ring, coeff_X_pow_mul, E_even, coeff_X_pow_mul',
    show 2 * m + 2 = 2 * (m + 1) by ring, E_even]
  have : ((if 3 ≤ 2 * (m + 1) then (expand ℤ 2 T).coeff (2 * (m + 1) - 3) else 0) : ℤ) = 0 := by
    split_ifs with h
    · rw [show 2 * (m + 1) - 3 = 2 * (m - 1) + 1 by omega, E_odd]
    · rfl
  rw [this]; ring

lemma cm_odd (T : Polynomial ℤ) (m : ℕ) :
    ((1 - X) ^ 3 * expand ℤ 2 T).coeff (2 * m + 3) = -3 * T.coeff (m + 1) - T.coeff m := by
  rw [split]
  simp only [coeff_sub, coeff_add, coeff_ofNat_mul]
  rw [show 2 * m + 3 = (2 * m + 2) + 1 by ring, coeff_X_mul,
    show 2 * m + 2 + 1 = 2 * m + 1 + 2 by ring, coeff_X_pow_mul, E_odd,
    show 2 * m + 1 + 2 = 2 * m + 3 by ring, coeff_X_pow_mul, E_even,
    show 2 * m + 3 = 2 * (m + 1) + 1 by ring, E_odd, show 2 * m + 2 = 2 * (m + 1) by ring, E_even]
  ring

lemma trunc_succ (d : ℕ) : truncation (d + 1) = (1 - X) ^ 3 * expand ℤ 2 (truncation d) := by
  unfold truncation
  have h : ∏ j ∈ Finset.range d, ((1 : Polynomial ℤ) - X ^ (2 ^ (j + 1))) ^ 3 =
      expand ℤ 2 (∏ j ∈ Finset.range d, ((1 : Polynomial ℤ) - X ^ (2 ^ j)) ^ 3) := by
    simp only [map_prod, map_pow, map_sub, map_one, expand_X]
    refine Finset.prod_congr rfl fun j _ => ?_
    rw [← pow_mul, show 2 * 2 ^ j = 2 ^ (j + 1) by ring]
  rw [Finset.prod_range_succ', mul_comm, h, pow_zero, pow_one]

lemma stab1 (d j : ℕ) (h : j < 2 ^ d) : (truncation (d + 1)).coeff j = (truncation d).coeff j := by
  have : truncation (d + 1) = truncation d - X ^ (2 ^ d) *
      (truncation d * (3 - 3 * X ^ (2 ^ d) + (X ^ (2 ^ d)) ^ 2)) := by
    unfold truncation; rw [Finset.prod_range_succ]; ring
  rw [this, coeff_sub, coeff_X_pow_mul', if_neg (by omega), sub_zero]

lemma stab (d j : ℕ) (h : j < 2 ^ d) : ∀ k, (truncation (d + k)).coeff j = (truncation d).coeff j := by
  intro k
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [← add_assoc, stab1 _ _ (lt_of_lt_of_le h (Nat.pow_le_pow_right (by norm_num) (by omega))), ih]

lemma cN (N i : ℕ) (h : i < N) : (truncation N).coeff i = a i := by
  obtain ⟨k, rfl⟩ : ∃ k, N = (i + 1) + k := ⟨N - (i + 1), by omega⟩
  rw [stab _ _ (lt_of_lt_of_le (Nat.lt_two_pow_self) (Nat.pow_le_pow_right (by norm_num) (by omega)))]
  rfl

lemma a0 : a 0 = 1 := by
  show (truncation (0 + 1)).coeff 0 = 1
  rw [trunc_succ, cm_zero]; simp [truncation]

lemma a1 : a 1 = -3 * a 0 := by
  show (truncation (1 + 1)).coeff 1 = _
  rw [trunc_succ, cm_one, cN _ _ (by norm_num)]

lemma aE (m : ℕ) : a (2 * m + 2) = a (m + 1) + 3 * a m := by
  show (truncation (2 * m + 2 + 1)).coeff (2 * m + 2) = _
  rw [trunc_succ, cm_even, cN _ _ (by omega), cN _ _ (by omega)]

lemma aO (m : ℕ) : a (2 * m + 3) = -3 * a (m + 1) - a m := by
  show (truncation (2 * m + 3 + 1)).coeff (2 * m + 3) = _
  rw [trunc_succ, cm_odd, cN _ _ (by omega), cN _ _ (by omega)]

lemma a3 (n : ℕ) : a (4 * n + 3) = 8 * a n := by
  rcases n with _ | n
  · rw [show 4 * 0 + 3 = 2 * 0 + 3 by rfl, aO, a1, a0]; norm_num
  · rw [show 4 * (n + 1) + 3 = 2 * (2 * n + 2) + 3 by ring, aO,
      show 2 * n + 2 + 1 = 2 * n + 3 by ring, aO, aE]; ring

lemma a2 (n : ℕ) : a (4 * n + 6) = 8 * a n := by
  rw [show 4 * n + 6 = 2 * (2 * n + 2) + 2 by ring, aE, show 2 * n + 2 + 1 = 2 * n + 3 by ring,
    aO, aE]; ring

lemma a2z : a 2 = 0 := by
  rw [show 2 = 2 * 0 + 2 by rfl, aE, a1]; ring

lemma parity : ∀ n, a n % 2 = if n % 4 < 2 then 1 else 0 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases n with _ | _ | n
    · simp [a0]
    · rw [a1, a0]; decide
    · rcases Nat.even_or_odd' n with ⟨m, rfl | rfl⟩
      · rw [show 2 * m + 1 + 1 = 2 * m + 2 by ring, aE]
        have h1 := ih (m + 1) (by omega)
        have h2 := ih m (by omega)
        split_ifs at h1 h2 ⊢ <;> omega
      · rw [show 2 * m + 1 + 1 + 1 = 2 * m + 3 by ring, aO]
        have h1 := ih (m + 1) (by omega)
        have h2 := ih m (by omega)
        split_ifs at h1 h2 ⊢ <;> omega

lemma thue0 : thue 0 = 1 := by simp [thue]

lemma thueE (k : ℕ) : thue (2 * k) = thue k := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · rfl
  · unfold thue
    rw [Nat.digits_def' (by norm_num) (by omega), show 2 * k % 2 = 0 by omega,
      show 2 * k / 2 = k by omega]
    simp

lemma thueO (k : ℕ) : thue (2 * k + 1) = - thue k := by
  unfold thue
  rw [Nat.digits_def' (by norm_num) (by omega), show (2 * k + 1) % 2 = 1 by omega,
    show (2 * k + 1) / 2 = k by omega]
  simp [pow_succ, pow_add]

lemma mod3 : ∀ N, (N % 3 = 0 → a N % 3 = thue (N / 3) % 3) ∧ (N % 3 ≠ 0 → a N % 3 = 0) := by
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    rcases N with _ | _ | n
    · simp [a0, thue0]
    · rw [a1]; omega
    · rcases Nat.even_or_odd' n with ⟨m, rfl | rfl⟩
      · rw [show 2 * m + 1 + 1 = 2 * m + 2 by ring, aE]
        have h1 := ih (m + 1) (by omega)
        constructor
        · intro h
          have hm : (m + 1) % 3 = 0 := by omega
          rw [show (2 * m + 2) / 3 = 2 * ((m + 1) / 3) by omega, thueE, ← h1.1 hm]
          omega
        · intro h
          have := h1.2 (by omega)
          omega
      · rw [show 2 * m + 1 + 1 + 1 = 2 * m + 3 by ring, aO]
        have h1 := ih m (by omega)
        constructor
        · intro h
          have hm : m % 3 = 0 := by omega
          rw [show (2 * m + 3) / 3 = 2 * (m / 3) + 1 by omega, thueO]
          have h4 := h1.1 hm
          omega
        · intro h
          have := h1.2 (by omega)
          omega

lemma dig (b r : ℕ) (hr : r < 4) (h : 0 < 4 * b + r) :
    Nat.digits 4 (4 * b + r) = r :: Nat.digits 4 b := by
  rw [Nat.digits_def' (by norm_num) h, show (4 * b + r) % 4 = r by omega,
    show (4 * b + r) / 4 = b by omega]

lemma tail_ok (b r : ℕ) (hr : r < 4) (H : ∀ t ∈ Nat.digits 4 (4 * b + r), t ≤ 1) :
    ∀ t ∈ Nat.digits 4 b, t ≤ 1 := by
  intro t ht
  rcases Nat.eq_zero_or_pos (4 * b + r) with h | h
  · have : b = 0 := by omega
    subst this; simp at ht
  · exact H t (by rw [dig b r hr h]; exact List.mem_cons_of_mem _ ht)

lemma cons_ok (b r : ℕ) (hr : r ≤ 1) (H : ∀ t ∈ Nat.digits 4 b, t ≤ 1) :
    ∀ t ∈ Nat.digits 4 (4 * b + r), t ≤ 1 := by
  intro t ht
  rcases Nat.eq_zero_or_pos (4 * b + r) with h | h
  · rw [h] at ht; simp at ht
  · rw [dig b r (by omega) h] at ht
    rcases List.mem_cons.1 ht with rfl | ht
    · exact hr
    · exact H t ht

lemma z4 (M : ℕ) : zeroIndex (4 * M) ↔ zeroIndex M := by
  constructor
  · rintro ⟨b, hb, hd⟩
    obtain ⟨c, rfl⟩ : ∃ c, b = 4 * c + 0 := ⟨b / 4, by omega⟩
    exact ⟨c, by omega, tail_ok c 0 (by norm_num) hd⟩
  · rintro ⟨c, hc, hd⟩
    exact ⟨4 * c + 0, by omega, cons_ok c 0 (by norm_num) hd⟩

lemma z43 (M : ℕ) : zeroIndex (4 * M + 3) ↔ zeroIndex M := by
  constructor
  · rintro ⟨b, hb, hd⟩
    obtain ⟨c, rfl⟩ : ∃ c, b = 4 * c + 1 := ⟨b / 4, by omega⟩
    exact ⟨c, by omega, tail_ok c 1 (by norm_num) hd⟩
  · rintro ⟨c, hc, hd⟩
    exact ⟨4 * c + 1, by omega, cons_ok c 1 le_rfl hd⟩

lemma znot (M r : ℕ) (hr : r = 1 ∨ r = 2) : ¬ zeroIndex (4 * M + r) := by
  rintro ⟨b, hb, hd⟩
  have hb4 : b % 4 = 2 ∨ b % 4 = 3 := by omega
  have := hd (b % 4) (by
    rw [Nat.digits_def' (by norm_num) (by omega)]; exact List.mem_cons_self)
  omega

lemma z0 : zeroIndex 0 := ⟨0, rfl, by simp⟩

lemma zero_iff : ∀ n, a n = 0 ↔ zeroIndex (n + 1) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    obtain ⟨k, r, hr, rfl⟩ : ∃ k r, r < 4 ∧ n = 4 * k + r := ⟨n / 4, n % 4, by omega, by omega⟩
    have hp := parity (4 * k + r)
    interval_cases r
    · rw [if_pos (by omega)] at hp
      constructor
      · intro h; rw [h] at hp; simp at hp
      · intro h; exact absurd h (znot k 1 (by norm_num))
    · rw [if_pos (by omega)] at hp
      constructor
      · intro h; rw [h] at hp; simp at hp
      · intro h; exact absurd h (by rw [show 4 * k + 1 + 1 = 4 * k + 2 by ring]; exact znot k 2 (by norm_num))
    · rw [show 4 * k + 2 + 1 = 4 * k + 3 by ring, z43]
      rcases k with _ | j
      · simp only [mul_zero, zero_add, a2z, true_iff]; exact z0
      · rw [show 4 * (j + 1) + 2 = 4 * j + 6 by ring, a2, ← ih j (by omega)]
        omega
    · rw [show 4 * k + 3 + 1 = 4 * (k + 1) by ring, z4, a3, ← ih k (by omega)]
      omega

theorem sol : (∀ n : ℕ, a (3*n) ≡ thue n [ZMOD 3] ∧ 3 ∣ a (3*n+1) ∧ 3 ∣ a (3*n+2)) ∧
    (∀ n : ℕ, a n = 0 ↔ zeroIndex (n+1)) := by
  refine ⟨fun n => ⟨?_, ?_, ?_⟩, zero_iff⟩
  · have := (mod3 (3 * n)).1 (by omega)
    rw [show 3 * n / 3 = n by omega] at this
    exact this
  · exact Int.dvd_of_emod_eq_zero ((mod3 (3 * n + 1)).2 (by omega))
  · exact Int.dvd_of_emod_eq_zero ((mod3 (3 * n + 2)).2 (by omega))

end OMA373308

theorem OMA.solution : type_of% @OMA.S_oeis_a373308.main := by
  exact OMA373308.sol
