import OMAStatements.S_oeis_a066337
import Mathlib

namespace OMA.A066337proof

open OMA.S_oeis_a066337 PowerSeries

/-- The least residue of a preimage block: `16 * (n / 16) + cc (n % 16)` is the least preimage. -/
def cc : ℕ → ℕ
  | 0 => 0 | 1 => 2 | 2 => 5 | 3 => 4 | 4 => 6 | 5 => 9 | 6 => 8 | 7 => 10
  | 8 => 13 | 9 => 12 | 10 => 14 | 15 => 17 | _ => 0

def pre (n : ℕ) : ℕ := 16 * (n / 16) + cc (n % 16)

def F (n : ℕ) : ℤ := if n % 16 ≤ 10 ∨ n % 16 = 15 then (pre n : ℤ) else -1

def gg (n : ℕ) : ℤ := if n % 16 ≤ 10 ∨ n % 16 = 15 then 1 else 0

lemma value_eq (q r : ℕ) (hr : r < 16) : value (16 * q + r) = 16 * q + low r := by
  unfold value
  rw [Nat.mul_add_div (by norm_num), Nat.div_eq_of_lt hr, Nat.mul_add_mod, Nat.mod_eq_of_lt hr]
  push_cast; ring

lemma value_pre (n : ℕ) (hg : n % 16 ≤ 10 ∨ n % 16 = 15) : value (pre n) = n := by
  have hn := Nat.div_add_mod n 16
  unfold pre
  generalize n / 16 = q at hn ⊢
  generalize hr : n % 16 = r at hn hg ⊢
  subst hn
  rcases hg with hg | hg
  · rw [value_eq q (cc r) (by interval_cases r <;> decide)]
    interval_cases r <;> simp [cc, low]
  · subst hg
    rw [show 16 * q + cc 15 = 16 * (q + 1) + 1 by simp [cc]; ring, value_eq _ _ (by norm_num)]
    simp [low]; ring

set_option maxHeartbeats 4000000 in
lemma value_ge (n k : ℕ) (h : value k = n) : (n % 16 ≤ 10 ∨ n % 16 = 15) ∧ pre n ≤ k := by
  have hk := Nat.div_add_mod k 16
  have hn := Nat.div_add_mod n 16
  have hk' := Nat.mod_lt k (show 16 > 0 by norm_num)
  have hn' := Nat.mod_lt n (show 16 > 0 by norm_num)
  unfold pre
  rw [← hk, value_eq _ _ hk'] at h
  generalize k / 16 = q' at h hk ⊢
  generalize k % 16 = r' at h hk hk' ⊢
  generalize n / 16 = q at hn ⊢
  generalize n % 16 = r at hn hn' ⊢
  subst hk hn
  interval_cases r <;> interval_cases r' <;> simp [cc, low] at h ⊢ <;> omega

lemma a_eq (n : ℕ) : a n = F n := by
  unfold a F
  by_cases hg : n % 16 ≤ 10 ∨ n % 16 = 15
  · have hex : ∃ m : ℕ, value m = (n : ℤ) := ⟨pre n, value_pre n hg⟩
    rw [dif_pos hex, if_pos hg]
    congr 1
    rw [Nat.find_eq_iff]
    exact ⟨value_pre n hg, fun k hk hv => absurd (value_ge n k hv).2 (by omega)⟩
  · have hex : ¬ ∃ m : ℕ, value m = (n : ℤ) := fun ⟨m, hm⟩ => hg (value_ge n m hm).1
    rw [dif_neg hex, if_neg hg]

lemma F_shift (q c : ℕ) : F (16 * q + c) = F c + 16 * q * gg c := by
  unfold F gg pre
  rw [Nat.mul_add_mod, Nat.mul_add_div (by norm_num)]
  split_ifs <;> push_cast <;> ring

lemma hF : ∀ c, 29 ≤ c → c < 45 →
    F c = F (c-1)-F (c-4)+F (c-5)-F (c-8)+F (c-9)-F (c-12)+F (c-13)+F (c-16)-
      F (c-17)+F (c-20)-F (c-21)+F (c-24)-F (c-25)+F (c-28)-F (c-29) := by
  intro c h1 h2; interval_cases c <;> decide

lemma hG : ∀ c, 29 ≤ c → c < 45 →
    gg c = gg (c-1)-gg (c-4)+gg (c-5)-gg (c-8)+gg (c-9)-gg (c-12)+gg (c-13)+gg (c-16)-
      gg (c-17)+gg (c-20)-gg (c-21)+gg (c-24)-gg (c-25)+gg (c-28)-gg (c-29) := by
  intro c h1 h2; interval_cases c <;> decide

lemma rec_a : recurrence := by
  intro n hn
  simp only [a_eq]
  obtain ⟨q, c, h1, h2, rfl⟩ : ∃ q c, 29 ≤ c ∧ c < 45 ∧ n = 16 * q + c :=
    ⟨(n - 29) / 16, 29 + (n - 29) % 16, by omega, by omega, by omega⟩
  have key : ∀ j, j ≤ 29 → F (16 * q + c - j) = F (c - j) + 16 * q * gg (c - j) :=
    fun j hj => by rw [Nat.add_sub_assoc (by omega), F_shift]
  rw [F_shift, key 1 (by norm_num), key 4 (by norm_num), key 5 (by norm_num), key 8 (by norm_num),
    key 9 (by norm_num), key 12 (by norm_num), key 13 (by norm_num), key 16 (by norm_num),
    key 17 (by norm_num), key 20 (by norm_num), key 21 (by norm_num), key 24 (by norm_num),
    key 25 (by norm_num), key 28 (by norm_num), key 29 (by norm_num)]
  linear_combination hF c h1 h2 + 16 * (q : ℤ) * hG c h1 h2

lemma denom_mul (φ : PowerSeries ℤ) : denominator * φ =
    φ - X ^ 1 * φ + X ^ 4 * φ - X ^ 5 * φ + X ^ 8 * φ - X ^ 9 * φ + X ^ 12 * φ - X ^ 13 * φ
      - X ^ 16 * φ + X ^ 17 * φ - X ^ 20 * φ + X ^ 21 * φ - X ^ 24 * φ + X ^ 25 * φ
      - X ^ 28 * φ + X ^ 29 * φ := by
  unfold denominator; ring

lemma numer_eq : numerator =
    C 2 * X ^ 1 + C 3 * X ^ 2 + C (-1) * X ^ 3 + C 2 * X ^ 4 + C 5 * X ^ 5 + C 2 * X ^ 6
      + C 1 * X ^ 7 + C 5 * X ^ 8 + C 4 * X ^ 9 + C 4 * X ^ 10 + C (-14) * X ^ 11
      + C 5 * X ^ 12 + C 4 * X ^ 13 + C 4 * X ^ 14 + C 4 * X ^ 15 + C 4 * X ^ 16
      + C 2 * X ^ 17 + C 1 * X ^ 18 + C 5 * X ^ 19 + C 2 * X ^ 20 + C (-1) * X ^ 21
      + C 2 * X ^ 22 + C 3 * X ^ 23 + C (-1) * X ^ 24 + C 2 * X ^ 27 + C (-1) * X ^ 28 := by
  unfold numerator; simp only [map_ofNat, map_neg, map_one]; ring

lemma gf_a : generatingFunction := by
  unfold generatingFunction
  rw [denom_mul, numer_eq]
  ext n
  simp only [map_add, map_sub, coeff_C_mul, coeff_X_pow, coeff_X_pow_mul', coeff_mk]
  rcases Nat.lt_or_ge n 29 with h | h
  · simp only [a_eq]
    interval_cases n <;> decide
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 29 := ⟨n - 29, by omega⟩
    have h1 : ∀ j, j ≤ 29 → (j ≤ m + 29 ↔ True) := fun j hj => by simp; omega
    have h2 : ∀ j, j ≤ 28 → (m + 29 = j ↔ False) := fun j hj => by simp; omega
    have h3 : ∀ j, j ≤ 29 → m + 29 - j = m + (29 - j) := fun j hj => by omega
    have r := rec_a (m + 29) (by omega)
    simp (disch := omega) only [h1, h2, h3, if_true, if_false, Nat.reduceSub, add_zero,
      mul_zero, add_zero] at r ⊢
    linear_combination r

theorem a066337 : type_of% @OMA.S_oeis_a066337.main := ⟨rec_a, gf_a⟩

end OMA.A066337proof

theorem OMA.solution : type_of% @OMA.S_oeis_a066337.main := OMA.A066337proof.a066337
