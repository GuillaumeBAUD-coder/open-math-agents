import FormalConjectures.Mathoverflow.«75792»

open Mathoverflow75792

namespace OMA

lemma successor_cube_bound {m k : ℕ} (hk : 0 < k) (hm : m ^ 3 ≤ 3 ^ k) :
    (m + 1) ^ 3 ≤ 3 * 3 ^ k := by
  by_cases h : 3 ≤ m
  · obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le h
    calc
      (3 + t + 1) ^ 3 ≤ 3 * (3 + t) ^ 3 := by ring_nf; omega
      _ ≤ 3 * 3 ^ k := Nat.mul_le_mul_left _ hm
  · have hmle : m ≤ 2 := by omega
    interval_cases m
    · exact le_trans (by decide : (0 + 1) ^ 3 ≤ 3 * 1)
        (Nat.mul_le_mul_left _ (Nat.one_le_pow _ _ (by decide)))
    · have h1 : (3 : ℕ) ^ 1 ≤ 3 ^ k := Nat.pow_le_pow_right (by decide) hk
      omega
    · have h2 : 2 ≤ k := by
        by_contra! hlt
        interval_cases k <;> norm_num at hm
      have hpow : (3 : ℕ) ^ 2 ≤ 3 ^ k := Nat.pow_le_pow_right (by decide) h2
      omega

lemma reachable_cube_bound {m k : ℕ} (hr : Reachable m k) : m ^ 3 ≤ 3 ^ k := by
  induction hr with
  | one => decide
  | @mul x y a b hx hy ihx ihy =>
    simpa only [mul_pow, pow_add] using Nat.mul_le_mul ihx ihy
  | @add x y a b hx hy ihx ihy =>
    obtain ⟨_, _, hx', ha'⟩ := hx.dec
    obtain ⟨_, _, hy', hb'⟩ := hy.dec
    rw [pow_add]
    by_cases hx1 : x = 1
    · rw [hx1, Nat.add_comm 1 y]
      exact (successor_cube_bound (by omega) ihy).trans
        (Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by decide : 0 < 3) (by omega : 1 ≤ a)))
    by_cases hy1 : y = 1
    · rw [hy1, Nat.mul_comm (3 ^ a)]
      exact (successor_cube_bound (by omega) ihx).trans
        (Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by decide : 0 < 3) (by omega : 1 ≤ b)))
    have hxy : x + y ≤ x * y := by
      obtain ⟨i, rfl⟩ := Nat.exists_eq_add_of_le (by omega : 2 ≤ x)
      obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le (by omega : 2 ≤ y)
      nlinarith
    calc
      (x + y) ^ 3 ≤ (x * y) ^ 3 := Nat.pow_le_pow_left hxy _
      _ ≤ _ := by simpa only [mul_pow] using Nat.mul_le_mul ihx ihy

end OMA

theorem OMA.solution : type_of% @Mathoverflow75792.complexity_three_pow := by
  intro n hn
  apply (Reachable.pow 3 n (by decide) hn).complexity_eq
  intro k hk hr
  have h := OMA.reachable_cube_bound hr
  rw [← pow_mul, Nat.mul_comm n 3] at h
  exact (not_le_of_gt (Nat.pow_lt_pow_right (by decide : 1 < 3) hk)) h
