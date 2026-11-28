import OMAReductions.R_Erdos406_erdos_406_variants_one_two_R1_H2_R1_H2_R1

-- Only the last 64 ternary digits matter, so we work modulo 3^64.
-- The range is cut into blocks of 64 exponents, explored by a binary tree.

namespace Erdos406LowDigits

def hasZero : ℕ → ℕ → Bool
  | 0, _ => false
  | n + 1, r => (r % 3 == 0) || hasZero n (r / 3)

def allUpTo (f : ℕ → Bool) : ℕ → Bool
  | 0 => true
  | n + 1 => f n && allUpTo f n

def tree (f : ℕ → Bool) : ℕ → ℕ → Bool
  | 0, s => f s
  | d + 1, s => tree f d s && tree f d (s + 2 ^ d)

def blockWith (lo base : ℕ) : Bool :=
  allUpTo (fun j => Nat.ble 164572 (lo + j) || hasZero 64 (base * 2 ^ j % 3 ^ 64)) 64

def block (b : ℕ) : Bool := blockWith (4096 + 64 * b) (2 ^ (4096 + 64 * b) % 3 ^ 64)

lemma hasZero_sound : ∀ n r, hasZero n r = true → ∃ i < n, (r / 3 ^ i) % 3 = 0 := by
  intro n
  induction n with
  | zero => intro r h; simp [hasZero] at h
  | succ n ih =>
    intro r h
    simp only [hasZero, Bool.or_eq_true, beq_iff_eq] at h
    rcases h with h | h
    · exact ⟨0, by omega, by simpa using h⟩
    · obtain ⟨i, hi, e⟩ := ih _ h
      refine ⟨i + 1, by omega, ?_⟩
      rwa [pow_succ', ← Nat.div_div_eq_div_mul]

lemma allUpTo_sound (f : ℕ → Bool) : ∀ n, allUpTo f n = true → ∀ j < n, f j = true := by
  intro n
  induction n with
  | zero => intro _ j hj; omega
  | succ n ih =>
    intro h j hj
    simp only [allUpTo, Bool.and_eq_true] at h
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
    · exact ih h.2 j hj
    · exact h.1

lemma tree_sound (f : ℕ → Bool) :
    ∀ d s, tree f d s = true → ∀ x, s ≤ x → x < s + 2 ^ d → f x = true := by
  intro d
  induction d with
  | zero =>
    intro s h x h1 h2
    have : x = s := by simp at h2; omega
    subst this
    simpa [tree] using h
  | succ d ih =>
    intro s h x h1 h2
    simp only [tree, Bool.and_eq_true] at h
    rw [pow_succ] at h2
    by_cases hx : x < s + 2 ^ d
    · exact ih s h.1 x h1 hx
    · exact ih _ h.2 x (by omega) (by omega)

lemma digit_mod (a i : ℕ) (hi : i < 64) :
    (a / 3 ^ i) % 3 = ((a % 3 ^ 64) / 3 ^ i) % 3 := by
  have h : (3 : ℕ) ^ 64 = 3 ^ i * 3 ^ (64 - i) := by
    rw [← pow_add]; congr 1; omega
  rw [h, Nat.mod_mul_right_div_self, Nat.mod_mod_of_dvd]
  exact dvd_pow_self 3 (by omega)

lemma combine (m lo j k i : ℕ) (h : lo + j = k)
    (e : ((2 ^ lo % m * 2 ^ j % m) / 3 ^ i) % 3 = 0) : ((2 ^ k % m) / 3 ^ i) % 3 = 0 := by
  rwa [Nat.mod_mul_mod, ← pow_add, h] at e

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem checked : tree block 12 0 = true := by
  decide +kernel

end Erdos406LowDigits

open Erdos406LowDigits in
theorem OMA.solution : OMA.R_Erdos406_erdos_406_variants_one_two_R1_H2_R1_H2_R1.H1 := by
  intro k h1 h2
  have hb : block ((k - 4096) / 64) = true :=
    tree_sound block 12 0 checked _ (Nat.zero_le _) (by
      have : (2 : ℕ) ^ 12 = 4096 := by norm_num
      omega)
  unfold block blockWith at hb
  have hj := allUpTo_sound _ 64 hb ((k - 4096) % 64) (Nat.mod_lt _ (by norm_num))
  have hk : 4096 + 64 * ((k - 4096) / 64) + (k - 4096) % 64 = k := by omega
  simp only [Bool.or_eq_true] at hj
  rcases hj with hj | hj
  · rw [hk, Nat.ble_eq] at hj
    omega
  · obtain ⟨i, hi, e⟩ := hasZero_sound _ _ hj
    refine ⟨i, hi, ?_⟩
    rw [digit_mod _ _ hi]
    exact combine _ _ _ _ _ hk e
