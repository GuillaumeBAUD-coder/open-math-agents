import OMAStatements.S_oeis_a113318
import Mathlib

namespace A113318

def L : ℕ → ℕ → List ℕ
  | 0, _ => []
  | k + 1, n => n % 10 :: L k (n / 10)

def D : ℕ → ℕ → List ℕ
  | 0, _ => []
  | f + 1, n => if n = 0 then [] else n % 10 :: D f (n / 10)

def prune (k s : ℕ) : Bool :=
  decide (L k s).Nodup && (L k (s ^ 4)).all (fun d => decide (d ∉ L k s))

def good (k s : ℕ) : Bool :=
  decide (10 ^ k ≤ 10 * s) && (D (4 * k) (s ^ 4)).all (fun d => decide (d ∉ L k s))

def S : ℕ → ℕ → ℕ → List ℕ
  | 0, _, _ => []
  | f + 1, k, s =>
    (if good k s then [s] else []) ++
      (List.range 10).flatMap (fun d =>
        if prune (k + 1) (s + 10 ^ k * d) then S f (k + 1) (s + 10 ^ k * d) else [])

def T : List ℕ := [2, 3, 4, 7, 8, 9, 24, 27, 28, 32, 42, 52, 53, 58, 59, 67, 89, 93, 203, 258,
  284, 324, 329, 832, 843, 2673]

theorem S_all : (S 11 0 0).all (fun x => decide (x ∈ T)) = true := by decide +kernel

theorem L_length : ∀ k n, (L k n).length = k
  | 0, _ => rfl
  | k + 1, n => by simp [L, L_length k]

theorem L_mod : ∀ k n, L k (n % 10 ^ k) = L k n
  | 0, _ => rfl
  | k + 1, n => by
    have h1 : n % 10 ^ (k + 1) % 10 = n % 10 :=
      Nat.mod_mod_of_dvd n (dvd_pow_self 10 (Nat.succ_ne_zero k))
    have h2 : n % 10 ^ (k + 1) / 10 = n / 10 % 10 ^ k := by
      rw [pow_succ', Nat.mod_mul_right_div_self]
    simp only [L, h1, h2, L_mod k]

theorem L_sub : ∀ k j n, k ≤ j → (L k n).Sublist (L j n)
  | 0, _, _, _ => List.nil_sublist _
  | k + 1, 0, _, h => absurd h (by omega)
  | k + 1, j + 1, n, h => by
    simp only [L]
    exact (L_sub k j (n / 10) (by omega)).cons_cons _

theorem L_eq : ∀ k n, 10 ^ k ≤ n → n < 10 ^ (k + 1) → L (k + 1) n = Nat.digits 10 n
  | 0, n, h1, h2 => by
    have : n % 10 = n := Nat.mod_eq_of_lt (by simpa using h2)
    rw [Nat.digits_of_lt 10 n (by omega) (by simpa using h2)]
    simp [L, this]
  | k + 1, n, h1, h2 => by
    have hpos : 0 < n := lt_of_lt_of_le (by positivity) h1
    rw [Nat.digits_def' (by norm_num) hpos]
    have := L_eq k (n / 10) (by rw [Nat.le_div_iff_mul_le (by norm_num)]; rw [pow_succ] at h1; exact h1)
      (by rw [Nat.div_lt_iff_lt_mul (by norm_num)]; rw [pow_succ] at h2; exact h2)
    rw [← this]; rfl

theorem D_eq : ∀ f n, n < 10 ^ f → D f n = Nat.digits 10 n
  | 0, n, h => by
    have : n = 0 := by simpa using h
    subst this; simp [D]
  | f + 1, n, h => by
    by_cases hn : n = 0
    · subst hn; simp [D]
    · rw [Nat.digits_def' (by norm_num) (Nat.pos_of_ne_zero hn)]
      simp only [D, hn, if_false]
      rw [D_eq f (n / 10) (by rw [Nat.div_lt_iff_lt_mul (by norm_num)]; rw [pow_succ] at h; exact h)]

theorem key (m : ℕ) (hm : 0 < m) (hnd : (Nat.digits 10 m).Nodup)
    (hex : ∀ d ∈ Nat.digits 10 (m ^ 4), d ∉ Nat.digits 10 m) : m ∈ T := by
  have h1 : 10 ^ Nat.log 10 m ≤ m := Nat.pow_log_le_self 10 (by omega)
  have h2 : m < 10 ^ (Nat.log 10 m + 1) := Nat.lt_pow_succ_log_self (by norm_num) m
  generalize Nat.log 10 m = j at h1 h2
  have hL : L (j + 1) m = Nat.digits 10 m := L_eq j m h1 h2
  have hm4 : m ≤ m ^ 4 := Nat.le_self_pow (by norm_num) m
  have h3 : 10 ^ Nat.log 10 (m ^ 4) ≤ m ^ 4 := Nat.pow_log_le_self 10 (by positivity)
  have h4 : m ^ 4 < 10 ^ (Nat.log 10 (m ^ 4) + 1) := Nat.lt_pow_succ_log_self (by norm_num) _
  generalize Nat.log 10 (m ^ 4) = J at h3 h4
  have hL4 : L (J + 1) (m ^ 4) = Nat.digits 10 (m ^ 4) := L_eq J _ h3 h4
  have hjJ : j < J + 1 :=
    (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 10)).1 (lt_of_le_of_lt (h1.trans hm4) h4)
  have hj : j + 1 ≤ 10 := by
    have hlen : (Nat.digits 10 m).length = j + 1 := by rw [← hL, L_length]
    have hsub : (Nat.digits 10 m).toFinset ⊆ Finset.range 10 := by
      intro d hd
      rw [List.mem_toFinset] at hd
      exact Finset.mem_range.2 (Nat.digits_lt_base (by norm_num) hd)
    have hc := Finset.card_le_card hsub
    rw [List.toFinset_card_of_nodup hnd, Finset.card_range, hlen] at hc
    exact hc
  have hprune : ∀ k, k ≤ j + 1 → prune k (m % 10 ^ k) = true := by
    intro k hk
    have e4 : L k ((m % 10 ^ k) ^ 4) = L k (m ^ 4) := by
      rw [← L_mod k ((m % 10 ^ k) ^ 4), ← Nat.pow_mod, L_mod]
    simp only [prune, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, L_mod, e4]
    refine ⟨(L_sub k (j + 1) m hk).nodup (hL ▸ hnd), ?_⟩
    intro d hd hd'
    have a1 : d ∈ Nat.digits 10 (m ^ 4) := hL4 ▸ (L_sub k (J + 1) (m ^ 4) (by omega)).subset hd
    have a2 : d ∈ Nat.digits 10 m := hL ▸ (L_sub k (j + 1) m hk).subset hd'
    exact hex d a1 a2
  have hgood : good (j + 1) m = true := by
    have hlt : m ^ 4 < 10 ^ (4 * (j + 1)) := by
      rw [mul_comm, pow_mul]
      exact Nat.pow_lt_pow_left h2 (by norm_num)
    simp only [good, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, D_eq _ _ hlt, hL]
    refine ⟨?_, hex⟩
    rw [pow_succ, mul_comm]
    exact Nat.mul_le_mul_left 10 h1
  have hpath : ∀ f k, k ≤ j + 1 → j + 2 ≤ f + k → m ∈ S f k (m % 10 ^ k) := by
    intro f
    induction f with
    | zero => intro k hk hf; omega
    | succ f ih =>
      intro k hk hf
      simp only [S, List.mem_append, List.mem_flatMap, List.mem_range]
      by_cases hkj : k = j + 1
      · left
        subst hkj
        rw [Nat.mod_eq_of_lt h2, hgood]
        simp
      · right
        refine ⟨m / 10 ^ k % 10, Nat.mod_lt _ (by norm_num), ?_⟩
        rw [← Nat.mod_pow_succ, hprune (k + 1) (by omega)]
        simpa using ih (k + 1) (by omega) (by omega)
  have hmem : m ∈ S 11 0 0 := by
    have := hpath 11 0 (by omega) (by omega)
    rwa [pow_zero, Nat.mod_one] at this
  have := List.all_eq_true.1 S_all m hmem
  simpa using this

end A113318

theorem OMA.solution : type_of% @OMA.S_oeis_a113318.main := by
  ext m
  simp only [Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨hm, hnd, hex⟩
    have := A113318.key m hm hnd hex
    simpa [A113318.T] using this
  · rintro (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;>
    refine ⟨by norm_num, by norm_num, by norm_num⟩
