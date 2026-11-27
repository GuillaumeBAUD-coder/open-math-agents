import OMAStatements.S_oeis_a067576
import Mathlib

-- Credit: @sntntHb (the owner of the agent is credited as the solver)
-- Proof sketch: let pc be the number of set bits. Binary recursion shows that below 2^n
-- the numbers with pc = n - 1 are exactly 2^n - 1 - 2^k for k < n. Hence for j <= i the
-- zero-based j-th number with i set bits is 2^(i+1) - 1 - 2^(i-j) (there are exactly j
-- such numbers below it), and the doubling rule T(i+1,j) + 1 = 2 (T(i,j) + 1) holds for
-- all i >= j. For j >= 2 the rule fails at i = j - 1, because T(j,j) = 2^(j+1) - 2 is even
-- while the rule forces it to be odd. So the least valid positive start is max 1 j.

namespace OMA.A067576Proof

def pc (n : ℕ) : ℕ := n.bitIndices.length

theorem pc_zero : pc 0 = 0 := by simp [pc]

theorem pc_even (m : ℕ) : pc (2 * m) = pc m := by simp [pc]

theorem pc_odd (m : ℕ) : pc (2 * m + 1) = pc m + 1 := by simp [pc]

theorem pow_pos' (k : ℕ) : 0 < 2 ^ k := Nat.two_pow_pos k

theorem pc_A : ∀ n y : ℕ, y < 2 ^ n → pc y ≤ n ∧ (pc y = n → y + 1 = 2 ^ n) := by
  intro n
  induction n with
  | zero => intro y hy; simp at hy; subst hy; simp [pc_zero]
  | succ n ih =>
    intro y hy
    rw [pow_succ] at hy
    rcases Nat.even_or_odd' y with ⟨m, rfl | rfl⟩
    · obtain ⟨h1, h2⟩ := ih m (by omega)
      rw [pc_even]
      refine ⟨by omega, fun h => ?_⟩
      have := h2 (by omega)
      omega
    · obtain ⟨h1, h2⟩ := ih m (by omega)
      rw [pc_odd]
      refine ⟨by omega, fun h => ?_⟩
      have := h2 (by omega)
      rw [pow_succ]
      omega

theorem pc_full : ∀ n : ℕ, pc (2 ^ n - 1) = n := by
  intro n
  induction n with
  | zero => simp [pc_zero]
  | succ n ih =>
    have hp := pow_pos' n
    have e : 2 ^ (n + 1) - 1 = 2 * (2 ^ n - 1) + 1 := by rw [pow_succ]; omega
    rw [e, pc_odd, ih]

theorem pc_B : ∀ n y : ℕ, y < 2 ^ n → pc y + 1 = n → ∃ k < n, y + 2 ^ k + 1 = 2 ^ n := by
  intro n
  induction n with
  | zero => intro y _ h; omega
  | succ n ih =>
    intro y hy h
    rw [pow_succ] at hy
    rcases Nat.even_or_odd' y with ⟨m, rfl | rfl⟩
    · rw [pc_even] at h
      have := (pc_A n m (by omega)).2 (by omega)
      refine ⟨0, by omega, ?_⟩
      rw [pow_succ]; simp; omega
    · rw [pc_odd] at h
      obtain ⟨k, hk, hk2⟩ := ih m (by omega) (by omega)
      refine ⟨k + 1, by omega, ?_⟩
      rw [pow_succ, pow_succ]
      omega

theorem pc_B' : ∀ n k : ℕ, k < n → pc (2 ^ n - 1 - 2 ^ k) + 1 = n := by
  intro n
  induction n with
  | zero => intro k hk; omega
  | succ n ih =>
    intro k hk
    rcases Nat.eq_zero_or_pos k with h0 | hpos
    · subst h0
      have hp := pow_pos' n
      have e : 2 ^ (n + 1) - 1 - 2 ^ 0 = 2 * (2 ^ n - 1) := by rw [pow_succ]; simp; omega
      rw [e, pc_even, pc_full]
    · obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
      have hlt : 2 ^ k' < 2 ^ n := Nat.pow_lt_pow_right (by norm_num) (by omega)
      have e : 2 ^ (n + 1) - 1 - 2 ^ (k' + 1) = 2 * (2 ^ n - 1 - 2 ^ k') + 1 := by
        rw [pow_succ, pow_succ]; omega
      rw [e, pc_odd, ih k' (by omega)]

/-- The candidate value of the zero-based j-th number with i set bits. -/
def f (i k : ℕ) : ℕ := 2 ^ (i + 1) - 1 - 2 ^ k

theorem count_f (i m : ℕ) (hm : m ≤ i) :
    Nat.count (fun a : ℕ => a.bitIndices.length = i) (f i m) = i - m := by
  rw [Nat.count_eq_card_filter_range]
  have hset : (Finset.range (f i m)).filter (fun a : ℕ => a.bitIndices.length = i) =
      (Finset.Ioc m i).image (f i) := by
    ext y
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_image, Finset.mem_Ioc]
    constructor
    · rintro ⟨hy, hpc⟩
      have hmi : 2 ^ m ≤ 2 ^ i := Nat.pow_le_pow_right (by norm_num) hm
      have hi1 : 2 ^ (i + 1) = 2 * 2 ^ i := by rw [pow_succ]; ring
      have hpm := pow_pos' m
      unfold f at hy
      obtain ⟨k, hk, hk2⟩ := pc_B (i + 1) y (by omega) (by unfold pc; omega)
      have hkm : m < k := by
        by_contra hc
        have : 2 ^ k ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) (by omega)
        omega
      refine ⟨k, ⟨hkm, by omega⟩, ?_⟩
      unfold f; omega
    · rintro ⟨k, ⟨hk1, hk2⟩, rfl⟩
      have hki : 2 ^ k ≤ 2 ^ i := Nat.pow_le_pow_right (by norm_num) hk2
      have hmk : 2 ^ m < 2 ^ k := Nat.pow_lt_pow_right (by norm_num) hk1
      have hi1 : 2 ^ (i + 1) = 2 * 2 ^ i := by rw [pow_succ]; ring
      have hpk := pow_pos' k
      have hlt : f i k < f i m := by
        show 2 ^ (i + 1) - 1 - 2 ^ k < 2 ^ (i + 1) - 1 - 2 ^ m
        omega
      refine ⟨hlt, ?_⟩
      have := pc_B' (i + 1) k (by omega)
      unfold pc f at *
      omega
  rw [hset, Finset.card_image_of_injOn, Nat.card_Ioc]
  intro a ha b hb hab
  simp only [Finset.coe_Ioc, Set.mem_Ioc] at ha hb
  have ha' : 2 ^ a ≤ 2 ^ i := Nat.pow_le_pow_right (by norm_num) ha.2
  have hb' : 2 ^ b ≤ 2 ^ i := Nat.pow_le_pow_right (by norm_num) hb.2
  have hi1 : 2 ^ (i + 1) = 2 * 2 ^ i := by rw [pow_succ]; ring
  have hab' : 2 ^ (i + 1) - 1 - 2 ^ a = 2 ^ (i + 1) - 1 - 2 ^ b := hab
  have hpa := pow_pos' a
  have hpb := pow_pos' b
  have : 2 ^ a = 2 ^ b := by omega
  exact Nat.pow_right_injective (le_refl 2) this

theorem entry_eq (i j : ℕ) (hj : j ≤ i) :
    OMA.S_oeis_a067576.entry i (j + 1) = 2 ^ (i + 1) - 1 - 2 ^ (i - j) := by
  unfold OMA.S_oeis_a067576.entry
  have hc := count_f i (i - j) (by omega)
  have hp : (f i (i - j)).bitIndices.length = i := by
    have := pc_B' (i + 1) (i - j) (by omega)
    unfold pc f at *; omega
  have hn := Nat.nth_count (p := fun a : ℕ => a.bitIndices.length = i) hp
  rw [hc, show i - (i - j) = j by omega] at hn
  simp only [Nat.add_sub_cancel]
  rw [hn]
  rfl

end OMA.A067576Proof

open OMA.A067576Proof in
theorem OMA.solution : type_of% @OMA.S_oeis_a067576.main := by
  intro j
  constructor
  · refine ⟨by omega, fun i hi => ?_⟩
    rw [entry_eq i j (by omega), entry_eq (i + 1) j (by omega)]
    have h1 : i + 1 - j = (i - j) + 1 := by omega
    rw [h1]
    have hle : 2 ^ (i - j) ≤ 2 ^ i := Nat.pow_le_pow_right (by norm_num) (by omega)
    have e1 : 2 ^ (i - j + 1) = 2 * 2 ^ (i - j) := by rw [pow_succ]; ring
    have e2 : 2 ^ (i + 1 + 1) = 2 * 2 ^ (i + 1) := by rw [pow_succ]; ring
    have e3 : 2 ^ (i + 1) = 2 * 2 ^ i := by rw [pow_succ]; ring
    have hp := pow_pos' (i - j)
    omega
  · rintro r ⟨hr, h⟩
    by_contra hlt
    push_neg at hlt
    have hj : 2 ≤ j := by omega
    have := h (j - 1) (by omega)
    rw [show j - 1 + 1 = j by omega, entry_eq j j le_rfl] at this
    simp only [Nat.sub_self, pow_zero] at this
    have e3 : 2 ^ (j + 1) = 2 * 2 ^ j := by rw [pow_succ]; ring
    have hp := pow_pos' j
    omega
