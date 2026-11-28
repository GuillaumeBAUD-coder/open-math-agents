import OMAStatements.S_oeis_a079450
import Mathlib

open OMA.S_oeis_a079450

namespace P079450

lemma u1 : u 1 = 1 := rfl

lemma uR (n : ℕ) (hn : 1 ≤ n) : u (n + 1) = Int.fract (3 / 2 * u n) + 1 := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  rfl

lemma bounds (n : ℕ) (hn : 1 ≤ n) : 1 ≤ u n ∧ u n < 2 := by
  induction n, hn using Nat.le_induction with
  | base => rw [u1]; norm_num
  | succ n hn ih =>
    rw [uR n hn]
    exact ⟨by linarith [Int.fract_nonneg ((3 : ℚ) / 2 * u n)],
      by linarith [Int.fract_lt_one ((3 : ℚ) / 2 * u n)]⟩

lemma step (n : ℕ) (hn : 1 ≤ n) :
    u (n + 1) = if u n < 4 / 3 then 3 / 2 * u n else 3 / 2 * u n - 1 := by
  rw [uR n hn]
  obtain ⟨h1, h2⟩ := bounds n hn
  split_ifs with h
  · have : ⌊(3 / 2 : ℚ) * u n⌋ = 1 := by
      rw [Int.floor_eq_iff]; constructor <;> push_cast <;> linarith
    rw [← Int.self_sub_floor, this]; push_cast; ring
  · have : ⌊(3 / 2 : ℚ) * u n⌋ = 2 := by
      rw [Int.floor_eq_iff]; constructor <;> push_cast <;> linarith [not_lt.mp h]
    rw [← Int.self_sub_floor, this]; push_cast; ring

lemma dyadic (n : ℕ) (hn : 1 ≤ n) : ∃ z : ℤ, u n * 2 ^ (n - 1) = z := by
  induction n, hn using Nat.le_induction with
  | base => exact ⟨1, by rw [u1]; norm_num⟩
  | succ n hn ih =>
    obtain ⟨z, hz⟩ := ih
    rw [step n hn]
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    rw [show k + 1 + 1 - 1 = k + 1 by omega]
    rw [show k + 1 - 1 = k by omega] at hz
    split_ifs
    · exact ⟨3 * z, by rw [pow_succ]; push_cast; rw [← hz]; ring⟩
    · exact ⟨3 * z - 2 ^ (k + 1), by rw [pow_succ]; push_cast; rw [← hz]; ring⟩

lemma ne43 (n : ℕ) (hn : 1 ≤ n) : u n ≠ 4 / 3 := by
  intro h
  obtain ⟨z, hz⟩ := dyadic n hn
  rw [h] at hz
  have h2 : (((2 ^ (n + 1) : ℕ) : ℤ) : ℚ) = ((3 * z : ℤ) : ℚ) := by
    push_cast
    rw [show n + 1 = (n - 1) + 2 by omega, pow_add]
    linarith
  have h3 : ((2 ^ (n + 1) : ℕ) : ℤ) = 3 * z := by exact_mod_cast h2
  have : ((3 : ℕ) : ℤ) ∣ ((2 ^ (n + 1) : ℕ) : ℤ) := ⟨z, by rw [h3]; norm_num⟩
  rw [Int.natCast_dvd_natCast] at this
  have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three this
  omega

lemma gt1 (n : ℕ) (hn : 2 ≤ n) : 1 < u n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  rw [step k (by omega)]
  obtain ⟨h1, h2⟩ := bounds k (by omega)
  have := ne43 k (by omega)
  split_ifs with h
  · linarith
  · have : 4 / 3 < u k := lt_of_le_of_ne (not_lt.mp h) (Ne.symm this)
    linarith

def r (N : ℕ) : ℚ := (3 - 3 / 2 * u N) * (2 / 3) ^ N

lemma r_notG (k : ℕ) (hk : 1 ≤ k) (h : ¬ u k < 4 / 3) : r (k + 1) = r k := by
  unfold r; rw [step k hk, if_neg h, pow_succ]; ring

lemma r_G (k : ℕ) (hk : 1 ≤ k) (h : u k < 4 / 3) : r (k + 1) = r k - (2 / 3) ^ k := by
  unfold r; rw [step k hk, if_pos h, pow_succ]; ring

lemma gap (N M : ℕ) (hN : 1 ≤ N) (hNM : N ≤ M) (h : ∀ k, N ≤ k → k < M → ¬ u k < 4 / 3) :
    r M = r N := by
  induction M, hNM using Nat.le_induction with
  | base => rfl
  | succ M hM ih =>
    rw [r_notG M (by omega) (h M hM (by omega)), ih (fun k h1 h2 => h k h1 (by omega))]

lemma cond_iff (k : ℕ) (hk : 1 ≤ k) : (2 / 3 : ℚ) ^ k ≤ r k ↔ u k < 4 / 3 := by
  unfold r
  have hp : (0 : ℚ) < (2 / 3) ^ k := by positivity
  constructor
  · intro h
    have h1 : (1 : ℚ) ≤ 3 - 3 / 2 * u k := by
      by_contra hc
      have : (3 - 3 / 2 * u k) * (2 / 3 : ℚ) ^ k < 1 * (2 / 3) ^ k :=
        mul_lt_mul_of_pos_right (not_le.mp hc) hp
      linarith
    rcases lt_or_gt_of_ne (ne43 k hk) with h2 | h2
    · exact h2
    · linarith
  · intro h
    have : (1 : ℚ) * (2 / 3) ^ k ≤ (3 - 3 / 2 * u k) * (2 / 3 : ℚ) ^ k :=
      mul_le_mul_of_nonneg_right (by linarith) hp.le
    linarith

lemma below (N : ℕ) (k : ℕ) (hk1 : 1 ≤ k) (hkN : k < N) : r N < (2 / 3) ^ k := by
  have hu := gt1 N (by omega)
  have hle : (2 / 3 : ℚ) ^ (N - 1) ≤ (2 / 3) ^ k :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
  have hp : (0 : ℚ) < (2 / 3) ^ (N - 1) := by positivity
  have e : r N = (3 - 3 / 2 * u N) * (2 / 3) * (2 / 3) ^ (N - 1) := by
    unfold r
    rw [show N = (N - 1) + 1 by omega, pow_succ, show N - 1 + 1 - 1 = N - 1 by omega]
    ring
  have : (3 - 3 / 2 * u N) * (2 / 3) * (2 / 3 : ℚ) ^ (N - 1) < 1 * (2 / 3) ^ (N - 1) :=
    mul_lt_mul_of_pos_right (by linarith) hp
  linarith

def Inv (l : List ℕ) (N : ℕ) : Prop :=
  (l.map fun j => (2 / 3 : ℚ) ^ j).sum = 1 - r N ∧ ∀ x, x ∈ l ↔ (1 ≤ x ∧ x < N ∧ u x < 4 / 3)

lemma inv_nil : Inv [] 1 := by
  refine ⟨?_, fun x => ?_⟩
  · simp only [List.map_nil, List.sum_nil, r, u1]; norm_num
  · simp only [List.not_mem_nil, false_iff]; omega

lemma claimA (l : List ℕ) (hl : Greedy l) : ∃ N, 1 ≤ N ∧ Inv l N := by
  induction hl with
  | nil => exact ⟨1, le_refl _, inv_nil⟩
  | snoc l e hl he ih =>
    obtain ⟨N, hN, hs, hm⟩ := ih
    obtain ⟨⟨he1, hec⟩, hmin⟩ := he
    rw [hs] at hec
    have hc : (2 / 3 : ℚ) ^ e ≤ r N := by linarith
    have heN : N ≤ e := by
      by_contra hcon
      exact absurd hc (not_le.mpr (below N e he1 (by omega)))
    have hnoG : ∀ k, N ≤ k → k < e → ¬ u k < 4 / 3 := by
      by_contra hcon
      have hex : ∃ j, N ≤ j ∧ j < e ∧ u j < 4 / 3 := by
        simp only [not_forall, not_not, exists_prop] at hcon
        exact hcon
      have hj := Nat.find_spec hex
      have hjmin : ∀ k < Nat.find hex, ¬ (N ≤ k ∧ k < e ∧ u k < 4 / 3) := fun k hk => Nat.find_min hex hk
      have hg : r (Nat.find hex) = r N :=
        gap N _ hN hj.1 (fun k h1 h2 hk => hjmin k h2 ⟨h1, by omega, hk⟩)
      have h3 : (2 / 3 : ℚ) ^ (Nat.find hex) ≤ r (Nat.find hex) := (cond_iff _ (by omega)).mpr hj.2.2
      have h4 := hmin (show Nat.find hex ∈ {k : ℕ | 1 ≤ k ∧ (l.map fun j => (2 / 3 : ℚ) ^ j).sum + (2 / 3 : ℚ) ^ k ≤ 1} from
        ⟨by omega, by rw [hs]; linarith⟩)
      omega
    have hgE : r e = r N := gap N e hN heN hnoG
    have heG : u e < 4 / 3 := (cond_iff e he1).mp (by rw [hgE]; exact hc)
    refine ⟨e + 1, by omega, ?_, fun x => ?_⟩
    · rw [List.map_append, List.sum_append, hs, r_G e he1 heG, hgE, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
      ring
    · rw [List.mem_append, hm, List.mem_singleton]
      constructor
      · rintro (⟨h1, h2, h3⟩ | rfl)
        · exact ⟨h1, by omega, h3⟩
        · exact ⟨he1, by omega, heG⟩
      · rintro ⟨h1, h2, h3⟩
        by_cases hxN : x < N
        · exact Or.inl ⟨h1, hxN, h3⟩
        · by_cases hxe : x = e
          · exact Or.inr hxe
          · exact absurd h3 (hnoG x (by omega) (by omega))

lemma claimB (N : ℕ) (hN : 1 ≤ N) : ∃ l, Greedy l ∧ Inv l N := by
  induction N, hN using Nat.le_induction with
  | base => exact ⟨[], Greedy.nil, inv_nil⟩
  | succ N hN ih =>
    obtain ⟨l, hl, hs, hm⟩ := ih
    by_cases hG : u N < 4 / 3
    · have hc := (cond_iff N hN).mpr hG
      refine ⟨l ++ [N], Greedy.snoc l N hl ⟨⟨hN, ?_⟩, ?_⟩, ?_, fun x => ?_⟩
      · rw [hs]; linarith
      · rintro k ⟨hk1, hkc⟩
        by_contra hcon
        have := below N k hk1 (by omega)
        rw [hs] at hkc
        linarith
      · rw [List.map_append, List.sum_append, hs, r_G N hN hG, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
        ring
      · rw [List.mem_append, hm, List.mem_singleton]
        constructor
        · rintro (⟨h1, h2, h3⟩ | rfl)
          · exact ⟨h1, by omega, h3⟩
          · exact ⟨hN, by omega, hG⟩
        · rintro ⟨h1, h2, h3⟩
          by_cases hxN : x < N
          · exact Or.inl ⟨h1, hxN, h3⟩
          · exact Or.inr (by omega)
    · refine ⟨l, hl, by rw [hs, r_notG N hN hG], fun x => ?_⟩
      rw [hm]
      constructor
      · rintro ⟨h1, h2, h3⟩; exact ⟨h1, by omega, h3⟩
      · rintro ⟨h1, h2, h3⟩
        refine ⟨h1, ?_, h3⟩
        by_contra hcon
        have : x = N := by omega
        rw [this] at h3
        exact hG h3

end P079450

open P079450 in
theorem OMA.solution : type_of% @OMA.S_oeis_a079450.main := by
  intro n hn
  have key : a (n + 1) = 3 * a n ↔ u n < 4 / 3 := by
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    unfold a
    rw [step (k + 1) hn, show k + 1 + 1 - 1 = k + 1 by omega, show k + 1 - 1 = k by omega]
    split_ifs with h
    · simp only [h, iff_true]; rw [pow_succ]; ring
    · simp only [h, iff_false]
      intro hc
      have : (2 : ℚ) ^ (k + 1) = 0 := by rw [pow_succ] at hc ⊢; linarith
      exact absurd this (by positivity)
  rw [key]
  constructor
  · intro hG
    obtain ⟨l, hl, _, hm⟩ := claimB (n + 1) (by omega)
    exact ⟨l, hl, (hm n).mpr ⟨hn, by omega, hG⟩⟩
  · rintro ⟨l, hl, hnl⟩
    obtain ⟨N, _, _, hm⟩ := claimA l hl
    exact ((hm n).mp hnl).2.2
