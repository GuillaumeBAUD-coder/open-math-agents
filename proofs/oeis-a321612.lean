import OMAStatements.S_oeis_a321612
import Mathlib

namespace OMA.A321612Proof

open OMA.S_oeis_a321612

lemma two_tri (i : ℕ) : 2 * tri i = i * (i + 1) := by
  unfold tri
  exact Nat.mul_div_cancel' (Nat.even_mul_succ_self i).two_dvd

lemma le_tri (m : ℕ) : m ≤ tri m := by
  rcases m with _ | m
  · simp [tri]
  · have := two_tri (m + 1)
    nlinarith

lemma tri_triangular (m : ℕ) : triangular (tri m) :=
  ⟨⟨m, Nat.lt_succ_of_le (le_tri m)⟩, rfl⟩

lemma triangular_iff (v : ℕ) : triangular v ↔ ∃ x, x * (x + 1) = 2 * v := by
  constructor
  · rintro ⟨i, h⟩
    exact ⟨i.val, by rw [← two_tri, h]⟩
  · rintro ⟨x, h⟩
    have hx : x < v + 1 := by nlinarith
    refine ⟨⟨x, hx⟩, ?_⟩
    have := two_tri x
    simp only
    omega

def isTriB (v : ℕ) : Bool := (List.range (v + 1)).any (fun x => tri x == v)

lemma isTriB_iff (v : ℕ) : isTriB v = true ↔ triangular v := by
  simp [isTriB, triangular, Fin.exists_iff]

def inTermsB (k : ℕ) : Bool :=
  (List.range k).any (fun m => decide (tri m < k) && decide (k ≤ 2 * tri m)) &&
  (List.range k).all (fun m => !(decide (tri m < k) && decide (k ≤ 2 * tri m)) ||
    isTriB (k - tri m))

lemma inTerms_iff (k : ℕ) : inTerms k ↔
    (∃ m, tri m < k ∧ k ≤ 2 * tri m) ∧
    (∀ m, tri m < k → k ≤ 2 * tri m → triangular (k - tri m)) := by
  unfold inTerms
  constructor
  · rintro ⟨⟨t, ht1, ht2⟩, h2⟩
    obtain ⟨i, hi⟩ := ht2
    refine ⟨⟨i.val, ?_, ?_⟩, ?_⟩
    · rw [hi]; exact t.isLt
    · rw [hi]; exact ht1
    · intro m hm1 hm2
      exact h2 ⟨tri m, hm1⟩ hm2 (tri_triangular m)
  · rintro ⟨⟨m, hm1, hm2⟩, h2⟩
    refine ⟨⟨⟨tri m, hm1⟩, hm2, tri_triangular m⟩, ?_⟩
    intro t ht1 ht2
    obtain ⟨i, hi⟩ := ht2
    have e : t.val = tri i.val := hi.symm
    rw [e] at ht1 ⊢
    exact h2 i.val (e ▸ t.isLt) ht1

lemma inTermsB_iff (k : ℕ) : inTermsB k = true ↔ inTerms k := by
  rw [inTerms_iff]
  simp only [inTermsB, Bool.and_eq_true, List.any_eq_true, List.all_eq_true, List.mem_range,
    decide_eq_true_eq, Bool.or_eq_true, Bool.not_eq_true', Bool.and_eq_false_iff,
    decide_eq_false_iff_not, not_lt, not_le, isTriB_iff]
  constructor
  · rintro ⟨⟨m, -, hm1, hm2⟩, h2⟩
    refine ⟨⟨m, hm1, hm2⟩, ?_⟩
    intro m' hm1' hm2'
    have hm' : m' < k := lt_of_le_of_lt (le_tri m') hm1'
    rcases h2 m' hm' with (h | h) | h
    · omega
    · omega
    · exact h
  · rintro ⟨⟨m, hm1, hm2⟩, h2⟩
    refine ⟨⟨m, lt_of_le_of_lt (le_tri m) hm1, hm1, hm2⟩, ?_⟩
    intro m' _
    by_cases a : tri m' < k
    · by_cases b : k ≤ 2 * tri m'
      · exact Or.inr (h2 m' a b)
      · exact Or.inl (Or.inr (by omega))
    · exact Or.inl (Or.inl (by omega))

set_option maxRecDepth 100000 in
lemma finite_part : ∀ k < 111, inTermsB k = (k == 2 || k == 4 || k == 6 || k == 7 || k == 9 ||
    k == 13 || k == 16 || k == 21 || k == 31) := by
  decide

lemma big (k : ℕ) (hk : 110 < k) : ¬ inTerms k := by
  rw [inTerms_iff]
  rintro ⟨-, h⟩
  have hex : ∃ n, k ≤ n * (n + 1) := ⟨k, by nlinarith⟩
  classical
  obtain ⟨n, hkn, hmin⟩ : ∃ n, k ≤ n * (n + 1) ∧ ∀ m < n, ¬ k ≤ m * (m + 1) :=
    ⟨Nat.find hex, Nat.find_spec hex, fun m hm => Nat.find_min hex hm⟩
  have hn11 : 11 ≤ n := by
    by_contra hc
    have : n * (n + 1) ≤ 10 * 11 := Nat.mul_le_mul (by omega) (by omega)
    omega
  obtain ⟨p, rfl⟩ : ∃ p, n = p + 1 := ⟨n - 1, by omega⟩
  have hlow : p * (p + 1) < k := by
    have := hmin p (by omega)
    omega
  have hkn' : k ≤ (p + 1) * (p + 2) := hkn
  have t0 : 2 * tri (p + 1) = (p + 1) * (p + 2) := two_tri _
  have t1 : 2 * tri (p + 2) = (p + 2) * (p + 3) := two_tri _
  have t2 : 2 * tri (p + 3) = (p + 3) * (p + 4) := two_tri _
  have hlt : (p + 3) * (p + 4) < 2 * k := by nlinarith
  have hmono1 : (p + 1) * (p + 2) ≤ (p + 2) * (p + 3) := Nat.mul_le_mul (by omega) (by omega)
  have hmono2 : (p + 2) * (p + 3) ≤ (p + 3) * (p + 4) := Nat.mul_le_mul (by omega) (by omega)
  obtain ⟨x, hx⟩ := (triangular_iff _).1 (h (p + 1) (by omega) (by omega))
  obtain ⟨y, hy⟩ := (triangular_iff _).1 (h (p + 2) (by omega) (by omega))
  obtain ⟨z, hz⟩ := (triangular_iff _).1 (h (p + 3) (by omega) (by omega))
  have hx' : x * (x + 1) + (p + 1) * (p + 2) = 2 * k := by omega
  have hy' : y * (y + 1) + (p + 2) * (p + 3) = 2 * k := by omega
  have hz' : z * (z + 1) + (p + 3) * (p + 4) = 2 * k := by omega
  clear hx hy hz h t0 t1 t2 hmin hex hkn
  rcases lt_trichotomy y (z + 1) with hyz | hyz | hyz
  · have : y * (y + 1) ≤ z * (z + 1) := Nat.mul_le_mul (by omega) (by omega)
    nlinarith
  · subst hyz
    have hz1 : z = p + 2 := by nlinarith
    subst hz1
    rcases le_or_gt x (p + 3) with hxp | hxp
    · have : x * (x + 1) ≤ (p + 3) * (p + 4) := Nat.mul_le_mul hxp (by omega)
      nlinarith
    · have : (p + 4) * (p + 5) ≤ x * (x + 1) := Nat.mul_le_mul hxp (by omega)
      nlinarith
  · have hge : (z + 2) * (z + 3) ≤ y * (y + 1) := Nat.mul_le_mul hyz (by omega)
    have hz2 : 2 * z + 1 ≤ p + 1 := by nlinarith
    have hsq : (2 * z + 1) * (2 * z + 1) ≤ (p + 1) * (p + 1) := Nat.mul_le_mul hz2 hz2
    nlinarith

end OMA.A321612Proof

open OMA.A321612Proof in
theorem OMA.solution : type_of% @OMA.S_oeis_a321612.main := by
  ext k
  simp only [Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
  by_cases hk : k < 111
  · rw [← inTermsB_iff, finite_part k hk]
    simp only [Bool.or_eq_true, beq_iff_eq]
    tauto
  · have := big k (by omega)
    constructor
    · intro h; exact absurd h this
    · intro h; omega
