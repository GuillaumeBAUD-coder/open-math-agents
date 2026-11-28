import OMAStatements.S_oeis_a024401
import Mathlib

namespace OMA.P024401

def S (n : ℕ) : Multiset ℕ := (Multiset.range (n + 2)).map (fun i => 3 * i + 2)

def a (n : ℕ) : ℕ := (S n).esymm 3 / (S n).esymm 2

/-- The first N terms of the arithmetic progression. -/
def T (N : ℕ) : Multiset ℕ := (Multiset.range N).map (fun i => 3 * i + 2)

lemma esymm_cons (c : ℕ) (s : Multiset ℕ) (k : ℕ) :
    (c ::ₘ s).esymm (k + 1) = s.esymm (k + 1) + c * s.esymm k := by
  unfold Multiset.esymm
  rw [Multiset.powersetCard_cons, Multiset.map_add, Multiset.sum_add, Multiset.map_map]
  congr 1
  simp only [Function.comp, Multiset.prod_cons]
  rw [Multiset.sum_map_mul_left]

lemma esymm_nil (k : ℕ) : (0 : Multiset ℕ).esymm (k + 1) = 0 := by
  unfold Multiset.esymm
  rw [Multiset.powersetCard_zero_right]
  simp

lemma e_zero (N : ℕ) : (T N).esymm 0 = 1 := by
  simp [Multiset.esymm]

lemma T_succ (N : ℕ) : T (N + 1) = (3 * N + 2) ::ₘ T N := by
  unfold T
  rw [Multiset.range_succ, Multiset.map_cons]

lemma e1_succ (N : ℕ) : (T (N + 1)).esymm 1 = (T N).esymm 1 + (3 * N + 2) := by
  rw [T_succ, esymm_cons, e_zero, mul_one]

lemma e2_succ (N : ℕ) : (T (N + 1)).esymm 2 = (T N).esymm 2 + (3 * N + 2) * (T N).esymm 1 := by
  rw [T_succ, esymm_cons]

lemma e3_succ (N : ℕ) : (T (N + 1)).esymm 3 = (T N).esymm 3 + (3 * N + 2) * (T N).esymm 2 := by
  rw [T_succ, esymm_cons]

lemma closed (N : ℕ) :
    48 * (((T N).esymm 1 : ℕ) : ℤ) = 72 * (N : ℤ) ^ 2 + 24 * (N : ℤ) ∧
    48 * (((T N).esymm 2 : ℕ) : ℤ) = 54 * (N : ℤ) ^ 4 - 36 * (N : ℤ) ^ 3 - 30 * (N : ℤ) ^ 2 + 12 * (N : ℤ) ∧
    48 * (((T N).esymm 3 : ℕ) : ℤ) = 27 * (N : ℤ) ^ 6 - 81 * (N : ℤ) ^ 5 + 27 * (N : ℤ) ^ 4 + 73 * (N : ℤ) ^ 3 - 30 * (N : ℤ) ^ 2 - 16 * (N : ℤ) := by
  induction N with
  | zero =>
    have hT : T 0 = 0 := rfl
    rw [hT, esymm_nil 0, esymm_nil 1, esymm_nil 2]
    simp
  | succ N ih =>
    obtain ⟨h1, h2, h3⟩ := ih
    refine ⟨?_, ?_, ?_⟩
    · rw [e1_succ]
      push_cast
      linear_combination h1 + 48 * (3 * (N : ℤ) + 2)
    · rw [e2_succ]
      push_cast
      linear_combination h2 + (3 * (N : ℤ) + 2) * h1
    · rw [e3_succ]
      push_cast
      linear_combination h3 + (3 * (N : ℤ) + 2) * h2

set_option maxRecDepth 20000 in
lemma val1 (q : ℕ) : (a (6 * q + 1) : ℤ) = 18 * (q : ℤ) ^ 2 + 11 * (q : ℤ) + 1 := by
  have hS : S (6 * q + 1) = T (6 * q + 1 + 2) := rfl
  obtain ⟨h1, h2, h3⟩ := closed (6 * q + 1 + 2)
  have hj := h3
  clear h1 h3
  unfold a
  rw [hS]
  generalize (T (6 * q + 1 + 2)).esymm 2 = A at h2 ⊢ hj
  generalize (T (6 * q + 1 + 2)).esymm 3 = B at hj ⊢
  push_cast at h2 hj ⊢
  have hA : 48 * (A : ℤ) = 69984 * (q : ℤ) ^ 4 + 132192 * (q : ℤ) ^ 3 + 92232 * (q : ℤ) ^ 2 + 28152 * (q : ℤ) + 3168 := by linear_combination h2
  have hq1 : (0 : ℤ) ≤ (q : ℤ) := Int.natCast_nonneg q
  have hq2 : (0 : ℤ) ≤ (q : ℤ) ^ 2 := pow_nonneg hq1 2
  have hq3 : (0 : ℤ) ≤ (q : ℤ) ^ 3 := pow_nonneg hq1 3
  have hq4 : (0 : ℤ) ≤ (q : ℤ) ^ 4 := pow_nonneg hq1 4
  have hP : (0 : ℤ) < 69984 * (q : ℤ) ^ 4 + 132192 * (q : ℤ) ^ 3 + 92232 * (q : ℤ) ^ 2 + 28152 * (q : ℤ) + 3168 := by linarith
  have hpos : 0 < (A : ℤ) := by linarith
  have hW : 48 * ((B : ℤ) - A * (18 * (q : ℤ) ^ 2 + 11 * (q : ℤ) + 1)) = 6912 * (q : ℤ) ^ 3 + 9792 * (q : ℤ) ^ 2 + 4512 * (q : ℤ) + 672 := by
    linear_combination hj - (18 * (q : ℤ) ^ 2 + 11 * (q : ℤ) + 1) * h2
  have hV : 48 * ((A : ℤ) - ((B : ℤ) - A * (18 * (q : ℤ) ^ 2 + 11 * (q : ℤ) + 1))) = 69984 * (q : ℤ) ^ 4 + 125280 * (q : ℤ) ^ 3 + 82440 * (q : ℤ) ^ 2 + 23640 * (q : ℤ) + 2496 := by
    linear_combination (1 + (18 * (q : ℤ) ^ 2 + 11 * (q : ℤ) + 1)) * h2 - hj
  have hW0 : (0 : ℤ) ≤ 6912 * (q : ℤ) ^ 3 + 9792 * (q : ℤ) ^ 2 + 4512 * (q : ℤ) + 672 := by linarith
  have hV0 : (0 : ℤ) < 69984 * (q : ℤ) ^ 4 + 125280 * (q : ℤ) ^ 3 + 82440 * (q : ℤ) ^ 2 + 23640 * (q : ℤ) + 2496 := by linarith
  exact ((Int.ediv_emod_unique (r := (B : ℤ) - A * (18 * (q : ℤ) ^ 2 + 11 * (q : ℤ) + 1)) (q := 18 * (q : ℤ) ^ 2 + 11 * (q : ℤ) + 1) hpos).2
    ⟨by ring, by linarith, by linarith⟩).1

set_option maxRecDepth 20000 in
lemma val2 (q : ℕ) : (a (6 * q + 2) : ℤ) = 18 * (q : ℤ) ^ 2 + 17 * (q : ℤ) + 3 := by
  have hS : S (6 * q + 2) = T (6 * q + 2 + 2) := rfl
  obtain ⟨h1, h2, h3⟩ := closed (6 * q + 2 + 2)
  have hj := h3
  clear h1 h3
  unfold a
  rw [hS]
  generalize (T (6 * q + 2 + 2)).esymm 2 = A at h2 ⊢ hj
  generalize (T (6 * q + 2 + 2)).esymm 3 = B at hj ⊢
  push_cast at h2 hj ⊢
  have hA : 48 * (A : ℤ) = 69984 * (q : ℤ) ^ 4 + 178848 * (q : ℤ) ^ 3 + 169992 * (q : ℤ) ^ 2 + 71208 * (q : ℤ) + 11088 := by linear_combination h2
  have hq1 : (0 : ℤ) ≤ (q : ℤ) := Int.natCast_nonneg q
  have hq2 : (0 : ℤ) ≤ (q : ℤ) ^ 2 := pow_nonneg hq1 2
  have hq3 : (0 : ℤ) ≤ (q : ℤ) ^ 3 := pow_nonneg hq1 3
  have hq4 : (0 : ℤ) ≤ (q : ℤ) ^ 4 := pow_nonneg hq1 4
  have hP : (0 : ℤ) < 69984 * (q : ℤ) ^ 4 + 178848 * (q : ℤ) ^ 3 + 169992 * (q : ℤ) ^ 2 + 71208 * (q : ℤ) + 11088 := by linarith
  have hpos : 0 < (A : ℤ) := by linarith
  have hW : 48 * ((B : ℤ) - A * (18 * (q : ℤ) ^ 2 + 17 * (q : ℤ) + 3)) = 23328 * (q : ℤ) ^ 4 + 66528 * (q : ℤ) ^ 3 + 69912 * (q : ℤ) ^ 2 + 32088 * (q : ℤ) + 5424 := by
    linear_combination hj - (18 * (q : ℤ) ^ 2 + 17 * (q : ℤ) + 3) * h2
  have hV : 48 * ((A : ℤ) - ((B : ℤ) - A * (18 * (q : ℤ) ^ 2 + 17 * (q : ℤ) + 3))) = 46656 * (q : ℤ) ^ 4 + 112320 * (q : ℤ) ^ 3 + 100080 * (q : ℤ) ^ 2 + 39120 * (q : ℤ) + 5664 := by
    linear_combination (1 + (18 * (q : ℤ) ^ 2 + 17 * (q : ℤ) + 3)) * h2 - hj
  have hW0 : (0 : ℤ) ≤ 23328 * (q : ℤ) ^ 4 + 66528 * (q : ℤ) ^ 3 + 69912 * (q : ℤ) ^ 2 + 32088 * (q : ℤ) + 5424 := by linarith
  have hV0 : (0 : ℤ) < 46656 * (q : ℤ) ^ 4 + 112320 * (q : ℤ) ^ 3 + 100080 * (q : ℤ) ^ 2 + 39120 * (q : ℤ) + 5664 := by linarith
  exact ((Int.ediv_emod_unique (r := (B : ℤ) - A * (18 * (q : ℤ) ^ 2 + 17 * (q : ℤ) + 3)) (q := 18 * (q : ℤ) ^ 2 + 17 * (q : ℤ) + 3) hpos).2
    ⟨by ring, by linarith, by linarith⟩).1

set_option maxRecDepth 20000 in
lemma val3 (q : ℕ) : (a (6 * q + 3) : ℤ) = 18 * (q : ℤ) ^ 2 + 23 * (q : ℤ) + 6 := by
  have hS : S (6 * q + 3) = T (6 * q + 3 + 2) := rfl
  obtain ⟨h1, h2, h3⟩ := closed (6 * q + 3 + 2)
  have hj := h3
  clear h1 h3
  unfold a
  rw [hS]
  generalize (T (6 * q + 3 + 2)).esymm 2 = A at h2 ⊢ hj
  generalize (T (6 * q + 3 + 2)).esymm 3 = B at hj ⊢
  push_cast at h2 hj ⊢
  have hA : 48 * (A : ℤ) = 69984 * (q : ℤ) ^ 4 + 225504 * (q : ℤ) ^ 3 + 271080 * (q : ℤ) ^ 2 + 144072 * (q : ℤ) + 28560 := by linear_combination h2
  have hq1 : (0 : ℤ) ≤ (q : ℤ) := Int.natCast_nonneg q
  have hq2 : (0 : ℤ) ≤ (q : ℤ) ^ 2 := pow_nonneg hq1 2
  have hq3 : (0 : ℤ) ≤ (q : ℤ) ^ 3 := pow_nonneg hq1 3
  have hq4 : (0 : ℤ) ≤ (q : ℤ) ^ 4 := pow_nonneg hq1 4
  have hP : (0 : ℤ) < 69984 * (q : ℤ) ^ 4 + 225504 * (q : ℤ) ^ 3 + 271080 * (q : ℤ) ^ 2 + 144072 * (q : ℤ) + 28560 := by linarith
  have hpos : 0 < (A : ℤ) := by linarith
  have hW : 48 * ((B : ℤ) - A * (18 * (q : ℤ) ^ 2 + 23 * (q : ℤ) + 6)) = 46656 * (q : ℤ) ^ 4 + 157248 * (q : ℤ) ^ 3 + 197424 * (q : ℤ) ^ 2 + 109392 * (q : ℤ) + 22560 := by
    linear_combination hj - (18 * (q : ℤ) ^ 2 + 23 * (q : ℤ) + 6) * h2
  have hV : 48 * ((A : ℤ) - ((B : ℤ) - A * (18 * (q : ℤ) ^ 2 + 23 * (q : ℤ) + 6))) = 23328 * (q : ℤ) ^ 4 + 68256 * (q : ℤ) ^ 3 + 73656 * (q : ℤ) ^ 2 + 34680 * (q : ℤ) + 6000 := by
    linear_combination (1 + (18 * (q : ℤ) ^ 2 + 23 * (q : ℤ) + 6)) * h2 - hj
  have hW0 : (0 : ℤ) ≤ 46656 * (q : ℤ) ^ 4 + 157248 * (q : ℤ) ^ 3 + 197424 * (q : ℤ) ^ 2 + 109392 * (q : ℤ) + 22560 := by linarith
  have hV0 : (0 : ℤ) < 23328 * (q : ℤ) ^ 4 + 68256 * (q : ℤ) ^ 3 + 73656 * (q : ℤ) ^ 2 + 34680 * (q : ℤ) + 6000 := by linarith
  exact ((Int.ediv_emod_unique (r := (B : ℤ) - A * (18 * (q : ℤ) ^ 2 + 23 * (q : ℤ) + 6)) (q := 18 * (q : ℤ) ^ 2 + 23 * (q : ℤ) + 6) hpos).2
    ⟨by ring, by linarith, by linarith⟩).1

set_option maxRecDepth 20000 in
lemma val4 (q : ℕ) : (a (6 * q + 4) : ℤ) = 18 * (q : ℤ) ^ 2 + 29 * (q : ℤ) + 11 := by
  have hS : S (6 * q + 4) = T (6 * q + 4 + 2) := rfl
  obtain ⟨h1, h2, h3⟩ := closed (6 * q + 4 + 2)
  have hj := h3
  clear h1 h3
  unfold a
  rw [hS]
  generalize (T (6 * q + 4 + 2)).esymm 2 = A at h2 ⊢ hj
  generalize (T (6 * q + 4 + 2)).esymm 3 = B at hj ⊢
  push_cast at h2 hj ⊢
  have hA : 48 * (A : ℤ) = 69984 * (q : ℤ) ^ 4 + 272160 * (q : ℤ) ^ 3 + 395496 * (q : ℤ) ^ 2 + 254520 * (q : ℤ) + 61200 := by linear_combination h2
  have hq1 : (0 : ℤ) ≤ (q : ℤ) := Int.natCast_nonneg q
  have hq2 : (0 : ℤ) ≤ (q : ℤ) ^ 2 := pow_nonneg hq1 2
  have hq3 : (0 : ℤ) ≤ (q : ℤ) ^ 3 := pow_nonneg hq1 3
  have hq4 : (0 : ℤ) ≤ (q : ℤ) ^ 4 := pow_nonneg hq1 4
  have hP : (0 : ℤ) < 69984 * (q : ℤ) ^ 4 + 272160 * (q : ℤ) ^ 3 + 395496 * (q : ℤ) ^ 2 + 254520 * (q : ℤ) + 61200 := by linarith
  have hpos : 0 < (A : ℤ) := by linarith
  have hW : 48 * ((B : ℤ) - A * (18 * (q : ℤ) ^ 2 + 29 * (q : ℤ) + 11)) = 6912 * (q : ℤ) ^ 3 + 20160 * (q : ℤ) ^ 2 + 19488 * (q : ℤ) + 6240 := by
    linear_combination hj - (18 * (q : ℤ) ^ 2 + 29 * (q : ℤ) + 11) * h2
  have hV : 48 * ((A : ℤ) - ((B : ℤ) - A * (18 * (q : ℤ) ^ 2 + 29 * (q : ℤ) + 11))) = 69984 * (q : ℤ) ^ 4 + 265248 * (q : ℤ) ^ 3 + 375336 * (q : ℤ) ^ 2 + 235032 * (q : ℤ) + 54960 := by
    linear_combination (1 + (18 * (q : ℤ) ^ 2 + 29 * (q : ℤ) + 11)) * h2 - hj
  have hW0 : (0 : ℤ) ≤ 6912 * (q : ℤ) ^ 3 + 20160 * (q : ℤ) ^ 2 + 19488 * (q : ℤ) + 6240 := by linarith
  have hV0 : (0 : ℤ) < 69984 * (q : ℤ) ^ 4 + 265248 * (q : ℤ) ^ 3 + 375336 * (q : ℤ) ^ 2 + 235032 * (q : ℤ) + 54960 := by linarith
  exact ((Int.ediv_emod_unique (r := (B : ℤ) - A * (18 * (q : ℤ) ^ 2 + 29 * (q : ℤ) + 11)) (q := 18 * (q : ℤ) ^ 2 + 29 * (q : ℤ) + 11) hpos).2
    ⟨by ring, by linarith, by linarith⟩).1

set_option maxRecDepth 20000 in
lemma val5 (q : ℕ) : (a (6 * q + 5) : ℤ) = 18 * (q : ℤ) ^ 2 + 35 * (q : ℤ) + 16 := by
  have hS : S (6 * q + 5) = T (6 * q + 5 + 2) := rfl
  obtain ⟨h1, h2, h3⟩ := closed (6 * q + 5 + 2)
  have hj := h3
  clear h1 h3
  unfold a
  rw [hS]
  generalize (T (6 * q + 5 + 2)).esymm 2 = A at h2 ⊢ hj
  generalize (T (6 * q + 5 + 2)).esymm 3 = B at hj ⊢
  push_cast at h2 hj ⊢
  have hA : 48 * (A : ℤ) = 69984 * (q : ℤ) ^ 4 + 318816 * (q : ℤ) ^ 3 + 543240 * (q : ℤ) ^ 2 + 410328 * (q : ℤ) + 115920 := by linear_combination h2
  have hq1 : (0 : ℤ) ≤ (q : ℤ) := Int.natCast_nonneg q
  have hq2 : (0 : ℤ) ≤ (q : ℤ) ^ 2 := pow_nonneg hq1 2
  have hq3 : (0 : ℤ) ≤ (q : ℤ) ^ 3 := pow_nonneg hq1 3
  have hq4 : (0 : ℤ) ≤ (q : ℤ) ^ 4 := pow_nonneg hq1 4
  have hP : (0 : ℤ) < 69984 * (q : ℤ) ^ 4 + 318816 * (q : ℤ) ^ 3 + 543240 * (q : ℤ) ^ 2 + 410328 * (q : ℤ) + 115920 := by linarith
  have hpos : 0 < (A : ℤ) := by linarith
  have hW : 48 * ((B : ℤ) - A * (18 * (q : ℤ) ^ 2 + 35 * (q : ℤ) + 16)) = 23328 * (q : ℤ) ^ 4 + 113184 * (q : ℤ) ^ 3 + 204696 * (q : ℤ) ^ 2 + 163560 * (q : ℤ) + 48720 := by
    linear_combination hj - (18 * (q : ℤ) ^ 2 + 35 * (q : ℤ) + 16) * h2
  have hV : 48 * ((A : ℤ) - ((B : ℤ) - A * (18 * (q : ℤ) ^ 2 + 35 * (q : ℤ) + 16))) = 46656 * (q : ℤ) ^ 4 + 205632 * (q : ℤ) ^ 3 + 338544 * (q : ℤ) ^ 2 + 246768 * (q : ℤ) + 67200 := by
    linear_combination (1 + (18 * (q : ℤ) ^ 2 + 35 * (q : ℤ) + 16)) * h2 - hj
  have hW0 : (0 : ℤ) ≤ 23328 * (q : ℤ) ^ 4 + 113184 * (q : ℤ) ^ 3 + 204696 * (q : ℤ) ^ 2 + 163560 * (q : ℤ) + 48720 := by linarith
  have hV0 : (0 : ℤ) < 46656 * (q : ℤ) ^ 4 + 205632 * (q : ℤ) ^ 3 + 338544 * (q : ℤ) ^ 2 + 246768 * (q : ℤ) + 67200 := by linarith
  exact ((Int.ediv_emod_unique (r := (B : ℤ) - A * (18 * (q : ℤ) ^ 2 + 35 * (q : ℤ) + 16)) (q := 18 * (q : ℤ) ^ 2 + 35 * (q : ℤ) + 16) hpos).2
    ⟨by ring, by linarith, by linarith⟩).1

set_option maxRecDepth 20000 in
lemma val6 (q : ℕ) : (a (6 * q + 6) : ℤ) = 18 * (q : ℤ) ^ 2 + 41 * (q : ℤ) + 22 := by
  have hS : S (6 * q + 6) = T (6 * q + 6 + 2) := rfl
  obtain ⟨h1, h2, h3⟩ := closed (6 * q + 6 + 2)
  have hj := h3
  clear h1 h3
  unfold a
  rw [hS]
  generalize (T (6 * q + 6 + 2)).esymm 2 = A at h2 ⊢ hj
  generalize (T (6 * q + 6 + 2)).esymm 3 = B at hj ⊢
  push_cast at h2 hj ⊢
  have hA : 48 * (A : ℤ) = 69984 * (q : ℤ) ^ 4 + 365472 * (q : ℤ) ^ 3 + 714312 * (q : ℤ) ^ 2 + 619272 * (q : ℤ) + 200928 := by linear_combination h2
  have hq1 : (0 : ℤ) ≤ (q : ℤ) := Int.natCast_nonneg q
  have hq2 : (0 : ℤ) ≤ (q : ℤ) ^ 2 := pow_nonneg hq1 2
  have hq3 : (0 : ℤ) ≤ (q : ℤ) ^ 3 := pow_nonneg hq1 3
  have hq4 : (0 : ℤ) ≤ (q : ℤ) ^ 4 := pow_nonneg hq1 4
  have hP : (0 : ℤ) < 69984 * (q : ℤ) ^ 4 + 365472 * (q : ℤ) ^ 3 + 714312 * (q : ℤ) ^ 2 + 619272 * (q : ℤ) + 200928 := by linarith
  have hpos : 0 < (A : ℤ) := by linarith
  have hW : 48 * ((B : ℤ) - A * (18 * (q : ℤ) ^ 2 + 41 * (q : ℤ) + 22)) = 46656 * (q : ℤ) ^ 4 + 250560 * (q : ℤ) ^ 3 + 503280 * (q : ℤ) ^ 2 + 448080 * (q : ℤ) + 149184 := by
    linear_combination hj - (18 * (q : ℤ) ^ 2 + 41 * (q : ℤ) + 22) * h2
  have hV : 48 * ((A : ℤ) - ((B : ℤ) - A * (18 * (q : ℤ) ^ 2 + 41 * (q : ℤ) + 22))) = 23328 * (q : ℤ) ^ 4 + 114912 * (q : ℤ) ^ 3 + 211032 * (q : ℤ) ^ 2 + 171192 * (q : ℤ) + 51744 := by
    linear_combination (1 + (18 * (q : ℤ) ^ 2 + 41 * (q : ℤ) + 22)) * h2 - hj
  have hW0 : (0 : ℤ) ≤ 46656 * (q : ℤ) ^ 4 + 250560 * (q : ℤ) ^ 3 + 503280 * (q : ℤ) ^ 2 + 448080 * (q : ℤ) + 149184 := by linarith
  have hV0 : (0 : ℤ) < 23328 * (q : ℤ) ^ 4 + 114912 * (q : ℤ) ^ 3 + 211032 * (q : ℤ) ^ 2 + 171192 * (q : ℤ) + 51744 := by linarith
  exact ((Int.ediv_emod_unique (r := (B : ℤ) - A * (18 * (q : ℤ) ^ 2 + 41 * (q : ℤ) + 22)) (q := 18 * (q : ℤ) ^ 2 + 41 * (q : ℤ) + 22) hpos).2
    ⟨by ring, by linarith, by linarith⟩).1

lemma va1 : a 1 = 1 := by
  have h := val1 0
  norm_num at h
  exact_mod_cast h

lemma va2 : a 2 = 3 := by
  have h := val2 0
  norm_num at h
  exact_mod_cast h

lemma va3 : a 3 = 6 := by
  have h := val3 0
  norm_num at h
  exact_mod_cast h

lemma va4 : a 4 = 11 := by
  have h := val4 0
  norm_num at h
  exact_mod_cast h

lemma va5 : a 5 = 16 := by
  have h := val5 0
  norm_num at h
  exact_mod_cast h

lemma rec (n : ℕ) (hn : 6 ≤ n) : (a n : ℤ) = 2 * (a (n - 1) : ℤ) - (a (n - 2) : ℤ) + (a (n - 3) : ℤ) - 2 * (a (n - 4) : ℤ) + (a (n - 5) : ℤ) := by
  obtain ⟨q, s, hs, hq⟩ : ∃ q s, s < 6 ∧ n = 6 * q + s + 6 :=
    ⟨(n - 6) / 6, (n - 6) % 6, Nat.mod_lt _ (by norm_num), by omega⟩
  interval_cases s
  · have e0 : n = 6 * q + 6 := by omega
    have e1 : n - 1 = 6 * q + 5 := by omega
    have e2 : n - 2 = 6 * q + 4 := by omega
    have e3 : n - 3 = 6 * q + 3 := by omega
    have e4 : n - 4 = 6 * q + 2 := by omega
    have e5 : n - 5 = 6 * q + 1 := by omega
    rw [e1, e2, e3, e4, e5, e0]
    rw [val6 q, val5 q, val4 q, val3 q, val2 q, val1 q]
    push_cast
    ring
  · have e0 : n = 6 * (q + 1) + 1 := by omega
    have e1 : n - 1 = 6 * q + 6 := by omega
    have e2 : n - 2 = 6 * q + 5 := by omega
    have e3 : n - 3 = 6 * q + 4 := by omega
    have e4 : n - 4 = 6 * q + 3 := by omega
    have e5 : n - 5 = 6 * q + 2 := by omega
    rw [e1, e2, e3, e4, e5, e0]
    rw [val1 (q + 1), val6 q, val5 q, val4 q, val3 q, val2 q]
    push_cast
    ring
  · have e0 : n = 6 * (q + 1) + 2 := by omega
    have e1 : n - 1 = 6 * (q + 1) + 1 := by omega
    have e2 : n - 2 = 6 * q + 6 := by omega
    have e3 : n - 3 = 6 * q + 5 := by omega
    have e4 : n - 4 = 6 * q + 4 := by omega
    have e5 : n - 5 = 6 * q + 3 := by omega
    rw [e1, e2, e3, e4, e5, e0]
    rw [val2 (q + 1), val1 (q + 1), val6 q, val5 q, val4 q, val3 q]
    push_cast
    ring
  · have e0 : n = 6 * (q + 1) + 3 := by omega
    have e1 : n - 1 = 6 * (q + 1) + 2 := by omega
    have e2 : n - 2 = 6 * (q + 1) + 1 := by omega
    have e3 : n - 3 = 6 * q + 6 := by omega
    have e4 : n - 4 = 6 * q + 5 := by omega
    have e5 : n - 5 = 6 * q + 4 := by omega
    rw [e1, e2, e3, e4, e5, e0]
    rw [val3 (q + 1), val2 (q + 1), val1 (q + 1), val6 q, val5 q, val4 q]
    push_cast
    ring
  · have e0 : n = 6 * (q + 1) + 4 := by omega
    have e1 : n - 1 = 6 * (q + 1) + 3 := by omega
    have e2 : n - 2 = 6 * (q + 1) + 2 := by omega
    have e3 : n - 3 = 6 * (q + 1) + 1 := by omega
    have e4 : n - 4 = 6 * q + 6 := by omega
    have e5 : n - 5 = 6 * q + 5 := by omega
    rw [e1, e2, e3, e4, e5, e0]
    rw [val4 (q + 1), val3 (q + 1), val2 (q + 1), val1 (q + 1), val6 q, val5 q]
    push_cast
    ring
  · have e0 : n = 6 * (q + 1) + 5 := by omega
    have e1 : n - 1 = 6 * (q + 1) + 4 := by omega
    have e2 : n - 2 = 6 * (q + 1) + 3 := by omega
    have e3 : n - 3 = 6 * (q + 1) + 2 := by omega
    have e4 : n - 4 = 6 * (q + 1) + 1 := by omega
    have e5 : n - 5 = 6 * q + 6 := by omega
    rw [e1, e2, e3, e4, e5, e0]
    rw [val5 (q + 1), val4 (q + 1), val3 (q + 1), val2 (q + 1), val1 (q + 1), val6 q]
    push_cast
    ring


lemma esymm_cast (s : Multiset ℕ) (k : ℕ) :
    (s.map (fun i : ℕ => (i : ℤ))).esymm k = ((s.esymm k : ℕ) : ℤ) := by
  simp only [Multiset.esymm, Multiset.powersetCard_map, Multiset.map_map, Function.comp,
    Nat.cast_multiset_sum, Nat.cast_multiset_prod]

lemma S_bridge (n : ℕ) : OMA.S_oeis_a024401.S n = (S n).map (fun i : ℕ => (i : ℤ)) := by
  unfold OMA.S_oeis_a024401.S S
  rw [Multiset.map_map]
  refine Multiset.map_congr rfl (fun i _ => ?_)
  simp

lemma a_bridge (n : ℕ) : OMA.S_oeis_a024401.a n = ((a n : ℕ) : ℤ) := by
  unfold OMA.S_oeis_a024401.a a
  rw [S_bridge, esymm_cast, esymm_cast]
  rw [show ((((S n).esymm 2 : ℕ) : ℤ) : ℚ) = (((S n).esymm 2 : ℕ) : ℚ) by push_cast; rfl,
    Rat.floor_intCast_div_natCast, Int.natCast_div]

lemma va0 : a 0 = 0 := by
  decide

end OMA.P024401

theorem OMA.solution : type_of% @OMA.S_oeis_a024401.main := by
  have hfun : OMA.S_oeis_a024401.a = fun n => ((OMA.P024401.a n : ℕ) : ℤ) :=
    funext OMA.P024401.a_bridge
  have part1 := OMA.P024401.rec
  refine ⟨?_, ?_⟩
  · intro n hn
    simp only [OMA.P024401.a_bridge]
    exact part1 n hn
  rw [hfun]
  have key : -(PowerSeries.C (1 : ℤ) * PowerSeries.mk (fun n => ((OMA.P024401.a n : ℕ) : ℤ)))
      + (PowerSeries.C (2 : ℤ) * (PowerSeries.mk (fun n => ((OMA.P024401.a n : ℕ) : ℤ)) * PowerSeries.X ^ 1))
      - (PowerSeries.C (1 : ℤ) * (PowerSeries.mk (fun n => ((OMA.P024401.a n : ℕ) : ℤ)) * PowerSeries.X ^ 2))
      + (PowerSeries.C (1 : ℤ) * (PowerSeries.mk (fun n => ((OMA.P024401.a n : ℕ) : ℤ)) * PowerSeries.X ^ 3))
      - (PowerSeries.C (2 : ℤ) * (PowerSeries.mk (fun n => ((OMA.P024401.a n : ℕ) : ℤ)) * PowerSeries.X ^ 4))
      + (PowerSeries.C (1 : ℤ) * (PowerSeries.mk (fun n => ((OMA.P024401.a n : ℕ) : ℤ)) * PowerSeries.X ^ 5))
      - (-(PowerSeries.X ^ 1 * PowerSeries.C (1 : ℤ))
      - (PowerSeries.X ^ 2 * PowerSeries.C (1 : ℤ))
      - (PowerSeries.X ^ 3 * PowerSeries.C (1 : ℤ))
      - (PowerSeries.X ^ 4 * PowerSeries.C (1 : ℤ))
      + (PowerSeries.X ^ 5 * PowerSeries.C (1 : ℤ))) = 0 := by
    ext n
    simp only [map_add, map_sub, map_neg, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_X_pow',
      PowerSeries.coeff_mk, PowerSeries.coeff_mul_C, PowerSeries.coeff_X_pow, PowerSeries.coeff_X,
      PowerSeries.coeff_C, map_zero]
    rcases Nat.lt_or_ge n 6 with hlt | hge
    · interval_cases n <;> norm_num [OMA.P024401.va0, OMA.P024401.va1, OMA.P024401.va2, OMA.P024401.va3, OMA.P024401.va4, OMA.P024401.va5]
    · obtain ⟨m, rfl⟩ : ∃ m, n = m + 6 := ⟨n - 6, by omega⟩
      have h := part1 (m + 6) (by omega)
      have z1 : ¬ (m + 6 = 1) := by omega
      have z2 : ¬ (m + 6 = 2) := by omega
      have z3 : ¬ (m + 6 = 3) := by omega
      have z4 : ¬ (m + 6 = 4) := by omega
      have z5 : ¬ (m + 6 = 5) := by omega
      have w1 : 1 ≤ m + 6 := by omega
      have w2 : 2 ≤ m + 6 := by omega
      have w3 : 3 ≤ m + 6 := by omega
      have w4 : 4 ≤ m + 6 := by omega
      have w5 : 5 ≤ m + 6 := by omega
      simp only [z1, z2, z3, z4, z5, w1, w2, w3, w4, w5, if_true, if_false, zero_mul, mul_zero, add_zero, sub_zero]
      linear_combination (-1) * h
  simp only [map_ofNat, map_one] at key
  linear_combination key
