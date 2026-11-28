import OMAStatements.S_oeis_a193229
import Mathlib.Tactic

namespace OMA.P_oeis_a193229

open OMA.S_oeis_a193229

private lemma a193229_zero_eq_one (n : ℕ) :
    a193229 (n + 1) 0 = a193229 (n + 1) 1 := by
  unfold a193229
  apply Finset.sum_congr rfl
  intro i _
  simp

private lemma a193229_diag (n : ℕ) :
    a193229 n n = n.factorial := by
  induction n with
  | zero => rfl
  | succ n ih =>
    unfold a193229
    rw [Finset.sum_eq_single n]
    · simp only [le_refl, ite_true, ih, Nat.factorial_succ]
    · intro i hi hne
      rw [Finset.mem_range] at hi
      rw [if_neg (by omega)]
    · intro hnot
      exact absurd (Finset.mem_range.mpr (by omega)) hnot

private lemma a193229_step (n k : ℕ) (hk1 : 1 ≤ k) (hkn : k ≤ n) :
    a193229 (n + 1) k = a193229 (n + 1) (k + 1) + k * a193229 n (k - 1) := by
  change (∑ i ∈ Finset.range (n + 1), if k ≤ i + 1 then (i + 1) * a193229 n i else 0) =
    (∑ i ∈ Finset.range (n + 1), if k + 1 ≤ i + 1 then (i + 1) * a193229 n i else 0) +
      k * a193229 n (k - 1)
  have hmem : k - 1 ∈ Finset.range (n + 1) := Finset.mem_range.mpr (by omega)
  rw [← Finset.add_sum_erase _ _ hmem, ← Finset.add_sum_erase _ _ hmem]
  have h1 : (if k ≤ k - 1 + 1 then (k - 1 + 1) * a193229 n (k - 1) else 0) = k * a193229 n (k - 1) := by
    rw [if_pos (by omega), show k - 1 + 1 = k by omega]
  have h2 : (if k + 1 ≤ k - 1 + 1 then (k - 1 + 1) * a193229 n (k - 1) else 0) = 0 := by
    rw [if_neg (by omega)]
  rw [h1, h2, zero_add]
  rw [add_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mem_erase, Finset.mem_range] at hi
  by_cases hki : k ≤ i + 1
  · rw [if_pos hki, if_pos (by omega)]
  · rw [if_neg hki, if_neg (by omega)]

private lemma prove_main :
    ∀ n k : ℕ, k ≤ n →
      2 ^ (n - k) * (n - k).factorial * a193229 n k = (2 * n - k).factorial := by
  intro n
  induction n with
  | zero =>
    intro k hk
    have hk0 : k = 0 := by omega
    subst hk0
    simp [a193229]
  | succ n ih =>
    -- Prove by induction on d = (n + 1) - k
    have haux : ∀ d : ℕ, d ≤ n + 1 →
        2 ^ d * d.factorial * a193229 (n + 1) (n + 1 - d) = (n + 1 + d).factorial := by
      intro d
      induction d with
      | zero =>
        intro _
        simp only [Nat.sub_zero, pow_zero, Nat.factorial_zero, mul_one, one_mul, add_zero]
        exact a193229_diag (n + 1)
      | succ d ihd =>
        intro hd
        by_cases htop : d = n
        · -- Then n + 1 - (d + 1) = 0
          subst d
          have hprev := ihd (by omega)
          have h0 : n + 1 - (n + 1) = 0 := by omega
          have h1 : n + 1 - n = 1 := by omega
          rw [h1] at hprev
          rw [h0, a193229_zero_eq_one]
          calc 2 ^ (n + 1) * (n + 1).factorial * a193229 (n + 1) 1
              = (2 * (n + 1)) * (2 ^ n * n.factorial * a193229 (n + 1) 1) := by
                  rw [pow_succ, Nat.factorial_succ]; ring
            _ = (2 * (n + 1)) * (n + 1 + n).factorial := by rw [hprev]
            _ = (n + 1 + (n + 1)).factorial := by
                  rw [show n + 1 + (n + 1) = (n + 1 + n) + 1 by omega, Nat.factorial_succ]
                  ring
        · -- 1 ≤ k = n + 1 - (d + 1) ≤ n
          set k := n + 1 - (d + 1)
          have hk1 : 1 ≤ k := by omega
          have hkn : k ≤ n := by omega
          have hk_succ : k + 1 = n + 1 - d := by omega
          have hprev := ihd (by omega)
          rw [← hk_succ] at hprev
          have hih := ih (k - 1) (by omega)
          have hsub1 : n - (k - 1) = d + 1 := by omega
          have hsub2 : 2 * n - (k - 1) = n + 1 + d := by omega
          rw [hsub1, hsub2] at hih
          rw [a193229_step n k hk1 hkn, mul_add]
          have hterm1 : 2 ^ (d + 1) * (d + 1).factorial * a193229 (n + 1) (k + 1) =
              2 * (d + 1) * (n + 1 + d).factorial := by
            calc 2 ^ (d + 1) * (d + 1).factorial * a193229 (n + 1) (k + 1)
                = 2 * (d + 1) * (2 ^ d * d.factorial * a193229 (n + 1) (k + 1)) := by
                    rw [pow_succ, Nat.factorial_succ]; ring
              _ = 2 * (d + 1) * (n + 1 + d).factorial := by rw [hprev]
          have hterm2 : 2 ^ (d + 1) * (d + 1).factorial * (k * a193229 n (k - 1)) =
              k * (n + 1 + d).factorial := by
            calc 2 ^ (d + 1) * (d + 1).factorial * (k * a193229 n (k - 1))
                = k * (2 ^ (d + 1) * (d + 1).factorial * a193229 n (k - 1)) := by ring
              _ = k * (n + 1 + d).factorial := by rw [hih]
          rw [hterm1, hterm2]
          have hcoef : 2 * (d + 1) + k = n + 1 + (d + 1) := by omega
          calc 2 * (d + 1) * (n + 1 + d).factorial + k * (n + 1 + d).factorial
              = (2 * (d + 1) + k) * (n + 1 + d).factorial := by ring
            _ = (n + 1 + (d + 1)) * (n + 1 + d).factorial := by rw [hcoef]
            _ = (n + 1 + (d + 1)).factorial := by
                  rw [show n + 1 + (d + 1) = (n + 1 + d) + 1 by omega, Nat.factorial_succ]
    intro k hk
    have h := haux (n + 1 - k) (by omega)
    rw [show n + 1 - (n + 1 - k) = k by omega, show n + 1 + (n + 1 - k) = 2 * (n + 1) - k by omega] at h
    exact h

end OMA.P_oeis_a193229

theorem OMA.solution : type_of% @OMA.S_oeis_a193229.main :=
  OMA.P_oeis_a193229.prove_main
