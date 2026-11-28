import OMAStatements.S_oeis_a203470
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic

namespace OMA.P_oeis_a203470

open OMA.S_oeis_a203470

private lemma factorial_dvd_prod_consec (m k : ℕ) :
    k.factorial ∣ ∏ r ∈ Finset.range k, (m + 1 + r) := by
  have heq : ∏ r ∈ Finset.range k, (m + 1 + r) = k.factorial * Nat.choose (m + k) k := by
    induction k with
    | zero => simp
    | succ k ih =>
      rw [Finset.prod_range_succ, ih]
      have hch : (k + 1) * Nat.choose (m + (k + 1)) (k + 1) = (m + 1 + k) * Nat.choose (m + k) k := by
        have h := Nat.add_one_mul_choose_eq (m + k) k
        rw [show m + k + 1 = m + (k + 1) by omega] at h
        linarith
      calc k.factorial * Nat.choose (m + k) k * (m + 1 + k)
          = k.factorial * ((m + 1 + k) * Nat.choose (m + k) k) := by ring
        _ = k.factorial * ((k + 1) * Nat.choose (m + (k + 1)) (k + 1)) := by rw [← hch]
        _ = (k + 1).factorial * Nat.choose (m + (k + 1)) (k + 1) := by
            rw [Nat.factorial_succ]; ring
  exact ⟨Nat.choose (m + k) k, heq⟩

private lemma a203470_succ (n : ℕ) (hn : 1 ≤ n) :
    a203470 (n + 1) = a203470 n * ∏ i ∈ Finset.Ico 2 (n + 2), (i + (n + 2)) := by
  unfold a203470
  have hmem : n + 2 ∈ Finset.Icc 2 (n + 2) := Finset.mem_Icc.mpr ⟨by omega, le_rfl⟩
  have herase : (Finset.Icc 2 (n + 2)).erase (n + 2) = Finset.Icc 2 (n + 1) := by
    ext j; simp only [Finset.mem_erase, Finset.mem_Icc]; omega
  rw [← Finset.mul_prod_erase _ _ hmem, herase, mul_comm]

private lemma superfactorial_succ (m : ℕ) :
    superfactorial (m + 1) = superfactorial m * (m + 1).factorial := by
  unfold superfactorial
  have hmem : m + 1 ∈ Finset.Icc 1 (m + 1) := Finset.mem_Icc.mpr ⟨by omega, le_rfl⟩
  have herase : (Finset.Icc 1 (m + 1)).erase (m + 1) = Finset.Icc 1 m := by
    ext k; simp only [Finset.mem_erase, Finset.mem_Icc]; omega
  rw [← Finset.mul_prod_erase _ _ hmem, herase, mul_comm]

private lemma prove_main :
    (∀ n : ℕ, 1 ≤ n → a203470 n ∣ a203470 (n + 1)) ∧
    (∀ n : ℕ, 1 ≤ n → superfactorial (n - 1) ∣ a203470 n) := by
  refine ⟨?_, ?_⟩
  · intro n hn
    exact ⟨_, a203470_succ n hn⟩
  · intro n hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    clear hn
    rw [show m + 1 - 1 = m by omega]
    induction m with
    | zero =>
      simp [superfactorial, a203470]
    | succ m ih =>
      rw [superfactorial_succ, a203470_succ (m + 1) (by omega)]
      apply mul_dvd_mul ih
      have hprod : ∏ i ∈ Finset.Ico 2 (m + 3), (i + (m + 3)) =
          ∏ r ∈ Finset.range (m + 1), (m + 4 + 1 + r) := by
        apply Finset.prod_bij (fun i _ => i - 2)
        · intro i hi; rw [Finset.mem_Ico] at hi; rw [Finset.mem_range]; omega
        · intro i1 h1 i2 h2 heq; rw [Finset.mem_Ico] at h1 h2; omega
        · intro r hr; rw [Finset.mem_range] at hr
          exact ⟨r + 2, Finset.mem_Ico.mpr ⟨by omega, by omega⟩, by omega⟩
        · intro i hi; rw [Finset.mem_Ico] at hi; omega
      rw [hprod]
      exact factorial_dvd_prod_consec (m + 4) (m + 1)

end OMA.P_oeis_a203470

theorem OMA.solution : type_of% @OMA.S_oeis_a203470.main :=
  OMA.P_oeis_a203470.prove_main
