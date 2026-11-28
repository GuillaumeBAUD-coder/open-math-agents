import OMAReductions.R_oeis_a284760_R1
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.Nat.ModEq
import Mathlib.Tactic.NormNum

open Finset

namespace D7PowerSum

lemma pow_mod_two (i k : ℕ) (hk : 0 < k) : i^k % 2 = i%2 := by
  rw [Nat.pow_mod]
  rcases Nat.mod_two_eq_zero_or_one i with hi|hi <;> simp [hi,hk.ne']

lemma four_block_sum (k : ℕ) (hk : 0 < k) (q : ℕ) :
    (∑ i ∈ range (4*q+2), i^k)%2 = 1 := by
  have hp (i : ℕ) : i^k%2=i%2 := pow_mod_two i k hk
  induction q with
  | zero => simp [sum_range_succ,hk.ne']
  | succ q ih =>
    rw [show 4*(q+1)+2=(4*q+2)+4 by omega,sum_range_add,Nat.add_mod,ih]
    norm_num [sum_range_succ,Nat.add_mod,Nat.mul_mod,hp]

theorem parity_obstruction (n : ℕ) (hn : n%4=2) :
    (∑ i ∈ Ico 1 n, i^(n-2))%n^4 ≠ 0 := by
  by_cases hn2 : n=2
  · subst n
    norm_num
  have hk : 0 < n-2 := by omega
  have hr : range n=insert 0 (Ico 1 n) := by
    ext i
    simp only [mem_range,mem_insert,mem_Ico]
    omega
  have he : (∑ i ∈ range n,i^(n-2))=∑ i ∈ Ico 1 n,i^(n-2) := by
    rw [hr,sum_insert (by simp)]
    simp [hk.ne']
  have hs : (∑ i ∈ Ico 1 n,i^(n-2))%2=1 := by
    rw [←he]
    have hn' : n=4*(n/4)+2 := by omega
    have h := four_block_sum (n-2) hk (n/4)
    rw [←hn'] at h
    exact h
  intro hzero
  have hnD : 2 ∣ n := by omega
  have hDn : n^4 ∣ (∑ i ∈ Ico 1 n,i^(n-2)) := Nat.dvd_of_mod_eq_zero hzero
  have hsum : (∑ i ∈ Ico 1 n,i^(n-2))%2=0 :=
    Nat.mod_eq_zero_of_dvd (hnD.trans ((dvd_pow_self n (by decide : 4≠0)).trans hDn))
  omega

end D7PowerSum

theorem OMA.solution : OMA.R_oeis_a284760_R1.H1 := by
  exact D7PowerSum.parity_obstruction
