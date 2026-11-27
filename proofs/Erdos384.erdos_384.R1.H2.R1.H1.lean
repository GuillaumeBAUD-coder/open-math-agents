import OMAReductions.R_Erdos384_erdos_384_R1_H2_R1
import Mathlib.Data.Nat.Choose.Factorization
import Mathlib.Tactic.IntervalCases

/-! Kummer's carry criterion certifies the finite range in Ecklund's theorem.
The list stores each prime power together with its base and exponent. -/

namespace Erdos384Finite

private def powers : List (ℕ × ℕ × ℕ) :=
  [(2,1,2),(2,2,4),(2,3,8),(2,4,16),(2,5,32),(2,6,64),
   (3,1,3),(3,2,9),(3,3,27),(3,4,81),(5,1,5),(5,2,25),(5,3,125),
   (7,1,7),(7,2,49),(7,3,343),(11,1,11),(11,2,121),(13,1,13),
   (13,2,169),(17,1,17),(17,2,289),(19,1,19),(23,1,23),(29,1,29)]

private lemma powers_valid : powers.all (fun (p,e,q) =>
    decide (p.Prime ∧ 0 < e ∧ p^e = q)) = true := by decide +kernel

private def check (k n : ℕ) := powers.any fun (p,_,q) =>
  decide (2*p ≤ n ∧ q ≤ k%q + (n-k)%q)

private def row (k : ℕ) :=
  (List.range (k*k+1)).all fun n => decide (n < 2*k) || check k n

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private lemma verified (k : ℕ) (hk : 4 ≤ k) (hk' : k < 60) : row k = true := by
  interval_cases k <;> decide +kernel

end Erdos384Finite

open Erdos384Finite in
theorem OMA.solution : OMA.R_Erdos384_erdos_384_R1_H2_R1.H1 := by
  intro n k hk hk' hn hkn
  have ok := List.all_eq_true.mp (verified k hk hk') n (List.mem_range.mpr (by omega))
  simp only [Bool.or_eq_true, decide_eq_true_eq] at ok
  obtain ⟨⟨p,e,q⟩,hc,found⟩ := List.any_eq_true.mp (ok.resolve_left (by omega))
  obtain ⟨hp,he,rfl⟩ : p.Prime ∧ 0 < e ∧ p^e = q :=
    of_decide_eq_true (List.all_eq_true.mp powers_valid _ hc)
  obtain ⟨hsmall,hcarry⟩ : 2*p ≤ n ∧ p^e ≤ k%(p^e) + (n-k)%(p^e) := of_decide_eq_true found
  refine ⟨p,hp,Nat.dvd_of_factorization_pos ?_,hsmall⟩
  rw [Nat.factorization_choose (b := max e (Nat.log p n)+1) hp (by omega) (by omega)]
  exact (Finset.card_pos.mpr ⟨e, Finset.mem_filter.mpr
    ⟨Finset.mem_Ico.mpr ⟨he,by omega⟩,hcarry⟩⟩).ne'
