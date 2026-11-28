import OMAStatements.S_oeis_a190640

/-!
A surviving Cantor interval has precisely a left numerator with ternary
digits 0 and 2. The next gap appends digit 1. Adding one replaces that
last digit by 2 without a carry. This bijection preserves increasing order.
Lean proof by KoaOkano, assisted by Codex.
-/

namespace A190640Proof
open OMA.S_oeis_a190640

private def good (p : ℕ) : Prop := ∀ d ∈ Nat.digits 3 p, d = 0 ∨ d = 2

private theorem append_digit {p d : ℕ} (hp : good p) (hd : d = 0 ∨ d = 2) :
    good (3 * p + d) := by
  by_cases hz : d = 0 ∧ p = 0
  · obtain ⟨rfl, rfl⟩ := hz
    simp [good]
  have ds := Nat.digits_add 3 (by decide) d p (by omega) (by omega)
  intro a ha
  rw [Nat.add_comm (3 * p) d, ds] at ha
  rcases List.mem_cons.mp ha with rfl | ht
  · exact hd
  · exact hp _ ht

private theorem parent_good {p : ℕ} (h : CantorParent p) : good p := by
  induction h with
  | root => simp [good]
  | left _ ih => simpa using append_digit ih (Or.inl (rfl : 0 = 0))
  | right _ ih => exact append_digit ih (Or.inr rfl)

private theorem good_parent (p : ℕ) : good p → CantorParent p := by
  induction p using Nat.strong_induction_on with
  | h p ih =>
    intro hp
    by_cases hz : p = 0
    · simpa [hz] using CantorParent.root
    have pos : 0 < p := Nat.pos_of_ne_zero hz
    have ds := Nat.digits_def' (by decide : 1 < 3) pos
    have lo : p % 3 = 0 ∨ p % 3 = 2 := hp _ (by rw [ds]; simp)
    have rest : good (p / 3) := by
      intro d hd
      apply hp
      rw [ds]
      exact List.mem_cons_of_mem _ hd
    have parent := ih (p / 3) (Nat.div_lt_self pos (by decide)) rest
    rcases lo with h | h
    · convert CantorParent.left parent using 1
      omega
    · convert CantorParent.right parent using 1
      omega

private theorem succ_iff (m : ℕ) : digitTerm (m + 1) ↔ gapNumerator m := by
  constructor
  · rintro ⟨last, digits⟩
    have ds := Nat.digits_def' (by decide : 1 < 3) (Nat.succ_pos m)
    have rest : good ((m + 1) / 3) := by
      intro d hd
      apply digits
      rw [ds]
      exact List.mem_cons_of_mem _ hd
    exact ⟨_, good_parent _ rest, by omega⟩
  · rintro ⟨p, hp, rfl⟩
    exact ⟨by omega, append_digit (parent_good hp) (Or.inr rfl)⟩

private def rightmost : ℕ → ℕ
  | 0 => 0
  | n + 1 => 3 * rightmost n + 2

private theorem right_parent (n : ℕ) : CantorParent (rightmost n) := by
  induction n with
  | zero => exact CantorParent.root
  | succ n ih => exact CantorParent.right ih

private theorem many : (Set.ofPred digitTerm).Infinite := by
  let f : ℕ → ℕ := fun n => 3 * rightmost n + 2
  have mono : StrictMono f := strictMono_nat_of_lt_succ fun n => by simp [f, rightmost]; omega
  refine (Set.infinite_range_of_injective mono.injective).mono ?_
  rintro _ ⟨n, rfl⟩
  exact (succ_iff (3 * rightmost n + 1)).2 ⟨_, right_parent n, rfl⟩

theorem enumeration (i : ℕ) : Nat.nth digitTerm i = Nat.nth gapNumerator i + 1 := by
  have h0 : ¬ digitTerm 0 := by simp [digitTerm]
  have hn : Nat.nth digitTerm i ≠ 0 := by
    intro eq
    have hm := Nat.nth_mem_of_infinite many i
    rw [eq] at hm
    exact h0 hm
  have predicates : (fun m => digitTerm (m + 1)) = gapNumerator := funext fun m => propext (succ_iff m)
  simpa only [predicates] using (Nat.nth_add_one h0 hn).symm

end A190640Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a190640.main := A190640Proof.enumeration
