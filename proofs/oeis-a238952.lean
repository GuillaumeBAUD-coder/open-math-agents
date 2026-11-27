import OMAStatements.S_oeis_a238952
import Mathlib

-- Problem: oeis-a238952
-- Credit: @JamesSlash (the owner of the agent is credited as the solver)

namespace OMA.P238952

lemma ind (n i : ℕ) (hn : 1 ≤ n) : n / i - (n - 1) / i = if i ∣ n then 1 else 0 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [Nat.succ_div]
  simp only [Nat.add_sub_cancel]
  split_ifs <;> omega

lemma card_proper (b : ℕ) (hb : b ≠ 0) : b.properDivisors.card + 1 = b.divisors.card := by
  rw [← Nat.cons_self_properDivisors hb, Finset.card_cons]

lemma key (n : ℕ) (hn : 1 ≤ n) :
    ∑ i ∈ Finset.Icc 1 (n/2), i.divisors.card * (n/i - (n-1)/i)
      = ∑ i ∈ n.properDivisors, i.divisors.card := by
  have h1 : ∀ i ∈ Finset.Icc 1 (n/2), i.divisors.card * (n/i - (n-1)/i)
      = if i ∣ n then i.divisors.card else 0 := by
    intro i _
    rw [ind n i hn]; split_ifs <;> simp
  rw [Finset.sum_congr rfl h1, ← Finset.sum_filter]
  apply Finset.sum_congr _ (fun _ _ => rfl)
  ext i
  simp only [Finset.mem_filter, Finset.mem_Icc, Nat.mem_properDivisors]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩
    exact ⟨h3, by omega⟩
  · rintro ⟨h3, h4⟩
    refine ⟨⟨Nat.pos_of_dvd_of_pos h3 hn |> fun h => h, ?_⟩, h3⟩
    obtain ⟨k, hk⟩ := h3
    rcases k with _ | _ | k
    · omega
    · omega
    · rw [Nat.le_div_iff_mul_le (by norm_num)]
      rw [hk]; nlinarith

theorem sol : type_of% @OMA.S_oeis_a238952.main := by
  intro n hn
  rw [key n hn, OMA.S_oeis_a238952.arcs]
  have hn0 : n ≠ 0 := by omega
  rw [← Nat.cons_self_properDivisors hn0, Finset.sum_cons, Finset.card_eq_sum_ones n.properDivisors,
    add_comm, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro b hb
  have hb0 : b ≠ 0 := by
    rintro rfl; simp at hb; omega
  exact card_proper b hb0

end OMA.P238952

theorem OMA.solution : type_of% @OMA.S_oeis_a238952.main := OMA.P238952.sol
