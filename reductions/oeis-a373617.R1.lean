import OMAStatements.S_oeis_a373617

-- Credit: @yukimiyazaki (agent: Codex, model: GPT-6)

namespace OMA.R_oeis_a373617_R1

open OMA.S_oeis_a373617

/-- Divisors larger than the requested sum cannot occur in its representation. -/
private theorem divisor_gap {p m : ℕ} (hm : m ≤ p)
    (gap : (∑ d ∈ (Finset.range (m+1)).filter (fun d => d ∣ p), d) < m) :
    ¬ IsPractical p := by
  intro hp
  obtain ⟨s, hs, he⟩ := hp.2 m hm
  have sub : s ⊆ (Finset.range (m+1)).filter (fun d => d ∣ p) := by
    intro d hd
    have small : d ≤ ∑ j ∈ s, j :=
      Finset.single_le_sum (f := fun j : ℕ => j) (fun _ _ => Nat.zero_le _) hd
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), (Nat.mem_divisors.mp (hs hd)).1⟩
  have bound := Finset.sum_le_sum_of_subset_of_nonneg (f := fun j : ℕ => j) sub
    (fun _ _ _ => Nat.zero_le _)
  exact (Nat.not_lt_of_ge (he.ge.trans bound)) gap

private theorem exceptional : ¬ IsRepresentable 106878 := by
  rintro ⟨p, k, practical, eqn⟩
  have hk : k < 134 := by
    by_contra! h
    have ht : 134 * (12 * 134 - 10) ≤ k * (12 * k - 10) :=
      Nat.mul_le_mul h (by omega)
    unfold polygonal at eqn
    omega
  let gaps : List ℕ := [13, 2, 32, 2, 4, 2, 505, 2, 4, 2, 16, 2, 40, 2, 8, 2, 4, 2, 509, 2, 4, 2, 8, 2, 13, 2, 16, 2, 4, 2, 281, 2, 4, 2, 32, 2, 13, 2, 8, 2, 4, 2, 61, 2, 4, 2, 8, 2, 40, 2, 64, 2, 4, 2, 29, 2, 4, 2, 16, 2, 13, 2, 8, 2, 4, 2, 404, 2, 4, 2, 8, 2, 13, 2, 16, 2, 4, 2, 29, 2, 4, 2, 256, 2, 364, 2, 8, 2, 4, 2, 61, 2, 4, 2, 8, 2, 13, 2, 32, 2, 4, 2, 92, 2, 4, 2, 16, 2, 13, 2, 8, 2, 4, 2, 253, 2, 4, 2, 8, 2, 40, 2, 16, 2, 4, 2, 29, 2, 4, 2, 32, 2, 13, 2]
  have certified : ∀ i : Fin 134, let p' := 106878 - polygonal i.val
                                  let m := gaps[i.val]!
                                  m ≤ p' ∧ (∑ d ∈ (Finset.range (m+1)).filter (fun d => d ∣ p'), d) < m := by
    decide +kernel
  have pe : p = 106878 - polygonal k := by omega
  obtain ⟨hm, hg⟩ := certified ⟨k,hk⟩
  exact divisor_gap hm hg (pe ▸ practical)

/-- Reproduce the finite range tested by Somu and Tran, starting just above the last exception. -/
def H1 : Prop := ∀ n : ℕ, 106878 < n → n ≤ 10^8 → IsRepresentable n

/-- The remaining infinite range of the practical-plus-14-gonal conjecture. -/
def H2 : Prop := ∀ n : ℕ, 10^8 < n → IsRepresentable n

theorem main : H1 → H2 → type_of% @OMA.S_oeis_a373617.main := by
  intro finiteRange tail
  refine ⟨⟨by decide, exceptional⟩, ?_⟩
  intro n hn
  by_contra! h
  exact hn.2 (if hb : n ≤ 10^8 then finiteRange n h hb else tail n (by omega))

end OMA.R_oeis_a373617_R1
