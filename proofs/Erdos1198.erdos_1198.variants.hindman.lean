import FormalConjectures.ErdosProblems.«1198»

/-! # Increasing block sums in Hindman's theorem -/
-- Credit: @steveDOTdigital

open Hindman Finset

namespace OMA.HindmanProof

-- Each block contains more positive terms than the sum of all previous terms.
private def cut (q : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | n + 1 => cut q n + (∑ j ∈ range (cut q n), q j) + 1

private theorem increasing_blocks (q : ℕ → ℕ) (hq : ∀ i, 0 < q i) :
    ∃ B : ℕ → Finset ℕ, (∀ n, (B n).Nonempty) ∧
      (∀ i j, i < j → Disjoint (B i) (B j)) ∧
      StrictMono (fun i => ∑ j ∈ B i, q j) := by
  let B (i : ℕ) := Ico (cut q i) (cut q (i + 1))
  have step (i : ℕ) : cut q i < cut q (i + 1) := by rw [cut]; omega
  have mono := strictMono_nat_of_lt_succ step
  refine ⟨B, fun i => ⟨cut q i, mem_Ico.2 ⟨le_rfl, step i⟩⟩, ?_, ?_⟩
  · intro i j hij
    apply disjoint_left.2
    intro x hx hy
    exact (mem_Ico.1 hx).2.not_ge ((mono.monotone hij).trans (mem_Ico.1 hy).1)
  · apply strictMono_nat_of_lt_succ
    intro i
    have lower (n : ℕ) : (B n).card ≤ ∑ j ∈ B n, q j := by
      calc
        _ = ∑ _j ∈ B n, 1 := by simp
        _ ≤ _ := sum_le_sum fun j _ => hq j
    have upper : ∑ j ∈ B i, q j ≤ ∑ j ∈ range (cut q (i+1)), q j := by
      apply sum_le_sum_of_subset_of_nonneg
      · exact fun j hj => mem_range.2 (mem_Ico.1 hj).2
      · intros; omega
    have hlen := lower (i+1)
    change (Ico _ _).card ≤ _ at hlen
    have endpt : cut q (i+1+1) = cut q (i+1) + (∑ j ∈ range (cut q (i+1)), q j) + 1 := rfl
    rw [Nat.card_Ico, endpt] at hlen
    omega

end OMA.HindmanProof

theorem OMA.solution : type_of% @Erdos1198.erdos_1198.variants.hindman := by
  classical
  intro c
  let part (d : Fin 2) := {n : ℕ | 0 < n ∧ c n = d}
  let ones : Stream' ℕ := fun _ => 1
  have cover : FS ones ⊆ ⋃₀ Set.range part := by
    intro n hn
    have pos {s : Stream' ℕ} (hall : ∀ i, 0 < s.get i) {m} (hm : m ∈ FS s) : 0 < m := by
      induction hm with
      | head' s => exact hall 0
      | tail' s m _ ih => exact ih (fun i => hall (i+1))
      | cons' s m _ ih => exact Nat.add_pos_left (hall 0) _
    exact Set.mem_sUnion.2 ⟨part (c n), ⟨c n, rfl⟩, pos (s := ones) (fun _ => Nat.zero_lt_one) hn, rfl⟩
  obtain ⟨_, ⟨d, rfl⟩, s, hs⟩ := FS_partition_regular ones _ (Set.finite_range part) cover
  obtain ⟨B, hB, hdisj, hmono⟩ := OMA.HindmanProof.increasing_blocks s.get
    (fun i => (hs (FS.singleton s i)).1)
  refine ⟨fun i => ∑ j ∈ B i, s.get j, hmono, ?_, d, ?_⟩
  · exact Finset.sum_pos (fun j _ => (hs (FS.singleton s j)).1) (hB 0)
  · intro T hT
    have hne : (T.biUnion B).Nonempty := by
      obtain ⟨t, ht⟩ := hT
      obtain ⟨j, hj⟩ := hB t
      exact ⟨j, mem_biUnion.2 ⟨t, ht, hj⟩⟩
    have hit := (hs (FS.finsetSum s _ hne)).2
    rw [sum_biUnion] at hit
    · exact hit
    · intro i _ j _ hij
      rcases lt_or_gt_of_ne hij with h | h
      · exact hdisj i j h
      · exact (hdisj j i h).symm
