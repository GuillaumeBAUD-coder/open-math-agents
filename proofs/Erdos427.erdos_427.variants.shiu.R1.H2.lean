import OMAReductions.R_Erdos427_erdos_427_variants_shiu_R1

-- Step Erdos427.erdos_427.variants.shiu.R1.H2: hypothesis H2 of reduction Erdos427.erdos_427.variants.shiu.R1

/-!
A pigeonhole count. Scan `[l, l + n)` from the left, keeping the length `t` of the current run of
good indices. If no run of `k` good indices exists then `t ≤ k - 1` throughout, every bad index
resets `t`, and so `#good ≤ (k - 1) * #bad + t ≤ (k - 1) * (#bad + 1)`.
-/

namespace OMA

theorem run_aux (good : ℕ → Bool) (l k : ℕ) (hk : 1 ≤ k) : ∀ n : ℕ,
    (¬ ∃ m : ℕ, l ≤ m ∧ m + k ≤ l + n ∧ ∀ i ∈ Finset.Ico m (m + k), good i = true) →
    ∃ t : ℕ, t ≤ k - 1 ∧ t ≤ n ∧ (∀ i : ℕ, l + n - t ≤ i → i < l + n → good i = true) ∧
      (∑ i ∈ Finset.Ico l (l + n), (if good i = true then 1 else 0)) ≤
        (k - 1) * (∑ i ∈ Finset.Ico l (l + n), (if good i = false then 1 else 0)) + t := by
  intro n
  induction n with
  | zero =>
    intro _
    exact ⟨0, Nat.zero_le _, le_refl 0, fun i h1 h2 => by omega, by simp⟩
  | succ n ih =>
    intro hno
    have hno' : ¬ ∃ m : ℕ, l ≤ m ∧ m + k ≤ l + n ∧
        ∀ i ∈ Finset.Ico m (m + k), good i = true := by
      intro h
      obtain ⟨m, h1, h2, h3⟩ := h
      exact hno ⟨m, h1, by omega, h3⟩
    obtain ⟨t, ht1, ht2, ht3, ht4⟩ := ih hno'
    have e1 : (∑ i ∈ Finset.Ico l (l + (n + 1)), (if good i = true then 1 else 0)) =
        (∑ i ∈ Finset.Ico l (l + n), (if good i = true then 1 else 0)) +
          (if good (l + n) = true then 1 else 0) :=
      Finset.sum_Ico_succ_top (Nat.le_add_right l n) _
    have e2 : (∑ i ∈ Finset.Ico l (l + (n + 1)), (if good i = false then 1 else 0)) =
        (∑ i ∈ Finset.Ico l (l + n), (if good i = false then 1 else 0)) +
          (if good (l + n) = false then 1 else 0) :=
      Finset.sum_Ico_succ_top (Nat.le_add_right l n) _
    rw [e1, e2]
    generalize (∑ i ∈ Finset.Ico l (l + n), (if good i = true then 1 else 0)) = G at ht4 ⊢
    generalize (∑ i ∈ Finset.Ico l (l + n), (if good i = false then 1 else 0)) = B at ht4 ⊢
    cases hg : good (l + n) with
    | false =>
      have a1 : (if false = true then 1 else 0 : ℕ) = 0 := by simp
      have a2 : (if false = false then 1 else 0 : ℕ) = 1 := by simp
      rw [a1, a2]
      refine ⟨0, Nat.zero_le _, Nat.zero_le _, fun i h1 h2 => by omega, ?_⟩
      have e : (k - 1) * (B + 1) = (k - 1) * B + (k - 1) := by ring
      rw [e]
      omega
    | true =>
      have a1 : (if true = true then 1 else 0 : ℕ) = 1 := by simp
      have a2 : (if true = false then 1 else 0 : ℕ) = 0 := by simp
      have e0 : B + 0 = B := Nat.add_zero B
      rw [a1, a2, e0]
      by_cases htk : t + 1 ≤ k - 1
      · refine ⟨t + 1, htk, by omega, ?_, by omega⟩
        intro i h1 h2
        by_cases hi : i = l + n
        · rw [hi]
          exact hg
        · exact ht3 i (by omega) (by omega)
      · exfalso
        apply hno
        refine ⟨l + n + 1 - k, by omega, by omega, ?_⟩
        intro i hi
        rw [Finset.mem_Ico] at hi
        by_cases hin : i = l + n
        · rw [hin]
          exact hg
        · exact ht3 i (by omega) (by omega)

end OMA

theorem OMA.solution : OMA.R_Erdos427_erdos_427_variants_shiu_R1.H2 := by
  unfold OMA.R_Erdos427_erdos_427_variants_shiu_R1.H2
  intro good l r k hk h
  by_contra hno
  by_cases hlr : l ≤ r
  · obtain ⟨n, hn⟩ := Nat.exists_eq_add_of_le hlr
    subst hn
    obtain ⟨t, ht1, _, _, ht4⟩ := OMA.run_aux good l k hk n hno
    rw [Finset.card_filter, Finset.card_filter] at h
    generalize (∑ i ∈ Finset.Ico l (l + n), (if good i = true then 1 else 0)) = G at ht4 h
    generalize (∑ i ∈ Finset.Ico l (l + n), (if good i = false then 1 else 0)) = B at ht4 h
    have e : (k - 1) * (B + 1) = (k - 1) * B + (k - 1) := by ring
    rw [e] at h
    omega
  · have he : Finset.Ico l r = ∅ := Finset.Ico_eq_empty (by omega)
    rw [he] at h
    simp at h
