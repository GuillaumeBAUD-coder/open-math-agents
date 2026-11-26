import FormalConjectures.ErdosProblems.«954»

namespace OMA

open Erdos954

/-- Later stages of the construction do not change the entries already written. -/
theorem rosenAux_stable (i : ℕ) : ∀ k, i ≤ k + 1 → rosenAux k i = rosenAux (i - 1) i := by
  intro k
  induction k with
  | zero =>
    intro h
    have h0 : i - 1 = 0 := by omega
    rw [h0]
  | succ k ih =>
    intro h
    by_cases hi : i = k + 2
    · subst hi
      rfl
    · have h1 : rosenAux (k + 1) i = rosenAux k i := by
        rw [rosenAux]
        simp [hi]
      rw [h1]
      exact ih (by omega)

theorem rosenAux_eq_rosen (k i : ℕ) (h : i ≤ k + 1) : rosenAux k i = rosen i := by
  unfold rosen
  rw [rosenAux_stable i k h, rosenAux_stable i i (by omega)]

theorem pairCount_congr (a b : ℕ → ℕ) (m n : ℕ) (h : ∀ i ≤ m, a i = b i) :
    pairCount a m n = pairCount b m n := by
  unfold pairCount
  congr 1
  apply Finset.filter_congr
  intro p hp
  rw [Finset.mem_product, Finset.mem_range, Finset.mem_range] at hp
  rw [h p.1 (by omega), h p.2 (by omega)]

theorem rosen_succ_succ (k : ℕ) :
    rosen (k + 2) = sInf {n : ℕ | pairCount rosen (k + 1) n < n} := by
  have h1 : rosen (k + 2) = rosenAux (k + 1) (k + 2) :=
    (rosenAux_eq_rosen (k + 1) (k + 2) le_rfl).symm
  have h2 : rosenAux (k + 1) (k + 2) =
      sInf {n : ℕ | pairCount (rosenAux k) (k + 1) n < n} := by
    rw [rosenAux]
    simp
  rw [h1, h2]
  congr 1
  ext n
  simp only [Set.mem_ofPred_eq]
  rw [pairCount_congr (rosenAux k) rosen (k + 1) n (fun i hi => rosenAux_eq_rosen k i hi)]

theorem pairCount_mono_right (a : ℕ → ℕ) (m : ℕ) {n n' : ℕ} (h : n ≤ n') :
    pairCount a m n ≤ pairCount a m n' := by
  unfold pairCount
  apply Finset.card_le_card
  intro p hp
  rw [Finset.mem_filter] at hp ⊢
  exact ⟨hp.1, hp.2.1, hp.2.2.1, le_trans hp.2.2.2 h⟩

theorem pairCount_succ_le (a : ℕ → ℕ) (m n : ℕ) :
    pairCount a m n ≤ pairCount a (m + 1) n := by
  unfold pairCount
  apply Finset.card_le_card
  intro p hp
  rw [Finset.mem_filter, Finset.mem_product, Finset.mem_range, Finset.mem_range] at hp ⊢
  exact ⟨⟨by omega, by omega⟩, hp.2⟩

/-- The pair `(0, m + 1)` is new at stage `m + 1`. -/
theorem pairCount_succ_add_one (a : ℕ → ℕ) (m n : ℕ) (h : a 0 + a (m + 1) ≤ n) :
    pairCount a m n + 1 ≤ pairCount a (m + 1) n := by
  unfold pairCount
  rw [← Finset.card_insert_of_notMem (a := ((0 : ℕ), m + 1))]
  · apply Finset.card_le_card
    intro p hp
    rw [Finset.mem_insert] at hp
    rcases hp with rfl | hp
    · simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range]
      exact ⟨⟨by omega, by omega⟩, by omega, by omega, h⟩
    · rw [Finset.mem_filter, Finset.mem_product, Finset.mem_range, Finset.mem_range] at hp ⊢
      exact ⟨⟨by omega, by omega⟩, hp.2⟩
  · simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range]
    omega

theorem rosen_zero' : rosen 0 = 0 := by
  simp [rosen, rosenAux]

theorem rosen_one' : rosen 1 = 1 := by
  simp [rosen, rosenAux]

theorem le_pairCount : ∀ k n : ℕ, n ≤ k → n ≤ pairCount rosen k n := by
  intro k
  induction k with
  | zero =>
    intro n hn
    omega
  | succ k ih =>
    intro n hn
    rcases Nat.lt_or_ge n (k + 1) with hlt | hge
    · exact le_trans (ih n (by omega)) (pairCount_succ_le rosen k n)
    · have hn' : n = k + 1 := by omega
      subst hn'
      rcases k with _ | j
      · have h : pairCount rosen 0 1 + 1 ≤ pairCount rosen 1 1 :=
          pairCount_succ_add_one rosen 0 1 (by
            show rosen 0 + rosen 1 ≤ 1
            rw [rosen_zero', rosen_one'])
        show 1 ≤ pairCount rosen 1 1
        omega
      · by_cases hS : pairCount rosen (j + 1) (j + 2) < j + 2
        · have hmem : (j + 2) ∈ {n : ℕ | pairCount rosen (j + 1) n < n} := hS
          have hle : sInf {n : ℕ | pairCount rosen (j + 1) n < n} ≤ j + 2 := Nat.sInf_le hmem
          have hin : sInf {n : ℕ | pairCount rosen (j + 1) n < n} ∈
              {n : ℕ | pairCount rosen (j + 1) n < n} := Nat.sInf_mem ⟨_, hmem⟩
          rw [← rosen_succ_succ] at hle hin
          have hin' : pairCount rosen (j + 1) (rosen (j + 2)) < rosen (j + 2) := hin
          have hge' : j + 2 ≤ rosen (j + 2) := by
            by_contra hc
            have := ih (rosen (j + 2)) (by omega)
            omega
          have heq : rosen (j + 2) = j + 2 := by omega
          have h3 : pairCount rosen (j + 1) (j + 2) + 1 ≤ pairCount rosen (j + 2) (j + 2) :=
            pairCount_succ_add_one rosen (j + 1) (j + 2) (by
              show rosen 0 + rosen (j + 2) ≤ j + 2
              rw [rosen_zero', heq]
              omega)
          have h4 : pairCount rosen (j + 1) (j + 1) ≤ pairCount rosen (j + 1) (j + 2) :=
            pairCount_mono_right rosen (j + 1) (by omega)
          have h5 : j + 1 ≤ pairCount rosen (j + 1) (j + 1) := ih (j + 1) le_rfl
          show j + 2 ≤ pairCount rosen (j + 2) (j + 2)
          omega
        · have h6 : pairCount rosen (j + 1) (j + 2) ≤ pairCount rosen (j + 2) (j + 2) :=
            pairCount_succ_le rosen (j + 1) (j + 2)
          show j + 2 ≤ pairCount rosen (j + 2) (j + 2)
          omega

end OMA

theorem OMA.solution : type_of% @Erdos954.erdos_954.variants.lower := by
  intro x
  exact OMA.le_pairCount x x le_rfl
