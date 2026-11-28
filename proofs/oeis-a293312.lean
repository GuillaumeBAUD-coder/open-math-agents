import OMAStatements.S_oeis_a293312

namespace OMA.S_oeis_a293312




/-- Walks of length k + 1 out of a whose entries are pairwise related and whose last entry is
related to b. -/
def Chain (n k : ℕ) (a b : Fin n) : Finset (Fin (k + 1) → Fin n) :=
  Finset.univ.filter (fun y => y 0 = a ∧ (∀ i : Fin k, n - 1 ≤ (y i.castSucc : ℕ) + y i.succ) ∧
    n - 1 ≤ (y (Fin.last k) : ℕ) + b)

lemma mem_chain {n k : ℕ} {a b : Fin n} {y : Fin (k + 1) → Fin n} :
    y ∈ Chain n k a b ↔ y 0 = a ∧ (∀ i : Fin k, n - 1 ≤ (y i.castSucc : ℕ) + y i.succ) ∧
      n - 1 ≤ (y (Fin.last k) : ℕ) + b := by
  simp [Chain]

lemma chain_zero (n : ℕ) (a b : Fin n) :
    (Chain n 0 a b).card = if n - 1 ≤ (a : ℕ) + b then 1 else 0 := by
  split_ifs with h
  · rw [Finset.card_eq_one]
    refine ⟨fun _ => a, ?_⟩
    ext y
    rw [mem_chain, Finset.mem_singleton]
    constructor
    · rintro ⟨h0, -, -⟩
      funext i
      rw [Fin.fin_one_eq_zero i]
      exact h0
    · rintro rfl
      exact ⟨rfl, fun i => i.elim0, h⟩
  · rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
    intro y hy
    rw [mem_chain] at hy
    obtain ⟨h0, -, hl⟩ := hy
    apply h
    have hlast : Fin.last 0 = 0 := rfl
    rw [hlast, h0] at hl
    exact hl

lemma chain_succ (n k : ℕ) (a b : Fin n) :
    (Chain n (k + 1) a b).card =
      ∑ c : Fin n, (Chain n k a c).card * (if n - 1 ≤ (c : ℕ) + b then 1 else 0) := by
  rw [Finset.card_eq_sum_card_fiberwise (f := fun y => y (Fin.last (k + 1)))
    (t := Finset.univ) (fun _ _ => Finset.mem_univ _)]
  refine Finset.sum_congr rfl fun c _ => ?_
  split_ifs with hcb
  · rw [mul_one]
    refine Finset.card_nbij' (fun y => Fin.init y) (fun y => Fin.snoc y c) ?_ ?_ ?_ ?_
    · intro y hy
      rw [Finset.mem_coe, Finset.mem_filter, mem_chain] at hy
      rw [Finset.mem_coe, mem_chain]
      obtain ⟨⟨h0, hch, -⟩, hc⟩ := hy
      refine ⟨?_, fun i => ?_, ?_⟩
      · exact h0
      · have := hch i.castSucc
        rwa [Fin.succ_castSucc] at this
      · have := hch (Fin.last k)
        rwa [Fin.succ_last, hc] at this
    · intro y hy
      rw [Finset.mem_coe, mem_chain] at hy
      rw [Finset.mem_coe, Finset.mem_filter, mem_chain]
      beta_reduce
      obtain ⟨h0, hch, hl⟩ := hy
      refine ⟨⟨?_, fun i => ?_, ?_⟩, ?_⟩
      · have : (0 : Fin (k + 1 + 1)) = Fin.castSucc 0 := rfl
        rw [this, Fin.snoc_castSucc]
        exact h0
      · refine Fin.lastCases ?_ (fun j => ?_) i
        · rw [Fin.snoc_castSucc, Fin.succ_last, Fin.snoc_last]
          exact hl
        · rw [Fin.snoc_castSucc, Fin.succ_castSucc, Fin.snoc_castSucc]
          exact hch j
      · rw [Fin.snoc_last]
        exact hcb
      · rw [Fin.snoc_last]
    · intro y hy
      rw [Finset.mem_coe, Finset.mem_filter] at hy
      rw [← hy.2]
      exact Fin.snoc_init_self y
    · intro y _
      exact Fin.init_snoc (α := fun _ => Fin n) _ _
  · rw [mul_zero, Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
    intro y hy
    rw [Finset.mem_filter, mem_chain] at hy
    exact hcb (hy.2 ▸ hy.1.2.2)

lemma pow_apply_eq (n k : ℕ) (a b : Fin n) : (M n ^ (k + 1)) a b = (Chain n k a b).card := by
  induction k generalizing b with
  | zero =>
    show (M n ^ 1) a b = _
    rw [pow_one, chain_zero]
    rfl
  | succ k ih =>
    rw [pow_succ, Matrix.mul_apply, chain_succ]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [ih c]
    rfl

lemma trace_eq (n m : ℕ) : Matrix.trace (M n ^ (m + 1)) =
    (Finset.univ.filter (fun y : Fin (m + 1) → Fin n =>
      ∀ j, n - 1 ≤ (y j : ℕ) + y (finRotate (m + 1) j))).card := by
  rw [Matrix.trace]
  simp only [Matrix.diag, pow_apply_eq]
  rw [Finset.card_eq_sum_card_fiberwise (f := fun y => y 0) (t := Finset.univ)
    (fun _ _ => Finset.mem_univ _)]
  refine Finset.sum_congr rfl fun a _ => ?_
  congr 1
  ext y
  simp only [Chain, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨h0, hch, hl⟩
    refine ⟨fun j => ?_, h0⟩
    refine Fin.lastCases ?_ (fun i => ?_) j
    · rw [finRotate_last, h0]
      exact hl
    · rw [finRotate_apply, Fin.coeSucc_eq_succ]
      exact hch i
  · rintro ⟨hall, h0⟩
    refine ⟨h0, fun i => ?_, ?_⟩
    · have := hall i.castSucc
      rwa [finRotate_apply, Fin.coeSucc_eq_succ] at this
    · have := hall (Fin.last m)
      rwa [finRotate_last, h0] at this

lemma labelings_eq (n k : ℕ) (hn : 1 ≤ n) :
    Set.ncard {p : (Fin k → ℕ) × (Fin k → ℕ) | IsMagicLabeling k (n - 1) p.1 p.2} =
      (Finset.univ.filter (fun y : Fin k → Fin n =>
        ∀ j, n - 1 ≤ (y j : ℕ) + y (finRotate k j))).card := by
  rw [← Set.ncard_coe_finset]
  refine Set.ncard_congr (fun p _ => fun j => (⟨n - 1 - p.1 j, by omega⟩ : Fin n)) ?_ ?_ ?_
  · intro p hp
    simp only [Set.mem_ofPred_eq, IsMagicLabeling] at hp
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq]
    intro j
    have h1 := hp j
    have h2 := hp (finRotate k j)
    omega
  · intro p q hp hq hpq
    simp only [Set.mem_ofPred_eq, IsMagicLabeling] at hp hq
    have h1 : p.1 = q.1 := by
      funext j
      have h := congrFun hpq j
      simp only [Fin.mk.injEq] at h
      have := hp j
      have := hq j
      omega
    have h2 : p.2 = q.2 := by
      funext j
      have := hp j
      have := hq j
      rw [h1] at *
      omega
    exact Prod.ext h1 h2
  · intro y hy
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hy
    refine ⟨(fun j => n - 1 - y j, fun j => y j + y (finRotate k j) - (n - 1)), ?_, ?_⟩
    · simp only [Set.mem_ofPred_eq, IsMagicLabeling]
      intro j
      have := hy j
      have := (y j).isLt
      have := (y (finRotate k j)).isLt
      omega
    · funext j
      ext
      simp only
      have := (y j).isLt
      omega

theorem conjecture : ∀ n k : ℕ, 1 ≤ n → 2 ≤ k →
    A n k = Set.ncard {p : (Fin k → ℕ) × (Fin k → ℕ) | IsMagicLabeling k (n - 1) p.1 p.2} := by
  intro n k hn hk
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  rw [A, trace_eq, labelings_eq n (m + 1) hn]

end OMA.S_oeis_a293312

theorem OMA.solution : type_of% @OMA.S_oeis_a293312.main :=
  OMA.S_oeis_a293312.conjecture
