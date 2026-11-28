import OMAStatements.S_oeis_a284125

-- Credit: @Dariusthedoggie
-- Proof: characterize length-2 longest repeated suffix by prefix pair-presence and triple-avoidance, decompose by last 3 bits into four 8-state DFAs, and sum their rational generating functions.

namespace OMA.P284125

open OMA.S_oeis_a284125 PowerSeries Matrix

/-- DFA state: the last two bits and whether the target pair has appeared. -/
abbrev St := Fin 2 × Fin 2 × Bool

/-- Whether the pair `(b0, c0)` occurs as a contiguous pair in `u`. -/
def has2 (b0 c0 : Fin 2) {m : ℕ} (u : Fin (m + 2) → Fin 2) : Prop :=
  ∃ i : Fin (m + 1), u ⟨(i : ℕ), by omega⟩ = b0 ∧ u ⟨(i : ℕ) + 1, by omega⟩ = c0

instance (b0 c0 : Fin 2) {m : ℕ} (u : Fin (m + 2) → Fin 2) : Decidable (has2 b0 c0 u) := by
  unfold has2; infer_instance

/-- Whether `u` avoids the contiguous triple `(a0, b0, c0)`. -/
def avoid3 (a0 b0 c0 : Fin 2) {m : ℕ} (u : Fin (m + 2) → Fin 2) : Prop :=
  ∀ i : Fin m, ¬ (u ⟨(i : ℕ), by omega⟩ = a0 ∧ u ⟨(i : ℕ) + 1, by omega⟩ = b0 ∧
    u ⟨(i : ℕ) + 2, by omega⟩ = c0)

instance (a0 b0 c0 : Fin 2) {m : ℕ} (u : Fin (m + 2) → Fin 2) : Decidable (avoid3 a0 b0 c0 u) := by
  unfold avoid3; infer_instance

lemma has2_snoc (b0 c0 : Fin 2) {m : ℕ} (v : Fin (m + 2) → Fin 2) (y : Fin 2) :
    has2 b0 c0 (Fin.snoc v y : Fin (m + 3) → Fin 2) ↔
      has2 b0 c0 v ∨ (v ⟨m + 1, by omega⟩ = b0 ∧ y = c0) := by
  constructor
  · rintro ⟨i, h1, h2⟩
    by_cases hi : (i : ℕ) < m + 1
    · left
      refine ⟨⟨i.1, hi⟩, ?_, ?_⟩
      · have e1 : (⟨i.1, by omega⟩ : Fin (m + 3)) = (⟨i.1, by omega⟩ : Fin (m + 2)).castSucc := rfl
        rw [e1, Fin.snoc_castSucc] at h1; exact h1
      · have e2 : (⟨i.1 + 1, by omega⟩ : Fin (m + 3)) = (⟨i.1 + 1, by omega⟩ : Fin (m + 2)).castSucc := rfl
        rw [e2, Fin.snoc_castSucc] at h2; exact h2
    · right
      have him : (i : ℕ) = m + 1 := by omega
      have e1 : (⟨i.1, by omega⟩ : Fin (m + 3)) = (⟨m + 1, by omega⟩ : Fin (m + 2)).castSucc := by
        ext; simp [him]
      have e2 : (⟨i.1 + 1, by omega⟩ : Fin (m + 3)) = Fin.last (m + 2) := by
        ext; simp [him]
      rw [e1, Fin.snoc_castSucc] at h1
      rw [e2, Fin.snoc_last] at h2
      exact ⟨h1, h2⟩
  · rintro (⟨i, h1, h2⟩ | ⟨h1, h2⟩)
    · refine ⟨⟨i.1, by omega⟩, ?_, ?_⟩
      · change (Fin.snoc v y : Fin (m + 3) → Fin 2) (⟨i.1, by omega⟩ : Fin (m + 2)).castSucc = b0
        rw [Fin.snoc_castSucc]; exact h1
      · change (Fin.snoc v y : Fin (m + 3) → Fin 2) (⟨i.1 + 1, by omega⟩ : Fin (m + 2)).castSucc = c0
        rw [Fin.snoc_castSucc]; exact h2
    · refine ⟨⟨m + 1, by omega⟩, ?_, ?_⟩
      · change (Fin.snoc v y : Fin (m + 3) → Fin 2) (⟨m + 1, by omega⟩ : Fin (m + 2)).castSucc = b0
        rw [Fin.snoc_castSucc]; exact h1
      · change (Fin.snoc v y : Fin (m + 3) → Fin 2) (Fin.last (m + 2)) = c0
        rw [Fin.snoc_last]; exact h2

lemma avoid3_snoc (a0 b0 c0 : Fin 2) {m : ℕ} (v : Fin (m + 2) → Fin 2) (y : Fin 2) :
    avoid3 a0 b0 c0 (Fin.snoc v y : Fin (m + 3) → Fin 2) ↔
      avoid3 a0 b0 c0 v ∧ ¬ (v ⟨m, by omega⟩ = a0 ∧ v ⟨m + 1, by omega⟩ = b0 ∧ y = c0) := by
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · intro i
      have hi := h ⟨i.1, by omega⟩
      have e0 : (⟨i.1, by omega⟩ : Fin (m + 3)) = (⟨i.1, by omega⟩ : Fin (m + 2)).castSucc := rfl
      have e1 : (⟨i.1 + 1, by omega⟩ : Fin (m + 3)) = (⟨i.1 + 1, by omega⟩ : Fin (m + 2)).castSucc := rfl
      have e2 : (⟨i.1 + 2, by omega⟩ : Fin (m + 3)) = (⟨i.1 + 2, by omega⟩ : Fin (m + 2)).castSucc := rfl
      rw [e0, e1, e2, Fin.snoc_castSucc, Fin.snoc_castSucc, Fin.snoc_castSucc] at hi
      exact hi
    · have hm := h ⟨m, by omega⟩
      have e0 : (⟨m, by omega⟩ : Fin (m + 3)) = (⟨m, by omega⟩ : Fin (m + 2)).castSucc := rfl
      have e1 : (⟨m + 1, by omega⟩ : Fin (m + 3)) = (⟨m + 1, by omega⟩ : Fin (m + 2)).castSucc := rfl
      have e2 : (⟨m + 2, by omega⟩ : Fin (m + 3)) = Fin.last (m + 2) := by ext; simp
      rw [e0, e1, e2, Fin.snoc_castSucc, Fin.snoc_castSucc, Fin.snoc_last] at hm
      exact hm
  · rintro ⟨hv, hlast⟩ i
    by_cases hi : (i : ℕ) < m
    · have e0 : (⟨i.1, by omega⟩ : Fin (m + 3)) = (⟨i.1, by omega⟩ : Fin (m + 2)).castSucc := rfl
      have e1 : (⟨i.1 + 1, by omega⟩ : Fin (m + 3)) = (⟨i.1 + 1, by omega⟩ : Fin (m + 2)).castSucc := rfl
      have e2 : (⟨i.1 + 2, by omega⟩ : Fin (m + 3)) = (⟨i.1 + 2, by omega⟩ : Fin (m + 2)).castSucc := rfl
      rw [e0, e1, e2, Fin.snoc_castSucc, Fin.snoc_castSucc, Fin.snoc_castSucc]
      exact hv ⟨i.1, hi⟩
    · have him : (i : ℕ) = m := by omega
      have e0 : (⟨i.1, by omega⟩ : Fin (m + 3)) = (⟨m, by omega⟩ : Fin (m + 2)).castSucc := by
        ext; simp [him]
      have e1 : (⟨i.1 + 1, by omega⟩ : Fin (m + 3)) = (⟨m + 1, by omega⟩ : Fin (m + 2)).castSucc := by
        ext; simp [him]
      have e2 : (⟨i.1 + 2, by omega⟩ : Fin (m + 3)) = Fin.last (m + 2) := by
        ext; simp [him]
      rw [e0, e1, e2, Fin.snoc_castSucc, Fin.snoc_castSucc, Fin.snoc_last]
      exact hlast

/-- Transfer matrix for pattern `(a0, b0, c0)` over the 8 DFA states. -/
def M (a0 b0 c0 : Fin 2) : Matrix St St ℤ :=
  Matrix.of fun s' s =>
    if s'.1 = s.2.1 ∧ ¬ (s.1 = a0 ∧ s.2.1 = b0 ∧ s'.2.1 = c0) ∧
        s'.2.2 = (s.2.2 || decide (s.2.1 = b0 ∧ s'.2.1 = c0))
    then 1 else 0

/-- Initial state vector for length-2 prefixes. -/
def v0 (b0 c0 : Fin 2) : St → ℤ :=
  fun s => if s.2.2 = decide (s.1 = b0 ∧ s.2.1 = c0) then 1 else 0

/-- Iterated transfer vectors `M ^ m *ᵥ v0`. -/
def vec (a0 b0 c0 : Fin 2) : ℕ → St → ℤ
  | 0 => v0 b0 c0
  | m + 1 => M a0 b0 c0 *ᵥ vec a0 b0 c0 m

lemma vec_eq (a0 b0 c0 : Fin 2) (m : ℕ) :
    vec a0 b0 c0 m = M a0 b0 c0 ^ m *ᵥ v0 b0 c0 := by
  induction m with
  | zero => simp [vec]
  | succ m ih => rw [vec, ih, pow_succ', Matrix.mulVec_mulVec]

/-- Combinatorial count of length-(m+2) prefixes in DFA state `s`. -/
def cnt (a0 b0 c0 : Fin 2) (m : ℕ) (s : St) : ℤ :=
  ∑ u : Fin (m + 2) → Fin 2,
    if u ⟨m, by omega⟩ = s.1 ∧ u ⟨m + 1, by omega⟩ = s.2.1 ∧
        avoid3 a0 b0 c0 u ∧ s.2.2 = decide (has2 b0 c0 u)
    then 1 else 0

lemma sum_snoc {m : ℕ} (f : (Fin (m + 3) → Fin 2) → ℤ) :
    ∑ u, f u = ∑ v : Fin (m + 2) → Fin 2, ∑ y : Fin 2, f (Fin.snoc v y) := by
  rw [← (Fin.snocEquiv (fun _ => Fin 2)).sum_comp, Fintype.sum_prod_type, Finset.sum_comm]
  rfl

lemma cnt_zero (a0 b0 c0 : Fin 2) : cnt a0 b0 c0 0 = v0 b0 c0 := by
  funext ⟨p2, p1, seen⟩
  unfold cnt v0
  let e : (Fin 2 → Fin 2) ≃ Fin 2 × Fin 2 :=
    { toFun := fun u => (u 0, u 1)
      invFun := fun p i => if i = 0 then p.1 else p.2
      left_inv := fun u => by funext i; fin_cases i <;> rfl
      right_inv := fun ⟨_, _⟩ => rfl }
  rw [← e.symm.sum_comp, Fintype.sum_prod_type]
  simp only [e, Equiv.coe_fn_symm_mk]
  rw [Finset.sum_eq_single p2]
  · rw [Finset.sum_eq_single p1]
    · have hav : avoid3 a0 b0 c0 (fun i : Fin 2 => if i = 0 then p2 else p1) := fun i => Fin.elim0 i
      have h2 : has2 b0 c0 (fun i : Fin 2 => if i = 0 then p2 else p1) ↔ (p2 = b0 ∧ p1 = c0) := by
        unfold has2
        constructor
        · rintro ⟨i, h1, h2⟩; fin_cases i; simpa using ⟨h1, h2⟩
        · rintro ⟨h1, h2⟩; exact ⟨0, by simpa using h1, by simpa using h2⟩
      simp [hav, h2]
    · intro y _ hy; simp [hy]
    · simp
  · intro x _ hx; apply Finset.sum_eq_zero; intro y _; simp [hx]
  · simp

lemma cnt_succ (a0 b0 c0 : Fin 2) (m : ℕ) :
    cnt a0 b0 c0 (m + 1) = M a0 b0 c0 *ᵥ cnt a0 b0 c0 m := by
  funext ⟨p1, y, seen'⟩
  unfold cnt
  rw [sum_snoc]
  have hterm : ∀ v : Fin (m + 2) → Fin 2,
      (∑ z : Fin 2,
        if (Fin.snoc v z : Fin (m + 3) → Fin 2) ⟨m + 1, by omega⟩ = p1 ∧
           (Fin.snoc v z : Fin (m + 3) → Fin 2) ⟨m + 2, by omega⟩ = y ∧
           avoid3 a0 b0 c0 (Fin.snoc v z) ∧
           seen' = decide (has2 b0 c0 (Fin.snoc v z)) then (1 : ℤ) else 0) =
      if v ⟨m + 1, by omega⟩ = p1 ∧ avoid3 a0 b0 c0 v ∧
         ¬ (v ⟨m, by omega⟩ = a0 ∧ v ⟨m + 1, by omega⟩ = b0 ∧ y = c0) ∧
         seen' = (decide (has2 b0 c0 v) || decide (v ⟨m + 1, by omega⟩ = b0 ∧ y = c0))
      then 1 else 0 := by
    intro v
    have e1 : (⟨m + 1, by omega⟩ : Fin (m + 3)) = (⟨m + 1, by omega⟩ : Fin (m + 2)).castSucc := rfl
    have e2 : (⟨m + 2, by omega⟩ : Fin (m + 3)) = Fin.last (m + 2) := by ext; simp
    rw [Finset.sum_eq_single y]
    · simp only [e1, e2, Fin.snoc_castSucc, Fin.snoc_last, avoid3_snoc, has2_snoc, Bool.decide_or]
      by_cases h1 : v ⟨m + 1, by omega⟩ = p1 <;>
        by_cases h2 : avoid3 a0 b0 c0 v <;>
        by_cases h3 : ¬ (v ⟨m, by omega⟩ = a0 ∧ v ⟨m + 1, by omega⟩ = b0 ∧ y = c0) <;>
        by_cases h4 : seen' = (decide (has2 b0 c0 v) || decide (v ⟨m + 1, by omega⟩ = b0 ∧ y = c0)) <;>
        simp [h1, h2, h3, h4]
    · intro z _ hz
      rw [e2, Fin.snoc_last]
      simp [hz]
    · simp
  simp_rw [hterm]
  -- Fiber over s = (v m, v (m+1), decide (has2 b0 c0 v))
  have hfib : ∀ v : Fin (m + 2) → Fin 2,
      (if v ⟨m + 1, by omega⟩ = p1 ∧ avoid3 a0 b0 c0 v ∧
          ¬ (v ⟨m, by omega⟩ = a0 ∧ v ⟨m + 1, by omega⟩ = b0 ∧ y = c0) ∧
          seen' = (decide (has2 b0 c0 v) || decide (v ⟨m + 1, by omega⟩ = b0 ∧ y = c0))
       then (1 : ℤ) else 0) =
      ∑ s : St, M a0 b0 c0 (p1, y, seen') s *
        (if v ⟨m, by omega⟩ = s.1 ∧ v ⟨m + 1, by omega⟩ = s.2.1 ∧
            avoid3 a0 b0 c0 v ∧ s.2.2 = decide (has2 b0 c0 v) then 1 else 0) := by
    intro v
    rw [Finset.sum_eq_single (v ⟨m, by omega⟩, v ⟨m + 1, by omega⟩, decide (has2 b0 c0 v))]
    · simp only [M, Matrix.of_apply, true_and]
      by_cases h1 : p1 = v ⟨m + 1, by omega⟩ <;>
        by_cases h2 : avoid3 a0 b0 c0 v <;>
        by_cases h3 : ¬ (v ⟨m, by omega⟩ = a0 ∧ v ⟨m + 1, by omega⟩ = b0 ∧ y = c0) <;>
        by_cases h4 : seen' = (decide (has2 b0 c0 v) || decide (v ⟨m + 1, by omega⟩ = b0 ∧ y = c0)) <;>
        simp [h1, eq_comm, h2, h4]
    · intro s _ hs
      have hneg : ¬ (v ⟨m, by omega⟩ = s.1 ∧ v ⟨m + 1, by omega⟩ = s.2.1 ∧
          avoid3 a0 b0 c0 v ∧ s.2.2 = decide (has2 b0 c0 v)) := by
        rintro ⟨h1, h2, _, h4⟩
        apply hs
        ext <;> simp [h1, h2, h4]
      simp [hneg]
    · simp
  simp_rw [hfib]
  rw [Finset.sum_comm]
  simp only [Matrix.mulVec, dotProduct]
  apply Finset.sum_congr rfl
  intro s _
  rw [Finset.mul_sum]

lemma cnt_eq (a0 b0 c0 : Fin 2) (m : ℕ) : cnt a0 b0 c0 m = vec a0 b0 c0 m := by
  induction m with
  | zero => rw [cnt_zero, vec]
  | succ m ih => rw [cnt_succ, ih, vec]

lemma valid_snoc_iff {m : ℕ} (u : Fin (m + 2) → Fin 2) (c0 : Fin 2) :
    valid (m + 3) (Fin.snoc u c0) ↔
      has2 (u ⟨m + 1, by omega⟩) c0 u ∧ avoid3 (u ⟨m, by omega⟩) (u ⟨m + 1, by omega⟩) c0 u := by
  set w : Fin (m + 3) → Fin 2 := Fin.snoc u c0
  have hu : ∀ j : ℕ, (hj : j < m + 2) → w ⟨j, by omega⟩ = u ⟨j, hj⟩ := by
    intro j hj
    change (Fin.snoc u c0 : Fin (m + 3) → Fin 2) (⟨j, hj⟩ : Fin (m + 2)).castSucc = u ⟨j, hj⟩
    rw [Fin.snoc_castSucc]
  have hc : w ⟨m + 2, by omega⟩ = c0 := by
    change (Fin.snoc u c0 : Fin (m + 3) → Fin 2) (Fin.last (m + 2)) = c0
    rw [Fin.snoc_last]
  constructor
  · rintro ⟨⟨_, i, hi, hmatch⟩, hno⟩
    refine ⟨?_, ?_⟩
    · refine ⟨⟨i.1, by omega⟩, ?_, ?_⟩
      · have h0 := hmatch ⟨0, by omega⟩
        simp only [Nat.add_zero] at h0
        have h1 : m + 3 - 2 = m + 1 := by omega
        rw [hu i.1 (by omega), hu (m + 3 - 2) (by omega)] at h0
        simpa [h1] using h0
      · have h1 := hmatch ⟨1, by omega⟩
        have heq : m + 3 - 2 + 1 = m + 2 := by omega
        rw [hu (i.1 + 1) (by omega)] at h1
        have hlast : w ⟨m + 3 - 2 + 1, by omega⟩ = c0 := by
          have hidx : (⟨m + 3 - 2 + 1, by omega⟩ : Fin (m + 3)) = ⟨m + 2, by omega⟩ := by ext; dsimp; omega
          rw [hidx]; exact hc
        rw [hlast] at h1
        exact h1
    · intro i ⟨h0, h1, h2⟩
      have := i.isLt
      apply hno ⟨3, by omega⟩ (by dsimp; omega)
      refine ⟨by dsimp; omega, ⟨i.1, by omega⟩, by dsimp; omega, ?_⟩
      intro k
      fin_cases k
      · simp only [Nat.add_zero]
        rw [hu i.1 (by omega), hu (m + 3 - 3) (by omega)]
        simpa [show m + 3 - 3 = m by omega] using h0
      · rw [hu (i.1 + 1) (by omega), hu (m + 3 - 3 + 1) (by omega)]
        simpa [show m + 3 - 3 + 1 = m + 1 by omega] using h1
      · rw [hu (i.1 + 2) (by omega)]
        have hlast : w ⟨m + 3 - 3 + 2, by omega⟩ = c0 := by
          have hidx : (⟨m + 3 - 3 + 2, by omega⟩ : Fin (m + 3)) = ⟨m + 2, by omega⟩ := by ext; dsimp; omega
          rw [hidx]; exact hc
        rw [hlast]; exact h2
  · rintro ⟨⟨i, h0, h1⟩, hav⟩
    have := i.isLt
    refine ⟨⟨by omega, ⟨i.1, by omega⟩, by dsimp; omega, ?_⟩, ?_⟩
    · intro k
      fin_cases k
      · simp only [Nat.add_zero]
        rw [hu i.1 (by omega), hu (m + 3 - 2) (by omega)]
        simpa [show m + 3 - 2 = m + 1 by omega] using h0
      · rw [hu (i.1 + 1) (by omega)]
        have hlast : w ⟨m + 3 - 2 + 1, by omega⟩ = c0 := by
          have hidx : (⟨m + 3 - 2 + 1, by omega⟩ : Fin (m + 3)) = ⟨m + 2, by omega⟩ := by ext; dsimp; omega
          rw [hidx]; exact hc
        rw [hlast]; exact h1
    · intro L hL ⟨hLn, i, hi, hmatch⟩
      have hL3 : 3 ≤ (L : ℕ) := by omega
      have hj : (i : ℕ) + ((L : ℕ) - 3) < m := by omega
      apply hav ⟨(i : ℕ) + ((L : ℕ) - 3), hj⟩
      refine ⟨?_, ?_, ?_⟩
      · have hm := hmatch ⟨(L : ℕ) - 3, by omega⟩
        have e1 : (i : ℕ) + ((L : ℕ) - 3) < m + 2 := by omega
        have e2 : m + 3 - (L : ℕ) + ((L : ℕ) - 3) = m := by omega
        rw [hu _ e1, hu _ (by rw [e2]; omega)] at hm
        simpa [e2] using hm
      · have hm := hmatch ⟨(L : ℕ) - 2, by omega⟩
        have e1 : (i : ℕ) + ((L : ℕ) - 2) = (i : ℕ) + ((L : ℕ) - 3) + 1 := by omega
        have e2 : m + 3 - (L : ℕ) + ((L : ℕ) - 2) = m + 1 := by omega
        rw [hu _ (by rw [e1]; omega), hu _ (by rw [e2]; omega)] at hm
        simpa [e1, e2] using hm
      · have hm := hmatch ⟨(L : ℕ) - 1, by omega⟩
        have e1 : (i : ℕ) + ((L : ℕ) - 1) = (i : ℕ) + ((L : ℕ) - 3) + 2 := by omega
        have hlast : w ⟨m + 3 - (L : ℕ) + ((L : ℕ) - 1), by omega⟩ = c0 := by
          have hidx : (⟨m + 3 - (L : ℕ) + ((L : ℕ) - 1), by omega⟩ : Fin (m + 3)) = ⟨m + 2, by omega⟩ := by ext; dsimp; omega
          rw [hidx]; exact hc
        rw [hu _ (by omega), hlast] at hm
        simpa [e1] using hm

/-- Bitwise complement preserves validity. -/
def flip (b : Fin 2) : Fin 2 := 1 - b

lemma flip_inj : Function.Injective flip := by decide
lemma flip_zero : flip 0 = 1 := by decide
lemma flip_flip (b : Fin 2) : flip (flip b) = b := by fin_cases b <;> decide

lemma valid_flip {n : ℕ} (w : Fin n → Fin 2) : valid n (fun i => flip (w i)) ↔ valid n w := by
  have hsuf : ∀ L : ℕ, sufAppearsTwice n L (fun i => flip (w i)) ↔ sufAppearsTwice n L w := by
    intro L
    unfold sufAppearsTwice
    constructor
    · rintro ⟨hL, i, hi, hm⟩
      exact ⟨hL, i, hi, fun k => flip_inj (hm k)⟩
    · rintro ⟨hL, i, hi, hm⟩
      exact ⟨hL, i, hi, fun k => congrArg flip (hm k)⟩
  unfold valid
  simp only [hsuf]

lemma a_add3 (m : ℕ) :
    (a (m + 3) : ℤ) =
    2 * (vec 0 0 0 m (0, 0, true) + vec 0 1 0 m (0, 1, true) +
         vec 1 0 0 m (1, 0, true) + vec 1 1 0 m (1, 1, true)) := by
  have ha : (a (m + 3) : ℤ) =
      ∑ u : Fin (m + 2) → Fin 2, ∑ c0 : Fin 2, if valid (m + 3) (Fin.snoc u c0) then 1 else 0 := by
    have ha0 : a (m + 3) = (Finset.univ.filter (valid (m + 3))).card := rfl
    rw [ha0, Finset.card_filter]
    push_cast
    exact sum_snoc (fun w => if valid (m + 3) w then (1 : ℤ) else 0)
  rw [ha, Finset.sum_comm, Fin.sum_univ_two]
  have h1 : (∑ u : Fin (m + 2) → Fin 2, if valid (m + 3) (Fin.snoc u 1) then (1 : ℤ) else 0) =
      ∑ u : Fin (m + 2) → Fin 2, if valid (m + 3) (Fin.snoc u 0) then (1 : ℤ) else 0 := by
    let e : (Fin (m + 2) → Fin 2) ≃ (Fin (m + 2) → Fin 2) :=
      { toFun := fun u i => flip (u i)
        invFun := fun u i => flip (u i)
        left_inv := fun u => by funext i; exact flip_flip (u i)
        right_inv := fun u => by funext i; exact flip_flip (u i) }
    rw [← e.sum_comp]
    apply Finset.sum_congr rfl
    intro u _
    have hsnoc : Fin.snoc (e u) 1 = fun i => flip ((Fin.snoc u 0 : Fin (m + 3) → Fin 2) i) := by
      funext i
      induction i using Fin.lastCases with
      | last => simp [flip_zero]
      | cast j => simp [e]
    simp only [hsnoc, valid_flip]
  rw [h1, ← two_mul]
  congr 1
  simp_rw [valid_snoc_iff]
  have hpart : ∀ u : Fin (m + 2) → Fin 2,
      (if has2 (u ⟨m + 1, by omega⟩) 0 u ∧ avoid3 (u ⟨m, by omega⟩) (u ⟨m + 1, by omega⟩) 0 u
       then (1 : ℤ) else 0) =
      ∑ p : Fin 2 × Fin 2,
        if u ⟨m, by omega⟩ = p.1 ∧ u ⟨m + 1, by omega⟩ = p.2 ∧
           avoid3 p.1 p.2 0 u ∧ true = decide (has2 p.2 0 u) then 1 else 0 := by
    intro u
    rw [Finset.sum_eq_single (u ⟨m, by omega⟩, u ⟨m + 1, by omega⟩)]
    · by_cases h1 : has2 (u ⟨m + 1, by omega⟩) 0 u <;>
        by_cases h2 : avoid3 (u ⟨m, by omega⟩) (u ⟨m + 1, by omega⟩) 0 u <;>
        simp [h1, h2]
    · intro p _ hp
      rw [if_neg]
      rintro ⟨ha, hb, _⟩
      apply hp; ext <;> simp [ha, hb]
    · simp
  simp_rw [hpart]
  rw [Finset.sum_comm, Fintype.sum_prod_type, Fin.sum_univ_two, Fin.sum_univ_two, Fin.sum_univ_two]
  have hf : ∀ a0 b0 : Fin 2,
      (∑ u : Fin (m + 2) → Fin 2,
        if u ⟨m, by omega⟩ = a0 ∧ u ⟨m + 1, by omega⟩ = b0 ∧
           avoid3 a0 b0 0 u ∧ true = decide (has2 b0 0 u) then (1 : ℤ) else 0) =
      vec a0 b0 0 m (a0, b0, true) := by
    intro a0 b0
    rw [← cnt_eq a0 b0 0 m]
    rfl
  rw [hf 0 0, hf 0 1, hf 1 0, hf 1 1]
  ring

def lookup2 (a0 a1 : ℤ) (i : Fin 2) : ℤ := match i with | ⟨0, _⟩ => a0 | ⟨1, _⟩ => a1
def lookupBool (af at_ : ℤ) (b : Bool) : ℤ := match b with | false => af | true => at_
def sum2 (f : Fin 2 → ℤ) : ℤ := f 0 + f 1
def sumBool (f : Bool → ℤ) : ℤ := f false + f true

def step (a0 b0 c0 : Fin 2) (v : St → ℤ) (s' : St) : ℤ :=
  sum2 fun x => sum2 fun y => sumBool fun b =>
    M a0 b0 c0 s' (x, y, b) * v (x, y, b)

lemma mulVec_eq_step (a0 b0 c0 : Fin 2) (v : St → ℤ) :
    M a0 b0 c0 *ᵥ v = step a0 b0 c0 v := by
  funext s'
  simp only [Matrix.mulVec, dotProduct, step, sum2, sumBool,
    Fintype.sum_prod_type, Fin.sum_univ_two, Fintype.sum_bool]
  ring

lemma st_ext {f g : St → ℤ} (h : ∀ x y : Fin 2, ∀ b : Bool, f (x, y, b) = g (x, y, b)) : f = g := by
  funext ⟨x, y, b⟩; exact h x y b

def t000_0 : St → ℤ | (x, y, b) => lookup2 (lookup2 (lookupBool 0 1 b) (lookupBool 1 0 b) y) (lookup2 (lookupBool 1 0 b) (lookupBool 1 0 b) y) x
def t000_1 : St → ℤ | (x, y, b) => lookup2 (lookup2 (lookupBool 0 1 b) (lookupBool 1 1 b) y) (lookup2 (lookupBool 2 0 b) (lookupBool 2 0 b) y) x
def t000_2 : St → ℤ | (x, y, b) => lookup2 (lookup2 (lookupBool 0 2 b) (lookupBool 2 1 b) y) (lookup2 (lookupBool 3 1 b) (lookupBool 3 1 b) y) x
def t000_3 : St → ℤ | (x, y, b) => lookup2 (lookup2 (lookupBool 0 4 b) (lookupBool 3 3 b) y) (lookup2 (lookupBool 5 2 b) (lookupBool 5 2 b) y) x
def t000_4 : St → ℤ | (x, y, b) => lookup2 (lookup2 (lookupBool 0 7 b) (lookupBool 5 6 b) y) (lookup2 (lookupBool 8 5 b) (lookupBool 8 5 b) y) x
def t000_5 : St → ℤ | (x, y, b) => lookup2 (lookup2 (lookupBool 0 13 b) (lookupBool 8 12 b) y) (lookup2 (lookupBool 13 11 b) (lookupBool 13 11 b) y) x

lemma v000_0 : vec 0 0 0 0 = t000_0 := st_ext (by decide +kernel)
lemma v000_1 : vec 0 0 0 1 = t000_1 := by
  rw [vec, mulVec_eq_step, v000_0]; exact st_ext (by decide +kernel)
lemma v000_2 : vec 0 0 0 2 = t000_2 := by
  rw [vec, mulVec_eq_step, v000_1]; exact st_ext (by decide +kernel)
lemma v000_3 : vec 0 0 0 3 = t000_3 := by
  rw [vec, mulVec_eq_step, v000_2]; exact st_ext (by decide +kernel)
lemma v000_4 : vec 0 0 0 4 = t000_4 := by
  rw [vec, mulVec_eq_step, v000_3]; exact st_ext (by decide +kernel)
lemma v000_5 : vec 0 0 0 5 = t000_5 := by
  rw [vec, mulVec_eq_step, v000_4]; exact st_ext (by decide +kernel)

def t010_0 : St → ℤ | (x, y, b) => lookup2 (lookup2 (lookupBool 1 0 b) (lookupBool 1 0 b) y) (lookup2 (lookupBool 0 1 b) (lookupBool 1 0 b) y) x
def t010_1 : St → ℤ | (x, y, b) => lookup2 (lookup2 (lookupBool 1 1 b) (lookupBool 1 1 b) y) (lookup2 (lookupBool 0 1 b) (lookupBool 2 0 b) y) x
def t010_2 : St → ℤ | (x, y, b) => lookup2 (lookup2 (lookupBool 1 2 b) (lookupBool 1 2 b) y) (lookup2 (lookupBool 0 2 b) (lookupBool 3 1 b) y) x
def t010_3 : St → ℤ | (x, y, b) => lookup2 (lookup2 (lookupBool 1 4 b) (lookupBool 1 4 b) y) (lookup2 (lookupBool 0 4 b) (lookupBool 4 3 b) y) x
def t010_4 : St → ℤ | (x, y, b) => lookup2 (lookup2 (lookupBool 1 8 b) (lookupBool 1 8 b) y) (lookup2 (lookupBool 0 7 b) (lookupBool 5 7 b) y) x
def t010_5 : St → ℤ | (x, y, b) => lookup2 (lookup2 (lookupBool 1 15 b) (lookupBool 1 15 b) y) (lookup2 (lookupBool 0 12 b) (lookupBool 6 15 b) y) x

lemma v010_0 : vec 0 1 0 0 = t010_0 := st_ext (by decide +kernel)
lemma v010_1 : vec 0 1 0 1 = t010_1 := by
  rw [vec, mulVec_eq_step, v010_0]; exact st_ext (by decide +kernel)
lemma v010_2 : vec 0 1 0 2 = t010_2 := by
  rw [vec, mulVec_eq_step, v010_1]; exact st_ext (by decide +kernel)
lemma v010_3 : vec 0 1 0 3 = t010_3 := by
  rw [vec, mulVec_eq_step, v010_2]; exact st_ext (by decide +kernel)
lemma v010_4 : vec 0 1 0 4 = t010_4 := by
  rw [vec, mulVec_eq_step, v010_3]; exact st_ext (by decide +kernel)
lemma v010_5 : vec 0 1 0 5 = t010_5 := by
  rw [vec, mulVec_eq_step, v010_4]; exact st_ext (by decide +kernel)

def t100_0 : St → ℤ | (x, y, b) => lookup2 (lookup2 (lookupBool 0 1 b) (lookupBool 1 0 b) y) (lookup2 (lookupBool 1 0 b) (lookupBool 1 0 b) y) x
def t100_1 : St → ℤ | (x, y, b) => lookup2 (lookup2 (lookupBool 0 1 b) (lookupBool 1 1 b) y) (lookup2 (lookupBool 2 0 b) (lookupBool 2 0 b) y) x
def t100_2 : St → ℤ | (x, y, b) => lookup2 (lookup2 (lookupBool 0 1 b) (lookupBool 2 1 b) y) (lookup2 (lookupBool 3 1 b) (lookupBool 3 1 b) y) x
def t100_3 : St → ℤ | (x, y, b) => lookup2 (lookup2 (lookupBool 0 1 b) (lookupBool 3 2 b) y) (lookup2 (lookupBool 5 2 b) (lookupBool 5 2 b) y) x

lemma v100_0 : vec 1 0 0 0 = t100_0 := st_ext (by decide +kernel)
lemma v100_1 : vec 1 0 0 1 = t100_1 := by
  rw [vec, mulVec_eq_step, v100_0]; exact st_ext (by decide +kernel)
lemma v100_2 : vec 1 0 0 2 = t100_2 := by
  rw [vec, mulVec_eq_step, v100_1]; exact st_ext (by decide +kernel)
lemma v100_3 : vec 1 0 0 3 = t100_3 := by
  rw [vec, mulVec_eq_step, v100_2]; exact st_ext (by decide +kernel)

def t110_0 : St → ℤ | (x, y, b) => lookup2 (lookup2 (lookupBool 1 0 b) (lookupBool 1 0 b) y) (lookup2 (lookupBool 0 1 b) (lookupBool 1 0 b) y) x
def t110_1 : St → ℤ | (x, y, b) => lookup2 (lookup2 (lookupBool 1 1 b) (lookupBool 1 1 b) y) (lookup2 (lookupBool 0 1 b) (lookupBool 2 0 b) y) x
def t110_2 : St → ℤ | (x, y, b) => lookup2 (lookup2 (lookupBool 1 2 b) (lookupBool 1 2 b) y) (lookup2 (lookupBool 0 2 b) (lookupBool 3 1 b) y) x
def t110_3 : St → ℤ | (x, y, b) => lookup2 (lookup2 (lookupBool 1 4 b) (lookupBool 1 4 b) y) (lookup2 (lookupBool 0 3 b) (lookupBool 4 3 b) y) x
def t110_4 : St → ℤ | (x, y, b) => lookup2 (lookup2 (lookupBool 1 7 b) (lookupBool 1 7 b) y) (lookup2 (lookupBool 0 5 b) (lookupBool 5 7 b) y) x

lemma v110_0 : vec 1 1 0 0 = t110_0 := st_ext (by decide +kernel)
lemma v110_1 : vec 1 1 0 1 = t110_1 := by
  rw [vec, mulVec_eq_step, v110_0]; exact st_ext (by decide +kernel)
lemma v110_2 : vec 1 1 0 2 = t110_2 := by
  rw [vec, mulVec_eq_step, v110_1]; exact st_ext (by decide +kernel)
lemma v110_3 : vec 1 1 0 3 = t110_3 := by
  rw [vec, mulVec_eq_step, v110_2]; exact st_ext (by decide +kernel)
lemma v110_4 : vec 1 1 0 4 = t110_4 := by
  rw [vec, mulVec_eq_step, v110_3]; exact st_ext (by decide +kernel)

lemma rel000 : vec 0 0 0 5 =
    (2 : ℤ) • vec 0 0 0 4 + (1 : ℤ) • vec 0 0 0 3 + (-1 : ℤ) • vec 0 0 0 2 +
    (-2 : ℤ) • vec 0 0 0 1 + (-1 : ℤ) • vec 0 0 0 0 := by
  rw [v000_5, v000_4, v000_3, v000_2, v000_1, v000_0]; exact st_ext (by decide +kernel)

lemma rel010 : vec 0 1 0 5 =
    (4 : ℤ) • vec 0 1 0 4 + (-6 : ℤ) • vec 0 1 0 3 + (5 : ℤ) • vec 0 1 0 2 +
    (-3 : ℤ) • vec 0 1 0 1 + (1 : ℤ) • vec 0 1 0 0 := by
  rw [v010_5, v010_4, v010_3, v010_2, v010_1, v010_0]; exact st_ext (by decide +kernel)

lemma rel100 : vec 1 0 0 3 =
    (2 : ℤ) • vec 1 0 0 2 + (-1 : ℤ) • vec 1 0 0 0 := by
  rw [v100_3, v100_2, v100_0]; exact st_ext (by decide +kernel)

lemma rel110 : vec 1 1 0 4 =
    (3 : ℤ) • vec 1 1 0 3 + (-2 : ℤ) • vec 1 1 0 2 + (-1 : ℤ) • vec 1 1 0 1 +
    (1 : ℤ) • vec 1 1 0 0 := by
  rw [v110_4, v110_3, v110_2, v110_1, v110_0]; exact st_ext (by decide +kernel)

lemma vec_shift (a0 b0 c0 : Fin 2) (m k : ℕ) :
    vec a0 b0 c0 (m + k) = M a0 b0 c0 ^ m *ᵥ vec a0 b0 c0 k := by
  rw [vec_eq, vec_eq, Matrix.mulVec_mulVec, pow_add]

def f000 (n : ℕ) : ℚ := if n < 3 then 0 else (vec 0 0 0 (n - 3) (0, 0, true) : ℚ)
def f010 (n : ℕ) : ℚ := if n < 3 then 0 else (vec 0 1 0 (n - 3) (0, 1, true) : ℚ)
def f100 (n : ℕ) : ℚ := if n < 3 then 0 else (vec 1 0 0 (n - 3) (1, 0, true) : ℚ)
def f110 (n : ℕ) : ℚ := if n < 3 then 0 else (vec 1 1 0 (n - 3) (1, 1, true) : ℚ)

lemma f000_rec (n : ℕ) (hn : 8 ≤ n) :
    f000 n = 2 * f000 (n - 1) + f000 (n - 2) - f000 (n - 3) - 2 * f000 (n - 4) - f000 (n - 5) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 8 := ⟨n - 8, by omega⟩
  have h : vec 0 0 0 (m + 5) =
      (2 : ℤ) • vec 0 0 0 (m + 4) + (1 : ℤ) • vec 0 0 0 (m + 3) + (-1 : ℤ) • vec 0 0 0 (m + 2) +
      (-2 : ℤ) • vec 0 0 0 (m + 1) + (-1 : ℤ) • vec 0 0 0 (m + 0) := by
    rw [vec_shift 0 0 0 m 5, rel000]
    simp only [Matrix.mulVec_add, Matrix.mulVec_smul, ← vec_shift]
  have hc : (vec 0 0 0 (m + 5) (0, 0, true) : ℚ) =
      2 * (vec 0 0 0 (m + 4) (0, 0, true) : ℚ) + (vec 0 0 0 (m + 3) (0, 0, true) : ℚ) -
      (vec 0 0 0 (m + 2) (0, 0, true) : ℚ) - 2 * (vec 0 0 0 (m + 1) (0, 0, true) : ℚ) -
      (vec 0 0 0 m (0, 0, true) : ℚ) := by
    have hv := congrFun h (0, 0, true)
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Nat.add_zero] at hv
    exact_mod_cast (show vec 0 0 0 (m + 5) (0, 0, true) =
      2 * vec 0 0 0 (m + 4) (0, 0, true) + vec 0 0 0 (m + 3) (0, 0, true) -
      vec 0 0 0 (m + 2) (0, 0, true) - 2 * vec 0 0 0 (m + 1) (0, 0, true) -
      vec 0 0 0 m (0, 0, true) by linarith)
  unfold f000
  simp only [show ¬ m + 8 < 3 by omega, show ¬ m + 8 - 1 < 3 by omega,
    show ¬ m + 8 - 2 < 3 by omega, show ¬ m + 8 - 4 < 3 by omega, show ¬ m + 8 - 5 < 3 by omega, if_false,
    show m + 8 - 3 = m + 5 by omega, show m + 8 - 1 - 3 = m + 4 by omega,
    show m + 8 - 2 - 3 = m + 3 by omega, show m + 8 - 4 - 3 = m + 1 by omega, show m + 8 - 5 - 3 = m by omega]
  exact hc

lemma f010_rec (n : ℕ) (hn : 8 ≤ n) :
    f010 n = 4 * f010 (n - 1) - 6 * f010 (n - 2) + 5 * f010 (n - 3) - 3 * f010 (n - 4) + f010 (n - 5) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 8 := ⟨n - 8, by omega⟩
  have h : vec 0 1 0 (m + 5) =
      (4 : ℤ) • vec 0 1 0 (m + 4) + (-6 : ℤ) • vec 0 1 0 (m + 3) + (5 : ℤ) • vec 0 1 0 (m + 2) +
      (-3 : ℤ) • vec 0 1 0 (m + 1) + (1 : ℤ) • vec 0 1 0 (m + 0) := by
    rw [vec_shift 0 1 0 m 5, rel010]
    simp only [Matrix.mulVec_add, Matrix.mulVec_smul, ← vec_shift]
  have hc : (vec 0 1 0 (m + 5) (0, 1, true) : ℚ) =
      4 * (vec 0 1 0 (m + 4) (0, 1, true) : ℚ) - 6 * (vec 0 1 0 (m + 3) (0, 1, true) : ℚ) +
      5 * (vec 0 1 0 (m + 2) (0, 1, true) : ℚ) - 3 * (vec 0 1 0 (m + 1) (0, 1, true) : ℚ) +
      (vec 0 1 0 m (0, 1, true) : ℚ) := by
    have hv := congrFun h (0, 1, true)
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Nat.add_zero] at hv
    exact_mod_cast (show vec 0 1 0 (m + 5) (0, 1, true) =
      4 * vec 0 1 0 (m + 4) (0, 1, true) - 6 * vec 0 1 0 (m + 3) (0, 1, true) +
      5 * vec 0 1 0 (m + 2) (0, 1, true) - 3 * vec 0 1 0 (m + 1) (0, 1, true) +
      vec 0 1 0 m (0, 1, true) by linarith)
  unfold f010
  simp only [show ¬ m + 8 < 3 by omega, show ¬ m + 8 - 1 < 3 by omega,
    show ¬ m + 8 - 2 < 3 by omega, show ¬ m + 8 - 4 < 3 by omega, show ¬ m + 8 - 5 < 3 by omega, if_false,
    show m + 8 - 3 = m + 5 by omega, show m + 8 - 1 - 3 = m + 4 by omega,
    show m + 8 - 2 - 3 = m + 3 by omega, show m + 8 - 4 - 3 = m + 1 by omega, show m + 8 - 5 - 3 = m by omega]
  exact hc

lemma f100_rec (n : ℕ) (hn : 6 ≤ n) :
    f100 n = 2 * f100 (n - 1) - f100 (n - 3) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 6 := ⟨n - 6, by omega⟩
  have h : vec 1 0 0 (m + 3) =
      (2 : ℤ) • vec 1 0 0 (m + 2) + (-1 : ℤ) • vec 1 0 0 (m + 0) := by
    rw [vec_shift 1 0 0 m 3, rel100]
    simp only [Matrix.mulVec_add, Matrix.mulVec_smul, ← vec_shift]
  have hc : (vec 1 0 0 (m + 3) (1, 0, true) : ℚ) =
      2 * (vec 1 0 0 (m + 2) (1, 0, true) : ℚ) - (vec 1 0 0 m (1, 0, true) : ℚ) := by
    have hv := congrFun h (1, 0, true)
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Nat.add_zero] at hv
    exact_mod_cast (show vec 1 0 0 (m + 3) (1, 0, true) =
      2 * vec 1 0 0 (m + 2) (1, 0, true) - vec 1 0 0 m (1, 0, true) by linarith)
  unfold f100
  simp only [show ¬ m + 6 < 3 by omega, show ¬ m + 6 - 1 < 3 by omega,
    if_false,
    show m + 6 - 3 = m + 3 by omega, show m + 6 - 1 - 3 = m + 2 by omega]
  exact hc

lemma f110_rec (n : ℕ) (hn : 7 ≤ n) :
    f110 n = 3 * f110 (n - 1) - 2 * f110 (n - 2) - f110 (n - 3) + f110 (n - 4) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 7 := ⟨n - 7, by omega⟩
  have h : vec 1 1 0 (m + 4) =
      (3 : ℤ) • vec 1 1 0 (m + 3) + (-2 : ℤ) • vec 1 1 0 (m + 2) +
      (-1 : ℤ) • vec 1 1 0 (m + 1) + (1 : ℤ) • vec 1 1 0 (m + 0) := by
    rw [vec_shift 1 1 0 m 4, rel110]
    simp only [Matrix.mulVec_add, Matrix.mulVec_smul, ← vec_shift]
  have hc : (vec 1 1 0 (m + 4) (1, 1, true) : ℚ) =
      3 * (vec 1 1 0 (m + 3) (1, 1, true) : ℚ) - 2 * (vec 1 1 0 (m + 2) (1, 1, true) : ℚ) -
      (vec 1 1 0 (m + 1) (1, 1, true) : ℚ) + (vec 1 1 0 m (1, 1, true) : ℚ) := by
    have hv := congrFun h (1, 1, true)
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Nat.add_zero] at hv
    exact_mod_cast (show vec 1 1 0 (m + 4) (1, 1, true) =
      3 * vec 1 1 0 (m + 3) (1, 1, true) - 2 * vec 1 1 0 (m + 2) (1, 1, true) -
      vec 1 1 0 (m + 1) (1, 1, true) + vec 1 1 0 m (1, 1, true) by linarith)
  unfold f110
  simp only [show ¬ m + 7 < 3 by omega, show ¬ m + 7 - 1 < 3 by omega,
    show ¬ m + 7 - 2 < 3 by omega, show ¬ m + 7 - 4 < 3 by omega, if_false,
    show m + 7 - 3 = m + 4 by omega, show m + 7 - 1 - 3 = m + 3 by omega,
    show m + 7 - 2 - 3 = m + 2 by omega, show m + 7 - 4 - 3 = m by omega]
  exact hc

lemma vals000 :
    vec 0 0 0 0 (0, 0, true) = 1 ∧ vec 0 0 0 1 (0, 0, true) = 1 ∧ vec 0 0 0 2 (0, 0, true) = 2 ∧
    vec 0 0 0 3 (0, 0, true) = 4 ∧ vec 0 0 0 4 (0, 0, true) = 7 := by
  rw [v000_0, v000_1, v000_2, v000_3, v000_4]; decide +kernel

lemma vals010 :
    vec 0 1 0 0 (0, 1, true) = 0 ∧ vec 0 1 0 1 (0, 1, true) = 1 ∧ vec 0 1 0 2 (0, 1, true) = 2 ∧
    vec 0 1 0 3 (0, 1, true) = 4 ∧ vec 0 1 0 4 (0, 1, true) = 8 := by
  rw [v010_0, v010_1, v010_2, v010_3, v010_4]; decide +kernel

lemma vals100 :
    vec 1 0 0 0 (1, 0, true) = 0 ∧ vec 1 0 0 1 (1, 0, true) = 0 ∧ vec 1 0 0 2 (1, 0, true) = 1 := by
  rw [v100_0, v100_1, v100_2]; decide +kernel

lemma vals110 :
    vec 1 1 0 0 (1, 1, true) = 0 ∧ vec 1 1 0 1 (1, 1, true) = 0 ∧
    vec 1 1 0 2 (1, 1, true) = 1 ∧ vec 1 1 0 3 (1, 1, true) = 3 := by
  rw [v110_0, v110_1, v110_2, v110_3]; decide +kernel

lemma gf000 :
    PowerSeries.mk f000 * ((1 - X - X ^ 2) * (1 - X - X ^ 2 - X ^ 3)) =
    X ^ 3 * (1 - X - X ^ 2) := by
  obtain ⟨v0, v1, v2, v3, v4⟩ := vals000
  set S := PowerSeries.mk f000 with hS
  have hl : S * ((1 - X - X ^ 2) * (1 - X - X ^ 2 - X ^ 3)) =
      S + C (-2 : ℚ) * (S * X ^ 1) + C (-1 : ℚ) * (S * X ^ 2) +
      C (1 : ℚ) * (S * X ^ 3) + C (2 : ℚ) * (S * X ^ 4) + C (1 : ℚ) * (S * X ^ 5) := by
    simp only [map_neg, map_ofNat, map_one]; ring
  have hr : (X ^ 3 * (1 - X - X ^ 2) : PowerSeries ℚ) =
      C (1 : ℚ) * X ^ 3 + C (-1 : ℚ) * X ^ 4 + C (-1 : ℚ) * X ^ 5 := by
    simp only [map_neg, map_one]; ring
  rw [hl, hr]
  ext n
  simp only [map_add, coeff_C_mul, coeff_mul_X_pow', coeff_C, hS, coeff_mk]
  rcases Nat.lt_or_ge n 8 with hn | hn
  · interval_cases n <;> simp [f000, v0, v1, v2, v3, v4] <;> norm_num
  · have hq := f000_rec n hn
    have c1 : 1 ≤ n := by omega
    have c2 : 2 ≤ n := by omega
    have c3 : 3 ≤ n := by omega
    have c4 : 4 ≤ n := by omega
    have c5 : 5 ≤ n := by omega
    have e3 : n - 3 ≠ 0 := by omega
    have e4 : n - 4 ≠ 0 := by omega
    have e5 : n - 5 ≠ 0 := by omega
    simp only [c1, c2, c3, c4, c5, e3, e4, e5, if_true, if_false]
    rw [hq]; ring

lemma gf010 :
    PowerSeries.mk f010 * ((1 - X) ^ 2 * (1 - 2 * X + X ^ 2 - X ^ 3)) =
    X ^ 4 * (1 - X) * (1 - X + X ^ 2) := by
  obtain ⟨v0, v1, v2, v3, v4⟩ := vals010
  set S := PowerSeries.mk f010 with hS
  have hl : S * ((1 - X) ^ 2 * (1 - 2 * X + X ^ 2 - X ^ 3)) =
      S + C (-4 : ℚ) * (S * X ^ 1) + C (6 : ℚ) * (S * X ^ 2) +
      C (-5 : ℚ) * (S * X ^ 3) + C (3 : ℚ) * (S * X ^ 4) + C (-1 : ℚ) * (S * X ^ 5) := by
    simp only [map_neg, map_ofNat, map_one]; ring
  have hr : (X ^ 4 * (1 - X) * (1 - X + X ^ 2) : PowerSeries ℚ) =
      C (1 : ℚ) * X ^ 4 + C (-2 : ℚ) * X ^ 5 + C (2 : ℚ) * X ^ 6 + C (-1 : ℚ) * X ^ 7 := by
    simp only [map_neg, map_ofNat, map_one]; ring
  rw [hl, hr]
  ext n
  simp only [map_add, coeff_C_mul, coeff_mul_X_pow', coeff_C, hS, coeff_mk]
  rcases Nat.lt_or_ge n 8 with hn | hn
  · interval_cases n <;> simp [f010, v0, v1, v2, v3, v4] <;> norm_num
  · have hq := f010_rec n hn
    have c1 : 1 ≤ n := by omega
    have c2 : 2 ≤ n := by omega
    have c3 : 3 ≤ n := by omega
    have c4 : 4 ≤ n := by omega
    have c5 : 5 ≤ n := by omega
    have c6 : 6 ≤ n := by omega
    have c7 : 7 ≤ n := by omega
    have e4 : n - 4 ≠ 0 := by omega
    have e5 : n - 5 ≠ 0 := by omega
    have e6 : n - 6 ≠ 0 := by omega
    have e7 : n - 7 ≠ 0 := by omega
    simp only [c1, c2, c3, c4, c5, c6, c7, e4, e5, e6, e7, if_true, if_false]
    rw [hq]; ring

lemma gf100 :
    PowerSeries.mk f100 * ((1 - X) * (1 - X - X ^ 2)) = X ^ 5 := by
  obtain ⟨v0, v1, v2⟩ := vals100
  set S := PowerSeries.mk f100 with hS
  have hl : S * ((1 - X) * (1 - X - X ^ 2)) =
      S + C (-2 : ℚ) * (S * X ^ 1) + C (1 : ℚ) * (S * X ^ 3) := by
    simp only [map_neg, map_ofNat, map_one]; ring
  have hr : (X ^ 5 : PowerSeries ℚ) = C (1 : ℚ) * X ^ 5 := by simp
  rw [hl, hr]
  ext n
  simp only [map_add, coeff_C_mul, coeff_mul_X_pow', coeff_C, hS, coeff_mk]
  rcases Nat.lt_or_ge n 6 with hn | hn
  · interval_cases n <;> simp [f100, v0, v1, v2]
  · have hq := f100_rec n hn
    have c1 : 1 ≤ n := by omega
    have c3 : 3 ≤ n := by omega
    have c5 : 5 ≤ n := by omega
    have e5 : n - 5 ≠ 0 := by omega
    simp only [c1, c3, c5, e5, if_true, if_false]
    rw [hq]; ring

lemma gf110 :
    PowerSeries.mk f110 * ((1 - X) ^ 2 * (1 - X - X ^ 2)) = X ^ 5 := by
  obtain ⟨v0, v1, v2, v3⟩ := vals110
  set S := PowerSeries.mk f110 with hS
  have hl : S * ((1 - X) ^ 2 * (1 - X - X ^ 2)) =
      S + C (-3 : ℚ) * (S * X ^ 1) + C (2 : ℚ) * (S * X ^ 2) +
      C (1 : ℚ) * (S * X ^ 3) + C (-1 : ℚ) * (S * X ^ 4) := by
    simp only [map_neg, map_ofNat, map_one]; ring
  have hr : (X ^ 5 : PowerSeries ℚ) = C (1 : ℚ) * X ^ 5 := by simp
  rw [hl, hr]
  ext n
  simp only [map_add, coeff_C_mul, coeff_mul_X_pow', coeff_C, hS, coeff_mk]
  rcases Nat.lt_or_ge n 7 with hn | hn
  · interval_cases n <;> simp [f110, v0, v1, v2, v3]
  · have hq := f110_rec n hn
    have c1 : 1 ≤ n := by omega
    have c2 : 2 ≤ n := by omega
    have c3 : 3 ≤ n := by omega
    have c4 : 4 ≤ n := by omega
    have c5 : 5 ≤ n := by omega
    have e5 : n - 5 ≠ 0 := by omega
    simp only [c1, c2, c3, c4, c5, e5, if_true, if_false]
    rw [hq]; ring

lemma a0 : a 0 = 0 := rfl
lemma a1 : a 1 = 0 := by decide
lemma a2 : a 2 = 0 := by decide

lemma series_decomp :
    PowerSeries.mk (fun n => (a n : ℚ)) =
    2 * (PowerSeries.mk f000 + PowerSeries.mk f010 + PowerSeries.mk f100 + PowerSeries.mk f110) := by
  have h2 : (2 : PowerSeries ℚ) = C (2 : ℚ) := (map_ofNat C 2).symm
  rw [h2]
  ext n
  simp only [coeff_C_mul, map_add, coeff_mk]
  rcases Nat.lt_or_ge n 3 with hn | hn
  · interval_cases n <;> simp [a0, a1, a2, f000, f010, f100, f110]
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
    have hq : (a (m + 3) : ℚ) =
        2 * ((vec 0 0 0 m (0, 0, true) : ℚ) + (vec 0 1 0 m (0, 1, true) : ℚ) +
             (vec 1 0 0 m (1, 0, true) : ℚ) + (vec 1 1 0 m (1, 1, true) : ℚ)) := by
      exact_mod_cast a_add3 m
    simp only [f000, f010, f100, f110, show ¬ m + 3 < 3 by omega, if_false,
      show m + 3 - 3 = m by omega]
    exact hq

theorem main_proof :
    PowerSeries.mk (fun n => (a n : ℚ)) *
      ((1 - X) ^ 2 * (1 - X - X ^ 2) * (1 - 2 * X + X ^ 2 - X ^ 3) * (1 - X - X ^ 2 - X ^ 3)) =
    2 * X ^ 3 * (1 + X ^ 2) *
      (1 - 4 * X + 6 * X ^ 2 - 5 * X ^ 3 + X ^ 4 + 2 * X ^ 5 + 2 * X ^ 6 - 2 * X ^ 7) := by
  rw [series_decomp]
  linear_combination
    2 * (1 - X) ^ 2 * (1 - 2 * X + X ^ 2 - X ^ 3) * gf000 +
    2 * (1 - X - X ^ 2) * (1 - X - X ^ 2 - X ^ 3) * gf010 +
    2 * (1 - X) * (1 - 2 * X + X ^ 2 - X ^ 3) * (1 - X - X ^ 2 - X ^ 3) * gf100 +
    2 * (1 - 2 * X + X ^ 2 - X ^ 3) * (1 - X - X ^ 2 - X ^ 3) * gf110

end OMA.P284125

theorem OMA.solution : type_of% @OMA.S_oeis_a284125.main := OMA.P284125.main_proof
