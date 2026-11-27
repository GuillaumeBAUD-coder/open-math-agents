import OMAReductions.R_LennonPittel_lennon_pittel_conjecture_R1
import Mathlib.Tactic

/-!
# Existence of Stable Matchings (Gale-Shapley, 1962)

Every complete strict preference profile on `Fin n` has at least one stable matching.
-/

namespace GaleShapleyH1Aux

structure State (n : ℕ) where
  nextProp : Fin n → ℕ
  engagedTo : Fin n → Option (Fin n)

def initState (n : ℕ) : State n where
  nextProp _ := 0
  engagedTo _ := none

def isFree {n : ℕ} (s : State n) (m : Fin n) : Prop :=
  ∀ w : Fin n, s.engagedTo w ≠ some m

def newFiance {n : ℕ} (p : StableMarriage.Profile n) (w m : Fin n) :
    Option (Fin n) → Option (Fin n)
  | none => some m
  | some m₀ => if p.womanRank w m < p.womanRank w m₀ then some m else some m₀

lemma newFiance_eq {n : ℕ} (p : StableMarriage.Profile n) (w m : Fin n)
    (opt : Option (Fin n)) (m₁ : Fin n)
    (h : newFiance p w m opt = some m₁) :
    m₁ = m ∨ opt = some m₁ := by
  cases opt with
  | none =>
    simp [newFiance] at h
    exact Or.inl h.symm
  | some m₀ =>
    simp only [newFiance] at h
    split_ifs at h
    · simp at h
      exact Or.inl h.symm
    · simp at h
      exact Or.inr (congrArg some h)

lemma newFiance_le_proposer {n : ℕ} (p : StableMarriage.Profile n) (w m : Fin n)
    (opt : Option (Fin n)) :
    ∃ m₁ : Fin n, newFiance p w m opt = some m₁ ∧ p.womanRank w m₁ ≤ p.womanRank w m := by
  cases opt with
  | none =>
    exact ⟨m, rfl, le_rfl⟩
  | some m₀ =>
    simp only [newFiance]
    split_ifs with hlt
    · exact ⟨m, rfl, le_rfl⟩
    · exact ⟨m₀, rfl, not_lt.mp hlt⟩

lemma newFiance_le_current {n : ℕ} (p : StableMarriage.Profile n) (w m m₀ : Fin n) :
    ∃ m₁ : Fin n, newFiance p w m (some m₀) = some m₁ ∧
      p.womanRank w m₁ ≤ p.womanRank w m₀ := by
  simp only [newFiance]
  split_ifs with hlt
  · exact ⟨m, rfl, le_of_lt hlt⟩
  · exact ⟨m₀, rfl, le_rfl⟩

def targetWoman {n : ℕ} (p : StableMarriage.Profile n) (s : State n)
    (m : Fin n) (hm_lt : s.nextProp m < n) : Fin n :=
  (p.manRank m).symm ⟨s.nextProp m, hm_lt⟩

lemma manRank_targetWoman_val {n : ℕ} (p : StableMarriage.Profile n) (s : State n)
    (m : Fin n) (hm_lt : s.nextProp m < n) :
    (p.manRank m (targetWoman p s m hm_lt)).val = s.nextProp m := by
  simp [targetWoman]

lemma eq_targetWoman_of_val_eq {n : ℕ} (p : StableMarriage.Profile n) (s : State n)
    (m : Fin n) (hm_lt : s.nextProp m < n) (w' : Fin n)
    (hval : (p.manRank m w').val = s.nextProp m) :
    w' = targetWoman p s m hm_lt := by
  apply (p.manRank m).injective
  apply Fin.ext
  rw [hval, manRank_targetWoman_val]

def applyProposal {n : ℕ} (p : StableMarriage.Profile n) (s : State n)
    (m : Fin n) (hm_lt : s.nextProp m < n) : State n where
  nextProp m' := if m' = m then s.nextProp m + 1 else s.nextProp m'
  engagedTo w' :=
    if w' = targetWoman p s m hm_lt then
      newFiance p (targetWoman p s m hm_lt) m (s.engagedTo (targetWoman p s m hm_lt))
    else s.engagedTo w'

noncomputable def step {n : ℕ} (p : StableMarriage.Profile n) (s : State n) : State n :=
  open Classical in
  if h : ∃ m : Fin n, isFree s m ∧ s.nextProp m < n then
    applyProposal p s (Classical.choose h) (Classical.choose_spec h).2
  else s

structure Inv {n : ℕ} (p : StableMarriage.Profile n) (s : State n) : Prop where
  le_n : ∀ m : Fin n, s.nextProp m ≤ n
  inj : ∀ w₁ w₂ m : Fin n, s.engagedTo w₁ = some m → s.engagedTo w₂ = some m → w₁ = w₂
  proposed_of_engaged : ∀ w m : Fin n,
    s.engagedTo w = some m → (p.manRank m w).val < s.nextProp m
  engaged_of_proposed : ∀ m w : Fin n,
    (p.manRank m w).val < s.nextProp m →
      ∃ m' : Fin n, s.engagedTo w = some m' ∧ p.womanRank w m' ≤ p.womanRank w m

lemma initState_inv {n : ℕ} (p : StableMarriage.Profile n) : Inv p (initState n) where
  le_n _ := Nat.zero_le n
  inj _ _ _ h _ := by simp [initState] at h
  proposed_of_engaged _ _ h := by simp [initState] at h
  engaged_of_proposed _ _ h := by simp [initState] at h

lemma applyProposal_inv {n : ℕ} (p : StableMarriage.Profile n) (s : State n)
    (m : Fin n) (hm_free : isFree s m) (hm_lt : s.nextProp m < n) (hs : Inv p s) :
    Inv p (applyProposal p s m hm_lt) where
  le_n m' := by
    simp only [applyProposal]
    split_ifs with hm'
    · omega
    · exact hs.le_n m'
  inj w₁ w₂ m₁ hw₁ hw₂ := by
    simp only [applyProposal] at hw₁ hw₂
    set w := targetWoman p s m hm_lt
    by_cases h1 : w₁ = w <;> by_cases h2 : w₂ = w <;>
      simp only [h1, h2, ↓reduceIte] at hw₁ hw₂
    · exact h1.trans h2.symm
    · rcases newFiance_eq p w m (s.engagedTo w) m₁ hw₁ with rfl | hold
      · exact absurd hw₂ (hm_free w₂)
      · exact hs.inj w₁ w₂ m₁ (h1 ▸ hold) hw₂
    · rcases newFiance_eq p w m (s.engagedTo w) m₁ hw₂ with rfl | hold
      · exact absurd hw₁ (hm_free w₁)
      · exact hs.inj w₁ w₂ m₁ hw₁ (h2 ▸ hold)
    · exact hs.inj w₁ w₂ m₁ hw₁ hw₂
  proposed_of_engaged w' m' hw' := by
    simp only [applyProposal] at hw' ⊢
    set w := targetWoman p s m hm_lt
    by_cases hww' : w' = w
    · simp only [hww', ↓reduceIte] at hw'
      rcases newFiance_eq p w m (s.engagedTo w) m' hw' with rfl | hold
      · simp only [↓reduceIte]
        rw [hww', manRank_targetWoman_val]
        omega
      · have hlt := hs.proposed_of_engaged w m' hold
        rw [hww']
        by_cases hm' : m' = m
        · subst hm'
          simp only [↓reduceIte]
          omega
        · simp only [hm', ↓reduceIte]
          exact hlt
    · simp only [hww', ↓reduceIte] at hw'
      have hlt := hs.proposed_of_engaged w' m' hw'
      by_cases hm' : m' = m
      · subst hm'
        simp only [↓reduceIte]
        omega
      · simp only [hm', ↓reduceIte]
        exact hlt
  engaged_of_proposed m' w' hlt := by
    simp only [applyProposal] at hlt ⊢
    set w := targetWoman p s m hm_lt
    by_cases hmw : m' = m ∧ w' = w
    · rcases hmw with ⟨rfl, hww'⟩
      rw [hww']
      simp only [↓reduceIte]
      exact newFiance_le_proposer p w m' (s.engagedTo w)
    · have hlt_old : (p.manRank m' w').val < s.nextProp m' := by
        by_cases hm' : m' = m
        · subst hm'
          simp only [↓reduceIte] at hlt
          have hne : (p.manRank m' w').val ≠ s.nextProp m' := by
            intro heq
            exact hmw ⟨rfl, eq_targetWoman_of_val_eq p s m' hm_lt w' heq⟩
          omega
        · simp only [hm', ↓reduceIte] at hlt
          exact hlt
      obtain ⟨m₀, hm₀_eng, hm₀_rank⟩ := hs.engaged_of_proposed m' w' hlt_old
      by_cases hww' : w' = w
      · rw [hww'] at hm₀_eng hm₀_rank ⊢
        simp only [↓reduceIte, hm₀_eng]
        obtain ⟨m₁, hm₁_eng, hm₁_rank⟩ := newFiance_le_current p w m m₀
        exact ⟨m₁, hm₁_eng, le_trans hm₁_rank hm₀_rank⟩
      · simp only [hww', ↓reduceIte]
        exact ⟨m₀, hm₀_eng, hm₀_rank⟩

lemma step_inv {n : ℕ} (p : StableMarriage.Profile n) {s : State n} (hs : Inv p s) :
    Inv p (step p s) := by
  unfold step
  by_cases h : ∃ m : Fin n, isFree s m ∧ s.nextProp m < n
  · rw [dif_pos h]
    exact applyProposal_inv p s (Classical.choose h) (Classical.choose_spec h).1
      (Classical.choose_spec h).2 hs
  · rw [dif_neg h]
    exact hs

lemma iterate_inv {n : ℕ} (p : StableMarriage.Profile n) :
    ∀ k : ℕ, Inv p ((step p)^[k] (initState n))
  | 0 => initState_inv p
  | k + 1 => by
    rw [Function.iterate_succ_apply']
    exact step_inv p (iterate_inv p k)

def pot {n : ℕ} (s : State n) : ℕ :=
  ∑ m : Fin n, s.nextProp m

lemma pot_initState (n : ℕ) : pot (initState n) = 0 := by
  simp [pot, initState]

lemma pot_le_mul {n : ℕ} {p : StableMarriage.Profile n} {s : State n} (hs : Inv p s) :
    pot s ≤ n * n := by
  calc
    pot s = ∑ m : Fin n, s.nextProp m := rfl
    _ ≤ ∑ _m : Fin n, n := Finset.sum_le_sum fun m _ => hs.le_n m
    _ = n * n := by simp

lemma pot_applyProposal {n : ℕ} (p : StableMarriage.Profile n) (s : State n)
    (m : Fin n) (hm_lt : s.nextProp m < n) :
    pot (applyProposal p s m hm_lt) = pot s + 1 := by
  unfold pot applyProposal
  have hfun : ∀ m' : Fin n,
      (if m' = m then s.nextProp m + 1 else s.nextProp m') =
        s.nextProp m' + (if m' = m then 1 else 0) := by
    intro m'
    split_ifs with h
    · subst h; rfl
    · simp
  simp_rw [hfun]
  rw [Finset.sum_add_distrib]
  simp

lemma step_eq_self_of_not_exists {n : ℕ} (p : StableMarriage.Profile n) (s : State n)
    (hhalt : ¬ ∃ m : Fin n, isFree s m ∧ s.nextProp m < n) :
    step p s = s := by
  unfold step
  rw [dif_neg hhalt]

lemma pot_step_of_exists {n : ℕ} (p : StableMarriage.Profile n) (s : State n)
    (hex : ∃ m : Fin n, isFree s m ∧ s.nextProp m < n) :
    pot (step p s) = pot s + 1 := by
  unfold step
  rw [dif_pos hex]
  exact pot_applyProposal p s (Classical.choose hex) (Classical.choose_spec hex).2

lemma iterate_halt_or_pot {n : ℕ} (p : StableMarriage.Profile n) :
    ∀ k : ℕ,
      (¬ ∃ m : Fin n, isFree ((step p)^[k] (initState n)) m ∧
        ((step p)^[k] (initState n)).nextProp m < n) ∨
      pot ((step p)^[k] (initState n)) = k
  | 0 => Or.inr (pot_initState n)
  | k + 1 => by
    rw [Function.iterate_succ_apply']
    set sk := (step p)^[k] (initState n)
    rcases iterate_halt_or_pot p k with hhalt | hpot
    · left
      rw [step_eq_self_of_not_exists p sk hhalt]
      exact hhalt
    · by_cases hex : ∃ m : Fin n, isFree sk m ∧ sk.nextProp m < n
      · right
        rw [pot_step_of_exists p sk hex, hpot]
      · left
        rw [step_eq_self_of_not_exists p sk hex]
        exact hex

lemma exists_wife_of_halted {n : ℕ} {p : StableMarriage.Profile n} {s : State n}
    (hs : Inv p s) (hhalt : ¬ ∃ m : Fin n, isFree s m ∧ s.nextProp m < n) (m : Fin n) :
    ∃ w : Fin n, s.engagedTo w = some m := by
  by_contra hfree_not
  have hm_free : isFree s m := fun w hw => hfree_not ⟨w, hw⟩
  have hm_ge : n ≤ s.nextProp m := by
    by_contra hlt
    exact hhalt ⟨m, hm_free, Nat.lt_of_not_le hlt⟩
  have hall_eng : ∀ w : Fin n, ∃ m' : Fin n, s.engagedTo w = some m' := by
    intro w
    have hw_lt : (p.manRank m w).val < s.nextProp m := lt_of_lt_of_le (p.manRank m w).isLt hm_ge
    obtain ⟨m', hm', _⟩ := hs.engaged_of_proposed m w hw_lt
    exact ⟨m', hm'⟩
  choose husband hHusband using hall_eng
  have hInj : Function.Injective husband := by
    intro w₁ w₂ h
    exact hs.inj w₁ w₂ (husband w₁) (hHusband w₁) (h ▸ hHusband w₂)
  obtain ⟨w, rfl⟩ := Finite.surjective_of_injective hInj m
  exact hm_free w (hHusband w)

lemma exists_stable_matching {n : ℕ} (p : StableMarriage.Profile n) :
    ∃ μ : StableMarriage.Matching n, StableMarriage.IsStable p μ := by
  let s := (step p)^[n * n + 1] (initState n)
  have hs : Inv p s := iterate_inv p (n * n + 1)
  have hhalt : ¬ ∃ m : Fin n, isFree s m ∧ s.nextProp m < n := by
    rcases iterate_halt_or_pot p (n * n + 1) with h | hpot
    · exact h
    · have hpot' : pot s = n * n + 1 := hpot
      have hle : pot s ≤ n * n := pot_le_mul hs
      omega
  have hmatch : ∀ m : Fin n, ∃ w : Fin n, s.engagedTo w = some m :=
    exists_wife_of_halted hs hhalt
  choose wife hWife using hmatch
  have hWifeInj : Function.Injective wife := by
    intro m₁ m₂ h
    have heq : some m₁ = some m₂ := by
      rw [← hWife m₁, h, hWife m₂]
    exact Option.some.inj heq
  let μ : StableMarriage.Matching n := Equiv.ofBijective wife hWifeInj.bijective_of_finite
  have hμ_eng : ∀ m : Fin n, s.engagedTo (μ m) = some m := fun m => hWife m
  have hμ_symm_eng : ∀ w : Fin n, s.engagedTo w = some (μ.symm w) := by
    intro w
    simpa [μ.apply_symm_apply] using hμ_eng (μ.symm w)
  refine ⟨μ, ?_⟩
  intro m w ⟨_hne, hman, hwoman⟩
  have hprop_cur : (p.manRank m (μ m)).val < s.nextProp m :=
    hs.proposed_of_engaged (μ m) m (hμ_eng m)
  have hprop_w : (p.manRank m w).val < s.nextProp m :=
    lt_trans hman hprop_cur
  obtain ⟨m', hm'_eng, hm'_rank⟩ := hs.engaged_of_proposed m w hprop_w
  rw [hμ_symm_eng w] at hm'_eng
  cases hm'_eng
  exact (not_lt_of_ge hm'_rank) hwoman

end GaleShapleyH1Aux

theorem prove_LennonPittel_H1 :
    ∀ n (p : StableMarriage.Profile n), 0 < StableMarriage.numStableMatchings p := by
  classical
  intro n p
  obtain ⟨μ, hμ⟩ := GaleShapleyH1Aux.exists_stable_matching p
  have hpos : 0 < Fintype.card {μ : StableMarriage.Matching n // StableMarriage.IsStable p μ} :=
    Fintype.card_pos_iff.mpr ⟨⟨μ, hμ⟩⟩
  unfold StableMarriage.numStableMatchings
  convert hpos

theorem OMA.solution : OMA.R_LennonPittel_lennon_pittel_conjecture_R1.H1 :=
  prove_LennonPittel_H1
