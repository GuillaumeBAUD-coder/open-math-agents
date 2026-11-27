import OMAReductions.R_LennonPittel_lennon_pittel_conjecture_R2

-- Step LennonPittel.lennon_pittel_conjecture.R2.H1: hypothesis H1 of reduction LennonPittel.lennon_pittel_conjecture.R2
-- Credit: @ishaanzee
-- Proof: Gale-Shapley deferred acceptance. The state records how many times each man has been
-- rejected; the invariant (a woman a man has passed is being proposed to by someone she prefers)
-- bounds every man's list, the total number of rejections grows each round, and at a round with
-- no rejection the proposals form a stable matching.

open StableMarriage

namespace GSAux

variable {n : ℕ} (p : Profile n)

/-- In state `s` (man `m` has been rejected `s m` times), man `m` proposes to his `s m`-th choice. -/
def Proposes (s : Fin n → ℕ) (m w : Fin n) : Prop := ((p.manRank m w : Fin n) : ℕ) = s m

/-- The deferred-acceptance invariant: if `m` has already passed `w` on his list, then someone
whom `w` prefers to `m` is currently proposing to her. -/
def Inv (s : Fin n → ℕ) : Prop :=
  ∀ m w, ((p.manRank m w : Fin n) : ℕ) < s m →
    ∃ m', Proposes p s m' w ∧ p.womanRank w m' < p.womanRank w m

/-- `m` is rejected: someone his current woman prefers is also proposing to her. -/
def Rejected (s : Fin n → ℕ) (m : Fin n) : Prop :=
  ∃ w, Proposes p s m w ∧ ∃ m', Proposes p s m' w ∧ p.womanRank w m' < p.womanRank w m

lemma proposes_unique {s : Fin n → ℕ} {m w w' : Fin n} (h : Proposes p s m w)
    (h' : Proposes p s m w') : w = w' := by
  unfold Proposes at h h'
  exact (p.manRank m).injective (Fin.ext (h.trans h'.symm))

lemma inv_bound {s : Fin n → ℕ} (hI : Inv p s) (m : Fin n) : s m < n := by
  by_contra hge
  push_neg at hge
  have hall : ∀ w, ∃ m', Proposes p s m' w ∧ p.womanRank w m' < p.womanRank w m :=
    fun w => hI m w (lt_of_lt_of_le (p.manRank m w).isLt hge)
  choose f hf using hall
  have hinj : Function.Injective f := by
    intro w w' h
    have h1 := (hf w).1
    have h2 := (hf w').1
    rw [h] at h1
    exact proposes_unique p h1 h2
  obtain ⟨w, hw⟩ := Finite.surjective_of_injective hinj m
  have := (hf w).2
  rw [hw] at this
  exact lt_irrefl _ this

lemma best_proposer {s : Fin n → ℕ} {m1 w : Fin n} (h1 : Proposes p s m1 w) :
    ∃ m, Proposes p s m w ∧ p.womanRank w m ≤ p.womanRank w m1 ∧ ¬ Rejected p s m := by
  classical
  obtain ⟨m, hm, hmin⟩ := Finset.exists_min_image (Finset.univ.filter (fun x => Proposes p s x w))
    (fun x => p.womanRank w x) ⟨m1, Finset.mem_filter.2 ⟨Finset.mem_univ _, h1⟩⟩
  have hmw : Proposes p s m w := (Finset.mem_filter.1 hm).2
  refine ⟨m, hmw, hmin m1 (Finset.mem_filter.2 ⟨Finset.mem_univ _, h1⟩), ?_⟩
  rintro ⟨w', hw', m', hm', hlt⟩
  have hww : w' = w := proposes_unique p hw' hmw
  subst hww
  exact absurd (hmin m' (Finset.mem_filter.2 ⟨Finset.mem_univ _, hm'⟩)) (not_le.2 hlt)

open Classical in
/-- One round: every rejected man moves on to his next choice. -/
noncomputable def step (s : Fin n → ℕ) : Fin n → ℕ := fun m => if Rejected p s m then s m + 1 else s m

lemma step_proposes {s : Fin n → ℕ} {m w : Fin n} (hr : ¬ Rejected p s m)
    (h : Proposes p s m w) : Proposes p (step p s) m w := by
  unfold Proposes at h ⊢
  simp only [step, if_neg hr]
  exact h

lemma inv_step {s : Fin n → ℕ} (hI : Inv p s) : Inv p (step p s) := by
  intro m w h
  by_cases hlt : ((p.manRank m w : Fin n) : ℕ) < s m
  · obtain ⟨m1, hp1, hb1⟩ := hI m w hlt
    obtain ⟨m', hp', hle, hnr⟩ := best_proposer p hp1
    exact ⟨m', step_proposes p hnr hp', lt_of_le_of_lt hle hb1⟩
  · have hrej : Rejected p s m := by
      by_contra hr
      simp only [step, if_neg hr] at h
      exact hlt h
    simp only [step, if_pos hrej] at h
    have hprop : Proposes p s m w := by unfold Proposes; omega
    obtain ⟨w0, hw0, m1, hm1, hb1⟩ := hrej
    have hww : w0 = w := proposes_unique p hw0 hprop
    subst hww
    obtain ⟨m', hp', hle, hnr⟩ := best_proposer p hm1
    exact ⟨m', step_proposes p hnr hp', lt_of_le_of_lt hle hb1⟩

lemma stable_of_no_rejection {s : Fin n → ℕ} (hI : Inv p s) (hno : ∀ m, ¬ Rejected p s m) :
    ∃ μ : Matching n, IsStable p μ := by
  have hb := inv_bound p hI
  let g : Fin n → Fin n := fun m => (p.manRank m).symm ⟨s m, hb m⟩
  have hgp : ∀ m, Proposes p s m (g m) := by
    intro m
    unfold Proposes
    simp [g]
  have hg_of : ∀ m w, Proposes p s m w → g m = w := fun m w h => proposes_unique p (hgp m) h
  have hinj : Function.Injective g := by
    intro m1 m2 h
    by_contra hne
    have hw1 := hgp m1
    have hw2 : Proposes p s m2 (g m1) := h ▸ hgp m2
    have hne' : p.womanRank (g m1) m1 ≠ p.womanRank (g m1) m2 :=
      fun e => hne ((p.womanRank (g m1)).injective e)
    rcases lt_or_gt_of_ne hne' with hlt | hlt
    · exact hno m2 ⟨g m1, hw2, m1, hw1, hlt⟩
    · exact hno m1 ⟨g m1, hw1, m2, hw2, hlt⟩
  let μ : Matching n := Equiv.ofBijective g hinj.bijective_of_finite
  refine ⟨μ, ?_⟩
  rintro m w ⟨-, hman, hwom⟩
  have hman' : ((p.manRank m w : Fin n) : ℕ) < s m := by
    have := (hgp m)
    unfold Proposes at this
    rw [Fin.lt_def] at hman
    have e : μ m = g m := rfl
    rw [e] at hman
    omega
  obtain ⟨m', hp', hb'⟩ := hI m w hman'
  have hμ : μ m' = w := hg_of m' w hp'
  have hsymm : μ.symm w = m' := by rw [← hμ, Equiv.symm_apply_apply]
  rw [hsymm] at hwom
  exact lt_asymm hb' hwom

lemma exists_stable_aux : ∀ (k : ℕ) (s : Fin n → ℕ), Inv p s → n * n - ∑ m, s m = k →
    ∃ μ : Matching n, IsStable p μ := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro s hI hk
    by_cases hrej : ∃ m, Rejected p s m
    · obtain ⟨m0, hm0⟩ := hrej
      have hI' := inv_step p hI
      have hlt : ∑ m, s m < ∑ m, step p s m := by
        apply Finset.sum_lt_sum
        · intro m _
          unfold step
          split_ifs <;> omega
        · exact ⟨m0, Finset.mem_univ _, by simp [step, if_pos hm0]⟩
      have hle : ∑ m, step p s m ≤ n * n := by
        calc ∑ m, step p s m ≤ ∑ _m : Fin n, n :=
              Finset.sum_le_sum (fun m _ => (inv_bound p hI' m).le)
          _ = n * n := by simp
      exact ih (n * n - ∑ m, step p s m) (by omega) (step p s) hI' rfl
    · push_neg at hrej
      exact stable_of_no_rejection p hI hrej

/-- Gale–Shapley: every profile has a stable matching. -/
theorem exists_stable : ∃ μ : Matching n, IsStable p μ :=
  exists_stable_aux p _ (fun _ => 0) (fun _ _ h => absurd h (Nat.not_lt_zero _)) rfl

end GSAux

theorem OMA.solution : OMA.R_LennonPittel_lennon_pittel_conjecture_R2.H1 := by
  intro n p
  classical
  obtain ⟨μ, hμ⟩ := GSAux.exists_stable p
  unfold StableMarriage.numStableMatchings
  exact Fintype.card_pos_iff.2 ⟨⟨μ, hμ⟩⟩
