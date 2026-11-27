import OMAReductions.R_IrvingLeather_irving_leather_growth_rate_R1

-- Step IrvingLeather.irving_leather_growth_rate.R1.H1: hypothesis H1 of reduction IrvingLeather.irving_leather_growth_rate.R1
-- Credit: @ishaanzee
-- Proof: put two profiles side by side, everyone ranking their own block first (in their own
-- order) and the other block after. A pair of stable matchings, one per block, combines into a
-- stable matching of the union (a cross-block pair never blocks), and the combination is injective.

open StableMarriage

namespace ILAux

/-- Men (or women) of the two blocks: block `A = Fin m` comes first, block `B = Fin n` second. -/
def e (m n : ℕ) : Fin m ⊕ Fin n ≃ Fin (m + n) := finSumFinEquiv

/-- The same positions with block `B` first. -/
def f (m n : ℕ) : Fin n ⊕ Fin m ≃ Fin (m + n) :=
  finSumFinEquiv.trans (finCongr (Nat.add_comm n m))

/-- Combined ranks: everybody ranks their own block first, in the order of their own instance. -/
def rk {m n : ℕ} (P : Fin m → Equiv.Perm (Fin m)) (Q : Fin n → Equiv.Perm (Fin n))
    (x : Fin (m + n)) : Equiv.Perm (Fin (m + n)) :=
  Sum.elim
    (fun a => (e m n).symm.trans ((Equiv.sumCongr (P a) (Equiv.refl (Fin n))).trans (e m n)))
    (fun a => (e m n).symm.trans ((Equiv.sumCongr (Equiv.refl (Fin m)) (Q a)).trans
      ((Equiv.sumComm (Fin m) (Fin n)).trans (f m n))))
    ((e m n).symm x)

lemma rk_ll {m n : ℕ} (P : Fin m → Equiv.Perm (Fin m)) (Q : Fin n → Equiv.Perm (Fin n))
    (a b : Fin m) : ((rk P Q (e m n (.inl a))) (e m n (.inl b))).val = (P a b).val := by
  simp [rk, e]

lemma rk_lr {m n : ℕ} (P : Fin m → Equiv.Perm (Fin m)) (Q : Fin n → Equiv.Perm (Fin n))
    (a : Fin m) (b : Fin n) : ((rk P Q (e m n (.inl a))) (e m n (.inr b))).val = m + b.val := by
  simp [rk, e]

lemma rk_rl {m n : ℕ} (P : Fin m → Equiv.Perm (Fin m)) (Q : Fin n → Equiv.Perm (Fin n))
    (a : Fin n) (b : Fin m) : ((rk P Q (e m n (.inr a))) (e m n (.inl b))).val = n + b.val := by
  simp [rk, e, f]
  omega

lemma rk_rr {m n : ℕ} (P : Fin m → Equiv.Perm (Fin m)) (Q : Fin n → Equiv.Perm (Fin n))
    (a b : Fin n) : ((rk P Q (e m n (.inr a))) (e m n (.inr b))).val = (Q a b).val := by
  simp [rk, e, f]

/-- The two instances side by side. -/
def comb {m n : ℕ} (p : Profile m) (q : Profile n) : Profile (m + n) :=
  ⟨rk p.manRank q.manRank, rk p.womanRank q.womanRank⟩

/-- Two matchings side by side. -/
def combM {m n : ℕ} (μ : Matching m) (ν : Matching n) : Matching (m + n) :=
  (e m n).symm.trans ((Equiv.sumCongr μ ν).trans (e m n))

lemma combM_inl {m n : ℕ} (μ : Matching m) (ν : Matching n) (a : Fin m) :
    combM μ ν (e m n (.inl a)) = e m n (.inl (μ a)) := by
  simp [combM]

lemma combM_inr {m n : ℕ} (μ : Matching m) (ν : Matching n) (a : Fin n) :
    combM μ ν (e m n (.inr a)) = e m n (.inr (ν a)) := by
  simp [combM]

lemma combM_symm_inl {m n : ℕ} (μ : Matching m) (ν : Matching n) (a : Fin m) :
    (combM μ ν).symm (e m n (.inl a)) = e m n (.inl (μ.symm a)) := by
  simp [combM]

lemma combM_symm_inr {m n : ℕ} (μ : Matching m) (ν : Matching n) (a : Fin n) :
    (combM μ ν).symm (e m n (.inr a)) = e m n (.inr (ν.symm a)) := by
  simp [combM]

lemma stable_comb {m n : ℕ} {p : Profile m} {q : Profile n} {μ : Matching m} {ν : Matching n}
    (hμ : IsStable p μ) (hν : IsStable q ν) : IsStable (comb p q) (combM μ ν) := by
  intro x y hb
  obtain ⟨hne, hman, hwom⟩ := hb
  obtain ⟨u, rfl⟩ := (e m n).surjective x
  obtain ⟨v, rfl⟩ := (e m n).surjective y
  simp only [comb] at hman hwom
  rcases u with a | a <;> rcases v with b | b
  · rw [combM_inl, Fin.lt_def, rk_ll, rk_ll] at hman
    rw [combM_symm_inl, Fin.lt_def, rk_ll, rk_ll] at hwom
    refine hμ a b ⟨fun h => hne ?_, Fin.lt_def.2 hman, Fin.lt_def.2 hwom⟩
    rw [combM_inl, h]
  · rw [combM_inl, Fin.lt_def, rk_lr, rk_ll] at hman
    have := (p.manRank a (μ a)).isLt
    omega
  · rw [combM_inr, Fin.lt_def, rk_rl, rk_rr] at hman
    have := (q.manRank a (ν a)).isLt
    omega
  · rw [combM_inr, Fin.lt_def, rk_rr, rk_rr] at hman
    rw [combM_symm_inr, Fin.lt_def, rk_rr, rk_rr] at hwom
    refine hν a b ⟨fun h => hne ?_, Fin.lt_def.2 hman, Fin.lt_def.2 hwom⟩
    rw [combM_inr, h]

lemma combM_injective {m n : ℕ} {μ μ' : Matching m} {ν ν' : Matching n}
    (h : combM μ ν = combM μ' ν') : μ = μ' ∧ ν = ν' := by
  constructor
  · ext a
    have := congrArg (fun ρ : Matching (m + n) => ρ (e m n (.inl a))) h
    simp only [combM_inl] at this
    have h2 := (e m n).injective this
    simp only [Sum.inl.injEq] at h2
    rw [h2]
  · ext a
    have := congrArg (fun ρ : Matching (m + n) => ρ (e m n (.inr a))) h
    simp only [combM_inr] at this
    have h2 := (e m n).injective this
    simp only [Sum.inr.injEq] at h2
    rw [h2]

lemma num_eq {k : ℕ} (p : Profile k) :
    numStableMatchings p = Nat.card {μ : Matching k // IsStable p μ} := by
  unfold numStableMatchings
  exact Fintype.card_eq_nat_card

lemma num_mul_le {m n : ℕ} (p : Profile m) (q : Profile n) :
    numStableMatchings p * numStableMatchings q ≤ numStableMatchings (comb p q) := by
  rw [num_eq, num_eq, num_eq, ← Nat.card_prod]
  refine Nat.card_le_card_of_injective
    (fun x => ⟨combM x.1.1 x.2.1, stable_comb x.1.2 x.2.2⟩) ?_
  rintro ⟨⟨μ, hμ⟩, ⟨ν, hν⟩⟩ ⟨⟨μ', hμ'⟩, ⟨ν', hν'⟩⟩ h
  have h' : combM μ ν = combM μ' ν' := congrArg Subtype.val h
  obtain ⟨rfl, rfl⟩ := combM_injective h'
  rfl

end ILAux

open ILAux

theorem OMA.solution : OMA.R_IrvingLeather_irving_leather_growth_rate_R1.H1 := by
  intro m n
  obtain ⟨p, -, hp⟩ := Finset.exists_mem_eq_sup (Finset.univ : Finset (Profile m))
    Finset.univ_nonempty (fun p => numStableMatchings p)
  obtain ⟨q, -, hq⟩ := Finset.exists_mem_eq_sup (Finset.univ : Finset (Profile n))
    Finset.univ_nonempty (fun q => numStableMatchings q)
  unfold IrvingLeather.maxStableMatchings
  rw [hp, hq]
  exact le_trans (num_mul_le p q)
    (Finset.le_sup (f := fun p : Profile (m + n) => numStableMatchings p) (Finset.mem_univ _))
