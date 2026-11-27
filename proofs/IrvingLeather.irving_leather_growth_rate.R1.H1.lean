import OMAReductions.R_IrvingLeather_irving_leather_growth_rate_R1

/-! Supermultiplicativity for the Irving–Leather reduction by tatashbar (PR 2995).
Place the two markets side by side. Everyone ranks the left market first.
A pair from different markets cannot block because its member in the left
market already has a partner there. -/

namespace OMA.StableMatchingProduct

open StableMarriage IrvingLeather

private def blockPerm {m n : ℕ} (a : Matching m) (b : Matching n) : Matching (m + n) :=
  (finSumFinEquiv.symm.trans (Equiv.sumCongr a b)).trans finSumFinEquiv

@[simp] private lemma block_left {m n : ℕ} (a : Matching m) (b : Matching n) (i : Fin m) :
    blockPerm a b (i.castAdd n) = (a i).castAdd n := by simp [blockPerm]

@[simp] private lemma block_right {m n : ℕ} (a : Matching m) (b : Matching n) (i : Fin n) :
    blockPerm a b (i.natAdd m) = (b i).natAdd m := by simp [blockPerm]

private lemma block_symm {m n : ℕ} (a : Matching m) (b : Matching n) :
    (blockPerm a b).symm = blockPerm a.symm b.symm := by rfl

private def blockRanks {m n : ℕ} (a : Fin m → Matching m) (b : Fin n → Matching n) :
    Fin (m + n) → Matching (m + n) :=
  Fin.addCases (fun i => blockPerm (a i) (Equiv.refl _))
    (fun j => blockPerm (Equiv.refl _) (b j))

private def profile {m n : ℕ} (p : Profile m) (q : Profile n) : Profile (m + n) :=
  ⟨blockRanks p.manRank q.manRank, blockRanks p.womanRank q.womanRank⟩

@[simp] private lemma left_lt {m n : ℕ} (i j : Fin m) :
    i.castAdd n < j.castAdd n ↔ i < j := Iff.rfl

@[simp] private lemma left_le {m n : ℕ} (i j : Fin m) :
    i.castAdd n ≤ j.castAdd n ↔ i ≤ j := Iff.rfl

@[simp] private lemma left_le_right {m n : ℕ} (i : Fin m) (j : Fin n) :
    i.castAdd n ≤ j.natAdd m := by
  change i.val ≤ m + j.val
  omega

@[simp] private lemma right_not_lt_left {m n : ℕ} (i : Fin m) (j : Fin n) :
    ¬ j.natAdd m < i.castAdd n := not_lt_of_ge (left_le_right i j)

private lemma stable {m n : ℕ} {p : Profile m} {q : Profile n}
    {a : Matching m} {b : Matching n} (ha : IsStable p a) (hb : IsStable q b) :
    IsStable (profile p q) (blockPerm a b) := by
  intro i j
  refine Fin.addCases (fun x => ?_) (fun x => ?_) i <;>
    refine Fin.addCases (fun y => ?_) (fun y => ?_) j
  · simpa [IsBlockingPair, profile, blockRanks, block_symm] using ha x y
  · simp [IsBlockingPair, profile, blockRanks, block_symm]
  · simp [IsBlockingPair, profile, blockRanks, block_symm]
  · simpa [IsBlockingPair, profile, blockRanks, block_symm] using hb x y

private lemma count_le {m n : ℕ} (p : Profile m) (q : Profile n) :
    numStableMatchings p * numStableMatchings q ≤ numStableMatchings (profile p q) := by
  classical
  let join : {a : Matching m // IsStable p a} × {b : Matching n // IsStable q b} →
      {c : Matching (m + n) // IsStable (profile p q) c} :=
    fun z => ⟨blockPerm z.1.1 z.2.1, stable z.1.2 z.2.2⟩
  have hinj : Function.Injective join := by
    intro s t heq
    have he := congrArg Subtype.val heq
    apply Prod.ext <;> apply Subtype.ext <;> apply Equiv.ext
    · intro i
      have h := DFunLike.congr_fun he (i.castAdd n)
      simpa [join] using h
    · intro j
      have h := DFunLike.congr_fun he (j.natAdd m)
      simpa [join] using h
  simpa [numStableMatchings, Fintype.card_prod] using Fintype.card_le_of_injective join hinj

theorem supermultiplicative (m n : ℕ) :
    maxStableMatchings m * maxStableMatchings n ≤ maxStableMatchings (m + n) := by
  classical
  obtain ⟨p, _, hp⟩ := Finset.exists_mem_eq_sup
    (Finset.univ : Finset (Profile m)) Finset.univ_nonempty numStableMatchings
  obtain ⟨q, _, hq⟩ := Finset.exists_mem_eq_sup
    (Finset.univ : Finset (Profile n)) Finset.univ_nonempty numStableMatchings
  unfold maxStableMatchings
  rw [hp, hq]
  exact (count_le p q).trans (Finset.le_sup (Finset.mem_univ (profile p q)))

end OMA.StableMatchingProduct

theorem OMA.solution : OMA.R_IrvingLeather_irving_leather_growth_rate_R1.H1 :=
  OMA.StableMatchingProduct.supermultiplicative
