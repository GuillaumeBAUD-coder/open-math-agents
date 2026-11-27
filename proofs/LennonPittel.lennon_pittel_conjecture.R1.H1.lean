import OMAReductions.R_LennonPittel_lennon_pittel_conjecture_R1

-- Step LennonPittel.lennon_pittel_conjecture.R1.H1: hypothesis H1 of reduction
-- LennonPittel.lennon_pittel_conjecture.R1.
-- Credit: @siraustin
--
-- H1 says that every complete strict preference profile has a stable matching.
-- This is the Gale-Shapley theorem. The proof below does not run the algorithm.
-- It works with a static invariant instead.
--
-- An assignment `a` sends every man to the woman he currently targets; it need not
-- be injective. Call it justified when every woman `w` that a man `m` ranks above
-- his target is targeted by some man whom `w` ranks above `m`. Sending every man to
-- his first choice is justified, vacuously.
--
-- Take a justified assignment that maximises the sum of the ranks the men give
-- their targets. If two men targeted the same woman `w`, let `ms` be the one she
-- likes best and `m` another one. Man `m` cannot be at the bottom of his list:
-- then every woman would be targeted by a man other than `m`, which is impossible
-- with `n` women and `n - 1` men. Moving `m` one place down his list keeps the
-- assignment justified and raises the sum, against maximality. So the maximal
-- assignment is injective, hence a matching, and a justified matching has no
-- blocking pair.

/-- Every woman a man ranks above his target is targeted by a man she ranks above him. -/
def gsJustified {n : ℕ} (p : StableMarriage.Profile n) (a : Fin n → Fin n) : Prop :=
  ∀ m w, p.manRank m w < p.manRank m (a m) →
    ∃ m', a m' = w ∧ p.womanRank w m' < p.womanRank w m

/-- A justified assignment that is injective is a stable matching. -/
theorem gs_stable_of_injective {n : ℕ} (p : StableMarriage.Profile n) (a : Fin n → Fin n)
    (hJ : gsJustified p a) (hinj : Function.Injective a) :
    ∃ μ : StableMarriage.Matching n, StableMarriage.IsStable p μ := by
  have hbij : Function.Bijective a := hinj.bijective_of_finite
  refine ⟨Equiv.ofBijective a hbij, ?_⟩
  intro m w hb
  obtain ⟨-, hm, hw⟩ := hb
  have hm' : p.manRank m w < p.manRank m (a m) := hm
  obtain ⟨m', hm'w, hlt⟩ := hJ m w hm'
  have hsymm : (Equiv.ofBijective a hbij).symm w = m' := by
    rw [Equiv.symm_apply_eq]
    exact hm'w.symm
  rw [hsymm] at hw
  exact lt_asymm hw hlt

/-- A justified assignment maximising the total rank is injective. -/
theorem gs_exists_justified_injective {n : ℕ} (p : StableMarriage.Profile n) :
    ∃ a : Fin n → Fin n, gsJustified p a ∧ Function.Injective a := by
  classical
  -- sending every man to his first choice is justified
  have hne : (Finset.univ.filter (gsJustified p)).Nonempty := by
    refine ⟨fun m => (p.manRank m).symm ⟨0, m.pos⟩, ?_⟩
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    intro m w h
    rw [Equiv.apply_symm_apply] at h
    exact absurd h (Nat.not_lt_zero _)
  -- a justified assignment with the largest total rank
  obtain ⟨a, ha, hmax⟩ := Finset.exists_max_image (Finset.univ.filter (gsJustified p))
    (fun a : Fin n → Fin n => ∑ m, (p.manRank m (a m)).val) hne
  have hJ : gsJustified p a := (Finset.mem_filter.mp ha).2
  refine ⟨a, hJ, ?_⟩
  by_contra hninj
  -- two men target the same woman `w`
  obtain ⟨m₁, m₂, heq, hne12⟩ := Function.not_injective_iff.mp hninj
  obtain ⟨w, hw1⟩ : ∃ w, a m₁ = w := ⟨_, rfl⟩
  have hw2 : a m₂ = w := heq.symm.trans hw1
  -- `ms` is the man `w` likes best among those who target her
  obtain ⟨ms, hmsS, hmin⟩ := Finset.exists_min_image (Finset.univ.filter (fun x => a x = w))
    (fun x => p.womanRank w x) ⟨m₁, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hw1⟩⟩
  have hmsw : a ms = w := (Finset.mem_filter.mp hmsS).2
  -- `m` is another man who targets her
  obtain ⟨m, hmw, hm_ne⟩ : ∃ m, a m = w ∧ m ≠ ms := by
    by_cases h : m₁ = ms
    · exact ⟨m₂, hw2, fun h2 => hne12 (h.trans h2.symm)⟩
    · exact ⟨m₁, hw1, h⟩
  have hms_ne : ms ≠ m := fun h => hm_ne h.symm
  have hlt : p.womanRank w ms < p.womanRank w m :=
    lt_of_le_of_ne (hmin m (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hmw⟩))
      (fun h => hm_ne ((p.womanRank w).injective h).symm)
  -- `w` is not the last woman on the list of `m`
  have hnext : (p.manRank m w).val + 1 < n := by
    by_contra hlast
    have hcover : ∀ v : Fin n, ∃ m', m' ≠ m ∧ a m' = v := by
      intro v
      by_cases hv : v = w
      · exact ⟨ms, hms_ne, hmsw.trans hv.symm⟩
      · have hrank : p.manRank m v < p.manRank m (a m) := by
          rw [hmw, Fin.lt_def]
          have h1 : (p.manRank m v).val < n := (p.manRank m v).isLt
          have h3 : (p.manRank m v).val ≠ (p.manRank m w).val :=
            fun h => hv ((p.manRank m).injective (Fin.ext h))
          omega
        obtain ⟨m', hm'v, hm'lt⟩ := hJ m v hrank
        refine ⟨m', ?_, hm'v⟩
        intro h
        rw [h] at hm'lt
        exact lt_irrefl _ hm'lt
    choose g hg using hcover
    have hginj : Function.Injective g := by
      intro v v' h
      have h1 : a (g v) = v := (hg v).2
      rw [h] at h1
      exact h1.symm.trans (hg v').2
    obtain ⟨v, hv⟩ := Finite.surjective_of_injective hginj m
    exact (hg v).1 hv
  -- the next woman on the list of `m`
  obtain ⟨w', hw'⟩ : ∃ w' : Fin n, (p.manRank m w').val = (p.manRank m w).val + 1 :=
    ⟨(p.manRank m).symm ⟨(p.manRank m w).val + 1, hnext⟩, by rw [Equiv.apply_symm_apply]⟩
  have ha'm : Function.update a m w' m = w' := Function.update_self m w' a
  have ha'ne : ∀ x, x ≠ m → Function.update a m w' x = a x :=
    fun x hx => Function.update_of_ne hx w' a
  -- moving `m` to `w'` keeps the assignment justified
  have hJ' : gsJustified p (Function.update a m w') := by
    intro m0 v hlt0
    by_cases hm0 : m0 = m
    · rw [hm0] at hlt0 ⊢
      rw [ha'm] at hlt0
      by_cases hvw : v = w
      · rw [hvw]
        exact ⟨ms, (ha'ne ms hms_ne).trans hmsw, hlt⟩
      · have hlt1 : p.manRank m v < p.manRank m (a m) := by
          rw [hmw, Fin.lt_def]
          rw [Fin.lt_def] at hlt0
          have h2 : (p.manRank m v).val ≠ (p.manRank m w).val :=
            fun h => hvw ((p.manRank m).injective (Fin.ext h))
          omega
        obtain ⟨m', hm'v, hm'lt⟩ := hJ m v hlt1
        have hm'ne : m' ≠ m := by
          intro h
          rw [h] at hm'lt
          exact lt_irrefl _ hm'lt
        exact ⟨m', (ha'ne m' hm'ne).trans hm'v, hm'lt⟩
    · rw [ha'ne m0 hm0] at hlt0
      obtain ⟨m', hm'v, hm'lt⟩ := hJ m0 v hlt0
      by_cases hm' : m' = m
      · have hvw : v = w := by rw [← hm'v, hm', hmw]
        rw [hvw]
        rw [hvw, hm'] at hm'lt
        exact ⟨ms, (ha'ne ms hms_ne).trans hmsw, lt_trans hlt hm'lt⟩
      · exact ⟨m', (ha'ne m' hm').trans hm'v, hm'lt⟩
  -- and raises the total rank, against maximality
  have hsum : ∑ x, (p.manRank x (a x)).val
      < ∑ x, (p.manRank x (Function.update a m w' x)).val := by
    apply Finset.sum_lt_sum
    · intro x _
      by_cases hx : x = m
      · rw [hx, ha'm, hmw]
        omega
      · exact le_of_eq (by rw [ha'ne x hx])
    · refine ⟨m, Finset.mem_univ m, ?_⟩
      rw [ha'm, hmw]
      omega
  exact absurd (hmax _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hJ'⟩)) (not_le.mpr hsum)

theorem OMA.solution : OMA.R_LennonPittel_lennon_pittel_conjecture_R1.H1 := by
  intro n p
  obtain ⟨a, hJ, hinj⟩ := gs_exists_justified_injective p
  obtain ⟨μ, hμ⟩ := gs_stable_of_injective p a hJ hinj
  unfold StableMarriage.numStableMatchings
  classical
  exact Fintype.card_pos_iff.mpr ⟨⟨μ, hμ⟩⟩
