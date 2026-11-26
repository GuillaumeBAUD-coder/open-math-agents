import FormalConjectures.GreensOpenProblems.«27»

-- Problem: Green's Open Problem 27 — previous lower
-- Upstream: formal-conjectures FormalConjectures/GreensOpenProblems/27.lean:135 (declaration Green27.green_27.variants.previous_lower)
-- Credit: @jlgmaarav (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

open Filter

/-! Straus's argument: if `A ⊆ ℤ/p` has `5 ^ |A| < p`, a pigeonhole (simultaneous Dirichlet
approximation) gives a dilation `μ A` lying in `(-p/5, p/5)`, where sums do not wrap around; then
`a* + a*` for the element `a*` with the largest representative has a unique representation. -/

/-- If two residues lie in the same fifth of `[0, p)`, they differ by less than `p / 5`. -/
lemma same_fifth {p u v : ℕ} (hp : 0 < p) (hu : u < p) (hv : v < p)
    (h : 5 * u / p = 5 * v / p) : 5 * |(u : ℤ) - v| < p := by
  have h1 := Nat.div_mul_le_self (5 * u) p
  have h2 := Nat.lt_div_mul_add (a := 5 * u) hp
  have h3 := Nat.div_mul_le_self (5 * v) p
  have h4 := Nat.lt_div_mul_add (a := 5 * v) hp
  rw [h] at h1 h2
  obtain ⟨X, hX⟩ : ∃ X, 5 * v / p * p = X := ⟨_, rfl⟩
  rw [hX] at h1 h2 h3 h4
  have h5 : |(5 : ℤ) * ((u : ℤ) - v)| < p := by rw [abs_lt]; constructor <;> omega
  rwa [abs_mul, abs_of_pos (by norm_num : (0 : ℤ) < 5)] at h5

lemma key (p : ℕ) [hp : Fact p.Prime] (A : Finset (ZMod p)) (hA : A.Nonempty)
    (hu : HasNoUniqueRepresentation A) : p ≤ 5 ^ A.card := by
  classical
  by_contra hlt
  push Not at hlt
  have hp0 : 0 < p := hp.out.pos
  -- Pigeonhole on the boxes `⌊5 val(l a) / p⌋ ∈ Fin 5`.
  let box : ZMod p → Fin 5 := fun x =>
    ⟨5 * x.val / p, (Nat.div_lt_iff_lt_mul hp0).mpr (by have := ZMod.val_lt x; omega)⟩
  let F : Fin (5 ^ A.card + 1) → (A → Fin 5) := fun l a => box (((l : ℕ) : ZMod p) * a)
  have hcard : Fintype.card (A → Fin 5) < Fintype.card (Fin (5 ^ A.card + 1)) := by
    simp [Fintype.card_fun, Fintype.card_coe]
  obtain ⟨l1, l2, hne, heq⟩ := Fintype.exists_ne_map_eq_of_card_lt F hcard
  -- `μ = l₂ - l₁` is a nonzero residue.
  set μ : ZMod p := (((((l2 : ℕ) : ℤ) - ((l1 : ℕ) : ℤ) : ℤ)) : ZMod p) with hμ
  have hμ0 : μ ≠ 0 := by
    intro h0
    rw [hμ, ZMod.intCast_zmod_eq_zero_iff_dvd] at h0
    have hl : (l1 : ℕ) ≠ (l2 : ℕ) := fun h => hne (Fin.ext h)
    have hb1 := l1.isLt
    have hb2 := l2.isLt
    have := Int.eq_zero_of_abs_lt_dvd h0 (by rw [abs_lt]; constructor <;> omega)
    omega
  -- The integer representatives `g a = val(l₂ a) - val(l₁ a)` of `μ a` are small.
  let g : ZMod p → ℤ := fun a =>
    ((((l2 : ℕ) : ZMod p) * a).val : ℤ) - ((((l1 : ℕ) : ZMod p) * a).val : ℤ)
  have hg_cast : ∀ a, (g a : ZMod p) = μ * a := by
    intro a
    simp only [g, hμ]
    push_cast
    simp only [ZMod.natCast_val, ZMod.cast_id', id]
    ring
  have hg_bound : ∀ a ∈ A, 5 * |g a| < p := by
    intro a ha
    have h := congrFun heq ⟨a, ha⟩
    simp only [F, box, Fin.mk.injEq] at h
    exact same_fifth hp0 (ZMod.val_lt _) (ZMod.val_lt _) h.symm
  have hg_inj : ∀ a ∈ A, ∀ b ∈ A, g a = g b → a = b := by
    intro a _ b _ hab
    have := congrArg (fun z : ℤ => (z : ZMod p)) hab
    simp only [hg_cast] at this
    exact mul_left_cancel₀ hμ0 this
  -- The element with the largest representative.
  obtain ⟨a0, ha0, hmax⟩ := A.exists_max_image g hA
  have hmem : a0 + a0 ∈ allUniqueSums (A : Set (ZMod p)) := by
    refine ⟨(a0, a0), ha0, ha0, rfl, fun a1 h1 a2 h2 hs => Or.inl ?_⟩
    have hz : ((g a1 + g a2 - 2 * g a0 : ℤ) : ZMod p) = 0 := by
      push_cast
      rw [hg_cast, hg_cast, hg_cast, ← mul_add, hs]
      ring
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at hz
    have e1 := hg_bound a1 h1
    have e2 := hg_bound a2 h2
    have e0 := hg_bound a0 ha0
    have hzero := Int.eq_zero_of_abs_lt_dvd hz (by
      rw [abs_lt]
      constructor <;>
        linarith [le_abs_self (g a1), neg_abs_le (g a1), le_abs_self (g a2), neg_abs_le (g a2),
          le_abs_self (g a0), neg_abs_le (g a0)])
    have m1 := hmax a1 h1
    have m2 := hmax a2 h2
    exact ⟨hg_inj a1 h1 a0 ha0 (by omega), hg_inj a2 h2 a0 ha0 (by omega)⟩
  rw [HasNoUniqueRepresentation] at hu
  rw [hu] at hmem
  exact hmem

/-- For `p ≥ 3` the whole group has no unique representations. -/
lemma univ_nur (p : ℕ) [Fact p.Prime] (hp3 : 3 ≤ p) :
    HasNoUniqueRepresentation (Finset.univ : Finset (ZMod p)) := by
  rw [HasNoUniqueRepresentation, Set.eq_empty_iff_forall_notMem]
  rintro n ⟨q, -, -, hq, huniq⟩
  -- Some element avoids `q.1` and `q.2`, since `p ≥ 3`.
  obtain ⟨a, -, ha⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (s := ({q.1, q.2} : Finset (ZMod p))) (t := Finset.univ)
    (by rw [Finset.card_univ, ZMod.card]; exact (Finset.card_le_two).trans_lt (by omega))
  have ha1 : a ≠ q.1 := fun h => ha (by simp [h])
  have ha2 : a ≠ q.2 := fun h => ha (by simp [h])
  rcases huniq a (Finset.mem_coe.mpr (Finset.mem_univ _)) (n - a)
      (Finset.mem_coe.mpr (Finset.mem_univ _)) (by ring) with h | h
  · exact ha1 h.1
  · exact ha2 h.1

theorem OMA.solution : type_of% @Green27.green_27.variants.previous_lower := by
  apply Asymptotics.IsBigO.of_bound (Real.log 5)
  have hev : ∀ᶠ p in Green27.primesAtTop, 3 ≤ p ∧ p.Prime :=
    ((eventually_ge_atTop 3).filter_mono inf_le_left).and
      ((eventually_principal.mpr fun p hp => hp).filter_mono inf_le_right)
  filter_upwards [hev] with p ⟨hp3, hp⟩
  have := Fact.mk hp
  have hlog5 : 0 < Real.log 5 := Real.log_pos (by norm_num)
  -- Every admissible set has `|A| ≥ log p / log 5`, so the infimum does too.
  have hge : Real.log p / Real.log 5 ≤ Green27.m p := by
    unfold Green27.m
    apply le_csInf
    · exact ⟨p, Finset.univ, by simp [ZMod.card]; omega, univ_nur p hp3, by simp [ZMod.card]⟩
    · rintro x ⟨A, h2, hA, rfl⟩
      have hle := key p A (Finset.card_pos.mp (by omega)) hA
      have := Real.log_le_log (by exact_mod_cast hp.pos)
        (show (p : ℝ) ≤ 5 ^ A.card by exact_mod_cast hle)
      rw [Real.log_pow] at this
      rw [div_le_iff₀ hlog5]
      linarith
  have hlogp : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast hp.one_lt.le)
  have hm0 : 0 ≤ Green27.m p := le_trans (div_nonneg hlogp hlog5.le) hge
  rw [Real.norm_of_nonneg hlogp, Real.norm_of_nonneg hm0]
  rw [div_le_iff₀ hlog5] at hge
  linarith
