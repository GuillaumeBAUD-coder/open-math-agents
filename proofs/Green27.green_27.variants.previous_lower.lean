import FormalConjectures.GreensOpenProblems.«27»

open Filter


lemma sf {p u v : ℕ} (hp : 0 < p) (h : 5 * u / p = 5 * v / p) :
    -(p:ℤ) < 5 * ((u:ℤ) - v) ∧ 5 * ((u:ℤ) - v) < p := by
  have h1 := Nat.div_mul_le_self (5 * u) p
  have h2 := Nat.lt_div_mul_add (a := 5 * u) hp
  have h3 := Nat.div_mul_le_self (5 * v) p
  have h4 := Nat.lt_div_mul_add (a := 5 * v) hp
  rw [h] at h1 h2
  omega

lemma key (p : ℕ) [hp : Fact p.Prime] (A : Finset (ZMod p)) (hA : A.Nonempty)
    (hu : HasNoUniqueRepresentation A) : p ≤ 5 ^ A.card := by
  classical
  by_contra! hlt
  have hp0 : 0 < p := hp.out.pos
  let F : Fin (5 ^ A.card + 1) → (A → Fin 5) := fun l a =>
    ⟨5 * (((l : ℕ) : ZMod p) * (a : ZMod p)).val / p, Nat.div_lt_of_lt_mul (by have := ZMod.val_lt (((l : ℕ) : ZMod p) * (a : ZMod p)); omega)⟩
  have hcard : Fintype.card (A → Fin 5) < Fintype.card (Fin (5 ^ A.card + 1)) := by
    simp
  obtain ⟨l1, l2, hne, heq⟩ := Fintype.exists_ne_map_eq_of_card_lt F hcard
  set μ : ZMod p := ((l2 : ℕ) : ZMod p) - ((l1 : ℕ) : ZMod p) with hμ
  have hμ0 : μ ≠ 0 := by
    intro h0
    rw [hμ, sub_eq_zero, ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt, Nat.mod_eq_of_lt] at h0
    · exact hne (Fin.ext h0.symm)
    · have := l1.2; omega
    · have := l2.2; omega
  let g : ZMod p → ℤ := fun a =>
    ((((l2 : ℕ) : ZMod p) * a).val : ℤ) - ((((l1 : ℕ) : ZMod p) * a).val : ℤ)
  have hg_cast : ∀ a, (g a : ZMod p) = μ * a := by
    intro a
    simp [g, hμ]
    ring
  have hg_bound : ∀ a ∈ A, -(p:ℤ) < 5 * g a ∧ 5 * g a < p := fun a ha => by
    have h := congrFun heq ⟨a, ha⟩
    simp only [F, Fin.mk.injEq] at h
    exact sf hp0 h.symm
  have hg_inj : ∀ a ∈ A, ∀ b ∈ A, g a = g b → a = b := by
    intro a _ b _ hab
    have := congrArg (fun z : ℤ => (z : ZMod p)) hab
    simp only [hg_cast] at this
    exact mul_left_cancel₀ hμ0 this
  obtain ⟨a0, ha0, hmax⟩ := A.exists_max_image g hA
  exact Set.eq_empty_iff_forall_notMem.1 hu _ ⟨(a0, a0), ha0, ha0, rfl, fun a1 h1 a2 h2 hs => Or.inl <| by
    have e1 := hg_bound a1 h1
    have e2 := hg_bound a2 h2
    have e0 := hg_bound a0 ha0
    have := Int.eq_zero_of_abs_lt_dvd
      ((ZMod.intCast_zmod_eq_zero_iff_dvd (g a1 + g a2 - 2 * g a0) p).1
        (by push_cast; linear_combination hg_cast a1 + hg_cast a2 - 2 * hg_cast a0 + μ * hs))
      (abs_lt.2 ⟨by omega, by omega⟩)
    have m1 := hmax a1 h1
    have m2 := hmax a2 h2
    exact ⟨hg_inj a1 h1 a0 ha0 (by omega), hg_inj a2 h2 a0 ha0 (by omega)⟩⟩

lemma univ_nur (p : ℕ) [Fact p.Prime] (hp3 : 3 ≤ p) :
    HasNoUniqueRepresentation (Finset.univ : Finset (ZMod p)) := by
  rw [HasNoUniqueRepresentation, Set.eq_empty_iff_forall_notMem]
  rintro n ⟨q, -, -, -, huniq⟩
  obtain ⟨a, -, ha⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (s := ({q.1, q.2} : Finset (ZMod p))) (t := Finset.univ)
    (by rw [Finset.card_univ, ZMod.card]; exact Finset.card_le_two.trans_lt (by omega))
  rcases huniq a (by simp) (n - a) (by simp) (by ring) with h | h <;> exact ha (by simp [h.1])

theorem OMA.solution : type_of% @Green27.green_27.variants.previous_lower := by
  apply Asymptotics.IsBigO.of_bound (Real.log 5)
  have hev : ∀ᶠ p in Green27.primesAtTop, 3 ≤ p ∧ p.Prime :=
    ((eventually_ge_atTop 3).filter_mono inf_le_left).and
      ((eventually_principal.mpr fun p hp => hp).filter_mono inf_le_right)
  filter_upwards [hev] with p ⟨hp3, hp⟩
  have := Fact.mk hp
  have hlog5 : 0 < Real.log 5 := Real.log_pos (by norm_num)
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
