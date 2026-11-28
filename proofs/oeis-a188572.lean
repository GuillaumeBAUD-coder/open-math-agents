import OMAStatements.S_oeis_a188572

-- Problem: OEIS A188572, a(n) = coefficient of sqrt(3) in (1 + sqrt(2) + sqrt(3))^n.
-- Conjecture (Clark Kimberling, Oct 23 2024): every prime p divides a(n) for infinitely many n.
-- Proof. Multiplication by 1 + sqrt(2) + sqrt(3) has determinant -8 in the basis (1, sqrt 2, sqrt 3, sqrt 6).
-- For odd p it is therefore a permutation of (ZMod p)^4, so its orbit through (1,0,0,0) is purely
-- periodic and comes back to (1,0,0,0), whose sqrt(3)-coordinate is 0 = a(0). For p = 2 every
-- coordinate of (1 + sqrt 2 + sqrt 3)^n is even as soon as n >= 2.

open OMA.S_oeis_a188572

/-- The step map `quadStep` over `ZMod p`. -/
def OMA.fstep (p : ℕ) (v : ZMod p × ZMod p × ZMod p × ZMod p) :
    ZMod p × ZMod p × ZMod p × ZMod p :=
  (v.1 + 2 * v.2.1 + 3 * v.2.2.1, v.1 + v.2.1 + 3 * v.2.2.2,
    v.1 + v.2.2.1 + 2 * v.2.2.2, v.2.1 + v.2.2.1 + v.2.2.2)

/-- Reduction of an integer quadruple modulo `p`. -/
def OMA.red (p : ℕ) (v : ℤ × ℤ × ℤ × ℤ) : ZMod p × ZMod p × ZMod p × ZMod p :=
  ((v.1 : ZMod p), (v.2.1 : ZMod p), (v.2.2.1 : ZMod p), (v.2.2.2 : ZMod p))

lemma OMA.red_step (p : ℕ) (v : ℤ × ℤ × ℤ × ℤ) :
    OMA.red p (quadStep v) = OMA.fstep p (OMA.red p v) := by
  obtain ⟨c1, c2, c3, c6⟩ := v
  simp [OMA.red, OMA.fstep, quadStep]

lemma OMA.red_pow (p : ℕ) (n : ℕ) :
    OMA.red p (quadPow n) = (OMA.fstep p)^[n] (1, 0, 0, 0) := by
  induction n with
  | zero => simp [OMA.red, quadPow]
  | succ n ih =>
    rw [Function.iterate_succ_apply', ← ih, ← OMA.red_step]
    rfl

lemma OMA.fstep_injective (p : ℕ) [Fact p.Prime] (h2 : (2 : ZMod p) ≠ 0) :
    Function.Injective (OMA.fstep p) := by
  rintro ⟨v1, v2, v3, v4⟩ ⟨w1, w2, w3, w4⟩ h
  simp only [OMA.fstep, Prod.mk.injEq] at h
  obtain ⟨h1, h2', h3, h4⟩ := h
  have h4ne : (4 : ZMod p) ≠ 0 := by
    have h22 : (4 : ZMod p) = 2 * 2 := by norm_num
    rw [h22]
    exact mul_ne_zero h2 h2
  have e1 : (4 : ZMod p) * (v1 - w1) = 0 := by linear_combination 2 * h1 + 2 * h2' - 6 * h4
  have e2 : (4 : ZMod p) * (v2 - w2) = 0 := by linear_combination h1 + 2 * h2' - 3 * h3
  have e3 : (2 : ZMod p) * (v3 - w3) = 0 := by linear_combination -h2' + h3 + h4
  have e4 : (4 : ZMod p) * (v4 - w4) = 0 := by linear_combination -h1 + h3 + 2 * h4
  have f1 : v1 = w1 := sub_eq_zero.mp ((mul_eq_zero.mp e1).resolve_left h4ne)
  have f2 : v2 = w2 := sub_eq_zero.mp ((mul_eq_zero.mp e2).resolve_left h4ne)
  have f3 : v3 = w3 := sub_eq_zero.mp ((mul_eq_zero.mp e3).resolve_left h2)
  have f4 : v4 = w4 := sub_eq_zero.mp ((mul_eq_zero.mp e4).resolve_left h4ne)
  rw [f1, f2, f3, f4]

/-- From `n = 2` on, all four coordinates are even. -/
lemma OMA.even_pow (n : ℕ) :
    ∃ x y z w : ℤ, quadPow (n + 2) = (2 * x, 2 * y, 2 * z, 2 * w) := by
  induction n with
  | zero => exact ⟨3, 1, 1, 1, by decide⟩
  | succ n ih =>
    obtain ⟨x, y, z, w, h⟩ := ih
    refine ⟨x + 2 * y + 3 * z, x + y + 3 * w, x + z + 2 * w, y + z + w, ?_⟩
    have hs : quadPow (n + 1 + 2) = quadStep (quadPow (n + 2)) := rfl
    rw [hs, h]
    simp only [quadStep, Prod.mk.injEq]
    refine ⟨by ring, by ring, by ring, by ring⟩

theorem OMA.solution : type_of% @OMA.S_oeis_a188572.main := by
  intro p hp N
  rcases hp.eq_two_or_odd' with rfl | hodd
  · obtain ⟨x, y, z, w, h⟩ := OMA.even_pow N
    refine ⟨N + 2, Nat.le_add_right N 2, ?_⟩
    have ha : a (N + 2) = 2 * z := by
      simp only [a, h]
    rw [ha]
    exact ⟨z, by norm_num⟩
  · haveI : Fact p.Prime := ⟨hp⟩
    have h2 : (2 : ZMod p) ≠ 0 := by
      intro h
      have h' : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
      rw [ZMod.natCast_eq_zero_iff] at h'
      have hle : p ≤ 2 := Nat.le_of_dvd (by norm_num) h'
      have hp2 : p = 2 := le_antisymm hle hp.two_le
      rw [hp2] at hodd
      exact absurd hodd (by decide)
    have hbij : Function.Bijective (OMA.fstep p) :=
      Finite.injective_iff_bijective.mp (OMA.fstep_injective p h2)
    have hT : 0 < orderOf (Equiv.ofBijective (OMA.fstep p) hbij) := orderOf_pos _
    refine ⟨N * orderOf (Equiv.ofBijective (OMA.fstep p) hbij), Nat.le_mul_of_pos_right N hT, ?_⟩
    have hpow : (Equiv.ofBijective (OMA.fstep p) hbij) ^ (N * orderOf (Equiv.ofBijective (OMA.fstep p) hbij)) = 1 := by
      rw [mul_comm, pow_mul, pow_orderOf_eq_one, one_pow]
    have hit : (OMA.fstep p)^[N * orderOf (Equiv.ofBijective (OMA.fstep p) hbij)] (1, 0, 0, 0)
        = (1, 0, 0, 0) := by
      have hiter := Equiv.Perm.iterate_eq_pow (Equiv.ofBijective (OMA.fstep p) hbij)
        (N * orderOf (Equiv.ofBijective (OMA.fstep p) hbij))
      rw [hpow] at hiter
      have hco : (⇑(Equiv.ofBijective (OMA.fstep p) hbij)) = OMA.fstep p := rfl
      rw [hco] at hiter
      rw [hiter]
      rfl
    have hred := OMA.red_pow p (N * orderOf (Equiv.ofBijective (OMA.fstep p) hbij))
    rw [hit] at hred
    have h3 : ((a (N * orderOf (Equiv.ofBijective (OMA.fstep p) hbij)) : ℤ) : ZMod p) = 0 := by
      have hc := congrArg (fun v => v.2.2.1) hred
      simpa [OMA.red, a] using hc
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp h3
