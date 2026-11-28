import OMAStatements.S_oeis_a188572

/-!
# Proof of Kimberling's conjecture for OEIS A188572

`a(n)` is the coefficient of `√3` in `(1 + √2 + √3)^n`. The statement: every prime `p` divides
`a(n)` for infinitely many `n`.

Multiplication by `α = 1 + √2 + √3` acts on the basis `(1, √2, √3, √6)` by the step map of the
statement. Since `α · (-4 - 2√2 + 2√6) = -8`, the step map has an explicit inverse up to the
factor `-8`. For an odd prime `p` it is therefore an injective self-map of the finite set
`(ZMod p)^4`, hence a permutation, hence of finite order `T`; so the orbit of `(1, 0, 0, 0)`
returns to its start at every multiple of `T`, and `a(kT) ≡ a(0) = 0 (mod p)` for all `k`.
For `p = 2` all four coordinates of `α^n` are even as soon as `n ≥ 2`.
-/

namespace OMA.S_oeis_a188572

/-- The step map on quadruples over `ZMod p`. -/
def stepZ (p : ℕ) (w : ZMod p × ZMod p × ZMod p × ZMod p) :
    ZMod p × ZMod p × ZMod p × ZMod p :=
  (w.1 + 2 * w.2.1 + 3 * w.2.2.1, w.1 + w.2.1 + 3 * w.2.2.2,
    w.1 + w.2.2.1 + 2 * w.2.2.2, w.2.1 + w.2.2.1 + w.2.2.2)

/-- Multiplication by `-4 - 2√2 + 2√6`, which is `-8 / (1 + √2 + √3)`. -/
def backZ (p : ℕ) (w : ZMod p × ZMod p × ZMod p × ZMod p) :
    ZMod p × ZMod p × ZMod p × ZMod p :=
  (-4 * w.1 - 4 * w.2.1 + 12 * w.2.2.2, -2 * w.1 - 4 * w.2.1 + 6 * w.2.2.1,
    4 * w.2.1 - 4 * w.2.2.1 - 4 * w.2.2.2, 2 * w.1 - 2 * w.2.2.1 - 4 * w.2.2.2)

/-- Reduction of an integer quadruple modulo `p`. -/
def red (p : ℕ) (v : ℤ × ℤ × ℤ × ℤ) : ZMod p × ZMod p × ZMod p × ZMod p :=
  ((v.1 : ZMod p), (v.2.1 : ZMod p), (v.2.2.1 : ZMod p), (v.2.2.2 : ZMod p))

theorem red_step (p : ℕ) (v : ℤ × ℤ × ℤ × ℤ) : red p (quadStep v) = stepZ p (red p v) := by
  obtain ⟨c1, c2, c3, c6⟩ := v
  simp [red, stepZ, quadStep]

theorem back_step (p : ℕ) (w : ZMod p × ZMod p × ZMod p × ZMod p) :
    backZ p (stepZ p w) = ((-8 : ZMod p) * w.1, (-8 : ZMod p) * w.2.1, (-8 : ZMod p) * w.2.2.1,
      (-8 : ZMod p) * w.2.2.2) := by
  obtain ⟨c1, c2, c3, c6⟩ := w
  simp only [backZ, stepZ, Prod.mk.injEq]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> ring

theorem red_iterate (p : ℕ) (n : ℕ) : red p (quadPow n) = (stepZ p)^[n] (red p (quadPow 0)) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', ← ih, ← red_step]
    rfl

theorem eight_ne_zero {p : ℕ} (hp : p.Prime) (hodd : Odd p) : (-8 : ZMod p) ≠ 0 := by
  intro h
  have h8 : ((8 : ℕ) : ZMod p) = 0 := by
    have : (8 : ZMod p) = 0 := by linear_combination -h
    exact_mod_cast this
  rw [ZMod.natCast_eq_zero_iff] at h8
  have h2 : p ∣ 2 := hp.dvd_of_dvd_pow (show p ∣ 2 ^ 3 by simpa using h8)
  have : p = 2 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h2
  subst this
  exact absurd hodd (by decide)

theorem stepZ_injective {p : ℕ} (hp : p.Prime) (hodd : Odd p) : Function.Injective (stepZ p) := by
  have : Fact p.Prime := ⟨hp⟩
  intro w w' h
  have hb := congrArg (backZ p) h
  rw [back_step, back_step] at hb
  have h8 := eight_ne_zero hp hodd
  simp only [Prod.mk.injEq] at hb
  obtain ⟨h1, h2, h3, h4⟩ := hb
  obtain ⟨c1, c2, c3, c6⟩ := w
  obtain ⟨d1, d2, d3, d6⟩ := w'
  simp only [Prod.mk.injEq]
  exact ⟨mul_left_cancel₀ h8 h1, mul_left_cancel₀ h8 h2, mul_left_cancel₀ h8 h3,
    mul_left_cancel₀ h8 h4⟩

theorem odd_case {p : ℕ} (hp : p.Prime) (hodd : Odd p) (N : ℕ) :
    ∃ n : ℕ, N ≤ n ∧ (p : ℤ) ∣ a n := by
  have : Fact p.Prime := ⟨hp⟩
  have hbij : Function.Bijective (stepZ p) :=
    Finite.injective_iff_bijective.mp (stepZ_injective hp hodd)
  let e : Equiv.Perm (ZMod p × ZMod p × ZMod p × ZMod p) := Equiv.ofBijective (stepZ p) hbij
  have hT : 0 < orderOf e := orderOf_pos e
  refine ⟨(N + 1) * orderOf e, ?_, ?_⟩
  · calc N ≤ (N + 1) * 1 := by omega
      _ ≤ (N + 1) * orderOf e := Nat.mul_le_mul_left _ hT
  · have hpow : e ^ ((N + 1) * orderOf e) = 1 := by
      rw [mul_comm, pow_mul, pow_orderOf_eq_one, one_pow]
    have hit : (stepZ p)^[(N + 1) * orderOf e] = id := by
      have h1 : (⇑e)^[(N + 1) * orderOf e] = ⇑(e ^ ((N + 1) * orderOf e)) :=
        Equiv.Perm.iterate_eq_pow e _
      rw [hpow] at h1
      exact h1
    have hred := red_iterate p ((N + 1) * orderOf e)
    rw [hit] at hred
    have h3 : ((a ((N + 1) * orderOf e) : ℤ) : ZMod p) = 0 := by
      have := congrArg (fun w => w.2.2.1) hred
      simpa [red, a, quadPow] using this
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp h3

theorem two_dvd_all (n : ℕ) :
    (2 : ℤ) ∣ (quadPow (n + 2)).1 ∧ (2 : ℤ) ∣ (quadPow (n + 2)).2.1 ∧
      (2 : ℤ) ∣ (quadPow (n + 2)).2.2.1 ∧ (2 : ℤ) ∣ (quadPow (n + 2)).2.2.2 := by
  induction n with
  | zero => decide
  | succ n ih =>
    have h : quadPow (n + 1 + 2) = quadStep (quadPow (n + 2)) := rfl
    rw [h]
    generalize quadPow (n + 2) = v at ih
    obtain ⟨c1, c2, c3, c6⟩ := v
    simp only [quadStep] at ih ⊢
    omega

end OMA.S_oeis_a188572

theorem OMA.solution : type_of% @OMA.S_oeis_a188572.main := by
  intro p hp N
  rcases hp.eq_two_or_odd' with rfl | hodd
  · exact ⟨N + 2, by omega, (OMA.S_oeis_a188572.two_dvd_all N).2.2.1⟩
  · exact OMA.S_oeis_a188572.odd_case hp hodd N
