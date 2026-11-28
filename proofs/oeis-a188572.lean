import OMAStatements.S_oeis_a188572
import Mathlib

/-!
Write `α = 1 + √2 + √3`. Then `α² = 2 (3 + √2 + √3 + √6)`, so every coordinate of `α^(n+2)`
is even; this settles `p = 2`. For an odd prime `p`, put `β = 2 + √2 - √6`; then `β α = 4`,
so multiplication by `α` is injective, hence bijective, on the finite set `(ℤ/p)^4`. It is
therefore a permutation of finite order `T ≥ 1`, and `α^(T k) ≡ 1 (mod p)` for every `k`, whose
`√3`-coordinate is `0`.
-/

namespace OMA.A188572Proof

open OMA.S_oeis_a188572

theorem two_dvd (n : ℕ) : (2 : ℤ) ∣ a (n + 2) := by
  show (2 : ℤ) ∣ (quadStep (quadStep (quadPow n))).2.2.1
  obtain ⟨c1, c2, c3, c6⟩ := quadPow n
  simp only [quadStep]
  exact ⟨c1 + 2 * c2 + 3 * c3 + 2 * c6, by ring⟩

variable {p : ℕ}

/-- Reduction modulo `p`, coordinatewise. -/
def toZ (v : ℤ × ℤ × ℤ × ℤ) : ZMod p × ZMod p × ZMod p × ZMod p :=
  ((v.1 : ZMod p), (v.2.1 : ZMod p), (v.2.2.1 : ZMod p), (v.2.2.2 : ZMod p))

/-- Multiplication by `1 + √2 + √3` modulo `p`. -/
def stepZ (v : ZMod p × ZMod p × ZMod p × ZMod p) : ZMod p × ZMod p × ZMod p × ZMod p :=
  (v.1 + 2 * v.2.1 + 3 * v.2.2.1, v.1 + v.2.1 + 3 * v.2.2.2,
    v.1 + v.2.2.1 + 2 * v.2.2.2, v.2.1 + v.2.2.1 + v.2.2.2)

/-- Multiplication by `2 + √2 - √6` modulo `p`. -/
def invZ (v : ZMod p × ZMod p × ZMod p × ZMod p) : ZMod p × ZMod p × ZMod p × ZMod p :=
  (2 * v.1 + 2 * v.2.1 - 6 * v.2.2.2, v.1 + 2 * v.2.1 - 3 * v.2.2.1,
    2 * v.2.2.1 - 2 * v.2.1 + 2 * v.2.2.2, -v.1 + v.2.2.1 + 2 * v.2.2.2)

theorem invZ_stepZ (v : ZMod p × ZMod p × ZMod p × ZMod p) :
    invZ (stepZ v) = (4 * v.1, 4 * v.2.1, 4 * v.2.2.1, 4 * v.2.2.2) := by
  obtain ⟨c1, c2, c3, c6⟩ := v
  simp only [invZ, stepZ, Prod.mk.injEq]
  refine ⟨by ring, by ring, by ring, by ring⟩

theorem toZ_step (v : ℤ × ℤ × ℤ × ℤ) : toZ (p := p) (quadStep v) = stepZ (toZ v) := by
  obtain ⟨c1, c2, c3, c6⟩ := v
  simp only [quadStep, toZ, stepZ]
  push_cast
  rfl

theorem toZ_pow (n : ℕ) :
    toZ (p := p) (quadPow n) = (stepZ (p := p))^[n] (toZ (1, 0, 0, 0)) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', ← ih]
    exact toZ_step _

theorem stepZ_injective [Fact p.Prime] (hp2 : p ≠ 2) : Function.Injective (stepZ (p := p)) := by
  have h4 : (4 : ZMod p) ≠ 0 := by
    intro h
    have h' : ((4 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
    have hd : p ∣ 2 ^ 2 := (ZMod.natCast_eq_zero_iff 4 p).1 h'
    have := (Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime) Nat.prime_two).1
      ((Fact.out : p.Prime).dvd_of_dvd_pow hd)
    exact hp2 this
  intro v w hvw
  have h := congrArg invZ hvw
  rw [invZ_stepZ, invZ_stepZ] at h
  simp only [Prod.mk.injEq] at h
  obtain ⟨h1, h2, h3, h6⟩ := h
  obtain ⟨v1, v2, v3, v6⟩ := v
  obtain ⟨w1, w2, w3, w6⟩ := w
  simp only [Prod.mk.injEq]
  exact ⟨mul_left_cancel₀ h4 h1, mul_left_cancel₀ h4 h2, mul_left_cancel₀ h4 h3,
    mul_left_cancel₀ h4 h6⟩

theorem odd_case [Fact p.Prime] (hp2 : p ≠ 2) (N : ℕ) : ∃ n : ℕ, N ≤ n ∧ (p : ℤ) ∣ a n := by
  have hbij : Function.Bijective (stepZ (p := p)) :=
    Finite.injective_iff_bijective.mp (stepZ_injective hp2)
  let σ : Equiv.Perm (ZMod p × ZMod p × ZMod p × ZMod p) := Equiv.ofBijective _ hbij
  have hT : 0 < orderOf σ := orderOf_pos σ
  refine ⟨orderOf σ * N, Nat.le_mul_of_pos_left N hT, ?_⟩
  have hpow : σ ^ (orderOf σ * N) = 1 := by rw [pow_mul, pow_orderOf_eq_one, one_pow]
  have hit : (stepZ (p := p))^[orderOf σ * N] (toZ (1, 0, 0, 0)) = toZ (1, 0, 0, 0) := by
    have := congrArg (fun τ : Equiv.Perm _ => τ (toZ (p := p) (1, 0, 0, 0))) hpow
    simp only [Equiv.Perm.coe_pow, Equiv.Perm.coe_one, id] at this
    exact this
  have h := toZ_pow (p := p) (orderOf σ * N)
  rw [hit] at h
  have h3 := congrArg (fun v => v.2.2.1) h
  simp only [toZ] at h3
  have h0 : ((a (orderOf σ * N) : ℤ) : ZMod p) = 0 := by
    rw [show a (orderOf σ * N) = (quadPow (orderOf σ * N)).2.2.1 from rfl, h3]
    simp
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).1 h0

end OMA.A188572Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a188572.main := by
  intro p hp N
  by_cases h2 : p = 2
  · subst h2
    exact ⟨N + 2, by omega, by exact_mod_cast OMA.A188572Proof.two_dvd N⟩
  · have : Fact p.Prime := ⟨hp⟩
    exact OMA.A188572Proof.odd_case h2 N
