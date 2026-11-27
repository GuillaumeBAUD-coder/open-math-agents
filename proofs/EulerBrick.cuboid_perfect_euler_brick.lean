import FormalConjectures.Wikipedia.EulerBrick

-- Problem: Open questions regarding the existence of Euler bricks — cuboid perfect euler brick
-- Upstream: formal-conjectures FormalConjectures/Wikipedia/EulerBrick.lean:152 (declaration EulerBrick.cuboid_perfect_euler_brick)
-- Credit: @OrangeHeadz (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

/-!
Sketch (after R. Sharipov, arXiv:1108.5348).  The third cuboid polynomial is
`P_abu(t) = (t²-a²)²(t²+u²)²(t²+b²)² + (t²-b²)²(t²+u²)²(t²+a²)² - (t²-u²)²(t²+a²)²(t²+b²)²`.
A perfect cuboid with edges `x₁, x₂, x₃`, face diagonals `d₁, d₂, d₃` and space diagonal `L` gives
the positive integer solution
`a = d₃ (L+x₂)(L+d₁)`, `b = d₂ (L+x₃)(L+d₁)`, `u = x₁ (L+x₃)(L+x₂)`, `t = (L+x₃)(L+x₂)(L+d₁)`
of `P_abu(t) = 0` with `a, b, u < t`.  Dividing out common prime factors of `a, b, u` (which must
divide `t`) we may assume `gcd(a, b, u) = 1`.  Then either the third conjecture applies, or we are
in one of the special cases `a = u`, `b = u`, `a = b`, `b u = a²`, `a u = b²`, where the polynomial
factors and the first or second conjecture applies.  An irreducible polynomial of degree at
least two has no integer root.
-/

namespace OMACuboid

open Polynomial

/-- The third cuboid polynomial, evaluated at an integer `t`. -/
def P (a b u t : ℤ) : ℤ :=
  (t ^ 2 - a ^ 2) ^ 2 * (t ^ 2 + u ^ 2) ^ 2 * (t ^ 2 + b ^ 2) ^ 2
    + (t ^ 2 - b ^ 2) ^ 2 * (t ^ 2 + u ^ 2) ^ 2 * (t ^ 2 + a ^ 2) ^ 2
    - (t ^ 2 - u ^ 2) ^ 2 * (t ^ 2 + a ^ 2) ^ 2 * (t ^ 2 + b ^ 2) ^ 2

/-- An admissible root of the cuboid equation. -/
def Sol (a b u t : ℤ) : Prop :=
  0 < a ∧ 0 < b ∧ 0 < u ∧ a < t ∧ b < t ∧ u < t ∧ P a b u t = 0

/- ### Irreducible polynomials of degree at least two have no integer roots -/

lemma not_irreducible_of_root {p : ℤ[X]} (hd : 2 ≤ p.natDegree) {t : ℤ} (ht : p.eval t = 0) :
    ¬ Irreducible p := by
  intro hirr
  obtain ⟨q, hq⟩ := Polynomial.dvd_iff_isRoot.mpr ht
  rcases hirr.isUnit_or_isUnit hq with h | h
  · exact Polynomial.not_isUnit_X_sub_C t h
  · have hq0 : q.natDegree = 0 := Polynomial.natDegree_eq_zero_of_isUnit h
    have hqne : q ≠ 0 := by
      rintro rfl
      rw [mul_zero] at hq
      exact hirr.ne_zero hq
    have h1 : p.natDegree = 1 := by
      rw [hq, Polynomial.natDegree_mul (Polynomial.X_sub_C_ne_zero t) hqne,
        Polynomial.natDegree_X_sub_C, hq0]
    omega

lemma natDegree_shape8 (c6 c4 c2 c0 : ℤ) :
    2 ≤ (X ^ 8 + C c6 * X ^ 6 + C c4 * X ^ 4 - C c2 * X ^ 2 + C c0 : ℤ[X]).natDegree := by
  have h : (X ^ 8 + C c6 * X ^ 6 + C c4 * X ^ 4 - C c2 * X ^ 2 + C c0 : ℤ[X]).natDegree = 8 := by
    compute_degree!
  omega

lemma natDegree_shape10 (c8 c6 c4 c2 c0 : ℤ) :
    2 ≤ (X ^ 10 + C c8 * X ^ 8 + C c6 * X ^ 6 - C c4 * X ^ 4 - C c2 * X ^ 2 - C c0 :
      ℤ[X]).natDegree := by
  have h : (X ^ 10 + C c8 * X ^ 8 + C c6 * X ^ 6 - C c4 * X ^ 4 - C c2 * X ^ 2 - C c0 :
      ℤ[X]).natDegree = 10 := by
    compute_degree!
  omega

lemma natDegree_shape12 (c10 c8 c6 c4 c2 c0 : ℤ) :
    2 ≤ (X ^ 12 + C c10 * X ^ 10 + C c8 * X ^ 8 + C c6 * X ^ 6 + C c4 * X ^ 4 + C c2 * X ^ 2
      + C c0 : ℤ[X]).natDegree := by
  have h : (X ^ 12 + C c10 * X ^ 10 + C c8 * X ^ 8 + C c6 * X ^ 6 + C c4 * X ^ 4 + C c2 * X ^ 2
      + C c0 : ℤ[X]).natDegree = 12 := by
    compute_degree!
  omega

lemma one_no_root {a b : ℤ} (h : EulerBrick.CuboidOneFor a b) (t : ℤ) :
    t ^ 8 + 6 * (a ^ 2 - b ^ 2) * t ^ 6 + (b ^ 4 - 4 * a ^ 2 * b ^ 2 + a ^ 4) * t ^ 4
      - 6 * a ^ 2 * b ^ 2 * (a ^ 2 - b ^ 2) * t ^ 2 + a ^ 4 * b ^ 4 ≠ 0 := by
  intro ht
  unfold EulerBrick.CuboidOneFor at h
  refine not_irreducible_of_root (natDegree_shape8 _ _ _ _) (t := t) ?_ h
  simp only [eval_add, eval_sub, eval_mul, eval_pow, eval_C, eval_X]
  linear_combination ht

lemma two_no_root {a b : ℤ} (h : EulerBrick.CuboidTwoFor a b) (t : ℤ) :
    t ^ 10 + (2 * b ^ 2 + a ^ 2) * (3 * b ^ 2 - 2 * a ^ 2) * t ^ 8
      + (b ^ 8 + 10 * a ^ 2 * b ^ 6 + 4 * a ^ 4 * b ^ 4 - 14 * a ^ 6 * b ^ 2 + a ^ 8) * t ^ 6
      - a ^ 2 * b ^ 2 * (b ^ 8 - 14 * a ^ 2 * b ^ 6 + 4 * a ^ 4 * b ^ 4 + 10 * a ^ 6 * b ^ 2 + a ^ 8)
        * t ^ 4
      - a ^ 6 * b ^ 6 * (b ^ 2 + 2 * a ^ 2) * (-2 * b ^ 2 + 3 * a ^ 2) * t ^ 2
      - b ^ 10 * a ^ 10 ≠ 0 := by
  intro ht
  unfold EulerBrick.CuboidTwoFor at h
  refine not_irreducible_of_root (natDegree_shape10 _ _ _ _ _) (t := t) ?_ h
  simp only [eval_add, eval_sub, eval_mul, eval_pow, eval_C, eval_X]
  linear_combination ht

lemma three_no_root {a b c : ℤ} (h : EulerBrick.CuboidThreeFor a b c) (t : ℤ) :
    P a b c t ≠ 0 := by
  intro ht
  unfold P at ht
  unfold EulerBrick.CuboidThreeFor at h
  refine not_irreducible_of_root (natDegree_shape12 _ _ _ _ _ _) (t := t) ?_ h
  simp only [eval_add, eval_mul, eval_pow, eval_C, eval_X]
  linear_combination ht

/- ### Coprimality bookkeeping -/

lemma gcd3_eq_one {a b u : ℤ}
    (hcop : ∀ r : ℕ, r.Prime → ¬ ((r : ℤ) ∣ a ∧ (r : ℤ) ∣ b ∧ (r : ℤ) ∣ u)) :
    gcd a (gcd b u) = 1 := by
  rw [← Int.coe_gcd b u, ← Int.coe_gcd]
  norm_cast
  by_contra hne
  obtain ⟨r, hr, hrd⟩ := Nat.exists_prime_and_dvd hne
  have h0 : (r : ℤ) ∣ ((Int.gcd a ((Int.gcd b u : ℕ) : ℤ) : ℕ) : ℤ) := Int.natCast_dvd_natCast.2 hrd
  have h1 : (r : ℤ) ∣ a := h0.trans (Int.gcd_dvd_left _ _)
  have h2 : (r : ℤ) ∣ ((Int.gcd b u : ℕ) : ℤ) := h0.trans (Int.gcd_dvd_right _ _)
  exact hcop r hr ⟨h1, h2.trans (Int.gcd_dvd_left _ _), h2.trans (Int.gcd_dvd_right _ _)⟩

lemma gcd2_eq_one {a u : ℤ}
    (hcop : ∀ r : ℕ, r.Prime → ¬ ((r : ℤ) ∣ a ∧ (r : ℤ) ∣ u)) :
    gcd u a = 1 := by
  rw [← Int.coe_gcd]
  norm_cast
  by_contra hne
  obtain ⟨r, hr, hrd⟩ := Nat.exists_prime_and_dvd hne
  have h0 : (r : ℤ) ∣ ((Int.gcd u a : ℕ) : ℤ) := Int.natCast_dvd_natCast.2 hrd
  exact hcop r hr ⟨h0.trans (Int.gcd_dvd_right _ _), h0.trans (Int.gcd_dvd_left _ _)⟩

/-- If `b u = a²` and no prime divides all of `a, b, u`, then `b = p²`, `u = q²`, `a = p q`. -/
lemma sq_decomp {a b u : ℤ} (ha : 0 < a) (hb : 0 < b) (hu : 0 < u) (h : b * u = a ^ 2)
    (hcop : ∀ r : ℕ, r.Prime → ¬ ((r : ℤ) ∣ a ∧ (r : ℤ) ∣ b ∧ (r : ℤ) ∣ u)) :
    ∃ p q : ℕ, p.Coprime q ∧ 0 < p ∧ 0 < q ∧ b = (p : ℤ) ^ 2 ∧ u = (q : ℤ) ^ 2 ∧
      a = (p : ℤ) * q := by
  lift a to ℕ using ha.le
  lift b to ℕ using hb.le
  lift u to ℕ using hu.le
  have h' : b * u = a ^ 2 := by exact_mod_cast h
  have ha' : 0 < a := by exact_mod_cast ha
  have hb' : 0 < b := by exact_mod_cast hb
  have hu' : 0 < u := by exact_mod_cast hu
  have hbu : Nat.Coprime b u := by
    apply Nat.Coprime.symm
    apply Nat.coprime_of_dvd
    intro k hk hku hkb
    have hka2 : k ∣ a ^ 2 := h' ▸ Dvd.dvd.mul_right hkb u
    have hka : k ∣ a := hk.dvd_of_dvd_pow hka2
    exact hcop k hk ⟨by exact_mod_cast hka, by exact_mod_cast hkb, by exact_mod_cast hku⟩
  obtain ⟨p, hp⟩ := exists_eq_pow_of_mul_eq_pow (Nat.isUnit_iff.2 hbu) h'
  obtain ⟨q, hq⟩ := exists_eq_pow_of_mul_eq_pow (Nat.isUnit_iff.2 hbu.symm)
    (show u * b = a ^ 2 by rw [mul_comm]; exact h')
  subst hp hq
  have hp0 : 0 < p := by
    rcases Nat.eq_zero_or_pos p with rfl | hp0
    · simp at hb'
    · exact hp0
  have hq0 : 0 < q := by
    rcases Nat.eq_zero_or_pos q with rfl | hq0
    · simp at hu'
    · exact hq0
  have hapq : a = p * q := by
    have : a ^ 2 = (p * q) ^ 2 := by rw [← h']; ring
    exact Nat.pow_left_injective (by norm_num : 2 ≠ 0) this
  refine ⟨p, q, ?_, hp0, hq0, by push_cast; ring, by push_cast; ring, by exact_mod_cast hapq⟩
  exact Nat.Coprime.coprime_dvd_left (dvd_pow_self p (by norm_num))
    (Nat.Coprime.coprime_dvd_right (dvd_pow_self q (by norm_num)) hbu)

/- ### The case analysis -/

lemma no_coprime_sol (h₁ : EulerBrick.CuboidOne) (h₂ : EulerBrick.CuboidTwo)
    (h₃ : EulerBrick.CuboidThree) {a b u t : ℤ} (hs : Sol a b u t)
    (hcop : ∀ r : ℕ, r.Prime → ¬ ((r : ℤ) ∣ a ∧ (r : ℤ) ∣ b ∧ (r : ℤ) ∣ u)) : False := by
  obtain ⟨ha, hb, hu, hat, hbt, hut, hP⟩ := hs
  have ht : 0 < t := lt_trans ha hat
  by_cases hau : a = u
  · subst hau
    have h0 : (t ^ 2 - b ^ 2) ^ 2 * (t ^ 2 + a ^ 2) ^ 4 = 0 := by
      rw [← hP]; unfold P; ring
    have h2 : t ^ 2 - b ^ 2 ≠ 0 := by nlinarith
    have h3 : t ^ 2 + a ^ 2 ≠ 0 := by positivity
    exact mul_ne_zero (pow_ne_zero 2 h2) (pow_ne_zero 4 h3) h0
  by_cases hbu : b = u
  · subst hbu
    have h0 : (t ^ 2 - a ^ 2) ^ 2 * (t ^ 2 + b ^ 2) ^ 4 = 0 := by
      rw [← hP]; unfold P; ring
    have h2 : t ^ 2 - a ^ 2 ≠ 0 := by nlinarith
    have h3 : t ^ 2 + b ^ 2 ≠ 0 := by positivity
    exact mul_ne_zero (pow_ne_zero 2 h2) (pow_ne_zero 4 h3) h0
  by_cases hab : a = b
  · subst hab
    have hg : gcd u a = 1 := gcd2_eq_one fun r hr hd => hcop r hr ⟨hd.1, hd.1, hd.2⟩
    have hirr := h₁ hg hu ha (Ne.symm hau)
    have h0 : (t ^ 2 + a ^ 2) ^ 2 *
        (t ^ 8 + 6 * (u ^ 2 - a ^ 2) * t ^ 6 + (a ^ 4 - 4 * u ^ 2 * a ^ 2 + u ^ 4) * t ^ 4
          - 6 * u ^ 2 * a ^ 2 * (u ^ 2 - a ^ 2) * t ^ 2 + u ^ 4 * a ^ 4) = 0 := by
      rw [← hP]; unfold P; ring
    have h3 : (t ^ 2 + a ^ 2) ^ 2 ≠ 0 := by positivity
    exact one_no_root hirr t ((mul_eq_zero.1 h0).resolve_left h3)
  by_cases hsq1 : b * u = a ^ 2
  · obtain ⟨p, q, hpq, hp, hq, rfl, rfl, rfl⟩ := sq_decomp ha hb hu hsq1 hcop
    have hne : p ≠ q := by
      rintro rfl
      exact hbu rfl
    have hirr := h₂ hpq hp hq hne
    have h0 : (t - (p : ℤ) * q) * (t + (p : ℤ) * q) *
        (t ^ 10 + (2 * (q : ℤ) ^ 2 + (p : ℤ) ^ 2) * (3 * (q : ℤ) ^ 2 - 2 * (p : ℤ) ^ 2) * t ^ 8
          + ((q : ℤ) ^ 8 + 10 * (p : ℤ) ^ 2 * (q : ℤ) ^ 6 + 4 * (p : ℤ) ^ 4 * (q : ℤ) ^ 4
              - 14 * (p : ℤ) ^ 6 * (q : ℤ) ^ 2 + (p : ℤ) ^ 8) * t ^ 6
          - (p : ℤ) ^ 2 * (q : ℤ) ^ 2 * ((q : ℤ) ^ 8 - 14 * (p : ℤ) ^ 2 * (q : ℤ) ^ 6
              + 4 * (p : ℤ) ^ 4 * (q : ℤ) ^ 4 + 10 * (p : ℤ) ^ 6 * (q : ℤ) ^ 2 + (p : ℤ) ^ 8)
            * t ^ 4
          - (p : ℤ) ^ 6 * (q : ℤ) ^ 6 * ((q : ℤ) ^ 2 + 2 * (p : ℤ) ^ 2)
            * (-2 * (q : ℤ) ^ 2 + 3 * (p : ℤ) ^ 2) * t ^ 2
          - (q : ℤ) ^ 10 * (p : ℤ) ^ 10) = 0 := by
      rw [← hP]; unfold P; ring
    have h2 : t - (p : ℤ) * q ≠ 0 := by linarith
    have h3 : t + (p : ℤ) * q ≠ 0 := by linarith
    exact two_no_root hirr t ((mul_eq_zero.1 h0).resolve_left (mul_ne_zero h2 h3))
  by_cases hsq2 : a * u = b ^ 2
  · obtain ⟨p, q, hpq, hp, hq, rfl, rfl, rfl⟩ := sq_decomp hb ha hu hsq2
      fun r hr hd => hcop r hr ⟨hd.2.1, hd.1, hd.2.2⟩
    have hne : p ≠ q := by
      rintro rfl
      exact hau rfl
    have hirr := h₂ hpq hp hq hne
    have h0 : (t - (p : ℤ) * q) * (t + (p : ℤ) * q) *
        (t ^ 10 + (2 * (q : ℤ) ^ 2 + (p : ℤ) ^ 2) * (3 * (q : ℤ) ^ 2 - 2 * (p : ℤ) ^ 2) * t ^ 8
          + ((q : ℤ) ^ 8 + 10 * (p : ℤ) ^ 2 * (q : ℤ) ^ 6 + 4 * (p : ℤ) ^ 4 * (q : ℤ) ^ 4
              - 14 * (p : ℤ) ^ 6 * (q : ℤ) ^ 2 + (p : ℤ) ^ 8) * t ^ 6
          - (p : ℤ) ^ 2 * (q : ℤ) ^ 2 * ((q : ℤ) ^ 8 - 14 * (p : ℤ) ^ 2 * (q : ℤ) ^ 6
              + 4 * (p : ℤ) ^ 4 * (q : ℤ) ^ 4 + 10 * (p : ℤ) ^ 6 * (q : ℤ) ^ 2 + (p : ℤ) ^ 8)
            * t ^ 4
          - (p : ℤ) ^ 6 * (q : ℤ) ^ 6 * ((q : ℤ) ^ 2 + 2 * (p : ℤ) ^ 2)
            * (-2 * (q : ℤ) ^ 2 + 3 * (p : ℤ) ^ 2) * t ^ 2
          - (q : ℤ) ^ 10 * (p : ℤ) ^ 10) = 0 := by
      rw [← hP]; unfold P; ring
    have h2 : t - (p : ℤ) * q ≠ 0 := by linarith
    have h3 : t + (p : ℤ) * q ≠ 0 := by linarith
    exact two_no_root hirr t ((mul_eq_zero.1 h0).resolve_left (mul_ne_zero h2 h3))
  · exact three_no_root
      (h₃ (gcd3_eq_one hcop) ha hb hu hab hbu (Ne.symm hau) hsq1 hsq2) t hP

/- ### Removing common factors -/

lemma P_modEq {r a b u a' b' u' t : ℤ} (ha : a ≡ a' [ZMOD r]) (hb : b ≡ b' [ZMOD r])
    (hu : u ≡ u' [ZMOD r]) : P a b u t ≡ P a' b' u' t [ZMOD r] := by
  have s : ∀ x x' : ℤ, x ≡ x' [ZMOD r] → (t ^ 2 - x ^ 2) ^ 2 ≡ (t ^ 2 - x' ^ 2) ^ 2 [ZMOD r] :=
    fun x x' h => ((Int.ModEq.refl _).sub (h.pow 2)).pow 2
  have p : ∀ x x' : ℤ, x ≡ x' [ZMOD r] → (t ^ 2 + x ^ 2) ^ 2 ≡ (t ^ 2 + x' ^ 2) ^ 2 [ZMOD r] :=
    fun x x' h => ((Int.ModEq.refl _).add (h.pow 2)).pow 2
  unfold P
  exact ((((s a a' ha).mul (p u u' hu)).mul (p b b' hb)).add
    (((s b b' hb).mul (p u u' hu)).mul (p a a' ha))).sub
    (((s u u' hu).mul (p a a' ha)).mul (p b b' hb))

lemma exists_coprime_sol : ∀ (n : ℕ) (a b u t : ℤ), t.toNat = n → Sol a b u t →
    ∃ a' b' u' t' : ℤ, Sol a' b' u' t' ∧
      ∀ r : ℕ, r.Prime → ¬ ((r : ℤ) ∣ a' ∧ (r : ℤ) ∣ b' ∧ (r : ℤ) ∣ u') := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro a b u t htn hs
    by_cases hc : ∀ r : ℕ, r.Prime → ¬ ((r : ℤ) ∣ a ∧ (r : ℤ) ∣ b ∧ (r : ℤ) ∣ u)
    · exact ⟨a, b, u, t, hs, hc⟩
    · simp only [not_forall, not_not] at hc
      obtain ⟨r, hr, ⟨a', rfl⟩, ⟨b', rfl⟩, ⟨u', rfl⟩⟩ := hc
      obtain ⟨ha, hb, hu, hat, hbt, hut, hP⟩ := hs
      have hr2 : (2 : ℤ) ≤ r := by exact_mod_cast hr.two_le
      have hrpos : (0 : ℤ) < r := by linarith
      have hrt : (r : ℤ) ∣ t := by
        have hprime : Prime (r : ℤ) := Nat.prime_iff_prime_int.mp hr
        have h12 : (r : ℤ) ∣ t ^ 12 := by
          have hmod : P ((r : ℤ) * a') ((r : ℤ) * b') ((r : ℤ) * u') t ≡ P 0 0 0 t [ZMOD r] :=
            P_modEq (Int.modEq_zero_iff_dvd.2 (dvd_mul_right _ _))
              (Int.modEq_zero_iff_dvd.2 (dvd_mul_right _ _))
              (Int.modEq_zero_iff_dvd.2 (dvd_mul_right _ _))
          rw [hP] at hmod
          have h0 : P 0 0 0 t = t ^ 12 := by unfold P; ring
          rw [h0] at hmod
          exact Int.modEq_zero_iff_dvd.1 hmod.symm
        exact hprime.dvd_of_dvd_pow h12
      obtain ⟨t', rfl⟩ := hrt
      have hP' : P a' b' u' t' = 0 := by
        have hh : (r : ℤ) ^ 12 * P a' b' u' t' = 0 := by
          rw [← hP]; unfold P; ring
        exact (mul_eq_zero.1 hh).resolve_left (pow_ne_zero 12 hrpos.ne')
      have ha' : 0 < a' := (mul_pos_iff_of_pos_left hrpos).1 ha
      have hb' : 0 < b' := (mul_pos_iff_of_pos_left hrpos).1 hb
      have hu' : 0 < u' := (mul_pos_iff_of_pos_left hrpos).1 hu
      have hat' : a' < t' := lt_of_mul_lt_mul_left hat hrpos.le
      have hbt' : b' < t' := lt_of_mul_lt_mul_left hbt hrpos.le
      have hut' : u' < t' := lt_of_mul_lt_mul_left hut hrpos.le
      have ht' : 0 < t' := lt_trans ha' hat'
      have hlt : t'.toNat < n := by
        rw [← htn]
        have : t' < (r : ℤ) * t' := by nlinarith
        omega
      exact ih t'.toNat hlt a' b' u' t' rfl ⟨ha', hb', hu', hat', hbt', hut', hP'⟩

/- ### From a perfect cuboid to a root -/

lemma cuboid_key (L x2 x3 d1 X Y Z : ℤ) (e1 : x2 ^ 2 + x3 ^ 2 = d1 ^ 2) :
    (X ^ 2 * Z ^ 2 * (2 * x3 * Y)) ^ 2 * (Y ^ 2 * X ^ 2 * (2 * L * Z)) ^ 2
        * (Y ^ 2 * Z ^ 2 * (2 * L * X)) ^ 2
      + (Y ^ 2 * Z ^ 2 * (2 * x2 * X)) ^ 2 * (Y ^ 2 * X ^ 2 * (2 * L * Z)) ^ 2
        * (X ^ 2 * Z ^ 2 * (2 * L * Y)) ^ 2
      - (Y ^ 2 * X ^ 2 * (2 * d1 * Z)) ^ 2 * (X ^ 2 * Z ^ 2 * (2 * L * Y)) ^ 2
        * (Y ^ 2 * Z ^ 2 * (2 * L * X)) ^ 2 = 0 := by
  linear_combination (64 * L ^ 4 * X ^ 10 * Y ^ 10 * Z ^ 10) * e1

lemma sol_of_cuboid {x1 x2 x3 d1 d2 d3 L : ℤ} (h1 : 0 < x1) (h2 : 0 < x2) (h3 : 0 < x3)
    (hd1 : 0 < d1) (hd2 : 0 < d2) (hd3 : 0 < d3) (hL : 0 < L)
    (e3 : x1 ^ 2 + x2 ^ 2 = d3 ^ 2) (e2 : x1 ^ 2 + x3 ^ 2 = d2 ^ 2)
    (e1 : x2 ^ 2 + x3 ^ 2 = d1 ^ 2) (eL : x1 ^ 2 + x2 ^ 2 + x3 ^ 2 = L ^ 2) :
    Sol (d3 * (L + x2) * (L + d1)) (d2 * (L + x3) * (L + d1)) (x1 * (L + x3) * (L + x2))
      ((L + x3) * (L + x2) * (L + d1)) := by
  have hd3L : d3 < L := by nlinarith
  have hd2L : d2 < L := by nlinarith
  have hx1L : x1 < L := by nlinarith
  have p1 : 0 < L + x2 := by linarith
  have p2 : 0 < L + x3 := by linarith
  have p3 : 0 < L + d1 := by linarith
  refine ⟨by positivity, by positivity, by positivity, ?_, ?_, ?_, ?_⟩
  · have hpos : 0 < (L + x3 - d3) * ((L + x2) * (L + d1)) :=
      mul_pos (by linarith) (mul_pos p1 p3)
    nlinarith
  · have hpos : 0 < (L + x2 - d2) * ((L + x3) * (L + d1)) :=
      mul_pos (by linarith) (mul_pos p2 p3)
    nlinarith
  · have hpos : 0 < (L + d1 - x1) * ((L + x3) * (L + x2)) :=
      mul_pos (by linarith) (mul_pos p2 p1)
    nlinarith
  · have k1 : ((L + x3) * (L + x2) * (L + d1)) ^ 2 - (d3 * (L + x2) * (L + d1)) ^ 2 =
        (L + x2) ^ 2 * (L + d1) ^ 2 * (2 * x3 * (L + x3)) := by
      linear_combination (-((L + x2) ^ 2 * (L + d1) ^ 2)) * eL + ((L + x2) ^ 2 * (L + d1) ^ 2) * e3
    have k2 : ((L + x3) * (L + x2) * (L + d1)) ^ 2 + (d3 * (L + x2) * (L + d1)) ^ 2 =
        (L + x2) ^ 2 * (L + d1) ^ 2 * (2 * L * (L + x3)) := by
      linear_combination ((L + x2) ^ 2 * (L + d1) ^ 2) * eL - ((L + x2) ^ 2 * (L + d1) ^ 2) * e3
    have k3 : ((L + x3) * (L + x2) * (L + d1)) ^ 2 - (d2 * (L + x3) * (L + d1)) ^ 2 =
        (L + x3) ^ 2 * (L + d1) ^ 2 * (2 * x2 * (L + x2)) := by
      linear_combination (-((L + x3) ^ 2 * (L + d1) ^ 2)) * eL + ((L + x3) ^ 2 * (L + d1) ^ 2) * e2
    have k4 : ((L + x3) * (L + x2) * (L + d1)) ^ 2 + (d2 * (L + x3) * (L + d1)) ^ 2 =
        (L + x3) ^ 2 * (L + d1) ^ 2 * (2 * L * (L + x2)) := by
      linear_combination ((L + x3) ^ 2 * (L + d1) ^ 2) * eL - ((L + x3) ^ 2 * (L + d1) ^ 2) * e2
    have k5 : ((L + x3) * (L + x2) * (L + d1)) ^ 2 - (x1 * (L + x3) * (L + x2)) ^ 2 =
        (L + x3) ^ 2 * (L + x2) ^ 2 * (2 * d1 * (L + d1)) := by
      linear_combination (-((L + x3) ^ 2 * (L + x2) ^ 2)) * eL + ((L + x3) ^ 2 * (L + x2) ^ 2) * e1
    have k6 : ((L + x3) * (L + x2) * (L + d1)) ^ 2 + (x1 * (L + x3) * (L + x2)) ^ 2 =
        (L + x3) ^ 2 * (L + x2) ^ 2 * (2 * L * (L + d1)) := by
      linear_combination ((L + x3) ^ 2 * (L + x2) ^ 2) * eL - ((L + x3) ^ 2 * (L + x2) ^ 2) * e1
    unfold P
    rw [k1, k2, k3, k4, k5, k6]
    exact cuboid_key L x2 x3 d1 (L + x2) (L + x3) (L + d1) e1

end OMACuboid

theorem OMA.solution : type_of% @EulerBrick.cuboid_perfect_euler_brick := by
  intro h₁ h₂ h₃ hex
  obtain ⟨a, b, c, hc⟩ := hex
  obtain ⟨⟨⟨r3, hr3⟩, ⟨r2, hr2⟩, ⟨r1, hr1⟩⟩, ⟨l, hl⟩⟩ := hc
  have e3 : ((a : ℕ) : ℤ) ^ 2 + ((b : ℕ) : ℤ) ^ 2 = ((r3 : ℕ) : ℤ) ^ 2 := by
    have h := congrArg (fun x : ℕ+ => ((x : ℕ) : ℤ)) hr3
    simp only [PNat.add_coe, PNat.pow_coe, PNat.mul_coe] at h
    push_cast at h
    linarith
  have e2 : ((a : ℕ) : ℤ) ^ 2 + ((c : ℕ) : ℤ) ^ 2 = ((r2 : ℕ) : ℤ) ^ 2 := by
    have h := congrArg (fun x : ℕ+ => ((x : ℕ) : ℤ)) hr2
    simp only [PNat.add_coe, PNat.pow_coe, PNat.mul_coe] at h
    push_cast at h
    linarith
  have e1 : ((b : ℕ) : ℤ) ^ 2 + ((c : ℕ) : ℤ) ^ 2 = ((r1 : ℕ) : ℤ) ^ 2 := by
    have h := congrArg (fun x : ℕ+ => ((x : ℕ) : ℤ)) hr1
    simp only [PNat.add_coe, PNat.pow_coe, PNat.mul_coe] at h
    push_cast at h
    linarith
  have eL : ((a : ℕ) : ℤ) ^ 2 + ((b : ℕ) : ℤ) ^ 2 + ((c : ℕ) : ℤ) ^ 2 = ((l : ℕ) : ℤ) ^ 2 := by
    have h := congrArg (fun x : ℕ+ => ((x : ℕ) : ℤ)) hl
    simp only [PNat.add_coe, PNat.pow_coe, PNat.mul_coe] at h
    push_cast at h
    linarith
  have pa : (0 : ℤ) < ((a : ℕ) : ℤ) := by exact_mod_cast a.pos
  have pb : (0 : ℤ) < ((b : ℕ) : ℤ) := by exact_mod_cast b.pos
  have pc : (0 : ℤ) < ((c : ℕ) : ℤ) := by exact_mod_cast c.pos
  have p1 : (0 : ℤ) < ((r1 : ℕ) : ℤ) := by exact_mod_cast r1.pos
  have p2 : (0 : ℤ) < ((r2 : ℕ) : ℤ) := by exact_mod_cast r2.pos
  have p3 : (0 : ℤ) < ((r3 : ℕ) : ℤ) := by exact_mod_cast r3.pos
  have pl : (0 : ℤ) < ((l : ℕ) : ℤ) := by exact_mod_cast l.pos
  have hs := OMACuboid.sol_of_cuboid pa pb pc p1 p2 p3 pl e3 e2 e1 eL
  obtain ⟨a', b', u', t', hs', hcop⟩ := OMACuboid.exists_coprime_sol _ _ _ _ _ rfl hs
  exact OMACuboid.no_coprime_sol h₁ h₂ h₃ hs' hcop
