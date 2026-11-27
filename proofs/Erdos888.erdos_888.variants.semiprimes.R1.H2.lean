import OMAReductions.R_Erdos888_erdos_888_variants_semiprimes_R1
import Mathlib

-- Step Erdos888.erdos_888.variants.semiprimes.R1.H2: hypothesis H2 of reduction Erdos888.erdos_888.variants.semiprimes.R1
-- Credit: @ivillar
-- H2: four increasing products of two distinct primes with a square product: outer = inner.
-- Proof: p1 divides one of the other three products, say b = p1 * x. Cancelling p1^2, the
-- product q1 * x * c * d is a square, and a short case analysis on where q1 and x go shows
-- that one of ab = cd, ac = bd, ad = bc holds. The ordering a ≤ b ≤ c ≤ d turns each of these
-- into ad = bc.

namespace OMAErdos888H2

/-- A product of two distinct primes. -/
def Semi (c : ℕ) : Prop := ∃ u v : ℕ, u.Prime ∧ v.Prime ∧ u ≠ v ∧ c = u * v

theorem sq_cancel {k m : ℕ} (hk : k ≠ 0) (h : IsSquare (k * k * m)) : IsSquare m := by
  obtain ⟨s, hs⟩ := h
  have hdvd : k ^ 2 ∣ s ^ 2 := ⟨m, by rw [pow_two, pow_two, ← hs]⟩
  obtain ⟨t, rfl⟩ := (Nat.pow_dvd_pow_iff (by norm_num)).mp hdvd
  refine ⟨t, ?_⟩
  have hk2 : 0 < k * k := Nat.mul_pos (Nat.pos_of_ne_zero hk) (Nat.pos_of_ne_zero hk)
  have : k * k * m = k * k * (t * t) := by rw [hs]; ring
  exact Nat.eq_of_mul_eq_mul_left hk2 this

theorem prime_dvd_of_sq {r m : ℕ} (hr : r.Prime) (h : IsSquare (r * m)) : r ∣ m := by
  obtain ⟨s, hs⟩ := h
  have h1 : r ∣ s * s := ⟨m, hs.symm⟩
  have h2 : r ∣ s := ((Nat.Prime.dvd_mul hr).mp h1).elim id id
  obtain ⟨t, rfl⟩ := h2
  refine ⟨t * t, ?_⟩
  have : r * m = r * (r * (t * t)) := by rw [hs]; ring
  exact Nat.eq_of_mul_eq_mul_left hr.pos this

theorem sq_two_primes {x y : ℕ} (hx : x.Prime) (hy : y.Prime) (h : IsSquare (x * y)) :
    x = y :=
  (Nat.prime_dvd_prime_iff_eq hx hy).mp (prime_dvd_of_sq hx h)

theorem semi_dvd {c r : ℕ} (hc : Semi c) (hr : r.Prime) (h : r ∣ c) :
    ∃ y, y.Prime ∧ y ≠ r ∧ c = r * y := by
  obtain ⟨u, v, hu, hv, huv, hcuv⟩ := hc
  rw [hcuv] at h
  rcases (Nat.Prime.dvd_mul hr).mp h with h1 | h1
  · have e := (Nat.prime_dvd_prime_iff_eq hr hu).mp h1
    refine ⟨v, hv, fun e' => huv (by rw [← e, e']), ?_⟩
    rw [hcuv, e]
  · have e := (Nat.prime_dvd_prime_iff_eq hr hv).mp h1
    refine ⟨u, hu, fun e' => huv (by rw [e', e]), ?_⟩
    rw [hcuv, e, mul_comm]

theorem semi_not_sq {c : ℕ} (hc : Semi c) : ¬ IsSquare c := by
  obtain ⟨u, v, hu, hv, huv, rfl⟩ := hc
  intro h
  exact huv (sq_two_primes hu hv h)

theorem semi_pos {c : ℕ} (hc : Semi c) : 0 < c := by
  obtain ⟨u, v, hu, hv, -, rfl⟩ := hc
  exact Nat.mul_pos hu.pos hv.pos

theorem semi_sq_mul {c d : ℕ} (hc : Semi c) (hd : Semi d) (h : IsSquare (c * d)) : c = d := by
  obtain ⟨u, v, hu, hv, huv, rfl⟩ := hc
  have h1 : u ∣ v * d :=
    prime_dvd_of_sq hu (by rw [show u * (v * d) = u * v * d by ring]; exact h)
  have h2 : u ∣ d := by
    rcases (Nat.Prime.dvd_mul hu).mp h1 with h3 | h3
    · exact absurd ((Nat.prime_dvd_prime_iff_eq hu hv).mp h3) huv
    · exact h3
  obtain ⟨w, hw, -, rfl⟩ := semi_dvd hd hu h2
  have h4 : IsSquare (v * w) :=
    sq_cancel hu.ne_zero (by rw [show u * u * (v * w) = u * v * (u * w) by ring]; exact h)
  rw [sq_two_primes hv hw h4]

theorem key {p q x a b c d : ℕ} (hp : p.Prime) (hq : q.Prime) (hx : x.Prime)
    (ha : a = p * q) (hb : b = p * x) (hc : Semi c) (hd : Semi d)
    (h : IsSquare (a * b * c * d)) :
    a * b = c * d ∨ a * c = b * d ∨ a * d = b * c := by
  subst ha
  subst hb
  have hS : IsSquare (q * x * c * d) :=
    sq_cancel hp.ne_zero
      (by rw [show p * p * (q * x * c * d) = p * q * (p * x) * c * d by ring]; exact h)
  by_cases hqx : q = x
  · rw [← hqx] at hS
    have hcd : IsSquare (c * d) :=
      sq_cancel hq.ne_zero (by rw [show q * q * (c * d) = q * q * c * d by ring]; exact hS)
    have hcd' := semi_sq_mul hc hd hcd
    right; left
    rw [hcd', ← hqx]
  · have hdvd : ∀ r s : ℕ, r.Prime → s.Prime → r ≠ s → IsSquare (r * (s * (c * d))) →
        r ∣ c ∨ r ∣ d := by
      intro r s hr hs hrs hsq
      have h1 := prime_dvd_of_sq hr hsq
      rcases (Nat.Prime.dvd_mul hr).mp h1 with h2 | h2
      · exact absurd ((Nat.prime_dvd_prime_iff_eq hr hs).mp h2) hrs
      · exact (Nat.Prime.dvd_mul hr).mp h2
    have hq' := hdvd q x hq hx hqx
      (by rw [show q * (x * (c * d)) = q * x * c * d by ring]; exact hS)
    have hx' := hdvd x q hx hq (Ne.symm hqx)
      (by rw [show x * (q * (c * d)) = q * x * c * d by ring]; exact hS)
    have other : ∀ y : ℕ, y.Prime → x ∣ q * y → x = y := by
      intro y hy hxy
      rcases (Nat.Prime.dvd_mul hx).mp hxy with h2 | h2
      · exact absurd ((Nat.prime_dvd_prime_iff_eq hx hq).mp h2) (Ne.symm hqx)
      · exact (Nat.prime_dvd_prime_iff_eq hx hy).mp h2
    have hqx0 : q * x ≠ 0 := Nat.mul_ne_zero hq.ne_zero hx.ne_zero
    rcases hq' with hqc | hqd
    · obtain ⟨y, hy, -, rfl⟩ := semi_dvd hc hq hqc
      rcases hx' with hxc | hxd
      · have e := other y hy hxc
        rw [← e] at hS
        exact absurd (sq_cancel hqx0 hS) (semi_not_sq hd)
      · obtain ⟨z, hz, -, rfl⟩ := semi_dvd hd hx hxd
        have hyz : IsSquare (y * z) :=
          sq_cancel hqx0
            (by rw [show q * x * (q * x) * (y * z) = q * x * (q * y) * (x * z) by ring]; exact hS)
        have e := sq_two_primes hy hz hyz
        right; right
        rw [e]; ring
    · obtain ⟨z, hz, -, rfl⟩ := semi_dvd hd hq hqd
      rcases hx' with hxc | hxd
      · obtain ⟨y, hy, -, rfl⟩ := semi_dvd hc hx hxc
        have hyz : IsSquare (y * z) :=
          sq_cancel hqx0
            (by rw [show q * x * (q * x) * (y * z) = q * x * (x * y) * (q * z) by ring]; exact hS)
        have e := sq_two_primes hy hz hyz
        right; left
        rw [e]; ring
      · have e := other z hz hxd
        rw [← e] at hS
        exact absurd (sq_cancel hqx0
          (by rw [show q * x * (q * x) * c = q * x * c * (q * x) by ring]; exact hS))
          (semi_not_sq hc)

end OMAErdos888H2

open OMAErdos888H2 in
theorem OMA.solution : OMA.R_Erdos888_erdos_888_variants_semiprimes_R1.H2 := by
  unfold OMA.R_Erdos888_erdos_888_variants_semiprimes_R1.H2
  intro p₁ q₁ p₂ q₂ p₃ q₃ p₄ q₄ hp₁ hq₁ h₁ hp₂ hq₂ h₂ hp₃ hq₃ h₃ hp₄ hq₄ h₄ hab hbc hcd hsq
  have sa : Semi (p₁ * q₁) := ⟨p₁, q₁, hp₁, hq₁, h₁.ne, rfl⟩
  have sb : Semi (p₂ * q₂) := ⟨p₂, q₂, hp₂, hq₂, h₂.ne, rfl⟩
  have sc : Semi (p₃ * q₃) := ⟨p₃, q₃, hp₃, hq₃, h₃.ne, rfl⟩
  have sd : Semi (p₄ * q₄) := ⟨p₄, q₄, hp₄, hq₄, h₄.ne, rfl⟩
  generalize hA : p₁ * q₁ = a at sa hab hsq ⊢
  generalize hB : p₂ * q₂ = b at sb hab hbc hsq ⊢
  generalize hC : p₃ * q₃ = c at sc hbc hcd hsq ⊢
  generalize hD : p₄ * q₄ = d at sd hcd hsq ⊢
  have hdisj : a * b = c * d ∨ a * c = b * d ∨ a * d = b * c := by
    have hp1 : p₁ ∣ b * c * d := by
      have h0 := prime_dvd_of_sq hp₁ (m := q₁ * (b * c * d))
        (by rw [show p₁ * (q₁ * (b * c * d)) = p₁ * q₁ * b * c * d by ring, hA]; exact hsq)
      rcases (Nat.Prime.dvd_mul hp₁).mp h0 with h | h
      · exact absurd ((Nat.prime_dvd_prime_iff_eq hp₁ hq₁).mp h) h₁.ne
      · exact h
    rcases (Nat.Prime.dvd_mul hp₁).mp hp1 with h | h
    · rcases (Nat.Prime.dvd_mul hp₁).mp h with h | h
      · obtain ⟨x, hx, -, hbx⟩ := semi_dvd sb hp₁ h
        exact key hp₁ hq₁ hx hA.symm hbx sc sd hsq
      · obtain ⟨x, hx, -, hcx⟩ := semi_dvd sc hp₁ h
        have h' := key hp₁ hq₁ hx hA.symm hcx sb sd
          (by rw [show a * c * b * d = a * b * c * d by ring]; exact hsq)
        rcases h' with h' | h' | h'
        · exact Or.inr (Or.inl h')
        · exact Or.inl h'
        · exact Or.inr (Or.inr (by rw [h']; ring))
    · obtain ⟨x, hx, -, hdx⟩ := semi_dvd sd hp₁ h
      have h' := key hp₁ hq₁ hx hA.symm hdx sb sc
        (by rw [show a * d * b * c = a * b * c * d by ring]; exact hsq)
      rcases h' with h' | h' | h'
      · exact Or.inr (Or.inr h')
      · exact Or.inl (by rw [h']; ring)
      · exact Or.inr (Or.inl (by rw [h']; ring))
  have hapos := semi_pos sa
  have hbpos := semi_pos sb
  have hcpos := semi_pos sc
  rcases hdisj with h | h | h
  · have hac : a = c := by
      by_contra hne
      have hlt : a < c := lt_of_le_of_ne (le_trans hab hbc) hne
      have : a * b < c * d :=
        calc a * b < c * b := Nat.mul_lt_mul_of_pos_right hlt hbpos
          _ ≤ c * d := Nat.mul_le_mul_left c (le_trans hbc hcd)
      omega
    have hbd : b = d := by
      rw [hac] at h
      exact Nat.eq_of_mul_eq_mul_left hcpos h
    rw [hac, hbd, mul_comm]
  · have hab' : a = b := by
      by_contra hne
      have hlt : a < b := lt_of_le_of_ne hab hne
      have : a * c < b * d :=
        calc a * c < b * c := Nat.mul_lt_mul_of_pos_right hlt hcpos
          _ ≤ b * d := Nat.mul_le_mul_left b hcd
      omega
    have hcd' : c = d := by
      rw [hab'] at h
      exact Nat.eq_of_mul_eq_mul_left hbpos h
    rw [hab', hcd']
  · exact h
