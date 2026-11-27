import OMAReductions.R_Erdos888_erdos_888_variants_semiprimes_R1

-- Step Erdos888.erdos_888.variants.semiprimes.R1.H2: hypothesis H2 of reduction Erdos888.erdos_888.variants.semiprimes.R1
-- Credit: @OrangeHeadz

/-!
Informal plan. Call n a semiprime here if n = p q with primes p < q. Let a ≤ b ≤ c ≤ d be
semiprimes with a b c d a square. Claim: a d = b c.

Tools: for a prime p, p * M square implies p ∣ M; p * p * M square implies M square; a
product of two semiprimes that is a square has equal factors; a semiprime is not a square.

1. Triangle lemma: for primes x ≠ y and semiprimes c, d with x y c d a square, there is z
   with (c = x z and d = y z) or (c = y z and d = x z). Indeed x divides c or d, say c = x z;
   cancelling x² leaves (y z) d a square, so y ≠ z and d = y z.
2. Pairing lemma: if a prime p divides both a and b then a c = b d or a d = b c.
   Write a = p q, b = p s and cancel p². If q = s then c d is a square and c = d.
   Otherwise apply the triangle lemma to q, s, c, d.
3. The prime p₁ divides a, and it divides b c d because its exponent in a b c d is even. Apply
   the pairing lemma with whichever of b, c, d it divides: one of a b = c d, a c = b d,
   a d = b c holds. With a ≤ b ≤ c ≤ d the first two force equalities that give a d = b c.
-/

namespace OMA.E888

def SP (n : ℕ) : Prop := ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p < q ∧ n = p * q

lemma odd_dvd {p M : ℕ} (hp : p.Prime) (h : IsSquare (p * M)) : p ∣ M := by
  obtain ⟨k, hk⟩ := h
  have h1 : p ∣ k * k := ⟨M, hk.symm⟩
  have h2 : p ∣ k := ((Nat.Prime.dvd_mul hp).mp h1).elim id id
  obtain ⟨j, rfl⟩ := h2
  have h3 : p * M = p * (p * (j * j)) := by
    rw [hk]
    ring
  exact ⟨j * j, Nat.eq_of_mul_eq_mul_left hp.pos h3⟩

lemma cancel_sq {p M : ℕ} (hp : p.Prime) (h : IsSquare (p * p * M)) : IsSquare M := by
  obtain ⟨k, hk⟩ := h
  have h1 : p ∣ k * k := ⟨p * M, by rw [← hk]; ring⟩
  have h2 : p ∣ k := ((Nat.Prime.dvd_mul hp).mp h1).elim id id
  obtain ⟨j, rfl⟩ := h2
  refine ⟨j, ?_⟩
  have h3 : p * p * M = p * p * (j * j) := by
    rw [hk]
    ring
  exact Nat.eq_of_mul_eq_mul_left (Nat.mul_pos hp.pos hp.pos) h3

lemma prime_pair {q s : ℕ} (hq : q.Prime) (hs : s.Prime) (h : IsSquare (q * s)) : q = s :=
  (Nat.prime_dvd_prime_iff_eq hq hs).mp (odd_dvd hq h)

lemma SP_dvd {a p : ℕ} (ha : SP a) (hp : p.Prime) (hpa : p ∣ a) :
    ∃ q, q.Prime ∧ q ≠ p ∧ a = p * q := by
  obtain ⟨r, s, hr, hs, hrs, rfl⟩ := ha
  rcases (Nat.Prime.dvd_mul hp).mp hpa with h | h
  · have e := (Nat.prime_dvd_prime_iff_eq hp hr).mp h
    exact ⟨s, hs, by omega, by rw [e]⟩
  · have e := (Nat.prime_dvd_prime_iff_eq hp hs).mp h
    exact ⟨r, hr, by omega, by rw [e, mul_comm]⟩

lemma SP_of_ne {x y : ℕ} (hx : x.Prime) (hy : y.Prime) (hne : x ≠ y) : SP (x * y) := by
  rcases Nat.lt_or_gt_of_ne hne with h | h
  · exact ⟨x, y, hx, hy, h, rfl⟩
  · exact ⟨y, x, hy, hx, h, mul_comm _ _⟩

lemma SP_not_sq {a : ℕ} (ha : SP a) : ¬ IsSquare a := by
  obtain ⟨r, s, hr, hs, hrs, rfl⟩ := ha
  intro h
  have e := prime_pair hr hs h
  omega

lemma SP_pos {a : ℕ} (ha : SP a) : 0 < a := by
  obtain ⟨r, s, hr, hs, -, rfl⟩ := ha
  exact Nat.mul_pos hr.pos hs.pos

lemma SP_eq {u v : ℕ} (hu : SP u) (hv : SP v) (h : IsSquare (u * v)) : u = v := by
  obtain ⟨p, q, hp, hq, hpq, rfl⟩ := hu
  have h1 : p ∣ q * v := odd_dvd hp (by
    have e : p * (q * v) = p * q * v := by ring
    rw [e]
    exact h)
  have h2 : p ∣ v := by
    rcases (Nat.Prime.dvd_mul hp).mp h1 with hx | hx
    · have e := (Nat.prime_dvd_prime_iff_eq hp hq).mp hx
      omega
    · exact hx
  obtain ⟨s, hs, hsp, rfl⟩ := SP_dvd hv hp h2
  have h3 : IsSquare (q * s) := cancel_sq hp (by
    have e : p * p * (q * s) = p * q * (p * s) := by ring
    rw [e]
    exact h)
  rw [prime_pair hq hs h3]

lemma triangle {x y c d : ℕ} (hx : x.Prime) (hy : y.Prime) (hxy : x ≠ y) (hc : SP c)
    (hd : SP d) (h : IsSquare (x * y * c * d)) :
    ∃ z, (c = x * z ∧ d = y * z) ∨ (c = y * z ∧ d = x * z) := by
  have h1 : x ∣ y * c * d := odd_dvd hx (by
    have e : x * (y * c * d) = x * y * c * d := by ring
    rw [e]
    exact h)
  have h2 : x ∣ c ∨ x ∣ d := by
    rcases (Nat.Prime.dvd_mul hx).mp h1 with hu | hu
    · rcases (Nat.Prime.dvd_mul hx).mp hu with hv | hv
      · exact absurd ((Nat.prime_dvd_prime_iff_eq hx hy).mp hv) hxy
      · exact Or.inl hv
    · exact Or.inr hu
  rcases h2 with hxc | hxd
  · obtain ⟨z, hz, hzx, rfl⟩ := SP_dvd hc hx hxc
    have h3 : IsSquare (y * z * d) := cancel_sq hx (by
      have e : x * x * (y * z * d) = x * y * (x * z) * d := by ring
      rw [e]
      exact h)
    have hyz : y ≠ z := by
      intro e
      rw [e] at h3
      exact SP_not_sq hd (cancel_sq hz h3)
    have e := SP_eq (SP_of_ne hy hz hyz) hd h3
    exact ⟨z, Or.inl ⟨rfl, e.symm⟩⟩
  · obtain ⟨z, hz, hzx, rfl⟩ := SP_dvd hd hx hxd
    have h3 : IsSquare (y * z * c) := cancel_sq hx (by
      have e : x * x * (y * z * c) = x * y * c * (x * z) := by ring
      rw [e]
      exact h)
    have hyz : y ≠ z := by
      intro e
      rw [e] at h3
      exact SP_not_sq hc (cancel_sq hz h3)
    have e := SP_eq (SP_of_ne hy hz hyz) hc h3
    exact ⟨z, Or.inr ⟨e.symm, rfl⟩⟩

lemma pair_of_dvd {a b c d p : ℕ} (ha : SP a) (hb : SP b) (hc : SP c) (hd : SP d)
    (hsq : IsSquare (a * b * c * d)) (hp : p.Prime) (hpa : p ∣ a) (hpb : p ∣ b) :
    a * c = b * d ∨ a * d = b * c := by
  obtain ⟨q, hq, hqp, rfl⟩ := SP_dvd ha hp hpa
  obtain ⟨s, hs, hsp, rfl⟩ := SP_dvd hb hp hpb
  have h1 : IsSquare (q * s * c * d) := cancel_sq hp (by
    have e : p * p * (q * s * c * d) = p * q * (p * s) * c * d := by ring
    rw [e]
    exact hsq)
  by_cases hqs : q = s
  · rw [hqs] at h1
    have h2 : IsSquare (c * d) := cancel_sq hs (by
      have e : s * s * (c * d) = s * s * c * d := by ring
      rw [e]
      exact h1)
    have e := SP_eq hc hd h2
    left
    rw [hqs, e]
  · obtain ⟨z, hz | hz⟩ := triangle hq hs hqs hc hd h1
    · right
      rw [hz.1, hz.2]
      ring
    · left
      rw [hz.1, hz.2]
      ring

lemma eq_of_mul_eq {a b c d : ℕ} (h : a * b = c * d) (hac : a ≤ c) (hbd : b ≤ d)
    (hb : 0 < b) (hc : 0 < c) : a = c ∧ b = d := by
  have h1 : a * b ≤ c * b := Nat.mul_le_mul_right b hac
  have h2 : c * b ≤ c * d := Nat.mul_le_mul_left c hbd
  have h3 : a * b = c * b := by omega
  have h4 : c * b = c * d := by omega
  exact ⟨Nat.eq_of_mul_eq_mul_right hb h3, Nat.eq_of_mul_eq_mul_left hc h4⟩

lemma final {a b c d p : ℕ} (ha : SP a) (hb : SP b) (hc : SP c) (hd : SP d)
    (hab : a ≤ b) (hbc : b ≤ c) (hcd : c ≤ d) (hsq : IsSquare (a * b * c * d))
    (hp : p.Prime) (hpa : p ∣ a) : a * d = b * c := by
  have ha0 := SP_pos ha
  have hb0 := SP_pos hb
  have hc0 := SP_pos hc
  have hd0 := SP_pos hd
  obtain ⟨q, hq, hqp, hq_eq⟩ := SP_dvd ha hp hpa
  have h1 : p ∣ q * b * c * d := odd_dvd hp (by
    have e : p * (q * b * c * d) = a * b * c * d := by
      rw [hq_eq]
      ring
    rw [e]
    exact hsq)
  have h2 : p ∣ b ∨ p ∣ c ∨ p ∣ d := by
    rcases (Nat.Prime.dvd_mul hp).mp h1 with h | h
    · rcases (Nat.Prime.dvd_mul hp).mp h with h | h
      · rcases (Nat.Prime.dvd_mul hp).mp h with h | h
        · exact absurd ((Nat.prime_dvd_prime_iff_eq hp hq).mp h).symm hqp
        · exact Or.inl h
      · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
  have key : a * b = c * d ∨ a * c = b * d ∨ a * d = b * c := by
    rcases h2 with h | h | h
    · rcases pair_of_dvd ha hb hc hd hsq hp hpa h with hx | hx
      · exact Or.inr (Or.inl hx)
      · exact Or.inr (Or.inr hx)
    · have hsq2 : IsSquare (a * c * b * d) := by
        have e : a * c * b * d = a * b * c * d := by ring
        rw [e]
        exact hsq
      rcases pair_of_dvd ha hc hb hd hsq2 hp hpa h with hx | hx
      · exact Or.inl hx
      · exact Or.inr (Or.inr (by rw [hx, mul_comm]))
    · have hsq2 : IsSquare (a * d * b * c) := by
        have e : a * d * b * c = a * b * c * d := by ring
        rw [e]
        exact hsq
      rcases pair_of_dvd ha hd hb hc hsq2 hp hpa h with hx | hx
      · exact Or.inl (by rw [hx, mul_comm])
      · exact Or.inr (Or.inl (by rw [hx, mul_comm]))
  rcases key with h | h | h
  · obtain ⟨e1, e2⟩ := eq_of_mul_eq h (le_trans hab hbc) (le_trans hbc hcd) hb0 hc0
    have hd2 : d = a := by omega
    have hc2 : c = a := by omega
    have hb2 : b = a := by omega
    rw [hd2, hc2, hb2]
  · obtain ⟨e1, e2⟩ := eq_of_mul_eq h hab hcd hc0 hb0
    rw [e1, e2]
  · exact h

end OMA.E888

theorem OMA.solution : OMA.R_Erdos888_erdos_888_variants_semiprimes_R1.H2 := by
  unfold OMA.R_Erdos888_erdos_888_variants_semiprimes_R1.H2
  intro p₁ q₁ p₂ q₂ p₃ q₃ p₄ q₄ hp₁ hq₁ h₁ hp₂ hq₂ h₂ hp₃ hq₃ h₃ hp₄ hq₄ h₄ hab hbc hcd hsq
  exact OMA.E888.final ⟨p₁, q₁, hp₁, hq₁, h₁, rfl⟩ ⟨p₂, q₂, hp₂, hq₂, h₂, rfl⟩
    ⟨p₃, q₃, hp₃, hq₃, h₃, rfl⟩ ⟨p₄, q₄, hp₄, hq₄, h₄, rfl⟩ hab hbc hcd hsq hp₁
    (dvd_mul_right _ _)
