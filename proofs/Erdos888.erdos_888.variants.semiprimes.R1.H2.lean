import OMAReductions.R_Erdos888_erdos_888_variants_semiprimes_R1
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Algebra.Group.Even

/-!
For four ordered squarefree semiprimes with square product, every prime factor
occurs an even number of times. Pair equal factors and discard pairings that
identify the two distinct primes of one semiprime. Each remaining pairing
equates the products of two pairs of semiprimes. Ordering forces the outside
pair to have the same product as the inside pair.
-/

private theorem hdTail {p t : ℕ} (hp : p.Prime) (hs : IsSquare (p*t)) : p ∣ t := by
  obtain ⟨r, hr⟩ := hs
  have hd : p ∣ r*r := hr ▸ Nat.dvd_mul_right p t
  obtain ⟨u, rfl⟩ := (hp.dvd_mul.mp hd).elim id id
  refine ⟨u*u, Nat.eq_of_mul_eq_mul_left hp.pos ?_⟩
  simpa only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hr

private theorem hCancel {p t : ℕ} (hp : p.Prime) (hs : IsSquare (p*(p*t))) : IsSquare t := by
  obtain ⟨r, hr⟩ := hs
  have hd : p ∣ r*r := hr ▸ Nat.dvd_mul_right p (p*t)
  obtain ⟨u, rfl⟩ := (hp.dvd_mul.mp hd).elim id id
  refine ⟨u, Nat.eq_of_mul_eq_mul_left (Nat.mul_pos hp.pos hp.pos) ?_⟩
  simpa only [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hr

private theorem hFactors {a b c d : ℕ} (ha : 0 < a) (hc : 0 < c)
    (hab : a ≤ b) (hcd : c ≤ d) (he : a*c = b*d) : a = b ∧ c = d := by
  constructor
  · by_contra hh
    have hlt : a < b := by omega
    exact (Nat.ne_of_lt (lt_of_lt_of_le (Nat.mul_lt_mul_of_pos_right hlt hc)
      (Nat.mul_le_mul_left _ hcd))) he
  · by_contra hh
    have hlt : c < d := by omega
    exact (Nat.ne_of_lt (lt_of_lt_of_le (Nat.mul_lt_mul_of_pos_left hlt ha)
      (Nat.mul_le_mul_right _ hab))) he

private theorem sortedPair {a b c d : ℕ} (ha : 0 < a) (hab : a ≤ b) (hbc : b ≤ c)
    (hcd : c ≤ d) (he : a*b = c*d ∨ a*c = b*d ∨ a*d = b*c) : a*d = b*c := by
  rcases he with h | h | h
  · obtain ⟨hx,hy⟩ := hFactors ha (lt_of_lt_of_le ha hab) (le_trans hab hbc) (le_trans hbc hcd) h
    simp only [hx, hy, Nat.mul_comm]
  · obtain ⟨hx,hy⟩ := hFactors ha (lt_of_lt_of_le ha (le_trans hab hbc)) hab hcd h
    simp only [hx, hy]
  · exact h
-- Remove a matching prime from each end of a pair and keep the remaining square.
private theorem match2 {a b : ℕ} (ha : a.Prime) (hb : b.Prime)
    (hs : IsSquare (a * b)) :
    a = b := by
  have hdiv := hdTail ha hs
  simp only [Nat.prime_dvd_prime_iff_eq ha hb] at hdiv
  exact hdiv

private theorem match4 {a b c d : ℕ} (ha : a.Prime) (hb : b.Prime) (hc : c.Prime) (hd : d.Prime)
    (hs : IsSquare (a * (b * (c * d)))) :
    (a = b ∧ IsSquare (c * d)) ∨ (a = c ∧ IsSquare (b * d)) ∨ (a = d ∧ IsSquare (b * c)) := by
  have hdiv := hdTail ha hs
  simp only [ha.dvd_mul, Nat.prime_dvd_prime_iff_eq ha hb, Nat.prime_dvd_prime_iff_eq ha hc, Nat.prime_dvd_prime_iff_eq ha hd] at hdiv
  rcases hdiv with hbe | hce | hde
  · refine Or.inl ⟨hbe, ?_⟩
    apply hCancel ha
    simpa only [hbe, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hs
  · refine Or.inr (Or.inl ⟨hce, ?_⟩)
    apply hCancel ha
    simpa only [hce, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hs
  · refine Or.inr (Or.inr (⟨hde, ?_⟩))
    apply hCancel ha
    simpa only [hde, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hs

private theorem match6 {a b c d e f : ℕ} (ha : a.Prime) (hb : b.Prime) (hc : c.Prime) (hd : d.Prime) (he : e.Prime) (hf : f.Prime)
    (hs : IsSquare (a * (b * (c * (d * (e * f)))))) :
    (a = b ∧ IsSquare (c * (d * (e * f)))) ∨ (a = c ∧ IsSquare (b * (d * (e * f)))) ∨ (a = d ∧ IsSquare (b * (c * (e * f)))) ∨ (a = e ∧ IsSquare (b * (c * (d * f)))) ∨ (a = f ∧ IsSquare (b * (c * (d * e)))) := by
  have hdiv := hdTail ha hs
  simp only [ha.dvd_mul, Nat.prime_dvd_prime_iff_eq ha hb, Nat.prime_dvd_prime_iff_eq ha hc, Nat.prime_dvd_prime_iff_eq ha hd, Nat.prime_dvd_prime_iff_eq ha he, Nat.prime_dvd_prime_iff_eq ha hf] at hdiv
  rcases hdiv with hbe | hce | hde | hee | hfe
  · refine Or.inl ⟨hbe, ?_⟩
    apply hCancel ha
    simpa only [hbe, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hs
  · refine Or.inr (Or.inl ⟨hce, ?_⟩)
    apply hCancel ha
    simpa only [hce, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hs
  · refine Or.inr (Or.inr (Or.inl ⟨hde, ?_⟩))
    apply hCancel ha
    simpa only [hde, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hs
  · refine Or.inr (Or.inr (Or.inr (Or.inl ⟨hee, ?_⟩)))
    apply hCancel ha
    simpa only [hee, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hs
  · refine Or.inr (Or.inr (Or.inr (Or.inr (⟨hfe, ?_⟩))))
    apply hCancel ha
    simpa only [hfe, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hs

private theorem match8 {a b c d e f g h : ℕ} (ha : a.Prime) (hb : b.Prime) (hc : c.Prime) (hd : d.Prime) (he : e.Prime) (hf : f.Prime) (hg : g.Prime) (hh : h.Prime)
    (hs : IsSquare (a * (b * (c * (d * (e * (f * (g * h)))))))) :
    (a = b ∧ IsSquare (c * (d * (e * (f * (g * h)))))) ∨ (a = c ∧ IsSquare (b * (d * (e * (f * (g * h)))))) ∨ (a = d ∧ IsSquare (b * (c * (e * (f * (g * h)))))) ∨ (a = e ∧ IsSquare (b * (c * (d * (f * (g * h)))))) ∨ (a = f ∧ IsSquare (b * (c * (d * (e * (g * h)))))) ∨ (a = g ∧ IsSquare (b * (c * (d * (e * (f * h)))))) ∨ (a = h ∧ IsSquare (b * (c * (d * (e * (f * g)))))) := by
  have hdiv := hdTail ha hs
  simp only [ha.dvd_mul, Nat.prime_dvd_prime_iff_eq ha hb, Nat.prime_dvd_prime_iff_eq ha hc, Nat.prime_dvd_prime_iff_eq ha hd, Nat.prime_dvd_prime_iff_eq ha he, Nat.prime_dvd_prime_iff_eq ha hf, Nat.prime_dvd_prime_iff_eq ha hg, Nat.prime_dvd_prime_iff_eq ha hh] at hdiv
  rcases hdiv with hbe | hce | hde | hee | hfe | hge | hhe
  · refine Or.inl ⟨hbe, ?_⟩
    apply hCancel ha
    simpa only [hbe, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hs
  · refine Or.inr (Or.inl ⟨hce, ?_⟩)
    apply hCancel ha
    simpa only [hce, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hs
  · refine Or.inr (Or.inr (Or.inl ⟨hde, ?_⟩))
    apply hCancel ha
    simpa only [hde, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hs
  · refine Or.inr (Or.inr (Or.inr (Or.inl ⟨hee, ?_⟩)))
    apply hCancel ha
    simpa only [hee, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hs
  · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hfe, ?_⟩))))
    apply hCancel ha
    simpa only [hfe, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hs
  · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hge, ?_⟩)))))
    apply hCancel ha
    simpa only [hge, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hs
  · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (⟨hhe, ?_⟩))))))
    apply hCancel ha
    simpa only [hhe, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hs


set_option maxHeartbeats 1200000 in
theorem OMA.solution : OMA.R_Erdos888_erdos_888_variants_semiprimes_R1.H2 := by
  intro a b c d e f g h ha hb hab hc hd hcd he hf hef hg hh hgh h12 h23 h34 hs
  apply sortedPair (Nat.mul_pos ha.pos hb.pos) h12 h23 h34
  have ev8 : IsSquare (a * (b * (c * (d * (e * (f * (g * h))))))) := by simpa only [Nat.mul_assoc] using hs
  rcases @match8 _ _ _ _ _ _ _ _ (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) ev8 with
      ⟨hj8, ev6⟩ | ⟨hj8, ev6⟩ | ⟨hj8, ev6⟩ | ⟨hj8, ev6⟩ | ⟨hj8, ev6⟩ | ⟨hj8, ev6⟩ | ⟨hj8, ev6⟩
  all_goals subst_vars
  all_goals try omega
  all_goals rcases @match6 _ _ _ _ _ _ (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) ev6 with
      ⟨hj6, ev4⟩ | ⟨hj6, ev4⟩ | ⟨hj6, ev4⟩ | ⟨hj6, ev4⟩ | ⟨hj6, ev4⟩
  all_goals subst_vars
  all_goals try omega
  all_goals rcases @match4 _ _ _ _ (by assumption) (by assumption) (by assumption) (by assumption) ev4 with
      ⟨hj4, ev2⟩ | ⟨hj4, ev2⟩ | ⟨hj4, ev2⟩
  all_goals subst_vars
  all_goals try omega
  all_goals have hlast := @match2 _ _ (by assumption) (by assumption) ev2
  all_goals subst_vars
  all_goals first | omega | exact Or.inl (by ac_rfl) | exact Or.inr (Or.inl (by ac_rfl)) | exact Or.inr (Or.inr (by ac_rfl))

