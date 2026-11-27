import OMAReductions.R_Erdos700_erdos_700_parts_ii_R1

-- Step Erdos700.erdos_700.parts.ii.R1.H1: hypothesis H1 of reduction Erdos700.erdos_700.parts.ii.R1
-- Credit: @implicitall
-- Proof: write q = p + a, r = p + b with b = 2a + 1 + c and 2 b^2 < p. If two of p, q, r do not
-- divide C(n, k) (n = pqr, 1 < k ≤ n/2), Lucas (via Choose.choose_modEq_choose_mod_mul_choose_div_nat)
-- forces k = (their product) * j, and comparing the last two base-P digits of the reduced binomial
-- coefficients for both primes gives incompatible bounds on j. Hence at least two of p, q, r divide
-- gcd(n, C(n,k)), which is then ≥ p q > sqrt n.

namespace OMA_E700H1

lemma dig {P x y : ℕ} (hP : P.Prime) (h : ¬ P ∣ x.choose y) :
    y % P ≤ x % P ∧ ¬ P ∣ (x / P).choose (y / P) := by
  have := Fact.mk hP
  have hm : x.choose y ≡ (x % P).choose (y % P) * (x / P).choose (y / P) [MOD P] :=
    Choose.choose_modEq_choose_mod_mul_choose_div_nat
  have hiff := Nat.ModEq.dvd_iff hm (dvd_refl P)
  constructor
  · by_contra hlt
    push Not at hlt
    apply h
    rw [hiff, Nat.choose_eq_zero_of_lt hlt, zero_mul]
    exact dvd_zero P
  · intro hd
    apply h
    rw [hiff]
    exact Dvd.dvd.mul_left hd _

lemma dm {P x u v : ℕ} (h : x = P * u + v) (hv : v < P) : x % P = v ∧ x / P = u := by
  have hP : 0 < P := by omega
  have e : P * u + v = v + P * u := by ring
  subst h
  rw [e]
  constructor
  · rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hv]
  · rw [Nat.add_mul_div_left _ _ hP, Nat.div_eq_of_lt hv, zero_add]

end OMA_E700H1
namespace OMA_E700H1

lemma ar_ab (a b p : ℕ) (hab : a ≤ b) (hs : 2 * b ^ 2 < p) : a * b < p := by
  have : a * b ≤ b * b := Nat.mul_le_mul_right b hab
  nlinarith

lemma ar_apb (a b p : ℕ) (hab : a ≤ b) (hs : 2 * b ^ 2 < p) : a + b < p := by
  rcases Nat.eq_zero_or_pos b with h | h
  · subst h; simp at hab; subst hab; omega
  · have : b ≤ b ^ 2 := by nlinarith
    omega

lemma ar_prod (a b p j : ℕ) (hab : a ≤ b) (hs : 2 * b ^ 2 < p) (hj : 2 * j ≤ p + b) :
    (p + a) * j < p * p := by
  have h1 := ar_ab a b p hab hs
  have h2 := ar_apb a b p hab hs
  have h3 : 2 * ((p + a) * j) ≤ (p + a) * (p + b) := by
    have := Nat.mul_le_mul_left (p + a) hj
    linarith
  have h4 : (p + a) * (p + b) < 2 * (p * p) := by
    have : (a + b + 1) * p ≤ p * p := Nat.mul_le_mul_right p (by omega)
    nlinarith
  omega

lemma ar_aj (a b p j : ℕ) (hab : a ≤ b) (hs : 2 * b ^ 2 < p) (hj : j ≤ a + b) : a * j < p := by
  have : a * j ≤ b * (2 * b) := Nat.mul_le_mul hab (by omega)
  nlinarith

end OMA_E700H1
namespace OMA_E700H1

/-- Case: `p` and `q = p + a` both fail to divide. -/
lemma casePQ (p a c j : ℕ) (hp : p.Prime) (hq : (p + a).Prime) (ha : 0 < a)
    (hs : 2 * (2 * a + 1 + c) ^ 2 < p) (hj : 1 ≤ j) (hj2 : 2 * j ≤ p + (2 * a + 1 + c))
    (h1 : ¬ p ∣ ((p + a) * (p + (2 * a + 1 + c))).choose ((p + a) * j))
    (h2 : ¬ (p + a) ∣ (p * (p + (2 * a + 1 + c))).choose (p * j)) : False := by
  set b := 2 * a + 1 + c with hb
  have hab' : a ≤ b := by omega
  have hab : a * b < p := ar_ab a b p hab' hs
  have hapb : a + b < p := ar_apb a b p hab' hs
  obtain ⟨d1, d1'⟩ := dig hp h1
  have d2 := (dig hp d1').1
  obtain ⟨e1, e2⟩ := dm (P := p) (x := (p + a) * (p + b)) (u := p + a + b) (v := a * b)
    (by ring) hab
  rw [e1] at d1
  rw [e2] at d2
  obtain ⟨e3, -⟩ := dm (P := p) (x := p + a + b) (u := 1) (v := a + b) (by ring) hapb
  rw [e3] at d2
  have hlt : (p + a) * j < p * p := ar_prod a b p j hab' hs hj2
  have hjle : j ≤ (p + a) * j / p := by
    rw [Nat.le_div_iff_mul_le hp.pos]
    have := Nat.mul_le_mul_right j (show p ≤ p + a by omega)
    linarith
  have hdlt : (p + a) * j / p < p := by
    rw [Nat.div_lt_iff_lt_mul hp.pos]; exact hlt
  rw [Nat.mod_eq_of_lt hdlt] at d2
  have hjab : j ≤ a + b := by omega
  have haj : a * j < p := ar_aj a b p j hab' hs hjab
  obtain ⟨e4, -⟩ := dm (P := p) (x := (p + a) * j) (u := j) (v := a * j) (by ring) haj
  rw [e4] at d1
  have hjb : j ≤ b := by
    by_contra hh; push Not at hh
    have : a * b < a * j := Nat.mul_lt_mul_of_pos_left hh ha
    omega
  -- base q = p + a
  obtain ⟨f1, f1'⟩ := dig hq h2
  have f2 := (dig hq f1').1
  have hw : a * (a + 1 + c) < p := ar_ab a (a + 1 + c) p (by omega)
    (lt_of_le_of_lt (Nat.mul_le_mul_left 2 (Nat.pow_le_pow_left (by omega) 2)) hs)
  obtain ⟨v, hv⟩ : ∃ v, p + a = a * (a + 1 + c) + v := ⟨p + a - a * (a + 1 + c), by omega⟩
  have hw1 : 1 ≤ a * (a + 1 + c) := Nat.one_le_iff_ne_zero.mpr (by positivity)
  have hvq : v < p + a := by omega
  obtain ⟨g1, g2⟩ := dm (P := p + a) (x := p * (p + b)) (u := p + a + c) (v := v)
    (by rw [hb]; zify at hv ⊢; linear_combination hv) hvq
  rw [g1] at f1
  rw [g2] at f2
  have hc : c < p + a := by
    have : c ≤ b := by omega
    have : b < p := by omega
    omega
  obtain ⟨g3, -⟩ := dm (P := p + a) (x := p + a + c) (u := 1) (v := c) (by ring) hc
  rw [g3] at f2
  obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
  have haj2 : a * (j' + 1) < p + a := by
    have : a * (j' + 1) ≤ a * b := Nat.mul_le_mul_left a hjb
    omega
  obtain ⟨t, ht⟩ : ∃ t, p + a = a * (j' + 1) + t := ⟨p + a - a * (j' + 1), by omega⟩
  have hta : 1 ≤ a * (j' + 1) := Nat.one_le_iff_ne_zero.mpr (by positivity)
  have htq : t < p + a := by omega
  obtain ⟨g4, g5⟩ := dm (P := p + a) (x := p * (j' + 1)) (u := j') (v := t)
    (by zify at ht ⊢; linear_combination ht) htq
  rw [g4] at f1
  rw [g5] at f2
  have hj'q : j' < p + a := by omega
  rw [Nat.mod_eq_of_lt hj'q] at f2
  have h3 : a * (a + 1 + c) ≤ a * (j' + 1) := by omega
  have := Nat.le_of_mul_le_mul_left h3 ha
  omega

end OMA_E700H1
namespace OMA_E700H1

lemma ar_prod' (a b p j : ℕ) (hab : a ≤ b) (hs : 2 * b ^ 2 < p) (hj : 2 * j ≤ p + a) :
    (p + b) * j < p * p := by
  have h1 := ar_ab a b p hab hs
  have h2 := ar_apb a b p hab hs
  have h3 : 2 * ((p + b) * j) ≤ (p + b) * (p + a) := by
    have := Nat.mul_le_mul_left (p + b) hj
    linarith
  have h4 : (p + b) * (p + a) < 2 * (p * p) := by
    have : (a + b + 1) * p ≤ p * p := Nat.mul_le_mul_right p (by omega)
    nlinarith
  omega

/-- `p * q` written in base `r = p + b`. -/
lemma pq_base_r (p a c : ℕ) (hs : 2 * (2 * a + 1 + c) ^ 2 < p) :
    (p * (p + a)) % (p + (2 * a + 1 + c)) = (2 * a + 1 + c) * (a + 1 + c) := by
  have hb : a + 1 + c ≤ 2 * a + 1 + c := by omega
  have hm : (2 * a + 1 + c) * (a + 1 + c) < p :=
    lt_of_le_of_lt (Nat.mul_le_mul_left _ hb) (by nlinarith)
  have hle : a + 1 + c ≤ (2 * a + 1 + c) * (a + 1 + c) := Nat.le_mul_of_pos_left _ (by omega)
  obtain ⟨u, hu⟩ : ∃ u, p = u + (a + 1 + c) := ⟨p - (a + 1 + c), by omega⟩
  refine (dm (P := p + (2 * a + 1 + c)) (u := u) (by rw [hu]; ring) (by omega)).1

/-- Case: `p` and `r = p + b` both fail to divide. -/
lemma casePR (p a c j : ℕ) (hp : p.Prime) (hr : (p + (2 * a + 1 + c)).Prime) (ha : 0 < a)
    (hs : 2 * (2 * a + 1 + c) ^ 2 < p) (hj : 1 ≤ j) (hj2 : 2 * j ≤ p + a)
    (h1 : ¬ p ∣ ((p + (2 * a + 1 + c)) * (p + a)).choose ((p + (2 * a + 1 + c)) * j))
    (h2 : ¬ (p + (2 * a + 1 + c)) ∣ (p * (p + a)).choose (p * j)) : False := by
  have hpq := pq_base_r p a c hs
  set b := 2 * a + 1 + c with hb
  have hab' : a ≤ b := by omega
  have hab : a * b < p := ar_ab a b p hab' hs
  have hapb : a + b < p := ar_apb a b p hab' hs
  obtain ⟨d1, d1'⟩ := dig hp h1
  have d2 := (dig hp d1').1
  obtain ⟨e1, e2⟩ := dm (P := p) (x := (p + b) * (p + a)) (u := p + a + b) (v := a * b)
    (by ring) hab
  rw [e1] at d1
  rw [e2] at d2
  obtain ⟨e3, -⟩ := dm (P := p) (x := p + a + b) (u := 1) (v := a + b) (by ring) hapb
  rw [e3] at d2
  have hlt : (p + b) * j < p * p := ar_prod' a b p j hab' hs hj2
  have hjle : j ≤ (p + b) * j / p := by
    rw [Nat.le_div_iff_mul_le hp.pos]
    have := Nat.mul_le_mul_right j (show p ≤ p + b by omega)
    linarith
  have hdlt : (p + b) * j / p < p := by
    rw [Nat.div_lt_iff_lt_mul hp.pos]; exact hlt
  rw [Nat.mod_eq_of_lt hdlt] at d2
  have hjab : j ≤ a + b := by omega
  have hbj : b * j < p := ar_aj b b p j le_rfl hs (by omega)
  obtain ⟨e4, -⟩ := dm (P := p) (x := (p + b) * j) (u := j) (v := b * j) (by ring) hbj
  rw [e4] at d1
  have hja : j ≤ a := by
    by_contra hh; push Not at hh
    have : b * a < b * j := Nat.mul_lt_mul_of_pos_left hh (by omega)
    have : a * b = b * a := Nat.mul_comm a b
    omega
  -- base r = p + b, one digit suffices
  have f1 := (dig hr h2).1
  rw [hpq] at f1
  obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
  have hbj2 : b * (j' + 1) ≤ b * a := Nat.mul_le_mul_left b hja
  obtain ⟨t, ht⟩ : ∃ t, p + b = b * (j' + 1) + t := ⟨p + b - b * (j' + 1), by omega⟩
  have hta : 1 ≤ b * (j' + 1) := Nat.one_le_iff_ne_zero.mpr (by positivity)
  have htq : t < p + b := by omega
  obtain ⟨g4, -⟩ := dm (P := p + b) (x := p * (j' + 1)) (u := j') (v := t)
    (by zify at ht ⊢; linear_combination ht) htq
  rw [g4] at f1
  -- f1 : t ≤ b * (a + 1 + c), so p + b ≤ b * a + b * (a + 1 + c) = b * b < p
  have hbb : b * a + b * (a + 1 + c) = b * b := by rw [hb]; ring
  have : b * b < p := by nlinarith
  omega

/-- Case: `q = p + a` and `r = p + b` both fail to divide. -/
lemma caseQR (p a c j : ℕ) (hq : (p + a).Prime) (hr : (p + (2 * a + 1 + c)).Prime) (ha : 0 < a)
    (hs : 2 * (2 * a + 1 + c) ^ 2 < p) (hj : 1 ≤ j) (hj2 : 2 * j ≤ p)
    (h1 : ¬ (p + a) ∣ ((p + (2 * a + 1 + c)) * p).choose ((p + (2 * a + 1 + c)) * j))
    (h2 : ¬ (p + (2 * a + 1 + c)) ∣ ((p + a) * p).choose ((p + a) * j)) : False := by
  have hpq := pq_base_r p a c hs
  set b := 2 * a + 1 + c with hb
  have hab' : a ≤ b := by omega
  have hab : a * b < p := ar_ab a b p hab' hs
  have hapb : a + b < p := ar_apb a b p hab' hs
  -- base q = p + a, two digits
  obtain ⟨f1, f1'⟩ := dig hq h1
  have f2 := (dig hq f1').1
  have hw : a * (a + 1 + c) < p := lt_of_le_of_lt (Nat.mul_le_mul_left a (by omega)) hab
  obtain ⟨v, hv⟩ : ∃ v, p + a = a * (a + 1 + c) + v := ⟨p + a - a * (a + 1 + c), by omega⟩
  have hw1 : 1 ≤ a * (a + 1 + c) := Nat.one_le_iff_ne_zero.mpr (by positivity)
  have hvq : v < p + a := by omega
  obtain ⟨g1, g2⟩ := dm (P := p + a) (x := (p + b) * p) (u := p + a + c) (v := v)
    (by rw [hb]; zify at hv ⊢; linear_combination hv) hvq
  rw [g2] at f2
  have hc : c < p + a := by omega
  obtain ⟨g3, -⟩ := dm (P := p + a) (x := p + a + c) (u := 1) (v := c) (by ring) hc
  rw [g3] at f2
  have hlt : (p + b) * j < (p + a) * (p + a) := by
    have h3 : 2 * ((p + b) * j) ≤ (p + b) * p := by
      have := Nat.mul_le_mul_left (p + b) hj2
      linarith
    have h4 : (p + b) * p < 2 * ((p + a) * (p + a)) := by
      have : b * p < p * p := Nat.mul_lt_mul_of_pos_right (by omega) (by omega)
      nlinarith
    omega
  have hjle : j ≤ (p + b) * j / (p + a) := by
    rw [Nat.le_div_iff_mul_le (by omega)]
    have := Nat.mul_le_mul_right j (show p + a ≤ p + b by omega)
    linarith
  have hdlt : (p + b) * j / (p + a) < p + a := by
    rw [Nat.div_lt_iff_lt_mul (by omega)]; exact hlt
  rw [Nat.mod_eq_of_lt hdlt] at f2
  have hjc : j ≤ c := by omega
  -- base r = p + b, one digit
  have k1 := (dig hr h2).1
  have hpq' : (p + a) * p = p * (p + a) := Nat.mul_comm _ _
  rw [hpq', hpq] at k1
  obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
  have hm : (a + 1 + c) * (j' + 1) ≤ (a + 1 + c) * c := Nat.mul_le_mul_left _ hjc
  have hmc : (a + 1 + c) * c < p := by
    have : (a + 1 + c) * c ≤ b * b := Nat.mul_le_mul (by omega) (by omega)
    nlinarith
  obtain ⟨t, ht⟩ : ∃ t, p + b = (a + 1 + c) * (j' + 1) + t :=
    ⟨p + b - (a + 1 + c) * (j' + 1), by omega⟩
  have hta : 1 ≤ (a + 1 + c) * (j' + 1) := Nat.one_le_iff_ne_zero.mpr (by positivity)
  have htq : t < p + b := by omega
  obtain ⟨g4, -⟩ := dm (P := p + b) (x := (p + a) * (j' + 1)) (u := j') (v := t)
    (by rw [hb] at ht ⊢; zify at ht ⊢; linear_combination ht) htq
  rw [g4] at k1
  -- k1 : t ≤ b * (a + 1 + c); so p + b ≤ (a+1+c) * (j'+1) + b * (a+1+c) < 2 b^2 < p
  have h5 : (a + 1 + c) * (j' + 1) + b * (a + 1 + c) ≤ 2 * b ^ 2 := by
    have : (a + 1 + c) * (j' + 1) ≤ b * b := le_trans hm (Nat.mul_le_mul (by omega) (by omega))
    have : b * (a + 1 + c) ≤ b * b := Nat.mul_le_mul_left b (by omega)
    nlinarith
  omega

end OMA_E700H1
namespace OMA_E700H1

lemma red {P X Y : ℕ} (hP : P.Prime) (h : ¬ P ∣ (P * X).choose (P * Y)) : ¬ P ∣ X.choose Y := by
  have := (dig hP h).2
  rwa [Nat.mul_div_cancel_left _ hP.pos, Nat.mul_div_cancel_left _ hP.pos] at this

lemma key (p a c k : ℕ) (hp : p.Prime) (hq : (p + a).Prime) (hr : (p + (2 * a + 1 + c)).Prime)
    (ha : 0 < a) (hs : 2 * (2 * a + 1 + c) ^ 2 < p) (hk1 : 1 < k)
    (hk2 : k ≤ p * (p + a) * (p + (2 * a + 1 + c)) / 2) :
    p * (p + a) ≤ Nat.gcd (p * (p + a) * (p + (2 * a + 1 + c)))
      ((p * (p + a) * (p + (2 * a + 1 + c))).choose k) := by
  set b := 2 * a + 1 + c with hb
  set n := p * (p + a) * (p + b) with hn
  have hp2 := hp.two_le
  have hn0 : 0 < n := by positivity
  have hg0 : 0 < Nat.gcd n (n.choose k) := Nat.gcd_pos_of_pos_left _ hn0
  have hk2' : k * 2 ≤ n := (Nat.le_div_iff_mul_le two_pos).mp hk2
  have cpq : Nat.Coprime p (p + a) := (Nat.coprime_primes hp hq).2 (by omega)
  have cpr : Nat.Coprime p (p + b) := (Nat.coprime_primes hp hr).2 (by omega)
  have cqr : Nat.Coprime (p + a) (p + b) := (Nat.coprime_primes hq hr).2 (by omega)
  have dpn : p ∣ n := ⟨(p + a) * (p + b), by rw [hn]; ring⟩
  have dqn : (p + a) ∣ n := ⟨p * (p + b), by rw [hn]; ring⟩
  have drn : (p + b) ∣ n := ⟨p * (p + a), by rw [hn]; ring⟩
  by_cases h1 : p ∣ n.choose k <;> by_cases h2 : (p + a) ∣ n.choose k <;>
    by_cases h3 : (p + b) ∣ n.choose k
  · exact Nat.le_of_dvd hg0 (Nat.Coprime.mul_dvd_of_dvd_of_dvd cpq
      (Nat.dvd_gcd dpn h1) (Nat.dvd_gcd dqn h2))
  · exact Nat.le_of_dvd hg0 (Nat.Coprime.mul_dvd_of_dvd_of_dvd cpq
      (Nat.dvd_gcd dpn h1) (Nat.dvd_gcd dqn h2))
  · refine le_trans (Nat.mul_le_mul_left p (by omega)) (Nat.le_of_dvd hg0
      (Nat.Coprime.mul_dvd_of_dvd_of_dvd cpr (Nat.dvd_gcd dpn h1) (Nat.dvd_gcd drn h3)))
  · -- only p divides: q and r do not
    exfalso
    have hqk := Erdos700.prime_dvd_of_not_dvd_choose _ n k hq dqn h2
    have hrk := Erdos700.prime_dvd_of_not_dvd_choose _ n k hr drn h3
    obtain ⟨j, rfl⟩ := Nat.Coprime.mul_dvd_of_dvd_of_dvd cqr hqk hrk
    have hj : 1 ≤ j := by
      rcases Nat.eq_zero_or_pos j with h | h
      · subst h; omega
      · exact h
    have hj2 : 2 * j ≤ p := by
      have : (p + a) * (p + b) * (2 * j) ≤ (p + a) * (p + b) * p := by
        rw [hn] at hk2'; nlinarith
      exact Nat.le_of_mul_le_mul_left this (by positivity)
    have e1 : n = (p + a) * ((p + b) * p) := by rw [hn]; ring
    have e2 : (p + a) * (p + b) * j = (p + a) * ((p + b) * j) := by ring
    have e3 : n = (p + b) * ((p + a) * p) := by rw [hn]; ring
    have e4 : (p + a) * (p + b) * j = (p + b) * ((p + a) * j) := by ring
    have h2' := h2
    rw [e1, e2] at h2'
    rw [e3, e4] at h3
    exact caseQR p a c j hq hr ha hs hj hj2 (red hq h2') (red hr h3)
  · refine le_trans ?_ (Nat.le_of_dvd hg0
      (Nat.Coprime.mul_dvd_of_dvd_of_dvd cqr (Nat.dvd_gcd dqn h2) (Nat.dvd_gcd drn h3)))
    rw [Nat.mul_comm]; exact Nat.mul_le_mul_left _ (by omega)
  · -- only q divides: p and r do not
    exfalso
    have hpk := Erdos700.prime_dvd_of_not_dvd_choose _ n k hp dpn h1
    have hrk := Erdos700.prime_dvd_of_not_dvd_choose _ n k hr drn h3
    obtain ⟨j, rfl⟩ := Nat.Coprime.mul_dvd_of_dvd_of_dvd cpr hpk hrk
    have hj : 1 ≤ j := by
      rcases Nat.eq_zero_or_pos j with h | h
      · subst h; omega
      · exact h
    have hj2 : 2 * j ≤ p + a := by
      have : p * (p + b) * (2 * j) ≤ p * (p + b) * (p + a) := by
        rw [hn] at hk2'; nlinarith
      exact Nat.le_of_mul_le_mul_left this (by positivity)
    have e1 : n = p * ((p + b) * (p + a)) := by rw [hn]; ring
    have e2 : p * (p + b) * j = p * ((p + b) * j) := by ring
    have e3 : n = (p + b) * (p * (p + a)) := by rw [hn]; ring
    have e4 : p * (p + b) * j = (p + b) * (p * j) := by ring
    have h1' := h1
    rw [e1, e2] at h1'
    rw [e3, e4] at h3
    exact casePR p a c j hp hr ha hs hj hj2 (red hp h1') (red hr h3)
  · -- only r divides (or none): p and q do not
    exfalso
    have hpk := Erdos700.prime_dvd_of_not_dvd_choose _ n k hp dpn h1
    have hqk := Erdos700.prime_dvd_of_not_dvd_choose _ n k hq dqn h2
    obtain ⟨j, rfl⟩ := Nat.Coprime.mul_dvd_of_dvd_of_dvd cpq hpk hqk
    have hj : 1 ≤ j := by
      rcases Nat.eq_zero_or_pos j with h | h
      · subst h; omega
      · exact h
    have hj2 : 2 * j ≤ p + b := by
      have : p * (p + a) * (2 * j) ≤ p * (p + a) * (p + b) := by
        rw [hn] at hk2'; nlinarith
      exact Nat.le_of_mul_le_mul_left this (by positivity)
    have e1 : n = p * ((p + a) * (p + b)) := by rw [hn]; ring
    have e2 : p * (p + a) * j = p * ((p + a) * j) := by ring
    have e3 : n = (p + a) * (p * (p + b)) := by rw [hn]; ring
    have e4 : p * (p + a) * j = (p + a) * (p * j) := by ring
    have h1' := h1
    rw [e1, e2] at h1'
    rw [e3, e4] at h2
    exact casePQ p a c j hp hq ha hs hj hj2 (red hp h1') (red hq h2)
  · exfalso
    have hpk := Erdos700.prime_dvd_of_not_dvd_choose _ n k hp dpn h1
    have hqk := Erdos700.prime_dvd_of_not_dvd_choose _ n k hq dqn h2
    obtain ⟨j, rfl⟩ := Nat.Coprime.mul_dvd_of_dvd_of_dvd cpq hpk hqk
    have hj : 1 ≤ j := by
      rcases Nat.eq_zero_or_pos j with h | h
      · subst h; omega
      · exact h
    have hj2 : 2 * j ≤ p + b := by
      have : p * (p + a) * (2 * j) ≤ p * (p + a) * (p + b) := by
        rw [hn] at hk2'; nlinarith
      exact Nat.le_of_mul_le_mul_left this (by positivity)
    have e1 : n = p * ((p + a) * (p + b)) := by rw [hn]; ring
    have e2 : p * (p + a) * j = p * ((p + a) * j) := by ring
    have e3 : n = (p + a) * (p * (p + b)) := by rw [hn]; ring
    have e4 : p * (p + a) * j = (p + a) * (p * j) := by ring
    have h1' := h1
    rw [e1, e2] at h1'
    rw [e3, e4] at h2
    exact casePQ p a c j hp hq ha hs hj hj2 (red hp h1') (red hq h2)

end OMA_E700H1

open OMA_E700H1 in
theorem OMA.solution : OMA.R_Erdos700_erdos_700_parts_ii_R1.H1 := by
  intro p q r hp hq hr hpq hqr hgap hsmall
  obtain ⟨a, rfl⟩ : ∃ a, q = p + a := ⟨q - p, by omega⟩
  obtain ⟨c, rfl⟩ : ∃ c, r = p + (2 * a + 1 + c) := ⟨r - p - (2 * a + 1), by omega⟩
  have ha : 0 < a := by omega
  have hs : 2 * (2 * a + 1 + c) ^ 2 < p := by
    have e : p + (2 * a + 1 + c) - p = 2 * a + 1 + c := by omega
    rw [e] at hsmall; exact hsmall
  have hp2 := hp.two_le
  have hb : 2 * a + 1 + c < p := by nlinarith
  have hn4 : 2 ≤ p * (p + a) * (p + (2 * a + 1 + c)) / 2 := by
    rw [Nat.le_div_iff_mul_le two_pos]
    have : 2 * 2 * 1 ≤ p * (p + a) * (p + (2 * a + 1 + c)) :=
      Nat.mul_le_mul (Nat.mul_le_mul hp2 (by omega)) (by omega)
    omega
  have hne : (Erdos700.fSet (p * (p + a) * (p + (2 * a + 1 + c)))).Nonempty :=
    ⟨_, Erdos700.f_mem _ 2 (by omega) hn4⟩
  obtain ⟨k, hk1, hk2, hkeq⟩ := Nat.sInf_mem hne
  have hf : Erdos700.f (p * (p + a) * (p + (2 * a + 1 + c))) =
      Nat.gcd (p * (p + a) * (p + (2 * a + 1 + c)))
        ((p * (p + a) * (p + (2 * a + 1 + c))).choose k) := by
    rw [Erdos700.f_eq]; exact hkeq
  have hkey := key p a c k hp hq hr ha hs hk1 hk2
  rw [hf]
  have hlt : p + (2 * a + 1 + c) < p * (p + a) := by nlinarith
  have hpos : 0 < p * (p + a) := by positivity
  calc p * (p + a) * (p + (2 * a + 1 + c)) < p * (p + a) * (p * (p + a)) :=
        Nat.mul_lt_mul_of_pos_left hlt hpos
    _ ≤ _ := by rw [sq]; exact Nat.mul_le_mul hkey hkey
