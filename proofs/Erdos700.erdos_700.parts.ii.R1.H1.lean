import OMAReductions.R_Erdos700_erdos_700_parts_ii_R1
import Mathlib.Tactic

/-!
# Erdos Problem 700, Step H1

Proof of Tresmontant's Lucas-digit inequality for close prime triples `p < q < r`
with increasing gaps `q - p < r - q` and `2 * (r - p) ^ 2 < p`.
-/

private lemma lucas_mod_le (P A B : ℕ) (hP : P.Prime) (h : ¬ P ∣ A.choose B) :
    B % P ≤ A % P := by
  have : Fact P.Prime := ⟨hP⟩
  by_contra hlt
  have hlt' : A % P < B % P := by omega
  apply h
  have hmod : A.choose B ≡ (A % P).choose (B % P) * (A / P).choose (B / P) [MOD P] :=
    Choose.choose_modEq_choose_mod_mul_choose_div_nat
  rw [Nat.choose_eq_zero_of_lt hlt', zero_mul] at hmod
  exact (Nat.modEq_zero_iff_dvd).1 hmod

private lemma lucas_not_dvd_div (P A B : ℕ) (hP : P.Prime) (h : ¬ P ∣ A.choose B) :
    ¬ P ∣ (A / P).choose (B / P) := by
  have : Fact P.Prime := ⟨hP⟩
  intro hdvd
  apply h
  have hmod : A.choose B ≡ (A % P).choose (B % P) * (A / P).choose (B / P) [MOD P] :=
    Choose.choose_modEq_choose_mod_mul_choose_div_nat
  have h0 : (A % P).choose (B % P) * (A / P).choose (B / P) ≡ 0 [MOD P] :=
    (Nat.modEq_zero_iff_dvd).2 (dvd_mul_of_dvd_right hdvd _)
  exact (Nat.modEq_zero_iff_dvd).1 (hmod.trans h0)

private lemma not_dvd_choose_of_mul (P A B : ℕ) (hP : P.Prime)
    (h : ¬ P ∣ (A * P).choose (B * P)) : ¬ P ∣ A.choose B := by
  have hdiv := lucas_not_dvd_div P (A * P) (B * P) hP h
  rwa [Nat.mul_div_cancel _ hP.pos, Nat.mul_div_cancel _ hP.pos] at hdiv

private lemma lucas_div_le (P A B : ℕ) (hP : P.Prime) (hB : B < P ^ 2)
    (h : ¬ P ∣ A.choose B) : B / P ≤ (A / P) % P := by
  have hle := lucas_mod_le P (A / P) (B / P) hP (lucas_not_dvd_div P A B hP h)
  have hdm : P * (B / P) + B % P = B := Nat.div_add_mod B P
  rw [sq] at hB
  have hBP : B / P < P := by
    by_contra hge
    have h1 : P ≤ B / P := by omega
    have h2 : P * P ≤ P * (B / P) := Nat.mul_le_mul_left P h1
    omega
  rwa [Nat.mod_eq_of_lt hBP] at hle

private lemma div_mod_of_eq (X P Q R : ℕ) (hX : X = Q * P + R) (hR : R < P) :
    X / P = Q ∧ X % P = R := by
  have hP : 0 < P := by omega
  have hdm : P * (X / P) + X % P = X := Nat.div_add_mod X P
  have hm : X % P < P := Nat.mod_lt X hP
  have hQ : X / P = Q := by
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
    · have h1 : X / P + 1 ≤ Q := hlt
      have h2 : P * (X / P) + P ≤ Q * P := by
        calc P * (X / P) + P = P * (X / P + 1) := by ring
          _ ≤ P * Q := Nat.mul_le_mul_left P h1
          _ = Q * P := mul_comm P Q
      omega
    · have h1 : Q + 1 ≤ X / P := hgt
      have h2 : Q * P + P ≤ P * (X / P) := by
        calc Q * P + P = P * (Q + 1) := by ring
          _ ≤ P * (X / P) := Nat.mul_le_mul_left P h1
      omega
  refine ⟨hQ, ?_⟩
  rw [hQ, mul_comm P Q] at hdm
  omega

private lemma le_div_of_mul_le (m q X : ℕ) (hq : 0 < q) (h : m * q ≤ X) :
    m ≤ X / q := by
  have hdm : q * (X / q) + X % q = X := Nat.div_add_mod X q
  have hm : X % q < q := Nat.mod_lt X hq
  by_contra hlt
  have h1 : X / q + 1 ≤ m := by omega
  have h2 : q * (X / q) + q ≤ m * q := by
    calc q * (X / q) + q = q * (X / q + 1) := by ring
      _ ≤ q * m := Nat.mul_le_mul_left q h1
      _ = m * q := mul_comm q m
  omega

private lemma add_sq_lt_two_sq (p δ : ℕ) (hδ : 3 ≤ δ) (hsmall : 2 * δ ^ 2 < p) :
    (p + δ) ^ 2 < 2 * p ^ 2 := by
  have hsmall' : 2 * (δ * δ) < p := by rwa [sq] at hsmall
  have h6δ : 6 * δ ≤ 2 * (δ * δ) := by
    calc 6 * δ = 2 * 3 * δ := by ring
      _ ≤ 2 * δ * δ := Nat.mul_le_mul_right δ (by omega)
      _ = 2 * (δ * δ) := by ring
  have h6δ1 : 6 * δ + 1 ≤ p := by omega
  have h1 : 6 * (δ * p) + p ≤ p * p := by
    calc 6 * (δ * p) + p = (6 * δ + 1) * p := by ring
      _ ≤ p * p := Nat.mul_le_mul_right p h6δ1
  have h2 : (p + δ) ^ 2 = p * p + 2 * (δ * p) + δ * δ := by ring
  have h3 : 2 * p ^ 2 = 2 * (p * p) := by ring
  omega

private lemma pr_base_q (p q r : ℕ) (hpq : p < q) (hqr : q < r)
    (hgap : q - p < r - q) (hsmall : 2 * (r - p) ^ 2 < p) :
    ((p * r) / q) % q = (r - q) - (q - p) - 1 ∧
      (p * r) % q = q - (q - p) * (r - q) := by
  let δ₁ := q - p
  let δ₂ := r - q
  let δ := r - p
  let c₁ := δ₂ - δ₁ - 1
  let c₀ := q - δ₁ * δ₂
  have hsmall' : 2 * (δ * δ) < p := by dsimp [δ]; rwa [sq] at hsmall
  have hδ_le_sq : δ ≤ δ * δ := by
    calc δ = 1 * δ := by ring
      _ ≤ δ * δ := Nat.mul_le_mul_right δ (by omega)
  have hδ₁δ₂_le : δ₁ * δ₂ ≤ δ * δ := Nat.mul_le_mul (by omega) (by omega)
  have hδ₁δ₂_pos : 0 < δ₁ * δ₂ := Nat.mul_pos (by omega) (by omega)
  have hc₁_eq : δ₂ = c₁ + δ₁ + 1 := by omega
  have hc₁_lt_q : c₁ < q := by omega
  have hc₀_lt_q : c₀ < q := by omega
  let p₀ := p - δ₁ * δ₂
  have hp₀ : p = p₀ + δ₁ * (c₁ + δ₁ + 1) := by
    have hp_eq : p = p₀ + δ₁ * δ₂ := by omega
    rw [hp_eq, hc₁_eq]
  have hq₀ : q = p₀ + δ₁ * (c₁ + δ₁ + 1) + δ₁ := by
    have hq_eq : q = p + δ₁ := by omega
    rw [hq_eq, hp₀]
  have hr₀ : r = p₀ + δ₁ * (c₁ + δ₁ + 1) + δ₁ + (c₁ + δ₁ + 1) := by
    have hr_eq : r = q + δ₂ := by omega
    rw [hr_eq, hq₀, hc₁_eq]
  have hc₀_eq : c₀ = p₀ + δ₁ := by omega
  have hpr_eq : p * r = (1 * q + c₁) * q + c₀ := by
    rw [hp₀, hq₀, hr₀, hc₀_eq]
    ring
  obtain ⟨hdiv, hmod⟩ := div_mod_of_eq (p * r) q (1 * q + c₁) c₀ hpr_eq hc₀_lt_q
  obtain ⟨_, hmod2⟩ := div_mod_of_eq ((p * r) / q) q 1 c₁ hdiv hc₁_lt_q
  exact ⟨hmod2, hmod⟩

private lemma pq_mod_r (p q r : ℕ) (hpq : p < q) (hqr : q < r)
    (hgap : q - p < r - q) (hsmall : 2 * (r - p) ^ 2 < p) :
    (p * q) % r = (r - p) * (r - q) := by
  let δ := r - p
  let δ₂ := r - q
  have hsmall' : 2 * (δ * δ) < p := by dsimp [δ]; rwa [sq] at hsmall
  have h6δ : 6 * δ ≤ 2 * (δ * δ) := by
    calc 6 * δ = 2 * 3 * δ := by ring
      _ ≤ 2 * δ * δ := Nat.mul_le_mul_right δ (by omega)
      _ = 2 * (δ * δ) := by ring
  have hδδ₂_le : δ * δ₂ ≤ δ * δ := Nat.mul_le_mul (by omega) (by omega)
  let d := r - δ - δ₂
  have hp_d : p = d + δ₂ := by omega
  have hq_d : q = d + δ := by omega
  have hr_d : r = d + δ + δ₂ := by omega
  have hpq_eq : p * q = d * r + δ * δ₂ := by
    rw [hp_d, hq_d, hr_d]
    ring
  exact (div_mod_of_eq (p * q) r d (δ * δ₂) hpq_eq (by omega)).2

private lemma qr_div_mod_p (p q r : ℕ) (hpq : p < q) (hqr : q < r)
    (hgap : q - p < r - q) (hsmall : 2 * (r - p) ^ 2 < p) :
    ((q * r) / p) % p = (q - p) + (r - p) := by
  let δ₁ := q - p
  let δ := r - p
  have hsmall' : 2 * (δ * δ) < p := by dsimp [δ]; rwa [sq] at hsmall
  have h6δ : 6 * δ ≤ 2 * (δ * δ) := by
    calc 6 * δ = 2 * 3 * δ := by ring
      _ ≤ 2 * δ * δ := Nat.mul_le_mul_right δ (by omega)
      _ = 2 * (δ * δ) := by ring
  have hδ₁δ_le : δ₁ * δ ≤ δ * δ := Nat.mul_le_mul (by omega) (by omega)
  have hq_eq : q = p + δ₁ := by omega
  have hr_eq : r = p + δ := by omega
  have hqr_eq : q * r = (1 * p + (δ₁ + δ)) * p + δ₁ * δ := by
    rw [hq_eq, hr_eq]
    ring
  obtain ⟨hdiv, _⟩ := div_mod_of_eq (q * r) p (1 * p + (δ₁ + δ)) (δ₁ * δ) hqr_eq (by omega)
  exact (div_mod_of_eq ((q * r) / p) p 1 (δ₁ + δ) hdiv (by omega)).2

private lemma case_qr (p q r k : ℕ) (hq : q.Prime) (hr : r.Prime)
    (hpq : p < q) (hqr : q < r) (hgap : q - p < r - q) (hsmall : 2 * (r - p) ^ 2 < p)
    (hk1 : 1 < k) (hk2 : k ≤ p * q * r / 2)
    (hqC : ¬ q ∣ (p * q * r).choose k) (hrC : ¬ r ∣ (p * q * r).choose k) : False := by
  let δ₁ := q - p
  let δ₂ := r - q
  let δ := r - p
  let c₁ := δ₂ - δ₁ - 1
  have hsmall' : 2 * (δ * δ) < p := by dsimp [δ]; rwa [sq] at hsmall
  have h6δ : 6 * δ ≤ 2 * (δ * δ) := by
    calc 6 * δ = 2 * 3 * δ := by ring
      _ ≤ 2 * δ * δ := Nat.mul_le_mul_right δ (by omega)
      _ = 2 * (δ * δ) := by ring
  have hqk : q ∣ k :=
    Erdos700.prime_dvd_of_not_dvd_choose q (p * q * r) k hq ⟨p * r, by ring⟩ hqC
  have hrk : r ∣ k :=
    Erdos700.prime_dvd_of_not_dvd_choose r (p * q * r) k hr ⟨p * q, by ring⟩ hrC
  have hqrk : q * r ∣ k :=
    Nat.Coprime.mul_dvd_of_dvd_of_dvd ((Nat.coprime_primes hq hr).2 (by omega)) hqk hrk
  obtain ⟨m, hm_eq⟩ := hqrk
  have hm_pos : 1 ≤ m := by
    rcases Nat.eq_zero_or_pos m with rfl | hpos
    · simp at hm_eq; omega
    · exact hpos
  have h2m_le : 2 * m ≤ p := by
    apply Nat.le_of_mul_le_mul_right _ (Nat.mul_pos hq.pos hr.pos)
    calc 2 * m * (q * r) = 2 * (q * r * m) := by ring
      _ = 2 * k := by rw [← hm_eq]
      _ ≤ p * q * r := by omega
      _ = p * (q * r) := by ring
  have hnd_q : ¬ q ∣ (p * r).choose (m * r) := by
    apply not_dvd_choose_of_mul q (p * r) (m * r) hq
    have hn' : p * r * q = p * q * r := by ring
    have hk' : m * r * q = k := by rw [hm_eq]; ring
    rwa [hn', hk']
  have hmr_lt : m * r < q ^ 2 := by
    have hmul : 2 * (m * r) + r ≤ 2 * q ^ 2 := by
      calc 2 * (m * r) + r = (2 * m + 1) * r := by ring
        _ ≤ q * (2 * q) := Nat.mul_le_mul (by omega) (by omega)
        _ = 2 * q ^ 2 := by ring
    omega
  have hm_le_c₁ : m ≤ c₁ := by
    have h1 : m ≤ (m * r) / q :=
      le_div_of_mul_le m q (m * r) hq.pos (Nat.mul_le_mul_left m hqr.le)
    have h2 : (m * r) / q ≤ ((p * r) / q) % q :=
      lucas_div_le q (p * r) (m * r) hq hmr_lt hnd_q
    rw [(pr_base_q p q r hpq hqr hgap hsmall).1] at h2
    exact le_trans h1 h2
  have hnd_r : ¬ r ∣ (p * q).choose (m * q) := by
    apply not_dvd_choose_of_mul r (p * q) (m * q) hr
    have hk' : m * q * r = k := by rw [hm_eq]; ring
    rwa [hk']
  let m' := m - 1
  have hm' : m = m' + 1 := by omega
  have hm'δ₂_le : m' * δ₂ ≤ δ * δ := Nat.mul_le_mul (by omega) (by omega)
  let q₀ := q - m' * δ₂
  have hq_q₀ : q = q₀ + m' * δ₂ := by omega
  have hr_q₀ : r = q₀ + m' * δ₂ + δ₂ := by omega
  have hmq_eq : m * q = m' * r + q₀ := by
    rw [hm', hq_q₀, hr_q₀]
    ring
  have hmδ₂_pos : 0 < m * δ₂ := Nat.mul_pos (by omega) (by omega)
  have hr_sum : r = q₀ + m * δ₂ := by
    rw [hm', hr_q₀]
    ring
  have hmq_mod : (m * q) % r = q₀ :=
    (div_mod_of_eq (m * q) r m' q₀ hmq_eq (by omega)).2
  have hle_r : q₀ ≤ δ * δ₂ := by
    have h := lucas_mod_le r (p * q) (m * q) hr hnd_r
    rwa [hmq_mod, pq_mod_r p q r hpq hqr hgap hsmall] at h
  have hmδ₂_bound : m * δ₂ + δ * δ₂ + δ₂ ≤ 2 * (δ * δ) := by
    calc m * δ₂ + δ * δ₂ + δ₂ = (m + δ + 1) * δ₂ := by ring
      _ ≤ (2 * δ) * δ := Nat.mul_le_mul (by omega) (by omega)
      _ = 2 * (δ * δ) := by ring
  omega

private lemma case_pr (p q r k : ℕ) (hp : p.Prime) (hr : r.Prime)
    (hpq : p < q) (hqr : q < r) (hgap : q - p < r - q) (hsmall : 2 * (r - p) ^ 2 < p)
    (hk1 : 1 < k) (hk2 : k ≤ p * q * r / 2)
    (hpC : ¬ p ∣ (p * q * r).choose k) (hrC : ¬ r ∣ (p * q * r).choose k) : False := by
  let δ₁ := q - p
  let δ₂ := r - q
  let δ := r - p
  have hsmall' : 2 * (δ * δ) < p := by dsimp [δ]; rwa [sq] at hsmall
  have hsq_p : (p + δ) ^ 2 < 2 * p ^ 2 := add_sq_lt_two_sq p δ (by omega) hsmall
  have hpk : p ∣ k :=
    Erdos700.prime_dvd_of_not_dvd_choose p (p * q * r) k hp ⟨q * r, by ring⟩ hpC
  have hrk : r ∣ k :=
    Erdos700.prime_dvd_of_not_dvd_choose r (p * q * r) k hr ⟨p * q, by ring⟩ hrC
  have hprk : p * r ∣ k :=
    Nat.Coprime.mul_dvd_of_dvd_of_dvd ((Nat.coprime_primes hp hr).2 (by omega)) hpk hrk
  obtain ⟨m, hm_eq⟩ := hprk
  have hm_pos : 1 ≤ m := by
    rcases Nat.eq_zero_or_pos m with rfl | hpos
    · simp at hm_eq; omega
    · exact hpos
  have h2m_le : 2 * m ≤ q := by
    apply Nat.le_of_mul_le_mul_right _ (Nat.mul_pos hp.pos hr.pos)
    calc 2 * m * (p * r) = 2 * (p * r * m) := by ring
      _ = 2 * k := by rw [← hm_eq]
      _ ≤ p * q * r := by omega
      _ = q * (p * r) := by ring
  have hnd_p : ¬ p ∣ (q * r).choose (m * r) := by
    apply not_dvd_choose_of_mul p (q * r) (m * r) hp
    have hn' : q * r * p = p * q * r := by ring
    have hk' : m * r * p = k := by rw [hm_eq]; ring
    rwa [hn', hk']
  have hmr_lt : m * r < p ^ 2 := by
    have hmul : 2 * (m * r) + r ≤ (p + δ) ^ 2 := by
      calc 2 * (m * r) + r = (2 * m + 1) * r := by ring
        _ ≤ (p + δ) * (p + δ) := Nat.mul_le_mul (by omega) (by omega)
        _ = (p + δ) ^ 2 := by ring
    omega
  have hm_le : m ≤ δ₁ + δ := by
    have h1 : m ≤ (m * r) / p :=
      le_div_of_mul_le m p (m * r) hp.pos (Nat.mul_le_mul_left m (lt_trans hpq hqr).le)
    have h2 : (m * r) / p ≤ ((q * r) / p) % p :=
      lucas_div_le p (q * r) (m * r) hp hmr_lt hnd_p
    rw [qr_div_mod_p p q r hpq hqr hgap hsmall] at h2
    exact le_trans h1 h2
  have hnd_r : ¬ r ∣ (p * q).choose (m * p) := by
    apply not_dvd_choose_of_mul r (p * q) (m * p) hr
    have hk' : m * p * r = k := by rw [hm_eq]; ring
    rwa [hk']
  have hmδ_bound : m * δ + δ * δ₂ ≤ 2 * (δ * δ) := by
    calc m * δ + δ * δ₂ = (m + δ₂) * δ := by ring
      _ ≤ (2 * δ) * δ := Nat.mul_le_mul_right δ (by omega)
      _ = 2 * (δ * δ) := by ring
  let m' := m - 1
  have hm' : m = m' + 1 := by omega
  have hm'δ_le : m' * δ ≤ m * δ := Nat.mul_le_mul_right δ (by omega)
  let p₁ := p - m' * δ
  have hp_p₁ : p = p₁ + m' * δ := by omega
  have hr_p₁ : r = p₁ + m' * δ + δ := by omega
  have hmp_eq : m * p = m' * r + p₁ := by
    rw [hm', hp_p₁, hr_p₁]
    ring
  have hmδ_pos : 0 < m * δ := Nat.mul_pos (by omega) (by omega)
  have hr_sum : r = p₁ + m * δ := by
    rw [hm', hr_p₁]
    ring
  have hmp_mod : (m * p) % r = p₁ :=
    (div_mod_of_eq (m * p) r m' p₁ hmp_eq (by omega)).2
  have hle_r : p₁ ≤ δ * δ₂ := by
    have h := lucas_mod_le r (p * q) (m * p) hr hnd_r
    rwa [hmp_mod, pq_mod_r p q r hpq hqr hgap hsmall] at h
  omega

private lemma case_pq (p q r k : ℕ) (hp : p.Prime) (hq : q.Prime)
    (hpq : p < q) (hqr : q < r) (hgap : q - p < r - q) (hsmall : 2 * (r - p) ^ 2 < p)
    (hk1 : 1 < k) (hk2 : k ≤ p * q * r / 2)
    (hpC : ¬ p ∣ (p * q * r).choose k) (hqC : ¬ q ∣ (p * q * r).choose k) : False := by
  let δ₁ := q - p
  let δ₂ := r - q
  let δ := r - p
  let c₁ := δ₂ - δ₁ - 1
  let c₀ := q - δ₁ * δ₂
  have hsmall' : 2 * (δ * δ) < p := by dsimp [δ]; rwa [sq] at hsmall
  have h6δ : 6 * δ ≤ 2 * (δ * δ) := by
    calc 6 * δ = 2 * 3 * δ := by ring
      _ ≤ 2 * δ * δ := Nat.mul_le_mul_right δ (by omega)
      _ = 2 * (δ * δ) := by ring
  have hsq_p : (p + δ) ^ 2 < 2 * p ^ 2 := add_sq_lt_two_sq p δ (by omega) hsmall
  have hpk : p ∣ k :=
    Erdos700.prime_dvd_of_not_dvd_choose p (p * q * r) k hp ⟨q * r, by ring⟩ hpC
  have hqk : q ∣ k :=
    Erdos700.prime_dvd_of_not_dvd_choose q (p * q * r) k hq ⟨p * r, by ring⟩ hqC
  have hpqk : p * q ∣ k :=
    Nat.Coprime.mul_dvd_of_dvd_of_dvd ((Nat.coprime_primes hp hq).2 (by omega)) hpk hqk
  obtain ⟨m, hm_eq⟩ := hpqk
  have hm_pos : 1 ≤ m := by
    rcases Nat.eq_zero_or_pos m with rfl | hpos
    · simp at hm_eq; omega
    · exact hpos
  have h2m_le : 2 * m ≤ r := by
    apply Nat.le_of_mul_le_mul_right _ (Nat.mul_pos hp.pos hq.pos)
    calc 2 * m * (p * q) = 2 * (p * q * m) := by ring
      _ = 2 * k := by rw [← hm_eq]
      _ ≤ p * q * r := by omega
      _ = r * (p * q) := by ring
  have hnd_p : ¬ p ∣ (q * r).choose (m * q) := by
    apply not_dvd_choose_of_mul p (q * r) (m * q) hp
    have hn' : q * r * p = p * q * r := by ring
    have hk' : m * q * p = k := by rw [hm_eq]; ring
    rwa [hn', hk']
  have hmq_lt : m * q < p ^ 2 := by
    have hmul : 2 * (m * q) + 2 * m ≤ (p + δ) ^ 2 := by
      calc 2 * (m * q) + 2 * m = (2 * m) * (q + 1) := by ring
        _ ≤ (p + δ) * (p + δ) := Nat.mul_le_mul (by omega) (by omega)
        _ = (p + δ) ^ 2 := by ring
    omega
  have hm_le : m ≤ δ₁ + δ := by
    have h1 : m ≤ (m * q) / p :=
      le_div_of_mul_le m p (m * q) hp.pos (Nat.mul_le_mul_left m hpq.le)
    have h2 : (m * q) / p ≤ ((q * r) / p) % p :=
      lucas_div_le p (q * r) (m * q) hp hmq_lt hnd_p
    rw [qr_div_mod_p p q r hpq hqr hgap hsmall] at h2
    exact le_trans h1 h2
  have hnd_q : ¬ q ∣ (p * r).choose (m * p) := by
    apply not_dvd_choose_of_mul q (p * r) (m * p) hq
    have hn' : p * r * q = p * q * r := by ring
    have hk' : m * p * q = k := by rw [hm_eq]; ring
    rwa [hn', hk']
  have hmδ₁_le : m * δ₁ ≤ 2 * (δ * δ) := by
    calc m * δ₁ ≤ (2 * δ) * δ := Nat.mul_le_mul (by omega) (by omega)
      _ = 2 * (δ * δ) := by ring
  have hmp_lt : m * p < q ^ 2 := by
    have hp_pos : 0 < p := hp.pos
    have hmul : m * p + p ≤ q ^ 2 := by
      calc m * p + p = (m + 1) * p := by ring
        _ ≤ q * q := Nat.mul_le_mul (by omega) (by omega)
        _ = q ^ 2 := by ring
    omega
  let m' := m - 1
  have hm' : m = m' + 1 := by omega
  have hm'δ₁_le : m' * δ₁ ≤ m * δ₁ := Nat.mul_le_mul_right δ₁ (by omega)
  let p₂ := p - m' * δ₁
  have hp_p₂ : p = p₂ + m' * δ₁ := by omega
  have hq_p₂ : q = p₂ + m' * δ₁ + δ₁ := by omega
  have hmp_eq : m * p = m' * q + p₂ := by
    rw [hm', hp_p₂, hq_p₂]
    ring
  have hmδ₁_pos : 0 < m * δ₁ := Nat.mul_pos (by omega) (by omega)
  have hq_sum1 : q = p₂ + m * δ₁ := by
    rw [hm', hq_p₂]
    ring
  obtain ⟨hmp_div, hmp_mod⟩ := div_mod_of_eq (m * p) q m' p₂ hmp_eq (by omega)
  have hpr_q := pr_base_q p q r hpq hqr hgap hsmall
  have hdiv_le : m' ≤ c₁ := by
    have h := lucas_div_le q (p * r) (m * p) hq hmp_lt hnd_q
    rwa [hmp_div, hpr_q.1] at h
  have hmod_le : p₂ ≤ c₀ := by
    have h := lucas_mod_le q (p * r) (m * p) hq hnd_q
    rwa [hmp_mod, hpr_q.2] at h
  have hδ₁δ₂_le_p : δ₁ * δ₂ ≤ δ * δ := Nat.mul_le_mul (by omega) (by omega)
  have hq_sum2 : q = c₀ + δ₁ * δ₂ := by omega
  have hδ₂_le_m : δ₂ ≤ m := by
    by_contra hlt
    have h1 : m + 1 ≤ δ₂ := by omega
    have h2 : m * δ₁ + δ₁ ≤ δ₁ * δ₂ := by
      calc m * δ₁ + δ₁ = δ₁ * (m + 1) := by ring
        _ ≤ δ₁ * δ₂ := Nat.mul_le_mul_left δ₁ h1
    omega
  omega

theorem prove_Erdos700_H1 :
    ∀ p q r : ℕ, p.Prime → q.Prime → r.Prime → p < q → q < r → q - p < r - q →
      2 * (r - p) ^ 2 < p → Erdos700.f (p * q * r) ^ 2 > p * q * r := by
  intro p q r hp hq hr hpq hqr hgap hsmall
  have hsmall' : 2 * ((r - p) * (r - p)) < p := by rwa [sq] at hsmall
  have h6δ : 6 * (r - p) ≤ 2 * ((r - p) * (r - p)) := by
    calc 6 * (r - p) = 2 * 3 * (r - p) := by ring
      _ ≤ 2 * (r - p) * (r - p) := Nat.mul_le_mul_right (r - p) (by omega)
      _ = 2 * ((r - p) * (r - p)) := by ring
  have hr_lt_pq : r < p * q := by
    calc r < 2 * p := by omega
      _ ≤ q * p := Nat.mul_le_mul_right p (by omega)
      _ = p * q := mul_comm q p
  have hpq_sq : p * q * r < (p * q) ^ 2 := by
    rw [sq]
    exact Nat.mul_lt_mul_of_pos_left hr_lt_pq (Nat.mul_pos hp.pos hq.pos)
  have hpq_ge : 2 * 2 ≤ p * q := Nat.mul_le_mul hp.two_le (by omega)
  have hn_ge : 4 * 2 ≤ p * q * r := Nat.mul_le_mul hpq_ge (by omega)
  have hne : (Erdos700.fSet (p * q * r)).Nonempty :=
    ⟨_, Erdos700.f_mem (p * q * r) 2 (by omega) (by omega)⟩
  obtain ⟨k, hk1, hk2, hkeq⟩ := Nat.sInf_mem hne
  rw [Erdos700.f_eq, hkeq]
  have finish_of_two : ∀ P₁ P₂ : ℕ, P₁.Prime → P₂.Prime → P₁ < P₂ →
      p ≤ P₁ → q ≤ P₂ → P₁ ∣ p * q * r → P₂ ∣ p * q * r →
      P₁ ∣ (p * q * r).choose k → P₂ ∣ (p * q * r).choose k →
      p * q * r < Nat.gcd (p * q * r) ((p * q * r).choose k) ^ 2 := by
    intro P₁ P₂ hP₁ hP₂ hlt hp₁ hq₂ hn₁ hn₂ hc₁ hc₂
    have hg_pos : 0 < Nat.gcd (p * q * r) ((p * q * r).choose k) :=
      Nat.gcd_pos_of_pos_left _ (by omega)
    have hcop : Nat.Coprime P₁ P₂ := (Nat.coprime_primes hP₁ hP₂).2 (by omega)
    have hdvd : P₁ * P₂ ∣ Nat.gcd (p * q * r) ((p * q * r).choose k) :=
      Nat.Coprime.mul_dvd_of_dvd_of_dvd hcop (Nat.dvd_gcd hn₁ hc₁) (Nat.dvd_gcd hn₂ hc₂)
    have hle1 : p * q ≤ P₁ * P₂ := Nat.mul_le_mul hp₁ hq₂
    have hle2 : P₁ * P₂ ≤ Nat.gcd (p * q * r) ((p * q * r).choose k) :=
      Nat.le_of_dvd hg_pos hdvd
    have hsq : (p * q) ^ 2 ≤ Nat.gcd (p * q * r) ((p * q * r).choose k) ^ 2 :=
      Nat.pow_le_pow_left (le_trans hle1 hle2) 2
    omega
  by_cases hpC : p ∣ (p * q * r).choose k
  · by_cases hqC : q ∣ (p * q * r).choose k
    · exact finish_of_two p q hp hq hpq le_rfl le_rfl
        ⟨q * r, by ring⟩ ⟨p * r, by ring⟩ hpC hqC
    · by_cases hrC : r ∣ (p * q * r).choose k
      · exact finish_of_two p r hp hr (lt_trans hpq hqr) le_rfl hqr.le
          ⟨q * r, by ring⟩ ⟨p * q, by ring⟩ hpC hrC
      · exact False.elim (case_qr p q r k hq hr hpq hqr hgap hsmall hk1 hk2 hqC hrC)
  · by_cases hqC : q ∣ (p * q * r).choose k
    · by_cases hrC : r ∣ (p * q * r).choose k
      · exact finish_of_two q r hq hr hqr hpq.le hqr.le
          ⟨p * r, by ring⟩ ⟨p * q, by ring⟩ hqC hrC
      · exact False.elim (case_pr p q r k hp hr hpq hqr hgap hsmall hk1 hk2 hpC hrC)
    · exact False.elim (case_pq p q r k hp hq hpq hqr hgap hsmall hk1 hk2 hpC hqC)

theorem OMA.solution : OMA.R_Erdos700_erdos_700_parts_ii_R1.H1 :=
  prove_Erdos700_H1
