import FormalConjectures.GreensOpenProblems.«32»

-- Problem: Green's Open Problem 32 — sh20 general
-- Upstream: formal-conjectures FormalConjectures/GreensOpenProblems/32.lean:92 (declaration Green32.green_32.variants.sh20_general)
-- Credit: @kintonc (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

namespace OMA.Green32General

open Polynomial Finset
open scoped Pointwise

private def TotalDegLe {p : ℕ} (D : ℕ) (P : Polynomial (Polynomial (ZMod p))) : Prop :=
  ∀ j : ℕ, P.coeff j = 0 ∨ (P.coeff j).natDegree + j ≤ D

private lemma totalDegLe_zero {p : ℕ} (D : ℕ) :
    TotalDegLe (p := p) D 0 := by
  intro j
  left
  simp

private lemma totalDegLe_add {p : ℕ} {D : ℕ}
    {P Q : Polynomial (Polynomial (ZMod p))}
    (hP : TotalDegLe D P) (hQ : TotalDegLe D Q) :
    TotalDegLe D (P + Q) := by
  intro j
  rw [Polynomial.coeff_add]
  rcases hP j with hPj | hPj <;> rcases hQ j with hQj | hQj
  · left; simp [hPj, hQj]
  · right; simp [hPj, hQj]
  · right; simp [hPj, hQj]
  · right
    have h1 : (P.coeff j + Q.coeff j).natDegree ≤ max (P.coeff j).natDegree (Q.coeff j).natDegree :=
      Polynomial.natDegree_add_le _ _
    omega

private lemma totalDegLe_neg {p : ℕ} {D : ℕ}
    {P : Polynomial (Polynomial (ZMod p))} (hP : TotalDegLe D P) :
    TotalDegLe D (-P) := by
  intro j
  rw [Polynomial.coeff_neg]
  rcases hP j with hj | hj
  · left; simp [hj]
  · right; simpa using hj

private lemma totalDegLe_sub {p : ℕ} {D : ℕ}
    {P Q : Polynomial (Polynomial (ZMod p))}
    (hP : TotalDegLe D P) (hQ : TotalDegLe D Q) :
    TotalDegLe D (P - Q) := by
  rw [sub_eq_add_neg]
  exact totalDegLe_add hP (totalDegLe_neg hQ)

private lemma totalDegLe_C_mul_X_pow {p : ℕ} {D : ℕ}
    (c : Polynomial (ZMod p)) (m : ℕ) (hc : c = 0 ∨ c.natDegree + m ≤ D) :
    TotalDegLe D (C c * X ^ m) := by
  intro j
  rw [Polynomial.coeff_C_mul_X_pow]
  split_ifs with hjm
  · subst hjm
    exact hc
  · left; rfl

private lemma natDeg_sum_mul_le {R : Type*} [CommRing R] (s : Finset (ℕ × ℕ))
    (f g : ℕ → Polynomial R) (D : ℕ)
    (h : ∀ x ∈ s, f x.1 = 0 ∨ g x.2 = 0 ∨ (f x.1).natDegree + (g x.2).natDegree ≤ D) :
    ∑ x ∈ s, f x.1 * g x.2 = 0 ∨ (∑ x ∈ s, f x.1 * g x.2).natDegree ≤ D := by
  by_cases hzero : ∑ x ∈ s, f x.1 * g x.2 = 0
  · exact Or.inl hzero
  · right
    have hle : (∑ x ∈ s, f x.1 * g x.2).natDegree ≤ s.sup (fun x => (f x.1 * g x.2).natDegree) :=
      Polynomial.natDegree_sum_le _ _
    have hsup : s.sup (fun x => (f x.1 * g x.2).natDegree) ≤ D := by
      apply Finset.sup_le
      intro x hx
      rcases h x hx with h1 | h2 | h3
      · simp [h1]
      · simp [h2]
      · exact (Polynomial.natDegree_mul_le).trans h3
    exact hle.trans hsup

private lemma totalDegLe_mul {p : ℕ} {D₁ D₂ : ℕ}
    {P Q : Polynomial (Polynomial (ZMod p))}
    (hP : TotalDegLe D₁ P) (hQ : TotalDegLe D₂ Q) :
    TotalDegLe (D₁ + D₂) (P * Q) := by
  intro j
  rw [Polynomial.coeff_mul]
  have hterm : ∀ x : ℕ × ℕ, x.1 + x.2 = j →
      P.coeff x.1 = 0 ∨ Q.coeff x.2 = 0 ∨ (P.coeff x.1).natDegree + (Q.coeff x.2).natDegree ≤ D₁ + D₂ - j := by
    intro x hxsum
    rcases hP x.1 with h1 | h1
    · exact Or.inl h1
    · rcases hQ x.2 with h2 | h2
      · exact Or.inr (Or.inl h2)
      · exact Or.inr (Or.inr (by omega))
  rcases natDeg_sum_mul_le _ (fun i => P.coeff i) (fun i => Q.coeff i) (D₁ + D₂ - j)
      (fun x hx => hterm x (Finset.HasAntidiagonal.mem_antidiagonal.mp hx)) with h0 | hdeg
  · exact Or.inl h0
  · by_cases hsum0 : ∑ x ∈ Finset.HasAntidiagonal.antidiagonal j, P.coeff x.1 * Q.coeff x.2 = 0
    · exact Or.inl hsum0
    · right
      have hex : ∃ x ∈ Finset.HasAntidiagonal.antidiagonal j, P.coeff x.1 ≠ 0 ∧ Q.coeff x.2 ≠ 0 := by
        by_contra hall
        push Not at hall
        apply hsum0
        apply Finset.sum_eq_zero
        intro x hx
        by_cases h1 : P.coeff x.1 = 0
        · simp [h1]
        · simp [hall x hx h1]
      rcases hex with ⟨x, hx, h1, h2⟩
      have hxsum : x.1 + x.2 = j := Finset.HasAntidiagonal.mem_antidiagonal.mp hx
      have h1' := (hP x.1).resolve_left h1
      have h2' := (hQ x.2).resolve_left h2
      omega

private lemma totalDegLe_X_pow_sub_X {p : ℕ} (hp : 1 < p) :
    TotalDegLe (p := p) p (X ^ p - X) := by
  intro j
  rw [Polynomial.coeff_sub, Polynomial.coeff_X_pow, Polynomial.coeff_X]
  split_ifs with h1 h2 h2
  · left; simp [h1, h2]
  · right; simp; omega
  · right; simp; omega
  · left; simp

private lemma div_X_pow_sub_X {p : ℕ} [Fact p.Prime] (hp : 1 < p) (D : ℕ) (hpD : p ≤ D) :
    ∀ n : ℕ, ∀ P : Polynomial (Polynomial (ZMod p)),
      P.natDegree ≤ n → TotalDegLe D P →
      ∃ U R : Polynomial (Polynomial (ZMod p)),
        P = (X ^ p - X) * U + R ∧ R.natDegree < p ∧ TotalDegLe (D - p) U ∧ TotalDegLe D R := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro P hPn hPD
    by_cases hPp : P.natDegree < p
    · refine ⟨0, P, by simp, hPp, totalDegLe_zero _, hPD⟩
    · have hp_le : p ≤ P.natDegree := Nat.le_of_not_lt hPp
      have hP_ne : P ≠ 0 := by
        intro h0
        subst h0
        simp at hp_le
        omega
      set m := P.natDegree - p
      set c := P.leadingCoeff
      have hc_ne : c ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hP_ne
      have hc_deg : c.natDegree + m ≤ D - p := by
        have hlead := (hPD P.natDegree).resolve_left (by simpa [c] using hc_ne)
        simp only [c, Polynomial.leadingCoeff] at hlead ⊢
        omega
      set Q : Polynomial (Polynomial (ZMod p)) := C c * X ^ m
      have hQ_deg : TotalDegLe (D - p) Q := totalDegLe_C_mul_X_pow c m (Or.inr hc_deg)
      have hPQ_deg : TotalDegLe D ((X ^ p - X) * Q) := by
        have h := totalDegLe_mul (totalDegLe_X_pow_sub_X (p := p) hp) hQ_deg
        rwa [Nat.add_sub_cancel' hpD] at h
      set P' := P - (X ^ p - X) * Q
      have hP'_deg : TotalDegLe D P' := totalDegLe_sub hPD hPQ_deg
      have hP'_natDeg : P'.natDegree < P.natDegree := by
        have hdeg_XpX : (X ^ p - X : Polynomial (Polynomial (ZMod p))).natDegree = p := by
          rw [Polynomial.natDegree_sub_eq_left_of_natDegree_lt]
          · exact Polynomial.natDegree_X_pow p
          · rw [Polynomial.natDegree_X, Polynomial.natDegree_X_pow]
            exact hp
        have hmonic : ((X ^ p - X : Polynomial (Polynomial (ZMod p)))).Monic := by
          rw [Polynomial.Monic, Polynomial.leadingCoeff, hdeg_XpX, Polynomial.coeff_sub,
            Polynomial.coeff_X_pow, Polynomial.coeff_X, if_pos rfl, if_neg (by omega), sub_zero]
        have hlead_mul : ((X ^ p - X) * Q).leadingCoeff = c := by
          rw [Polynomial.leadingCoeff_mul, hmonic.leadingCoeff, one_mul]
          exact Polynomial.leadingCoeff_C_mul_X_pow c m
        have hQ_ne : Q ≠ 0 := by
          rw [← Polynomial.leadingCoeff_ne_zero, Polynomial.leadingCoeff_C_mul_X_pow]
          exact hc_ne
        have hnat_mul : ((X ^ p - X) * Q).natDegree = P.natDegree := by
          have hQ_deg_eq : Q.natDegree = m := by simp [Q, hc_ne]
          rw [Polynomial.natDegree_mul hmonic.ne_zero hQ_ne, hdeg_XpX, hQ_deg_eq]
          omega
        have hcoeff_ge : ∀ j, P.natDegree ≤ j → P'.coeff j = 0 := by
          intro j hj
          rw [Polynomial.coeff_sub]
          rcases eq_or_lt_of_le hj with rfl | hgt
          · have h1 : P.coeff P.natDegree = c := rfl
            have h2 : ((X ^ p - X) * Q).coeff P.natDegree = c := by
              rw [← hnat_mul]
              exact hlead_mul
            rw [h1, h2, sub_self]
          · rw [Polynomial.coeff_eq_zero_of_natDegree_lt hgt,
              Polynomial.coeff_eq_zero_of_natDegree_lt (hnat_mul ▸ hgt), sub_zero]
        by_cases hP'0 : P' = 0
        · rw [hP'0, Polynomial.natDegree_zero]
          omega
        · by_contra hge
          have hle : P.natDegree ≤ P'.natDegree := Nat.le_of_not_lt hge
          exact Polynomial.leadingCoeff_ne_zero.mpr hP'0 (hcoeff_ge P'.natDegree hle)
      have hP'_lt_n : P'.natDegree < n := lt_of_lt_of_le hP'_natDeg hPn
      rcases ih P'.natDegree hP'_lt_n P' le_rfl hP'_deg with ⟨U', R, hU'R, hRp, hU'deg, hRdeg⟩
      refine ⟨Q + U', R, ?_, hRp, totalDegLe_add hQ_deg hU'deg, hRdeg⟩
      rw [mul_add, add_assoc, ← hU'R]
      simp [P']

private noncomputable def topHom {p : ℕ} (D : ℕ) (P : Polynomial (Polynomial (ZMod p))) : Polynomial (ZMod p) :=
  ∑ j ∈ Finset.range (D + 1), C ((P.coeff j).coeff (D - j)) * X ^ j

private lemma topHom_add {p : ℕ} (D : ℕ) (P Q : Polynomial (Polynomial (ZMod p))) :
    topHom D (P + Q) = topHom D P + topHom D Q := by
  simp only [topHom, Polynomial.coeff_add, Polynomial.C_add, add_mul, Finset.sum_add_distrib]

private lemma topHom_natDegree_le {p : ℕ} (D : ℕ) (P : Polynomial (Polynomial (ZMod p))) :
    (topHom D P).natDegree ≤ D := by
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro j hj
  rw [Finset.mem_range] at hj
  have h1 : (C ((P.coeff j).coeff (D - j))).natDegree = 0 := Polynomial.natDegree_C _
  have h2 : (X ^ j : Polynomial (ZMod p)).natDegree ≤ j := Polynomial.natDegree_X_pow_le j
  have h3 : (C ((P.coeff j).coeff (D - j)) * X ^ j).natDegree ≤
      (C ((P.coeff j).coeff (D - j))).natDegree + (X ^ j).natDegree := Polynomial.natDegree_mul_le
  omega

private lemma coeff_topHom {p : ℕ} (D : ℕ) (P : Polynomial (Polynomial (ZMod p))) (j : ℕ) :
    (topHom D P).coeff j = if j ≤ D then (P.coeff j).coeff (D - j) else 0 := by
  simp only [topHom, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul_X_pow]
  split_ifs with hj
  · rw [Finset.sum_eq_single j]
    · simp
    · intro k _ hkj
      simp [hkj.symm]
    · intro hnot
      exfalso
      apply hnot
      exact Finset.mem_range.mpr (Nat.lt_succ_of_le hj)
  · apply Finset.sum_eq_zero
    intro k hk
    rw [Finset.mem_range] at hk
    rw [if_neg (by omega)]

private lemma topHom_mul {p : ℕ} {D₁ D₂ : ℕ}
    {P Q : Polynomial (Polynomial (ZMod p))}
    (hP : TotalDegLe D₁ P) (hQ : TotalDegLe D₂ Q) :
    topHom (D₁ + D₂) (P * Q) = topHom D₁ P * topHom D₂ Q := by
  ext j
  rw [coeff_topHom, Polynomial.coeff_mul]
  split_ifs with hj
  · rw [Polynomial.coeff_mul, Polynomial.finsetSum_coeff]
    apply Finset.sum_congr rfl
    intro x hx
    have hxsum : x.1 + x.2 = j := Finset.HasAntidiagonal.mem_antidiagonal.mp hx
    rw [Polynomial.coeff_mul]
    by_cases hx1 : x.1 ≤ D₁
    · by_cases hx2 : x.2 ≤ D₂
      · rw [coeff_topHom, coeff_topHom, if_pos hx1, if_pos hx2]
        trans (P.coeff x.1).coeff (D₁ - x.1) * (Q.coeff x.2).coeff (D₂ - x.2)
        · apply Finset.sum_eq_single (D₁ - x.1, D₂ - x.2)
          · intro y hy hy_ne
            have hysum : y.1 + y.2 = D₁ + D₂ - j := Finset.HasAntidiagonal.mem_antidiagonal.mp hy
            by_cases hy1 : D₁ - x.1 < y.1
            · have hP0 : (P.coeff x.1).coeff y.1 = 0 := by
                rcases hP x.1 with h0 | hdeg
                · simp [h0]
                · apply Polynomial.coeff_eq_zero_of_natDegree_lt
                  omega
              simp [hP0]
            · have hy2 : D₂ - x.2 < y.2 := by
                by_contra hle
                have : y = (D₁ - x.1, D₂ - x.2) := Prod.ext (by omega) (by omega)
                exact hy_ne this
              have hQ0 : (Q.coeff x.2).coeff y.2 = 0 := by
                rcases hQ x.2 with h0 | hdeg
                · simp [h0]
                · apply Polynomial.coeff_eq_zero_of_natDegree_lt
                  omega
              simp [hQ0]
          · intro hnot
            exfalso
            apply hnot
            rw [Finset.HasAntidiagonal.mem_antidiagonal]
            omega
        · simp
      · simp only [coeff_topHom, if_neg hx2, mul_zero]
        apply Finset.sum_eq_zero
        intro y _
        have hQ0 : (Q.coeff x.2).coeff y.2 = 0 := by
          rcases hQ x.2 with h0 | hdeg
          · simp [h0]
          · exfalso; omega
        simp [hQ0]
    · simp only [coeff_topHom, if_neg hx1, zero_mul]
      apply Finset.sum_eq_zero
      intro y _
      have hP0 : (P.coeff x.1).coeff y.1 = 0 := by
        rcases hP x.1 with h0 | hdeg
        · simp [h0]
        · exfalso; omega
      simp [hP0]
  · symm
    rw [Polynomial.coeff_mul]
    apply Finset.sum_eq_zero
    intro x hx
    have hxsum : x.1 + x.2 = j := Finset.HasAntidiagonal.mem_antidiagonal.mp hx
    by_cases hx1 : x.1 ≤ D₁
    · have hx2 : ¬ (x.2 ≤ D₂) := by omega
      simp only [coeff_topHom, if_neg hx2, mul_zero]
    · simp only [coeff_topHom, if_neg hx1, zero_mul]

private lemma topHom_C_X {p : ℕ} :
    topHom (p := p) 1 (C Polynomial.X) = 1 := by
  ext j
  rw [coeff_topHom]
  rcases eq_or_ne j 0 with rfl | hj0
  · simp
  · split_ifs with hj
    · have hj1 : j = 1 := by omega
      subst hj1
      simp [Polynomial.coeff_one]
    · simp [Polynomial.coeff_one, hj0]

private lemma topHom_lin {p : ℕ} (a b : ZMod p) :
    topHom 1 (Polynomial.X + C (Polynomial.X * C a + C b)) = Polynomial.X + C a := by
  ext j
  rw [coeff_topHom]
  rcases Nat.lt_trichotomy j 1 with hj0 | rfl | hj1
  · have : j = 0 := by omega
    subst this
    simp [Polynomial.coeff_add, Polynomial.coeff_X, Polynomial.coeff_C]
  · simp [Polynomial.coeff_add, Polynomial.coeff_X]
  · rw [if_neg (by omega)]
    simp [Polynomial.coeff_add, Polynomial.coeff_X, Polynomial.coeff_C,
      show 1 ≠ j by omega, show j ≠ 0 by omega]

private lemma topHom_X_pow_sub_X {p : ℕ} (hp : 1 < p) :
    topHom (p := p) p (X ^ p - X) = X ^ p := by
  ext j
  rw [coeff_topHom]
  split_ifs with hj
  · rw [Polynomial.coeff_sub, Polynomial.coeff_X_pow, Polynomial.coeff_X]
    rcases eq_or_ne j p with rfl | hjp
    · rw [if_pos rfl, if_neg hp.ne'.symm]
      simp [Polynomial.coeff_X_pow]
    · rcases eq_or_ne j 1 with rfl | hj1
      · rw [if_neg hjp, if_pos rfl]
        simp [Polynomial.coeff_one, show p - 1 ≠ 0 by omega, Polynomial.coeff_X_pow, hjp]
      · rw [if_neg hjp, if_neg hj1.symm]
        simp [Polynomial.coeff_X_pow, hjp]
  · rw [Polynomial.coeff_X_pow, if_neg (by omega)]

private lemma topHom_C_X_pow_sub_X {p : ℕ} (hp : 1 < p) :
    topHom (p := p) p (C (X ^ p - X : Polynomial (ZMod p))) = 1 := by
  ext j
  rw [coeff_topHom]
  split_ifs with hj
  · rcases eq_or_ne j 0 with rfl | hj0
    · rw [Polynomial.coeff_C, if_pos rfl, Nat.sub_zero, Polynomial.coeff_sub,
        Polynomial.coeff_X_pow, Polynomial.coeff_X, if_pos rfl, if_neg hp.ne'.symm, sub_zero,
        Polynomial.coeff_one, if_pos rfl]
    · rw [Polynomial.coeff_C, if_neg hj0, Polynomial.coeff_zero, Polynomial.coeff_one, if_neg hj0]
  · simp [Polynomial.coeff_one, show j ≠ 0 by omega]

private lemma deriv_eq_zero_natDeg_lt {p : ℕ} (hp : p.Prime)
    {q : Polynomial (ZMod p)} (hq_deg : q.natDegree < p) (hq_deriv : q.derivative = 0) :
    q.natDegree = 0 := by
  haveI : Fact p.Prime := ⟨hp⟩
  by_contra hpos
  have h1 : 1 ≤ q.natDegree := Nat.pos_of_ne_zero hpos
  have hq_ne : q ≠ 0 := by
    intro h0
    subst h0
    simp at hpos
  have hcoeff : q.derivative.coeff (q.natDegree - 1) = (q.natDegree : ZMod p) * q.leadingCoeff := by
    rw [Polynomial.coeff_derivative, Nat.sub_add_cancel h1, ← Polynomial.leadingCoeff,
      Nat.cast_sub h1, Nat.cast_one, sub_add_cancel, mul_comm]
  rw [hq_deriv, Polynomial.coeff_zero] at hcoeff
  have hnat_ne : (q.natDegree : ZMod p) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]
    exact Nat.not_dvd_of_pos_of_lt h1 hq_deg
  have hlead_ne : q.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hq_ne
  exact mul_ne_zero hnat_ne hlead_ne hcoeff.symm

private lemma totalDegLe_lin {p : ℕ} (a b : ZMod p) :
    TotalDegLe 1 (Polynomial.X + C (Polynomial.X * C a + C b)) := by
  intro j
  rcases Nat.lt_trichotomy j 1 with hj0 | rfl | hj1
  · have : j = 0 := by omega
    subst this
    right
    simp only [Polynomial.coeff_add, Polynomial.coeff_X_zero, zero_add,
      Polynomial.coeff_C_zero, add_zero]
    have h1 : (Polynomial.X * C a).natDegree ≤ 1 := by
      have hmul : (Polynomial.X * C a).natDegree ≤ Polynomial.X.natDegree + (C a).natDegree :=
        Polynomial.natDegree_mul_le
      have hX : (Polynomial.X : Polynomial (ZMod p)).natDegree ≤ 1 := Polynomial.natDegree_X_le
      have hC : (C a).natDegree = 0 := Polynomial.natDegree_C a
      omega
    have h2 : (C b).natDegree = 0 := Polynomial.natDegree_C b
    have h3 : (Polynomial.X * C a + C b).natDegree ≤ max (Polynomial.X * C a).natDegree (C b).natDegree :=
      Polynomial.natDegree_add_le _ _
    omega
  · right
    have hcoeff1 : (Polynomial.X + C (Polynomial.X * C a + C b)).coeff 1 = 1 := by simp
    rw [hcoeff1, Polynomial.natDegree_one]
  · left
    simp [Polynomial.coeff_add, Polynomial.coeff_X, Polynomial.coeff_C,
      show 1 ≠ j by omega, show j ≠ 0 by omega]

theorem sh20_general_aux :
    ∀ (p : ℕ), p.Prime →
      ∀ A : Finset (ZMod p), 1 < A.card →
      ∃ c : (ZMod p)ˣ, Green32.HasGap (c • A) ⌊2 * (p : ℝ) / A.card - 2⌋₊ := by
  intro p hp A hA
  haveI : Fact p.Prime := ⟨hp⟩
  set L := ⌊2 * (p : ℝ) / A.card - 2⌋₊
  by_cases hL0 : L = 0
  · rw [hL0]
    exact ⟨1, Green32.hasGap_zero _⟩
  have hL_pos : 0 < L := Nat.pos_of_ne_zero hL0
  have hA_le_p : A.card ≤ p := by
    calc A.card ≤ (Finset.univ : Finset (ZMod p)).card := Finset.card_le_univ A
      _ = p := ZMod.card p
  by_cases hA_eq_p : A.card = p
  · exfalso
    apply hL0
    simp only [L, hA_eq_p]
    have hp_pos : (0 : ℝ) < p := Nat.cast_pos.mpr hp.pos
    have : 2 * (p : ℝ) / (p : ℝ) - 2 = 0 := by field_simp; ring
    rw [this, Nat.floor_zero]
  have hAp : A.card < p := lt_of_le_of_ne hA_le_p hA_eq_p
  by_cases hA2 : A.card = 2
  · rcases Finset.card_eq_two.mp hA2 with ⟨a₁, a₂, hne, rfl⟩
    have hsub_ne : a₂ - a₁ ≠ 0 := sub_ne_zero.mpr hne.symm
    let c : (ZMod p)ˣ := Units.mk0 (a₂ - a₁)⁻¹ (inv_ne_zero hsub_ne)
    refine ⟨c, (c : ZMod p) * a₁ + 2, fun i hi => ?_⟩
    have hL_le : L ≤ p - 2 := by
      have hp2 : 2 ≤ p := hp.two_le
      have hreal : (2 * (p : ℝ) / (({a₁, a₂} : Finset (ZMod p)).card : ℝ) - 2) = ((p - 2 : ℕ) : ℝ) := by
        rw [hA2]
        push_cast [hp2]
        ring
      simp only [L, hreal, Nat.floor_natCast]
      exact le_rfl
    intro hmem
    rw [Finset.mem_smul_finset] at hmem
    rcases hmem with ⟨a, ha, ha_eq⟩
    rw [Units.smul_def, smul_eq_mul] at ha_eq
    have hca₂ : (c : ZMod p) * a₂ = (c : ZMod p) * a₁ + 1 := by
      have hcval : (c : ZMod p) = (a₂ - a₁)⁻¹ := rfl
      rw [hcval]
      have : (a₂ - a₁)⁻¹ * a₂ - (a₂ - a₁)⁻¹ * a₁ = 1 := by
        rw [← mul_sub, inv_mul_cancel₀ hsub_ne]
      exact eq_add_of_sub_eq' this
    rw [Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with rfl | rfl
    · have h0 : ((i + 2 : ℕ) : ZMod p) = 0 := by
        push_cast
        linear_combination -ha_eq
      rw [ZMod.natCast_eq_zero_iff] at h0
      exact absurd h0 (Nat.not_dvd_of_pos_of_lt (by omega) (by omega))
    · have h0 : ((i + 1 : ℕ) : ZMod p) = 0 := by
        push_cast
        linear_combination -ha_eq + hca₂
      rw [ZMod.natCast_eq_zero_iff] at h0
      exact absurd h0 (Nat.not_dvd_of_pos_of_lt (by omega) (by omega))
  -- Remaining main case: 3 ≤ A.card < p
  have hA3 : 3 ≤ A.card := by omega
  have hp5 : 5 ≤ p := by
    have : 4 ≤ p := by omega
    by_contra hlt
    have hp4 : p = 4 := by omega
    subst hp4
    exact absurd hp (by decide)
  have hLp : L < p := by
    have hfloor : (L : ℝ) ≤ 2 * (p : ℝ) / A.card - 2 := by
      apply Nat.floor_le
      have : (A.card : ℝ) < p := by exact_mod_cast hAp
      have : (0 : ℝ) < A.card := by positivity
      rw [sub_nonneg, le_div_iff₀ this]
      linarith
    have hA_ge3 : (3 : ℝ) ≤ A.card := by exact_mod_cast hA3
    have hdiv : 2 * (p : ℝ) / A.card ≤ 2 * (p : ℝ) / 3 :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) hA_ge3
    have hlt_real : (L : ℝ) < p := by linarith
    exact_mod_cast hlt_real
  have h_not_dvd : ¬ (A.card ∣ 2 * p) := by
    intro hdvd
    rcases (Nat.dvd_mul.mp hdvd) with ⟨d₁, d₂, hd₁, hd₂, heq⟩
    rcases hp.eq_one_or_self_of_dvd d₂ hd₂ with rfl | rfl
    · have : d₁ ≤ 2 := Nat.le_of_dvd (by omega) hd₁
      omega
    · have : 1 ≤ d₁ := Nat.pos_of_ne_zero (by rintro rfl; omega)
      nlinarith
  have h_ineq : A.card * L + A.card + 1 < 2 * p := by
    set q := (2 * p) / A.card
    set r := (2 * p) % A.card
    have hqr : A.card * q + r = 2 * p := Nat.div_add_mod (2 * p) A.card
    have hr_pos : 1 ≤ r := Nat.pos_of_ne_zero (fun hr0 => h_not_dvd (Nat.dvd_of_mod_eq_zero hr0))
    have hr_lt : r < A.card := Nat.mod_lt _ (by omega)
    have hq_ge2 : 2 ≤ q := by nlinarith
    have hfloor : (L : ℝ) ≤ 2 * (p : ℝ) / A.card - 2 := by
      apply Nat.floor_le
      have : (A.card : ℝ) < p := by exact_mod_cast hAp
      have : (0 : ℝ) < A.card := by positivity
      rw [sub_nonneg, le_div_iff₀ this]
      linarith
    have h2p_real : 2 * (p : ℝ) = (A.card : ℝ) * q + r := by exact_mod_cast hqr.symm
    have hA_pos_r : (0 : ℝ) < A.card := by positivity
    have hr_lt_r : (r : ℝ) < A.card := by exact_mod_cast hr_lt
    have hdiv_lt : 2 * (p : ℝ) / A.card < (q : ℝ) + 1 := by
      rw [h2p_real, add_div, mul_div_cancel_left₀ _ hA_pos_r.ne']
      have : (r : ℝ) / A.card < 1 := (div_lt_one hA_pos_r).mpr hr_lt_r
      linarith
    have hL_lt_q1 : (L : ℝ) < ((q - 1 : ℕ) : ℝ) := by
      have : ((q - 1 : ℕ) : ℝ) = (q : ℝ) - 1 := by
        rw [Nat.cast_sub (by omega), Nat.cast_one]
      linarith
    have hL_lt_q1_nat : L < q - 1 := by exact_mod_cast hL_lt_q1
    have hL2 : L + 2 ≤ q := by omega
    nlinarith
  by_contra h_no_gap
  push Not at h_no_gap
  let B : Finset (ZMod p) := (Finset.range L).image (Nat.cast : ℕ → ZMod p)
  have hB_card : B.card = L := by
    rw [Finset.card_image_of_injOn]
    · exact Finset.card_range L
    · intro i hi j hj hij
      rw [Finset.mem_coe, Finset.mem_range] at hi hj
      have hi' : (i : ZMod p).val = i := ZMod.val_cast_of_lt (lt_trans hi hLp)
      have hj' : (j : ZMod p).val = j := ZMod.val_cast_of_lt (lt_trans hj hLp)
      rw [← hi', ← hj', hij]
  have h_vanish : ∀ d t : ZMod p, d * ∏ a ∈ A, ∏ b ∈ B, (t + d * a + b) = 0 := by
    intro d t
    by_cases hd : d = 0
    · simp [hd]
    · let c : (ZMod p)ˣ := Units.mk0 d hd
      have hng := h_no_gap c
      simp only [Green32.HasGap, not_exists, not_forall, not_not] at hng
      rcases hng (-t - ((L - 1 : ℕ) : ZMod p)) with ⟨i, hi, hmem⟩
      rw [Finset.mem_smul_finset] at hmem
      rcases hmem with ⟨a, ha, ha_eq⟩
      have hca : d * a = -t - ((L - 1 : ℕ) : ZMod p) + (i : ZMod p) := by
        simpa [c, smul_eq_mul] using ha_eq
      set j := L - 1 - i
      have hj_lt : j < L := by omega
      have hj_mem : (j : ZMod p) ∈ B := Finset.mem_image.mpr ⟨j, Finset.mem_range.mpr hj_lt, rfl⟩
      have hj_cast : ((j : ℕ) : ZMod p) = ((L - 1 : ℕ) : ZMod p) - (i : ZMod p) := by
        have hi_le : i ≤ L - 1 := by omega
        rw [Nat.cast_sub hi_le]
      have hzero : t + d * a + (j : ZMod p) = 0 := by
        rw [hca, hj_cast]
        ring
      have hprod_zero : (∏ b ∈ B, (t + d * a + b)) = 0 :=
        Finset.prod_eq_zero hj_mem hzero
      have hprod2_zero : (∏ a ∈ A, ∏ b ∈ B, (t + d * a + b)) = 0 :=
        Finset.prod_eq_zero ha hprod_zero
      rw [hprod2_zero, mul_zero]
  by_cases hAL_lt_p : A.card * L < p
  · let P : Polynomial (ZMod p) := ∏ a ∈ A, ∏ b ∈ B, (X + C (a + b))
    have hP_monic : P.Monic := by
      apply Polynomial.monic_prod_of_monic
      intro a _
      apply Polynomial.monic_prod_of_monic
      intro b _
      exact Polynomial.monic_X_add_C _
    have hP_deg : P.natDegree = A.card * L := by
      rw [Polynomial.natDegree_prod_of_monic]
      · simp only [Polynomial.natDegree_prod_of_monic _ _ (fun b _ => Polynomial.monic_X_add_C _),
          Polynomial.natDegree_X_add_C, Finset.sum_const, smul_eq_mul, mul_one, hB_card]
      · intro a _
        exact Polynomial.monic_prod_of_monic _ _ (fun b _ => Polynomial.monic_X_add_C _)
    have hP_roots : ∀ t : ZMod p, P.IsRoot t := by
      intro t
      rw [Polynomial.IsRoot, Polynomial.eval_prod]
      have h1 := h_vanish 1 t
      simp only [one_mul] at h1
      simpa [P, Polynomial.eval_prod, add_assoc] using h1
    have hcard_le : p ≤ P.roots.card := by
      calc p = (Finset.univ : Finset (ZMod p)).card := (ZMod.card p).symm
        _ ≤ P.roots.toFinset.card := Finset.card_le_card (fun t _ =>
            Multiset.mem_toFinset.mpr ((Polynomial.mem_roots hP_monic.ne_zero).mpr (hP_roots t)))
        _ ≤ P.roots.card := Multiset.toFinset_card_le _
    have hroots_deg : P.roots.card ≤ P.natDegree := Polynomial.card_roots' P
    omega
  have hp_le_AL : p ≤ A.card * L := Nat.le_of_not_lt hAL_lt_p
  set k := A.card * L - p + 1
  have hk_pos : 1 ≤ k := by omega
  have hk_lt_p : k < p := by omega
  have hD_eq : A.card * L + 1 = p + k := by omega
  let W : Polynomial (Polynomial (ZMod p)) :=
    C Polynomial.X * ∏ a ∈ A, ∏ b ∈ B, (Polynomial.X + C (Polynomial.X * C a + C b))
  have hCX_deg : TotalDegLe 1 (C (Polynomial.X : Polynomial (ZMod p))) := by
    intro j
    rcases eq_or_ne j 0 with rfl | hj
    · right; simp
    · left; simp [Polynomial.coeff_C, hj]
  have h_inner_top : ∀ a : ZMod p,
      TotalDegLe L (∏ b ∈ B, (Polynomial.X + C (Polynomial.X * C a + C b))) ∧
      topHom L (∏ b ∈ B, (Polynomial.X + C (Polynomial.X * C a + C b))) = (X + C a) ^ L := by
    intro a
    rw [← hB_card]
    induction B using Finset.induction with
    | empty =>
      simp only [Finset.prod_empty, Finset.card_empty, pow_zero]
      refine ⟨?_, ?_⟩
      · intro j
        rcases eq_or_ne j 0 with rfl | hj
        · right; simp
        · left; simp [Polynomial.coeff_one, hj]
      · ext j
        rw [coeff_topHom]
        rcases eq_or_ne j 0 with rfl | hj
        · simp
        · split_ifs <;> simp [Polynomial.coeff_one, hj]
    | insert b s hbs ih =>
      rw [Finset.prod_insert hbs, Finset.card_insert_of_notMem hbs, pow_succ', add_comm s.card 1]
      refine ⟨totalDegLe_mul (totalDegLe_lin a b) ih.1, ?_⟩
      rw [topHom_mul (totalDegLe_lin a b) ih.1, topHom_lin, ih.2]
  have h_outer_top : ∀ s : Finset (ZMod p),
      TotalDegLe (s.card * L) (∏ a ∈ s, ∏ b ∈ B, (Polynomial.X + C (Polynomial.X * C a + C b))) ∧
      topHom (s.card * L) (∏ a ∈ s, ∏ b ∈ B, (Polynomial.X + C (Polynomial.X * C a + C b))) =
        ∏ a ∈ s, (X + C a) ^ L := by
    intro s
    induction s using Finset.induction with
    | empty =>
      simp only [Finset.prod_empty, Finset.card_empty, zero_mul]
      refine ⟨?_, ?_⟩
      · intro j
        rcases eq_or_ne j 0 with rfl | hj
        · right; simp
        · left; simp [Polynomial.coeff_one, hj]
      · ext j
        rw [coeff_topHom]
        rcases eq_or_ne j 0 with rfl | hj
        · simp
        · split_ifs <;> simp [Polynomial.coeff_one, hj]
    | insert a s has ih =>
      rw [Finset.prod_insert has, Finset.card_insert_of_notMem has, add_mul, one_mul,
        add_comm (s.card * L) L, Finset.prod_insert has]
      refine ⟨totalDegLe_mul (h_inner_top a).1 ih.1, ?_⟩
      rw [topHom_mul (h_inner_top a).1 ih.1, (h_inner_top a).2, ih.2]
  have hprod_deg : TotalDegLe (A.card * L) (∏ a ∈ A, ∏ b ∈ B, (Polynomial.X + C (Polynomial.X * C a + C b))) :=
    (h_outer_top A).1
  have hW_deg : TotalDegLe (A.card * L + 1) W := by
    rw [add_comm (A.card * L) 1]
    exact totalDegLe_mul hCX_deg hprod_deg
  rcases div_X_pow_sub_X hp.one_lt (A.card * L + 1) (by omega) W.natDegree W le_rfl hW_deg with
    ⟨U, R, hW_eq, hR_deg, hU_deg, _⟩
  rw [show A.card * L + 1 - p = k from by omega] at hU_deg
  have hR_coeff_vanish : ∀ j : ℕ, ∀ d₀ : ZMod p, (R.coeff j).eval d₀ = 0 := by
    intro j d₀
    let φ : Polynomial (Polynomial (ZMod p)) →+* Polynomial (ZMod p) :=
      Polynomial.mapRingHom (Polynomial.evalRingHom d₀)
    have hφR_eval : ∀ t₀ : ZMod p, (φ R).eval t₀ = 0 := by
      intro t₀
      have hφW : φ W = C d₀ * ∏ a ∈ A, ∏ b ∈ B, (X + C (d₀ * a + b)) := by
        simp only [W, φ, Polynomial.coe_mapRingHom, Polynomial.map_mul, Polynomial.map_prod,
          Polynomial.map_add, Polynomial.map_C, Polynomial.coe_evalRingHom, Polynomial.eval_add,
          Polynomial.eval_X, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.map_X, add_assoc]
      have hW_t₀ : (φ W).eval t₀ = 0 := by
        rw [hφW]
        simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_prod,
          Polynomial.eval_add, Polynomial.eval_X, ← add_assoc]
        exact h_vanish d₀ t₀
      have hφW_eq : φ W = (X ^ p - X) * φ U + φ R := by
        have := congrArg φ hW_eq
        simpa only [φ, Polynomial.coe_mapRingHom, Polynomial.map_add, Polynomial.map_mul,
          Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X] using this
      have hXpX : (X ^ p - X : Polynomial (ZMod p)).eval t₀ = 0 := by
        simp [ZMod.pow_card t₀]
      rw [hφW_eq, Polynomial.eval_add, Polynomial.eval_mul, hXpX, zero_mul, zero_add] at hW_t₀
      exact hW_t₀
    have hφR_zero : φ R = 0 := by
      by_contra hne
      have hdeg_lt : (φ R).natDegree < p := lt_of_le_of_lt Polynomial.natDegree_map_le hR_deg
      have hcard_le : p ≤ (φ R).roots.card := by
        calc p = (Finset.univ : Finset (ZMod p)).card := (ZMod.card p).symm
          _ ≤ (φ R).roots.toFinset.card := Finset.card_le_card (fun t _ =>
              Multiset.mem_toFinset.mpr ((Polynomial.mem_roots hne).mpr (hφR_eval t)))
          _ ≤ (φ R).roots.card := Multiset.toFinset_card_le _
      have hroots : (φ R).roots.card ≤ (φ R).natDegree := Polynomial.card_roots' (φ R)
      omega
    have hcoeff : (φ R).coeff j = (R.coeff j).eval d₀ := by
      simp [φ]
    rw [← hcoeff, hφR_zero, Polynomial.coeff_zero]
  have hXpX_deg : (X ^ p - X : Polynomial (ZMod p)).natDegree = p := by
    rw [Polynomial.natDegree_sub_eq_left_of_natDegree_lt]
    · exact Polynomial.natDegree_X_pow p
    · rw [Polynomial.natDegree_X, Polynomial.natDegree_X_pow]
      exact hp.one_lt
  have hXpX_monic : (X ^ p - X : Polynomial (ZMod p)).Monic := by
    rw [Polynomial.Monic, Polynomial.leadingCoeff, hXpX_deg, Polynomial.coeff_sub,
      Polynomial.coeff_X_pow, Polynomial.coeff_X, if_pos rfl, if_neg hp.one_lt.ne, sub_zero]
  have hR_dvd : ∀ j : ℕ, R.coeff j = (X ^ p - X) * (R.coeff j /ₘ (X ^ p - X)) := by
    intro j
    set q := R.coeff j
    have hmod_eval : ∀ d₀ : ZMod p, (q %ₘ (X ^ p - X)).eval d₀ = 0 := by
      intro d₀
      have hdiv := Polynomial.modByMonic_add_div q (X ^ p - X)
      have heval := congrArg (Polynomial.eval d₀) hdiv
      simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_sub,
        Polynomial.eval_pow, Polynomial.eval_X, ZMod.pow_card d₀, sub_self, zero_mul,
        add_zero] at heval
      rw [hR_coeff_vanish j d₀] at heval
      exact heval
    have hmod_zero : q %ₘ (X ^ p - X) = 0 := by
      by_contra hne
      have hdeg_lt : (q %ₘ (X ^ p - X)).natDegree < p := by
        have hdeg : (q %ₘ (X ^ p - X)).degree < (X ^ p - X : Polynomial (ZMod p)).degree :=
          Polynomial.degree_modByMonic_lt q hXpX_monic
        rw [Polynomial.degree_eq_natDegree hne, Polynomial.degree_eq_natDegree hXpX_monic.ne_zero,
          hXpX_deg] at hdeg
        exact_mod_cast hdeg
      have hcard_le : p ≤ (q %ₘ (X ^ p - X)).roots.card := by
        calc p = (Finset.univ : Finset (ZMod p)).card := (ZMod.card p).symm
          _ ≤ (q %ₘ (X ^ p - X)).roots.toFinset.card := Finset.card_le_card (fun d _ =>
              Multiset.mem_toFinset.mpr ((Polynomial.mem_roots hne).mpr (hmod_eval d)))
          _ ≤ (q %ₘ (X ^ p - X)).roots.card := Multiset.toFinset_card_le _
      have hroots : (q %ₘ (X ^ p - X)).roots.card ≤ (q %ₘ (X ^ p - X)).natDegree :=
        Polynomial.card_roots' _
      omega
    have hdiv := Polynomial.modByMonic_add_div q (X ^ p - X)
    rw [hmod_zero, zero_add] at hdiv
    exact hdiv.symm
  let V : Polynomial (Polynomial (ZMod p)) :=
    ∑ j ∈ Finset.range (R.natDegree + 1), C (R.coeff j /ₘ (X ^ p - X)) * X ^ j
  have hR_eq_CV : R = C (X ^ p - X) * V := by
    ext j
    rw [Polynomial.coeff_C_mul]
    simp only [V, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul_X_pow]
    by_cases hj : j < R.natDegree + 1
    · rw [Finset.sum_eq_single j]
      · rw [if_pos rfl, ← hR_dvd j]
      · intro i _ hij
        simp [hij.symm]
      · intro hnot
        exact absurd (Finset.mem_range.mpr hj) hnot
    · have hj_gt : R.natDegree < j := by omega
      rw [Polynomial.coeff_eq_zero_of_natDegree_lt hj_gt]
      have hsum0 : (∑ i ∈ Finset.range (R.natDegree + 1), if j = i then R.coeff i /ₘ (X ^ p - X) else 0) = 0 := by
        apply Finset.sum_eq_zero
        intro i hi
        rw [Finset.mem_range] at hi
        rw [if_neg (by omega)]
      rw [hsum0, mul_zero]
  have hV_deg : TotalDegLe k V := by
    intro j
    simp only [V, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul_X_pow]
    by_cases hj : j < R.natDegree + 1
    · rw [Finset.sum_eq_single j]
      · rw [if_pos rfl]
        by_cases h0 : R.coeff j /ₘ (X ^ p - X) = 0
        · exact Or.inl h0
        · right
          have hRj_ne : R.coeff j ≠ 0 := by
            rw [hR_dvd j]
            exact mul_ne_zero hXpX_monic.ne_zero h0
          have hRj_deg : (R.coeff j).natDegree + j ≤ A.card * L + 1 := by
            have := ‹TotalDegLe (A.card * L + 1) R› j
            exact this.resolve_left hRj_ne
          have hmul_deg : (R.coeff j).natDegree = p + (R.coeff j /ₘ (X ^ p - X)).natDegree := by
            conv_lhs => rw [hR_dvd j]
            rw [Polynomial.natDegree_mul hXpX_monic.ne_zero h0, hXpX_deg]
          have hk_def : k = A.card * L - p + 1 := rfl
          omega
      · intro i _ hij
        simp [hij, hij.symm]
      · intro hnot
        exact absurd (Finset.mem_range.mpr hj) hnot
    · left
      apply Finset.sum_eq_zero
      intro i hi
      rw [Finset.mem_range] at hi
      rw [if_neg (by omega)]
  set f : Polynomial (ZMod p) := ∏ a ∈ A, (X + C a) ^ L
  set g : Polynomial (ZMod p) := topHom k U
  set h : Polynomial (ZMod p) := topHom k V
  have hf_eq : f = X ^ p * g + h := by
    have h_lhs : topHom (A.card * L + 1) W = f := by
      rw [add_comm (A.card * L) 1]
      change topHom (1 + A.card * L) (C Polynomial.X * _) = f
      rw [topHom_mul hCX_deg hprod_deg, topHom_C_X, one_mul, (h_outer_top A).2]
    have h_rhs : topHom (p + k) ((X ^ p - X) * U + C (X ^ p - X) * V) = X ^ p * g + h := by
      have hCXpX_deg : TotalDegLe p (C (X ^ p - X : Polynomial (ZMod p))) := by
        intro j
        rcases eq_or_ne j 0 with rfl | hj
        · right; rw [Polynomial.coeff_C, if_pos rfl, add_zero, hXpX_deg]
        · left; rw [Polynomial.coeff_C, if_neg hj]
      rw [topHom_add, topHom_mul (totalDegLe_X_pow_sub_X hp.one_lt) hU_deg,
        topHom_mul hCXpX_deg hV_deg, topHom_X_pow_sub_X hp.one_lt,
        topHom_C_X_pow_sub_X hp.one_lt, one_mul]
    rw [← h_lhs, hD_eq, hW_eq, hR_eq_CV, h_rhs]
  have hg_deg : g.natDegree ≤ k := topHom_natDegree_le k U
  have hh_deg : h.natDegree ≤ k := topHom_natDegree_le k V
  have hXp_deriv : (X ^ p : Polynomial (ZMod p)).derivative = 0 := by
    rw [Polynomial.derivative_X_pow, CharP.cast_eq_zero, C_0, zero_mul]
  have hf_deriv : f.derivative = X ^ p * g.derivative + h.derivative := by
    rw [hf_eq, Polynomial.derivative_add, Polynomial.derivative_mul, hXp_deriv, zero_mul, zero_add]
  have h_wronskian : f.derivative * g - f * g.derivative = h.derivative * g - h * g.derivative := by
    rw [hf_deriv, hf_eq]
    ring
  have h_dvd_each : ∀ a ∈ A, (X + C a) ^ (L - 1) ∣ h.derivative * g - h * g.derivative := by
    intro a ha
    rw [← h_wronskian]
    have hf_split : f = (X + C a) ^ L * ∏ a' ∈ A.erase a, (X + C a') ^ L := by
      simp only [f, ← Finset.mul_prod_erase A (fun x => (X + C x) ^ L) ha]
    have hdvd_f : (X + C a) ^ (L - 1) ∣ f := by
      rw [hf_split]
      have hpow : (X + C a) ^ L = (X + C a) ^ (L - 1) * (X + C a) := by
        conv_lhs => rw [show L = (L - 1) + 1 by omega]
        rw [pow_succ]
      rw [hpow, mul_assoc]
      exact dvd_mul_right _ _
    have hdvd_fd : (X + C a) ^ (L - 1) ∣ f.derivative := by
      rw [hf_split, Polynomial.derivative_mul, Polynomial.derivative_pow,
        Polynomial.derivative_X_add_C, mul_one]
      have hpow : (X + C a) ^ L = (X + C a) ^ (L - 1) * (X + C a) := by
        conv_lhs => rw [show L = (L - 1) + 1 by omega]
        rw [pow_succ]
      rw [hpow]
      apply dvd_add
      · exact ⟨C (L : ZMod p) * ∏ a' ∈ A.erase a, (X + C a') ^ L, by simp; ring⟩
      · exact ⟨(X + C a) * (∏ a' ∈ A.erase a, (X + C a') ^ L).derivative, by ring⟩
    exact dvd_sub (dvd_mul_of_dvd_left hdvd_fd g) (dvd_mul_of_dvd_left hdvd_f g.derivative)
  have h_prod_dvd : (∏ a ∈ A, (X + C a) ^ (L - 1)) ∣ h.derivative * g - h * g.derivative := by
    apply Finset.prod_dvd_of_coprime
    · intro a₁ _ a₂ _ hne
      apply IsCoprime.pow
      have hdiff : a₁ - a₂ ≠ 0 := sub_ne_zero.mpr hne
      refine ⟨C (a₁ - a₂)⁻¹, -C (a₁ - a₂)⁻¹, ?_⟩
      calc C (a₁ - a₂)⁻¹ * (X + C a₁) + -C (a₁ - a₂)⁻¹ * (X + C a₂)
          = C ((a₁ - a₂)⁻¹ * (a₁ - a₂)) := by simp only [C_sub, C_mul]; ring
        _ = 1 := by rw [inv_mul_cancel₀ hdiff, C_1]
    · exact h_dvd_each
  by_cases hW_ne : h.derivative * g - h * g.derivative ≠ 0
  · have hdeg_le := Polynomial.natDegree_le_of_dvd h_prod_dvd hW_ne
    have hlhs_deg : (∏ a ∈ A, (X + C a) ^ (L - 1)).natDegree = A.card * (L - 1) := by
      have hmon : ∀ a ∈ A, ((X + C a) ^ (L - 1)).Monic := fun a _ =>
        (Polynomial.monic_X_add_C a).pow (L - 1)
      rw [Polynomial.natDegree_prod_of_monic _ _ hmon]
      simp [Polynomial.natDegree_X_add_C]
    have hrhs_deg : (h.derivative * g - h * g.derivative).natDegree ≤ 2 * k - 1 := by
      have hd1 : h.derivative.natDegree ≤ k - 1 := by
        have := Polynomial.natDegree_derivative_le (p := h)
        omega
      have hd2 : g.derivative.natDegree ≤ k - 1 := by
        have := Polynomial.natDegree_derivative_le (p := g)
        omega
      have hm1 : (h.derivative * g).natDegree ≤ h.derivative.natDegree + g.natDegree :=
        Polynomial.natDegree_mul_le
      have hm2 : (h * g.derivative).natDegree ≤ h.natDegree + g.derivative.natDegree :=
        Polynomial.natDegree_mul_le
      have hs : (h.derivative * g - h * g.derivative).natDegree ≤
          max (h.derivative * g).natDegree (h * g.derivative).natDegree :=
        Polynomial.natDegree_sub_le _ _
      omega
    rw [hlhs_deg] at hdeg_le
    have hk_def : k = A.card * L - p + 1 := rfl
    have hmul : A.card * (L - 1) = A.card * L - A.card := Nat.mul_sub_one A.card L
    omega
  push Not at hW_ne
  have h_deriv_eq : h.derivative * g = h * g.derivative := sub_eq_zero.mp hW_ne
  have hg_ne : g ≠ 0 := by
    intro hg0
    rw [hg0, mul_zero, zero_add] at hf_eq
    have hf_deg : f.natDegree = A.card * L := by
      rw [Polynomial.natDegree_prod_of_monic _ _ (fun a _ => (Polynomial.monic_X_add_C a).pow L)]
      simp [Polynomial.natDegree_X_add_C]
    rw [hf_eq] at hf_deg
    omega
  set D := EuclideanDomain.gcd g h
  have hD_def : D = EuclideanDomain.gcd g h := rfl
  have hD_ne : D ≠ 0 := by
    intro hD0
    have hdvd : D ∣ g := EuclideanDomain.gcd_dvd_left g h
    rw [hD0, zero_dvd_iff] at hdvd
    exact hg_ne hdvd
  rcases EuclideanDomain.gcd_dvd_left g h with ⟨g₁, hg₁⟩
  rcases EuclideanDomain.gcd_dvd_right g h with ⟨h₁, hh₁⟩
  have h_coprime : IsCoprime g₁ h₁ := by
    let a₀ := EuclideanDomain.gcdA g h
    let b₀ := EuclideanDomain.gcdB g h
    have hbez : D = g * a₀ + h * b₀ :=
      hD_def.trans (EuclideanDomain.gcd_eq_gcd_ab g h)
    have hbez' : D * 1 = D * (a₀ * g₁ + b₀ * h₁) := by
      linear_combination hbez + a₀ * hg₁ + b₀ * hh₁
    have h1 := mul_left_cancel₀ hD_ne hbez'
    exact ⟨a₀, b₀, h1.symm⟩
  have h_deriv_red : h₁.derivative * g₁ = h₁ * g₁.derivative := by
    have hhd : h.derivative = D.derivative * h₁ + D * h₁.derivative := by
      conv_lhs => rw [hh₁]
      exact Polynomial.derivative_mul
    have hgd : g.derivative = D.derivative * g₁ + D * g₁.derivative := by
      conv_lhs => rw [hg₁]
      exact Polynomial.derivative_mul
    have h1 : D * D * (h₁.derivative * g₁) = D * D * (h₁ * g₁.derivative) := by
      have hL : h.derivative * g = (D.derivative * h₁ + D * h₁.derivative) * (D * g₁) := by
        rw [hhd]; conv_lhs => rhs; rw [hg₁]
      have hR : h * g.derivative = (D * h₁) * (D.derivative * g₁ + D * g₁.derivative) := by
        rw [hgd]; conv_lhs => lhs; rw [hh₁]
      rw [hL, hR] at h_deriv_eq
      linear_combination h_deriv_eq
    exact mul_left_cancel₀ (mul_ne_zero hD_ne hD_ne) h1
  have hg₁_dvd : g₁ ∣ g₁.derivative := by
    have hdvd : g₁ ∣ h₁ * g₁.derivative := ⟨h₁.derivative, by rw [← h_deriv_red]; ring⟩
    exact h_coprime.dvd_of_dvd_mul_left hdvd
  have hh₁_dvd : h₁ ∣ h₁.derivative := by
    have hdvd : h₁ ∣ g₁ * h₁.derivative := ⟨g₁.derivative, by rw [mul_comm g₁ h₁.derivative, h_deriv_red]⟩
    exact h_coprime.symm.dvd_of_dvd_mul_left hdvd
  have hg₁_deriv_zero : g₁.derivative = 0 := by
    by_contra hne
    have hle := Polynomial.natDegree_le_of_dvd hg₁_dvd hne
    have hlt : g₁.derivative.natDegree < g₁.natDegree := by
      have h1 : g₁.natDegree ≠ 0 := by
        intro h0
        rw [Polynomial.eq_C_of_natDegree_eq_zero h0, Polynomial.derivative_C] at hne
        exact hne rfl
      have h2 := Polynomial.natDegree_derivative_le (p := g₁)
      omega
    omega
  have hh₁_deriv_zero : h₁.derivative = 0 := by
    by_contra hne
    have hle := Polynomial.natDegree_le_of_dvd hh₁_dvd hne
    have hlt : h₁.derivative.natDegree < h₁.natDegree := by
      have h1 : h₁.natDegree ≠ 0 := by
        intro h0
        rw [Polynomial.eq_C_of_natDegree_eq_zero h0, Polynomial.derivative_C] at hne
        exact hne rfl
      have h2 := Polynomial.natDegree_derivative_le (p := h₁)
      omega
    omega
  have hg₁_ne : g₁ ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hg₁
    exact hg_ne hg₁
  have hg₁_deg_le : g₁.natDegree ≤ g.natDegree :=
    Polynomial.natDegree_le_of_dvd ⟨D, by rw [hg₁]; ring⟩ hg_ne
  have hh₁_deg_le : h₁.natDegree ≤ h.natDegree := by
    by_cases hh0 : h = 0
    · have hh₁' : 0 = D * h₁ := hh0 ▸ hh₁
      have hh₁0 : h₁ = 0 := by
        rcases mul_eq_zero.mp hh₁'.symm with hD0 | h10
        · exact absurd hD0 hD_ne
        · exact h10
      rw [hh₁0]; simp
    · exact Polynomial.natDegree_le_of_dvd ⟨D, by rw [hh₁]; ring⟩ hh0
  have hg₁_deg0 : g₁.natDegree = 0 :=
    deriv_eq_zero_natDeg_lt hp (lt_of_le_of_lt (hg₁_deg_le.trans hg_deg) hk_lt_p) hg₁_deriv_zero
  have hh₁_deg0 : h₁.natDegree = 0 :=
    deriv_eq_zero_natDeg_lt hp (lt_of_le_of_lt (hh₁_deg_le.trans hh_deg) hk_lt_p) hh₁_deriv_zero
  have hg₁_C : g₁ = C (g₁.coeff 0) := Polynomial.eq_C_of_natDegree_eq_zero hg₁_deg0
  have hh₁_C : h₁ = C (h₁.coeff 0) := Polynomial.eq_C_of_natDegree_eq_zero hh₁_deg0
  have hc₁_ne : g₁.coeff 0 ≠ 0 := by
    intro h0
    rw [h0, C_0] at hg₁_C
    exact hg₁_ne hg₁_C
  set c : ZMod p := h₁.coeff 0 * (g₁.coeff 0)⁻¹
  have hh_eq_cg : h = C c * g := by
    let c₁ := g₁.coeff 0
    let c₂ := h₁.coeff 0
    have hinner : C c₂ = C c₁ * C c := by
      rw [← C_mul, mul_comm c₁ c, mul_assoc, inv_mul_cancel₀ hc₁_ne, mul_one]
    calc h = D * h₁ := hh₁
      _ = D * C c₂ := by rw [hh₁_C]
      _ = D * (C c₁ * C c) := by rw [hinner]
      _ = C c * (D * C c₁) := by ring
      _ = C c * (D * g₁) := by rw [← hg₁_C]
      _ = C c * g := by rw [← hg₁]
  have hf_frob : f = (X + C c) ^ p * g := by
    have hpow : (X + C c : Polynomial (ZMod p)) ^ p = X ^ p + C c := by
      rw [add_pow_char, ← C_pow, ZMod.pow_card]
    rw [hf_eq, hh_eq_cg, hpow]
    ring
  have hf_ne : f ≠ 0 := by
    have hf_monic : f.Monic :=
      Polynomial.monic_prod_of_monic _ _ (fun a _ => (Polynomial.monic_X_add_C a).pow L)
    exact hf_monic.ne_zero
  have hdvd_frob : (X - C (-c)) ^ p ∣ f := by
    refine ⟨g, ?_⟩
    simpa [sub_neg_eq_add] using hf_frob
  have hp_le_mult : p ≤ f.rootMultiplicity (-c) :=
    (Polynomial.le_rootMultiplicity_iff hf_ne).mpr hdvd_frob
  have hmult_le_L : f.rootMultiplicity (-c) ≤ L := by
    have h_ind : ∀ s : Finset (ZMod p),
        (∏ a ∈ s, (X + C a) ^ L).rootMultiplicity (-c) ≤ if c ∈ s then L else 0 := by
      intro s
      induction s using Finset.induction with
      | empty =>
        simp
      | insert a s has ih =>
        have ha_ne : (X + C a) ^ L ≠ 0 := ((Polynomial.monic_X_add_C a).pow L).ne_zero
        have hs_ne : (∏ x ∈ s, (X + C x) ^ L) ≠ 0 :=
          (Polynomial.monic_prod_of_monic _ _ (fun x _ => (Polynomial.monic_X_add_C x).pow L)).ne_zero
        rw [Finset.prod_insert has, Polynomial.rootMultiplicity_mul (mul_ne_zero ha_ne hs_ne)]
        by_cases hac : a = c
        · subst hac
          have h1 : ((X + C c) ^ L).rootMultiplicity (-c) ≤ L := by
            have hdvd := Polynomial.pow_rootMultiplicity_dvd ((X + C c) ^ L) (-c)
            have hdeg := Polynomial.natDegree_le_of_dvd hdvd ha_ne
            rw [Polynomial.natDegree_pow, Polynomial.natDegree_X_sub_C, mul_one] at hdeg
            rw [Polynomial.natDegree_pow, Polynomial.natDegree_X_add_C, mul_one] at hdeg
            exact hdeg
          have h2 : c ∉ s := has
          simp only [if_neg h2] at ih
          rw [if_pos (Finset.mem_insert_self c s)]
          omega
        · have hne_eval : ((X + C a) ^ L).eval (-c) ≠ 0 := by
            simp only [Polynomial.eval_pow, Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C]
            apply pow_ne_zero
            intro h0
            apply hac
            linear_combination h0
          have h1 : ((X + C a) ^ L).rootMultiplicity (-c) = 0 :=
            Polynomial.rootMultiplicity_eq_zero hne_eval
          rw [h1, zero_add]
          simpa [Finset.mem_insert, Ne.symm hac] using ih
    calc f.rootMultiplicity (-c)
        ≤ if c ∈ A then L else 0 := h_ind A
      _ ≤ L := by split_ifs <;> omega
  omega

end OMA.Green32General

theorem OMA.solution : type_of% @Green32.green_32.variants.sh20_general :=
  OMA.Green32General.sh20_general_aux
