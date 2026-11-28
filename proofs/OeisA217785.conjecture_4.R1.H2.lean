import OMAReductions.R_OeisA217785_conjecture_4_R1

/-!
# Proof of `OeisA217785.conjecture_4.R1.H2`

For `n = 8 k (k + 1)` with `k ≥ 1`, the polynomial `s_n(x) = ∑_{j=0}^n (j + 1) x^j` is reducible
modulo every prime `p`:
- For `p = 2`, `s_n(x) ≡ (∑_{j=0}^{n/2} x^j)^2`.
- For odd `p ∣ n + 1`, the identity `(x - 1)^2 s_n(x) = (n + 1) x^{n+2} - (n + 2) x^{n+1} + 1`
  yields `s_n(x) ≡ (1 - x)^{p - 2} (∑_{j=0}^{(n+1)/p - 1} x^j)^p`.
- For odd `p ∣ n + 2` with `p ∤ n + 1`, `s_n(1) = (n + 1)(n + 2)/2 ≡ 0`, so `x - 1` divides `s_n`.
- For odd `p ∤ (n + 1)(n + 2)`, if `s_n` were irreducible over `ZMod p`, the Vandermonde product
  `δ = ∏_{i < j} (α^{p^j} - α^{p^i})` in `AdjoinRoot s_n` would satisfy `δ^p = -δ` (since `n` is
  even), forcing `δ^2` to be a non-square in `ZMod p`, whereas differentiating `(x - 1)^2 s_n(x)`
  gives `(n + 1)^n δ^2 = 2 (n + 2)^{n - 1} = ((4 k + 2) (n + 2)^{n/2 - 1})^2`, a square in `ZMod p`.
-/

namespace OMA.Proof_OeisA217785_conjecture_4_R1_H2

open Polynomial Finset OeisA217785

private lemma mul_sq_sub_one_polyS (n : ℕ) :
    (X - 1 : ℤ[X]) ^ 2 * polyS n =
      C ((n : ℤ) + 1) * X ^ (n + 2) - C ((n : ℤ) + 2) * X ^ (n + 1) + 1 := by
  induction n with
  | zero =>
    simp [polyS]
    ring
  | succ n ih =>
    have hsucc : polyS (n + 1) = polyS n + C ((n : ℤ) + 2) * X ^ (n + 1) := by
      unfold polyS
      rw [Finset.sum_range_succ]
      push_cast
      simp only [map_add, map_one, map_ofNat]
      ring
    rw [hsucc, mul_add, ih]
    push_cast
    simp only [map_add, map_one, map_ofNat]
    ring

private lemma two_mul_polyS_add_sub_one_mul_deriv (n : ℕ) :
    2 * polyS n + (X - 1 : ℤ[X]) * derivative (polyS n) =
      C (((n : ℤ) + 1) * ((n : ℤ) + 2)) * X ^ n := by
  have h1 := congrArg Polynomial.derivative (mul_sq_sub_one_polyS n)
  have hlhs : Polynomial.derivative ((X - 1 : ℤ[X]) ^ 2 * polyS n) =
      (X - 1 : ℤ[X]) * (2 * polyS n + (X - 1 : ℤ[X]) * derivative (polyS n)) := by
    simp only [derivative_mul, derivative_pow, derivative_sub, derivative_X, derivative_one,
      sub_zero, mul_one, Nat.cast_ofNat, C_ofNat]
    ring
  have hrhs : Polynomial.derivative
      (C ((n : ℤ) + 1) * X ^ (n + 2) - C ((n : ℤ) + 2) * X ^ (n + 1) + 1) =
      (X - 1 : ℤ[X]) * (C (((n : ℤ) + 1) * ((n : ℤ) + 2)) * X ^ n) := by
    simp only [derivative_add, derivative_sub, derivative_mul, derivative_C, zero_mul, zero_add,
      derivative_X_pow, derivative_one, add_zero]
    rw [show n + 2 - 1 = n + 1 by omega, show n + 1 - 1 = n by omega]
    simp only [Nat.cast_add, Nat.cast_one, Nat.cast_ofNat, map_mul, map_add, map_one, map_ofNat]
    ring
  rw [hlhs, hrhs] at h1
  have hne : (X - 1 : ℤ[X]) ≠ 0 := by
    intro h
    have := congrArg (Polynomial.eval 0) h
    norm_num at this
  exact mul_left_cancel₀ hne h1

private lemma coeff_polyS_map (p n j : ℕ) :
    ((polyS n).map (Int.castRingHom (ZMod p))).coeff j =
      if j < n + 1 then ((j + 1 : ℕ) : ZMod p) else 0 := by
  rw [Polynomial.coeff_map]
  unfold polyS
  rw [Polynomial.finsetSum_coeff]
  by_cases hj : j < n + 1
  · rw [if_pos hj, Finset.sum_eq_single j]
    · rw [Polynomial.coeff_C_mul_X_pow, if_pos rfl]
      simp
    · intro k _ hkj
      rw [Polynomial.coeff_C_mul_X_pow, if_neg hkj.symm]
    · intro hmem
      exact absurd (Finset.mem_range.mpr hj) hmem
  · rw [if_neg hj, Finset.sum_eq_zero]
    · simp
    · intro k hk
      rw [Polynomial.coeff_C_mul_X_pow, if_neg]
      have := Finset.mem_range.mp hk
      omega

private lemma natDegree_polyS_map_le (p n : ℕ) :
    ((polyS n).map (Int.castRingHom (ZMod p))).natDegree ≤ n := by
  apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
  intro j hj
  rw [coeff_polyS_map, if_neg (by omega)]

private lemma natDegree_polyS_map_eq (p n : ℕ) (hndvd : ¬ p ∣ n + 1) :
    ((polyS n).map (Int.castRingHom (ZMod p))).natDegree = n := by
  apply le_antisymm (natDegree_polyS_map_le p n)
  apply Polynomial.le_natDegree_of_ne_zero
  rw [coeff_polyS_map, if_pos (by omega)]
  intro h0
  exact hndvd ((ZMod.natCast_eq_zero_iff (n + 1) p).mp h0)

private lemma leadingCoeff_polyS_map (p n : ℕ) (hndvd : ¬ p ∣ n + 1) :
    ((polyS n).map (Int.castRingHom (ZMod p))).leadingCoeff = ((n + 1 : ℕ) : ZMod p) := by
  rw [Polynomial.leadingCoeff, natDegree_polyS_map_eq p n hndvd, coeff_polyS_map, if_pos (by omega)]

private lemma not_irreducible_of_mul_natDegree_pos {F : Type*} [Field F] {f a b : F[X]}
    (hfab : f = a * b) (ha : 0 < a.natDegree) (hb : 0 < b.natDegree) : ¬ Irreducible f := by
  intro hirr
  rcases hirr.isUnit_or_isUnit hfab with hu | hu
  · have := Polynomial.natDegree_eq_zero_of_isUnit hu
    omega
  · have := Polynomial.natDegree_eq_zero_of_isUnit hu
    omega

private lemma sum_pow_two_char_two {R : Type*} [CommRing R] [CharP R 2] {ι : Type*}
    (s : Finset ι) (g : ι → R) : (∑ i ∈ s, g i) ^ 2 = ∑ i ∈ s, (g i) ^ 2 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, add_pow_char, ih]

private lemma case_p_eq_two (m : ℕ) (hm : 1 ≤ m) :
    ¬ Irreducible ((polyS (2 * m)).map (Int.castRingHom (ZMod 2))) := by
  let g : (ZMod 2)[X] := ∑ j ∈ Finset.range (m + 1), X ^ j
  have hsq : (polyS (2 * m)).map (Int.castRingHom (ZMod 2)) = g * g := by
    have hpow : g * g = ∑ j ∈ Finset.range (m + 1), X ^ (2 * j) := by
      rw [← sq]
      dsimp only [g]
      rw [sum_pow_two_char_two]
      refine Finset.sum_congr rfl ?_
      intro j _
      rw [← pow_mul, mul_comm]
    rw [hpow]
    ext k
    rw [coeff_polyS_map, Polynomial.finsetSum_coeff]
    by_cases hk : k < 2 * m + 1
    · rw [if_pos hk]
      rcases Nat.even_or_odd k with ⟨j, rfl⟩ | ⟨j, rfl⟩
      · have hj : j < m + 1 := by omega
        rw [Finset.sum_eq_single j]
        · rw [show j + j = 2 * j by omega, Polynomial.coeff_X_pow_self]
          have h2 : (2 : ZMod 2) = 0 := by decide
          push_cast
          linear_combination (j : ZMod 2) * h2
        · intro i _ hij
          rw [Polynomial.coeff_X_pow, if_neg (by omega)]
        · intro hmem
          exact absurd (Finset.mem_range.mpr hj) hmem
      · rw [Finset.sum_eq_zero]
        · have h2 : (2 : ZMod 2) = 0 := by decide
          push_cast
          linear_combination ((j : ZMod 2) + 1) * h2
        · intro i _
          rw [Polynomial.coeff_X_pow, if_neg (by omega)]
    · rw [if_neg hk, Finset.sum_eq_zero]
      intro i hi
      have := Finset.mem_range.mp hi
      rw [Polynomial.coeff_X_pow, if_neg (by omega)]
  have hgdeg : g.natDegree = m := by
    apply le_antisymm
    · apply Polynomial.natDegree_sum_le_of_forall_le
      intro j hj
      have := Finset.mem_range.mp hj
      rw [Polynomial.natDegree_X_pow]
      omega
    · apply Polynomial.le_natDegree_of_ne_zero
      rw [Polynomial.finsetSum_coeff, Finset.sum_eq_single m]
      · simp
      · intro j _ hjm
        rw [Polynomial.coeff_X_pow, if_neg hjm.symm]
      · intro hmem
        exact absurd (Finset.mem_range.mpr (by omega)) hmem
  exact not_irreducible_of_mul_natDegree_pos hsq (by omega) (by omega)

private lemma case_p_dvd_succ (p n : ℕ) [Fact p.Prime] (hpodd : p ≠ 2) (hn : 16 ≤ n)
    (hdvd : p ∣ n + 1) : ¬ Irreducible ((polyS n).map (Int.castRingHom (ZMod p))) := by
  have hp : p.Prime := Fact.out
  have hp3 : 3 ≤ p := by
    have := hp.two_le
    omega
  obtain ⟨q, hq⟩ := hdvd
  have hqpos : 1 ≤ q := by
    by_contra h0
    have : q = 0 := by omega
    rw [this, mul_zero] at hq
    omega
  let f : (ZMod p)[X] := (polyS n).map (Int.castRingHom (ZMod p))
  have hid := congrArg (Polynomial.map (Int.castRingHom (ZMod p))) (mul_sq_sub_one_polyS n)
  simp only [Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_sub, Polynomial.map_add,
    Polynomial.map_X, Polynomial.map_one, Polynomial.map_C] at hid
  have hn1 : ((n : ZMod p) + 1) = 0 := by
    have h0 : ((n + 1 : ℕ) : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff (n + 1) p).mpr ⟨q, hq⟩
    simpa [Nat.cast_add] using h0
  have hn2 : ((n : ZMod p) + 2) = 1 := by
    calc (n : ZMod p) + 2 = ((n : ZMod p) + 1) + 1 := by ring
      _ = 1 := by rw [hn1, zero_add]
  have hid' : (X - 1 : (ZMod p)[X]) ^ 2 * f = 1 - X ^ (n + 1) := by
    change (X - 1 : (ZMod p)[X]) ^ 2 * ((polyS n).map (Int.castRingHom (ZMod p))) = _
    rw [hid]
    have h1' : Int.castRingHom (ZMod p) ((n : ℤ) + 1) = 0 := by simp [hn1]
    have h2' : Int.castRingHom (ZMod p) ((n : ℤ) + 2) = 1 := by simp [hn2]
    rw [h1', h2']
    simp [sub_eq_add_neg, add_comm]
  let h : (ZMod p)[X] := ∑ j ∈ Finset.range q, X ^ j
  have hgeom : (1 - X : (ZMod p)[X]) * h = 1 - X ^ q := by
    dsimp only [h]
    rw [mul_comm]
    exact geom_sum_mul_neg X q
  have hpowp : (1 - X ^ (n + 1) : (ZMod p)[X]) = (1 - X) ^ p * h ^ p := by
    rw [← mul_pow, hgeom, sub_pow_char, one_pow, ← pow_mul, hq, mul_comm q p]
  have hsplit : (1 - X : (ZMod p)[X]) ^ p = (X - 1) ^ 2 * (1 - X) ^ (p - 2) := by
    have hsq : (1 - X : (ZMod p)[X]) ^ 2 = (X - 1) ^ 2 := by ring
    rw [← hsq, ← pow_add, show 2 + (p - 2) = p by omega]
  have hfac : f = (1 - X : (ZMod p)[X]) ^ (p - 2) * h ^ p := by
    have heq : (X - 1 : (ZMod p)[X]) ^ 2 * f =
        (X - 1 : (ZMod p)[X]) ^ 2 * ((1 - X : (ZMod p)[X]) ^ (p - 2) * h ^ p) := by
      rw [hid', hpowp, hsplit, mul_assoc]
    have hne : (X - 1 : (ZMod p)[X]) ^ 2 ≠ 0 := by
      intro h0
      have h1 := eq_zero_of_pow_eq_zero h0
      have h2 := congrArg (Polynomial.eval 0) h1
      simp at h2
    exact mul_left_cancel₀ hne heq
  have hdeg1X : (1 - X : (ZMod p)[X]).natDegree = 1 := by
    have : (1 - X : (ZMod p)[X]) = -(X - C 1) := by simp [sub_eq_add_neg, add_comm]
    rw [this, Polynomial.natDegree_neg, Polynomial.natDegree_X_sub_C]
  have hdeg_pow : ((1 - X : (ZMod p)[X]) ^ (p - 2)).natDegree = p - 2 := by
    rw [Polynomial.natDegree_pow, hdeg1X, mul_one]
  by_cases hq1 : q = 1
  · have hp17 : 17 ≤ p := by
      rw [hq1, mul_one] at hq
      omega
    have hheq : h = 1 := by simp [h, hq1]
    have hfac2 : f = (1 - X : (ZMod p)[X]) * (1 - X : (ZMod p)[X]) ^ (p - 3) := by
      rw [hfac, hheq, one_pow, mul_one, ← pow_succ', show p - 3 + 1 = p - 2 by omega]
    have hdeg2 : ((1 - X : (ZMod p)[X]) ^ (p - 3)).natDegree = p - 3 := by
      rw [Polynomial.natDegree_pow, hdeg1X, mul_one]
    exact not_irreducible_of_mul_natDegree_pos hfac2 (by omega) (by omega)
  · have hq2 : 2 ≤ q := by omega
    have hhdeg : h.natDegree = q - 1 := by
      apply le_antisymm
      · apply Polynomial.natDegree_sum_le_of_forall_le
        intro j hj
        have := Finset.mem_range.mp hj
        rw [Polynomial.natDegree_X_pow]
        omega
      · apply Polynomial.le_natDegree_of_ne_zero
        rw [Polynomial.finsetSum_coeff, Finset.sum_eq_single (q - 1)]
        · simp
        · intro j _ hjne
          rw [Polynomial.coeff_X_pow, if_neg hjne.symm]
        · intro hmem
          exact absurd (Finset.mem_range.mpr (by omega)) hmem
    have hhpdeg : (h ^ p).natDegree = p * (q - 1) := by
      rw [Polynomial.natDegree_pow, hhdeg]
    have hhp_pos : 0 < (h ^ p).natDegree := by
      rw [hhpdeg]
      exact Nat.mul_pos hp.pos (by omega)
    exact not_irreducible_of_mul_natDegree_pos hfac (by omega) hhp_pos

private lemma case_p_dvd_add_two (p n : ℕ) [Fact p.Prime] (hpodd : p ≠ 2) (hn : 16 ≤ n)
    (hndvd1 : ¬ p ∣ n + 1) (hdvd2 : p ∣ n + 2) :
    ¬ Irreducible ((polyS n).map (Int.castRingHom (ZMod p))) := by
  have hp : p.Prime := Fact.out
  let f : (ZMod p)[X] := (polyS n).map (Int.castRingHom (ZMod p))
  have hid := congrArg (Polynomial.map (Int.castRingHom (ZMod p)))
    (two_mul_polyS_add_sub_one_mul_deriv n)
  have hev := congrArg (Polynomial.eval (1 : ZMod p)) hid
  simp only [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_sub, Polynomial.map_ofNat,
    Polynomial.map_X, Polynomial.map_one, Polynomial.map_C, Polynomial.map_pow,
    Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_ofNat,
    Polynomial.eval_X, Polynomial.eval_one, Polynomial.eval_C, Polynomial.eval_pow,
    sub_self, zero_mul, add_zero, one_pow, mul_one] at hev
  have hn2 : ((n : ZMod p) + 2) = 0 := by
    have h0 : ((n + 2 : ℕ) : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff (n + 2) p).mpr hdvd2
    simpa [Nat.cast_add] using h0
  have h2f : (2 : ZMod p) * f.eval 1 = 0 := by
    have h2' : Int.castRingHom (ZMod p) (((n : ℤ) + 1) * ((n : ℤ) + 2)) = 0 := by simp [hn2]
    rw [h2'] at hev
    exact hev
  have h2ne : (2 : ZMod p) ≠ 0 := by
    intro h0
    have hd : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp (by simpa using h0)
    have hle := Nat.le_of_dvd (by omega) hd
    have := hp.two_le
    omega
  have hroot : f.eval 1 = 0 := (mul_eq_zero.mp h2f).resolve_left h2ne
  obtain ⟨g, hfg⟩ := Polynomial.dvd_iff_isRoot.mpr hroot
  have hfdeg : f.natDegree = n := natDegree_polyS_map_eq p n hndvd1
  have hne : f ≠ 0 := by
    intro h0
    rw [h0, Polynomial.natDegree_zero] at hfdeg
    omega
  have hgne : g ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hfg
    exact hne hfg
  have hx1ne : (X - C 1 : (ZMod p)[X]) ≠ 0 := Polynomial.X_sub_C_ne_zero 1
  have hdeg_add : f.natDegree = (X - C (1 : ZMod p)).natDegree + g.natDegree := by
    rw [hfg, Polynomial.natDegree_mul hx1ne hgne]
  rw [hfdeg, Polynomial.natDegree_X_sub_C] at hdeg_add
  exact not_irreducible_of_mul_natDegree_pos hfg (by rw [Polynomial.natDegree_X_sub_C]; omega)
    (by omega)

private lemma eval_map_pow_char {p : ℕ} [Fact p.Prime] {K : Type*} [Field K] [CharP K p]
    (φ : ZMod p →+* K) (q : (ZMod p)[X]) (x : K) :
    (q.map φ).eval (x ^ p) = ((q.map φ).eval x) ^ p := by
  induction q using Polynomial.induction_on' with
  | add q₁ q₂ ih₁ ih₂ =>
    simp only [Polynomial.map_add, Polynomial.eval_add, ih₁, ih₂, add_pow_char]
  | monomial k c =>
    simp only [Polynomial.map_monomial, Polynomial.eval_monomial, mul_pow, ← pow_mul, mul_comm k p]
    congr 1
    rw [← map_pow, ZMod.pow_card]

private lemma eval_map_pow_char_pow {p : ℕ} [Fact p.Prime] {K : Type*} [Field K] [CharP K p]
    (φ : ZMod p →+* K) (q : (ZMod p)[X]) (x : K) :
    ∀ i : ℕ, (q.map φ).eval (x ^ (p ^ i)) = ((q.map φ).eval x) ^ (p ^ i)
  | 0 => by simp
  | i + 1 => by
    rw [pow_succ, pow_mul, eval_map_pow_char, eval_map_pow_char_pow φ q x i, ← pow_mul, ← pow_succ]

private lemma vandermonde_pow_char {K : Type*} [CommRing K] {p n : ℕ} [Fact p.Prime] [CharP K p]
    (hn_pos : 0 < n) (hn_even : Even n) (r : ℕ → K) (hr_step : ∀ i : ℕ, (r i) ^ p = r (i + 1))
    (hr_n : r n = r 0) :
    (∏ e ∈ (Finset.univ : Finset (Fin n × Fin n)).filter (fun e => e.1 < e.2),
        (r e.2.val - r e.1.val)) ^ p =
      -(∏ e ∈ (Finset.univ : Finset (Fin n × Fin n)).filter (fun e => e.1 < e.2),
        (r e.2.val - r e.1.val)) := by
  classical
  let S : Finset (Fin n × Fin n) := (Finset.univ : Finset (Fin n × Fin n)).filter (fun e => e.1 < e.2)
  let δ : K := ∏ e ∈ S, (r e.2.val - r e.1.val)
  change δ ^ p = -δ
  let next : Fin n → Fin n := fun i => ⟨(i.val + 1) % n, Nat.mod_lt _ hn_pos⟩
  have hr_next : ∀ i : Fin n, r (i.val + 1) = r (next i).val := by
    intro i
    dsimp only [next]
    by_cases hlt : i.val + 1 < n
    · rw [Nat.mod_eq_of_lt hlt]
    · have := i.isLt
      have heq : i.val + 1 = n := by omega
      rw [heq, Nat.mod_self]
      exact hr_n
  have hp1 : δ ^ p = ∏ e ∈ S, (r (next e.2).val - r (next e.1).val) := by
    dsimp only [δ]
    rw [← Finset.prod_pow]
    refine Finset.prod_congr rfl ?_
    intro e _
    rw [sub_pow_char, hr_step, hr_step, hr_next, hr_next]
  let S₁ : Finset (Fin n × Fin n) := S.filter (fun e => e.2.val + 1 < n)
  let S₂ : Finset (Fin n × Fin n) := S.filter (fun e => ¬ e.2.val + 1 < n)
  have hdisj : Disjoint S₁ S₂ := Finset.disjoint_filter.mpr (fun _ _ h1 h2 => h2 h1)
  have hunion : S₁ ∪ S₂ = S := by
    ext e
    simp only [S₁, S₂, Finset.mem_union, Finset.mem_filter]
    tauto
  let ψ : Fin n × Fin n → Fin n × Fin n := fun e =>
    if e.2.val + 1 < n then (next e.1, next e.2) else (next e.2, next e.1)
  have hψ_mem : ∀ e ∈ S, ψ e ∈ S := by
    intro e he
    have hlt : e.1.val < e.2.val := (Finset.mem_filter.mp he).2
    have hlt2 := e.2.isLt
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    dsimp only [ψ, next]
    by_cases h : e.2.val + 1 < n
    · rw [if_pos h]
      change (e.1.val + 1) % n < (e.2.val + 1) % n
      rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt h]
      omega
    · rw [if_neg h]
      have he2 : e.2.val + 1 = n := by omega
      change (e.2.val + 1) % n < (e.1.val + 1) % n
      rw [he2, Nat.mod_self, Nat.mod_eq_of_lt (by omega)]
      omega
  have hψ_inj : ∀ e₁ ∈ S, ∀ e₂ ∈ S, ψ e₁ = ψ e₂ → e₁ = e₂ := by
    intro e₁ he₁ e₂ he₂ heq
    have hlt₁ : e₁.1.val < e₁.2.val := (Finset.mem_filter.mp he₁).2
    have hlt₂ : e₂.1.val < e₂.2.val := (Finset.mem_filter.mp he₂).2
    have hb₁ := e₁.2.isLt
    have hb₂ := e₂.2.isLt
    dsimp only [ψ, next] at heq
    by_cases h1 : e₁.2.val + 1 < n <;> by_cases h2 : e₂.2.val + 1 < n
    · rw [if_pos h1, if_pos h2] at heq
      have hf1 := congrArg (fun q => q.1.val) heq
      have hf2 := congrArg (fun q => q.2.val) heq
      dsimp only at hf1 hf2
      rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at hf1
      rw [Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt h2] at hf2
      exact Prod.ext (Fin.ext (by omega)) (Fin.ext (by omega))
    · rw [if_pos h1, if_neg h2] at heq
      have hf1 := congrArg (fun q => q.1.val) heq
      dsimp only at hf1
      have he2' : e₂.2.val + 1 = n := by omega
      rw [Nat.mod_eq_of_lt (by omega), he2', Nat.mod_self] at hf1
      omega
    · rw [if_neg h1, if_pos h2] at heq
      have hf1 := congrArg (fun q => q.1.val) heq
      dsimp only at hf1
      have he1' : e₁.2.val + 1 = n := by omega
      rw [he1', Nat.mod_self, Nat.mod_eq_of_lt (by omega)] at hf1
      omega
    · rw [if_neg h1, if_neg h2] at heq
      have hf2 := congrArg (fun q => q.2.val) heq
      dsimp only at hf2
      rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at hf2
      exact Prod.ext (Fin.ext (by omega)) (Fin.ext (by omega))
  have hψ_surj : ∀ e' ∈ S, ∃ e, ∃ (_ : e ∈ S), ψ e = e' := by
    intro e' he'
    have hlt' : e'.1.val < e'.2.val := (Finset.mem_filter.mp he').2
    have hb' := e'.2.isLt
    by_cases h0 : e'.1.val = 0
    · let e : Fin n × Fin n := (⟨e'.2.val - 1, by omega⟩, ⟨n - 1, by omega⟩)
      refine ⟨e, ?_, ?_⟩
      · rw [Finset.mem_filter]
        refine ⟨Finset.mem_univ _, ?_⟩
        change e'.2.val - 1 < n - 1
        omega
      · dsimp only [ψ, next, e]
        rw [if_neg (by omega)]
        apply Prod.ext <;> apply Fin.ext
        · change (n - 1 + 1) % n = e'.1.val
          rw [Nat.sub_add_cancel (by omega), Nat.mod_self, h0]
        · change (e'.2.val - 1 + 1) % n = e'.2.val
          rw [Nat.sub_add_cancel (by omega), Nat.mod_eq_of_lt e'.2.isLt]
    · let e : Fin n × Fin n := (⟨e'.1.val - 1, by omega⟩, ⟨e'.2.val - 1, by omega⟩)
      refine ⟨e, ?_, ?_⟩
      · rw [Finset.mem_filter]
        refine ⟨Finset.mem_univ _, ?_⟩
        change e'.1.val - 1 < e'.2.val - 1
        omega
      · dsimp only [ψ, next, e]
        rw [if_pos (by omega)]
        apply Prod.ext <;> apply Fin.ext
        · change (e'.1.val - 1 + 1) % n = e'.1.val
          rw [Nat.sub_add_cancel (by omega), Nat.mod_eq_of_lt e'.1.isLt]
        · change (e'.2.val - 1 + 1) % n = e'.2.val
          rw [Nat.sub_add_cancel (by omega), Nat.mod_eq_of_lt e'.2.isLt]
  have hS2_card : S₂.card = n - 1 := by
    let lastN : Fin n := ⟨n - 1, by omega⟩
    have heq : S₂ = (Finset.univ.filter (fun i : Fin n => i.val < n - 1)).image
        (fun i : Fin n => (i, lastN)) := by
      ext ⟨a, b⟩
      simp only [S₂, S, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
      constructor
      · rintro ⟨hab, hb⟩
        have hbLt := b.isLt
        have hbv : b = lastN := Fin.ext (by dsimp [lastN]; omega)
        have haLt : a.val < b.val := hab
        exact ⟨a, by omega, Prod.ext rfl hbv.symm⟩
      · rintro ⟨i, hi, heq'⟩
        rcases Prod.mk.inj heq' with ⟨rfl, rfl⟩
        exact ⟨by change i.val < lastN.val; dsimp [lastN]; exact hi, by dsimp [lastN]; omega⟩
    rw [heq, Finset.card_image_of_injective]
    · have hfilt : (Finset.univ.filter (fun i : Fin n => i.val < n - 1)) =
          Finset.univ.erase lastN := by
        ext i
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase, ne_eq,
          Fin.ext_iff, and_true]
        change i.val < n - 1 ↔ i.val ≠ n - 1
        have := i.isLt
        omega
      rw [hfilt, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_fin]
    · intro i j h
      exact congrArg Prod.fst h
  have hprod_ψ : ∏ e ∈ S, (r (ψ e).2.val - r (ψ e).1.val) = δ :=
    Finset.prod_bij (fun e _ => ψ e) hψ_mem hψ_inj hψ_surj (fun _ _ => rfl)
  rw [hp1, ← hunion, Finset.prod_union hdisj]
  have h1 : ∏ e ∈ S₁, (r (next e.2).val - r (next e.1).val) =
      ∏ e ∈ S₁, (r (ψ e).2.val - r (ψ e).1.val) := by
    refine Finset.prod_congr rfl ?_
    intro e he
    have hlt : e.2.val + 1 < n := (Finset.mem_filter.mp he).2
    simp [ψ, hlt]
  have h2 : ∏ e ∈ S₂, (r (next e.2).val - r (next e.1).val) =
      (-1 : K) ^ S₂.card * ∏ e ∈ S₂, (r (ψ e).2.val - r (ψ e).1.val) := by
    rw [← Finset.prod_const, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl ?_
    intro e he
    have hnlt : ¬ e.2.val + 1 < n := (Finset.mem_filter.mp he).2
    simp only [ψ, if_neg hnlt]
    ring
  rw [h1, h2, ← mul_assoc, mul_comm (∏ e ∈ S₁, _), mul_assoc, ← Finset.prod_union hdisj,
    hunion, hprod_ψ, hS2_card]
  rcases hn_even with ⟨m, hm⟩
  have hodd : Odd (n - 1) := ⟨m - 1, by omega⟩
  rw [hodd.neg_one_pow, neg_one_mul]

private lemma prod_offDiag_eq_vandermonde_sq {K : Type*} [CommRing K] {n : ℕ}
    (h4 : 4 ∣ n) (r : ℕ → K) :
    (∏ i : Fin n, ∏ j ∈ Finset.univ.erase i, (r i.val - r j.val)) =
      (∏ e ∈ (Finset.univ : Finset (Fin n × Fin n)).filter (fun e => e.1 < e.2),
        (r e.2.val - r e.1.val)) ^ 2 := by
  classical
  let S : Finset (Fin n × Fin n) := (Finset.univ : Finset (Fin n × Fin n)).filter (fun e => e.1 < e.2)
  let δ : K := ∏ e ∈ S, (r e.2.val - r e.1.val)
  change (∏ i : Fin n, ∏ j ∈ Finset.univ.erase i, (r i.val - r j.val)) = δ ^ 2
  let S' : Finset (Fin n × Fin n) := S.image Prod.swap
  have hdisj : Disjoint S S' := by
    rw [Finset.disjoint_left]
    intro e he1 he2
    rcases Finset.mem_image.mp he2 with ⟨e', he', rfl⟩
    have h1' : e'.2 < e'.1 := (Finset.mem_filter.mp he1).2
    have h2' : e'.1 < e'.2 := (Finset.mem_filter.mp he').2
    exact lt_asymm h1' h2'
  have hoff : (Finset.univ : Finset (Fin n)).offDiag = S ∪ S' := by
    ext ⟨a, b⟩
    simp only [Finset.mem_offDiag, Finset.mem_univ, true_and, Finset.mem_union, S, S',
      Finset.mem_filter, Finset.mem_image, Prod.swap]
    constructor
    · intro hab
      rcases lt_or_gt_of_ne hab with h | h
      · exact Or.inl h
      · exact Or.inr ⟨(b, a), h, rfl⟩
    · rintro (h | ⟨⟨x, y⟩, hxy, heq⟩)
      · exact h.ne
      · cases heq; exact hxy.ne'
  have hdbl : (∏ i : Fin n, ∏ j ∈ Finset.univ.erase i, (r i.val - r j.val)) =
      ∏ e ∈ (Finset.univ : Finset (Fin n)).offDiag, (r e.1.val - r e.2.val) := by
    have hoff_bi : (Finset.univ : Finset (Fin n)).offDiag =
        Finset.univ.biUnion (fun i : Fin n => (Finset.univ.erase i).image (Prod.mk i)) := by
      ext ⟨a, b⟩
      simp only [Finset.mem_offDiag, Finset.mem_univ, true_and, Finset.mem_biUnion,
        Finset.mem_image, Finset.mem_erase]
      constructor
      · intro hab
        exact ⟨a, b, ⟨hab.symm, trivial⟩, rfl⟩
      · rintro ⟨i, j, ⟨hji, _⟩, heq⟩
        rcases Prod.mk.inj heq with ⟨rfl, rfl⟩
        exact hji.symm
    rw [hoff_bi, Finset.prod_biUnion]
    · refine Finset.prod_congr rfl ?_
      intro i _
      rw [Finset.prod_image (fun _ _ _ _ h => (Prod.mk.inj h).2)]
    · intro i _ j _ hij
      change Disjoint ((Finset.univ.erase i).image (Prod.mk i))
        ((Finset.univ.erase j).image (Prod.mk j))
      rw [Finset.disjoint_left]
      intro e he1 he2
      rcases Finset.mem_image.mp he1 with ⟨_, _, rfl⟩
      rcases Finset.mem_image.mp he2 with ⟨_, _, h2⟩
      exact hij (Prod.mk.inj h2).1.symm
  have hS_prod : ∏ e ∈ S, (r e.1.val - r e.2.val) = (-1 : K) ^ S.card * δ := by
    dsimp only [δ]
    rw [← Finset.prod_const, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl ?_
    intro e _
    ring
  have hS'_prod : ∏ e ∈ S', (r e.1.val - r e.2.val) = δ := by
    dsimp only [S', δ]
    rw [Finset.prod_image (fun _ _ _ _ h => Prod.swap_injective h)]
    rfl
  have hScard_even : Even S.card := by
    have hpair : 2 * S.card = n * (n - 1) := by
      have hcard_off : ((Finset.univ : Finset (Fin n)).offDiag).card = n * (n - 1) := by
        rw [Finset.offDiag_card, Finset.card_fin, ← Nat.mul_sub_one]
      rw [hoff, Finset.card_union_of_disjoint hdisj,
        Finset.card_image_of_injective S Prod.swap_injective] at hcard_off
      omega
    rcases h4 with ⟨t, rfl⟩
    refine ⟨t * (4 * t - 1), ?_⟩
    have : 4 * t * (4 * t - 1) = 4 * (t * (4 * t - 1)) := by ring
    omega
  rw [hdbl, hoff, Finset.prod_union hdisj, hS_prod, hS'_prod, hScard_even.neg_one_pow,
    one_mul, sq]

private lemma contradiction_in_field {p k : ℕ} [Fact p.Prime] {K : Type*} [Field K] [CharP K p]
    [Fintype K] (φ : ZMod p →+* K) (α : K) (hpodd : p ≠ 2) (hk : 0 < k)
    (hndvd1 : ¬ p ∣ 8 * k * (k + 1) + 1) (hndvd2 : ¬ p ∣ 8 * k * (k + 1) + 2)
    (hcardK : Fintype.card K = p ^ (8 * k * (k + 1)))
    (hroot : (((polyS (8 * k * (k + 1))).map (Int.castRingHom (ZMod p))).map φ).eval α = 0)
    (hgen : ∀ x : K, ∃ q : (ZMod p)[X], x = (q.map φ).eval α) : False := by
  classical
  set n := 8 * k * (k + 1) with hn_def
  set m := 4 * k * (k + 1) with hm_def
  have hn2m : n = 2 * m := by
    rw [hn_def, hm_def]
    ring
  have hm8 : 8 ≤ m := by nlinarith
  have hn16 : 16 ≤ n := by omega
  have hn_pos : 0 < n := by omega
  have hp : p.Prime := Fact.out
  have hp2 : 2 < p := by
    have := hp.two_le
    omega
  let f : (ZMod p)[X] := (polyS n).map (Int.castRingHom (ZMod p))
  have hfdeg : f.natDegree = n := natDegree_polyS_map_eq p n hndvd1
  have hflc : f.leadingCoeff = ((n + 1 : ℕ) : ZMod p) := leadingCoeff_polyS_map p n hndvd1
  let F : K[X] := f.map φ
  -- Conjugates r i = α ^ (p ^ i)
  let r : ℕ → K := fun i => α ^ (p ^ i)
  have hr_root : ∀ i : ℕ, F.eval (r i) = 0 := by
    intro i
    dsimp only [F, r]
    rw [eval_map_pow_char_pow φ f α i, hroot, zero_pow (pow_ne_zero i hp.ne_zero)]
  have hpow_card : ∀ x : K, x ^ (p ^ n) = x := by
    intro x
    by_cases hx : x = 0
    · rw [hx, zero_pow (pow_ne_zero n hp.ne_zero)]
    · have hcardU : Fintype.card Kˣ = p ^ n - 1 := by
        rw [Fintype.card_units, hcardK]
      let u : Kˣ := Units.mk0 x hx
      have hu : u ^ (p ^ n - 1) = 1 := by
        rw [← hcardU]
        exact pow_card_eq_one
      have hxu : x ^ (p ^ n - 1) = 1 := by
        have := congrArg (fun v : Kˣ => (v : K)) hu
        simpa [u] using this
      have hpn1 : 1 ≤ p ^ n := Nat.one_le_pow n p hp.pos
      calc x ^ (p ^ n) = x ^ (p ^ n - 1 + 1) := by rw [Nat.sub_add_cancel hpn1]
        _ = x ^ (p ^ n - 1) * x := by rw [pow_succ]
        _ = x := by rw [hxu, one_mul]
  have hr_n : r n = r 0 := by
    dsimp only [r]
    rw [pow_zero, pow_one]
    exact hpow_card α
  -- Injectivity of r on Fin n
  have hr_lt_ne : ∀ a b : Fin n, a.val < b.val → r a.val ≠ r b.val := by
    intro a b hlt hij
    let d := b.val - a.val
    have hd_pos : 0 < d := by omega
    have hd_lt : d < n := by
      have := b.isLt
      omega
    have hαd : α ^ (p ^ d) = α := by
      have hpow_eq : (α ^ (p ^ d)) ^ (p ^ a.val) = α ^ (p ^ a.val) := by
        rw [← pow_mul, ← pow_add, show d + a.val = b.val by omega]
        exact hij.symm
      have hiter : ∀ t : ℕ, ∀ x y : K, x ^ (p ^ t) = y ^ (p ^ t) → x = y := by
        intro t
        induction t with
        | zero => intro x y h; simpa using h
        | succ t ih =>
          intro x y h
          apply ih
          rw [pow_succ, pow_mul, pow_mul] at h
          exact frobenius_inj K p h
      exact hiter a.val (α ^ (p ^ d)) α hpow_eq
    have hall : ∀ x : K, x ^ (p ^ d) = x := by
      intro x
      obtain ⟨q, rfl⟩ := hgen x
      rw [← eval_map_pow_char_pow φ q α d, hαd]
    let g : K[X] := X ^ (p ^ d) - X
    have hpd2 : 2 ≤ p ^ d := by
      calc 2 ≤ p := hp.two_le
        _ = p ^ 1 := (pow_one p).symm
        _ ≤ p ^ d := Nat.pow_le_pow_right hp.pos hd_pos
    have hgdeg : g.natDegree = p ^ d := by
      dsimp only [g]
      rw [Polynomial.natDegree_sub_eq_left_of_natDegree_lt]
      · exact Polynomial.natDegree_X_pow (p ^ d)
      · rw [Polynomial.natDegree_X, Polynomial.natDegree_X_pow]
        omega
    have hgne : g ≠ 0 := by
      intro h0
      rw [h0, Polynomial.natDegree_zero] at hgdeg
      omega
    have hsub : (Finset.univ : Finset K).val ≤ g.roots := by
      rw [Multiset.le_iff_subset (Finset.univ : Finset K).nodup]
      intro x _
      rw [Polynomial.mem_roots hgne, Polynomial.IsRoot.def]
      simp [g, hall x]
    have hcard_le : Fintype.card K ≤ p ^ d := by
      calc Fintype.card K = (Finset.univ : Finset K).val.card := rfl
        _ ≤ g.roots.card := Multiset.card_le_card hsub
        _ ≤ g.natDegree := Polynomial.card_roots' g
        _ = p ^ d := hgdeg
    rw [hcardK] at hcard_le
    have hlt_pow : p ^ d < p ^ n := Nat.pow_lt_pow_right hp.one_lt hd_lt
    omega
  have hr_inj : Function.Injective (fun i : Fin n => r i.val) := by
    intro i j hij
    by_contra hne
    rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hne) with hlt | hlt
    · exact hr_lt_ne i j hlt hij
    · exact hr_lt_ne j i hlt hij.symm
  -- Factorization F = C c * ∏ i : Fin n, (X - C (r i))
  let c : K := φ ((n + 1 : ℕ) : ZMod p)
  let d : K := φ ((n + 2 : ℕ) : ZMod p)
  have hc_ne : c ≠ 0 := by
    intro h0
    have h0' : φ ((n + 1 : ℕ) : ZMod p) = φ 0 := by rw [map_zero]; exact h0
    exact hndvd1 ((ZMod.natCast_eq_zero_iff (n + 1) p).mp (φ.injective h0'))
  have hd_ne : d ≠ 0 := by
    intro h0
    have h0' : φ ((n + 2 : ℕ) : ZMod p) = φ 0 := by rw [map_zero]; exact h0
    exact hndvd2 ((ZMod.natCast_eq_zero_iff (n + 2) p).mp (φ.injective h0'))
  have hFdeg : F.natDegree = n := by
    dsimp only [F]
    rw [Polynomial.natDegree_map_eq_of_injective φ.injective, hfdeg]
  have hFlc : F.leadingCoeff = c := by
    dsimp only [F, c]
    rw [Polynomial.leadingCoeff_map_of_injective φ.injective, hflc]
  have hprod_dvd : (∏ i : Fin n, (X - C (r i.val))) ∣ F := by
    apply Finset.prod_dvd_of_coprime
    · intro i _ j _ hij
      exact Polynomial.pairwise_coprime_X_sub_C hr_inj hij
    · intro i _
      exact Polynomial.dvd_iff_isRoot.mpr (hr_root i.val)
  have hprod_monic : (∏ i : Fin n, (X - C (r i.val))).Monic :=
    Polynomial.monic_prod_of_monic _ _ (fun i _ => Polynomial.monic_X_sub_C _)
  have hprod_deg : (∏ i : Fin n, (X - C (r i.val))).natDegree = n := by
    rw [Polynomial.natDegree_prod_of_monic _ _ (fun i _ => Polynomial.monic_X_sub_C _)]
    simp
  have hF_fac : F = C c * ∏ i : Fin n, (X - C (r i.val)) := by
    obtain ⟨q, hq⟩ := hprod_dvd
    have hq_ne : q ≠ 0 := by
      intro h0
      rw [h0, mul_zero] at hq
      have : F.natDegree = 0 := by rw [hq, Polynomial.natDegree_zero]
      omega
    have hq_deg : q.natDegree = 0 := by
      have h1 := congrArg Polynomial.natDegree hq
      rw [hFdeg, Polynomial.natDegree_mul hprod_monic.ne_zero hq_ne, hprod_deg] at h1
      omega
    have hq_eq : q = C q.leadingCoeff := by
      rw [Polynomial.leadingCoeff, hq_deg]
      exact Polynomial.eq_C_of_natDegree_eq_zero hq_deg
    have hqlc : q.leadingCoeff = c := by
      have h1 := congrArg Polynomial.leadingCoeff hq
      rw [hFlc, Polynomial.leadingCoeff_mul, hprod_monic.leadingCoeff, one_mul] at h1
      exact h1.symm
    rw [hq, hq_eq, hqlc, mul_comm]
  -- Vandermonde product δ
  let S : Finset (Fin n × Fin n) := (Finset.univ : Finset (Fin n × Fin n)).filter (fun e => e.1 < e.2)
  let δ : K := ∏ e ∈ S, (r e.2.val - r e.1.val)
  have hδ_ne : δ ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro e he
    have hlt : e.1 < e.2 := (Finset.mem_filter.mp he).2
    exact sub_ne_zero.mpr fun heq => hlt.ne' (hr_inj heq)
  have hδ_pow : δ ^ p = -δ :=
    vandermonde_pow_char hn_pos ⟨m, by omega⟩ r
      (fun i => by dsimp only [r]; rw [← pow_mul, ← pow_succ]) hr_n
  -- Evaluate ∏ i, F.derivative.eval (r i) via the factorization
  have hderiv_at : ∀ i : Fin n, F.derivative.eval (r i.val) =
      c * ∏ j ∈ Finset.univ.erase i, (r i.val - r j.val) := by
    intro i
    have hsplit : (∏ j : Fin n, (X - C (r j.val))) =
        (X - C (r i.val)) * ∏ j ∈ Finset.univ.erase i, (X - C (r j.val)) :=
      (Finset.mul_prod_erase Finset.univ (fun j : Fin n => (X - C (r j.val)))
        (Finset.mem_univ i)).symm
    rw [hF_fac, hsplit, Polynomial.derivative_mul, Polynomial.derivative_C, zero_mul, zero_add,
      Polynomial.derivative_mul, Polynomial.derivative_sub, Polynomial.derivative_X,
      Polynomial.derivative_C, sub_zero, one_mul, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_X,
      Polynomial.eval_C, sub_self, zero_mul, add_zero, Polynomial.eval_prod]
    refine congrArg (c * ·) (Finset.prod_congr rfl ?_)
    intro j _
    simp
  have hprod_deriv : ∏ i : Fin n, F.derivative.eval (r i.val) = c ^ n * δ ^ 2 := by
    have h1 : ∏ i : Fin n, F.derivative.eval (r i.val) =
        c ^ n * ∏ i : Fin n, ∏ j ∈ Finset.univ.erase i, (r i.val - r j.val) := by
      calc ∏ i : Fin n, F.derivative.eval (r i.val)
          = ∏ i : Fin n, (c * ∏ j ∈ Finset.univ.erase i, (r i.val - r j.val)) :=
            Finset.prod_congr rfl (fun i _ => hderiv_at i)
        _ = (∏ _i : Fin n, c) * ∏ i : Fin n, ∏ j ∈ Finset.univ.erase i, (r i.val - r j.val) :=
            Finset.prod_mul_distrib
        _ = c ^ n * _ := by simp
    rw [h1, prod_offDiag_eq_vandermonde_sq ⟨2 * k * (k + 1), by rw [hn_def]; ring⟩ r]
  -- Evaluate ∏ i, r i and ∏ i, (r i - 1)
  have hF0 : F.eval 0 = 1 := by
    dsimp only [F, f]
    rw [Polynomial.eval_map, Polynomial.eval₂_map]
    unfold polyS
    rw [Polynomial.eval₂_finsetSum, Finset.sum_eq_single 0]
    · simp
    · intro j _ hj0
      simp [zero_pow hj0]
    · intro hmem
      exact absurd (Finset.mem_range.mpr (by omega)) hmem
  have hprod_r : c * ∏ i : Fin n, r i.val = 1 := by
    have h0 := hF0
    rw [hF_fac, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_prod] at h0
    have hneg : (∏ i : Fin n, (X - C (r i.val)).eval 0) = (-1 : K) ^ n * ∏ i : Fin n, r i.val := by
      calc ∏ i : Fin n, (X - C (r i.val)).eval 0
          = ∏ i : Fin n, ((-1 : K) * r i.val) :=
            Finset.prod_congr rfl (fun i _ => by simp)
        _ = (∏ _i : Fin n, (-1 : K)) * ∏ i : Fin n, r i.val := Finset.prod_mul_distrib
        _ = (-1 : K) ^ n * ∏ i : Fin n, r i.val := by simp
    rw [hneg, (show Even n from ⟨m, by omega⟩).neg_one_pow, one_mul] at h0
    exact h0
  have h2_ne : (2 : K) ≠ 0 := by
    intro h0
    have h0' : φ (2 : ZMod p) = φ 0 := by
      rw [map_ofNat, map_zero]
      exact h0
    have hd : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp (by simpa using φ.injective h0')
    have := Nat.le_of_dvd (by omega) hd
    omega
  have hF_deriv_id : 2 * F + (X - 1 : K[X]) * F.derivative = C (c * d) * X ^ n := by
    have hid := congrArg (Polynomial.map (φ.comp (Int.castRingHom (ZMod p))))
      (two_mul_polyS_add_sub_one_mul_deriv n)
    have hFmap : (polyS n).map (φ.comp (Int.castRingHom (ZMod p))) = F := by
      dsimp only [F, f]
      rw [Polynomial.map_map]
    simp only [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_sub, Polynomial.map_ofNat,
      Polynomial.map_X, Polynomial.map_one, Polynomial.map_C, Polynomial.map_pow] at hid
    rw [← Polynomial.derivative_map, hFmap] at hid
    convert hid using 2
    congr 1
    dsimp only [c, d]
    simp [map_mul, map_add, map_ofNat]
  have h2F1 : 2 * F.eval 1 = c * d := by
    have h := congrArg (Polynomial.eval (1 : K)) hF_deriv_id
    simp at h
    exact h
  have hprod_sub1 : 2 * ∏ i : Fin n, (r i.val - 1) = d := by
    have h1 : F.eval 1 = c * ∏ i : Fin n, (r i.val - 1) := by
      rw [hF_fac, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_prod]
      congr 1
      have hneg : (∏ i : Fin n, (X - C (r i.val)).eval 1) =
          (-1 : K) ^ n * ∏ i : Fin n, (r i.val - 1) := by
        calc ∏ i : Fin n, (X - C (r i.val)).eval 1
            = ∏ i : Fin n, ((-1 : K) * (r i.val - 1)) :=
              Finset.prod_congr rfl (fun i _ => by simp)
          _ = (∏ _i : Fin n, (-1 : K)) * ∏ i : Fin n, (r i.val - 1) := Finset.prod_mul_distrib
          _ = (-1 : K) ^ n * ∏ i : Fin n, (r i.val - 1) := by simp
      rw [hneg, (show Even n from ⟨m, by omega⟩).neg_one_pow, one_mul]
    rw [h1] at h2F1
    have hmul : c * (2 * ∏ i : Fin n, (r i.val - 1)) = c * d := by linear_combination h2F1
    exact mul_left_cancel₀ hc_ne hmul
  -- Multiply the derivative identity at each r i
  have hkey_each : ∀ i : Fin n, (r i.val - 1) * F.derivative.eval (r i.val) =
      c * d * (r i.val) ^ n := by
    intro i
    have h := congrArg (Polynomial.eval (r i.val)) hF_deriv_id
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_ofNat, Polynomial.eval_sub,
      Polynomial.eval_X, Polynomial.eval_one, Polynomial.eval_C, Polynomial.eval_pow,
      hr_root i.val, mul_zero, zero_add] at h
    exact h
  have hkey_prod : (∏ i : Fin n, (r i.val - 1)) * (∏ i : Fin n, F.derivative.eval (r i.val)) =
      (c * d) ^ n * (∏ i : Fin n, r i.val) ^ n := by
    rw [← Finset.prod_mul_distrib]
    calc ∏ i : Fin n, (r i.val - 1) * F.derivative.eval (r i.val)
        = ∏ i : Fin n, (c * d * (r i.val) ^ n) :=
          Finset.prod_congr rfl (fun i _ => hkey_each i)
      _ = (∏ _i : Fin n, (c * d)) * ∏ i : Fin n, (r i.val) ^ n := Finset.prod_mul_distrib
      _ = (c * d) ^ n * (∏ i : Fin n, r i.val) ^ n := by
          rw [Finset.prod_const, Finset.card_fin, Finset.prod_pow]
  have hdisc_eq : c ^ n * δ ^ 2 = 2 * d ^ (n - 1) := by
    have h1 : d * (c ^ n * δ ^ 2) = 2 * d ^ n := by
      calc d * (c ^ n * δ ^ 2)
          = (2 * ∏ i : Fin n, (r i.val - 1)) * (∏ i : Fin n, F.derivative.eval (r i.val)) := by
            rw [hprod_sub1, hprod_deriv]
        _ = 2 * ((∏ i : Fin n, (r i.val - 1)) * (∏ i : Fin n, F.derivative.eval (r i.val))) := by
            ring
        _ = 2 * ((c * d) ^ n * (∏ i : Fin n, r i.val) ^ n) := by rw [hkey_prod]
        _ = 2 * (d ^ n * (c * ∏ i : Fin n, r i.val) ^ n) := by
            rw [mul_pow c d n, mul_pow c _ n]; ring
        _ = 2 * d ^ n := by rw [hprod_r, one_pow, mul_one]
    have h2 : d * (c ^ n * δ ^ 2) = d * (2 * d ^ (n - 1)) := by
      rw [h1]
      have : d ^ n = d * d ^ (n - 1) := by
        rw [← pow_succ', Nat.sub_add_cancel (by omega)]
      rw [this]
      ring
    exact mul_left_cancel₀ hd_ne h2
  -- Show δ ^ 2 = (φ u) ^ 2 for u ∈ ZMod p
  let u : ZMod p :=
    ((4 * k + 2 : ℕ) : ZMod p) * ((n + 2 : ℕ) : ZMod p) ^ (m - 1) *
      (((n + 1 : ℕ) : ZMod p) ^ m)⁻¹
  have h2d_sq : 2 * d = (φ ((4 * k + 2 : ℕ) : ZMod p)) ^ 2 := by
    have hnat : 2 * (n + 2) = (4 * k + 2) ^ 2 := by
      rw [hn_def]
      ring
    have hcast : (2 : K) * d = φ (((2 * (n + 2) : ℕ) : ZMod p)) := by
      dsimp only [d]
      rw [Nat.cast_mul, map_mul, Nat.cast_ofNat, map_ofNat]
    rw [hcast, hnat, Nat.cast_pow, map_pow]
  have hδ_sq : δ ^ 2 = (φ u) ^ 2 := by
    have hcm_ne : c ^ m ≠ 0 := pow_ne_zero m hc_ne
    have hcm_sq : (c ^ m) ^ 2 * δ ^ 2 = (φ ((4 * k + 2 : ℕ) : ZMod p) * d ^ (m - 1)) ^ 2 := by
      calc (c ^ m) ^ 2 * δ ^ 2
          = c ^ n * δ ^ 2 := by rw [← pow_mul, show m * 2 = n by omega]
        _ = 2 * d ^ (n - 1) := hdisc_eq
        _ = (2 * d) * (d ^ (m - 1)) ^ 2 := by
            rw [← pow_mul, mul_assoc, ← pow_succ', show (m - 1) * 2 + 1 = n - 1 by omega]
        _ = (φ ((4 * k + 2 : ℕ) : ZMod p) * d ^ (m - 1)) ^ 2 := by
            rw [h2d_sq, mul_pow]
    have hφu : φ u = φ ((4 * k + 2 : ℕ) : ZMod p) * d ^ (m - 1) * (c ^ m)⁻¹ := by
      dsimp only [u, c, d]
      rw [map_mul, map_mul, map_inv₀, map_pow, map_pow]
    rw [hφu, mul_pow, inv_pow]
    have hcm2_ne : (c ^ m) ^ 2 ≠ 0 := pow_ne_zero 2 hcm_ne
    symm
    rw [mul_inv_eq_iff_eq_mul₀ hcm2_ne, mul_comm (δ ^ 2)]
    exact hcm_sq.symm
  -- Contradiction: δ = ±φ u implies δ ^ p = δ, contradicting δ ^ p = -δ
  have hφ_fix : ∀ x : ZMod p, (φ x) ^ p = φ x := fun x => by
    rw [← map_pow φ x p, ZMod.pow_card]
  have hδ_fix : δ ^ p = δ := by
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp hδ_sq with hpos | hneg
    · rw [hpos, hφ_fix u]
    · rw [hneg, (hp.odd_of_ne_two hpodd).neg_pow, hφ_fix u]
  have h2δ : (2 : K) * δ = 0 := by
    rw [two_mul, add_eq_zero_iff_eq_neg]
    exact hδ_fix.symm.trans hδ_pow
  rcases mul_eq_zero.mp h2δ with h20 | hδ0
  · exact h2_ne h20
  · exact hδ_ne hδ0

private lemma case_p_coprime (p k : ℕ) [Fact p.Prime] (hpodd : p ≠ 2) (hk : 0 < k)
    (hndvd1 : ¬ p ∣ 8 * k * (k + 1) + 1) (hndvd2 : ¬ p ∣ 8 * k * (k + 1) + 2) :
    ¬ Irreducible ((polyS (8 * k * (k + 1))).map (Int.castRingHom (ZMod p))) := by
  intro hirr
  let n := 8 * k * (k + 1)
  let f : (ZMod p)[X] := (polyS n).map (Int.castRingHom (ZMod p))
  have hfdeg : f.natDegree = n := natDegree_polyS_map_eq p n hndvd1
  have : Fact (Irreducible f) := ⟨hirr⟩
  let K := AdjoinRoot f
  let φ : ZMod p →+* K := AdjoinRoot.of f
  have : CharP K p := charP_of_injective_ringHom φ.injective p
  let pb := AdjoinRoot.powerBasis hirr.ne_zero
  let : Fintype K := Fintype.ofEquiv (Fin pb.dim → ZMod p) pb.basis.equivFun.symm
  have hcardK : Fintype.card K = p ^ n := by
    calc Fintype.card K = Fintype.card (Fin pb.dim → ZMod p) :=
          Fintype.card_congr pb.basis.equivFun
      _ = (Fintype.card (ZMod p)) ^ pb.dim := by simp
      _ = p ^ n := by rw [ZMod.card, AdjoinRoot.powerBasis_dim, hfdeg]
  have hroot : (f.map φ).eval (AdjoinRoot.root f) = 0 := by
    rw [Polynomial.eval_map]
    exact AdjoinRoot.eval₂_root f
  have hgen : ∀ x : K, ∃ q : (ZMod p)[X], x = (q.map φ).eval (AdjoinRoot.root f) := by
    intro x
    obtain ⟨q, rfl⟩ := AdjoinRoot.mk_surjective x
    refine ⟨q, ?_⟩
    rw [Polynomial.eval_map, ← AdjoinRoot.aeval_eq, Polynomial.aeval_def]
    rfl
  exact contradiction_in_field φ (AdjoinRoot.root f) hpodd hk hndvd1 hndvd2 hcardK hroot hgen

end OMA.Proof_OeisA217785_conjecture_4_R1_H2

theorem OMA.solution : OMA.R_OeisA217785_conjecture_4_R1.H2 := by
  rintro n _ ⟨k, hk, rfl⟩ p hp
  have : Fact p.Prime := ⟨hp⟩
  by_cases hp2 : p = 2
  · subst hp2
    have hm : 1 ≤ 4 * k * (k + 1) := by nlinarith
    have heq : 8 * k * (k + 1) = 2 * (4 * k * (k + 1)) := by ring
    rw [heq]
    exact OMA.Proof_OeisA217785_conjecture_4_R1_H2.case_p_eq_two (4 * k * (k + 1)) hm
  · by_cases hdvd1 : p ∣ 8 * k * (k + 1) + 1
    · exact OMA.Proof_OeisA217785_conjecture_4_R1_H2.case_p_dvd_succ p (8 * k * (k + 1)) hp2
        (by nlinarith) hdvd1
    · by_cases hdvd2 : p ∣ 8 * k * (k + 1) + 2
      · exact OMA.Proof_OeisA217785_conjecture_4_R1_H2.case_p_dvd_add_two p (8 * k * (k + 1)) hp2
          (by nlinarith) hdvd1 hdvd2
      · exact OMA.Proof_OeisA217785_conjecture_4_R1_H2.case_p_coprime p k hp2 hk hdvd1 hdvd2
