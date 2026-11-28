import FormalConjectures.OEIS.«115257»
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Algebra.Polynomial.Eval.Coeff

open Polynomial OeisA115257
namespace OMA.R_OeisA115257_conjecture_R1

lemma even_pos (q : Bool) (x : ℚ) (m : ℕ) :
    0 < (if q then polyQ (2*m) else polyP (2*m)).eval x := by
  let b (k : ℕ) : ℚ := Nat.centralBinom k

  have b_nonneg (k : ℕ) : 0 ≤ b k := by
    simp only [b]
    positivity

  have b_succ (k : ℕ) :
      b (k+1) = (2*(2*(k:ℚ)+1)/((k:ℚ)+1))*b k := by
    have h : ((k:ℚ)+1)*b (k+1) = 2*(2*(k:ℚ)+1)*b k := by
      simp only [b]
      exact_mod_cast Nat.succ_mul_centralBinom_succ k
    field_simp
    nlinarith [h]

  let terms (q : Bool) (t : ℚ) (k : ℕ) : ℚ :=
    b k ^ 2 * t^k / (if q then (k:ℚ)+1 else 1)

  have terms_nonneg (q : Bool) (t : ℚ) (ht : 0 ≤ t) (k : ℕ) :
      0 ≤ terms q t k := by
    cases q <;> simp [terms] <;> positivity

  let ratio (q : Bool) (t : ℚ) (k : ℕ) : ℚ :=
    4*(2*(k:ℚ)+1)^2*t/((k:ℚ)+1) / (if q then (k:ℚ)+2 else (k:ℚ)+1)

  have ratio_nonneg (q : Bool) (t : ℚ) (ht : 0 ≤ t) (k : ℕ) :
      0 ≤ ratio q t k := by
    cases q <;> simp [ratio] <;> positivity

  have terms_succ (q : Bool) (t : ℚ) (k : ℕ) :
      terms q t (k+1) = ratio q t k * terms q t k := by
    cases q <;> simp [terms, ratio, b_succ, pow_succ, Nat.cast_add, Nat.cast_one]
    all_goals
      field_simp
      <;> ring

  have ratio_mono (q : Bool) (t : ℚ) (ht : 0 ≤ t) (k : ℕ) :
      ratio q t k ≤ ratio q t (k+1) := by
    cases q
    · simp only [ratio, Bool.false_eq_true, ↓reduceIte, Nat.cast_add, Nat.cast_one]
      rw [div_div, div_div]
      apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
      have hk : 0 ≤ (k:ℚ) := by positivity
      have h : 0 ≤ (4*(k:ℚ)^2 + 10*(k:ℚ) +5)*t := by positivity
      nlinarith
    · simp only [ratio, ↓reduceIte, Nat.cast_add, Nat.cast_one]
      rw [div_div, div_div]
      apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
      have h : 0 ≤ (8*(k:ℚ)+6)*((k:ℚ)+2)*t := by positivity
      nlinarith

  have terms_convex (q : Bool) (t : ℚ) (ht : 0 ≤ t) (k : ℕ) :
      2*terms q t (k+1) ≤ terms q t k + terms q t (k+2) := by
    have h1 := terms_succ q t k
    have h2 := terms_succ q t (k+1)
    have h3 := ratio_mono q t ht k
    have h4 := terms_nonneg q t ht k
    have h5 := terms_nonneg q t ht (k+1)
    have h6 := mul_le_mul_of_nonneg_right h3 h5
    rw [← h2] at h6
    have h7 : 0 ≤ (ratio q t k - 1)^2 * terms q t k :=
      mul_nonneg (sq_nonneg _) h4
    rw [h1] at h6
    rw [h1]
    nlinarith

  have even_alt_sum_aux (u : ℕ → ℚ) (hc : ∀ k, 2*u (k+1) ≤ u k+u (k+2)) (m : ℕ) :
      u 0 + u (2*m) ≤ 2 * ∑ k ∈ Finset.range (2*m+1), (-1:ℚ)^k*u k := by
    induction m with
    | zero => simp
              linarith
    | succ m ih =>
      have hr : 2*(m+1)+1 = (2*m+1)+1+1 := by omega
      rw [hr, Finset.sum_range_succ, Finset.sum_range_succ]
      rw [show 2*m+1+1 = 2*m+2 by omega,
          pow_add, pow_add, pow_mul]
      norm_num
      rw [show 2*(m+1) = 2*m+2 by omega]
      have h := hc (2*m)
      linarith

  have terms_zero (q : Bool) (t : ℚ) : terms q t 0 = 1 := by
    cases q <;> simp [terms, b, Nat.centralBinom]

  have even_alt_sum_pos (q : Bool) (t : ℚ) (ht : 0 ≤ t) (m : ℕ) :
      0 < ∑ k ∈ Finset.range (2*m+1), (-1:ℚ)^k * terms q t k := by
    have h := even_alt_sum_aux (terms q t) (terms_convex q t ht) m
    rw [terms_zero] at h
    have hn := terms_nonneg q t ht (2*m)
    linarith

  have eval_terms (q : Bool) (t : ℚ) (n : ℕ) :
      (if q then polyQ n else polyP n).eval t =
        ∑ k ∈ Finset.range (n+1), terms q t k := by
    cases q <;> simp [polyQ, polyP, terms, b, Polynomial.eval_finsetSum,
      Polynomial.eval_mul, Polynomial.eval_pow]
    · apply Finset.sum_congr rfl
      intro k hk
      rw [div_mul_eq_mul_div]

  have eval_neg_terms (q : Bool) (t : ℚ) (n : ℕ) :
      (if q then polyQ n else polyP n).eval (-t) =
        ∑ k ∈ Finset.range (n+1), (-1:ℚ)^k * terms q t k := by
    rw [eval_terms]
    apply Finset.sum_congr rfl
    intro k hk
    simp only [terms]
    rw [show -t = (-1:ℚ)*t by ring, mul_pow]
    ring

  have polyPQ_even_pos (q : Bool) (x : ℚ) (m : ℕ) :
      0 < (if q then polyQ (2*m) else polyP (2*m)).eval x := by
    by_cases hx : 0 ≤ x
    · rw [eval_terms]
      have h0 : (0:ℕ) ∈ Finset.range (2*m+1) := by simp
      calc
        0 < 1 := by norm_num
        _ = terms q x 0 := (terms_zero q x).symm
        _ ≤ _ := Finset.single_le_sum (fun k hk => terms_nonneg q x hx k) h0
    · rw [show x = -(-x) by ring, eval_neg_terms]
      exact even_alt_sum_pos q (-x) (by linarith) m

  exact polyPQ_even_pos q x m

lemma coeff_family (q : Bool) (n i : ℕ) :
    (if q then polyQ n else polyP n).coeff i =
      if i ≤ n then (Nat.centralBinom i : ℚ)^2 / (if q then (i:ℚ)+1 else 1) else 0 := by
  cases q
  · change (polyP n).coeff i = _
    rw [polyP, finsetSum_coeff]
    simp only [coeff_C_mul_X_pow, Finset.sum_ite_eq, Finset.mem_range, Nat.lt_succ_iff,
      Bool.false_eq_true, if_false, div_one]
  · change (polyQ n).coeff i = _
    rw [polyQ, finsetSum_coeff]
    simp only [coeff_C_mul_X_pow, Finset.sum_ite_eq, Finset.mem_range, Nat.lt_succ_iff, if_true]

lemma coeff_top (q : Bool) (n : ℕ) :
    (if q then polyQ n else polyP n).coeff n ≠ 0 := by
  rw [coeff_family, if_pos (le_refl n)]
  have hb : (Nat.centralBinom n : ℚ) ≠ 0 := by exact_mod_cast Nat.centralBinom_ne_zero n
  apply div_ne_zero (pow_ne_zero 2 hb)
  cases q <;> simp <;> positivity

lemma even_no_linear_factor (q : Bool) (m : ℕ) (g : Polynomial ℚ)
    (hd : g.natDegree = 1) : ¬ g ∣ (if q then polyQ (2*m) else polyP (2*m)) := by
  intro h
  have hn : g ≠ 0 := by intro hg; simp [hg] at hd
  have hdegree : g.degree = 1 := by rw [degree_eq_natDegree hn, hd]; rfl
  obtain ⟨x, hx⟩ := exists_root_of_degree_eq_one hdegree
  obtain ⟨f, hf⟩ := h
  have hzero : (if q then polyQ (2*m) else polyP (2*m)).eval x = 0 := by
    rw [hf, eval_mul, hx.eq_zero, zero_mul]
  have hpos := even_pos q (x : ℚ) m
  rw [hzero] at hpos
  exact (lt_irrefl 0) hpos

-- H1 asks only for exclusion of higher-degree possible proper factors.
def H1 : Prop := ∀ (q : Bool) (n : ℕ), 1 ≤ n →
  ∀ (g : Polynomial ℚ), g.Monic → 2 ≤ g.natDegree →
    g.natDegree ≤ (if q then polyQ n else polyP n).natDegree / 2 →
      ¬ g ∣ (if q then polyQ n else polyP n)

-- H2 isolates rational-root exclusion at odd degrees above one.
def H2 : Prop := ∀ (q : Bool) (n : ℕ), 3 ≤ n → Odd n →
  ∀ (x : ℚ), (if q then polyQ n else polyP n).eval x ≠ 0

lemma irreducible_aux (h1 : H1) (h2 : H2) (q : Bool) (n : ℕ) (hn : 1 ≤ n) :
    Irreducible (if q then polyQ n else polyP n) := by
  let p : Polynomial ℚ := if q then polyQ n else polyP n
  change Irreducible p
  have htop : p.coeff n ≠ 0 := coeff_top q n
  have hp0 : p ≠ 0 := by intro h; simp [h] at htop
  have hpn : n ≤ p.natDegree := le_natDegree_of_ne_zero htop
  have hpu : ¬ IsUnit p := by
    intro h; have hh := natDegree_eq_zero_of_isUnit h; omega
  by_cases hsmall : n = 1
  · subst n
    apply irreducible_of_degree_eq_one
    rw [degree_eq_natDegree hp0]
    have hh : p.natDegree ≤ 1 := by
      apply natDegree_le_iff_coeff_eq_zero.mpr
      intro i hi
      change (if q then polyQ 1 else polyP 1).coeff i = 0
      rw [coeff_family, if_neg (by omega)]
    have he : p.natDegree = 1 := by omega
    rw [he]
    rfl
  · rw [irreducible_iff_lt_natDegree_lt hp0 hpu]
    intro g hg hd hdiv
    have hdpos : 0 < g.natDegree := (Finset.mem_Ioc.mp hd).1
    have hdle : g.natDegree ≤ p.natDegree / 2 := (Finset.mem_Ioc.mp hd).2
    by_cases hlin : g.natDegree = 1
    · rcases Nat.even_or_odd n with he | ho
      · obtain ⟨m, hm⟩ := he
        have hnn : n = 2*m := by omega
        change g ∣ (if q then polyQ n else polyP n) at hdiv
        rw [hnn] at hdiv
        exact even_no_linear_factor q m g hlin hdiv
      · have hg0 : g ≠ 0 := hg.ne_zero
        have hd1 : g.degree = 1 := by rw [degree_eq_natDegree hg0, hlin]; rfl
        obtain ⟨x, hx⟩ := exists_root_of_degree_eq_one hd1
        obtain ⟨f, hf⟩ := hdiv
        have hz : p.eval x = 0 := by rw [hf, eval_mul, hx.eq_zero, zero_mul]
        have ho' := ho
        obtain ⟨k, hk⟩ := ho'
        exact h2 q n (by omega) ho x hz
    · exact h1 q n hn g hg (by omega) hdle hdiv

theorem main : H1 → H2 → type_of% @OeisA115257.conjecture := by
  intro h1 h2 n hn
  exact ⟨irreducible_aux h1 h2 false n hn, irreducible_aux h1 h2 true n hn⟩

end OMA.R_OeisA115257_conjecture_R1
