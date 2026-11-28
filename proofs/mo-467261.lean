import OMAStatements.S_mo_467261
import Mathlib

-- Problem: Monotonicity of ratio of symmetric polynomials (MathOverflow 467261).
-- Proof outline: write h_l(1^(n-t), x^t) as an explicit polynomial in x, derive the
-- three-term recurrence in l and the identity (x-1) d/dx h_l = l h_l - (n+l-1) h_(l-1)
-- (as in the MathOverflow answer to the question). Then the ratios R_l(t) = h_(l+1)/h_l
-- are positive, strictly increasing and discretely concave in t by induction on l, and
-- the AM-HM inequality gives the discrete strict convexity of h_(l-1)/h_l in t, which is
-- the sign of the logarithmic derivative of the ratio.

open MvPolynomial Polynomial Finset

namespace M467


lemma eval_prod_X {σ : Type*} (w : σ → ℝ) (s : Multiset σ) :
    MvPolynomial.eval w (s.map MvPolynomial.X).prod = (s.map w).prod := by
  rw [map_multiset_prod, Multiset.map_map]
  simp

lemma eval_hsymm {σ : Type*} [Fintype σ] [DecidableEq σ] (w : σ → ℝ) (k : ℕ) :
    MvPolynomial.eval w (hsymm σ ℝ k) = ∑ s : Sym σ k, ((s : Multiset σ).map w).prod := by
  simp only [hsymm, map_sum, eval_prod_X]
  rfl

lemma hsymm_option {α : Type*} [Fintype α] [DecidableEq α] (w : Option α → ℝ) (k : ℕ) :
    MvPolynomial.eval w (hsymm (Option α) ℝ (k + 1)) =
      w none * MvPolynomial.eval w (hsymm (Option α) ℝ k) +
        MvPolynomial.eval (w ∘ some) (hsymm α ℝ (k + 1)) := by
  rw [eval_hsymm, eval_hsymm, eval_hsymm]
  rw [← (symOptionSuccEquiv (α := α) (n := k)).symm.sum_comp, Fintype.sum_sum_type, Finset.mul_sum]
  congr 1
  · refine Finset.sum_congr rfl fun s _ => ?_
    show ((SymOptionSuccEquiv.decode (Sum.inl s) : Multiset (Option α)).map w).prod = _
    rw [SymOptionSuccEquiv.decode_inl, Sym.coe_cons, Multiset.map_cons, Multiset.prod_cons]
  · refine Finset.sum_congr rfl fun s _ => ?_
    show ((SymOptionSuccEquiv.decode (Sum.inr s) : Multiset (Option α)).map w).prod = _
    simp [Multiset.map_map]

lemma hsymm_fin_zero (w : Fin 0 → ℝ) (k : ℕ) :
    MvPolynomial.eval w (hsymm (Fin 0) ℝ (k + 1)) = 0 := by
  rw [eval_hsymm]
  have : IsEmpty (Sym (Fin 0) (k + 1)) := by
    constructor
    intro s
    have := s.2
    have h : (s : Multiset (Fin 0)) = 0 := Multiset.eq_zero_of_forall_notMem (fun a => a.elim0)
    rw [Sym.val_eq_coe, h] at this
    simp at this
  simp

lemma hsymm_fin_succ (m : ℕ) (w : Fin (m + 1) → ℝ) (k : ℕ) :
    MvPolynomial.eval w (hsymm (Fin (m + 1)) ℝ k) =
      MvPolynomial.eval (w ∘ (finSuccEquiv m).symm) (hsymm (Option (Fin m)) ℝ k) := by
  rw [← rename_hsymm (Option (Fin m)) ℝ k (finSuccEquiv m).symm, eval_rename]


/-- coefficient of `x^j` in `h_l(1^a, x^t)` -/
noncomputable def cf (a t l j : ℕ) : ℝ :=
  if j ≤ l then ((a.multichoose (l - j) * t.multichoose j : ℕ) : ℝ) else 0

noncomputable def Q (a t l : ℕ) : ℝ[X] :=
  ∑ j ∈ range (l + 1), Polynomial.C (cf a t l j) * Polynomial.X ^ j

lemma coeff_Q (a t l j : ℕ) : (Q a t l).coeff j = cf a t l j := by
  simp only [Q, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul_X_pow]
  rw [Finset.sum_ite_eq (range (l + 1)) j (fun k => cf a t l k)]
  split_ifs with h
  · rfl
  · simp only [mem_range] at h
    simp [cf, show ¬ j ≤ l by omega]

lemma Q_zero (a t : ℕ) : Q a t 0 = 1 := by
  ext j
  rw [coeff_Q, Polynomial.coeff_one]
  rcases j with _ | j <;> simp [cf]

lemma Q_A (a t k : ℕ) : Q (a + 1) t (k + 1) = Q (a + 1) t k + Q a t (k + 1) := by
  ext j
  rw [Polynomial.coeff_add, coeff_Q, coeff_Q, coeff_Q]
  unfold cf
  by_cases h1 : j ≤ k
  · rw [if_pos (by omega), if_pos h1, if_pos (by omega)]
    rw [show k + 1 - j = (k - j) + 1 by omega, Nat.multichoose_succ_succ]
    push_cast; ring
  · by_cases h2 : j = k + 1
    · subst h2; simp
    · rw [if_neg (by omega), if_neg h1, if_neg (by omega)]; simp

lemma Q_B (a t k : ℕ) :
    Q a (t + 1) (k + 1) = Polynomial.X * Q a (t + 1) k + Q a t (k + 1) := by
  ext j
  rw [Polynomial.coeff_add]
  rcases j with _ | j
  · rw [Polynomial.coeff_X_mul_zero, coeff_Q, coeff_Q]
    simp [cf]
  · rw [Polynomial.coeff_X_mul, coeff_Q, coeff_Q, coeff_Q]
    unfold cf
    by_cases h1 : j ≤ k
    · rw [if_pos (by omega), if_pos h1, if_pos (by omega)]
      rw [show k + 1 - (j + 1) = k - j by omega, Nat.multichoose_succ_succ]
      push_cast; ring
    · rw [if_neg (by omega), if_neg h1, if_neg (by omega)]; simp


lemma mc_succ (a u : ℕ) : (u + 1) * a.multichoose (u + 1) = (a + u) * a.multichoose u := by
  rcases a with _ | a
  · rw [Nat.multichoose_zero_succ]
    rcases u with _ | u
    · simp
    · rw [Nat.multichoose_zero_succ]; simp
  · rw [Nat.multichoose_eq, Nat.multichoose_eq, show a + 1 + (u + 1) - 1 = a + u + 1 by omega,
      show a + 1 + u - 1 = a + u by omega]
    have := Nat.add_one_mul_choose_eq (a + u) u
    rw [show a + 1 + u = a + u + 1 by omega]
    linarith [this, mul_comm (Nat.choose (a + u + 1) (u + 1)) (u + 1)]

lemma mc_succ_real (a u : ℕ) :
    ((u : ℝ) + 1) * (a.multichoose (u + 1) : ℝ) = ((a : ℝ) + u) * (a.multichoose u : ℝ) := by
  exact_mod_cast mc_succ a u

lemma Q_rec (a t l : ℕ) :
    Polynomial.C ((l : ℝ) + 2) * Q a t (l + 2) =
      Polynomial.C ((l : ℝ) + 1 + a) * Q a t (l + 1) +
        Polynomial.C ((l : ℝ) + 1 + t) * (Polynomial.X * Q a t (l + 1)) -
          Polynomial.C ((a : ℝ) + t + l) * (Polynomial.X * Q a t l) := by
  ext j
  simp only [Polynomial.coeff_sub, Polynomial.coeff_add, Polynomial.coeff_C_mul]
  rcases j with _ | j
  · simp only [Polynomial.coeff_X_mul_zero, coeff_Q, cf]
    simp only [zero_le, if_true, Nat.sub_zero, Nat.multichoose_zero_right, mul_one, mul_zero,
      sub_zero, add_zero]
    have := mc_succ_real a (l + 1)
    push_cast at this ⊢
    linarith
  · simp only [Polynomial.coeff_X_mul, coeff_Q, cf]
    by_cases h1 : j ≤ l
    · rw [if_pos (by omega), if_pos (by omega), if_pos (by omega), if_pos h1]
      obtain ⟨u, rfl⟩ : ∃ u, l = j + u := ⟨l - j, by omega⟩
      rw [show j + u + 2 - (j + 1) = u + 1 by omega, show j + u + 1 - (j + 1) = u by omega,
        show j + u + 1 - j = u + 1 by omega, show j + u - j = u by omega]
      push_cast
      have R1 := mc_succ_real a u
      have R2 := mc_succ_real t j
      have hu : ((u : ℝ) + 1) ≠ 0 := by positivity
      have hj : ((j : ℝ) + 1) ≠ 0 := by positivity
      have e1 : (a.multichoose (u + 1) : ℝ) = ((a : ℝ) + u) * (a.multichoose u : ℝ) / ((u : ℝ) + 1) := by
        field_simp; linarith
      have e2 : (t.multichoose (j + 1) : ℝ) = ((t : ℝ) + j) * (t.multichoose j : ℝ) / ((j : ℝ) + 1) := by
        field_simp; linarith
      rw [e1, e2]
      field_simp
      ring
    · by_cases h2 : j = l + 1
      · subst h2
        rw [if_pos (by omega), if_neg (by omega), if_pos (by omega), if_neg (by omega)]
        rw [show l + 2 - (l + 1 + 1) = 0 by omega, show l + 1 - (l + 1) = 0 by omega]
        simp only [Nat.multichoose_zero_right, one_mul, mul_zero, add_zero, sub_zero]
        have := mc_succ_real t (l + 1)
        push_cast at this ⊢
        linarith
      · rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]
        simp

lemma Q_der (a t l : ℕ) :
    Polynomial.X * Polynomial.derivative (Q a t (l + 1)) - Polynomial.derivative (Q a t (l + 1)) =
      Polynomial.C ((l : ℝ) + 1) * Q a t (l + 1) - Polynomial.C ((a : ℝ) + t + l) * Q a t l := by
  ext j
  simp only [Polynomial.coeff_sub, Polynomial.coeff_C_mul, Polynomial.coeff_derivative]
  have hX : (Polynomial.X * Polynomial.derivative (Q a t (l + 1))).coeff j =
      (j : ℝ) * (Q a t (l + 1)).coeff j := by
    rcases j with _ | j
    · simp
    · rw [Polynomial.coeff_X_mul, Polynomial.coeff_derivative]; push_cast; ring
  rw [hX, coeff_Q, coeff_Q, coeff_Q]
  unfold cf
  by_cases h1 : j ≤ l
  · rw [if_pos (by omega), if_pos (by omega), if_pos h1]
    obtain ⟨u, rfl⟩ : ∃ u, l = j + u := ⟨l - j, by omega⟩
    rw [show j + u + 1 - j = u + 1 by omega, show j + u + 1 - (j + 1) = u by omega,
      show j + u - j = u by omega]
    push_cast
    have R1 := mc_succ_real a u
    have R2 := mc_succ_real t j
    linear_combination (-(t.multichoose j : ℝ)) * R1 - (a.multichoose u : ℝ) * R2
  · by_cases h2 : j = l + 1
    · subst h2
      rw [if_pos (by omega), if_neg (by omega), if_neg (by omega)]
      simp
    · rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]
      simp

lemma Q_nonneg_coeff (a t l j : ℕ) : 0 ≤ cf a t l j := by
  unfold cf; split_ifs <;> positivity

lemma Q_pos (a t l : ℕ) (ha : 1 ≤ a) (x : ℝ) (hx : 0 < x) : 0 < (Q a t l).eval x := by
  rw [Q, Polynomial.eval_finsetSum]
  rw [Finset.sum_range_succ']
  have h0 : 0 < Polynomial.eval x (Polynomial.C (cf a t l 0) * Polynomial.X ^ 0) := by
    simp only [pow_zero, mul_one, Polynomial.eval_C, cf, zero_le, if_true, Nat.sub_zero,
      Nat.multichoose_zero_right, mul_one]
    have : 0 < a.multichoose l := by
      rw [Nat.multichoose_eq]; exact Nat.choose_pos (by omega)
    exact_mod_cast this
  have h1 : 0 ≤ ∑ i ∈ range l, Polynomial.eval x (Polynomial.C (cf a t l (i + 1)) * Polynomial.X ^ (i + 1)) := by
    apply Finset.sum_nonneg; intro i _
    simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
    exact mul_nonneg (Q_nonneg_coeff _ _ _ _) (by positivity)
  linarith


/-- number of `false` labels -/
def cF {m : ℕ} (b : Fin m → Bool) : ℕ := ∑ j, if b j then 0 else 1
/-- number of `true` labels -/
def cT {m : ℕ} (b : Fin m → Bool) : ℕ := ∑ j, if b j then 1 else 0

lemma Q_zero_zero (k : ℕ) : Q 0 0 (k + 1) = 0 := by
  ext j
  rw [coeff_Q, Polynomial.coeff_zero]
  unfold cf
  split_ifs with h
  · rcases j with _ | j
    · simp
    · simp
  · rfl

lemma formula (x : ℝ) : ∀ (m : ℕ) (b : Fin m → Bool) (k : ℕ),
    MvPolynomial.eval (fun j => if b j then x else 1) (hsymm (Fin m) ℝ k) =
      (Q (cF b) (cT b) k).eval x := by
  intro m
  induction m with
  | zero =>
    intro b k
    have h1 : cF b = 0 := by simp [cF]
    have h2 : cT b = 0 := by simp [cT]
    rw [h1, h2]
    rcases k with _ | k
    · simp [hsymm_zero, Q_zero]
    · rw [hsymm_fin_zero, Q_zero_zero]; simp
  | succ m ih =>
    intro b k
    induction k with
    | zero => simp [hsymm_zero, Q_zero]
    | succ k ihk =>
      rw [hsymm_fin_succ, hsymm_option, ← hsymm_fin_succ, ihk]
      have hs : ((fun j => if b j then x else 1) ∘ (finSuccEquiv m).symm) ∘ some =
          (fun j => if (b ∘ Fin.succ) j then x else 1) := by
        funext j; simp
      rw [hs, ih]
      have hF : cF b = (if b 0 then 0 else 1) + cF (b ∘ Fin.succ) := by
        unfold cF; rw [Fin.sum_univ_succ]; rfl
      have hT : cT b = (if b 0 then 1 else 0) + cT (b ∘ Fin.succ) := by
        unfold cT; rw [Fin.sum_univ_succ]; rfl
      rw [hF, hT]
      simp only [Function.comp_apply, finSuccEquiv_symm_none]
      cases hb : b 0
      · simp only [Bool.false_eq_true, if_false, zero_add, one_mul]
        rw [add_comm 1, Q_A, Polynomial.eval_add]
      · simp only [if_true, zero_add]
        rw [add_comm 1, Q_B, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X]


noncomputable def H (n l t : ℕ) (x : ℝ) : ℝ := (Q (n - t) t l).eval x

lemma H_pos {n l t : ℕ} (ht : t + 1 ≤ n) {x : ℝ} (hx : 0 < x) : 0 < H n l t x :=
  Q_pos _ _ _ (by omega) x hx

lemma H_zero (n t : ℕ) (x : ℝ) : H n 0 t x = 1 := by simp [H, Q_zero]

lemma H_one {n t : ℕ} (ht : t ≤ n) (x : ℝ) : H n 1 t x = n + (x - 1) * t := by
  simp only [H, Q, Finset.sum_range_succ, Finset.sum_range_zero, cf, Polynomial.eval_add,
    Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  simp only [zero_le, if_true, le_refl, Nat.sub_zero, Nat.sub_self, Nat.multichoose_one_right,
    Nat.multichoose_zero_right, pow_zero, pow_one, mul_one, one_mul, zero_add]
  rw [Nat.cast_sub ht]
  simp only [Polynomial.eval_zero, zero_add]
  ring

lemma H_rec {n t : ℕ} (ht : t ≤ n) (l : ℕ) (x : ℝ) :
    ((l : ℝ) + 2) * H n (l + 2) t x =
      (((l : ℝ) + 1) * (1 + x) + n + (x - 1) * t) * H n (l + 1) t x -
        ((n : ℝ) + l) * x * H n l t x := by
  have := congrArg (Polynomial.eval x) (Q_rec (n - t) t l)
  simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_add, Polynomial.eval_sub,
    Polynomial.eval_X] at this
  simp only [H]
  rw [this, Nat.cast_sub ht]
  ring

lemma H_der {n t : ℕ} (ht : t ≤ n) (l : ℕ) (x : ℝ) :
    HasDerivAt (fun y => H n (l + 1) t y)
      ((Polynomial.derivative (Q (n - t) t (l + 1))).eval x) x ∧
    (x - 1) * (Polynomial.derivative (Q (n - t) t (l + 1))).eval x =
      ((l : ℝ) + 1) * H n (l + 1) t x - ((n : ℝ) + l) * H n l t x := by
  refine ⟨Polynomial.hasDerivAt _ x, ?_⟩
  have := congrArg (Polynomial.eval x) (Q_der (n - t) t l)
  simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_sub,
    Polynomial.eval_X] at this
  simp only [H]
  rw [Nat.cast_sub ht] at this
  have e : (((n : ℝ) - t) + t + l) = (n : ℝ) + l := by ring
  rw [e] at this
  linarith

lemma amhm {p q r : ℝ} (hp : 0 < p) (hq : 0 < q) (hpq : p + q ≤ 2 * r) :
    2 / r ≤ 1 / p + 1 / q := by
  have hr : 0 < r := by linarith
  rw [div_add_div _ _ hp.ne' hq.ne', div_le_div_iff₀ hr (by positivity)]
  nlinarith [sq_nonneg (p - q)]

lemma amhm_strict {p q r : ℝ} (hp : 0 < p) (hq : 0 < q) (hpq : p + q ≤ 2 * r) (hne : p < q) :
    2 / r < 1 / p + 1 / q := by
  have hr : 0 < r := by linarith
  rw [div_add_div _ _ hp.ne' hq.ne', div_lt_div_iff₀ hr (by positivity)]
  nlinarith [mul_pos (sub_pos.2 hne) (sub_pos.2 hne)]

lemma R_succ {n t : ℕ} (ht : t + 1 ≤ n) (l : ℕ) {x : ℝ} (hx : 0 < x) :
    H n (l + 2) t x / H n (l + 1) t x =
      ((((l : ℝ) + 1) * (1 + x) + n + (x - 1) * t) -
        ((n : ℝ) + l) * x / (H n (l + 1) t x / H n l t x)) / ((l : ℝ) + 2) := by
  have h1 := H_pos (l := l + 1) ht hx
  have h0 := H_pos (l := l) ht hx
  have hr := H_rec (n := n) (t := t) (by omega) l x
  field_simp
  linarith

lemma R_props {n : ℕ} (hn : 1 ≤ n) {x : ℝ} (hx : 1 < x) : ∀ l : ℕ,
    (∀ t, t + 2 ≤ n → H n (l + 1) t x / H n l t x < H n (l + 1) (t + 1) x / H n l (t + 1) x) ∧
    (∀ t, t + 3 ≤ n → H n (l + 1) t x / H n l t x + H n (l + 1) (t + 2) x / H n l (t + 2) x ≤
      2 * (H n (l + 1) (t + 1) x / H n l (t + 1) x)) := by
  have hx0 : 0 < x := by linarith
  intro l
  induction l with
  | zero =>
    refine ⟨fun t ht => ?_, fun t ht => ?_⟩
    · rw [H_one (by omega), H_one (by omega), H_zero, H_zero]
      push_cast
      nlinarith
    · rw [H_one (by omega), H_one (by omega), H_one (by omega), H_zero, H_zero, H_zero]
      push_cast
      linarith
  | succ l ih =>
    obtain ⟨ihm, ihc⟩ := ih
    have hβ : 0 < ((n : ℝ) + l) * x := by
      have : (1 : ℝ) ≤ n := by exact_mod_cast hn
      positivity
    refine ⟨fun t ht => ?_, fun t ht => ?_⟩
    · rw [R_succ (by omega) l hx0, R_succ (by omega) l hx0]
      apply div_lt_div_of_pos_right _ (by positivity)
      have hp : 0 < H n (l + 1) t x / H n l t x :=
        div_pos (H_pos (by omega) hx0) (H_pos (by omega) hx0)
      have := div_lt_div_of_pos_left hβ hp (ihm t ht)
      push_cast
      nlinarith
    · rw [R_succ (by omega) l hx0, R_succ (by omega) l hx0, R_succ (by omega) l hx0]
      have hp : 0 < H n (l + 1) t x / H n l t x :=
        div_pos (H_pos (by omega) hx0) (H_pos (by omega) hx0)
      have hq : 0 < H n (l + 1) (t + 2) x / H n l (t + 2) x :=
        div_pos (H_pos (by omega) hx0) (H_pos (by omega) hx0)
      have key := amhm hp hq (ihc t ht)
      set p := H n (l + 1) t x / H n l t x
      set q := H n (l + 1) (t + 2) x / H n l (t + 2) x
      set r := H n (l + 1) (t + 1) x / H n l (t + 1) x
      have hl : (0 : ℝ) < (l : ℝ) + 2 := by positivity
      rw [← add_div, ← mul_div_assoc, div_le_div_iff_of_pos_right hl]
      have e1 : ((n : ℝ) + l) * x / p = ((n : ℝ) + l) * x * (1 / p) := by ring
      have e2 : ((n : ℝ) + l) * x / q = ((n : ℝ) + l) * x * (1 / q) := by ring
      have e3 : ((n : ℝ) + l) * x / r = ((n : ℝ) + l) * x * (2 / r) / 2 := by ring
      rw [e1, e2, e3]
      push_cast
      nlinarith [mul_le_mul_of_nonneg_left key hβ.le]


lemma sum_range_ite (c : ℕ) : ∀ n : ℕ,
    (∑ j ∈ range n, (if c ≤ j then 0 else 1 : ℕ)) = min c n := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    split_ifs with h <;> omega

lemma cF_block (n c : ℕ) (hc : c ≤ n) :
    cF (fun j : Fin n => decide (c ≤ j.val)) = c := by
  unfold cF
  rw [Fin.sum_univ_eq_sum_range (fun j => if decide (c ≤ j) = true then 0 else 1) n]
  simp only [decide_eq_true_eq]
  rw [sum_range_ite]; omega

lemma cF_add_cT {m : ℕ} (b : Fin m → Bool) : cF b + cT b = m := by
  unfold cF cT
  rw [← Finset.sum_add_distrib]
  have : ∀ j, ((if b j = true then 0 else 1) + if b j = true then 1 else 0) = 1 := by
    intro j; cases b j <;> rfl
  simp only [this, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one]

lemma re_eq (n l t : ℕ) (ht : t ≤ n) (x : ℝ) :
    OMA.S_mo_467261.repeatedEvaluation n l t x = H n l t x := by
  unfold OMA.S_mo_467261.repeatedEvaluation H
  have hw : (fun j : Fin n => if j.val < n - t then (1 : ℝ) else x) =
      (fun j => if (fun j : Fin n => decide (n - t ≤ j.val)) j then x else 1) := by
    funext j
    by_cases h : j.val < n - t
    · have h' : ¬ (n - t ≤ j.val) := by omega
      simp only [h, if_true, h', decide_false, Bool.false_eq_true, if_false]
    · have h' : n - t ≤ j.val := by omega
      simp only [h, if_false, h', decide_true, if_true]
  rw [hw, formula]
  have h1 := cF_block n (n - t) (by omega)
  have h2 := cF_add_cT (fun j : Fin n => decide (n - t ≤ j.val))
  rw [h1] at h2 ⊢
  rw [show cT (fun j : Fin n => decide (n - t ≤ j.val)) = t by omega]

end M467

open M467 in
theorem OMA.solution : type_of% @OMA.S_mo_467261.main := by
  intro n ell i hn hell hi2 hin
  obtain ⟨l, rfl⟩ : ∃ l, ell = l + 1 := ⟨ell - 1, by omega⟩
  obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
  have hj : j + 3 ≤ n := by omega
  have hfun : (fun x : ℝ =>
      OMA.S_mo_467261.repeatedEvaluation n (l + 1) (j + 1) x ^ 2 /
        (OMA.S_mo_467261.repeatedEvaluation n (l + 1) (j + 1 + 1) x *
          OMA.S_mo_467261.repeatedEvaluation n (l + 1) (j + 1 - 1) x)) =
      fun x => H n (l + 1) (j + 1) x ^ 2 / (H n (l + 1) (j + 2) x * H n (l + 1) j x) := by
    funext x
    rw [re_eq _ _ _ (by omega), re_eq _ _ _ (by omega), re_eq _ _ _ (by omega)]
    rfl
  rw [hfun]
  -- derivative data
  set dA := fun x : ℝ => (Polynomial.derivative (Q (n - (j + 1)) (j + 1) (l + 1))).eval x
  set dB := fun x : ℝ => (Polynomial.derivative (Q (n - (j + 2)) (j + 2) (l + 1))).eval x
  set dC := fun x : ℝ => (Polynomial.derivative (Q (n - j) j (l + 1))).eval x
  have hder : ∀ x : ℝ, 1 < x → HasDerivAt
      (fun x => H n (l + 1) (j + 1) x ^ 2 / (H n (l + 1) (j + 2) x * H n (l + 1) j x))
      (((2 : ℕ) * H n (l + 1) (j + 1) x ^ (2 - 1) * dA x *
          (H n (l + 1) (j + 2) x * H n (l + 1) j x) -
        H n (l + 1) (j + 1) x ^ 2 *
          (dB x * H n (l + 1) j x + H n (l + 1) (j + 2) x * dC x)) /
        (H n (l + 1) (j + 2) x * H n (l + 1) j x) ^ 2) x := by
    intro x hx
    have hx0 : 0 < x := by linarith
    have hA := (H_der (n := n) (t := j + 1) (by omega) l x).1
    have hB := (H_der (n := n) (t := j + 2) (by omega) l x).1
    have hC := (H_der (n := n) (t := j) (by omega) l x).1
    exact (hA.pow 2).div (hB.mul hC)
      (mul_pos (H_pos (by omega) hx0) (H_pos (by omega) hx0)).ne'
  apply strictMonoOn_of_deriv_pos (convex_Ioi 1)
  · intro x hx
    exact (hder x hx).continuousAt.continuousWithinAt
  · intro x hx
    rw [interior_Ioi] at hx
    have hx1 : (1 : ℝ) < x := hx
    have hx0 : 0 < x := by linarith
    rw [(hder x hx1).deriv]
    have hA := H_pos (n := n) (l := l + 1) (t := j + 1) (by omega) hx0
    have hB := H_pos (n := n) (l := l + 1) (t := j + 2) (by omega) hx0
    have hC := H_pos (n := n) (l := l + 1) (t := j) (by omega) hx0
    have hA0 := H_pos (n := n) (l := l) (t := j + 1) (by omega) hx0
    have hB0 := H_pos (n := n) (l := l) (t := j + 2) (by omega) hx0
    have hC0 := H_pos (n := n) (l := l) (t := j) (by omega) hx0
    have eA := (H_der (n := n) (t := j + 1) (by omega) l x).2
    have eB := (H_der (n := n) (t := j + 2) (by omega) l x).2
    have eC := (H_der (n := n) (t := j) (by omega) l x).2
    obtain ⟨hm, hc⟩ := R_props (n := n) (by omega) hx1 l
    have m1 := hm j (by omega)
    have m2 := hm (j + 1) (by omega)
    have c1 := hc j (by omega)
    have key := amhm_strict (div_pos hC hC0) (div_pos hB hB0) c1 (by linarith)
    rw [one_div_div, one_div_div] at key
    -- key : 2 / (A / A0) < C0 / C + B0 / B
    set A := H n (l + 1) (j + 1) x
    set B := H n (l + 1) (j + 2) x
    set C := H n (l + 1) j x
    set A0 := H n l (j + 1) x
    set B0 := H n l (j + 2) x
    set C0 := H n l j x
    have key2 : 2 * A0 * B * C < A * B * C0 + A * C * B0 := by
      have e : 2 / (A / A0) = 2 * A0 / A := by field_simp
      rw [e, div_add_div _ _ hC.ne' hB.ne', div_lt_div_iff₀ hA (by positivity)] at key
      nlinarith [key]
    apply div_pos _ (by positivity)
    have hnum : (x - 1) * ((((2 : ℕ) : ℝ) * A ^ (2 - 1) * dA x * (B * C) -
        A ^ 2 * (dB x * C + B * dC x))) =
        ((n : ℝ) + l) * A * (A * B * C0 + A * C * B0 - 2 * A0 * B * C) := by
      simp only [Nat.cast_ofNat, show 2 - 1 = 1 from rfl, pow_one]
      linear_combination (2 * A * B * C) * eA - (A ^ 2 * C) * eB - (A ^ 2 * B) * eC
    have hpos : 0 < ((n : ℝ) + l) * A * (A * B * C0 + A * C * B0 - 2 * A0 * B * C) := by
      have : (0 : ℝ) < (n : ℝ) + l := by
        have : (4 : ℝ) ≤ n := by exact_mod_cast hn
        linarith [(Nat.cast_nonneg l : (0 : ℝ) ≤ l)]
      have h3 : 0 < A * B * C0 + A * C * B0 - 2 * A0 * B * C := by linarith
      positivity
    rw [← hnum] at hpos
    exact pos_of_mul_pos_right hpos (by linarith)
