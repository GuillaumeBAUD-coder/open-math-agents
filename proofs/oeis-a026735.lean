import OMAStatements.S_oeis_a026735

/-!
OEIS A026735 (Clark Kimberling): a(n) = Sum_{k=0..floor(n/2)} T(n-k,k), T given by A026725.
Conjecture: G.f.:-1/2*(2*x^6-5*x^4+8*x^3+x-2+x*(x-1)*(x^2+x+1)*(1-4*x^3)^(1/2))/(x^6+4*x^3-1)/(x^2+x-1). - Maksym Voznyy (voznyy(AT)mail.ru), Aug 11 2009

Proof. With D(r) = T(2r+1, r), the entries that the extra term adds, induction on n gives the
explicit formula T(n, k) = C(n, k) + sum_r D(r) C(n-2r-3, k-r-1) (`expl`), so D(m) = C(2m+1, m) +
sum_(r<m) D(r) C(2(m-1-r), m-1-r) (`D_conv`). In series of w this is D = F + w D L with L = sum_m
C(2m, m) w^m, L^2 (1 - 4w) = 1 and 2w F = L - 1 (`Dw_eq`, `Lw_sq`, `Fw_eq`), whence 2w(1 - 4w - w^2)
D = (1 - w)(1 - 4w) L - 1 + 5w (`Dw_closed`). Summing the antidiagonals, a(n+2) = a(n+1) + a(n) +
D((n-2)/3) for n = 2 mod 3 (`anti_rec`), so (1 - X - X^2) A = 1 + X^4 D(X^3) (`anti_eq`). At w =
X^3, L(X^3) is the inverse of the square root S = (1 - 4X^3)^(1/2) of the block (`S_sq`, `L3S`), and
the block's identity follows by algebra (`key`, `gf`).
-/

namespace OMA.S_oeis_a026735

open Finset PowerSeries


/-! ### The operator θ = X d/dX on rational power series -/

/-- θ multiplies the n-th coefficient by n. -/
noncomputable def θ (F : ℚ⟦X⟧) : ℚ⟦X⟧ := PowerSeries.mk fun n => (n : ℚ) * coeff n F

lemma coeff_θ (F : ℚ⟦X⟧) (n : ℕ) : coeff n (θ F) = n * coeff n F := coeff_mk _ _

lemma θ_add (F G : ℚ⟦X⟧) : θ (F + G) = θ F + θ G := by
  ext n
  simp [coeff_θ, mul_add]

lemma θ_sub (F G : ℚ⟦X⟧) : θ (F - G) = θ F - θ G := by
  ext n
  simp [coeff_θ, mul_sub]

lemma θ_mul (F G : ℚ⟦X⟧) : θ (F * G) = θ F * G + F * θ G := by
  ext n
  simp only [coeff_θ, map_add, coeff_mul, mul_sum, ← sum_add_distrib]
  refine sum_congr rfl (fun p hp => ?_)
  rw [HasAntidiagonal.mem_antidiagonal] at hp
  rw [← hp]
  push_cast
  ring

lemma θ_C (c : ℚ) : θ (C c) = 0 := by
  ext n
  rw [coeff_θ, coeff_C]
  split_ifs with h <;> simp [h]

lemma θ_one : θ 1 = 0 := by
  rw [← map_one C, θ_C]

lemma θ_ofNat (c : ℕ) [c.AtLeastTwo] : θ (no_index (OfNat.ofNat c : ℚ⟦X⟧)) = 0 := by
  rw [← map_ofNat C c, θ_C]

lemma θ_X : θ X = X := by
  ext n
  rw [coeff_θ, coeff_X]
  split_ifs with h <;> simp [h]

lemma θ_X_pow (k : ℕ) : θ (X ^ k) = (k : ℚ⟦X⟧) * X ^ k := by
  ext n
  rw [coeff_θ, coeff_X_pow, ← map_natCast C, coeff_C_mul, coeff_X_pow]
  split_ifs with h <;> simp [h]

lemma θ_neg (F : ℚ⟦X⟧) : θ (-F) = -θ F := by
  ext n
  simp [coeff_θ]

lemma θ_sq (F : ℚ⟦X⟧) : θ (F ^ 2) = 2 * F * θ F := by
  rw [pow_two, θ_mul]
  ring

/-- The coefficients of A * B up to K only see those of B up to K. -/
lemma coeff_mul_low (A B : ℚ⟦X⟧) (K : ℕ) (h : ∀ j ≤ K, coeff j B = 0) : coeff K (A * B) = 0 := by
  rw [coeff_mul]
  refine sum_eq_zero (fun p hp => ?_)
  rw [HasAntidiagonal.mem_antidiagonal] at hp
  rw [h p.2 (by omega), mul_zero]

lemma coeff_X_pow_mul_low (W : ℚ⟦X⟧) (K : ℕ) : coeff K (X ^ (K + 1) * W) = 0 := by
  rw [coeff_X_pow_mul', if_neg (by omega)]

lemma ne_zero_of_constantCoeff {G : ℚ⟦X⟧} (h : constantCoeff G ≠ 0) : G ≠ 0 := by
  intro hG
  rw [hG, map_zero] at h
  exact h rfl

lemma cc_ofNat (c : ℕ) [c.AtLeastTwo] :
    constantCoeff (no_index (OfNat.ofNat c : ℚ⟦X⟧)) = OfNat.ofNat c := by
  rw [← map_ofNat C c, constantCoeff_C]

/-- The polynomial sum_i cs_i X^i. -/
noncomputable def pl (cs : List ℚ) : ℚ⟦X⟧ := ∑ i ∈ range cs.length, C (cs.getD i 0) * X ^ i

lemma coeff_pl_mul (cs : List ℚ) (G : ℚ⟦X⟧) (n : ℕ) (h : cs.length ≤ n + 1) :
    coeff n (pl cs * G) = ∑ i ∈ range cs.length, cs.getD i 0 * coeff (n - i) G := by
  unfold pl
  rw [sum_mul, map_sum]
  refine sum_congr rfl (fun i hi => ?_)
  rw [mem_range] at hi
  rw [mul_assoc, coeff_C_mul, coeff_X_pow_mul', if_pos (by omega)]

lemma coeff_pl_big (cs : List ℚ) (n : ℕ) (h : cs.length ≤ n) : coeff n (pl cs) = 0 := by
  unfold pl
  rw [map_sum]
  refine sum_eq_zero (fun i hi => ?_)
  rw [mem_range] at hi
  rw [coeff_C_mul, coeff_X_pow, if_neg (by omega), mul_zero]


/-! ### The array A026725 -/

lemma T_big (n k : ℕ) (h : n < k) : T n k = 0 := by
  rcases n with _ | _ | n
  · simp only [T]
    rw [if_neg (by omega)]
  · simp only [T]
    rw [if_neg (by omega)]
  · rw [T, if_pos h]

lemma T_zero (n : ℕ) : T n 0 = 1 := by
  rcases n with _ | _ | n
  · simp [T]
  · simp [T]
  · rw [T, if_neg (by omega), if_pos (Or.inl rfl)]

lemma T_diag (n : ℕ) : T n n = 1 := by
  rcases n with _ | _ | n
  · simp [T]
  · simp [T]
  · rw [T, if_neg (by omega), if_pos (Or.inr rfl)]

lemma T_rec (n k : ℕ) (h1 : 1 ≤ k) (h2 : k ≤ n + 1) :
    T (n + 2) k = T (n + 1) (k - 1) + T (n + 1) k +
      (if n % 2 = 1 ∧ 2 * k = n + 1 then T n (k - 1) else 0) := by
  rw [T, if_neg (by omega), if_neg (by omega)]
  split_ifs <;> ring

/-- D(r) = T(2r + 1, r): the entries that the extra term adds, along the subdiagonal. -/
def D (r : ℕ) : ℕ := T (2 * r + 1) r

/-- What the extra terms contribute to T(n, k): sum_r D(r) C(n - 2r - 3, k - r - 1). -/
def ds (n k : ℕ) : ℕ :=
  ∑ r ∈ range n, if 2 * r + 3 ≤ n ∧ r + 1 ≤ k then D r * (n - 2 * r - 3).choose (k - r - 1) else 0

lemma ds_zero_right (n : ℕ) : ds n 0 = 0 := by
  unfold ds
  exact sum_eq_zero (fun r _ => if_neg (by omega))

lemma ds_big (n k : ℕ) (h : n ≤ k + 1) : ds n k = 0 := by
  unfold ds
  refine sum_eq_zero (fun r _ => ?_)
  split_ifs with hc
  · rw [Nat.choose_eq_zero_of_lt (by omega), mul_zero]
  · rfl

lemma ds_succ (n k : ℕ) (hk : 1 ≤ k) :
    ds (n + 2) k = ds (n + 1) (k - 1) + ds (n + 1) k +
      (if n % 2 = 1 ∧ 2 * k = n + 1 then D (k - 1) else 0) := by
  unfold ds
  rw [sum_range_succ, if_neg (by omega), add_zero]
  have key : ∀ r ∈ range (n + 1),
      (if 2 * r + 3 ≤ n + 2 ∧ r + 1 ≤ k then D r * (n + 2 - 2 * r - 3).choose (k - r - 1) else 0) =
      (if 2 * r + 3 ≤ n + 1 ∧ r + 1 ≤ k - 1 then
          D r * (n + 1 - 2 * r - 3).choose (k - 1 - r - 1) else 0) +
        (if 2 * r + 3 ≤ n + 1 ∧ r + 1 ≤ k then D r * (n + 1 - 2 * r - 3).choose (k - r - 1)
          else 0) +
        (if r = k - 1 ∧ n % 2 = 1 ∧ 2 * k = n + 1 then D r else 0) := by
    intro r _
    rcases (show (2 * r + 3 ≤ n + 1 ∧ r + 2 ≤ k) ∨ (2 * r + 3 ≤ n + 1 ∧ k = r + 1) ∨ k ≤ r ∨
      (2 * r + 3 = n + 2 ∧ k = r + 1) ∨ (2 * r + 3 = n + 2 ∧ r + 2 ≤ k) ∨
      (n + 2 < 2 * r + 3 ∧ r + 1 ≤ k) by omega) with h | h | h | h | h | h
    · have c1 : 2 * r + 3 ≤ n + 2 ∧ r + 1 ≤ k := by omega
      have c2 : 2 * r + 3 ≤ n + 1 ∧ r + 1 ≤ k - 1 := by omega
      have c3 : 2 * r + 3 ≤ n + 1 ∧ r + 1 ≤ k := by omega
      have c4 : ¬ (r = k - 1 ∧ n % 2 = 1 ∧ 2 * k = n + 1) := by omega
      rw [if_pos c1, if_pos c2, if_pos c3, if_neg c4, add_zero,
        show n + 2 - 2 * r - 3 = (n + 1 - 2 * r - 3) + 1 by omega,
        show k - r - 1 = (k - 1 - r - 1) + 1 by omega, Nat.choose_succ_succ',
        show k - 1 - r - 1 + 1 = k - r - 1 by omega]
      ring
    · have c1 : 2 * r + 3 ≤ n + 2 ∧ r + 1 ≤ k := by omega
      have c2 : ¬ (2 * r + 3 ≤ n + 1 ∧ r + 1 ≤ k - 1) := by omega
      have c3 : 2 * r + 3 ≤ n + 1 ∧ r + 1 ≤ k := by omega
      have c4 : ¬ (r = k - 1 ∧ n % 2 = 1 ∧ 2 * k = n + 1) := by omega
      rw [if_pos c1, if_neg c2, if_pos c3, if_neg c4, show k - r - 1 = 0 by omega,
        Nat.choose_zero_right, Nat.choose_zero_right]
      ring
    · have c1 : ¬ (2 * r + 3 ≤ n + 2 ∧ r + 1 ≤ k) := by omega
      have c2 : ¬ (2 * r + 3 ≤ n + 1 ∧ r + 1 ≤ k - 1) := by omega
      have c3 : ¬ (2 * r + 3 ≤ n + 1 ∧ r + 1 ≤ k) := by omega
      have c4 : ¬ (r = k - 1 ∧ n % 2 = 1 ∧ 2 * k = n + 1) := by omega
      rw [if_neg c1, if_neg c2, if_neg c3, if_neg c4]
    · have c1 : 2 * r + 3 ≤ n + 2 ∧ r + 1 ≤ k := by omega
      have c2 : ¬ (2 * r + 3 ≤ n + 1 ∧ r + 1 ≤ k - 1) := by omega
      have c3 : ¬ (2 * r + 3 ≤ n + 1 ∧ r + 1 ≤ k) := by omega
      have c4 : r = k - 1 ∧ n % 2 = 1 ∧ 2 * k = n + 1 := by omega
      rw [if_pos c1, if_neg c2, if_neg c3, if_pos c4, show n + 2 - 2 * r - 3 = 0 by omega,
        show k - r - 1 = 0 by omega, Nat.choose_zero_right]
      ring
    · have c1 : 2 * r + 3 ≤ n + 2 ∧ r + 1 ≤ k := by omega
      have c2 : ¬ (2 * r + 3 ≤ n + 1 ∧ r + 1 ≤ k - 1) := by omega
      have c3 : ¬ (2 * r + 3 ≤ n + 1 ∧ r + 1 ≤ k) := by omega
      have c4 : ¬ (r = k - 1 ∧ n % 2 = 1 ∧ 2 * k = n + 1) := by omega
      rw [if_pos c1, if_neg c2, if_neg c3, if_neg c4, show n + 2 - 2 * r - 3 = 0 by omega,
        Nat.choose_eq_zero_of_lt (by omega)]
      ring
    · have c1 : ¬ (2 * r + 3 ≤ n + 2 ∧ r + 1 ≤ k) := by omega
      have c2 : ¬ (2 * r + 3 ≤ n + 1 ∧ r + 1 ≤ k - 1) := by omega
      have c3 : ¬ (2 * r + 3 ≤ n + 1 ∧ r + 1 ≤ k) := by omega
      have c4 : ¬ (r = k - 1 ∧ n % 2 = 1 ∧ 2 * k = n + 1) := by omega
      rw [if_neg c1, if_neg c2, if_neg c3, if_neg c4]
  rw [sum_congr rfl key, sum_add_distrib, sum_add_distrib]
  congr 1
  by_cases hP : n % 2 = 1 ∧ 2 * k = n + 1
  · rw [if_pos hP, sum_eq_single (k - 1)]
    · rw [if_pos ⟨rfl, hP⟩]
    · intro r _ hr
      rw [if_neg (by tauto)]
    · intro h
      rw [mem_range] at h
      omega
  · rw [if_neg hP]
    exact sum_eq_zero (fun r _ => if_neg (by tauto))

/-- The explicit formula: T(n, k) = C(n, k) + sum_r D(r) C(n - 2r - 3, k - r - 1). -/
theorem expl (n k : ℕ) : T n k = n.choose k + ds n k := by
  induction n using Nat.strong_induction_on generalizing k with
  | _ n ih =>
    rcases n with _ | _ | n
    · rcases k with _ | k <;> simp [T, ds]
    · rcases k with _ | _ | k
      · simp [T, ds]
      · simp [T, ds]
      · rw [Nat.choose_eq_zero_of_lt (by omega)]
        simp [T, ds]
    · rcases (show k = 0 ∨ (1 ≤ k ∧ k ≤ n + 1) ∨ n + 2 ≤ k by omega) with hk | hk | hk
      · subst hk
        rw [T_zero, Nat.choose_zero_right, ds_zero_right]
      · obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
        have hr := T_rec n (j + 1) (by omega) hk.2
        have hs := ds_succ n (j + 1) (by omega)
        rw [show j + 1 - 1 = j by omega] at hr hs
        rw [hr, ih (n + 1) (by omega) j, ih (n + 1) (by omega) (j + 1), hs,
          Nat.choose_succ_succ (n + 1) j]
        split_ifs with hc
        · have hD : T n j = D j := by
            rw [show n = 2 * j + 1 by omega]
            rfl
          rw [hD]
          ring
        · ring
      · rw [ds_big (n + 2) k (by omega), add_zero]
        rcases (show k = n + 2 ∨ n + 2 < k by omega) with h | h
        · subst h
          rw [T_diag, Nat.choose_self]
        · rw [T_big _ _ h, Nat.choose_eq_zero_of_lt h]

/-- The subdiagonal: D(m) = C(2m + 1, m) + sum_(r < m) D(r) C(2(m - 1 - r), m - 1 - r). -/
lemma D_conv (m : ℕ) : (D m : ℚ) = ((2 * m + 1).choose m : ℚ) +
    ∑ r ∈ range m, (D r : ℚ) * ((m - 1 - r).centralBinom : ℚ) := by
  have h := expl (2 * m + 1) m
  rw [show T (2 * m + 1) m = D m from rfl] at h
  rw [h, ds]
  push_cast
  congr 1
  rw [← sum_subset (range_subset_range.mpr (show m ≤ 2 * m + 1 by omega))]
  · refine sum_congr rfl (fun r hr => ?_)
    rw [mem_range] at hr
    rw [if_pos (by omega), Nat.centralBinom_eq_two_mul_choose,
      show 2 * m + 1 - 2 * r - 3 = 2 * (m - 1 - r) by omega,
      show m - r - 1 = m - 1 - r by omega]
  · intro r _ hr
    rw [mem_range] at hr
    rw [if_neg (by omega)]

/-! ### The subdiagonal series in w -/

noncomputable def Dw : ℚ⟦X⟧ := PowerSeries.mk fun m => (D m : ℚ)

noncomputable def Lw : ℚ⟦X⟧ := PowerSeries.mk fun m => (m.centralBinom : ℚ)

noncomputable def Fw : ℚ⟦X⟧ := PowerSeries.mk fun m => ((2 * m + 1).choose m : ℚ)

lemma Dw_eq : Dw = Fw + X * (Dw * Lw) := by
  ext m
  rw [map_add]
  rcases m with _ | m
  · simp only [Dw, Fw, coeff_mk, coeff_zero_X_mul, add_zero]
    rw [D_conv 0]
    simp
  · rw [coeff_succ_X_mul, coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    simp only [Dw, Fw, Lw, coeff_mk]
    rw [D_conv (m + 1)]
    congr 1

lemma Fw_eq : 2 * X * Fw = Lw - 1 := by
  ext m
  rcases m with _ | m
  · simp [Fw, Lw]
  · rw [mul_assoc, show (2 : ℚ⟦X⟧) = C 2 from (map_ofNat C 2).symm, coeff_C_mul, coeff_succ_X_mul,
      map_sub, coeff_one, if_neg (by omega), sub_zero]
    simp only [Fw, Lw, coeff_mk]
    rw [Nat.centralBinom_eq_two_mul_choose, show 2 * (m + 1) = 2 * m + 1 + 1 by ring,
      Nat.choose_succ_succ, Nat.choose_symm_half]
    push_cast
    ring

lemma θ_const (F : ℚ⟦X⟧) : constantCoeff (θ F) = 0 := by
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_θ]
  simp

lemma θLw : (1 - 4 * X) * θ Lw = 2 * X * Lw := by
  ext m
  rcases m with _ | m
  · simp [θ_const]
  · rw [sub_mul, one_mul, map_sub, mul_assoc, show (4 : ℚ⟦X⟧) = C 4 from (map_ofNat C 4).symm,
      coeff_C_mul, coeff_succ_X_mul, mul_assoc,
      show (2 : ℚ⟦X⟧) = C 2 from (map_ofNat C 2).symm, coeff_C_mul, coeff_succ_X_mul, coeff_θ,
      coeff_θ]
    simp only [Lw, coeff_mk]
    have h := Nat.succ_mul_centralBinom_succ m
    have hq : ((m + 1 : ℕ) : ℚ) * ((m + 1).centralBinom : ℚ) =
        2 * (2 * m + 1) * (m.centralBinom : ℚ) := by exact_mod_cast h
    push_cast at hq ⊢
    linear_combination hq

lemma θ_const_eq {F : ℚ⟦X⟧} (h : θ F = 0) : F = C (constantCoeff F) := by
  ext n
  rcases n with _ | n
  · simp
  · have := congrArg (coeff (n + 1)) h
    rw [coeff_θ, map_zero] at this
    rw [coeff_C, if_neg (by omega)]
    have h1 : ((n + 1 : ℕ) : ℚ) ≠ 0 := by positivity
    exact (mul_eq_zero.mp this).resolve_left h1

lemma Lw_const : constantCoeff Lw = 1 := by
  simp [Lw, ← coeff_zero_eq_constantCoeff_apply]

/-- Lw = 1/sqrt(1 - 4w): Lw^2 (1 - 4w) = 1. -/
lemma Lw_sq : Lw ^ 2 * (1 - 4 * X) = 1 := by
  have h : θ (Lw ^ 2 * (1 - 4 * X)) = 0 := by
    rw [θ_mul, θ_sq, θ_sub, θ_one, θ_mul, θ_ofNat, θ_X]
    linear_combination (2 * Lw) * θLw
  rw [θ_const_eq h]
  simp [Lw_const]

/-- The closed form of the subdiagonal series. -/
lemma Dw_closed : 2 * X * (1 - 4 * X - X ^ 2) * Dw = (1 - X) * (1 - 4 * X) * Lw - 1 + 5 * X := by
  linear_combination (2 * X * (1 + X * Lw) * (1 - 4 * X)) * Dw_eq + (2 * X ^ 3 * Dw + X) * Lw_sq +
    ((1 + X * Lw) * (1 - 4 * X)) * Fw_eq

lemma coeff_sub_X_pow (q : ℕ) (hq : q ≠ 0) (F : ℚ⟦X⟧) (n : ℕ) :
    coeff n (F.subst (X ^ q : ℚ⟦X⟧)) = if q ∣ n then coeff (n / q) F else 0 := by
  rw [coeff_subst_X_pow hq]
  simp

/-- The closed form at w = X^q. -/
lemma Dq_closed (q : ℕ) (hq : q ≠ 0) :
    2 * X ^ q * (1 - 4 * X ^ q - (X ^ q) ^ 2) * Dw.subst (X ^ q : ℚ⟦X⟧) =
      (1 - X ^ q) * (1 - 4 * X ^ q) * Lw.subst (X ^ q : ℚ⟦X⟧) - 1 + 5 * X ^ q := by
  have ha : HasSubst (X ^ q : ℚ⟦X⟧) := HasSubst.X_pow hq
  have h := congrArg (substAlgHom ha) Dw_closed
  simp only [map_mul, map_sub, map_add, map_one, map_ofNat, map_pow, substAlgHom_X ha,
    coe_substAlgHom] at h
  exact h

/-- Lw^2 (1 - 4w) = 1 at w = X^q. -/
lemma Lq_sq (q : ℕ) (hq : q ≠ 0) :
    (Lw.subst (X ^ q : ℚ⟦X⟧)) ^ 2 * (1 - 4 * X ^ q) = 1 := by
  have ha : HasSubst (X ^ q : ℚ⟦X⟧) := HasSubst.X_pow hq
  have h := congrArg (substAlgHom ha) Lw_sq
  simp only [map_mul, map_sub, map_one, map_ofNat, map_pow, substAlgHom_X ha,
    coe_substAlgHom] at h
  exact h

lemma Lq_const (q : ℕ) (hq : q ≠ 0) : constantCoeff (Lw.subst (X ^ q : ℚ⟦X⟧)) = 1 := by
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_sub_X_pow q hq, if_pos (dvd_zero q),
    Nat.zero_div, coeff_zero_eq_constantCoeff_apply, Lw_const]

/-! ### The antidiagonal sums -/

/-- The array in coordinates P(i, j) = T(i + j, j). -/
lemma P_rec (i j : ℕ) (hi : 1 ≤ i) (hj : 1 ≤ j) :
    T (i + j) j = T (i + j - 1) (j - 1) + T (i + j - 1) j + (if i = j + 1 then D (j - 1) else 0) := by
  obtain ⟨n, hn⟩ : ∃ n, i + j = n + 2 := ⟨i + j - 2, by omega⟩
  rw [hn, T_rec n j hj (by omega), show n + 2 - 1 = n + 1 by omega]
  by_cases h : i = j + 1
  · rw [if_pos (show n % 2 = 1 ∧ 2 * j = n + 1 by omega), if_pos h,
      show D (j - 1) = T (2 * (j - 1) + 1) (j - 1) from rfl, show 2 * (j - 1) + 1 = n by omega]
  · rw [if_neg (show ¬ (n % 2 = 1 ∧ 2 * j = n + 1) by omega), if_neg h]

lemma anti_term (n j : ℕ) (hj : j ≤ n + 1) :
    T (n + 1 - j) (j + 1) = T (n - j) j + T (n - j) (j + 1) + (if n = 3 * j + 2 then D j else 0) := by
  rcases (show 2 * j + 1 ≤ n ∨ n = 2 * j ∨ n < 2 * j by omega) with h | h | h
  · have hp := P_rec (n - 2 * j) (j + 1) (by omega) (by omega)
    rw [show n - 2 * j + (j + 1) = n + 1 - j by omega, show n + 1 - j - 1 = n - j by omega,
      show j + 1 - 1 = j by omega] at hp
    rw [hp]
    by_cases h3 : n = 3 * j + 2
    · rw [if_pos (by omega), if_pos h3]
    · rw [if_neg (by omega), if_neg h3]
  · subst h
    rw [show 2 * j + 1 - j = j + 1 by omega, T_diag, show 2 * j - j = j by omega, T_diag,
      T_big j (j + 1) (by omega), if_neg (by omega)]
  · rw [T_big _ _ (by omega), T_big (n - j) j (by omega), T_big (n - j) (j + 1) (by omega),
      if_neg (by omega)]

lemma a_eq' (n : ℕ) : a n = ∑ j ∈ range (n + 1), T (n - j) j := by
  unfold a
  apply sum_subset (range_subset_range.mpr (by omega))
  intro j hj hj'
  rw [mem_range] at hj hj'
  exact T_big _ _ (by omega)

lemma anti_rec (n : ℕ) : a (n + 2) = a (n + 1) + a n + (if n % 3 = 2 then D (n / 3) else 0) := by
  have s0 : a (n + 2) = (∑ j ∈ range (n + 2), T (n + 1 - j) (j + 1)) + 1 := by
    rw [a_eq', sum_range_succ', Nat.sub_zero, T_zero]
    congr 1
    refine sum_congr rfl (fun j _ => ?_)
    rw [show n + 2 - (j + 1) = n + 1 - j by omega]
  have s1 : ∑ j ∈ range (n + 2), T (n - j) j = a n := by
    rw [a_eq', sum_range_succ, show n - (n + 1) = 0 by omega, T_big 0 (n + 1) (by omega), add_zero]
  have s2 : (∑ j ∈ range (n + 2), T (n - j) (j + 1)) + 1 = a (n + 1) := by
    rw [a_eq', sum_range_succ' (fun j => T (n + 1 - j) j), Nat.sub_zero, T_zero,
      sum_range_succ (fun j => T (n - j) (j + 1)) (n + 1), show n - (n + 1) = 0 by omega,
      T_big 0 (n + 1 + 1) (by omega), add_zero]
    congr 1
    refine sum_congr rfl (fun j _ => ?_)
    rw [show n + 1 - (j + 1) = n - j by omega]
  have s3 : ∑ j ∈ range (n + 2), (if n = 3 * j + 2 then D j else 0) =
      if n % 3 = 2 then D (n / 3) else 0 := by
    by_cases h : n % 3 = 2
    · rw [if_pos h, sum_eq_single (n / 3)]
      · rw [if_pos (by omega)]
      · intro j _ hj
        rw [if_neg (by omega)]
      · intro hj
        rw [mem_range] at hj
        omega
    · rw [if_neg h]
      exact sum_eq_zero (fun j _ => if_neg (by omega))
  rw [s0, sum_congr rfl (fun j hj => anti_term n j (by rw [mem_range] at hj; omega)),
    sum_add_distrib, sum_add_distrib, s1, s3]
  omega

/-- The antidiagonal sums as a series, and the subdiagonal series and Lw at w = X^3. -/
noncomputable def Aser : ℚ⟦X⟧ := PowerSeries.mk fun n => (a n : ℚ)

noncomputable def D3 : ℚ⟦X⟧ := Dw.subst (X ^ 3 : ℚ⟦X⟧)

noncomputable def L3 : ℚ⟦X⟧ := Lw.subst (X ^ 3 : ℚ⟦X⟧)

lemma anti_eq : (1 - X - X ^ 2) * Aser = 1 + X ^ 4 * D3 := by
  have h0 : a 0 = 1 := by decide
  have h1 : a 1 = 1 := by decide
  have hc : ∀ m, coeff (m + 2) ((1 - X - X ^ 2) * Aser) =
      (a (m + 2) : ℚ) - a (m + 1) - a m := by
    intro m
    rw [sub_mul, sub_mul, one_mul, map_sub, map_sub, coeff_succ_X_mul, coeff_X_pow_mul',
      if_pos (by omega), show m + 2 - 2 = m by omega]
    simp [Aser]
  ext n
  rcases n with _ | _ | m
  · simp [Aser, h0]
  · rw [sub_mul, sub_mul, one_mul, map_sub, map_sub, coeff_succ_X_mul, coeff_X_pow_mul',
      if_neg (show ¬ (2 ≤ 0 + 1) by omega), map_add, coeff_one, if_neg (show ¬ (0 + 1 = 0) by omega),
      zero_add, coeff_X_pow_mul', if_neg (show ¬ (4 ≤ 0 + 1) by omega)]
    simp [Aser, h0, h1]
  · rw [hc m, anti_rec m, map_add, coeff_one, if_neg (show ¬ (m + 1 + 1 = 0) by omega), zero_add,
      coeff_X_pow_mul']
    by_cases hm : m % 3 = 2
    · rw [if_pos hm, if_pos (show 4 ≤ m + 1 + 1 by omega), D3, coeff_sub_X_pow 3 (by norm_num),
        if_pos (show 3 ∣ m + 1 + 1 - 4 by omega), Dw, coeff_mk,
        show (m + 1 + 1 - 4) / 3 = m / 3 by omega]
      push_cast
      ring
    · rw [if_neg hm]
      split_ifs with h4
      · rw [D3, coeff_sub_X_pow 3 (by norm_num), if_neg (show ¬ 3 ∣ m + 1 + 1 - 4 by omega)]
        push_cast
        ring
      · push_cast
        ring

/-! ### The square root -/

lemma rad_const : constantCoeff (-4 * X ^ 3 : PowerSeries ℚ) = 0 := by
  simp

lemma S_sq : S ^ 2 = 1 - 4 * X ^ 3 := by
  have ha : HasSubst (-4 * X ^ 3 : PowerSeries ℚ) := HasSubst.of_constantCoeff_zero' rad_const
  rw [S, ← subst_pow ha, pow_two (PowerSeries.binomialSeries ℚ (1 / 2 : ℚ)),
    ← PowerSeries.binomialSeries_add,
    show (1 / 2 : ℚ) + 1 / 2 = ((1 : ℕ) : ℚ) by norm_num, PowerSeries.binomialSeries_nat, pow_one,
    ← coe_substAlgHom ha, map_add, map_one, coe_substAlgHom ha, subst_X ha]
  ring

lemma S_const : constantCoeff S = 1 := by
  have ha := HasSubst.of_constantCoeff_zero' rad_const
  have h := constantCoeff_subst ha (PowerSeries.binomialSeries ℚ (1 / 2 : ℚ))
  rw [finsum_eq_single _ 0] at h
  · refine h.trans ?_
    simp
  · intro d hd
    have h0 : MvPowerSeries.constantCoeff (-4 * X ^ 3 : PowerSeries ℚ) = 0 := rad_const
    rw [map_pow, h0, zero_pow hd, smul_zero]

/-- L3 = 1/sqrt(1 - 4X^3) is the inverse of S. -/
lemma L3S : L3 * S = 1 := by
  have hsq : L3 ^ 2 * (1 - 4 * X ^ 3) = 1 := Lq_sq 3 (by norm_num)
  have h1 : (L3 * S - 1) * (L3 * S + 1) = 0 := by
    linear_combination L3 ^ 2 * S_sq + hsq
  rcases mul_eq_zero.mp h1 with h | h
  · exact sub_eq_zero.mp h
  · exfalso
    have := congrArg constantCoeff h
    rw [map_add, map_mul, S_const, show L3 = Lw.subst (X ^ 3 : ℚ⟦X⟧) from rfl,
      Lq_const 3 (by norm_num)] at this
    norm_num at this

/-- The block's identity before the divisions. -/
lemma key : Aser * ((X ^ 6 + 4 * X ^ 3 - 1) * (X ^ 2 + X - 1)) = C (-1 / 2 : ℚ) * (2 * X ^ 6 - 5 * X ^ 4 + 8 * X ^ 3 + X - 2 + X * (X - 1) * (X ^ 2 + X + 1) * S) := by
  have hq : 2 * X ^ 3 * (1 - 4 * X ^ 3 - (X ^ 3) ^ 2) * D3 =
      (1 - X ^ 3) * (1 - 4 * X ^ 3) * L3 - 1 + 5 * X ^ 3 := Dq_closed 3 (by norm_num)
  have h2 : C (-1 / 2 : ℚ) * 2 = -1 := by
    rw [show (2 : ℚ⟦X⟧) = C 2 from (map_ofNat C 2).symm, ← map_mul]
    norm_num
  have hX : (2 * X ^ 3 : ℚ⟦X⟧) ≠ 0 :=
    mul_ne_zero (ne_zero_of_constantCoeff (by simp [cc_ofNat])) (pow_ne_zero _ X_ne_zero)
  apply mul_left_cancel₀ hX
  linear_combination (X ^ 4 * (1 - X ^ 3) * S) * L3S - (X ^ 4 * (1 - X ^ 3) * L3) * S_sq +
    X ^ 4 * hq + (2 * X ^ 3 * (1 - 4 * X ^ 3 - X ^ 6)) * anti_eq - (X ^ 3 * (2 * X ^ 6 - 5 * X ^ 4 + 8 * X ^ 3 + X - 2 + X * (X - 1) * (X ^ 2 + X + 1) * S)) * h2

/-- Voznyy's generating function. -/
theorem gf : PowerSeries.mk (fun n => (a n : ℚ)) =
      C (-1 / 2 : ℚ) * (2 * X ^ 6 - 5 * X ^ 4 + 8 * X ^ 3 + X - 2 +
        X * (X - 1) * (X ^ 2 + X + 1) * S) *
        (X ^ 6 + 4 * X ^ 3 - 1 : PowerSeries ℚ)⁻¹ * (X ^ 2 + X - 1 : PowerSeries ℚ)⁻¹ := by
  have hk := key
  have i1 : (X ^ 6 + 4 * X ^ 3 - 1 : ℚ⟦X⟧) * (X ^ 6 + 4 * X ^ 3 - 1 : ℚ⟦X⟧)⁻¹ = 1 :=
    PowerSeries.mul_inv_cancel _ (by simp)
  have i2 : (X ^ 2 + X - 1 : ℚ⟦X⟧) * (X ^ 2 + X - 1 : ℚ⟦X⟧)⁻¹ = 1 :=
    PowerSeries.mul_inv_cancel _ (by simp)
  rw [show PowerSeries.mk (fun n => (a n : ℚ)) = Aser from rfl]
  linear_combination ((X ^ 6 + 4 * X ^ 3 - 1 : ℚ⟦X⟧)⁻¹ * (X ^ 2 + X - 1 : ℚ⟦X⟧)⁻¹) * hk -
    (Aser * ((X ^ 2 + X - 1) * (X ^ 2 + X - 1 : ℚ⟦X⟧)⁻¹)) * i1 - Aser * i2





lemma ch_half (m : ℕ) : 2 * (2 * m + 1).choose m = (m + 1).centralBinom := by
  rw [Nat.centralBinom_eq_two_mul_choose, show 2 * (m + 1) = 2 * m + 1 + 1 by ring,
    Nat.choose_succ_succ', Nat.choose_symm_half]
  ring

lemma D_conv_nat (m : ℕ) : D m = (2 * m + 1).choose m + ∑ r ∈ range m, D r * (m - 1 - r).centralBinom := by
  have h := D_conv m
  exact_mod_cast h

/-- Controls: the entry's listed terms, a(0) to a(36). -/
theorem controls :
    a 0 = 1 ∧ a 1 = 1 ∧ a 2 = 2 ∧ a 3 = 3 ∧
    a 4 = 6 ∧ a 5 = 9 ∧ a 6 = 15 ∧ a 7 = 28 ∧
    a 8 = 43 ∧ a 9 = 71 ∧ a 10 = 130 ∧ a 11 = 201 ∧
    a 12 = 331 ∧ a 13 = 597 ∧ a 14 = 928 ∧ a 15 = 1525 ∧
    a 16 = 2720 ∧ a 17 = 4245 ∧ a 18 = 6965 ∧ a 19 = 12315 ∧
    a 20 = 19280 ∧ a 21 = 31595 ∧ a 22 = 55472 ∧ a 23 = 87067 ∧
    a 24 = 142539 ∧ a 25 = 248802 ∧ a 26 = 391341 ∧ a 27 = 640143 ∧
    a 28 = 1111864 ∧ a 29 = 1752007 ∧ a 30 = 2863871 ∧ a 31 = 4953162 ∧
    a 32 = 7817033 ∧ a 33 = 12770195 ∧ a 34 = 22004810 ∧ a 35 = 34775005 ∧
    a 36 = 56779815 := by
  have cb0 : Nat.centralBinom 0 = 1 := Nat.centralBinom_zero
  have cb1 : Nat.centralBinom 1 = 2 := by
    have h := Nat.succ_mul_centralBinom_succ 0
    rw [show (0 : ℕ) + 1 = 1 from rfl, cb0] at h
    omega
  have cb2 : Nat.centralBinom 2 = 6 := by
    have h := Nat.succ_mul_centralBinom_succ 1
    rw [show (1 : ℕ) + 1 = 2 from rfl, cb1] at h
    omega
  have cb3 : Nat.centralBinom 3 = 20 := by
    have h := Nat.succ_mul_centralBinom_succ 2
    rw [show (2 : ℕ) + 1 = 3 from rfl, cb2] at h
    omega
  have cb4 : Nat.centralBinom 4 = 70 := by
    have h := Nat.succ_mul_centralBinom_succ 3
    rw [show (3 : ℕ) + 1 = 4 from rfl, cb3] at h
    omega
  have cb5 : Nat.centralBinom 5 = 252 := by
    have h := Nat.succ_mul_centralBinom_succ 4
    rw [show (4 : ℕ) + 1 = 5 from rfl, cb4] at h
    omega
  have cb6 : Nat.centralBinom 6 = 924 := by
    have h := Nat.succ_mul_centralBinom_succ 5
    rw [show (5 : ℕ) + 1 = 6 from rfl, cb5] at h
    omega
  have cb7 : Nat.centralBinom 7 = 3432 := by
    have h := Nat.succ_mul_centralBinom_succ 6
    rw [show (6 : ℕ) + 1 = 7 from rfl, cb6] at h
    omega
  have cb8 : Nat.centralBinom 8 = 12870 := by
    have h := Nat.succ_mul_centralBinom_succ 7
    rw [show (7 : ℕ) + 1 = 8 from rfl, cb7] at h
    omega
  have cb9 : Nat.centralBinom 9 = 48620 := by
    have h := Nat.succ_mul_centralBinom_succ 8
    rw [show (8 : ℕ) + 1 = 9 from rfl, cb8] at h
    omega
  have cb10 : Nat.centralBinom 10 = 184756 := by
    have h := Nat.succ_mul_centralBinom_succ 9
    rw [show (9 : ℕ) + 1 = 10 from rfl, cb9] at h
    omega
  have cb11 : Nat.centralBinom 11 = 705432 := by
    have h := Nat.succ_mul_centralBinom_succ 10
    rw [show (10 : ℕ) + 1 = 11 from rfl, cb10] at h
    omega
  have cb12 : Nat.centralBinom 12 = 2704156 := by
    have h := Nat.succ_mul_centralBinom_succ 11
    rw [show (11 : ℕ) + 1 = 12 from rfl, cb11] at h
    omega
  have cb13 : Nat.centralBinom 13 = 10400600 := by
    have h := Nat.succ_mul_centralBinom_succ 12
    rw [show (12 : ℕ) + 1 = 13 from rfl, cb12] at h
    omega
  have ch0 : Nat.choose 1 0 = 1 := by
    have h := ch_half 0
    rw [show 2 * (0 : ℕ) + 1 = 1 from rfl, cb1] at h
    omega
  have ch1 : Nat.choose 3 1 = 3 := by
    have h := ch_half 1
    rw [show 2 * (1 : ℕ) + 1 = 3 from rfl, show (1 : ℕ) + 1 = 2 from rfl, cb2] at h
    omega
  have ch2 : Nat.choose 5 2 = 10 := by
    have h := ch_half 2
    rw [show 2 * (2 : ℕ) + 1 = 5 from rfl, show (2 : ℕ) + 1 = 3 from rfl, cb3] at h
    omega
  have ch3 : Nat.choose 7 3 = 35 := by
    have h := ch_half 3
    rw [show 2 * (3 : ℕ) + 1 = 7 from rfl, show (3 : ℕ) + 1 = 4 from rfl, cb4] at h
    omega
  have ch4 : Nat.choose 9 4 = 126 := by
    have h := ch_half 4
    rw [show 2 * (4 : ℕ) + 1 = 9 from rfl, show (4 : ℕ) + 1 = 5 from rfl, cb5] at h
    omega
  have ch5 : Nat.choose 11 5 = 462 := by
    have h := ch_half 5
    rw [show 2 * (5 : ℕ) + 1 = 11 from rfl, show (5 : ℕ) + 1 = 6 from rfl, cb6] at h
    omega
  have ch6 : Nat.choose 13 6 = 1716 := by
    have h := ch_half 6
    rw [show 2 * (6 : ℕ) + 1 = 13 from rfl, show (6 : ℕ) + 1 = 7 from rfl, cb7] at h
    omega
  have ch7 : Nat.choose 15 7 = 6435 := by
    have h := ch_half 7
    rw [show 2 * (7 : ℕ) + 1 = 15 from rfl, show (7 : ℕ) + 1 = 8 from rfl, cb8] at h
    omega
  have ch8 : Nat.choose 17 8 = 24310 := by
    have h := ch_half 8
    rw [show 2 * (8 : ℕ) + 1 = 17 from rfl, show (8 : ℕ) + 1 = 9 from rfl, cb9] at h
    omega
  have ch9 : Nat.choose 19 9 = 92378 := by
    have h := ch_half 9
    rw [show 2 * (9 : ℕ) + 1 = 19 from rfl, show (9 : ℕ) + 1 = 10 from rfl, cb10] at h
    omega
  have ch10 : Nat.choose 21 10 = 352716 := by
    have h := ch_half 10
    rw [show 2 * (10 : ℕ) + 1 = 21 from rfl, show (10 : ℕ) + 1 = 11 from rfl, cb11] at h
    omega
  have ch11 : Nat.choose 23 11 = 1352078 := by
    have h := ch_half 11
    rw [show 2 * (11 : ℕ) + 1 = 23 from rfl, show (11 : ℕ) + 1 = 12 from rfl, cb12] at h
    omega
  have ch12 : Nat.choose 25 12 = 5200300 := by
    have h := ch_half 12
    rw [show 2 * (12 : ℕ) + 1 = 25 from rfl, show (12 : ℕ) + 1 = 13 from rfl, cb13] at h
    omega
  have d0 : D 0 = 1 := by
    have h := D_conv_nat 0
    simp only [sum_range_succ, sum_range_zero, zero_add, show 2 * 0 + 1 = 1 from rfl] at h
    rw [h]
    norm_num [ch0]
  have d1 : D 1 = 4 := by
    have h := D_conv_nat 1
    simp only [sum_range_succ, sum_range_zero, zero_add, show 2 * 1 + 1 = 3 from rfl] at h
    rw [h]
    norm_num [ch1, d0, cb0]
  have d2 : D 2 = 16 := by
    have h := D_conv_nat 2
    simp only [sum_range_succ, sum_range_zero, zero_add, show 2 * 2 + 1 = 5 from rfl] at h
    rw [h]
    norm_num [ch2, d0, d1, cb0, cb1]
  have d3 : D 3 = 65 := by
    have h := D_conv_nat 3
    simp only [sum_range_succ, sum_range_zero, zero_add, show 2 * 3 + 1 = 7 from rfl] at h
    rw [h]
    norm_num [ch3, d0, d1, d2, cb0, cb1, cb2]
  have d4 : D 4 = 267 := by
    have h := D_conv_nat 4
    simp only [sum_range_succ, sum_range_zero, zero_add, show 2 * 4 + 1 = 9 from rfl] at h
    rw [h]
    norm_num [ch4, d0, d1, d2, d3, cb0, cb1, cb2, cb3]
  have d5 : D 5 = 1105 := by
    have h := D_conv_nat 5
    simp only [sum_range_succ, sum_range_zero, zero_add, show 2 * 5 + 1 = 11 from rfl] at h
    rw [h]
    norm_num [ch5, d0, d1, d2, d3, d4, cb0, cb1, cb2, cb3, cb4]
  have d6 : D 6 = 4597 := by
    have h := D_conv_nat 6
    simp only [sum_range_succ, sum_range_zero, zero_add, show 2 * 6 + 1 = 13 from rfl] at h
    rw [h]
    norm_num [ch6, d0, d1, d2, d3, d4, d5, cb0, cb1, cb2, cb3, cb4, cb5]
  have d7 : D 7 = 19196 := by
    have h := D_conv_nat 7
    simp only [sum_range_succ, sum_range_zero, zero_add, show 2 * 7 + 1 = 15 from rfl] at h
    rw [h]
    norm_num [ch7, d0, d1, d2, d3, d4, d5, d6, cb0, cb1, cb2, cb3, cb4, cb5, cb6]
  have d8 : D 8 = 80380 := by
    have h := D_conv_nat 8
    simp only [sum_range_succ, sum_range_zero, zero_add, show 2 * 8 + 1 = 17 from rfl] at h
    rw [h]
    norm_num [ch8, d0, d1, d2, d3, d4, d5, d6, d7, cb0, cb1, cb2, cb3, cb4, cb5, cb6, cb7]
  have d9 : D 9 = 337284 := by
    have h := D_conv_nat 9
    simp only [sum_range_succ, sum_range_zero, zero_add, show 2 * 9 + 1 = 19 from rfl] at h
    rw [h]
    norm_num [ch9, d0, d1, d2, d3, d4, d5, d6, d7, d8, cb0, cb1, cb2, cb3, cb4, cb5, cb6, cb7, cb8]
  have d10 : D 10 = 1417582 := by
    have h := D_conv_nat 10
    simp only [sum_range_succ, sum_range_zero, zero_add, show 2 * 10 + 1 = 21 from rfl] at h
    rw [h]
    norm_num [ch10, d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, cb0, cb1, cb2, cb3, cb4, cb5, cb6, cb7, cb8, cb9]
  have d11 : D 11 = 5965622 := by
    have h := D_conv_nat 11
    simp only [sum_range_succ, sum_range_zero, zero_add, show 2 * 11 + 1 = 23 from rfl] at h
    rw [h]
    norm_num [ch11, d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, cb0, cb1, cb10, cb2, cb3, cb4, cb5, cb6, cb7, cb8, cb9]
  have d12 : D 12 = 25130844 := by
    have h := D_conv_nat 12
    simp only [sum_range_succ, sum_range_zero, zero_add, show 2 * 12 + 1 = 25 from rfl] at h
    rw [h]
    norm_num [ch12, d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, cb0, cb1, cb10, cb11, cb2, cb3, cb4, cb5, cb6, cb7, cb8, cb9]
  have v0 : a 0 = 1 := by decide
  have v1 : a 1 = 1 := by decide
  have v2 : a 2 = 2 := by
    rw [show 2 = 0 + 2 from rfl, anti_rec 0, show 0 + 1 = 1 from rfl, v1, v0, if_neg (show ¬ 0 % 3 = 2 by decide)]
  have v3 : a 3 = 3 := by
    rw [show 3 = 1 + 2 from rfl, anti_rec 1, show 1 + 1 = 2 from rfl, v2, v1, if_neg (show ¬ 1 % 3 = 2 by decide)]
  have v4 : a 4 = 6 := by
    rw [show 4 = 2 + 2 from rfl, anti_rec 2, show 2 + 1 = 3 from rfl, v3, v2, if_pos (show 2 % 3 = 2 from rfl), show 2 / 3 = 0 from rfl, d0]
  have v5 : a 5 = 9 := by
    rw [show 5 = 3 + 2 from rfl, anti_rec 3, show 3 + 1 = 4 from rfl, v4, v3, if_neg (show ¬ 3 % 3 = 2 by decide)]
  have v6 : a 6 = 15 := by
    rw [show 6 = 4 + 2 from rfl, anti_rec 4, show 4 + 1 = 5 from rfl, v5, v4, if_neg (show ¬ 4 % 3 = 2 by decide)]
  have v7 : a 7 = 28 := by
    rw [show 7 = 5 + 2 from rfl, anti_rec 5, show 5 + 1 = 6 from rfl, v6, v5, if_pos (show 5 % 3 = 2 from rfl), show 5 / 3 = 1 from rfl, d1]
  have v8 : a 8 = 43 := by
    rw [show 8 = 6 + 2 from rfl, anti_rec 6, show 6 + 1 = 7 from rfl, v7, v6, if_neg (show ¬ 6 % 3 = 2 by decide)]
  have v9 : a 9 = 71 := by
    rw [show 9 = 7 + 2 from rfl, anti_rec 7, show 7 + 1 = 8 from rfl, v8, v7, if_neg (show ¬ 7 % 3 = 2 by decide)]
  have v10 : a 10 = 130 := by
    rw [show 10 = 8 + 2 from rfl, anti_rec 8, show 8 + 1 = 9 from rfl, v9, v8, if_pos (show 8 % 3 = 2 from rfl), show 8 / 3 = 2 from rfl, d2]
  have v11 : a 11 = 201 := by
    rw [show 11 = 9 + 2 from rfl, anti_rec 9, show 9 + 1 = 10 from rfl, v10, v9, if_neg (show ¬ 9 % 3 = 2 by decide)]
  have v12 : a 12 = 331 := by
    rw [show 12 = 10 + 2 from rfl, anti_rec 10, show 10 + 1 = 11 from rfl, v11, v10, if_neg (show ¬ 10 % 3 = 2 by decide)]
  have v13 : a 13 = 597 := by
    rw [show 13 = 11 + 2 from rfl, anti_rec 11, show 11 + 1 = 12 from rfl, v12, v11, if_pos (show 11 % 3 = 2 from rfl), show 11 / 3 = 3 from rfl, d3]
  have v14 : a 14 = 928 := by
    rw [show 14 = 12 + 2 from rfl, anti_rec 12, show 12 + 1 = 13 from rfl, v13, v12, if_neg (show ¬ 12 % 3 = 2 by decide)]
  have v15 : a 15 = 1525 := by
    rw [show 15 = 13 + 2 from rfl, anti_rec 13, show 13 + 1 = 14 from rfl, v14, v13, if_neg (show ¬ 13 % 3 = 2 by decide)]
  have v16 : a 16 = 2720 := by
    rw [show 16 = 14 + 2 from rfl, anti_rec 14, show 14 + 1 = 15 from rfl, v15, v14, if_pos (show 14 % 3 = 2 from rfl), show 14 / 3 = 4 from rfl, d4]
  have v17 : a 17 = 4245 := by
    rw [show 17 = 15 + 2 from rfl, anti_rec 15, show 15 + 1 = 16 from rfl, v16, v15, if_neg (show ¬ 15 % 3 = 2 by decide)]
  have v18 : a 18 = 6965 := by
    rw [show 18 = 16 + 2 from rfl, anti_rec 16, show 16 + 1 = 17 from rfl, v17, v16, if_neg (show ¬ 16 % 3 = 2 by decide)]
  have v19 : a 19 = 12315 := by
    rw [show 19 = 17 + 2 from rfl, anti_rec 17, show 17 + 1 = 18 from rfl, v18, v17, if_pos (show 17 % 3 = 2 from rfl), show 17 / 3 = 5 from rfl, d5]
  have v20 : a 20 = 19280 := by
    rw [show 20 = 18 + 2 from rfl, anti_rec 18, show 18 + 1 = 19 from rfl, v19, v18, if_neg (show ¬ 18 % 3 = 2 by decide)]
  have v21 : a 21 = 31595 := by
    rw [show 21 = 19 + 2 from rfl, anti_rec 19, show 19 + 1 = 20 from rfl, v20, v19, if_neg (show ¬ 19 % 3 = 2 by decide)]
  have v22 : a 22 = 55472 := by
    rw [show 22 = 20 + 2 from rfl, anti_rec 20, show 20 + 1 = 21 from rfl, v21, v20, if_pos (show 20 % 3 = 2 from rfl), show 20 / 3 = 6 from rfl, d6]
  have v23 : a 23 = 87067 := by
    rw [show 23 = 21 + 2 from rfl, anti_rec 21, show 21 + 1 = 22 from rfl, v22, v21, if_neg (show ¬ 21 % 3 = 2 by decide)]
  have v24 : a 24 = 142539 := by
    rw [show 24 = 22 + 2 from rfl, anti_rec 22, show 22 + 1 = 23 from rfl, v23, v22, if_neg (show ¬ 22 % 3 = 2 by decide)]
  have v25 : a 25 = 248802 := by
    rw [show 25 = 23 + 2 from rfl, anti_rec 23, show 23 + 1 = 24 from rfl, v24, v23, if_pos (show 23 % 3 = 2 from rfl), show 23 / 3 = 7 from rfl, d7]
  have v26 : a 26 = 391341 := by
    rw [show 26 = 24 + 2 from rfl, anti_rec 24, show 24 + 1 = 25 from rfl, v25, v24, if_neg (show ¬ 24 % 3 = 2 by decide)]
  have v27 : a 27 = 640143 := by
    rw [show 27 = 25 + 2 from rfl, anti_rec 25, show 25 + 1 = 26 from rfl, v26, v25, if_neg (show ¬ 25 % 3 = 2 by decide)]
  have v28 : a 28 = 1111864 := by
    rw [show 28 = 26 + 2 from rfl, anti_rec 26, show 26 + 1 = 27 from rfl, v27, v26, if_pos (show 26 % 3 = 2 from rfl), show 26 / 3 = 8 from rfl, d8]
  have v29 : a 29 = 1752007 := by
    rw [show 29 = 27 + 2 from rfl, anti_rec 27, show 27 + 1 = 28 from rfl, v28, v27, if_neg (show ¬ 27 % 3 = 2 by decide)]
  have v30 : a 30 = 2863871 := by
    rw [show 30 = 28 + 2 from rfl, anti_rec 28, show 28 + 1 = 29 from rfl, v29, v28, if_neg (show ¬ 28 % 3 = 2 by decide)]
  have v31 : a 31 = 4953162 := by
    rw [show 31 = 29 + 2 from rfl, anti_rec 29, show 29 + 1 = 30 from rfl, v30, v29, if_pos (show 29 % 3 = 2 from rfl), show 29 / 3 = 9 from rfl, d9]
  have v32 : a 32 = 7817033 := by
    rw [show 32 = 30 + 2 from rfl, anti_rec 30, show 30 + 1 = 31 from rfl, v31, v30, if_neg (show ¬ 30 % 3 = 2 by decide)]
  have v33 : a 33 = 12770195 := by
    rw [show 33 = 31 + 2 from rfl, anti_rec 31, show 31 + 1 = 32 from rfl, v32, v31, if_neg (show ¬ 31 % 3 = 2 by decide)]
  have v34 : a 34 = 22004810 := by
    rw [show 34 = 32 + 2 from rfl, anti_rec 32, show 32 + 1 = 33 from rfl, v33, v32, if_pos (show 32 % 3 = 2 from rfl), show 32 / 3 = 10 from rfl, d10]
  have v35 : a 35 = 34775005 := by
    rw [show 35 = 33 + 2 from rfl, anti_rec 33, show 33 + 1 = 34 from rfl, v34, v33, if_neg (show ¬ 33 % 3 = 2 by decide)]
  have v36 : a 36 = 56779815 := by
    rw [show 36 = 34 + 2 from rfl, anti_rec 34, show 34 + 1 = 35 from rfl, v35, v34, if_neg (show ¬ 34 % 3 = 2 by decide)]
  exact ⟨v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13, v14, v15, v16, v17, v18, v19, v20, v21, v22, v23, v24, v25, v26, v27, v28, v29, v30, v31, v32, v33, v34, v35, v36⟩

/-- Voznyy's generating function. -/
theorem conjecture :
    PowerSeries.mk (fun n => (a n : ℚ)) =
      C (-1 / 2 : ℚ) * (2 * X ^ 6 - 5 * X ^ 4 + 8 * X ^ 3 + X - 2 +
        X * (X - 1) * (X ^ 2 + X + 1) * S) *
        (X ^ 6 + 4 * X ^ 3 - 1 : PowerSeries ℚ)⁻¹ * (X ^ 2 + X - 1 : PowerSeries ℚ)⁻¹ :=
  gf

end OMA.S_oeis_a026735

theorem OMA.solution : type_of% @OMA.S_oeis_a026735.main :=
  OMA.S_oeis_a026735.conjecture
