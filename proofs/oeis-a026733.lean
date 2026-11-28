import OMAStatements.S_oeis_a026733

/-!
OEIS A026733 (Clark Kimberling): a(n) = Sum_{k=0..floor(n/2)} T(n,k), T given by A026725.
Conjecture: (-n+2)*a(n) +(n-2)*a(n-1) +2*(4*n-13)*a(n-2) +8*(-n+4)*a(n-3) +5*(-3*n+14)*a(n-4) +(15*n-94)*a(n-5) +2*(-2*n+9)*a(n-6) +4*(n-6)*a(n-7)=0.

Proof. With D(r) = T(2r+1, r), the entries that the extra term adds, induction on n gives the
explicit formula T(n, k) = C(n, k) + sum_r D(r) C(n-2r-3, k-r-1) (`expl`), so D(m) = C(2m+1, m) +
sum_(r<m) D(r) C(2(m-1-r), m-1-r) (`D_conv`). In series of w this is D = F + w D L with L = sum_m
C(2m, m) w^m, L^2 (1 - 4w) = 1 and 2w F = L - 1 (`Dw_eq`, `Lw_sq`, `Fw_eq`), whence 2w(1 - 4w - w^2)
D = (1 - w)(1 - 4w) L - 1 + 5w (`Dw_closed`). Summing the half rows, a(2m+2) = 2 a(2m+1) + T(2m+1,
m+1) and a(2m+3) = 2 a(2m+2) - T(2m+2, m+1) + D(m) (`half_even`, `half_odd`), and the explicit
formula gives the series of the two entries next to the middle in terms of D, F and L (`c1_eq`,
`c0_eq`, `C1w_eq`, `C0w_eq`); at w = X^2 this gives 4(1 - 2X)(1 - 4X^2 - X^4) H = P + Q L(X^2) for
the half-row sums H (`hHs`, `s1`, `hH`). L(X^2) satisfies a first-order equation in θ = X d/dX
(`ode0`), and Mathar's recurrence is the differential equation L H = B, an identity linear in L(X^2)
(`ode`); its coefficient of X^n is the recurrence (`recur`).
-/

namespace OMA.S_oeis_a026733

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

/-! ### The half-row sums -/

lemma half_even (m : ℕ) : (a (2 * m + 2) : ℚ) = 2 * a (2 * m + 1) + T (2 * m + 1) (m + 1) := by
  have ha2 : a (2 * m + 2) = ∑ k ∈ range (m + 1 + 1), T (2 * m + 2) k := by
    unfold a
    rw [show (2 * m + 2) / 2 + 1 = m + 1 + 1 by omega]
  have ha1 : a (2 * m + 1) = ∑ k ∈ range (m + 1), T (2 * m + 1) k := by
    unfold a
    rw [show (2 * m + 1) / 2 + 1 = m + 1 by omega]
  have e1 : ∑ k ∈ range (m + 1 + 1), (T (2 * m + 2) k : ℚ) =
      ∑ j ∈ range (m + 1), (T (2 * m + 2) (j + 1) : ℚ) + 1 := by
    rw [sum_range_succ', T_zero]
    push_cast
    ring
  have e2 : ∑ j ∈ range (m + 1), (T (2 * m + 2) (j + 1) : ℚ) =
      ∑ j ∈ range (m + 1), ((T (2 * m + 1) j : ℚ) + T (2 * m + 1) (j + 1)) := by
    refine sum_congr rfl (fun j hj => ?_)
    rw [mem_range] at hj
    rw [T_rec (2 * m) (j + 1) (by omega) (by omega),
      if_neg (show ¬ (2 * m % 2 = 1 ∧ 2 * (j + 1) = 2 * m + 1) by omega),
      show j + 1 - 1 = j by omega]
    push_cast
    ring
  have e3 : ∑ j ∈ range (m + 1), (T (2 * m + 1) (j + 1) : ℚ) + 1 =
      ∑ k ∈ range (m + 1), (T (2 * m + 1) k : ℚ) + T (2 * m + 1) (m + 1) := by
    have h1 : ∑ k ∈ range (m + 1 + 1), (T (2 * m + 1) k : ℚ) =
        ∑ j ∈ range (m + 1), (T (2 * m + 1) (j + 1) : ℚ) + 1 := by
      rw [sum_range_succ', T_zero]
      push_cast
      ring
    rw [← h1, sum_range_succ]
  rw [ha2, ha1]
  push_cast
  rw [e1, e2, sum_add_distrib]
  linarith [e3]

lemma half_odd (m : ℕ) :
    (a (2 * m + 3) : ℚ) = 2 * a (2 * m + 2) - T (2 * m + 2) (m + 1) + D m := by
  have ha3 : a (2 * m + 3) = ∑ k ∈ range (m + 1 + 1), T (2 * m + 3) k := by
    unfold a
    rw [show (2 * m + 3) / 2 + 1 = m + 1 + 1 by omega]
  have ha2 : a (2 * m + 2) = ∑ k ∈ range (m + 1 + 1), T (2 * m + 2) k := by
    unfold a
    rw [show (2 * m + 2) / 2 + 1 = m + 1 + 1 by omega]
  have e1 : ∑ k ∈ range (m + 1 + 1), (T (2 * m + 3) k : ℚ) =
      ∑ j ∈ range (m + 1), (T (2 * m + 3) (j + 1) : ℚ) + 1 := by
    rw [sum_range_succ', T_zero]
    push_cast
    ring
  have e2 : ∑ j ∈ range (m + 1), (T (2 * m + 3) (j + 1) : ℚ) =
      ∑ j ∈ range (m + 1), ((T (2 * m + 2) j : ℚ) + T (2 * m + 2) (j + 1) +
        (if j = m then (D m : ℚ) else 0)) := by
    refine sum_congr rfl (fun j hj => ?_)
    rw [mem_range] at hj
    have hr := T_rec (2 * m + 1) (j + 1) (by omega) (by omega)
    rw [show 2 * m + 1 + 2 = 2 * m + 3 by ring, show 2 * m + 1 + 1 = 2 * m + 2 by ring,
      show j + 1 - 1 = j by omega] at hr
    rw [hr]
    by_cases hj' : j = m
    · rw [hj', if_pos (show (2 * m + 1) % 2 = 1 ∧ 2 * (m + 1) = 2 * m + 2 by omega), if_pos rfl]
      push_cast
      rfl
    · rw [if_neg (show ¬ ((2 * m + 1) % 2 = 1 ∧ 2 * (j + 1) = 2 * m + 2) by omega), if_neg hj']
      push_cast
      ring
  have e3 : ∑ j ∈ range (m + 1), (if j = m then (D m : ℚ) else 0) = D m := by
    rw [sum_eq_single m]
    · rw [if_pos rfl]
    · intro j _ hj
      rw [if_neg hj]
    · intro h
      exact absurd (mem_range.mpr (by omega)) h
  have e4 : ∑ j ∈ range (m + 1), (T (2 * m + 2) j : ℚ) + T (2 * m + 2) (m + 1) =
      ∑ k ∈ range (m + 1 + 1), (T (2 * m + 2) k : ℚ) := by
    rw [sum_range_succ (fun k => (T (2 * m + 2) k : ℚ)) (m + 1)]
  have e5 : ∑ j ∈ range (m + 1), (T (2 * m + 2) (j + 1) : ℚ) + 1 =
      ∑ k ∈ range (m + 1 + 1), (T (2 * m + 2) k : ℚ) := by
    rw [sum_range_succ' (fun k => (T (2 * m + 2) k : ℚ)) (m + 1), T_zero]
    push_cast
    ring
  rw [ha3, ha2]
  push_cast
  rw [e1, e2, sum_add_distrib, sum_add_distrib, e3]
  linarith [e4, e5]

/-- The two entries next to the middle: T(2m+1, m+1) and T(2m+2, m+1). -/
lemma c1_eq (m : ℕ) : (T (2 * m + 1) (m + 1) : ℚ) = ((2 * m + 1).choose m : ℚ) +
    ∑ r ∈ range m, (D r : ℚ) * ((2 * (m - 1 - r)).choose (m - r) : ℚ) := by
  have h := expl (2 * m + 1) (m + 1)
  rw [h, ds, Nat.choose_symm_half]
  push_cast
  congr 1
  rw [← sum_subset (range_subset_range.mpr (show m ≤ 2 * m + 1 by omega))]
  · refine sum_congr rfl (fun r hr => ?_)
    rw [mem_range] at hr
    rw [if_pos (by omega), show 2 * m + 1 - 2 * r - 3 = 2 * (m - 1 - r) by omega,
      show m + 1 - r - 1 = m - r by omega]
  · intro r _ hr
    rw [mem_range] at hr
    rw [if_neg (by omega)]

lemma c0_eq (m : ℕ) : (T (2 * m + 2) (m + 1) : ℚ) = ((m + 1).centralBinom : ℚ) +
    ∑ r ∈ range m, (D r : ℚ) * ((2 * (m - 1 - r) + 1).choose (m - 1 - r) : ℚ) := by
  have h := expl (2 * m + 2) (m + 1)
  rw [h, ds, show (2 * m + 2).choose (m + 1) = (m + 1).centralBinom by
    rw [Nat.centralBinom_eq_two_mul_choose, show 2 * (m + 1) = 2 * m + 2 by ring]]
  push_cast
  congr 1
  rw [← sum_subset (range_subset_range.mpr (show m ≤ 2 * m + 2 by omega))]
  · refine sum_congr rfl (fun r hr => ?_)
    rw [mem_range] at hr
    rw [if_pos (by omega), show 2 * m + 2 - 2 * r - 3 = 2 * (m - 1 - r) + 1 by omega,
      show m + 1 - r - 1 = m - 1 - r + 1 by omega, Nat.choose_symm_half]
  · intro r _ hr
    rw [mem_range] at hr
    rw [if_neg (by omega)]

noncomputable def C1w : ℚ⟦X⟧ := PowerSeries.mk fun m => (T (2 * m + 1) (m + 1) : ℚ)

noncomputable def C0w : ℚ⟦X⟧ := PowerSeries.mk fun m => (T (2 * m + 2) (m + 1) : ℚ)

noncomputable def Ew : ℚ⟦X⟧ := PowerSeries.mk fun j => ((2 * j).choose (j + 1) : ℚ)

lemma Ew_eq : Ew = Fw - Lw := by
  ext j
  simp only [Ew, Fw, Lw, coeff_mk, map_sub]
  rw [Nat.centralBinom_eq_two_mul_choose]
  have h := Nat.choose_succ_succ' (2 * j) j
  rw [Nat.choose_symm_half] at h
  have hq : ((2 * j + 1).choose j : ℚ) = ((2 * j).choose j : ℚ) + ((2 * j).choose (j + 1) : ℚ) := by
    exact_mod_cast h
  linarith

lemma C1w_eq : C1w = Fw + X * (Dw * (Fw - Lw)) := by
  rw [← Ew_eq]
  ext m
  rw [map_add]
  rcases m with _ | m
  · simp only [C1w, Fw, coeff_mk, coeff_zero_X_mul, add_zero]
    rw [c1_eq 0]
    simp
  · rw [coeff_succ_X_mul, coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    simp only [C1w, Fw, Dw, Ew, coeff_mk]
    rw [c1_eq (m + 1)]
    congr 1
    refine sum_congr rfl (fun r hr => ?_)
    rw [mem_range] at hr
    rw [show m + 1 - 1 - r = m - r by omega, show m + 1 - r = m - r + 1 by omega]

lemma C0w_eq : X * C0w = Lw - 1 + X ^ 2 * (Dw * Fw) := by
  ext n
  rcases n with _ | _ | m
  · simp [Lw]
  · rw [coeff_succ_X_mul, map_add, map_sub, coeff_X_pow_mul', if_neg (show ¬ (2 ≤ 0 + 1) by omega),
      coeff_one, if_neg (show ¬ (0 + 1 = 0) by omega)]
    simp only [C0w, Lw, coeff_mk]
    rw [c0_eq 0]
    simp
  · rw [coeff_succ_X_mul, map_add, map_sub, coeff_X_pow_mul', if_pos (show 2 ≤ m + 1 + 1 by omega),
      coeff_one, if_neg (show ¬ (m + 1 + 1 = 0) by omega), show m + 1 + 1 - 2 = m by omega,
      coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, sub_zero]
    simp only [C0w, Lw, Dw, Fw, coeff_mk]
    rw [c0_eq (m + 1)]
    congr 1

/-- The half-row sums as a series, and the series in w at w = X^2. -/
noncomputable def H : ℚ⟦X⟧ := PowerSeries.mk fun n => (a n : ℚ)

noncomputable def D2 : ℚ⟦X⟧ := Dw.subst (X ^ 2 : ℚ⟦X⟧)

noncomputable def L2 : ℚ⟦X⟧ := Lw.subst (X ^ 2 : ℚ⟦X⟧)

noncomputable def F2 : ℚ⟦X⟧ := Fw.subst (X ^ 2 : ℚ⟦X⟧)

noncomputable def C1s : ℚ⟦X⟧ := C1w.subst (X ^ 2 : ℚ⟦X⟧)

noncomputable def C0s : ℚ⟦X⟧ := C0w.subst (X ^ 2 : ℚ⟦X⟧)

lemma hF2 : 2 * X ^ 2 * F2 = L2 - 1 := by
  have ha : HasSubst (X ^ 2 : ℚ⟦X⟧) := HasSubst.X_pow (by norm_num)
  have h := congrArg (substAlgHom ha) Fw_eq
  simp only [map_mul, map_sub, map_one, map_ofNat, substAlgHom_X ha, coe_substAlgHom] at h
  exact h

lemma hC1 : C1s = F2 + X ^ 2 * (D2 * (F2 - L2)) := by
  have ha : HasSubst (X ^ 2 : ℚ⟦X⟧) := HasSubst.X_pow (by norm_num)
  have h := congrArg (substAlgHom ha) C1w_eq
  simp only [map_add, map_mul, map_sub, substAlgHom_X ha, coe_substAlgHom] at h
  exact h

lemma hC0 : X ^ 2 * C0s = L2 - 1 + (X ^ 2) ^ 2 * (D2 * F2) := by
  have ha : HasSubst (X ^ 2 : ℚ⟦X⟧) := HasSubst.X_pow (by norm_num)
  have h := congrArg (substAlgHom ha) C0w_eq
  simp only [map_add, map_mul, map_sub, map_one, map_pow, substAlgHom_X ha, coe_substAlgHom] at h
  exact h

lemma hHs : (1 - 2 * X) * H = 1 - X + X ^ 2 * C1s + X ^ 3 * (D2 - C0s) := by
  have h0 : a 0 = 1 := by decide
  have h1 : a 1 = 1 := by decide
  have hc : ∀ m, coeff (m + 1) ((1 - 2 * X) * H) = (a (m + 1) : ℚ) - 2 * a m := by
    intro m
    rw [sub_mul, one_mul, map_sub, mul_assoc, show (2 : ℚ⟦X⟧) = C 2 from (map_ofNat C 2).symm,
      coeff_C_mul, coeff_succ_X_mul]
    simp [H]
  ext n
  rcases n with _ | _ | m
  · simp [H, h0]
  · rw [hc 0, h0, h1, map_add, map_add, map_sub, coeff_one, if_neg (show ¬ (0 + 1 = 0) by omega),
      coeff_X, if_pos (show 0 + 1 = 1 by omega), coeff_X_pow_mul',
      if_neg (show ¬ (2 ≤ 0 + 1) by omega), coeff_X_pow_mul', if_neg (show ¬ (3 ≤ 0 + 1) by omega)]
    norm_num
  · rcases Nat.even_or_odd' m with ⟨k, rfl | rfl⟩
    · rw [hc (2 * k + 1), show 2 * k + 1 + 1 = 2 * k + 2 by ring, half_even k, map_add, map_add,
        map_sub, coeff_one, if_neg (show ¬ (2 * k + 2 = 0) by omega), coeff_X,
        if_neg (show ¬ (2 * k + 2 = 1) by omega), coeff_X_pow_mul',
        if_pos (show 2 ≤ 2 * k + 2 by omega), coeff_X_pow_mul', show 2 * k + 2 - 2 = 2 * k by omega,
        C1s, coeff_sub_X_pow 2 (by norm_num), if_pos (show 2 ∣ 2 * k by omega),
        show 2 * k / 2 = k by omega, C1w, coeff_mk]
      split_ifs with h3
      · rw [map_sub, D2, C0s, coeff_sub_X_pow 2 (by norm_num), coeff_sub_X_pow 2 (by norm_num),
          if_neg (show ¬ 2 ∣ 2 * k + 2 - 3 by omega), if_neg (show ¬ 2 ∣ 2 * k + 2 - 3 by omega)]
        ring
      · ring
    · rw [hc (2 * k + 1 + 1), show 2 * k + 1 + 1 + 1 = 2 * k + 3 by ring,
        show 2 * k + 1 + 1 = 2 * k + 2 by ring, half_odd k, map_add, map_add, map_sub, coeff_one,
        if_neg (show ¬ (2 * k + 3 = 0) by omega), coeff_X, if_neg (show ¬ (2 * k + 3 = 1) by omega),
        coeff_X_pow_mul', if_pos (show 2 ≤ 2 * k + 3 by omega), coeff_X_pow_mul',
        if_pos (show 3 ≤ 2 * k + 3 by omega), show 2 * k + 3 - 2 = 2 * k + 1 by omega,
        show 2 * k + 3 - 3 = 2 * k by omega, C1s, coeff_sub_X_pow 2 (by norm_num),
        if_neg (show ¬ 2 ∣ 2 * k + 1 by omega), map_sub, D2, C0s, coeff_sub_X_pow 2 (by norm_num),
        coeff_sub_X_pow 2 (by norm_num), if_pos (show 2 ∣ 2 * k by omega),
        if_pos (show 2 ∣ 2 * k by omega), show 2 * k / 2 = k by omega, Dw, C0w, coeff_mk, coeff_mk]
      ring

lemma s1 : 2 * (1 - 2 * X) * H = 1 + (1 - 2 * X) * L2 + X ^ 2 * (1 - X - 2 * X ^ 2) * D2 * L2 +
    X ^ 2 * (3 * X - 1) * D2 := by
  apply mul_left_cancel₀ (pow_ne_zero 2 (X_ne_zero (R := ℚ)))
  linear_combination (2 * X ^ 2) * hHs + (2 * X ^ 4) * hC1 - (2 * X ^ 3) * hC0 +
    (X ^ 2 + (X ^ 4 - X ^ 5) * D2) * hF2

/-- The half-row sums in closed form. -/
lemma hH : (4 - 8 * X - 16 * X ^ 2 + 32 * X ^ 3 - 4 * X ^ 4 + 8 * X ^ 5) * H = (4 - 4 * X - 16 * X ^ 2 + 16 * X ^ 3) + (4 * X ^ 2 - 4 * X ^ 3 - 16 * X ^ 4 + 16 * X ^ 5) * L2 := by
  have hq : 2 * X ^ 2 * (1 - 4 * X ^ 2 - (X ^ 2) ^ 2) * D2 =
      (1 - X ^ 2) * (1 - 4 * X ^ 2) * L2 - 1 + 5 * X ^ 2 := Dq_closed 2 (by norm_num)
  have hsq : L2 ^ 2 * (1 - 4 * X ^ 2) = 1 := Lq_sq 2 (by norm_num)
  linear_combination (2 * (1 - 4 * X ^ 2 - X ^ 4)) * s1 +
    ((1 - X - 2 * X ^ 2) * L2 + (3 * X - 1)) * hq + ((1 - X - 2 * X ^ 2) * (1 - X ^ 2)) * hsq

/-- L2 = 1/sqrt(1 - 4X^2) satisfies a first-order equation. -/
lemma ode0 : (2 - 8 * X ^ 2) * θ L2 = (8 * X ^ 2) * L2 := by
  have hsq : L2 ^ 2 * (1 - 4 * X ^ 2) = 1 := Lq_sq 2 (by norm_num)
  have h := congrArg θ hsq
  simp only [θ_add, θ_sub, θ_mul, θ_sq, θ_X_pow, θ_X, θ_ofNat, θ_one, θ_neg, Nat.cast_ofNat] at h
  have hL : L2 ≠ 0 := ne_zero_of_constantCoeff (by
    rw [show L2 = Lw.subst (X ^ 2 : ℚ⟦X⟧) from rfl, Lq_const 2 (by norm_num)]
    norm_num)
  apply mul_left_cancel₀ hL
  linear_combination h

/-- Mathar's recurrence as a differential equation: L H = B. -/
lemma ode : pl [-1, 1, 8, -8, -15, 15, -4, 4] * θ (H) + pl [2, -1, -10, 8, 10, -19, -6, 4] * H = pl [2, 0, -10, 4, 12, -8] := by
  have e1 : (4 - 8 * X - 16 * X ^ 2 + 32 * X ^ 3 - 4 * X ^ 4 + 8 * X ^ 5) * H = (4 - 4 * X - 16 * X ^ 2 + 16 * X ^ 3) + (4 * X ^ 2 - 4 * X ^ 3 - 16 * X ^ 4 + 16 * X ^ 5) * L2 := hH
  have e2 : (-8 * X - 32 * X ^ 2 + 96 * X ^ 3 - 16 * X ^ 4 + 40 * X ^ 5) * H + (4 - 8 * X - 16 * X ^ 2 + 32 * X ^ 3 - 4 * X ^ 4 + 8 * X ^ 5) * θ (H) =
      (-4 * X - 32 * X ^ 2 + 48 * X ^ 3) + (8 * X ^ 2 - 12 * X ^ 3 - 64 * X ^ 4 + 80 * X ^ 5) * L2 + (4 * X ^ 2 - 4 * X ^ 3 - 16 * X ^ 4 + 16 * X ^ 5) * θ (L2) := by
    have h := congrArg θ e1
    simp only [θ_add, θ_sub, θ_mul, θ_sq, θ_X_pow, θ_X, θ_ofNat, θ_one, θ_neg, Nat.cast_ofNat] at h
    linear_combination h
  have o1 := ode0
  have hK : ((-4 + 8 * X) : ℚ⟦X⟧) ≠ 0 := ne_zero_of_constantCoeff (by simp [cc_ofNat])
  have h : (-4 + 8 * X) * ((-1 + X + 8 * X ^ 2 - 8 * X ^ 3 - 15 * X ^ 4 + 15 * X ^ 5 - 4 * X ^ 6 + 4 * X ^ 7) * θ (H) + (2 - X - 10 * X ^ 2 + 8 * X ^ 3 + 10 * X ^ 4 - 19 * X ^ 5 - 6 * X ^ 6 + 4 * X ^ 7) * H) = (-4 + 8 * X) * (2 - 10 * X ^ 2 + 4 * X ^ 3 + 12 * X ^ 4 - 8 * X ^ 5) := by
    linear_combination (-2 + 3 * X + 12 * X ^ 2 - 16 * X ^ 3) * e1 + (1 - X - 4 * X ^ 2 + 4 * X ^ 3) * e2 + (2 * X ^ 2 - 4 * X ^ 3 - 6 * X ^ 4 + 16 * X ^ 5 - 8 * X ^ 6) * o1
  have ha1 : pl [-1, 1, 8, -8, -15, 15, -4, 4] = (-1 + X + 8 * X ^ 2 - 8 * X ^ 3 - 15 * X ^ 4 + 15 * X ^ 5 - 4 * X ^ 6 + 4 * X ^ 7) := by
    simp only [pl, sum_range_succ, range_zero, sum_empty, List.length_cons, List.length_nil,
      List.getD_cons_zero, List.getD_cons_succ, map_neg, map_ofNat C, map_one, map_zero]
    ring
  have ha0 : pl [2, -1, -10, 8, 10, -19, -6, 4] = (2 - X - 10 * X ^ 2 + 8 * X ^ 3 + 10 * X ^ 4 - 19 * X ^ 5 - 6 * X ^ 6 + 4 * X ^ 7) := by
    simp only [pl, sum_range_succ, range_zero, sum_empty, List.length_cons, List.length_nil,
      List.getD_cons_zero, List.getD_cons_succ, map_neg, map_ofNat C, map_one, map_zero]
    ring
  have hB : pl [2, 0, -10, 4, 12, -8] = (2 - 10 * X ^ 2 + 4 * X ^ 3 + 12 * X ^ 4 - 8 * X ^ 5) := by
    simp only [pl, sum_range_succ, range_zero, sum_empty, List.length_cons, List.length_nil,
      List.getD_cons_zero, List.getD_cons_succ, map_neg, map_ofNat C, map_one, map_zero]
    ring
  rw [ha1, ha0, hB]
  exact mul_left_cancel₀ hK h

/-- Mathar's recurrence. -/
theorem recur : ∀ n : ℕ, 7 ≤ n →
    (-(n : ℤ) + 2) * (a n : ℤ) + ((n : ℤ) - 2) * (a (n - 1) : ℤ) + 2 * (4 * (n : ℤ) - 13) * (a (n - 2) : ℤ) + 8 * (-(n : ℤ) + 4) * (a (n - 3) : ℤ) + 5 * (-3 * (n : ℤ) + 14) * (a (n - 4) : ℤ) + (15 * (n : ℤ) - 94) * (a (n - 5) : ℤ) + 2 * (-2 * (n : ℤ) + 9) * (a (n - 6) : ℤ) + 4 * ((n : ℤ) - 6) * (a (n - 7) : ℤ) = 0 := by
  intro n hn
  have h := congrArg (coeff n) ode
  rw [map_add, coeff_pl_mul _ _ _ (by norm_num; omega), coeff_pl_mul _ _ _ (by norm_num; omega), coeff_pl_big _ _ (by norm_num; omega)] at h
  simp only [coeff_θ, H, coeff_mk, sum_range_succ, sum_range_zero, zero_add, List.getD_cons_zero,
    List.getD_cons_succ, List.length_cons, List.length_nil, Nat.sub_zero] at h
  have c1 : ((n - 1 : ℕ) : ℚ) = (n : ℚ) - 1 := by
    rw [Nat.cast_sub (by omega)]
    norm_num
  have c2 : ((n - 2 : ℕ) : ℚ) = (n : ℚ) - 2 := by
    rw [Nat.cast_sub (by omega)]
    norm_num
  have c3 : ((n - 3 : ℕ) : ℚ) = (n : ℚ) - 3 := by
    rw [Nat.cast_sub (by omega)]
    norm_num
  have c4 : ((n - 4 : ℕ) : ℚ) = (n : ℚ) - 4 := by
    rw [Nat.cast_sub (by omega)]
    norm_num
  have c5 : ((n - 5 : ℕ) : ℚ) = (n : ℚ) - 5 := by
    rw [Nat.cast_sub (by omega)]
    norm_num
  have c6 : ((n - 6 : ℕ) : ℚ) = (n : ℚ) - 6 := by
    rw [Nat.cast_sub (by omega)]
    norm_num
  have c7 : ((n - 7 : ℕ) : ℚ) = (n : ℚ) - 7 := by
    rw [Nat.cast_sub (by omega)]
    norm_num
  rw [c1, c2, c3, c4, c5, c6, c7] at h
  have goal : (-(n : ℚ) + 2) * (a n : ℚ) + ((n : ℚ) - 2) * (a (n - 1) : ℚ) + 2 * (4 * (n : ℚ) - 13) * (a (n - 2) : ℚ) + 8 * (-(n : ℚ) + 4) * (a (n - 3) : ℚ) + 5 * (-3 * (n : ℚ) + 14) * (a (n - 4) : ℚ) + (15 * (n : ℚ) - 94) * (a (n - 5) : ℚ) + 2 * (-2 * (n : ℚ) + 9) * (a (n - 6) : ℚ) + 4 * ((n : ℚ) - 6) * (a (n - 7) : ℚ) = 0 := by
    linear_combination h
  exact_mod_cast goal

/-- Controls: the entry's listed terms, a(0) to a(30). -/
theorem controls :
    a 0 = 1 ∧ a 1 = 1 ∧ a 2 = 3 ∧ a 3 = 5 ∧
    a 4 = 13 ∧ a 5 = 23 ∧ a 6 = 57 ∧ a 7 = 103 ∧
    a 8 = 249 ∧ a 9 = 455 ∧ a 10 = 1083 ∧ a 11 = 1993 ∧
    a 12 = 4693 ∧ a 13 = 8679 ∧ a 14 = 20275 ∧ a 15 = 37633 ∧
    a 16 = 87377 ∧ a 17 = 162643 ∧ a 18 = 375789 ∧ a 19 = 701075 ∧
    a 20 = 1613413 ∧ a 21 = 3015563 ∧ a 22 = 6916957 ∧ a 23 = 12948083 ∧
    a 24 = 29617161 ∧ a 25 = 55513327 ∧ a 26 = 126678893 ∧ a 27 = 237705547 ∧
    a 28 = 541325021 ∧ a 29 = 1016736115 ∧ a 30 = 2311294377 := by
  have v0 : a 0 = 1 := by decide +kernel
  have v1 : a 1 = 1 := by decide +kernel
  have v2 : a 2 = 3 := by decide +kernel
  have v3 : a 3 = 5 := by decide +kernel
  have v4 : a 4 = 13 := by decide +kernel
  have v5 : a 5 = 23 := by decide +kernel
  have v6 : a 6 = 57 := by decide +kernel
  have v7 : a 7 = 103 := by
    have h := recur 7 (by norm_num)
    rw [show (7 : ℕ) - 1 = 6 from rfl, show (7 : ℕ) - 2 = 5 from rfl, show (7 : ℕ) - 3 = 4 from rfl, show (7 : ℕ) - 4 = 3 from rfl, show (7 : ℕ) - 5 = 2 from rfl, show (7 : ℕ) - 6 = 1 from rfl, show (7 : ℕ) - 7 = 0 from rfl, v6, v5, v4, v3, v2, v1, v0] at h
    generalize a 7 = x at h ⊢
    push_cast at h
    omega
  have v8 : a 8 = 249 := by
    have h := recur 8 (by norm_num)
    rw [show (8 : ℕ) - 1 = 7 from rfl, show (8 : ℕ) - 2 = 6 from rfl, show (8 : ℕ) - 3 = 5 from rfl, show (8 : ℕ) - 4 = 4 from rfl, show (8 : ℕ) - 5 = 3 from rfl, show (8 : ℕ) - 6 = 2 from rfl, show (8 : ℕ) - 7 = 1 from rfl, v7, v6, v5, v4, v3, v2, v1] at h
    generalize a 8 = x at h ⊢
    push_cast at h
    omega
  have v9 : a 9 = 455 := by
    have h := recur 9 (by norm_num)
    rw [show (9 : ℕ) - 1 = 8 from rfl, show (9 : ℕ) - 2 = 7 from rfl, show (9 : ℕ) - 3 = 6 from rfl, show (9 : ℕ) - 4 = 5 from rfl, show (9 : ℕ) - 5 = 4 from rfl, show (9 : ℕ) - 6 = 3 from rfl, show (9 : ℕ) - 7 = 2 from rfl, v8, v7, v6, v5, v4, v3, v2] at h
    generalize a 9 = x at h ⊢
    push_cast at h
    omega
  have v10 : a 10 = 1083 := by
    have h := recur 10 (by norm_num)
    rw [show (10 : ℕ) - 1 = 9 from rfl, show (10 : ℕ) - 2 = 8 from rfl, show (10 : ℕ) - 3 = 7 from rfl, show (10 : ℕ) - 4 = 6 from rfl, show (10 : ℕ) - 5 = 5 from rfl, show (10 : ℕ) - 6 = 4 from rfl, show (10 : ℕ) - 7 = 3 from rfl, v9, v8, v7, v6, v5, v4, v3] at h
    generalize a 10 = x at h ⊢
    push_cast at h
    omega
  have v11 : a 11 = 1993 := by
    have h := recur 11 (by norm_num)
    rw [show (11 : ℕ) - 1 = 10 from rfl, show (11 : ℕ) - 2 = 9 from rfl, show (11 : ℕ) - 3 = 8 from rfl, show (11 : ℕ) - 4 = 7 from rfl, show (11 : ℕ) - 5 = 6 from rfl, show (11 : ℕ) - 6 = 5 from rfl, show (11 : ℕ) - 7 = 4 from rfl, v10, v9, v8, v7, v6, v5, v4] at h
    generalize a 11 = x at h ⊢
    push_cast at h
    omega
  have v12 : a 12 = 4693 := by
    have h := recur 12 (by norm_num)
    rw [show (12 : ℕ) - 1 = 11 from rfl, show (12 : ℕ) - 2 = 10 from rfl, show (12 : ℕ) - 3 = 9 from rfl, show (12 : ℕ) - 4 = 8 from rfl, show (12 : ℕ) - 5 = 7 from rfl, show (12 : ℕ) - 6 = 6 from rfl, show (12 : ℕ) - 7 = 5 from rfl, v11, v10, v9, v8, v7, v6, v5] at h
    generalize a 12 = x at h ⊢
    push_cast at h
    omega
  have v13 : a 13 = 8679 := by
    have h := recur 13 (by norm_num)
    rw [show (13 : ℕ) - 1 = 12 from rfl, show (13 : ℕ) - 2 = 11 from rfl, show (13 : ℕ) - 3 = 10 from rfl, show (13 : ℕ) - 4 = 9 from rfl, show (13 : ℕ) - 5 = 8 from rfl, show (13 : ℕ) - 6 = 7 from rfl, show (13 : ℕ) - 7 = 6 from rfl, v12, v11, v10, v9, v8, v7, v6] at h
    generalize a 13 = x at h ⊢
    push_cast at h
    omega
  have v14 : a 14 = 20275 := by
    have h := recur 14 (by norm_num)
    rw [show (14 : ℕ) - 1 = 13 from rfl, show (14 : ℕ) - 2 = 12 from rfl, show (14 : ℕ) - 3 = 11 from rfl, show (14 : ℕ) - 4 = 10 from rfl, show (14 : ℕ) - 5 = 9 from rfl, show (14 : ℕ) - 6 = 8 from rfl, show (14 : ℕ) - 7 = 7 from rfl, v13, v12, v11, v10, v9, v8, v7] at h
    generalize a 14 = x at h ⊢
    push_cast at h
    omega
  have v15 : a 15 = 37633 := by
    have h := recur 15 (by norm_num)
    rw [show (15 : ℕ) - 1 = 14 from rfl, show (15 : ℕ) - 2 = 13 from rfl, show (15 : ℕ) - 3 = 12 from rfl, show (15 : ℕ) - 4 = 11 from rfl, show (15 : ℕ) - 5 = 10 from rfl, show (15 : ℕ) - 6 = 9 from rfl, show (15 : ℕ) - 7 = 8 from rfl, v14, v13, v12, v11, v10, v9, v8] at h
    generalize a 15 = x at h ⊢
    push_cast at h
    omega
  have v16 : a 16 = 87377 := by
    have h := recur 16 (by norm_num)
    rw [show (16 : ℕ) - 1 = 15 from rfl, show (16 : ℕ) - 2 = 14 from rfl, show (16 : ℕ) - 3 = 13 from rfl, show (16 : ℕ) - 4 = 12 from rfl, show (16 : ℕ) - 5 = 11 from rfl, show (16 : ℕ) - 6 = 10 from rfl, show (16 : ℕ) - 7 = 9 from rfl, v15, v14, v13, v12, v11, v10, v9] at h
    generalize a 16 = x at h ⊢
    push_cast at h
    omega
  have v17 : a 17 = 162643 := by
    have h := recur 17 (by norm_num)
    rw [show (17 : ℕ) - 1 = 16 from rfl, show (17 : ℕ) - 2 = 15 from rfl, show (17 : ℕ) - 3 = 14 from rfl, show (17 : ℕ) - 4 = 13 from rfl, show (17 : ℕ) - 5 = 12 from rfl, show (17 : ℕ) - 6 = 11 from rfl, show (17 : ℕ) - 7 = 10 from rfl, v16, v15, v14, v13, v12, v11, v10] at h
    generalize a 17 = x at h ⊢
    push_cast at h
    omega
  have v18 : a 18 = 375789 := by
    have h := recur 18 (by norm_num)
    rw [show (18 : ℕ) - 1 = 17 from rfl, show (18 : ℕ) - 2 = 16 from rfl, show (18 : ℕ) - 3 = 15 from rfl, show (18 : ℕ) - 4 = 14 from rfl, show (18 : ℕ) - 5 = 13 from rfl, show (18 : ℕ) - 6 = 12 from rfl, show (18 : ℕ) - 7 = 11 from rfl, v17, v16, v15, v14, v13, v12, v11] at h
    generalize a 18 = x at h ⊢
    push_cast at h
    omega
  have v19 : a 19 = 701075 := by
    have h := recur 19 (by norm_num)
    rw [show (19 : ℕ) - 1 = 18 from rfl, show (19 : ℕ) - 2 = 17 from rfl, show (19 : ℕ) - 3 = 16 from rfl, show (19 : ℕ) - 4 = 15 from rfl, show (19 : ℕ) - 5 = 14 from rfl, show (19 : ℕ) - 6 = 13 from rfl, show (19 : ℕ) - 7 = 12 from rfl, v18, v17, v16, v15, v14, v13, v12] at h
    generalize a 19 = x at h ⊢
    push_cast at h
    omega
  have v20 : a 20 = 1613413 := by
    have h := recur 20 (by norm_num)
    rw [show (20 : ℕ) - 1 = 19 from rfl, show (20 : ℕ) - 2 = 18 from rfl, show (20 : ℕ) - 3 = 17 from rfl, show (20 : ℕ) - 4 = 16 from rfl, show (20 : ℕ) - 5 = 15 from rfl, show (20 : ℕ) - 6 = 14 from rfl, show (20 : ℕ) - 7 = 13 from rfl, v19, v18, v17, v16, v15, v14, v13] at h
    generalize a 20 = x at h ⊢
    push_cast at h
    omega
  have v21 : a 21 = 3015563 := by
    have h := recur 21 (by norm_num)
    rw [show (21 : ℕ) - 1 = 20 from rfl, show (21 : ℕ) - 2 = 19 from rfl, show (21 : ℕ) - 3 = 18 from rfl, show (21 : ℕ) - 4 = 17 from rfl, show (21 : ℕ) - 5 = 16 from rfl, show (21 : ℕ) - 6 = 15 from rfl, show (21 : ℕ) - 7 = 14 from rfl, v20, v19, v18, v17, v16, v15, v14] at h
    generalize a 21 = x at h ⊢
    push_cast at h
    omega
  have v22 : a 22 = 6916957 := by
    have h := recur 22 (by norm_num)
    rw [show (22 : ℕ) - 1 = 21 from rfl, show (22 : ℕ) - 2 = 20 from rfl, show (22 : ℕ) - 3 = 19 from rfl, show (22 : ℕ) - 4 = 18 from rfl, show (22 : ℕ) - 5 = 17 from rfl, show (22 : ℕ) - 6 = 16 from rfl, show (22 : ℕ) - 7 = 15 from rfl, v21, v20, v19, v18, v17, v16, v15] at h
    generalize a 22 = x at h ⊢
    push_cast at h
    omega
  have v23 : a 23 = 12948083 := by
    have h := recur 23 (by norm_num)
    rw [show (23 : ℕ) - 1 = 22 from rfl, show (23 : ℕ) - 2 = 21 from rfl, show (23 : ℕ) - 3 = 20 from rfl, show (23 : ℕ) - 4 = 19 from rfl, show (23 : ℕ) - 5 = 18 from rfl, show (23 : ℕ) - 6 = 17 from rfl, show (23 : ℕ) - 7 = 16 from rfl, v22, v21, v20, v19, v18, v17, v16] at h
    generalize a 23 = x at h ⊢
    push_cast at h
    omega
  have v24 : a 24 = 29617161 := by
    have h := recur 24 (by norm_num)
    rw [show (24 : ℕ) - 1 = 23 from rfl, show (24 : ℕ) - 2 = 22 from rfl, show (24 : ℕ) - 3 = 21 from rfl, show (24 : ℕ) - 4 = 20 from rfl, show (24 : ℕ) - 5 = 19 from rfl, show (24 : ℕ) - 6 = 18 from rfl, show (24 : ℕ) - 7 = 17 from rfl, v23, v22, v21, v20, v19, v18, v17] at h
    generalize a 24 = x at h ⊢
    push_cast at h
    omega
  have v25 : a 25 = 55513327 := by
    have h := recur 25 (by norm_num)
    rw [show (25 : ℕ) - 1 = 24 from rfl, show (25 : ℕ) - 2 = 23 from rfl, show (25 : ℕ) - 3 = 22 from rfl, show (25 : ℕ) - 4 = 21 from rfl, show (25 : ℕ) - 5 = 20 from rfl, show (25 : ℕ) - 6 = 19 from rfl, show (25 : ℕ) - 7 = 18 from rfl, v24, v23, v22, v21, v20, v19, v18] at h
    generalize a 25 = x at h ⊢
    push_cast at h
    omega
  have v26 : a 26 = 126678893 := by
    have h := recur 26 (by norm_num)
    rw [show (26 : ℕ) - 1 = 25 from rfl, show (26 : ℕ) - 2 = 24 from rfl, show (26 : ℕ) - 3 = 23 from rfl, show (26 : ℕ) - 4 = 22 from rfl, show (26 : ℕ) - 5 = 21 from rfl, show (26 : ℕ) - 6 = 20 from rfl, show (26 : ℕ) - 7 = 19 from rfl, v25, v24, v23, v22, v21, v20, v19] at h
    generalize a 26 = x at h ⊢
    push_cast at h
    omega
  have v27 : a 27 = 237705547 := by
    have h := recur 27 (by norm_num)
    rw [show (27 : ℕ) - 1 = 26 from rfl, show (27 : ℕ) - 2 = 25 from rfl, show (27 : ℕ) - 3 = 24 from rfl, show (27 : ℕ) - 4 = 23 from rfl, show (27 : ℕ) - 5 = 22 from rfl, show (27 : ℕ) - 6 = 21 from rfl, show (27 : ℕ) - 7 = 20 from rfl, v26, v25, v24, v23, v22, v21, v20] at h
    generalize a 27 = x at h ⊢
    push_cast at h
    omega
  have v28 : a 28 = 541325021 := by
    have h := recur 28 (by norm_num)
    rw [show (28 : ℕ) - 1 = 27 from rfl, show (28 : ℕ) - 2 = 26 from rfl, show (28 : ℕ) - 3 = 25 from rfl, show (28 : ℕ) - 4 = 24 from rfl, show (28 : ℕ) - 5 = 23 from rfl, show (28 : ℕ) - 6 = 22 from rfl, show (28 : ℕ) - 7 = 21 from rfl, v27, v26, v25, v24, v23, v22, v21] at h
    generalize a 28 = x at h ⊢
    push_cast at h
    omega
  have v29 : a 29 = 1016736115 := by
    have h := recur 29 (by norm_num)
    rw [show (29 : ℕ) - 1 = 28 from rfl, show (29 : ℕ) - 2 = 27 from rfl, show (29 : ℕ) - 3 = 26 from rfl, show (29 : ℕ) - 4 = 25 from rfl, show (29 : ℕ) - 5 = 24 from rfl, show (29 : ℕ) - 6 = 23 from rfl, show (29 : ℕ) - 7 = 22 from rfl, v28, v27, v26, v25, v24, v23, v22] at h
    generalize a 29 = x at h ⊢
    push_cast at h
    omega
  have v30 : a 30 = 2311294377 := by
    have h := recur 30 (by norm_num)
    rw [show (30 : ℕ) - 1 = 29 from rfl, show (30 : ℕ) - 2 = 28 from rfl, show (30 : ℕ) - 3 = 27 from rfl, show (30 : ℕ) - 4 = 26 from rfl, show (30 : ℕ) - 5 = 25 from rfl, show (30 : ℕ) - 6 = 24 from rfl, show (30 : ℕ) - 7 = 23 from rfl, v29, v28, v27, v26, v25, v24, v23] at h
    generalize a 30 = x at h ⊢
    push_cast at h
    omega
  exact ⟨v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13, v14, v15, v16, v17, v18, v19, v20, v21, v22, v23, v24, v25, v26, v27, v28, v29, v30⟩

/-- Mathar's conjecture. -/
theorem conjecture : ∀ n : ℕ, 7 ≤ n →
      (-(n : ℤ) + 2) * (a n : ℤ) + ((n : ℤ) - 2) * (a (n - 1) : ℤ) + 2 * (4 * (n : ℤ) - 13) * (a (n - 2) : ℤ) + 8 * (-(n : ℤ) + 4) * (a (n - 3) : ℤ) + 5 * (-3 * (n : ℤ) + 14) * (a (n - 4) : ℤ) + (15 * (n : ℤ) - 94) * (a (n - 5) : ℤ) + 2 * (-2 * (n : ℤ) + 9) * (a (n - 6) : ℤ) + 4 * ((n : ℤ) - 6) * (a (n - 7) : ℤ) = 0 :=
  recur

end OMA.S_oeis_a026733

theorem OMA.solution : type_of% @OMA.S_oeis_a026733.main :=
  OMA.S_oeis_a026733.conjecture
