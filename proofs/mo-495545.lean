import OMAStatements.S_mo_495545
import Mathlib

/-!
Proof of the identity for the triangle of OEIS A078121 (MathOverflow 495545).

Write `M` for the lower triangular array `T`, `D` for the diagonal sign array and `S` for the shift.
The recursion says that `T (a + k) (b + k)` is the `2^k`-th power of `M`. We show that `D M D` is
the inverse of `M`, so `P = M - D M D` commutes with every power of `M`, and then prove by
induction on `k` that `P` applied to column `k` shifted up by one gives column `k + 1` (shifted)
minus the first unit vector. The entries of `P` are `T a c * (1 - (-1)^(a + c))`.
-/

open Finset

namespace OMA.Helpers

/-- Product of a lower triangular array with a column vector, truncated at the row index. -/
def mo495545App (A : ℕ → ℕ → ℤ) (v : ℕ → ℤ) (a : ℕ) : ℤ :=
  ∑ c ∈ range (a + 1), A a c * v c

/-- Product of two lower triangular arrays. -/
def mo495545Mul (A B : ℕ → ℕ → ℤ) (a b : ℕ) : ℤ :=
  mo495545App A (fun c => B c b) a

/-- Lower triangularity. -/
def mo495545Low (A : ℕ → ℕ → ℤ) : Prop := ∀ a b, a < b → A a b = 0

theorem mo495545_sum_ext (A : ℕ → ℕ → ℤ) (hA : mo495545Low A) (v : ℕ → ℤ) (a N : ℕ)
    (hN : a + 1 ≤ N) :
    ∑ c ∈ range N, A a c * v c = ∑ c ∈ range (a + 1), A a c * v c := by
  symm
  apply Finset.sum_subset (Finset.range_subset_range.mpr hN)
  intro c hc hc'
  simp only [Finset.mem_range] at hc hc'
  rw [hA a c (by omega), zero_mul]

theorem mo495545_app_assoc (A B : ℕ → ℕ → ℤ) (hB : mo495545Low B) (v : ℕ → ℤ) (a : ℕ) :
    mo495545App A (mo495545App B v) a = mo495545App (mo495545Mul A B) v a := by
  simp only [mo495545Mul, mo495545App]
  calc ∑ c ∈ range (a + 1), A a c * ∑ e ∈ range (c + 1), B c e * v e
      = ∑ c ∈ range (a + 1), A a c * ∑ e ∈ range (a + 1), B c e * v e := by
        refine Finset.sum_congr rfl (fun c hc => ?_)
        rw [mo495545_sum_ext B hB v c (a + 1) (by simp only [Finset.mem_range] at hc; omega)]
    _ = ∑ c ∈ range (a + 1), ∑ e ∈ range (a + 1), A a c * (B c e * v e) := by
        refine Finset.sum_congr rfl (fun c _ => ?_)
        rw [Finset.mul_sum]
    _ = ∑ e ∈ range (a + 1), ∑ c ∈ range (a + 1), A a c * (B c e * v e) := Finset.sum_comm
    _ = ∑ e ∈ range (a + 1), (∑ c ∈ range (a + 1), A a c * B c e) * v e := by
        refine Finset.sum_congr rfl (fun e _ => ?_)
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl (fun c _ => ?_)
        ring

theorem mo495545_mul_assoc (A B C : ℕ → ℕ → ℤ) (hB : mo495545Low B) :
    mo495545Mul (mo495545Mul A B) C = mo495545Mul A (mo495545Mul B C) := by
  funext a b
  simp only [mo495545Mul]
  rw [← mo495545_app_assoc A B hB]

theorem mo495545_low_mul (A B : ℕ → ℕ → ℤ) (hB : mo495545Low B) :
    mo495545Low (mo495545Mul A B) := by
  intro a b hab
  simp only [mo495545Mul, mo495545App]
  apply Finset.sum_eq_zero
  intro c hc
  simp only [Finset.mem_range] at hc
  rw [hB c b (by omega), mul_zero]

theorem mo495545_app_congr (A : ℕ → ℕ → ℤ) (v w : ℕ → ℤ) (a : ℕ)
    (h : ∀ c, c ≤ a → v c = w c) : mo495545App A v a = mo495545App A w a := by
  simp only [mo495545App]
  refine Finset.sum_congr rfl (fun c hc => ?_)
  simp only [Finset.mem_range] at hc
  rw [h c (by omega)]

theorem mo495545_app_delta (A : ℕ → ℕ → ℤ) (a : ℕ) :
    mo495545App A (fun c => if c = 0 then 1 else 0) a = A a 0 := by
  simp only [mo495545App, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq' (range (a + 1)) 0 (fun c => A a c)]
  simp only [Finset.mem_range, Nat.zero_lt_succ, if_true]

section

variable (T : ℕ → ℕ → ℤ) (h0 : ∀ n, T n 0 = 1) (hz : ∀ n k, n < k → T n k = 0)
  (hr : ∀ n k, T (n + 1) (k + 1) = ∑ i ∈ Finset.range (n + 1), T n i * T i k)

include h0 hz hr in
theorem mo495545_diag : ∀ n, T n n = 1 := by
  intro n
  induction n with
  | zero => exact h0 0
  | succ n ih =>
    rw [hr n n, Finset.sum_range_succ, Finset.sum_eq_zero, ih]
    · ring
    · intro i hi
      simp only [Finset.mem_range] at hi
      rw [hz i n hi, mul_zero]

include hr in
theorem mo495545_shift (n k : ℕ) : T (n + 1) (k + 1) = mo495545Mul T T n k := by
  rw [hr n k]
  rfl

include h0 hz hr in
/-- The alternating row sums vanish except in row zero. -/
theorem mo495545_alt : ∀ n, mo495545App T (fun i => (-1 : ℤ) ^ i) n = if n = 0 then 1 else 0 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases n with _ | n
    · simp [mo495545App, h0]
    · simp only [mo495545App]
      rw [Finset.sum_range_succ']
      have hstep : ∀ i ∈ range (n + 1), T (n + 1) (i + 1) * (-1 : ℤ) ^ (i + 1)
          = -(mo495545Mul T T n i * (-1 : ℤ) ^ i) := by
        intro i _
        rw [mo495545_shift T hr n i, pow_succ]
        ring
      rw [Finset.sum_congr rfl hstep, Finset.sum_neg_distrib]
      have h2 : ∑ i ∈ range (n + 1), mo495545Mul T T n i * (-1 : ℤ) ^ i
          = mo495545App (mo495545Mul T T) (fun i => (-1 : ℤ) ^ i) n := rfl
      rw [h2, ← mo495545_app_assoc T T hz]
      rw [mo495545_app_congr T _ (fun c => if c = 0 then 1 else 0) n
        (fun c hc => ih c (by omega))]
      rw [mo495545_app_delta]
      simp [h0]

/-- The array `(-1)^i * T i b`. -/
def mo495545D (T : ℕ → ℕ → ℤ) (i b : ℕ) : ℤ := (-1 : ℤ) ^ i * T i b

include hz in
theorem mo495545_low_D : mo495545Low (mo495545D T) := by
  intro a b hab
  simp only [mo495545D]
  rw [hz a b hab, mul_zero]

include h0 hz hr in
/-- `M D M = D`. -/
theorem mo495545_inv : ∀ n k, mo495545Mul T (mo495545D T) n k = if n = k then (-1 : ℤ) ^ k else 0 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro k
    rcases n with _ | n
    · simp only [mo495545Mul, mo495545App, mo495545D, zero_add, Finset.sum_range_one, h0, pow_zero,
        one_mul]
      rcases k with _ | k
      · simp [h0]
      · rw [hz 0 (k + 1) (by omega)]
        simp
    · rcases k with _ | k
      · have h1 : mo495545Mul T (mo495545D T) (n + 1) 0 = mo495545App T (fun i => (-1 : ℤ) ^ i) (n + 1) := by
          simp only [mo495545Mul, mo495545App, mo495545D, h0, mul_one]
        rw [h1, mo495545_alt T h0 hz hr]
        simp
      · have h1 : mo495545Mul T (mo495545D T) (n + 1) (k + 1)
            = -mo495545App (mo495545Mul T T) (fun i => mo495545Mul (mo495545D T) T i k) n := by
          simp only [mo495545Mul, mo495545App, mo495545D]
          rw [Finset.sum_range_succ', hz 0 (k + 1) (by omega), mul_zero, mul_zero, add_zero,
            ← Finset.sum_neg_distrib]
          refine Finset.sum_congr rfl (fun i _ => ?_)
          rw [hr n i, hr i k, pow_succ]
          have hb : ∑ b ∈ range (i + 1), (-1 : ℤ) ^ i * T i b * T b k
              = (-1 : ℤ) ^ i * ∑ b ∈ range (i + 1), T i b * T b k := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl (fun b _ => ?_)
            ring
          rw [hb]
          ring
        rw [h1]
        have h2 : (fun i => mo495545Mul (mo495545D T) T i k)
            = mo495545App (mo495545D T) (fun b => T b k) := rfl
        rw [h2, mo495545_app_assoc _ _ (mo495545_low_D T hz),
          mo495545_mul_assoc T T _ hz, ← mo495545_app_assoc T _ (mo495545_low_mul T _ (mo495545_low_D T hz))]
        have h3 : ∀ c, c ≤ n → mo495545App (mo495545Mul T (mo495545D T)) (fun b => T b k) c
            = (-1 : ℤ) ^ c * T c k := by
          intro c hc
          simp only [mo495545App]
          rw [Finset.sum_congr rfl (fun b _ => by rw [ih c (by omega) b])]
          simp only [ite_mul, zero_mul]
          rw [Finset.sum_ite_eq (range (c + 1)) c (fun b => (-1 : ℤ) ^ b * T b k)]
          simp
        rw [mo495545_app_congr T _ _ n h3]
        have h4 : mo495545App T (fun c => (-1 : ℤ) ^ c * T c k) n = mo495545Mul T (mo495545D T) n k := rfl
        rw [h4, ih n (by omega) k]
        by_cases hnk : n = k
        · subst hnk
          simp [pow_succ]
        · have : ¬ (n + 1 = k + 1) := by omega
          simp [hnk]

/-- `D M D`, the inverse of `M`. -/
def mo495545Q (T : ℕ → ℕ → ℤ) (i b : ℕ) : ℤ := (-1 : ℤ) ^ i * T i b * (-1 : ℤ) ^ b

include hz in
theorem mo495545_low_Q : mo495545Low (mo495545Q T) := by
  intro a b hab
  simp only [mo495545Q]
  rw [hz a b hab, mul_zero, zero_mul]

include h0 hz hr in
theorem mo495545_TQ : mo495545Mul T (mo495545Q T) = fun a b => if a = b then 1 else 0 := by
  funext a b
  have h := mo495545_inv T h0 hz hr a b
  have e : mo495545Mul T (mo495545Q T) a b = mo495545Mul T (mo495545D T) a b * (-1 : ℤ) ^ b := by
    simp only [mo495545Mul, mo495545App, mo495545Q, mo495545D, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun c _ => ?_)
    ring
  rw [e, h]
  by_cases hab : a = b
  · subst hab
    simp only [if_true]
    rw [← pow_add, ← two_mul, pow_mul]
    simp
  · simp [hab]

include h0 hz hr in
theorem mo495545_QT : mo495545Mul (mo495545Q T) T = fun a b => if a = b then 1 else 0 := by
  funext a b
  have h := mo495545_inv T h0 hz hr a b
  have e : mo495545Mul (mo495545Q T) T a b = (-1 : ℤ) ^ a * mo495545Mul T (mo495545D T) a b := by
    simp only [mo495545Mul, mo495545App, mo495545Q, mo495545D, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun c _ => ?_)
    ring
  rw [e, h]
  by_cases hab : a = b
  · subst hab
    simp only [if_true]
    rw [← pow_add, ← two_mul, pow_mul]
    simp
  · simp [hab]

/-- The shifted arrays `A k a b = T (a + k) (b + k)`; `A k` is the `2^k`-th power of `T`. -/
def mo495545A (T : ℕ → ℕ → ℤ) (k a b : ℕ) : ℤ := T (a + k) (b + k)

include hz in
theorem mo495545_low_A (k : ℕ) : mo495545Low (mo495545A T k) := by
  intro a b hab
  exact hz _ _ (by omega)

include hz hr in
theorem mo495545_A_succ (k : ℕ) :
    mo495545A T (k + 1) = mo495545Mul (mo495545A T k) (mo495545A T k) := by
  funext a b
  simp only [mo495545A, mo495545Mul, mo495545App]
  have e1 : a + (k + 1) = (a + k) + 1 := by omega
  have e2 : b + (k + 1) = (b + k) + 1 := by omega
  rw [e1, e2, hr]
  have e3 : a + k + 1 = k + (a + 1) := by omega
  rw [e3, Finset.sum_range_add]
  rw [Finset.sum_eq_zero (s := range k), zero_add]
  · refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [show a + k = k + a by omega, show j + k = k + j by omega]
  · intro i hi
    simp only [Finset.mem_range] at hi
    rw [hz i (b + k) (by omega), mul_zero]

theorem mo495545_A_zero : mo495545A T 0 = T := by
  funext a b
  simp [mo495545A]

theorem mo495545_comm_sq (X Y : ℕ → ℕ → ℤ) (hX : mo495545Low X) (hY : mo495545Low Y)
    (h : mo495545Mul Y X = mo495545Mul X Y) :
    mo495545Mul Y (mo495545Mul X X) = mo495545Mul (mo495545Mul X X) Y := by
  rw [← mo495545_mul_assoc Y X X hX, h, mo495545_mul_assoc X Y X hY, h,
    ← mo495545_mul_assoc X X Y hX]

include h0 hz hr in
theorem mo495545_comm_A (k : ℕ) :
    mo495545Mul T (mo495545A T k) = mo495545Mul (mo495545A T k) T ∧
    mo495545Mul (mo495545Q T) (mo495545A T k) = mo495545Mul (mo495545A T k) (mo495545Q T) := by
  induction k with
  | zero =>
    rw [mo495545_A_zero]
    exact ⟨rfl, by rw [mo495545_QT T h0 hz hr, mo495545_TQ T h0 hz hr]⟩
  | succ k ih =>
    rw [mo495545_A_succ T hz hr k]
    exact ⟨mo495545_comm_sq _ _ (mo495545_low_A T hz k) hz ih.1,
      mo495545_comm_sq _ _ (mo495545_low_A T hz k) (mo495545_low_Q T hz) ih.2⟩

/-- `P = M - M⁻¹`. -/
def mo495545P (T : ℕ → ℕ → ℤ) (a c : ℕ) : ℤ := T a c - mo495545Q T a c

include hz in
theorem mo495545_low_P : mo495545Low (mo495545P T) := by
  intro a b hab
  simp only [mo495545P]
  rw [hz a b hab, mo495545_low_Q T hz a b hab, sub_zero]

include h0 hz hr in
theorem mo495545_comm_P (k : ℕ) :
    mo495545Mul (mo495545P T) (mo495545A T k) = mo495545Mul (mo495545A T k) (mo495545P T) := by
  have h := mo495545_comm_A T h0 hz hr k
  have e1 : mo495545Mul (mo495545P T) (mo495545A T k)
      = fun a b => mo495545Mul T (mo495545A T k) a b - mo495545Mul (mo495545Q T) (mo495545A T k) a b := by
    funext a b
    simp only [mo495545Mul, mo495545App, mo495545P, sub_mul, Finset.sum_sub_distrib]
  have e2 : mo495545Mul (mo495545A T k) (mo495545P T)
      = fun a b => mo495545Mul (mo495545A T k) T a b - mo495545Mul (mo495545A T k) (mo495545Q T) a b := by
    funext a b
    simp only [mo495545Mul, mo495545App, mo495545P, mul_sub, Finset.sum_sub_distrib]
  rw [e1, e2, h.1, h.2]

include h0 hz hr in
theorem mo495545_key : ∀ k a, mo495545App (mo495545P T) (fun c => mo495545A T k (c + 1) 0) a
    = mo495545A T (k + 1) a 0 - (if a = 0 then 1 else 0) := by
  intro k
  induction k with
  | zero =>
    intro a
    simp only [mo495545A, add_zero, h0]
    have e1 : mo495545App (mo495545P T) (fun _ => (1 : ℤ)) a
        = mo495545App T (fun _ => (1 : ℤ)) a - (-1 : ℤ) ^ a * mo495545Mul T (mo495545D T) a 0 := by
      simp only [mo495545App, mo495545Mul, mo495545P, mo495545Q, mo495545D, sub_mul,
        Finset.sum_sub_distrib, Finset.mul_sum, h0]
      congr 1
      refine Finset.sum_congr rfl (fun c _ => ?_)
      ring
    rw [e1, mo495545_inv T h0 hz hr a 0]
    have e2 : mo495545App T (fun _ => (1 : ℤ)) a = T (a + 1) (0 + 1) := by
      rw [hr a 0]
      simp only [mo495545App, h0]
    rw [e2]
    by_cases ha : a = 0
    · subst ha
      simp
    · simp [ha]
  | succ k ih =>
    intro a
    set X := mo495545A T k with hXdef
    have hX : mo495545Low X := mo495545_low_A T hz k
    have hY : mo495545A T (k + 1) = mo495545Mul X X := mo495545_A_succ T hz hr k
    -- s' = Y s + s
    have hs : (fun c => mo495545A T (k + 1) (c + 1) 0)
        = fun c => mo495545App (mo495545A T (k + 1)) (fun e => X (e + 1) 0) c + X (c + 1) 0 := by
      funext c
      rw [show mo495545A T (k + 1) (c + 1) 0 = mo495545Mul X X (c + 1) 0 by rw [hY]]
      simp only [mo495545Mul, mo495545App]
      rw [Finset.sum_range_succ' (fun e => X (c + 1) e * X e 0)]
      have hX00 : X 0 0 = 1 := by
        simp only [hXdef, mo495545A, zero_add]
        exact mo495545_diag T h0 hz hr k
      rw [hX00, mul_one]
      congr 1
      refine Finset.sum_congr rfl (fun e _ => ?_)
      simp only [hXdef, mo495545A]
      rw [show c + 1 + k = c + (k + 1) by omega, show e + 1 + k = e + (k + 1) by omega]
    rw [hs]
    have e1 : mo495545App (mo495545P T)
        (fun c => mo495545App (mo495545A T (k + 1)) (fun e => X (e + 1) 0) c + X (c + 1) 0) a
        = mo495545App (mo495545P T) (mo495545App (mo495545A T (k + 1)) (fun e => X (e + 1) 0)) a
          + mo495545App (mo495545P T) (fun c => X (c + 1) 0) a := by
      simp only [mo495545App, mul_add, Finset.sum_add_distrib]
    rw [e1, ih a, mo495545_app_assoc _ _ (mo495545_low_A T hz (k + 1)), mo495545_comm_P T h0 hz hr (k + 1),
      ← mo495545_app_assoc _ _ (mo495545_low_P T hz)]
    rw [mo495545_app_congr _ _ (fun c => mo495545A T (k + 1) c 0 - (if c = 0 then 1 else 0)) a
      (fun c _ => ih c)]
    have e2 : mo495545App (mo495545A T (k + 1)) (fun c => mo495545A T (k + 1) c 0 - (if c = 0 then 1 else 0)) a
        = mo495545Mul (mo495545A T (k + 1)) (mo495545A T (k + 1)) a 0
          - mo495545App (mo495545A T (k + 1)) (fun c => if c = 0 then 1 else 0) a := by
      simp only [mo495545App, mo495545Mul, mul_sub, Finset.sum_sub_distrib]
    rw [e2, mo495545_app_delta, ← mo495545_A_succ T hz hr (k + 1)]
    ring

end

end OMA.Helpers

open OMA.Helpers in
theorem OMA.solution : type_of% @OMA.S_mo_495545.main := by
  intro T h0 hz hr n k hk hkn
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  obtain ⟨a, rfl⟩ : ∃ a, n = a + (k' + 1) := ⟨n - (k' + 1), by omega⟩
  have ha : 0 < a := by omega
  have key := mo495545_key T h0 hz hr k' a
  rw [show a + (k' + 1) - (k' + 1) = a by omega, show k' + 1 - 1 = k' by omega]
  have hlhs : mo495545A T (k' + 1) a 0 = T (a + (k' + 1)) (k' + 1) := by
    simp [mo495545A]
  rw [hlhs, if_neg (by omega), sub_zero] at key
  rw [← key]
  simp only [mo495545App, mo495545P, mo495545Q, mo495545A]
  rw [Finset.sum_range_succ, mo495545_diag T h0 hz hr a]
  have hlast : ((1 : ℤ) - (-1 : ℤ) ^ a * 1 * (-1 : ℤ) ^ a) = 0 := by
    rw [mul_one, ← pow_add, ← two_mul, pow_mul]
    simp
  rw [hlast, zero_mul, add_zero]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  have hp : (-1 : ℤ) ^ (a + (k' + 1) + (k' + 1) + i + 1) = -((-1 : ℤ) ^ a * (-1 : ℤ) ^ i) := by
    rw [show a + (k' + 1) + (k' + 1) + i + 1 = (a + i + 1) + 2 * (k' + 1) by omega, pow_add, pow_mul,
      pow_add, pow_add]
    simp
  rw [hp, show i + 1 + k' = k' + 1 + i by omega, show 0 + k' = k' by omega]
  ring
