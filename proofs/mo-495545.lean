import OMAStatements.S_mo_495545
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Ring

open scoped BigOperators

namespace Mo495545Proof

private def isLower (A : ℕ → ℕ → ℤ) : Prop :=
  ∀ n k, n < k → A n k = 0

private def idMat (n k : ℕ) : ℤ :=
  if n = k then 1 else 0

private def matMul (A B : ℕ → ℕ → ℤ) (n k : ℕ) : ℤ :=
  ∑ i ∈ Finset.range (n + 1), A n i * B i k

private def shiftMat (A : ℕ → ℕ → ℤ) (n k : ℕ) : ℤ :=
  A (n + 1) (k + 1)

private def signConj (A : ℕ → ℕ → ℤ) (n k : ℕ) : ℤ :=
  (-1 : ℤ) ^ (n + k) * A n k

private def matVec (A : ℕ → ℕ → ℤ) (v : ℕ → ℤ) (n : ℕ) : ℤ :=
  ∑ i ∈ Finset.range (n + 1), A n i * v i

private def shiftVec (v : ℕ → ℤ) (n : ℕ) : ℤ :=
  v (n + 1)

private def e0 (n : ℕ) : ℤ :=
  if n = 0 then 1 else 0

private def matPow (A : ℕ → ℕ → ℤ) : ℕ → ℕ → ℕ → ℤ
  | 0 => idMat
  | p + 1 => matMul (matPow A p) A

private lemma isLower_idMat : isLower idMat := by
  intro n k hnk
  simp [idMat, hnk.ne]

private lemma isLower_matMul {A B : ℕ → ℕ → ℤ} (hB : isLower B) :
    isLower (matMul A B) := by
  intro n k hnk
  apply Finset.sum_eq_zero
  intro i hi
  rw [Finset.mem_range] at hi
  rw [hB i k (by omega), mul_zero]

private lemma isLower_signConj {A : ℕ → ℕ → ℤ} (hA : isLower A) :
    isLower (signConj A) := by
  intro n k hnk
  simp [signConj, hA n k hnk]

private lemma isLower_matPow {A : ℕ → ℕ → ℤ} (hA : isLower A) (p : ℕ) :
    isLower (matPow A p) := by
  induction p with
  | zero => exact isLower_idMat
  | succ p _ => exact isLower_matMul hA

private lemma idMat_matMul (A : ℕ → ℕ → ℤ) :
    matMul idMat A = A := by
  funext n k
  unfold matMul idMat
  rw [Finset.sum_eq_single n]
  · simp
  · intro i _ hin
    simp [hin.symm]
  · intro hn
    exfalso
    exact hn (Finset.mem_range.mpr (Nat.lt_succ_self n))

private lemma matMul_idMat {A : ℕ → ℕ → ℤ} (hA : isLower A) :
    matMul A idMat = A := by
  funext n k
  unfold matMul idMat
  by_cases hk : k ≤ n
  · rw [Finset.sum_eq_single k]
    · simp
    · intro i _ hik
      simp [hik]
    · intro hkn
      exfalso
      exact hkn (Finset.mem_range.mpr (by omega))
  · rw [hA n k (by omega)]
    apply Finset.sum_eq_zero
    intro i hi
    rw [Finset.mem_range] at hi
    have hik : i ≠ k := by omega
    simp [hik]

private lemma matMul_assoc (A : ℕ → ℕ → ℤ) {B : ℕ → ℕ → ℤ} (hB : isLower B)
    (C : ℕ → ℕ → ℤ) :
    matMul (matMul A B) C = matMul A (matMul B C) := by
  funext n k
  unfold matMul
  simp_rw [Finset.sum_mul, Finset.mul_sum]
  have hcomm : ∑ j ∈ Finset.range (n + 1), ∑ i ∈ Finset.range (n + 1), A n i * B i j * C j k =
      ∑ i ∈ Finset.range (n + 1), ∑ j ∈ Finset.range (n + 1), A n i * B i j * C j k :=
    Finset.sum_comm
  rw [hcomm]
  simp_rw [mul_assoc]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [Finset.mem_range] at hi
  symm
  refine Finset.sum_subset (Finset.range_mono (Nat.succ_le_succ (Nat.lt_succ_iff.mp hi)))
    fun j hj hjn => ?_
  rw [Finset.mem_range] at hj hjn
  rw [hB i j (by omega), zero_mul, mul_zero]

private lemma shiftMat_matMul (A : ℕ → ℕ → ℤ) {B : ℕ → ℕ → ℤ} (hB : isLower B) :
    shiftMat (matMul A B) = matMul (shiftMat A) (shiftMat B) := by
  funext n k
  unfold shiftMat matMul
  rw [Finset.sum_range_succ']
  rw [hB 0 (k + 1) (Nat.zero_lt_succ k), mul_zero, add_zero]

private lemma neg_one_pow_add_add (n i k : ℕ) :
    (-1 : ℤ) ^ (n + i) * (-1 : ℤ) ^ (i + k) = (-1 : ℤ) ^ (n + k) := by
  rw [← pow_add, show n + i + (i + k) = (n + k) + 2 * i by omega, pow_add, pow_mul,
    show (-1 : ℤ) ^ 2 = 1 by decide, one_pow, mul_one]

private lemma signConj_matMul (A B : ℕ → ℕ → ℤ) :
    signConj (matMul A B) = matMul (signConj A) (signConj B) := by
  funext n k
  unfold signConj matMul
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  calc
    (-1 : ℤ) ^ (n + k) * (A n i * B i k)
        = ((-1 : ℤ) ^ (n + i) * (-1 : ℤ) ^ (i + k)) * (A n i * B i k) := by
          rw [neg_one_pow_add_add]
    _ = (-1 : ℤ) ^ (n + i) * A n i * ((-1 : ℤ) ^ (i + k) * B i k) := by ring

private lemma signConj_idMat : signConj idMat = idMat := by
  funext n k
  unfold signConj idMat
  split_ifs with h
  · subst h
    rw [show n + n = 2 * n by omega, pow_mul, show (-1 : ℤ) ^ 2 = 1 by decide, one_pow, mul_one]
  · ring

private lemma shiftMat_signConj (A : ℕ → ℕ → ℤ) :
    shiftMat (signConj A) = signConj (shiftMat A) := by
  funext n k
  unfold shiftMat signConj
  rw [show n + 1 + (k + 1) = (n + k) + 2 by omega, pow_add, show (-1 : ℤ) ^ 2 = 1 by decide,
    mul_one]

private lemma signConj_signConj (A : ℕ → ℕ → ℤ) :
    signConj (signConj A) = A := by
  funext n k
  unfold signConj
  rw [← mul_assoc, ← pow_add, show n + k + (n + k) = 2 * (n + k) by omega, pow_mul,
    show (-1 : ℤ) ^ 2 = 1 by decide, one_pow, one_mul]

private lemma matPow_succ_left {A : ℕ → ℕ → ℤ} (hA : isLower A) (p : ℕ) :
    matPow A (p + 1) = matMul A (matPow A p) := by
  induction p with
  | zero =>
    simp [matPow, idMat_matMul, matMul_idMat hA]
  | succ p ih =>
    calc
      matPow A (p + 2) = matMul (matPow A (p + 1)) A := rfl
      _ = matMul (matMul A (matPow A p)) A := by rw [ih]
      _ = matMul A (matMul (matPow A p) A) := matMul_assoc A (isLower_matPow hA p) A
      _ = matMul A (matPow A (p + 1)) := rfl

private lemma matPow_add {A : ℕ → ℕ → ℤ} (hA : isLower A) (a b : ℕ) :
    matPow A (a + b) = matMul (matPow A a) (matPow A b) := by
  induction b with
  | zero =>
    simp [matPow, matMul_idMat (isLower_matPow hA a)]
  | succ b ih =>
    rw [← add_assoc, show matPow A (a + b + 1) = matMul (matPow A (a + b)) A from rfl]
    rw [ih, matMul_assoc (matPow A a) (isLower_matPow hA b) A]
    rfl

private lemma matPow_two_mul {A : ℕ → ℕ → ℤ} (hA : isLower A) (p : ℕ) :
    matPow (matMul A A) p = matPow A (2 * p) := by
  induction p with
  | zero => rfl
  | succ p ih =>
    change matMul (matPow (matMul A A) p) (matMul A A) = matPow A (2 * p + 2)
    rw [ih, ← matMul_assoc (matPow A (2 * p)) hA A]
    rfl

private lemma shiftMat_idMat : shiftMat idMat = idMat := by
  funext n k
  unfold shiftMat idMat
  simp

private lemma shiftMat_matPow {A : ℕ → ℕ → ℤ} (hA : isLower A) (p : ℕ) :
    shiftMat (matPow A p) = matPow (shiftMat A) p := by
  induction p with
  | zero => exact shiftMat_idMat
  | succ p ih =>
    change shiftMat (matMul (matPow A p) A) = matMul (matPow (shiftMat A) p) (shiftMat A)
    rw [shiftMat_matMul (matPow A p) hA, ih]

private lemma shift_iter_eq_matPow (T : ℕ → ℕ → ℤ)
    (hlt : isLower T) (hrec : shiftMat T = matMul T T) (d n k : ℕ) :
    T (n + d) (k + d) = matPow T (2 ^ d) n k := by
  induction d generalizing n k with
  | zero =>
    simp [matPow, idMat_matMul]
  | succ d ih =>
    have h1 : T (n + (d + 1)) (k + (d + 1)) = shiftMat (fun a b => T (a + d) (b + d)) n k := by
      unfold shiftMat
      ring_nf
    have h2 : (fun a b => T (a + d) (b + d)) = matPow T (2 ^ d) := by
      funext a b
      exact ih a b
    rw [h1, h2, shiftMat_matPow hlt (2 ^ d), hrec, matPow_two_mul hlt (2 ^ d),
      show 2 * 2 ^ d = 2 ^ (d + 1) by ring]

private lemma T_mul_signConj (T : ℕ → ℕ → ℤ)
    (h0 : ∀ n, T n 0 = 1) (hlt : isLower T) (hrec : shiftMat T = matMul T T) :
    ∀ n k, matMul T (signConj T) n k = idMat n k := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro k
    cases n with
    | zero =>
      unfold matMul signConj idMat
      rw [Finset.sum_range_one]
      cases k with
      | zero => simp [h0 0]
      | succ k => simp [hlt 0 (k + 1) (Nat.zero_lt_succ k)]
    | succ n =>
      cases k with
      | zero =>
        unfold matMul signConj idMat
        simp only [add_zero]
        rw [Finset.sum_range_succ']
        simp only [pow_zero, h0 0, mul_one]
        have hstep : ∑ j ∈ Finset.range (n + 1), T (n + 1) (j + 1) * ((-1 : ℤ) ^ (j + 1) * T (j + 1) 0) =
            - ∑ r ∈ Finset.range (n + 1), T n r * ∑ j ∈ Finset.range (n + 1), T r j * (-1 : ℤ) ^ j := by
          have hsub : ∀ j ∈ Finset.range (n + 1),
              T (n + 1) (j + 1) * ((-1 : ℤ) ^ (j + 1) * T (j + 1) 0) =
              - (∑ r ∈ Finset.range (n + 1), T n r * (T r j * (-1 : ℤ) ^ j)) := by
            intro j _
            have hT : T (n + 1) (j + 1) = ∑ r ∈ Finset.range (n + 1), T n r * T r j := by
              have := congrFun (congrFun hrec n) j
              simpa [shiftMat, matMul] using this
            rw [h0 (j + 1), mul_one, hT, pow_succ, Finset.sum_mul, ← Finset.sum_neg_distrib]
            refine Finset.sum_congr rfl fun r _ => ?_
            ring
          rw [Finset.sum_congr rfl hsub, Finset.sum_neg_distrib, Finset.sum_comm]
          congr 1
          refine Finset.sum_congr rfl fun r _ => ?_
          rw [← Finset.mul_sum]
        rw [hstep, h0 (n + 1)]
        have hinner : ∑ r ∈ Finset.range (n + 1), T n r * ∑ j ∈ Finset.range (n + 1), T r j * (-1 : ℤ) ^ j = 1 := by
          have hterm : ∀ r ∈ Finset.range (n + 1),
              T n r * ∑ j ∈ Finset.range (n + 1), T r j * (-1 : ℤ) ^ j = T n r * idMat r 0 := by
            intro r hr
            rw [Finset.mem_range] at hr
            congr 1
            have hsum : ∑ j ∈ Finset.range (n + 1), T r j * (-1 : ℤ) ^ j =
                ∑ j ∈ Finset.range (r + 1), T r j * (-1 : ℤ) ^ j := by
              symm
              refine Finset.sum_subset (Finset.range_mono (Nat.succ_le_succ (Nat.lt_succ_iff.mp hr)))
                fun j hj hjn => ?_
              rw [Finset.mem_range] at hj hjn
              rw [hlt r j (by omega), zero_mul]
            rw [hsum]
            have hih := ih r hr 0
            simpa [matMul, signConj, h0] using hih
          rw [Finset.sum_congr rfl hterm]
          have hmid := congrFun (congrFun (matMul_idMat hlt) n) 0
          simpa [matMul, h0 n] using hmid
        rw [hinner]
        simp
      | succ k =>
        have h1 : matMul T (signConj T) (n + 1) (k + 1) =
            shiftMat (matMul T (signConj T)) n k := rfl
        rw [h1, shiftMat_matMul T (isLower_signConj hlt), hrec, shiftMat_signConj, hrec,
          signConj_matMul]
        have hassoc1 := congrFun (congrFun (matMul_assoc (matMul T T) (isLower_signConj hlt) (signConj T)) n) k
        change matMul (matMul T T) (matMul (signConj T) (signConj T)) n k = idMat (n + 1) (k + 1)
        rw [← hassoc1]
        have hmid : matMul (matMul T T) (signConj T) = matMul T (matMul T (signConj T)) :=
          matMul_assoc T hlt (signConj T)
        rw [hmid]
        have hcollapse : ∀ j ∈ Finset.range (n + 1),
            matMul T (matMul T (signConj T)) n j = T n j := by
          intro j _
          unfold matMul
          have hsub : ∀ i ∈ Finset.range (n + 1),
              T n i * (∑ r ∈ Finset.range (i + 1), T i r * signConj T r j) =
              T n i * idMat i j := by
            intro i hi
            rw [Finset.mem_range] at hi
            congr 1
            exact ih i hi j
          rw [Finset.sum_congr rfl hsub]
          have hid := congrFun (congrFun (matMul_idMat hlt) n) j
          simpa [matMul] using hid
        have houter : matMul (matMul T (matMul T (signConj T))) (signConj T) n k =
            matMul T (signConj T) n k := by
          unfold matMul
          refine Finset.sum_congr rfl fun j hj => ?_
          change matMul T (matMul T (signConj T)) n j * signConj T j k = T n j * signConj T j k
          rw [hcollapse j hj]
        rw [houter, ih n (Nat.lt_succ_self n) k]
        simp [idMat]

private lemma signConj_T_mul (T : ℕ → ℕ → ℤ)
    (h0 : ∀ n, T n 0 = 1) (hlt : isLower T) (hrec : shiftMat T = matMul T T) :
    matMul (signConj T) T = idMat := by
  have h1 : matMul T (signConj T) = idMat := by
    funext n k
    exact T_mul_signConj T h0 hlt hrec n k
  have h2 := congrArg signConj h1
  rw [signConj_matMul, signConj_signConj, signConj_idMat] at h2
  exact h2

private lemma matVec_matMul (A : ℕ → ℕ → ℤ) {B : ℕ → ℕ → ℤ} (hB : isLower B)
    (v : ℕ → ℤ) :
    matVec (matMul A B) v = matVec A (matVec B v) := by
  funext n
  unfold matVec matMul
  simp_rw [Finset.sum_mul, Finset.mul_sum]
  have hcomm : ∑ j ∈ Finset.range (n + 1), ∑ i ∈ Finset.range (n + 1), A n i * B i j * v j =
      ∑ i ∈ Finset.range (n + 1), ∑ j ∈ Finset.range (n + 1), A n i * B i j * v j :=
    Finset.sum_comm
  rw [hcomm]
  simp_rw [mul_assoc]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [Finset.mem_range] at hi
  symm
  refine Finset.sum_subset (Finset.range_mono (Nat.succ_le_succ (Nat.lt_succ_iff.mp hi)))
    fun j hj hjn => ?_
  rw [Finset.mem_range] at hj hjn
  rw [hB i j (by omega), zero_mul, mul_zero]

private lemma matVec_idMat (v : ℕ → ℤ) : matVec idMat v = v := by
  funext n
  unfold matVec idMat
  rw [Finset.sum_eq_single n]
  · simp
  · intro i _ hin
    simp [hin.symm]
  · intro hn
    exfalso
    exact hn (Finset.mem_range.mpr (Nat.lt_succ_self n))

private lemma matVec_e0 (A : ℕ → ℕ → ℤ) (n : ℕ) :
    matVec A e0 n = A n 0 := by
  unfold matVec e0
  rw [Finset.sum_eq_single 0]
  · simp
  · intro i _ hi0
    simp [hi0]
  · intro h0
    exfalso
    exact h0 (Finset.mem_range.mpr (Nat.zero_lt_succ n))

private lemma matVec_sum (A : ℕ → ℕ → ℤ) (s : Finset ℕ) (f : ℕ → ℕ → ℤ) (n : ℕ) :
    matVec A (fun i => ∑ j ∈ s, f j i) n = ∑ j ∈ s, matVec A (f j) n := by
  unfold matVec
  simp_rw [Finset.mul_sum]
  exact Finset.sum_comm

private lemma u_zero_col (T : ℕ → ℕ → ℤ) (h0 : ∀ n, T n 0 = 1) (p : ℕ) :
    matPow T p 0 0 = 1 := by
  induction p with
  | zero => simp [matPow, idMat]
  | succ p ih =>
    change matMul (matPow T p) T 0 0 = 1
    simp [matMul, ih, h0 0]

private lemma shiftVec_u_succ (T : ℕ → ℕ → ℤ)
    (h0 : ∀ n, T n 0 = 1) (hlt : isLower T) (hrec : shiftMat T = matMul T T)
    (p m : ℕ) :
    shiftVec (fun n => matPow T (p + 1) n 0) m =
      1 + matVec (matMul T T) (shiftVec (fun n => matPow T p n 0)) m := by
  have hleft : matPow T (p + 1) (m + 1) 0 =
      matVec T (fun n => matPow T p n 0) (m + 1) := by
    rw [matPow_succ_left hlt p, ← matVec_e0 (matMul T (matPow T p)) (m + 1),
      matVec_matMul T (isLower_matPow hlt p) e0]
    congr 1
    funext i
    exact matVec_e0 (matPow T p) i
  change matPow T (p + 1) (m + 1) 0 = _
  rw [hleft]
  unfold matVec
  rw [Finset.sum_range_succ']
  dsimp only
  rw [u_zero_col T h0 p, h0 (m + 1), mul_one, add_comm]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  have hT : T (m + 1) (j + 1) = matMul T T m j := by
    have := congrFun (congrFun hrec m) j
    simpa [shiftMat] using this
  rw [hT]
  rfl

private lemma shiftVec_u_eq_sum (T : ℕ → ℕ → ℤ)
    (h0 : ∀ n, T n 0 = 1) (hlt : isLower T) (hrec : shiftMat T = matMul T T)
    (p m : ℕ) :
    shiftVec (fun n => matPow T p n 0) m =
      ∑ j ∈ Finset.range p, matVec (matPow T (2 * j)) (fun _ => (1 : ℤ)) m := by
  induction p generalizing m with
  | zero =>
    simp [shiftVec, matPow, idMat]
  | succ p ih =>
    rw [shiftVec_u_succ T h0 hlt hrec p m]
    have ih_fun : shiftVec (fun n => matPow T p n 0) =
        fun i => ∑ j ∈ Finset.range p, matVec (matPow T (2 * j)) (fun _ => (1 : ℤ)) i := by
      funext i
      exact ih i
    rw [ih_fun, Finset.sum_range_succ', add_comm (1 : ℤ)]
    congr 1
    · rw [matVec_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [← matVec_matMul (matMul T T) (isLower_matPow hlt (2 * j))]
      have hmul : matMul (matMul T T) (matPow T (2 * j)) = matPow T (2 * (j + 1)) := by
        calc
          matMul (matMul T T) (matPow T (2 * j))
              = matMul (matPow T 2) (matPow T (2 * j)) := by
                congr 1
                simp [matPow, idMat_matMul]
          _ = matPow T (2 + 2 * j) := (matPow_add hlt 2 (2 * j)).symm
          _ = matPow T (2 * (j + 1)) := by ring_nf
      rw [hmul]
    · simp [matPow, matVec_idMat]

private lemma sum_range_sub_int (f : ℕ → ℤ) (p : ℕ) :
    ∑ j ∈ Finset.range p, (f (j + 1) - f j) = f p - f 0 := by
  induction p with
  | zero => simp
  | succ p ih =>
    rw [Finset.sum_range_succ, ih]
    ring

private lemma diff_matVec_shiftVec_u (T : ℕ → ℕ → ℤ)
    (h0 : ∀ n, T n 0 = 1) (hlt : isLower T) (hrec : shiftMat T = matMul T T)
    (p m : ℕ) (hm : 0 < m) :
    matVec T (shiftVec (fun n => matPow T p n 0)) m -
      matVec (signConj T) (shiftVec (fun n => matPow T p n 0)) m =
      matPow T (2 * p) m 0 := by
  have hsu : shiftVec (fun n => matPow T p n 0) =
      fun i => ∑ j ∈ Finset.range p, matVec (matPow T (2 * j)) (fun _ => (1 : ℤ)) i := by
    funext i
    exact shiftVec_u_eq_sum T h0 hlt hrec p i
  have hones : (fun _ : ℕ => (1 : ℤ)) = matVec T e0 := by
    funext i
    rw [matVec_e0, h0 i]
  rw [hsu, matVec_sum, matVec_sum, hones]
  have hpos : ∀ j ∈ Finset.range p,
      matVec T (matVec (matPow T (2 * j)) (matVec T e0)) m = matPow T (2 * (j + 1)) m 0 := by
    intro j _
    rw [← matVec_matMul (matPow T (2 * j)) hlt e0,
      ← matVec_matMul T (isLower_matMul hlt) e0]
    have hpow : matMul T (matMul (matPow T (2 * j)) T) = matPow T (2 * (j + 1)) := by
      change matMul T (matPow T (2 * j + 1)) = matPow T (2 * (j + 1))
      rw [← matPow_succ_left hlt (2 * j + 1), show 2 * j + 1 + 1 = 2 * (j + 1) by omega]
    rw [hpow, matVec_e0]
  have hneg : ∀ j ∈ Finset.range p,
      matVec (signConj T) (matVec (matPow T (2 * j)) (matVec T e0)) m = matPow T (2 * j) m 0 := by
    intro j _
    rw [← matVec_matMul (matPow T (2 * j)) hlt e0,
      ← matVec_matMul (signConj T) (isLower_matMul hlt) e0]
    have hcomm : matMul (matPow T (2 * j)) T = matMul T (matPow T (2 * j)) := by
      change matPow T (2 * j + 1) = matMul T (matPow T (2 * j))
      exact matPow_succ_left hlt (2 * j)
    rw [hcomm, ← matMul_assoc (signConj T) hlt (matPow T (2 * j)),
      signConj_T_mul T h0 hlt hrec, idMat_matMul, matVec_e0]
  rw [Finset.sum_congr rfl hpos, Finset.sum_congr rfl hneg, ← Finset.sum_sub_distrib]
  rw [sum_range_sub_int (fun j => matPow T (2 * j) m 0) p]
  simp [matPow, idMat, hm.ne']

end Mo495545Proof

theorem OMA.solution : type_of% @OMA.S_mo_495545.main := by
  intro T h0 hlt hrec n k hk0 hkn
  let m : ℕ := n - k
  have hm_pos : 0 < m := by omega
  have hnk : n = m + k := by omega
  let p : ℕ := 2 ^ (k - 1)
  have h2p : 2 * p = 2 ^ k := by
    dsimp [p]
    have hk_eq : k = (k - 1) + 1 := by omega
    conv_rhs => rw [hk_eq]
    ring
  have h_lhs : T n k = Mo495545Proof.matPow T (2 * p) m 0 := by
    rw [h2p, ← Mo495545Proof.shift_iter_eq_matPow T hlt (by funext a b; exact hrec a b) k m 0]
    simp [hnk]
  have h_diff := Mo495545Proof.diff_matVec_shiftVec_u T h0 hlt
    (by funext a b; exact hrec a b) p m hm_pos
  rw [← h_diff] at h_lhs
  rw [h_lhs]
  unfold Mo495545Proof.matVec Mo495545Proof.signConj Mo495545Proof.shiftVec
  rw [← Finset.sum_sub_distrib, Finset.sum_range_succ]
  dsimp only
  have hlast : T m m * Mo495545Proof.matPow T p (m + 1) 0 -
      (-1 : ℤ) ^ (m + m) * T m m * Mo495545Proof.matPow T p (m + 1) 0 = 0 := by
    rw [show m + m = 2 * m by omega, pow_mul, show (-1 : ℤ) ^ 2 = 1 by decide, one_pow]
    ring
  rw [hlast, add_zero]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hu : Mo495545Proof.matPow T p (i + 1) 0 = T (k + i) (k - 1) := by
    have hs := Mo495545Proof.shift_iter_eq_matPow T hlt (by funext a b; exact hrec a b)
      (k - 1) (i + 1) 0
    rw [← hs]
    have harg1 : i + 1 + (k - 1) = k + i := by omega
    have harg2 : 0 + (k - 1) = k - 1 := by omega
    rw [harg1, harg2]
  rw [hu]
  have hsign : (-1 : ℤ) ^ (n + k + i + 1) = - ((-1 : ℤ) ^ (m + i)) := by
    rw [show n + k + i + 1 = (m + i) + 2 * k + 1 by omega, pow_add, pow_add, pow_mul,
      show (-1 : ℤ) ^ 2 = 1 by decide, one_pow]
    ring
  rw [hsign]
  change T (n - k) i * T (k + i) (k - 1) -
      (-1 : ℤ) ^ (m + i) * T (n - k) i * T (k + i) (k - 1) =
    T (n - k) i * T (k + i) (k - 1) * (1 + -((-1 : ℤ) ^ (m + i)))
  ring
