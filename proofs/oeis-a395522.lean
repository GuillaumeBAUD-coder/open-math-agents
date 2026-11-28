import OMAStatements.S_oeis_a395522
import Mathlib.Algebra.CharP.Lemmas
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Nat.Factorization.Induction
import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Data.Nat.ModEq
import Mathlib.Data.Nat.Periodic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.LinearAlgebra.Matrix.CharP
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

-- Credit: @maaaakks
-- A395522. Eventual stabilization of least periods of the iterated Fibonacci function.

namespace FibPeriod

def transition (k : ℕ) : Equiv.Perm (ZMod k × ZMod k) where
  toFun u := (u.2, u.1 + u.2)
  invFun u := (u.2 - u.1, u.1)
  left_inv u := by ext <;> simp
  right_inv u := by ext <;> simp

@[simp] theorem transition_pair (k n : ℕ) :
    transition k ((Nat.fib n : ZMod k), (Nat.fib (n + 1) : ZMod k)) =
      ((Nat.fib (n + 1) : ZMod k), (Nat.fib (n + 2) : ZMod k)) := by
  simp [transition, Nat.fib_add_two]

theorem transition_pow (k n t : ℕ) :
    (transition k ^ t) ((Nat.fib n : ZMod k), (Nat.fib (n + 1) : ZMod k)) =
      ((Nat.fib (n + t) : ZMod k), (Nat.fib (n + t + 1) : ZMod k)) := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [pow_succ', Equiv.Perm.mul_apply, ih, transition_pair]
    rfl

def IsTime (k t : ℕ) : Prop := transition k ^ t = 1

theorem period_of_time {k t : ℕ} (h : IsTime k t) (n : ℕ) :
    Nat.fib (n + t) ≡ Nat.fib n [MOD k] := by
  apply (ZMod.natCast_eq_natCast_iff _ _ _).mp
  have hpair := transition_pow k n t
  rw [show transition k ^ t = 1 from h, Equiv.Perm.one_apply] at hpair
  exact (congrArg Prod.fst hpair).symm

theorem exists_time (k : ℕ) (hk : 0 < k) : ∃ t, 0 < t ∧ IsTime k t := by
  let : NeZero k := ⟨Nat.ne_of_gt hk⟩
  exact ⟨orderOf (transition k), orderOf_pos _, pow_orderOf_eq_one _⟩

theorem modEq_fib_of_time {k t a b : ℕ} (h : IsTime k t) (hab : a ≡ b [MOD t]) :
    Nat.fib a ≡ Nat.fib b [MOD k] := by
  have hperiod : Function.Periodic (fun n => Nat.fib n % k) t := period_of_time h
  change Nat.fib a % k = Nat.fib b % k
  rw [← hperiod.map_mod_nat a, ← hperiod.map_mod_nat b]
  change a % t = b % t at hab
  rw [hab]

theorem periodic_mod_iff {α : Type*} (f : ℕ → α) (t : ℕ) :
    Function.Periodic f t ↔ ∀ a b : ℕ, a ≡ b [MOD t] → f a = f b := by
  refine ⟨fun h a b hab => ?_, fun h a => ?_⟩
  · change a % t = b % t at hab
    rw [← h.map_mod_nat a, ← h.map_mod_nat b, hab]
  · exact h (a + t) a (Nat.add_mod_right _ _)

theorem periodic_mod_of_gcd {α : Type*} {f : ℕ → α} {a b : ℕ}
    (ha : Function.Periodic f a) (hb : Function.Periodic f b) :
    Function.Periodic f (a.gcd b) := by
  induction b using Nat.strong_induction_on generalizing a with
  | h b ih =>
    by_cases hb0 : b = 0
    · simpa [hb0] using ha
    · rw [Nat.gcd_comm a b, Nat.gcd_rec b a, Nat.gcd_comm (a % b) b]
      apply ih (a % b) (Nat.mod_lt _ (Nat.pos_of_ne_zero hb0)) hb
      intro x
      rw [← hb.map_mod_nat (x + a % b), ← hb.map_mod_nat x]
      rw [Nat.add_mod_mod]
      calc
        f ((x + a) % b) = f (x + a) := hb.map_mod_nat _
        _ = f x := ha x
        _ = f (x % b) := (hb.map_mod_nat _).symm

theorem least_positive_period_dvd {α : Type*} {f : ℕ → α} {M : ℕ}
    (hM : 0 < M) (hper : Function.Periodic f M) :
    ∃ t, 0 < t ∧ Function.Periodic f t ∧
      ∀ s, 0 < s → Function.Periodic f s → t ∣ s := by
  classical
  have h : ∃ t, 0 < t ∧ Function.Periodic f t := ⟨M, hM, hper⟩
  refine ⟨Nat.find h, (Nat.find_spec h).1, (Nat.find_spec h).2, ?_⟩
  intro s _ hs
  have ht := (Nat.find_spec h).1
  have hg := periodic_mod_of_gcd (Nat.find_spec h).2 hs
  have hle := Nat.find_min' h ⟨Nat.gcd_pos_of_pos_left _ ht, hg⟩
  have heq := le_antisymm (Nat.gcd_le_left _ ht) hle
  rw [← heq]
  exact Nat.gcd_dvd_right _ _

theorem exists_rank (k : ℕ) (hk : 0 < k) :
    ∃ z : ℕ, 0 < z ∧ ∀ n : ℕ, k ∣ Nat.fib n ↔ z ∣ n := by
  obtain ⟨t, ht, htime⟩ := exists_time k hk
  have hnonempty : ∃ n : ℕ, 0 < n ∧ k ∣ Nat.fib n := by
    refine ⟨t, ht, ?_⟩
    simpa [Nat.ModEq, Nat.dvd_iff_mod_eq_zero] using period_of_time htime 0
  let z := Nat.find hnonempty
  have hz := Nat.find_spec hnonempty
  refine ⟨z, hz.1, fun n => ⟨?_, fun h => hz.2.trans (Nat.fib_dvd _ _ h)⟩⟩
  intro hn
  have hg : k ∣ Nat.fib (z.gcd n) := by
    rw [Nat.fib_gcd]
    exact Nat.dvd_gcd hz.2 hn
  have hmin : z ≤ z.gcd n :=
    Nat.find_min' hnonempty ⟨Nat.gcd_pos_of_pos_left _ hz.1, hg⟩
  have heq : z.gcd n = z := le_antisymm (Nat.gcd_le_left _ hz.1) hmin
  rw [← heq]
  exact Nat.gcd_dvd_right _ _

noncomputable def rank (k : ℕ) : ℕ :=
  if hk : 0 < k then Classical.choose (exists_rank k hk) else 0

theorem rank_spec {k : ℕ} (hk : 0 < k) :
    0 < rank k ∧ ∀ n : ℕ, k ∣ Nat.fib n ↔ rank k ∣ n := by
  rw [rank, dif_pos hk]
  exact Classical.choose_spec (exists_rank k hk)

theorem rank_pos {k : ℕ} (hk : 0 < k) : 0 < rank k := (rank_spec hk).1

theorem rank_dvd_iff {k n : ℕ} (hk : 0 < k) : rank k ∣ n ↔ k ∣ Nat.fib n :=
  ((rank_spec hk).2 n).symm

theorem rank_dvd_of_dvd {k l : ℕ} (hk : 0 < k) (hl : 0 < l) (h : k ∣ l) :
    rank k ∣ rank l :=
  (rank_dvd_iff hk).mpr (h.trans ((rank_dvd_iff hl).mp (dvd_refl _)))

theorem rank_dvd_of_time {k t : ℕ} (hk : 0 < k) (ht : IsTime k t) :
    rank k ∣ t := by
  apply (rank_dvd_iff hk).mpr
  simpa [Nat.ModEq, Nat.dvd_iff_mod_eq_zero] using period_of_time ht 0

theorem rank_lcm {k l : ℕ} (hk : 0 < k) (hl : 0 < l) :
    rank (k.lcm l) = (rank k).lcm (rank l) := by
  have hkl := Nat.lcm_pos hk hl
  apply Nat.dvd_antisymm
  · apply (rank_dvd_iff hkl).mpr
    exact Nat.lcm_dvd ((rank_dvd_iff hk).mp (Nat.dvd_lcm_left _ _))
      ((rank_dvd_iff hl).mp (Nat.dvd_lcm_right _ _))
  · exact Nat.lcm_dvd (rank_dvd_of_dvd hk hkl (Nat.dvd_lcm_left _ _))
      (rank_dvd_of_dvd hl hkl (Nat.dvd_lcm_right _ _))

theorem rank_iterate_pos {k : ℕ} (hk : 0 < k) (m : ℕ) :
    0 < rank^[m] k := by
  induction m with
  | zero => exact hk
  | succ m ih =>
    rw [Function.iterate_succ_apply']
    exact rank_pos ih

theorem dvd_fib_iterate_iff {k : ℕ} (hk : 0 < k) (m n : ℕ) :
    k ∣ Nat.fib^[m] n ↔ rank^[m] k ∣ n := by
  induction m generalizing n with
  | zero => rfl
  | succ m ih =>
    rw [Function.iterate_succ_apply, ih, Function.iterate_succ_apply',
      rank_dvd_iff (rank_iterate_pos hk m)]

theorem rank_eq_of_first {k r : ℕ} (hk : 0 < k) (hr : 0 < r) (hdiv : k ∣ Nat.fib r)
    (hbelow : ∀ n < r, 0 < n → ¬ k ∣ Nat.fib n) : rank k = r := by
  have hkr : rank k ∣ r := (rank_dvd_iff hk).mpr hdiv
  have hle := Nat.le_of_dvd hr hkr
  by_contra hne
  have hlt := lt_of_le_of_ne hle hne
  exact hbelow _ hlt (rank_pos hk) ((rank_dvd_iff hk).mp (dvd_refl _))

theorem rank_one : rank 1 = 1 := rank_eq_of_first (by decide) (by decide) (by decide) (by decide)

theorem rank_two : rank 2 = 3 := rank_eq_of_first (by decide) (by decide) (by decide) (by decide)

theorem rank_three : rank 3 = 4 := rank_eq_of_first (by decide) (by decide) (by decide) (by decide)

theorem rank_four : rank 4 = 6 := rank_eq_of_first (by decide) (by decide) (by decide) (by decide)

theorem rank_eight : rank 8 = 6 := rank_eq_of_first (by decide) (by decide) (by decide) (by decide)

theorem rank_five : rank 5 = 5 := rank_eq_of_first (by decide) (by decide) (by decide) (by decide)

end FibPeriod

namespace FibPeriod

abbrev Mat (R : Type*) := Matrix (Fin 2) (Fin 2) R

def Q (R : Type*) [Semiring R] : Mat R :=
  !![0, 1; 1, 1]

theorem Q_sq (R : Type*) [Semiring R] : Q R ^ 2 = Q R + 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Q, pow_two, Matrix.mul_apply, Fin.sum_univ_two]

theorem discr_sq (R : Type*) [Ring R] : (2 * Q R - 1) ^ 2 = 5 := by
  calc
    (2 * Q R - 1) ^ 2 = 4 * Q R ^ 2 - 4 * Q R + 1 := by noncomm_ring
    _ = 5 := by
      rw [Q_sq]
      noncomm_ring
      norm_num [nsmul_eq_mul]

theorem Q_pow_mul_pred (R : Type*) [Ring R] (n : ℕ) :
    Q R ^ (n + 1) * (Q R - 1) = Q R ^ n := by
  have hx : Q R * (Q R - 1) = 1 := by
    rw [mul_sub, mul_one, ← pow_two, Q_sq]
    abel
  rw [pow_succ, mul_assoc, hx, mul_one]

theorem Q_pow_prime_sq {p : ℕ} (hp : p.Prime) (hodd : p ≠ 2) (hfive : p ≠ 5) :
    Q (ZMod p) ^ (p ^ 2 - 1) = 1 := by
  let : Fact p.Prime := ⟨hp⟩
  let s : ZMod p →+* Mat (ZMod p) := algebraMap (ZMod p) (Mat (ZMod p))
  have hs2 : s (2 : ZMod p) = 2 := map_natCast s 2
  have hs5 : s (5 : ZMod p) = 5 := map_natCast s 5
  have hpodd := hp.odd_of_ne_two hodd
  obtain ⟨a, ha⟩ := hpodd
  have hp2 : 1 ≤ p ^ 2 := Nat.one_le_pow _ _ hp.pos
  have hexp : p ^ 2 = 2 * ((p - 1) * (a + 1)) + 1 := by
    have hsub : p - 1 = 2 * a := by omega
    rw [hsub, ha]
    ring
  have h5 : (5 : ZMod p) ≠ 0 := by
    intro hz
    have hdiv : p ∣ 5 := (ZMod.natCast_eq_zero_iff 5 p).mp hz
    exact hfive ((Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 5)).mp hdiv)
  have hscalar : (5 : Mat (ZMod p)) ^ ((p - 1) * (a + 1)) = 1 := by
    calc
      (5 : Mat (ZMod p)) ^ ((p - 1) * (a + 1)) =
          s ((5 : ZMod p) ^ ((p - 1) * (a + 1))) := by rw [map_pow, hs5]
      _ = 1 := by rw [pow_mul, ZMod.pow_card_sub_one_eq_one h5, one_pow, map_one]
  let D : Mat (ZMod p) := 2 * Q (ZMod p) - 1
  have hD : D ^ (p ^ 2) = D := by
    calc
      D ^ (p ^ 2) = D ^ (2 * ((p - 1) * (a + 1))) * D := by rw [hexp, pow_succ]
      _ = D := by rw [pow_mul, show D ^ 2 = 5 from discr_sq _, hscalar, one_mul]
  have h2 : (2 : Mat (ZMod p)) ^ (p ^ 2) = 2 := by
    calc
      (2 : Mat (ZMod p)) ^ (p ^ 2) = s ((2 : ZMod p) ^ (p ^ 2)) := by rw [map_pow, hs2]
      _ = 2 := by rw [ZMod.pow_card_pow, hs2]
  have h2Q : Commute (2 : Mat (ZMod p)) (Q (ZMod p)) := Nat.cast_commute 2 _
  have hfrob : 2 * Q (ZMod p) ^ (p ^ 2) - 1 = 2 * Q (ZMod p) - 1 := by
    unfold D at hD
    rw [sub_pow_char_pow_of_commute p 2 (Commute.one_right _), one_pow,
      h2Q.mul_pow, h2] at hD
    exact hD
  have hQ : Q (ZMod p) ^ (p ^ 2) = Q (ZMod p) := by
    have hmul : 2 * Q (ZMod p) ^ (p ^ 2) = 2 * Q (ZMod p) := by
      simpa only [sub_add_cancel] using congrArg (fun x : Mat (ZMod p) => x + 1) hfrob
    have hunit : IsUnit (2 : Mat (ZMod p)) := by
      have hdiv : ¬ p ∣ 2 := fun h => hodd
        ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h)
      have hne : (2 : ZMod p) ≠ 0 := by
        exact fun h => hdiv ((ZMod.natCast_eq_zero_iff 2 p).mp h)
      rw [← hs2]
      exact (isUnit_iff_ne_zero.mpr hne).map s
    exact hunit.mul_left_cancel hmul
  have hn : p ^ 2 - 1 + 1 = p ^ 2 := by omega
  calc
    Q (ZMod p) ^ (p ^ 2 - 1) = Q (ZMod p) ^ (p ^ 2 - 1 + 1) * (Q (ZMod p) - 1) :=
      (Q_pow_mul_pred (ZMod p) (p ^ 2 - 1)).symm
    _ = Q (ZMod p) * (Q (ZMod p) - 1) := by rw [hn, hQ]
    _ = 1 := by simpa only [zero_add, pow_one, pow_zero] using Q_pow_mul_pred (ZMod p) 0

end FibPeriod

namespace FibPeriod

theorem mapMatrix_Q {R S : Type*} [Ring R] [Ring S] (f : R →+* S) :
    f.mapMatrix (Q R) = Q S := by
  ext i j
  change ((Q R).map f) i j = Q S i j
  fin_cases i <;> fin_cases j <;> simp [Q]

abbrev IsMatrixTime (k t : ℕ) : Prop := Q (ZMod k) ^ t = 1

theorem matrix_time_dvd {k l t : ℕ} (h : k ∣ l) (ht : IsMatrixTime l t) :
    IsMatrixTime k t := by
  have hh := congrArg (ZMod.castHom h (ZMod k)).mapMatrix ht
  simpa only [map_pow, mapMatrix_Q, map_one] using hh

theorem matrix_time_mul {k t : ℕ} (h : IsMatrixTime k t) (x : ℕ) :
    IsMatrixTime k (t * x) := by
  change _ ^ (t * x) = _
  rw [pow_mul, h, one_pow]

theorem one_add_pow_of_sq_zero {R : Type*} [Ring R] {x : R} (h : x ^ 2 = 0) (n : ℕ) :
    (1 + x) ^ n = 1 + n • x := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hx : x * x = 0 := by simpa [pow_two] using h
    have hnx : (n • x) * x = 0 := by rw [nsmul_eq_mul, mul_assoc, hx, mul_zero]
    simp only [pow_succ, ih, add_mul, mul_add, one_mul, mul_one, hnx, add_zero,
      succ_nsmul]
    abel

theorem matrix_time_lift {p e t : ℕ} (he : 0 < e)
    (ht : IsMatrixTime (p ^ e) t) : IsMatrixTime (p ^ (e + 1)) (t * p) := by
  classical
  let E : Mat ℤ := Q ℤ ^ t - 1
  have hzero : (Int.castRingHom (ZMod (p ^ e))).mapMatrix E = 0 := by
    simp only [E, map_sub, map_pow, mapMatrix_Q, map_one, ht, sub_self]
  have hdiv : ∀ i j, (p : ℤ) ^ e ∣ E i j := by
    intro i j
    have hz : (E i j : ZMod (p ^ e)) = 0 :=
      congrArg (fun M : Mat (ZMod (p ^ e)) => M i j) hzero
    have hd := (CharP.intCast_eq_zero_iff (ZMod (p ^ e)) (p ^ e) _).mp hz
    simpa only [Nat.cast_pow] using hd
  let R := ZMod (p ^ (e + 1))
  let W : Mat ℤ := fun i j => Classical.choose (hdiv i j)
  let X : Mat R := Q R ^ t - 1
  have hX : X = (p : R) ^ e • (Int.castRingHom R).mapMatrix W := by
    have hmap : (Int.castRingHom R).mapMatrix E = X := by
      simp only [E, X, map_sub, map_pow, mapMatrix_Q, map_one]
    rw [← hmap]
    ext i j
    change (E i j : R) = (p : R) ^ e * (W i j : R)
    rw [show E i j = (p : ℤ) ^ e * W i j from Classical.choose_spec (hdiv i j)]
    change (Int.castRingHom R) ((p : ℤ) ^ e * W i j) =
      (p : R) ^ e * (Int.castRingHom R) (W i j)
    rw [map_mul, map_pow, map_natCast]
  have hpzero : (p : R) ^ (e + 1) = 0 := by
    rw [← Nat.cast_pow]
    exact ZMod.natCast_self _
  have hX2 : X ^ 2 = 0 := by
    have hscalar : ((p : R) ^ e) ^ 2 = 0 := by
      rw [← pow_mul]
      have hle : e + 1 ≤ e * 2 := by omega
      rw [← Nat.add_sub_of_le hle, pow_add, hpzero, zero_mul]
    rw [hX, smul_pow, hscalar, zero_smul]
  have hpx : p • X = 0 := by
    rw [hX, ← Nat.cast_smul_eq_nsmul R, smul_smul, ← pow_succ', hpzero, zero_smul]
  change Q R ^ (t * p) = 1
  rw [pow_mul, show Q R ^ t = 1 + X by dsimp [X]; abel, one_add_pow_of_sq_zero hX2,
    hpx, add_zero]

theorem matrix_time_prime_power {p t : ℕ} (h : IsMatrixTime p t) (e : ℕ) :
    IsMatrixTime (p ^ (e + 1)) (t * p ^ e) := by
  induction e with
  | zero => simpa [pow_one] using h
  | succ e ih =>
    simpa only [pow_succ, mul_assoc] using matrix_time_lift (by omega) ih

theorem matrix_time_two : IsMatrixTime 2 3 := by decide
theorem matrix_time_three : IsMatrixTime 3 8 := by decide
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
theorem matrix_time_five : IsMatrixTime 5 20 := by decide
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
theorem matrix_time_24 : IsMatrixTime 24 24 := by decide

end FibPeriod

namespace FibPeriod

theorem Q_pow_fib (R : Type*) [Ring R] (n : ℕ) :
    Q R ^ n =
      !![(Nat.fib (n + 1) : R) - (Nat.fib n : R), (Nat.fib n : R);
         (Nat.fib n : R), (Nat.fib (n + 1) : R)] := by
  induction n with
  | zero =>
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  | succ n ih =>
    rw [pow_succ, ih]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Q, Matrix.mul_apply, Fin.sum_univ_two, Nat.fib_add_two]

theorem fib_mul_five_integer (n : ℕ) :
    ∃ c : ℤ, (Nat.fib (5 * n) : ℤ) = 5 * (Nat.fib n : ℤ) * c ∧ ¬ (5 : ℤ) ∣ c := by
  set u : ℤ := (Nat.fib (n + 1) : ℤ)
  set v : ℤ := (Nat.fib n : ℤ)
  let delta := (u - v) * u - v ^ 2
  have hmat : Q ℤ ^ n = !![u - v, v; v, u] := Q_pow_fib ℤ n
  have hdet : (Q ℤ).det = -1 := by norm_num [Q, Matrix.det_fin_two_of]
  have hdelta : delta = (-1) ^ n := by
    have hh := congrArg Matrix.det hmat
    rw [Matrix.det_pow, hdet, Matrix.det_fin_two_of] at hh
    simp [delta, pow_two, ← hh]
  have hdelta2 : delta ^ 2 = 1 := by
    rw [hdelta, ← pow_mul, Nat.mul_comm, pow_mul]
    norm_num
  let c : ℤ := 5 * v ^ 4 + 5 * delta * v ^ 2 + 1
  refine ⟨c, ?_, ?_⟩
  · have hfive := congrArg (fun M : Mat ℤ => M 0 1) (Q_pow_fib ℤ (5 * n))
    rw [Nat.mul_comm, pow_mul, hmat] at hfive
    have hpoly : ((!![u-v, v; v, u] : Mat ℤ) ^ 5) 0 1 =
        5 * v * c + v * (delta ^ 2 - 1) * 5 := by
      simp [c, delta, pow_succ, Matrix.mul_apply, Fin.sum_univ_two]
      ring
    rw [hpoly, hdelta2] at hfive
    simpa [v, Nat.mul_comm n 5] using hfive.symm
  · intro h
    have heq : c = 5 * (v ^ 4 + delta * v ^ 2) + 1 := by dsimp [c]; ring
    have hone : (5 : ℤ) ∣ (1 : ℤ) := by
      have hh := dvd_sub h (dvd_mul_right (5 : ℤ) (v ^ 4 + delta * v ^ 2))
      rwa [heq, add_sub_cancel_left] at hh
    norm_num at hone

theorem exact_five_power_dvd (e : ℕ) :
    5 ^ e ∣ Nat.fib (5 ^ e) ∧ ¬ 5 ^ (e + 1) ∣ Nat.fib (5 ^ e) := by
  induction e with
  | zero => decide
  | succ e ih =>
    obtain ⟨c, heq, hc⟩ := fib_mul_five_integer (5 ^ e)
    have heq' : (Nat.fib (5 ^ (e + 1)) : ℤ) = 5 * ((Nat.fib (5 ^ e) : ℤ) * c) := by
      simpa [pow_succ', mul_assoc] using heq
    have hcast : (5 : ℤ) ^ e ∣ (Nat.fib (5 ^ e) : ℤ) := by exact_mod_cast ih.1
    constructor
    · have hh : (5 : ℤ) ^ (e + 1) ∣ (Nat.fib (5 ^ (e + 1)) : ℤ) := by
        rw [heq', pow_succ']
        exact mul_dvd_mul_left _ (hcast.trans (dvd_mul_right _ _))
      exact_mod_cast hh
    · intro hdvd
      have hc' : IsCoprime (5 : ℤ) c := by
        apply Int.isCoprime_iff_gcd_eq_one.mpr
        change Nat.Coprime 5 c.natAbs
        apply (by decide : Nat.Prime 5).coprime_iff_not_dvd.mpr
        intro h
        exact hc (Int.dvd_natAbs.mp (by exact_mod_cast h))
      have hcast' : (5 : ℤ) ^ (e + 1 + 1) ∣ (Nat.fib (5 ^ (e + 1)) : ℤ) := by
        exact_mod_cast hdvd
      rw [heq', pow_succ'] at hcast'
      have hh : (5 : ℤ) ^ (e + 1) ∣ (Nat.fib (5 ^ e) : ℤ) * c :=
        (mul_dvd_mul_iff_left (by norm_num : (5 : ℤ) ≠ 0)).mp hcast'
      apply ih.2
      exact_mod_cast (hc'.pow_left (m := e + 1)).dvd_of_dvd_mul_right hh

theorem rank_five_power (e : ℕ) : rank (5 ^ e) = 5 ^ e := by
  cases e with
  | zero => simpa using rank_one
  | succ e =>
    have hpos : 0 < (5 : ℕ) ^ (e + 1) := by positivity
    have hdvd := (rank_dvd_iff hpos).mpr (exact_five_power_dvd (e + 1)).1
    obtain ⟨j, hj, hval⟩ := (Nat.dvd_prime_pow (by decide : Nat.Prime 5)).mp hdvd
    suffices j = e + 1 by simpa [this] using hval
    by_contra hne
    have hje : j ≤ e := by omega
    have hr : rank (5 ^ (e + 1)) ∣ 5 ^ e := hval ▸ pow_dvd_pow 5 hje
    exact (exact_five_power_dvd e).2 ((rank_dvd_iff hpos).mp hr)

end FibPeriod

namespace FibPeriod

theorem period_of_matrix {k t : ℕ} (ht : IsMatrixTime k t) :
    Function.Periodic (fun n => Nat.fib n % k) t := by
  intro n
  apply (ZMod.natCast_eq_natCast_iff' _ _ _).mp
  have hm : Q (ZMod k) ^ (n + t) = Q (ZMod k) ^ n := by
    rw [pow_add, ht, mul_one]
  rw [Q_pow_fib, Q_pow_fib] at hm
  exact congrArg (fun M : Mat (ZMod k) => M 0 1) hm

theorem fib_modEq_of_matrix {k t x y : ℕ} (ht : IsMatrixTime k t)
    (h : x ≡ y [MOD t]) : Nat.fib x ≡ Nat.fib y [MOD k] :=
  (periodic_mod_iff (fun n => Nat.fib n % k) t).mp (period_of_matrix ht) x y h

def coreModulus (e : ℕ) : ℕ := 24 * 5 ^ e

theorem coreModulus_mono {e f : ℕ} (h : e ≤ f) : coreModulus e ∣ coreModulus f :=
  Nat.mul_dvd_mul_left 24 (pow_dvd_pow 5 h)

theorem fib_respects_core (e : ℕ) {x y : ℕ} (h : x ≡ y [MOD coreModulus e]) :
    Nat.fib x ≡ Nat.fib y [MOD coreModulus e] := by
  have h24 : Nat.fib x ≡ Nat.fib y [MOD 24] :=
    fib_modEq_of_matrix matrix_time_24 (h.of_dvd (dvd_mul_right _ _))
  have h5 : Nat.fib x ≡ Nat.fib y [MOD (5 ^ e)] := by
    cases e with
    | zero =>
      change Nat.fib x % 1 = Nat.fib y % 1
      rw [Nat.mod_one, Nat.mod_one]
    | succ e =>
      have hm := matrix_time_prime_power matrix_time_five e
      have heq : 20 * 5 ^ e = 4 * 5 ^ (e + 1) := by rw [pow_succ]; ring
      rw [heq] at hm
      have hd : 4 * 5 ^ (e + 1) ∣ coreModulus (e + 1) :=
        mul_dvd_mul_right (by decide : 4 ∣ 24) _
      exact fib_modEq_of_matrix hm (h.of_dvd hd)
  exact (Nat.modEq_and_modEq_iff_modEq_mul ((by decide : Nat.Coprime 24 5).pow_right _)).mp
    ⟨h24, h5⟩

def FibComp (k M d : ℕ) : Prop :=
  ∀ x y, x ≡ y [MOD M] → Nat.fib^[d] x ≡ Nat.fib^[d] y [MOD k]

theorem fibComp_of_dvd {k M d : ℕ} (h : k ∣ M) (hc : FibComp M M d) : FibComp k M d :=
  fun x y hxy => (hc x y hxy).of_dvd h

theorem fibComp_self_zero (k : ℕ) : FibComp k k 0 := fun _ _ h => h

theorem fibComp_step {k t M d : ℕ} (ht : IsMatrixTime k t) (h : FibComp t M d) :
    FibComp k M (d + 1) := by
  intro x y hxy
  simp only [Function.iterate_succ_apply']
  exact fib_modEq_of_matrix ht (h x y hxy)

theorem fibComp_more_input {k d e f : ℕ} (h : e ≤ f) (hc : FibComp k (coreModulus e) d) :
    FibComp k (coreModulus f) d :=
  fun x y hxy => hc x y (hxy.of_dvd (coreModulus_mono h))

theorem fibComp_more_time {k d c e : ℕ} (hd : d ≤ c) (hc : FibComp k (coreModulus e) d) :
    FibComp k (coreModulus e) c := by
  have loop (z : ℕ) : FibComp k (coreModulus e) (d + z) := by
    induction z with
    | zero => simpa
    | succ z ih =>
      intro x y hxy
      rw [Nat.add_succ]
      simp only [Function.iterate_succ_apply]
      exact ih _ _ (fib_respects_core e hxy)
  obtain ⟨z, rfl⟩ := Nat.exists_eq_add_of_le hd
  exact loop z

def Good (k : ℕ) : Prop := ∃ d e, FibComp k (coreModulus e) d

theorem good_of_dvd_core {k e : ℕ} (hk : k ∣ coreModulus e) : Good k :=
  ⟨0, e, fibComp_of_dvd hk (fibComp_self_zero _)⟩

theorem good_of_coprime_mul {k l : ℕ} (hcop : k.Coprime l) (hk : Good k) (hl : Good l) :
    Good (k * l) := by
  obtain ⟨d, e, hk⟩ := hk
  obtain ⟨f, g, hl⟩ := hl
  refine ⟨max d f, max e g, ?_⟩
  have hkc := fibComp_more_time (le_max_left d f) (fibComp_more_input (le_max_left e g) hk)
  have hlc := fibComp_more_time (le_max_right d f) (fibComp_more_input (le_max_right e g) hl)
  intro x y hxy
  exact (Nat.modEq_and_modEq_iff_modEq_mul hcop).mp ⟨hkc x y hxy, hlc x y hxy⟩

theorem good_step {k t : ℕ} (ht : IsMatrixTime k t) (h : Good t) : Good k := by
  obtain ⟨d, e, hc⟩ := h
  exact ⟨d + 1, e, fibComp_step ht hc⟩

theorem good_one : Good 1 := good_of_dvd_core (e := 0) (one_dvd _)

theorem good_pow_two (e : ℕ) : Good (2 ^ e) := by
  induction e with
  | zero => simpa using good_one
  | succ e ih =>
    have h3 : Good 3 := good_of_dvd_core (e := 0) (by decide)
    exact good_step (matrix_time_prime_power matrix_time_two e)
      (good_of_coprime_mul ((by decide : Nat.Coprime 3 2).pow_right _) h3 ih)

theorem good_pow_three (e : ℕ) : Good (3 ^ e) := by
  induction e with
  | zero => simpa using good_one
  | succ e ih =>
    have h8 : Good 8 := by simpa using good_pow_two 3
    exact good_step (matrix_time_prime_power matrix_time_three e)
      (good_of_coprime_mul ((by decide : Nat.Coprime 8 3).pow_right _) h8 ih)

theorem good_pow_five (e : ℕ) : Good (5 ^ e) := by
  cases e with
  | zero => simpa using good_one
  | succ e =>
    have h := matrix_time_prime_power matrix_time_five e
    have heq : 20 * 5 ^ e = 4 * 5 ^ (e + 1) := by rw [pow_succ]; ring
    rw [heq] at h
    exact good_step h (good_of_dvd_core (mul_dvd_mul_right (by decide : 4 ∣ 24) _))

theorem good_of_factors {k : ℕ} (hn : k ≠ 0)
    (factors : ∀ p, p.Prime → p ∣ k → ∀ e, Good (p ^ e)) : Good k := by
  refine Nat.recOnPrimeCoprime
    (motive := fun k => k ≠ 0 → (∀ p, p.Prime → p ∣ k → ∀ e, Good (p ^ e)) → Good k)
    ?_ ?_ ?_ k hn factors
  · simp
  · intro p e hp _ factors
    by_cases he : e = 0
    · simpa [he] using good_one
    · exact factors p hp (dvd_pow_self _ he) e
  · intro a b ha hb hco iha ihb _ factors
    exact good_of_coprime_mul hco
      (iha (by omega) (fun p hp hd e => factors p hp (hd.trans (dvd_mul_right _ _)) e))
      (ihb (by omega) (fun p hp hd e => factors p hp (hd.trans (dvd_mul_left _ _)) e))

theorem prime_lt_of_dvd_pred_square {p q : ℕ} (hp : p.Prime) (hodd : p ≠ 2)
    (hq : q.Prime) (hd : q ∣ p ^ 2 - 1) : q < p := by
  have hp' : 1 < p := hp.one_lt
  have heq : p ^ 2 - 1 = (p - 1) * (p + 1) := by
    obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hp.pos)
    rw [hm, Nat.succ_eq_add_one, Nat.add_sub_cancel]
    have hsq : (m + 1) ^ 2 = m * (m + 1 + 1) + 1 := by ring
    omega
  rw [heq] at hd
  rcases hq.dvd_mul.mp hd with h | h
  · exact lt_of_le_of_lt (Nat.le_of_dvd (by omega) h) (by omega)
  · have hle := Nat.le_of_dvd (by omega : 0 < p + 1) h
    by_contra! hnot
    rcases (show q = p ∨ q = p + 1 by omega) with he | he
    · subst q
      have hone : p ∣ 1 := by simpa using Nat.dvd_sub h (dvd_refl p)
      exact hp.not_dvd_one hone
    · have ht : 2 ∣ q := by rw [he]; exact (even_iff_two_dvd.mp (hp.odd_of_ne_two hodd).add_one)
      have htwo := (Nat.prime_dvd_prime_iff_eq Nat.prime_two hq).mp ht
      omega

theorem good_prime_power (p : ℕ) (hp : p.Prime) (e : ℕ) : Good (p ^ e) := by
  induction p using Nat.strong_induction_on generalizing e with
  | h p ih =>
    by_cases h2 : p = 2
    · simpa [h2] using good_pow_two e
    by_cases h3 : p = 3
    · simpa [h3] using good_pow_three e
    by_cases h5 : p = 5
    · simpa [h5] using good_pow_five e
    have hsqp : 1 < p ^ 2 := hp.one_lt.trans_le (Nat.le_self_pow (by decide) _)
    have hpred : Good (p ^ 2 - 1) := good_of_factors (by omega)
      (fun q hq hd e => ih q (prime_lt_of_dvd_pred_square hp h2 hq hd) hq e)
    have hcop : (p ^ 2 - 1).Coprime p := by
      apply Nat.Coprime.symm
      apply hp.coprime_iff_not_dvd.mpr
      intro h
      exact (Nat.lt_irrefl _) (prime_lt_of_dvd_pred_square hp h2 hp h)
    induction e with
    | zero => simpa using good_one
    | succ e he =>
      exact good_step (matrix_time_prime_power (Q_pow_prime_sq hp h2 h5) e)
        (good_of_coprime_mul (hcop.pow_right _) hpred he)

theorem good_positive {k : ℕ} (hk : 0 < k) : Good k :=
  good_of_factors (Nat.ne_of_gt hk) (fun p hp _ e => good_prime_power p hp e)

end FibPeriod

namespace FibPeriod

theorem rank_of_mul {a b : ℕ} (ha : 0 < a) (hb : 0 < b) (h : a.Coprime b) :
    rank (a * b) = (rank a).lcm (rank b) := by
  rw [← h.lcm_eq_mul, rank_lcm ha hb]

theorem rank_six : rank 6 = 12 := by
  rw [show (6 : ℕ) = 2 * 3 by decide, rank_of_mul (by decide) (by decide) (by decide),
    rank_two, rank_three]
  decide

theorem rank_twelve : rank 12 = 12 := by
  conv_lhs => rw [show (12 : ℕ) = 4 * 3 by decide, rank_of_mul (by decide) (by decide) (by decide),
    rank_four, rank_three]
  decide

theorem rank_twentyfour : rank 24 = 12 := by
  rw [show (24 : ℕ) = 8 * 3 by decide, rank_of_mul (by decide) (by decide) (by decide),
    rank_eight, rank_three]
  decide

theorem rank_core_dvd {a : ℕ} (ha : 0 < a) (h : a ∣ 24) : rank a ∣ 24 := by
  have hd := rank_dvd_of_dvd ha (by decide : 0 < (24 : ℕ)) h
  rw [rank_twentyfour] at hd
  exact hd.trans (by decide)

theorem rank_mul_five {a : ℕ} (ha : 0 < a) (hd : a ∣ 24) (e : ℕ) :
    rank (a * 5 ^ e) = rank a * 5 ^ e := by
  have hco := (by decide : Nat.Coprime 24 5).coprime_dvd_left hd
  have hrco := (by decide : Nat.Coprime 24 5).coprime_dvd_left (rank_core_dvd ha hd)
  rw [rank_of_mul ha (by positivity) (hco.pow_right _), rank_five_power, (hrco.pow_right e).lcm_eq_mul]

theorem rank_iterate_core_mul {a : ℕ} (ha : 0 < a) (hd : a ∣ 24) (e d : ℕ) :
    rank^[d] (a * 5 ^ e) = rank^[d] a * 5 ^ e := by
  induction d generalizing a with
  | zero => rfl
  | succ d ih =>
    simp only [Function.iterate_succ_apply]
    rw [rank_mul_five ha hd e]
    exact ih (rank_pos ha) (rank_core_dvd ha hd)

theorem rank_core_four {a : ℕ} (ha : 0 < a) (hd : a ∣ 24) :
    rank^[4] a = 1 ∨ rank^[4] a = 12 := by
  have hle := Nat.le_of_dvd (by decide : 0 < (24 : ℕ)) hd
  have hall : ∀ n ≤ 24, n ∣ 24 → n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 6 ∨
      n = 8 ∨ n = 12 ∨ n = 24 := by decide
  rcases hall a hle hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [Function.iterate_succ_apply', rank_one, rank_two, rank_three, rank_four,
      rank_six, rank_eight, rank_twelve, rank_twentyfour]

@[simp] theorem fib_iterate_zero (d : ℕ) : Nat.fib^[d] 0 = 0 :=
  Function.iterate_fixed Nat.fib_zero d

theorem rank_iterate_dvd_of_fibComp {k M d : ℕ} (hk : 0 < k) (h : FibComp k M d) :
    rank^[d] k ∣ M := by
  have hc := h M 0 (by simp [Nat.ModEq])
  rw [fib_iterate_zero, Nat.modEq_zero_iff_dvd] at hc
  exact (dvd_fib_iterate_iff hk d M).mp hc

theorem rank_gt_one {k : ℕ} (hk : 1 < k) : 1 < rank k := by
  have hp : 0 < k := by omega
  have hr := rank_pos hp
  by_contra! h
  have heq : rank k = 1 := by omega
  have hd : k ∣ Nat.fib 1 := (rank_dvd_iff hp).mp (by simp [heq])
  have : k = 1 := Nat.dvd_one.mp (by simpa using hd)
  omega

theorem rank_iterate_gt_one {k : ℕ} (hk : 1 < k) (n : ℕ) : 1 < rank^[n] k := by
  induction n with
  | zero => exact hk
  | succ n ih => simpa only [Function.iterate_succ_apply'] using rank_gt_one ih

theorem stable_rank_and_core {k : ℕ} (hk : 1 < k) :
    ∃ d e b, b ≤ e ∧ FibComp k (coreModulus e) d ∧
      ((rank^[d] k = 5 ^ b ∧ 0 < b) ∨ rank^[d] k = 12 * 5 ^ b) ∧
      rank (rank^[d] k) = rank^[d] k := by
  have hp : 0 < k := by omega
  obtain ⟨d, e, hcomp⟩ := good_positive hp
  have hdvd := rank_iterate_dvd_of_fibComp hp hcomp
  obtain ⟨a, c, ha, hc, hac⟩ := exists_dvd_and_dvd_of_dvd_mul hdvd
  obtain ⟨b, hb, rfl⟩ := (Nat.dvd_prime_pow (by decide : Nat.Prime 5)).mp hc
  have hapos : 0 < a := Nat.pos_of_dvd_of_pos ha (by decide)
  have heq : rank^[d + 4] k = rank^[4] a * 5 ^ b := by
    rw [Nat.add_comm d 4, Function.iterate_add_apply, hac, rank_iterate_core_mul hapos ha]
  refine ⟨d + 4, e, b, hb, fibComp_more_time (by omega) hcomp, ?_, ?_⟩
  · rcases rank_core_four hapos ha with h | h
    · have hval : rank^[d + 4] k = 5 ^ b := by rw [heq, h, one_mul]
      refine Or.inl ⟨hval, ?_⟩
      by_contra! hz
      have hb0 : b = 0 := by omega
      have ht := rank_iterate_gt_one hk (d + 4)
      simp [hval, hb0] at ht
    · exact Or.inr (by rw [heq, h])
  · rcases rank_core_four hapos ha with h | h
    · rw [heq, h, one_mul, rank_five_power]
    · rw [heq, h, rank_mul_five (by decide) (by decide), rank_twelve]

end FibPeriod

namespace FibPeriod

def state24 (e x : ℕ) : Fin 24 × ZMod (5 ^ e) :=
  (⟨x % 24, Nat.mod_lt x (by decide)⟩, (x : ZMod (5 ^ e)))

def restrict5 {j e : ℕ} (h : j ≤ e) : ZMod (5 ^ e) →+* ZMod (5 ^ j) :=
  ZMod.castHom (pow_dvd_pow 5 h) _

theorem state24_surjective (e : ℕ) : Function.Surjective (state24 e) := by
  let : NeZero (5 ^ e) := ⟨by positivity⟩
  rintro ⟨r, z⟩
  obtain ⟨n, h₁, h₂⟩ := Nat.chineseRemainder ((by decide : Nat.Coprime 24 5).pow_right e) r.val z.val
  refine ⟨n, Prod.ext (Fin.ext ?_) ?_⟩
  · simpa [state24, Nat.ModEq, Nat.mod_eq_of_lt r.isLt] using h₁
  · have hz := (ZMod.natCast_eq_natCast_iff n z.val (5 ^ e)).mpr h₂
    simpa [state24, ZMod.natCast_zmod_val] using hz

theorem state24_fst_eq_iff (e x y : ℕ) :
    (state24 e x).1 = (state24 e y).1 ↔ x ≡ y [MOD 24] := by
  exact ⟨congrArg Fin.val, fun h => Fin.ext h⟩

theorem state24_restrict_eq_iff {j e : ℕ} (h : j ≤ e) (x y : ℕ) :
    restrict5 h (state24 e x).2 = restrict5 h (state24 e y).2 ↔ x ≡ y [MOD (5 ^ j)] := by
  simpa only [state24, map_natCast] using ZMod.natCast_eq_natCast_iff x y (5 ^ j)

theorem state24_mod_24_5 {j e : ℕ} (h : j ≤ e) (x y : ℕ) :
    (x ≡ y [MOD (24 * 5 ^ j)]) ↔
      (state24 e x).1 = (state24 e y).1 ∧
        restrict5 h (state24 e x).2 = restrict5 h (state24 e y).2 := by
  rw [state24_fst_eq_iff, state24_restrict_eq_iff]
  exact (Nat.modEq_and_modEq_iff_modEq_mul ((by decide : Nat.Coprime 24 5).pow_right j)).symm

theorem state24_fst_half_iff (e x y : ℕ) :
    ((state24 e x).1.val ≡ (state24 e y).1.val [MOD 12]) ↔ x ≡ y [MOD 12] := by
  have hx : (state24 e x).1.val ≡ x [MOD 12] := by
    simpa [state24] using (Nat.mod_modEq x 24).of_dvd (by decide : 12 ∣ 24)
  have hy : (state24 e y).1.val ≡ y [MOD 12] := by
    simpa [state24] using (Nat.mod_modEq y 24).of_dvd (by decide : 12 ∣ 24)
  exact ⟨fun hh => hx.symm.trans (hh.trans hy), fun hh => hx.trans (hh.trans hy.symm)⟩

theorem state24_mod_12_5 {j e : ℕ} (h : j ≤ e) (x y : ℕ) :
    (x ≡ y [MOD (12 * 5 ^ j)]) ↔
      ((state24 e x).1.val ≡ (state24 e y).1.val [MOD 12]) ∧
        restrict5 h (state24 e x).2 = restrict5 h (state24 e y).2 := by
  rw [state24_fst_half_iff, state24_restrict_eq_iff]
  exact (Nat.modEq_and_modEq_iff_modEq_mul ((by decide : Nat.Coprime 12 5).pow_right j)).symm

theorem state24_eq_iff (e x y : ℕ) :
    state24 e x = state24 e y ↔ x ≡ y [MOD (24 * 5 ^ e)] := by
  rw [state24_mod_24_5 (le_refl e)]
  refine ⟨fun h => ⟨congrArg Prod.fst h, congrArg (fun q => restrict5 (le_refl e) q.2) h⟩, ?_⟩
  rintro ⟨h₁, h₂⟩
  apply Prod.ext h₁
  exact (ZMod.natCast_eq_natCast_iff x y (5 ^ e)).mpr
    ((state24_restrict_eq_iff (le_refl e) x y).mp h₂)

theorem restrict5_surjective {j e : ℕ} (h : j ≤ e) :
    Function.Surjective (restrict5 h) := by
  let : NeZero (5 ^ j) := ⟨by positivity⟩
  intro z
  refine ⟨(z.val : ZMod (5 ^ e)), ?_⟩
  rw [map_natCast, ZMod.natCast_zmod_val]

set_option maxRecDepth 10000 in
theorem fin24_half_iff (r s : Fin 24) :
    (r.val ≡ s.val [MOD 12]) ↔ s = r ∨ s = r + 12 := by
  have h : ∀ r s : Fin 24, (r.val ≡ s.val [MOD 12]) ↔ s = r ∨ s = r + 12 := by decide
  exact h r s

theorem mixed_period_shape {t e b : ℕ} (hdiv : t ∣ 24 * 5 ^ e)
    (hbase : 12 * 5 ^ b ∣ t) :
    ∃ j, b ≤ j ∧ j ≤ e ∧ (t = 12 * 5 ^ j ∨ t = 24 * 5 ^ j) := by
  obtain ⟨a, u, ha, hu, rfl⟩ := exists_dvd_and_dvd_of_dvd_mul hdiv
  obtain ⟨j, hj, rfl⟩ := (Nat.dvd_prime_pow (by decide : Nat.Prime 5)).mp hu
  have hd12 : 12 ∣ a * 5 ^ j := (dvd_mul_right 12 (5 ^ b)).trans hbase
  have ha12 : 12 ∣ a := ((by decide : Nat.Coprime 12 5).pow_right j).dvd_of_dvd_mul_right hd12
  have hpow : 5 ^ b ∣ a * 5 ^ j := (dvd_mul_left (5 ^ b) 12).trans hbase
  have hco : (5 ^ b).Coprime a :=
    ((by decide : Nat.Coprime 24 5).coprime_dvd_left ha).symm.pow_left b
  have hb : b ≤ j :=
    (Nat.pow_dvd_pow_iff_le_right (by decide : 1 < (5 : ℕ))).mp
      (hco.dvd_of_dvd_mul_left hpow)
  have hall : ∀ u ≤ 24, 12 ∣ u → u ∣ 24 → u = 12 ∨ u = 24 := by decide
  have habound := Nat.le_of_dvd (by decide : 0 < (24 : ℕ)) ha
  refine ⟨j, hb, hj, ?_⟩
  rcases hall a habound ha12 ha with rfl | rfl
  · exact Or.inl rfl
  · exact Or.inr rfl

end FibPeriod

namespace FibPeriod

abbrev Period (k m t : ℕ) : Prop :=
  Function.Periodic (fun x => Nat.fib^[m] x % k) t

def Stabilizes (k : ℕ) : Prop :=
  ∃ N t : ℕ, 0 < N ∧ 0 < t ∧
    ∀ m : ℕ, N ≤ m → Period k m t ∧
      ∀ s : ℕ, 0 < s → Period k m s → t ≤ s

theorem period_core {k d e m : ℕ} (hcomp : FibComp k (coreModulus e) d) (hm : d ≤ m) :
    Period k m (coreModulus e) :=
  (periodic_mod_iff (fun x => Nat.fib^[m] x % k) _).mpr (fibComp_more_time hm hcomp)

theorem rank_iterate_dvd_of_period {k m t : ℕ} (hk : 0 < k) (ht : Period k m t) :
    rank^[m] k ∣ t := by
  have h : Nat.fib^[m] t % k = 0 := by
    simpa only [zero_add, fib_iterate_zero, Nat.zero_mod] using ht 0
  exact (dvd_fib_iterate_iff hk m t).mp ((Nat.dvd_iff_mod_eq_zero).mpr h)

theorem rank_later {k d m : ℕ} (hfix : rank (rank^[d] k) = rank^[d] k) (hm : d ≤ m) :
    rank^[m] k = rank^[d] k := by
  obtain ⟨z, rfl⟩ := Nat.exists_eq_add_of_le hm
  rw [Nat.add_comm, Function.iterate_add_apply]
  exact Function.iterate_fixed hfix z

theorem least_later_of_candidate_stability {k N M : ℕ} (hN : 0 < N) (hM : 0 < M)
    (hper : ∀ m, N ≤ m → Period k m M)
    (hstable : ∀ m, N ≤ m → ∀ t, 0 < t → t ∣ M → (Period k N t ↔ Period k m t)) :
    Stabilizes k := by
  obtain ⟨t, ht, htN, htmin⟩ := least_positive_period_dvd hM (hper N le_rfl)
  have htM : t ∣ M := htmin M hM (hper N le_rfl)
  refine ⟨N, t, hN, ht, fun m hm => ⟨(hstable m hm t ht htM).mp htN, ?_⟩⟩
  intro s hs hsm
  obtain ⟨u, hu, hum, hmin⟩ := least_positive_period_dvd hM (hper m hm)
  have huM : u ∣ M := hmin M hM (hper m hm)
  have huN := (hstable m hm u hu huM).mpr hum
  exact Nat.le_of_dvd hs ((htmin u hu huN).trans (hmin s hs hsm))

theorem least_later_of_fixed_period {k N t : ℕ} (hN : 0 < N) (ht : 0 < t)
    (hper : ∀ m, N ≤ m → Period k m t)
    (hmin : ∀ m, N ≤ m → ∀ s, 0 < s → Period k m s → t ∣ s) : Stabilizes k :=
  ⟨N, t, hN, ht, fun m hm => ⟨hper m hm, fun s hs hsm => Nat.le_of_dvd hs (hmin m hm s hs hsm)⟩⟩

theorem stabilizes_one : Stabilizes 1 := by
  refine ⟨1, 1, by decide, by decide, ?_⟩
  intro m _
  exact ⟨fun x => by simp only [Nat.mod_one], fun s hs _ => hs⟩

theorem stabilizes_of_rank_cases {k : ℕ} (hk : 0 < k)
    (pure : ∀ d e b, b ≤ e → FibComp k (coreModulus e) d →
      rank^[d] k = 5 ^ b → 0 < b → rank (rank^[d] k) = rank^[d] k → Stabilizes k)
    (mixed : ∀ d e b, b ≤ e → FibComp k (coreModulus e) d →
      rank^[d] k = 12 * 5 ^ b → rank (rank^[d] k) = rank^[d] k → Stabilizes k) :
    Stabilizes k := by
  by_cases hk1 : k = 1
  · simpa [hk1] using stabilizes_one
  · obtain ⟨d, e, b, hbe, hcomp, hcase, hfix⟩ := stable_rank_and_core (by omega : 1 < k)
    rcases hcase with ⟨hpure, hb⟩ | hmixed
    · exact pure d e b hbe hcomp hpure hb hfix
    · exact mixed d e b hbe hcomp hmixed hfix

end FibPeriod

namespace A395522Fibers

def baseStep (r : Fin 24) : Fin 24 :=
  ⟨Nat.fib r.val % 24, Nat.mod_lt _ (by decide)⟩

def basePath (r : Fin 24) : ℕ → Fin 24
  | 0 => r
  | d + 1 => baseStep (basePath r d)

def baseCore (r : Fin 24) : Prop :=
  r = 0 ∨ r = 1 ∨ r = 5 ∨ r = 13 ∨ r = 17

instance (r : Fin 24) : Decidable (baseCore r) := by
  unfold baseCore
  infer_instance

def baseClass (r : Fin 24) : Fin 4 :=
  ⟨r.val % 4, Nat.mod_lt _ (by decide)⟩

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem base_six_enters_core : ∀ r : Fin 24, baseCore (basePath r 6) := by decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem base_six_zero : ∀ r : Fin 24, basePath r 6 = 0 ↔ r = 0 ∨ r = 12 := by decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem base_core_step (r : Fin 24) (h : baseCore r) :
    baseCore (baseStep r) ∧ baseStep (baseStep r) = r ∧
      (baseStep r = 0 ↔ r = 0) ∧ baseClass r = (if r = 0 then 0 else 1) := by
  have hall : ∀ r : Fin 24, baseCore r →
      baseCore (baseStep r) ∧ baseStep (baseStep r) = r ∧
        (baseStep r = 0 ↔ r = 0) ∧ baseClass r = (if r = 0 then 0 else 1) := by decide
  exact hall r h

theorem base_enters_core_for_later (r : Fin 24) (d : ℕ) :
    baseCore (basePath r (6 + d)) := by
  induction d with
  | zero => exact base_six_enters_core r
  | succ d ih => exact (base_core_step _ ih).1

theorem base_later_zero (r : Fin 24) (d : ℕ) :
    basePath r (6 + d) = 0 ↔ r = 0 ∨ r = 12 := by
  induction d with
  | zero => exact base_six_zero r
  | succ d ih =>
      change baseStep (basePath r (6+d)) = 0 ↔ _
      exact (base_core_step _ (base_enters_core_for_later r d)).2.2.1.trans ih

def multiplier5 (r : Fin 4) : ℕ :=
  if r = 0 then 2 else if r = 1 then 1 else if r = 2 then 3 else 4

def product5 (r : Fin 24) : ℕ → ℕ
  | 0 => 1
  | d + 1 => multiplier5 (baseClass (basePath r d)) * product5 r d % 5

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem base_shift_detected : ∀ s : Fin 24, s ≠ 0 → ∃ r : Fin 24,
    basePath r 6 ≠ 0 ∧ basePath (r + s) 6 ≠ 0 ∧ product5 r 6 ≠ product5 (r + s) 6 := by
  decide

theorem product5_lt (r : Fin 24) (d : ℕ) : product5 r d < 5 := by
  cases d with
  | zero => change 1 < 5; decide
  | succ d => exact Nat.mod_lt _ (by decide)

theorem product5_later (r : Fin 24) (hn : basePath r 6 ≠ 0) (d : ℕ) :
    product5 r (6 + d) = product5 r 6 := by
  induction d with
  | zero => rfl
  | succ d ih =>
      have hp : basePath r (6 + d) ≠ 0 := fun h ↦ hn ((base_six_zero r).2 ((base_later_zero r d).1 h))
      have hc : baseClass (basePath r (6+d)) = 1 := by
        simpa [hp] using (base_core_step _ (base_enters_core_for_later r d)).2.2.2
      change multiplier5 (baseClass (basePath r (6+d))) * product5 r (6+d) % 5 = product5 r 6
      rw [hc, ih]
      simpa [multiplier5] using Nat.mod_eq_of_lt (product5_lt r 6)

def relativeTrail (r s : Fin 24) : ℕ → Option Bool
  | 0 => some false
  | d + 1 => do
    let leading ← relativeTrail r s d
    let a := baseClass (basePath r d)
    let b := baseClass (basePath s d)
    if b = a then some leading else
      if b = a + 2 then some (!leading) else none

def pairType (r s : Fin 24) (d : ℕ) : Fin 24 × Fin 24 × Option Bool :=
  (basePath r d, basePath s d, relativeTrail r s d)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem half_shift_path (r : Fin 24) : ∃ flip : Bool,
    relativeTrail r (r+12) 6 = some flip ∧
      (basePath r 6 = 0 ↔ basePath (r+12) 6 = 0) ∧
      (basePath r 6 = 0 → flip = false) := by
  have hall : ∀ r : Fin 24, ∃ flip : Bool,
      relativeTrail r (r+12) 6 = some flip ∧
        (basePath r 6 = 0 ↔ basePath (r+12) 6 = 0) ∧
        (basePath r 6 = 0 → flip = false) := by decide
  exact hall r

theorem half_shift_edges :
    pairType 1 (1+12) 6 = (1, 13, some false) ∧
    pairType 3 (3+12) 6 = (1, 17, some true) ∧
    pairType 5 (5+12) 6 = (5, 17, some false) ∧
    pairType 6 (6+12) 6 = (1, 1, some true) := by
  decide

end A395522Fibers

namespace A395522Fibers

section

variable {Y α : Type*} [AddGroup Y]

def twist (flag : Bool) (y : Y) : Y := if flag then -y else y

def fiberPath (phi : Fin 4 → Y → Y) (r : Fin 24) (y : Y) : ℕ → Y
  | 0 => y
  | d + 1 => phi (baseClass (basePath r d)) (fiberPath phi r y d)

omit [AddGroup Y] in
theorem fiberPath_surjective (phi : Fin 4 → Y → Y)
    (hphi : ∀ c, Function.Surjective (phi c)) (r : Fin 24) (d : ℕ) :
    Function.Surjective (fun y => fiberPath phi r y d) := by
  induction d with
  | zero => exact Function.surjective_id
  | succ d ih => exact (hphi _).comp ih

theorem fiberPath_relative (phi : Fin 4 → Y → Y)
    (hodd : ∀ c y, phi c (-y) = -phi c y)
    (hhalf : ∀ c y, phi (c + 2) y = -phi c y)
    (r s : Fin 24) (y : Y) (d : ℕ) (flag : Bool)
    (h : relativeTrail r s d = some flag) :
    fiberPath phi s y d = twist flag (fiberPath phi r y d) := by
  induction d generalizing flag with
  | zero =>
      change some false = some flag at h
      cases h
      rfl
  | succ d ih =>
      cases hp : relativeTrail r s d with
      | none => simp [relativeTrail, hp] at h
      | some previous =>
          by_cases hs : baseClass (basePath s d) = baseClass (basePath r d)
          · simp [relativeTrail, hp, hs] at h
            subst flag
            simp only [fiberPath, hs, ih previous hp]
            cases previous <;> simp [twist, hodd]
          · by_cases hs' : baseClass (basePath s d) = baseClass (basePath r d) + 2
            · have hne : baseClass (basePath r d) + 2 ≠ baseClass (basePath r d) :=
                fun e ↦ hs (hs'.trans e)
              simp [relativeTrail, hp, hs', hne] at h
              have he : flag = !previous := by rw [h]; cases flag <;> rfl
              subst flag
              simp only [fiberPath, hs', ih previous hp, hhalf]
              cases previous <;> simp [twist, hodd]
            · simp [relativeTrail, hp, hs, hs'] at h

def collapseNonzero (H : Fin 24 → Y → α) : Prop :=
  ∀ a b y flag, baseCore a → a ≠ 0 → baseCore b → b ≠ 0 → H a y = H b (twist flag y)

theorem half_observation_six (phi : Fin 4 → Y → Y)
    (hodd : ∀ c y, phi c (-y) = -phi c y)
    (hhalf : ∀ c y, phi (c + 2) y = -phi c y)
    (hsurj : ∀ c, Function.Surjective (phi c)) (H : Fin 24 → Y → α) :
    (∀ r y, H (basePath r 6) (fiberPath phi r y 6) =
      H (basePath (r+12) 6) (fiberPath phi (r+12) y 6)) ↔ collapseNonzero H := by
  constructor
  · intro hyp
    have edge (r a b : Fin 24) (flag : Bool)
        (he : pairType r (r+12) 6 = (a, b, some flag)) (y : Y) :
        H a y = H b (twist flag y) := by
      have ha := congrArg Prod.fst he
      have hb := congrArg (fun z => z.2.1) he
      have hflag := congrArg (fun z => z.2.2) he
      change basePath r 6 = a at ha
      change basePath (r+12) 6 = b at hb
      change relativeTrail r (r+12) 6 = some flag at hflag
      obtain ⟨x, hx⟩ := fiberPath_surjective phi hsurj r 6 y
      change fiberPath phi r x 6 = y at hx
      have h := hyp r x
      rw [ha, hb, fiberPath_relative phi hodd hhalf _ _ _ _ _ hflag, hx] at h
      exact h
    have edge113 (y : Y) : H 1 y = H 13 y := by
      simpa [twist] using edge 1 1 13 false half_shift_edges.1 y
    have edge117 (y : Y) : H 1 y = H 17 (-y) := by
      simpa [twist] using edge 3 1 17 true half_shift_edges.2.1 y
    have edge517 (y : Y) : H 5 y = H 17 y := by
      simpa [twist] using edge 5 5 17 false half_shift_edges.2.2.1 y
    have edge11 (y : Y) : H 1 y = H 1 (-y) := by
      simpa [twist] using edge 6 1 1 true half_shift_edges.2.2.2 y
    have allToOne (a : Fin 24) (ha : baseCore a) (ha0 : a ≠ 0) (y : Y) : H a y = H 1 y := by
      have eq17 : H 17 y = H 1 y := by
        calc
          H 17 y = H 1 (-y) := by simpa using (edge117 (-y)).symm
          _ = H 1 y := (edge11 y).symm
      unfold baseCore at ha
      rcases ha with h | h | h | h | h <;> subst a
      · exact (ha0 rfl).elim
      · rfl
      · exact (edge517 y).trans eq17
      · exact (edge113 y).symm
      · exact eq17
    intro a b y flag ha ha0 hb hb0
    rw [allToOne a ha ha0, allToOne b hb hb0]
    cases flag
    · rfl
    · exact edge11 y
  · intro hyp r y
    obtain ⟨flag, hflag, hzero, hzeroFlag⟩ := half_shift_path r
    rw [fiberPath_relative phi hodd hhalf _ _ _ _ _ hflag]
    by_cases hz : basePath r 6 = 0
    · rw [hz, hzero.1 hz, hzeroFlag hz]
      rfl
    · exact hyp _ _ _ _ (base_six_enters_core r) hz (base_six_enters_core (r+12))
        (fun h ↦ hz (hzero.2 h))

theorem basePath_add (r : Fin 24) (d e : ℕ) :
    basePath r (d+e) = basePath (basePath r d) e := by
  induction e with
  | zero => rfl
  | succ e ih => exact congrArg baseStep ih

omit [AddGroup Y] in
theorem fiberPath_add (phi : Fin 4 → Y → Y) (r : Fin 24) (y : Y) (d e : ℕ) :
    fiberPath phi r y (d+e) = fiberPath phi (basePath r d) (fiberPath phi r y d) e := by
  induction e with
  | zero => rfl
  | succ e ih =>
      change phi (baseClass (basePath r (d+e))) (fiberPath phi r y (d+e)) =
        phi (baseClass (basePath (basePath r d) e)) (fiberPath phi (basePath r d) (fiberPath phi r y d) e)
      rw [basePath_add r d e, ih]

end

end A395522Fibers

namespace A395522Fibers

theorem basePath_core (r : Fin 24) (d : ℕ) (hr : baseCore r) :
    baseCore (basePath r d) := by
  induction d with
  | zero => exact hr
  | succ d ih => exact (base_core_step _ ih).1

theorem basePath_zero_iff (r : Fin 24) (d : ℕ) (hr : baseCore r) :
    basePath r d = 0 ↔ r = 0 := by
  induction d with
  | zero => rfl
  | succ d ih => exact (base_core_step _ (basePath_core r d hr)).2.2.1.trans ih

theorem basePath_start_step (r : Fin 24) (d : ℕ) :
    basePath (baseStep r) d = baseStep (basePath r d) := by
  induction d with
  | zero => rfl
  | succ d ih => exact congrArg baseStep ih

theorem basePath_involutive (r : Fin 24) (d : ℕ) (hr : baseCore r) :
    basePath (basePath r d) d = r := by
  induction d with
  | zero => rfl
  | succ d ih =>
      change baseStep (basePath (baseStep (basePath r d)) d) = r
      rw [basePath_start_step, ih]
      exact (base_core_step _ hr).2.1

theorem fiberPath_nonzero {Y : Type*} (phi : Fin 4 → Y → Y) (r : Fin 24) (d : ℕ)
    (hr : baseCore r) (hr0 : r ≠ 0) (y : Y) :
    fiberPath phi r y d = (phi 1)^[d] y := by
  induction d with
  | zero => rfl
  | succ d ih =>
      have hn : basePath r d ≠ 0 := fun e ↦ hr0 ((basePath_zero_iff r d hr).mp e)
      have hc : baseClass (basePath r d) = 1 := by
        simpa [hn] using (base_core_step _ (basePath_core r d hr)).2.2.2
      change phi (baseClass (basePath r d)) (fiberPath phi r y d) = (phi 1)^[d+1] y
      rw [hc, ih, Function.iterate_succ_apply']

theorem twist_iterate {Y : Type*} [AddGroup Y] (f : Y → Y) (hf : ∀ z, f (-z) = -f z)
    (d : ℕ) (flag : Bool) (y : Y) : f^[d] (twist flag y) = twist flag (f^[d] y) := by
  cases flag with
  | false => rfl
  | true =>
      change f^[d] (-y) = -(f^[d] y)
      induction d with
      | zero => rfl
      | succ d ih => rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih, hf]

theorem half_observation_later {Y α : Type*} [AddGroup Y] (phi : Fin 4 → Y → Y)
    (hodd : ∀ c y, phi c (-y) = -phi c y)
    (hhalf : ∀ c y, phi (c+2) y = -phi c y)
    (hsurj : ∀ c, Function.Surjective (phi c)) (H : Fin 24 → Y → α) (d : ℕ) :
    (∀ r y, H (basePath r (6+d)) (fiberPath phi r y (6+d)) =
      H (basePath (r+12) (6+d)) (fiberPath phi (r+12) y (6+d))) ↔ collapseNonzero H := by
  let shifted (r : Fin 24) (y : Y) := H (basePath r d) (fiberPath phi r y d)
  have hshift : (∀ r y, H (basePath r (6+d)) (fiberPath phi r y (6+d)) =
      H (basePath (r+12) (6+d)) (fiberPath phi (r+12) y (6+d))) ↔ collapseNonzero shifted := by
    simpa only [shifted, basePath_add _ 6 d, fiberPath_add _ _ _ 6 d] using
      half_observation_six phi hodd hhalf hsurj shifted
  refine hshift.trans ⟨?_, ?_⟩
  · intro h a b y flag ha ha0 hb hb0
    have hca := basePath_core a d ha
    have hcb := basePath_core b d hb
    have hca0 : basePath a d ≠ 0 := fun e ↦ ha0 ((basePath_zero_iff a d ha).mp e)
    have hcb0 : basePath b d ≠ 0 := fun e ↦ hb0 ((basePath_zero_iff b d hb).mp e)
    obtain ⟨z, hz⟩ := fiberPath_surjective phi hsurj a d y
    change fiberPath phi a z d = y at hz
    rw [fiberPath_nonzero phi a d ha ha0] at hz
    have he := h (basePath a d) (basePath b d) z flag hca hca0 hcb hcb0
    dsimp only [shifted] at he
    rw [basePath_involutive a d ha, basePath_involutive b d hb,
      fiberPath_nonzero phi _ d hca hca0, fiberPath_nonzero phi _ d hcb hcb0,
      twist_iterate (phi 1) (hodd 1), hz] at he
    exact he
  · intro h a b y flag ha ha0 hb hb0
    dsimp only [shifted]
    rw [fiberPath_nonzero phi a d ha ha0, fiberPath_nonzero phi b d hb hb0,
      twist_iterate (phi 1) (hodd 1)]
    exact h _ _ _ _ (basePath_core a d ha) (fun e ↦ ha0 ((basePath_zero_iff a d ha).mp e))
      (basePath_core b d hb) (fun e ↦ hb0 ((basePath_zero_iff b d hb).mp e))

end A395522Fibers

namespace A395522Fibers

def fibZ (n : ℕ) : ℤ := Nat.fib n

theorem fibZ_add_two (n : ℕ) : fibZ (n+2) = fibZ n + fibZ (n+1) := by
  simp [fibZ, Nat.fib_add_two]

def lucas (n : ℕ) : ℕ := 2 * Nat.fib (n+1) - Nat.fib n

theorem lucas_cast (n : ℕ) : (lucas n : ℤ) = 2 * fibZ (n+1) - fibZ n := by
  have h : Nat.fib n ≤ 2 * Nat.fib (n+1) := by
    have hf : Nat.fib n ≤ Nat.fib (n+1) := Nat.fib_le_fib_succ
    omega
  simp [lucas, fibZ, Int.ofNat_sub h]

theorem lucasZ_add_two (n : ℕ) :
    (lucas (n+2) : ℤ) = (lucas n : ℤ) + (lucas (n+1) : ℤ) := by
  rw [lucas_cast, lucas_cast, lucas_cast, show n+2+1=n+1+2 by omega,
    fibZ_add_two (n+1), fibZ_add_two n]
  ring

theorem fibZ_twice (n : ℕ) : fibZ (2*n) = fibZ n * (lucas n : ℤ) := by
  unfold fibZ lucas
  rw [Nat.fib_two_mul, Nat.cast_mul]

theorem fibZ_twice_succ (n : ℕ) : fibZ (2*n+1) = fibZ (n+1)^2 + fibZ n^2 := by
  simp [fibZ, Nat.fib_two_mul_add_one]

theorem fibZ_cassini (n : ℕ) :
    fibZ (n+1)^2 - fibZ n * fibZ (n+1) - fibZ n^2 = (-1 : ℤ)^n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [show n.succ+1=n+2 by omega, fibZ_add_two, pow_succ]
      calc
        _ = -(fibZ (n+1)^2 - fibZ n * fibZ (n+1) - fibZ n^2) := by ring
        _ = _ := by rw [ih]; ring

theorem fibZ_difference_even (r d : ℕ) (hd : Even d) :
    fibZ (r+2*d) - fibZ r = fibZ d * (lucas (r+d) : ℤ) := by
  let P (n : ℕ) := fibZ (n+2*d) - fibZ n = fibZ d * (lucas (n+d) : ℤ)
  have h0 : P 0 := by simpa [P, fibZ] using fibZ_twice d
  have h1 : P 1 := by
    have hp : (-1 : ℤ)^d = 1 := by
      rcases hd with ⟨i, hi⟩
      rw [hi, ← two_mul, pow_mul]
      simp [show (-1 : ℤ)^2 = 1 by decide]
    have hc := fibZ_cassini d
    rw [hp] at hc
    change fibZ (1+2*d) - fibZ 1 = fibZ d * (lucas (1+d) : ℤ)
    rw [show 1+2*d=2*d+1 by omega, fibZ_twice_succ, show fibZ 1=1 by rfl,
      show 1+d=d+1 by omega, lucas_cast, show d+1+1=d+2 by omega, fibZ_add_two]
    apply sub_eq_zero.mp
    calc
      _ = (fibZ (d+1)^2 - fibZ d * fibZ (d+1) - fibZ d^2) - 1 := by ring
      _ = 0 := by rw [hc]; decide
  have hs (n : ℕ) (ha : P n) (hb : P (n+1)) : P (n+2) := by
    change fibZ (n+2*d) - fibZ n = _ at ha
    change fibZ (n+1+2*d) - fibZ (n+1) = _ at hb
    change fibZ (n+2+2*d) - fibZ (n+2) = _
    rw [show n+2+2*d=n+2*d+2 by omega, fibZ_add_two (n+2*d),
      show n+2*d+1=n+1+2*d by omega, fibZ_add_two n]
    calc
      _ = (fibZ (n+2*d) - fibZ n) + (fibZ (n+1+2*d) - fibZ (n+1)) := by ring
      _ = _ := by
        rw [ha, hb, show n+2+d=n+d+2 by omega, lucasZ_add_two,
          show n+d+1=n+1+d by omega]
        ring
  have hall : ∀ n, P n ∧ P (n+1) := by
    intro n
    induction n with
    | zero => exact ⟨h0, h1⟩
    | succ n ih => exact ⟨ih.2, hs n ih.1 ih.2⟩
  exact (hall r).1

theorem odd_rank_lucas_coprime (z : ℕ → ℕ)
    (hz : ∀ q, 0 < q → ∀ n, q ∣ Nat.fib n ↔ z q ∣ n)
    (q : ℕ) (hq : 0 < q) (hqo : Odd q) (hzo : Odd (z q)) (s : ℕ) :
    q.Coprime (lucas s) := by
  by_contra hc
  obtain ⟨p, hp, hpq, hpl⟩ := Nat.Prime.not_coprime_iff_dvd.mp hc
  have hzp : z p ∣ z q := (hz p hp.pos _).mp (hpq.trans ((hz q hq _).mpr dvd_rfl))
  have hzpo : Odd (z p) := Nat.not_even_iff_odd.mp fun he ↦ hzo.not_two_dvd_nat (he.two_dvd.trans hzp)
  have hF : p ∣ Nat.fib (2*s) := by
    rw [Nat.fib_two_mul]
    exact dvd_mul_of_dvd_right hpl _
  have hs : z p ∣ s := (Nat.coprime_two_right.mpr hzpo).dvd_of_dvd_mul_right (by
    simpa [Nat.mul_comm] using (hz p hp.pos _).mp hF)
  have hfs : p ∣ Nat.fib s := (hz p hp.pos _).mpr hs
  have hsum : lucas s + Nat.fib s = 2 * Nat.fib (s+1) := by
    have hle : Nat.fib s ≤ Nat.fib (s+1) := Nat.fib_le_fib_succ
    unfold lucas
    omega
  have h2 : p ∣ 2 * Nat.fib (s+1) := hsum ▸ dvd_add hpl hfs
  have hpn2 : ¬p ∣ 2 := by
    intro hpd
    rcases (Nat.dvd_prime Nat.prime_two).mp hpd with h | h
    · exact hp.ne_one h
    · exact hqo.not_two_dvd_nat (h ▸ hpq)
  have hn : p ∣ Nat.fib (s+1) := (hp.dvd_mul.mp h2).resolve_left hpn2
  have hg : Nat.gcd (Nat.fib s) (Nat.fib (s+1)) = 1 := Nat.fib_coprime_fib_succ s
  exact hp.ne_one (Nat.dvd_one.mp (hg ▸ Nat.dvd_gcd hfs hn))

theorem fib_modEq_odd_rank (z : ℕ → ℕ)
    (hz : ∀ q, 0 < q → ∀ n, q ∣ Nat.fib n ↔ z q ∣ n)
    (q : ℕ) (hq : 0 < q) (hqo : Odd q) (hzo : Odd (z q))
    {x y : ℕ} (hxy : x ≡ y [MOD 4]) :
    Nat.fib x ≡ Nat.fib y [MOD q] ↔ x ≡ y [MOD z q] := by
  have core (r d : ℕ) (hd : Even d) :
      Nat.fib r ≡ Nat.fib (r+2*d) [MOD q] ↔ r ≡ r+2*d [MOD z q] := by
    have hf := fibZ_difference_even r d hd
    have hfc : ((Nat.fib d * lucas (r+d) : ℕ) : ℤ) = fibZ d * (lucas (r+d) : ℤ) := by
      simp [fibZ]
    rw [Nat.modEq_iff_dvd (n := q)]
    change ((q : ℤ) ∣ fibZ (r+2*d) - fibZ r) ↔ _
    rw [hf, ← hfc, Int.natCast_dvd_natCast, (odd_rank_lucas_coprime z hz q hq hqo hzo _).dvd_mul_right,
      hz q hq d, Nat.modEq_iff_dvd' (by omega : r ≤ r+2*d), Nat.add_sub_cancel_left]
    simpa [Nat.mul_comm] using ((Nat.coprime_two_right.mpr hzo).dvd_mul_right (m := d)).symm
  rcases le_total x y with hle | hle
  · obtain ⟨s, hs⟩ := hxy.dvd'
    have hy : y = x + 2*(2*s) := by omega
    rw [hy]
    exact core x (2*s) (even_two_mul _)
  · obtain ⟨s, hs⟩ := hxy.symm.dvd'
    have hx : x = y + 2*(2*s) := by omega
    rw [hx]
    exact ⟨fun h ↦ ((core y (2*s) (even_two_mul _)).mp h.symm).symm,
      fun h ↦ ((core y (2*s) (even_two_mul _)).mpr h.symm).symm⟩

end A395522Fibers

namespace A395522Fibers

def fibC (L n : ℕ) : ZMod L := Nat.fib n

@[simp] theorem fibC_zero (L : ℕ) : fibC L 0 = 0 := by simp [fibC]

@[simp] theorem fibC_one (L : ℕ) : fibC L 1 = 1 := by simp [fibC]

theorem fibC_add_two (L n : ℕ) : fibC L (n+2) = fibC L n + fibC L (n+1) := by
  simp [fibC, Nat.fib_add_two]

theorem fibC_neg_half_period (L : ℕ) (hodd : Odd L) (hdiv : L ∣ Nat.fib L) (n : ℕ) :
    fibC L (n+2*L) = -fibC L n := by
  have hz : fibC L L = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr hdiv
  have h0 : fibC L (0+2*L) = -fibC L 0 := by
    have hf : L ∣ Nat.fib (2*L) := hdiv.trans (Nat.fib_dvd _ _ (dvd_mul_left _ _))
    simpa [fibC] using (ZMod.natCast_eq_zero_iff _ _).mpr hf
  have hc : fibC L (L+1)^2 - fibC L L * fibC L (L+1) - fibC L L^2 = (-1 : ZMod L)^L := by
    have h := congrArg (fun z : ℤ => (z : ZMod L)) (fibZ_cassini L)
    simpa [fibC, fibZ] using h
  rw [hz, zero_mul, zero_pow (by decide), sub_zero, sub_zero, hodd.neg_one_pow] at hc
  have h1 : fibC L (1+2*L) = -fibC L 1 := by
    have ht : fibC L (2*L+1) = fibC L (L+1)^2 + fibC L L^2 := by
      simp [fibC, Nat.fib_two_mul_add_one]
    rw [Nat.add_comm 1, ht, hz, zero_pow (by decide), add_zero, hc, fibC_one]
  have hpair : ∀ j, (fibC L (j+2*L) = -fibC L j) ∧
      (fibC L (j+1+2*L) = -fibC L (j+1)) := by
    intro j
    induction j with
    | zero => exact ⟨h0, h1⟩
    | succ j ih =>
        refine ⟨ih.2, ?_⟩
        rw [show j+1+1+2*L=j+2*L+2 by omega, show j+1+1=j+2 by omega,
          fibC_add_two, fibC_add_two, show j+2*L+1=j+1+2*L by omega, ih.1, ih.2, neg_add]
  exact (hpair n).1

theorem fibC_full_period (L : ℕ) (hodd : Odd L) (hdiv : L ∣ Nat.fib L) (n : ℕ) :
    fibC L (n+4*L) = fibC L n := by
  rw [show n+4*L=n+2*L+2*L by omega,
    fibC_neg_half_period L hodd hdiv, fibC_neg_half_period L hodd hdiv, neg_neg]

theorem fibC_reflect_period (L P : ℕ) (hP : 2 ≤ P)
    (hz : fibC L P = 0) (ho : fibC L (P+1) = 1) (n : ℕ) (hn : n ≤ P) :
    fibC L (P-n) = (-1 : ZMod L)^(n+1) * fibC L n := by
  have f1 : fibC L (P-1) = 1 := by
    have hs : fibC L (P+1) = fibC L (P-1) + fibC L P := by
      have h := fibC_add_two L (P-1)
      rw [show P-1+2=P+1 by omega, show P-1+1=P by omega] at h
      exact h
    rw [hz, add_zero, ho] at hs
    exact hs.symm
  have claim : ∀ t, t ≤ P → fibC L (P-t) = (-1 : ZMod L)^(t+1) * fibC L t := by
    intro t
    induction t using Nat.strong_induction_on with
    | h t ih =>
        intro ht
        rcases t with _ | t
        · simp [hz]
        rcases t with _ | j
        · change fibC L (P-1) = (-1 : ZMod L)^2 * fibC L 1
          simp [f1]
        · have h0 := ih j (by omega) (by omega)
          have h1 := ih (j+1) (by omega) (by omega)
          have hrec : fibC L (P-j) = fibC L (P-(j+2)) + fibC L (P-(j+1)) := by
            have h := fibC_add_two L (P-(j+2))
            rw [show P-(j+2)+2=P-j by omega, show P-(j+2)+1=P-(j+1) by omega] at h
            exact h
          change fibC L (P-(j+2)) = (-1 : ZMod L)^(j+2+1) * fibC L (j+2)
          calc
            fibC L (P-(j+2)) = fibC L (P-j) - fibC L (P-(j+1)) := by rw [hrec]; simp
            _ = _ := by
              rw [h0, h1, fibC_add_two]
              simp only [pow_succ]
              ring
  exact claim n hn

theorem fibC_reflect (L : ℕ) (hL : 0 < L) (hodd : Odd L) (hdiv : L ∣ Nat.fib L)
    (n : ℕ) (hn : n ≤ 4*L) :
    fibC L (4*L-n) = (-1 : ZMod L)^(n+1) * fibC L n := by
  refine fibC_reflect_period L (4*L) (by omega) ?_ ?_ n hn
  · simpa using fibC_full_period L hodd hdiv 0
  · simpa [Nat.add_comm 1] using fibC_full_period L hodd hdiv 1

end A395522Fibers

namespace A395522Fibers

def representative (L : ℕ) (a : Fin 4) (y : ZMod L) : ℕ :=
  y.val + L * ((a.val + 4 - y.val % 4) % 4)

theorem rep_mod_four (L : ℕ) (hL : L % 4 = 1) (a : Fin 4) (y : ZMod L) :
    representative L a y % 4 = a.val := by
  have ha := a.isLt
  unfold representative
  rw [Nat.add_mod, Nat.mul_mod, hL, one_mul, Nat.mod_mod]
  omega

theorem rep_cast (L : ℕ) [NeZero L] (a : Fin 4) (y : ZMod L) :
    (representative L a y : ZMod L) = y := by
  simp [representative]

theorem rep_lt (L : ℕ) [NeZero L] (a : Fin 4) (y : ZMod L) :
    representative L a y < 4*L := by
  have hy := ZMod.val_lt y
  have ho : (a.val+4-y.val%4)%4 ≤ 3 := by omega
  have hm := Nat.mul_le_mul_left L ho
  unfold representative
  omega

def phi (L : ℕ) (a : Fin 4) (y : ZMod L) : ZMod L :=
  fibC L (representative L a y)

section Phi

variable (z : ℕ → ℕ) (zspec : ∀ q, 0 < q → ∀ n, q ∣ Nat.fib n ↔ z q ∣ n)
variable (L : ℕ) [NeZero L] (hL4 : L % 4 = 1) (hRank : z L = L)

private theorem odd_of_mod_four (q : ℕ) (h : q % 4 = 1) : Odd q :=
  ⟨q / 2, by omega⟩

include zspec hL4 hRank

theorem phi_eval (a : Fin 4) (y : ZMod L) (n : ℕ) (hn4 : n % 4 = a.val)
    (hnL : (n : ZMod L) = y) : phi L a y = fibC L n := by
  have hxy : representative L a y ≡ n [MOD 4] := (rep_mod_four L hL4 a y).trans hn4.symm
  have ho := odd_of_mod_four L hL4
  have hzo : Odd (z L) := by simpa only [hRank] using ho
  have h := fib_modEq_odd_rank z zspec L (NeZero.pos L) ho hzo hxy
  rw [hRank] at h
  apply (ZMod.natCast_eq_natCast_iff _ _ _).mpr
  exact h.mpr ((ZMod.natCast_eq_natCast_iff _ _ _).mp ((rep_cast L a y).trans hnL.symm))

theorem phi_injective (a : Fin 4) : Function.Injective (phi L a) := by
  intro y y' h
  have hxy : representative L a y ≡ representative L a y' [MOD 4] :=
    (rep_mod_four L hL4 a y).trans (rep_mod_four L hL4 a y').symm
  have ho := odd_of_mod_four L hL4
  have hzo : Odd (z L) := by simpa only [hRank] using ho
  have hh := fib_modEq_odd_rank z zspec L (NeZero.pos L) ho hzo hxy
  rw [hRank] at hh
  have hcast := (ZMod.natCast_eq_natCast_iff _ _ _).mpr
    (hh.mp ((ZMod.natCast_eq_natCast_iff _ _ _).mp h))
  exact (rep_cast L a y).symm.trans (hcast.trans (rep_cast L a y'))

theorem phi_surjective (a : Fin 4) : Function.Surjective (phi L a) :=
  Finite.injective_iff_surjective.mp (phi_injective z zspec L hL4 hRank a)

theorem phi_half (a : Fin 4) (y : ZMod L) : phi L (a+2) y = -phi L a y := by
  let x := representative L a y
  have hx := rep_mod_four L hL4 a y
  have hx4 : (x+2*L) % 4 = (a+2).val := by
    change (representative L a y+2*L) % 4 = (a.val+2) % 4
    omega
  have hxL : ((x+2*L : ℕ) : ZMod L) = y := by
    change ((representative L a y + 2*L : ℕ) : ZMod L) = y
    simp [rep_cast]
  have hdiv : L ∣ Nat.fib L := (zspec L (NeZero.pos L) L).mpr (by rw [hRank])
  rw [phi_eval z zspec L hL4 hRank _ _ _ hx4 hxL,
    fibC_neg_half_period L (odd_of_mod_four L hL4) hdiv]
  rfl

theorem phi_odd (a : Fin 4) (y : ZMod L) : phi L a (-y) = -phi L a y := by
  let x := representative L a y
  have hxle : x ≤ 4*L := (rep_lt L a y).le
  have hx4 : x % 4 = a.val := rep_mod_four L hL4 a y
  have ha := a.isLt
  have hdiv : L ∣ Nat.fib L := (zspec L (NeZero.pos L) L).mpr (by rw [hRank])
  have hodd := odd_of_mod_four L hL4
  have hf := fibC_reflect L (NeZero.pos L) hodd hdiv x hxle
  have hback : ((4*L-x : ℕ) : ZMod L) = -y := by
    rw [Nat.cast_sub hxle]
    change (↑(4*L : ℕ) : ZMod L) - ↑(representative L a y) = -y
    simp [rep_cast]
  by_cases hae : a.val % 2 = 0
  · have hback4 : (4*L-x) % 4 = a.val := by omega
    have hxodd : Odd (x+1) := ⟨x/2, by omega⟩
    rw [phi_eval z zspec L hL4 hRank _ _ _ hback4 hback, hf, hxodd.neg_one_pow, neg_one_mul]
    rfl
  · have hback4 : (4*L-x+2*L) % 4 = a.val := by omega
    have hback2 : ((4*L-x+2*L : ℕ) : ZMod L) = -y := by
      simp [hback]
    have hxeven : Even (x+1) := ⟨(x+1)/2, by omega⟩
    rw [phi_eval z zspec L hL4 hRank _ _ _ hback4 hback2,
      fibC_neg_half_period L hodd hdiv, hf, hxeven.neg_one_pow, one_mul]
    rfl

end Phi

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem five_multiplier_check : ∀ n : Fin 20,
    fibC 5 n.val = (multiplier5 ⟨n.val % 4, Nat.mod_lt _ (by decide)⟩ : ZMod 5) * n.val := by
  decide

theorem five_multiplier (n : ℕ) :
    fibC 5 n = (multiplier5 ⟨n % 4, Nat.mod_lt _ (by decide)⟩ : ZMod 5) * n := by
  have hp : Function.Periodic (fibC 5) 20 := fibC_full_period 5 (by decide) (by decide)
  let i : Fin 20 := ⟨n%20, Nat.mod_lt _ (by decide)⟩
  have hfour : (⟨i.val%4, Nat.mod_lt _ (by decide)⟩ : Fin 4) =
      ⟨n%4, Nat.mod_lt _ (by decide)⟩ := by
    apply Fin.ext
    change n % 20 % 4 = n % 4
    omega
  have hfive : (i.val : ZMod 5) = (n : ZMod 5) := by
    apply (ZMod.natCast_eq_natCast_iff _ _ _).mpr
    change n % 20 % 5 = n % 5
    omega
  have hf := five_multiplier_check i
  rw [hfour, hfive] at hf
  exact (hp.map_mod_nat n).symm.trans hf

end A395522Fibers

namespace A395522Fibers

theorem fiberPath_injective {Y : Type*} (phi : Fin 4 → Y → Y)
    (hphi : ∀ c, Function.Injective (phi c)) (r : Fin 24) (d : ℕ) :
    Function.Injective (fun y => fiberPath phi r y d) := by
  induction d with
  | zero => exact Function.injective_id
  | succ d ih => exact (hphi _).comp ih

theorem fiberPath_project {Y W : Type*} (phi : Fin 4 → Y → Y) (psi : Fin 4 → W → W)
    (rho : Y → W) (h : ∀ c y, rho (phi c y) = psi c (rho y))
    (r : Fin 24) (d : ℕ) (y : Y) :
    rho (fiberPath phi r y d) = fiberPath psi r (rho y) d := by
  induction d with
  | zero => rfl
  | succ d ih =>
      simp only [fiberPath, h, ih]

def observation {Y α : Type*} (phi : Fin 4 → Y → Y) (d : ℕ)
    (H : Fin 24 → Y → α) (r : Fin 24) (y : Y) : α :=
  H (basePath r d) (fiberPath phi r y d)

def constantInBase {Y W α : Type*} (rho : Y → W) (H : Fin 24 → Y → α) : Prop :=
  ∀ r, baseCore r → ∀ x y, rho x = rho y → H r x = H r y

theorem full_observation_later {Y W α : Type*} (phi : Fin 4 → Y → Y)
    (psi : Fin 4 → W → W) (rho : Y → W)
    (hproject : ∀ c y, rho (phi c y) = psi c (rho y))
    (hphi : ∀ c, Function.Surjective (phi c)) (hpsi : ∀ c, Function.Injective (psi c))
    (H : Fin 24 → Y → α) (d : ℕ) :
    (∀ r x y, rho x = rho y →
      observation phi (6+d) H r x = observation phi (6+d) H r y) ↔ constantInBase rho H := by
  constructor
  · intro h r hr x y hxy
    let base := basePath r (6+d)
    obtain ⟨a, ha⟩ := fiberPath_surjective phi hphi base (6+d) x
    obtain ⟨b, hb⟩ := fiberPath_surjective phi hphi base (6+d) y
    change fiberPath phi base a (6+d) = x at ha
    change fiberPath phi base b (6+d) = y at hb
    have hp : rho (fiberPath phi base a (6+d)) = rho (fiberPath phi base b (6+d)) := by
      rw [ha, hb, hxy]
    rw [fiberPath_project phi psi rho hproject, fiberPath_project phi psi rho hproject] at hp
    have hab := fiberPath_injective psi hpsi base (6+d) hp
    have hh := h base a b hab
    unfold observation at hh
    rw [show basePath base (6+d) = r from basePath_involutive r (6+d) hr, ha, hb] at hh
    exact hh
  · intro h r x y hxy
    apply h _ (base_enters_core_for_later r d)
    rw [fiberPath_project phi psi rho hproject, fiberPath_project phi psi rho hproject, hxy]

def constantBetweenSigns {Y W α : Type*} [AddGroup W] (rho : Y → W)
    (H : Fin 24 → Y → α) : Prop :=
  ∀ r s x y flag, baseCore r → r ≠ 0 → baseCore s → s ≠ 0 →
    rho y = twist flag (rho x) → H r x = H s y

theorem half_observation_projected {Y W α : Type*} [AddGroup W]
    (phi : Fin 4 → Y → Y) (psi : Fin 4 → W → W) (rho : Y → W)
    (hproject : ∀ c y, rho (phi c y) = psi c (rho y))
    (hpsi : ∀ c, Function.Surjective (psi c)) (hrho : Function.Surjective rho)
    (hodd : ∀ c y, psi c (-y) = -psi c y)
    (hhalf : ∀ c y, psi (c+2) y = -psi c y)
    (H : Fin 24 → Y → α) (d : ℕ) (hfull : constantInBase rho H) :
    (∀ r x y, rho x = rho y → observation phi (6+d) H r x =
      observation phi (6+d) H (r+12) y) ↔ constantBetweenSigns rho H := by
  classical
  let lift (r : Fin 24) (w : W) := H r (Classical.choose (hrho w))
  have hlift (r : Fin 24) (y : Y) (hr : baseCore r) : lift r (rho y) = H r y :=
    hfull r hr _ _ (Classical.choose_spec (hrho (rho y)))
  have hobs (r : Fin 24) (y : Y) :
      observation psi (6+d) lift r (rho y) = observation phi (6+d) H r y := by
    unfold observation
    rw [← fiberPath_project phi psi rho hproject]
    exact hlift _ _ (base_enters_core_for_later r d)
  have hshift : (∀ r x y, rho x = rho y → observation phi (6+d) H r x =
      observation phi (6+d) H (r+12) y) ↔
      (∀ r w, observation psi (6+d) lift r w = observation psi (6+d) lift (r+12) w) := by
    constructor
    · intro h r w
      obtain ⟨x, rfl⟩ := hrho w
      rw [hobs, hobs]
      exact h r x x rfl
    · intro h r x y hxy
      rw [← hobs, ← hobs, ← hxy]
      exact h r (rho x)
  have hclasses : collapseNonzero lift ↔ constantBetweenSigns rho H := by
    constructor
    · intro h r s x y flag hr hr0 hs hs0 hxy
      rw [← hlift r x hr, ← hlift s y hs, hxy]
      exact h r s (rho x) flag hr hr0 hs hs0
    · intro h r s w flag hr hr0 hs hs0
      obtain ⟨x, hx⟩ := hrho w
      obtain ⟨y, hy⟩ := hrho (twist flag w)
      rw [← hx, show twist flag (rho x) = rho y from (congrArg (twist flag) hx).trans hy.symm,
        hlift r x hr, hlift s y hs]
      exact h r s x y flag hr hr0 hs hs0 (hy.trans (congrArg (twist flag) hx).symm)
  exact hshift.trans ((half_observation_later psi hodd hhalf hpsi lift d).trans hclasses)

end A395522Fibers

namespace A395522Fibers

theorem rank_orbit_odd (z : ℕ → ℕ)
    (hzmono : ∀ ⦃a b⦄, a ∣ b → z a ∣ z b)
    (hz2 : z^[4] 2 = 12) (hz12 : z 12 = 12)
    {k B h : ℕ} (hB : Odd B) (hBfix : z B = B) (hBhit : z^[h] k = B) :
    ∀ j, Odd (z^[j] k) := by
  have hmono : ∀ j, ∀ ⦃a b⦄, a ∣ b → z^[j] a ∣ z^[j] b := by
    intro j
    induction j with
    | zero => exact fun _ _ hab ↦ hab
    | succ j ih =>
        intro a b hab
        rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
        exact hzmono (ih hab)
  have fixed_iterate (a : ℕ) (ha : z a = a) (j : ℕ) : z^[j] a = a := by
    induction j with
    | zero => rfl
    | succ j ih => rw [Function.iterate_succ_apply', ih, ha]
  intro j
  apply Nat.not_even_iff_odd.mp
  intro he
  have hd : 12 ∣ z^[4] (z^[j] k) := hz2 ▸ hmono 4 he.two_dvd
  have he' : 12 ∣ z^[h] (z^[4] (z^[j] k)) := by
    have hh := hmono h hd
    rwa [fixed_iterate 12 hz12 h] at hh
  have het : z^[h] (z^[4] (z^[j] k)) = B := by
    rw [← Function.iterate_add_apply, ← Function.iterate_add_apply,
      show h+4+j=4+j+h by omega, Function.iterate_add_apply, hBhit, fixed_iterate B hBfix]
  exact hB.not_two_dvd_nat ((by decide : 2 ∣ 12).trans (het ▸ he'))

theorem iterate_modEq_odd_rank (z : ℕ → ℕ)
    (hz : ∀ q, 0 < q → ∀ n, q ∣ Nat.fib n ↔ z q ∣ n)
    (m q x y : ℕ) (hq : ∀ j, 0 < z^[j] q ∧ Odd (z^[j] q))
    (hxy : ∀ j, Nat.fib^[j] x ≡ Nat.fib^[j] y [MOD 4]) :
    Nat.fib^[m] x ≡ Nat.fib^[m] y [MOD q] ↔ x ≡ y [MOD z^[m] q] := by
  induction m generalizing q with
  | zero => rfl
  | succ m ih =>
      have hq0 : 0 < q ∧ Odd q := hq 0
      have hq1 : 0 < z q ∧ Odd (z q) := hq 1
      have hq' : ∀ j, 0 < z^[j] (z q) ∧ Odd (z^[j] (z q)) := by
        intro j
        simpa only [Function.iterate_succ_apply] using hq (j+1)
      rw [Function.iterate_succ_apply' Nat.fib, Function.iterate_succ_apply' Nat.fib,
        Function.iterate_succ_apply z]
      exact (fib_modEq_odd_rank z hz q hq0.1 hq0.2 hq1.2 (hxy m)).trans (ih (z q) hq')

theorem five_path {Y : Type*} (phi : Fin 4 → Y → Y) (rho : Y → ZMod 5)
    (hphi : ∀ a y, rho (phi a y) = (multiplier5 a : ZMod 5) * rho y)
    (r : Fin 24) (d : ℕ) (y : Y) :
    rho (fiberPath phi r y d) = (product5 r d : ZMod 5) * rho y := by
  have hcast (n : ℕ) : ((n%5 : ℕ) : ZMod 5) = n :=
    (ZMod.natCast_eq_natCast_iff _ _ _).mpr (Nat.mod_modEq _ _)
  induction d with
  | zero => simp [fiberPath, product5]
  | succ d ih =>
      change rho (phi (baseClass (basePath r d)) (fiberPath phi r y d)) =
        ((multiplier5 (baseClass (basePath r d)) * product5 r d % 5 : ℕ) : ZMod 5) * rho y
      rw [hphi, ih, hcast, Nat.cast_mul, mul_assoc]

theorem separate_shift_five {Y α : Type*} (phi : Fin 4 → Y → Y) (rho : Y → ZMod 5)
    (hphi : ∀ a y, rho (phi a y) = (multiplier5 a : ZMod 5) * rho y)
    (H : Fin 24 → Y → α)
    (hsep : ∀ r s x y, baseCore r → r ≠ 0 → baseCore s → s ≠ 0 → H r x = H s y → rho x = rho y)
    (d : ℕ) (s : Fin 24) (hs : s ≠ 0) : ∃ r : Fin 24, ∀ x y, rho x = 1 → rho y = 1 →
      H (basePath r (6+d)) (fiberPath phi r x (6+d)) ≠
      H (basePath (r+s) (6+d)) (fiberPath phi (r+s) y (6+d)) := by
  obtain ⟨r, hr, hrs, hmul⟩ := base_shift_detected s hs
  refine ⟨r, ?_⟩
  intro x y hx hy he
  have nonzero (a : Fin 24) (ha : basePath a 6 ≠ 0) : basePath a (6+d) ≠ 0 :=
    fun he ↦ ha ((base_six_zero a).mpr ((base_later_zero a d).mp he))
  have hm := hsep _ _ _ _ (base_enters_core_for_later r d) (nonzero r hr)
    (base_enters_core_for_later (r+s) d) (nonzero (r+s) hrs) he
  rw [five_path phi rho hphi, five_path phi rho hphi, hx, hy, mul_one, mul_one,
    product5_later r hr, product5_later (r+s) hrs] at hm
  apply hmul
  have hn := (ZMod.natCast_eq_natCast_iff _ _ _).mp hm
  change product5 r 6 % 5 = product5 (r+s) 6 % 5 at hn
  rwa [Nat.mod_eq_of_lt (product5_lt r 6), Nat.mod_eq_of_lt (product5_lt (r+s) 6)] at hn

end A395522Fibers

open FibPeriod

namespace A395522Fibers

theorem rank_spec_iff (q : ℕ) (hq : 0 < q) (n : ℕ) :
    q ∣ Nat.fib n ↔ rank q ∣ n := ((rank_spec hq).2 n)

theorem five_pow_mod_four (e : ℕ) : (5^e : ℕ) % 4 = 1 := by
  induction e with
  | zero => decide
  | succ e ih => rw [pow_succ, Nat.mul_mod, ih]

theorem phi5_injective (e : ℕ) (a : Fin 4) : Function.Injective (phi (5^e) a) := by
  let : NeZero (5^e) := ⟨by positivity⟩
  exact phi_injective rank rank_spec_iff _ (five_pow_mod_four e) (rank_five_power e) a

theorem phi5_surjective (e : ℕ) (a : Fin 4) : Function.Surjective (phi (5^e) a) := by
  let : NeZero (5^e) := ⟨by positivity⟩
  exact phi_surjective rank rank_spec_iff _ (five_pow_mod_four e) (rank_five_power e) a

theorem phi5_half (e : ℕ) (a : Fin 4) (y : ZMod (5^e)) :
    phi (5^e) (a+2) y = -phi (5^e) a y := by
  let : NeZero (5^e) := ⟨by positivity⟩
  exact phi_half rank rank_spec_iff _ (five_pow_mod_four e) (rank_five_power e) a y

theorem phi5_odd (e : ℕ) (a : Fin 4) (y : ZMod (5^e)) :
    phi (5^e) a (-y) = -phi (5^e) a y := by
  let : NeZero (5^e) := ⟨by positivity⟩
  exact phi_odd rank rank_spec_iff _ (five_pow_mod_four e) (rank_five_power e) a y

theorem restrict5_phi {j e : ℕ} (h : j ≤ e) (a : Fin 4) (y : ZMod (5^e)) :
    restrict5 h (phi (5^e) a y) = phi (5^j) a (restrict5 h y) := by
  let : NeZero (5^e) := ⟨by positivity⟩
  let : NeZero (5^j) := ⟨by positivity⟩
  let r := representative (5^e) a y
  have hr : (r : ZMod (5^j)) = restrict5 h y := by
    rw [← map_natCast (restrict5 h), show (r : ZMod (5^e)) = y from rep_cast _ _ _]
  rw [phi_eval rank rank_spec_iff _ (five_pow_mod_four j) (rank_five_power j)
    _ _ r (rep_mod_four _ (five_pow_mod_four e) a y) hr]
  change restrict5 h (Nat.fib r : ZMod (5^e)) = (Nat.fib r : ZMod (5^j))
  exact map_natCast _ _

theorem restrict5_phi_multiplier {e : ℕ} (h : 1 ≤ e) (a : Fin 4) (y : ZMod (5^e)) :
    restrict5 h (phi (5^e) a y) = (multiplier5 a : ZMod 5) * restrict5 h y := by
  rw [restrict5_phi h]
  let r := representative 5 a (restrict5 h y)
  change fibC 5 r = (multiplier5 a : ZMod 5) * restrict5 h y
  rw [five_multiplier]
  have hc : (⟨r%4, Nat.mod_lt _ (by decide)⟩ : Fin 4) = a :=
    Fin.ext (rep_mod_four 5 (by decide) a (restrict5 h y))
  rw [hc, show (r : ZMod 5) = restrict5 h y from rep_cast _ _ _]

theorem baseClass_state24 (e n : ℕ) : (baseClass (state24 e n).1).val = n%4 := by
  change n%24%4 = n%4
  omega

theorem state24_fib (e n : ℕ) : state24 e (Nat.fib n) =
    (baseStep (state24 e n).1, phi (5^e) (baseClass (state24 e n).1) (state24 e n).2) := by
  let : NeZero (5^e) := ⟨by positivity⟩
  apply Prod.ext
  · apply Fin.ext
    change Nat.fib n % 24 = Nat.fib (n%24) %24
    exact fib_modEq_of_matrix matrix_time_24 (Nat.mod_modEq n 24).symm
  · change fibC (5^e) n = phi (5^e) (baseClass (state24 e n).1) (n : ZMod (5^e))
    exact (phi_eval rank rank_spec_iff _ (five_pow_mod_four e) (rank_five_power e) _ _ _
      (baseClass_state24 e n).symm rfl).symm

theorem state24_fib_iterate (e d n : ℕ) : state24 e (Nat.fib^[d] n) =
    (basePath (state24 e n).1 d, fiberPath (phi (5^e)) (state24 e n).1 (state24 e n).2 d) := by
  induction d with
  | zero => rfl
  | succ d ih =>
      rw [Function.iterate_succ_apply', state24_fib, ih]
      rfl

noncomputable def stateRepresentative (e : ℕ) (r : Fin 24) (y : ZMod (5^e)) : ℕ :=
  Classical.choose (state24_surjective e (r, y))

theorem state_stateRepresentative (e : ℕ) (r : Fin 24) (y : ZMod (5^e)) :
    state24 e (stateRepresentative e r y) = (r, y) :=
  Classical.choose_spec (state24_surjective e (r,y))

noncomputable def coreOutput (k e h : ℕ) (r : Fin 24) (y : ZMod (5^e)) : ℕ :=
  Nat.fib^[h] (stateRepresentative e r y) % k

theorem coreOutput_state {k e h : ℕ} (hc : FibComp k (coreModulus e) h) (x : ℕ) :
    coreOutput k e h (state24 e x).1 (state24 e x).2 = Nat.fib^[h] x % k := by
  apply hc
  apply (state24_eq_iff e _ _).mp
  exact state_stateRepresentative e (state24 e x).1 (state24 e x).2

theorem observe_fib {k e h : ℕ} (hc : FibComp k (coreModulus e) h) (d x : ℕ) :
    observation (phi (5^e)) d (coreOutput k e h) (state24 e x).1 (state24 e x).2 =
    Nat.fib^[h+d] x % k := by
  unfold observation
  rw [Function.iterate_add_apply, ← coreOutput_state hc (Nat.fib^[d] x), state24_fib_iterate]

end A395522Fibers

open FibPeriod

namespace A395522Fibers

theorem period_state_iff {k e h : ℕ} (hc : FibComp k (coreModulus e) h) (d t : ℕ)
    (R : (Fin 24 × ZMod (5^e)) → (Fin 24 × ZMod (5^e)) → Prop)
    (hR : ∀ x y, x ≡ y [MOD t] ↔ R (state24 e x) (state24 e y)) :
    Function.Periodic (fun x => Nat.fib^[h+d] x % k) t ↔ ∀ a b, R a b →
      observation (phi (5^e)) d (coreOutput k e h) a.1 a.2 =
        observation (phi (5^e)) d (coreOutput k e h) b.1 b.2 := by
  rw [periodic_mod_iff]
  constructor
  · intro hl a b hab
    obtain ⟨x, hx⟩ := state24_surjective e a
    obtain ⟨y, hy⟩ := state24_surjective e b
    have hxy : x ≡ y [MOD t] := (hR x y).mpr (by rw [hx, hy]; exact hab)
    have he := hl x y hxy
    rw [← observe_fib hc d x, ← observe_fib hc d y, hx, hy] at he
    exact he
  · intro hh x y hxy
    rw [← observe_fib hc d x, ← observe_fib hc d y]
    exact hh _ _ ((hR x y).mp hxy)

theorem full_period_iff {k e h j : ℕ} (hc : FibComp k (coreModulus e) h) (hj : j ≤ e) (d : ℕ) :
    Function.Periodic (fun x => Nat.fib^[h+(6+d)] x % k) (24*5^j) ↔
      constantInBase (restrict5 hj) (coreOutput k e h) := by
  let H := coreOutput k e h
  let R (a b : Fin 24 × ZMod (5^e)) := a.1 = b.1 ∧ restrict5 hj a.2 = restrict5 hj b.2
  refine (period_state_iff hc (6+d) _ R (state24_mod_24_5 hj)).trans ?_
  have hf := full_observation_later (phi (5^e)) (phi (5^j)) (restrict5 hj)
    (restrict5_phi hj) (phi5_surjective e) (phi5_injective j) H d
  refine ⟨?_, ?_⟩
  · intro h
    apply hf.mp
    intro r x y hxy
    exact h (r,x) (r,y) ⟨rfl,hxy⟩
  · intro h a b hab
    rcases a with ⟨r,x⟩
    rcases b with ⟨s,y⟩
    change r=s ∧ restrict5 hj x=restrict5 hj y at hab
    obtain ⟨rfl,hxy⟩ := hab
    exact hf.mpr h _ _ _ hxy

theorem half_period_iff {k e h j : ℕ} (hc : FibComp k (coreModulus e) h) (hj : j ≤ e) (d : ℕ) :
    Function.Periodic (fun x => Nat.fib^[h+(6+d)] x % k) (12*5^j) ↔
      constantInBase (restrict5 hj) (coreOutput k e h) ∧
      constantBetweenSigns (restrict5 hj) (coreOutput k e h) := by
  let H := coreOutput k e h
  let R (a b : Fin 24 × ZMod (5^e)) :=
    (b.1 = a.1 ∨ b.1 = a.1+12) ∧ restrict5 hj a.2 = restrict5 hj b.2
  have hR : ∀ x y, x ≡ y [MOD (12*5^j)] ↔ R (state24 e x) (state24 e y) := by
    intro x y
    rw [state24_mod_12_5 hj, fin24_half_iff]
  refine (period_state_iff hc (6+d) _ R hR).trans ?_
  have hf := full_observation_later (phi (5^e)) (phi (5^j)) (restrict5 hj)
    (restrict5_phi hj) (phi5_surjective e) (phi5_injective j) H d
  have hh := half_observation_projected (phi (5^e)) (phi (5^j)) (restrict5 hj)
    (restrict5_phi hj) (phi5_surjective j) (restrict5_surjective hj) (phi5_odd j) (phi5_half j) H d
  constructor
  · intro h
    have hfull : constantInBase (restrict5 hj) H := hf.mp (fun r x y he => h (r,x) (r,y) ⟨Or.inl rfl,he⟩)
    exact ⟨hfull, (hh hfull).mp (fun r x y he => h (r,x) (r+12,y) ⟨Or.inr rfl,he⟩)⟩
  · rintro ⟨hc1,hc2⟩ ⟨r,x⟩ ⟨s,y⟩ hab
    change (s=r ∨ s=r+12) ∧ restrict5 hj x=restrict5 hj y at hab
    obtain ⟨hs,hxy⟩ := hab
    rcases hs with rfl | rfl
    · exact hf.mpr hc1 _ _ _ hxy
    · exact (hh hc1).mpr hc2 _ _ _ hxy

theorem mixed_period_stable {k e h b t : ℕ} (hc : FibComp k (coreModulus e) h)
    (hdvd : t ∣ coreModulus e) (hb : 12*5^b ∣ t) (d : ℕ) :
    Function.Periodic (fun x => Nat.fib^[h+(6+d)] x % k) t ↔
      Function.Periodic (fun x => Nat.fib^[h+6] x % k) t := by
  obtain ⟨j, _, hj, ht | ht⟩ := mixed_period_shape hdvd hb
  · rw [ht, half_period_iff hc hj d]
    simpa only [Nat.add_zero] using (half_period_iff hc hj 0).symm
  · rw [ht, full_period_iff hc hj d]
    simpa only [Nat.add_zero] using (full_period_iff hc hj 0).symm

end A395522Fibers

namespace FibPeriod

open A395522Fibers

theorem rank_dvd_mono_all : ∀ ⦃a b : ℕ⦄, a ∣ b → rank a ∣ rank b := by
  intro a b hab
  by_cases hb : b = 0
  · subst b
    simp [rank]
  · have hbpos := Nat.pos_of_ne_zero hb
    have hapos := Nat.pos_of_dvd_of_pos hab hbpos
    exact rank_dvd_of_dvd hapos hbpos hab

theorem restrict_fiberPath {e b : ℕ} (hbe : b ≤ e)
    (phi : Fin 4 → ZMod (5 ^ e) → ZMod (5 ^ e)) (psi : Fin 4 → ZMod (5 ^ b) → ZMod (5 ^ b))
    (hmap : ∀ a y, restrict5 hbe (phi a y) = psi a (restrict5 hbe y))
    (r : Fin 24) (x y : ZMod (5 ^ e)) (hxy : restrict5 hbe x = restrict5 hbe y) (n : ℕ) :
    restrict5 hbe (fiberPath phi r x n) = restrict5 hbe (fiberPath phi r y n) := by
  induction n with
  | zero => exact hxy
  | succ n ih =>
    change restrict5 hbe (phi _ (fiberPath phi r x n)) =
      restrict5 hbe (phi _ (fiberPath phi r y n))
    rw [hmap, hmap, ih]

theorem fst_state_add (e x t : ℕ) :
    (state24 e (x + t)).1 = (state24 e x).1 + (state24 e t).1 := by
  apply Fin.ext
  exact Nat.add_mod x t 24

theorem pure_stabilizes {k d e b : ℕ} (hk : 0 < k) (hbe : b ≤ e)
    (hB : rank^[d] k = 5 ^ b) (hb : 0 < b) (hfix : rank (rank^[d] k) = rank^[d] k)
    (phi : Fin 4 → ZMod (5 ^ e) → ZMod (5 ^ e))
    (psi : Fin 4 → ZMod (5 ^ b) → ZMod (5 ^ b))
    (hmap : ∀ a y, restrict5 hbe (phi a y) = psi a (restrict5 hbe y))
    (hmap1 : ∀ a y, restrict5 (show 1 ≤ e by omega) (phi a y) =
      (multiplier5 a : ZMod 5) * restrict5 (show 1 ≤ e by omega) y)
    (hpath : ∀ (j x : ℕ), state24 e (Nat.fib^[j] x) =
      (basePath (state24 e x).1 j, fiberPath phi (state24 e x).1 (state24 e x).2 j))
    (H : Fin 24 → ZMod (5 ^ e) → ℕ)
    (hH : ∀ x, H (state24 e x).1 (state24 e x).2 = Nat.fib^[d] x % k) :
    Stabilizes k := by
  have htwo : rank^[4] 2 = 12 := by
    simp [Function.iterate_succ_apply', rank_two, rank_three, rank_four, rank_six]
  have hodd : ∀ j, Odd (rank^[j] k) :=
    rank_orbit_odd rank rank_dvd_mono_all htwo rank_twelve ((by decide : Odd (5 : ℕ)).pow)
      (hB ▸ hfix) hB
  have hrank : ∀ q, 0 < q → ∀ n, q ∣ Nat.fib n ↔ rank q ∣ n :=
    fun _ hq _ => (rank_dvd_iff hq).symm
  have H_core (r s : Fin 24) (y z : ZMod (5 ^ e)) (hr : baseCore r) (hs : baseCore s)
      (hzero : r = 0 ↔ s = 0) :
      H r y = H s z ↔ restrict5 hbe y = restrict5 hbe z := by
    obtain ⟨u, hu⟩ := state24_surjective e (r, y)
    obtain ⟨v, hv⟩ := state24_surjective e (s, z)
    have hcu (j : ℕ) : (state24 e (Nat.fib^[j] u)).1 = basePath r j := by
      rw [hpath, hu]
    have hcv (j : ℕ) : (state24 e (Nat.fib^[j] v)).1 = basePath s j := by
      rw [hpath, hv]
    have hm4 (j : ℕ) : Nat.fib^[j] u ≡ Nat.fib^[j] v [MOD 4] := by
      have hz : basePath r j = 0 ↔ basePath s j = 0 :=
        (basePath_zero_iff r j hr).trans (hzero.trans (basePath_zero_iff s j hs).symm)
      change Nat.fib^[j] u % 4 = Nat.fib^[j] v % 4
      rw [← baseClass_state24 e, ← baseClass_state24 e, hcu, hcv]
      rw [(base_core_step _ (basePath_core r j hr)).2.2.2,
        (base_core_step _ (basePath_core s j hs)).2.2.2]
      by_cases h0 : basePath r j = 0
      · simp [h0, hz.mp h0]
      · have h1 : basePath s j ≠ 0 := fun h => h0 (hz.mpr h)
        simp [h0, h1]
    have hcomp := iterate_modEq_odd_rank rank hrank d k u v
      (fun j => ⟨rank_iterate_pos hk j, hodd j⟩) hm4
    rw [hB] at hcomp
    have hHu : H r y = Nat.fib^[d] u % k := by simpa [hu] using hH u
    have hHv : H s z = Nat.fib^[d] v % k := by simpa [hv] using hH v
    rw [hHu, hHv]
    exact hcomp.trans (by simpa [hu, hv] using (state24_restrict_eq_iff hbe u v).symm)
  have hobs (j x : ℕ) :
      H (basePath (state24 e x).1 (6 + j)) (fiberPath phi (state24 e x).1 (state24 e x).2 (6 + j)) =
        Nat.fib^[d + (6 + j)] x % k := by
    rw [Function.iterate_add_apply]
    have hh := hH (Nat.fib^[6 + j] x)
    rw [hpath (6 + j) x] at hh
    exact hh
  let t := 24 * 5 ^ b
  have hp (j : ℕ) : Period k (d + (6 + j)) t := by
    intro x
    obtain ⟨hr, hz⟩ := (state24_mod_24_5 hbe (x + t) x).mp (Nat.add_mod_right x t)
    change Nat.fib^[d + (6 + j)] (x + t) % k = Nat.fib^[d + (6 + j)] x % k
    rw [← hobs j (x + t), ← hobs j x, hr]
    have hcore := base_enters_core_for_later (state24 e x).1 j
    exact (H_core _ _ _ _ hcore hcore Iff.rfl).mpr
      (restrict_fiberPath hbe phi psi hmap _ _ _ hz (6 + j))
  have hdvd (j s : ℕ) (hs : Period k (d + (6 + j)) s) : t ∣ s := by
    have hsB := rank_iterate_dvd_of_period hk hs
    rw [rank_later hfix (by omega), hB] at hsB
    have hs5 : 5 ∣ s := (show 5 ∣ 5 ^ b from dvd_pow_self _ (by omega)).trans hsB
    have hs24 : 24 ∣ s := by
      by_contra hs24
      let shift := (state24 e s).1
      have hshift : shift ≠ 0 := by
        intro h
        apply hs24
        exact Nat.dvd_iff_mod_eq_zero.mpr (congrArg Fin.val h)
      have hrho : ∀ a y, restrict5 (show 1 ≤ e by omega) (phi a y) =
          (multiplier5 a : ZMod 5) * restrict5 (show 1 ≤ e by omega) y := hmap1
      have hsep (r q : Fin 24) (y z : ZMod (5 ^ e))
          (hr : baseCore r) (hr0 : r ≠ 0) (hq : baseCore q) (hq0 : q ≠ 0)
          (hh : H r y = H q z) :
          restrict5 (show 1 ≤ e by omega) y = restrict5 (show 1 ≤ e by omega) z := by
        have he := (H_core _ _ _ _ hr hq (by simp [hr0, hq0])).mp hh
        obtain ⟨a, ha⟩ := state24_surjective e (r, y)
        obtain ⟨c, hc⟩ := state24_surjective e (q, z)
        have he' := (state24_restrict_eq_iff hbe a c).mp (by simpa [ha, hc] using he)
        have hfive : a ≡ c [MOD 5] := he'.of_dvd (dvd_pow_self _ (by omega))
        simpa [ha, hc] using
          (state24_restrict_eq_iff (show 1 ≤ e by omega) a c).mpr hfive
      obtain ⟨r, hr⟩ := separate_shift_five phi (restrict5 (show 1 ≤ e by omega))
        hrho H hsep j shift hshift
      obtain ⟨z, hz⟩ := restrict5_surjective (show 1 ≤ e by omega) (1 : ZMod 5)
      obtain ⟨x, hx⟩ := state24_surjective e (r, z)
      have hx1 : restrict5 (show 1 ≤ e by omega) (state24 e x).2 = 1 := by simpa [hx] using hz
      have hx2 : restrict5 (show 1 ≤ e by omega) (state24 e (x + s)).2 = 1 := by
        have hmod : x + s ≡ x [MOD 5] := by
          simpa using (Nat.ModEq.refl x).add (Nat.modEq_zero_iff_dvd.mpr hs5)
        exact ((state24_restrict_eq_iff (show 1 ≤ e by omega) (x + s) x).mpr hmod).trans hx1
      have hstep : (state24 e (x + s)).1 = r + shift := by rw [fst_state_add, hx]
      have hbad := hs x
      change Nat.fib^[d + (6 + j)] (x + s) % k = Nat.fib^[d + (6 + j)] x % k at hbad
      rw [← hobs j (x + s), ← hobs j x, hstep, hx] at hbad
      exact hr _ _ (by simpa [hx] using hx1) hx2 hbad.symm
    exact ((by decide : Nat.Coprime 24 5).pow_right b).mul_dvd_of_dvd_of_dvd hs24 hsB
  apply least_later_of_fixed_period (N := d + 6) (t := t) (by omega) (by dsimp [t]; positivity)
  · intro m hm
    obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hm
    simpa only [Nat.add_assoc] using hp j
  · intro m hm s _ hs
    obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hm
    exact hdvd j s (by simpa only [Nat.add_assoc] using hs)

end FibPeriod

namespace FibPeriod

open A395522Fibers

theorem mixed_stabilizes {k d e b : ℕ} (hk : 0 < k)
    (hcomp : FibComp k (coreModulus e) d) (hB : rank^[d] k = 12 * 5 ^ b)
    (hfix : rank (rank^[d] k) = rank^[d] k) : Stabilizes k := by
  apply least_later_of_candidate_stability (N := d + 6) (M := coreModulus e)
    (by omega) (by unfold coreModulus; positivity)
  · exact fun _ hm => period_core hcomp (by omega)
  · intro m hm t _ htM
    obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hm
    have hdiv {v : ℕ} (hv : d ≤ v) (hper : Period k v t) : 12 * 5 ^ b ∣ t := by
      have hd := rank_iterate_dvd_of_period hk hper
      rwa [rank_later hfix hv, hB] at hd
    constructor
    · intro hp
      have hb := hdiv (by omega) hp
      simpa only [Nat.add_assoc] using (mixed_period_stable hcomp htM hb j).mpr hp
    · intro hp
      have hb := hdiv (by omega) hp
      exact (mixed_period_stable hcomp htM hb j).mp (by simpa only [Nat.add_assoc] using hp)

theorem source_iter_eq (m x : ℕ) : OMA.S_oeis_a395522.iterFib m x = Nat.fib^[m] x := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [OMA.S_oeis_a395522.iterFib, Function.iterate_succ_apply', ih]

theorem source_period_iff (m k t : ℕ) :
    OMA.S_oeis_a395522.isPeriod m k t ↔ Period k m t := by
  change (∀ x : ℕ, OMA.S_oeis_a395522.iterFib m (x+t) % k = OMA.S_oeis_a395522.iterFib m x % k) ↔
    (∀ x : ℕ, Nat.fib^[m] (x+t) % k = Nat.fib^[m] x % k)
  simp only [source_iter_eq]

end FibPeriod

open FibPeriod A395522Fibers in
theorem OMA.solution : type_of% @OMA.S_oeis_a395522.main := by
  intro k hk
  have h : Stabilizes k := by
    apply stabilizes_of_rank_cases hk
    · intro d e b hbe hcomp hB hb hfix
      exact pure_stabilizes hk hbe hB hb hfix (phi (5 ^ e)) (phi (5 ^ b))
        (restrict5_phi hbe) (restrict5_phi_multiplier (by omega)) (state24_fib_iterate e)
        (coreOutput k e d) (coreOutput_state hcomp)
    · exact fun _ _ _ _ hcomp hB hfix => mixed_stabilizes hk hcomp hB hfix
  simpa only [Stabilizes, source_period_iff] using h
