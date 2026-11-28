import FormalConjectures.ErdosProblems.«470»
import Mathlib.Algebra.Field.GeomSum
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Data.Finset.Sort
import Mathlib.Data.List.Forall2
import Mathlib.Data.Nat.Factorization.Induction
import Mathlib.Data.Nat.GCD.BigOperators
import Mathlib.Data.Nat.Log
import Mathlib.Data.Set.Card
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.NumberTheory.FactorisationProperties
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace OddWeirdSubproblems

open Finset

abbrev Coordinates := List (ℕ × ℕ)

def powerSum (p : ℕ) : ℕ → ℕ
  | 0 => 1
  | e + 1 => powerSum p e + p ^ (e + 1)

theorem powerSum_eq_sum (p e : ℕ) : powerSum p e = ∑ i ∈ range (e + 1), p ^ i := by
  induction e with
  | zero => simp [powerSum]
  | succ e ih => rw [powerSum, sum_range_succ, ih]

def number (fs : Coordinates) : ℕ := (fs.map fun (p, e) => p ^ e).prod

def divisorSum (fs : Coordinates) : ℕ := (fs.map fun (p, e) => powerSum p e).prod

def index (p e : ℕ) : ℚ := (powerSum p e : ℚ) / (p : ℚ) ^ e

def limitingIndex (p : ℕ) : ℚ := (p : ℚ) / ((p : ℚ) - 1)

structure Slot where
  prime : ℕ
  exponent : ℕ
  fixed : Bool

def Slot.Fits (s : Slot) (x : ℕ × ℕ) : Prop :=
  x.1.Prime ∧ s.prime = x.1 ∧ s.exponent ≤ x.2 ∧ (s.fixed = true → s.exponent = x.2)

def Slot.upper (s : Slot) : ℚ :=
  if s.fixed then index s.prime s.exponent else limitingIndex s.prime

def Slot.minimum (s : Slot) : ℕ × ℕ := (s.prime, s.exponent)

def TailFits : ℕ → Coordinates → Prop
  | _, [] => True
  | p, (q, e) :: qs => p ≤ q ∧ 2 < q ∧ q.Prime ∧ Odd q ∧ 0 < e ∧ TailFits (q + 2) qs

def tailUpper : ℕ → ℕ → ℚ
  | _, 0 => 1
  | p, r + 1 => limitingIndex p * tailUpper (p + 2) r

theorem index_le_limitingIndex {p e : ℕ} (hp : 1 < p) :
    index p e ≤ limitingIndex p := by
  have hpq : (1 : ℚ) < p := by exact_mod_cast hp
  have hpow : (0 : ℚ) < (p : ℚ) ^ e := pow_pos (by linarith) _
  unfold index limitingIndex
  rw [powerSum_eq_sum]
  push_cast
  rw [div_le_div_iff₀ hpow (sub_pos.mpr hpq), geom_sum_mul, pow_succ]
  linarith

theorem limitingIndex_antitone {p q : ℕ} (hp : 1 < p) (hpq : p ≤ q) :
    limitingIndex q ≤ limitingIndex p := by
  have hp' : (1 : ℚ) < p := by exact_mod_cast hp
  have hpq' : (p : ℚ) ≤ q := by exact_mod_cast hpq
  unfold limitingIndex
  rw [div_le_div_iff₀ (sub_pos.mpr (hp'.trans_le hpq')) (sub_pos.mpr hp')]
  nlinarith

theorem slot_index_le {s : Slot} {x : ℕ × ℕ} (h : s.Fits x) :
    index x.1 x.2 ≤ s.upper := by
  obtain ⟨hp, hs, _, he⟩ := h
  cases hf : s.fixed
  · simpa [Slot.upper, hf, hs] using (index_le_limitingIndex (e := x.2) hp.one_lt)
  · simp [Slot.upper, hf, hs, he hf]

theorem index_nonneg (p e : ℕ) : 0 ≤ index p e := by unfold index; positivity

theorem limitingIndex_nonneg {p : ℕ} (hp : 1 < p) : 0 ≤ limitingIndex p := by
  have hp' : (1 : ℚ) < p := by exact_mod_cast hp
  exact div_nonneg (by positivity) (sub_nonneg.mpr hp'.le)

theorem coordinate_index_eq (xs : Coordinates) :
    (xs.map fun x => index x.1 x.2).prod = (divisorSum xs : ℚ) / (number xs : ℚ) := by
  induction xs with
  | nil => simp [divisorSum, number]
  | cons x xs ih =>
    rcases x with ⟨p, e⟩
    simp only [List.map_cons, List.prod_cons, ih]
    simp only [index, divisorSum, number, List.map_cons, List.prod_cons, Nat.cast_mul,
      Nat.cast_pow, div_mul_div_comm]

theorem coordinate_prod_nonneg (xs : Coordinates) :
    0 ≤ (xs.map fun x => index x.1 x.2).prod := by
  induction xs with
  | nil => norm_num
  | cons x xs ih => exact mul_nonneg (index_nonneg _ _) ih

theorem slot_prod_upper {ss : List Slot} {xs : Coordinates}
    (h : List.Forall₂ Slot.Fits ss xs) :
    (xs.map fun x => index x.1 x.2).prod ≤ (ss.map Slot.upper).prod := by
  induction h with
  | nil => simp
  | cons h₁ _ ih =>
    simp only [List.map_cons, List.prod_cons]
    refine mul_le_mul (slot_index_le h₁) ih ?_ ((index_nonneg _ _).trans (slot_index_le h₁))
    exact coordinate_prod_nonneg _

theorem tailUpper_nonneg {p : ℕ} (hp : 1 < p) (r : ℕ) : 0 ≤ tailUpper p r := by
  induction r generalizing p with
  | zero => simp [tailUpper]
  | succ r ih => exact mul_nonneg (limitingIndex_nonneg hp) (ih (by omega))

theorem tailUpper_antitone {p q : ℕ} (hp : 1 < p) (hpq : p ≤ q) (r : ℕ) :
    tailUpper q r ≤ tailUpper p r := by
  induction r generalizing p q with
  | zero => simp [tailUpper]
  | succ r ih =>
    exact mul_le_mul (limitingIndex_antitone hp hpq) (ih (by omega) (by omega))
      (tailUpper_nonneg (show 1 < q + 2 by omega) r) (limitingIndex_nonneg hp)

theorem tail_prod_upper {p : ℕ} {xs : Coordinates} (hp : 1 < p) (h : TailFits p xs) :
    (xs.map fun x => index x.1 x.2).prod ≤ tailUpper p xs.length := by
  induction xs generalizing p with
  | nil => simp [tailUpper]
  | cons x xs ih =>
    rcases x with ⟨q, e⟩
    obtain ⟨hpq, _, hq, _, _, ht⟩ := h
    simp only [List.map_cons, List.prod_cons, List.length_cons, tailUpper]
    exact mul_le_mul ((index_le_limitingIndex hq.one_lt).trans (limitingIndex_antitone hp hpq))
      ((ih (show 1 < q + 2 by omega) ht).trans
        (tailUpper_antitone (show 1 < p + 2 by omega) (by omega) xs.length))
      (coordinate_prod_nonneg xs) (limitingIndex_nonneg hp)

theorem tailFits_of_sorted {xs : Coordinates} {p : ℕ}
    (hp : 2 < p)
    (hlo : ∀ x ∈ xs, p ≤ x.1)
    (hlocal : ∀ x ∈ xs, x.1.Prime ∧ Odd x.1 ∧ 0 < x.2)
    (horder : xs.Pairwise (fun x y => x.1 < y.1)) : TailFits p xs := by
  induction xs generalizing p with
  | nil => trivial
  | cons x xs ih =>
    obtain ⟨q, e⟩ := x
    have hq := hlo (q, e) (by simp)
    obtain ⟨hprime, hodd, he⟩ := hlocal (q, e) (by simp)
    change p ≤ q at hq
    obtain ⟨horder, htail⟩ := List.pairwise_cons.mp horder
    refine ⟨hq, by omega, hprime, hodd, he, ih (by omega) ?_ ?_ htail⟩
    · intro z hz
      have hlt := horder z hz
      have hzodd := (hlocal z (List.mem_cons_of_mem _ hz)).2.1
      obtain ⟨a, ha⟩ := hodd
      obtain ⟨b, hb⟩ := hzodd
      change q < z.1 at hlt
      omega
    · intro z hz
      exact hlocal z (List.mem_cons_of_mem _ hz)

def PrimeCoordinates (xs : Coordinates) : Prop :=
  (∀ x ∈ xs, x.1.Prime) ∧ xs.Pairwise (fun x y => x.1 < y.1)

theorem number_cons (x : ℕ × ℕ) (xs : Coordinates) :
    number (x :: xs) = x.1 ^ x.2 * number xs := rfl

theorem number_append (xs ys : Coordinates) : number (xs ++ ys) = number xs * number ys := by
  simp [number, List.prod_append]

theorem divisorSum_append (xs ys : Coordinates) :
    divisorSum (xs ++ ys) = divisorSum xs * divisorSum ys := by
  simp [divisorSum, List.prod_append]

theorem number_pos {xs : Coordinates} (h : ∀ x ∈ xs, Nat.Prime x.1) : 0 < number xs := by
  induction xs with
  | nil => decide
  | cons x xs ih =>
    rw [number_cons]
    exact Nat.mul_pos (pow_pos (h x (by simp)).pos _)
      (ih (fun y hy => h y (List.mem_cons_of_mem _ hy)))

theorem divisorSum_eq {xs : Coordinates} (hs : PrimeCoordinates xs) :
    divisorSum xs = ∑ d ∈ (number xs).divisors, d := by
  induction xs with
  | nil => decide
  | cons x xs ih =>
    obtain ⟨hp, hlt⟩ := hs
    obtain ⟨horder, htail⟩ := List.pairwise_cons.mp hlt
    have hp' : ∀ y ∈ xs, Nat.Prime y.1 := fun y hy => hp y (List.mem_cons_of_mem _ hy)
    have hcop : (x.1 ^ x.2).Coprime (number xs) := by
      apply Nat.coprime_list_prod_right_iff.mpr
      intro m hm
      obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hm
      exact Nat.coprime_pow_primes _ _ (hp x (by simp)) (hp' y hy) (horder y hy).ne
    rw [number_cons, hcop.sum_divisors_mul, ← ih ⟨hp', htail⟩,
      ← ArithmeticFunction.sigma_one_apply, ArithmeticFunction.sigma_one_apply_prime_pow (hp x (by simp))]
    change powerSum x.1 x.2 * divisorSum xs = _
    rw [powerSum_eq_sum]

theorem deficient_iff_divisorSum_lt {xs : Coordinates} (hs : PrimeCoordinates xs) :
    (number xs).Deficient ↔ divisorSum xs < 2 * number xs := by
  rw [divisorSum_eq hs, Nat.sum_divisors_eq_sum_properDivisors_add_self]
  unfold Nat.Deficient
  omega

theorem slot_fits_split {s : Slot} {x : ℕ × ℕ} (h : s.Fits x) (hf : s.fixed = false) :
    ({s with fixed := true} : Slot).Fits x ∨ ({s with exponent := s.exponent + 1} : Slot).Fits x := by
  obtain ⟨hp, hq, he, _⟩ := h
  by_cases eq : s.exponent = x.2
  · exact Or.inl ⟨hp, hq, he, fun _ => eq⟩
  · exact Or.inr ⟨hp, hq, by dsimp; omega, by simp [hf]⟩

theorem minimum_dvd {ss : List Slot} {xs : Coordinates} (h : List.Forall₂ Slot.Fits ss xs) :
    number (ss.map Slot.minimum) ∣ number xs := by
  induction h with
  | nil => exact dvd_rfl
  | @cons s x ss xs hfit _ ih =>
    simp only [List.map_cons, number_cons, Slot.minimum, hfit.2.1]
    exact Nat.mul_dvd_mul (pow_dvd_pow _ hfit.2.2.1) ih

theorem exists_fit_of_mem {s : Slot} {ss : List Slot} {xs : Coordinates}
    (h : List.Forall₂ Slot.Fits ss xs) (hm : s ∈ ss) : ∃ x ∈ xs, s.Fits x := by
  induction h with
  | nil => simp at hm
  | @cons t x ts xs hfit ht ih =>
    rcases List.mem_cons.mp hm with rfl | hm
    · exact ⟨x, by simp, hfit⟩
    · obtain ⟨y, hy, hsy⟩ := ih hm
      exact ⟨y, List.mem_cons_of_mem _ hy, hsy⟩

theorem minimum_valid {ss : List Slot} {xs : Coordinates}
    (h : List.Forall₂ Slot.Fits ss xs) (hxs : PrimeCoordinates xs) :
    PrimeCoordinates (ss.map Slot.minimum) := by
  induction h with
  | nil => simp [PrimeCoordinates]
  | @cons s x ss xs hfit ht ih =>
    obtain ⟨hp, hpw⟩ := hxs
    obtain ⟨horder, htail⟩ := List.pairwise_cons.mp hpw
    obtain ⟨htp, htw⟩ := ih ⟨fun y hy => hp y (List.mem_cons_of_mem _ hy), htail⟩
    constructor
    · simp only [List.map_cons, List.mem_cons, forall_eq_or_imp]
      exact ⟨by simpa only [Slot.minimum, hfit.2.1] using hfit.1, htp⟩
    · simp only [List.map_cons, List.pairwise_cons]
      refine ⟨?_, htw⟩
      intro y hy
      obtain ⟨t, htmem, rfl⟩ := List.mem_map.mp hy
      obtain ⟨z, hzmem, hzfit⟩ := exists_fit_of_mem ht htmem
      simpa only [Slot.minimum, hfit.2.1, hzfit.2.1] using horder z hzmem

end OddWeirdSubproblems

namespace OddWeirdSubproblems

open Finset

structure Box where
  slots : List Slot
  next : ℕ
  remaining : ℕ

def Box.Matches (b : Box) (xs ys : Coordinates) : Prop :=
  List.Forall₂ Slot.Fits b.slots xs ∧ TailFits b.next ys ∧ ys.length = b.remaining

def Box.Closed (b : Box) : Prop :=
  ∀ xs ys, b.Matches xs ys → PrimeCoordinates (xs ++ ys) →
    (number (xs ++ ys)).Weird →
    (∀ d ∈ (number (xs ++ ys)).properDivisors, d.Deficient) → False

def Box.minimum (b : Box) : Coordinates := b.slots.map Slot.minimum

def Box.upper (b : Box) : ℚ := (b.slots.map Slot.upper).prod * tailUpper b.next b.remaining

def Slot.upperNum (s : Slot) : ℕ :=
  if s.fixed then powerSum s.prime s.exponent else s.prime

def Slot.upperDen (s : Slot) : ℕ :=
  if s.fixed then s.prime ^ s.exponent else s.prime - 1

def tailNum : ℕ → ℕ → ℕ
  | _, 0 => 1
  | p, r + 1 => p * tailNum (p + 2) r

def tailDen : ℕ → ℕ → ℕ
  | _, 0 => 1
  | p, r + 1 => (p - 1) * tailDen (p + 2) r

def Box.upperNum (b : Box) : ℕ := (b.slots.map Slot.upperNum).prod * tailNum b.next b.remaining

def Box.upperDen (b : Box) : ℕ := (b.slots.map Slot.upperDen).prod * tailDen b.next b.remaining

theorem Slot.upper_eq (s : Slot) (hp : 1 < s.prime) :
    s.upper = (s.upperNum : ℚ) / (s.upperDen : ℚ) := by
  cases hs : s.fixed
  · have h : 1 ≤ s.prime := by omega
    simp [Slot.upper, Slot.upperNum, Slot.upperDen, hs, limitingIndex, Nat.cast_sub h]
  · simp [Slot.upper, Slot.upperNum, Slot.upperDen, hs, index]

theorem slot_upper_eq {ss : List Slot} (h : ∀ s ∈ ss, 1 < s.prime) :
    (ss.map Slot.upper).prod = ((ss.map Slot.upperNum).prod : ℚ) /
      ((ss.map Slot.upperDen).prod : ℚ) := by
  induction ss with
  | nil => simp
  | cons s ss ih =>
    simp only [List.map_cons, List.prod_cons, Nat.cast_mul]
    rw [s.upper_eq (h s (by simp)), ih (fun t ht => h t (by simp [ht])), div_mul_div_comm]

theorem tailUpper_eq {p : ℕ} (hp : 1 < p) (r : ℕ) :
    tailUpper p r = (tailNum p r : ℚ) / (tailDen p r : ℚ) := by
  induction r generalizing p with
  | zero => simp [tailUpper, tailNum, tailDen]
  | succ r ih =>
    simp only [tailUpper, tailNum, tailDen, Nat.cast_mul, limitingIndex]
    rw [ih (by omega), div_mul_div_comm, Nat.cast_sub (show 1 ≤ p by omega)]
    simp

theorem Slot.upperDen_pos (s : Slot) (hp : 1 < s.prime) : 0 < s.upperDen := by
  unfold Slot.upperDen
  split
  · exact pow_pos (by omega) _
  · omega

theorem slot_den_pos {ss : List Slot} (h : ∀ s ∈ ss, 1 < s.prime) :
    0 < (ss.map Slot.upperDen).prod := by
  induction ss with
  | nil => decide
  | cons s ss ih =>
    exact Nat.mul_pos (s.upperDen_pos (h s (by simp))) (ih (fun t ht => h t (by simp [ht])))

theorem tail_den_pos {p : ℕ} (hp : 1 < p) (r : ℕ) : 0 < tailDen p r := by
  induction r generalizing p with
  | zero => simp [tailDen]
  | succ r ih => exact Nat.mul_pos (by omega) (ih (by omega))

theorem close_of_upper_le_two {b : Box} (hnext : 1 < b.next) (hbound : b.upper ≤ 2) :
    b.Closed := by
  intro xs ys ⟨hxs, hys, hylen⟩ hvalid hw _
  have hprod :
      ((xs ++ ys).map fun x => index x.1 x.2).prod ≤ b.upper := by
    rw [List.map_append, List.prod_append, Box.upper, ← hylen]
    have h := slot_prod_upper hxs
    exact mul_le_mul h (tail_prod_upper hnext hys) (coordinate_prod_nonneg _)
      ((coordinate_prod_nonneg _).trans h)
  rw [coordinate_index_eq, divisorSum_eq hvalid, ← Nat.abundancyIndex] at hprod
  exact (Nat.abundant_iff_two_lt_abundancyIndex.mp hw.1).not_ge (hprod.trans hbound)

theorem close_of_upperNum_le {b : Box} (hnext : 1 < b.next)
    (hbound : b.upperNum ≤ 2 * b.upperDen) : b.Closed := by
  intro xs ys hmatch hcoord hw hprim
  have hslot (s : Slot) (hs : s ∈ b.slots) : 1 < s.prime := by
    obtain ⟨x, _, hfit⟩ := exists_fit_of_mem hmatch.1 hs
    rw [hfit.2.1]
    exact hfit.1.one_lt
  have hden : 0 < b.upperDen := Nat.mul_pos (slot_den_pos hslot) (tail_den_pos hnext _)
  have h : b.upper ≤ 2 := by
    rw [Box.upper, slot_upper_eq hslot, tailUpper_eq hnext, div_mul_div_comm, ← Nat.cast_mul, ← Nat.cast_mul]
    change (b.upperNum : ℚ) / (b.upperDen : ℚ) ≤ 2
    rw [div_le_iff₀ (by exact_mod_cast hden)]
    exact_mod_cast hbound
  exact close_of_upper_le_two hnext h xs ys hmatch hcoord hw hprim

theorem primeCoordinates_left {xs ys : Coordinates} (h : PrimeCoordinates (xs ++ ys)) :
    PrimeCoordinates xs :=
  ⟨fun x hx => h.1 x (List.mem_append_left _ hx), (List.pairwise_append.mp h.2).1⟩

theorem close_at_nondeficient_minimum {b : Box}
    (hnondef : 2 * number b.minimum ≤ divisorSum b.minimum)
    (hpoint : ¬ (number b.minimum).Abundant ∨ (number b.minimum).Pseudoperfect ∨
      ∃ d ∈ (number b.minimum).properDivisors, ¬ d.Deficient) :
    b.Closed := by
  intro xs ys ⟨hfit, _, _⟩ hvalid hw hprimitive
  have hdvd : number b.minimum ∣ number (xs ++ ys) := by
    rw [number_append]
    exact dvd_mul_of_dvd_left (minimum_dvd hfit) _
  have hmin : PrimeCoordinates b.minimum := minimum_valid hfit (primeCoordinates_left hvalid)
  have hnd : ¬ (number b.minimum).Deficient :=
    fun h => (deficient_iff_divisorSum_lt hmin).mp h |>.not_ge hnondef
  obtain hlt | heq := lt_or_eq_of_le (Nat.le_of_dvd hw.1.pos hdvd)
  · exact hnd (hprimitive _ (Nat.mem_properDivisors.mpr ⟨hdvd, hlt⟩))
  · rw [heq] at hpoint
    rcases hpoint with h | h | ⟨d, hd, h⟩
    · exact h hw.1
    · exact hw.2 h
    · exact h (hprimitive d hd)

def tightlySorted : List ℕ → Bool
  | [] => true
  | [_] => true
  | a :: b :: as => decide (a < b) && tightlySorted (b :: as)

theorem tightlySorted_pairwise {ds : List ℕ} (h : tightlySorted ds = true) :
    ds.Pairwise (· < ·) := by
  induction ds with
  | nil => exact .nil
  | cons a ds ih =>
    cases ds with
    | nil => exact .cons (by simp) .nil
    | cons b ds =>
      simp only [tightlySorted, Bool.and_eq_true, decide_eq_true_eq] at h
      have hpw := ih h.2
      refine .cons ?_ hpw
      intro c hc
      rcases List.mem_cons.mp hc with rfl | hc
      · exact h.1
      · exact h.1.trans ((List.pairwise_cons.mp hpw).1 c hc)

theorem tightlySorted_nodup {ds : List ℕ} (h : tightlySorted ds = true) : ds.Nodup :=
  (tightlySorted_pairwise h).imp Nat.ne_of_lt

theorem pseudoperfect_of_excess_list {n : ℕ} {ds : List ℕ}
    (hn : 0 < n) (hnodup : ds.Nodup) (hdivs : ∀ d ∈ ds, d ∣ n ∧ d < n)
    (hsum : ∑ d ∈ n.divisors, d = 2 * n + ds.sum) : n.Pseudoperfect := by
  have hds : ∑ d ∈ ds.toFinset, d = ds.sum := by
    clear hsum hdivs
    induction ds with
    | nil => simp
    | cons d ds ih =>
      obtain ⟨hd, hnd⟩ := List.nodup_cons.mp hnodup
      have hd' : d ∉ ds.toFinset := by simpa using hd
      rw [List.toFinset_cons, sum_insert hd', List.sum_cons, ih hnd]
  have hsub : ds.toFinset ⊆ n.properDivisors := by
    intro d hd
    exact Nat.mem_properDivisors.mpr (hdivs d (List.mem_toFinset.mp hd))
  refine ⟨hn, n.properDivisors \ ds.toFinset, sdiff_subset, ?_⟩
  have hdiff := sum_sdiff (f := fun d : ℕ => d) hsub
  rw [Nat.sum_divisors_eq_sum_properDivisors_add_self] at hsum
  omega

theorem close_minimum_eq_two {b : Box}
    (h : divisorSum b.minimum = 2 * number b.minimum) : b.Closed := by
  intro xs ys hmatch hvalid hw hproper
  have hv : PrimeCoordinates b.minimum := minimum_valid hmatch.1 (primeCoordinates_left hvalid)
  have hp : ¬ (number b.minimum).Abundant := by
    rw [Nat.abundant_iff_sum_divisors, ← divisorSum_eq hv, h]
    exact lt_irrefl _
  exact close_at_nondeficient_minimum h.ge (Or.inl hp) xs ys hmatch hvalid hw hproper

theorem close_minimum_witness {b : Box} {ds : List ℕ}
    (hnodup : ds.Nodup) (hdivs : ∀ d ∈ ds, d ∣ number b.minimum ∧ d < number b.minimum)
    (hsum : divisorSum b.minimum = 2 * number b.minimum + ds.sum) : b.Closed := by
  intro xs ys hmatch hvalid hw hproper
  have hv : PrimeCoordinates b.minimum := minimum_valid hmatch.1 (primeCoordinates_left hvalid)
  have hnondef : 2 * number b.minimum ≤ divisorSum b.minimum := by omega
  have h : (number b.minimum).Pseudoperfect := pseudoperfect_of_excess_list
    (number_pos hv.1) hnodup hdivs (divisorSum_eq hv ▸ hsum)
  exact close_at_nondeficient_minimum hnondef (Or.inr (Or.inl h)) xs ys hmatch hvalid hw hproper

theorem close_minimum_has_nondeficient_divisor {b : Box} {d : ℕ}
    (hnondef : 2 * number b.minimum ≤ divisorSum b.minimum)
    (hdvd : d ∣ number b.minimum) (hdlt : d < number b.minimum) (hd : ¬ d.Deficient) :
    b.Closed :=
  close_at_nondeficient_minimum hnondef (Or.inr (Or.inr
    ⟨d, Nat.mem_properDivisors.mpr ⟨hdvd, hdlt⟩, hd⟩))

theorem forall₂_slot_split {ss : List Slot} {xs : Coordinates} {i : ℕ} {s : Slot}
    (h : List.Forall₂ Slot.Fits ss xs) (hi : ss[i]? = some s) (hf : s.fixed = false) :
    List.Forall₂ Slot.Fits (ss.set i {s with fixed := true}) xs ∨
    List.Forall₂ Slot.Fits (ss.set i {s with exponent := s.exponent + 1}) xs := by
  induction h generalizing i with
  | nil => simp at hi
  | @cons t x ss xs hfit _ ih =>
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hi
      subst t
      rcases slot_fits_split hfit hf with h | h
      · exact Or.inl (.cons h (by assumption))
      · exact Or.inr (.cons h (by assumption))
    | succ i =>
      simp only [List.getElem?_cons_succ] at hi
      rcases ih hi with h | h
      · exact Or.inl (.cons hfit h)
      · exact Or.inr (.cons hfit h)

theorem close_split_slot {b : Box} {i : ℕ} {s : Slot}
    (hi : b.slots[i]? = some s) (hf : s.fixed = false)
    (h₁ : ({b with slots := b.slots.set i {s with fixed := true}} : Box).Closed)
    (h₂ : ({b with slots := b.slots.set i {s with exponent := s.exponent + 1}} : Box).Closed) :
    b.Closed := by
  intro xs ys ⟨hf₂, ht, hr⟩ hp hw hprim
  rcases forall₂_slot_split hf₂ hi hf with h | h
  · exact h₁ xs ys ⟨h, ht, hr⟩ hp hw hprim
  · exact h₂ xs ys ⟨h, ht, hr⟩ hp hw hprim

theorem close_split_next {ss : List Slot} {p r : ℕ} (hodd : Odd p)
    (hskip : (⟨ss, p + 2, r + 1⟩ : Box).Closed)
    (htake : p.Prime → (⟨ss ++ [⟨p, 1, false⟩], p + 2, r⟩ : Box).Closed) :
    (⟨ss, p, r + 1⟩ : Box).Closed := by
  intro xs ys ⟨hx, hy, hlen⟩ hcoord hw hprim
  cases ys with
  | nil => simp at hlen
  | cons y ys =>
    obtain ⟨q, e⟩ := y
    obtain ⟨hpq, hqlo, hq, hqodd, he, ht⟩ := hy
    change p ≤ q at hpq
    by_cases heq : q = p
    · subst q
      have hfit : Slot.Fits ⟨p, 1, false⟩ (p, e) :=
        ⟨hq, rfl, he, by simp⟩
      have eq : xs ++ (p, e) :: ys = (xs ++ [(p, e)]) ++ ys := by
        simp [List.append_assoc]
      rw [eq] at hcoord hw hprim
      exact htake hq (xs ++ [(p, e)]) ys
        ⟨List.rel_append hx (.cons hfit .nil), ht, by simpa using hlen⟩ hcoord hw hprim
    · have hlt : p + 2 ≤ q := by
        obtain ⟨a, ha⟩ := hodd
        obtain ⟨b, hb⟩ := hqodd
        omega
      exact hskip xs ((q, e) :: ys) ⟨hx, ⟨hlt, hqlo, hq, hqodd, he, ht⟩, hlen⟩ hcoord hw hprim

theorem number_gt_one_of_tail {p : ℕ} {ys : Coordinates} (h : TailFits p ys)
    (hne : ys ≠ []) : 1 < number ys := by
  induction ys generalizing p with
  | nil => contradiction
  | cons y ys ih =>
    obtain ⟨q, e⟩ := y
    obtain ⟨_, hq, hprime, _, he, ht⟩ := h
    have hpow : 1 < q ^ e := one_lt_pow₀ (by omega) he.ne'
    rw [number_cons]
    change 1 < q ^ e * number ys
    by_cases hnil : ys = []
    · simpa [hnil, number] using hpow
    · exact hpow.trans_le (Nat.le_mul_of_pos_right _ (ih ht hnil).pos)

theorem close_minimum_with_tail {b : Box} (hr : 0 < b.remaining)
    (hnondef : 2 * number b.minimum ≤ divisorSum b.minimum) : b.Closed := by
  intro xs ys ⟨hfit, htail, hylen⟩ hvalid hw hprimitive
  have hne : ys ≠ [] := by
    rintro rfl
    simp at hylen
    omega
  have hlarge := number_gt_one_of_tail htail hne
  have hxs : 0 < number xs := number_pos (primeCoordinates_left hvalid).1
  have hdvd := minimum_dvd hfit
  have hlt : number b.minimum < number (xs ++ ys) := by
    rw [number_append]
    exact (Nat.le_of_dvd hxs hdvd).trans_lt (by
      simpa using (Nat.mul_lt_mul_of_pos_left hlarge hxs))
  have hmem : number b.minimum ∈ (number (xs ++ ys)).properDivisors :=
    Nat.mem_properDivisors.mpr ⟨by
      rw [number_append]
      exact dvd_mul_of_dvd_left hdvd _, hlt⟩
  have hv : PrimeCoordinates b.minimum := minimum_valid hfit (primeCoordinates_left hvalid)
  exact (deficient_iff_divisorSum_lt hv).mp (hprimitive _ hmem) |>.not_ge hnondef

def decrement : Coordinates → ℕ → Coordinates
  | [], _ => []
  | (p, e) :: xs, 0 => (p, e - 1) :: xs
  | x :: xs, i + 1 => x :: decrement xs i

theorem decrement_primes (xs : Coordinates) (i : ℕ) :
    (decrement xs i).map Prod.fst = xs.map Prod.fst := by
  induction xs generalizing i with
  | nil => simp [decrement]
  | cons x xs ih =>
    rcases x with ⟨p, e⟩
    cases i with
    | zero => rfl
    | succ i => simp [decrement, ih i]

theorem decrement_coordinates {xs : Coordinates} (h : PrimeCoordinates xs) (i : ℕ) :
    PrimeCoordinates (decrement xs i) := by
  have hprime (ls : Coordinates) :
      (∀ x ∈ ls, Nat.Prime x.1) ↔ ∀ p ∈ ls.map Prod.fst, Nat.Prime p := by simp
  have hordered (ls : Coordinates) :
      ls.Pairwise (fun x y => x.1 < y.1) ↔ (ls.map Prod.fst).Pairwise (· < ·) :=
    List.pairwise_map.symm
  rw [PrimeCoordinates, hprime, hordered, decrement_primes]
  exact ⟨(hprime xs).mp h.1, (hordered xs).mp h.2⟩

theorem decrement_dvd (xs : Coordinates) (i : ℕ) :
    number (decrement xs i) ∣ number xs := by
  induction xs generalizing i with
  | nil => simp [decrement]
  | cons x xs ih =>
    rcases x with ⟨p, e⟩
    cases i with
    | zero =>
      simp only [decrement, number_cons]
      exact Nat.mul_dvd_mul (pow_dvd_pow p (Nat.sub_le e 1)) dvd_rfl
    | succ i =>
      exact Nat.mul_dvd_mul dvd_rfl (ih i)

theorem close_minimum_decrement {b : Box} {i : ℕ}
    (hnondef : 2 * number b.minimum ≤ divisorSum b.minimum)
    (hlt : number (decrement b.minimum i) < number b.minimum)
    (hdec : 2 * number (decrement b.minimum i) ≤ divisorSum (decrement b.minimum i)) :
    b.Closed := by
  intro xs ys hfit hvalid hw hprim
  have hv : PrimeCoordinates b.minimum := minimum_valid hfit.1 (primeCoordinates_left hvalid)
  have hd : ¬ (number (decrement b.minimum i)).Deficient :=
    fun h => (deficient_iff_divisorSum_lt (decrement_coordinates hv i)).mp h |>.not_ge hdec
  exact close_minimum_has_nondeficient_divisor hnondef (decrement_dvd b.minimum i)
    hlt hd xs ys hfit hvalid hw hprim

end OddWeirdSubproblems

namespace OddWeirdSubproblems

open scoped BigOperators

def primeCoordinates (n : ℕ) : List (ℕ × ℕ) :=
  n.primeFactors.sort.map (fun p => (p, n.factorization p))

theorem mem_primeCoordinates {n p a : ℕ} :
    (p, a) ∈ primeCoordinates n ↔ p ∈ n.primeFactors ∧ a = n.factorization p := by
  simp only [primeCoordinates, List.mem_map, Finset.mem_sort, Prod.mk.injEq]
  constructor
  · rintro ⟨q, hq, rfl, rfl⟩
    exact ⟨hq, rfl⟩
  · rintro ⟨hp, rfl⟩
    exact ⟨p, hp, rfl, rfl⟩

theorem primeCoordinates_pairwise (n : ℕ) :
    (primeCoordinates n).Pairwise (fun x y => x.1 < y.1) := by
  simpa only [primeCoordinates, List.pairwise_map] using n.primeFactors.sortedLT_sort.pairwise

theorem primeCoordinates_length (n : ℕ) :
    (primeCoordinates n).length = n.primeFactors.card := by
  simp [primeCoordinates, Finset.length_sort]

theorem primeCoordinates_prime_pos {n : ℕ} {x : ℕ × ℕ}
    (hx : x ∈ primeCoordinates n) : x.1.Prime ∧ 0 < x.2 := by
  obtain ⟨p, a⟩ := x
  obtain ⟨hp, rfl⟩ := mem_primeCoordinates.mp hx
  exact ⟨Nat.prime_of_mem_primeFactors hp, by
    rw [Nat.pos_iff_ne_zero, ← Finsupp.mem_support_iff, Nat.support_factorization]
    exact hp⟩

theorem primeCoordinates_odd {n : ℕ} (hn : Odd n) {x : ℕ × ℕ}
    (hx : x ∈ primeCoordinates n) : Odd x.1 := by
  obtain ⟨p, a⟩ := x
  exact hn.of_dvd_nat (Nat.dvd_of_mem_primeFactors (mem_primeCoordinates.mp hx).1)

theorem primeCoordinates_prod_map (n : ℕ) (f : ℕ × ℕ → ℕ) :
    ((primeCoordinates n).map f).prod =
      ∏ p ∈ n.primeFactors, f (p, n.factorization p) := by
  rw [primeCoordinates, List.map_map, ← List.prod_toFinset _ (Finset.sort_nodup _ _),
    Finset.sort_toFinset]
  rfl

theorem primeCoordinates_prod {n : ℕ} (hn : n ≠ 0) :
    ((primeCoordinates n).map (fun x => x.1 ^ x.2)).prod = n := by
  rw [primeCoordinates_prod_map]
  exact (Nat.prod_primeFactors_pow_factorization hn).symm

theorem primeCoordinates_three {n : ℕ} (hodd : Odd n) (hthree : 3 ∣ n) :
    ∃ xs : List (ℕ × ℕ), primeCoordinates n = (3, n.factorization 3) :: xs ∧
      ∀ x ∈ xs, 5 ≤ x.1 := by
  have hp : 3 ∈ n.primeFactors := Nat.mem_primeFactors.mpr
    ⟨by decide, hthree, hodd.pos.ne'⟩
  let tail := n.primeFactors.erase 3
  have htail (p : ℕ) (hp' : p ∈ tail) : 5 ≤ p := by
    obtain ⟨hne, hmem⟩ := Finset.mem_erase.mp hp'
    have hmin := (Nat.prime_of_mem_primeFactors hmem).one_lt
    obtain ⟨k, hk⟩ := hodd.of_dvd_nat (Nat.dvd_of_mem_primeFactors hmem)
    omega
  have hlo : ∀ p ∈ tail, 3 ≤ p := fun p hp' => (show 3 ≤ 5 by decide).trans (htail p hp')
  have hn3 : 3 ∉ tail := Finset.notMem_erase _ _
  refine ⟨tail.sort.map (fun p => (p, n.factorization p)), ?_, ?_⟩
  · rw [primeCoordinates, ← Finset.insert_erase hp, Finset.sort_insert (· ≤ ·) hlo hn3]
    rfl
  · intro x hx
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hx
    exact htail p ((Finset.mem_sort (· ≤ ·)).mp hp)

end OddWeirdSubproblems

namespace OddWeirdSubproblems

open Finset

theorem pseudoperfectOfDvd {d n : ℕ} (hn : 0 < n) (hd : d ∣ n)
    (hp : d.Pseudoperfect) : n.Pseudoperfect := by
  obtain ⟨k, rfl⟩ := hd
  obtain ⟨_, s, hsub, hsum⟩ := hp
  have hk := Nat.pos_of_mul_pos_left hn
  let scale : ℕ ↪ ℕ := ⟨(· * k), fun _ _ h => Nat.eq_of_mul_eq_mul_right hk h⟩
  refine ⟨hn, s.map scale, ?_, ?_⟩
  · intro x hx
    obtain ⟨a, ha, rfl⟩ := mem_map.mp hx
    obtain ⟨had, halt⟩ := Nat.mem_properDivisors.mp (hsub ha)
    exact Nat.mem_properDivisors.mpr
      ⟨Nat.mul_dvd_mul_right had k, Nat.mul_lt_mul_of_pos_right halt hk⟩
  · rw [sum_map]
    change (∑ a ∈ s, a * k) = d * k
    rw [← sum_mul, hsum]

theorem primitiveWeirdDivisor {n : ℕ} (hw : n.Weird) :
    ∃ d : ℕ, d ∣ n ∧ d.Weird ∧ ∀ k ∈ d.properDivisors, k.Deficient := by
  have hex : ∃ d : ℕ, d ∣ n ∧ ¬ d.Deficient :=
    ⟨n, dvd_rfl, fun h => (not_lt_of_gt hw.1) h⟩
  let d := Nat.find hex
  have hd : d ∣ n := (Nat.find_spec hex).1
  have hnd : ¬ d.Deficient := (Nat.find_spec hex).2
  have hpos : 0 < d := Nat.pos_of_dvd_of_pos hd hw.1.pos
  have hnp : ¬ d.Pseudoperfect := fun hp => hw.2 (pseudoperfectOfDvd hw.1.pos hd hp)
  refine ⟨d, hd, ⟨?_, hnp⟩, ?_⟩
  · by_contra hna
    exact hnp (((Nat.perfect_iff_not_abundant_and_not_deficient hpos.ne).2
      ⟨hna, hnd⟩).pseudoperfect)
  · intro k hk
    obtain ⟨hkd, hlt⟩ := Nat.mem_properDivisors.mp hk
    by_contra! hndef
    exact (not_le_of_gt hlt) (Nat.find_min' hex ⟨hkd.trans hd, hndef⟩)

theorem primeDivisorNcard (n : ℕ) :
    {p : ℕ | p ∈ n.divisors ∧ p.Prime}.ncard = n.primeFactors.card := by
  have hs : {p : ℕ | p ∈ n.divisors ∧ p.Prime} = (n.primeFactors : Set ℕ) := by
    ext p
    simp only [Set.mem_ofPred_eq, Finset.mem_coe, Nat.mem_primeFactors, Nat.mem_divisors]
    tauto
  rw [hs, Set.ncard_coe_finset]

theorem atLeastSixOfPrimitive
    (verify : ∀ m : ℕ, Odd m → m.Abundant → m.primeFactors.card ≤ 5 →
      (∀ d ∈ m.properDivisors, d.Deficient) → m.Pseudoperfect) :
    ∀ n : ℕ, Odd n → n.Weird → 6 ≤ {p : ℕ | p ∈ n.divisors ∧ p.Prime}.ncard := by
  intro n ho hw
  rw [primeDivisorNcard]
  by_contra! hc
  obtain ⟨d, hd, hdw, hproper⟩ := primitiveWeirdDivisor hw
  have hcard := Finset.card_le_card (Nat.primeFactors_mono hd hw.1.pos.ne')
  exact hdw.2 (verify d (ho.of_dvd_nat hd) hdw.1 (by omega) hproper)

end OddWeirdSubproblems

namespace OddWeird

def primeSaturationRatio (p : ℕ) : ℚ := 1 + 1 / ((p : ℚ) - 1)

private theorem primeSaturationRatio_one_le {p : ℕ} (hp : 1 < p) :
    1 ≤ primeSaturationRatio p := by
  have hp' : (1 : ℚ) < p := by exact_mod_cast hp
  have hinv : (0 : ℚ) ≤ 1 / ((p : ℚ) - 1) := by positivity
  unfold primeSaturationRatio
  linarith

private theorem primeSaturationRatio_antitone {a b : ℕ} (ha : 1 < a) (hab : a ≤ b) :
    primeSaturationRatio b ≤ primeSaturationRatio a := by
  have ha' : (1 : ℚ) < a := by exact_mod_cast ha
  have hab' : (a : ℚ) ≤ b := by exact_mod_cast hab
  simpa only [primeSaturationRatio, add_comm] using add_le_add_left
    (one_div_le_one_div_of_le (sub_pos.mpr ha') (sub_le_sub_right hab' 1)) 1

private theorem primeSaturationRatio_prod_le (k : ℕ) (S : Finset ℕ) (b : ℕ) (hb : 1 < b)
    (hcard : S.card = k) (hS : ∀ p ∈ S, Odd p ∧ b ≤ p) :
    (∏ p ∈ S, primeSaturationRatio p) ≤
      ∏ i ∈ Finset.range k, primeSaturationRatio (b + 2 * i) := by
  induction k generalizing S b with
  | zero => simp [Finset.card_eq_zero.mp hcard]
  | succ k ih =>
    have hne : S.Nonempty := Finset.card_pos.mp (by omega)
    let p := S.min' hne
    have hp : p ∈ S := Finset.min'_mem S hne
    have htail (q : ℕ) (hq : q ∈ S.erase p) : Odd q ∧ b + 2 ≤ q := by
      obtain ⟨hqne, hqS⟩ := Finset.mem_erase.mp hq
      have hpq : p ≤ q := Finset.min'_le S q hqS
      obtain ⟨hpo, hbp⟩ := hS p hp
      obtain ⟨hqo, _⟩ := hS q hqS
      refine ⟨hqo, ?_⟩
      rcases hpo with ⟨a, ha⟩
      rcases hqo with ⟨c, hc⟩
      omega
    have hc : (S.erase p).card = k := by rw [Finset.card_erase_of_mem hp, hcard]; omega
    have htailLe := ih (S.erase p) (b + 2) (by omega) hc htail
    rw [← Finset.prod_erase_mul S primeSaturationRatio hp,
      Finset.prod_range_succ', Nat.mul_zero, Nat.add_zero]
    have hshift : ∏ i ∈ Finset.range k, primeSaturationRatio (b + 2 + 2 * i) =
        ∏ i ∈ Finset.range k, primeSaturationRatio (b + 2 * (i + 1)) := by
      refine Finset.prod_congr rfl fun i _ => ?_
      congr 1
      omega
    refine mul_le_mul (htailLe.trans_eq hshift) (primeSaturationRatio_antitone hb (hS p hp).2)
      (zero_le_one.trans (primeSaturationRatio_one_le (hb.trans_le (hS p hp).2))) ?_
    exact Finset.prod_nonneg fun i _ => zero_le_one.trans (primeSaturationRatio_one_le (by omega))

private theorem geomRatio_le_primeSaturationRatio (p a : ℕ) (hp : 1 < p) :
    (∑ i ∈ Finset.range (a + 1), (p : ℚ) ^ i) / (p : ℚ) ^ a ≤ primeSaturationRatio p := by
  have hp' : (1 : ℚ) < p := by exact_mod_cast hp
  have hm : (0 : ℚ) < (p : ℚ) - 1 := sub_pos.mpr hp'
  have hpow : (0 : ℚ) < (p : ℚ) ^ a := by positivity
  have hr : primeSaturationRatio p = (p : ℚ) / ((p : ℚ) - 1) := by
    unfold primeSaturationRatio
    apply (eq_div_iff hm.ne').mpr
    rw [add_mul, one_mul, div_mul_cancel₀ _ hm.ne']
    ring
  rw [hr, div_le_div_iff₀ hpow hm, geom_sum_mul, pow_succ]
  linarith

private theorem abundancyIndex_eq_factorization_product {n : ℕ} (hn : n ≠ 0) :
    n.abundancyIndex = ∏ p ∈ n.primeFactors,
      (∑ i ∈ Finset.range (n.factorization p + 1), (p : ℚ) ^ i) / (p : ℚ) ^ n.factorization p := by
  have hsigma := ArithmeticFunction.sigma_eq_prod_primeFactors_sum_range_factorization_pow_mul
    (k := 1) hn
  rw [ArithmeticFunction.sigma_one_apply] at hsigma
  simp only [mul_one] at hsigma
  have hpow := Nat.prod_primeFactors_pow_factorization hn
  rw [Nat.abundancyIndex, hsigma]
  conv_lhs =>
    arg 2
    rw [hpow]
  simp only [Nat.cast_prod, Nat.cast_sum, Nat.cast_pow, ← Finset.prod_div_distrib]

theorem abundancyIndex_le_of_odd_of_primeFactors_sdiff_card_le {n b k : ℕ} {E : Finset ℕ}
    (hodd : Odd n) (hb : 1 < b) (hcard : (n.primeFactors \ E).card ≤ k)
    (hmin : ∀ p ∈ n.primeFactors \ E, b ≤ p) :
    n.abundancyIndex ≤
      (∏ p ∈ n.primeFactors ∩ E,
        (∑ i ∈ Finset.range (n.factorization p + 1), (p : ℚ) ^ i) / (p : ℚ) ^ n.factorization p) *
      ∏ i ∈ Finset.range k, primeSaturationRatio (b + 2 * i) := by
  have hn : n ≠ 0 := by
    rcases hodd with ⟨a, ha⟩
    omega
  let S := n.primeFactors \ E
  let R (p : ℕ) :=
    (∑ i ∈ Finset.range (n.factorization p + 1), (p : ℚ) ^ i) / (p : ℚ) ^ n.factorization p
  have hR (p : ℕ) : 0 ≤ R p := by
    unfold R
    positivity
  have hS (p : ℕ) (hp : p ∈ S) : Odd p ∧ b ≤ p :=
    ⟨hodd.of_dvd_nat (Nat.dvd_of_mem_primeFactors (Finset.mem_sdiff.mp hp).1), hmin p hp⟩
  have hproduct : (∏ p ∈ S, R p) ≤ ∏ i ∈ Finset.range k, primeSaturationRatio (b + 2 * i) := by
    calc
      _ ≤ ∏ p ∈ S, primeSaturationRatio p :=
        Finset.prod_le_prod (fun p _ => hR p) (fun p hp =>
          geomRatio_le_primeSaturationRatio p _ (hb.trans_le (hmin p hp)))
      _ ≤ ∏ i ∈ Finset.range S.card, primeSaturationRatio (b + 2 * i) :=
        primeSaturationRatio_prod_le _ S b hb rfl hS
      _ ≤ ∏ i ∈ Finset.range k, primeSaturationRatio (b + 2 * i) :=
        Finset.prod_le_prod_of_subset_of_one_le (Finset.range_mono hcard)
          (fun i _ => zero_le_one.trans (primeSaturationRatio_one_le (by omega)))
          (fun i _ _ => primeSaturationRatio_one_le (by omega))
  rw [abundancyIndex_eq_factorization_product hn]
  change (∏ p ∈ n.primeFactors, R p) ≤ (∏ p ∈ n.primeFactors ∩ E, R p) * _
  conv_lhs =>
    rw [← Finset.sdiff_union_inter n.primeFactors E,
      Finset.prod_union (Finset.disjoint_sdiff_inter n.primeFactors E),
      mul_comm (∏ p ∈ S, R p)]
  exact mul_le_mul_of_nonneg_left hproduct (Finset.prod_nonneg fun p _ => hR p)

theorem deficient_of_odd_of_primeFactors_card_le_five_of_not_three_dvd {n : ℕ}
    (hodd : Odd n) (hcard : n.primeFactors.card ≤ 5) (hthree : ¬ 3 ∣ n) : n.Deficient := by
  have hn : n ≠ 0 := by
    rintro rfl
    exact hthree (dvd_zero 3)
  have hS (p : ℕ) (hp : p ∈ n.primeFactors) : 5 ≤ p := by
    have hpn := Nat.dvd_of_mem_primeFactors hp
    have hpo := hodd.of_dvd_nat hpn
    have hp3 : p ≠ 3 := fun h => hthree (h ▸ hpn)
    have hp1 := (Nat.prime_of_mem_primeFactors hp).one_lt
    rcases hpo with ⟨a, ha⟩
    omega
  have hindex : n.abundancyIndex ≤ ∏ i ∈ Finset.range 5, primeSaturationRatio (5 + 2 * i) := by
    simpa using abundancyIndex_le_of_odd_of_primeFactors_sdiff_card_le (E := ∅) (k := 5)
      hodd (b := 5) (by decide) (by simpa using hcard) (fun p hp => hS p (by simpa using hp))
  have h := hindex.trans_lt (show (∏ i ∈ Finset.range 5, primeSaturationRatio (5 + 2 * i)) < 2 by
    norm_num [Finset.prod_range_succ, primeSaturationRatio])
  have hn' : (0 : ℚ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  rw [Nat.abundancyIndex, div_lt_iff₀ hn'] at h
  have hsum : ∑ d ∈ n.divisors, d < 2 * n := by exact_mod_cast h
  rw [Nat.sum_divisors_eq_sum_properDivisors_add_self] at hsum
  unfold Nat.Deficient
  omega

end OddWeird

namespace OddWeirdSubproblems

theorem noPrimitiveWeird_three_of_coordinate_roots {k lower : ℕ} {fixed : Bool}
    (roots : ∀ r ≤ k, (⟨[⟨3, lower, fixed⟩], 5, r⟩ : Box).Closed)
    {n : ℕ} (ho : Odd n) (hw : n.Weird) (hc : n.primeFactors.card ≤ k + 1)
    (hproper : ∀ d ∈ n.properDivisors, d.Deficient) (h3 : 3 ∣ n)
    (hval : lower ≤ n.factorization 3) (hfixed : fixed = true → lower = n.factorization 3) :
    False := by
  obtain ⟨ys, hys, hmin⟩ := primeCoordinates_three ho h3
  let xs : Coordinates := [(3, n.factorization 3)]
  have hcat : primeCoordinates n = xs ++ ys := hys
  have hn : number (xs ++ ys) = n := by
    rw [← hcat]
    exact primeCoordinates_prod ho.pos.ne'
  have hpw : (xs ++ ys).Pairwise (fun x y => x.1 < y.1) := hcat ▸ primeCoordinates_pairwise n
  have hprime (x : ℕ × ℕ) (hx : x ∈ xs ++ ys) : x.1.Prime ∧ 0 < x.2 :=
    primeCoordinates_prime_pos (hcat.symm ▸ hx)
  have hlen := primeCoordinates_length n
  rw [hcat] at hlen
  simp only [xs, List.cons_append, List.nil_append, List.length_cons] at hlen
  have hlen' : ys.length ≤ k := by omega
  have ht : TailFits 5 ys := by
    apply tailFits_of_sorted (by decide : 2 < 5) hmin _
      (List.pairwise_append.mp hpw).2.1
    intro x hx
    have hxmem : x ∈ xs ++ ys := List.mem_append_right _ hx
    exact ⟨(hprime x hxmem).1, primeCoordinates_odd ho (hcat.symm ▸ hxmem),
      (hprime x hxmem).2⟩
  have hfit : List.Forall₂ Slot.Fits [⟨3, lower, fixed⟩] xs :=
    .cons ⟨show Nat.Prime 3 by decide, rfl, hval, hfixed⟩ .nil
  exact roots ys.length hlen' xs ys ⟨hfit, ht, rfl⟩ ⟨fun x hx => (hprime x hx).1, hpw⟩
    (hn.symm ▸ hw) (hn.symm ▸ hproper)

theorem atLeastSix_of_threeRoots
    (one : ∀ r ≤ 4, (⟨[⟨3, 1, true⟩], 5, r⟩ : Box).Closed)
    (high : ∀ r ≤ 4, (⟨[⟨3, 2, false⟩], 5, r⟩ : Box).Closed) :
    ∀ n : ℕ, Odd n → n.Weird → 6 ≤ {p : ℕ | p ∈ n.divisors ∧ p.Prime}.ncard := by
  apply atLeastSixOfPrimitive
  intro n ho ha hc hproper
  by_contra hpp
  have h3 : 3 ∣ n := by
    by_contra h
    exact (not_lt_of_gt ha)
      (OddWeird.deficient_of_odd_of_primeFactors_card_le_five_of_not_three_dvd ho hc h)
  have hprime : Nat.Prime 3 := by decide
  have hpositive := hprime.factorization_pos_of_dvd ho.pos.ne' h3
  by_cases h9 : 2 ≤ n.factorization 3
  · exact noPrimitiveWeird_three_of_coordinate_roots high ho ⟨ha, hpp⟩ hc hproper h3 h9
      (by simp)
  · exact noPrimitiveWeird_three_of_coordinate_roots one ho ⟨ha, hpp⟩ hc hproper h3
      (by omega) (by omega)

end OddWeirdSubproblems

namespace OddWeirdSubproblems

def witnessOk (n s : ℕ) (ds : List ℕ) : Bool :=
  ds.all (fun d => decide (d ∣ n ∧ d < n)) && tightlySorted ds && decide (s = 2 * n + ds.sum)

theorem witnessOk_closes {b : Box} {ds : List ℕ}
    (h : witnessOk (number b.minimum) (divisorSum b.minimum) ds = true) :
    b.Closed := by
  simp only [witnessOk, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  exact close_minimum_witness (tightlySorted_nodup h.1.2) (by simpa using h.1.1) h.2

def decrementOk (fs : Coordinates) (i : ℕ) : Bool :=
  let ds := decrement fs i
  decide (number ds < number fs ∧ 2 * number ds ≤ divisorSum ds)

def minimumOk (witness : ℕ → List ℕ) (b : Box) : Bool :=
  let n := number b.minimum
  let s := divisorSum b.minimum
  decide (0 < b.remaining) || decide (s = 2 * n) ||
    (List.range b.slots.length).any (decrementOk b.minimum) || witnessOk n s (witness n)

theorem minimumOk_closes {witness : ℕ → List ℕ} {b : Box}
    (hnondef : 2 * number b.minimum ≤ divisorSum b.minimum)
    (h : minimumOk witness b = true) : b.Closed := by
  simp only [minimumOk, Bool.or_eq_true, decide_eq_true_eq, List.any_eq_true] at h
  rcases h with ((h | h) | h) | h
  · exact close_minimum_with_tail h hnondef
  · exact close_minimum_eq_two h
  · obtain ⟨i, _, hi⟩ := h
    simp only [decrementOk, decide_eq_true_eq] at hi
    exact close_minimum_decrement hnondef hi.1 hi.2
  · exact witnessOk_closes h

def chooseSlot (b : Box) : Option ℕ :=
  ((b.slots.zipIdx.filter (fun (s, _) => !s.fixed)).foldl
    (fun best (s, i) =>
      let key := s.prime ^ (s.exponent + 1)
      if (b.remaining == 0 || key < b.next) && key < best.1
      then (key, some i) else best)
    (b.slots.foldl (fun n s => max n (s.prime ^ (s.exponent + 1) + 1)) 1, none)).2

def replay (witness : ℕ → List ℕ) : ℕ → Box → Bool
  | 0, _ => false
  | fuel + 1, b =>
    if 2 * number b.minimum ≤ divisorSum b.minimum then minimumOk witness b
    else if b.upperNum ≤ 2 * b.upperDen then true
    else match (chooseSlot b).bind (fun i => b.slots[i]?.map (fun s => (i, s))) with
    | some (i, s) =>
      if s.fixed then false else
      replay witness fuel {b with slots := b.slots.set i {s with fixed := true}} &&
      replay witness fuel {b with slots := b.slots.set i {s with exponent := s.exponent + 1}}
    | none =>
      match b.remaining with
      | 0 => false
      | r + 1 =>
        replay witness fuel ⟨b.slots, b.next + 2, r + 1⟩ &&
        if b.next.minFac = b.next then
          replay witness fuel ⟨b.slots ++ [⟨b.next, 1, false⟩], b.next + 2, r⟩
        else true

theorem replay_closes {witness : ℕ → List ℕ} {fuel : ℕ} {b : Box}
    (hlo : 1 < b.next) (hodd : Odd b.next) (h : replay witness fuel b = true) :
    b.Closed := by
  induction fuel generalizing b with
  | zero => simp [replay] at h
  | succ fuel ih =>
    rw [replay] at h
    split at h
    · exact minimumOk_closes ‹_› h
    split at h
    · exact close_of_upperNum_le hlo ‹_›
    split at h
    next i s hs =>
      have hi : b.slots[i]? = some s := by
        have hb := Option.bind_eq_some_iff.mp hs
        obtain ⟨j, _, hj⟩ := hb
        cases hg : b.slots[j]? <;> simp_all
      split at h
      · contradiction
      · have hf : s.fixed = false := by simp_all
        obtain ⟨h₁, h₂⟩ := Bool.and_eq_true_iff.mp h
        exact close_split_slot hi hf (ih hlo hodd h₁) (ih hlo hodd h₂)
    next =>
      rcases b with ⟨ss, p, r⟩
      cases r with
      | zero => contradiction
      | succ r =>
        obtain ⟨hskip, htake⟩ := Bool.and_eq_true_iff.mp h
        have hodd' : Odd (p + 2) := by
          obtain ⟨k, hk⟩ := hodd
          exact ⟨k + 1, by dsimp at hk; omega⟩
        have hlo' : 1 < p + 2 := by dsimp at hlo; omega
        apply close_split_next hodd (ih hlo' hodd' hskip)
        intro hp
        exact ih hlo' hodd' (by simpa only [if_pos hp.minFac_eq] using htake)

def slotEqual (a b : Slot) : Bool :=
  decide ((a.prime, a.exponent, a.fixed) = (b.prime, b.exponent, b.fixed))

theorem slotEqual_iff_eq (a b : Slot) : slotEqual a b = true ↔ a = b := by
  cases a; cases b; simp [slotEqual, Slot.mk.injEq]

def slotsEqual : List Slot → List Slot → Bool
  | [], [] => true
  | a :: as, b :: bs => slotEqual a b && slotsEqual as bs
  | _, _ => false

theorem slotsEqual_iff_eq (as bs : List Slot) : slotsEqual as bs = true ↔ as = bs := by
  induction as generalizing bs <;> cases bs <;>
    simp [slotsEqual, slotEqual_iff_eq, *]

def boxEqual (a b : Box) : Bool :=
  slotsEqual a.slots b.slots && decide (a.next = b.next) && decide (a.remaining = b.remaining)

theorem boxEqual_iff_eq (a b : Box) : boxEqual a b = true ↔ a = b := by
  cases a; cases b; simp [boxEqual, slotsEqual_iff_eq, Box.mk.injEq, and_assoc]

end OddWeirdSubproblems

namespace OddWeirdSubproblems

def Box.ClosedBelow (b : Box) (B : ℕ) : Prop :=
  ∀ xs ys, b.Matches xs ys → PrimeCoordinates (xs ++ ys) →
    number (xs ++ ys) < B → (number (xs ++ ys)).Weird →
    (∀ d ∈ (number (xs ++ ys)).properDivisors, d.Deficient) → False

theorem closedBelow_of_closed {b : Box} (h : b.Closed) (B : ℕ) : b.ClosedBelow B :=
  fun xs ys hm hv _ hw hp => h xs ys hm hv hw hp

theorem closeBelow_split_slot {b : Box} {B i : ℕ} {s : Slot}
    (hi : b.slots[i]? = some s) (hf : s.fixed = false)
    (h₁ : ({b with slots := b.slots.set i {s with fixed := true}} : Box).ClosedBelow B)
    (h₂ : ({b with slots := b.slots.set i {s with exponent := s.exponent + 1}} : Box).ClosedBelow B) :
    b.ClosedBelow B := by
  intro xs ys ⟨hf₂, ht, hr⟩ hp hlt hw hprim
  rcases forall₂_slot_split hf₂ hi hf with h | h
  · exact h₁ xs ys ⟨h, ht, hr⟩ hp hlt hw hprim
  · exact h₂ xs ys ⟨h, ht, hr⟩ hp hlt hw hprim

theorem closeBelow_split_next {ss : List Slot} {B p r : ℕ} (hodd : Odd p)
    (hskip : (⟨ss, p + 2, r + 1⟩ : Box).ClosedBelow B)
    (htake : p.Prime → (⟨ss ++ [⟨p, 1, false⟩], p + 2, r⟩ : Box).ClosedBelow B) :
    (⟨ss, p, r + 1⟩ : Box).ClosedBelow B := by
  intro xs ys ⟨hx, hy, hlen⟩ hcoord hlt hw hprim
  cases ys with
  | nil => simp at hlen
  | cons y ys =>
    obtain ⟨q, e⟩ := y
    obtain ⟨hpq, hqlo, hq, hqodd, he, ht⟩ := hy
    change p ≤ q at hpq
    by_cases heq : q = p
    · subst q
      have hfit : Slot.Fits ⟨p, 1, false⟩ (p, e) := ⟨hq, rfl, he, by simp⟩
      have eq : xs ++ (p, e) :: ys = (xs ++ [(p, e)]) ++ ys := by simp [List.append_assoc]
      rw [eq] at hcoord hlt hw hprim
      exact htake hq (xs ++ [(p, e)]) ys
        ⟨List.rel_append hx (.cons hfit .nil), ht, by simpa using hlen⟩ hcoord hlt hw hprim
    · have hqmin : p + 2 ≤ q := by
        obtain ⟨a, ha⟩ := hodd
        obtain ⟨b, hb⟩ := hqodd
        omega
      exact hskip xs ((q, e) :: ys) ⟨hx, ⟨hqmin, hqlo, hq, hqodd, he, ht⟩, hlen⟩
        hcoord hlt hw hprim

end OddWeirdSubproblems

namespace OddWeirdSubproblems

open Finset

theorem squarefreeExcess {m q s : ℕ} (hq : q.Prime) (hfresh : ¬ q ∣ m)
    (hs : (∑ d ∈ m.divisors, d) = s) (hdef : s ≤ 2 * m) :
    (∑ d ∈ (m * q).divisors, d) + (2 * m - s) * q = 2 * (m * q) + s := by
  have hc : m.Coprime q := (hq.coprime_iff_not_dvd.mpr hfresh).symm
  have hqsum : (∑ d ∈ q.divisors, d) = 1 + q := by
    rw [hq.divisors]
    simp [hq.ne_one.symm]
  have hadd := congrArg (· * q) (Nat.sub_add_cancel hdef)
  rw [Nat.add_mul, Nat.mul_assoc] at hadd
  rw [hc.sum_divisors_mul, hs, hqsum, Nat.mul_add, Nat.mul_one]
  omega

theorem squarefreePseudoperfectOfSubset {m q s h : ℕ} (hq : q.Prime) (hfresh : ¬ q ∣ m)
    (hs : (∑ d ∈ m.divisors, d) = s) (hdef : s ≤ 2 * m)
    (hh : h = 0 ∨ h ∈ m.properDivisors) {t : Finset ℕ} (ht : t ⊆ m.divisors)
    (htsum : (∑ d ∈ t, d) + (2 * m - s + h) * q = s) :
    (m * q).Pseudoperfect := by
  have hm : 0 < m := Nat.pos_of_ne_zero (fun hm => hfresh (hm ▸ dvd_zero q))
  have hmq : 0 < m * q := Nat.mul_pos hm hq.pos
  have hltmq : m < m * q := by simpa using Nat.mul_lt_mul_of_pos_left hq.one_lt hm
  have heq := squarefreeExcess hq hfresh hs hdef
  rw [Nat.add_mul] at htsum
  have hbase : t ⊆ (m * q).properDivisors := by
    intro d hd
    have hdvd := (Nat.mem_divisors.mp (ht hd)).1
    exact Nat.mem_properDivisors.mpr
      ⟨hdvd.trans (dvd_mul_right m q),
        (Nat.le_of_dvd hm hdvd).trans_lt hltmq⟩
  suffices hex : ∃ u ⊆ (m * q).properDivisors, ∑ d ∈ u, d = (∑ d ∈ t, d) + h * q by
    obtain ⟨u, hu, hus⟩ := hex
    refine ⟨hmq, (m * q).properDivisors \ u, Finset.sdiff_subset, ?_⟩
    have hc := Finset.sum_sdiff (f := fun d : ℕ => d) hu
    rw [Nat.sum_divisors_eq_sum_properDivisors_add_self] at heq
    omega
  rcases hh with rfl | hh
  · exact ⟨t, hbase, by simp⟩
  · obtain ⟨hdiv, hlt⟩ := Nat.mem_properDivisors.mp hh
    have hmem : h * q ∈ (m * q).properDivisors := Nat.mem_properDivisors.mpr
      ⟨Nat.mul_dvd_mul_right hdiv q, Nat.mul_lt_mul_of_pos_right hlt hq.pos⟩
    have hnot : h * q ∉ t := fun htq =>
      hfresh ((dvd_mul_left q h).trans (Nat.mem_divisors.mp (ht htq)).1)
    refine ⟨insert (h * q) t, Finset.insert_subset hmem hbase, ?_⟩
    rw [Finset.sum_insert hnot, Nat.add_comm]

theorem squarefreePseudoperfectOfInterval {m q s h a b : ℕ} (hq : q.Prime)
    (hfresh : ¬ q ∣ m) (hs : (∑ d ∈ m.divisors, d) = s) (hdef : s ≤ 2 * m)
    (hh : h = 0 ∨ h ∈ m.properDivisors)
    (hcover : ∀ x, a ≤ x → x ≤ b → ∃ t ⊆ m.divisors, ∑ d ∈ t, d = x)
    (hlo : a + (2 * m - s + h) * q ≤ s)
    (hhi : s ≤ b + (2 * m - s + h) * q) : (m * q).Pseudoperfect := by
  obtain ⟨t, ht, hsum⟩ := hcover (s - (2 * m - s + h) * q) (by omega) (by omega)
  exact squarefreePseudoperfectOfSubset hq hfresh hs hdef hh ht (by omega)

theorem subsetSumIntervalInsert {D : Finset ℕ} {v a b : ℕ} (hv : v ∉ D)
    (hcover : ∀ x, a ≤ x → x ≤ b → ∃ t ⊆ D, ∑ d ∈ t, d = x)
    (htouch : a + v ≤ b + 1) :
    ∀ x, a ≤ x → x ≤ b + v → ∃ t ⊆ insert v D, ∑ d ∈ t, d = x := by
  intro x ha hb
  by_cases hx : x ≤ b
  · obtain ⟨t, ht, hs⟩ := hcover x ha hx
    exact ⟨t, ht.trans (Finset.subset_insert v D), hs⟩
  · obtain ⟨t, ht, hs⟩ := hcover (x - v) (by omega) (by omega)
    refine ⟨insert v t, Finset.insert_subset_insert _ ht, ?_⟩
    rw [Finset.sum_insert (fun h => hv (ht h)), hs]
    omega

theorem subsetSumIntervalReflect {D : Finset ℕ} {a b : ℕ}
    (hcover : ∀ x, a ≤ x → x ≤ b → ∃ t ⊆ D, ∑ d ∈ t, d = x)
    (hab : a ≤ b) (hb : b ≤ ∑ d ∈ D, d) :
    ∀ x, (∑ d ∈ D, d) - b ≤ x → x ≤ (∑ d ∈ D, d) - a →
      ∃ t ⊆ D, ∑ d ∈ t, d = x := by
  intro x hlow hhigh
  obtain ⟨t, ht, hs⟩ := hcover ((∑ d ∈ D, d) - x) (by omega) (by omega)
  refine ⟨D \ t, Finset.sdiff_subset, ?_⟩
  have htotal := Finset.sum_sdiff (f := fun d : ℕ => d) ht
  omega

theorem squarefreePseudoperfectOfProperInterval {m q s h a b c : ℕ} (hq : q.Prime)
    (hfresh : ¬ q ∣ m) (hs : (∑ d ∈ m.divisors, d) = s) (hdef : s ≤ 2 * m)
    (hh : h = 0 ∨ h ∈ m.properDivisors) (hc : c = 0 ∨ c = m)
    (hcover : ∀ x, a ≤ x → x ≤ b → ∃ t ⊆ m.properDivisors, ∑ d ∈ t, d = x)
    (hlo : a + c + (2 * m - s + h) * q ≤ s)
    (hhi : s ≤ b + c + (2 * m - s + h) * q) : (m * q).Pseudoperfect := by
  refine squarefreePseudoperfectOfInterval hq hfresh hs hdef hh ?_ hlo hhi
  intro x hx hy
  have hm : m ≠ 0 := fun hm => hfresh (hm ▸ dvd_zero q)
  obtain ⟨t, ht, hsum⟩ := hcover (x - c) (by omega) (by omega)
  have hbase : t ⊆ m.divisors := fun d hd =>
    Nat.mem_divisors.mpr ⟨(Nat.mem_properDivisors.mp (ht hd)).1, hm⟩
  rcases hc with hz | he
  · subst c
    exact ⟨t, hbase, by simpa using hsum⟩
  · subst c
    have hnot : m ∉ t := fun h => (lt_irrefl m) (Nat.mem_properDivisors.mp (ht h)).2
    refine ⟨insert m t, Finset.insert_subset (Nat.mem_divisors.mpr ⟨dvd_rfl, hm⟩) hbase, ?_⟩
    rw [Finset.sum_insert hnot, hsum]
    omega

end OddWeirdSubproblems

namespace OddWeirdSubproblems

theorem close_jump_next {ss : List Slot} {p stop r : ℕ}
    (hskip : (⟨ss, stop, r + 1⟩ : Box).Closed)
    (htake : ∀ q, p ≤ q → q < stop → q.Prime → Odd q →
      (⟨ss ++ [⟨q, 1, false⟩], q + 2, r⟩ : Box).Closed) :
    (⟨ss, p, r + 1⟩ : Box).Closed := by
  intro xs ys ⟨hx, hy, hlen⟩ hcoord hw hprim
  cases ys with
  | nil => simp at hlen
  | cons y ys =>
    obtain ⟨q, e⟩ := y
    obtain ⟨hpq, hqlo, hq, hqodd, he, ht⟩ := hy
    by_cases hqcut : q < stop
    · have hfit : Slot.Fits ⟨q, 1, false⟩ (q, e) :=
        ⟨hq, rfl, he, by simp⟩
      have eq : xs ++ (q, e) :: ys = (xs ++ [(q, e)]) ++ ys := by simp [List.append_assoc]
      rw [eq] at hcoord hw hprim
      exact htake q hpq hqcut hq hqodd (xs ++ [(q, e)]) ys
        ⟨List.rel_append hx (.cons hfit .nil), ht, by simpa using hlen⟩ hcoord hw hprim
    · exact hskip xs ((q, e) :: ys)
        ⟨hx, ⟨Nat.le_of_not_gt hqcut, hqlo, hq, hqodd, he, ht⟩, hlen⟩ hcoord hw hprim

theorem close_squarefree_interval
    {ss : List Slot} {q next : ℕ} {m s h a b c : ℕ}
    (hm : number (ss.map Slot.minimum) = m)
    (hs : divisorSum (ss.map Slot.minimum) = s)
    (hdef : s ≤ 2 * m)
    (hh : h = 0 ∨ (h ∣ m ∧ h < m)) (hc : c = 0 ∨ c = m)
    (hcover : ∀ x, a ≤ x → x ≤ b → ∃ t ⊆ m.properDivisors, ∑ d ∈ t, d = x)
    (hlo : a + c + (2 * m - s + h) * q ≤ s)
    (hhi : s ≤ b + c + (2 * m - s + h) * q)
    (hnd : (2 * m - s) * q ≤ s) :
    (⟨ss ++ [⟨q, 1, false⟩], next, 0⟩ : Box).Closed := by
  let box : Box := ⟨ss ++ [⟨q, 1, false⟩], next, 0⟩
  intro xs ys hmatch hvalid hw hprim
  have hminimum : PrimeCoordinates box.minimum :=
    minimum_valid hmatch.1 (primeCoordinates_left hvalid)
  have hcoords : box.minimum = ss.map Slot.minimum ++ [(q, 1)] := by
    simp [box, Box.minimum, Slot.minimum]
  rw [hcoords] at hminimum
  have hq : q.Prime := hminimum.1 (q, 1) (by simp)
  have hqcop : q.Coprime m := by
    rw [← hm]
    apply Nat.coprime_list_prod_right_iff.mpr
    intro w hw
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hw
    have hyq := (List.pairwise_append.mp hminimum.2).2.2 y hy (q, 1) (by simp)
    rw [← pow_one q]
    exact Nat.coprime_pow_primes _ _ hq (hminimum.1 y (List.mem_append_left _ hy)) (Ne.symm hyq.ne)
  have hsum : ∑ d ∈ m.divisors, d = s := by
    rw [← hm, ← divisorSum_eq (primeCoordinates_left hminimum), hs]
  have hnot : ¬ q ∣ m := hq.coprime_iff_not_dvd.mp hqcop
  have hpp : (m * q).Pseudoperfect := squarefreePseudoperfectOfProperInterval hq hnot
    hsum hdef (hh.imp_right Nat.mem_properDivisors.mpr) hc hcover hlo hhi
  have hn : number box.minimum = m * q := by
    rw [hcoords, number_append, hm]
    simp [number]
  have hd : 2 * number box.minimum ≤ divisorSum box.minimum := by
    rw [divisorSum_eq (hcoords.symm ▸ hminimum), hn]
    have he := squarefreeExcess hq hnot hsum hdef
    omega
  exact close_at_nondeficient_minimum hd (Or.inr (Or.inl (hn.symm ▸ hpp)))
    xs ys hmatch hvalid hw hprim

theorem close_nondeficient_squarefree_prefix {ss : List Slot} {q next r : ℕ}
    (hr : 0 < r)
    (hnondef : 2 * number (ss.map Slot.minimum) * q ≤
      divisorSum (ss.map Slot.minimum) * (1 + q)) :
    (⟨ss ++ [⟨q, 1, false⟩], next, r⟩ : Box).Closed := by
  apply close_minimum_with_tail (b := ⟨ss ++ [({ prime := q, exponent := 1, fixed := false } : Slot)], next, r⟩) hr
  change 2 * number ((ss ++ [({ prime := q, exponent := 1, fixed := false } : Slot)]).map Slot.minimum) ≤
    divisorSum ((ss ++ [({ prime := q, exponent := 1, fixed := false } : Slot)]).map Slot.minimum)
  rw [List.map_append, number_append, divisorSum_append, ← Nat.mul_assoc]
  simpa [Slot.minimum, number, divisorSum, powerSum] using hnondef

def HeadRangeClosed (ss : List Slot) (r lo hi : ℕ) : Prop :=
  ∀ q, lo ≤ q → q < hi → q.Prime → Odd q →
    (⟨ss ++ [⟨q, 1, false⟩], q + 2, r⟩ : Box).Closed

theorem headRange_join {ss : List Slot} {r lo mid hi : ℕ}
    (h₁ : HeadRangeClosed ss r lo mid) (h₂ : HeadRangeClosed ss r mid hi) :
    HeadRangeClosed ss r lo hi := by
  intro q hqlo hqhi hp ho
  by_cases h : q < mid
  · exact h₁ q hqlo h hp ho
  · exact h₂ q (Nat.le_of_not_gt h) hqhi hp ho

theorem headRange_single {ss : List Slot} {r q : ℕ}
    (h : q.Prime → Odd q → (⟨ss ++ [⟨q, 1, false⟩], q + 2, r⟩ : Box).Closed) :
    HeadRangeClosed ss r q (q + 1) := by
  intro p hlo hhi hp ho
  have e : p = q := by omega
  subst p
  exact h hp ho

theorem headRange_squarefree {ss : List Slot} {m s h a b c lo hi : ℕ}
    (hm : number (ss.map Slot.minimum) = m)
    (hs : divisorSum (ss.map Slot.minimum) = s)
    (hdef : s ≤ 2 * m)
    (hh : h = 0 ∨ (h ∣ m ∧ h < m)) (hc : c = 0 ∨ c = m)
    (hcover : ∀ x, a ≤ x → x ≤ b → ∃ t ⊆ m.properDivisors, ∑ d ∈ t, d = x)
    (hlow : s ≤ b + c + (2 * m - s + h) * lo)
    (hhigh : a + c + (2 * m - s + h) * (hi - 1) ≤ s) :
    HeadRangeClosed ss 0 lo hi := by
  intro q hqlo hqhi _ _
  have hu : q ≤ hi - 1 := by omega
  have ha := Nat.mul_le_mul_left (2 * m - s + h) hu
  have hb := Nat.mul_le_mul_left (2 * m - s + h) hqlo
  have hc' := Nat.mul_le_mul_right q (show 2 * m - s ≤ 2 * m - s + h by omega)
  exact close_squarefree_interval hm hs hdef hh hc hcover (by omega) (by omega) (by omega)

theorem decrement_append_left {xs ys : Coordinates} {i : ℕ} (hi : i < xs.length) :
    decrement (xs ++ ys) i = decrement xs i ++ ys := by
  induction xs generalizing i with
  | nil => simp at hi
  | cons x xs ih =>
    rcases x with ⟨p, e⟩
    cases i with
    | zero => rfl
    | succ i =>
      have hi' : i < xs.length := by simpa using hi
      simp [decrement, ih hi']

theorem product_after_head (ss : List Slot) (q : ℕ) :
    number ((ss ++ [({ prime := q, exponent := 1, fixed := false } : Slot)]).map Slot.minimum)
    = number (ss.map Slot.minimum) * q := by
  rw [List.map_append, number_append]
  simp [number, Slot.minimum]

theorem headRange_decrement_nondeficient {ss : List Slot} {r lo hi i z t : ℕ}
    (hi' : i < ss.length)
    (hz : number (decrement (ss.map Slot.minimum) i) = z)
    (ht : divisorSum (decrement (ss.map Slot.minimum) i) = t)
    (hzlt : z < number (ss.map Slot.minimum))
    (hcut : (2 * z - t) * (hi - 1) ≤ t) :
    HeadRangeClosed ss r lo hi := by
  intro q _ hqhi hq _
  let b : Box := ⟨ss ++ [⟨q, 1, false⟩], q + 2, r⟩
  intro xs ys hfit hcoord hw hprim
  have hv : PrimeCoordinates b.minimum :=
    minimum_valid hfit.1 (primeCoordinates_left hcoord)
  have hminimum : b.minimum = ss.map Slot.minimum ++ [(q, 1)] := by
    simp [b, Box.minimum, Slot.minimum]
  have hcut' : 2 * (z * q) ≤ t * (1 + q) := by
    have hq' : q ≤ hi - 1 := by omega
    have h₁ := (Nat.mul_le_mul_left (2 * z - t) hq').trans hcut
    have h₂ := Nat.mul_le_mul_right q (show 2 * z ≤ 2 * z - t + t by omega)
    rw [Nat.add_mul] at h₂
    rw [← Nat.mul_assoc, Nat.mul_add]
    simp only [Nat.mul_one]
    omega
  have hdcoords : decrement b.minimum i = decrement (ss.map Slot.minimum) i ++ [(q, 1)] := by
    rw [hminimum, decrement_append_left (by simpa using hi')]
  have hdn : number (decrement b.minimum i) = z * q := by
    rw [hdcoords, number_append, hz]
    simp [number]
  have hds : divisorSum (decrement b.minimum i) = t * (1 + q) := by
    rw [hdcoords, divisorSum_append, ht]
    simp [divisorSum, powerSum]
  have hdnd : ¬ (number (decrement b.minimum i)).Deficient := by
    rw [deficient_iff_divisorSum_lt (decrement_coordinates hv i), hdn, hds]
    exact hcut'.not_gt
  have hdnlt : number (decrement b.minimum i) < number b.minimum := by
    rw [hdn, show number b.minimum = _ from product_after_head ss q]
    exact Nat.mul_lt_mul_of_pos_right hzlt hq.pos
  have hminDvd : number b.minimum ∣ number (xs ++ ys) := by
    rw [number_append]
    exact dvd_mul_of_dvd_left (minimum_dvd hfit.1) _
  have hdvd := (decrement_dvd b.minimum i).trans hminDvd
  have hlt := hdnlt.trans_le (Nat.le_of_dvd hw.1.pos hminDvd)
  exact hdnd (hprim _ (Nat.mem_properDivisors.mpr ⟨hdvd, hlt⟩))

end OddWeirdSubproblems

namespace OddWeirdSubproblems

theorem closeBelow_jump_next {ss : List Slot} {B p stop r : ℕ}
    (hskip : (⟨ss, stop, r + 1⟩ : Box).ClosedBelow B)
    (htake : ∀ q, p ≤ q → q < stop → q.Prime → Odd q →
      (⟨ss ++ [⟨q, 1, false⟩], q + 2, r⟩ : Box).ClosedBelow B) :
    (⟨ss, p, r + 1⟩ : Box).ClosedBelow B := by
  intro xs ys ⟨hx, hy, hlen⟩ hcoord hsize hw hprim
  cases ys with
  | nil => simp at hlen
  | cons y ys =>
    obtain ⟨q, e⟩ := y
    obtain ⟨hpq, hqlo, hq, hqodd, he, ht⟩ := hy
    by_cases hqcut : q < stop
    · have hfit : Slot.Fits ⟨q, 1, false⟩ (q, e) := ⟨hq, rfl, he, by simp⟩
      have hsplit : xs ++ (q, e) :: ys = (xs ++ [(q, e)]) ++ ys := by simp [List.append_assoc]
      rw [hsplit] at hcoord hsize hw hprim
      exact htake q hpq hqcut hq hqodd (xs ++ [(q, e)]) ys
        ⟨List.rel_append hx (.cons hfit .nil), ht, by simpa using hlen⟩ hcoord hsize hw hprim
    · exact hskip xs ((q, e) :: ys)
        ⟨hx, ⟨Nat.le_of_not_gt hqcut, hqlo, hq, hqodd, he, ht⟩, hlen⟩ hcoord hsize hw hprim

end OddWeirdSubproblems

namespace OddWeirdSubproblems

def RankFloor : List ℕ → Coordinates → Prop
  | [], _ => True
  | _ :: _, [] => True
  | p :: ps, x :: xs => p ≤ x.1 ∧ RankFloor ps xs

theorem tailFits_weaken {p q : ℕ} {xs : Coordinates} (hp : p ≤ q) (h : TailFits q xs) :
    TailFits p xs := by
  cases xs with
  | nil => trivial
  | cons x xs =>
    obtain ⟨r, e⟩ := x
    obtain ⟨hlo, hpos, hprime, hodd, he, ht⟩ := h
    exact ⟨hp.trans hlo, hpos, hprime, hodd, he, ht⟩

theorem number_ge_floor_product {ps : List ℕ} {xs : Coordinates}
    (hr : RankFloor ps xs) (hlen : ps.length ≤ xs.length)
    (hp : ∀ x ∈ xs, x.1.Prime ∧ 0 < x.2) : ps.prod ≤ number xs := by
  induction ps generalizing xs with
  | nil => exact number_pos (fun x hx => (hp x hx).1)
  | cons p ps ih =>
    cases xs with
    | nil => simp at hlen
    | cons x xs =>
      obtain ⟨q, e⟩ := x
      obtain ⟨hle, ht⟩ := hr
      obtain ⟨hq, he⟩ := hp (q, e) (by simp)
      have hpq : p ≤ q ^ e := hle.trans (by
        simpa using Nat.pow_le_pow_right hq.pos (show 1 ≤ e by omega))
      exact Nat.mul_le_mul hpq
        (ih ht (by simpa using hlen) (fun y hy => hp y (List.mem_cons_of_mem _ hy)))

theorem one_le_limitingIndex {p : ℕ} (hp : 1 < p) : 1 ≤ limitingIndex p := by
  have hp' : (1 : ℚ) < p := by exact_mod_cast hp
  unfold limitingIndex
  rw [le_div_iff₀ (sub_pos.mpr hp')]
  linarith

theorem floorIndex_ge_one {ps : List ℕ} (hp : ∀ p ∈ ps, 1 < p) :
    1 ≤ (ps.map limitingIndex).prod := by
  induction ps with
  | nil => simp
  | cons p ps ih =>
    simp only [List.map_cons, List.prod_cons]
    exact one_le_mul_of_one_le_of_one_le (one_le_limitingIndex (hp p (by simp)))
      (ih (fun q hq => hp q (by simp [hq])))

theorem floorIndex_upper {ps : List ℕ} {xs : Coordinates}
    (hr : RankFloor ps xs) (hlen : xs.length ≤ ps.length)
    (hp : ∀ p ∈ ps, 1 < p) :
    (xs.map fun x => index x.1 x.2).prod ≤ (ps.map limitingIndex).prod := by
  induction ps generalizing xs with
  | nil =>
    have hn : xs = [] := by simpa using hlen
    simp [hn]
  | cons p ps ih =>
    cases xs with
    | nil => exact floorIndex_ge_one hp
    | cons x xs =>
      obtain ⟨q, e⟩ := x
      obtain ⟨hpq, ht⟩ := hr
      have hp' := hp p (by simp)
      have hq : 1 < q := hp'.trans_le hpq
      exact mul_le_mul ((index_le_limitingIndex hq).trans (limitingIndex_antitone hp' hpq))
        (ih ht (by simpa using hlen) (fun r hr => hp r (by simp [hr])))
        (coordinate_prod_nonneg _) (limitingIndex_nonneg hp')

end OddWeirdSubproblems

namespace OddWeirdSubproblems

def hasOddFactor (n : ℕ) : ℕ → ℕ → Bool
  | 0, _ => false
  | fuel + 1, d =>
    if n < d * d then false
    else if n % d = 0 then true
    else hasOddFactor n fuel (d + 2)

theorem hasOddFactor_false_of_prime {n : ℕ} (hp : n.Prime) (fuel d : ℕ)
    (hd : 2 ≤ d) : hasOddFactor n fuel d = false := by
  induction fuel generalizing d with
  | zero => rfl
  | succ fuel ih =>
    rw [hasOddFactor]
    split
    · rfl
    · next h =>
      have hlt : d < n := by
        have h₂ := Nat.mul_le_mul_right d hd
        omega
      have hmod : n % d ≠ 0 := by
        intro hmod
        rcases (Nat.dvd_prime hp).mp (Nat.dvd_of_mod_eq_zero hmod) with h₁ | hn
        · omega
        · omega
      exact (if_neg hmod).trans (ih (d + 2) (by omega))

def mayBeOddPrime (n : ℕ) : Bool := !hasOddFactor n n 3

theorem mayBeOddPrime_of_prime {n : ℕ} (hp : n.Prime) : mayBeOddPrime n = true := by
  simp [mayBeOddPrime, hasOddFactor_false_of_prime hp]

end OddWeirdSubproblems

namespace OddWeirdSubproblems

def firstAllowedOdd (p : ℕ) : ℕ → ℕ
  | 0 => p
  | fuel + 1 => if mayBeOddPrime p then p else firstAllowedOdd (p + 2) fuel

theorem firstAllowedOdd_ge (p fuel : ℕ) : p ≤ firstAllowedOdd p fuel := by
  induction fuel generalizing p with
  | zero => rfl
  | succ fuel ih =>
    rw [firstAllowedOdd]
    split
    · rfl
    · exact (Nat.le_add_right _ _).trans (ih _)

theorem firstAllowedOdd_odd {p : ℕ} (hp : Odd p) (fuel : ℕ) : Odd (firstAllowedOdd p fuel) := by
  induction fuel generalizing p with
  | zero => exact hp
  | succ fuel ih =>
    rw [firstAllowedOdd]
    split
    · exact hp
    · exact ih (by obtain ⟨k, hk⟩ := hp; exact ⟨k + 1, by omega⟩)

theorem firstAllowedOdd_le_prime {p q : ℕ} (hp : Odd p) (hq : Odd q)
    (hprime : q.Prime) (hle : p ≤ q) (fuel : ℕ) : firstAllowedOdd p fuel ≤ q := by
  induction fuel generalizing p with
  | zero => exact hle
  | succ fuel ih =>
    rw [firstAllowedOdd]
    split
    · exact hle
    · next h =>
      have hneq : p ≠ q := by
        intro he
        subst q
        exact h (mayBeOddPrime_of_prime hprime)
      obtain ⟨a, ha⟩ := hp
      obtain ⟨b, hb⟩ := hq
      exact ih ⟨a + 1, by omega⟩ (by omega)

def tailPrimeFloor (p : ℕ) : ℕ → List ℕ
  | 0 => []
  | r + 1 =>
    let q := firstAllowedOdd p 32
    q :: tailPrimeFloor (q + 2) r

theorem tailPrimeFloor_length (p r : ℕ) : (tailPrimeFloor p r).length = r := by
  induction r generalizing p with
  | zero => rfl
  | succ r ih => simp only [tailPrimeFloor, List.length_cons, ih]

theorem tailPrimeFloor_gt_one {p : ℕ} (hp : 1 < p) (r : ℕ) :
    ∀ q ∈ tailPrimeFloor p r, 1 < q := by
  induction r generalizing p with
  | zero => simp [tailPrimeFloor]
  | succ r ih =>
    intro q hq
    rcases List.mem_cons.mp hq with rfl | hq
    · exact hp.trans_le (firstAllowedOdd_ge _ _)
    · apply ih (hp.trans_le ((firstAllowedOdd_ge _ _).trans (Nat.le_add_right _ _))) _ hq

theorem tailPrimeFloor_correct {p : ℕ} (hp : Odd p) {xs : Coordinates} (ht : TailFits p xs)
    (r : ℕ) : RankFloor (tailPrimeFloor p r) xs := by
  induction r generalizing p xs with
  | zero => trivial
  | succ r ih =>
    cases xs with
    | nil => trivial
    | cons x xs =>
      obtain ⟨q, e⟩ := x
      obtain ⟨hlo, _, hprime, hodd, _, ht'⟩ := ht
      have hfirst := firstAllowedOdd_le_prime hp hodd hprime hlo 32
      have hodd' : Odd (firstAllowedOdd p 32 + 2) := by
        obtain ⟨k, hk⟩ := firstAllowedOdd_odd hp 32
        exact ⟨k + 1, by omega⟩
      exact ⟨hfirst, ih hodd' (tailFits_weaken (by omega) ht')⟩

private theorem tailFits_prime_pos {p : ℕ} {xs : Coordinates} (ht : TailFits p xs) :
    ∀ x ∈ xs, x.1.Prime ∧ 0 < x.2 := by
  induction xs generalizing p with
  | nil => simp
  | cons x xs ih =>
    obtain ⟨q, e⟩ := x
    obtain ⟨_, _, hq, _, he, htail⟩ := ht
    intro y hy
    rcases List.mem_cons.mp hy with rfl | hy
    · exact ⟨hq, he⟩
    · exact ih htail y hy

theorem tailPrimeFloor_product_le {p : ℕ} (hp : Odd p) {xs : Coordinates} (ht : TailFits p xs)
    {r : ℕ} (hr : r ≤ xs.length) : (tailPrimeFloor p r).prod ≤ number xs := by
  exact number_ge_floor_product (tailPrimeFloor_correct hp ht _)
    (by simpa only [tailPrimeFloor_length] using hr) (tailFits_prime_pos ht)

theorem closeBelow_of_ranked_minimum_ge {b : Box} {B : ℕ} (hodd : Odd b.next)
    (hB : B ≤ number b.minimum * (tailPrimeFloor b.next b.remaining).prod) : b.ClosedBelow B := by
  intro xs ys ⟨hf, ht, hy⟩ hcoord hlt _ _
  have hx := Nat.le_of_dvd (number_pos (primeCoordinates_left hcoord).1) (minimum_dvd hf)
  have hy' := tailPrimeFloor_product_le hodd ht hy.ge
  rw [number_append] at hlt
  exact hlt.not_ge (hB.trans (Nat.mul_le_mul hx hy'))

def rankedUpperNum (b : Box) : ℕ :=
  (b.slots.map Slot.upperNum).prod * (tailPrimeFloor b.next b.remaining).prod

def rankedUpperDen (b : Box) : ℕ :=
  (b.slots.map Slot.upperDen).prod * ((tailPrimeFloor b.next b.remaining).map (· - 1)).prod

private theorem ranked_indices_eq {ps : List ℕ} (h : ∀ p ∈ ps, 1 < p) :
    (ps.map limitingIndex).prod = (ps.prod : ℚ) / (((ps.map (· - 1)).prod : ℕ) : ℚ) := by
  induction ps with
  | nil => simp
  | cons p ps ih =>
    have hp : 1 ≤ p := (h p (by simp)).le.trans (by omega)
    simp only [List.map_cons, List.prod_cons, Nat.cast_mul]
    rw [ih (fun q hq => h q (by simp [hq])), ← div_mul_div_comm, limitingIndex, Nat.cast_sub hp]
    simp

private theorem ranked_floor_den_pos {ps : List ℕ} (h : ∀ p ∈ ps, 1 < p) :
    0 < (ps.map (· - 1)).prod := by
  induction ps with
  | nil => decide
  | cons p ps ih =>
    have hp := h p (by simp)
    exact Nat.mul_pos (by omega : 0 < p - 1) (ih (fun q hq => h q (by simp [hq])))

theorem close_of_ranked_upper {b : Box} (hnext : 1 < b.next) (hodd : Odd b.next)
    (hbound : rankedUpperNum b ≤ 2 * rankedUpperDen b) : b.Closed := by
  intro xs ys ⟨hslots, htail, hlen⟩ hvalid hw _
  let ps := tailPrimeFloor b.next b.remaining
  have hp : ∀ q ∈ ps, 1 < q := tailPrimeFloor_gt_one hnext _
  have hslot (s : Slot) (hs : s ∈ b.slots) : 1 < s.prime := by
    obtain ⟨x, _, hx⟩ := exists_fit_of_mem hslots hs
    rw [hx.2.1]
    exact hx.1.one_lt
  have hden : 0 < rankedUpperDen b := Nat.mul_pos (slot_den_pos hslot) (ranked_floor_den_pos hp)
  have hupper : (b.slots.map Slot.upper).prod * (ps.map limitingIndex).prod ≤ 2 := by
    rw [slot_upper_eq hslot, ranked_indices_eq hp, div_mul_div_comm, ← Nat.cast_mul, ← Nat.cast_mul]
    change (rankedUpperNum b : ℚ) / (rankedUpperDen b : ℚ) ≤ 2
    rw [div_le_iff₀ (by exact_mod_cast hden)]
    exact_mod_cast hbound
  have hrat := floorIndex_upper (tailPrimeFloor_correct hodd htail b.remaining)
    (by simpa only [tailPrimeFloor_length] using hlen.le) hp
  have hle : ((xs ++ ys).map (fun x => index x.1 x.2)).prod ≤ 2 := by
    rw [List.map_append, List.prod_append]
    exact (mul_le_mul (slot_prod_upper hslots) hrat (coordinate_prod_nonneg _)
      ((coordinate_prod_nonneg _).trans (slot_prod_upper hslots))).trans hupper
  rw [coordinate_index_eq, divisorSum_eq hvalid, ← Nat.abundancyIndex] at hle
  exact (Nat.abundant_iff_two_lt_abundancyIndex.mp hw.1).not_ge hle

end OddWeirdSubproblems

namespace OddWeirdSubproblems

theorem closeBelow_fix_slot_of_size {b : Box} {B i : ℕ} {s : Slot}
    (hi : b.slots[i]? = some s) (hf : s.fixed = false) (hodd : Odd b.next)
    (hB : B ≤ number ({b with slots := b.slots.set i {s with exponent := s.exponent + 1}} : Box).minimum *
      (tailPrimeFloor b.next b.remaining).prod)
    (hfixed : ({b with slots := b.slots.set i {s with fixed := true}} : Box).ClosedBelow B) :
    b.ClosedBelow B :=
  closeBelow_split_slot hi hf hfixed (closeBelow_of_ranked_minimum_ge hodd hB)

def sizeFixedSlot (B : ℕ) (b : Box) : Option (ℕ × Slot) :=
  let floor := (tailPrimeFloor b.next b.remaining).prod
  ((List.range b.slots.length).filterMap fun i => b.slots[i]?.map fun s => (i, s)).find?
    fun (i, s) => !s.fixed &&
      decide (B ≤ number ({b with slots := b.slots.set i {s with exponent := s.exponent + 1}} : Box).minimum * floor)

theorem sizeFixedSlot_closes {B i : ℕ} {b : Box} {s : Slot}
    (h : sizeFixedSlot B b = some (i, s)) (hodd : Odd b.next)
    (hfixed : ({b with slots := b.slots.set i {s with fixed := true}} : Box).ClosedBelow B) :
    b.ClosedBelow B := by
  unfold sizeFixedSlot at h
  have hmem := List.find?_some h
  have hprune := List.mem_of_find?_eq_some h
  obtain ⟨j, _, hslot⟩ := List.mem_filterMap.mp hprune
  obtain ⟨u, hu, he⟩ := Option.map_eq_some_iff.mp hslot
  cases he
  simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq] at hmem
  exact closeBelow_fix_slot_of_size hu hmem.1 hodd hmem.2 hfixed

end OddWeirdSubproblems

namespace OddWeirdSubproblems

open Finset

def exponentBudget (B : ℕ) (b : Box) : ℕ :=
  (B - 1) / (number b.minimum * (tailPrimeFloor b.next b.remaining).prod)

private def floorSlot (p : ℕ) : Slot := ⟨p, 1, false⟩

private def exponentCapSlot (R : ℕ) (s : Slot) : ℕ × ℕ :=
  (s.prime, if s.fixed then s.exponent else s.exponent + Nat.log s.prime R)

def exponentCapCoordinates (B : ℕ) (b : Box) : Coordinates :=
  ((b.slots ++ (tailPrimeFloor b.next b.remaining).map floorSlot).map
    (exponentCapSlot (exponentBudget B b)))

def exponentCapOk (B : ℕ) (b : Box) : Bool :=
  let cs := exponentCapCoordinates B b
  decide (divisorSum cs ≤ 2 * number cs)

private theorem index_succ_of_pos {p e : ℕ} (hp : 0 < p) :
    index p (e + 1) = index p e + 1 / (p : ℚ) ^ (e + 1) := by
  have hsum : powerSum p (e + 1) = p * powerSum p e + 1 := by
    simp only [powerSum_eq_sum]
    exact geom_sum_succ
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast hp.ne'
  unfold index
  rw [hsum, Nat.cast_add, Nat.cast_mul, Nat.cast_one, add_div, pow_succ',
    mul_div_mul_left _ _ hp0]

private theorem index_mono_exponent {p : ℕ} (hp : 0 < p) : Monotone (index p) := by
  apply monotone_nat_of_le_succ
  intro e
  rw [index_succ_of_pos hp]
  exact le_add_of_nonneg_right (by positivity)

private theorem index_antitone_base {p q : ℕ} (hp : 0 < p) (hpq : p ≤ q) (e : ℕ) :
    index q e ≤ index p e := by
  induction e with
  | zero => simp [index, powerSum]
  | succ e ih =>
    rw [index_succ_of_pos hp, index_succ_of_pos (hp.trans_le hpq)]
    have hpR : (0 : ℚ) < p := by exact_mod_cast hp
    have hpqR : (p : ℚ) ≤ q := by exact_mod_cast hpq
    exact add_le_add ih (one_div_le_one_div_of_le (pow_pos hpR _)
      (pow_le_pow_left₀ hpR.le hpqR _))

private def NumericalFit (s : Slot) (x : ℕ × ℕ) : Prop :=
  1 < s.prime ∧ s.prime ≤ x.1 ∧ s.exponent ≤ x.2 ∧ (s.fixed = true → s.exponent = x.2)

private theorem numericalFit_of_slotFits {ss : List Slot} {xs : Coordinates}
    (h : List.Forall₂ Slot.Fits ss xs) : List.Forall₂ NumericalFit ss xs := by
  apply h.imp
  intro s x hx
  obtain ⟨hp, hq, he, hfix⟩ := hx
  exact ⟨hq ▸ hp.one_lt, hq.le, he, hfix⟩

private theorem numericalFit_of_rankFloor {ps : List ℕ} {xs : Coordinates} {p : ℕ}
    (hr : RankFloor ps xs) (hl : ps.length = xs.length)
    (hps : ∀ q ∈ ps, 1 < q) (ht : TailFits p xs) :
    List.Forall₂ NumericalFit (ps.map floorSlot) xs := by
  induction ps generalizing xs p with
  | nil =>
    have hx : xs = [] := List.length_eq_zero_iff.mp hl.symm
    subst xs
    exact .nil
  | cons q ps ih =>
    cases xs with
    | nil => simp at hl
    | cons x xs =>
      obtain ⟨t, e⟩ := x
      obtain ⟨hle, htail⟩ := hr
      obtain ⟨_, _, _, _, he, ht'⟩ := ht
      exact .cons ⟨hps q (by simp), hle, he, by simp [floorSlot]⟩
        (ih htail (by simpa using hl) (fun q' hq' => hps q' (List.mem_cons_of_mem _ hq')) ht')

private theorem numericalFit_pow_le {s : Slot} {x : ℕ × ℕ} (h : NumericalFit s x) :
    s.prime ^ s.exponent ≤ x.1 ^ x.2 :=
  (Nat.pow_le_pow_right (Nat.zero_lt_one.trans h.1) h.2.2.1).trans
    (Nat.pow_le_pow_left h.2.1 _)

private theorem numericalFit_minimum_pos_le {ss : List Slot} {xs : Coordinates}
    (h : List.Forall₂ NumericalFit ss xs) :
    0 < number (ss.map Slot.minimum) ∧ number (ss.map Slot.minimum) ≤ number xs := by
  induction h with
  | nil => exact ⟨Nat.one_pos, le_rfl⟩
  | @cons s x ss xs hx _ ih =>
    simp only [List.map_cons, number_cons, Slot.minimum]
    exact ⟨Nat.mul_pos (pow_pos (Nat.zero_lt_one.trans hx.1) _) ih.1,
      Nat.mul_le_mul (numericalFit_pow_le hx) ih.2⟩

private theorem numericalFit_cap {ss : List Slot} {xs : Coordinates} {R : ℕ}
    (h : List.Forall₂ NumericalFit ss xs)
    (hsize : number xs < number (ss.map Slot.minimum) * (R + 1)) :
    List.Forall₂ (fun s x => NumericalFit s x ∧ x.2 ≤ (exponentCapSlot R s).2) ss xs := by
  induction h with
  | nil => exact .nil
  | @cons s x ss xs hx ht ih =>
    simp only [List.map_cons, number_cons, Slot.minimum] at hsize
    have htail := numericalFit_minimum_pos_le ht
    have hp : 0 < s.prime := Nat.zero_lt_one.trans hx.1
    have hsizeTail : number xs < number (ss.map Slot.minimum) * (R + 1) := by
      apply Nat.lt_of_mul_lt_mul_left (a := s.prime ^ s.exponent)
      rw [← Nat.mul_assoc]
      exact (Nat.mul_le_mul_right _ (numericalFit_pow_le hx)).trans_lt hsize
    have hpower : s.prime ^ (x.2 - s.exponent) ≤ R := by
      by_contra! hh
      have hmul : (s.prime ^ s.exponent * number (ss.map Slot.minimum)) *
          s.prime ^ (x.2 - s.exponent) ≤ x.1 ^ x.2 * number xs := by
        calc
          _ = s.prime ^ x.2 * number (ss.map Slot.minimum) := by
            rw [mul_right_comm, ← pow_add, Nat.add_sub_of_le hx.2.2.1]
          _ ≤ _ := Nat.mul_le_mul (Nat.pow_le_pow_left hx.2.1 _) htail.2
      exact hsize.not_ge ((Nat.mul_le_mul_left _ (Nat.succ_le_of_lt hh)).trans hmul)
    have he : x.2 ≤ (exponentCapSlot R s).2 := by
      cases hf : s.fixed
      · have hh := Nat.le_log_of_pow_le hx.1 hpower
        simp only [exponentCapSlot, hf, Bool.false_eq_true, if_false]
        have hle := hx.2.2.1
        omega
      · simp [exponentCapSlot, hf, hx.2.2.2 hf]
    exact .cons ⟨hx, he⟩ (ih hsizeTail)

private theorem indices_le_exponentCap {ss : List Slot} {xs : Coordinates} {R : ℕ}
    (h : List.Forall₂ (fun s x => NumericalFit s x ∧ x.2 ≤ (exponentCapSlot R s).2) ss xs) :
    (xs.map (fun x => index x.1 x.2)).prod ≤
      ((ss.map (exponentCapSlot R)).map (fun x => index x.1 x.2)).prod := by
  induction h with
  | nil => simp
  | @cons s x ss xs hx _ ih =>
    have hp : 0 < s.prime := Nat.zero_lt_one.trans hx.1.1
    have hhead : index x.1 x.2 ≤ index (exponentCapSlot R s).1 (exponentCapSlot R s).2 :=
      (index_antitone_base hp hx.1.2.1 _).trans (index_mono_exponent hp hx.2)
    simp only [List.map_cons, List.prod_cons]
    exact mul_le_mul hhead ih (coordinate_prod_nonneg xs) (index_nonneg _ _)

private theorem match_capped_numericalFit {b : Box} {B : ℕ} {xs ys : Coordinates}
    (hnext : 1 < b.next) (hodd : Odd b.next) (hmatch : b.Matches xs ys)
    (hsize : number (xs ++ ys) < B) :
    List.Forall₂ (fun s x => NumericalFit s x ∧ x.2 ≤ (exponentCapSlot (exponentBudget B b) s).2)
      (b.slots ++ (tailPrimeFloor b.next b.remaining).map floorSlot) (xs ++ ys) := by
  obtain ⟨hslots, ht, hl⟩ := hmatch
  let ps := tailPrimeFloor b.next b.remaining
  let ss := b.slots ++ ps.map floorSlot
  let A := number b.minimum * ps.prod
  let R := exponentBudget B b
  have hfit : List.Forall₂ NumericalFit ss (xs ++ ys) :=
    List.rel_append (numericalFit_of_slotFits hslots)
      (numericalFit_of_rankFloor (tailPrimeFloor_correct hodd ht b.remaining)
        ((tailPrimeFloor_length b.next b.remaining).trans hl.symm)
        (tailPrimeFloor_gt_one hnext _) ht)
  have hAeq : number (ss.map Slot.minimum) = A := by
    simp only [ss, A, Box.minimum, List.map_append, number_append]
    congr 1
    induction ps with
    | nil => rfl
    | cons p ps ih => simp only [List.map_cons, number_cons, List.prod_cons, Slot.minimum, floorSlot,
        pow_one, ih]
  have hA : 0 < A := hAeq ▸ (numericalFit_minimum_pos_le hfit).1
  have hnextSize : B - 1 < A * (R + 1) := by
    rw [Nat.mul_comm, ← Nat.div_lt_iff_lt_mul hA]
    exact Nat.lt_succ_self _
  have hR : number (xs ++ ys) < number (ss.map Slot.minimum) * (R + 1) := by
    rw [hAeq]
    omega
  exact numericalFit_cap hfit hR

theorem abundancyIndex_le_exponentCap_of_matches_below {b : Box} {B : ℕ} {xs ys : Coordinates}
    (hnext : 1 < b.next) (hodd : Odd b.next) (hmatch : b.Matches xs ys)
    (hcoords : PrimeCoordinates (xs ++ ys)) (hsize : number (xs ++ ys) < B) :
    (number (xs ++ ys)).abundancyIndex ≤
      (divisorSum (exponentCapCoordinates B b) : ℚ) / (number (exponentCapCoordinates B b) : ℚ) := by
  have h := indices_le_exponentCap (match_capped_numericalFit hnext hodd hmatch hsize)
  change _ ≤ ((exponentCapCoordinates B b).map (fun x => index x.1 x.2)).prod at h
  rw [coordinate_index_eq, coordinate_index_eq, divisorSum_eq hcoords, ← Nat.abundancyIndex] at h
  exact h

theorem closeBelow_of_exponentCap {b : Box} {B : ℕ} (hnext : 1 < b.next) (hodd : Odd b.next)
    (hcap : divisorSum (exponentCapCoordinates B b) ≤ 2 * number (exponentCapCoordinates B b)) :
    b.ClosedBelow B := by
  intro xs ys hmatch hcoords hsize hw _
  have h := abundancyIndex_le_exponentCap_of_matches_below hnext hodd hmatch hcoords hsize
  let z := (number (exponentCapCoordinates B b) : ℚ)
  have hz : 0 ≤ z := by positivity
  have hh : (divisorSum (exponentCapCoordinates B b) : ℚ) ≤ 2 * z := by
    dsimp only [z]
    exact_mod_cast hcap
  have hle : (divisorSum (exponentCapCoordinates B b) : ℚ) / z ≤ 2 := by
    refine (div_le_div_of_nonneg_right hh hz).trans ?_
    by_cases h0 : z = 0
    · simp [h0]
    · simp [h0]
  exact (Nat.abundant_iff_two_lt_abundancyIndex.mp hw.1).not_ge (h.trans hle)

theorem exponentCapOk_closes {b : Box} {B : ℕ} (hnext : 1 < b.next) (hodd : Odd b.next)
    (h : exponentCapOk B b = true) : b.ClosedBelow B :=
  closeBelow_of_exponentCap hnext hodd (of_decide_eq_true h)

private def freezeSlot (R : ℕ) (s : Slot) : Slot :=
  {s with fixed := s.fixed || decide (R < s.prime)}

def freezeSizeSlots (B : ℕ) (b : Box) : Box :=
  {b with slots := b.slots.map (freezeSlot (exponentBudget B b))}

private theorem slots_fit_frozen {ss : List Slot} {xs : Coordinates} {R : ℕ}
    (hf : List.Forall₂ Slot.Fits ss xs)
    (hcap : List.Forall₂ (fun s x => NumericalFit s x ∧ x.2 ≤ (exponentCapSlot R s).2) ss xs) :
    List.Forall₂ Slot.Fits (ss.map (freezeSlot R)) xs := by
  induction hf with
  | nil => exact .nil
  | @cons s x ss xs hs _ ih =>
    cases hcap with
    | cons hc hcs =>
      refine .cons ⟨hs.1, hs.2.1, hs.2.2.1, ?_⟩ (ih hcs)
      intro hfix
      change (s.fixed || decide (R < s.prime)) = true at hfix
      obtain hf | hsmall := Bool.or_eq_true_iff.mp hfix
      · exact hs.2.2.2 hf
      · have hlog : Nat.log s.prime R = 0 := Nat.log_of_lt (of_decide_eq_true hsmall)
        apply Nat.le_antisymm hs.2.2.1
        have hre := hc.2
        simp only [exponentCapSlot, hlog, Nat.add_zero, ite_self] at hre
        exact hre

theorem freezeSizeSlots_closes {B : ℕ} {b : Box} (hnext : 1 < b.next) (hodd : Odd b.next)
    (h : (freezeSizeSlots B b).ClosedBelow B) : b.ClosedBelow B := by
  intro xs ys hmatch hcoords hsize hw hproper
  have hslots := List.forall₂_take b.slots.length
    (match_capped_numericalFit hnext hodd hmatch hsize)
  rw [hmatch.1.length_eq] at hslots
  have hx : (b.slots ++ (tailPrimeFloor b.next b.remaining).map floorSlot).take xs.length = b.slots := by
    rw [← hmatch.1.length_eq]
    simp
  rw [hx, List.take_left] at hslots
  exact h xs ys ⟨slots_fit_frozen hmatch.1 hslots, hmatch.2⟩ hcoords hsize hw hproper

end OddWeirdSubproblems

namespace OddWeirdSubproblems

open Finset

def Covered (D : Finset ℕ) (a b : ℕ) : Prop :=
  ∀ x, a ≤ x → x ≤ b → ∃ t ⊆ D, ∑ d ∈ t, d = x

def bitsStep (bits value : ℕ) : ℕ := bits ||| (bits <<< value)

def subsetBits : List ℕ → ℕ
  | [] => 1
  | w :: ws => bitsStep (subsetBits ws) w

theorem testBit_subsetBits {ds : List ℕ} (hnodup : ds.Nodup) {x : ℕ}
    (h : (subsetBits ds).testBit x = true) :
    ∃ t ⊆ ds.toFinset, ∑ d ∈ t, d = x := by
  induction ds generalizing x with
  | nil =>
    have hx : x = 0 := by
      cases x with
      | zero => rfl
      | succ x =>
        change (1 : ℕ).testBit (x + 1) = true at h
        simp [Nat.testBit_succ] at h
    exact ⟨∅, by simp, by simp [hx]⟩
  | cons w ws ih =>
    obtain ⟨hnmem, hnd⟩ := List.nodup_cons.mp hnodup
    simp only [subsetBits, bitsStep, Nat.testBit_or, Nat.testBit_shiftLeft,
      Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
    rcases h with hl | ⟨hlo, hr⟩
    · obtain ⟨t, ht, hs⟩ := ih hnd hl
      exact ⟨t, ht.trans (by simp), hs⟩
    · obtain ⟨t, ht, hs⟩ := ih hnd hr
      have hnot : w ∉ t := fun hmem => hnmem (List.mem_toFinset.mp (ht hmem))
      refine ⟨insert w t, by simpa using Finset.insert_subset_insert w ht, ?_⟩
      rw [sum_insert hnot, hs]
      omega

def bitIntervalOk (ds : List ℕ) (a b : ℕ) : Bool :=
  let mask := 2 ^ (b + 1 - a) - 1
  decide (((subsetBits ds >>> a) &&& mask) = mask)

theorem cover_of_bitIntervalOk {ds : List ℕ} {a b : ℕ}
    (hnodup : ds.Nodup) (h : bitIntervalOk ds a b = true) :
    Covered ds.toFinset a b := by
  intro x hlo hhi
  simp only [bitIntervalOk, decide_eq_true_eq] at h
  have hb := congrArg (fun k : ℕ => k.testBit (x - a)) h
  have hj : x - a < b + 1 - a := by omega
  simp only [Nat.testBit_and, Nat.testBit_shiftRight, Nat.testBit_two_pow_sub_one,
    decide_eq_true hj, Bool.and_true] at hb
  rw [show a + (x - a) = x by omega] at hb
  exact testBit_subsetBits hnodup hb

def growIntervalOk (a : ℕ) : ℕ → List ℕ → Bool
  | _, [] => true
  | b, w :: ws => decide (a + w ≤ b + 1) && growIntervalOk a (b + w) ws

theorem cover_of_growIntervalOk {ds ws : List ℕ} {a b : ℕ}
    (hnodup : (ds ++ ws).Nodup) (hcover : Covered ds.toFinset a b)
    (h : growIntervalOk a b ws = true) :
    Covered (ds ++ ws).toFinset a (b + ws.sum) := by
  induction ws generalizing ds b with
  | nil => simpa using hcover
  | cons w ws ih =>
    simp only [growIntervalOk, Bool.and_eq_true, decide_eq_true_eq] at h
    have heq : ds ++ w :: ws = (ds ++ [w]) ++ ws := by simp [List.append_assoc]
    rw [heq] at hnodup ⊢
    rw [List.sum_cons, ← Nat.add_assoc]
    apply ih hnodup _ h.2
    have hnot : w ∉ ds.toFinset := by
      intro hw
      have hnd : (ds ++ [w]).Nodup := (List.nodup_append.mp hnodup).1
      exact (List.nodup_append.mp hnd).2.2 _ (List.mem_toFinset.mp hw) _ (by simp) rfl
    have heq' : (ds ++ [w]).toFinset = insert w ds.toFinset := by
      ext d
      simp
    rw [heq']
    exact subsetSumIntervalInsert hnot hcover h.1

theorem cover_mono {D E : Finset ℕ} {a b : ℕ} (hDE : D ⊆ E)
    (h : Covered D a b) : Covered E a b := by
  intro x hx hy
  obtain ⟨t, ht, hs⟩ := h x hx hy
  exact ⟨t, ht.trans hDE, hs⟩

def divisorListOk (n : ℕ) (ds : List ℕ) : Bool :=
  tightlySorted ds && ds.all (fun d => decide (d ∣ n ∧ d < n))

theorem divisorListOk_sound {n : ℕ} {ds : List ℕ} (h : divisorListOk n ds = true) :
    ds.Nodup ∧ ds.toFinset ⊆ n.properDivisors := by
  simp only [divisorListOk, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  exact ⟨tightlySorted_nodup h.1, fun d hd => Nat.mem_properDivisors.mpr (h.2 d (List.mem_toFinset.mp hd))⟩

theorem cover_of_validated_growth {n a b : ℕ} {ds ws : List ℕ}
    (hd : divisorListOk n (ds ++ ws) = true)
    (hb : bitIntervalOk ds a b = true) (hg : growIntervalOk a b ws = true) :
    Covered n.properDivisors a (b + ws.sum) := by
  obtain ⟨hnodup, hsub⟩ := divisorListOk_sound hd
  exact cover_mono hsub (cover_of_growIntervalOk hnodup
    (cover_of_bitIntervalOk (List.nodup_append.mp hnodup).1 hb) hg)

theorem sum_toFinset_of_nodup {ds : List ℕ} (h : ds.Nodup) :
    ∑ d ∈ ds.toFinset, d = ds.sum := by
  simpa using List.sum_toFinset (fun x : ℕ => x) h

end OddWeirdSubproblems

namespace OddWeirdSubproblems

def divisorsFromCoordinates : Coordinates → List ℕ
  | [] => [1]
  | (p, e) :: fs =>
    let ds := divisorsFromCoordinates fs
    (List.range (e + 1)).flatMap (fun i => ds.map (fun d => d * p ^ i))

def mergeDivisors : ℕ → List ℕ → List ℕ → List ℕ
  | 0, xs, ys => xs ++ ys
  | _ + 1, [], ys => ys
  | _ + 1, xs, [] => xs
  | fuel + 1, x :: xs, y :: ys =>
    if x ≤ y then x :: mergeDivisors fuel xs (y :: ys)
    else y :: mergeDivisors fuel (x :: xs) ys

def sortDivisors : ℕ → List ℕ → List ℕ
  | 0, ds => ds
  | fuel + 1, ds =>
    if ds.length < 2 then ds
    else
      let mid := ds.length / 2
      mergeDivisors ds.length (sortDivisors fuel (ds.take mid)) (sortDivisors fuel (ds.drop mid))

def sortedDivisors (fs : Coordinates) : List ℕ :=
  sortDivisors 30 (divisorsFromCoordinates fs)

def smallPrefix : ℕ → List ℕ → List ℕ
  | _, [] => []
  | room, d :: ds => if d ≤ room then d :: smallPrefix (room - d) ds else []

def highestPresent : ℕ → ℕ → ℕ → ℕ
  | 0, _, lo => lo
  | fuel + 1, bits, lo =>
    let mid := lo + 2 ^ fuel
    if bits >>> mid = 0 then highestPresent fuel bits lo
    else highestPresent fuel bits mid

def effectiveLow (bits total : ℕ) : ℕ :=
  let mask := 2 ^ (total / 2 + 1) - 1
  let missing := mask ^^^ (mask &&& bits)
  if missing = 0 then 0 else highestPresent 10 missing 0 + 1

def bitWitness : List ℕ → ℕ → List ℕ
  | [], _ => []
  | w :: ws, x =>
    if (subsetBits ws).testBit x then bitWitness ws x
    else w :: bitWitness ws (x - w)

end OddWeirdSubproblems

namespace OddWeirdSubproblems

open Finset

structure IntervalSource where
  kind : ℕ
  low : ℕ
  high : ℕ

structure CoreCoverage where
  proper : List ℕ
  small : List ℕ
  growing : List ℕ
  seedLo : ℕ
  seedHi : ℕ
  central : List IntervalSource

def IntervalSource.ok (n : ℕ) (c : CoreCoverage) (t : IntervalSource) : Bool :=
  if t.kind = 0 then
    divisorListOk n (c.small ++ c.growing) &&
      bitIntervalOk c.small c.seedLo c.seedHi &&
      growIntervalOk c.seedLo c.seedHi c.growing &&
      decide (c.seedLo ≤ t.low ∧ t.high ≤ c.seedHi + c.growing.sum)
  else if t.kind = 1 then
    divisorListOk n c.small && bitIntervalOk c.small t.low t.high
  else if t.kind = 2 then
    divisorListOk n c.proper && tightlySorted c.small &&
      decide (c.small = c.proper.take c.small.length) &&
      bitIntervalOk c.small t.low t.high &&
      decide (t.low ≤ t.high ∧ t.high ≤ c.proper.sum)
  else false

end OddWeirdSubproblems

namespace OddWeirdSubproblems

def bestDeletionBound (ss : List Slot) (stop : ℕ) : Option (ℕ × ℕ) :=
  let fs := ss.map Slot.minimum
  (List.range ss.length).foldl (fun best i =>
    let ds := decrement fs i
    let z := number ds
    let t := divisorSum ds
    let d := 2 * z - t
    let jump := if d = 0 then stop else min stop (t / d + 1)
    if z < number fs && (best.map Prod.snd).getD 0 < jump then some (i, jump) else best) none

end OddWeirdSubproblems

namespace OddWeirdSubproblems

def nextThreshold (b : Box) : ℕ :=
  let n := number b.minimum
  let s := divisorSum b.minimum
  let bound := s / (2 * n - s)
  2 * ((bound + 1) / 2) + 1

theorem nextThreshold_odd (b : Box) : Odd (nextThreshold b) :=
  ⟨_, rfl⟩

theorem threshold_odd_product_le {b : Box} {q : ℕ} (hq : Odd q)
    (hlt : q < nextThreshold b)
    (hdef : divisorSum b.minimum < 2 * number b.minimum) :
    (2 * number b.minimum - divisorSum b.minimum) * q ≤ divisorSum b.minimum := by
  let d := 2 * number b.minimum - divisorSum b.minimum
  have hd : 0 < d := Nat.sub_pos_of_lt hdef
  let k := divisorSum b.minimum / d
  have hqk : q ≤ k := by
    obtain ⟨a, ha⟩ := hq
    change q < 2 * ((k + 1) / 2) + 1 at hlt
    omega
  exact (Nat.mul_le_mul_left d hqk).trans (Nat.mul_div_le _ _)

def chooseWideSlot (b : Box) : Option ℕ :=
  let num := (b.slots.map Slot.upperNum).prod
  let den := (b.slots.map Slot.upperDen).prod
  let limit := if b.remaining = 1 then
      if num < 2 * den && (2 * den - 1) / (2 * den - num) - b.next < 20
      then b.next else 0
    else if b.remaining = 2 && 100 < b.next then b.next * b.next else b.next
  ((b.slots.zipIdx.filter (fun (s, _) => !s.fixed)).foldl
    (fun best (s, i) =>
      let key := s.prime ^ (s.exponent + 1)
      if (limit = 0 || b.remaining = 0 || key < limit) &&
        key < best.1
      then (key, some i) else best)
    (b.slots.foldl (fun n s => max n (s.prime ^ (s.exponent + 1) + 1)) 1, none)).2

end OddWeirdSubproblems

namespace OddWeirdSubproblems

structure LiteralInterval where
  seed : List ℕ
  growth : List ℕ
  low : ℕ
  seedHigh : ℕ
  multiple : ℕ
  shift : ℕ

def literalIntervalOk (n s first stop : ℕ) (a : LiteralInterval) : Bool :=
  let high := a.seedHigh + a.growth.sum
  let slope := 2 * n - s + a.multiple
  divisorListOk n (a.seed ++ a.growth) &&
  bitIntervalOk a.seed a.low a.seedHigh &&
  growIntervalOk a.low a.seedHigh a.growth &&
  decide (s ≤ 2 * n ∧ (a.multiple = 0 ∨ (a.multiple ∣ n ∧ a.multiple < n)) ∧
    (a.shift = 0 ∨ a.shift = n) ∧
    s ≤ high + a.shift + slope * first ∧ a.low + a.shift + slope * (stop - 1) ≤ s)

theorem literalIntervalOk_closes {ss : List Slot} {first stop : ℕ} {a : LiteralInterval}
    (h : literalIntervalOk (number (ss.map Slot.minimum)) (divisorSum (ss.map Slot.minimum))
      first stop a = true) : HeadRangeClosed ss 0 first stop := by
  simp only [literalIntervalOk, Bool.and_eq_true, decide_eq_true_eq] at h
  exact headRange_squarefree rfl rfl h.2.1 h.2.2.1 h.2.2.2.1
    (cover_of_validated_growth h.1.1.1 h.1.1.2 h.1.2) h.2.2.2.2.1 h.2.2.2.2.2

inductive SweepAction where
  | nonprimitive (i stop : ℕ)
  | interval (stop : ℕ) (cert : LiteralInterval)
  | composite (stop : ℕ)
  | point (witness : List ℕ)

def SweepAction.stop (first : ℕ) : SweepAction → ℕ
  | .nonprimitive _ stop | .interval stop _ | .composite stop => stop
  | .point _ => first + 1

def sweepActionOk (ss : List Slot) (first : ℕ) : SweepAction → Bool
  | .nonprimitive i stop =>
    let fs := ss.map Slot.minimum
    let ds := decrement fs i
    let z := number ds
    let t := divisorSum ds
    decide (i < ss.length ∧ z < number fs ∧ (2 * z - t) * (stop - 1) ≤ t)
  | .interval stop cert =>
    let fs := ss.map Slot.minimum
    literalIntervalOk (number fs) (divisorSum fs) first stop cert
  | .composite stop =>
    (List.range (stop - first)).all
      (fun j => decide ((first + j) % 2 = 0) || !mayBeOddPrime (first + j))
  | .point ds =>
    let b : Box := ⟨ss ++ [⟨first, 1, false⟩], first + 2, 0⟩
    decide (2 * number b.minimum ≤ divisorSum b.minimum) &&
      minimumOk (fun _ => ds) b

theorem sweepActionOk_closes {ss : List Slot} {first : ℕ} {a : SweepAction}
    (h : sweepActionOk ss first a = true) : HeadRangeClosed ss 0 first (a.stop first) := by
  cases a with
  | nonprimitive i stop =>
    simp only [sweepActionOk, decide_eq_true_eq] at h
    exact headRange_decrement_nondeficient h.1 rfl rfl h.2.1 h.2.2
  | interval stop cert =>
    exact literalIntervalOk_closes h
  | composite stop =>
    simp only [sweepActionOk, List.all_eq_true, Bool.or_eq_true, decide_eq_true_eq,
      Bool.not_eq_true'] at h
    intro q hlo hhi hp ho
    change q < stop at hhi
    have hno := h (q - first) (List.mem_range.mpr (by omega))
    rw [show first + (q - first) = q by omega] at hno
    rcases hno with he | hnp
    · obtain ⟨k, hk⟩ := ho
      omega
    · exact (Bool.false_ne_true (hnp.symm.trans (mayBeOddPrime_of_prime hp))).elim
  | point ds =>
    simp only [sweepActionOk, Bool.and_eq_true, decide_eq_true_eq] at h
    exact headRange_single (fun _ _ => minimumOk_closes h.1 h.2)

end OddWeirdSubproblems

namespace OddWeirdSubproblems

def divisorsAtMost : Coordinates → ℕ → List ℕ
  | [], B => if 1 ≤ B then [1] else []
  | (p, e) :: fs, B =>
    (List.range (e + 1)).flatMap (fun i =>
      let w := p ^ i
      if w ≤ B then (divisorsAtMost fs (B / w)).map (fun d => d * w)
      else [])

def cappedExponent (p cap : ℕ) : ℕ → ℕ
  | 0 => 0
  | e + 1 => if p ^ (e + 1) ≤ cap then e + 1 else cappedExponent p cap e

def largestDivisorSearch : Coordinates → ℕ → ℕ
  | [], B => if B = 0 then 0 else 1
  | (p, e) :: fs, B =>
    if B = 0 then 0
    else if p ^ e * number fs ≤ B then p ^ e * number fs
    else if fs.isEmpty then p ^ cappedExponent p B e
    else
      let lo := cappedExponent p (B / number fs) e
      let hi := cappedExponent p B e
      (List.range (hi + 1 - lo)).foldl (fun best j =>
        let w := p ^ (lo + j)
        max best (w * largestDivisorSearch fs (B / w))) 0

def largestDivisorUpTo (fs : Coordinates) (B : ℕ) : ℕ :=
  largestDivisorSearch fs.reverse B

def greedyWitness (fs : Coordinates) (seed : List ℕ) (bits : ℕ) :
    ℕ → ℕ → ℕ → Option (List ℕ)
  | 0, _, _ => none
  | fuel + 1, cap, target =>
    if target ≤ seed.sum && bits.testBit target then some (bitWitness seed target)
    else
      let d := largestDivisorUpTo fs (min cap target)
      if d ≤ seed.sum then none
      else
        (greedyWitness fs seed bits fuel (d - 1) (target - d)).map (d :: ·)

def sparseHintedWitness (fs : Coordinates) (slot h target : ℕ) : Option (List ℕ) := do
  let (p, _) ← fs[slot]?
  let rest := fs.eraseIdx slot
  let shift := h * p
  if target < shift then none else
    let ds := sortDivisors 20 (divisorsAtMost rest 1024)
    let seed := smallPrefix 1024 ds
    let target := target - shift
    let chosen ← greedyWitness rest seed (subsetBits seed) 64 (number rest) target
    pure (if shift = 0 then chosen else shift :: chosen)

end OddWeirdSubproblems

namespace OddWeirdSubproblems

def packedIndexWitness (fs : Coordinates) (slot h : ℕ) : List ℕ :=
  let n := number fs
  let s := divisorSum fs
  (sparseHintedWitness fs slot h (s - 2 * n)).getD [] |> sortDivisors 30

end OddWeirdSubproblems

namespace OddWeirdSubproblems

def readVarNat : ℕ → List ℕ → Option (ℕ × List ℕ)
  | 0, _ | _, [] => none
  | fuel + 1, b :: bs =>
    if b < 128 then some (b, bs)
    else (readVarNat fuel bs).map (fun (n, rest) => (b % 128 + 128 * n, rest))

def readNatList : ℕ → List ℕ → Option (List ℕ × List ℕ)
  | 0, rest => some ([], rest)
  | n + 1, bs => do
    let (value, tail) ← readVarNat 64 bs
    let (values, rest) ← readNatList n tail
    pure (value :: values, rest)

def readLengthPrefixed (bs : List ℕ) : Option (List ℕ × List ℕ) := do
  let (n, rest) ← readVarNat 64 bs
  readNatList n rest

def bytesFromNat : ℕ → ℕ → List ℕ
  | 0, _ => []
  | n + 1, v => v % 256 :: bytesFromNat n (v / 256)

private def readLittleBytes : ℕ → List ℕ → Option (ℕ × List ℕ)
  | 0, data => some (0, data)
  | _ + 1, [] => none
  | n + 1, byte :: data => do
    let (value, rest) ← readLittleBytes n data
    pure (byte + (value <<< 8), rest)

private def copyPacked (value size distance count : ℕ) : ℕ :=
  let chunk := value >>> (8 * (size - distance))
  let wholeBytes := count - count % distance
  let whole := chunk * (((1 <<< (8 * wholeBytes)) - 1) / ((1 <<< (8 * distance)) - 1))
  let remainder := chunk % (1 <<< (8 * (count % distance)))
  whole + (remainder <<< (8 * wholeBytes))

def expandPackedTokens : ℕ → List ℕ → ℕ → ℕ → Option (List ℕ)
  | _, [], size, value => some (bytesFromNat size value)
  | 0, _ :: _, _, _ => none
  | fuel + 1, token :: data, size, value => do
    let (arg, rest) ← readVarNat 64 data
    if token = 0 then
      let (chunk, rest) ← readLittleBytes arg rest
      expandPackedTokens fuel rest (size + arg) (value + (chunk <<< (8 * size)))
    else if token = 1 && 0 < arg && arg ≤ size then
      let (count, rest) ← readVarNat 64 rest
      let chunk := copyPacked value size arg count
      expandPackedTokens fuel rest (size + count) (value + (chunk <<< (8 * size)))
    else none

def decodeInterval (bs : List ℕ) : Option (LiteralInterval × List ℕ) := do
  let (seed, rest) ← readLengthPrefixed bs
  let (growth, rest) ← readLengthPrefixed rest
  let (lo, rest) ← readVarNat 64 rest
  let (hi, rest) ← readVarNat 64 rest
  let (h, rest) ← readVarNat 64 rest
  let (c, rest) ← readVarNat 64 rest
  pure (⟨seed, growth, lo, hi, h, c⟩, rest)

def decodeSweepAction : List ℕ → Option (SweepAction × List ℕ)
  | [] => none
  | 0 :: rest => do
    let (i, rest) ← readVarNat 64 rest
    let (stop, rest) ← readVarNat 64 rest
    pure (.nonprimitive i stop, rest)
  | 1 :: rest => do
    let (stop, rest) ← readVarNat 64 rest
    let (cert, rest) ← decodeInterval rest
    pure (.interval stop cert, rest)
  | 2 :: rest => do
    let (stop, rest) ← readVarNat 64 rest
    pure (.composite stop, rest)
  | 3 :: rest => do
    let (ds, rest) ← readLengthPrefixed rest
    pure (.point ds, rest)
  | _ => none

end OddWeirdSubproblems

namespace OddWeirdSubproblems

def takeLargestWeight (cap : ℕ) : List ℕ → ℕ → ℕ × List ℕ
  | [], best => (best, [])
  | d :: ds, best =>
    if d ≤ cap then takeLargestWeight cap ds d else (best, d :: ds)

def scanGrowth (low target : ℕ) : ℕ → ℕ → List ℕ → Option (List ℕ)
  | 0, _, _ => none
  | fuel + 1, high, ds =>
    if target ≤ high then some []
    else
      let (d, rest) := takeLargestWeight (high + 1 - low) ds 0
      if d = 0 then none
      else (scanGrowth low target fuel (high + d) rest).map (d :: ·)

def sortedGrowth (fs : Coordinates) (low seedMax target high : ℕ) : Option (List ℕ) :=
  if target ≤ high then some [] else
    let ds := (sortedDivisors fs).dropWhile (· ≤ seedMax)
    scanGrowth low target 96 high (ds.takeWhile (· < number fs))

end OddWeirdSubproblems

namespace OddWeirdSubproblems

def decodePoint (b : Box) (data : List ℕ) : Option (List ℕ × List ℕ) := do
  let (tag, rest) ← readVarNat 64 data
  let i := tag / 8
  let j := tag % 8
  let fs := b.minimum
  let h := if j < 2 then j else ((fs.eraseIdx i)[j - 2]?.map Prod.fst).getD 0
  pure (packedIndexWitness fs i h, rest)

def minimumNeedsWitness (b : Box) : Bool := !minimumOk (fun _ => []) b

structure PointReplay where
  verify : Box → List ℕ → Option (List ℕ)
  sound : ∀ {b data tail}, verify b data = some tail → b.Closed

def PointReplay.ofDivisors (read : Box → List ℕ → Option (List ℕ × List ℕ)) : PointReplay where
  verify b data := do
    let (ds, tail) ← read b data
    if witnessOk (number b.minimum) (divisorSum b.minimum) ds then some tail else none
  sound := by
    intro b data tail h
    obtain ⟨⟨ds, tail'⟩, _, h⟩ := Option.bind_eq_some_iff.mp h
    dsimp only at h
    split at h
    · exact witnessOk_closes ‹_›
    · contradiction

def consumeMinimum (checkPoint : PointReplay) (b : Box) (data : List ℕ) : Option (List ℕ) :=
  if minimumNeedsWitness b then checkPoint.verify b data else some data

theorem consumeMinimum_closes
    {readPoint : PointReplay} {b : Box} {data tail : List ℕ}
    (hnd : 2 * number b.minimum ≤ divisorSum b.minimum)
    (h : consumeMinimum readPoint b data = some tail) : b.Closed := by
  unfold consumeMinimum minimumNeedsWitness at h
  split at h
  · exact readPoint.sound h
  · next hn =>
    have hm : minimumOk (fun _ => []) b = true := by simpa using hn
    exact minimumOk_closes hnd hm

def divisorOfRank (rank : ℕ) (xs : Coordinates) : ℕ :=
  let result := xs.reverse.foldl (fun (r, value) (p, e) =>
    (r / (e + 1), value * p ^ (r % (e + 1)))) (rank, 1)
  result.2

def rankDivisorList (fs : Coordinates) (gaps : List ℕ) : List ℕ :=
  let result := gaps.foldl (fun (previous, ds) gap =>
    let rank := previous + gap
    (rank, divisorOfRank (rank - 1) fs :: ds)) (0, [])
  sortDivisors 20 result.2

def decodeRankDivisors (fs : Coordinates) (bs : List ℕ) :
    Option (List ℕ × List ℕ) := do
  let (ds, rest) ← readLengthPrefixed bs
  pure (rankDivisorList fs ds, rest)

def decodeStreamAction (b : Box) (first top : ℕ) (bs : List ℕ) :
    Option (SweepAction × List ℕ) := do
  let (tag, rest) ← readVarNat 64 bs
  if tag = 0 then
    let (gap, rest) ← readVarNat 64 rest
    pure (.composite (first + gap), rest)
  else if tag = 1 then
    let (ds, rest) ← decodeRankDivisors (b.minimum ++ [(first, 1)]) rest
    pure (.point ds, rest)
  else
    let selector := (tag - 2) / 2
    let useCore := selector % 2
    let j := selector / 2
    let h := if j < 2 then j else (b.slots[j - 2]?.map Slot.prime).getD 0
    let n := number b.minimum
    let s := divisorSum b.minimum
    let shift := if useCore = 0 then 0 else n
    let candidates := sortDivisors 20 (divisorsAtMost b.minimum (min 1024 (n - 1)))
    let seed := smallPrefix 1024 candidates
    let lo := effectiveLow (subsetBits seed) seed.sum
    let hi := seed.sum - lo
    let slope := 2 * n - s + h
    let stop := min top ((s - shift - lo) / slope + 1)
    if (tag - 2) % 2 = 0 then
      let goal := s - (shift + slope * first)
      let ds ← sortedGrowth b.minimum lo (seed.getLast?.getD 0) goal hi
      pure (.interval stop ⟨seed, ds, lo, hi, h, shift⟩, rest)
    else
      let (ds, rest) ← decodeRankDivisors b.minimum rest
      pure (.interval stop ⟨seed, ds, lo, hi, h, shift⟩, rest)

abbrev SweepReader := Box → ℕ → ℕ → List ℕ → Option (SweepAction × List ℕ)

structure SweepVerifier where
  run : Box → ℕ → ℕ → List ℕ → Option (ℕ × List ℕ)
  sound : ∀ {b first top data stop tail}, run b first top data = some (stop, tail) →
    HeadRangeClosed b.slots 0 first stop

def SweepVerifier.ofActions (reader : SweepReader) : SweepVerifier where
  run b first top data := do
    let (a, rest) ← reader b first top data
    if sweepActionOk b.slots first a then some (a.stop first, rest) else none
  sound := by
    intro b first top data stop tail h
    obtain ⟨⟨a, rest⟩, _, h⟩ := Option.bind_eq_some_iff.mp h
    dsimp only at h
    split at h
    · have he : a.stop first = stop := by simpa using congrArg (Option.map Prod.fst) h
      exact he ▸ sweepActionOk_closes ‹_›
    · contradiction

def consumeSweep (readSweep : SweepVerifier) (b : Box) (stop : ℕ) : ℕ → ℕ → List ℕ → Option (List ℕ)
  | 0, first, data => if stop ≤ first then some data else none
  | fuel + 1, first, data =>
    if stop ≤ first then none else do
      let (next, rest) ← readSweep.run b first stop data
      if first < next then
        consumeSweep readSweep b stop fuel next rest
      else none

theorem consumeSweep_closes {readSweep : SweepVerifier} {b : Box} {stop fuel first : ℕ}
    {data tail : List ℕ} (h : consumeSweep readSweep b stop fuel first data = some tail) :
    HeadRangeClosed b.slots 0 first stop := by
  induction fuel generalizing first data with
  | zero =>
    simp only [consumeSweep] at h
    split at h
    · intro q hlo hhi
      omega
    · contradiction
  | succ fuel ih =>
    simp only [consumeSweep] at h
    split at h
    · contradiction
    · next hl =>
      obtain ⟨⟨next, rest⟩, ha, h⟩ := Option.bind_eq_some_iff.mp h
      dsimp only at h
      split at h
      · exact headRange_join (readSweep.sound ha) (ih h)
      · contradiction

def consumeWholeSweep (readSweep : SweepVerifier) (b : Box) (stop : ℕ) (data : List ℕ) : Option (List ℕ) := do
  let (count, rest) ← readVarNat 64 data
  match bestDeletionBound b.slots stop with
  | some (i, jump) =>
    if b.next < jump then
      if sweepActionOk b.slots b.next (.nonprimitive i jump) then
        consumeSweep readSweep b stop count jump rest
      else none
    else consumeSweep readSweep b stop count b.next rest
  | none => consumeSweep readSweep b stop count b.next rest

theorem consumeWholeSweep_closes {readSweep : SweepVerifier} {b : Box} {stop : ℕ} {data tail : List ℕ}
    (h : consumeWholeSweep readSweep b stop data = some tail) : HeadRangeClosed b.slots 0 b.next stop := by
  unfold consumeWholeSweep at h
  cases hd : readVarNat 64 data with
  | none => simp [hd] at h
  | some row =>
    obtain ⟨count, rest⟩ := row
    rw [hd] at h
    dsimp only at h
    split at h
    · next i jump heq =>
      split at h
      · split at h
        · exact headRange_join (sweepActionOk_closes (a := .nonprimitive i jump) ‹_›) (consumeSweep_closes h)
        · contradiction
      · exact consumeSweep_closes h
    · exact consumeSweep_closes h

structure BranchPruning where
  verify : Box → List ℕ → Option (Bool × List ℕ)
  sound : ∀ {b data tail}, verify b data = some (true, tail) → b.Closed

def BranchPruning.none : BranchPruning where
  verify _ data := some (false, data)
  sound := by
    intro _ _ _ h
    simp at h

def streamReplay (readPoint : PointReplay) (readSweep : SweepVerifier)
    (prune : BranchPruning) (cut : Box → Bool) : ℕ → Box → List ℕ → Option (List ℕ)
  | 0, _, _ => none
  | fuel + 1, b, data =>
    if cut b then some data
    else do
      let (closed, data) ← prune.verify b data
      if closed then some data
      else if 2 * number b.minimum ≤ divisorSum b.minimum then consumeMinimum readPoint b data
      else if b.upperNum ≤ 2 * b.upperDen then some data
      else if 0 < b.remaining && b.next < nextThreshold b then
        (if b.remaining = 1 then consumeWholeSweep readSweep b (nextThreshold b) data else some data).bind
          (streamReplay readPoint readSweep prune cut fuel {b with next := nextThreshold b})
      else match (chooseWideSlot b).bind (fun i => b.slots[i]?.map (fun s => (i, s))) with
      | some (i, s) => do
        if s.fixed then none else
          let data ← streamReplay readPoint readSweep prune cut fuel {b with slots := b.slots.set i {s with fixed := true}} data
          streamReplay readPoint readSweep prune cut fuel {b with slots := b.slots.set i {s with exponent := s.exponent + 1}} data
      | none =>
        match b.remaining with
        | 0 => none
        | r + 1 => do
          let data ← streamReplay readPoint readSweep prune cut fuel ⟨b.slots, b.next + 2, r + 1⟩ data
          if mayBeOddPrime b.next then
            streamReplay readPoint readSweep prune cut fuel ⟨b.slots ++ [⟨b.next, 1, false⟩], b.next + 2, r⟩ data
          else some data

theorem stream_threshold_closes {readSweep : SweepVerifier} {ss : List Slot} {p r : ℕ} {data : List ℕ}
    (hdef : divisorSum (ss.map Slot.minimum) < 2 * number (ss.map Slot.minimum))
    (hcheck : r = 0 → ∃ tail,
      let b : Box := ⟨ss, p, 1⟩
      consumeWholeSweep readSweep b (nextThreshold b) data = some tail)
    (hskip : (⟨ss, nextThreshold ⟨ss, p, r + 1⟩, r + 1⟩ : Box).Closed) :
    (⟨ss, p, r + 1⟩ : Box).Closed := by
  apply close_jump_next hskip
  intro q hp hq hprime ho
  cases r with
  | zero =>
    obtain ⟨tail, h⟩ := hcheck rfl
    exact consumeWholeSweep_closes h q hp hq hprime ho
  | succ r =>
    apply close_nondeficient_squarefree_prefix (Nat.succ_pos _)
    have hu := threshold_odd_product_le ho hq hdef
    have h := Nat.mul_le_mul_right q
      (show 2 * number (ss.map Slot.minimum) ≤
        2 * number (ss.map Slot.minimum) - divisorSum (ss.map Slot.minimum) +
          divisorSum (ss.map Slot.minimum) by omega)
    rw [Nat.add_mul] at h
    rw [Nat.mul_add, Nat.mul_one]
    exact le_trans h (Nat.add_le_add_right hu _)

theorem streamReplay_closes
    {readPoint : PointReplay} {readSweep : SweepVerifier} {prune : BranchPruning} {cut : Box → Bool} {fuel : ℕ} {b : Box} {data tail : List ℕ}
    (hcut : ∀ box, cut box = true → box.Closed)
    (hlo : 1 < b.next) (hodd : Odd b.next) (h : streamReplay readPoint readSweep prune cut fuel b data = some tail) :
    b.Closed := by
  induction fuel generalizing b data tail with
  | zero => simp [streamReplay] at h
  | succ fuel ih =>
    rw [streamReplay] at h
    split at h
    · exact hcut b ‹_›
    obtain ⟨⟨closed, input⟩, hprune, h⟩ := Option.bind_eq_some_iff.mp h
    cases closed
    · simp only [Bool.false_eq_true, if_false] at h
      split at h
      · exact consumeMinimum_closes ‹_› h
      next hnondef =>
        split at h
        · exact close_of_upperNum_le hlo ‹_›
        split at h
        next hguard =>
          obtain ⟨hr, hnext⟩ : 0 < b.remaining ∧ b.next < nextThreshold b := by simpa using hguard
          rcases b with ⟨ss, p, r⟩
          cases r with
          | zero => exact (Nat.lt_irrefl 0 hr).elim
          | succ r =>
            have hnd : divisorSum (ss.map Slot.minimum) <
                2 * number (ss.map Slot.minimum) := Nat.lt_of_not_ge hnondef
            have hs : ∃ mid,
                (if r + 1 = 1 then consumeWholeSweep readSweep ⟨ss, p, r + 1⟩
                  (nextThreshold ⟨ss, p, r + 1⟩) input else some input) = some mid ∧
                streamReplay readPoint readSweep prune cut fuel ⟨ss, nextThreshold ⟨ss, p, r + 1⟩, r + 1⟩ mid = some tail :=
              Option.bind_eq_some_iff.mp h
            obtain ⟨mid, hmid, hend⟩ := hs
            apply stream_threshold_closes (readSweep := readSweep) (data := input) hnd _
              (ih (hlo.trans hnext) (nextThreshold_odd _) hend)
            intro heq
            subst r
            exact ⟨mid, by simpa using hmid⟩
        next =>
          split at h
          next i s hs =>
            have hi : b.slots[i]? = some s := by
              obtain ⟨j, _, hj⟩ := Option.bind_eq_some_iff.mp hs
              cases hg : b.slots[j]? <;> simp_all
            split at h
            · contradiction
            · have hf : s.fixed = false := by simp_all
              obtain ⟨mid, h₁, h₂⟩ := Option.bind_eq_some_iff.mp h
              exact close_split_slot hi hf (ih hlo hodd h₁) (ih hlo hodd h₂)
          next =>
            rcases b with ⟨ss, p, r⟩
            cases r with
            | zero => contradiction
            | succ r =>
              obtain ⟨mid, hskip, htake⟩ := Option.bind_eq_some_iff.mp h
              have hodd' : Odd (p + 2) := by
                obtain ⟨k, hk⟩ := hodd
                exact ⟨k + 1, by dsimp at hk; omega⟩
              have hlo' : 1 < p + 2 := by dsimp at hlo; omega
              apply close_split_next hodd (ih hlo' hodd' hskip)
              intro hp
              exact ih hlo' hodd' (by simpa only [if_pos (mayBeOddPrime_of_prime hp)] using htake)
    · exact prune.sound hprune

def checkPacked (readPoint : PointReplay) (readSweep : SweepVerifier)
    (cut : Box → Bool) (fuel : ℕ) (b : Box) (count value : ℕ) (prune : BranchPruning := .none) : Bool :=
  match expandPackedTokens count (bytesFromNat count value) 0 0 with
  | none => false
  | some raw => match streamReplay readPoint readSweep prune cut fuel b raw with
    | some [] => true
    | _ => false

theorem checkPackedBlock
    {readPoint : PointReplay} {b : Box} {cut : Box → Bool} {fuel count value : ℕ}
    (readSweep : SweepVerifier := .ofActions decodeStreamAction)
    (prune : BranchPruning := .none)
    (hcut : ∀ box, cut box = true → box.Closed) (hlo : 1 < b.next) (hodd : Odd b.next)
    (h : checkPacked readPoint readSweep cut fuel b count value prune = true) : b.Closed := by
  unfold checkPacked at h
  split at h
  · contradiction
  · split at h
    · exact streamReplay_closes hcut hlo hodd ‹_›
    · contradiction

inductive ClosedCuts : List Box → Prop
  | nil : ClosedCuts []
  | cons {b : Box} {bs : List Box} : b.Closed → ClosedCuts bs → ClosedCuts (b :: bs)

theorem ClosedCuts.closedOfMem {cuts : List Box} (hcuts : ClosedCuts cuts)
    {b : Box} (hb : b ∈ cuts) : b.Closed := by
  induction hcuts with
  | nil => simp at hb
  | cons hd _ ih =>
    rcases List.mem_cons.mp hb with rfl | hb
    · exact hd
    · exact ih hb

end OddWeirdSubproblems

namespace OddWeirdSubproblems

def boundedSweepEnd (B : ℕ) (b : Box) : ℕ :=
  min (nextThreshold b) (2 * (((B - 1) / number b.minimum + 1) / 2) + 1)

private theorem boundedSweep_closes {B : ℕ} {b : Box} {data tail : List ℕ}
    {readSweep : SweepVerifier}
    (h : consumeWholeSweep readSweep b (boundedSweepEnd B b) data = some tail)
    (hrest : ({b with next := nextThreshold b} : Box).ClosedBelow B)
    (hr : b.remaining = 1) : b.ClosedBelow B := by
  rcases b with ⟨ss, p, r⟩
  change r = 1 at hr
  subst r
  apply closeBelow_jump_next (stop := nextThreshold ⟨ss, p, 1⟩) hrest
  intro q hq hqhi hp hodd
  by_cases hcut : q < boundedSweepEnd B ⟨ss, p, 1⟩
  · exact closedBelow_of_closed (consumeWholeSweep_closes h q hq hcut hp hodd) B
  · intro xs ys hm hv hlt _ _
    have hy : ys = [] := List.length_eq_zero_iff.mp hm.2.2
    have hx := Nat.le_of_dvd (number_pos (primeCoordinates_left hv).1) (minimum_dvd hm.1)
    have hmpos : 0 < number (ss.map Slot.minimum) := by
      have hvalid := minimum_valid hm.1 (primeCoordinates_left hv)
      simp only [List.map_append, List.map_cons, List.map_nil] at hvalid
      exact number_pos (primeCoordinates_left hvalid).1
    have hu : (B - 1) / number (ss.map Slot.minimum) < q := by
      unfold boundedSweepEnd at hcut
      change ¬ q < min (nextThreshold ⟨ss, p, 1⟩)
        (2 * (((B - 1) / number (ss.map Slot.minimum) + 1) / 2) + 1) at hcut
      omega
    have hsize := Nat.lt_mul_of_div_lt hu hmpos
    rw [Nat.mul_comm] at hsize
    dsimp only at hx
    rw [List.map_append] at hx
    change number (ss.map Slot.minimum ++ [(q, 1)]) ≤ number xs at hx
    rw [number_append, number_cons] at hx
    simp only [pow_one, show number [] = 1 from rfl, mul_one] at hx
    simp only [hy, List.append_nil] at hlt
    omega

private theorem thresholdSweep_closes {B : ℕ} {b : Box} {data tail : List ℕ}
    {readSweep : SweepVerifier} {limited : Bool}
    (h : consumeWholeSweep readSweep b
      (if limited then boundedSweepEnd B b else nextThreshold b) data = some tail)
    (hrest : ({b with next := nextThreshold b} : Box).ClosedBelow B)
    (hr : b.remaining = 1) : b.ClosedBelow B := by
  cases limited
  · rcases b with ⟨ss, p, r⟩
    change r = 1 at hr
    subst r
    apply closeBelow_jump_next (stop := nextThreshold ⟨ss, p, 1⟩) hrest
    intro q hq hqhi hp hodd
    exact closedBelow_of_closed (consumeWholeSweep_closes h q hq hqhi hp hodd) B
  · exact boundedSweep_closes h hrest hr

private theorem closeBelow_skip_composites {ss : List Slot} {B p r fuel : ℕ}
    (hodd : Odd p) (h : (⟨ss, firstAllowedOdd p fuel, r + 1⟩ : Box).ClosedBelow B) :
    (⟨ss, p, r + 1⟩ : Box).ClosedBelow B :=
  closeBelow_jump_next h fun _ hlo hhi hp hq =>
    (hhi.not_ge (firstAllowedOdd_le_prime hodd hq hp hlo fuel)).elim

private def normalizeSlots (fast : Bool) (B : ℕ) (b : Box) : Box :=
  if fast then freezeSizeSlots B b else b

private theorem normalizeSlots_closedBelow {B : ℕ} {b : Box} (fast : Bool)
    (hlo : 1 < b.next) (hodd : Odd b.next)
    (h : (normalizeSlots fast B b).ClosedBelow B) : b.ClosedBelow B := by
  cases fast
  · exact h
  · exact freezeSizeSlots_closes hlo hodd h

def replayWithSizeLimit (limited fast : Bool) (B : ℕ) (readPoint : PointReplay) (readSweep : SweepVerifier)
    (prune : BranchPruning) (cut : Box → Bool) : ℕ → Box → List ℕ → Option (List ℕ)
  | 0, _, _ => none
  | fuel + 1, b, data =>
    if cut b then some data
    else if limited && decide (B ≤ number b.minimum * (tailPrimeFloor b.next b.remaining).prod) then some data
    else if (limited && fast) && exponentCapOk B b then some data
    else
      let b := normalizeSlots (limited && fast) B b
      match (if !limited || fast then none else sizeFixedSlot B b) with
      | some (i, s) =>
        replayWithSizeLimit limited fast B readPoint readSweep prune cut fuel
          {b with slots := b.slots.set i {s with fixed := true}} data
      | none =>
        if rankedUpperNum b ≤ 2 * rankedUpperDen b then some data
        else do
          let (closed, data) ← prune.verify b data
          if closed then some data
          else if 2 * number b.minimum ≤ divisorSum b.minimum then consumeMinimum readPoint b data
          else if 0 < b.remaining && b.next < nextThreshold b then
            (if b.remaining = 1 then consumeWholeSweep readSweep b
                (if limited then boundedSweepEnd B b else nextThreshold b) data
              else some data).bind
              (replayWithSizeLimit limited fast B readPoint readSweep prune cut fuel {b with next := nextThreshold b})
          else match (chooseWideSlot b).bind (fun i => b.slots[i]?.map (fun s => (i, s))) with
          | some (i, s) => do
            if s.fixed then none else
              let data ← replayWithSizeLimit limited fast B readPoint readSweep prune cut fuel
                {b with slots := b.slots.set i {s with fixed := true}} data
              replayWithSizeLimit limited fast B readPoint readSweep prune cut fuel
                {b with slots := b.slots.set i {s with exponent := s.exponent + 1}} data
          | none =>
            match b.remaining with
            | 0 => none
            | r + 1 =>
              let q := firstAllowedOdd b.next 32
              if b.next < q then
                replayWithSizeLimit limited fast B readPoint readSweep prune cut fuel ⟨b.slots, q, r + 1⟩ data
              else do
                let data ← replayWithSizeLimit limited fast B readPoint readSweep prune cut fuel
                  ⟨b.slots, b.next + 2, r + 1⟩ data
                if mayBeOddPrime b.next then
                  replayWithSizeLimit limited fast B readPoint readSweep prune cut fuel
                    ⟨b.slots ++ [⟨b.next, 1, false⟩], b.next + 2, r⟩ data
                else some data

theorem replayWithSizeLimit_closes
    {limited fast : Bool} {B : ℕ} {readPoint : PointReplay} {readSweep : SweepVerifier} {prune : BranchPruning}
    {cut : Box → Bool} {fuel : ℕ} {b : Box} {data tail : List ℕ}
    (hcut : ∀ box, cut box = true → box.ClosedBelow B)
    (hlo : 1 < b.next) (hodd : Odd b.next)
    (h : replayWithSizeLimit limited fast B readPoint readSweep prune cut fuel b data = some tail) :
    b.ClosedBelow B := by
  induction fuel generalizing b data tail with
  | zero => contradiction
  | succ fuel ih =>
    rw [replayWithSizeLimit] at h
    split at h
    · exact hcut b ‹_›
    split at h
    · exact closeBelow_of_ranked_minimum_ge hodd (of_decide_eq_true (Bool.and_eq_true_iff.mp ‹_›).2)
    split at h
    · exact exponentCapOk_closes hlo hodd ((Bool.and_eq_true_iff.mp ‹_›).2)
    apply normalizeSlots_closedBelow (limited && fast) hlo hodd
    have hlo' : 1 < (normalizeSlots (limited && fast) B b).next := by
      cases limited <;> cases fast <;> simpa [normalizeSlots, freezeSizeSlots] using hlo
    have hodd' : Odd (normalizeSlots (limited && fast) B b).next := by
      cases limited <;> cases fast <;> simpa [normalizeSlots, freezeSizeSlots] using hodd
    dsimp only at h
    generalize hbox : normalizeSlots (limited && fast) B b = normalized at h ⊢
    rw [hbox] at hlo' hodd'
    clear hlo hodd
    rename_i h_cut h_min h_cap
    clear h_cut h_min h_cap hbox b
    have hlo := hlo'
    have hodd := hodd'
    clear hlo' hodd'
    split at h
    · next i s hsize =>
      have hsize' : sizeFixedSlot B normalized = some (i, s) := by cases limited <;> cases fast <;> simp_all
      exact sizeFixedSlot_closes hsize' hodd (ih hlo hodd h)
    · split at h
      · exact closedBelow_of_closed (close_of_ranked_upper hlo hodd ‹_›) B
      obtain ⟨⟨closed, input⟩, hprune, h⟩ := Option.bind_eq_some_iff.mp h
      cases closed
      · simp only [Bool.false_eq_true, if_false] at h
        split at h
        · exact closedBelow_of_closed (consumeMinimum_closes ‹_› h) B
        next hnondef =>
          split at h
          next hguard =>
            obtain ⟨hr, hnext⟩ : 0 < normalized.remaining ∧ normalized.next < nextThreshold normalized := by simpa using hguard
            obtain ⟨mid, hmid, hend⟩ := Option.bind_eq_some_iff.mp h
            have hskip := ih (hlo.trans hnext) (nextThreshold_odd _) hend
            rcases normalized with ⟨ss, p, r⟩
            cases r with
            | zero => exact (Nat.lt_irrefl 0 hr).elim
            | succ r =>
              cases r with
              | zero => exact thresholdSweep_closes (limited := limited) (by simpa using hmid) hskip rfl
              | succ r =>
                apply closeBelow_jump_next hskip
                intro q _ hq _ ho
                apply closedBelow_of_closed _ B
                apply close_nondeficient_squarefree_prefix (by omega)
                have hnd : divisorSum (ss.map Slot.minimum) <
                    2 * number (ss.map Slot.minimum) := Nat.lt_of_not_ge hnondef
                have hu := threshold_odd_product_le ho hq hnd
                have hbase := Nat.mul_le_mul_right q
                  (show 2 * number (ss.map Slot.minimum) ≤
                    2 * number (ss.map Slot.minimum) - divisorSum (ss.map Slot.minimum) +
                      divisorSum (ss.map Slot.minimum) by omega)
                rw [Nat.add_mul] at hbase
                rw [Nat.mul_add, Nat.mul_one]
                exact le_trans hbase (Nat.add_le_add_right hu _)
          next =>
            split at h
            next i s hs =>
              have hi : normalized.slots[i]? = some s := by
                obtain ⟨j, _, hj⟩ := Option.bind_eq_some_iff.mp hs
                cases hg : normalized.slots[j]? <;> simp_all
              split at h
              · contradiction
              · have hf : s.fixed = false := by simp_all
                obtain ⟨mid, h₁, h₂⟩ := Option.bind_eq_some_iff.mp h
                exact closeBelow_split_slot hi hf (ih hlo hodd h₁) (ih hlo hodd h₂)
            next =>
              rcases normalized with ⟨ss, p, r⟩
              cases r with
              | zero => contradiction
              | succ r =>
                dsimp only at h
                split at h
                · exact closeBelow_skip_composites hodd
                    (ih (hlo.trans_le (firstAllowedOdd_ge _ _)) (firstAllowedOdd_odd hodd _) h)
                · obtain ⟨mid, hskip, htake⟩ := Option.bind_eq_some_iff.mp h
                  have hodd' : Odd (p + 2) := by
                    obtain ⟨k, hk⟩ := hodd
                    exact ⟨k + 1, by dsimp at hk; omega⟩
                  have hlo' : 1 < p + 2 := by dsimp at hlo; omega
                  apply closeBelow_split_next hodd (ih hlo' hodd' hskip)
                  intro hp
                  exact ih hlo' hodd' (by simpa only [if_pos (mayBeOddPrime_of_prime hp)] using htake)
      · exact closedBelow_of_closed (prune.sound hprune) B

private theorem unboundedReplay_independent_of_bound
    (B : ℕ) (readPoint : PointReplay) (readSweep : SweepVerifier) (prune : BranchPruning)
    (cut : Box → Bool) (fuel : ℕ) (b : Box) (data : List ℕ) :
    replayWithSizeLimit false true 0 readPoint readSweep prune cut fuel b data =
      replayWithSizeLimit false true B readPoint readSweep prune cut fuel b data := by
  induction fuel generalizing b data with
  | zero => rfl
  | succ fuel ih =>
    simp only [replayWithSizeLimit, Bool.false_and, Bool.false_eq_true, if_false,
      normalizeSlots, Bool.not_false, Bool.true_or, if_true, ih]

def unboundedRankedStream (readPoint : PointReplay) (readSweep : SweepVerifier)
    (prune : BranchPruning) (cut : Box → Bool) : ℕ → Box → List ℕ → Option (List ℕ) :=
  replayWithSizeLimit false true 0 readPoint readSweep prune cut

theorem unboundedRankedStream_closes
    {readPoint : PointReplay} {readSweep : SweepVerifier} {prune : BranchPruning}
    {cut : Box → Bool} {fuel : ℕ} {b : Box} {data tail : List ℕ}
    (hcut : ∀ box, cut box = true → box.Closed)
    (hlo : 1 < b.next) (hodd : Odd b.next)
    (h : unboundedRankedStream readPoint readSweep prune cut fuel b data = some tail) :
    b.Closed := by
  intro xs ys hm hv hw hp
  let B := number (xs ++ ys) + 1
  change replayWithSizeLimit false true 0 readPoint readSweep prune cut fuel b data = some tail at h
  rw [unboundedReplay_independent_of_bound B] at h
  exact replayWithSizeLimit_closes (fun box hc => closedBelow_of_closed (hcut box hc) B)
    hlo hodd h xs ys hm hv (Nat.lt_succ_self _) hw hp

end OddWeirdSubproblems

namespace OddWeirdSubproblems

open Finset

def PrefixGapBound : ℕ → List ℕ → Prop
  | _, [] => True
  | G, d :: ds => d ≤ G ∧ PrefixGapBound (G + d) ds

theorem PrefixGapBound.scale {G : ℕ} {ds : List ℕ} (h : PrefixGapBound G ds) (v : ℕ) :
    PrefixGapBound (v * G) (ds.map (v * ·)) := by
  induction ds generalizing G with
  | nil => trivial
  | cons d ds ih =>
    obtain ⟨hd, hs⟩ := h
    exact ⟨Nat.mul_le_mul_left v hd, by simpa only [Nat.mul_add] using ih hs⟩

private theorem growIntervalOk_of_prefixGapBound {C T G : ℕ} {ws : List ℕ}
    (hgap : PrefixGapBound G ws) (hwidth : G + 2 * C ≤ T + 1) :
    growIntervalOk C (T - C) ws = true := by
  induction ws generalizing T G with
  | nil => rfl
  | cons w ws ih =>
    obtain ⟨hw, htail⟩ := hgap
    simp only [growIntervalOk, Bool.and_eq_true, decide_eq_true_eq]
    refine ⟨by omega, ?_⟩
    rw [show T - C + w = T + w - C by omega]
    exact ih htail (by omega)

theorem cover_of_fresh_prefixGapBound {D : Finset ℕ} {ws : List ℕ} {C T G : ℕ}
    (hcover : Covered D C (T - C)) (hnd : ws.Nodup) (hfresh : Disjoint D ws.toFinset)
    (hgap : PrefixGapBound G ws) (hwidth : G + 2 * C ≤ T + 1) :
    Covered (D ∪ ws.toFinset) C (T + ws.sum - C) := by
  have hnodup : (D.toList ++ ws).Nodup := by
    apply List.nodup_append.mpr
    refine ⟨Finset.nodup_toList _, hnd, ?_⟩
    intro d hd d' hd' h
    subst d'
    exact (Finset.disjoint_left.mp hfresh) (Finset.mem_toList.mp hd) (List.mem_toFinset.mpr hd')
  have hg := cover_of_growIntervalOk hnodup (by simpa using hcover)
    (growIntervalOk_of_prefixGapBound hgap hwidth)
  simpa only [List.toFinset_append, Finset.toList_toFinset, show T - C + ws.sum = T + ws.sum - C by omega]
    using hg

private theorem sumDivisors_coprime_prime_power {u p : ℕ} (hp : p.Prime) (hpu : ¬ p ∣ u)
    (b : ℕ) : (∑ d ∈ (u * p ^ b).divisors, d) =
      (∑ d ∈ u.divisors, d) * ∑ j ∈ range (b + 1), p ^ j := by
  rw [((hp.coprime_iff_not_dvd.mpr hpu).symm.pow_right b).sum_divisors_mul,
    Nat.sum_divisors_prime_pow hp]

private theorem sumProperDivisors_raise_coprime_prime_power {u p a : ℕ}
    (hp : p.Prime) (hpu : ¬ p ∣ u) :
    (∑ d ∈ (u * p ^ (a + 1)).properDivisors, d) =
      (∑ d ∈ (u * p ^ a).properDivisors, d) + p ^ (a + 1) * (∑ d ∈ u.properDivisors, d) + u * p ^ a := by
  let hsum := sumDivisors_coprime_prime_power hp hpu
  have h : (∑ d ∈ (u * p ^ (a + 1)).divisors, d) =
      (∑ d ∈ (u * p ^ a).divisors, d) + (∑ d ∈ u.divisors, d) * p ^ (a + 1) := by
    rw [hsum, hsum, sum_range_succ, Nat.mul_add]
  rw [Nat.sum_divisors_eq_sum_properDivisors_add_self (n := u),
    Nat.sum_divisors_eq_sum_properDivisors_add_self (n := u * p ^ a),
    Nat.sum_divisors_eq_sum_properDivisors_add_self (n := u * p ^ (a + 1)), Nat.add_mul,
    mul_comm (∑ d ∈ u.properDivisors, d)] at h
  omega

theorem cover_raise_coprime_prime_power {u p a C G : ℕ} {ds : List ℕ}
    (hu : 0 < u) (hp : p.Prime) (hpu : ¬ p ∣ u) (hnd : ds.Nodup)
    (hds : ds.toFinset = u.properDivisors) (hgap : PrefixGapBound G ds) :
    let m := u * p ^ a
    let n := u * p ^ (a + 1)
    let v := p ^ (a + 1)
    let T := ∑ d ∈ m.properDivisors, d
    let U := ∑ d ∈ u.properDivisors, d
    Covered m.properDivisors C (T - C) →
    v * G + 2 * C ≤ T + 1 →
    m + 2 * C ≤ T + v * U + 1 →
    Covered n.properDivisors C ((∑ d ∈ n.properDivisors, d) - C) := by
  intro m n v T U hcover hscaled hlast
  let ws := ds.map (v * ·)
  have hv : 0 < v := pow_pos hp.pos _
  have hm : 0 < m := Nat.mul_pos hu (pow_pos hp.pos _)
  have hn : n = m * p := by simp only [n, m, pow_succ, mul_assoc]
  have hvnot : ¬ v ∣ m := by
    intro hvm
    apply hpu
    apply (Nat.mul_dvd_mul_iff_left (pow_pos hp.pos a)).mp
    simpa only [v, m, pow_succ, mul_comm p, mul_comm u] using hvm
  have hval {d : ℕ} (hd : d ∈ ws.toFinset) : ∃ e ∈ u.properDivisors, d = v * e := by
    obtain ⟨e, he, heq⟩ := List.mem_map.mp (List.mem_toFinset.mp hd)
    exact ⟨e, hds ▸ List.mem_toFinset.mpr he, heq.symm⟩
  have hfresh : Disjoint m.properDivisors ws.toFinset := by
    apply Finset.disjoint_left.mpr
    intro d hd hd'
    obtain ⟨e, _, rfl⟩ := hval hd'
    exact hvnot ((dvd_mul_right v e).trans (Nat.mem_properDivisors.mp hd).1)
  have hws : ws.Nodup := hnd.map (mul_right_injective₀ hv.ne')
  have hsum : ws.sum = v * U := by
    unfold U
    rw [← hds, sum_toFinset_of_nodup hnd]
    simpa only [List.map_id, ws, id_eq] using List.sum_map_mul_left ds id v
  have hc := cover_of_fresh_prefixGapBound hcover hws hfresh (hgap.scale v) hscaled
  rw [hsum] at hc
  have hnot : m ∉ m.properDivisors ∪ ws.toFinset := by
    intro h
    rcases Finset.mem_union.mp h with h | h
    · exact Nat.self_notMem_properDivisors h
    · obtain ⟨e, _, he⟩ := hval h
      exact hvnot ⟨e, he⟩
  have hmore := subsetSumIntervalInsert hnot hc (by omega : C + m ≤ T + v * U - C + 1)
  have hsub : insert m (m.properDivisors ∪ ws.toFinset) ⊆ n.properDivisors := by
    have hmlt : m < n := by
      rw [hn]
      simpa only [mul_one] using Nat.mul_lt_mul_of_pos_left hp.one_lt hm
    have hmdvd : m ∣ n := hn ▸ dvd_mul_right m p
    intro d hd
    rcases Finset.mem_insert.mp hd with rfl | hd
    · exact Nat.mem_properDivisors.mpr ⟨hmdvd, hmlt⟩
    rcases Finset.mem_union.mp hd with hd | hd
    · exact Nat.mem_properDivisors.mpr
        ⟨(Nat.mem_properDivisors.mp hd).1.trans hmdvd, (Nat.mem_properDivisors.mp hd).2.trans hmlt⟩
    · obtain ⟨e, he, rfl⟩ := hval hd
      obtain ⟨hdvd, hlt⟩ := Nat.mem_properDivisors.mp he
      change v * e ∈ (u * v).properDivisors
      rw [mul_comm u v]
      exact Nat.mem_properDivisors.mpr ⟨mul_dvd_mul_left v hdvd, Nat.mul_lt_mul_of_pos_left hlt hv⟩
  have htotal : (∑ d ∈ n.properDivisors, d) = T + v * U + m :=
    sumProperDivisors_raise_coprime_prime_power (a := a) hp hpu
  rw [htotal, show T + v * U + m - C = T + v * U - C + m by omega]
  exact cover_mono hsub hmore

private theorem mul_sumProperDivisors_le_raise_coprime_prime_power {u p a : ℕ}
    (hp : p.Prime) (hpu : ¬ p ∣ u) :
    p * (∑ d ∈ (u * p ^ a).properDivisors, d) ≤ (∑ d ∈ (u * p ^ (a + 1)).properDivisors, d) := by
  have h : (∑ d ∈ (u * p ^ (a + 1)).divisors, d) =
      p * (∑ d ∈ (u * p ^ a).divisors, d) + ∑ d ∈ u.divisors, d := by
    rw [sumDivisors_coprime_prime_power hp hpu (a + 1), sumDivisors_coprime_prime_power hp hpu a,
      geom_sum_succ, Nat.mul_add, Nat.mul_one, mul_left_comm]
  have hm : u * p ^ (a + 1) = p * (u * p ^ a) := by
    rw [pow_succ]
    ac_rfl
  rw [Nat.sum_divisors_eq_sum_properDivisors_add_self (n := u * p ^ (a + 1)),
    Nat.sum_divisors_eq_sum_properDivisors_add_self (n := u * p ^ a), Nat.mul_add] at h
  conv at h =>
    lhs
    arg 2
    rw [hm]
  omega

theorem cover_raise_coprime_prime_power_add {u p a C G : ℕ} {ds : List ℕ}
    (hu : 0 < u) (hp : p.Prime) (hpu : ¬ p ∣ u) (hC : 0 < C) (hnd : ds.Nodup)
    (hds : ds.toFinset = u.properDivisors) (hgap : PrefixGapBound G ds) :
    let m := u * p ^ a
    let v := p ^ (a + 1)
    let T := ∑ d ∈ m.properDivisors, d
    let U := ∑ d ∈ u.properDivisors, d
    Covered m.properDivisors C (T - C) →
    v * G + 2 * C ≤ T + 1 →
    m + 2 * C ≤ T + v * U + 1 →
    ∀ j : ℕ, let n := u * p ^ (a + j)
      Covered n.properDivisors C ((∑ d ∈ n.properDivisors, d) - C) := by
  intro m v T U hcover hscaled hlast j
  let M (b : ℕ) := u * p ^ b
  let V (b : ℕ) := p ^ (b + 1)
  let S (b : ℕ) := ∑ d ∈ (M b).properDivisors, d
  have hpush {x y : ℕ} (h : x + 2 * C ≤ y + 1) :
      p * x + 2 * C ≤ p * y + 1 := by
    have hm := Nat.mul_le_mul_left p (show x + (2 * C - 1) ≤ y by omega)
    rw [Nat.mul_add] at hm
    have hl := Nat.le_mul_of_pos_left (2 * C - 1) hp.pos
    omega
  have hstep (b : ℕ) (hc : Covered (M b).properDivisors C (S b - C))
      (hs : V b * G + 2 * C ≤ S b + 1) (hl : M b + 2 * C ≤ S b + V b * U + 1) :
      Covered (M (b + 1)).properDivisors C (S (b + 1) - C) ∧
      V (b + 1) * G + 2 * C ≤ S (b + 1) + 1 ∧
      M (b + 1) + 2 * C ≤ S (b + 1) + V (b + 1) * U + 1 := by
    have hM : M (b + 1) = p * M b := by
      unfold M
      rw [pow_succ]
      ac_rfl
    have hV : V (b + 1) = p * V b := by simp only [V, pow_succ']
    have hS : p * S b ≤ S (b + 1) := mul_sumProperDivisors_le_raise_coprime_prime_power hp hpu
    refine ⟨cover_raise_coprime_prime_power (a := b) hu hp hpu hnd hds hgap hc hs hl, ?_, ?_⟩
    · rw [hV, mul_assoc]
      exact (hpush hs).trans (Nat.add_le_add_right hS 1)
    · rw [hM, hV, mul_assoc p (V b) U]
      have hh := hpush hl
      rw [Nat.mul_add] at hh
      exact hh.trans (Nat.add_le_add_right (Nat.add_le_add_right hS _) 1)
  have hall (i : ℕ) : Covered (M (a + i)).properDivisors C (S (a + i) - C) ∧
      V (a + i) * G + 2 * C ≤ S (a + i) + 1 ∧
      M (a + i) + 2 * C ≤ S (a + i) + V (a + i) * U + 1 := by
    induction i with
    | zero => exact ⟨hcover, hscaled, hlast⟩
    | succ i ih => exact hstep (a + i) ih.1 ih.2.1 ih.2.2
  exact (hall j).1

end OddWeirdSubproblems

namespace OddWeirdSubproblems

open Finset

def GapUpTo (n g : ℕ) : Prop :=
  ∀ d ∈ n.properDivisors, d ≤ g + ∑ x ∈ n.properDivisors.filter (· < d), x

instance (n g : ℕ) : Decidable (GapUpTo n g) := by
  unfold GapUpTo
  infer_instance

private theorem sum_filtered_toFinset_eq_listSum {ds : List ℕ} (hnd : ds.Nodup) (d : ℕ) :
    (∑ x ∈ ds.toFinset.filter (· < d), x) = (ds.filter (fun x => decide (x < d))).sum := by
  rw [← sum_toFinset_of_nodup (hnd.filter (fun x => decide (x < d))), List.toFinset_filter]
  simp

private theorem prefixGapBound_of_sortedLT {ds : List ℕ} {g : ℕ} (hs : ds.SortedLT)
    (hg : ∀ d ∈ ds, d ≤ g + (ds.filter (fun x => decide (x < d))).sum) :
    PrefixGapBound g ds := by
  induction ds generalizing g with
  | nil => trivial
  | cons w ds ih =>
    obtain ⟨hsmall, htail⟩ := List.pairwise_cons.mp hs.pairwise
    refine ⟨?_, ih htail.sortedLT ?_⟩
    · have hnil : ds.filter (fun d => decide (d < w)) = [] := by
        apply List.filter_eq_nil_iff.mpr
        intro d hd
        simpa only [decide_eq_true_eq] using not_lt_of_gt (hsmall d hd)
      have hw := hg w List.mem_cons_self
      simpa [List.filter_cons, hnil] using hw
    · intro d hd
      have hh := hg d (List.mem_cons_of_mem _ hd)
      simpa [List.filter_cons, hsmall d hd, Nat.add_assoc] using hh

theorem GapUpTo.prefixGapBound_sort {n g : ℕ} (hg : GapUpTo n g) :
    PrefixGapBound g n.properDivisors.sort := by
  let ds := n.properDivisors.sort
  have hd : ds.toFinset = n.properDivisors := Finset.sort_toFinset _ _
  apply prefixGapBound_of_sortedLT (Finset.sortedLT_sort n.properDivisors)
  intro d hmem
  rw [← sum_filtered_toFinset_eq_listSum (Finset.sort_nodup _ _) d, hd]
  exact hg d (hd ▸ List.mem_toFinset.mpr hmem)

end OddWeirdSubproblems

namespace OddWeirdSubproblems

open Finset

def HasSubsetSum (D : Finset ℕ) (x : ℕ) : Prop := ∃ t ⊆ D, ∑ d ∈ t, d = x

def DenseLowSums (D : Finset ℕ) (C G : ℕ) : Prop :=
  ∀ j, j + G ≤ C → ∃ x, j ≤ x ∧ x < j + G ∧ HasSubsetSum D x

theorem DenseLowSums.mono {D E : Finset ℕ} {C G : ℕ} (h : DenseLowSums D C G)
    (hsub : D ⊆ E) : DenseLowSums E C G := by
  intro j hj
  obtain ⟨x, hx, hy, t, ht, hs⟩ := h j hj
  exact ⟨x, hx, hy, t, ht.trans hsub, hs⟩

theorem gapUpTo_of_central_and_low {n C G : ℕ}
    (hG : 0 < G) (hC : 2 * C ≤ ∑ d ∈ n.properDivisors, d)
    (hcovered : Covered n.properDivisors C ((∑ d ∈ n.properDivisors, d) - C))
    (hlow : DenseLowSums n.properDivisors C G) : GapUpTo n G := by
  intro d hd
  let D := n.properDivisors
  let T := ∑ v ∈ D, v
  let S := ∑ v ∈ D.filter (· < d), v
  change d ≤ G + S
  by_contra! hgap
  have hdT : d ≤ T := single_le_sum (f := fun x : ℕ => x) (fun _ _ => Nat.zero_le _) hd
  have hC' : 2 * C ≤ T := hC
  have hgap' : S + G < d := by omega
  obtain ⟨x, hx, hx', t, hsub, hsum⟩ : ∃ x, S < x ∧ x ≤ S + G ∧ HasSubsetSum D x := by
    by_cases hS : S < C
    · by_cases hspace : S + 1 + G ≤ C
      · obtain ⟨x, hx, hx', hp⟩ := hlow (S + 1) hspace
        exact ⟨x, by omega, by omega, hp⟩
      · have hc := hcovered C le_rfl (by omega : C ≤ T - C)
        exact ⟨C, hS, by omega, hc⟩
    · by_cases hS' : S < T - C
      · have hc := hcovered (S + 1) (by omega) (by omega : S + 1 ≤ T - C)
        exact ⟨S + 1, by omega, by omega, hc⟩
      · let j := T - (S + G)
        have hj : j + G ≤ C := by dsimp [j]; omega
        obtain ⟨z, hz, hz', t, ht, hs⟩ := hlow j hj
        have ht' := sum_sdiff (f := fun v : ℕ => v) ht
        change (∑ v ∈ D \ t, v) + (∑ v ∈ t, v) = T at ht'
        refine ⟨T - z, ?_, ?_, D \ t, sdiff_subset, ?_⟩
        · dsimp [j] at hz'
          omega
        · dsimp [j] at hz
          omega
        · omega
  have hsmall : t ⊆ D.filter (· < d) := by
    intro v hv
    refine Finset.mem_filter.mpr ⟨hsub hv, ?_⟩
    have hle : v ≤ ∑ k ∈ t, k := single_le_sum (f := fun k : ℕ => k) (fun _ _ => Nat.zero_le _) hv
    omega
  have hle : (∑ v ∈ t, v) ≤ S := sum_le_sum_of_subset hsmall
  omega

def lowDensityOk (ds : List ℕ) (C G : ℕ) : Bool :=
  let bits := subsetBits ds
  (List.range (C + 1 - G)).all (fun j =>
    (List.range G).any (fun i => bits.testBit (j + i)))

theorem lowDensityOk_sound {ds : List ℕ} {C G : ℕ} (hn : ds.Nodup)
    (h : lowDensityOk ds C G = true) : DenseLowSums ds.toFinset C G := by
  intro j hj
  simp only [lowDensityOk, List.all_eq_true, List.any_eq_true, List.mem_range] at h
  obtain ⟨i, hi, hbit⟩ := h j (by omega)
  exact ⟨j + i, by omega, by omega, testBit_subsetBits hn hbit⟩

def lowModulusOk (ds : List ℕ) (C M : ℕ) : Bool :=
  let bits := subsetBits ds
  (List.range C).all (fun i => !(decide (M ∣ i)) || bits.testBit i)

theorem lowModulusOk_sound {ds : List ℕ} {C M : ℕ} (hn : ds.Nodup)
    (h : lowModulusOk ds C M = true) : ∀ i < C, M ∣ i → HasSubsetSum ds.toFinset i := by
  intro i hi hd
  simp only [lowModulusOk, List.all_eq_true, List.mem_range, Bool.or_eq_true,
    Bool.not_eq_true', decide_eq_false_iff_not] at h
  exact testBit_subsetBits hn ((h i hi).resolve_left fun hno => hno hd)

theorem pseudoperfect_of_central_and_modulus {n C M : ℕ}
    (hA : n.Abundant) (hc : C ≤ n)
    (hcover : Covered n.properDivisors C ((∑ d ∈ n.properDivisors, d) - C))
    (hsmall : ∀ x < C, M ∣ x → HasSubsetSum n.properDivisors x)
    (hm : M ∣ 2 * n) (hs : M ∣ ∑ d ∈ n.divisors, d) : n.Pseudoperfect := by
  let T := ∑ d ∈ n.properDivisors, d
  let excess := T - n
  have ha : n < T := hA
  have heq := Nat.sum_divisors_eq_sum_properDivisors_add_self (n := n)
  change (∑ d ∈ n.divisors, d) = T + n at heq
  have hdvd : M ∣ excess := by
    have hd := Nat.dvd_sub hs hm
    rwa [heq, show T + n - 2 * n = excess by dsimp [excess]; omega] at hd
  have hwitness : HasSubsetSum n.properDivisors excess := by
    by_cases h : excess < C
    · exact hsmall excess h hdvd
    · exact hcover excess (by omega) (by dsimp [excess]; omega : excess ≤ T - C)
  obtain ⟨t, ht, hsum⟩ := hwitness
  refine ⟨hA.pos, n.properDivisors \ t, sdiff_subset, ?_⟩
  have hdiff := sum_sdiff (f := fun v : ℕ => v) ht
  change (∑ v ∈ n.properDivisors \ t, v) + (∑ v ∈ t, v) = T at hdiff
  dsimp [excess] at hsum
  omega

end OddWeirdSubproblems

namespace OddWeirdSubproblems

open Finset

theorem cover_of_fresh_finset_steps {D E : Finset ℕ} {C T : ℕ}
    (hcover : Covered D C (T - C)) (hdis : Disjoint D E)
    (hstep : ∀ d ∈ E, d + 2 * C ≤ T + (∑ x ∈ E.filter (· < d), x) + 1) :
    Covered (D ∪ E) C (T + (∑ x ∈ E, x) - C) := by
  induction E using Finset.induction_on_max with
  | empty => simpa using hcover
  | insert d E hlt ih =>
    have hnd : d ∉ E := fun hd => (lt_irrefl d) (hlt d hd)
    have hfilter (x : ℕ) (hx : x ≤ d) : (insert d E).filter (· < x) = E.filter (· < x) := by
      rw [Finset.filter_insert, if_neg (not_lt_of_ge hx)]
    have hc := ih (hdis.mono_right (Finset.subset_insert _ _)) (fun x hx => by
      have h := hstep x (Finset.mem_insert_of_mem hx)
      rwa [hfilter x (hlt x hx).le] at h)
    have hb := hstep d (Finset.mem_insert_self _ _)
    rw [hfilter d le_rfl, Finset.filter_true_of_mem hlt] at hb
    have hnot : d ∉ D ∪ E := by
      have hdD : d ∉ D := fun hd =>
        (Finset.disjoint_left.mp hdis) hd (Finset.mem_insert_self _ _)
      simp [hdD, hnd]
    have hc' := subsetSumIntervalInsert hnot hc (by omega : C + d ≤ T + (∑ x ∈ E, x) - C + 1)
    rw [Finset.sum_insert hnd, Finset.union_insert]
    rw [show T + (d + ∑ x ∈ E, x) - C = T + (∑ x ∈ E, x) - C + d by omega]
    exact hc'

theorem cover_raise_existing_prime {u q a C G : ℕ}
    (hu : 0 < u) (hq : q.Prime) (hqu : ¬ q ∣ u) (ha : 0 < a) :
    let n := u * q ^ a
    let T := ∑ d ∈ n.properDivisors, d
    GapUpTo n G → Covered n.properDivisors C (T - C) →
    q * G + 2 * C ≤ (∑ d ∈ u.divisors, d) + 1 →
    Covered (n * q).properDivisors C ((∑ d ∈ (n * q).properDivisors, d) - C) := by
  intro n T hgap hcover hbound
  let D := n.properDivisors
  let E := (n * q).properDivisors \ D
  have hn : 0 < n := Nat.mul_pos hu (pow_pos hq.pos a)
  have hnlt : n < n * q := by
    simpa only [mul_one] using Nat.mul_lt_mul_of_pos_left hq.one_lt hn
  have hDn : D ⊆ (n * q).properDivisors := by
    intro d hd
    obtain ⟨hdiv, hlt⟩ := Nat.mem_properDivisors.mp hd
    exact Nat.mem_properDivisors.mpr ⟨hdiv.trans (dvd_mul_right n q), hlt.trans hnlt⟩
  have hDis : Disjoint D E := Finset.sdiff_disjoint.symm
  have hUnion : D ∪ E = (n * q).properDivisors := by
    exact (Finset.union_comm D E).trans (Finset.sdiff_union_of_subset hDn)
  have hqn : q ∣ n := by
    have hqa : q ∣ q ^ a := by
      simpa only [pow_one] using pow_dvd_pow q ha
    exact dvd_mul_of_dvd_right hqa u
  have hU : u.divisors ⊆ D := by
    have hpow : 1 < q ^ a := by
      simpa only [pow_zero] using pow_lt_pow_right₀ hq.one_lt ha
    have hult : u < n := by
      simpa only [mul_one] using Nat.mul_lt_mul_of_pos_left hpow hu
    intro d hd
    have hdu := Nat.dvd_of_mem_divisors hd
    exact Nat.mem_properDivisors.mpr
      ⟨hdu.trans (dvd_mul_right u (q ^ a)), (Nat.le_of_dvd hu hdu).trans_lt hult⟩
  have hstep (d : ℕ) (hd : d ∈ E) :
      d + 2 * C ≤ T + (∑ x ∈ E.filter (· < d), x) + 1 := by
    obtain ⟨hdnq, hdn⟩ := Finset.mem_sdiff.mp hd
    obtain ⟨hdiv, hlt⟩ := Nat.mem_properDivisors.mp hdnq
    have hqd : q ∣ d := by
      by_contra hnot
      have hcop := (hq.coprime_iff_not_dvd.mpr hnot).symm
      have hdiv' := hcop.dvd_of_dvd_mul_right hdiv
      have hdlt : d < n := lt_of_le_of_ne (Nat.le_of_dvd hn hdiv')
        (fun heq => hnot (heq.symm ▸ hqn))
      exact hdn (Nat.mem_properDivisors.mpr ⟨hdiv', hdlt⟩)
    obtain ⟨w, rfl⟩ := hqd
    have hw : w ∈ D := Nat.mem_properDivisors.mpr
      ⟨(Nat.mul_dvd_mul_iff_left hq.pos).mp (by simpa only [mul_comm n q] using hdiv),
        (Nat.mul_lt_mul_left hq.pos).mp (by simpa only [mul_comm n q] using hlt)⟩
    let I := (D.filter (· < w)).image (q * ·)
    have hscale : I ⊆ D ∪ E.filter (· < q * w) := by
      intro x hx
      obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
      obtain ⟨hyD, hyw⟩ := Finset.mem_filter.mp hy
      obtain ⟨hyd, hyn⟩ := Nat.mem_properDivisors.mp hyD
      by_cases hmem : q * y ∈ D
      · exact Finset.mem_union_left _ hmem
      · have hnew : q * y ∈ (n * q).properDivisors := by
          rw [mul_comm n q]
          exact Nat.mem_properDivisors.mpr ⟨mul_dvd_mul_left q hyd, Nat.mul_lt_mul_of_pos_left hyn hq.pos⟩
        exact Finset.mem_union_right _ (Finset.mem_filter.mpr
          ⟨Finset.mem_sdiff.mpr ⟨hnew, hmem⟩, Nat.mul_lt_mul_of_pos_left hyw hq.pos⟩)
    have hIU : Disjoint u.divisors I := by
      apply Finset.disjoint_left.mpr
      intro x hx hxI
      obtain ⟨y, _, rfl⟩ := Finset.mem_image.mp hxI
      exact hqu ((dvd_mul_right q y).trans (Nat.dvd_of_mem_divisors hx))
    have htot := Finset.sum_le_sum_of_subset (f := fun x : ℕ => x)
      (Finset.union_subset (hU.trans Finset.subset_union_left) hscale)
    rw [Finset.sum_union hIU, Finset.sum_union (hDis.mono_right (Finset.filter_subset _ _))] at htot
    have hgw := Nat.mul_le_mul_left q (hgap w hw)
    rw [Nat.mul_add] at hgw
    have hIsum : (∑ x ∈ I, x) = q * (∑ x ∈ D.filter (· < w), x) := by
      unfold I
      rw [Finset.sum_image (fun _ _ _ _ h => mul_left_cancel₀ hq.ne_zero h), ← Finset.mul_sum]
    change _ ≤ q * G + q * (∑ x ∈ D.filter (· < w), x) at hgw
    rw [← hIsum] at hgw
    change _ ≤ T + (∑ x ∈ E.filter (· < q * w), x) at htot
    omega
  have hf := cover_of_fresh_finset_steps hcover hDis hstep
  change Covered (D ∪ E) C (((∑ x ∈ D, x) + ∑ x ∈ E, x) - C) at hf
  rw [← Finset.sum_union hDis, hUnion] at hf
  exact hf

end OddWeirdSubproblems

namespace OddWeirdSubproblems

open Finset

private theorem properDivisorSubsetOfDvd {n m : ℕ} (hm : 0 < m) (h : n ∣ m) :
    n.properDivisors ⊆ m.properDivisors := by
  intro d hd
  obtain ⟨hdvd, hdlt⟩ := Nat.mem_properDivisors.mp hd
  exact Nat.mem_properDivisors.mpr ⟨hdvd.trans h, hdlt.trans_le (Nat.le_of_dvd hm h)⟩

theorem cover_mul_existing_prime_factors {u k C G : ℕ} (hu : 0 < u) (hk : 0 < k)
    (hG : 0 < G) (hC : 2 * C ≤ ∑ d ∈ u.properDivisors, d)
    (hcovered : Covered u.properDivisors C ((∑ d ∈ u.properDivisors, d) - C))
    (hlow : DenseLowSums u.properDivisors C G)
    (hprimes : ∀ q : ℕ, q.Prime → q ∣ k →
      q ∣ u ∧ q * G + 2 * C ≤ (∑ d ∈ (ordCompl[q] u).divisors, d) + 1) :
    Covered (u * k).properDivisors C ((∑ d ∈ (u * k).properDivisors, d) - C) := by
  revert hk hprimes
  induction k using induction_on_primes with
  | zero => omega
  | one =>
    intro _ _
    simpa using hcovered
  | prime_mul q k hq ih =>
    intro hkq hprimes
    have hk : 0 < k := Nat.pos_of_mul_pos_left hkq
    have hcov := ih hk (fun p hp hpk => hprimes p hp (dvd_mul_of_dvd_right hpk q))
    let n := u * k
    have hn : 0 < n := Nat.mul_pos hu hk
    have hun : u ∣ n := dvd_mul_right u k
    have hsub := properDivisorSubsetOfDvd hn hun
    have hgap : GapUpTo n G :=
      gapUpTo_of_central_and_low hG (hC.trans (Finset.sum_le_sum_of_subset hsub))
        hcov (hlow.mono hsub)
    obtain ⟨hqu, hbound⟩ := hprimes q hq (dvd_mul_right q k)
    let v := ordCompl[q] n
    have hv : 0 < v := Nat.ordCompl_pos q hn.ne'
    have hqv : ¬ q ∣ v := hq.coprime_iff_not_dvd.mp (Nat.coprime_ordCompl hq hn.ne')
    have hqn : q ∣ n := dvd_mul_of_dvd_left hqu k
    have ha : 0 < n.factorization q := hq.factorization_pos_of_dvd hn.ne' hqn
    have hvn : v * q ^ n.factorization q = n :=
      (mul_comm _ _).trans (Nat.ordProj_mul_ordCompl_eq_self n q)
    have hsubv : (ordCompl[q] u).divisors ⊆ v.divisors :=
      Nat.divisors_subset_of_dvd hv.ne' (Nat.ordCompl_dvd_ordCompl_of_dvd hun q)
    have hbudget : q * G + 2 * C ≤ (∑ d ∈ v.divisors, d) + 1 :=
      hbound.trans (Nat.add_le_add_right (Finset.sum_le_sum_of_subset hsubv) 1)
    have hlift := cover_raise_existing_prime (C := C) (G := G) hv hq hqv ha
      (by simpa only [hvn] using hgap) (by simpa only [hvn] using hcov) hbudget
    simpa only [hvn, n, Nat.mul_assoc, mul_comm k q] using hlift

end OddWeirdSubproblems

namespace OddWeirdSubproblems

theorem freshPrime_deficiency_lt {u s t r : ℕ} (hu : 0 < u) (ht : 1 < t)
    (hs : s ≤ 2 * u)
    (hratio : 2 < ((s : ℚ) / u) * ((t : ℚ) / ((t : ℚ) - 1)) ^ r) :
    (2 * u - s) * t < 2 * r * u := by
  have huq : (0 : ℚ) < u := by exact_mod_cast hu
  have htq : (1 : ℚ) < t := by exact_mod_cast ht
  have htq0 : (0 : ℚ) < t := zero_lt_one.trans htq
  have hz : (0 : ℚ) < ((t : ℚ) - 1) / t := div_pos (sub_pos.mpr htq) htq0
  have hrecip : ((t : ℚ) / ((t : ℚ) - 1)) ^ r =
      ((((t : ℚ) - 1) / t) ^ r)⁻¹ := by
    rw [← inv_pow, inv_div]
  rw [hrecip, ← div_eq_mul_inv, lt_div_iff₀ (pow_pos hz r)] at hratio
  have hzsub : ((t : ℚ) - 1) / t - 1 = -(1 / (t : ℚ)) := by
    rw [sub_div, div_self htq0.ne', sub_sub_cancel_left]
  have hbern := one_add_mul_sub_le_pow ((by norm_num : (-1 : ℚ) ≤ 0).trans hz.le) r
  rw [hzsub, mul_neg, ← sub_eq_add_neg, mul_one_div] at hbern
  have hmul := mul_lt_mul_of_pos_right
    ((lt_div_iff₀ huq).mp ((mul_le_mul_of_nonneg_left hbern (by norm_num : (0 : ℚ) ≤ 2)).trans_lt
      hratio)) htq0
  have hclear : 2 * (1 - (r : ℚ) / t) * (u : ℚ) * (t : ℚ) =
      2 * (u : ℚ) * (t : ℚ) - 2 * (r : ℚ) * (u : ℚ) := by
    calc
      _ = 2 * (u : ℚ) * ((1 - (r : ℚ) / t) * (t : ℚ)) := by ring
      _ = _ := by rw [sub_mul, one_mul, div_mul_cancel₀ _ htq0.ne']; ring
  rw [hclear] at hmul
  have hq : (2 * (u : ℚ) - s) * (t : ℚ) < 2 * (r : ℚ) * (u : ℚ) := by
    nlinarith only [hmul]
  exact_mod_cast (show (((2 * u - s : ℕ) : ℚ) * (t : ℚ)) < 2 * (r : ℚ) * (u : ℚ) by
    simpa only [Nat.cast_sub hs, Nat.cast_mul, Nat.cast_ofNat] using hq)

theorem freshPrimeBudget_of_ratio {u s t P r : ℕ} (hu : 0 < u) (ht : 1 < t)
    (hus : u ≤ s) (hs : s ≤ 2 * u) (hP : 2 * r ≤ P) (hPt : P ≤ t)
    (hratio : 2 < ((s : ℚ) / u) * ((t : ℚ) / ((t : ℚ) - 1)) ^ r) :
    (2 * u - s) * t < 2 * r * u ∧ (P - 2 * r) * u < P * (s - u) := by
  have htbudget := freshPrime_deficiency_lt hu ht hs hratio
  have hPbudget := (Nat.mul_le_mul_left (2 * u - s) hPt).trans_lt htbudget
  have hsum : 2 * u - s + (s - u) = u := by omega
  have h₁ := congrArg (fun n : ℕ => P * n) hsum
  have h₂ := congrArg (fun n : ℕ => n * u) (Nat.sub_add_cancel hP)
  simp only [Nat.mul_add, Nat.add_mul] at h₁ h₂
  rw [Nat.mul_comm (2 * u - s) P] at hPbudget
  exact ⟨htbudget, by omega⟩

theorem freshPrimeBudget {u t P r : ℕ} (hu : 0 < u) (hdef : u.Deficient)
    (ht : 1 < t) (hP : 2 * r ≤ P) (hPt : P ≤ t)
    (hratio : 2 < u.abundancyIndex * ((t : ℚ) / ((t : ℚ) - 1)) ^ r) :
    (2 * u - ∑ d ∈ u.divisors, d) * t < 2 * r * u ∧
      (P - 2 * r) * u < P * (∑ d ∈ u.properDivisors, d) := by
  have hsum : (∑ d ∈ u.divisors, d) = (∑ d ∈ u.properDivisors, d) + u :=
    Nat.sum_divisors_eq_sum_properDivisors_add_self
  have hus : u ≤ ∑ d ∈ u.divisors, d := by omega
  have hs : (∑ d ∈ u.divisors, d) ≤ 2 * u := by
    unfold Nat.Deficient at hdef
    omega
  have h := freshPrimeBudget_of_ratio hu ht hus hs hP hPt hratio
  simpa only [hsum, Nat.add_sub_cancel_right] using h

theorem abundancyIndex_le_pow_of_fresh_primes {v t r : ℕ} (hv : 0 < v) (ht : 1 < t)
    (hcard : v.primeFactors.card ≤ r) (hmin : ∀ p ∈ v.primeFactors, t ≤ p) :
    v.abundancyIndex ≤ ((t : ℚ) / ((t : ℚ) - 1)) ^ r := by
  let localIndex (p : ℕ) : ℚ :=
    (∑ i ∈ Finset.range (v.factorization p + 1), (p : ℚ) ^ i) /
      (p : ℚ) ^ v.factorization p
  have hindex : v.abundancyIndex = ∏ p ∈ v.primeFactors, localIndex p := by
    have hsigma := ArithmeticFunction.sigma_eq_prod_primeFactors_sum_range_factorization_pow_mul
      (k := 1) hv.ne'
    rw [ArithmeticFunction.sigma_one_apply] at hsigma
    simp only [mul_one] at hsigma
    rw [Nat.abundancyIndex, hsigma]
    conv_lhs => arg 2; rw [Nat.prod_primeFactors_pow_factorization hv.ne']
    simp only [localIndex, Nat.cast_prod, Nat.cast_sum, Nat.cast_pow, ← Finset.prod_div_distrib]
  have htq : (1 : ℚ) < t := by exact_mod_cast ht
  have hone : (1 : ℚ) ≤ (t : ℚ) / ((t : ℚ) - 1) := by
    exact (one_le_div (sub_pos.mpr htq)).mpr (by linarith)
  rw [hindex]
  refine (Finset.prod_le_prod (g := fun _ => (t : ℚ) / ((t : ℚ) - 1))
    (fun p _ => ?_) (fun p hp => ?_)).trans ?_
  · unfold localIndex
    exact div_nonneg (Finset.sum_nonneg fun _ _ => pow_nonneg (Nat.cast_nonneg p) _)
      (pow_nonneg (Nat.cast_nonneg p) _)
  · have hpq : (t : ℚ) ≤ p := by exact_mod_cast hmin p hp
    have hpq1 := htq.trans_le hpq
    calc
      localIndex p ≤ (p : ℚ) / ((p : ℚ) - 1) := by
        unfold localIndex
        rw [div_le_div_iff₀ (pow_pos (show (0 : ℚ) < p by linarith) _) (sub_pos.mpr hpq1),
          geom_sum_mul, pow_succ]
        linarith
      _ ≤ (t : ℚ) / ((t : ℚ) - 1) := by
        rw [div_le_div_iff₀ (sub_pos.mpr hpq1) (sub_pos.mpr htq)]
        nlinarith
  · rw [Finset.prod_const]
    exact pow_le_pow_right₀ hone hcard

theorem freshPrimeBudget_of_coprime_completion {u v t P r : ℕ}
    (hdef : u.Deficient) (hcop : u.Coprime v) (habund : (u * v).Abundant)
    (ht : 1 < t) (hP : 2 * r ≤ P) (hPt : P ≤ t)
    (hcard : v.primeFactors.card ≤ r) (hmin : ∀ p ∈ v.primeFactors, t ≤ p) :
    (2 * u - ∑ d ∈ u.divisors, d) * t < 2 * r * u ∧
      (P - 2 * r) * u < P * (∑ d ∈ u.properDivisors, d) := by
  have hu := Nat.pos_of_mul_pos_right habund.pos
  have hv := Nat.pos_of_mul_pos_left habund.pos
  have hidx := Nat.abundant_iff_two_lt_abundancyIndex.mp habund
  have hmul : (u * v).abundancyIndex = u.abundancyIndex * v.abundancyIndex := by
    simp only [Nat.abundancyIndex, hcop.sum_divisors_mul, Nat.cast_mul, div_mul_div_comm]
  rw [hmul] at hidx
  have huindex : 0 ≤ u.abundancyIndex := by unfold Nat.abundancyIndex; positivity
  exact freshPrimeBudget hu hdef ht hP hPt
    (hidx.trans_le (mul_le_mul_of_nonneg_left
      (abundancyIndex_le_pow_of_fresh_primes hv ht hcard hmin) huindex))

end OddWeirdSubproblems

namespace OddWeirdSubproblems

open Finset

theorem coprime_coordinateProduct {p : ℕ} {xs : Coordinates} (hp : p.Prime)
    (hv : ∀ x ∈ xs, x.1.Prime) (hf : ∀ x ∈ xs, p ≠ x.1) : p.Coprime (number xs) := by
  apply Nat.coprime_list_prod_right_iff.mpr
  intro w hw
  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hw
  rw [← pow_one p]
  exact Nat.coprime_pow_primes _ _ hp (hv x hx) (hf x hx)

theorem erase_coordinate {fs : Coordinates} {p e : ℕ}
    (hv : PrimeCoordinates fs) (hm : (p, e) ∈ fs) :
    let rest := fs.erase (p, e)
    PrimeCoordinates rest ∧ p.Prime ∧ ¬p ∣ number rest ∧ number fs = number rest * p ^ e := by
  intro rest
  have hrest : PrimeCoordinates rest :=
    ⟨fun x hx => hv.1 x (List.erase_subset hx), hv.2.erase (p, e)⟩
  have hp := hv.1 (p, e) hm
  have hpw : (fs.map Prod.fst).Pairwise (· ≠ ·) :=
    List.pairwise_map.mpr (hv.2.imp fun h => Nat.ne_of_lt h)
  have hperm := List.perm_cons_erase hm
  have hn : p ∉ rest.map Prod.fst := by
    have hd := (hperm.map Prod.fst).nodup_iff.mp hpw
    exact (List.nodup_cons.mp hd).1
  have hfresh (x : ℕ × ℕ) (hx : x ∈ rest) : p ≠ x.1 := by
    intro he
    apply hn
    rw [he]
    exact List.mem_map_of_mem hx
  refine ⟨hrest, hp, hp.coprime_iff_not_dvd.mp (coprime_coordinateProduct hp hrest.1 hfresh), ?_⟩
  have hnum := (hperm.map (fun x => x.1 ^ x.2)).prod_nat
  simpa [number, Nat.mul_comm] using hnum

theorem cover_proper_central {n lo hi : ℕ}
    (h : Covered n.properDivisors lo hi) (hlo : lo ≤ hi)
    (hhi : hi ≤ ∑ d ∈ n.properDivisors, d)
    (hmid : (∑ d ∈ n.properDivisors, d) / 2 ≤ hi) :
    Covered n.properDivisors lo ((∑ d ∈ n.properDivisors, d) - lo) := by
  intro x hx hy
  by_cases hx' : x ≤ hi
  · exact h x hx hx'
  · exact subsetSumIntervalReflect h hlo hhi x (by omega) hy

structure CentralCoverData where
  seed : List ℕ
  growth : List ℕ
  low : ℕ
  seedHigh : ℕ

def CentralCoverData.ok (data : CentralCoverData) (n total : ℕ) : Bool :=
  let high := data.seedHigh + data.growth.sum
  divisorListOk n (data.seed ++ data.growth) &&
    bitIntervalOk data.seed data.low data.seedHigh &&
    growIntervalOk data.low data.seedHigh data.growth &&
    decide (data.low ≤ high ∧ high ≤ total ∧ total / 2 ≤ high)

theorem CentralCoverData.sound {data : CentralCoverData} {n total : ℕ}
    (hsum : ∑ d ∈ n.properDivisors, d = total) (h : data.ok n total = true) :
    Covered n.properDivisors data.low (total - data.low) := by
  simp only [CentralCoverData.ok, Bool.and_eq_true, decide_eq_true_eq] at h
  rw [← hsum]
  exact cover_proper_central (cover_of_validated_growth h.1.1.1 h.1.1.2 h.1.2)
    h.2.1 (hsum.symm ▸ h.2.2.1) (hsum.symm ▸ h.2.2.2)

end OddWeirdSubproblems

namespace OddWeirdSubproblems

open Finset

private theorem affine_mul_bound_of_le {base u a b c : ℕ}
    (hbase : 0 < base) (hu : base ≤ u) (h : a * base + c ≤ b * base) :
    a * u + c ≤ b * u := by
  have hab : a ≤ b := (Nat.mul_le_mul_right_iff hbase).mp (le_trans (Nat.le_add_right _ _) h)
  have hd := Nat.mul_le_mul_left (b - a) hu
  have hb := Nat.sub_add_cancel hab
  have hb₁ := congrArg (· * base) hb
  have hb₂ := congrArg (· * u) hb
  rw [Nat.add_mul] at hb₁ hb₂
  omega

def FreshIntervalBudget (base P r C G M : ℕ) : Prop :=
  let R := base * (P - 2 * r)
  let Z := base * P
  let K := (2 * C - 1) * P
  2 * r * G * Z + M * K ≤ M * R ∧ Z + K ≤ (P + 1) * R

instance (base P r C G M : ℕ) : Decidable (FreshIntervalBudget base P r C G M) := by
  unfold FreshIntervalBudget
  infer_instance

theorem FreshIntervalBudget.lift {base P r C G M u v p a : ℕ}
    (hbudget : FreshIntervalBudget base P r C G M) (hbase : 0 < base) (hle : base ≤ u)
    (hC : 0 < C) (hP : 2 * r < P) (hPt : P ≤ p)
    (hp : p.Prime) (hpu : ¬ p ∣ u) (hdef : u.Deficient)
    (hcop : u.Coprime v) (hA : (u * v).Abundant)
    (hcard : v.primeFactors.card ≤ r) (hmin : ∀ q ∈ v.primeFactors, p ≤ q)
    (hM : M ∣ 2 * u - ∑ d ∈ u.divisors, d) (hgap : GapUpTo u G)
    (hcover : Covered u.properDivisors C ((∑ d ∈ u.properDivisors, d) - C)) :
    Covered (u * p ^ a).properDivisors C ((∑ d ∈ (u * p ^ a).properDivisors, d) - C) := by
  let T := ∑ d ∈ u.properDivisors, d
  let delta := 2 * u - ∑ d ∈ u.divisors, d
  let k := 2 * C - 1
  have hu := hbase.trans_le hle
  have hp0 : 0 < P := Nat.zero_le _ |>.trans_lt hP
  have hT : T < u := hdef
  have hs := Nat.sum_divisors_eq_sum_properDivisors_add_self (n := u)
  have hdelta : 0 < delta := by dsimp [delta, T] at *; omega
  have hM0 : 0 < M := Nat.pos_of_dvd_of_pos hM hdelta
  have hMle := Nat.le_of_dvd hdelta hM
  have ⟨hpbound, hTbound⟩ :=
    freshPrimeBudget_of_coprime_completion hdef hcop hA hp.one_lt hP.le hPt hcard hmin
  change delta * p < 2 * r * u at hpbound
  change (P - 2 * r) * u < P * T at hTbound
  have ha₁ : (2 * r * G * P) * u + M * (k * P) ≤ (M * (P - 2 * r)) * u := by
    apply affine_mul_bound_of_le hbase hle
    simpa only [FreshIntervalBudget, k, Nat.mul_left_comm, Nat.mul_comm, Nat.mul_assoc] using hbudget.1
  have hb₁ : p * G + k ≤ T := by
    apply (Nat.mul_le_mul_right_iff (Nat.mul_pos hM0 hp0)).mp
    calc
      (p * G + k) * (M * P) ≤ (2 * r * G * P) * u + M * (k * P) := by
        have hm := Nat.mul_le_mul_right (G * P)
          ((Nat.mul_le_mul_right p hMle).trans hpbound.le)
        rw [Nat.add_mul]
        apply Nat.add_le_add
        · simpa only [Nat.mul_left_comm, Nat.mul_comm, Nat.mul_assoc] using hm
        · exact le_of_eq (by ac_rfl)
      _ ≤ (M * (P - 2 * r)) * u := ha₁
      _ ≤ T * (M * P) := by
        simpa only [Nat.mul_left_comm, Nat.mul_comm, Nat.mul_assoc] using
          Nat.mul_le_mul_left M hTbound.le
  have ha₂ : P * u + k * P ≤ ((P + 1) * (P - 2 * r)) * u := by
    apply affine_mul_bound_of_le hbase hle
    simpa only [FreshIntervalBudget, k, Nat.mul_left_comm, Nat.mul_comm, Nat.mul_assoc] using hbudget.2
  have hb₂ : u + k ≤ (p + 1) * T := by
    apply (Nat.mul_le_mul_right_iff hp0).mp
    calc
      (u + k) * P = P * u + k * P := by rw [Nat.add_mul, mul_comm u P]
      _ ≤ ((P + 1) * (P - 2 * r)) * u := ha₂
      _ ≤ ((P + 1) * T) * P := by
        simpa only [Nat.mul_left_comm, Nat.mul_comm, Nat.mul_assoc] using
          Nat.mul_le_mul_left (P + 1) hTbound.le
      _ ≤ ((p + 1) * T) * P := by
        exact Nat.mul_le_mul_right P (Nat.mul_le_mul_right T (Nat.succ_le_succ hPt))
  have ha := cover_raise_coprime_prime_power_add (a := 0) hu hp hpu hC
    (Finset.sort_nodup _ _) (Finset.sort_toFinset _ _) hgap.prefixGapBound_sort
  simp only [pow_zero, mul_one, zero_add, pow_one] at ha
  refine ha hcover (by dsimp [k] at hb₁; omega) ?_ a
  change u + 2 * C ≤ T + p * T + 1
  rw [Nat.add_mul, Nat.one_mul] at hb₂
  dsimp [k] at hb₂
  omega

theorem coordinatePrime_dvd_exists {p : ℕ} {ys : Coordinates} (hp : p.Prime)
    (hvalid : ∀ x ∈ ys, x.1.Prime) (hd : p ∣ number ys) : ∃ x ∈ ys, x.1 = p := by
  induction ys with
  | nil =>
    have h := Nat.dvd_one.mp (show p ∣ 1 by simpa [number] using hd)
    exact (hp.ne_one h).elim
  | cons y ys ih =>
    rw [number_cons] at hd
    rcases hp.dvd_mul.mp hd with h | h
    · rcases (Nat.dvd_prime (hvalid y (by simp))).mp (hp.dvd_of_dvd_pow h) with h | h
      · exact (hp.ne_one h).elim
      · exact ⟨y, by simp, h.symm⟩
    · obtain ⟨q, hq, he⟩ := ih (fun x hx => hvalid x (List.mem_cons_of_mem _ hx)) h
      exact ⟨q, List.mem_cons_of_mem _ hq, he⟩

theorem primeFactors_card_number_le {ys : Coordinates} (hv : ∀ x ∈ ys, x.1.Prime) :
    (number ys).primeFactors.card ≤ ys.length := by
  have hsub : (number ys).primeFactors ⊆ (ys.map Prod.fst).toFinset := by
    intro p hp
    obtain ⟨x, hx, he⟩ := coordinatePrime_dvd_exists
      (Nat.prime_of_mem_primeFactors hp) hv (Nat.dvd_of_mem_primeFactors hp)
    exact List.mem_toFinset.mpr (List.mem_map.mpr ⟨x, hx, he⟩)
  exact (card_le_card hsub).trans (by simpa using List.toFinset_card_le (ys.map Prod.fst))

theorem properDivisors_subset_of_dvd {u v : ℕ} (hv : 0 < v) (huv : u ∣ v) :
    u.properDivisors ⊆ v.properDivisors := by
  intro d h
  obtain ⟨hd, hlt⟩ := Nat.mem_properDivisors.mp h
  exact Nat.mem_properDivisors.mpr ⟨hd.trans huv, hlt.trans_le (Nat.le_of_dvd hv huv)⟩

private theorem tailFits_mono_start {xs : Coordinates} {p q : ℕ} (hle : p ≤ q)
    (h : TailFits q xs) : TailFits p xs := by
  cases xs with
  | nil => trivial
  | cons x xs =>
    obtain ⟨u, e⟩ := x
    exact ⟨hle.trans h.1, h.2⟩

theorem cover_fresh_tail_with_lift {base P r C G M u : ℕ} {ys : Coordinates}
    (hbase : 0 < base) (hbu : base ≤ u) (hG : 0 < G)
    (lift : ∀ {x v p a}, base ≤ x → P ≤ p → p.Prime → ¬ p ∣ x → x.Deficient →
      x.Coprime v → (x * v).Abundant → v.primeFactors.card ≤ r →
      (∀ q ∈ v.primeFactors, p ≤ q) → M ∣ (2 * x - ∑ d ∈ x.divisors, d) →
      GapUpTo x G →
      Covered x.properDivisors C ((∑ d ∈ x.properDivisors, d) - C) →
      Covered (x * p ^ a).properDivisors C ((∑ d ∈ (x * p ^ a).properDivisors, d) - C))
    (hv : PrimeCoordinates ys) (htail : TailFits P ys) (hr : ys.length ≤ r)
    (hcop : u.Coprime (number ys))
    (hA : (u * number ys).Abundant)
    (hprim : ∀ d ∈ (u * number ys).properDivisors, d.Deficient)
    (hsigma : M ∣ ∑ d ∈ u.divisors, d) (h2u : M ∣ 2 * u)
    (hCT : 2 * C ≤ ∑ d ∈ u.properDivisors, d)
    (hlow : DenseLowSums u.properDivisors C G)
    (hcover : Covered u.properDivisors C ((∑ d ∈ u.properDivisors, d) - C)) :
    Covered (u * number ys).properDivisors C ((∑ d ∈ (u * number ys).properDivisors, d) - C) := by
  induction ys generalizing u with
  | nil => simpa [number] using hcover
  | cons y ys ih =>
    obtain ⟨p, e⟩ := y
    obtain ⟨hPt, _, hp, _, he, htail'⟩ := htail
    have hu : 0 < u := hbase.trans_le hbu
    have hv' : PrimeCoordinates ys :=
      ⟨fun x hx => hv.1 x (List.mem_cons_of_mem _ hx), (List.pairwise_cons.mp hv.2).2⟩
    have he' : 1 ≤ e := by omega
    have hnum : 1 < number ((p, e) :: ys) := by
      rw [number_cons]
      have hw : p ≤ p ^ e := by simpa using Nat.pow_le_pow_right hp.pos he'
      exact (hp.one_lt.trans_le hw).trans_le (Nat.le_mul_of_pos_right _ (number_pos hv'.1))
    have hdef : u.Deficient := hprim u (Nat.mem_properDivisors.mpr
      ⟨dvd_mul_right _ _, by simpa using Nat.mul_lt_mul_of_pos_left hnum hu⟩)
    have hM := Nat.dvd_sub h2u hsigma
    have hpmin (q : ℕ) (hq : q ∈ (number ((p, e) :: ys)).primeFactors) : p ≤ q := by
      obtain ⟨x, hx, hxe⟩ := coordinatePrime_dvd_exists (Nat.prime_of_mem_primeFactors hq)
        hv.1 (Nat.dvd_of_mem_primeFactors hq)
      rcases List.mem_cons.mp hx with rfl | hx
      · exact hxe.symm ▸ le_rfl
      · exact hxe ▸ ((List.pairwise_cons.mp hv.2).1 x hx).le
    have hpu : u.Coprime p := by
      apply hcop.of_dvd_right
      rw [number_cons]
      exact (dvd_pow_self p (by omega : e ≠ 0)).trans (dvd_mul_right _ _)
    have hc : Covered (u * p ^ e).properDivisors C
        ((∑ d ∈ (u * p ^ e).properDivisors, d) - C) :=
      lift hbu hPt hp (hp.coprime_iff_not_dvd.mp hpu.symm) hdef
        hcop hA ((primeFactors_card_number_le hv.1).trans hr) hpmin hM
        (gapUpTo_of_central_and_low hG hCT hcover hlow) hcover
    let u' := u * p ^ e
    have hu' : 0 < u' := Nat.mul_pos hu (pow_pos hp.pos _)
    have hdiv : u ∣ u' := dvd_mul_right _ _
    have hsub := properDivisors_subset_of_dvd hu' hdiv
    have heq : u * number ((p, e) :: ys) = u' * number ys := by
      rw [number_cons, Nat.mul_assoc]
    rw [heq] at hA hprim ⊢
    apply ih (hbu.trans (Nat.le_of_dvd hu' hdiv)) hv' _ _ _ hA hprim _ _
      (hCT.trans (sum_le_sum_of_subset hsub)) (hlow.mono hsub) hc
    · exact tailFits_mono_start (show P ≤ p + 2 by omega) htail'
    · exact (Nat.le_succ _).trans hr
    · apply Nat.Coprime.mul_left
      · apply hcop.of_dvd_right
        rw [number_cons]
        exact dvd_mul_left _ _
      · apply Nat.Coprime.pow_left
        exact coprime_coordinateProduct hp hv'.1
          (fun x hx => ((List.pairwise_cons.mp hv.2).1 x hx).ne)
    · change M ∣ ∑ d ∈ (u * p ^ e).divisors, d
      rw [(hpu.pow_right e).sum_divisors_mul]
      exact hsigma.trans (dvd_mul_right _ _)
    · exact h2u.trans (by dsimp [u']; rw [← Nat.mul_assoc]; exact dvd_mul_right _ _)

theorem cover_fresh_tail {base P r C G M u : ℕ} {ys : Coordinates}
    (hbase : 0 < base) (hbu : base ≤ u) (hC : 0 < C) (hG : 0 < G)
    (hP : 2 * r < P) (hbudget : FreshIntervalBudget base P r C G M)
    (hv : PrimeCoordinates ys) (htail : TailFits P ys) (hr : ys.length ≤ r)
    (hcop : u.Coprime (number ys))
    (hA : (u * number ys).Abundant)
    (hprim : ∀ d ∈ (u * number ys).properDivisors, d.Deficient)
    (hsigma : M ∣ ∑ d ∈ u.divisors, d) (h2u : M ∣ 2 * u)
    (hCT : 2 * C ≤ ∑ d ∈ u.properDivisors, d)
    (hlow : DenseLowSums u.properDivisors C G)
    (hcover : Covered u.properDivisors C ((∑ d ∈ u.properDivisors, d) - C)) :
    Covered (u * number ys).properDivisors C ((∑ d ∈ (u * number ys).properDivisors, d) - C) :=
  cover_fresh_tail_with_lift hbase hbu hG (fun hx => hbudget.lift hbase hx hC hP)
    hv htail hr hcop hA hprim hsigma h2u hCT hlow hcover

end OddWeirdSubproblems

namespace OddWeirdSubproblems

open Finset

private def properSum (n : ℕ) : ℕ := ∑ d ∈ n.properDivisors, d

private theorem sumDivisors_fresh_pow {u q : ℕ} (hq : q.Prime) (hqu : ¬ q ∣ u)
    (a : ℕ) :
    (∑ d ∈ (u * q ^ a).divisors, d) =
      (∑ d ∈ u.divisors, d) * ∑ j ∈ range (a + 1), q ^ j := by
  rw [((hq.coprime_iff_not_dvd.mpr hqu).symm.pow_right a).sum_divisors_mul,
    Nat.sum_divisors_prime_pow hq]

private theorem properSum_fresh_pow_step {u q : ℕ} (hq : q.Prime) (hqu : ¬ q ∣ u)
    (a : ℕ) :
    properSum (u * q ^ (a + 1)) = properSum (u * q ^ a) + q ^ (a + 1) * properSum u +
      u * q ^ a := by
  have h := calc
    (∑ d ∈ (u * q ^ (a + 1)).divisors, d) =
        (∑ d ∈ u.divisors, d) * ∑ j ∈ range (a + 1 + 1), q ^ j :=
      sumDivisors_fresh_pow hq hqu (a + 1)
    _ = (∑ d ∈ (u * q ^ a).divisors, d) + (∑ d ∈ u.divisors, d) * q ^ (a + 1) := by
      rw [sum_range_succ, Nat.mul_add, sumDivisors_fresh_pow hq hqu a]
  rw [Nat.sum_divisors_eq_sum_properDivisors_add_self (n := u * q ^ (a + 1)),
    Nat.sum_divisors_eq_sum_properDivisors_add_self (n := u * q ^ a),
    Nat.sum_divisors_eq_sum_properDivisors_add_self (n := u), Nat.add_mul,
    mul_comm (∑ d ∈ u.properDivisors, d)] at h
  unfold properSum
  omega

private theorem properSum_scale_le_fresh_pow {u q : ℕ} (hq : q.Prime) (hqu : ¬ q ∣ u)
    (a : ℕ) : q * properSum (u * q ^ a) ≤ properSum (u * q ^ (a + 1)) := by
  have h : (∑ d ∈ (u * q ^ (a + 1)).divisors, d) =
      q * (∑ d ∈ (u * q ^ a).divisors, d) + ∑ d ∈ u.divisors, d := by
    rw [sumDivisors_fresh_pow hq hqu (a + 1), sumDivisors_fresh_pow hq hqu a,
      geom_sum_succ, Nat.mul_add, Nat.mul_one, mul_left_comm]
  have hscale : u * q ^ (a + 1) = q * (u * q ^ a) := by
    rw [pow_succ]
    ac_rfl
  rw [Nat.sum_divisors_eq_sum_properDivisors_add_self (n := u * q ^ (a + 1)),
    Nat.sum_divisors_eq_sum_properDivisors_add_self (n := u * q ^ a), Nat.mul_add] at h
  conv at h =>
    lhs
    arg 2
    rw [hscale]
  unfold properSum
  omega

private theorem cover_raise_fresh_pow_alternate {u q a C G : ℕ} {ds : List ℕ}
    (hu : 1 < u) (hq : q.Prime) (hqu : ¬ q ∣ u) (hnd : ds.Nodup)
    (hds : ds.toFinset = u.properDivisors.erase 1) (hgap : PrefixGapBound (G + 1) ds) :
    let m := u * q ^ a
    let v := q ^ (a + 1)
    let T := properSum m
    Covered m.properDivisors C (T - C) →
      v + 2 * C ≤ T + 1 →
      m + 2 * C ≤ T + v + 1 →
      v * G + 2 * C ≤ T + m + 1 →
      Covered (u * q ^ (a + 1)).properDivisors C (properSum (u * q ^ (a + 1)) - C) := by
  intro m v T hcover hfirst hsecond hthird
  let n := u * q ^ (a + 1)
  let ws := ds.map (v * ·)
  have hv : 0 < v := pow_pos hq.pos _
  have hm : 0 < m := Nat.mul_pos (Nat.zero_lt_one.trans hu) (pow_pos hq.pos _)
  have hn : n = m * q := by simp only [n, m, pow_succ, mul_assoc]
  have hvnot : ¬ v ∣ m := by
    intro h
    apply hqu
    apply (Nat.mul_dvd_mul_iff_left (pow_pos hq.pos a)).mp
    simpa only [v, m, pow_succ, mul_comm q, mul_comm u] using h
  have hvm : v ≠ m := fun he => hvnot (he ▸ dvd_rfl)
  have hvfresh : v ∉ m.properDivisors := fun h => hvnot (Nat.mem_properDivisors.mp h).1
  have hmfresh : m ∉ insert v m.properDivisors := by
    intro h
    rcases Finset.mem_insert.mp h with he | hm'
    · exact hvm he.symm
    · exact Nat.self_notMem_properDivisors hm'
  have hcover₁ := subsetSumIntervalInsert hvfresh hcover (by omega : C + v ≤ T - C + 1)
  have hcover₂ := subsetSumIntervalInsert hmfresh hcover₁ (by omega : C + m ≤ T - C + v + 1)
  have hinterval : Covered (insert m (insert v m.properDivisors)) C (T + v + m - C) := by
    rwa [show T + v + m - C = T - C + v + m by omega]
  have hval {d : ℕ} (hd : d ∈ ws.toFinset) : ∃ e ∈ u.properDivisors, e ≠ 1 ∧ d = v * e := by
    obtain ⟨e, he, heq⟩ := List.mem_map.mp (List.mem_toFinset.mp hd)
    have hei := Finset.mem_erase.mp (hds ▸ List.mem_toFinset.mpr he)
    exact ⟨e, hei.2, hei.1, heq.symm⟩
  have hdisjoint : Disjoint (insert m (insert v m.properDivisors)) ws.toFinset := by
    apply Finset.disjoint_left.mpr
    intro d hd hd'
    obtain ⟨e, _, he, rfl⟩ := hval hd'
    rcases Finset.mem_insert.mp hd with hm' | hd
    · exact hvnot ⟨e, hm'.symm⟩
    rcases Finset.mem_insert.mp hd with hv' | hd
    · apply he
      apply mul_left_cancel₀ hv.ne'
      simpa only [mul_one] using hv'
    · exact hvnot ((dvd_mul_right v e).trans (Nat.mem_properDivisors.mp hd).1)
  have hws : ws.Nodup := hnd.map (mul_right_injective₀ hv.ne')
  have hwidth : v * (G + 1) + 2 * C ≤ T + v + m + 1 := by
    rw [Nat.mul_add, Nat.mul_one]
    omega
  have hfinal := cover_of_fresh_prefixGapBound hinterval hws hdisjoint (hgap.scale v) hwidth
  have hsub : insert m (insert v m.properDivisors) ∪ ws.toFinset ⊆ n.properDivisors := by
    have hmlt : m < n := by
      rw [hn]
      simpa only [mul_one] using Nat.mul_lt_mul_of_pos_left hq.one_lt hm
    have hmdvd : m ∣ n := hn ▸ dvd_mul_right m q
    intro d hd
    rcases Finset.mem_union.mp hd with hd | hd
    · rcases Finset.mem_insert.mp hd with rfl | hd
      · exact Nat.mem_properDivisors.mpr ⟨hmdvd, hmlt⟩
      rcases Finset.mem_insert.mp hd with rfl | hd
      · refine Nat.mem_properDivisors.mpr ⟨dvd_mul_left v u, ?_⟩
        simpa only [one_mul] using Nat.mul_lt_mul_of_pos_right hu hv
      · obtain ⟨hdvd, hlt⟩ := Nat.mem_properDivisors.mp hd
        exact Nat.mem_properDivisors.mpr ⟨hdvd.trans hmdvd, hlt.trans hmlt⟩
    · obtain ⟨e, he, _, rfl⟩ := hval hd
      obtain ⟨hdvd, hlt⟩ := Nat.mem_properDivisors.mp he
      change v * e ∈ (u * v).properDivisors
      rw [mul_comm u v]
      exact Nat.mem_properDivisors.mpr ⟨mul_dvd_mul_left v hdvd, Nat.mul_lt_mul_of_pos_left hlt hv⟩
  have hone : 1 ∈ u.properDivisors := Nat.mem_properDivisors.mpr ⟨one_dvd _, hu⟩
  have hsum : ds.sum + 1 = properSum u := by
    rw [← sum_toFinset_of_nodup hnd, hds]
    exact Finset.sum_erase_add _ (fun d => d) hone
  have hscaled : ws.sum = v * ds.sum := by
    simpa only [List.map_id, ws, id_eq] using List.sum_map_mul_left ds id v
  have htotal : properSum n = T + v + m + ws.sum := by
    rw [show properSum n = T + v * properSum u + m from properSum_fresh_pow_step hq hqu a,
      ← hsum, hscaled, Nat.mul_add, Nat.mul_one]
    ac_rfl
  change Covered n.properDivisors C (properSum n - C)
  rw [htotal]
  exact cover_mono hsub hfinal

theorem cover_coprime_prime_power_alternate {u q C G : ℕ}
    (hu : 0 < u) (hq : q.Prime) (hqu : ¬ q ∣ u) (hC : 0 < C)
    (hgap : GapUpTo u G) :
    let T := ∑ d ∈ u.properDivisors, d
    Covered u.properDivisors C (T - C) →
    q + 2 * C ≤ T + 1 →
    u + 2 * C ≤ T + q + 1 →
    q * G + 2 * C ≤ T + u + 1 →
    ∀ a : ℕ, Covered (u * q ^ a).properDivisors C ((∑ d ∈ (u * q ^ a).properDivisors, d) - C) := by
  intro T hcover hfirst hsecond hthird
  have hu' : 1 < u := by
    by_contra! h
    have he : u = 1 := by omega
    have hT : T = 0 := by simp [T, he]
    have hp := hq.one_lt
    omega
  let ds := (u.properDivisors.erase 1).sort
  have hone : 1 ∈ u.properDivisors := Nat.mem_properDivisors.mpr ⟨one_dvd _, hu'⟩
  have hs : u.properDivisors.sort = 1 :: ds := by
    calc
      _ = (insert 1 (u.properDivisors.erase 1)).sort := by rw [Finset.insert_erase hone]
      _ = _ := by
        apply Finset.sort_insert (· ≤ ·)
        · intro d hd
          have hdiv := (Nat.mem_properDivisors.mp ((Finset.mem_erase.mp hd).2)).1
          exact Nat.pos_of_dvd_of_pos hdiv hu
        · simp
  have hds : ds.toFinset = u.properDivisors.erase 1 := Finset.sort_toFinset _ _
  have hrest : PrefixGapBound (G + 1) ds := by
    have hg := hgap.prefixGapBound_sort
    rw [hs] at hg
    exact hg.2
  let M (a : ℕ) := u * q ^ a
  let V (a : ℕ) := q ^ (a + 1)
  let S (a : ℕ) := properSum (M a)
  have hpush {x y : ℕ} (h : x + 2 * C ≤ y + 1) : q * x + 2 * C ≤ q * y + 1 := by
    have hm := Nat.mul_le_mul_left q (show x + (2 * C - 1) ≤ y by omega)
    rw [Nat.mul_add] at hm
    have hl := Nat.le_mul_of_pos_left (2 * C - 1) hq.pos
    omega
  have hall (a : ℕ) : Covered (M a).properDivisors C (S a - C) ∧
      V a + 2 * C ≤ S a + 1 ∧ M a + 2 * C ≤ S a + V a + 1 ∧
      V a * G + 2 * C ≤ S a + M a + 1 := by
    induction a with
    | zero => simpa [M, V, S, properSum, T] using ⟨hcover, hfirst, hsecond, hthird⟩
    | succ a ih =>
      obtain ⟨hc, h₁, h₂, h₃⟩ := ih
      have hm : M (a + 1) = q * M a := by unfold M; rw [pow_succ]; ac_rfl
      have hv : V (a + 1) = q * V a := by simp only [V, pow_succ']
      have hs : q * S a ≤ S (a + 1) := properSum_scale_le_fresh_pow hq hqu a
      refine ⟨cover_raise_fresh_pow_alternate (a := a) hu' hq hqu
          (Finset.sort_nodup _ _) hds hrest hc h₁ h₂ h₃, ?_, ?_, ?_⟩
      · rw [hv]
        exact (hpush h₁).trans (Nat.add_le_add_right hs 1)
      · rw [hm, hv]
        have hh := hpush h₂
        rw [Nat.mul_add] at hh
        exact hh.trans (Nat.add_le_add_right (Nat.add_le_add_right hs _) 1)
      · rw [hv, mul_assoc, hm]
        have hh := hpush h₃
        rw [Nat.mul_add] at hh
        exact hh.trans (Nat.add_le_add_right (Nat.add_le_add_right hs _) 1)
  intro a
  exact (hall a).1

end OddWeirdSubproblems

namespace OddWeirdSubproblems

def FreshTwoCaseBudget (base P r C G M : ℕ) : Prop :=
  let R := base * (P - 2 * r)
  let Z := base * P
  let K := (2 * C - 1) * P
  2 * r * Z + M * K ≤ M * R ∧
    Z + K ≤ (P + 1) * R ∧
    2 * r * G * Z + M * K ≤ M * (R + Z) ∧
    2 * r * G * base + (G + 1) * K ≤ R

instance (base P r C G M : ℕ) : Decidable (FreshTwoCaseBudget base P r C G M) := by
  unfold FreshTwoCaseBudget
  infer_instance

private theorem affine_mul_mono {base u a b c : ℕ}
    (hb : 0 < base) (hu : base ≤ u) (h : a * base + c ≤ b * base) :
    a * u + c ≤ b * u := by
  have hab : a ≤ b := (Nat.mul_le_mul_right_iff hb).mp (le_trans (Nat.le_add_right _ _) h)
  have hbase : c ≤ (b - a) * base := by
    have he := congrArg (· * base) (Nat.sub_add_cancel hab)
    rw [Nat.add_mul] at he
    omega
  have hnew := hbase.trans (Nat.mul_le_mul_left _ hu)
  have he := congrArg (· * u) (Nat.sub_add_cancel hab)
  rw [Nat.add_mul] at he
  omega

theorem FreshTwoCaseBudget.alternatives {base u T P r C G M p : ℕ}
    (h : FreshTwoCaseBudget base P r C G M) (hbase : 0 < base) (hle : base ≤ u)
    (hC : 0 < C) (hP : 2 * r < P) (hPp : P ≤ p) (hT : T < u)
    (hM : M ∣ u - T) (hprime : (u - T) * p < 2 * r * u)
    (hratio : (P - 2 * r) * u < P * T) :
    (p * G + 2 * C ≤ T + 1 ∧ u + 2 * C ≤ (p + 1) * T + 1) ∨
    (p + 2 * C ≤ T + 1 ∧ u + 2 * C ≤ T + p + 1 ∧
      p * G + 2 * C ≤ T + u + 1) := by
  let k := 2 * C - 1
  let R := (P - 2 * r) * u
  have hPpos : 0 < P := by omega
  have hdelta : 0 < u - T := by omega
  have hMpos : 0 < M := Nat.pos_of_dvd_of_pos hM hdelta
  have hMle : M ≤ u - T := Nat.le_of_dvd hdelta hM
  have hMp : M * p ≤ 2 * r * u := ((Nat.mul_le_mul_right p hMle).trans_lt hprime).le
  have hk₂ : k + 1 = 2 * C := by dsimp [k]; omega
  change 2 * r * (base * P) + M * (k * P) ≤ M * (base * (P - 2 * r)) ∧
    base * P + k * P ≤ (P + 1) * (base * (P - 2 * r)) ∧
    2 * r * G * (base * P) + M * (k * P) ≤ M * (base * (P - 2 * r) + base * P) ∧
    2 * r * G * base + (G + 1) * (k * P) ≤ base * (P - 2 * r) at h
  have ha : 2 * r * (u * P) + M * (k * P) ≤ M * R := by
    have hx : (2 * r * P) * base + M * (k * P) ≤ (M * (P - 2 * r)) * base :=
      by simpa only [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using h.1
    simpa only [R, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using affine_mul_mono hbase hle hx
  have hb : u * P + k * P ≤ (P + 1) * R := by
    have hx : P * base + k * P ≤ ((P + 1) * (P - 2 * r)) * base :=
      by simpa only [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using h.2.1
    simpa only [R, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using affine_mul_mono hbase hle hx
  have hc : 2 * r * G * (u * P) + M * (k * P) ≤ M * (R + P * u) := by
    have hx : (2 * r * G * P) * base + M * (k * P) ≤
        (M * (P - 2 * r + P)) * base := by
      simp only [Nat.mul_add, Nat.add_mul]
      simpa only [Nat.mul_add, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using h.2.2.1
    have hv := affine_mul_mono hbase hle hx
    simpa only [R, Nat.mul_add, Nat.add_mul, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hv
  have hd : 2 * r * G * u + (G + 1) * (k * P) ≤ R := by
    apply affine_mul_mono hbase hle
    simpa only [Nat.mul_comm (P - 2 * r) base] using h.2.2.2
  have hR : R ≤ P * T := hratio.le
  have hqk : p + k ≤ T := by
    apply (Nat.mul_le_mul_right_iff (Nat.mul_pos hMpos hPpos)).mp
    calc
      (p + k) * (M * P) = (M * p) * P + M * (k * P) := by rw [Nat.add_mul]; ac_rfl
      _ ≤ 2 * r * (u * P) + M * (k * P) := by
        simpa only [Nat.mul_assoc] using Nat.add_le_add_right (Nat.mul_le_mul_right P hMp) _
      _ ≤ M * R := ha
      _ ≤ T * (M * P) := by
        simpa only [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using Nat.mul_le_mul_left M hR
  have hlast : u + k ≤ (p + 1) * T := by
    apply (Nat.mul_le_mul_right_iff hPpos).mp
    rw [Nat.add_mul]
    calc
      _ ≤ (P + 1) * R := hb
      _ ≤ (P + 1) * (P * T) := Nat.mul_le_mul_left _ hR
      _ ≤ (p + 1) * T * P := by
        have hm := Nat.mul_le_mul_right (P * T) (Nat.succ_le_succ hPp)
        simpa only [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hm
  by_cases hsmall : p * G + k ≤ T
  · left
    omega
  · right
    have hscaled : p * G + k ≤ T + u := by
      apply (Nat.mul_le_mul_right_iff (Nat.mul_pos hMpos hPpos)).mp
      calc
        (p * G + k) * (M * P) = (M * p) * (G * P) + M * (k * P) := by rw [Nat.add_mul]; ac_rfl
        _ ≤ 2 * r * G * (u * P) + M * (k * P) := by
          simpa only [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using
            Nat.add_le_add_right (Nat.mul_le_mul_right (G * P) hMp) _
        _ ≤ M * (R + P * u) := hc
        _ ≤ (T + u) * (M * P) := by
          simpa only [Nat.mul_add, Nat.add_mul, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using
            Nat.mul_le_mul_left M (Nat.add_le_add_right hR (P * u))
    have hmiss : G * (u - T + k) + k ≤ T := by
      apply (Nat.mul_le_mul_right_iff hPpos).mp
      have huT : (u - T) * P + T * P = u * P := by rw [← Nat.add_mul, Nat.sub_add_cancel hT.le]
      have hd₀ : P * u - T * P ≤ 2 * r * u := by
        have hsum : R + 2 * r * u = P * u := by
          unfold R
          rw [← Nat.add_mul, Nat.sub_add_cancel hP.le]
        have hRT : R ≤ T * P := by simpa only [Nat.mul_comm T P] using hR
        exact Nat.sub_le_iff_le_add.mpr (by
          rw [← hsum, Nat.add_comm]
          exact Nat.add_le_add_left hRT _)
      have he := Nat.mul_le_mul_left G hd₀
      have hd₁ : (u - T) * P = P * u - T * P := by
        rw [Nat.mul_comm P u]
        omega
      rw [← hd₁] at he
      calc
        _ = G * ((u - T) * P) + (G + 1) * (k * P) := by
          simp only [Nat.add_mul, Nat.mul_add, Nat.one_mul]
          ac_rfl
        _ ≤ 2 * r * G * u + (G + 1) * (k * P) := by
          simpa only [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using
            Nat.add_le_add_right he ((G + 1) * (k * P))
        _ ≤ R := hd
        _ ≤ T * P := by simpa only [Nat.mul_comm T P] using hR
    have hwide : u - T + k < p := by
      by_contra! hm
      have hx := Nat.mul_le_mul_right G hm
      rw [Nat.mul_comm (u - T + k) G] at hx
      omega
    exact ⟨by omega, by omega, by omega⟩

open Finset

theorem FreshTwoCaseBudget.lift {base P r C G M u v p a : ℕ}
    (hbudget : FreshTwoCaseBudget base P r C G M) (hbase : 0 < base) (hle : base ≤ u)
    (hC : 0 < C) (hP : 2 * r < P) (hPt : P ≤ p)
    (hp : p.Prime) (hpu : ¬ p ∣ u) (hdef : u.Deficient)
    (hcop : u.Coprime v) (hA : (u * v).Abundant)
    (hcard : v.primeFactors.card ≤ r) (hmin : ∀ q ∈ v.primeFactors, p ≤ q)
    (hM : M ∣ 2 * u - ∑ d ∈ u.divisors, d) (hgap : GapUpTo u G)
    (hcover : Covered u.properDivisors C ((∑ d ∈ u.properDivisors, d) - C)) :
    Covered (u * p ^ a).properDivisors C ((∑ d ∈ (u * p ^ a).properDivisors, d) - C) := by
  let T := ∑ d ∈ u.properDivisors, d
  have hsum : (∑ d ∈ u.divisors, d) = T + u := Nat.sum_divisors_eq_sum_properDivisors_add_self
  have hdeficiency : 2 * u - (∑ d ∈ u.divisors, d) = u - T := by rw [hsum]; omega
  obtain ⟨hprime, hratio⟩ :=
    freshPrimeBudget_of_coprime_completion hdef hcop hA hp.one_lt hP.le hPt hcard hmin
  rw [hdeficiency] at hprime hM
  obtain ⟨hw, hlast⟩ | ⟨hfirst, hsecond, hthird⟩ :=
    hbudget.alternatives hbase hle hC hP hPt hdef hM hprime hratio
  · have hstep := cover_raise_coprime_prime_power_add (a := 0) (hbase.trans_le hle) hp hpu hC
      (Finset.sort_nodup _ _) (Finset.sort_toFinset _ _) hgap.prefixGapBound_sort
    simp only [pow_zero, mul_one, zero_add, pow_one] at hstep
    apply hstep hcover hw _ a
    change u + 2 * C ≤ T + p * T + 1
    calc
      _ ≤ (p + 1) * T + 1 := hlast
      _ = _ := by rw [Nat.add_mul, Nat.one_mul]; ac_rfl
  · exact cover_coprime_prime_power_alternate (hbase.trans_le hle) hp hpu hC hgap
      hcover hfirst hsecond hthird a

theorem cover_fresh_tail_of_twoCaseBudget {base P r C G M u : ℕ} {ys : Coordinates}
    (hbase : 0 < base) (hbu : base ≤ u) (hC : 0 < C) (hG : 0 < G)
    (hP : 2 * r < P) (hbudget : FreshTwoCaseBudget base P r C G M)
    (hv : PrimeCoordinates ys) (htail : TailFits P ys) (hr : ys.length ≤ r)
    (hcop : u.Coprime (number ys))
    (hA : (u * number ys).Abundant)
    (hprim : ∀ d ∈ (u * number ys).properDivisors, d.Deficient)
    (hsigma : M ∣ ∑ d ∈ u.divisors, d) (h2u : M ∣ 2 * u)
    (hCT : 2 * C ≤ ∑ d ∈ u.properDivisors, d)
    (hlow : DenseLowSums u.properDivisors C G)
    (hcover : Covered u.properDivisors C ((∑ d ∈ u.properDivisors, d) - C)) :
    Covered (u * number ys).properDivisors C ((∑ d ∈ (u * number ys).properDivisors, d) - C) :=
  cover_fresh_tail_with_lift hbase hbu hG (fun hx => hbudget.lift hbase hx hC hP)
    hv htail hr hcop hA hprim hsigma h2u hCT hlow hcover

end OddWeirdSubproblems

namespace OddWeirdSubproblems

def CentralCoverData.growUntil (low target : ℕ) : ℕ → List ℕ → List ℕ
  | _, [] => []
  | high, d :: ds =>
    if high < target && low + d ≤ high + 1 then
      d :: CentralCoverData.growUntil low target (high + d) ds
    else []

def buildCentralCover (fs : Coordinates) : CentralCoverData :=
  let n := number fs
  let total := divisorSum fs - n
  let ds := (sortedDivisors fs).takeWhile (· < n)
  let seed := smallPrefix 1024 ds
  let low := effectiveLow (subsetBits seed) seed.sum
  let high := seed.sum - low
  let growth := CentralCoverData.growUntil low (total / 2) high (ds.drop seed.length)
  ⟨seed, growth, low, high⟩

theorem headRange_of_valid_core {ss : List Slot} {first stop : ℕ}
    (h : PrimeCoordinates (ss.map Slot.minimum) → HeadRangeClosed ss 0 first stop) :
    HeadRangeClosed ss 0 first stop := by
  intro q hlo hhi hp ho xs ys hmatch hvalid hw hproper
  have hc := minimum_valid hmatch.1 (primeCoordinates_left hvalid)
  have hpref : PrimeCoordinates (ss.map Slot.minimum) := by
    change PrimeCoordinates ((ss ++ [(⟨q, 1, false⟩ : Slot)]).map Slot.minimum) at hc
    rw [List.map_append] at hc
    exact primeCoordinates_left hc
  exact h hpref q hlo hhi hp ho xs ys hmatch hvalid hw hproper

end OddWeirdSubproblems

namespace OddWeirdSubproblems

def paletteModulus (b : Box) : ℕ :=
  Nat.gcd (2 * number b.minimum)
    ((b.slots.filter Slot.fixed).map fun s => powerSum s.prime s.exponent).prod

theorem fixedPowerSum_prod_dvd {ss : List Slot} {xs : Coordinates}
    (hfit : List.Forall₂ Slot.Fits ss xs) :
    ((ss.filter Slot.fixed).map fun s => powerSum s.prime s.exponent).prod ∣ divisorSum xs := by
  induction hfit with
  | nil => simp [divisorSum]
  | @cons s x ss xs hs _ ih =>
    cases hf : s.fixed
    · simpa [List.filter_cons, hf, divisorSum] using
        dvd_mul_of_dvd_right ih (powerSum x.1 x.2)
    · have hsum : powerSum s.prime s.exponent = powerSum x.1 x.2 := by
        rw [hs.2.1, hs.2.2.2 hf]
      simpa [List.filter_cons, hf, hsum, divisorSum] using
        Nat.mul_dvd_mul (dvd_rfl : powerSum x.1 x.2 ∣ powerSum x.1 x.2) ih

theorem paletteModulus_dvd_append {b : Box} {xs : Coordinates}
    (hfit : List.Forall₂ Slot.Fits b.slots xs) (tail : Coordinates) :
    paletteModulus b ∣ 2 * number (xs ++ tail) ∧
      paletteModulus b ∣ divisorSum (xs ++ tail) := by
  constructor
  · have hmin : number b.minimum ∣ number xs := minimum_dvd hfit
    have hg : paletteModulus b ∣ 2 * number b.minimum := Nat.gcd_dvd_left _ _
    rw [number_append]
    exact hg.trans (Nat.mul_dvd_mul_left 2 (dvd_mul_of_dvd_left hmin _))
  · have hg : paletteModulus b ∣
        ((b.slots.filter Slot.fixed).map fun s => powerSum s.prime s.exponent).prod :=
      Nat.gcd_dvd_right _ _
    rw [divisorSum_append]
    exact dvd_mul_of_dvd_left (hg.trans (fixedPowerSum_prod_dvd hfit)) _

end OddWeirdSubproblems

namespace OddWeirdSubproblems

open Finset

private theorem number_of_fits_mul {ss : List Slot} {xs : Coordinates}
    (h : List.Forall₂ Slot.Fits ss xs) :
    ∃ k : ℕ, 0 < k ∧ number xs = number (ss.map Slot.minimum) * k ∧
      ∀ q, q.Prime → q ∣ k → ∃ s ∈ ss, s.fixed = false ∧ s.prime = q := by
  induction h with
  | nil =>
    refine ⟨1, Nat.one_pos, by simp [number], ?_⟩
    exact fun q hq hd => (hq.ne_one (Nat.dvd_one.mp hd)).elim
  | @cons s x ss xs hx htail ih =>
    obtain ⟨hq, he, hle, hfix⟩ := hx
    obtain ⟨k, hk, hnumber, hprimes⟩ := ih
    let extra := x.2 - s.exponent
    refine ⟨s.prime ^ extra * k, Nat.mul_pos (pow_pos (he ▸ hq.pos) _) hk, ?_, ?_⟩
    · simp only [number_cons, List.map_cons, Slot.minimum, hnumber]
      rw [← he, ← Nat.add_sub_of_le hle, pow_add]
      dsimp [extra]
      ac_rfl
    · intro p hp hd
      rcases hp.dvd_mul.mp hd with h | h
      · have hf : s.fixed = false := by
          cases hf : s.fixed
          · rfl
          · have hzero : extra = 0 := by dsimp [extra]; rw [hfix hf]; simp
            rw [hzero, pow_zero] at h
            exact (hp.ne_one (Nat.dvd_one.mp h)).elim
        have hs : s.prime.Prime := he ▸ hq
        rcases (Nat.dvd_prime hs).mp (hp.dvd_of_dvd_pow h) with h | hp'
        · exact (hp.ne_one h).elim
        · exact ⟨s, by simp, hf, hp'.symm⟩
      · obtain ⟨t, ht, hfix', heq⟩ := hprimes p hp h
        exact ⟨t, List.mem_cons_of_mem _ ht, hfix', heq⟩

private theorem coprime_coordinate_concat {xs ys : Coordinates} (hv : PrimeCoordinates (xs ++ ys)) :
    (number xs).Coprime (number ys) := by
  apply Nat.coprime_list_prod_right_iff.mpr
  intro z hz
  obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hz
  have hy' := hv.1 y (List.mem_append_right _ hy)
  apply Nat.Coprime.pow_right
  apply Nat.Coprime.symm
  exact coprime_coordinateProduct hy'
    (primeCoordinates_left hv).1 (fun x hx =>
      ((List.pairwise_append.mp hv.2).2.2 x hx y hy).ne.symm)

theorem properSum_of_validCoordinates {fs : Coordinates} (hv : PrimeCoordinates fs) :
    ∑ d ∈ (number fs).properDivisors, d = divisorSum fs - number fs := by
  have hs := Nat.sum_divisors_eq_sum_properDivisors_add_self (n := number fs)
  rw [← divisorSum_eq hv] at hs
  omega

def paletteBudgetsOkAt (useAlternate : Bool) (b : Box) (M G : ℕ) (data : CentralCoverData) : Bool :=
  let fs := b.minimum
  let n := number fs
  let T := divisorSum fs - n
  let C := data.low
  lowDensityOk data.seed C G && lowModulusOk data.seed C M &&
    decide (0 < C ∧ 0 < G ∧ C ≤ n ∧ 2 * C ≤ T) &&
    b.slots.all (fun s => s.fixed || decide (0 < s.exponent ∧
      s.prime * G + 2 * C ≤ divisorSum (fs.erase s.minimum) + 1)) &&
    decide (b.remaining = 0 ∨ (2 * b.remaining < b.next ∧
      (FreshIntervalBudget n b.next b.remaining C G M ∨
        (useAlternate = true ∧ FreshTwoCaseBudget n b.next b.remaining C G M))))

def paletteBudgetsOkWith (useAlternate : Bool) (b : Box) (G : ℕ)
    (data : CentralCoverData) : Bool :=
  paletteBudgetsOkAt useAlternate b (paletteModulus b) G data

theorem paletteBudgetsOkAt_excludes {useAlternate : Bool} {b : Box} {M G : ℕ}
    {data : CentralCoverData} {Q : Coordinates → Prop}
    (hM : ∀ {xs}, List.Forall₂ Slot.Fits b.slots xs → Q xs → ∀ ys,
      M ∣ 2 * number (xs ++ ys) ∧ M ∣ divisorSum (xs ++ ys))
    (hdata : PrimeCoordinates b.minimum →
      Covered (number b.minimum).properDivisors data.low
        (divisorSum b.minimum - number b.minimum - data.low) ∧
      data.seed.Nodup ∧ data.seed.toFinset ⊆ (number b.minimum).properDivisors)
    (hok : paletteBudgetsOkAt useAlternate b M G data = true) :
    ∀ xs ys, b.Matches xs ys → Q xs → PrimeCoordinates (xs ++ ys) →
      (number (xs ++ ys)).Weird → (∀ d ∈ (number (xs ++ ys)).properDivisors, d.Deficient) →
      False := by
  intro xs ys hmatch hQ hv hw hprim
  have hxs := primeCoordinates_left hv
  have hys : PrimeCoordinates ys :=
    ⟨fun y hy => hv.1 y (List.mem_append_right _ hy), (List.pairwise_append.mp hv.2).2.1⟩
  have hbase := minimum_valid hmatch.1 hxs
  let n := number b.minimum
  let C := data.low
  let u := number xs
  simp only [paletteBudgetsOkAt, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq,
    List.all_eq_true] at hok
  obtain ⟨⟨⟨⟨hlow, hmod⟩, hc, hg, hcn, hcT⟩, hslots⟩, htail⟩ := hok
  obtain ⟨hcert, hsnd, hseedsub⟩ := hdata hbase
  have hbaseT := properSum_of_validCoordinates hbase
  have hfixedLow : DenseLowSums n.properDivisors C G := (lowDensityOk_sound hsnd hlow).mono hseedsub
  have hfixedMod : ∀ x < C, M ∣ x → HasSubsetSum n.properDivisors x := by
    intro x hx hdx
    obtain ⟨t, ht, hs⟩ := lowModulusOk_sound hsnd hmod x hx hdx
    exact ⟨t, ht.trans hseedsub, hs⟩
  have hn : 0 < n := number_pos hbase.1
  have hu : 0 < u := number_pos hxs.1
  obtain ⟨k, hk, heq, hprimes⟩ := number_of_fits_mul hmatch.1
  have heq' : u = n * k := heq
  have hnU : n ∣ u := ⟨k, heq'⟩
  have hNle : n ≤ u := Nat.le_of_dvd hu hnU
  have hsub := properDivisors_subset_of_dvd hu hnU
  have hcofactor (q : ℕ) (hp : q.Prime) (hd : q ∣ k) :
      q ∣ n ∧ q * G + 2 * C ≤ (∑ d ∈ (ordCompl[q] n).divisors, d) + 1 := by
    obtain ⟨s, hs, hfix, hp'⟩ := hprimes q hp hd
    obtain ⟨he, hbudget⟩ := (hslots s hs).resolve_left (by simp [hfix])
    have hsm : (q, s.exponent) ∈ b.minimum := by
      exact List.mem_map.mpr ⟨s, hs, by simp [Slot.minimum, hp']⟩
    let rest := b.minimum.erase (q, s.exponent)
    obtain ⟨hrest, hq, hnot, hnumber⟩ := erase_coordinate hbase hsm
    have hrest' : PrimeCoordinates rest := hrest
    have hnot' : ¬ q ∣ number rest := hnot
    have hnumber' : n = number rest * q ^ s.exponent := hnumber
    have hc : ordCompl[q] n = number rest := by
      rw [hnumber', Nat.mul_comm, Nat.ordCompl_pow_mul_of_not_dvd _ hq hnot']
    constructor
    · have hdvd : q ^ s.exponent ∣ n := by
        rw [hnumber']
        exact dvd_mul_left _ _
      exact (dvd_pow_self q he.ne').trans hdvd
    · rw [hc, ← divisorSum_eq hrest']
      simpa only [Slot.minimum, hp'] using hbudget
  have hpreCover : Covered u.properDivisors C ((∑ d ∈ u.properDivisors, d) - C) := by
    rw [heq']
    exact cover_mul_existing_prime_factors hn hk hg (hbaseT.symm ▸ hcT)
      (hbaseT.symm ▸ hcert) hfixedLow hcofactor
  rw [number_append] at hw hprim
  have hfull : Covered (u * number ys).properDivisors C
      ((∑ d ∈ (u * number ys).properDivisors, d) - C) := by
    rcases htail with hzero | ⟨hf, hb⟩
    · have he : ys = [] := List.length_eq_zero_iff.mp (hmatch.2.2.trans hzero)
      simpa [he, number] using hpreCover
    · have hmd := hM hmatch.1 hQ []
      simp only [List.append_nil] at hmd
      have hsigma : M ∣ ∑ d ∈ u.divisors, d := by rw [← divisorSum_eq hxs]; exact hmd.2
      have hct := (hbaseT.symm ▸ hcT).trans (sum_le_sum_of_subset hsub)
      rcases hb with hb | ⟨_, hb⟩
      · exact cover_fresh_tail hn hNle hc hg hf hb hys hmatch.2.1 hmatch.2.2.le
          (coprime_coordinate_concat hv) hw.1 hprim hsigma hmd.1 hct (hfixedLow.mono hsub) hpreCover
      · exact cover_fresh_tail_of_twoCaseBudget hn hNle hc hg hf hb hys hmatch.2.1
          hmatch.2.2.le (coprime_coordinate_concat hv) hw.1 hprim hsigma hmd.1
          hct (hfixedLow.mono hsub) hpreCover
  have hmul : n ∣ u * number ys := hnU.trans (dvd_mul_right _ _)
  have hfullSub := properDivisors_subset_of_dvd hw.1.pos hmul
  have hs : divisorSum (xs ++ ys) = ∑ d ∈ (u * number ys).divisors, d := by
    rw [divisorSum_eq hv, number_append]
  have hm := hM hmatch.1 hQ ys
  rw [number_append, hs] at hm
  apply hw.2
  apply pseudoperfect_of_central_and_modulus hw.1
    (hcn.trans (Nat.le_of_dvd hw.1.pos hmul)) hfull _ hm.1 hm.2
  intro x hx hdx
  obtain ⟨t, ht, hs⟩ := hfixedMod x hx hdx
  exact ⟨t, ht.trans hfullSub, hs⟩

theorem paletteBudgetsOkWith_closes {useAlternate : Bool} {b : Box} {G : ℕ} {data : CentralCoverData}
    (hdata : PrimeCoordinates b.minimum →
      Covered (number b.minimum).properDivisors data.low
        (divisorSum b.minimum - number b.minimum - data.low) ∧
      data.seed.Nodup ∧ data.seed.toFinset ⊆ (number b.minimum).properDivisors)
    (hok : paletteBudgetsOkWith useAlternate b G data = true) : b.Closed := by
  intro xs ys hm hv hw hp
  exact paletteBudgetsOkAt_excludes (Q := fun _ => True)
    (fun hfit _ ys => paletteModulus_dvd_append hfit ys) hdata hok xs ys hm trivial hv hw hp

theorem CentralCoverData.seed_sound {data : CentralCoverData} {n T : ℕ}
    (hok : data.ok n T = true) : data.seed.Nodup ∧ data.seed.toFinset ⊆ n.properDivisors := by
  simp only [CentralCoverData.ok, Bool.and_eq_true, decide_eq_true_eq] at hok
  obtain ⟨hnodup, hseed⟩ := divisorListOk_sound hok.1.1.1
  refine ⟨(List.nodup_append.mp hnodup).1, ?_⟩
  intro x hx
  exact hseed (List.mem_toFinset.mpr (List.mem_append_left _ (List.mem_toFinset.mp hx)))

end OddWeirdSubproblems

namespace OddWeirdSubproblems

open Finset

def knownTailLiftOk (C G : ℕ) (pre : Coordinates) : Coordinates → Bool
  | [] => true
  | (p, e) :: ys =>
    let m := number pre
    let T := divisorSum pre - m
    decide (p * G + 2 * C ≤ T + 1 ∧ m + 2 * C ≤ (p + 1) * T + 1) &&
      knownTailLiftOk C G (pre ++ [(p, e)]) ys

theorem knownTailLiftOk_sound {pre ys : Coordinates} {C G : ℕ}
    (hv : PrimeCoordinates (pre ++ ys)) (hC : 0 < C) (hG : 0 < G)
    (hCT : 2 * C ≤ ∑ d ∈ (number pre).properDivisors, d)
    (hlow : DenseLowSums (number pre).properDivisors C G)
    (hcovered : Covered (number pre).properDivisors C
      ((∑ d ∈ (number pre).properDivisors, d) - C))
    (hok : knownTailLiftOk C G pre ys = true) :
    Covered (number (pre ++ ys)).properDivisors C
      ((∑ d ∈ (number (pre ++ ys)).properDivisors, d) - C) := by
  induction ys generalizing pre with
  | nil => simpa only [List.append_nil] using hcovered
  | cons y ys ih =>
    obtain ⟨p, e⟩ := y
    let m := number pre
    let T := ∑ d ∈ m.properDivisors, d
    let new := pre ++ [(p, e)]
    have hpre := primeCoordinates_left hv
    have hm : 0 < m := number_pos hpre.1
    have hp : p.Prime := hv.1 (p, e) (List.mem_append_right _ (by simp))
    have hnot : ¬ p ∣ m := by
      apply hp.coprime_iff_not_dvd.mp
      exact coprime_coordinateProduct hp hpre.1 fun x hx =>
        ((List.pairwise_append.mp hv.2).2.2 x hx (p, e) (by simp)).ne.symm
    have hT : T = divisorSum pre - m := properSum_of_validCoordinates hpre
    simp only [knownTailLiftOk, Bool.and_eq_true, decide_eq_true_eq] at hok
    have hlift := cover_raise_coprime_prime_power_add (a := 0) hm hp hnot hC
      (Finset.sort_nodup _ _) (Finset.sort_toFinset _ _)
      (gapUpTo_of_central_and_low hG hCT hcovered hlow).prefixGapBound_sort
    simp only [pow_zero, mul_one, zero_add, pow_one] at hlift
    have hs : p * G + 2 * C ≤ T + 1 := by rw [hT]; exact hok.1.1
    have hl : m + 2 * C ≤ T + p * T + 1 := by
      rw [hT]
      simpa only [Nat.add_mul, Nat.one_mul, Nat.add_comm (p * _)] using hok.1.2
    have heq : number new = m * p ^ e := by
      rw [number_append, number_cons, show number [] = 1 from rfl, Nat.mul_one]
    have hv' : PrimeCoordinates (new ++ ys) := by
      simpa only [new, List.append_assoc, List.singleton_append] using hv
    have hm' : 0 < number new := number_pos (primeCoordinates_left hv').1
    have hsub := properDivisors_subset_of_dvd hm' (heq.symm ▸ dvd_mul_right m (p ^ e))
    have hnew := ih hv' (hCT.trans (sum_le_sum_of_subset hsub)) (hlow.mono hsub)
      (heq.symm ▸ hlift hcovered hs hl e) hok.2
    simpa only [new, List.append_assoc, List.singleton_append] using hnew

def prefixPaletteOkWith (useAlternate : Bool) (b : Box) (G k : ℕ) : Bool :=
  let pre := b.minimum.take k
  let data := buildCentralCover pre
  data.ok (number pre) (divisorSum pre - number pre) &&
  decide (2 * data.low ≤ divisorSum pre - number pre) &&
  knownTailLiftOk data.low G pre (b.minimum.drop k) &&
  paletteBudgetsOkWith useAlternate b G data

theorem prefixCoverFromData {b : Box} {G k : ℕ}
    (hv : PrimeCoordinates b.minimum) :
    let pre := b.minimum.take k
    let data := buildCentralCover pre
    data.ok (number pre) (divisorSum pre - number pre) = true →
    2 * data.low ≤ divisorSum pre - number pre →
    0 < data.low → 0 < G → lowDensityOk data.seed data.low G = true →
    knownTailLiftOk data.low G pre (b.minimum.drop k) = true →
    Covered (number b.minimum).properDivisors data.low
      (divisorSum b.minimum - number b.minimum - data.low) ∧
    data.seed.Nodup ∧ data.seed.toFinset ⊆ (number b.minimum).properDivisors := by
  intro pre data hdata hCT hC hG hlow htail
  let ys := b.minimum.drop k
  have heq : pre ++ ys = b.minimum := List.take_append_drop k _
  have hv' : PrimeCoordinates (pre ++ ys) := heq.symm ▸ hv
  have hpre := primeCoordinates_left hv'
  have hsum := properSum_of_validCoordinates hpre
  have hcovered := CentralCoverData.sound hsum hdata
  have ⟨hnd, hsub⟩ := CentralCoverData.seed_sound hdata
  have hdense := (lowDensityOk_sound hnd hlow).mono hsub
  have hc := knownTailLiftOk_sound hv' hC hG
    (hsum.symm ▸ hCT) hdense (hsum.symm ▸ hcovered) htail
  have hdvd : number pre ∣ number b.minimum := by
    rw [← heq, number_append]
    exact dvd_mul_right _ _
  rw [heq, properSum_of_validCoordinates hv] at hc
  exact ⟨hc, hnd, hsub.trans (properDivisors_subset_of_dvd (number_pos hv.1) hdvd)⟩

theorem prefixPaletteOkWith_closes {useAlternate : Bool} {b : Box} {G k : ℕ}
    (hok : prefixPaletteOkWith useAlternate b G k = true) : b.Closed := by
  simp only [prefixPaletteOkWith, Bool.and_eq_true, decide_eq_true_eq] at hok
  obtain ⟨⟨⟨hdata, hCT⟩, htail⟩, hbudget⟩ := hok
  apply paletteBudgetsOkWith_closes _ hbudget
  intro hv
  have hstats := hbudget
  simp only [paletteBudgetsOkWith, paletteBudgetsOkAt, Bool.and_eq_true, decide_eq_true_eq] at hstats
  exact prefixCoverFromData hv hdata hCT hstats.1.1.2.1 hstats.1.1.2.2.1 hstats.1.1.1.1 htail

end OddWeirdSubproblems

namespace OddWeirdSubproblems

def prefixSweepOk (b : Box) (first stop G k h shift : ℕ) : Bool :=
  let fs := b.minimum
  let pre := fs.take k
  let data := buildCentralCover pre
  let n := number fs
  let s := divisorSum fs
  let slope := 2 * n - s + h
  data.ok (number pre) (divisorSum pre - number pre) &&
    lowDensityOk data.seed data.low G &&
    knownTailLiftOk data.low G pre (fs.drop k) &&
    decide (2 * data.low ≤ divisorSum pre - number pre ∧ 0 < data.low ∧ 0 < G ∧
      s ≤ 2 * n ∧ (h = 0 ∨ (h ∣ n ∧ h < n)) ∧ (shift = 0 ∨ shift = n) ∧
      s ≤ s - n - data.low + shift + slope * first ∧
      data.low + shift + slope * (stop - 1) ≤ s)

theorem prefixSweepOk_closes {b : Box} {first stop G k h shift : ℕ}
    (hok : prefixSweepOk b first stop G k h shift = true) : HeadRangeClosed b.slots 0 first stop := by
  simp only [prefixSweepOk, Bool.and_eq_true, decide_eq_true_eq] at hok
  obtain ⟨⟨⟨hdata, hdense⟩, htail⟩, hwidth, hC, hG, hs, hh, hshift, hfirst, hstop⟩ := hok
  apply headRange_of_valid_core
  intro hv
  have hcover := (prefixCoverFromData hv hdata hwidth hC hG hdense htail).1
  exact headRange_squarefree rfl rfl hs hh hshift hcover hfirst hstop

end OddWeirdSubproblems

namespace OddWeirdSubproblems

open Finset

def pointBitsOk (n s : ℕ) (seed picks : List ℕ) (shift : ℕ) : Bool :=
  let used := 2 * n + picks.sum + shift
  divisorListOk n (seed ++ picks) &&
    (decide (shift = 0) ||
      (decide (shift ∣ n ∧ shift < n) && !(seed ++ picks).contains shift)) &&
    decide (used ≤ s) && (subsetBits seed).testBit (s - used)

theorem pointBitsOk_closes {b : Box} {seed picks : List ℕ} {shift : ℕ}
    (h : pointBitsOk (number b.minimum) (divisorSum b.minimum) seed picks shift = true) :
    b.Closed := by
  simp only [pointBitsOk, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq,
    Bool.not_eq_true'] at h
  obtain ⟨⟨⟨hdiv, hshift⟩, hbudget⟩, hbits⟩ := h
  obtain ⟨hnd, hsub⟩ := divisorListOk_sound hdiv
  obtain ⟨hseed, hpicks, hd⟩ := List.nodup_append.mp hnd
  obtain ⟨t, ht, hsum⟩ := testBit_subsetBits hseed hbits
  have htdiv : t ⊆ (number b.minimum).properDivisors := by
    intro d hdmem
    exact hsub (List.mem_toFinset.mpr (List.mem_append_left _ (List.mem_toFinset.mp (ht hdmem))))
  have hpdiv : picks.toFinset ⊆ (number b.minimum).properDivisors := by
    intro d hdmem
    exact hsub (List.mem_toFinset.mpr (List.mem_append_right _ (List.mem_toFinset.mp hdmem)))
  have hdisj : Disjoint t picks.toFinset := by
    refine Finset.disjoint_left.mpr (fun d hdt hdp => ?_)
    exact hd d (List.mem_toFinset.mp (ht hdt)) d (List.mem_toFinset.mp hdp) rfl
  let u := t ∪ picks.toFinset
  have hudiv : u ⊆ (number b.minimum).properDivisors := union_subset htdiv hpdiv
  have husum : ∑ d ∈ u, d = (∑ d ∈ t, d) + picks.sum := by
    dsimp [u]
    rw [sum_union hdisj, sum_toFinset_of_nodup hpicks]
  have close (v : Finset ℕ) (hv : v ⊆ (number b.minimum).properDivisors)
      (hs : divisorSum b.minimum = 2 * number b.minimum + ∑ d ∈ v, d) : b.Closed := by
    apply close_minimum_witness (ds := v.toList) (Finset.nodup_toList v)
    · intro d hm
      exact Nat.mem_properDivisors.mp (hv (Finset.mem_toList.mp hm))
    · simpa only [Finset.sum_toList] using hs
  rcases hshift with rfl | ⟨hproper, hnot⟩
  · apply close u hudiv
    omega
  · have hnot' : shift ∉ u := by
      intro hm
      have havoid : shift ∉ seed ++ picks := by simpa using hnot
      rcases Finset.mem_union.mp hm with htm | hpm
      · exact havoid (List.mem_append_left _ (List.mem_toFinset.mp (ht htm)))
      · exact havoid (List.mem_append_right _ (List.mem_toFinset.mp hpm))
    apply close (insert shift u) (insert_subset (Nat.mem_properDivisors.mpr hproper) hudiv)
    rw [sum_insert hnot']
    omega

end OddWeirdSubproblems

namespace OddWeirdSubproblems

def pivotPosition (xs : Coordinates) : ℕ :=
  ((xs.zipIdx).foldl (fun (largest, best) ((_, e), i) =>
    if largest < e then (e, i) else (largest, best)) (0, 0)).2

def reconstructLargePicks (fs : Coordinates) (p e : ℕ) :
    List ℕ → ℕ → ℕ → List ℕ × ℕ
  | [], _, target => ([], target)
  | rank :: ranks, cap, target =>
    let base := divisorOfRank rank fs
    let exponent := cappedExponent p (min cap target / base) e
    let d := base * p ^ exponent
    let (ds, remainder) := reconstructLargePicks fs p e ranks (d - 1) (target - d)
    (d :: ds, remainder)

def guidedBitPointOk (b : Box) (slot h : ℕ) (ranks : List ℕ) : Bool :=
  let fs := b.minimum
  let rest := fs.eraseIdx slot
  let k := pivotPosition rest
  let (p, e) := rest[k]?.getD (1, 0)
  let shift := (fs[slot]?.map Prod.fst).getD 0 * h
  let target := divisorSum fs - 2 * number fs - shift
  let (ds, _) := reconstructLargePicks (rest.eraseIdx k) p e ranks (number rest) target
  let seed := smallPrefix 1024 (sortDivisors 20 (divisorsAtMost rest 1024))
  pointBitsOk (number fs) (divisorSum fs) seed ds.reverse shift

def verifyGuidedBitPoint (b : Box) (data : List ℕ) : Option (List ℕ) := do
  let (tag, rest) ← readVarNat 64 data
  let i := tag / 8
  let j := tag % 8
  let fs := b.minimum
  let h := if j < 2 then j else ((fs.eraseIdx i)[j - 2]?.map Prod.fst).getD 0
  let (ranks, rest) ← readLengthPrefixed rest
  if guidedBitPointOk b i h ranks then some rest else none

def guidedBitPoint : PointReplay where
  verify := verifyGuidedBitPoint
  sound := by
    intro b data tail h
    unfold verifyGuidedBitPoint at h
    obtain ⟨⟨tag, rest⟩, _, h⟩ := Option.bind_eq_some_iff.mp h
    dsimp only at h
    obtain ⟨⟨ranks, rest'⟩, _, h⟩ := Option.bind_eq_some_iff.mp h
    dsimp only at h
    generalize hok : guidedBitPointOk b (tag / 8) _ ranks = ok at h
    cases ok
    · contradiction
    · exact pointBitsOk_closes (by simpa only [guidedBitPointOk] using hok)

end OddWeirdSubproblems

namespace OddWeirdSubproblems

private def rankedBoundedPoint : PointReplay :=
  PointReplay.ofDivisors fun b data => do
    let (count, tail) ← readVarNat 64 data
    if count = 0 then decodeRankDivisors b.minimum tail else readNatList count tail

private def verifyBoundedPoint (b : Box) (data : List ℕ) : Option (List ℕ) :=
  match data with
  | 0 :: 0 :: rest => guidedBitPoint.verify b rest
  | _ => rankedBoundedPoint.verify b data

def boundedPoint : PointReplay where
  verify := verifyBoundedPoint
  sound := by
    intro b data tail h
    unfold verifyBoundedPoint at h
    split at h
    · exact guidedBitPoint.sound h
    · exact rankedBoundedPoint.sound h

private def decodeBoundedSweepAction : SweepReader := fun b first _ data =>
  match data with
  | 5 :: tail => do
    let (ds, rest) ← decodeRankDivisors (b.minimum ++ [(first, 1)]) tail
    pure (.point ds, rest)
  | _ => decodeSweepAction data

private def literalBoundedSweep : SweepVerifier :=
  SweepVerifier.ofActions decodeBoundedSweepAction

private def sweepCoreShift (b : Box) (tag : ℕ) : ℕ :=
  if tag = 1 then number b.minimum else 0

private def verifyPrefixSweep (b : Box) (first : ℕ) (data : List ℕ) :
    Option (ℕ × List ℕ) := do
  let (params, rest) ← readNatList 5 data
  let [stop, G, k, h, j] := params | none
  if prefixSweepOk b first stop G k h (sweepCoreShift b j) then some (stop, rest) else none

private theorem verifyPrefixSweep_sound {b : Box} {first stop : ℕ} {data tail : List ℕ}
    (h : verifyPrefixSweep b first data = some (stop, tail)) : HeadRangeClosed b.slots 0 first stop := by
  unfold verifyPrefixSweep at h
  obtain ⟨⟨params, rest⟩, _, h⟩ := Option.bind_eq_some_iff.mp h
  dsimp only at h
  split at h
  · split at h
    · have he := congrArg Prod.fst (Option.some.inj h)
      dsimp only at he
      subst stop
      exact prefixSweepOk_closes ‹_›
    · contradiction
  · contradiction

def boundedSweep : SweepVerifier where
  run b first top data :=
    if data.head? = some 4 then verifyPrefixSweep b first (data.drop 1)
    else literalBoundedSweep.run b first top data
  sound := by
    intro b first top data stop tail h
    change (if data.head? = some 4 then verifyPrefixSweep b first (data.drop 1)
      else literalBoundedSweep.run b first top data) = some (stop, tail) at h
    split at h
    · exact verifyPrefixSweep_sound h
    · exact literalBoundedSweep.sound h

def boundedPalettePruningWith (useAlternate : Bool) : BranchPruning where
  verify b data := do
    let (G, rest) ← readVarNat 64 data
    if G = 0 then some (false, rest)
    else do
      let (k, rest) ← readVarNat 64 rest
      if prefixPaletteOkWith useAlternate b G k then some (true, rest) else none
  sound := by
    intro b data tail h
    obtain ⟨⟨G, rest⟩, _, h⟩ := Option.bind_eq_some_iff.mp h
    dsimp only at h
    split at h
    · simp at h
    · obtain ⟨⟨k, input⟩, _, h⟩ := Option.bind_eq_some_iff.mp h
      dsimp only at h
      split at h
      · exact prefixPaletteOkWith_closes ‹_›
      · contradiction

inductive ClosedBelowCuts (B : ℕ) : List Box → Prop
  | nil : ClosedBelowCuts B []
  | cons {b : Box} {bs : List Box} :
      b.ClosedBelow B → ClosedBelowCuts B bs → ClosedBelowCuts B (b :: bs)

theorem ClosedBelowCuts.closedOfMem {B : ℕ} {cuts : List Box} (hcuts : ClosedBelowCuts B cuts)
    {b : Box} (hb : b ∈ cuts) : b.ClosedBelow B := by
  induction hcuts with
  | nil => simp at hb
  | cons hd _ ih =>
    rcases List.mem_cons.mp hb with rfl | hb
    · exact hd
    · exact ih hb

end OddWeirdSubproblems

namespace OddWeirdSubproblems

def checkUnboundedRankedBlock (fuel : ℕ) (b : Box) (cuts : List Box) (count value : ℕ) : Bool :=
  match expandPackedTokens count (bytesFromNat count value) 0 0 with
  | none => false
  | some data =>
    match unboundedRankedStream boundedPoint boundedSweep (boundedPalettePruningWith true)
        (fun q => cuts.any (boxEqual q)) fuel b data with
    | some [] => true
    | _ => false

theorem checkUnboundedRankedBlock_closes {b : Box} {cuts : List Box}
    (hcuts : ClosedCuts cuts) (fuel count value : ℕ)
    (hlo : 1 < b.next) (hodd : Odd b.next)
    (h : checkUnboundedRankedBlock fuel b cuts count value = true) :
    b.Closed := by
  unfold checkUnboundedRankedBlock at h
  split at h
  · contradiction
  · split at h
    · apply unboundedRankedStream_closes _ hlo hodd ‹_›
      intro q hq
      obtain ⟨c, hc, he⟩ := List.any_eq_true.mp hq
      exact (boxEqual_iff_eq q c).mp he ▸ hcuts.closedOfMem hc
    · contradiction

end OddWeirdSubproblems

namespace OddWeirdSubproblems

private theorem nineSmallBlock1 : (⟨[⟨3, 2, false⟩], 5, 0⟩ : Box).Closed := by
  apply replay_closes (witness := (fun _ => [])) (fuel := 1)
  · exact (show 1 < 5 by decide)
  · exact ⟨2, rfl⟩
  · decide +kernel

theorem nineSmallComputed0 : (⟨[⟨3, 2, false⟩], 5, 0⟩ : Box).Closed :=
  nineSmallBlock1

private theorem nineSmallBlock2 : (⟨[⟨3, 2, false⟩], 5, 1⟩ : Box).Closed := by
  apply replay_closes (witness := (fun _ => [])) (fuel := 1)
  · exact (show 1 < 5 by decide)
  · exact ⟨2, rfl⟩
  · decide +kernel

theorem nineSmallComputed1 : (⟨[⟨3, 2, false⟩], 5, 1⟩ : Box).Closed :=
  nineSmallBlock2

private def nineSmallBlock3Rows : List (Nat × List Nat) := [
    (1575, [5, 9, 15, 45]),
    (945, [1, 5, 9, 15]),
    (2205, [5, 7, 9, 15]),
    (7425, [1, 5, 9, 15]),
    (131625, [3, 9, 15, 25, 27, 75, 125, 135, 225, 375]),
    (342225, [5, 9, 15, 25, 27, 39, 45, 65, 75, 81, 117, 135, 169, 195, 225, 351, 405]),
    (78975, [1, 25]),
    (570375, [1, 3, 5, 9, 25, 27, 75, 125, 225, 675]),
]

private theorem nineSmallBlock3 : (⟨[⟨3, 2, false⟩], 5, 2⟩ : Box).Closed := by
  apply replay_closes (witness := (fun n => (nineSmallBlock3Rows.lookup n).getD [])) (fuel := 12)
  · exact (show 1 < 5 by decide)
  · exact ⟨2, rfl⟩
  · decide +kernel

theorem nineSmallComputed2 : (⟨[⟨3, 2, false⟩], 5, 2⟩ : Box).Closed :=
  nineSmallBlock3

end OddWeirdSubproblems

namespace OddWeirdSubproblems

private def oneFourBlock0 : Box := ⟨[⟨3,1,true⟩],5,3⟩
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem oneFourBlock0Closed : oneFourBlock0.Closed := by
  apply checkPackedBlock (readPoint := PointReplay.ofDivisors decodePoint) (fuel := 18) (count := 24) (value := 0x809080c1009010100040102010603101810010006021600)
    (cut := fun _ => false)
  · simp
  · exact (show 1 < 5 by decide)
  · exact ⟨2,rfl⟩
  · decide +kernel

theorem oneFourRootClosed : (⟨[⟨3,1,true⟩],5,3⟩ : Box).Closed := oneFourBlock0Closed

end OddWeirdSubproblems

namespace OddWeirdSubproblems

private def oneFiveBlock0 : Box := ⟨[⟨3,1,true⟩,⟨5,2,false⟩,⟨7,1,false⟩],39,2⟩
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem oneFiveBlock0Closed : oneFiveBlock0.Closed := by
  apply checkPackedBlock (readPoint := PointReplay.ofDivisors decodePoint) (fuel := 34) (count := 283) (value := 0x222518012018202000002016010e000505010501c40105600100000420051d06000518011c1601181c01001602180d0818181b16010520130005018301151d1014100d0016010100160208200f00051f01040a0120021d000016012512012001001602050008051d00181801001602000016011809010016021d011601202018001601100225181601251d041808022001001202001008150000000500184d000557011004181820251816012023101d051601080000101d10100c0100160220002216012012000800001d22002018120000240031000532010d25160100251015101001091816011800101818011000000016010400160100182400190500001d2000180018000100160225011a100018001920180020003f00)
    (cut := fun _ => false)
  · simp
  · exact (show 1 < 39 by decide)
  · exact ⟨19,rfl⟩
  · decide +kernel

private def oneFiveBlock1 : Box := ⟨[⟨3,1,true⟩,⟨5,1,false⟩,⟨7,1,false⟩],9,2⟩
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem oneFiveBlock1Closed : oneFiveBlock1.Closed := by
  apply checkPackedBlock (readPoint := PointReplay.ofDivisors decodePoint) (fuel := 52) (count := 559) (value := 0x60c01001801000202010002060404251005060102010503020406010b0c1701200503010203090309081701010d100d2d00096a010406080f0804102502010d0000010203100005018501010203010b0c030125020a000945010b01020804080505031010000008010012020100060218001d231000001500160121000502a201090a0101000102020a0101020c080702001a08010006160005640102020808130804081000181d251d0e000502a001211601202016011601000808220303030403050c030306020a01020303031117011b1d0d2400063d01010100064b0104080101060802060f0b0201000e0201000212000802e5010702b7010f1714040010222200181d15250e0101000602010002160017028501010102000602a9011f07040409160116010d1d12010d091601010006140011028201061213080425100800010012021d0100120225180500042300202524001d00087d011d011d00040005790125210200051401210023000400052401001816010020060005560116010200054401151601210400062c011020230300050701052101001602002400231601001001001602051b140005280100001d1800010016021601160116011d1816012205010016021201000023081f000809011801001602050005090124180200060a01201800001601010016020100120d000601010b2a010a1f01061c17140408181d250a251a0801001602140100120101010201010202020401010202010104020413171404101810203000)
    (cut := fun b => boxEqual b oneFiveBlock0)
  · intro b h
    have e := (boxEqual_iff_eq _ _).mp h
    exact e.symm ▸ oneFiveBlock0Closed
  · exact (show 1 < 9 by decide)
  · exact ⟨4,rfl⟩
  · decide +kernel

private def oneFiveBlock2 : Box := ⟨[⟨3,1,true⟩],5,4⟩
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem oneFiveBlock2Closed : oneFiveBlock2.Closed := by
  apply checkPackedBlock (readPoint := PointReplay.ofDivisors decodePoint) (fuel := 30) (count := 188) (value := 0x1810000020010016020a000529010e03011107010d010201010d0c0f1702241d1808232401001602101d1000030100160201000100020105090307010d0301080b170208010001010306070b0607170218101d010002030105030309010b090a1702200100010201030a0e061702001c0001000102040402020807130d0602010101010105020a01031418081001000e02140010120900101300082000142518140820000818100100101d2000180d00180008180018200001aa00)
    (cut := fun b => boxEqual b oneFiveBlock1)
  · intro b h
    have e := (boxEqual_iff_eq _ _).mp h
    exact e.symm ▸ oneFiveBlock1Closed
  · exact (show 1 < 5 by decide)
  · exact ⟨2,rfl⟩
  · decide +kernel

theorem oneFiveRootClosed : (⟨[⟨3,1,true⟩],5,4⟩ : Box).Closed := oneFiveBlock2Closed

end OddWeirdSubproblems

namespace OddWeirdSubproblems

private def nineFourBlock0 : Box := ⟨[⟨3,2,false⟩,⟨5,1,false⟩],13,2⟩
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem nineFourBlock0Closed : nineFourBlock0.Closed := by
  apply checkPackedBlock (readPoint := PointReplay.ofDivisors decodePoint) (fuel := 38) (count := 377) (value := 0x20101010205000618010406060d0704031910010e0106010100060101010202010101010401010602060f0b08041009101c01012a00060201010203010203030306110b010100020f000801bd010b0404081008000008030001191c010004060603030208081c1014180018140806011a180818101018081012011c1010181a10101019191201181918080c18081801010012021a14181a1a010012021c50000601c8011a0100063601081a1a101b0c100c1818141901001202120110081018180b120108181c00055a010c10101c1a110e011201080b000506010653011808141c010012021401000a020808041812011814081410100a140e011018010001020202040606070f02080818001008101c1818101019081201181018103f000545011410181813141010141001001202181014141b140810101201181c0c181c141a020810120100081800080018000801000a021a1812101c08101018081403101b0100120210181408081201101810101018101818105500)
    (cut := fun _ => false)
  · simp
  · exact (show 1 < 13 by decide)
  · exact ⟨6,rfl⟩
  · decide +kernel

private def nineFourBlock1 : Box := ⟨[⟨3,2,false⟩],5,3⟩
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem nineFourBlock1Closed : nineFourBlock1.Closed := by
  apply checkPackedBlock (readPoint := PointReplay.ofDivisors decodePoint) (fuel := 29) (count := 132) (value := 0x100020604041c0801141c1a010012021a1410140203060301080102090913010412010c02100e010202040606030f0803180c1c18080812080100120209081c0e0108080801000a020814001401000602100100010102010a030a080000100400081b100810180808101b080818081003101800181010181808180818081c1008018100)
    (cut := fun b => boxEqual b nineFourBlock0)
  · intro b h
    have e := (boxEqual_iff_eq _ _).mp h
    exact e.symm ▸ nineFourBlock0Closed
  · exact (show 1 < 5 by decide)
  · exact ⟨2,rfl⟩
  · decide +kernel

theorem nineFourRootClosed : (⟨[⟨3,2,false⟩],5,3⟩ : Box).Closed := nineFourBlock1Closed

end OddWeirdSubproblems

namespace OddWeirdSubproblems

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem nineFiveRankedRootBlock0 : (⟨[⟨3,2,false⟩,⟨7,1,false⟩,⟨17,1,false⟩,⟨19,1,false⟩],21,1⟩ : Box).Closed :=
  checkUnboundedRankedBlock_closes (.nil)
    34 417 0x10909030805000701ef0107030b040805000940010914140b111706100800051201050f020005090116172320040005150104122b2b29050600060b0120200826041806000501010c029e01071111030400074d010621223e4a473b4b4f09200000000d101d201a352c1500053f01124e204847384a071809000501e7010501ac011c02202a372f33070809000a200151275f4b5f05200700060f013e095c3f6f5b73071009000d0101107401230207010103020a060502000d0b0f0f00080b010d0f160318000000030900057b01040f0a100b0506000725010c0f0b101905000000000e15162b17232f07101300056c011d32273a0605000901b90101226136270524070006019d010001000e54011f02020401020103010304010a051d0203000f111a201600052e01010b101104050006260102030003030013161d2220230610000000050510050400000000080a263a0420000022000c4d011902020306010301020408051702030019470f3f0a010600000d04050b04080000000c0a0b0308000000060702102e000913010303000c0418161705080a000b0101000100
    (by decide) ⟨10, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem nineFiveRankedRootBlock1 : (⟨[⟨3,4,false⟩,⟨7,2,false⟩,⟨13,1,false⟩,⟨23,1,false⟩],31,1⟩ : Box).Closed :=
  checkUnboundedRankedBlock_closes (.nil)
    28 644 0xa1416170400052a011415161617051000000013242a2229052011000621010f2a0a202c0520000000181c190d000504c201001c0207112c20061509000a04eb010c271f1f0518000000040f051720292c2c08001300096f01683c7952266f1f7208100a000d01bd011b300a173b2f06250000000e0b15171f051d000000051c2222172c061d1d00097c0121082229230606000701bc011225162e373b060700065e0107029b010508172c2c38061d0800091a011215262704180000000f1c211d2c23061811000a01b4010d1235082f233b07100900060e011139584e5d3f06240800060f011c1c065a46373b070007028d01077f013432125e72764f776309210b0012028701610201010101070b12011107020301010e0502000203005918000556015804020009141316041d0a00067001050305031d0000000a090d0b04080e000502c6011d03200300071d010c1413261f052500000015191a172f051b1100050189010d0195014d010005019d014c040200010911031800000003070210100006190109100f0401000000050b141604080e000611010501e3010d081117052006000501ca01000000090404111108000501b0010419110322000000011116070c000970010b0f1603040008210110071b2e2f2f2f072000000003030003030024130b142c2c0619000872010e6b01410200000203400402001008081a200f00063e010310050f150500000000130e1a2904200000000d1d11110410190007210108392e3b04230000001e220b2c2f0521000000402e0f261305201a000815011319171a0505000523010a1f0102033f0401001618080320000000000710140b0408150009010100370200050d01360402000303002b02000003032a0402001100
    (by decide) ⟨15, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem nineFiveRankedRootBlock2 : (⟨[⟨3,2,false⟩,⟨7,1,false⟩,⟨13,1,false⟩],25,2⟩ : Box).Closed :=
  checkUnboundedRankedBlock_closes (.nil)
    27 538 0x100a05110400054a010f16110320000000040f1103090000000f0e0e1014000501eb01090114000005000704a6010b170200054801100511031a0500074f010a111717041b0000001802051a04180f0009019101080f1111041d0000000517111a1105230000000d040f110404000000160d0f031d21000632011213022504000c039801020b141610110607000529010722173804000501ef010a1a140f17050600085e012022160b042006000b018301100d16031d0500065f011e111d14200500050286011c1b323b1337062008000529010a5601110f241d04000501ac0102020a222c2306180000000e2e20230f000701bb010502b20124241429112c0600050c01191c073235462f071009000501f901060f010b100823292323071009001301aa0125022407041a230504030805020003030004100208000000040c0b14110501000000141d11020c060629000b6e010409021d0000001b0b0e111a0c000541011820230318000000120e160f0c00056801051a17031c050006010106150100000a0f0210000000151314170408000000030300140507071c05200000001c111e35132400050a01250710302f051807001475010d1005161105100000000a12090d00061201100e1b0f041d000000121b151704180f00083f01020302000627010a0d0d1011201a07080000000205171f252706181400050d010c040e2a2c2906150800060e01121f1f22232306080800180101000100
    (by decide) ⟨12, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem nineFiveRankedRootBlock3 : (⟨[⟨3,7,false⟩,⟨7,4,false⟩,⟨13,2,true⟩,⟨19,2,false⟩],1691,1⟩ : Box).Closed :=
  checkUnboundedRankedBlock_closes (.nil)
    38 902 0x2dac7020500061a01c6040200190e10222f605007250d00050101080b01bb010009039101da9d0200060d01061101f301000603900102d902000705a301d99804020008030a20261c0b1d08140000000016020b0729263a0721000000000805040b0511060d2800051a011020041c1305180000000f0f39162e3841380e091d00000018000b01ad01d7f10200070f01f00100056601d7d30200073d01d201000601cb01d6f90200062d01d6f804020003301b2a604e46445f091b0000000303000000001900060f01b30401000002d78b0800061a01d78a02000a2901d4010005029e01d19b0200060f01d19a0200054701d0f30200063801d0f202000a03bc01cedf040100140a273d23050b000501b40130363611373420071500000b0009028c01c8e90200070f01e80100050f01c8cd0200060f01c8cc0200050f01c7fb0200060f01c7fa02000502d701c6870200061001c68602000601ab01c0bb0200061b01c0ba0402040009028501b0e3040100029597080006029d01959602000902c60194fb02000901f90193c1040104000802960189e10200054f01062701d4fd040100130708413b4706230d000702b101c5e7020300060b01e601000902b101c5870401000001c08309000601fc01c082040200050007029601a2ed02000679015fbb020300050901ba01000760015f93040100005eff020900051701fe0402000c0c1e1f052c061800000e00080382015ec1040100005d0700060295015d8c020008018c015901000501c3014ef90200050f014ef80200065b013ae90200053c013ae804020400070d01ef01000c0d01d704010002030600060b018bbf040104000729018a9104010002889d0800070f019c040200000288850800061a018884040200050007190186db040100028199020900060b019801000836010281830300063601fdeb0200061b01fdea0402000e0d06213b05110c0006540101d3fb020400060b01fa040200000500051001d38d020005019c0101cd0200071101cdaa04020002030001acab0b0005280101acaa0456a70600054201569504040017253b0b596067680820001000066501580100061b01588c0402000057dd0800050e0157dc0200053d01518d0200052201518c0428cd050005450128c6040400010608041105020c000527012ccf0200060d01ce040200002cad02000002032cac04021000060c012acb0401040005010100020321a90410d9020100020310d40403001200
    (by decide) ⟨845, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem nineFiveRankedRootBlock4 : (⟨[⟨3,6,true⟩,⟨7,3,false⟩,⟨13,2,false⟩,⟨19,2,false⟩],1115,1⟩ : Box).Closed :=
  checkUnboundedRankedBlock_closes (.nil)
    28 659 0x14243320571f1f2b4b0a000501b801040601b471286635072200000003030f00092001a10401001b361807211516341a2b340b0500000014000b018901bd8904010002030002bce70b00063301bce604020400076d01baf302000501a001066001b8bf040100021c412b235f06200d00064b01aeb30200070f010501f10102ae9d0300061001ae9c02000602e401ac810200064c01ac800402004e461908320e06210000004b1b511655484344500918000000001f00080b01ff0100090b019de30401000006000510019c9d02000571010291ef0300054b010291ee03000a02aa0101da9304010003070006029d0172d50401000c2d6012522c566508190000001c483e4804221800080101050d01ed040100005cd307000526015cd204020021213f2e3a1706190d000a560159ff02000601980141cb020005160141ca0420e9020100020320e50404001ab31100060d01b2040200001a970700054b011a960402000c2b2c25380e4a14081a000000273b1b5704250019000c1801e1040100271b252e052c06100c000b2a0119c7040100030300178f020b000533018e040200342c02113e0b5307250d000d01900111cd02000601e50110b5020006018e01b40402030005250117a3040100200a1d2d1d0a000801b50116e5020300050c01e40402000203060005530116a7040100053e103b04200b00053b0113eb0200060e01ea010005490113bd0200053b0113bc04020016121a131b050b000515011b192c232c3e0621000000010a271704151100090101050d019f0401000010810700050e01108004020000000ebf02000002030ebe0402000a161a261318000522011d0f162b2f052207000518010a080d1c191d0615000000000304072325051013000901010002030aa70401000000000b00
    (by decide) ⟨557, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem nineFiveRankedRootBlock5 : (⟨[⟨3,5,false⟩,⟨7,3,false⟩,⟨13,2,false⟩,⟨19,1,true⟩],225,1⟩ : Box).Closed :=
  checkUnboundedRankedBlock_closes (.nil)
    24 445 0x130322252705000839011611172d37390624080009380115070f271d05220700104901b5040100010f0e1f2505210b000701890117290f2505180600064601030300201f3022300800070c010c092a1d0e050600070198010f4001ab04010009112e292709000602af01221b1113051d0600070e010f19111d2705220700062801000b13271d2f052308000e390103990401000c0d0d0d0d0a0005019401030300040e06221c050900062b01390c1c2c45460607000647010f01b601f304010005151311041d0a000d6801e504010014160b0318000000080d010f0410000000040d141c2c05181c00070d01050f0521042206000a3301eb010006019701ea0402000a0e13111305150000000c0d1c0e11051015000611010d0f1713051406000d3701dd040100030a0d16041d0000000f090f0d110508140005140108170b030400053a0101080509040d06000a0101053201b704010004202a2e2e051800000010070f111305101500050c0104081c2635051d000000000b00062401ed0100060d01ec0402000002c30700061701c2040200081e111b0418000b00050f01bd0100060f01bc040200000000029d0200000203029c0402000203001600
    (by decide) ⟨112, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem nineFiveRankedRootBlock6 : (⟨[⟨3,5,false⟩,⟨7,2,false⟩,⟨13,2,false⟩,⟨19,1,false⟩],103,1⟩ : Box).Closed :=
  checkUnboundedRankedBlock_closes (.cons nineFiveRankedRootBlock5 (.cons nineFiveRankedRootBlock4 (.cons nineFiveRankedRootBlock3 (.nil))))
    34 664 0x1c3140351d6308070b0005028501070b01f689040100000600050f01f4fb040100004de6cb0900051a014de6ca03000803fa014cafa3040100003dcfeb0a00052e013dcfea04270403020601121609040503070801060202021700075b011ee7f50300055a0111c79903000603a601c7980408e3cd0600055c0108e3cc0300065c0101daa103000604b001daa0040204000502d80170930200052e017092045a5a0c0b5c015d010456095c0654040402010101140501000203388904042100054a0148ee020006650148eece0424b7b5070005180124b7a7040400030308000603c901ebcf0475eb0500054b0175e70403002a08391426530625000000003f1e2f272314062019000b4e01399f04010000389d0800051001389c0200070199012dcf02000556012dce0416ef05000502e90116e704040019203829400a0005018a0124241316020d3d0b1109110b00070101070a01c5040100000500051b01b70401000d2807031f0b06140c00072f011a8d02000533011a8c04020011061f0f1d0a00060b01080312130b05000660010a17121604210000080009019d0119e7020300050b01e604020300081601bd0401002408303b4505200b000a77011993020009520118c902000501c801053b01169b0401000a010b070f050b00054901211a1a2304220600073f0111dd0200060d01dc0402000011c9020800050a01c8040203000725019104010300071a010ff9040100271b282e1c0b201d08100f00050101070a01c104010300061a01119d040100000000000d9b0b00052e010d9a0402040006380108db040204020a06010504020407060c040102100504ad02030002030004a91f0005230104a804029502010002030294040400001000050f01e10401000203000191020000020301900402001300
    (by decide) ⟨51, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem nineFiveRankedRootBlock7 : (⟨[⟨3,3,false⟩,⟨7,1,false⟩,⟨13,1,false⟩,⟨19,1,false⟩],25,1⟩ : Box).Closed :=
  checkUnboundedRankedBlock_closes (.cons nineFiveRankedRootBlock6 (.nil))
    29 677 0x2232373e4b05210000002a112b272d05100007190125073b3f4e0523000000333d43363a323a071813000904fe01422f3b04200000001e04283439142f07100009018e012a142c2b3b380710000000076938626d77062013001101ee01890100056a01028804020011351a373f3e06200000002e341d3b04231600070289010816343247052007000e01b801f1040100200b071f170900051e0114140a1704150007000501ff0110151d0300056501011e101829050600091a0101ef020300051701ee0402000419151704100a000d6801db0401000d161d1d04220000000305070904010000000f13171704251c000703960106211f25051906000601d6011c1b17030007140106230e0433190600000419081c040e00060c01130a14233a051807000d01010601b801018b0200050c0106019201670401000303004302000003034204020009050511111600054c010a0e1503180000000825173604180e000564010636010a07090f0f05060005019a01150e1d20200520000000000c0d13150f000701960117101703000501ab010f05161f170508070008190110060b14170502000000060a222223051011000b01010a4d01410401000203003902000002033804020003031300055601032b04010006030903080a0006260109011d00000004100b0900056a010b0f0f030005019801070a0b03010006000a018f010a010a050b050000000007070703150f00077a010a010d0e040500050f01080a0b04100500093301020e0b0e042006000536010d030a0000000f10161104080c000642010a0c030300051b01060107040105000c3601090b050b0400050901050b1403000644010c16081a1a050800000003091303200f00070901030302000c29011f0201010201020106051d0203000510021100060b0104071117040806000b0101000100
    (by decide) ⟨12, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem nineFiveRankedRootBlock8 : (⟨[⟨3,2,false⟩,⟨7,1,false⟩,⟨13,1,false⟩,⟨17,1,false⟩],19,1⟩ : Box).Closed :=
  checkUnboundedRankedBlock_closes (.nil)
    24 564 0x5049d01a10200110203079f040100020303d00f000570010f182b290422060005039e0102200e0404000801c601469d0200050d01469c0402000044d90800050e0144d8040200000035bf0900051a0135be041ae90500053a011adf02000723010de70200050191010de6040101040e0306020e04010a050100030306f304040004031a0006590102850401830201000303018204030e0008039c016b0401001d0a363a3e0900052101161d171f04000565012022231c04000a180124372b3a0f05200000001439173b042010000509010a7a01b30401001c2d3a0321090007520101a9020300056201a804020001160911170518000000190d0d1d04150000000621101a04181d000626010e0d0905040500061d010b0e150404000511011309031800000006161903140c00070c01082f2f032305000d0101053e01019d0401000e1a1720040a000701b10106190171040100040300530200000203520e000801b0010002033904010003090b030b00071401011602000501ae01121b0522160506000701a401370379270e02060700050101065d010d0b140300055201061601060a1e2b0400061601151a161d04200600050d01030d1e071f2006080000000b000b68014101000530014001000668013502010303070406060502000711080320000000040300070502101b000835012f01000538012e040200030306000517012504010008060303040900050a010a0702080000000303000305021d0e000a0101001d02000003031c0402000403000e00
    (by decide) ⟨9, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem nineFiveRankedRootBlock9 : (⟨[⟨3,3,false⟩,⟨7,1,false⟩,⟨11,1,false⟩],39,2⟩ : Box).Closed :=
  checkUnboundedRankedBlock_closes (.nil)
    31 505 0x4070a0b04080600060d01251c0b172f05250700051d010702bb0104190b3a230500055501061b1c222e051d000009000602e10102282e3b2f0606000601b401086f0124071720202c2307100900064e0112070731253b3907000502d401090b0d1d1726272708080000004b5114674712000502d2011230080e2f580607000802c701052812071f3b0600051e010e0d09152b2e06180000000b000878013101085a5b4b0607000601db011302ad013d020201010b030702070307010101020e053b02012f08015708035f01010a05040005070b0f260008018b01060e11161105080000000a0d072019110608000014000802bb0116240b2b0400064b010d02ad013502212001232f190a02080502000303002f0201030602050a0205080502001308050b04242500051d010a01f401120d15110400051801020703030205000a1001120602000e019a01140d131d042006000a018a011e0d20292c292c07100000001e202317232306100000000322052d13272f07180000000116560b4e272900057601132b513b46052007000718012a1f14172f052500000020064a5f5b05230012001667013102040120442c23040108052f020e00081201131b0f1704180600053001082d01060814233b2f3b072500000001141c354a55062000000015313935350521000000020300000003032800150101000100
    (by decide) ⟨19, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem nineFiveRankedRootBlock10 : (⟨[⟨3,4,false⟩,⟨7,2,false⟩,⟨11,2,false⟩,⟨31,1,false⟩],47,1⟩ : Box).Closed :=
  checkUnboundedRankedBlock_closes (.nil)
    29 740 0x70a151515171707000502de0130131b3b3805000605970110282c03000502b5010a070e1419231a070800000b00067e0101091a22403b3a4608080a000a03e3010f231d2505050005700113273449470500057501020418130b1d1d07080000001842483b4d613b0724000000093d351d3a2c4a071b21000741012a453f403805210000000c324c5b5a5e062312000701fb01011e10260b2c172f08080a000871010503a401062a174d5449474a0909000546010602920145455749052500000010303a3b7705200000001024054438353b4a081c000702bc01240c052122353b233b090a0007039f0102042819442c0607000902c801181202020517174147440a100c00057901060185010b018201a5020a1e01051101051107010a0501a30201010307050d080a171206010c05040019163738250005019f01080f1c1a11050807000501d901271a0a2b23070d07000801fe010d161511050106000501f30128262531310500051b010413262b384747070800080f013c08162e3847061808000501f5010a01a701019d020300050c019c040200030306000601b0018d040100091d021c00000022221e1d0f00077801081b1e1d0400056d0114191a22170500072b01141d1e2604000501ef01050f0f17171706140000003010182f352c1100055501190d0a0921050600073801330e46442c051d0700092b010a2c2d1b041a00000021121b032000000001192c11202c061d0000001a08211c20000d01af010415480d0e29061808000d0101060d010187040104000901a3017b01000501a301050198016f040100010713171705080b00060c0112070b17042206000617011322211d230520000000060f1d2b29050d1100071f01030100083b0169020000020368040200020f07031a0f000616010306060f042000000002020e0b08051d00001200062a010c070713041806000a0101005f0202051d091b240102020501010c0559020300030300000000020357040100030300470200000303460402002e00
    (by decide) ⟨23, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem nineFiveRankedRootBlock11 : (⟨[⟨3,3,false⟩,⟨7,1,false⟩,⟨11,1,false⟩],33,2⟩ : Box).Closed :=
  checkUnboundedRankedBlock_closes (.cons nineFiveRankedRootBlock9 (.nil))
    31 384 0xa140d150405000773011b2c202c04230000000e091d250d00050901241414170418060008550121091c43441d0618000000331408352f10000501bd0109019d013020233a04200000000627062a141a2b070812000502c20107172c2f060806000917010c643261735f630720000000030d000f019f014d02032e02072530020532022c0327060401100549020206030109020a0f081f0005019c01056801470401000704101104180a000622011a1a1f0b170522000000130e0f0320000000010a0e101105080000001c00070197010407110308050007300118092b261d051d000000012c165c1f5e5f6377090800000037191e4468266d0718210006080102030000000500100188013d0204010201010b040406030a053b020115030404030605040003030035020000030334040200030a0b0b042c000a0e010c0e0d03100500060d01030300090d022500000003030c00092b011e26202e0425000000010d091c21010610000604010303000000060c18232005020c000f0101000100
    (by decide) ⟨16, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem nineFiveRankedRootBlock12 : (⟨[⟨3,7,false⟩,⟨7,3,false⟩,⟨11,3,false⟩,⟨29,2,false⟩],243,1⟩ : Box).Closed :=
  checkUnboundedRankedBlock_closes (.nil)
    24 650 0x1e4e324658530600063401043c462b3b05000904cc015152595d5d5b3b070800076801181c081925050005038b0100503d1e716f6f07000701b1012a0508301331310718090009720120054171726f63072100000015182a221d35352c14000501d801060f3a254239410708000504ba01111f31152d2f07180000003c12092347052012000b04bc011202083d462c2f473b09150000000e241e2527270615000501e8011e063e402e13434545450b08000d000b5b010c0c1f1f551a4147081d0000000f362c3b3b232307151600050f01506d2601897b018906200a000e01af01333628545538534a5909180000000c3144745e7601860720180007038301020302000c018601b1020100232c4e3e3b4f0622000000061b0808293235231700061401063a0110190a2b2f4323070005029b01062901301b3222162c3b07100900093601241e1b12162b352f2f3b0a100c0006029b0102010005190106153f696361701a5965590b150d000601cb0103030003001302b301ab04010006170823192f0618000000253f364704220000000c15131f382f3b071a21000b028501a302020005028001a2040200040e0d0d1717061a00000014292c1d1300054201191d0a372b05000522011b1c191708050d0008000717010d05160b051500000015382613230e000860010a161c2c0400062e0112222d23042500000018101e1517050f0008018201191c353a4a47233b082000000001162a351d05201400076c0119061f142c23172f0810000000513d2a5e2f1200050a010f2324545d052007000817012d12113337390e0e0815000000030e000a35010309062a0b1c3a3b2c091800000012020a13072d2f070d0000000b0c1705353b060822000a12010f010100020302870401000800
    (by decide) ⟨121, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem nineFiveRankedRootBlock13 : (⟨[⟨3,3,false⟩,⟨7,2,false⟩,⟨11,1,false⟩,⟨29,1,false⟩],31,1⟩ : Box).Closed :=
  checkUnboundedRankedBlock_closes (.cons nineFiveRankedRootBlock12 (.nil))
    31 676 0x22b39294405220000000c1f0f172305100000000f1511162e2c0b2f08081e00073d013c250d48593b0600050b0140385a613b4b06070005048001130a41380e3807070007170150384c395f5706230000000f1e4f47041d110009100111240f271f051507000c0187018b0100051a01028a04020400087701f3040103000501f801d1010006018601d0040200091211121313060b000702fe0112512f581d051807000902a5010b082d2d2f05000501fd0112154339443a0607000601da010701d5010a2b24300400065f0112511b4f4556416a080900081f010d01e801d904010001081c08260518000c000b5301cb0100065301ca04020004090317171f0a00057201231c23032005000601a201190d171d0400051701070d0e1a040d060007180109090d23230500067e01221e1f270405000502c3010701f501bf0100061001be04020300063401a90100060f01a8010006018001019302030005580192040200081117150f1706180000001603121b130518160008019201160f0f041805000501a701041a2c0e05200000000a20120d160f060d0000001309052a2905180000001e000c018f01060c019701000a019201018902000619017702000002037604020003030c00066d016b0100056d01050f0153040100050a0d0708000801cc0103070703020500060b010c1317030400080190010109191704000509010404030b04000501a0011b1e1f211a0510070006120101020711110506000a0189010c5f01450100050b010554013b0401000303000700052c01330401000713170318000000150a2203201100062b010c050b03080000000c1510161717060810000a1001272222170420060007260108240102033104010006060503010b00060c011e1d2011041000000003030b000701010025020105020402020501080502000f00
    (by decide) ⟨15, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem nineFiveRankedRootBlock14 : (⟨[⟨3,3,false⟩,⟨7,2,false⟩,⟨11,1,false⟩,⟨23,1,false⟩],27,1⟩ : Box).Closed :=
  checkUnboundedRankedBlock_closes (.nil)
    29 651 0x1000901ce010b890405c5020100020305c404030003031100051b0102a1040195020100030301900403000c1b262e170515000b04bd0107019201d5040100150d07231f05220000000018240726170515000509012215250320000000000900085301cb0100060f01ca04020300053b01bb0100064401ba0402002828172f08000502c0010f183f2a37350610000900065f012113292f05150600055401494329410505000703be01030300030007019801b7010006019801b601000701980105018b01a7040100040907070d050a000727010b1e1e170405000703ab0106110b1f0f052107000513010604150207131107080900056f010c2801ff0100062801fe0402001d1a0f0f04210a00052b010d1d1629051506000c4d01f1020200052501f00402000220142b2b051200000d00056a01830100053e0103820200053e01062301f70401000d1a1b1e08000801d90116161e0310000007000b01f40102cb04010400050f01ff0100060f01fe0100077301af01000502a60101ae02000564010501ca01790401000305000776015b040100062e0b2304250000000d362d1f042413000727010a151714230520000000121f0717142320070813000801d401162a2f042300000003090007740101950200060f0194040200030300018709000526010186040200131e1d1f04240b00060b01050c0b0300050601030100061f016d02000003036c040200041f0b23042010000620010a0b0503000500054501070d0305000000001b1921162317060f00073a0102030200050101060c01650401030005140100000203550401000d030f03150d000712011d000000000a0b0b0b041000000003030000051317032400000002100803081f000e010100350200000203340402000b00
    (by decide) ⟨13, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem nineFiveRankedRootBlock15 : (⟨[⟨3,2,false⟩,⟨7,1,false⟩,⟨11,1,false⟩],25,2⟩ : Box).Closed :=
  checkUnboundedRankedBlock_closes (.cons nineFiveRankedRootBlock11 (.cons nineFiveRankedRootBlock10 (.cons nineFiveRankedRootBlock13 (.nil))))
    31 292 0xa0b02180000000b0b0703080c00092601030b022004000961010a0a0e171123060808000519010f770105030f031505000637010a130a15041400000019080b03180000000a0515150416000c01e0011614140320000000060208111705180f000d2a011212211c1105000501900124070b200405000601a901412206381b0b0607000601ac011201b3013d02020406020502030408053b020208010803070102080504000303003502052901170711071404010a050200030300002f02000003032e040200160f11031d000000060e1317044800071a011e1a2a222e05200700063f0103160a2923051807000c3e012d02000002032c0402000d100210000000080a0b031016000b1c01070b0503100000000303000d04140b04081100110101000100
    (by decide) ⟨12, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem nineFiveRankedRootBlock16 : (⟨[⟨3,2,false⟩,⟨7,1,false⟩,⟨11,1,false⟩,⟨19,1,false⟩],21,1⟩ : Box).Closed :=
  checkUnboundedRankedBlock_closes (.nil)
    24 601 0x6230103b9020f010202020101010805000b030303b7130005190101dc040404000742010f8902000b03030f8709000501f80107c404030002030700056a0102cb0401a7020100020301a50403001a0519151300080c011a111f1d0415060005070108019101c5040103000e019f01020f021004000503c10116160303000c01c5017d0100057c017c040200020300070005028c01035f041c02151604030605010002032f0403000f0a13110420000000091216141b07060d00000012051d22042c000901fd01120c15161d050807000702cb01110e0f1f04220600070101062701c3040100051a07042e24060b0008470101b90200061b01b80100064a01050f01a30100064a01018f0200053001018e04020008040b03090006130108110200050285010d07100514051807000d01820173010005190172040200030306000601b10167040100030300510800057b0150040200070906000645010b130f2404000501870109090200056a01070702010000000905080a00092e010b0a02230000000002090a00081a01040a07030d0000000904050b00050801080b0b03080006000e01d6013b020441011104053502030b00054501330100051401320402000e05020808000615013102000003033004020002050e01040f0007010105140123040100040c010f040000020902100f00071c010b01090300051201050100082f010a09020300081f011810190300054b011416360f1305180000001322251a041810000f1301140f021d0000000308000c27011d0206030301020201020805170203000d05110320000000030906031c000d0101000100
    (by decide) ⟨10, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem nineFiveRankedRootBlock17 : (⟨[⟨3,2,false⟩,⟨7,1,false⟩,⟨11,1,false⟩],13,2⟩ : Box).Closed :=
  checkUnboundedRankedBlock_closes (.cons nineFiveRankedRootBlock16 (.cons nineFiveRankedRootBlock15 (.cons nineFiveRankedRootBlock14 (.nil))))
    26 700 0x801f80101b7020802020204010101080501b5020a040206140005470107030301b30500057f015b040600040300210800057a01200411020305000703a90105b702000b020305b5090005200102db020008450101d5020c020503020106050011020301d304010002036a0404001a000825010eaf0407050103010101010104020302020201100501000303079704031d000801b901028704010400050391019902020005630198044f0207020301050900050c014902020401050603010208050600080902100000000c0d0703240000000c010a0521000823010b09021504000504a0010f0408051005000a0f01080e03040805000e6a01018b0401000303007d0900050d017c0100060d01590100052101580100052101064301470401000e14130308000701fd01570100057d0156040203000802b00143040100030a02080800053b010f070f042000000008000e02c2012d0417020200030b0b110401000000050b11031814000715010d0a0a03000602ab010a1d23032005000b3f01350214030c040f0b030301010a052f0210000519012d02000003032c040200040e100b041010000901c7010f0c0705040500060c010c01c9012104010003070208000000040b020e000c530115020309010104050200070d05030800000008010815000801870102030b0a0b05100700075d0104100b03000a019a010d1416160400064f010e141117051806000d0182013702020201030104030302010a053502020204030101020403020a05040003032000050c012f040100050106000768010109070504080600050f01050c010b0f0503100500050e01090101053f01230401000107030301090005430107020200050b010f0e2220040806000e46011b020100020811030000000013101a031d001200051c0100033a011b030106080008190106063812042a06000003030002120d031d1100130101000100
    (by decide) ⟨6, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem nineFiveRankedRootBlock18 : (⟨[⟨3,3,false⟩,⟨5,2,false⟩,⟨37,1,false⟩],43,2⟩ : Box).Closed :=
  checkUnboundedRankedBlock_closes (.nil)
    25 449 0x311022404000703e501060b0b03000509010d110f130410000000041b1103140000001b1a201c22051d18000526010e03020008019d01064f010b0e17262c1a06240000001a131111041c000000100a1216171900062e010e1c1c1d170606000847011e151c2204140000000905240d102b0f000502b201000614111c1c0510080008340106040e0d101106080000001e091a24221000050a01090a0434340506000a01b00106091a1611051407000b42010f0329293232061808000a34010e12181723222307080007019a011206040519081107010900061201270d4e294f0506001119011c300531323435071809001501f801390202201c20020201021f1e03010c0535020300010a161c04180000000f1e20201a2200080198010d151a1d041006000c01b8013102050701040d0306052f0203000000050b021414000956010203030a0b050600053b011905111d05140600071a01030f0f11170514000000040404180e112b071200062201051e01030728171a23061008000815010116210e22230600113d0107131c0b1d050600072701011c0523230518000000272510221a2c061d12000714010a210419221a061000000002020d00120101000100
    (by decide) ⟨21, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem nineFiveRankedRootBlock19 : (⟨[⟨3,3,false⟩,⟨5,2,false⟩,⟨31,1,false⟩],49,2⟩ : Box).Closed :=
  checkUnboundedRankedBlock_closes (.nil)
    30 359 0x9091203140000001303161c04140f000801a9010805050a04010600052601313c033b0979060000020f191b040e000601f101060184010f28082f1a05100700083201181019110418000000120d222c040e000802a0011c162834352906100000000180652d5b018705141400104e01480f124f2243523b3b091c00000030272b4e593b5c471600051b014005520f3b4e5a5f5f09220000001850510f690f3f4f0818180005060106019f011101d3013f0206100804010306053d0223251b48070e1b01080504000202003b0201001e2523202c1a2c072028000d019a010c0b02dc041812060000071113032400000007190b0b1105141900073b011508111704240600061c01080e1a1c1d05250700081c010e2b312c230500082f010a1f112c2c05200700050101071d01000015121319202b232c081000000007162e2b1a0520001700050401000202000c152b08290518000000000f1b1f212306081600160101000100
    (by decide) ⟨24, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem nineFiveRankedRootBlock20 : (⟨[⟨3,3,false⟩,⟨5,2,false⟩,⟨31,1,false⟩,⟨43,1,false⟩],45,1⟩ : Box).Closed :=
  checkUnboundedRankedBlock_closes (.nil)
    28 497 0x41411201a1a062400000019151c031c0000000c0b1122202306141b00093601071b1b111d05100000000f051723220f000501e701240b0511171a0607000901dc01191a3f0f7b4776071c09000c01cb0107018c011611171704000517012d1f0e222b05200008000501de01063117222306060006019b010d0198016901000502a60168040200080d111d0800052c011613110f04000516010809030d04000949010d180822041d0600074b0103051615041000000003040a050b050f0006340118131d11041d06000a3801080522152205150000000602131c04141000071e010a07100811110608080009028001091f0b1105180600160180015f0401000612130f13051400000009151d03220000000607050804001c000933010409050b1111060d0000001a20171b041811000639010616292c293406200000000104161a2320060913000a1b011e181c0e112c06180000002e0d0711042411000511010b010106410157040200050192014f0100057e014e040200060e070b040900071f010d190b1d170524000000060a13031d00000002141c051c05181900060601000000020200101c0b17041c0000000a1111130f051c000000010c282004101f00081901150212041b180407080000010a15051705110010010100410200000202400402000202002f0201000202001500
    (by decide) ⟨22, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem nineFiveRankedRootBlock21 : (⟨[⟨3,3,false⟩,⟨5,2,false⟩,⟨31,1,false⟩],43,2⟩ : Box).Closed :=
  checkUnboundedRankedBlock_closes (.cons nineFiveRankedRootBlock20 (.cons nineFiveRankedRootBlock19 (.nil)))
    37 355 0x115051d11051800000018130b1a04211000061e011b051c171d0506000501dd01160b0b1117061d0700060101060e010a0410110f11060b080007370130023f344e4138230810000000010b050832314314000535010802683957230610080008019f012535172b27060600060288010d4f010b162508112c350708000701e10115341d5c57675e07210000003114594e2f46062414000801d30108057c327d74130720000000012c09261d11092727091017001001010b01a9015102010103040401020b02090a054f020300090f1717160005018101090d0e110408060007230104301111230520000000270502291a2323071413000548010b5a014b0201030305010206010202010108010e0549020306030504040201060402010c0547020500020200450200000202440402000a031303153800060a01030b02100400060c010f14202904200600050d01060101050d01020239040100020200000000000d00
    (by decide) ⟨21, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem nineFiveRankedRootBlock22 : (⟨[⟨3,6,false⟩,⟨5,4,false⟩,⟨31,1,false⟩,⟨37,1,false⟩],129,1⟩ : Box).Closed :=
  checkUnboundedRankedBlock_closes (.nil)
    24 568 0x21628213b3d0607000801c30111296a4e5d5b06230800094d011245392a775f5f5f7f09240000000d240e080514382f080818000802b00107018b01043f10402c14442f3b3b530b1000000027060a4d5350475f53091000001d000801c8010b02c401d901000602c401d804020004090b151b171d070c00077e010f18041c1d221a070800057d0114463a473f062007001001ce01cd0401001b0f1134342c0620000000332629172f14000902b2010610141c1d1d060700054701060323171d051807000e019001c1040100121e1b171705180000000e030e0b0b1314000901d701050a090b0b05080000000403050f0b05101100054c011e28271d0405000601d101061901011f0528051d0000000222131d1d170610000551010570010501e7013f1d553b4d07180000000f576632595f061812000515011602a001b3040100020b160f130900053f0100120c293437051c0800054701054401010e253337052407000801010a500106019001aa0402000d0720231105100000000a131603250000001c0c132a201106141e00050f0105210111231104100500070e01031f172929050600067701094001ab02040101ad0b310b34063c01013703030e0501a7020d0e0401020f0504080103030c05040003111a1717052c00050a010f1c202304200600084a0101a3020300055101a20402000e111203240000000c140b03151100051e010e0e02200000000d1a0f03200c00052901000000050713030700060b010a02251d041d060013010100020201910401000800
    (by decide) ⟨64, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem nineFiveRankedRootBlock23 : (⟨[⟨3,3,false⟩,⟨5,2,false⟩,⟨31,1,false⟩],33,2⟩ : Box).Closed :=
  checkUnboundedRankedBlock_closes (.cons nineFiveRankedRootBlock21 (.cons nineFiveRankedRootBlock22 (.nil)))
    29 717 0x4140f0b1d2306070005019d010c0d222f2f17062208000803a101075c01a50100065c01a40402001e221b11041c00000000041e0521041d1400080101053b01930401000c0a131b1b1b0610000000140b0212000601a4011a03111b041200000000101c11110420000012000a4601810100050e01018002000601c1016f01000501b4016e0402000720292b08000601c2010309021804000516010f08231a04000501f80100070212151106040800092101010c17100f0a0e0b08000012061505111106051300050c010c510169040100130b1703130000000c1c100e041000000006010f03101a000828010a1017141d0506000501f3010c02100e100606000901f8010a0b16160414000008000d0191015f04010300050e01550100050190015401000502c101054d01370100067801130e1726230500052f010f19222b232306210000000d10111a17050c0000000c0a163d2b3e06231d00083d01251d172320050600050b010e11232c3506200700080e01041a352304210600086c01240b29030400073901020202000d018c017f01000602b201770100054e01760402000e191c1b04150a00060d010c1a10151105140700062601181a1c1911050005660103161b1704000539010606110e0b171707090900093d010630016b01000563016a040200011d1f1a1a23060b00070c011b0520230420060006240106070c0e0b0506000701010601a6016b0401000c0d191c1b05100b00065201101a1b031400000000121e1c1c1b051510000b4a01610100050d0160040200020200570200000202560402000311170322000000070f1c031d00061b010e1911171d1d061800000a00053e01240b0e222b051007000801010556014d02050601020704010108010a054902010202030102040202030104040502011005470205250007290102024504010002020031020308030604052f0202032e0101110203011207010c050400020200000000002a00
    (by decide) ⟨16, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem nineFiveRankedRootBlock24 : (⟨[⟨3,3,false⟩,⟨5,2,false⟩,⟨29,1,false⟩],49,2⟩ : Box).Closed :=
  checkUnboundedRankedBlock_closes (.nil)
    26 526 0x50b010b11031d0400060d011621201a1a0506000702940113023132113206250000000616261a2c051012000f01aa014f020103040803060201020a0a050200031b151d041500076001050b031c04010600000004051717172306140000003009150a39173b232f091d20000e01ee0149020224044c0256060547020201250226022829042305010c05040002021e00050e014304010003110b031800000b00050f0116111d04200500095a01031c1d03180000001e282a291a230613000012000e01cf01390201000000060d0f031a0000000e0b1c1b11051815000802850103101711050500072d01080f2217171d060700063301061c011909111c04250600060e010c181f222b35061c08000b710124070b3232232c0700065d0105340104281a2b0400050188010115060b102c2c071509001301f50141020a262b66120906050200020200281a09203b203b071800000020341e2b233706250000000418111a0b3b2b07102f00051a010e01ae0103080a0b0b0508070006250107160f0f1305100000001a151717170f000576011a17171d040500077901081e011413191b041b000000131b1f0b221d061c00120006040102020200062d011e091b211d052200000004130b0b1b171707100000000f2a18222211061c000000020819170418000029000616011b201b1d05150000000716141a1d05141000050c01150418232c05200700160101000100
    (by decide) ⟨24, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem nineFiveRankedRootBlock25 : (⟨[⟨3,3,false⟩,⟨5,2,false⟩,⟨29,1,false⟩,⟨43,1,false⟩],45,1⟩ : Box).Closed :=
  checkUnboundedRankedBlock_closes (.nil)
    29 588 0xc0a0f0f1111060d000000120f101104151100083b010f031323170606000804a501320a374d512f06250000001b372934341a2312000903c5010f0315121144473b081800000c000801e7010a67019b02010154595a5a67510d5404030c05019702060b050e021b04030d050a050400242e072c2b23230721000000062107142b111a232c091038000701fe01142f19111a34072008000801c301093517576d3f4f072309000e01eb0101950203000564019404020007160b0b17051c000000070d221100062c012714292c041b06000823010a1a0b0b11050005590103191f1704200600062701051d1d04200000070007250110172703000801ca01020202000d01e4010189020005019101053401770401000f182a19221a062400000018162008350518000000061e1d2b1f271f000601960111134504250500050101080194011e0d1117231d0610000000033416232e3b3b0713000501a801283216372f3b07200800080f011308443b44051b07000e62017b01000519017a04020300095e016b01000652015f02000002025e0402000703171704181000060c010414101104220600061a010601161d11170618000000041d160b232f3b071514000630010f730153040100020206000667014b0401000b070224000000050b02200f0007150105060603080000000507070b04100e00072f010b131811080520000000010b0f0b0418000000150517031d18000815010c120515181106080800050f0105010108120102023b040100040b02180a00070101003302010501010302030108052f0203000202001400
    (by decide) ⟨22, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem nineFiveRankedRootBlock26 : (⟨[⟨3,3,false⟩,⟨5,2,false⟩,⟨29,1,false⟩,⟨41,1,false⟩],43,1⟩ : Box).Closed :=
  checkUnboundedRankedBlock_closes (.nil)
    29 467 0x15242f33223206250800050601076001c7040100070218201a05240b000703e801140f22110400055d01221a1b071f1f06000502a101040a02252a23230710000000141d212137052113000813010d0f1c212d16222f2c09080b000601010e5d01bd04010028342b232c05220000001b1c26383a05200000000d17222904121e00061b01251e2f2a3423062000000018421b0e2f4e3f4f08211500086d013c214346505247081809000d02ae01061b01b3010006640101a30200064901a201000b49018904010003191f111123060b00051c01031b1b07262e2e232f09080000003d30133722080b2f081c18000d7701019b020300050c019a01000a7801018d0200050c010601bc017904010300086001690401001a19051d1d1d060b000701af01051b111d040500051601151d1d1117051800000010132920172306181200071101300e0a2b39172f3b08100000000d000d01860167010005190166040200020206000529015b04010300053f015301000507015204020300051401030b022004000517010a0f0b031c0500061c010c0a0821200508070008140104040d1010050d0700050c010c26013f0401000e050b0b04180a00051701000f10161111051008000c0101000202350401000202000a00
    (by decide) ⟨21, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem nineFiveRankedRootBlock27 : (⟨[⟨3,6,false⟩,⟨5,4,false⟩,⟨29,2,false⟩,⟨37,2,false⟩],279,1⟩ : Box).Closed :=
  checkUnboundedRankedBlock_closes (.nil)
    29 552 0x2041072d6d3f4f07230900062201240326573823475959590a180000001f120a2e2a3853777109141a000802da0168083601f25701d427028302860915000011001002e10109060d26392e4f4753470a100000000f00060301051601030430200a557d4701850186680b180f00056b010d019b01d50206051317040e11080402040a08010e0503d3020478020406720204780b737e040d01ef020b7e710b0102160503cf02130202020e10011802020d0b100e040310050600251916392e535207240000003c2c1d4b3f5306205900080282011b0d2e2e2f0618000000011a230f27272d0715130007590109054251460500055901272d02522c5959071509000c01880103cd0200060f01cc0100070f01c30100060f01c204020002020003af020a00056901ae04020000050c0336223b06200d00072b012427262b2005200700051b0112361d1d43473e070800066701071635170b3b0807000501c801063201411119192d4a0600053a0124192a1d0b382f232f09000e6501070d0193040100020200070005120103830401001339393b232c06200d000619013c054e522f3b0600051d0101132b2e1d370610000000020c00052c01006152293e664f06200000002a094b0a2950533b4709100000001a000c4c01fd0100064c01fc0402000d282217230520000000070319171d051c15000518012531163a3a05240000001812261129353807151300060c011838431f042406000a01010002db020000020202da0402000d00
    (by decide) ⟨139, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem nineFiveRankedRootBlock28 : (⟨[⟨3,3,false⟩,⟨5,2,false⟩,⟨29,1,false⟩,⟨37,1,false⟩],39,1⟩ : Box).Closed :=
  checkUnboundedRankedBlock_closes (.cons nineFiveRankedRootBlock27 (.nil))
    34 703 0x4090f0b151306150000000c0420222b10000677010e0e191d2e05200000001b1e22112626061012000a04fc01020e091b170500051a012a200b292d33061d08000804e2010c30331f3705220000000c08010b2105180000000f1c02101423291b000a1101303f1f144356520718090008150112104e290b2f061808000b028f010c019e01d501000503850106019201c904010006141511041c0a000601bd0109070d11041200000000161915031d0000001e161e1f04200000000a04021428222100056b010501f70101060e1d1d06180000000d0c0e1704240000000a191402081d0610001c000601b501092a071d290b071c0000000b000d03d201b10100063401b00402000d24311f04230000000d00096801ab04010010250505290b061c0c000b039e019701000626019601000501bc010601bd01d3040100171a08232c05240b00072501029b0203000524019a040200010a050f17170608000000090307332e052116000508010801a401028704010008051117090005290101241d031805000534010d131d1d17052200000000080a09051d051c120005230113050b0418000000000c1c1f0322000000120815140b051518000b1a011e09312246061a07000c0101074a01df0100061c01de0100054a01072501b104010300055e01910100062e0190040200030c09111105050b00060101051801990401001009131504090007019201018b02000501b501018a02000501b401050c017704010002020600063301670401000303090b0b05100b00062301010514171105200000000d0f110d00056d0104021214170508000000000b00060c011204081a042006000526010a2e01510216181e160212061402030a054f0203000f0f0b031b170005160100100b050b11051c00000a000a1e0102024b0401000a0d0e11042000000016081703181400090101003f02000002023e040200020200290201001200
    (by decide) ⟨19, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem nineFiveRankedRootBlock29 : (⟨[⟨3,3,false⟩,⟨5,2,false⟩,⟨29,1,false⟩],33,2⟩ : Box).Closed :=
  checkUnboundedRankedBlock_closes (.cons nineFiveRankedRootBlock28 (.cons nineFiveRankedRootBlock26 (.cons nineFiveRankedRootBlock25 (.cons nineFiveRankedRootBlock24 (.nil)))))
    30 314 0xe0a120b0b1306140000000f1605082c23062413000712010501c7011a1c1c03000801c7010979016d010005790105100161040100030f0b171d05250b00061701190b170325000000000f212108292306201100073501070f0b221d23061d0000000c21070819112c07100000000e0f0b1504091d000816010c130b1008111a070b09000512011201810159040100020200510200000202500402000f0f021400070c010d0f1d03000c0f0113160517040500076301020200080b0b111705100a00095301071410100817200700057901142b11261a052400000004281d352117061012001501010517014104010002050505040800000005050b031800130007190102030b0704100000003905613e2d040d02080000020216000519010e041011110518000000020200010714161905081400160101000100
    (by decide) ⟨16, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem nineFiveRankedRootBlock30 : (⟨[⟨3,3,false⟩,⟨5,2,false⟩],31,3⟩ : Box).Closed :=
  checkUnboundedRankedBlock_closes (.cons nineFiveRankedRootBlock23 (.cons nineFiveRankedRootBlock18 (.nil)))
    26 436 0xa11110f04250600062d01100a0b120400051101180f0b03000501e901151a20030006028301242a182a292906150009000a038f010e13171104240000000905190f040e000801c301252620313205060006140107370124161f22291a06200800061701181b1c2004200000000f0514261729061511000801d00101141f2c2906100000000a000912012d2a102920232c0708000623010f37013d010005019b013c04020007111103140900074301080f050b10060100000013162b2b2c2c061112000801010901d501330401000303030308000000100a050324000000010a0f031019000901b70103030e1104080600063701140b1417041006001001b5010509070704000531010309050511050800000015052126201a06181200091c010666010913031000000003191b1b041c0d00051f01085101181729320420000000121326172b1a2c071d1200073601121f2b1732232c352c350a100c00062301151c423e1b3e1f4f08140a000a350109051d041505000f4b010122223432232c071809000737011035010710261a1a2c2c07220900061701020200131c331a232c353508120d00070901020202000f0101000100
    (by decide) ⟨15, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem nineFiveRankedRootBlock31 : (⟨[⟨3,3,false⟩,⟨5,2,false⟩,⟨23,1,false⟩],81,2⟩ : Box).Closed :=
  checkUnboundedRankedBlock_closes (.nil)
    36 520 0x20b070b1305000501ec01141420172105000501ec01252a163522352307200000001b1626070811231a140009029901095a016f040100100b1c211d051c00000006180b1d230514000801b7010a151303100000002116222b232c06180000000205191b1105081a000a028601040511221a1a2307080900090101084c01650401000202005b0204030305040d040a01020a055902031800063101080b0f131305060005038301021811111a060c000000190234232f44062012000502df010109040404000b01fe010b111b0325000000000503030b0f05150000001e161b221d0518000000010e1911042023000970010d1b2121042000000018081d161711061011000a25013c300717202c443b47470a180000001b1e1d2a083e3d2c081800083101072e01031207161305100700073501041c1c1a221a1a1a090800000006262a210811061015000d630109120607071a1a1a23230a080c00061e01020200130f362a1a3e2c460b00051c01181d182c383b061c0800072e01180209266965676b0800050d01022060275a5e635e080900054b011e304b101a57560808000948011677015f02010300052701012122192029232c08110a00061b010f1c190b231706100000000a1528112305110005370106040102020200082b010c13132b352c353e080900050c01273a3a3e3547071000000004390e202c2c2c3e081015001c0101000100
    (by decide) ⟨40, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem nineFiveRankedRootBlock32 : (⟨[⟨3,3,false⟩,⟨5,2,false⟩,⟨23,1,false⟩],73,2⟩ : Box).Closed :=
  checkUnboundedRankedBlock_closes (.cons nineFiveRankedRootBlock31 (.nil))
    31 527 0x1816112123051800000001070517041c10000803fd01190e37353806240000000118270520222929081014000943010305091011050c000000011616130415000000100605170f18000501bf0125363a233b35061d0800070281010649010e3a113a382f061808000a62010a1909231d29290700053701150d4c2b2c41473b47470a18000000082022061b261f261f270a081b000902a1010702e4010a18334234323b08140000000d0d4b2f4b52474f082416000c0101095b018f02033f350b783107403c010a05018b0202060204020e06060303070301010e0504000f201121270005018d01090d0200083a010624221d0421060006160114070f1b1d05000501c20101130b110410060008260101890200053e0101880402000910111d1d051000000000123c3e292c061817000a0101050b0179040103000801ce016901000601ce015901000501810158040200090e0d0f1305130b00063c0103171b17042006000801c7015102010208120201040402030a054f02031100072e011a211121041c0000000f11100b11051410000a120127154e3e3a5006000e4901281c2c2f320506000627010a6a017901000535017804020016121703140000000f0e14290420120007460119021a3e412f06200800051a010934016d02000002026c04020002020c00051d015f040100020200120f191b1105180000000a1d222629052500000002021d000b0101000100
    (by decide) ⟨36, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem nineFiveRankedRootBlock33 : (⟨[⟨3,3,false⟩,⟨5,2,false⟩,⟨23,1,false⟩,⟨67,1,false⟩],69,1⟩ : Box).Closed :=
  checkUnboundedRankedBlock_closes (.nil)
    29 673 0x910311731233207000619011d1f21041d0500081b010e3429452f4607200000000a142b382f320612000601c601064d0125072e5047465207240900063d01240e323e0425000000041b132530233d464609100000000415342d525e3b6a081521000c1b0130304c39203b2f47080900064b010d039801b5020603030a08081008020101010c0501b302020201044006414809023f090190440401100504000f25192620290620000000090f161b04183900072a011b2022222305250700061c01193110143b051c07000501010503860124221a04200500056d0108019701ad01000602a801ac0402000716231b1d051d000000081a141d1b171400054301030b26170f0500050a010f181928200506000801e3010720200f230518000000150d101a2b052011000543011e13111a3505000501a60105030f151b1b06100800094e01093136352f3706180800063d0130142b3c19223e07150000000f273f2e394f47071415000b0191013c320b234d5053080800053e010c192017141f1e1d09040a00051501110101056601a3040100141f11172305140000000411150725051c15000701ad0113031c2305210600092901241011332905200000002434213c4b22674608181400054a0106320521570706001001e401052e018f0100050e01018e0200060d0179010005790178010005790105490163040100120b13130410000b00050185010807040300053501030915031c0000000c0e080d090f1007000000000f02163818000a7f0113122421111a2223081000000c00052b0100001918111a0a0b3a3b081b00000e000f58015b0100050e015a040200020200004f02000002024e04020005030b03101700062c01060b07031000000001041805141a081708080000001e15161404201b00050b011b020814041806000e0101000100
    (by decide) ⟨34, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem nineFiveRankedRootBlock34 : (⟨[⟨3,4,false⟩,⟨5,3,false⟩,⟨23,1,false⟩,⟨61,1,false⟩],63,1⟩ : Box).Closed :=
  checkUnboundedRankedBlock_closes (.nil)
    34 680 0x33133534464406200000001a081b262817061013000801b1011511211d05140000000a1a0528230e000601aa011c1f2d0852525e08080006220107480136264f393a3b06000501bb01193d11562c525e3b4709000801cb010602da01424c5c41494a657768770b1b0c000538010601b0010f0398018b020406660462026a0c046771016c01c80a0501011205028702031b000804ab0102830401002212152c262d0624000000020f1d0314000b1d010e091d3304000601dd01274b484c235238070800053001050f0109018901f3010006018901f204020030271e142c2e3a07200000000e1b151d1b15000734010501f4010d0c182b1720232c09100a00062001020202000d01ec01f30401000d0d1a191505180b00060c0106060e0d0405000702a901100111070f05150700060d011c27391c170506000665010c6e01e50100062401e40402001011262b272f0a000541010e143c2f3e05250700074a01f10100064a01f00402001a09251d2d0518000000132123032413000516010c29152b041d0000000d042102382906180012000701d9011a324e4104000d370101e3020300053501e204020001161a17111106150000000027312a29382f06170006330109211d171f051c000009000f6801d50401000e200b1d2123061800000020051a130f0521160006430107141b1b1d1d06100800051501272917463b06200700050a0107050f05000500081a0124113e404705200000000b270b0e223506141200050e010f4101bb0401000e19161711170610000000111d260325000000130e20031d1c000616010d10112b2905250000000d15373504181000090101060c01b301000a0c0101910401000202070005310173040100091a1b1b1d05100b0006010100790200050d01780100060d01690200000202680402000202000000000202570401001600
    (by decide) ⟨31, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem nineFiveRankedRootBlock35 : (⟨[⟨3,3,false⟩,⟨5,2,false⟩,⟨23,1,false⟩,⟨59,1,false⟩],61,1⟩ : Box).Closed :=
  checkUnboundedRankedBlock_closes (.nil)
    32 621 0x23450595c052307000502e0013d462f4a50500600051c011e0929504f05200700083f0133573152595b595f08180000002012162773777a07200000000f111a2c534a7607232200081a014c546046504a67656568680c190d00082e010b01f401c10401000d080d0b1d171d070c0007049e010609140b2327061808000509010a01ca01b901000b0c01af010005028c01065001970401001b27292c2905250b0006029101111a150f2726251f081d0000001c1720282212000540010d0c2a110823061008000c01c2019b0100064a019a0100054a010762018504010019110b2c4605250000001e1e08261a130007420119282f380420000000243121342b1a061011000b7801970100060f019601000601ae01028302030005160182040200022626202c05200b000a4e01028304010400057a01f30100064e01f20402000e313a414405240000000d1e162f0805221500050c011c3a05350b05000747012407083e1641061d08000c0101050f01dd04010300053b01d10100062c01d00402000319091611111707140d0006670119111d1438052007000b6a01c70100060f01c60100060f01019f0200065b019e01000a01b3017b04010002070a0a0b0509000000191c1b1704141400060c01100a1d1505100600051b0107041309171715070109000651010f0b081a1a050d000000000b00095a0101810200050e0101800200060d016f0100050e016e0100074b015d0100053d015c040200010a09070b05020000000c050b17042414000715010a090b030005090100100d100310000008000515010721014f02000002024e04020002020c000512014504010003080b03080900060101000202000400
    (by decide) ⟨30, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem nineFiveRankedRootBlock36 : (⟨[⟨3,7,false⟩,⟨5,4,false⟩,⟨23,2,false⟩,⟨53,1,false⟩],513,1⟩ : Box).Closed :=
  checkUnboundedRankedBlock_closes (.nil)
    31 788 0x246436653f5d6f776b09220000002733465c47595207221700074f01185471725c6d5d7f6e090a00071001094e20496665766508000a05b8010701bb01b301000601bb01b20402004445522f5f5b0621000000484f524d445006251700071c01410e636c6f3f062300000004334f443a66475808200000170007028b012010182022251d1f1f0a0a00060581010e018801a90401000c0d065c4b5b5f0b00060188012d3f5157615947650809000802b101141674335e7e7e07200000000c13374c264d355047091017000801e80148313d3243173b6b536b0b0b000d02cb0107a9020300052701a804020022240d331f272f2f0815000000202e353b2739061c19000e5b019f040100251c49337e7b4f6b0820000000162c1b403f3b434d081a0009019b014e28326456626559090900081d01745c6c693f5b6f07250000000c0d0f3a38314c55081816001001ce01078302000502ac010601c201db0401000724231d2f0510000000112038230b5306200000000912272726172c3a322200052001301022424f47061d08000a7a01180c300f1533333e2f09000501ad011a112a232b2306180800070e01012938274b0506000a72011a3d4a4e46435b07240000001e2420313433061014000b01df0108364a5e530506000743010c3c102f35414a440800050d010a2502312a224a1a08100a00120101075e01e9040100313d3e4753576a070c0006018a01073101e10100063101e00402000c48044b61642c655f091000000004083c3e1b08563b08141c000d01d10106c9020300050d01c8040203000901d70106a502000601ca0105e90200064101e80402000e16141104140000001527422a40372c383b4a0a1819000719010854561237614f4b08200a000626010202000300072201d30100062201d2040200060415131316202e3809080f00054101062e0105c1020300054d01c004020003090d0d11050d000000110d05270f17140005180109250b112c05190700061d01031915171f0f06150800051901000302212a1d101d07120a00080101080b01ab0401000400060d01059b0200060d01000000020204f10401000202000d00
    (by decide) ⟨256, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem nineFiveRankedRootBlock37 : (⟨[⟨3,3,false⟩,⟨5,2,false⟩,⟨23,1,false⟩,⟨53,1,false⟩],55,1⟩ : Box).Closed :=
  checkUnboundedRankedBlock_closes (.cons nineFiveRankedRootBlock36 (.nil))
    27 582 0x55d018104010028092436333337071900000016524d4d5f6b062100000004406046583b06202300065301181015231d2306100000003e596701855f018373072116000a02fe010501000601860105920200053601065101fd0401000628112a3a1f4307240000002d370e291a26200714190009790104f30200061001f201000701a30104df0200060c01de04020004a5020700050b01a404020300076c01048d0200076c0103bd0200061901bc0402000c1107252f051b0b00072c01930100062c019204020014101122042400000000062434370e433544081018000c01d30103870200052701038604020009213a3a2f05220c00070101051001e301000701b90102bd0200051b0102bc040204000901a901e1010006019d0101a102030005018e01a0040200062122231a230a00053e011a0b15171f2706180000000c030e0516081917080215000901a90105031c1d051500000009361d2e3805231000051c0110330734292f060700072e0102111e1e0a0a2307010900092401080a112e3107113c12010a000005301a5d6047370720160010018701060c01b301000b0c01a904010300087d01018b02000501ab0106019f016f0401000607020d0800052a0105110322000000060711101705200e00052201055b010208000000060d170e04250b000622010710051111050807000910011204081917050d07000740010b3e015d02000002025c04020002020c000522014f040100080a0f1104200000000001030b0310000000000a0e0b1104141d00050d010a0101000202410401000202000a00
    (by decide) ⟨27, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem nineFiveRankedRootBlock38 : (⟨[⟨3,3,false⟩,⟨5,2,false⟩,⟨23,1,false⟩,⟨47,1,false⟩],49,1⟩ : Box).Closed :=
  checkUnboundedRankedBlock_closes (.nil)
    36 736 0x504fa010603c101cf040180ab050005028b010180a7040300061a5c1c201a2d4d0820000000340e2c1c06150907101c00077a01dcbb020300060b01ba0100097a01dcad0200057a01dbed0200061101dbec02000605e80101dacf0300064f01dace040200542d6c5d220a3b5c08100f000d04f301d9ab04010400084d01d89102000b03c701ccc5040100052e022f04220b000703ed01ad0100074301ada604020400071b01acfd0401000001abb70900061a01abb602000a2901a48704010001a1fd0800070f01fc0402000001a1a708000602fa01a1a6040204000803f10187830401040009018f0147d10423ef050005780123e80403000606012e114f4f2c38380a10000902e5011cc7020300050a01c6040200075b011c9904010009382f33560523000000332f443b473b06221700060101050e01cd01000517011ba302000551011ba204020400060c01fb040103000801c00115b3040add05000517010ad902000517010601a90109d50404eb020100020204ea04030e0008019f0103df0200060193010281020006680180040200181b131d25270a000538010b261d1d230521070005150116071b031d00000000120d040e16060210000826010c0511150400000000030a21251525061d00000015121f23440e4429081800000021000d2101df020200051c01de0402001c2d4c5a5e624f07230d00090101060c01c101000a0c0102990200050c0106019301cf010007019c01019702030005018301960402000504010558014002018d55064a0600000c07020516081107081300091601191c08141420071800000a000b43010189020101020201010103010102030101030403010202140502000f14171a04212100064301052a013705056043080000000b0f0503241100070101060a0101830401000500050b017504010002020600050f01610401000203090704080a000616010e0b0f031d0000000015170e1717052300000002021500090101004d02000002024c0402000202000e00
    (by decide) ⟨24, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem nineFiveRankedRootBlock39 : (⟨[⟨3,3,false⟩,⟨5,2,false⟩,⟨23,1,false⟩,⟨43,1,false⟩],45,1⟩ : Box).Closed :=
  checkUnboundedRankedBlock_closes (.nil)
    34 790 0x8270132f7040202020104010301010a020202020204040112050100020219bb04031f00084a0103fd04028105000503e80101fe040300062a120f1b092707180e000671010603011b300d332f3b4758530c0d000901010b2401b10100052f010618019704010001095e57125e4b07200000001000080b019b040103000701cc010b830200072701a50100062701a404020005042c1f273a06210c000702a701050f019b0401000202000a8709000543010a860402000a091e21251d060c000554010c0a190b191d06070005019201120914130f151707000502cb010008170b340403060009000a580109f70200061001f601000701f301090100067e0109a804020020040c0e160f2707100000000030520f57475e4b07210000001e000702c301d9020200051801d804020030251e392b05200b000c03e801079104010009090c0313051000000004121a2504181500051601101401171e051800000048040d3346051a11000901d40106a90200060d01a8040200000689070005180106880402000503030905050b000601920105f9020300050b01f80402000400071701db0401001e03292e2d051a0b00050601066c010587040104000501a301e90100050f0104e80200060f0102d9020005100102d802000702870101d502000601bd01d4046b02010002026a0404001c1f021f17220621000000010203071b000601880104020d0e0e1408070d0000000d090f0f11051b1300091c01081501cf0401000c1415031d0900070101056301c30401000c0b0b03200000001e0e111114051d000015000601b40111031c00000000040705070b0005500107090a10080506000b54015f630a2b653106000001020f1611050810000501010b3a01b10100063a01b0040200080e100e0b05080b000523010f090f0408000000000a02051c0e22171708081300051d010a460101990200054e0101980200054d01051901770401000d0e0a100f05080000000c181608041c1400051c010000040a100b06000617010705021804000901010002026b0401000000005b02000002025a0402000202003302010207020103010201010a052f0203002900
    (by decide) ⟨22, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem nineFiveRankedRootBlock40 : (⟨[⟨3,3,false⟩,⟨5,2,false⟩,⟨23,1,false⟩],43,2⟩ : Box).Closed :=
  checkUnboundedRankedBlock_closes (.cons nineFiveRankedRootBlock39 (.cons nineFiveRankedRootBlock38 (.cons nineFiveRankedRootBlock37 (.cons nineFiveRankedRootBlock35 (.cons nineFiveRankedRootBlock33 (.cons nineFiveRankedRootBlock32 (.cons nineFiveRankedRootBlock34 (.nil))))))))
    43 372 0x4100b11041c0007000601a1010f0b0318000006000501ee010b05030300075701100b0f031d05000520012c01b0302e0f37060800053201066c010f18210e2211070c08001101860143020103000502ba010d0b1713050500081e012f262f320505000a01db0112041c0f1b21061008000a029d01242a464a4d440624000000103d34514a505253081d1500055901055501090a16383a2b06100000001e42292b225e5e07150000002d2d0b3c324c50071f00080195010f4c01970277383d093a3e013d080501950203001b2614322932062519000a520107090f15111d1d081000000b0005660133404c2e4f443b47081c0a000e420101910200050180010190040200011c172104220b00060e0116142e2929320620080009530104111c212929472f4709180b000d0101050b017f01000a0b016d04010002020600051c015b04010014051615170518000000000809050a0f100601000000021b000a12015502000002025404020002020c000f0101000100
    (by decide) ⟨21, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem nineFiveRankedRootBlock41 : (⟨[⟨3,3,false⟩,⟨5,2,false⟩,⟨23,1,false⟩],31,2⟩ : Box).Closed :=
  checkUnboundedRankedBlock_closes (.cons nineFiveRankedRootBlock40 (.nil))
    34 936 0x5019401a302001f020203a10409000505d201d1010006059c015f02001702025d07000518012f0403030007310107c7020003020207c50900057b0103e30403002428091f2a1e06210d00060f012d290b2f33333a072309000b49010adb0200060d01da010005028401c7020200050c01c60100056801062d01a30401000331061f332606230c000611010306053605261a3829090d0b00050a010a7f010a8b040104000a1501eb040100080a13032409000604a6010603b901d50401000009c50700060f01c40100062a0109a90200060c01a80402000995020700050391019401000501d9010008fb0300060f01fa010006029b010883020005310108820402000912061b071e060c00076901051a01c10401001c0a171f04210a00083e01068f0200051801068e040200055a012a0b6506000d000501b301a90100060d01a804020000059902080005140198040200000a0b032009000a17010585040100000301100e0508000d000b2b01f70401030009029301d1040100121e220b080005019a011816180712050600060190010601f4018b04010300052101f70100062101f60402000400051801d90401001c210b22042300000c000502b801c9010005300103c80402000a0507070408000000000911150f042500000000050e03030d1e000c02b301d901000602b301d801000603d00101d50200060c01d404020001cb0600062801ca0402001005110804180a000d02c101b101000802c101018702000602c8018604010411010613191d08054302040f00080c013f0401030009170109910404040006170104c804030005000816010f950407cb050005360107ca040304000801eb0104ad04029902040106010101030701070201010d0e050317000501a001057f019504018b0201000202018a04030018071417042014000601800106040a101615060d000000060709070d0508000000012115111d161407101e00093701120b1d14200620000000000304130d10101107080000001001030b041200001f000501980110110b041d05000e45019101000558010290040200061910222305240000000c0d051a17051500001800052c011b011c11081d17170810000000211416251d05181400080101082301fb01000b2301db04010001cd020700050b01cc040200000500060c01b704010300084901018904010007030b0b0414000000000103050b11050d0000000710111a04250000000023000629017b0100050f017a0100080f0165020000020264040200020200000002023704011400050101000100
    (by decide) ⟨15, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem nineFiveRankedRootBlock42 : (⟨[⟨3,5,true⟩,⟨5,5,false⟩,⟨19,2,false⟩],101,2⟩ : Box).Closed :=
  checkUnboundedRankedBlock_closes (.nil)
    28 536 0x210173244474707000803d10109162621461706000501e701000d082135472e2f07200000002d3d1832530e1d072216000f4401fd04010002020600063801e504010016091f0f1f2f061c0c000642013c042f2c2f2f06000664014f3d5548473b061c08000d0101052b01cf04010018042c2c1f051b0000000016332c08110515000702c101082a01bd0100062a01bc0402001c350a1647462f07250d000643012425050b474406200800074501038d0200054901038c02000b4901ff0401001828050522443838080d00050196014528405838530600093b012e2a1934202c23081509000c5b01f30100065b01f20402000202000700054f01e70401000e0d2d462f2f06240c00071d011b0f33272a1a112c0814000000122d173b393b31071d160007018401121f042f321a1a3b4a09180b000d01eb01c3020000020202c20402001c072035084706201300071701f9020100031b1c2e1623172f08180e0009019201eb0204211603010a02040a030a0501e902030001db02010001d5020213010602330803031001010c0502001e3c212b37353b07203400082301c10205040308050f130503080b0f02010e0502000e1a20231705101b00075f0101bf0201003f12171f08170620000000081f0e20201d06100000000b16062c1d0518000000031b1d3704222b0008220101b502010001af020a0614190b01040b050c04010c0501ad02031a000501010b0b01080101000202000400
    (by decide) ⟨50, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem nineFiveRankedRootBlock43 : (⟨[⟨3,6,true⟩,⟨5,5,false⟩,⟨19,3,false⟩],101,2⟩ : Box).Closed :=
  checkUnboundedRankedBlock_closes (.nil)
    30 778 0x323203304409313b0800083e013f0d5246534706250800071f0104090a674965594a59680a18000000290816174d5b5f1600090680014e421960254a67650809000603f7010a0101051f01f3040100125d4f050b443b59080d000a01800107e90200060f01e80100060f0107b90200054a0107b802000b4a01e7040100192223172305100000005a5b430b645959072017000516013d243f4b6e376f01874f090b00065c0109270106c7020300050c01c601000501c601061601a30401000607443904180a000b01e60106890200056601074f01eb04010001222905271d0a000501af011305443b4a5906070008049d010e2922163e443b07200000003f0c2b2668052213000513011225240832596507210900050a010a018a01058104010400072f01ed04010300093e01cd0401000e07250f37051800000030630b1d5865062316000701c101061b01c1010006510104b1020300050c01b00402030008420104970401002533110b53470620000000000c13130528270614000000011f2e074f3b473b4a091827000a0101060c01d904010002020600055d0103c90401003004202238351a3e08150f000b02e901c302102005090308020809040901010f000502990102ab0201001049484c4c2f53473b09180000002131235b502c674a081b1d00051201142d0545134406180800054d0109029d019102081e0209040c171008010a05028f0215060d030f0104030404071104050e05028d0205001049064c4150385308180000004e09173256595959081d3d000701da010501d4018902070e100804010e0b0507090e01020e05028702030001eb020401060c110302040204190e13020e0501e902030021332a212f35293b35350a100000003d205735534a59680825480009770101e702090502060e0f01070f0e01030c0501e50212030a03030b20030d010308040c02031005040001d902010001cf02010001c90224050503030d070d0a02071404010e050200250231312e385007205000072f0101c10215070d130b0910110b0201020c05020001bb020117000b0101090b0102020200080101000100
    (by decide) ⟨50, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem nineFiveRankedRootBlock44 : (⟨[⟨3,8,false⟩,⟨5,4,true⟩,⟨19,3,false⟩],105,2⟩ : Box).Closed :=
  checkUnboundedRankedBlock_closes (.nil)
    38 765 0x192816220b3a23072100000001314114351d120009019e013f2f314a04220600083401070a01bd040100000500050f01ad04010002020005870900053401058604020002274025473b06210d00095d01051a01f10401000334460e0e3806250c0006340104e50200060f01e4010006480104c7020005390104c60402000d14392c04200000003c3f13111c3b3b47081700085301152739401a49062008000b01840103ff0200060f01fe040203000501f001eb010005780103ea0402003304100b230a000504bc0100080d1e0e2306000502e201091f100c3e1d2c071809000a0101054701cd040100312505172305220b00060b01091f2303040007048101201a242625251f0700052f0101211a3a232f3b07230900073001084501b50100062a01b40402001a241e2325252707180d00060d0133371d290b0525070008610102990200061b019804020019091520393b060b000803c10102910200000202029004020001f30206040197019e08074858019c0202510c0501f10203000e1c111b0b11062c00071101030d182229111a232c09100b00051c010801a501ed020100040a370a0826472c4a091d0f0005450107018a01e102030a020c041f090105020a0501df02030001d502020206070306060b04010905060724000602a10101cf0201001c273922233b3b3b081c0f00052401066701c7020201e90c01945e4c054f01010a0502000d22083535051800074601013f2849170b3b07180000001102021426410a273f4f5e0b081900060101086a01bf01001001d2011b1c36223b2c0620080008018a01f102480647560801ec044e02510a0501ef02030001eb025603474f0f430d4b05504e0248040401100501e9020300300e36352c380620000000032d1f20433a06184100082801df0201001815323223052100000010222822203a061c0000001f20232d23051c2000084001d302010001cd02010010300e17292c06240000000202000001c5020404060602090808010e0103050402031005020033190e322e232f07203800070b0101bd020104001a0101000100
    (by decide) ⟨52, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem nineFiveRankedRootBlock45 : (⟨[⟨3,8,false⟩,⟨5,6,false⟩,⟨19,3,false⟩],139,2⟩ : Box).Closed :=
  checkUnboundedRankedBlock_closes (.nil)
    22 775 0x21040d436259597777090a00077d011c402c2c3a175e6a69091d0000000901301c273735474709180006038d0105450128403a1e262f43373f474f4f0c100e000c01010701fe01a90201730301e4650f620e650b70710c0502a5020300240a11524f4406241e00081501870201000f07434d41232f0b0009029401028102010005141b262735370c0005190130194b494a35464d081c000000032d48160b173b140005270103032319284444532c090a00072301181622362705000516012a0c22172d43410700056f011827204d3905180700070f0120322e484905000603a3010801a801f10265026e016f01056a0b02d46c026a060201100501ef020300080507272f3720000501d201333f2b3229382f07000502f601004e1f61292c0e4708180a000802a8012d364367564706000501d5010903e001e50201020a04020705020a04010e100708050a010101140501e30203003c4b143a504d2353530918000000091b1e30453d083e3e091036000513010f212151396b58072009000d02db01dd0201000626130f1b27232308100e00073e0101d302010001cb07000602c001026c0401e66601e873650370080202010e11001102ed012d42474d3b47061c0800052c01056901830240020e01e25001a02f1201b001801f020c050281020300034e1d14354d4407210006019901056201ff02047003bd03030301e102026305090c0501fb020300273c3642414a441e000536011921233d2f373f0725000000151225445f47061800001600071d0103304834513b3b47080005018201124b151a636468072009000c3901ef0201000604292f3a4d0620000000061437756b2c7407191800091501093f6c356e44715974680a0b00063d01073e01e30204050265700202dd02c20604040f0005720101db02010000152e142b083e352c09120000000101172b4f574d590818000000022100084f0101d102010001c9020e60433d3101d201ad53504d43110c050200302151515344062200000002082c2e52051b000000020200000001c70210101042010e72039f0101dd03010c05024800100101000100
    (by decide) ⟨69, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem nineFiveRankedRootBlock46 : (⟨[⟨3,8,false⟩,⟨5,5,false⟩,⟨19,3,false⟩],111,2⟩ : Box).Closed :=
  checkUnboundedRankedBlock_closes (.cons nineFiveRankedRootBlock45 (.nil))
    29 687 0x9332a3541175307080005028b011e585e5d535006000502b30106635e353b590621080008018c01303f3108445006000516010e252322474706240000001360405c555606211300065c014e3613234d0e77716809000603ee010605010c1a220f26270a0c000000300b1b2b4c352d4b4f4d0a141a00073701191a13567117737769690a1d000000281e1b375927451600060d0106144712613b6d6908180a000c01010b028201064701e9040100090716505e4406220000003c4520404d1d4a4a17000d02fe0104dd0200060f01dc0100060f0104cb020300050c01ca0402000902a80104b10401000f3c2141145350470d000501fc0104062b2d25330600055701211569636b74740708000a4b0101142707333707180000000c0d4c4d44594712000501ef01101f270b675362072409000901f1016c6335475965071908000946011e39241a4d290607000c0381010c120a4e4a2f0607000602c6011210274e385c2c3b59680a1c000000155a66456d7f67018677091d00001d000875010e02c801f3020601020408040107141603020301100504050201140502ef02030034084a535005200000002108401d41594707230000000e361d4147051a3a000b01b401193d27232f17382f080005770101131f212a2b2b2b23232c0b090d0005080109018c010c02265c5f415907200000000c3009394a2c524450091600091101031c0a35475c06000859010b01a301d50213101d4102820e627d01c27110010c0502d1020300191a424a203b4450082000075d0124131622291d290710000000190f393935373f071a000000010625464744475308182200050501075b0104211d4d5306240000001f040b37656559680820001500093c01400a3217757174747709200b00062b01020200063002494a35472c08180d000b0101070a01b302010300050101000202000000000700
    (by decide) ⟨55, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem nineFiveRankedRootBlock47 : (⟨[⟨3,8,false⟩,⟨5,5,false⟩,⟨19,3,false⟩,⟨103,1,false⟩],105,1⟩ : Box).Closed :=
  checkUnboundedRankedBlock_closes (.nil)
    24 579 0x20403e38416e624a08000501c2015a1646496e76018507200a00080196010ae50200060f01e401000602d6010ad7020006018801d6040200121a093a313b0a000502ec010404111a1c1f26252709080b00075d0124024644416267072200000000215d43232c444a38624a590b1900073c010f0424262144383b4709080000000e001001a501d104010300083a01c304010006362324394359071c0d00091f010ac3020300051c01c2040200276020490b64566508210e00050801096001af0401000e2233253b314f070c000701b801114841297671650708000701c70169081a6e565606000501910100182a1c0b2f29293508140b0007130118222a1a243c4527373f0a100c00050f010f02d2010a870401000c11464d6767650720000000002d2e1a461d561800056a01000f0f04020a282e22292f2f0b080e000b5901075601f70100065601f6010005560106018401a9040100224744404f450625000000324a392f4f051500080f01363d21254f4306180800074d010b084c41313b06230800053001093b0109c70200060f01c601000601c70109bd020300052b01bc0402002028353b4405240b00060e01281e082e383a061b0800050c010d4001ad0401000a1a031942134107180d000b2801ab040100030b33331b2d45071a0d000627010c40302d31051c07000d3f01099d04010034073537274306220d00052d01001036302f354d3907180000000064246621270a457753092119000e0101071b01fd040100000008f1020900050d01f0040200020200000000020208b10401001100
    (by decide) ⟨52, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem nineFiveRankedRootBlock48 : (⟨[⟨3,8,false⟩,⟨5,5,false⟩,⟨19,3,false⟩],103,2⟩ : Box).Closed :=
  checkUnboundedRankedBlock_closes (.cons nineFiveRankedRootBlock47 (.cons nineFiveRankedRootBlock46 (.nil)))
    28 434 0x3551a6e6265060008019f01140f1c07471345071d0000003c19123f053823446b53536b0c1000000012064b2a401a2c3b4d59470b2900060193010b2c010530018f040100163e12131b41310b00085d013d16373b492c062008000d23010701000601820107860402000e3c0d5425273159080e00060191010b4601fd0401004b311735677406220c0007100134243d09454b4f0718090008140112366355692f0847685f0a140c000d7f010901d101e304010300050f01bf0100060f01be01000601e60106870203000501b301860402003025053e3565764a0c00080197010c192d2b372f31071c0900092e01306c3f177175735c6b746b0b100d00061801180c0230153441443a3b3b44470d080000001200095a01077401068d02190101020700061001060101020201010406040201010402040c0204060c0204030e0102030110020110072c0502001b132b55384453472e00050d011001040e3a29475608000a1e010516010685040100020224252052551d56740820000000020200001800052e0105f30200060f01f20100070f01d70100060f01d604020002020005ad020000020205ac040200000000001700
    (by decide) ⟨51, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem nineFiveRankedRootBlock49 : (⟨[⟨3,7,false⟩,⟨5,5,false⟩,⟨19,2,false⟩],101,2⟩ : Box).Closed :=
  checkUnboundedRankedBlock_closes (.cons nineFiveRankedRootBlock48 (.nil))
    33 593 0x1200b533f1d394345090a000701fa01063230561c43415557590a18000000282625664466595375091d0000000a512f573508233b5947470b142a000a03c00136393a01997b526201aa59018c019e0b100006029301074c010501d501f302028e1e0201ee3c03a803a005d23c019903a101f3781b030110050eed0203000202000eeb26000601b001ea040200141710561b453145081d0e0005080109028a01dd040103000901c901c30401005109306a7a4b770b0005028f011142161768680620000000182b6367455823072014000903e60110020613222e1f2d2f2d0a0d000000095d5d5245414453596568680c181d00076401065d78667853477d687a7d0b1d0d000815012a0f373f41556268656b6b0b1c0d000d02ea010ec70200063501c6040200080d01b90100056c01075f01a104010004122a5343414b4f4f091c0f00070192010eb7020300050c01b601000501de010635019d04010008140e1c073635372f091500000036300a0d236768190005018b01124f172f23505f474a09180b000b57010e9302000857010dfd020006018c01fc04020069541432673b4a072200000f0005018001019101956d52475b01a3082000000060570458375d5c2c6868535f0c100000000221000551010c3701c904010002020600062b01b3040100644d23125347018b07200000000c1b061c212d2939202f380b0c1e00080101050f01ab0401000000000d970900050f010d960200060f010c9102000002020c9004020002020e000538010ac50401000006001201011e1e010f01010201000b01010c0c01090101000202000400
    (by decide) ⟨50, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem nineFiveRankedRootBlock50 : (⟨[⟨3,6,true⟩,⟨5,4,false⟩,⟨19,2,false⟩],101,2⟩ : Box).Closed :=
  checkUnboundedRankedBlock_closes (.cons nineFiveRankedRootBlock43 (.nil))
    32 423 0x20202001e03f4011503c3010a01a1013f02400d1a261d3b08180a000901b301050d01fd0401000005c90700060c01c8040200059b0600052001059a0402000500060901f30401000400050d019704010000048107000518010480040200012a462c3805200c00053b0103eb020300050a01ea04020300073101d704010013100315111d06140c00063e010b13171f27051c0000000022141b1b27051812000c02960103990401000303070b1117171108080000000d0b0e050b1706101a000507010801f001a50401001a190b111d05130b000701dc01930202000501d70192040200282120292f05210b00050601000100060901fb040103000501b70101f504010001db02010001d70205020e0308010414070e02010c0501d302030001cd02014b4c080101f64809080501c702030001c3020f0a080b03130a0201020a0501c1020302020e0303050110010d0101070405100501bf02050024162b4638474a3b081d660008350101bd02010001b702130111060410020407150a0501b502010201010b010a020b04011704030101100501b302052d001a38011d01010201001a0101000100
    (by decide) ⟨50, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem nineFiveRankedRootBlock51 : (⟨[⟨3,5,false⟩,⟨5,3,false⟩,⟨19,1,false⟩],101,2⟩ : Box).Closed :=
  checkUnboundedRankedBlock_closes (.cons nineFiveRankedRootBlock42 (.cons nineFiveRankedRootBlock50 (.cons nineFiveRankedRootBlock49 (.cons nineFiveRankedRootBlock44 (.nil)))))
    36 655 0x202a2512092d1d07180000001f091c481741444a0815000701f90105143f3a2b4f0600060188010612361f3e4a0e4a0800050d01180a3d54290e41440809000601d00109029a01060c019b0100063e01051b0191040100050a311c3b440a00095a010983020005260109820402001b243e3538050b000c400108d704010002020007eb0a00064b01ea040200330a2317443b4a07200d00050601071801b90401003d1032452938060b00081701051a01af040100130d413b1a05220b0007330107930200054f0107920402000b192f27041d0b000701a001012a202a12230600050b010916311c401a06180800070d01040e0d0d040d06000b0101050e01e3040100000006cb0800056b0106ca040200000007001201011b1b010c01010b01890119038a0103c30200063401c204020005038101052801af040100070e0f0b11111d0b000541010030053a3a3805210800083b01038f0200056701038e04020016051b171d05100c00061b01041a35353a2f0600062a010a161f291a232307140900050b010c2401dd0401000f2a111d3823060b00050b011b2a07222305200700080101050c01c904010002ab020000020202aa0402000c04100b110b160704190007019801e7020c04070801030409040201110c0501e50201120d0501020205060a070701010e0501e302050001db02010001cd02200104080309020b04020a05020001c90219010322010d030107064b00051101c7020604080405080b0b040e02010c0501c502050001b7021411100a06070114080501b50204030e03050a100c04010a0501b30205001e2a052608203b2f3b09184100071f01b5023c1103020e01060501b3020300150d212811292307151800060a0101ad0201040011010106050100000202000202000800
    (by decide) ⟨50, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem nineFiveRankedRootBlock52 : (⟨[⟨3,9,false⟩,⟨5,6,false⟩,⟨19,3,false⟩,⟨97,2,false⟩],5529,1⟩ : Box).Closed :=
  checkUnboundedRankedBlock_closes (.nil)
    35 968 0xc1e0e3e01bd4701ba01eb01eb09210f000612012656206d70795d6b75770a0b00071401243c333d466451237f7301810b1d0e0006220118547e1e0c4a7601a31401c801b601bc01ce01bc01fb01e601fb11181c00062c01020202000b01a301ef0100062201ee0402002848212e2c230f472f3747570c15120008410147e3020006018101e204020020200c2c1b2525354f373f0b101100052001084c4925315f73630a09000501830121423905386a67206a6b770c0c0006018401067f0112063c10050d2001913201830185019277018601a10f13000000213c3f48019c7e7c7c7d655901ad01a401b30e1c2e000601010a4a01cf0100064a01ce0402000610242123131d5d5961630f000603a101061e2a46524d75616173750b00050390011e122707130a5b502c74766b530d140f000e7c0147c30200060f01c201000601ef0147a1020300056801a004020001603301cc2f028601be7702870912000702f4010422400d15473737574f0a1200000000241b0633130645200e32464753233b2f53112200071b01061e4b3f07281758672958565959686810081200080b010c5001bf040100011b042631325e0181018e018f018c6b0c140000001e0c20052924302e1d1d2f27310d0d28000701f70101213c1f0a052608414947292c474a4a100c12000e01fa01479f0200060d01060c01fd01000a770146010007029c014501000603cb0145c00200053401061b01a10401001c0d0d740b73776b01810e000801c501050d01ad0401000044910700051b0144900200061b01050f01f10100061c0143a102000501cd0143a0040204000901f701428b02000501a50106029701a1040100044a344a4e2f532f393b530b181100055201400d363f53173951470a0a0005580104110c0f2e362f2d2f370a000501da0101583473454a6e01c308200b000801cc011e3c101e18184c5f2b67653b0c080e000901010c1b01a3040100062021123829373b3b09180f000601010609018904010300050b014087040100000600060c01ed01000a0188013fa502000639013ed5020300056301d40402001015360c2f2f26621d383b65590d141300060101070a01c30401000400064f01ab0100070d01056001e9010007360139c9020300055c01c8040200400339041c0f27273f470a141000050601070a019b0401000400050c013e830200060c01050f01e90401000202003da70900050f013da60200060f013cab02000518013caa02000834010202398f04010038c10900060d01c00402000038ad0700050f0138ac0200060f0137f5020005110137f404020002020000003593020000020235920402001600
    (by decide) ⟨2764, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem nineFiveRankedRootBlock53 : (⟨[⟨3,7,false⟩,⟨5,5,false⟩,⟨19,2,false⟩,⟨97,1,false⟩],1201,1⟩ : Box).Closed :=
  checkUnboundedRankedBlock_closes (.cons nineFiveRankedRootBlock52 (.nil))
    37 649 0x25200a2e506b176953530a000802b60103001503124b455b2b580b293b492c67100212000e029e01051e01ff0401001c6d025e7277735f080d000901ba0130f10200060f01f00100070f01e10100060f01e00100060f0130b70200051b0130b602000a66012fe902000603e3012de50200062d01e4040200000a112215232d1f27090d000000001a510e7201975f5b07211d0008019c012da50200060d01a4040200002d8107000511012d8002000811012b990200050180012b9802000b029201d50401001236163a2d0b4b6a0c00050180010c09214b4a275f07200900081e010e321c59577271071c0000001954066647665f690815000901ad011c0d11212d2e47672f090a000712011806551f63206b5f237d0a180c00083f01083c01a10100063c01a00100063c01053001970401003c301e2942212351080d000701bb0106181321272b07100800052901077d01248f0200050f01248e0200060f0123f50200063701f40100063701052b01c9040100280f4c42313b06180c00060e0117543161575f062200000a0007740123a7020005100123a6020007100122fd0200062801fc01000b6b01ef040100284e3e134f37061d000d00072a0122970200050f0122960200062a0121ff0200061b01fe0402001c041909131706180c0007620121b90200061901b80100061901062401b704010021cb020700050c01ca01000a490121a502000a490120a502000749011ff30401000006000659011efd04010040034461153767071a0e00060101001da9020400050c01a804020300080c011d8b0200053101060901a904010300051c011c830401000000001ba902000002021ba80402000202001700050c01179502000a0c0110b7040100020200000002020dc50401001100
    (by decide) ⟨600, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem nineFiveRankedRootBlock54 : (⟨[⟨3,4,false⟩,⟨5,3,false⟩,⟨19,1,false⟩,⟨97,1,false⟩],115,1⟩ : Box).Closed :=
  checkUnboundedRankedBlock_closes (.cons nineFiveRankedRootBlock53 (.nil))
    34 875 0x90a0e3916293a17232f2f0b10000e000e6f01128b0401002d291d3e4e4b5b07210e00050801095401f70100055401064801d10401001638164a430f3b072200000f000505f8014c524a372705000804e4013861312d25746e2f082000000012061034161f293a3b09141800080101070d01bd01000b01a701119904010020455d325b5e4f0c000801db0151072a1b4f370620080006320110a1020300050d01a0040203000971011081040100221f2d30042500000048391e4b304c23590817000a03a3010ec70200061901c604020300073201b901000632010ea1020300052301a00402003419361d1f0519000000303c3c1f230b4129081818000a01cd010e930200052501071801fb0401000dab0600065a01aa0402000400083601950100060c010501fb01d70100072a0109b1020005320109b0040200115a6052501c68070d000802c201060c010702ea01050c01c50401000dbd0600060e01bc01000501ab010da70200050f010da602000601ab010c9f020005018e010c9e0402000e05063f413545070d00071d013c0c1f2b1b2737071809000503bd01215140322a233b080800054d010901ba01060c01c901000601d201054501b90401003222192541051d0000000014100f1d440518160005230132242f2f3b062200000000275166291a5f061813000f02ec010b0100060395010ba4020005019c010ac10200050f010ac00200064a0108ef0200062e01ee0402000320481a26470a0005490100150c08524a3e3e20590918000d000a02a10108df0200050d0108de0402000007e9080005380107e802000c01820106ef04010012284c47375606200d000a01e301050f0199010006260105850200050c01058404020004ef0700061a01ee04020000000600050f01db010006410104ad0200060c01ac04020004a90600061801a8040200060e120b040d0a0006018e01048b0200051d01048a02000701bb01052e0103e704010002020002ad0a00050f0102ac020007018f01a90100066601a80402000c112507041c0a00061901030f09171d1d1d07150000002104251515051b1300051d01051901191f3a083b23062300000019101a0b0b1d06141300090f011232352f04240600052001060101051a01dd0100061a01dc04020014171d031800000b00052101000001d10400060f01d00100060f0101a5020000020201a4040200020200001000
    (by decide) ⟨57, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem nineFiveRankedRootBlock55 : (⟨[⟨3,4,false⟩,⟨5,2,false⟩,⟨19,1,false⟩],91,2⟩ : Box).Closed :=
  checkUnboundedRankedBlock_closes (.cons nineFiveRankedRootBlock51 (.cons nineFiveRankedRootBlock54 (.nil)))
    24 583 0x202730401000603030b0408000000091607150416000676010701eb0171040100050e090d040c0a0008230167020e010d0104010106080565020300000000040e0a0d0517060100001d00077801d102010001c902140e100e060505140c010a0501c7021807010307040e05010407020c0501c50205000d36091d1f172f232f0933000602ce01065d01bb0201000e0e1a202c2c06200c000801f801b5021c0501020a080425080501b30203001c1d0229200b0620190005390106360101ab0202020906021a010f140506030c0502001b0b081d080819111109051e0007500195020100018f02010800060b010b01e6010f01e4010c01df01090d050708042126080900056b01040a32202305250700072d01c502130b040911020506030101010c0501c102030022211717271a0006790100072b2903200600071f01bf020100100e1337353b060b00050b011314382f3b05000902880101b3020100080205051505040c00083f01ad02010001a5020a0709150206080101010a0501a3020300018d020705040709020103010504040f020102100502001117171f1f27061837000701a801018902010005000b17010801010c01a4010a420173020501010204060101040c010503070e0502001510111704240000000209080a1405082400075d017102010001091e111d171a070c00073b01050a010748010629016f025e0c2503082f290404010a056d020300080d0f0b0b170619000509010c05170408050005180100001e1f1f2220052009000711016b0201000000020202020a000a0101000100
    (by decide) ⟨45, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem nineFiveRankedRootBlock56 : (⟨[⟨3,4,false⟩,⟨5,2,false⟩,⟨19,1,false⟩],85,2⟩ : Box).Closed :=
  checkUnboundedRankedBlock_closes (.cons nineFiveRankedRootBlock55 (.nil))
    33 555 0x2000801c5015e85042f8d05000518012f82040304000a04cb0123a90411db05000502890111d4040300000148341d263807230e000603be010c213f4967767607230000000240222e15354513000503bf0109240a09012811202c2c0a010c000c02c7010e9f0200060f010701ff010e870200053d010e8604020034026a263b130b00050b011e1a4258642306210000003c3f4f193e0b38071b1400070101050e01fd04010000000de708000527010de602000a01b3010cd302000a01f9010ac3020006300108f1020300052101f00402002205432b2c050a00050a01103e3549042206000b01b00108f902000601b00107eb020005110107ea0200085c0106f1020005190106f00403bb050005190103b8040404000501ce01063201039e0401d3020100020201cf04040002020001c7140006018701c6040200331f20142305200b00074a019f020200050c019e04020002020600063901930401001e2a0a2c3823060b00051c011521362023172f0721000000002c5444073323634f4f092018000a0101070d018b0100050d010601a50102810200060c01051001c10100070198010181020005740101800402000508030a04080000000a04151604181400086901080a0504180500065c0103111b28260e2c0718000000193836363f46061914000b2301060c0a1416150607000810010a13120e221f21070809000b01010519017f02000002027e040200130d0f032400001100080d01020271040100020200000000000d00
    (by decide) ⟨42, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem nineFiveRankedRootBlock57 : (⟨[⟨3,3,false⟩,⟨5,2,false⟩,⟨19,1,false⟩],75,2⟩ : Box).Closed :=
  checkUnboundedRankedBlock_closes (.cons nineFiveRankedRootBlock56 (.nil))
    31 740 0x2020007dd060005220107dc0403f305000502d00103ee0404000202070006058d019304010004950600060f01940100060f0104870203000503d901860100072701e50100061801e40100051801062801c104010003cb0600060f01ca0100060f0103af020300050d01ae0100051c010703e2019301000703e2018b01000603e2018a010007019401019d0200060184019c04020006080d1104100a00080c011005041504000a4d0106160b100811071008000801010b01a701a104010011220b1704240a00081e0109018c0199040100060c0d1413101107080d000903e70109070d0f0f051807000a048401870100066f018601000a01ac01630401000c0f0811191a060c0c00083c01630100054901620402030008049301087f0164d70432b105000501800132ab0403002e0d3420292539133b270a181100060101061101fd04010300053c01b6f30200062b01b6f20402005065203a707263070d0005019b01376e0c3f3072062308000902eb01b5a30200061101b5a204020400056201aea50200066101aea402000b01f00195fb044b8105000524014afd02000a240127fb020005700107620117b5040bdb05000516010bda040304000801b50104eb0402b7020100020202b504030002020001ed14000601f801ec0402001b041f1f3a2f062200000000300e27172e15000501ec010e13110b1d1706100800050b010b4d01038904010400050f01f50100060f01f404020300056801e30100063f01e204020002070e101505040000000021112923042400000000190a2629293806202100090101051001d304010300065901c5010005540102c4020005018501060d01e504010300051101054f018f04010300090f0104150f031805000b49010c0a2a2b2b2c2c0808000000181a3526123327071400062901085201094301018d0200051e01018c0402000d0e14172005200c00052d01072a017d0100050d017c0402000202005f02000002025e040200030b02251500080101000202000000000700
    (by decide) ⟨37, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem nineFiveRankedRootBlock58 : (⟨[⟨3,3,false⟩,⟨5,2,false⟩,⟨19,1,false⟩],73,2⟩ : Box).Closed :=
  checkUnboundedRankedBlock_closes (.cons nineFiveRankedRootBlock57 (.nil))
    27 612 0x902ed01ff04020203010203020206090a0501bf02030015291a1d07092f1a000839012c2b17092f310607000702ee0130102231414706200800083d0109cd020300053a01cc0402000317221c1c252707180d00061b0122040f261b1b310708000501e60108300d57573706250800050c010c049c0109bd02000601b20108f70200050f0108f60200075f01db0100061a01da0402001e24160d3005180b00083601e90100063601e8040200141f2f231b2f0625000000001e120c2e0b1c0b07180000000e38342c203a061824000a02860107df0200060f01de0100060f0107af020005100107ae02000702e40106c3020300052501c20402002e314517464a06240c00067d011f45401c3805210700060101060c01f301000a2d010693040100222e1c30041c00000d00090c01f701000a02c80105af040104000802820102ed04010400062a01bb010006018001ba046102010002025d040400030e0f10110515000000100409031d1b000701e9010113141417052207000501f1010601ba010b050b0324000000080a070507050e00072401031b1b0d080b1a1a080800000011030b0f04180000000803220e1e1e1c000701ac010d3801c10100063801c0040200010c0d09150f1107080d00061e011e1d20171723071c000000061a0d15040d00000014000a2e01b70100062e01b604020018181a0320000000130b130f041c1200050b010e0a0f0b04010600093e01019d0200000202019c04020002020e000518016f040100150d0e11042100000009050707041b00001500052801120b0d19171a06080800050101080b016d0401030005010100020255040100020200000b00
    (by decide) ⟨36, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem nineFiveRankedRootBlock59 : (⟨[⟨3,3,false⟩,⟨5,2,false⟩,⟨19,1,false⟩],69,2⟩ : Box).Closed :=
  checkUnboundedRankedBlock_closes (.cons nineFiveRankedRootBlock58 (.nil))
    36 519 0x502b601c101000602b601c00401e304000602b601e0040400043d60370e233707200d000602f9011307222b2041460908000601d6010f019d01f3040100422d0a3247490a00060182011a3636162e2d0618000000212e243d41474a2929091b000000021a00051a010c6201e3010006620112bb0200066301ba040200011a44325c5f4f5f08200000002a363a49574a3b1d59091b000502a3013a12311519061d0700071d01295c485c265e4a2708210000000041195a0b0f13062216000a0101051001a904010300051f0112830200050f0112820200060f01108f0200051b01108e02000a1b010cc504010002020009c70a0005250109c602000a01f70107a30403d3050005190103d10403000501820103a902000501820103a80401df050005160101d40404000202070007019101c904650201000202640403000e0813200b05240000000217000501a601051322142005200700051801080903171705000547010f132505292c1d0718000000000d000a6b01d9027a0234022b05062c3a042c010b010e0501d302031600053f01d10100065001d00402000a090f111105180b00060c010a0e0a11040500061a01050101052a01c3040100020c0d0a1005080b0005250100010403130b0b060809000801010001a7030005160101a60200081501020273040100730700050f01720100080f015902000002025804020002020000000f00
    (by decide) ⟨34, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem nineFiveRankedRootBlock60 : (⟨[⟨3,3,false⟩,⟨5,2,false⟩,⟨19,1,false⟩],63,2⟩ : Box).Closed :=
  checkUnboundedRankedBlock_closes (.cons nineFiveRankedRootBlock59 (.nil))
    28 524 0x2020005c9020700057e01c80402e70400067e01e40404030006019c0102a8eb0218060b010408040308050013020202a8e915000501c4010194b50404004e910800050d014e90040200004deb08000502a8014dea04030007430148c90424a9050005160124a404030400080183011fe5040ff705000516010ff204030400087901058f0402cb050005160102c7040304000a01c201f1047f02010002027804030003040d0a101606081400062f011c091a080b052407000501ae01060b0e0f150608000000181b151f1f2306180000000f14140e171a06221d000d5301060c01910401000202060005290102890401040005210135260b5e534006000000020105090e0f00050a010c0f0d1514050d070009110111270d192526060700064f010c630181022202210619072701242103010c05020002021400074a01fb0401000d0514142005230b00077901f70100067901f60402000c160d07041c0a00064f01090c061304180000000006150d1310050c11000b0101054801e90401000b0f1007000614011211030b0c0406000000001516111104240000001021210817051d00001d0006670102040e05050508000800083b0101c10200060f01c0010006460101810200052b01018004020002090f03080000000a141503201200050b0104040f1504080600070101007f0200050d017e0402000000005f02000002025e04020002020000001600
    (by decide) ⟨31, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem nineFiveRankedRootBlock61 : (⟨[⟨3,3,false⟩,⟨5,2,false⟩,⟨19,1,false⟩],55,2⟩ : Box).Closed :=
  checkUnboundedRankedBlock_closes (.cons nineFiveRankedRootBlock60 (.nil))
    31 699 0x1000604b301cf01000601af01ce0401e9040006038101e70404001227180a1c1d062000000e000503bd0101091921323a0708000000000c000504b5010d321f1f132708200800050d010e2601b704010015382b1f3a2306200c000504cf0106251c2a1a070907000d018e0105a70200060c01050f01ed01000601820104c90200061801c801000b02d701f504010004950600050d0104940402000003f108000602b201f001000501aa010c02d80111170b200520000000001e1f200b042400000000050f070f041c000000000f1c0f181d2a282b08092800050e010f038501d5040103000a7701b7040103000903c301ab040100050d0b0b11051d0b000501d601090b0f1105140600050c01130912181905040000000a000a03be01a901000603be01a8040200052b0175010005018701740100050188010643015fe302000102025fe109000565012ff10403000202070007028101f10401bf020100020201b804030003060e130d0f0f071800000018132a2a0e052221000710010408101316091707080008018c0112100d161c050d0700077e010b4201eb0100074201cd0100064201cc0100054201062701b704010001120b130409000501f601030511070418000000020a0008028701073601b3010006028301039b02000610010801e701038b0203000517018a040200040e0f111c05080b00050601070a019904010300071a018304010011061707041a0000000009051503211300061401030b0403000d4701051901df040100041511201705200b000732019f01000632019e04020012030d031c00000000060b07030d000000000c0a0a1916051c00084101072e018b0100053d01028a0200063d010531019d0401000b05111104240000000d1e1f1f0b05180015000622010a090b0408000000000900051301019b0200000202019a04020b00070d010002026d0401000202000000000d00
    (by decide) ⟨27, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem nineFiveRankedRootBlock62 : (⟨[⟨3,2,false⟩,⟨5,1,false⟩,⟨19,1,false⟩],29,2⟩ : Box).Closed :=
  checkUnboundedRankedBlock_closes (.cons nineFiveRankedRootBlock61 (.nil))
    32 850 0x501860181020005020203ff08000631018001000702af01018f0200250202018d0900051a01470403030009300105ff02000501bb0105fc0200065501ff01000630016901000502e8016804350300050296013404040300057a010505c9019f02002b0202039c080005250101cf040304000869015d042f020200000700056601f302002f020204f10800066601b9040300191a072e1f05220000001107081c2905201500051201141607031000000005170e03240d000605f00103071b1b131d071d0800090101060c01ef01000a01c201068f02000601b60104c7020013020204c5040a000501d501a30403000205000504f601e7020e01050604030605002f020201e510000523017301000a01b6014f040103000704be011c8d02000102021c8b09000517010e86020007170147a7020035020247a40900054d0123d3040300050008450177f5043c8105000517013bfa0403000202070006220112ed0409bd0500054d0109b60403001803060e191e0f070d0e00050101060c01ad0401030008350109a3040104000502b001fd010005100107fc020007560105f1020005460105f00402fb020100020202f804040e00093c01fd0401000c01050a110900060b0104050b1516050807000574011a140b04230000000800061f018d01000501c501028c02000502ca01060e01f504010002020007000601e5010195044f02050005190106030103010a0549021603181617030401080547020202030101010401010303020c050700020227000501af0143040103000c01e6010e0f021c0400062a010110171a0424000008000501fb01090f0505020000001319170804140000000f111417042017000f01a7013f020205010c0201010404050a053d02080106040804040301010a053b020500020200372400052c013604020005020e0e040900052d01070902000663010f191a031505000b5901290100055a012804020005080b03000900066101180508191105240000000811110d000558010b050503150500050501071801020507051005000000001e1d1c2020051d11000533010c5801310200000202300402000202002502010003030f031c0000000202000001030b0318220008100101070508170806100800052c010a15011108534b6a1d51030f420a0b0014010100030200000500
    (by decide) ⟨14, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem nineFiveRankedRootBlock63 : (⟨[⟨3,7,false⟩,⟨5,2,true⟩,⟨17,3,false⟩],101,2⟩ : Box).Closed :=
  checkUnboundedRankedBlock_closes (.nil)
    32 720 0x80107100b0b0b070800000008080405131d06081400052a0112110b2023170623000000000724240e171d120005028801061e0526232c29070800064f010b5301e70100060f01e601000601cd0103d10200064401d00402000219070b04220000000034042114222a163f43470a19000501d7011e1e04172c3e293e290a180b000901d5010b3001bd0100063001bc0402000606060a0305080b00050292010e0b0b03000502b701011917130405000649010603a601ab0100054a0103aa0402000803131509150b000501ae011b1215021c081a23080c0a00087101181c1c191313061d08000639010f1827200b1d061808000c04a901ff0100065601fe04020002020600067201f104010019091f20170b060b000702fb011e1b070b221706000802b601121e1d170b0520000000090b2414101f1a290813000630010a03d301dd020200052801dc040200081216051116060b000702940102080a0e131706000701bc010803a60102b9040100011b101a230b062000000004101311170521000000222a25200d1c061d2200096601f10206010204030303030903020b02010e0501ef0203001221020a1705241e00060c010a0e1316040500075a010621252a281c0e0e2c09180b00064901092e17110e35061d0000000c0f121b28213623170915000550010b01b601e302050192055808220e2e022c04010c0501df020300080e050a051106081e0007300101d302010009021c1618191d19080c00000012120606281126221a00076a01031b172a2c2906210800051a010a4001cf02010013050e2017050d0b00051d010a5001bb020100010605170b17202308200e0006018b010005160a1611060808000a1901b30201000c040d0e0e1a1a2308080e0009010105310108430101bd02010001b90211010102040106010101020202040202040703021405020001b102010001ab02010601010703020301030102010701091005023b00160101000202000400
    (by decide) ⟨50, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem nineFiveRankedRootBlock64 : (⟨[⟨3,6,true⟩,⟨5,2,true⟩,⟨17,2,false⟩],101,2⟩ : Box).Closed :=
  checkUnboundedRankedBlock_closes (.nil)
    23 584 0xa0e0d0717051c000000000421052004221100082601038702000501c4010386040200011a170b0b05230c000511010e050b11050a060011038201060c09140b050600064b01093301c1040100030e050f0b110a000601cd01060a2214200506000502bb01070819190b050c0700050b010c2e01b10401000c13101604090007018e01191e0a170b05220000000012041413040811000d02880195040103000603a601db04010012060b161919201a080c0e00091e01d101000602f301d00402000912241e211d292008090e00094301c3020303025836320231080501c1021401040a020201040503040701010e0501bf02050002120f090f0b062b00073a011207102a292006080000000b000602d201bf02010001af02030a03030303010309030a0501ad02030001020b131d141d1711090823000601c401000001ad0212010d010202040a030206030c0501a702030001a502050b050601010803030104010c0501a302032d00100101050a010e1708040400052b010d051a08042406000d3e01eb0401000d070a0505050a0005630115181703200500082001d50100063301d404020002020906050e190508000e000d3d01af04010004070d0f04140a00072a01a1020200052501a00402000c130e0804220a00051501000a0a040e111706100900070101052c010287040100376c6f290907060c00054001d30100060c01d204020001c90600061501c80100081501bb04010001b90600061f01b80402000400051601a90401000a0511031d090005100101a7020000020201a604020b00120101000100
    (by decide) ⟨50, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem nineFiveRankedRootBlock65 : (⟨[⟨3,6,false⟩,⟨5,2,true⟩,⟨17,2,false⟩],101,2⟩ : Box).Closed :=
  checkUnboundedRankedBlock_closes (.cons nineFiveRankedRootBlock64 (.cons nineFiveRankedRootBlock63 (.nil)))
    31 493 0xe0e0e0f04080600075901bd0100060f01bc01000601c20103ab0200064a01aa040200160507111105230000000c150d181408060c1600060101052901990401000705030315000000000c0e0f080805151400051f01083e01038b0200056901038a0402000e03090f040d0b00060d010a16141a1105250700063401161a0e032505000502ca010c100905090606000b02b301073701d90401000c0c0f19081706200c0006019d010f05141111052107000a02e201c7020200050d01c6040200020206000602d00102a704010006040b101905220000000518071a111a06241700093201e702090c030204070101080501e5020a2121041c0a242420290a0501e30205000f0f0f020b110610002900096a01db02010001cb0201040201020205050301030501020e05020007100a0a100506200009018f01c7022e230119012c021a09020a0501c502030001b7020402020102010b04081f00072d010d180711111108100000000c030b0b11051100077701054e010b0101060207010601010a0502000115050e05171111080c180008750101ad0201000a011817081a1a07080e000f4d0106070a0b0b0510070007490101b5024c22260542280201080501b3020300022b6e6b0873060000090f050804142100060f0101b302010001ab020109001401010002020000000600
    (by decide) ⟨50, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem nineFiveRankedRootBlock66 : (⟨[⟨3,4,true⟩,⟨5,4,true⟩,⟨17,3,false⟩],117,2⟩ : Box).Closed :=
  checkUnboundedRankedBlock_closes (.nil)
    42 587 0x510a3e1e1b6253072209000602e70130525d13274f4f070800094001119d0200054a01119c02000a4a0110e702000704de010f9504010400071d010eeb0401002c553603225a33374f630a1000097d01050d019d040100000b8707000525010b8602000a4d010a9b040100063d41350e05210c0006280107bf0200060f01be01000628010791020005190107900402000b050f131d05180c0006240106e7020300050c01e60402030008210106c1040100021b434704200b000b4901e304010002020600063d01d304010012151d2527270619000000030c131b1a0b060517000618010e120510110b060700050189012a390b3a04240007000c240104b5040100010b1b271f270b000502aa0100101a17232305230009000c3c01ef0401001508352f042400000c00054101bd0100064101bc0402002223252727051a0b0006250104280b38380506000801bf01051d01a1040100120919191b1106010c00091e010381020005350103800402000410091611171d07140e000d01ac01e504010015272b3b04200a00057901053c01df0100060c01de04020002bf0600063001be04020003140915151106050000000216342f3544061b0000001024181c041d2000093701b90100060c01b804020002af0600060c01ae04020002ab020700051a01aa040200151605462c4a4a07200d0005010108230193040100332d1a372c052100000001253108352c06181600050701072601028104010001fd020800051a01fc0402001b2424071d1f2c070d0d00070101060901f90100050901020201f504010600250101000100
    (by decide) ⟨58, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem nineFiveRankedRootBlock67 : (⟨[⟨3,4,true⟩,⟨5,6,false⟩,⟨17,3,false⟩],153,2⟩ : Box).Closed :=
  checkUnboundedRankedBlock_closes (.nil)
    38 799 0xf0d3720083a06000501c1011a2b172d3105000512010806b50106241d211b1d310708000646014c4709510f250158663601060c00001b31011b390b372c38230a101b0008019201091e01d70100061e01d604020006019e010e052d300418000700082701c90100062701c8040200111d2517171f061d0c00050f0126023a3a17050009780104830200054b010482040200313a200823232307230e00062801080b17271f27061d0000002136354a292c062013000614012e042f4635384a071d0900062201097f01df0100067f01de040200272a362b223b06250c000a02de012124420a480e0623000000000c000b2c01b304010027123735292e2307250d00075101041325340b0e072108000b01d60105260191040100240e0221232f0a000501860109052341440524000000000b000528018901000501f50103880402000121341d2f3b06240d000703d3011c16141d2b2b34350900000000030706140a45380e08180000001a000b028001e102022a090401060c040c040503040101010101120502dd02160e13020405070d030a08030c0502db020500021307201d200622000000201a1c112331063e0007019401100625171a173a071b09000736011d0829080b05210000002e363f080e2b3b071200064b01071901d902010300053d012212111c312f06190800097301cd0225020e070407090c11040a0502cb020300060001030b17061000000012131747263a062026000520010601c8010002c902010002ad0201001d140b3b2f233b2f081c15000671011525272229192b231a232c0b140d00060f012d012a361c1c41071c09000501010601ab0197020410040313080804041808010c05029502030002910217100e0318080808080507050c05028f0203011a0717100401010e080602010e050400030d221911112307104400053b010638018f020c0318151c04080402030a05028d0203000289020702020312021e0a01010a050287020300060e1214151117072f000728010002810201001c051304035b2b0b232f0a0000240c37352c0e4a3b2c4a3b0b252000051101020200091e1f061a143a071a0c000a0e0101ff020104001d0101000100
    (by decide) ⟨76, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem nineFiveRankedRootBlock68 : (⟨[⟨3,4,true⟩,⟨5,5,false⟩,⟨17,2,true⟩],121,2⟩ : Box).Closed :=
  checkUnboundedRankedBlock_closes (.nil)
    41 775 0x16190123081a060005029e01101a25370f1f062208000906dc0128211a051b1306210800070101060c019701000a01b9011785040104000601a30116af040100090912130f05150c0006370113c10200060e01c00402000000138308000529011382040200160e0b05171d06180d000601ac01072a1c2c14232307220900064f010db90200060d01b8040200000d9b0700050f010d9a02000601c5010c8502000501b6010c84040200070e11170f051500000000140a030911051600060f011c1916220e261a23081d0a0011058e0108b502000b4d01fb040100010c10100b0f0601000000090f2816192b2c071018000601a10107191d1d04000602a5010402082b190e0624000000020c000701ab01060c01c70401030008320107990401000309031d1117060c0005390110160f11151106140800062d0105010006019901059204020002020700060901ff0100081f01ed040100120c0f12040900072301060901dd04010300053101048d04010001020f222211221a0810001000094601d50100062901d40402001a010d031c09000902e301020e0305090506020800081d01b70100061d01b6040200121d1923292c2307200d000829010393020000020203920402001e0d200e2b23062114000653010d0126201a0506000b6f01f502040b0a080304090220030a0502ef020300030111111705181a00074e01ed02190b010107090b08060101010c0502e702030001131d1b04141b000801ca01cb02010002c5020100150119292223062011000601b1010313270527052c2308100a000a01e201b902050319020d03040403020a0502b7020300000c160f1c151900057c010c0616141a23061808000901b301b50201040c0b0104010101010a0502b3020300029d020620040204020a1402030a05029b02040c0e0a0e100801030201020c0502990205000289020a0903020310020b08050287020300028302191507010b010405030202010c0502810203000d090f1c171706106800074701028102010001fd02071403050306080803010a0501fb02030001f502011d0025010100020200000500
    (by decide) ⟨60, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem nineFiveRankedRootBlock69 : (⟨[⟨3,4,true⟩,⟨5,5,false⟩,⟨17,2,false⟩],117,2⟩ : Box).Closed :=
  checkUnboundedRankedBlock_closes (.cons nineFiveRankedRootBlock68 (.cons nineFiveRankedRootBlock67 (.nil)))
    29 884 0x22a0f1e1f2d21192737290b1c0d000723011f23311f1731334545091b000000182d5719014c6325232614680c181c00051a010740013af702000623010604d501060901db04010300062701df01000502a6013ac50200062801c404020000303d173a0b2f13082500001000092701d101000627013ab70200060c01b60402003abb020700050c01ba04020300080199013a9f02000a059a0139af020006500134ff020005280134fe04020074410e4d01845f674b0821000012000a2601e30401000035cd0700060c01cc04020035c5020700050d01c404020300090d0135ad0200053d0106300131c50401002806000602e10128880402001e151a071919061d000000000c05081c041c1700090101050f01f701000601e6012701000603b10127c202000501e601062401b1040100042a050a382f061c00000000061d23232f052117000c01a70125c90401000000002309000601a70123d204020007282b173d5932470821000000222622401c4918000502f201583407244f4a6307230000001001011f391a0b2c081a16000727012824033515172b3b081c00000018210511070906180000002d1c3e3a4d4706232000072f011a290f052b1f3708180000001d447039744557130815000602ee01153004042219440d0e1d2c0b000701d8010b3801e104010300050f01d30100060f01d201000639011487020300051a01860402001e290f0e0d141b1a12090a0f000a01e301148d02000701e30113c50200050f0113c40200062b0111890200051c01118804020001271c25234a4407200e000702cf010af70200060f01f60402000202000ae10900060c01e00402000ae3020700050b01e204020300070182010acd04010400055901f30100063201f204020048482a053145503559440a1800000048092709375756413259470b1f000b440109c30200060d01c20402000009b3020800053401b20402001f251a0e442c06200c000601c00109091c080e3b060700054b010418242f3105180008000d3f0109a30200053f0105330108df04010002280e0a2f0b06200000003c393543413806231800050e012e0c46071c354a072000000b000c3301f104010002020005d90900064001d8040200241208261405200000000e010f191b311d1d08191800070101051c01c1040100150106211d3106180c0008130105ad020000020205ac040a00060c01050701020200000000000700
    (by decide) ⟨58, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem nineFiveRankedRootBlock70 : (⟨[⟨3,5,true⟩,⟨5,4,true⟩,⟨17,3,false⟩],213,2⟩ : Box).Closed :=
  checkUnboundedRankedBlock_closes (.nil)
    46 669 0x53601f90401000305050f2f130a0006019b01141a212309051c0000000018090816171106101300070101057d01eb0100062801ea040200123f080d3e3b4707180d000c3401bf010006340106b3020300052501b20402000911082f2944470b00064901070d0317111706140800060101060c01a50401000202060005100106990401000f310b38040a00075c0105210f1f1f1f060700050183010633391c29291d0708000550010c4c01ed0401000b17301d1d273107180d00050801093101b5040100120911143538062300000028172c113105201600075e010607260b0b17062008000b390105a50401000d0405161705080c000638010e1821272f3131070800065e0133422a3e1d293b4a081a000b000f6a01e10401002739292304240a0007018f0104c10200060c01c004020004a50600060c01a4040200048d0207000539018c0402000612052e2f13273108180e00051c010c251610081123232c09140000000e0310050b0b1d071517000e02ca010485040100093f191c1a1d0e1d1d092110000620010d13161a1a141a070509000616010d031c1b312b34390a090a0008029501086101f10100062001f00402003c1f0d1c1a471d07220d00050199010601960103e50200062401e4040200181b24231f270618000000041212271d05221600071d01df020000020203de0402000a02061d0519082c08151500081d01c702010003a90201000a042817202b29112c2c0a101500081a01a1020100039f0201000c0c140521172007091200073f0103970201000383020100062e1914172c1d4a4a4a0a1d160008590102fb020100100a1e012802351b06160a00004b302b1d1d3206201a00083301ef02010002ed02010002e90203030403030413082001040201010e0502e70203200012140102020200190101000100
    (by decide) ⟨106, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem nineFiveRankedRootBlock71 : (⟨[⟨3,5,true⟩,⟨5,4,true⟩,⟨17,2,true⟩],173,2⟩ : Box).Closed :=
  checkUnboundedRankedBlock_closes (.nil)
    52 756 0x4d5a503000603eb01d5a40402000004ccd3090006180104ccd1030005180102a6a90403000001a885020001ad020201a8800401000202548204031c00050a0125c50200082c0120d50410b3050005640110aa0403000a030b06051506100d000b04cd011cf5020008550119ff04083a360305023805310304050c05010002020cff0403001e0d251f290806182200050101050d01f7040100000da507000533010da40406d50500061d01d204040300060a01d9040103000620010c950406930500052001068a0403000aeb0700062001ea040200000500051601bb0405a10400052301059d0403000a8f0700050d010a8e0402000009070006049d0109e60404f70500053e0104f30404000803091c161c0b07100e00050b012a251d2c052506000501b6010b261a042505000a3301079d0200055f01079c0403cf020100020203ce040400121405050b051416000512010c100a0b0f060d0008000c5201ed0401000a0b101a2905250b000b3c01c30401000c010e050b100f07010d0006230105b1020300052101b004020025082011040900050b010b2a260811052007000b018c01058f0401000c0d0a10050b11070d0005660118101f2304210600072f0104e5020300052b01e404020008030910050f06040000000d021703121400050c010808191111051407000b1601d70401000704100b1105100b000b2501a10401000804040f0b0b060d000000000c010207172906170007320106610104870401001e222b03220a00071d01f10100061d01f0040200150415271d17082b081000001000064501dd0100060c01dc04020003d70600063901d604020300061801c5040100150716221a11062000000e00053101051801bb04010006010e0f0b050a0006730103b70200060c01b604020003a10600060b01a0040200020500051b010381040100071c0b141a232c07200e00072801ff0100060c01fe04020002f90600061c01f8040200120102131610051108020e00061a0102e7020300050901e60402000000020202df04010c00310101000100
    (by decide) ⟨86, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem nineFiveRankedRootBlock72 : (⟨[⟨3,5,true⟩,⟨5,6,false⟩,⟨17,2,true⟩],229,2⟩ : Box).Closed :=
  checkUnboundedRankedBlock_closes (.nil)
    45 764 0x6f90200062901f801000b2901e9040100010f0a28111106210c0009450106c1020300050c01c00402000205000605910106b3040100181621111722170c000802a80127260e2323052207000701850127312914110606000b01ac01097f01f10401000c04150917210a000558010f0d05031b0500052e010f2113252e31352c08210000002133251402233535081817000841012d002d17251a353508100a000e03960105df020300052701de04020012101c23231d060b0007019601180a041c230506000602af010802f501058f0401002a1e110829232c0c000804c201161c081d320506000604b5010802ce01e9040100081414101c1d1707100d000647010c12101115170615000900081c01cb0100061c01ca040200011a191910171d071000000f00061f01af0100061f01ae0402002514040e31322b07150000000211000601d90104a70200060c01a6040200048f0207000501dc018e04020004830201001e27043135353507250000000f122b312c2b06181d00075801fd02010300071601df02010002020f180e34342c06220e00074c0103b702010003b302040116020d040f040804040701010e0503b102030003ab0201000395020100140420070919061e33040a32000776018b0201000d181920051506140c000802ae01ff02010002fd020705040205010401171602010c05020002f702010002f10209020606031404180903080201020e050230001101010a330104810401001212242e34223535081000001100063c01fb0100062401fa040200030e1a2c2605250b00050101062f01dd040100020203b50800061801b4040200251911193405200b000501990103b10200061501b00402000400050c01a904010003930600060c0192040200038b0200000202038a04020002fd02030304010103200d030d0a0502fb020300011b1f111d05182b00064101053b0102fb04010002f7020807060b100705010403030e0c0502f5020404060b090b03050b01040107020102100504001b2126140e2b2307200000000202000002ef02014100290101000100
    (by decide) ⟨114, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem nineFiveRankedRootBlock73 : (⟨[⟨3,5,true⟩,⟨5,6,false⟩,⟨17,3,false⟩],271,2⟩ : Box).Closed :=
  checkUnboundedRankedBlock_closes (.nil)
    36 826 0x618101a16232307140900061c0107272d453b4444072300000018032e1b54563b4a14000601f701050b01057f01e70100067f01e60402000904420b3b3b470b000501b60128162e150f0500051701223234392505200700064701142815152d051d0000003c3d1748295906251200052f01363f232347290e071c090009019b01605b3a3d1d2047476b091c0000000f2f33263b233538081a1800080101087701cb0202000503d301ca040200102b10113731313b0c000702cf0106520104bd020d01180513140407050c08010c0504bb02030b2b0425010c0403020a0504001e0527371d2b3829000902af012139140d0d17493b4a091b000000244e303747323a59081700060290010702960104b5020501100406040214141c03020c0504b302030004930201002e2751283947583808230000002d3051233e1a4a071c3100097701eb02010003e1020c140c1705041308040d030103010e0502001224060d2e26232b232c0a24000602e6010602b901dd020100422519111a535907220d000802ce01d302010003b9021353113c0101de147813156401c515030e0503b7020300092a4c3a2b1d4a4a590928000a4601af020100039f06000902da0197020100038f0202030e061c10120603140d190c0502001842332023080b3b082000000033092723473a595308182e000516010802e5010f4848253226590708000802ba0102ff02002002d5011f19031c1717171d08150a00060d01093c21053805250700060181012a095b1d1d476b47080900050281010c2401b90401000d0e0515231117071500000002342d350927061a18000b01f70104b1040100049102010010574332354a3b59081b1400084801e9020d0a060a0c05170114050b0405070405100503e7020300130f1a0916222307102200087901df02010003db0201000418130550494a4a4a594a0b1a001700077101d1020a04101718160814030304010c0502004e4e0c3a324706201a00065101b702010003ad020100039d020100039b02030706041d04041a0410100403020e05039902030003950201001201164d3a4706203300073b01038d0201000042241a50353b594a09181000060f01038502010002fd020109000f0101090b0102020200080101000100
    (by decide) ⟨135, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem nineFiveRankedRootBlock74 : (⟨[⟨3,5,true⟩,⟨5,6,false⟩,⟨17,3,false⟩],225,2⟩ : Box).Closed :=
  checkUnboundedRankedBlock_closes (.cons nineFiveRankedRootBlock73 (.nil))
    28 694 0x5018f0108e90200063a01e8040200150111442629594708200e0005200102120e10051c170804000000004b34572c0b35062115000a5d0108dd0200060f01dc04020300057401c50100067401c40402004c3011144d264a1d080d00051a011325370a4a443b0708000565013011094f352959072109000503a0012a0d53444a593b590909000d028a01081a01b90401001e42161c0e593b07210d00083801050f01ad0401000202000899090005300108980402000f2014172c530b00063d012403151356281a0e3b4a0a180c0005019301082901e90100062901e80402000429352d3b273b07180d00054b014f403a493805000a02970107df0200060f01de0100063b0107cd0200052c0107cc0402000707191414161717080e00060e01012c15192527061808000a01a401ff0100060f01fe01000601dd0106f1020006019501f004020030402f14474a06240c00081e01201c45464958072108000513010f4823522b41530708000e01e801055901e30401002c020c1d0d27061b00000035332739042015000601b101280c071705180000002921133125050f00065601362a253a09051b070006730103334c37282c061808000c01e10106d7020005390106d6040200092740233417472f080e00051a0103070f0a19171708050900050d012e05513e351d062008000a5a01f70100065a01f60402000202000700054e01ed0401001c19082e2f3b06220c00061e01102804442f4747072100000004012527133b3b13000b0191011e092208263b062008000523010a5101bd0100065101bc04020019431a323b3b1707250d000660014e5423472c3b06240800061f012509610f1a295f4744590a1900000003280b051d2b382c081c19000f4301059502000002020594040200302439433e3b47072000000015292f313131273b08182200070701050b01020204f104010600100101000100
    (by decide) ⟨112, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem nineFiveRankedRootBlock75 : (⟨[⟨3,5,true⟩,⟨5,6,false⟩,⟨17,3,false⟩],195,2⟩ : Box).Closed :=
  checkUnboundedRankedBlock_closes (.cons nineFiveRankedRootBlock74 (.nil))
    24 759 0x26401b1a253b2f353b091b0000000078346601817e7e4b672b09221b0006100118126c5e287c7d7d0821000000020e00060191010b2801b504010055292d6e7363760b0005038a0120510b32413a06250800050a010a01970127a502000a0c0126f104010400084a0124e904010004797c62440189725f0e000549012a2a2b214350522c23440a180c000a4e0125810200050e012580040200000023910900057c0123900200057c01063501bf04010004514353300e5f56080d00053401030f010d3009282d360b171741380e050000000214000a018601053b01a90401001e0208325747380b00061a011802100b2e35270708000502c301306956064c576f072009000c51011f9f0200051b011f9e02000a5a011efd0401000202001dd5020b00053101d40402000218030d1e2b2e1f080800001000063201190d0d0e3c2543083a500b0200000e000c03cc011de302000502a5011cc702000555011cc602000a01dc011a930401004e270a64554d64686b090f00051c01163305112727071d000000274d283e5856473b4a59590b20000000291d3d4657370b072124000a0185010ebf0200060f01be0100061b010e990200060c01980402000e9d0600056c010e9c0200056c0107018301f70401002a0619122d1b061b0c000601ec011c1137273a051c000000171a052923051d00000019101c0f5e120a10081d00074b0130301f1f354506000501ba01183c132121433244081800000c000a0181010df50200061801f401000501bd01061801d10401000dd5020700050c01d4040203000817010db30401003c3f204a564406200d000b01a701e90401030007019d01d704010006070805140b110b11090200000000333c3f413a35594a081c00050d013d3050482b4458072209000b3c01c90100063c01c80402002828463b3a41061d00000033310223584950071800001a0006250118631417085c4d2308180a000a2a0109cb020300050c01ca04020002020600061901b90401003215363b1b31062500000e00080e01020209ab04010600070101000100
    (by decide) ⟨97, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem nineFiveRankedRootBlock76 : (⟨[⟨3,5,true⟩,⟨5,6,false⟩,⟨17,3,false⟩],193,2⟩ : Box).Closed :=
  checkUnboundedRankedBlock_closes (.cons nineFiveRankedRootBlock75 (.nil))
    24 477 0x107901802d376f5f6f08210b00062001682560745957735b08090005029101300634474128293537450a1c0c000501910107440155810200050f0155800200076001f10100063701f0040200037e7e061f2022730180018f2c5f0c18000000032142243e433223583a4a583b0d10260009570154d10200060e01d001000502c10154c10200060c01c004020054b30600060f01b2010006490154a30200053a0154a204020040023d670e6f23630d00084601506c74464a4f76072509000d6e0153f30200066e01528d02000501c401528c040204000801e90149b30401004c283207565a732f080e000701f301494954712e018f06250900050801092801cb040100542c396e1213770720000000002d54245a4b4e6207221a000d58014a8f040104000901ad0142fb0401000c080e0713030f07140e0006019401223a4e4c262528071d000000420654364171533b081d16000710014507726e765947071b09000a0101083201e50401000041c90700061a01c80402002006160f3a25061c000d0005100141b7020300050b01b60402000400063001419902000a0c01408d040100020207000512013ad70401001c081709511b06200d00050601070a01b70100060a0102023b9104010000000036bf020000020236be040200001700
    (by decide) ⟨96, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem nineFiveRankedRootBlock77 : (⟨[⟨3,5,true⟩,⟨5,5,false⟩,⟨17,3,false⟩],181,2⟩ : Box).Closed :=
  checkUnboundedRankedBlock_closes (.cons nineFiveRankedRootBlock76 (.nil))
    33 522 0x121a03190a24151607272f0c050000000039606757016f6b6e74018e475f0c182100050c01070101070d01dd0100060d01061101c101000702e101d1870200062601d186040200634c78010f6f01825c713e590b1a13000b01f601d0f70200071f01f601000603ae01061201db01000702900101d0a10300064101d0a00402000f0c06270110101c0e4c4a5d235c0e010000000a16030326213a2d1b093b0b102500080101060f01ff0100054801cee50200070e01e404020001ce9d07000711019c04020300057701ce810200062901ce8004020029413d486e5a334f08230f00060101060f01ed0401000001cdb50800074e01b40402003c272a44191a060b000501a6013115283535385307200900070290010f275725280a370b414d290b180000002d0137501825320721000000001d00087501cd8b0200061a01cd8a04020400081b01ccd104010001cb9d0800062b01cb9c04020400097701cabb0200050d01066a01c0a10401000202000196c30b0006300196c20402007445573b01826f6e6b08201000060187015870737301836f1b0800092b01019c8503000643019c84040200691721226e297c0c00060d012a6a36340e527d07200900080101060a019bcb0401000500061001ff04010000000199c909000511010199c8040205000522017ddd0200050f017ddc04020002020057b1020000020257b0040200000000020200001b00
    (by decide) ⟨90, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem nineFiveRankedRootBlock78 : (⟨[⟨3,5,true⟩,⟨5,4,true⟩,⟨17,2,false⟩],173,2⟩ : Box).Closed :=
  checkUnboundedRankedBlock_closes (.cons nineFiveRankedRootBlock71 (.cons nineFiveRankedRootBlock70 (.nil)))
    20 573 0xdf88f0300061901f88e040200000600060e01db0401000df7970700061001f79602000550010df6e50300063201f6e4040204000903d101e78702000803bb01b3e504010005000603b001b201000602d0010da4b10204000503a001a4b00402000c80fb020900060b01fa0402000005000503a20180d50200050189010bcdff0300051d010bcdfe0405e7830700051d0105e6ff0300061d0103d8df030005300103d8de0401ecb3070005180101ecaf0404050008440101a4a10452910600056401529004030075bf020800050a01be04020300061701759904010074ab020800050b01aa01000901cb01748502000a780163b302000701f40150c30200080195014ffd020005018b0147db0200053f0147da0423ef020100020223ed0404001025405c17431500054d01274b4e311d505323081800000038202b3b252b061c150009028a0115e9020300050c01e801000a018801159302000a01910113d904010018042c23462306200000001e132a1f050e2b2308141a00063c01070a01f70401030006170112b704010011e5020800050b01e404020300071c0111ab0401001319541c29504756081d0f0005080108018b010f01000519010ee1020300050c01e0040203000815010e8904010400060c01db0100050c010549010db90401000202000cf30a000529010cf20402000c04050b16171d070b0000000004042f1a353849071a00082701098102000002020980040200012a17251d051c130005140100011909091d052008000a1001020208e3040106000c0101000100
    (by decide) ⟨86, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem nineFiveRankedRootBlock79 : (⟨[⟨3,6,true⟩,⟨5,4,true⟩,⟨17,3,false⟩],253,2⟩ : Box).Closed :=
  checkUnboundedRankedBlock_closes (.nil)
    57 873 0x3f0a2f234444442c08210a0005650131081a3805200600080101050f01db010006360109c50200056a0109c40402002a18242f131d3107180e000504a1011818091b16110600093f01060c01df0401030008430108cd040100220a0d404905240c000502c8014240162f0b3806000701c8010e0e1f1f1b1b1d07080000000c00072601ff0100062601fe0100052601066901ef04010006334549492c06200c00072901e30100060f01e204020002020007d50900061a01d4040200162a1230272f060b000701c401079902030005260198040200152c13271d0522000000003c100720080e061817000e4a01078d0401002531112004200b0007790116450b494705000802ef010c1748350e1d062408000515013f3f280b352c2c2c4a09180b00050e010a0101056901e5040100300a22350b230a000502c901161a1b250405000604a301081b051d17051200000008210f132705231100067b013e372c2c2c2c0722080006029c0112400d0b29051b0700060f01210d37172c0e1d072009000c03ed0106d3020000020206d2040200068b020a110a030701040805060c0602010e05068502030005b702071a010103010e01031005010c0505b302030010131b280d2c0e2c08234400073a01a3021a0303011005020406220d0304010e0505a1020300059b022d010402080402130d0313010c05020010454344473b0625320007019e01058902010a010305050603050107090c050587020300060e09140b17060d001f00063a01d5020e0603110e130506030901020c05020004c302040318020c0612080e010a0504c102030004a70201001542450a2f384a07203400053e0104a302010004990201002d0214410e3b062012000701b301048b02270c0201010f0409050202030c050489020300041e0626281a291a080d2000084801fb02010003f102010009311632474406231100063101e702010003e1020605020109062708100404010c0503df02030003d702010001241c181f0e202b0805002a00077301cb020204090f0101030509070b0403020e05020003c702010003bd0204020202020c02061009080c0b010603100503bb020300010f15110b111d070c3c00075e0103b1020d05021d0406020805030b0104010e05020006181339381d062000000012110d2f2f381d07182900060a0103af020104001901010e1001020202000d0101000100
    (by decide) ⟨126, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem nineFiveRankedRootBlock80 : (⟨[⟨3,6,true⟩,⟨5,4,true⟩,⟨17,2,true⟩],205,2⟩ : Box).Closed :=
  checkUnboundedRankedBlock_closes (.nil)
    63 749 0x202368f040100002e0b000601b8012eee040e020105070202050707080202010e050100020217b7040400131d000601f70113c0040200001207000603f40112ca0409040006450109a50404001006000605c20110a402000503b701000100051601d30407f10400062301e90403000f890600050d010f88040200000ec508000516010ec40407a9050005200107a20404000d06000603ae010d94040300070494010ce10406b5050005230106b00403000b910700050d010b90040200000aef0800062001ee0405bd0400062001b704040300062a01cd040100000aaf020800051d01ae0405a10201000202059704040006100208292306251600064a010a1615111d05190000000027102519292906250014000a2a0108c1020005620108c00402001c070508080823070d00050b010f0b05082c052207000d2401dd040100010525110829060b000546011207030f1c051007000c02ed01078d040100020e0f0911050b0007038c0106cd0200062d01cc0402001b2105082b1a060b000501f401131d2c03200500070101050c01b904010006050006019c0106860402000d171a2b04210b000b1701e90401000e110b1d171d06180c00060101052801db04010027272226110521000000001e010522290829071518000801d5010501000602970105a0040200020204d30900061901d20402000c140a101c1d06100c0005650104cb0200061501ca0402000400050c01bd04010004950600060c019404020004870600050c01048604020003f10700060c01f004020003ed0600060c01ec04020003e50600062001e40100082001d90401001c0b072004220a00066201cd0100066201cc04020300061701c3040100010310090f05010b00050601072701bb0401000d112a0f220b2f07220000000c0d0d1a140a1b07081900090101051b01b504010001021e2a052b1107150d00071d01af0100061d01ae0402000101130d131410111109090f00061d0103a50200060c01a404020003a1020000020203a004020f003c0101000100
    (by decide) ⟨102, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem nineFiveRankedRootBlock81 : (⟨[⟨3,6,true⟩,⟨5,7,false⟩,⟨17,2,true⟩],281,2⟩ : Box).Closed :=
  checkUnboundedRankedBlock_closes (.nil)
    47 616 0x2020012160432383e0624000d00071a01d10100061a01d00402000012080a0f1105150c00063b0107b9020000020207b8040200001825262827280b0815000503b9011e16160e1f173e3e0809000502d00108021522050b06070006018e0106010105150106d70401000202063c281a3b233e0725100008019b0105db0221020604060b020606010703010d0e0505d7020300003c10193c2035353e091800002500075101d1020523020304010d1a02030a0505cf02030000130f0e2123170b08141d00071d0105bd020100160517112f0a000601bf010a10031b0405000802a601011c0a17222335072109000601a60105810201001e28132b171a3e07200000000c153a3d041b17000801b60104eb0204020c090c0309040a02021402030e0504e902030004cd02121716020608020201040a0504cb02030004c702010004bd020e10020402060b19140601020c0504bb020a0501070a060b04040c020207020e0504000c0002011009111108016100074d0104ad0201003725303a3135340714000000210d2d1a383e062019000901e401049b020100048f020b030601021213150c010a05020004830201002a3623083e3e3e07182400091801fd02010018062b071d3e353e3e09240f00072b010003f3020100242e13213a3a2007100f00084c01e50201001e14200a1d1d2307100d00084f01df02010003d502021602100317010b010404010c0503d30203002a0a2e16322c2c3e082000000016141f1a3e05252e00083e0103c902010003c7020100363c253e0e05200000000202000003bb02010003b9020b0c0812060701070b01040302030302100503b7020336002c0101000100
    (by decide) ⟨140, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem nineFiveRankedRootBlock82 : (⟨[⟨3,6,true⟩,⟨5,6,false⟩,⟨17,2,true⟩],243,2⟩ : Box).Closed :=
  checkUnboundedRankedBlock_closes (.cons nineFiveRankedRootBlock81 (.nil))
    62 758 0x120f041603052907180900053a010dad020300050a01ac01000876010d8f0401000206000605b3010ce304010400061901c10401001e2502311a23232c081b0e00060101050f01ab01000648010b8d0200052f010b8c0402001e0811171735060c000601c1010609330f103310350909000604c601073e010a97020300050a01960402000704b4010a85020006780109ef0200062601ee0402000901262127050a00054401331d3429290525070008470109010006018601098604020400054301f50100064301f40402001824161b27281d0714000000092d06182610222b0810001b0005018e0126190d09112307100800070101050f01e301000501d9010008d30300063401d204020036071320352c3507200d00050b011d1717350524000000001b18053b3e1a06221200082601088702000526010886040200142228192105180c000501ea01281b282305190600093301f90100063301f80402000f1508081a3b0a00065901130f111d272906190000000024111d23041c1200092a0107c7020300052601c60402000108070e050b110701000000001813092222110614001a000b01ca0107af0401001c1f1d3c112c0b000c320106cf040100020230311a35230c0008190105d7020300051701d604020001331d202c23060b00064f01060901cb010007090105b70200084601fd04010001212f353e09000627011e2730171a2c3507180900071a0104e90200065401e8040200361c3c263405200b000b3201c904010300062901c30401000c1026083e2c06250c00064101031e0b39083c3d3d3b09140b00050101073001b904010004ab0600060c01aa040200049906000624019804020013201327162906100c0005060100000200050c018b04010004810600053f0104800200084b01f90100080901ef0100080901e30100083901dd0401000a160e223d343d070c00083b01d30100060c01d204020003c7020700050901c604020300060901c30401000000020203b90401000125391d0811111a2309101800060a0103b702010400390101000100
    (by decide) ⟨121, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem nineFiveRankedRootBlock83 : (⟨[⟨3,6,true⟩,⟨5,7,false⟩,⟨17,3,false⟩],283,2⟩ : Box).Closed :=
  checkUnboundedRankedBlock_closes (.nil)
    57 874 0xf4e374c51214753081d000000044e3e5c37644a6768680a180000001634423a393b0623000a01c60109af0200060d01ae04020000099f0700061a019e0402000b1325273b05240b00073701099d020300050b019c04020300076601098d0401000a06073a2f3b4507180e000503af011433333b2332351a2c0a150b00051701073801088b02000505cd01088a04020400062c01fb0401004b06575b5f3a2c4959590a0f000702c4012e5e2639530b594708250a000b06880106db04010009090205261d26192c1a0f00050380014c122c293b4f47530809000603c701063801cd020b071a080601080a0e1b14150c0506c7020300132404112329292308140000000020333823251d3b45081b2d0005770105350106b102180f102803030702120713010c0506ab0203000311521b17502b674a0920000501e7011212280229282f3211091000000d00095601e1021601063309110302070b060524020201100505dd020300180406610b0e380e680920000000331e16055e67502953091a32000532010601820105c50201001809221750443b4a59092310000801b601059d020100130c34582667296808220f00082a019502041004111e02120e02040e0607050603100505930203005a2f5b535f291f000a02e601058702191e120707070601130113010304040404011205020000383a373741310718002300097a01f5020100091802024d0b06200c00073a01dd02210a0204041602160514100e05111000067f01030c0a2e2431322929230a02000000301f315f053a385917000d018301cd020703030d070327020f1e021808090e0504cb0203002b1a45105501084d140208020c000002022800051801bf02010003013d16085f476568091b0f00093e01b70217080c0a1506010c1b080c020c1604011005020004a90201000c1e6d7b746265597d09240000004e18512405372c68081933000a01b501049b020100049302010004850201000a282e054343273b0818001a00074f01f7020100335b2e1639551a4a4a0921000000041b0526385c585908181c0008019b0103f30201001304260e29052c3d3e353e350c100000002e164958084a6807201f0005740106700103e702010003e502010003dd02010003d9020100273619500d684a3b4a680a192000081c0103d102010808040406023a010c081102020e050214002f01010002020000000600
    (by decide) ⟨141, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem nineFiveRankedRootBlock84 : (⟨[⟨3,6,true⟩,⟨5,6,false⟩,⟨17,3,false⟩],279,2⟩ : Box).Closed :=
  checkUnboundedRankedBlock_closes (.cons nineFiveRankedRootBlock83 (.nil))
    57 871 0x325194657383b072309000b4301d30401000009c30700060f01c204020002020009b10900065d01b004020000242443282647593b080e0005019d01183654645605240700070101060c01b30401000202000700052a01a1040100422220582c650a00052a010011025b532c1d2c3b080a0009019401099102000502800109900402003e362b25273b06240d000601af010b100f19392731070800055b011f0f373d41051a07000d06800108ff0401004b11375c26472c65080e000542014b33630b3b2c3b072009000b350107ff040100121b11542667624a0820000000124b255b3e5c3865081b000602ef01241826523b2c3b072109000c3c01f3040100184808295662680b00060d013f181b2547586707000504bc0100302442540d662c1d2c4a680b180e000601de010b1801d3040100333f341d583b3b07200d00060101051c01c504010001021405130f111d1d09050f00051b0106ab020000020206aa0402001f20310d295f2c4a08221600076201db02060405171c140a030a0402030c0505d702030005bf020701101b150c080f0406080203020e0505bd0203000599020601211102121203050406040a0b0e05059502210d0a04050a0504030404150c05040021363d46496206235b00067501059102450c05030b01120110020202040505051005058d0203001f4b510b3a565921000901b0010583020914141d02090704030d04020b0106011005058102030004f1020a040402060404131408101404120102100502000609404155675907200000003c1f4f1c35620618004600062501d9020406040b0b1b110b0614040c07020e0504d7020300031c38313b45061c1f0005018d0104cb02010004bd0205070d1c2004020a040201020c0504bb02060102140a0210010c0414010f040203100504b9020500156034325f3b4a0723390007019d0104b302010004a70202060204031c0420050f040808050e05020004970201000491020100048302010003f5020102031f0b190401130c08010c0503f302030049542e625811590724480008690103f102010003e502010003e10225100c04050502040c051a08020a08051005020003db02010003d502110c040a1a14040506030d04030d0401100502004b5a2a342b29650721460007480103cf021b03120a0a0112080810060101010e050214002a010106080102020200050101000100
    (by decide) ⟨139, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem nineFiveRankedRootBlock85 : (⟨[⟨3,6,true⟩,⟨5,6,false⟩,⟨17,3,false⟩],243,2⟩ : Box).Closed :=
  checkUnboundedRankedBlock_closes (.cons nineFiveRankedRootBlock84 (.nil))
    27 787 0x1308670e50470625000000185d3d1a7c20324435091b160008480114c50200060f010704b50114b70200053a0114b602000501e701063901eb04010048342027155253071a000000000f0107362240352e173b0a0c1d000901880113f3020300050b01f201000902900113ab0200067d0112cf02000501930112ce0402002b28581a2c7a470c0005029d013206213b093b1d3b080900070391010675173005112f1108220000006f5a2a766a3b227768160005028001281a290e340f1d252f27370b100000001000050580011b1e091d1e0e293b47533b0c100d000b0101060c01b501000515010609018504010300051c01108902000701ec010fdb020300050c01da01000a33010f9f0401005b255c666e5059072100000014290d2543051d1800093001eb010006300106019c01062f01c7040100030d253c1132353544444447520d0813000953010dcb0200061a01ca01000501f401050f01a90100066e010d8102000539010d80040200362549151747535108180000002d2e2f321d462c19000501e7013c244d49566165624a091d0b000902eb010c830200050d010c82040200000be90800060c01e80402000beb0600067001ea0100067001060c01d104010300096301b30401003a3a22586e5311650c00050198013763613a7b1d7a596b09180b000726015a5a24551129322c29474a0b180d00071701160937635f3e0e6b59090a000e01e1010bc50200061801c40100062601050c01ab0401000baf0600060e01ae01000501fd010b01000661010b0100066101062a01fb0401004e3d285338564a070c00071001032e1b185b0b2b3808200a0005070108018301a70100060183010a950200061c01940402006d215f5f6277357d081a0e000643010a97020300050d019604020002020600074b01830401001e2e1126372331071d0d00062b012631260f3f51090700050c0130011f4c07665f07180900061501032513280d691041081b000000020e000c470102020a9104010002020009ff0c00062701fe040200103d2b4127051b00000000010711093f051c160009140109ef020000020209ee04020b000b0101000100
    (by decide) ⟨121, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem nineFiveRankedRootBlock86 : (⟨[⟨3,6,true⟩,⟨5,6,false⟩,⟨17,3,false⟩],231,2⟩ : Box).Closed :=
  checkUnboundedRankedBlock_closes (.cons nineFiveRankedRootBlock85 (.nil))
    29 917 0x8100a30221933152c35362f0c020e000603f901101e381f4008340d275361610c0d000602bc013c4b2a422a3909442c083b0b140d000a0101070a019f04010300060197016f8f0200060197016eff0200061f01fe040200541e01960e7f7e4b7f01a709201100072d01bd0100060e01bc04020000006ead0800061f01ac040200040c210b031e1f272f270a151000073d016e8b0200050f016e8a02000601df016dfb020300052d01fa0402001a1c061114250f3727370a1510000503f4011421161b2d2f2f1f09100a000d0189016da902000a0c016aa302000a03eb015c93040100086c7046019a019b7707230000004606543b28274153081a1d00052101180120090b2c2525250904000000011e042130181d31262f3a290c041c0006230106104a11333f414f47530a0b0005110154561f181a3f1b375361610b1800000f000e049f015e8304010055747e57273b06240d000639015da502000510015da40200071001529d020005018401529c02000a01840144f504010037245a63674367686b090f00075001055e01d30401001e1c554444582c595909210f0005380106040f100b0b070100000000557c496e237b333714000501e201090a131c1d21082a2c20290b0500000021365131686506200000001b000e01c4012b0100061b012bbe02000a02fe012aff0200064a0128bf0200062301be04020024270402361c050841173847440d0d13000801850128ed0200060d01ec0402000028db0700051a0128da0403000801d4012601000701de0123b50200051c0123b404020030284309170b3b3b08180f00062b0124c5020300053f01c4040200151b283e381a5907210000000c251e13402d503b4447470b101d00061501302d1e515c366b7608200a000c7601060c01b501000a0c0124890200056801065c01a504010027141c695574475908200000001848386a2f6f2707201a000732011e130929290510000000000c0c24300d31070740342b45380d000000000110180c0c2a262d33270a022900070a010a3d0122b904010400051b0120e902030005018901e80402001e323f235143062200000e00052f01402d2c556b266b263b090a000a5d01061901e90401000021dd020800050c01dc0402000202060005430121b70401000202001ff30a000543011ff204020001064407352f061c0000001e2407203e4d50071d1900050e013f246f0d447177071c0900050101061b01020220830401000000001ecf02000002021ece04021500050101000100
    (by decide) ⟨115, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem nineFiveRankedRootBlock87 : (⟨[⟨3,6,true⟩,⟨5,5,false⟩,⟨17,2,false⟩],205,2⟩ : Box).Closed :=
  checkUnboundedRankedBlock_closes (.cons nineFiveRankedRootBlock82 (.cons nineFiveRankedRootBlock86 (.nil)))
    30 806 0x202000193e5b902000502020193e5b711000502990149f2dc0403050005410106b602000604cb0106b6fc04039bc10700060186019bbe0404001e282a360b0d1a041a383935250d0500000000200e20291e0643350f44391b0c0d26000a02f901060f01cf0401000007f9a90800060f01f901000504e20107f4970300061b01f4960200054501061a01e9b504010007a491020900050c01a49004020400077a01079aff0403cdc50700052a0103cdbf04030500051201038b0200066b01038bf403000a01950101c9e30464f5020100020264f104030010000801eb0130454e3f0f46460700061f01300119184b43464e514f29520c1000000020044a45222d52530820001c000e04d701618102000601f50160f50200062b01f404020010285042354653530825000000004824214f0f473f07201b0008410160b7020005260160b602000a01ec015e8504010010414a4f2305240c00071a0153dd0200052d0153dc040200140e151e19050b00057e01070a01d101000844014da9040100004be50800050e014be402000501cd0144f9020005360144f8040200291002031627372f47530a2111000801f401070a01eb040100000500050d01db04010000308d0700053301308c040200110a450a2317370c000501fb0103300222321a061808000b02c2012d9f02000601850128d9020005220128d804020006012145154539433a2e170b1412000901e40127a1020005250127a00402040008540126ed0401003c494d5223052200000e000501e101fd0100050f0124fc04020002020021f70a0005160121f60402000500050d01bd040100001ca307000543011ca202000843011ba10200054301051f0119cf040100240109132528061400000000091b1826323d2b0719000d550114a9020005190114a8020008580113e504010002020012fb0a00063f01fa0402000c221622323d2c0722000000001a06181425171d0710000000002d1b123118082f380815000000022c000b4f0112d1020300050a01d00402030006220112970401000e1219261b05250000000024152529041b1600080101050e01f3040100000011bf020000020211be040211000b01010002020000000600
    (by decide) ⟨102, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem nineFiveRankedRootBlock88 : (⟨[⟨3,10,false⟩,⟨5,4,true⟩,⟨17,2,true⟩],279,2⟩ : Box).Closed :=
  checkUnboundedRankedBlock_closes (.nil)
    55 907 0x50c01f3010005018101061701e30401000624070e282b06200c00060101052601d304010016100f1d040900050b010e0e0a16160518070009390108c5020000020208c40402001e2527201a1a06241400060e010a0a1511081106210800062c0114101c13091d06000a0288010705970107c5040100020224160508171a06200f00061101010c1c0a18071d1a20090a0006028501077f0106ab02020101010403010103020505030401150201120506a9020300069f020202020d090508030104030302010e05069d020300081418100f17113b000901820106850276433504783906320a36063d0c050681020300010d1708172b1107200000000001141c1905200000001b272a08110806180000003700052201bd0201000d010a1311111d071d00000013100208171a0617000527010504a90105a50201bb700101810132018003080505a102030007060c120d1a1b07101e00073a010c0313051b06100700095301ff02010004f9027f0171770a3c3b016c0309010c0504f70203000e0210041b0f11071423000702ed0104eb0202740803740103360639033406030e0504e9020300120a14181a05091f000a018901db02030204020604040109080103050402010101120504d90243383938400701ab0205030a0504d702050004c52d000501800102020407040102020303040104051205020008181c1a0f1c0615000000120d1607100e101a080a2700092701b70206020a02040704060201030a01020e050200242606160729220714001e00092001a9020100180623191a050a0005019a01120c0619080807140800093501a10204020202020408070311040301010e0502000495020100001b251019080620000000030a0602170e06082c00082d01048702010004810202020302010407040803030901020902100502000a06250619221a07100026000a019a01f502020804020201010a0102060404040302100503f30203001807061d10201f000501bb0109020d180b171911080800000c0008019801e702010003e506000b5d010100150c020e2211230808100000002716112a2905201600093201cf02093901b701ad7e36073804010a05020003cb02783b3c41350b3c3c3309383c02010101100502280009570103e302010003d702010003d502050404040402020403010902010304060102120503d30203002110190823262607232f00081401cd020100210d0d20112b06220000000202000003c902011700320101000100
    (by decide) ⟨139, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem nineFiveRankedRootBlock89 : (⟨[⟨3,9,true⟩,⟨5,4,true⟩,⟨17,2,true⟩],251,2⟩ : Box).Closed :=
  checkUnboundedRankedBlock_closes (.nil)
    61 733 0x10f3020300050a01f2010008290110ab02000701f5010e87040104000616010dd70401000c8f07000516010c8e0403000703e9010bed0401000adb0700060d01da040200000ac10700060c01c00402000aa9020700050c01a80402000205000601fc010a91040100020e0a16151d11070d000565010807090f0511060d08000559010f1117041905000e690109970401001b070b252c2306200d000602ee011a040f191d0500070199011c21042a292c062008000e3501d504010000120f090f0b06100c000501c10119091b1705050005680124030c270f1628202b09100000000e000b3e0108b702000702f20107bb0401000202270217141705250e00061c0106a5020300051a01a40402000306130a0d160519080c000f000a7d01069704010012130e10050b06140d00072301ff0100062301fe0402000400051a01b70401000d0a0e0a050b060d0c00062801059f0200050c01059e04020004fb0700061d01fa040200091515160714170808080e00083f01f50100063f01f40402000f150b2a052906200c000b4a01e70401000d0f0a17192606210000000015100a20261a1a07180008260104d70200064601d60402000c01080310110b070c00000013210819110518000000001b00071801c1040100212a2520231a06240c000c2501b304010004a70600062501a6040200140e0411170b0b07140d00073001050c019d04010004930600060c0192040200048506000501920104840402000a011914291a06240d00050601000100060901fd0100080901f10401000400056801e304010003e1027b0303310a39033c393c04010c0503df02030003d50205040806010902010102070109030101100503d3027a023f313c0601350a38043e0c0503cf023a46383d0237740308010a050600120c0d180e112b07105a00063d0103d3020000020203d204020003cb02010708010704130601020a0503c902030003c702023a027601043502017c0438043d0e0503c1020337003b0101000100
    (by decide) ⟨125, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem nineFiveRankedRootBlock90 : (⟨[⟨3,9,false⟩,⟨5,4,true⟩,⟨17,2,true⟩],229,2⟩ : Box).Closed :=
  checkUnboundedRankedBlock_closes (.cons nineFiveRankedRootBlock89 (.cons nineFiveRankedRootBlock88 (.nil)))
    29 738 0xd093216091f33330809000501820114080a0f090a270b08210a00072c017fd30200060f01d20100064c017fbd020300051801bc0402000a012822171d1117081d00001000080b01ad04010300074e017f970401007ebf0700060e01be010005019c017e01000603db017e01000b03db017be7040100090d0e352e0b0b070d000501ff010101110e06261d071009000d039a0174eb0401001d091e323b05220c000b03830163fb020006570150b7020005180150b60402000925100804220b0006570139930200050d0139920402000038fd0800060f01fc0100064a013801000604a10138ba04020400060a0136fb020008018b0132f502000a03ba012dbd0401000a0d0e0713050b07140e000636011fed0200061901ec0100063701050d01d7040100001f9b0700051e011f9a0402001b012b2326201a1a2c091810000727011def0200053a011dee02000501db01061701ff04010004060a1c1d1a0a00067e01070a01f1040100000500050d01e1040100001bb307000550011bb2040200090616282223290719000000001200071301ad04010300060a01a3040103000617011a95040100061b19210711061d0d000a520119eb02000502c90118f5020005510118f40402001e0f072608110b000501b801000d0a16050505070006510107080817110e06230000000c241d0b14142c29081c1500050d01090101050d01bb0401000011a9070005260111a802000a260110dd040100080304040f15060c000734010ead02000535010eac02000a35010dfb040100140e15160b1c05071400000000081a0a090b170b07101b000779010cab020300050c01aa040203000826010c87040100061f24021a0806200d00084d01060c01ef0401000202000700050c01d50401000abd0600060f01bc0402000202000aa50900052c010aa40402000d041b0a150515000000000f01070b292323071d190005240107190109bb020300051601ba04020007160419041d0a00090f01020209a704010600120101000100
    (by decide) ⟨114, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem nineFiveRankedRootBlock91 : (⟨[⟨3,8,true⟩,⟨5,4,true⟩,⟨17,2,true⟩],223,2⟩ : Box).Closed :=
  checkUnboundedRankedBlock_closes (.nil)
    74 758 0x4acbf020001df020204acbc0e000503930102969f0403000d141512070b0b070e000503c101100606173333062408000748016abb0200054a016aba0200084a0154a30402040601030601080604080206030e05010002022a91040300010a01040d15060c0000000018043934202e061030000902870145df020005200145de0200082c013bd10200072c012901000504cf0125ff0200050c0125fe0402001ab907000533011ab80200083f011801000804910117d304010400062c0116bd0401000500050d01df040100000f0600060c010fa00402000da107000520010da00403000703b9010cf50401000500050d01c1040100000ba307000516010ba20402000500050d019d040100000a8707000516010a860402000500050d01ef0401000009db0700050c0109da04020008eb0700061b01ea04020000021a090f150511080d0006710108ad020300052401ac040200061418041b17060b000558010e0911111b1d061c08000b02c50108910401000305191d261106210d000a4e01079d040100020207190e151c1b06140f00071b018f0100061b018e04020006070805110b170b000801f90106830200054a01068204020004122a220e11060c000c1601eb040100091f021a0805200b00060101051d01a70401000c13282c081a2c2c08180e0007220105910200054001059004020400061501ed01000501c8011b0b0414000000000800077601e704010300066d01db040100010f080b232606200c00063001cb0100060c01ca04020004b70600060c01b604020004a90600061801a8040200060113091c050a00063e01049d0200060c019c04020004950207000518019404020018101f20081106240c000b560104890401001215040f072b2007100e00050101073d01fb0100080901f50100080901e90100080901db04010300061901d9040100180e0305030b1b07100d0005060100000200050c01cd04010003cb0600060c01ca04020003c5020000020203c40402001201120a040b14081a09081b00060a0103c102010400450101000100
    (by decide) ⟨111, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem nineFiveRankedRootBlock92 : (⟨[⟨3,8,true⟩,⟨5,4,true⟩,⟨17,3,false⟩],271,2⟩ : Box).Closed :=
  checkUnboundedRankedBlock_closes (.nil)
    62 1000 0x37090e2311590624000000030a06130b1819201a09081600050101060c01a301000a5d010d8302000651010cdf02000516010cde0200081601d7040100000bbf020800050901be04020300060b01bb040103000701ab010ba30401000aed0700067b01ec04020300090c01d701000b1501bf04010300060c01bd0401000202000700054e01a9040100182b1b312705240b000518010f2419091d061c07000503d8011a131d311d062107000501d90112360b170521000000122e43341d0e0610000502dd010929010a950200054e010a94040200100a0523353806230000000014030409051c060c19000b06c20108f30401001114022028474a0c000602dc0116221b1c311327071800000b00071b01c90100061b01c804020030330a39492b490b00084f0107a3020300051901a20402000003160f05050b1d08140e000a05e401079104010024021744490e2c07200e00065401152431283b05000704890127210243480b4a0708000904d90106f1020000020206f00402000695020909030203040b021f010203010b05051005069302030002024237460e473b3b071831000502ce01066301f5020502010c02040c02010f040113030b020401120505ef02030005c70203050407080b05010c030401090204020201120505c502030005bf020f01010905020e041005030808010e0505bd0203002a1b07172911595347091d5a0008540105af020402020601050f0202010b030101060d0e07120505ab02030005990209040e0607040106011c04050b050e05059502030004073425462c29072400000000362d1b1c1f115323470919004d00094101ff02010004ef020303020f120f03010e1701010c0504eb0203001827280b0e2c1d07212300061801df0201000109150f2e05232335090c0000110007019e01d5020102020202010b0204020e0e02040b040105060402010101180504d102030004c702010004b5020b046701c7570e5113645e026404010e0504b30203000d1f05272531273131091d4a000702af0104ad020100049f0203010b0304040f030808080c0c0403021005049d020300048f02060e09071b0d0304040403020c05020004090515051611070b000000301632080e47061a4600065201048b0205110706051004041003050406010101100504890203002e3d2b410e1d06202200062c01fd02010003f90201ca631064570d60550e04016004010e0502002e180b081d1d3b4a08192400083401f102010003ed0210040804040b010601080406030702010101120503eb020300391e4f22355323355909202b00082b0103e502010003dd02010003d902010003d7027101c6035101c80e01685c0303030c050223002d0101080a0102020200070101000100
    (by decide) ⟨135, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem nineFiveRankedRootBlock93 : (⟨[⟨3,9,true⟩,⟨5,4,true⟩,⟨17,3,false⟩],259,2⟩ : Box).Closed :=
  checkUnboundedRankedBlock_closes (.nil)
    69 976 0x11d70200060d01d604020000119f0700050f01119e04020002020010db0a000501a40110da040300071601e90401000400060c01c10100051f01060901930100071f010e8b0401000500060c01e701000a57010dbd04010400060a01a7040103000724018b0401001a1b2a173817061800000003040a081a0b1d11081519000a64010c87040100000600060901ed04010300060c01b10100060c01050f01990401000202000b8109000543010b8004020400060a01fd04010300072201e70401000d2a05332d05190000001801112f3e1741071a1700060101050e01e504010000000ad108000549010ad00402001843344641294707250e000504b20127202f0e3b38060006018501103403272d0b2f071a000000030c0c0f0a19081120090817000c05b70109a10200051b0109a004020027241c19380e1d07210e00072e01e90100062e01e8040200042128341a0e2c0721000000001b070c223234551123091d000000002000071b01c10100061b01c004020015162f08143a47070c000701e10107af020300052a01ae0402002413052044492c2c080d00070197012920191109131331081c0a000b04cd01078b040100011548310b291d070d0006019c0106ab020000020206aa0402000689026302ab135205670555106206010c050685020803870b0260660401c868010a050400010a1b2119082b292c090800003e00075901d90203060308030209110101030518070405100505d702030024183c3619260e491d0920240007610105cf02010005bf0219050c12010409020301010a0e090205100505bd0203001f361c260844062527000602e20105a902050a576201cd010308600401c45907090e0505a5020300063c3105381d06210000001e051c3a1d2c061d2d000802eb01058d02010004fb0259666270560b61076464640202010e050200010104190f171c1d080924000702bf0104eb02020b070208080f06080c000501d0010603100504e902030004e10217020a0a0805061001020f1204010e0504df02030004d302050104010d02010f02030e010101020c080e0102140504d102030015152a283b2906244700061201c1020100032a1b280e3806200c000501920104b902010004a9020100049702010004950201000485020100048302010003fb02027101b764060957080564045c04050e05020003f502040808040116090407010b010a020e0503f302030003ed0203010c14130302030c020307030103021005020003e502010003e10206010501040309080705100116080702100503df020300210c0d460e440e3b4a091b018d00060a0103df020104002901010c0e01020202000b0101000100
    (by decide) ⟨129, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem nineFiveRankedRootBlock94 : (⟨[⟨3,10,false⟩,⟨5,4,true⟩,⟨17,4,false⟩],339,2⟩ : Box).Closed :=
  checkUnboundedRankedBlock_closes (.nil)
    43 890 0x4272317374606000602f50103020f2e30202c2c35090d0b000a5701df02030202020b05041a05010805060608020401120505dd020300153c31310b1d2c072524000622011b1b1e2d102208342f1123350c0c0000001e5d591d3b685f625309211c000531010c01d901d5020a5602aa066e675a0201cc045a0208010e0502000e18180e131c171d081420000702b30105c5020100151039052f3b441d3b3b0f000501dd01221f1b21131d2f071809000a018b01af0201c852085c066d025a0864046004010e0505ab020300150440491c494a2c0823000000012019302709061900000036212e3a3b2323072539000746012d40453e17442c072500000003030c1216180e28282b290b080000000717332f0e5606222400061b013c18385110225346081b0000003c2d0c460d2c0618000000180009450193020410050f020d02090905060901011000064a0102393523443806240800064b012d1e16083b2b3b072200000006453025400e49473b4a0a19180008028d01058102010004ef0201010710020403070609090b14020201100502003c021826443a2c23000801ce0124242f2b233247494a090a00063a010801cd01e5020100080408141811111708090e00061f0103121919292211112c2c0a15000000101a081b0f31273108181900055e0107019401d702010004c5025c6401d601b809086166540d04010c0504c102030004bd0209010701080708021e04050f04010e0504bb0205600e02a46d62025177510b0402030e0504b90205002a242a13272f31310819520007250104ad0201001b0b140e0f292c08232c2c0b140000001e3d0d45341d1d07201e000701cb01301e214b3a283d622909180b000b0189019b0201000499020108000501a70102482e1a4a351d3b081800000c000b7d018702010003ff02038701c6646701c90e0154040d0a05020003f902010015250d262a292908231a0a102900070101077f01e902655c725f029e01cb0c54100464010c05021300090188010101000b0101061301970201001f2a032e2e131d071c0d000556010489020100048502010001140f05111d1d07100000000202000003fd02010003f902052201020308070104050602020d0305100503f702030003f1020100032e0d140b2c06250000001817092731310624510006290103e702010003e302010003e1020e010104040b01080403030101120115100503df02032300290101000100
    (by decide) ⟨169, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem nineFiveRankedRootBlock95 : (⟨[⟨3,10,false⟩,⟨5,4,true⟩,⟨17,3,false⟩],279,2⟩ : Box).Closed :=
  checkUnboundedRankedBlock_closes (.cons nineFiveRankedRootBlock94 (.nil))
    27 798 0x12081a19141b1c1d08090005068d01041c221523060c000000181b05200b0e1a474a3b0a1816000704bc0104340c17413b060005200159604c01854e471b6b5309230c00085201093f1c1a470e470720090005058b011e0d3e293b0e1d082109000720012a36251441105307250900050383012d08024f20114156560b180b00070294012d1f132823460b472c3b0a180c000e0101060c01c90100060c01050f01b1010006019c010b970200066b01960100056b01201d0713313108180000003c03371f3111202356470a1917000639011f1f13371a29062308000502f4010f26213717230707000501d801330f464420565935090900063c0103031408291d26291a0914000c000c0293010b950200050185010b9404020002020700061601fd0401002003060731051d000000000f00070d01fb01000554010647010ae5040100100f392532471d0721000000272526170b1a1d5319000501a7010c1307050726082b2c2c0a0d0c000614011320190e2f440e072009000a029d01050f01c104010002020009b10900054d0109b0040200143541382c2c06220000000c1717272505190000000c2b554d0e05182100071d012145332917380e2c080900050c010f153d371d3b0620080009019601f5010006019601f4040200152a07291d1d2c2c080d0007019501031010442c440e2c08210a00060185011e45090a48260e07000576010c018701cb040100122d480834471d2c082000000012051b25132d061a0000000c21381a44051b2300071f01120c542b0e5523111109180000001b1543462038441d081c0000001b000d01e20107b9020300052d01b80402002d050b1a1d1d4a07220d00060f0108031a05100b1b070a0900050b010b01b001079504010015151434173b4a072300000003081a11171d0611190008430137163826442c07250000000345333e2c4144473b091a000000071205151c1c23070c22000717011b240427281610172b09080b000556010a3a01b10201140305060221050d03010502010e0506ab020300060403101c151d11170914000000481e370c332f4407182e000b0f01068f02010400080101050701020200000000000700
    (by decide) ⟨139, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem nineFiveRankedRootBlock96 : (⟨[⟨3,9,false⟩,⟨5,4,true⟩,⟨17,3,false⟩],243,2⟩ : Box).Closed :=
  checkUnboundedRankedBlock_closes (.cons nineFiveRankedRootBlock93 (.cons nineFiveRankedRootBlock95 (.nil)))
    30 884 0x2c1a0a0b2e353b081b0a000503a6010f3f3720555906000501a2011b121e1e1b2a450841472f0b0c00072a0154574819130d3c4c3d67140b1a0000001000060783010d123306142e0a38472347470d080e00050f010b0101052d01990401001a300831132731071c0d000505f301392a5a264f5f4f4f630b0a000903b301208f0200054f01208e0200054f01063401f9040100270c2c452211353508220000003c40555a3f5b2718000501d4012d2a2e0740233e0e08180a000c02f4011fbb0200050195011505a701af040100133d3e4623052300000001120416161b1d11081500000024312d16202b37232f09152600083801179b020300050c019a01000a3801178f040100023208383721372f08180000000f10310516222e232f09101d00085c0116ef020300050c01ee01000579010604f101065e010604ef019d04010006131928383b060b000501b601044b373158351107200000000320080809252d071b000000060411311f0d3e0e2c470a23000902f8010502e401a7020200050a01a60402000702f9011291020006400111d7020300050c01d601000a2501118f0401000fa10700060d01a0040200000f930700051b010f9202000b5a01e90100065a010eb90200063f01b80402000337254e0f381d4659350a1b0011000672010410093c292d467508200a000b0101061901bd040100000eb1020800050c01b001000a02b5010e8b02000661010de1020005029a010de00402003f36142340381d470821000000000b2212111d13091327091d00056501274537083b4406250800081301392a133158112023590a190b00051001117101c30100057101066501a704010001280f292927090b00057c010e30320538230600052501101814142614350700082f010c2818241305060005220110242515132f061800000019052b231b052200000000121e3d1d474407181e000b0101070d01a3010005630106019a010c8704010005000a34011a14293a29392f071c000000042d514c4d47574b4f091600076901032b5549323814263e53680b1c000e000955011e8d0200051b011e8c040200020207000544011ceb0200064e011ba10200054e011ba004020018121f231737172f081d00000009130428171711081a09101d00050d0118041a453b4406200800050101060a011691040100000000020215b904010002020014cd020000020214cc04021d00050101000100
    (by decide) ⟨121, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem nineFiveRankedRootBlock97 : (⟨[⟨3,9,false⟩,⟨5,4,true⟩,⟨17,3,false⟩],241,2⟩ : Box).Closed :=
  checkUnboundedRankedBlock_closes (.cons nineFiveRankedRootBlock96 (.nil))
    29 722 0x243234315237235e08240000000128240b68262b4766371b0b221a0005240110100002092c2217152b2d2d0c0c0e000701a5013c2f2d171b0d2937081c000b000f3901dd010005019401062d01d104010008280a09160b0d2d17090800000000380c720e0189364f1b0821001f000d2d0166b9040100245929636a134707250e00063e01481c6c2d3a1f4f462e170a200c000e01a801f1040100082015340a5353334e09230f00053a0120205b1e255a132709230a00050a010b7a01eb0100057a01066e01df040100291d50243e2e0f5e3b0d00062e01081018121c210d0d070f0a15000000001c585024060e37271319000601ac01282410032b255a262709200b000a230165c9020300051f01c80402000c241b0439262b0b2c23380b0411000601010702f501658102000a02f50163b30401006024286d1b12534708200f000612012470717513018701826e08220c000701ad01240c28563523435f7f530a200c00092d015fd10200052d015fd004020005192a4223266207230000000030081d2a0e0e534a5b09211d00090185015eef0200050f015eee020006280153b90200061901b804020054830600050d01548202000501c501b70100065d01b6040200020500070288014abb0401000410272b2b29370c00051a010f3e1d0b07411b071b0900052601122414282d2f23071809000713010942211c43341a61473b0a1a0c000560010a3d01e30100061c01e2040200000e320f24282307180d00082101d30100062101d20402001e6009075437422c382c0a181000050101051e01a30100061e01a20402000810080d091013070d000000021100051c0153970200060d01960402000053870700052e015386040200050006450152d70401040008230151cd04010400051a014f8502000530014ec302000518014ec204020002020700061601c304010046f9020700050a01f8040200000000020246c1040100000000408102000002024080040200001e00
    (by decide) ⟨120, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem nineFiveRankedRootBlock98 : (⟨[⟨3,9,false⟩,⟨5,4,true⟩,⟨17,3,false⟩],233,2⟩ : Box).Closed :=
  checkUnboundedRankedBlock_closes (.cons nineFiveRankedRootBlock97 (.nil))
    31 655 0x80439592d526a163709200b0007018d01be8d0200061b01be8c040200020600083f01f504010001bdf10700072701f001000501d101083201d904010300071901e10401000001bdcb0800074b01ca04020300070f01c5040103000601a001063201af040100242c4c01917276371f08210000002d3c10124c0428630a526429470d0d21000801ec01bd9f0200070f019e0402000001bd070007048101bd8804020001482167085340432f2f0a1d1100073001bcf5020300060d01f401000b4b01bcdd0401003663546f2b255e2b5947712f470d18140007018d01bbad0200071b01ac01000601ce01060e019504010001bb830700067201bb82040204000a1b01eb0401000520341c2a0312475709220000001200095601f304010300084b01d904010027451b2b2335460723000000003c131b4002234718000502ad013c0f0f243c083911290e0e0b1c000e000b018e01bacb020300060c01ca040200000500070a01af010008018d01ba890200051a0101b9e10300061b01b9e0040300071e01b89f04010400054d01b7f70200064d01b7f604020400096f01b2d30401000c250d453f4a5f1b0183091000066d011a201b252b1733080800000000543c61155b271767082217000a650101a78b030006019601a78a04020400071701a6e904010400070d01df04010300093f01a4bf020005018f0107018201f90401000c2c3d3d626d474f08200e000530011818301b091a28491d56562c5e0e0c000011000e2701cb040100425a444d1429062500000000180c49645c28530721001a000c290186b5040100018589020900051b018588040200091001112f281a47081c0f00050101060e010184f304010002070005190102026fc304010002020059a7020000020259a60402000000001900
    (by decide) ⟨116, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem nineFiveRankedRootBlock99 : (⟨[⟨3,8,true⟩,⟨5,7,false⟩,⟨17,2,true⟩],283,2⟩ : Box).Closed :=
  checkUnboundedRankedBlock_closes (.nil)
    58 957 0x52801b1040100130e110b2f052100000015301325202017071417000941010c930200050c010c920402000ab3020800050a01b2040203000626010a9d040100020218180f0b21230d0006018f013010221a3223062308000b6b010891040100071c262035324407200000000d191b31310517000803c1010116161146050006039201091813221d1a1d07080005029e012001211d05120600071e010f1645312344062508000604840137284d2f234d50082400000b000f2701fb040100181e1c221d2d0a000504c501002d48021a5047061a090007010107058d0107d304010006e3021304020607020e1401030c010c0506df02020a080403020308030c11030802020202011205040002080d10100f0b11080c0000001f423740113b061b44000902830106bd020201040217020a18100103090c0506bb021104080a02020402060b05020a090809100506b7020304030508010506050e0506050808043900052801001e154046233b062209000701b301068502010303050e0604070112020b040403010401120506810203001e0403141d3306102400082a01fd020301020c04170c020a03100104010e0505f90203001b254933292329350810002200084a01e90202025c04655d01015e010402a10c0505e702030005d102020101bf010201590704590703810c0505cf0203002a213a2332353400053601061e2740372c4a07180900086f01b30201003f49494a3b4d06230c000538010513019f0201000f0f2f3a232306200c000746018b02020a0206040e10090602080705010e05020001012d052f05141b00061e012415062f050e4d1a1a2c350b140000000d1e170f2229061918000501eb01071a01058102010004f102010015151033463d2c071c1300087a01dd02026757045c0b01bd015e01b907050c0504d902030004d30204110a032303070404050a0504d102030004c302015b010a5a02590b01b50501c26004010e0504c102030004b1020201010207010402010507012e030803100504ad020300022c2017281706140000002d130b3d262c06187200082501ad0201002403250b314329293d1a2c0b100000001e041f151c2e2d07101d0007019c01049d02010004990201000491020100240a21313a084644230914000000243f493a50052100002600074501048b020c0501060d0802031214030401010e050489020300048302010003f9020f020e03090604110b01040403020e0503f70203002d0b261138412c07240000000202000003f302010003f102010003ed025c645c0b5d02015f0155086355050601100503eb02036800380101000100
    (by decide) ⟨141, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem nineFiveRankedRootBlock100 : (⟨[⟨3,8,true⟩,⟨5,6,false⟩,⟨17,2,true⟩],279,2⟩ : Box).Closed :=
  checkUnboundedRankedBlock_closes (.cons nineFiveRankedRootBlock99 (.nil))
    64 761 0xc181e2231323d3e08100000000e06052935051814000604b0010a3701f304010002020600060a01d10100090a01d704010300071701b704010036372e202f201a07100d000901cf010c97040100000bfb08000545010bfa0402001b010b25233b3b0c000702b3011d2011292c0623000000001a091c09051b1707131400057e01142005212906140700070101050287018d01000538010a8c04020002021e100b2817211d0715000000001324192222232707141d0005350113101d20230606000901fa0108870200056e010886040200212514113e2c2c07230000001e27163c2f1a06191900050e01010a2010222327070007390124183919333d17343b0a0a000b019b01052901f10401000713132515111d0b00060d01121a140f26232307080008720107cb020005019f0107ca0402000c030f0e21221d0710000000040f080511051700064c01092822272329061c08000c4101db0401001207331d3b3e0620000000063c073311320616000601dc011b071019342f230708000527010a0a161d173b293b081000000c000b610106b5040100131c343d3b05200c000b4b01ff0401001e1f0529040900081901f70100061901f60402000d2a140e3805210b00061c0105e5020300051a01e40402001e271c1938050e2b08110e00050101072b01cb0100080901ad04010300061901990401000f16262323113b07230d00050601066801058704010004fd0700060c01fc04020004ed0600061b01ec0402000d0111272923232908180e00061801d90100061801d8040200242125343d0900083501d10100063501d00402000306070b17080e1717111a0b0811000c5701bf040100180207202905200b0005400104ad0200061e01ac0100081e01a90401030006150199040100049702070005090196040203000618018d040100130621282a2006150c0006010105090104870200080901ff0401000400050c01f504010003f10600060c01f004020003ef0600061b01ee0402001b1e391929083b07100d0006110103eb020000020203ea04020b003b0101000100
    (by decide) ⟨139, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem nineFiveRankedRootBlock101 : (⟨[⟨3,9,true⟩,⟨5,7,false⟩,⟨17,2,true⟩],283,2⟩ : Box).Closed :=
  checkUnboundedRankedBlock_closes (.nil)
    62 953 0x2020d8b040100000ce90c00050c010ce80402000af10700060f01f00100050f01000adb03000572010ada04020002020416161d3d1a0d00074501013f05312935440720090007029901140e31344f0506000b7001053901b7040100120a1c111d2f271d0815000000000a16051d17294419000601cd01362d3040433e062008000a3a0108a1020005018e0108a00402000c120e28211d230c000806b201012f43412944062008000513011c0d14203b2c0725080007010105090107f50401000500055001fd0401000639133c2b462c0b000564011e0d1e22221c2e2c08100000000c2c2423380513000803a9011e1f192c28170610080005058c01202c211d2f061b0000000a00071b01d5020000020206d404020013052a37464435072114000714019b0201000a130a2a11354107200d00064b010691020100201f3131333535071d0e00052601053701fd0212050202190f1102040406090c0505f9020300102e32414405201c000601ce012d1c3f2141453b3e44090005048101072401e30203040404081211050f0608030c0505dd0203000f0d1041174706241d0006750105c302045c6002a0020461045501c304050c05020005ad02025c015f055b0265605e0202a50c0505ab020300059b2e0005029401015b0401c25e6304605c5b040610050200058f02010606020403050602020802011501010704020204051605058d02030030210733412f4d3e4709193c00097501fd020100080c021a1b1d2d07140000000c2a251a262f061418000712012d373c2b3b413e3e4709180b00052b01054101e90202035b02026501b701c704605b015a020813000502b201091633402b444407240900084401df02010013053f2e3b474d4747091a001000085401cf02030101030103010103020c01031408030d0a0201140504cb0203002d3c20473e0522240008019801bb020301050d01030702030a060c04190e0504b9020300091c0e3845233e07102000085001b70202025c045c045c60600204055c045b5a6303010202011605020004a70204020204060604010b0f06050108040802031205020000191a262e1d06100000002406392f3e3e0618480007019a0104a302010004990201000493020100070108162b112217081800086f01048b020a0e17050905010e02010a05048902030004810201000a1e24313a291a464609102400064f0103fd02010003f902081004020103061601040b01040602011005020003f50201846a0c01a901e60c603a26461a010c0503f30203001407152821112d07100000000202000003e7020149003a0101000100
    (by decide) ⟨141, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem nineFiveRankedRootBlock102 : (⟨[⟨3,9,true⟩,⟨5,6,false⟩,⟨17,2,true⟩],273,2⟩ : Box).Closed :=
  checkUnboundedRankedBlock_closes (.cons nineFiveRankedRootBlock101 (.nil))
    66 778 0x480f301f172b3e5909100b000831010f830200053b010f8204020400072301dd0401000e191d2133050a000501f30120101f052331060700086e01050e01d30100050185010eb10200051a010eb00402000c253c0e2950062100000f000501bf01d50100061701d40100091701af040100000db7020800050a01b60402000702f8010d910401000cef020800051801ee040200152a1e22143a2c0b000c038e010ccd0401002d0a1633211a293508100000001200070a01dd04010300061a010ac70401000202271617141a2c2c0e00082101052501ab0401001e0e3203240000000009141f20111a3507251600072a01080100065f010894040200031c151d1d2329071c000000000d0f060e16221423080c001d000902c50107eb0200051a0107ea0402000d07180e322306200d00063e0106f50200060c01f404020006cd0600060c01cc04020006950600060c019404020006050006019401068a04020012191a281c11060c000c3e01f70401000601370b2f2306200c00063e01dd0100063e01dc040200190d190a252727270c00050385010907070522232307000601d101073301bd04010006090b0f11050c0b0006570105a90200062601a804020018180b1937081a2308200e000701b701050c0195040100058b0600053a01058a04020400062501f90401001c1e0f07102c2c2c0820000000031e2d3c3c382307181a000b4001e504010004dd0600061a01dc040200180636081d3b2307250d00051b0104cb0200066c01ca0402003627142031223e3d0814000f000b2401b704010004391a2b1a1a2c072100000015021a0a161d110710000000001d00071901b3040100141905210b0b1707150d00063c01060901a30401000400050c019f04010004970600060c019604020004910600061f01900402001b13151033103d1a3d09100f00051f0100000004890500050c01048804020003ff0700064601fe04020300062101f9040100010915232929061a0000000b1920082305181600060101051c01f7040100011530200e33353e08150e0006110103f3020000020203f204020b003d0101000100
    (by decide) ⟨136, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem nineFiveRankedRootBlock103 : (⟨[⟨3,10,false⟩,⟨5,6,true⟩,⟨17,2,true⟩],351,2⟩ : Box).Closed :=
  checkUnboundedRankedBlock_closes (.nil)
    45 928 0x131627142b3b0621000000000a0106213220223408100017000b01b201fd02064e024e02055102d34f05045004550e0505f90203000f1f371d3d202307222100065101022711271d2329071c00000016070e26111a3835081c16000a6b01e30204041b0108030a020804050302030e0505dd0203000a210a3c2f3e3d0724000000362e05020e35062a000c7701c3020d0402020402060b02040a1410011000054e011c012f3a1d3d291109100000002515053311350614000601fd01064201af025250045701a15b010301a801a004050c0505ab020300059b0204040404060a02010103081e02050e0502002410142322352c35081b37000501e901052501058f0204021201030302030205180202010e05058d0203000a1f1d331d3d061f00060283011e2a141438113b3b081a0000000d000a02a201ff02010018041a1d281706100000001c1716221b051d000000000f2510312c061b2100061901360f0f2e320523000000041820382b3823071a13000901ad01e90201b30c4b5f30497801840190190a05020004e102070902020604011701010f0602010e0504df0203001519251a3505223200087301cf020204505004505401535402045949074c0c4e0601140504cb02030000140b04151128071026000802e301bb024a040283490301075004019e065006030e0504b902030021393b1a1a1a062300000015033c1020112c072c00084001101d3d313e2c07250800093201b902010004a702010004a502505801a00303a107044d010256030c05020000130d012328203b081800002a00080183019b01000801d201048d0254520201a60101a50b4a090150030101f103091600057601830201002d022d1d32111a1a080d000601b2010801e101fb0201001b0621040b21343e350d000901c601f702010003e90201080014028f01131c2e2b3535353e0818000b00074a01b7020402020404080804010a0e0d050201021005020004a702025301500450545401a8095204504d0b01100502001a042615171d293500050c0115130f1428343d07180900064e0104a3020100049902010004950201000f0d131429083e072000000002020000048b02015401024d0402cc0b495e014f01590e05048902030004810201000104042a3c1a1a11230910480006580103fd02010003f9025301044c54545f5454490301074906054c0602011405020003f502019d04074901a804505804034b01af02010e0503f302030003e902060401010e1501010107050b04090e0503e7020352002a0101000100
    (by decide) ⟨175, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem nineFiveRankedRootBlock104 : (⟨[⟨3,10,false⟩,⟨5,7,false⟩,⟨17,2,true⟩],351,2⟩ : Box).Closed :=
  checkUnboundedRankedBlock_closes (.nil)
    47 887 0x181a032f171d2f0708000904f0010683020502020404040406060b1403020a0104010502011405068102030000180b2b4c35062000002800094301e902040808070a0e0b0104010b0107020201100505e702303c1601f26c3a01cf6c0b620a0505e30205000c0142024e4a381a4409103500085301065501c9022422623c3001e503af4924010a0505c50203000f36213d2f41441c0009510105b30201000136180e233506210d0006130109000103140445082c232c0b140d000953010752019f02010005213a3b44050a00070f0118063117412c23072009000801f10105930201000f012529112c2c0c000805980124252b454f2f41353547470b0c000602dc0109028501058302090e02060a0e05050b020d0a0c05058102030004ed026177020a0e186001cc01b4173d0c48602203100504eb020501030c040403020601020726080401100504001616262e2f1d232f081b4e00065701043145214a34344f0815000b000b1901e50201001b03364540233d46081500000011000802b801d302015f5c02026203e15e065c010102010e0504d10203000c0b023446293d2c0821000702da0103241536383438463d4f0a0005039c0108400104bf0204605c045c0402a063645c045707030e05020004bd02595c0602580b01c05b6502940c010c0504bb0203000004261f292b354f0837000602d9010701b501ab01000601d5010100049f020901020a020204040305041708020e051005049d02030004991e000601e2010100048504000552010718221615111707150000003f05021d2046061814000530010802930103f9025c055b03806008025d5c04015f045b01020201120502003918313143463e0725000025001d02930112182d073823113e082000000006183c49342c50071a16000701af0104bb0204010201010101010202040b010802150c0404040302160504b902030004a902010004a70204600557025f080297090201bc5c08610e05020007240920271c1d07144500077801049d0201000497020100048f020d01010204030201020402060503010308041d06080116050200048302010003ff021701fe01d8456d1a3c02a1080503fd0203000924010b3c41294447230a104d00062401071e1f2b2d2e3207100900073a0103fd020100001b4017113b3b072000001000061a01f702010030192811352c354747091d0000000202000202000003eb02011d002a0101000100
    (by decide) ⟨175, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem nineFiveRankedRootBlock105 : (⟨[⟨3,10,false⟩,⟨5,7,false⟩,⟨17,2,true⟩],281,2⟩ : Box).Closed :=
  checkUnboundedRankedBlock_closes (.cons nineFiveRankedRootBlock104 (.nil))
    29 772 0xe0816051127061508000865010e8502000529010e8404020000313d234123350c000502b001000313164e324d0625090009018e01f90100060f01f80402000502c0010dd10200062e01d00402000612181f272e2e350c0008019a0114161e2115292f071d0900052401055101b70100065101b60402000624221934234f0b00055c01000100084301ab04010001052e3829050a00057401000f1711262c07140800060e0101422b576258061d08000b68010d93020300050b019204020300075d010d87040100041b4b053d4144070d000803dd010c02081c2c291d330809000901ea010309282627342f0700057601241a26092e1b373908000502b001030f30304a054d3d23090a00070280010c01bd010b870200062c010af10200052c010af004020002021824160e461a3e072110000e5401d104010002020008c50900062101c4040200100d162d312f3507180d00052a010801a501b9020200052401b804020019142c1d281706190000000f2533332f05231600050801093d01ad04010015251738112c4407220d00060f01181604282f1a2c07210900060f010e301a1c251b3407100900094501083901088104010008030e171c282e0c000538010c12101b2c33352c08140000000e161f17172e0618000000181516160b17061020000c01ce010808221d16222307000501ea0107482a233d443e4708180a000b028f010787020000020207860402001812140744343d44082200000002301c2827051c200005530106018601dd020102040503090306010107050506060211070401140506db02025c60025e62630657696001c10c0506d902010803050402020215060601071802031005060015074e3b3b05204800083101131c02142043292c294d440b0c00050d0124052b312d3134081000000004120321233a2d07150000001800063c01073b01a102246a01a94a01a70d02930148180b620c05069d0203000a0d05111b2f290710000000150c33311d354a3e44091500000002023400061f010697020b4a018201910d01b36d451b02940c010c05069302031900120101000100
    (by decide) ⟨140, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem nineFiveRankedRootBlock106 : (⟨[⟨3,10,false⟩,⟨5,6,false⟩,⟨17,2,true⟩],273,2⟩ : Box).Closed :=
  checkUnboundedRankedBlock_closes (.cons nineFiveRankedRootBlock105 (.cons nineFiveRankedRootBlock103 (.nil)))
    31 725 0x18313941233e4707000806a201120a042c35171d0700051e01020100050281010f02310b0e20320722000000011a140537373a071115000718012c15410e1b5b6a5377770a0b000602f3010c0101095e01bb0401002a4c2b445305250b000876010fad0200060c01ac0402000f950600060e019404020000000f870209000529018604020000060e02071e1f07100d000702970115012e1134061c07000508010830010f8904010400072601fb0401000ee5020700051a01e404020018062137081908071a0d000c0191010ed704010018193405113d2323082200000000121224171b272807101c00084101d90100060f01d8040203000502ca01b30100063201b2040200150a0d0a0e29322935090e00053a0129342c21221f17082009000e01ab010d8f02000542010d8e04020008051a090705140000000c2a221f232f3d071818000e01d7010ceb0401000201070a201c1b1108140f000652010af30200060f01f20100050f01000add0300055b010adc04020002020c1b282e29382307211000063501082025222329060006180101081b031723060006730109272a2a383a0600080192010e200a1a1b1c2907100900052e010a540108b9020300055101b80402000210170b2523290718000000121e0d291105160009028c012733200e23382307250000000f0714263e051a130008100120040b1f1b11071008000e01af0108a10401000c1c021028382307200e000601af010d1e0426111d0610000900073901f7020000020207f604020a00067c01fd040100061c13263d383e0b00052401241b241111050600050b01243610373e06180700061a01071b100708203d0721000000151324142e3a061d1400082e010c0d3617352c0620000000091530141f20383e3b09101600061001161e34233d23353e08200a000c010105130106d50401002d362717111a2c07240e000916019b0201000f15021d23352c07230000000202000000069102011900160101000100
    (by decide) ⟨136, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem nineFiveRankedRootBlock107 : (⟨[⟨3,10,false⟩,⟨5,6,false⟩,⟨17,2,true⟩],253,2⟩ : Box).Closed :=
  checkUnboundedRankedBlock_closes (.cons nineFiveRankedRootBlock106 (.nil))
    33 745 0x62a19083737230700064c01040a2a25253a21400800054c010d553133657f0620000000133f02270b1f2b1a534f0a141700083601072a0123cb020300052801ca04020024200a1b23292f070c00050e01180419311d252d1d0809000802fe01060c01c101000a05c10123a70200064f0122ff0200062901fe0402002501574a592c3507210d00050c01030536272e061407000801a90122dd0200060e01dc0100050e0122b5020005180122b40402000500050f01d1010006680121bb0200050e0121ba0200051d0120010006018a0120f602000625011efb02000516011efa040300071901a3040100001997020800050c019601000a01ec0119810401002404333d2c6206210d00050801092501ef0100053001071801db0401000e1014141b251707150000001000070b01189b02000903ce0117f702000603ce0116f702000501870116f60402001a1a2216232f33070d00073b010a041c4344573535082500000002030f1333353307100000002d1507214c1a503e081023000701d3013f2439172e463e3d590a1000000d00064001002d27242e391d3b4446090b000702cc010c3c123d156f1d4d4747470b100d00090101082701e10100062701e00100064f01051b01d30401000f2d423c4d470620000d00071a01bd0100061a01bc04020009242632313a060b000701d10113950200050e011394040200000012ff0900067e01fe0100067e01057201af0401003f3039104b1a5007240000000c1924254555591700057501181b393c0b4a4a35081a0a000731010c03481f3a353b23475f0a180c0006018d0111002a230180527d6f0900050d0119293e225a7b725b08210a000a01010a4801bd0100060f01bc04020002020012b10900063901b00402002d1b2d1c403b350b00061b01060830250f2333170810000000002402041108294f0720001800084201129d0200000202129c0402000e1207251b1106101400050601070b01f9040100000500060c01e50401000202000000020211a104010f00070101000100
    (by decide) ⟨126, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem nineFiveRankedRootBlock108 : (⟨[⟨3,9,false⟩,⟨5,6,false⟩,⟨17,2,true⟩],239,2⟩ : Box).Closed :=
  checkUnboundedRankedBlock_closes (.cons nineFiveRankedRootBlock102 (.cons nineFiveRankedRootBlock107 (.nil)))
    30 797 0xa03d30109c3f10404e1ff020100020204e1f804030018182a0d2e092d1d40091c00057701493d7c46627f7b5309200000001b1233401f633a4f3b440a15000000001d00082a01052e019504010004071c1b2335292f080d00070f011e1f320f293e3f071009000901cd013e8d0200054d013e8c040200081419090d2232230d00062a0124031b1c202e280710000000280d481f2d232b6308251600061001400b42282c344646080900053d011539010130294443553d4f081500000008421522153b460715000000272d273a19233e5f230923000a01d9013df30200060e01f20100050195013dd9020300050c01d801000a04d8013d8b02000633013c910200055f013c900402002448371a52503e07200e00063201070a01c301000802d2013bab0401000206000745013ab702000502bb012007091f031d071408000701860125494c220b4b3b0720090008500138b50200060d01b404020000389f0700056901389e02000802bc0137dd04010018490a21030b4b3f082000000004041c0e05201a1a23091c1d00050d010a280c2b073506100009000c4201a301000a420130f3040100003f2d02233e59062300001000062a0136e9020300051901e80402001438392e5d4f5f07210d000b7e0136d3040104000802cf0135f10401000032ab0800050f0132aa0200067c012dd70200056d012dd6040200141a0b332f2f2f07180000001002191e151f2d071000000018271e103a354f4d0819270006200148494955226a6b476b09100b000519010024151902533b4a07120a00090101060a01218704010400063c0120e3040100001fb70800050f011fb602000601ba011dd102000516011dd00403000601ae0118810401000017ef020900050a01ee01000835011791020006350116990200051c0116980402000927162e2f4647070d0008410112f9020300050a01f8040200040005620112bd04010002020011f30a00062801f20402002d16251a3b2c470721000000000942341a4c3506201900081f01e10100061f01e00402000c483d1e2d214c4a230b0a101000071e0111ad020000020211ac0402000202000000020210eb040117000c0101000100
    (by decide) ⟨119, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem nineFiveRankedRootBlock109 : (⟨[⟨3,8,true⟩,⟨5,6,true⟩,⟨17,4,false⟩],295,2⟩ : Box).Closed :=
  checkUnboundedRankedBlock_closes (.nil)
    63 956 0x242d1c31760b7159357a0a1b0c00050101070a01f5040100000500054f01e10401002440282b5c38595908210e000601a50107010a09212117232909140b000501a1011e16272911290710000000003c2129402f7d597d7d092017000c7d010a9702000538010a960402003c254f573b62620c000701bd010f4e234047383b0700060197014214480b53650624080009420109f5020300054001f4040200013f232f0b5653680c0006018501300a5d262c682c4a0825000000002d6a018a321326296853091d1a000903b4010a450109b70401000119363927273b070d000501ca0113044e760b717d6b59091c0b000905ea0108910200055a0108900402003f15074d502c6807210e000b1901d90401001e5152284167593b080d00064101050901078d0401000500052001ff04010027096d192955356b7d590a181000096001e70100061b01e6040200014540572659560b00091b01c5020000020206c4040200005a5a3e35646507201400072a019b0201001515401b664656673b090e0007019201062e140e4756563b59590a1b0c00085601068102010005e90202040a040d1003130b09101403020e0505e70202040e0405070b0801050e04080414040c040203140505e30205005a2e392a5c3a1d1d65680a1800000003273a224d77740721000000005200057401db020a061a13010701070202240414010e0505d7020300153c3d4f4d3567651f000a3001c502010005ad021601010543130c0d0106030204020201100505ab02030009245b20283a2c4a0820280007190105a1020100120b3921073d08232c2c3e0b140000000216000502e101058b0207180c1402050c0215050c0304010301040301011405058702030004f302010004ef020207030602090733082601020c0504eb02030004db020d03081c050e02041404080804090101100504d9020201890308017f0f7d0c0192029001910401840405100504d70205002d15400b5f5c470720000000366c332b64356a7a08180183000701da0104d70201001819286144654a07220e00082e01cb02010004c502051e0111030414110c02040606060201100504c10203003c1f451d586806250000000202000004bb02010609070f05080404040801070d060e0219120504b902030004af02060403100f3c110503050a010c0504ad02030004a902010004a502041031070103080f08040c0202020102100504a302030004a1021908070d080a020204173a010c05049d02030004910201000487020100048302010003fb0202010204040c0403090410040c17050e060b020314050201bd003d0101000100
    (by decide) ⟨147, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem nineFiveRankedRootBlock110 : (⟨[⟨3,8,true⟩,⟨5,7,false⟩,⟨17,4,false⟩],333,2⟩ : Box).Closed :=
  checkUnboundedRankedBlock_closes (.nil)
    56 952 0x212e192a4175737708000502d301244c160181533801850185081800000048191b3f1f594f071a00000022344a47411106230009048a01081b01e3040100123c27445576744a08220e00082a01053001950401005a1f346a26743b0b00073001141f53543b573b4f59091b0b000501e40106350107890200053c010788040200213c2257716877590d000503eb01004b2a61734765062300000000401f04333b4d3e07150005028c010a3d01ef020000020206ee04020006cb020303040d05041528080b050710110401100506c7020300150425073b4a464d3e3e3e470c1033000901cb0106a302060102040d01020410020d0104100410020c01040609011404011a05069d02030006870205061004060a100225010b0805070404060509011405068502020410040c010507050d081d030406220203120504002125084d6b295974082160000801a501ef02010015052e555131574f081a0e0005018f01054d01df02020e01900401aa05018f050903018d04070404019401ac190007018e01dd02030015120614161719292b2332230c050000003f2e2e4e414419202347500b1500002400097a01cb020504060a02020c06220f04070d1001030a020405140502003c09366c52704a07212300075001b1020100124f0a436d712c7408240e0007680105a50201a1019f040c01900702019702090197050804019c0401a001980603140505a10203003f095756733b01836877091832000801c601058f02147801a01401b502970287123b293c3d51290e05058d0203005a251b6a5f5f4a3b59092600091b01f702010004f30201003f024c0a41355371082013000801e801df02010004db02100f030217290b100202020e02030e0504d90206010203010e02140807010d04030d1628020102140504d702050001026a435e352c7159680a1941000a6901cf02040304050b0907140408110a0a060401030408080f021605020015060f0f434a353e473e3e0b15002a000a01b701c902010004bf020904040408040d030c010327121504070605120504bb020300131c163934443b3e3509142b000a1901b10201004b106c26386859596809180f00051d01056901ab02010004a902010015103d48296b657408211300077c0104a302010004930201003c51114c0b0b7465597768770c19000000272a08302f22626808200000003f5b412c7a01837d072032000713010f054d574669535f6b530a210c00093b01048b020d0b0503080510090a140507032904011005048902030004850201003f2337612c7406230000000202000003fd02013200340101000100
    (by decide) ⟨166, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem nineFiveRankedRootBlock111 : (⟨[⟨3,8,true⟩,⟨5,6,false⟩,⟨17,3,false⟩],279,2⟩ : Box).Closed :=
  checkUnboundedRankedBlock_closes (.cons nineFiveRankedRootBlock109 (.cons nineFiveRankedRootBlock110 (.nil)))
    24 841 0x13b30200050f0113b20200060f0112ef02000605d601ee01000503a20106018301a7040100125d602317674a68080d0007048201322c4a472d2f273159590a0b000601a601257e2952019a6b7a08210000002854462b1c4f45275909180000001e221c6a23627d0186081b26000727011909440b597d06200000000f03031e3f393916670b53533b5f0e111b001101a2010504c7019f040103000504d401e501000604d401e40402000818423a55051d0b00060e01040b1f19564b061c080006460118241b3d4e5c6a6508000536013420203e3a41061808000501010b04b601dd0100054d010704a901a50401001e0c2235514b594f080d000702fd014b39426d171d2f536b091900000000741a3059357c5f0817000602f1010e01de010e9d02000b04d801f7040100273c5e15415f6b6b08180000004b191d01960e797d7d01a101a10a222000051101010a183943203b323e470a100c00091e010b8b02000525010b8a0402000c1a0f49374d55071d0e000c7701f50401000abb0600060f01ba01000602c1010aa90200063401a80402001220322c1d232f07100d000614010309031b0a0b270e2b1a23340c010e000b77010a9702030005280196040200481c314b152d061d0000001e4b463556747471081d001a000d019e010a8504010069216341504a593b7409201000062d010607224f176b566508090005019c013c095d35321d564a08210a00066a011628231d292f2f09140900053101084f0109c7020005780109c60402001222310875261a6759590a200000000b282625414558071c000801f30118523e4e3727314f59091a0b00082a01031c1c0b312f23081409000d1101089b040104000901010801df016c192d4f5277440720090006450112f50200060d01f40402000012b50700050f0112b404020002020011f10a00063301f00402002419084a0e466b0b00055f012d180b073722323e2309140b00060101050d01e90401000011b10700061e01b0040200031b2d33573b74326509180f0007480111ab0200050e0111aa040200000010f5020000020210f4040200132a284d5f2056072000000030423d05295c503b684a0a18002c0006280106162c50592306210800050101060c01fb04010300060d0102020dd70401000002020a00050101000100
    (by decide) ⟨139, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem nineFiveRankedRootBlock112 : (⟨[⟨3,8,true⟩,⟨5,6,false⟩,⟨17,3,false⟩],259,2⟩ : Box).Closed :=
  checkUnboundedRankedBlock_closes (.cons nineFiveRankedRootBlock111 (.nil))
    30 711 0x32a5020300053401a40402001d117a018901b652018701db082212000601fe01030931071f5c018377147a680b190e000801010609019301000704a101328902000502b40131f9020300050c01f801000a01e60131a50200065c012e8302000625010502a8010d043c09360a073649142c2f232f0f0400001200071b01bf0100061b01be0402003c02116e577b5f0b000801cc012ea70200051c012ea6020005018b010671012bb3020006018a0128990200056f0128980402005414033769232f4f47091c000000304830480860484858700d58691f7f590f018f132e14082a000d01f501601a253f6145235d08000601a7017e494d223e32536b081c0a000601be0102020200060101061901b70401000020ad020800050c01ac01000a01d8012089020005028c01062801d30401004b2a280b787a2347080d000501cb01135d1c21744747072400000b000a02a4011ee302000501e4011dbd0200067b01bc0100077b01830100067b0182040200181b22634d2f69690818000000321e0b2929274d4508191b000511011c6064524b69374f3b530a0b000602ac010125130a1e2c086b595f5f6b530d100f00054101001809380c0c213c1f272f0a140d000a01010801a0011d850200050f011d840200060f011ce902000535011ce80200066401052901d50401005a5b4e6e7b326b0722000000000602491f5f747d07201a00075b011be30200052f011be204020400074c011ad90401040008750119c10401000500050f01af0100066c01169f0200050f01169e020006510115c70200064201c60402003763730b4479593508240e00050101063501cd0100055c0114fb0200063601fa040200081935290b3b06250c0007370115c9020300050c01c80402000202060005270115b904010002020014e70a00062701e60402001a03204c394d4d07180d00060101050f01ed04010000000014a1020000020214a004021200070101000100
    (by decide) ⟨129, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem nineFiveRankedRootBlock113 : (⟨[⟨3,9,true⟩,⟨5,6,true⟩,⟨17,3,false⟩],283,2⟩ : Box).Closed :=
  checkUnboundedRankedBlock_closes (.nil)
    69 1025 0x6c054d415059233508000701d00113a9020005230113a804020400072401e5040100341d334e5223060b000601ad0112df020300050b01de04020300076b01129f0401000500050d01ef040100000ec707000516010ec60402000500050d01bb040100000ba50700050c010ba40402000ae70700060d01e6040200000ad3020800050901d204020300061d01bf0401000e2b482f3f2937375309200f000d07c1010aad0401001f100a3435595907200e0007450109eb0200051c0109ea040200332d16222b35672c0d000801940108b7020005530108b60402000606250d6653624a0820000000305d3e140b623b071c1b000702cc0110231c3945313b4545091d0b000b3501fb040100070a0f091011171d080d0e00061c0107ab0200062501aa0402002a2c303f3f413b0b000901d701050c019b04010007810600051c0107800402000f600b525c29674a08230f00072f01dd020000020206dc0402003327605f3b49470723000000001b4807294611444759597d0b1b25000905930106b102022664167614537728018d018b0299252b01c603100506ab02030006950203020f040110020a170408080103141002031205069302030005fd02018a7f02020802930185130188047b110188040184060201120505f902090182110189029d79019b0201830193018c0202010e05040022323e410743453b08187d00075a01ed020504020a020101040c02120d1208080804021003140505e7020300122754464d472c4a082127000702dd0105d70201001e43193456654a07240e00061801bd0201000618135b464953594a590a181000085d01b10214283d133c14160114253c03cf018c01c70101dd10050200059b02141513153b3c14503c01018c01b6018c7601a00202980112050200120c040b0b1c1b1d1d0908430006018901090257574435623b59680a1d0c00071d01058102010004fd0201004b061f3e32355f2c68680a251600082f01e702060304080503080107090b1e09100c080401120504e50203000c0a07022619112c1a2c0a082700083c01e30265271428511301130203b97602ae28143b52100502005a4b275e5b380e2c4a09202300065e01122e6649673b4a59680918000c00073801d7020100125b415e472c06220c00062601d102010004c70201003c184e5d1c663b4708200000000354405e67586207181f000601960104b9020100245b325c2c682c07220e000701c00104b302010004b1021901040308040326221f010202030101100504ad02030004ab020100049b0201000491020100048d02040705040b050f09040b020a140810011005048b0209050b140908031e09150b090c050400048302010003ff02018804018c01900b028a0a01840c79137d070301010103120503fd02037b004001010002020000000600
    (by decide) ⟨141, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem nineFiveRankedRootBlock114 : (⟨[⟨3,9,true⟩,⟨5,7,false⟩,⟨17,4,false⟩],333,2⟩ : Box).Closed :=
  checkUnboundedRankedBlock_closes (.nil)
    56 1048 0x4e2e39436771650700065b01202a36274c57061b0800051c01124b33721775534a4a092000000018582a5c5e5d5f07251700074201216c3d018143494a018008200c000b590108870200055a01088604020024425e544735470c000903e2013c4e633a747106220009000b5f01b30401001e0a2208665671070c0005028f011c0d21182a1a354f2c50470b140d000c310107a5020300052d01a40402004e051a6d38594a070c0007028c01031b7026320e018007230a000a4a01054001078904010006e5020000020206e40402001210220856685918000506b3010124021c052c3b353509140b000806d801013c403323394f4f5909000703a701065701b902210c010f1116240204040e1004010e0506b7021202018a14167604b22814018d26029a1401a10e0506b5020500020e1a311d3b3b454f091a3a00076d01069d02010003224c1927273b4508180f000628010683020201060d031d0f070b09042513050e0506810203001f273d3e375c1d3b082000002400056401f30214285078282802c0673a2702d52701a37813130201120505ef020300090c45436e1d565908252800077d0105dd02021001050e0604050302120c05141815100505d70203000f021f4e0e0835232c2c50470c152800054e01084b01c1020302060a0406140a131a0a04010a080c01040401140505bd02030005b50202040e06020a2c0b040f040a07041203100505b302030006115b1a6b1d74590840000b018a019f020100153f5d7f5f7f6507240d000a73018501000501d40108019401a00f019107019913019a01a6018e030b0401a1120505830201a00202c50101a803018f01a90404019c019a0a019c0401100504004e273e73676e3b7108230000003012514252415f2c01860950000602d501050f010924141a0e710607000a01cd010581020100150613192b3b6e71080e000902c101eb0205030c040c1c130c020e0402040a060e0203120504e90203002d6305614459594a68091b26000a018701e70205041c040418010407050e1212021601100504e502030004db0202019c02020c01900202070195010d0201900b01a8019c019c01a4019c0405160504d9020c019413018d03e00102d2019309010301a10c05040004d30204040802031304160d10040b030204080c01120504d10203000f09145e377171747709207d000876010004c902010004bd02100806020412020c110f0b100804040402010101140504bb021006020c090f2307010804100407010408011205040004b7020102040408040f0203080701050f13170a0304040c020102180502000f2557266b442c4a08200000003c1f3f3a0b593b4a08186e000716010004b30201001033195264657107200f00081401ad020100046a400b654a062300000002020000049d0201000493020100048f0201000487020100048102012b00360101000100
    (by decide) ⟨166, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem nineFiveRankedRootBlock115 : (⟨[⟨3,9,true⟩,⟨5,6,false⟩,⟨17,3,false⟩],279,2⟩ : Box).Closed :=
  checkUnboundedRankedBlock_closes (.cons nineFiveRankedRootBlock113 (.cons nineFiveRankedRootBlock114 (.nil)))
    31 842 0x254323666685f07000502fe01196f3037752c505e6a502f0b150d00081301100a1e56554565476b091d0b00070101060c01a501000a0c0115950200060c010506b301c50100057f01067301f10401005a1b0f1a76019c7a596b09200000002840152e2d315f6108190000001e3f272f237d597468680a1a2c000835010c542714663963694747530b18000000064a3d194f4f4545081800001c000503fd011224242e160b31291a350c010c000d018601050f01f504010300050f01e90100060f01e801000705b201a30100066e01a20402002c341c444d583b07240d0006490120040d4c433b0600060284013c482a234b686707200000000319302a33052f353509150000000a241648586306242200091a0109242a30271d17383b3b0a00070292010b02f401139b02000604c4019a040203000502f60112d9020005500112d80402000134334e615d675353091d0000002a100d1d455d4f071b00072301043258747573695f6b0919000000010a40175250018c0198019b6b0a181d000a70010f950200050f010f9402000603d5010eeb02000561010eea040200092b4d6b6201806807210f00077d011f05313317232908080008018101053701d10401000448365a474f061a0000000052251f41515706200019000502b4010760311a62061b07000a01a3010bbb0200050c010bba0402000afb0700060d01fa0100054301e70100063601e6040200032d2702072334354747500b10000701fc010c0a2d2710313108324f50470c100e000953010ad30200060d01d2040200000ac1020800054a01c00402002211562341394f5908190e0006600118613f491d6e22380b5f5f6b0c10000000121b0a0c241318210f10323a3e470e0121000701010d01a7010a8b04010002020700051e0109fb0401001005324d0e65715908210000003c22134939051a1900075c01163e2c3a1d4c4e4f4f0918000000124c601d6a7c01a047081a00000006786d4f4d6e7d018508182700050d010325493b5d6706240800082601302e2f2f623b590722000000003f2d1c49434a293b4d500a10000000021d000a140108c30200051c0108c2040204000a010100020200052b0114cd0200060d01cc0402000014810700050f01148004020002020013b1020000020213b00402000000001700
    (by decide) ⟨139, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem nineFiveRankedRootBlock116 : (⟨[⟨3,9,true⟩,⟨5,6,false⟩,⟨17,3,false⟩],265,2⟩ : Box).Closed :=
  checkUnboundedRankedBlock_closes (.cons nineFiveRankedRootBlock115 (.nil))
    23 632 0x4b39214041536b596b7d0a2300000024300d271a163e38203b3b3b0c0c00000008711f22019501f40187018701d70921300005130172019f7901ad7901a17a018f081b0e00081d0125df0200062801de0402003d33343e53596807230d00070101050f01cf01000602990125a10200050f0125a0020006740123ad0200065701ac0402006c135f0e0e356a5908200000000d1b1531343e14432f443b0b1d000701890104340716393751470809000603b00103121e3f1539494c4f4f0b173b3b47100811000b630123c30200050e0123c202000501fc0121e5020300055201e401000b01a501f104010032342b672d6b7173081b0e0007540131267241645c5f5c746b770b0c000701ec01040d2a0c4107273f3d4f474f0c140e00104401a70401000c101f27355f614563091a000000002d101765194a7707251c000701ac01483c3d6355402d37380b50476b0d140000000013000d01f101219b04010002020020f70a0005490120f60200065701053d01b7040100275d454f45672335082100000000121b18131f282b34291a230b050000000a112822192e262708082c0009019c011fc90200050e011fc80200055a011e990200050f011e980200063d011cd902000521011cd8040200241e1919252b31293b09101000053101055a0118e30200060d01051c0118cf0200050f0118ce0200065b0117e30200061701e204020300063601eb010005690117870200063501860402000132114d375b0618000000061e6a795f1c70385309181a00090101050d01e50401000017d30700050f0117d204020002020016ef020b00051701ee04020004060719171b061500000e00090c01f70100080c010202169904010600050101000100
    (by decide) ⟨132, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem nineFiveRankedRootBlock117 : (⟨[⟨3,10,false⟩,⟨5,6,true⟩,⟨17,4,false⟩],385,2⟩ : Box).Closed :=
  checkUnboundedRankedBlock_closes (.nil)
    45 1070 0x4b15275c632b5f2c4a09250b000601d201184c073a531a2c2c4a091a0b000b4d01dd02283f1411503c2853018c4e275002eb03901401100505d702030024206314295c6823000601a70113272a266562596808190a00050e0106062017533b470723000000000d000804fa01c302020401880188040f79107c018c080a028602a4030191100505bd02030005b50201987f02018b01960181019b0401840185018e019702010e0505b302030024164048595c5f4a4800051c013d245b541735685959680a1d000000015b260b58747d4408210000001c000917019f020100304b2a143a672c3b080d000901f9010585020d02860c0180120299029401907d019c0a050583020101020404090102040c040a06040303090102010c0302010d0104010704060320050400011510231b444507180000000636512332356507195100055c01050397018302018a0a02990202890601990298039105020d0c05020004ed0201977f0a04020286090183019f018c0188030189018c040184040202011405020015303c273e55443b44000502ac0133224535503553071d09000814010f032754674a566265680a0b00064801061501e90201000718545c651d6807200d000801be01dd0201001e3d5d5d4161476859680a201000083601050392010003141c3e3143274508180b000801f601cb02010004bf020100181828436462653b4a59680b1816000701d8010001000503c8010004b50201081404100907051e05040a070a04011005020004af020101060c040f0504040503080b01050a01030818080116050200049f020504041b0414031d030e020202150e0502000495020100049102010012016f677b7c79476b7d0a1b60000901012603d7012d21274f52592c4a0820000000242122615767492c081a17000510013309083a582c65596809250b00074a010581020100333c4e43382c4a07210e000802c901eb020104018a057d04029602a9018404018c018309018e0201100504e902030012363d19643b673b5959680b182d0008018301e70202970201990289019f018c7c010188018b080107050e0504e502030004db02117902018a02018f029a08018709018c01887f120e0504d902080401070404010d02142308040f01044a00076c01d50201018f087c0c01800b02970104019001830903a50e0504d10203005a4e4b2a1a614a684a68680b21002b00077a01c902010004bd020901830c01890299029508790f04018401810196010405100504bb020602010f04010a0c0913060b03040c1008011205040004b70201020401860204040180040d027904080180040188018c02a502960405160502001f40405e0b656807200000000f071b172626292908107300064c0104b3020100301804521a0e3b1d4a0e000a1701ad020100030940170d2b1d1d62092000000002020000049d0201000493020100048f0201000487020100048302012e00260101000100
    (by decide) ⟨192, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem nineFiveRankedRootBlock118 : (⟨[⟨3,10,false⟩,⟨5,6,true⟩,⟨17,4,false⟩],309,2⟩ : Box).Closed :=
  checkUnboundedRankedBlock_closes (.cons nineFiveRankedRootBlock117 (.nil))
    34 856 0x32100d2437134545081a0a00073b01fd0100060d01fc040200000ae90700062e01e80402000a0e2a1a42273145081a00000000142c1342071d41071d1b000b02c3010ad5020300050a01d404020300076e01c10401002d4c11384d1d5907220d000504ee01145b405f787906000602d901070413355c445807240000000600313e253a59622c65590b18190008210104392a2f291d11656b091c0000000a03030e23191e2d2e090d19000501011001ce010a8d04010002020009fd0a000502bd0109fc040200061e0905266765684a4a0a20000000181123251343061d00000024181c3935441d0718280008018201052f3a4a29654a07210000000e0e302e1b3041071b1500054101245d341f6244673b08000501a40115242546142865441d09180b000548010645010925221c5f38564a0825000000482d5d072f7665447a6b0a18190007290113361c111023352c353e0a100000000f03480e572c681d624a0a1800001d000901ee010d6001c30401002d5a193e65624a0722000000040f260f3f311d0718000000240636255850295f081d26000848013c04274257675868082000000000102e2f372f3b071a1600050f011e062532415f5f6808210a000c5b010887040100102b2d1d45273b4508190f00086a0107b50200066b01b40402000624171d21231d292909100f00063d011022543e44686807250000001b3f72706535596b7d7d0a2218000b0101052e01a504010003302146236664473b09200f00060e0121045338622c06250800091f01078b0200000202078a0402001e34171a563b0e2c0822000018000701e6010501840106e504010006052b323531393145091800000007232f3904231900051b01302d543441622c0721000000090f602844673850081816000a01d20106b9020403020e0424100f08110d0207020e0506b70202951800060201018c05018704030801900188047f01040405120506b5020500184031434129583b08242300071601069d020100092722222f320e3b082300001100064301068302028c0188020190018605018a0a7f0f0298018408050e05068102030010271b26676506232700061101122725050e3d2c233509140000000202000202130007290105f302018a01820601860e7e019a017d0601040802980188018e0201120505ef02032200180101000100
    (by decide) ⟨154, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem nineFiveRankedRootBlock119 : (⟨[⟨3,10,true⟩,⟨5,7,false⟩,⟨17,4,false⟩],421,2⟩ : Box).Closed :=
  checkUnboundedRankedBlock_closes (.nil)
    34 585 0xe043b3143574f4f59091a0b000903fc0105850203019c04019c010909018d01a001a11002b401ae019c040193050912050583020302040218260904030904030504080404130d011405040004ef02030508100b0401080601010c1a100212140512050200095e020835747707200000003c183f3d5b716e6208186a0009028601eb02010901920202019c01a6019a01a903e20413000502c0010401100504e9020300155a4251643a2973590920001500072c01df020100090c121b0508161a232c232c0c080000001e3c694c1c4a593b4a1e00070188010601a50104d902090b04100b05150c071f041002030e0504d702030004cd020128633c641428018d03a6018c01b401b23c3c0201b5100504cb020300031c1b183a2811442c3535470c10460006370112724954430186019e7a081b0000002d4c5370710185061918000a028a01c10201000927603173752c685909200f00062101692a146e2665687468770a2100000050422356453b594f081a00001b000801830104b9020100121b15070e34473e4709101000092e01b702040107100c09032f0e0203011407050403021205020010312026627701856877770a192500094201b10204019c01a001a004019c0d01a501960b01910f018d01aa090195070202011405020036181f5a2b3d4744583e595059620e143400053801094901a1020103050f1013190d04021010040c080110050200049702010004930201001e135a05764447740821000000020200393f0f65019b01ad01b301a108223e000a130104890201000485020109001b0101000100
    (by decide) ⟨210, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem nineFiveRankedRootBlock120 : (⟨[⟨3,10,false⟩,⟨5,7,false⟩,⟨17,4,false⟩],361,2⟩ : Box).Closed :=
  checkUnboundedRankedBlock_closes (.cons nineFiveRankedRootBlock119 (.nil))
    51 1035 0x12316a3b6b77760724000000060a0b49412b114f4d3e3e0b1500001b000a018f01c1020102040b018d010102040198040401980202019c0402019a0702019705019b13019e019e01a004011e0506bd0208019902bf03019d01ab019810019e01930f019c0401980405100506bb0205002d335134525567586509200000002a14466e01832c7777018609196a000b03c70106124b5e767176684a09230b0005520109018b0106a3021a120203111d02020a06280202010e05069d0203000689021414142828141478143c282801a003cf276316019d0302c1140506850203004e275b57610e627442000802810112052508331020322932352c2c350e0d000000030202483c05382323353e3e0c150000001b1b0413020710172b1a23232c0d0c33000c6101055d01f902143d3b14018c1414782803a702ac13262a29147828782701120201180505f50203003324466b53532c3b5909222f0006100127545f65018377070009019201420601816672595977081b0b000501010702e60105e302020201a0019c04019c01a4019d0f03019101ab04019c0103019b019607050103160505dd02030005c70210041102112211040407011701090e0505c50203003c0472503e5c62594a00050f012e09786379500185018308210c00051a01081601bb02010030256d49352c5907200d00094901a3021527143c283d3b28640103e2018c01a014782664023c01a1140505a102030006274f4c3e266228000601ef01360f39184123442c3550470b100d00070501072e018b020401ec03a903ec0c0c02a301910c090a050587020300184b455f0e2c5907250022000b7101058702010004f102010004ed02013e7514283c3c01f3505003a101df028401dd20000503a101e102050199020205019901a0019e02ce0502b20a0198040802bc020312050200150c42346b3865072800095601d90201000c150e163d2c503535470a141000087a010501b901cf02010015253460585867710c00052301075a54533b6271071809000901de01c1020100040152666559716808200e000801fd01bb020410010308080401040b21160a1602060401120502000436366a3253687777770a23000701cc013f4b344323647471080900065c01060183013604495c4f7d7a59477d7d018f0c20000000395b190191716b0186019b01b301a10a202300051101092e18510e204f3b56470a100c000c01aa0104b90201002451545d05614a5974770f00072a01066201b30201000f15486e676e6e7759770a200000000c0c3e2c332d564f4f4f0a181f0005050108310104a1020100049702010004930201001011524044562c6577770a2300000001074d2b0181627468082029000705010002020000048b020f0191019e03ee02c3019701a9018d040902019014010e0502000485020126002e0101000100
    (by decide) ⟨180, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem nineFiveRankedRootBlock121 : (⟨[⟨3,10,false⟩,⟨5,7,false⟩,⟨17,4,false⟩],315,2⟩ : Box).Closed :=
  checkUnboundedRankedBlock_closes (.cons nineFiveRankedRootBlock120 (.nil))
    25 656 0x10252086238745908250a000701a9011f1308321d35387408200a000d6e010a9f020300050c019e040200020206000553010a8d0401000954320b71760b0005038e01001209061e1f1f26222c232c2c2c0d080000001826431d2f505801a06b09200000001a232d421d43454f081a2c00081a012710111417357a6808230a00050d010e3601db04010029233d494f450a00051a0104215609554d06180800080491014758411d31061c07000b01ec010501f801cf0401004b055136662c74710c00051f0118502e2644051b07000b02ba01042e332a666871680820000000135d3664385859018616000902ed010748191c657401a1080005430101306d1920437d01a7019e091a0d000521013f272b734a01842c01800a00053001180a5e253768676c59596d0b200d00082001044a1e6c6750018008000501a90112043a74217801837c0819000c000f4301096f260e670e018c47018f091d0000001b062d050e1110202029352c0c0c1e000516010c1830542326172c3e580a100c00065c010e02b9010801000601c001089204020000516931373b760c0005028101091b6d5241203201a0019e01a10d00051101154b20141a0e0183770900052a010515010e3c48255e01890189071800000d000b1d011e3c5a26323b6e686801860a180d001001b401053301bd0401001b34184566712c710c00083301074827354747650183082400000d000a01830107af0200061e01ae0402004e510a2871714a76082100001000066101079302000544010792040200063d1950585f764a0d00082c011016434629593b07220900061d0103156344082c71710800050d0124015b165044537708090007140105130119432941018071072000000002020002021100090d0106ed020104000d0101000100
    (by decide) ⟨157, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem nineFiveRankedRootBlock122 : (⟨[⟨3,10,false⟩,⟨5,7,false⟩,⟨17,3,false⟩],285,2⟩ : Box).Closed :=
  checkUnboundedRankedBlock_closes (.cons nineFiveRankedRootBlock121 (.nil))
    27 782 0x1a0222174c5831454f091b0b000647010254482a3462156f766b536b0c18000000481b4b7876584d62687a0a1a0000001218060e3216452e353f473f47470e100000000612382e13280b606b7d0a183f000c56014e364c792f01ac597d018f09220d00063b012d3030335d424e0555584459500d1500000018030c04022521340b0b172f2f2f2f3b10080000000648066c33023c70682c3e680c140000000039000f6201060c01d704010300096601cf0401001210202a5f1d01806808230f00063201242734112f39694747530a00050181011f6d587629475907000801e401030c284060225532623e62590c0d001201ae010fc1020300050c01c001000a02e9010f9304010015202844485c734a68090f0007049d016f3616610180687d072500000016280b493b3b3b45450918000000143c103f4b2f60315f4f0a1800000009063648150b113e472c3e0b1037000909010a3f01f304010300073501eb040100102e522954435507180d000613010f301811043a293523413b0b150d000801a4010d1a01db0401001e172a3e38414f07240d000801010501a501d30401001008134b314d4d4f0c0005660103241d09443b4f071809000601eb01631d0d76714a07230000004a4a083b6a6753071d00000036254b49223d2c5959470a22000901d401044b1828562c56018508220b00071f010c2e21327c6758590820000000140e285b493b6359081b17000619010614014e60274446647d74081d000000000e000f01e6010b9102000501ed010b9004020002020700067701fb040100061a325b21516a53535f0a18000000122d2e4308341a4d4d353e500c102100077c01010c24030610281d29232c2c35353535100812000663010630301e104b353a434d3b4753470e0510000916011e032406253126235947470c100d000c0101056a01e70401000e121d16131f0614000000023e3822315331071818000539013c0e3c422e3f31071a09000726010249334b704f735f5f6b0a000513012a2270018227674f0198019901990a2010000525010a01010712010ad502000002020ad404020b0006010100020200000500
    (by decide) ⟨142, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem nineFiveRankedRootBlock123 : (⟨[⟨3,10,false⟩,⟨5,7,false⟩,⟨17,3,false⟩],281,2⟩ : Box).Closed :=
  checkUnboundedRankedBlock_closes (.cons nineFiveRankedRootBlock122 (.nil))
    30 774 0x2413360275647d01a00820000000014808444e58414f57091c00000016341a3d5653315f612500056201104e04166d472c6868091a00000012020e2a13443b373f09101900085601062a4c1f4f535e653b47530b0c000566011b42290b216a51535f09000557013f1c1e330e1d34354f353e3e0c0d000702d301202203435b4b553b45090005250148102a261c4e293b0b5f470b140d000a0185010e6c315e6f3939717709000501ff012a007e70760188567d597d0a180d00062f01180c1e074836490a3b4d474753535347100d120008480103183618193c4c585f3e4750500d140f000b0386011978547915465b463b5f018201800c140000000a131e3f0d5361683b7373501f000701c601100101060c01a301000b0c019901000a02950116890401001c3e3e4b437665530d000702ee01070d01fb01000701ef01050f01eb01000601e20115970200050f01159602000601c70114bd02000601b801bc0402002c3d2a44395e535f0c0005028e0134223f271b4561454f0918000000133124287c1d2c01820823000000360915161c373235233e470b1029000767010a1e25422a2b4c442c47470c100d000902d60136361524141c1654353e2c3e59590e1000000012070a2825152d413b3b0a101f000702ae010c24334252174361613e47590c150e000657013c1d44029d01926e029f029501f70925100009010107018d01e501000601b801e404020300090c01db0100053b01062401cd0401001212031e57086159355f47620c1012000601c201020202000a6f01c104010300086401b301000601c50113e902000601a901e80402001026064e3a5e3b3b0c00051b011a283a6a466b5e47081a0000000401847e4f5c6a20771600081c011403351f3a134f0700054e010f5a1b5d6d11526e08180a000b0101050d018f040100001487070005470114860200054701064801f9040100275915655d3b062000000016295226304d61071818000515010c5b312b5301894447081d0b00051a010501010013ef020400050d01ee040203000a0d01e10401000202000000000202139b04010000001300
    (by decide) ⟨140, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem nineFiveRankedRootBlock124 : (⟨[⟨3,10,false⟩,⟨5,6,false⟩,⟨17,3,false⟩,⟨277,1,false⟩],279,1⟩ : Box).Closed :=
  checkUnboundedRankedBlock_closes (.nil)
    27 842 0x481040344c29736567091a0b000603b0010e6c12576f762f7d770a0a000704b5010c301b366f1a517e6a0182018347776b01830f13000701bb010810121813150d0f332d35272f37370f0c0000000015000c01b3011a9702071e042a120a14321c0a0c08010b0a0906230106060116051a930202bd0602be02d304f90d02b7058802061b02b6010d04ef180102c512050400043628357444776545000502930106294c4135274f4f081d00000024301e3c493a411a2c3e0a1519000649011e141e27312b17233509150000000a2c50222e291b4131570a180000000c243330344b4a4c3e3e503e0c1400002d0007250148345e575f6d4f4f091d0a000b5601060c018f040103000803ba011a8102000601b80119eb0200063f01ea0402004a34031d415d018047535f0a1a1100081901031b0928406e44675c684701835f6b0e1011000579010902e001d901000610010801ac0119c302000602d001c204020300055a01cf0100065a01ce04020006042216233b45071a0000002e3f606256564a6808220000000503324c62018301865f0820002a000901ac016f6c7679445f442309200a000901010501f6018b010007028201ff0100063301fe04020000102622332d532f3b0d000601bf012d1b0c1c1d1132081a3e0a140c00051b010802c901d901000601cf01d80402000205000802c601eb040100240416281345530b000501f70118185a33053f555708190000000f0301426b46741d0186091800001b00067f0118455a316a352c018009000a01ef01042a0727745e6b69750900053f016c253319530192744177091a0000000c031c2d110e34323223350b151c000c01f001052f012a423101be5d01a36801c201a1090e0007019d010b01ca0119850200051b01198404020002020700062801f7010006280118e30200067a01e2040200101c142e496665070c0006018f01070d01d1010007019101055401bd01000601840117d3020300054f01d2040200013c492b44152f0b00050c0110164203263a31070800061b0130120508164d23071a00000003391f313140554708181600093301188b0200000202188a04020b00072601ff0401001a1b50354151061b000000001c1e2846462f06191800060101070e0117db04010002020000000000020216f70401001300
    (by decide) ⟨139, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem nineFiveRankedRootBlock125 : (⟨[⟨3,10,false⟩,⟨5,6,false⟩,⟨17,3,false⟩,⟨271,1,false⟩],273,1⟩ : Box).Closed :=
  checkUnboundedRankedBlock_closes (.nil)
    29 647 0xe344a7258294d3b6909000675011028161d49514d47675d0a180c00053a012863422d465c536847536b0d10000000101931062e272d45472f373f47470e15000022000801b5010715213b232f2f353b09140000003027570f10100a61414f655f2f3b6b5f101f000601d40107770140401b372e6b455f5f0a0a00077601011854604b362e5e527153776b01830e140012000e01a501ef0201020a0c0e040321031a0106170701103007031a060c0814140d1a050200045b0c65018f019d01af7d08250000000031604b3e69512f6b473b47470d143f00061601042625485857455d7709180b00053401074901e70100065001e60402005d301829342b534a59090e000602b701201a20312b4d4f4d472f550b0008028201481b18574c2c72537d476b0b1000000f000b02aa0123e1020100000023d90900060f01d80100070f01bf0100060f01be01000602d3012395020005028d012394040200343e60615c74473b5f770f00061001302a3e293a6f3b47476b0a18000000001000081501ff04010300070b01f1040103000701890122c902000501f30105220120f70401000a300b1f45374f51081b000000011b2d15050e291135090800001f00054f0104133b4e6232446b0800055e013c241e27081a4a5217442f534747530f101100072f012415487005714d5368350a1b0c000614013c481b09151a392c5317500b000b35010d3601f10401004b032e57203b2c47080d00054201011e3336254e4e432017533b0c100000000212000558010d3401e50401000021cf020800052701ce04020006271b1f6974350720000000000e062e0a4d2b45071d1a000901010002022189040100020200001fc90e00050f011fc80402000202001df702000002021df60402001400
    (by decide) ⟨136, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem nineFiveRankedRootBlock126 : (⟨[⟨3,10,false⟩,⟨5,6,false⟩,⟨17,3,false⟩,⟨269,1,false⟩],271,1⟩ : Box).Closed :=
  checkUnboundedRankedBlock_closes (.nil)
    28 684 0x81a141c2844342f464d57564f570e10000000081801052b1d333b402f3b3b41410e1523000839010c021e390d1d1755273747574f5757101011000703dc0133330a511a01dd01b501cb01a701a70b10000601e5010801f801055401930100065401920402001004082021201532271f372f3737370f0d15000601b701010a01273030222838322c353e0d0d0f00061701014b3f4c0945522317236853535f6b0f1011000b01900129870200053d0129860402040007018301fb04010300067a01ff040100005131434d655907230000000a2022313e163f2f3f09101b00074f0128f50200066b01f40402001e0e122b111b2d39292f0a101000050199016a5e176553684a5909230000000027163e5e377d3b680820000000000b282a17455b656108182600050f010a0101060c01e90100060c01050f01c7010006660128010006029b0128900402000e403d68676f5f47536b0a1000052e010e2633054f794751775f0a190c00050a010b2701f50401001018245e472f454f081a00000000044c4e49655906241a00060101070d01e30100060d0105510127af04010002020025a10a000601f401a004020048721d35525977350821000000003c1a3e2945493b4d3b091c0005320103241a1d466b68350824000000283c0a0a5a2313018b0183530a210000000202000303244659323b5c3b3e7a0b182e000817010c010d0c030e072616353b47530d0b0f00090101081b01bf0100061b01be040200212e0d512c6406220c0007590126af0200060f01ae0100065b0126910200054c012690040200483e1e5221374f3b4709190000001b060215454a2e17173b0a101f00061d014b273b565f44234708220a000512015d1c78536b7a072008000801010025b9030005100125b802000610010023c30300050f0123c204020002020021b7020000020221b60402001400
    (by decide) ⟨135, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem nineFiveRankedRootBlock127 : (⟨[⟨3,10,false⟩,⟨5,6,false⟩,⟨17,3,false⟩,⟨263,1,false⟩],265,1⟩ : Box).Closed :=
  checkUnboundedRankedBlock_closes (.nil)
    32 1067 0x55001d504010024072840223d3939292f410b1511000628010a210923154b35554d53574d47570e1000000004120758585b5b43018901977d0b21000502a801050d010701af01c901000601af01c80402001a1b665a1635635347090e000507a201402819503f096567475f6b6b0d1a00000048040f2126345d5145450a1b1d00061e01181b0d04273033025141414f472f53534711091300063f010d1c01af0401005410524115675f535f09180f00080101053701a30401000e163e744e2b675d7d5f0a1c1000060189010112141b2423274c5657373f4f0d100f000b019101a301000601b301a204020014190f1b225e632f6b5f0a1a0000000c15040416130e33202c293e23350e0923000701010802c101fd0401000122221c0d074d473f47272f3f0d15000000091325220733474d681a622100056f0118015e4a475b774f08180a000b02a501540436421f167f2223018353019b01830d1412000b7b01a10202ca07020b02bc02c407fa02ae060302dc0cf402b80c040310051c00050298014a990200065901980402001018041915233e45174d3f0b10000000012e221b33585955454f1e000502cd011833215d19234d6b623b68019e0c1a0f00071401120c112305162f372f3f370b1400000f00095c014a8d0200055c014a8c040200305a4344657d5607200000000851695e435701995f4f630a251e00051d0109074c466f537d07220000000b042d413a494d594f590a1c180005110114144c4e4e09555759590a180c000a3501f50100063501f40100057201052a01e7040100124e5b5b4c52465f383b7101a4680d1014000556010a1f01e70100061f01e60402002c401d33233b637708200e0009750149c30200050f0149c20200060f0148d50200050f0148d402000601900147a7020005570147a604020400066a01f10401003e1e3f13213b5d535f6b6b0b1d000000242d7352607b061b000601da0120646d01845a732f775f09250000007e2d5a704761384d01bc7a0a1b1c0009210146d10200062a01d00402001a0c422b4a493d2f3f3f0a101000070101050e01bb01000501ce014601000601da01469a0200050284010601b30144f702000501be010527013ed9040100080a14131922292d232527270c080000001e38072f445b575f605f0a18000024000501cb011218011a1119130d15352e2f2f0d08001000082d01cb0100062d01ca0402002819111113291e252f1f0a0800000004102641070b4f453709181e0007360142c10200060d01c00402000042a3020800052601a2040200162c03211d27310718000000301c7c357e6a136f0823000000001e00070b01429104010000000700050f01f3040100020200419b0900050c01419a0402003fc90700061e01c804020054793961377b7b273b09210f00060101003f9d03000510013f9c02000610010039f90300050f0139f804020002020034ad020000020234ac0402001400
    (by decide) ⟨132, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem nineFiveRankedRootBlock128 : (⟨[⟨3,15,false⟩,⟨5,10,false⟩,⟨17,5,false⟩,⟨257,2,false⟩],64727,1⟩ : Box).Closed :=
  checkUnboundedRankedBlock_closes (.nil)
    30 1073 0x230063850461c161535576647576767101100052c0118404239133258615f45655f5f570e0f0008039e0102300c2c22322431681d6d554f474f0f1000075d01221272465601986d1d6d6d01cb019f01af0d180000000802081334542b533f4d6637675f0e25000505c301120615240133633d36234929475959684a59595959160d0000003c181b01907e0621414a3b01830183746b2b00092e0146040206461e51562e6771273b59630f140000003c3c3001900a7a621f4637696b018d018d0e1027000c23010f124b3f4b15225a51635229376767584a5965685915011700117501ed040100020a502236586a564d5d65474f5f5f6f6f1110000000013333043f3651513a522043445c2f5f5f5353130d2f00053f01057d01303926486e645f534f4f5f6f0e150000002d1221064221100542540b490181443b56687777680186150c00002c0010029201e50100056301075601d704010012180006183c1d0d2e073c25273f373d3f3f1217000604d7016c42794f5167650197530180019b019b100005039201280c0e0c0c78483f76273b455959630181101200060392010c018401cf010005028001087601c104010010180c0618283c2c1d0f0f1d1f3f3737100816000502fc013c24063c3334412a576529592c5968596813091300083a012d5a78362530643e35701a382c594a687701951210000000243c10273f335746405a5e5e205f506b100c2a00080c010e2b01990401000f30004b6c275d39756b5874580185770186018377120d1b000f02c701ff910401000220180c120515050755373f57570e1100000000300f24181f0963025c526a746b01837729000501f6011401f506039b1303a402927201ef09241000050d01080101070d01fb01000b0d01feb902000c01e9019304010000123c1e1f461f1b2733332f353b0d11000000062a2a143015463952353b35470d152600065b01080c3016022d421135332f2f41474d4d100005430112101f2a0b284b0b1d33474147470e100000002d0624276f10554f3e29676223473e506b111026000801ab01243648311522147378735c687a595959101000000015000801bb01f30201001e30482515101b1b2d234541414d0e15000000000c2a0c033d281552292f3547475326000649010306031845255d6d6a41505962746b74741110000015000f01c601eb01000501d201073901dd0401000c2a2010163805111d3f47414d474d0f14000501830106062751390755085f4d625959620f1410000509010b018001d501000b018001c704010000061454125b1b196b7d530a100007540103fd9f0203d203b20c03cf03b515d40b9303a70706080403d60603a70d0e0c03c803bc1801160503fd9b020300060c030934193f053a274135410d103c00051901161154666901a94b7b7d5f0b180d00060101090c01970401000400071b01fd810200050d01060e01fcbf040100020200000000020203fb9b0401001300
    (by decide) ⟨32363, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem nineFiveRankedRootBlock129 : (⟨[⟨3,13,false⟩,⟨5,8,false⟩,⟨17,5,false⟩,⟨257,2,false⟩],60613,1⟩ : Box).Closed :=
  checkUnboundedRankedBlock_closes (.cons nineFiveRankedRootBlock128 (.nil))
    26 968 0x60d01c701000b01ed01fdb9040100020a28381e1e32333b3f27373f3f37140006150118101a2a19063415252d362f27373f0f10000f7d01fcf3040100020600100e0103fbcf0300071101ce01000705bb01fbc10200066d01fbc00402003020483601943e192f01af01af019f0b1d00000015002436421d2f4158476247500d100029000501b8011b0a0f1e3940450811112346234744100811000e048401fa0100062a01086301f9d702000705b001f783020300065f0182040200080d01fb0100054801073b01ed04010002180328240e34360f35353735373f3f3f110c0000000c243c3f1e044e2d321d2f2c52475347102b00067701094801f8a902000548010b3b01180c14080e0d0a231f1b2d211d290e0f00051a010c4275304669617b5668777459627d0f101100050b010c02ca01f7870200053001072301f9040100091207362b3a11412c23473e470d0813000509010a029a01f6b502000c0e01f595040104000a03d801f2c50401000230023a0e280b252b3e3f1f47470e10000000183c04420d115a3e5b2c23236847472700050281011e0c0a2a0656084e25131d274f0d140f000701bb0107028701a30203de048418060207d00fd7160fcd21048403e0049003d32503de1a03e008080801160503ef9f0207ed120f03df03f003f704980fe503d303f204ae03c810180603f90103f9120503ef9d020500121926052c25072f2f37473f470d5d00050183011010181a002a0139151b3d3317373f3710091200052e010f301b5a02206b26230e6265682c7468110d12000602af0114141615281f175e074e5d4e614d590f0d11000e01010659019b040100000a20302805311b131d2317372f2f3f10080000003c030f696f6a313e7c352947740186680f102b000619011e2d2d122d07226060726b530183676868100b13000601010601bf01ef870200061101ef860200071101eec90200061101eec804020400055101edad0200070e01ac04020003edb1070007018f01b0040200100a4134392c5b775f091a000000121212152418301c1c183137173220323e11082500070101065d019b04010002020003ecdf0a00064c01ecde040200020600094901c3040100013054023434084a3a383517385f535f100c00000014141e140e2607493547434b4b4b4f0f0c2a00051801067101ed8f0200062601ed8e0402000500070a01f304010300064a01eba504010400054b01ea8d0200060e01ea8c04020003e8e90800060f01e8e80402000003e7d1020a00061c01d004020034307005018239657f1f09181000060101051201e7830401000000000003e5ed020000020203e5ec0402001700
    (by decide) ⟨30306, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem nineFiveRankedRootBlock130 : (⟨[⟨3,12,false⟩,⟨5,8,false⟩,⟨17,4,true⟩,⟨257,2,false⟩],58271,1⟩ : Box).Closed :=
  checkUnboundedRankedBlock_closes (.nil)
    29 947 0x12074941254c7361616d770b0c000503b001151512131245201b2829280e1d0e383b473b4a1414000561010759010a11244020196b532f616b6f3f0d100000001615244e6f385d77637f0a1d1e00071b010c0f1854543c0a7901a03e4d01897d47745f10141400051d010902ad01e9a7020300060d01a601000502dc01073301990401000210380e620f3d355d3f375710000904830120283a41533925433f5d0a000f6701e985040100303c5a69697c3b76019e770a1c0000000c463c1a64552f67392513310c1523000809010b3201d904010030033c5478721a6156592c3b682f0e10000000320c5a3c47032d495569610b23000902be01061101c5040103000502d801e8890200062f01e888040200046e584647416569590e00057501220b66477a37780183676b0a180d00084601c10100070f01c00402000003e7b50800073701b4040200092d42154830214b346a32446e6b0e140000002a32350f0973436b6b091822000c01c101e7a1020300064b01a0040200024a3f5a645325533b091d0000001200051001f50100071001f401000602a801e6e10200071201e001000802a801e6a5020300061501a4010008038901e793040104000701bb01e6d30401003210000662493d69754f0a10000530011e22404233512f6b63630a00061001040a3c0d3674655b69570a19000000000c08032c6c018373018708181c0005140124153651300d345d5834325c3e0d0e000702e60108018601e5b10200061101e5b002000702ad01e4f10200061101e4f002000601850103e2b70300072301b604020002301a402c42524d61274d670c1000001400066301e2fb020300060b01fa01000901a901e2bb040100021e4a484c4f1d634f091800000000091c36073a556165656a710b102100054d010001000701d901e19b0200061001e19a020005680103e0dd0300061201e0dc0200073d0103dea90300062b01dea8040200012240241d17154525370a150000001400085b01da8f0401000003d9fd020a00060d01fc040203000901b101d90100053f01d8b9020300060b01b80402000400071a01a50100051a0103d7ed0300062401d7ec040300077e01d8990401000500084b01c304010003d4a1020800065701a004020300052101d2cf020300065301ce04020000300330143a543e5957570b101100065f0103d6e5020400060b01e404020300071a01d6a904010003d5910800062701d590040200000600060d01d4d50401000202000800050e01d2af04010003c8e7020000020203c8e60402000001014b0d0507381109151e00070101000100
    (by decide) ⟨29135, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem nineFiveRankedRootBlock131 : (⟨[⟨3,10,false⟩,⟨5,7,false⟩,⟨17,3,false⟩,⟨257,2,false⟩],21865,1⟩ : Box).Closed :=
  checkUnboundedRankedBlock_closes (.cons nineFiveRankedRootBlock130 (.cons nineFiveRankedRootBlock129 (.nil)))
    28 795 0x4001e826433302c23b0293029701bf01ff0b211300083201d70100073201d60100063201062501c90401000a122022241931341b15392f37370e0c000016000601da01eb890200062601eb8802000506a8010a0a01073f01ef0100056401e9e3020300063001e204020052361445780195657f6b019b0a1b0000000010165474355c1d019f081821000e7201e9a104010002060008018101e88902000b018101e5cb04010400064d01dcad0401000003db9d0900065001db9c04020016422513090e3e793d01890a180000000030041807180d4b7b7b0920000502f00124504371018a4d1b69081a0b00070101071d01dad304010400054f0103d9c5020400050b01d9c40402000500060d01c79f02000a0d0103a802000503fc010702c401fde304010018033c3f2a1f251d4a144635444d594710041700052b01072d01f5cf020300062701ce0402000f12061f5a606d6144495c716273626510011600050a010b6201f5a902000701a501f4d1020300065101d00402000418120c181b0527052c1d2e2e2f0e02001500054e01010e09122c031e0b0f1d272b270e040000000c1e4b1f512f19382c204f4d475059626211142500050b010d3501c9040100063c36504301ce2f01a7018f0911000501f60112242d130d372a422211433b2c0d080f000f01b501f4a30200050e010701a701f3cb02000701f801f2930200062301f292040200405036174a654b4b018b018d7f0b1d1400077901ece10200070f01e00402000002ec0700071b01ec8c0402000500061101e104010300054f01eb8d0200065801eb8c0402003e2a5006245857636d630a10000512010c38360d402f3a39555f596d0c18000000001e0f33420610094f491c530186680d1022000d0101060f01bd0401000002e99b0800063601e99a040200042f1f134401976e2c08220000000036060149215b4e5b412b414d0c152200050101073a01e8c1020300060c01c004020300082801e89d020006280102e6f10300062901e6f004020400060d01e1970401000000000800051201e09f0401000202000002c2bd0c0005110102c2bc04020002020001dc8d020000020201dc8c0402001700
    (by decide) ⟨10932, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem nineFiveRankedRootBlock132 : (⟨[⟨3,10,false⟩,⟨5,6,false⟩,⟨17,3,false⟩],259,2⟩ : Box).Closed :=
  checkUnboundedRankedBlock_closes (.cons nineFiveRankedRootBlock127 (.cons nineFiveRankedRootBlock126 (.cons nineFiveRankedRootBlock125 (.cons nineFiveRankedRootBlock124 (.cons nineFiveRankedRootBlock123 (.cons nineFiveRankedRootBlock118 (.nil)))))))
    29 451 0x50c01c30100052701061b01b904010024093031527620473509200f000b6001159d02000601870114cd020300055101cc04020300057801f90100067801f80402001812013a443f173b3b0d00054e01154e195d531a386568650a190c000602fd01014827011a2b3237382f3b3b0c100000000012000b27011487040100366c4e627a444707250000001012100a3466442c5909181c000c7301ef010006730113a90200064b01a8040200001e162b627a440b000601ee0101344048163b3907000501ac012e544727575051072009000612010912061002271f2820230a080c000b01d10113b9020300051901b804020002121c293f1517071d0d000501010601c50113a1040104000501be0112df020005160112de0402000500050d01a7040100000f990700050f010f980402000202000eef0a00053c010eee0402001e10051d1c1d2c3b08200000000163024f2c553547476b7d0b251f00060f013c332a253b453107180900084a01d50100064a01d40402003c0d1f443127430720000000000e0630302021370718000000272e424f346e5f74082600060d015a072333406806190009000d1e010bbd02000002020bbc040a00050601020202000c0101000100
    (by decide) ⟨129, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem nineFiveRankedRootBlock133 : (⟨[⟨3,9,true⟩,⟨5,6,false⟩,⟨17,3,false⟩],253,2⟩ : Box).Closed :=
  checkUnboundedRankedBlock_closes (.cons nineFiveRankedRootBlock116 (.nil))
    29 778 0x63401cf04010001182224261b2e2e35373737373f0e0c000000000c124830061c3628412c3a533b0e0427000d4a01bf01000701f401f29b020300060a019a04020300072f0197040100002709627a01e0445c01ec092500000000120315303c31173320381a0c0522000c01aa01f2870200060e01070d01e1040103000901c801f1930401000500060f01ed0401000001eec90800070e01c804020001eeb70700071101b60402030005018301ee930200066801ee9204020400070b01b904010300074201eda90401000e221a430561435963090f000501940169722e5b7d0d7f74620a1d0b000517015a5e335f6d20560186018f091d0d000c02ac01061101f30100073901eca90200061b01eca80402000500061101eb04010300055501e9b70200061e01e9b6040200020600071b01dbfb02000603f30101a6ff0300063701a6fe0402000500062d01bd0401002c2e2633603561071a00000000066c07245c292907241a000901b10101ada10300060e01ada004020001aafb0800071001fa040200000001aadf0900061201aade02000702a001018981030005100101898003000601ff016cad0200054a016cac0402003e644070295147770d000810011201646c1151533b08180a000622017901921f071f01bd474708230000000c0a1e0e0d0914162525230b041c00051a010616013166425837503b3a2f476b5f6b0e100f000701ca010a2301a70100062301a604020003044b392d1f083a3b523b5f0c141200093f01408b0200055b01408a04020009201a3b0c152e36374f370b140000004c01130a5871776208220000003f361e413426593e5947470b152f00090101051f01f904010015018d6d3601b1776307230f000859013fdf0200050f013fde0200060f013ed902000002023ed804020002020e00065601bf0401001a6c7e425e730622000000422b6026018b773e072100001b00054901183c30483f483140142e382f0c0d000010000b1a013a9b0401000a2e3e3d2d37273b0818000000001300070b0139f7040100000600050c0135bb0401000202000000020230d5040100000000001500
    (by decide) ⟨126, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem nineFiveRankedRootBlock134 : (⟨[⟨3,7,false⟩,⟨5,5,false⟩,⟨17,3,false⟩],231,2⟩ : Box).Closed :=
  checkUnboundedRankedBlock_closes (.cons nineFiveRankedRootBlock112 (.cons nineFiveRankedRootBlock133 (.cons nineFiveRankedRootBlock132 (.cons nineFiveRankedRootBlock131 (.nil)))))
    43 973 0x296ab0300070f01aa010005570196970200061b0196960200051b01072d01e50100052d01e10100071101e001000611010295cd0300071c01cc01000703e001060e019b0401000295dd0700070f01dc010005380195ab0200070e01aa0402000295930700061b0195920200066801060e01e10401000294ad0700060f0194ac040200000293fd0900071b01fc0402000400061101e30100071b0193010007340193b202000802820190a904010400080183010506e4018fe30200071101e20402000005001073010617322b2b211d3b31450a18000000061e27331e1219393a372f3a0c0c1d0005330108247978516633237f09220b00052b010a3807110d332b1d27310b18000000243c48363d5802323244624a4a0d1a1e000a0101060f01c504010000028fb30800062d018fb20402002822073f1f2b251d081a000000001f082d323b2c3807201c00050101051001ff0100071001fe0100071e01ed0100070e01ec040200028efb0700071001fa01000610018eb50200061a018eb40402000500061001d3010005019a01028d8f0300060e018d01000504d00189e9020300060d01e801000a04de010289a503000b018a01feb90401000041215c0955672f3f091800001200052b01e50100071b01e401000603c101060e01c104010001e7b10700071001b0040200000001e78f020a00051901e78e04020018121c260726500b0815001000090d01e387040100000600070e01e2d50200060e01060d01aae902000a02b6010180bb040400070189010802a30104ca87040a620401eb706104070463030a61010409016e020114050100020202a58304030010472a225b796b25376f616f0c32000502bf01011e48194b07333d41400b2c412f501003000013000601d1012d2d2d4b09204322018d2c3266504a7d018f01801104000000122d3c3c035d1215163a496671553b3b10012b000901010a1f017693020300051a01920402003c222b69606f7c07190d000c41017685020006680175f3020300053201f20402000a0209091321232c150f33272f0d0800000000282c34432b2f2727373f3f470c102500050101080b01a304010300071c0175950401000a2e185535334f31594f4f0b1d1200050101060c01ef010006018201052001dd0401001212060e232b3e3e2d272f0b14001200063c0174830200050f0174820200060f0170cd0200050f0170cc0200063a0160ef0200051e0160ee0402001c123e0f09334b172f530a181100063a0162f90200060d01f804020000628f0700051c01628e04020002020700061b0155f904010002020049dd0a0005100149dc0402000000000800060401020200000400
    (by decide) ⟨115, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem nineFiveRankedRootBlock135 : (⟨[⟨3,7,false⟩,⟨5,4,true⟩,⟨17,2,false⟩],219,2⟩ : Box).Closed :=
  checkUnboundedRankedBlock_closes (.cons nineFiveRankedRootBlock91 (.cons nineFiveRankedRootBlock90 (.cons nineFiveRankedRootBlock98 (.cons nineFiveRankedRootBlock92 (.nil)))))
    35 686 0x801950104aba9040295d7020109000505a601d4040300203921256c734763080d000801c90154f7020300051a01f60402000c5024422e0e264e08210e000b01ac0154a902000601b6014b970200050f014b9602000636014001000604b10140b0040200313c094e12722e2f08240f00076401050d01cb040100003da307000518013da202000a01ba0138a504010036a10700060d01a00402000036810700056e013680020009048501328d04010025074a0b3423355908200000001f30202214323847081b1c000701be01063f0221505856072009000b01a8011acf02000802c00119d10401040008490118af02000703b9011499040100001307000603960113d0020006270112f5020005180112f40402000500050f01b5010006400110850200052501108402000a25010fc90401000119490d444706220d00052b010df70200061b01f6010006029b01050f01d301000602ee010dab0200056d010daa040204000901010a02e7011008010a120d0b17080c0000000901240f1625170823091818000702c8010011111215360a0a07210000002724060a18252826080e0a1900001b000e4e01db970401000002daf9020a00060b01f804020300073401da9d0401000e02000f07170307100000000001032a0b11050624000000000f101c0b072606212600070101080b01ef0401030007018401d9d10200061a01d8f7020300060a01f604020300066a01d88d0200066a01d6e90200060e01d6e804020002d1f10800061001d1f0020005400102d0d30300061101d0d204020002020002bfb10b00061f01bfb00402000f21020a190d1c0d3a0915100007350195d1020300050c0195d0040204000723010294e504010500061901c691040100060903181905060d0d00070101051101c5db0401000202000184e502000002020184e40402150005010100020200000500
    (by decide) ⟨109, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem nineFiveRankedRootBlock136 : (⟨[⟨3,7,false⟩,⟨5,4,false⟩,⟨17,2,false⟩],205,2⟩ : Box).Closed :=
  checkUnboundedRankedBlock_closes (.cons nineFiveRankedRootBlock135 (.cons nineFiveRankedRootBlock134 (.cons nineFiveRankedRootBlock108 (.cons nineFiveRankedRootBlock100 (.nil)))))
    33 693 0x202000adbaf0700052a010adbae0403040503040b040b0108040c04030301010112050100020205add704040005f9c3022600060b01c204020300070b01f9a304010400073b01f88704010400051101f2eb0200061101f2ea0200063a0105ecf50300062901ecf40402001451654d530e6d07210e00060101051001d5af0200053b0105d0cf030005110105d0ce03000601df0104de020006580104de02000503af01d2e90200063b01d2e80402000500071501d1e304010400070b01a70100090b019c91040100000600050f019ba5040100000297930900060f01979204020000028408000602d80102848e0402050007520101c1fd046185020100020260fe0403000c4b1a41384a06230000000f06193911261d170b680a1427000620011a1a1522211533071500000000152d143b464706201500050b010b62012c9702000a62012bd70401000029a90800050f0129a802000672012691020005630126900402001b171d3d17470b000501de012d0c4b17073d112c08100a000702de0130681e4b684f236367090a000a018901060c01f501000a3e011cd90401001b1249210a3e464408100f000760011bd502000562011bd402000a6f011aa104010400060c01df0100051601060a01cf0401030006018101158302000a018101149f04010002030f1133112d0710000000002442274946444707201b000901b60111c10200060d01c004020000118f0700053301118e04020002020700063101cd04010024423a20234d06210000000027101005342c3e07201900063c0110bf020300050a01be04020300066e011091040100020600063e010fd90401001c1b3f2c473e06220000000d332b312f4747071b19000837010e8d0200050d010e8c040200000ded0800061701ec0402000400050e01e304010000000dc50800051a010dc4040204000e0101060401020200000000000700
    (by decide) ⟨102, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem nineFiveRankedRootBlock137 : (⟨[⟨3,5,true⟩,⟨5,4,false⟩,⟨17,2,false⟩],173,2⟩ : Box).Closed :=
  checkUnboundedRankedBlock_closes (.cons nineFiveRankedRootBlock78 (.cons nineFiveRankedRootBlock77 (.cons nineFiveRankedRootBlock72 (.nil))))
    26 399 0xc252432040a0b2f0809150b0009290120af020300050a01ae01000801c601208b0401000c03261d2922172e08100f000c02f8011e01000b01ab011be704010400060a01b30100084f011a9b0401000019ad080005750119ac040300070c019b01000a39011887040104000701970117a904010012001e321a0a000601bb0102010007470113ad04010400063d0112ef0200063d01052701e30401001e100d111f220610000000001612201b0515000a01da0111970200052b0111960402040006380110e502000a01cd010ff704010400062301b10401000a9d0207000517019c0402000013052623051d0b000b3c010a8b0401003021052c290a000617011216021919081a0801000000254439463705251300060e010c1d2e161935062008000c5901df04010002190a0f2309000641010d1c17031a05000a380107cd020300053301cc0402001014180905152307180000000c2410222919342b08141a00050c011e1716150b05180700070101060c0197040100020206000514010787040104000d0101000202000000000700
    (by decide) ⟨86, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem nineFiveRankedRootBlock138 : (⟨[⟨3,4,true⟩,⟨5,3,false⟩,⟨17,1,false⟩],101,2⟩ : Box).Closed :=
  checkUnboundedRankedBlock_closes (.cons nineFiveRankedRootBlock69 (.cons nineFiveRankedRootBlock66 (.nil)))
    45 466 0x1a030b111d1d061d08000b4a010bf30200081d010af10405bd0500051d0105b804030400060a01d904010300062301089504048b0201000202048a04030009040d14171719070c18000703c501050d01a90401000006890700050c01068804020005eb0700060d01ea040200000506000601cf0105ce0402001e100526290525000000001b271d222011061018000940010497020005180104960402001510100804200b00072901ff0100062901fe0402001005082c0420000000000f0912101c1d220716000501ba01073801c50100063801c4040200010410151b1106100000000d071d11041400072e01051801990401000e150b1b04100a0006190103830200052e010382040200120f1b1d1d05180c00050101063b01e50401000d08101004010a00071a01cf0100061a01ce040200060f05171705080b000801b501c90100061e01c80100083501ab04010300062c01a7040100029f06000617019e040200070e100b04050a00060180019b0202000509019a0402030005090102850401000500051b01f50401000a0a020f10111a070d0d00071a01f1010005520101f004020001020b21111a06110d0006190101ef02040701010717010507010a0501e902031300240101050401000202000400
    (by decide) ⟨50, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem nineFiveRankedRootBlock139 : (⟨[⟨3,4,false⟩,⟨5,2,true⟩,⟨17,1,false⟩],101,2⟩ : Box).Closed :=
  checkUnboundedRankedBlock_closes (.cons nineFiveRankedRootBlock65 (.nil))
    23 642 0xc0a0f0b0b0b060508000b26019f0401000c0e051604080a0005290119281d0e0e2c0707000558010b02a20191040100040809111105100b00072501f90100062501f804020010080b201705220b00060197011505142304220600076801ef010006029b01ee0402000d1908170b05200b000b01ee01dd04010001b7020301030904080405030205020c0501b502030d030403090403080501b302050001af0202270901042f01220a3004010c0501ad0203000a131021040843000802a501a502010107010405040302070b010c0501a302030007070d1315050d1c0007260101a3020102040103030503010308010304020310050200010d070d0f0906031f00053b010a01010902c5011608140805230600071a01910202000515019004020008040510040c0a000a200102830401000d040e17040a000501b2010c08031004100007000b02ac01ed040100180e191104240a00067201e50100060c01e404020001d50600060c01d404020001b10600061501b004020300062301a904010001a106000601c901a004020012060e0e0805200b000506010701d1019d040103000801010c01ea010c0b071011110610000900075d01a102040a090404030305010106010c05019d020300081f2018000a640101030a05020201040c0401020c050200010a140a0501051619020a1b00060198010001950201000191020100041f1d0b0b2306250014000627018b020c0102010d030602040202010c05018902031400082e0104081103200500052101019d02000634019c040200080e040b05051000000006041619041c1400050101060901970401000400050c018f040100018d0600060c018c04020001870200000202018604020f0008010100020200000500
    (by decide) ⟨50, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem nineFiveRankedRootBlock140 : (⟨[⟨3,4,false⟩,⟨5,2,false⟩,⟨17,1,false⟩,⟨97,1,false⟩],99,1⟩ : Box).Closed :=
  checkUnboundedRankedBlock_closes (.nil)
    31 470 0x202005089020e0202060201060550870200030202508618000501ad01288404050000020208000702e401df0401b3020100020201af0403000c090d1807191a28081700077201191a020b07472b4708230000001c05022b2f4e37072016000601010a7f01ed0100063401ec0402000902081a252c06200c00050701083401df04010002071d19041c0a00051c01054b01c70100064b01c6040200050d070b0b050c0b00087b01060c01bb01000501cc010001000526019b0401000d0403031105140b00050a010c03090415000600092101a10100062101a004020005071103180900051e011102250300087e01048302000501b3010482040204000a1901e90401000208090b11111107080d00050601071801e704010004100d120905180b00050701081501cf04010300060c01bd0401030008260103a9040100020e0e0a0b111107140000000005262603221700050a01060101053a01c504010002020a130514111106220e000559010a0b05040d05000541011522192a0515060007010108390102b3020005390102b20200063901052d0199040100030d070f041c0000000e0b0b030c1200050b0108120511040b06000701010001a7030005100101a604020002020000006d02000002026c0402001400
    (by decide) ⟨49, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem nineFiveRankedRootBlock141 : (⟨[⟨3,4,false⟩,⟨5,2,false⟩,⟨17,1,false⟩],85,2⟩ : Box).Closed :=
  checkUnboundedRankedBlock_closes (.cons nineFiveRankedRootBlock140 (.cons nineFiveRankedRootBlock139 (.cons nineFiveRankedRootBlock138 (.cons nineFiveRankedRootBlock137 (.cons nineFiveRankedRootBlock136 (.cons nineFiveRankedRootBlock87 (.cons nineFiveRankedRootBlock80 (.cons nineFiveRankedRootBlock79 (.nil)))))))))
    39 943 0x604a50104870200590202048509000501ab010283040300090c0d182b1d062100000014311a2b223606170006039f0114081209091b061c00000012000a21020519351300075601095101f90100061801f80100051801061901df0401000bdf0600063901de0100073901052c01c50401000a021a28210b2c2d27090800000003271e15342132380808001d000806b0019701000606b0019601000671010606bc0106018c01062101ad010006018001054c01ab040100150713070009028301051d018f0401000c040421111114220810000010000601d501810100051a0109800402000a0903050b0e06080d000601cf0108d50200050f0108d40200060f0107cf020005100107ce020007028b0106f7020300050901f6040200070c01ff040103000801f20106a504010005fd0700060f01fc010006340105bb0200050c0105ba04020003ed0700060d01ec0402000003d10700060c01d004020003c30600060f01c20100065c010301000603f90103aa0401df020100020201d504040002020001b31400063401b204020004151503220000000d191a110411000602900109070b03150000000413080804210e00077b0101c50200050e0101c4040300053901790100053c0178040200041e0f38213737390c000502b801505c5c5d474e0622000900053b01010911062a2e2b2d2d0a080b0005190106300127c30200056d0127c202000a01e40125b1040100061c122e0b2d060c0005018c011025163a041d06000c2f0123f104010400072401228f040100180c0b2950320621000000000407514d35052318000c02fa011c9902000601c0011b8d0200050f011b8c0200064f0119b3020005400119b2040200181b304d41590b0005740130420835412c1d071809000702be01271b3a1c235023072009000a650118010005028f011701000601c00117f2020006280116cb0200050c0116ca04020013ff0700060d01fe0402000013b7070005490113b602000a01ce0112c9040100060c4b4a453206200000002d092222081a47470818000000001e00070a01d3040103000601ba010fa70401000202000ee70a00062801e6040200320f2e17372306180000001d16522b36633b63082319000750010ed10200060d01d0040200000eab0700060c01aa0402000e970600050e010e9604020000000df309000529010df204020006203122331539071c000000015417614f5f4f6308201b00072b010b950200050d010b94040200000aff020900050c01fe04020002020600051a010adf0401040012010106040102020200070101000100
    (by decide) ⟨42, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem nineFiveRankedRootBlock142 : (⟨[⟨3,3,false⟩,⟨5,2,false⟩,⟨17,1,false⟩],75,2⟩ : Box).Closed :=
  checkUnboundedRankedBlock_closes (.cons nineFiveRankedRootBlock141 (.nil))
    44 994 0x602a6010eed02000502020e08000605e90107b604030400084001958102000302020294fd0a0005028b01018ac00403001c38322f3a0525000000000507292d2d460625000000092b121313273b07202500090101050d01b5040100000d950700050d010d94040200000ab308000529010ab204020018091e191c1c1f1f08080f000b7a0109f90200067a0108a5020005190108a4040404000605dd010492040404000506b301ef0100066101ee040200060e21160b1706230c000b3b019d0401001510191104250a000646010a18071a042006000504a501030b031c000000000c1302080805150f000601010b0291018f01000706a6019101000602b70190010006670106180106f7020011020206f509000503c30103bb040300050009029b01ef9b0477d1050005160177cd04030400080284013a97041d8f0500050382011d8b04030019290c21200c1807200e000701a20194a10200071101a0010007110194870200061101948602000601c0010293f30300070e01f20402000293d30700071001d20100061e0193b90200060e0193b80402000292a70800071001a601000603ed01928d0200060e01928c040200028eab020900060c01aa040203000824018e91040100040d020504050610000000031815060210070718000000001d00080b019504010300071a018483040100000283d1020a00050b0183d00403000701be010282b7030005490101fe02000703b201fef402000602db010603a501f10401000c040108171c09070c0000000012211513021107282b0d0a081d000e03a701e6990401040008039b01db8504010019170d0d262706220d000602d301acdf0200061001acde0200051c0101a6b103000602ab01a6b00402006206000601ee016201000601ee0160d50200054b0160d40430b505000501a10130aa0404040008590122eb0200054d0106400117fd04010010031c0f2c2606090000000004120c141e150f07081a00071b011bd1020300051801d004020010070f110d0306020c000b01f2011bbb02000a0c011ab5040100020600066e0111e5040100090c0b16160e16070d00063b011001000601cf011084040204000801b4010cb104069d0500055601069804030004051c131d051d0c00067b010e14131117050d00000900057701bb0100050f0106ba04020002020005e3020b00050901e204020300060e01c904010002020600075e0105870402cb020100020202c304030002020001d11400061701d0040200070a20032400000b00053d01f50100063d01f40402000e0f0b0b0410000b000535010d10110315000000000616180e04140f000a0101050f01e9040100000000018509000508010184040200000202000000000c00
    (by decide) ⟨37, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem nineFiveRankedRootBlock143 : (⟨[⟨3,2,true⟩,⟨5,2,false⟩,⟨17,1,false⟩],29,2⟩ : Box).Closed :=
  checkUnboundedRankedBlock_closes (.nil)
    27 507 0x1b071703230500066a01100a191a1a08071300000011161627042011000704a4010703be018d01000502aa01018c02000502a9010526017901000a02a90169010006029e014f0100053b014e0402000f0b0b07000803a3010807070304000501ba01090302000400055f0102140804030000000209000b01c1013501000502b4013404020002060b0117060211080000050b0b032100000003030c031b0007160104070f0f040005220115071d11041806000837011408051a1a0520000000000c090a0b0401000000240611070946060000030409180424000000192b1f0b38080732082f0009490107010d0b11110607000601dc01081408050400080184010609111113262b070109000901f70116131a1e2f2f07240000000c03111f053923230802000017001269016102000003026004020900080b0155040100030500060b0143040100020200000002022f0401000e11021200077d010501140000000008030b07040c000801ac010d0a02000632010f070b16130500070011640133020000020232040200050b02250e000520010b110200056c010c070d100405000b3401010a02180400053c01110503200400070c0107100f032405000842010c0405162023062000090010360105070703100500051a011105021a0000000805051104100000000e132203181500050701030202000f0101000100
    (by decide) ⟨14, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem nineFiveRankedRootBlock144 : (⟨[⟨3,2,false⟩,⟨5,1,false⟩],19,3⟩ : Box).Closed :=
  checkUnboundedRankedBlock_closes (.cons nineFiveRankedRootBlock30 (.cons nineFiveRankedRootBlock29 (.cons nineFiveRankedRootBlock41 (.cons nineFiveRankedRootBlock62 (.nil)))))
    38 735 0x90c0f15041d070006420112110307151e06070005230104120b070d06180700060c0108021915160506000d0101053101f70401000b0303170705180b000655011d1702250000000025292f0f04220e00060101054701e9020000030201e804020a00090c01b30401000302060006059d018701000603c50165010005310164040200161011110409000715010d090b110405000502f7010104100320000007000a2e0149010005029a01480402000205000801b4013d041f02030204020203020708051d02041100054e010a01970121bf020261020521bb020001020221b910000502cb0110df0405040008018f0175043b0300057b013a04030000050302080007560106030b03140500074b0113190b1a1105200700053101082e0104021611171906000000000c03040d0410000501010b02da010b0b02240400060c0103020200080383010507010901bf010db90406df050005160106dc040304000902b0019904028d040005038001028c040300101d0e49130a000974011e2d1e21272e29343b4a4a0b0c00072601072501f90100062501f8040200011e0424273c3f0e0e3a354a0c0012000c3a01e90100060f01e80100063a0109b70200062b01b6040200120814011c251d0710000000001e351a38230521000000021c00070296010901000601d8010901000701d801060c01ff01000a7b0108bf04010015221628472c0b0005018f010f28462f12617b070800057701055601078b0200050f01078a02000601870106f1020300050901f004020300060c01eb0401030008220106d30401001a0d1f1e041d000000001a181e0504181500080101060c01950401030008650104870401000921051504180000000011141627042000000000063d0a0d4349061c00000000250009500103cb0200050f0103ca0200060f0102ad0200052e0102ac040200020200080005140101d9046d02010002026c040300020200000002025b0401000202003502000002023404022400080101000100
    (by decide) ⟨9, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem nineFiveRankedRootBlock145 : (⟨[⟨3,4,true⟩,⟨5,2,true⟩,⟨13,1,true⟩],501,2⟩ : Box).Closed :=
  checkUnboundedRankedBlock_closes (.nil)
    78 811 0xd0b0e03210500050b01040e0323000006000525018302000302020d810800063c01c101000501b101080321000000000f0d050325000000000d100d0b0e11061d18000e62010cc3040003fd02020c940a0005240106a1040300080d070904100b000b3e01d70400048902020bae0900063e01eb0403000e030a0a0409000502ca01070a050304000502f101010d0d0a02080e07180000000c000b02e1010bc70400048b02020b9e0a00061301e30403000ac90600062801c70100062801a40403000d1002032209000504c301010b031d0400073a010aa502000553010aa3020005180105920200085301ed040004ad020209d00900062801f604030013150d040d16061400000e00064f01d1020406020504050800051301cf0100061301e804040009b502000d020209b30d00061801da0403000400052601ab040004bb02020991040100020204d50403000a070b0b04191900053b01099302000545010992040004c1020208f804030c00061501eb04010008030303150900050601071301d5040100090b021c08000b2b01c104010008bb0600062b01ba0402000710050804210000000c01070d0a051014000b3101a704010008970600060c0196040200088b0207000519018a040200040d02110b111107200d000b3e01088504010011060102040906000006070204040a14000b2001e504010300061701cd0401000c0207161005150b00050101072101c904010007c10600062101c0040200070d1003100900050601000100062d01b304010007a70600060c01a604020007a30600060c01a2040200078d0207000509018c0100076601078504010006fb0700064501fa04020002010d0909051000000003090904040c14000b1a01ed040100650533022d04010403030a0f00050101062101dd04010006d30600060c01d204020006c50600061501c40100086401b904010006b30600061b01b20402000c0a021814050e070c00082801ab0100060c01aa04020006a70600061c01a604020012150a0a0202100e08100e00063c01069d0200060c019c0402000697020700050901960402000000020206910401000689021404120101041402011108010c050685020322004c0101000100
    (by decide) ⟨250, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem nineFiveRankedRootBlock146 : (⟨[⟨3,2,false⟩,⟨5,1,false⟩],15,3⟩ : Box).Closed :=
  checkUnboundedRankedBlock_closes (.cons nineFiveRankedRootBlock144 (.cons nineFiveRankedRootBlock143 (.cons nineFiveRankedRootBlock142 (.nil))))
    40 754 0x20006019e01049b02030005038101980100057e01028d020005019b010508011d040103000606940108d902000501f50108d702000601f501ac04030300055401f1020a06040904050011020201ef0e00055d0178040400030b0f03010000000b110b0304140000000d161017041d1b0006120110051a142005050000090007029e0108058d01b50401000302000189090006049101880402030005059b01005f02001702025d08000519012f0403000402060005170106d9020005170106d7020005170103ac0200071701028d0200030202028b090006720186010007160101cf02002b020201cd0900053501670403000002020700060495019304150217050119060501000202490403110009260109a10200054901099f020005260104d002000a26016d040100040009028c01ef02003b020202ed080006018201b7040303000801e7015b01000801e7010ef302000502020ef1090005210107b90403040005250104e0f903000601d801e0f8040001020204e0a30a0006018601b0bc02000501a2010802db01b104019d04000601eb019801000601eb015701000501a101560402000701fa0103fd020011020203fb040a000501c601fe040300010422141617060c0c000b1a0107bb040100180f091c08110807090e0005010107018a0106a70200050f010005af020043020205ad0a00051e0102d704030000000001d5020e020604020106050043020201d304010002026a1f000a7a014d040103000b7201e5040100048f0600052701048e04020002060007018b01dd040100060f19130f170e07020d00075a01df0100065a01de040200000500066501b50401df0400067001da010008700101b5020300056d01b4046103000556015a04040300080501063c01bb040100210a191d1d1d06230c00086201b50100060d01b40402000003950208000509019404020300050b0103930401040007180102f70401bf050005170101bb02000a1601020201a90459020100020254040300020211000b0101080a0103020200070101000100
    (by decide) ⟨7, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem nineFiveRankedRootBlock147 : (⟨[⟨3,2,true⟩,⟨5,6,false⟩,⟨11,2,true⟩],139,2⟩ : Box).Closed :=
  checkUnboundedRankedBlock_closes (.nil)
    40 737 0x10f14160b052207000504a3010a0a0f0305150000001c0e1d061a031b071100070296012018010904200007000a01c7010fc5020300051801c40402000c211d1f160900070589010735010f9d0200053501051e010deb0401000d0d0f0e0b050b000546010c1218050d1017070800060b01070101050f01e904010003020007bf0900063a01be0402000a0906050b1106200000000d060f021a1607170818000767010d0f0407171706180800053901062d0107970200055801079604020006020707040a000579010a130a1905180600050b0101060a03041006000c01a30106f304010003150c1004101119081000000002101c1d14171f07201b000a7b0105e9020300051501e80402000e0e10032209000b620105d3040100000a030911051000000007080303041d1500050b01131317080420060007350104eb020300053401ea0402000b040e050e05240b00070e0107010a0505061507000725010d0311110519000008000b3c0104b70401000a0d030f04140b00061a010003fd0300063c01fc040200060d070f1005000b0006028b01180e0e0e040500087501051901cf0401000c0d0b030414000b00071901c30100061901c20402000c0210191905220b00062501038f0200060c018e0402000387020000030203860402000f030d171705251700082201f7020225020b0205060502f502030006180817081a11072418000a2401f1020a12080c04060601080502ef0203001514180f1819070714001b00097601cd020b041009020e0a03080502cb0203000c0b0d171a16000544010a07030322000000010b0e1404180e00084501b302010002ad02010002a90218100602040c0501020103020c0502a502030002a3020100031313170e0520000000030200120b0b130e1417081a09193c00092001990204080a060804090802070a050200030c18051905141700082e0102970210100c0108020a0601020a050295020300028b020104040814040d03040808010c05022600230101000100
    (by decide) ⟨69, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem nineFiveRankedRootBlock148 : (⟨[⟨3,2,true⟩,⟨5,6,false⟩,⟨11,4,false⟩],175,2⟩ : Box).Closed :=
  checkUnboundedRankedBlock_closes (.nil)
    42 912 0x301090933080b2008000b02e60105d30200060f01d20402000507a00105c3020300052501c204020019061d051c0b0a000501ce01250604071d2c340708000605e201083101b3040100020f0805070900057b010a010a031705060008039e010601031e1f05180000000a000a02800105a5040100191b051926290b00080e0107271b26170b0607000701d6010a18080d111d1d070006069001030c0f2831262b0700052d01000100092e01b70100062e01b60402002121070a23050a000504e1011b0b0f281628263108010a000d018d0104a70200062a01a60402001f0728081a2906210c00060e01020a0f0a0b0b06100800084c0104890200051c010488040200061f060606034e46080e000801ac01fb0100067d01fa0402000918231a0b1d0625000000030e08081c1400050a011a1610151f05190700081201091b2528262e1a1d08090006048101060101053b01bb0401000f111b22141c2b07210000001e0c2807034a470140091a000703d8012b2a2217291d0600050490010001000703d8018f0100062f018e040200042202090705232908200000000a02040d1c051f1908011b00082c010501df018301000522010382040200002519260b0e0620000000010c0f02221122070019000d01bc01fd0208031802180e191401010a0502fb020e0a0e1d0f1103050309041c0005760110061d11071b061b000000032a040229102f3523091816000a3301f302052c12070e021419080502ef02030012211f292b262c1d081a000702ce0106301c1919230607000b01c101e5020203131d11170110041202010c0502e10203040508251c0410040e02050c05040000140a0e0a1a1b07030000001b041b130507101f082b0a023b000566010801c601df0213080c0404044407060403020c0502dd0207091b0304160305142404010c0502db02050002cd020f0507141b13171007020a0502cb02030002c302080408043d0407050301030d03010401100502001e10191c081a06225900074d012d00220c241d2814260a240b0005010109019901b9022107010814050f041004110201020e0502b70203001f0407050e2c1d2c081800000001240108351a1d07202d0007170127132d261c0d35231135230b180d000501010534010002b102010002af02010002a90211021101020a082b141001040c0502a502030007201116261d2c071c0000000302000302000002a5020100001212142a200b0e323509224500080c0102a302010400230101000100
    (by decide) ⟨87, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem nineFiveRankedRootBlock149 : (⟨[⟨3,2,true⟩,⟨5,6,false⟩,⟨11,4,false⟩],151,2⟩ : Box).Closed :=
  checkUnboundedRankedBlock_closes (.cons nineFiveRankedRootBlock148 (.nil))
    27 721 0x1b36182b23200e0721000000081e08483e1a2f3208201600080196010a040a1a0e1a272508040a000a03820118810200053501188004020400090c01ed010006018401051d01b90401003305312427280e07220d00084f0117910200050e011790020005760116e1020005410116e0040200020c1528040a000701b5010706090e160506000503cb011b2e1f1a353a06000502d801020204161e0706180009000a01b8011597020300050c019601000a049f0115870200064d0114df0200060c01de04020014bf0600060f01be040203000501ac01990100053c0114980402001c16201b221315071b0e00050f0105213204250500060101060c01b50401000302000700050d01a5040100000d8907000549010d880402001a0415140509061d0d00072a01201a080815061d000000000a09030c110b0605000000181c271d1a1f0d37280918210007019801074401c70100060f01c601000602e4010cb90200063501b8040200011a201e0523060b0005160114061d07070500060197010f1a0f200505000d73010c9f0200052e010c9e0402000102050b0f161507000e00060e01280c0f2c1f1d0600073801061b0109bf020300051901be04020019041e0922152307180d000c2701af0401001c12031b1d1f06200c00064f0101030c1b14051807000d0187010989040100051f030a1d051a0c0005750103131d1f051c0600095b0108fd020300056001fc04020008000222132315070400000f00057f0112110b090b17071800000000010c020615111f37464d380b050000000a060421370f2b08352b0a010000000418240e050b0b381409233600100101051301088504010016261c051a342f07220e00052401001819221b22230b071d0a0007360107fb020300050c01fa01000a3c0107d70401000016312e29082f0e081800000024013d342f4f521308200000001f000a210106c9020300050c01c80402000302000000030206b104010f00090101000100
    (by decide) ⟨75, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem nineFiveRankedRootBlock150 : (⟨[⟨3,2,true⟩,⟨5,4,true⟩,⟨11,3,false⟩],137,2⟩ : Box).Closed :=
  checkUnboundedRankedBlock_closes (.nil)
    50 901 0x302000705a901e0b104000189030202e0a50b0005320101b0980403002a2832313a3a1f0725000000030d0604071a1f1a052020230b0d1021000a018d01728102000a0c0171b304010400081b0170c7040100030200688d0a00052501688c02000a02a7013de50401002408130b04210b000703df010e0100060282010e0100070282010df70200050f010df60402040005028a01f3020200052301f2040200210e2c2c192c060b000557010505070f041c06000c70010c810401000118070f11051b00000000070b1d0914000601f5010f0c1516081a17071800000b000a3f010ba10203000501db01a004020018200d1d04210a0006230108d1020300052201d0040200050a11070b050400000000090d120a040315000c01900108a104010014070e03111d060c00050e01241524141c2c1d07180900091c01ed0100061c01ec040200210d0e2529051d0b00094f0106d10200060c01d004020006890600056901068804020003020700063301f3040100071407140b2c06200c000601b6010c080f1b1b1d06070005018201222805260e1d062208000c04a501058d0401000708230b04200b00060494010b0214171108081508000b3401c50100063401c4040200010a251c2929060b00050b0110092a082b0520000000000c090d071a052512000a03aa0104b1020005190104b00402000a0811131305180c000703b301e30100060c01e204020003d70600061b01d60402000c1803030b1106050c00072a0103c10200062d01c0040200241408280b1d06230c00060f01080d0f0f040511071009000521010602df01b70100060c01b604020003870200000302038604020f0005160102e30401000c2417200b2b1d1d2c1d0a1d110005018b010501c901d902010002d5020c07042a08100203080502d102030002cd020e030e081005130d03060a0502cb02030002c10208030d02071010080c03030101010e0502bd02030003030105100e2426084b00073701bd02120f020f031a060502b90227040c0203030b02040c04040c03010201021205040002ad0201001b28281c1a05222f000601a4010002a5020100029f02070814050f0103010c040301050a010301011205029b020b0c11030805030d070805090c050400031c171a0e0b0e071900003b000730019702011708010b050310041102030c05029502030001070701070f050700000000010c2305170b061d2900060a010295020104002b0101000302000400
    (by decide) ⟨68, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem nineFiveRankedRootBlock151 : (⟨[⟨3,2,true⟩,⟨5,4,false⟩,⟨11,2,true⟩],125,2⟩ : Box).Closed :=
  checkUnboundedRankedBlock_closes (.cons nineFiveRankedRootBlock147 (.nil))
    44 790 0x40912210f030f0708200000001e1217060e1c09272c1d2c0b24001b0006059401011104121305071008000601a7010188890300062401888804020400070b0187ef040100000600060e01eb0401000186f5070006100186f402000529010185f3020400050d0185f204020400080295010181ad0401006fa70800051a016fa602000979016ecd02000601f1013c01000673013ce804020002010614190a0006038f010709070a0903061c000000100c12040e0d1707150000001812120b0e160e14081821000b02b00113d70200060d0105670113970200050f01139604020003020010fd0a0005140110fc04020000060007720139e9020300050a01e801000801c40139cd0401000027d102000b030227cf0f0005390113e80403000a0c0306161506100d000501c30114d702000501810114d60402000011f70214040a0c0401060511f502000183030211f304011d000641010500130a0502021106180a000601e401060c01f70401000305000601d2010a9704058d0500051d01058b0200071d0109c30401040006360108fb0404c1020100030204bd04030e00062301fd0401000005e50700060c01e404020005cd020700050a01cc04020300062d0105b704010002040f1104150b000538010704030f0505000501d0011818171104210600090101052101cf0401000e050b030d0000000016141008042213000622010489020005018d01048804020004020e0b110520000000000c0d18010415000c2301e30401000707080309050a000601db01000102100b04150008000b2a01b70401001a0201110202060b000a150195040100100f031104180a00050101050901038b0401040006019601e30401000a04170504220a00061701dd0100061701dc0402000c030d0f04050a00061701d10100061701d00402000d0b0f11041c0a00062401cb0100060c01ca04020002af0600061801ae0402000e0e090a0905100b00064201990100060c019804020002930600060c019204020002910600060c0190040200028b0600061e018a0402000400051501830401000d0b0224080005100102810200000302028004020b00280101000100
    (by decide) ⟨62, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem nineFiveRankedRootBlock152 : (⟨[⟨3,2,true⟩,⟨5,2,false⟩,⟨11,1,false⟩],81,2⟩ : Box).Closed :=
  checkUnboundedRankedBlock_closes (.cons nineFiveRankedRootBlock151 (.cons nineFiveRankedRootBlock150 (.cons nineFiveRankedRootBlock149 (.nil))))
    46 650 0x10707011a1a062109000509010a2b01d301000502da01061f01c3040100050b11031c000000000d0f021511000e41018904018902010002020184040300030200590201000002020b1404251c000669010c0f090d0b05190000000016181a03240011000d038e0102810401000b14022509000902db01db0100063f01da040201040305020201040103090c05010002026d0404170005570106010f0f040800000001020e080b050810000502c40107029c01d10100060e01d001000501e40101b7020006028e01b60100067d012136052c292f370723000000022629691b453b466b230a200019000a01be0125062e510a31333609210a0008790130160c2c0f22232923233b0b1d00000020000659274e524b3e09210000005f3c0b7d6772400184082029000501010b01b1012197020300050c019604020300080c01218d02000b0c01e9040100030500063e01208704010002050f23210d06180d000506010632011fbb04010000001ee30900050f011ee20402000302001a950a00050d011a9404020400080c010201000a02a101030a021704200600064001190c050504230600094b01c10100064b01c0040200120d070716191607010d000e7f01b90401000e0b0b0314000000030d000801b201ad0401000f0d13020e050c0b00092601a90100062601a804020000090a0d1a19060400000018050407042400001700084301a10100064301a0040200018d021001030e0201031004010a05018b020317000671010c3201a9040100040f180e0e05080b00071b0101a50200063a01a404020013021108111a061c0c000501010716019b0401000c04100904090006060100000200050c0197040100019102000002020190040200001100080a0103020200070101000100
    (by decide) ⟨40, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem nineFiveRankedRootBlock153 : (⟨[⟨3,2,false⟩,⟨5,1,false⟩],13,3⟩ : Box).Closed :=
  checkUnboundedRankedBlock_closes (.cons nineFiveRankedRootBlock146 (.cons nineFiveRankedRootBlock145 (.nil)))
    57 863 0x30200550202050205000503025304010003022a04041700051c01390100051c0138041d02020f030a0401020108051702050000030200270200000302260402000000002300050f01f4a90401000004f3bd0900050f0104f3bc04020000039aa30a00051d01039aa2030005290103999c030005280101cd9104040079ad0800050d0179ac040200006e07000601e3016ebe04000102026eb40900052001379f040400579d0700052001579c0402000051c9080005200151c4020005200128e404030038b70700055f0138b604020000368d020001020236890f00053f011b8604030007080e0b111106210d000901e40127d50401000026c70204020102040526c502041602141802021602010a050003020226c32400052a0113a304060025c10700052a0125c00402000024c302181404140212080108050001020224c1190005200112a10404001d0600060299011d0100050299011d8702000520011d8402000520010ec30403001cbf0700053d011cbe040200001bf90800051d011bf60200051d010dfc0403040005480119c504010000198f0800054801198d02000520010cc704030017f7070005480117f60402000017c708000501fd0117c502000528010be30403000f070711041a0b0009740115f30401000015cd08000520011501000601d5010ae604030013df070005200113de0402000013c1020003020213bf0f00062b01e004030012eb020700053401ea04020002020012cf0214160619040512cd1200062901cc0100062901a70405000c01040407050d0b000902830112b504010000129b080005200112980200052001098d04030011d307000502a40111d20402000011bb02000d020211b80f0005410108dd0403000e0d0d0a040a00055c01010d021005052300000000040d050e041000056f01070d10032105000a3e010fcd02000502020f0800074401e604030009041011042400000000090b0b031a000000000a0208032100000000080d030315000000002900072401cd020508030a0405000d02020ecb0e00062601a604040004070b032209000634010e95022c2e020301010605000502020e931100053301078a04040007040405042000000000120115150d0d05071018000c3d010daf040003f302020cf9040100020206d70403130026010105040100020200020203020800090101000100
    (by decide) ⟨6, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem nineFiveRankedRootBlock154 : (⟨[⟨3,2,false⟩],7,4⟩ : Box).Closed :=
  checkUnboundedRankedBlock_closes (.cons nineFiveRankedRootBlock17 (.cons nineFiveRankedRootBlock0 (.cons nineFiveRankedRootBlock8 (.cons nineFiveRankedRootBlock2 (.cons nineFiveRankedRootBlock1 (.cons nineFiveRankedRootBlock7 (.nil)))))))
    32 428 0x190203050201020106051702030004030005090f0b041917000627010a1017031a0000000d08111a0420000000191902180000000a070f03181d000a02c501030e110b0b05010000000d1011031d0f00073801061c081a2005000a170107211a03230000000f0a111117050e000a6e01201513333b2c3b2c08180a00057f011256011f02010802030101020101010a051d020300060302150005019c010410170300066c010102030304000a1d010e0502200000000d0d110309000000020d020813001501b901090a171504180000000b18161104200f00054a0105460107082211040005640110100b1d1705100000000f101514110f00053f01090117030205000e69011b05101a20052100000008030d0b04101000072f010c120f16191106080000000c0a14161705080000000a08100308000000100a0f0a042200064c0106050100000303000e1d36233a052000000012192d33170518160012010106190115254a4a5b06200000000414225c3f4f5f07201300051b0124180c422f474b0710000000183d403e5636374b080816001201010f1b010f17111711050800000003050c000e0101000100
    (by decide) ⟨3, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem nineFiveRankedRootBlock155 : (⟨[⟨3,2,false⟩],5,4⟩ : Box).Closed :=
  checkUnboundedRankedBlock_closes (.cons nineFiveRankedRootBlock154 (.cons nineFiveRankedRootBlock153 (.cons nineFiveRankedRootBlock152 (.nil))))
    42 640 0x30203000701af01d1020001030201ce0800051801680100076c014b020605020500030302490b00051e01250404030006018001199902000003021998040001030218e810000502b3010ccc0200071f0103bd0208040204040306050003020203bb11000603b401de04040300061601d90100061601d701000516016c01000816019b01000616019901000516014d040303000617018f01000501f501018d020005190147040303000604830101e1ed030005360101e1eb0300051b0170f6040300000a0f03250a000a380129f704010002060006610128d90200052c011ee102000302021edf0900052d010fb0040300101316080705100c000b02c5010af104010400053901ab020005020208a90800057a0104950200067a01770100053501760402000008060a031005020c00067801060108070505080000000008010b140e050d12000a01f10109bd0200056b0109bc04020400080c0108e704010400082b01079b0401040005220104fd02000602940104b70200057c0104b50200057c01029b02000a7c016b04010000140e18191005220c00053d010005200a0a130521000000000c00056a01b70100060d01b604020000068f0700050c01068e04020005cb020800050d01ca04020003020600065b0105ab04010003ff0700065e01fe040203000501a601d302000b020203d10800067701e9040303000877016704010000060f0d140900063c0106080b0711052300000000051504050b09061200080101050f01ad010005370100039302000002020392040200130b0e11042000000000100502181b000a2b0102bb02120d0205004f020202b90401000202019d04041600061c0102025d040105000801010a0c0103020200090101000100
    (by decide) ⟨2, rfl⟩ (by decide +kernel)

theorem nineFiveRankedRoot_closed : (⟨[⟨3,2,false⟩],5,4⟩ : Box).Closed :=
  nineFiveRankedRootBlock155

end OddWeirdSubproblems

open OddWeirdSubproblems

private theorem threeOnceTiny (r : ℕ) (hr : r ≤ 2) :
    (⟨[⟨3, 1, true⟩], 5, r⟩ : Box).Closed := by
  interval_cases r
  all_goals
    apply close_of_upperNum_le (show 1 < 5 by decide)
    decide +kernel

theorem OMA.solution : type_of% @Erdos470.erdos_470.variants.odd_weird_prime_div := by
  apply atLeastSix_of_threeRoots
  · intro r hr
    by_cases hs : r ≤ 2
    · exact threeOnceTiny r hs
    · interval_cases r
      · exact oneFourRootClosed
      · exact oneFiveRootClosed
  · intro r hr
    interval_cases r
    · exact nineSmallComputed0
    · exact nineSmallComputed1
    · exact nineSmallComputed2
    · exact nineFourRootClosed
    · exact nineFiveRankedRoot_closed
