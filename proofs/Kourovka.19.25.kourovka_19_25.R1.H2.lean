import OMAReductions.R_Kourovka_19_25_kourovka_19_25_R1
import Mathlib

/-! The affine-line group in the counterexample of van Doorn, Judin, Monticone
and Morrison. We count its orders, and those of the two other factors, before
combining the three distributions by least common multiples. -/

open Finset

namespace Affine42

structure A where
  u : ZMod 6
  t : ZMod 7
deriving DecidableEq, Fintype

private lemma extA {a b : A} (hu : a.u = b.u) (ht : a.t = b.t) : a = b := by
  cases a
  cases b
  congr

private def scale (u : ZMod 6) : ZMod 7 := 3^u.val

private theorem scale_add : ∀ u v, scale (u+v) = scale u * scale v := by decide +kernel
private theorem scale_zero : scale 0 = 1 := by decide +kernel

instance : Group A where
  one := ⟨0,0⟩
  mul a b := ⟨a.u+b.u,a.t+scale a.u*b.t⟩
  inv a := ⟨-a.u,-(scale (-a.u)*a.t)⟩
  mul_assoc a b c := by
    apply extA
    · exact add_assoc _ _ _
    · change a.t + scale a.u * b.t + scale (a.u+b.u) * c.t =
        a.t + scale a.u * (b.t + scale b.u * c.t)
      rw [scale_add]
      ring
  one_mul a := by
    apply extA
    · exact zero_add _
    · change 0 + scale 0 * a.t = a.t
      rw [scale_zero, one_mul, zero_add]
  mul_one a := by
    apply extA
    · exact add_zero _
    · change a.t + scale a.u * 0 = a.t
      rw [mul_zero, add_zero]
  inv_mul_cancel a := by
    apply extA
    · exact neg_add_cancel _
    · exact neg_add_cancel _

private abbrev C := Multiplicative (ZMod 6)
private abbrev S := Equiv.Perm (Fin 4)

private def ordC (u : C) : ℕ := ![1,6,3,2,3,6] u.toAdd
private def ordS (p : S) : ℕ :=
  if p = 1 then 1 else if p ^ 2 = 1 then 2 else if p ^ 3 = 1 then 3 else 4
private def ordA (a : A) : ℕ :=
  if a.u = 0 then (if a.t = 0 then 1 else 7) else ordC (Multiplicative.ofAdd a.u)

private lemma order_cert {G : Type} [Group G] (v : G) {n : ℕ}
    (hc : 0 < n ∧ v ^ n = 1 ∧ ∀ i : Fin n, 0 < i.val → v ^ i.val ≠ 1) :
    orderOf v = n :=
  (orderOf_eq_iff hc.1).mpr ⟨hc.2.1, fun i hi hp => hc.2.2 ⟨i,hi⟩ hp⟩

private lemma oc (u : C) : orderOf u = ordC u :=
  order_cert u ((by decide +kernel : ∀ v : C, 0 < ordC v ∧ v^(ordC v) = 1 ∧
    ∀ i : Fin (ordC v), 0 < i.val → v^i.val ≠ 1) u)
private lemma os (p : S) : orderOf p = ordS p :=
  order_cert p ((by decide +kernel : ∀ v : S, 0 < ordS v ∧ v^(ordS v) = 1 ∧
    ∀ i : Fin (ordS v), 0 < i.val → v^i.val ≠ 1) p)
private lemma oa (a : A) : orderOf a = ordA a :=
  order_cert a ((by decide +kernel : ∀ v : A, 0 < ordA v ∧ v^(ordA v) = 1 ∧
    ∀ i : Fin (ordA v), 0 < i.val → v^i.val ≠ 1) a)

private lemma sum_over_orders {T : Type} [Fintype T] (o : T → ℕ)
    (rangeOrder : Finset ℕ) (inside : ∀ a, o a ∈ rangeOrder) (m : ℕ → ℕ)
    (count : ∀ n ∈ rangeOrder, (univ.filter (fun a => o a = n)).card = m n)
    (f : ℕ → ℕ) :
    ∑ a, f (o a) = ∑ n ∈ rangeOrder, m n * f n := by
  rw [← sum_fiberwise_of_maps_to (s := univ) (g := o) (fun a _ => inside a)]
  apply sum_congr rfl
  intro n hn
  rw [← count n hn]
  exact sum_const_nat fun a ha => congrArg f (mem_filter.mp ha).2

private def countA (n : ℕ) : ℕ := match n with
  | 1 => 1 | 2 => 7 | 3 => 14 | 6 => 14 | 7 => 6 | _ => 0

private def countS (n : ℕ) : ℕ := match n with
  | 1 => 1 | 2 => 9 | 3 => 8 | 4 => 6 | _ => 0

private def countC (n : ℕ) : ℕ := match n with
  | 1 => 1 | 2 => 1 | 3 => 2 | 6 => 2 | _ => 0

private lemma sumA (f : ℕ → ℕ) : ∑ a : A, f (ordA a) =
    ∑ n ∈ ({1,2,3,6,7} : Finset ℕ), countA n * f n := by
  apply sum_over_orders _ _ (by decide +kernel)
  intro n hn
  fin_cases hn <;> decide +kernel

private lemma sumS (f : ℕ → ℕ) : ∑ p : S, f (ordS p) =
    ∑ n ∈ ({1,2,3,4} : Finset ℕ), countS n * f n := by
  apply sum_over_orders _ _ (by decide +kernel)
  intro n hn
  fin_cases hn <;> decide +kernel

private lemma sumC (f : ℕ → ℕ) : ∑ u : C, f (ordC u) =
    ∑ n ∈ ({1,2,3,6} : Finset ℕ), countC n * f n := by
  apply sum_over_orders _ _ (by decide +kernel)
  intro n hn
  fin_cases hn <;> decide +kernel

theorem witness : ∃ (K : Type) (_ : Group K) (_ : Fintype K), Fintype.card K = 42 ∧
    ∑ h : Multiplicative (ZMod 6) × Equiv.Perm (Fin 4) × K, Nat.totient (orderOf h) = 23984 := by
  refine ⟨A, inferInstance, inferInstance, by decide +kernel, ?_⟩
  simp only [Fintype.sum_prod_type, Prod.orderOf_mk, oc, os, oa]
  let valuesA : Finset ℕ := {1,2,3,6,7}
  let valuesS : Finset ℕ := {1,2,3,4}
  let valuesC : Finset ℕ := {1,2,3,6}
  let term (c z a : ℕ) := Nat.totient (c.lcm (z.lcm a))
  calc
    _ = ∑ u : C, ∑ p : S, ∑ a ∈ valuesA, countA a * term (ordC u) (ordS p) a := by
      apply sum_congr rfl
      intro u _
      apply sum_congr rfl
      intro p _
      exact sumA (term (ordC u) (ordS p))
    _ = ∑ u : C, ∑ z ∈ valuesS, countS z *
        ∑ a ∈ valuesA, countA a * term (ordC u) z a := by
      apply sum_congr rfl
      intro u _
      exact sumS (fun z => ∑ a ∈ valuesA, countA a * term (ordC u) z a)
    _ = ∑ c ∈ valuesC, countC c * ∑ z ∈ valuesS, countS z *
        ∑ a ∈ valuesA, countA a * term c z a :=
      sumC (fun c => ∑ z ∈ valuesS, countS z * ∑ a ∈ valuesA, countA a * term c z a)
    _ = 23984 := by decide +kernel

end Affine42

theorem OMA.solution : OMA.R_Kourovka_19_25_kourovka_19_25_R1.H2 := Affine42.witness
