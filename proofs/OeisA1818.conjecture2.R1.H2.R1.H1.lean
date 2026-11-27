import OMAReductions.R_OeisA1818_conjecture2_R1_H2_R1
import Mathlib

-- Credit: @marcusbuffett
/-! Delete one vertex of a long cycle, and average over the positions in
which it can be reinserted. The reciprocal-difference identity makes the
resulting sum telescope (compare Yang–Zhang, arXiv:2605.19502, Lemma 11). Conjugation averages recover each cycle type. -/
namespace CycleCancellation
open Finset Equiv
variable {α R : Type*} [Fintype α] [DecidableEq α] [CommRing R]

def weight (C : α → α → R) (s : Perm α) := ∏ i, C (s i) i

lemma insertion (C : α → α → R)
    (tri : ∀ a x b, a ≠ x → x ≠ b → a ≠ b →
      C a x * C x b = C a b * (C a x + C x b))
    (s : Perm α) {x y : α} (hx : s x = x) (hxy : x ≠ y) (hy : s y ≠ y) :
    weight C (s * swap x y) =
      (∏ i ∈ univ.erase x, C (s i) i) * (C (s y) x + C x y) := by
  classical
  have hsx : s y ≠ x := fun h => hxy (s.injective (hx.trans h.symm))
  let f := fun i => C ((s * swap x y) i) i
  let g := fun i => C (s i) i
  have he : y ∈ (univ : Finset α).erase x := mem_erase.mpr ⟨hxy.symm, mem_univ _⟩
  have rest : (∏ i ∈ (univ.erase x).erase y, f i) =
      ∏ i ∈ (univ.erase x).erase y, g i := by
    apply prod_congr rfl
    intro i hi
    have hiy := (mem_erase.mp hi).1
    have hix := (mem_erase.mp (mem_erase.mp hi).2).1
    simp [f,g,Perm.mul_apply,swap_apply_of_ne_of_ne hix hiy]
  have fx : f x = C (s y) x := by simp [f,Perm.mul_apply]
  have fy : f y = C x y := by simp [f,Perm.mul_apply,hx]
  change (∏ i, f i) = (∏ i ∈ univ.erase x, g i) * _
  rw [← mul_prod_erase univ f (mem_univ x), ← mul_prod_erase _ f he,
      ← mul_prod_erase _ g he, fx, fy, rest, ← mul_assoc, tri _ _ _ hsx hxy hy]
  dsimp [g]
  ring

lemma orbit_sum (C : α → α → R)
    (skew : ∀ i j, C i j = -C j i)
    (tri : ∀ a x b, a ≠ x → x ≠ b → a ≠ b →
      C a x * C x b = C a b * (C a x + C x b))
    (s : Perm α) {x u : α} (hx : s x = x) (hu : s u ≠ u) :
    (∑ y ∈ univ.filter (s.SameCycle u), weight C (s * swap x y)) = 0 := by
  classical
  let O := univ.filter (s.SameCycle u)
  have hy (y : α) (hy : y ∈ O) : s y ≠ y := fun h =>
    hu (((mem_filter.mp hy).2).apply_eq_self_iff.mpr h)
  have xy (y : α) (h : y ∈ O) : x ≠ y := fun he => hy y h (he ▸ hx)
  have perm : (∑ y ∈ O, C (s y) x) = ∑ y ∈ O, C y x := by
    apply sum_nbij' s s.symm
    · intro y h
      exact mem_filter.mpr ⟨mem_univ _, (mem_filter.mp h).2.apply_right⟩
    · intro y h
      exact mem_filter.mpr ⟨mem_univ _, (mem_filter.mp h).2.symm_apply_right⟩
    · simp
    · simp
    · simp
  change (∑ y ∈ O, _) = _
  calc
    _ = ∑ y ∈ O, (∏ i ∈ univ.erase x, C (s i) i) * (C (s y) x + C x y) :=
      sum_congr rfl fun y h => insertion C tri s hx (xy y h) (hy y h)
    _ = _ := by
      rw [← mul_sum, sum_add_distrib, perm]
      have neg : (∑ y ∈ O, C x y) = -(∑ y ∈ O, C y x) := by
        rw [← sum_neg_distrib]
        exact sum_congr rfl fun y _ => skew x y
      rw [neg, add_neg_cancel, mul_zero]
end CycleCancellation

namespace CycleCancellation
open Finset Equiv
variable {α R : Type*} [Fintype α] [DecidableEq α] [CommRing R]

omit [DecidableEq α] in
lemma weight_conj (C : α → α → R) (g t : Perm α) :
    weight C (g * t * g⁻¹) = weight (fun i j => C (g i) (g j)) t := by
  unfold weight
  rw [← Equiv.prod_comp g (fun i => C ((g * t * g⁻¹) i) i)]
  simp [Perm.mul_apply]

def average (C : α → α → R) (t : Perm α) : R :=
  ∑ g : Perm α, weight C (g * t * g⁻¹)

lemma average_conj (C : α → α → R) (t h : Perm α) :
    average C (h*t*h⁻¹) = average C t := by
  unfold average
  calc
    _ = ∑ g : Perm α, weight C ((g*h)*t*(g*h)⁻¹) := by
      apply sum_congr rfl
      intro g _
      simp [mul_assoc]
    _ = _ := Equiv.sum_comp (Equiv.mulRight h) (fun g => weight C (g*t*g⁻¹))

lemma average_zero (C : α → α → R) (skew : ∀ i j, C i j = -C j i)
    (tri : ∀ a x b, a ≠ x → x ≠ b → a ≠ b →
      C a x * C x b = C a b * (C a x + C x b))
    (units : ∀ k : ℕ, 0 < k → k ≤ Fintype.card α → IsUnit (k : R))
    (t : Perm α) {k : ℕ} (hk : k ∈ t.cycleType) (hk3 : 3 ≤ k) :
    average C t = 0 := by
  classical
  have ex : ∃ x, t (t x) ≠ x := by
    by_contra! h
    have hpow : t^2 = 1 := Perm.ext fun x => by simpa [pow_two,Perm.mul_apply] using h x
    have hd := (Perm.dvd_of_mem_cycleType hk).trans (orderOf_dvd_of_pow_eq_one hpow)
    have := Nat.le_of_dvd (by decide : 0 < 2) hd
    omega
  obtain ⟨x, hx⟩ := ex
  let u := t⁻¹ x
  have htu : t u = x := t.apply_symm_apply x
  let s := t * swap x u
  have hsx : s x = x := by simpa [s,Perm.mul_apply] using htu
  have hsu : s u ≠ u := by
    simp only [s,Perm.mul_apply,swap_apply_right]
    intro h
    exact hx ((congrArg t h).trans htu)
  have ht : s * swap x u = t := by simp [s,mul_assoc,Equiv.swap_mul_self]
  let O := univ.filter (s.SameCycle u)
  have hpos : 0 < O.card := card_pos.mpr ⟨u, mem_filter.mpr ⟨mem_univ _, Perm.SameCycle.rfl⟩⟩
  have same (y : α) (hy : y ∈ O) : average C (s * swap x y) = average C t := by
    obtain ⟨j,hj⟩ := (mem_filter.mp hy).2
    let h := s^j
    have hhx : h x = x := (show Function.IsFixedPt s x from hsx).perm_zpow j
    have hhy : h u = y := hj
    have comm : Commute h s := (Commute.refl s).zpow_left j
    have eq : h*t*h⁻¹ = s * swap x y := by
      rw [← ht, ← mul_assoc, comm.eq, mul_assoc s h, Equiv.mul_swap_eq_swap_mul, hhx, hhy]
      group
    rw [← eq, average_conj]
  have zero : (∑ y ∈ O, average C (s * swap x y)) = 0 := by
    unfold average
    rw [sum_comm]
    apply sum_eq_zero
    intro g _
    simp_rw [weight_conj]
    exact orbit_sum (fun i j => C (g i) (g j)) (fun i j => skew _ _) (fun a z b haz hzb hab =>
      tri _ _ _ (g.injective.ne haz) (g.injective.ne hzb) (g.injective.ne hab)) s hsx hsu
  rw [sum_congr rfl same, sum_const, nsmul_eq_mul] at zero
  exact (units O.card hpos (card_le_univ O)).mul_left_cancel (by simpa using zero)

lemma class_sum_zero (C : α → α → R) (skew : ∀ i j, C i j = -C j i)
    (tri : ∀ a x b, a ≠ x → x ≠ b → a ≠ b →
      C a x * C x b = C a b * (C a x + C x b))
    (units : ∀ k : ℕ, 0 < k → k ≤ Fintype.card α → IsUnit (k : R))
    (factorialUnit : IsUnit ((Fintype.card (Perm α) : ℕ) : R))
    (c : Multiset ℕ) (hc : ∃ k ∈ c, 3 ≤ k) :
    (∑ t ∈ univ.filter (fun t : Perm α => t.cycleType = c), weight C t) = 0 := by
  classical
  let K := univ.filter (fun t : Perm α => t.cycleType = c)
  have perm (g : Perm α) : (∑ t ∈ K, weight C (g*t*g⁻¹)) = ∑ t ∈ K, weight C t := by
    apply sum_nbij' (fun t => g*t*g⁻¹) (fun t => g⁻¹*t*g)
    · intro t h
      exact mem_filter.mpr ⟨mem_univ _, Perm.cycleType_conj.trans (mem_filter.mp h).2⟩
    · intro t h
      apply mem_filter.mpr
      exact ⟨mem_univ _, by simpa using (show (g⁻¹*t*(g⁻¹)⁻¹).cycleType = c from
        Perm.cycleType_conj.trans (mem_filter.mp h).2)⟩
    · intro t _; group
    · intro t _; group
    · intro t _; rfl
  have zero : (∑ t ∈ K, average C t) = 0 := by
    apply sum_eq_zero
    intro t h
    obtain ⟨k,hk,hle⟩ := hc
    apply average_zero C skew tri units t (k := k) _ hle
    simpa [(mem_filter.mp h).2] using hk
  unfold average at zero
  rw [sum_comm] at zero
  simp_rw [perm] at zero
  apply factorialUnit.mul_left_cancel
  simpa [K,nsmul_eq_mul] using zero

end CycleCancellation

namespace CycleCancellation
open Equiv Finset

lemma inverse_triangle {n : ℕ} {a b d : ZMod n} (hd : a+b = d)
    (ha : IsUnit a) (hb : IsUnit b) (hu : IsUnit d) :
    a⁻¹*b⁻¹ = d⁻¹*(a⁻¹+b⁻¹) := by
  apply hu.mul_left_cancel
  rw [← mul_assoc d d⁻¹, ZMod.mul_inv_of_unit _ hu, one_mul, ← hd]
  calc (a+b)*(a⁻¹*b⁻¹) = (a*a⁻¹)*b⁻¹ + (b*b⁻¹)*a⁻¹ := by ring
    _ = _ := by rw [ZMod.mul_inv_of_unit _ ha,ZMod.mul_inv_of_unit _ hb]; ring

lemma cauchy_class_sum (p : ℕ) (hp : p.Prime) (c : Multiset ℕ) (hc : ∃ k ∈ c, 3 ≤ k) :
    let C : Fin (p-1) → Fin (p-1) → ZMod (p^2) := fun i j =>
      if i=j then 0 else ((i.val : ZMod (p^2)) - j.val)⁻¹
    (∑ t ∈ univ.filter (fun t : Perm (Fin (p-1)) => t.cycleType = c), ∏ i, C (t i) i) = 0 := by
  classical
  intro C
  have small (k : ℕ) (hk : 0 < k) (hl : k < p) : IsUnit (k : ZMod (p^2)) :=
    (ZMod.isUnit_natCast_iff_not_dvd_pow hp (by decide)).mpr (Nat.not_dvd_of_pos_of_lt hk hl)
  have diffPos (i j : Fin (p-1)) (h : j < i) :
      IsUnit ((i.val : ZMod (p^2)) - j.val) := by
    have hlt : j.val < i.val := h
    have hbound := i.isLt
    have H := small (i.val-j.val) (by omega) (by omega)
    rwa [Nat.cast_sub hlt.le] at H
  have diff (i j : Fin (p-1)) (h : i ≠ j) : IsUnit ((i.val : ZMod (p^2))-j.val) := by
    rcases lt_or_gt_of_ne h with h|h
    · simpa using (diffPos j i h).neg
    · exact diffPos i j h
  apply class_sum_zero C _ _ _ _ c hc
  · intro i j
    by_cases h : i=j
    · subst j; simp [C]
    · simp only [C,if_neg h,if_neg (Ne.symm h)]
      apply ZMod.inv_eq_of_mul_eq_one
      have e := ZMod.mul_inv_of_unit _ (diff j i (Ne.symm h))
      linear_combination e
  · intro a x b hax hxb hab
    simp only [C,if_neg hax,if_neg hxb,if_neg hab]
    exact inverse_triangle (by ring) (diff _ _ hax) (diff _ _ hxb) (diff _ _ hab)
  · intro k hk hk'
    apply small _ hk
    simp only [Fintype.card_fin] at hk'
    have := hp.pos
    omega
  · rw [Fintype.card_perm, Fintype.card_fin, ZMod.isUnit_natCast_iff_not_dvd_pow hp (by decide),
        hp.dvd_factorial]
    have := hp.pos
    omega

end CycleCancellation

theorem OMA.solution : OMA.R_OeisA1818_conjecture2_R1_H2_R1.H1 := by
  intro p hp _ C c hc
  exact CycleCancellation.cauchy_class_sum p hp c hc
