import OMAReductions.R_OeisA2426_conjecture_R1

/-! # The central trinomial coefficient at a prime -/
-- Credit: @steveDOTdigital
namespace OMA.Trinomial
open Polynomial Finset
open scoped Polynomial

-- Read the middle coefficient by first choosing which factors contribute an even degree.
private lemma middle (R : Type*) [CommRing R] (n : ℕ) :
    (((X^2+1+X : R[X])^n).coeff n) = (OeisA2426.a n : R) := by
  classical
  rw [add_pow, ← lcoeff_apply, map_sum]
  simp only [lcoeff_apply,← C_eq_natCast,coeff_mul_C]
  have digit (j : ℕ) (hj : j ∈ range (n+1)) :
      (((X^2+1 : R[X])^j * X^(n-j)).coeff n) =
        if 2 ∣ j then (j.choose (j/2) : R) else 0 := by
    have le : j ≤ n := by simpa using hj
    have exp : (X^2+1 : R[X])^j = expand R 2 ((X+1)^j) := by simp
    rw [show n = j+(n-j) by omega]
    simp only [Nat.add_sub_cancel_left,coeff_mul_X_pow,exp,coeff_expand (by decide : 0 < 2),coeff_X_add_one_pow]
  rw [OeisA2426.a, Nat.cast_sum]
  simp only [Nat.cast_mul]
  calc
    _ = ∑ j ∈ (range (n+1)).filter (fun j => 2 ∣ j), (n.choose j : R) * (j.choose (j/2) : R) := by
      rw [sum_filter]
      apply sum_congr rfl
      intro j hj
      rw [digit j hj]
      split_ifs <;> ring
    _ = _ := by
      symm
      apply sum_nbij' (fun k => 2*k) (fun j => j/2)
      · intro k hk
        simp only [mem_filter,mem_range] at *
        exact ⟨by omega,dvd_mul_right _ _⟩
      · intro j hj
        simp only [mem_filter,mem_range] at *
        omega
      · intro k _; omega
      · intro j hj
        obtain ⟨_,t,ht⟩ := mem_filter.mp hj
        omega
      · intro k _
        simp

-- Two roots with sum and product one factor the trinomial into linear polynomials.
private lemma central {R : Type*} [CommRing R] (u v : R) (sum : u+v=1) (prod : u*v=1) (p : ℕ) :
    (OeisA2426.a p : R) =
    ∑ i ∈ range (p+1), u^(p-i)*v^i*(p.choose i : R)^2 := by
  have factor : (X^2+1+X : R[X]) = (X+C u)*(X+C v) := by
    calc
      _ = X^2+C (u+v)*X+C (u*v) := by rw [sum,prod]; simp; ring
      _ = _ := by rw [map_add,map_mul]; ring
  rw [← middle R p,factor,mul_pow,coeff_mul]
  let f (i j : ℕ) : R := ((X+C u)^p).coeff i * ((X+C v)^p).coeff j
  calc
    _ = ∑ i ∈ range (p+1), f i (p-i) := Finset.Nat.sum_antidiagonal_eq_sum_range_succ f p
    _ = _ := by
      refine sum_congr rfl (fun i hi => ?_)
      have le : i ≤ p := by simpa using hi
      dsimp only [f]
      rw [coeff_X_add_C_pow,coeff_X_add_C_pow,Nat.choose_symm le,show p-(p-i)=i by omega]
      ring

private lemma powers {R : Type*} [CommRing R] (w : R) (root : w^2=w-1) :
    w^6=1 ∧ w^5=1-w := by
  have cube : w^3 = -1 := by linear_combination (w+1)*root
  constructor
  · rw [show 6=3*2 by decide,pow_mul,cube]; ring
  · rw [show 5=3+2 by decide,pow_add,cube,root]; ring

private lemma prime_middle (p : ℕ) (big : 3 < p) (hp : p.Prime) :
    OeisA2426.a p ≡ 1 [MOD p^2] := by
  let F := ZMod (p^2)
  let K := QuadraticAlgebra F (-1) 1
  let u : K := QuadraticAlgebra.omega
  let v : K := 1-u
  have root : u^2=u-1 := by
    rw [pow_two]
    calc
      _ = algebraMap F K (-1) + algebraMap F K 1 * u := QuadraticAlgebra.omega_mul_omega_eq_algebraMap
      _ = _ := by simp; ring
  have hv : v^2 = v-1 := by dsimp [v]; linear_combination root
  have hu := powers u root
  have hv' := powers v hv
  have su : u+v=1 := by dsimp [v]; ring
  have mu : u*v=1 := by dsimp [v]; linear_combination -root
  have n3 : ¬ 3 ∣ p := by
    intro h
    rcases (Nat.dvd_prime hp).mp h with h|h <;> omega
  have odd := hp.mod_two_eq_one_iff_ne_two.mpr (show p ≠ 2 by omega)
  have res : p%6=1 ∨ p%6=5 := by omega
  have reduce (w : K) (w6 : w^6=1) : w^p=w^(p%6) := by
    calc
      _ = w^(p%6 + 6*(p/6)) := by rw [Nat.mod_add_div]
      _ = _ := by rw [pow_add,pow_mul,w6,one_pow,mul_one]
  have ends : u^p+v^p=1 := by
    rw [reduce u hu.1,reduce v hv'.1]
    rcases res with h|h
    · simpa only [h,pow_one] using su
    · rw [h,hu.2,hv'.2]; dsimp [v]; ring
  have vanish (i : ℕ) (hi : i ≠ 0) (lt : i < p) : (p.choose i : K)^2 = 0 := by
    have d : p^2 ∣ (p.choose i)^2 := pow_dvd_pow_of_dvd (hp.dvd_choose_self hi lt) 2
    have z : ((p.choose i)^2 : F) = 0 := by
      exact_mod_cast ((ZMod.natCast_eq_zero_iff ((p.choose i)^2) (p^2)).mpr d)
    have mapped := congrArg (algebraMap F K) z
    change algebraMap F K ((p.choose i : F)^2) = algebraMap F K 0 at mapped
    rw [map_pow,map_natCast,map_zero] at mapped
    exact mapped
  have eqK : (OeisA2426.a p : K) = 1 := by
    rw [central u v su mu,sum_range_succ]
    have cut : (∑ i ∈ range p, u^(p-i)*v^i*(p.choose i : K)^2) = u^p := by
      rw [sum_eq_single 0]
      · simp
      · intro i hi ne
        rw [vanish i ne (mem_range.mp hi),mul_zero]
      · simp [hp.pos]
    simpa [cut] using ends
  apply (ZMod.natCast_eq_natCast_iff _ _ _).mp
  apply (QuadraticAlgebra.algebraMap_injective (R := F) (a := -1) (b := 1))
  change algebraMap F K (OeisA2426.a p : F) = algebraMap F K ((1 : ℕ) : F)
  rw [map_natCast, map_natCast, Nat.cast_one]
  exact eqK

end OMA.Trinomial

theorem OMA.solution : OMA.R_OeisA2426_conjecture_R1.H1 := OMA.Trinomial.prime_middle
