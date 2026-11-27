import FormalConjectures.OEIS.«1818»

/-! # A reduction for Sun's permanent congruence

The two matrix identities are the Cayley-to-Cauchy formula and the signed
Cauchy permanent evaluation in Yang and Zhang, arXiv:2605.19502, Proposition 17
and Theorem 2. The scalar congruence is proved here by pairing the even
multiples on opposite sides of p.
-/
-- Credit: @steveDOTdigital

namespace OMA.R_OeisA1818_conjecture2_R1
open Finset

-- Each pair (p-r)(p+r) contributes minus the square of one odd r.
private theorem pair_factors (p h : ℕ) (ph : p=h+h+1) :
    (∏ i ∈ range (p-1), 2*((i : ZMod (p^2))+1)) = (-1 : ZMod (p^2))^h * (OeisA1818.a h : ZMod (p^2)) := by
  let f (i : ℕ) : ZMod (p^2) := 2*(i+1)
  have e : p-1=h+h := by omega
  have zero_sq : (p : ZMod (p^2))^2=0 := by
    rw [←Nat.cast_pow]
    exact ZMod.natCast_self _
  have pc : (p : ZMod (p^2)) = h+h+1 := by
    simpa only [Nat.cast_add,Nat.cast_one] using congrArg (fun n : ℕ => (n : ZMod (p^2))) ph
  change (∏ i ∈ range (p-1), f i) = _
  rw [e,prod_range_add,←prod_range_reflect f h,←prod_mul_distrib]
  calc
    _ = ∏ j ∈ range h, (-1 : ZMod (p^2)) * (2*(j : ZMod (p^2))+1)^2 := by
      apply prod_congr rfl
      intro j hj
      have hj' := mem_range.mp hj
      have diff : h-1-j+1+j=h := by omega
      have castd : ((h-1-j : ℕ) : ZMod (p^2))+1+j=h := by
        simpa only [Nat.cast_add,Nat.cast_one] using congrArg (fun n : ℕ => (n : ZMod (p^2))) diff
      let r : ZMod (p^2) := 2*(j : ZMod (p^2))+1
      have left : f (h-1-j)=(p : ZMod (p^2))-r := by
        dsimp [f,r]; linear_combination 2*castd - pc
      have right : f (h+j)=(p : ZMod (p^2))+r := by
        dsimp [f,r]; push_cast; linear_combination -pc
      rw [left,right]
      change (_-r)*(_+r) = -1*r^2
      linear_combination zero_sq
    _ = _ := by
      rw [prod_mul_distrib,prod_pow]
      simp [OeisA1818.a]

/-- The matching expansion relates the two permanents by the product of the even multiples. -/
def H1 : Prop := ∀ p : ℕ, p.Prime → p≠2 →
  Matrix.permanent (fun i j : Fin (p-1) => OeisA1818.fEntry (p:=p) (i.val+1) (j.val+1)) = (∏ i ∈ range (p-1), 2*((i : ZMod (p^2))+1)) * Matrix.permanent (fun i j : Fin (p-1) =>
    if i=j then 0 else ((i.val : ZMod (p^2)) - j.val)⁻¹)

/-- The reciprocal-difference permanent is a sign modulo the square of the prime. -/
def H2 : Prop := ∀ p : ℕ, p.Prime → p≠2 →
  Matrix.permanent (fun i j : Fin (p-1) =>
    if i=j then 0 else ((i.val : ZMod (p^2)) - j.val)⁻¹) = (-1 : ZMod (p^2))^((p-1)/2)

theorem main : H1 → H2 → type_of% @OeisA1818.conjecture2 := by
  intro h1 h2 p hp hn
  let h := (p-1)/2
  obtain ⟨t,ht⟩ := hp.odd_of_ne_two hn
  have ph : p=h+h+1 := by dsimp [h]; omega
  change Matrix.permanent (fun i j : Fin (p-1) => OeisA1818.fEntry (p:=p) (i.val+1) (j.val+1)) = (OeisA1818.a h : ZMod (p^2))
  rw [h1 p hp hn,h2 p hp hn,pair_factors p h ph]
  change (-1 : ZMod (p^2))^h * _ * (-1)^h = _
  rw [mul_right_comm,←mul_pow]
  simp

end OMA.R_OeisA1818_conjecture2_R1
