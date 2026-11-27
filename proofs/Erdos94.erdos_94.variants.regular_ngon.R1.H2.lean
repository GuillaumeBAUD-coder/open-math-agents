import OMAReductions.R_Erdos94_erdos_94_variants_regular_ngon_R1

/-! This formalizes the deficit argument outlined in reduction #1183.
Adding two multiplicities modulo n can only decrease their total deficit. -/

open Finset

namespace OMA.DistanceCount

private def loss (n x : ℕ) : ℝ := (x : ℝ) * ((n : ℝ) - x)

private theorem join_loss {n x y : ℕ} (hn : 0 < n) (hx : x ≤ n) (hy : y < n) :
    loss n ((x+y)%n) ≤ loss n x + loss n y := by
  by_cases h : x+y < n
  · rw [Nat.mod_eq_of_lt h]
    simp only [loss,Nat.cast_add]
    nlinarith [mul_nonneg (Nat.cast_nonneg (α:=ℝ) x) (Nat.cast_nonneg (α:=ℝ) y)]
  · have hle : n ≤ x+y := by omega
    have hh : (x+y)%n = x+y-n := by
      rw [Nat.mod_eq_sub_mod hle, Nat.mod_eq_of_lt (by omega)]
    rw [hh]
    simp only [loss,Nat.cast_sub hle,Nat.cast_add]
    have h₁ : (0:ℝ) ≤ (n:ℝ)-x := by exact sub_nonneg.mpr (by exact_mod_cast hx)
    have h₂ : (0:ℝ) ≤ (n:ℝ)-y := by exact sub_nonneg.mpr (by exact_mod_cast hy.le)
    nlinarith [mul_nonneg h₁ h₂]

private theorem collected {α : Type*} [DecidableEq α] (s : Finset α) (w : α → ℕ)
    {n : ℕ} (hn : 0 < n) (hw : ∀ i ∈ s, w i ≤ n) :
    loss n ((∑ i ∈ s, w i)%n) ≤ ∑ i ∈ s, loss n (w i) := by
  induction s using Finset.induction_on with
  | empty => simp [loss]
  | @insert i s hi ih =>
    rw [sum_insert hi, sum_insert hi, ← Nat.add_mod_mod]
    exact (join_loss hn (hw i (by simp)) (Nat.mod_lt _ hn)).trans
      (add_le_add_right (ih fun j hj => hw j (by simp [hj])) _)

private theorem even_remainder (k : ℕ) (hk : 0 < k) : (2*k).choose 2 % (2*k) = k := by
  have h : 2*k-1 = 2*(k-1)+1 := by omega
  rw [Nat.choose_two_right]
  have he : 2*k*(2*k-1)/2 = k + (k-1)*(2*k) := by
    rw [Nat.mul_assoc, Nat.mul_div_cancel_left _ (by decide : 0<2), h]
    ring
  rw [he, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (by omega)]

end OMA.DistanceCount

open OMA.DistanceCount

theorem OMA.solution : OMA.R_Erdos94_erdos_94_variants_regular_ngon_R1.H2 := by
  classical
  intro n P hcard hcap
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have hP := Finset.card_eq_zero.mp hcard
    subst P
    simp [distanceSet, distanceMultiplicity]
  let s := distanceSet P
  let w := distanceMultiplicity P
  have ht : ∑ i ∈ s, w i = n.choose 2 := by simpa [s,w,hcard] using sum_distanceMultiplicity P
  have hreal : (∑ i ∈ s, (w i : ℝ)) = (n:ℝ)*((n:ℝ)-1)/2 := by
    rw [← Nat.cast_sum, ht, Nat.cast_choose_two]
  have hsum := collected s w hn hcap
  have hident : ∑ i ∈ s, loss n (w i) = (n:ℝ)*(∑ i ∈ s, (w i : ℝ)) - ∑ i ∈ s, (w i:ℝ)^2 := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    unfold loss
    ring
  rw [ht,hident,hreal] at hsum
  change (∑ i ∈ s, (w i : ℝ)^2) ≤ _
  split
  · have hz : 0 ≤ loss n (n.choose 2 % n) := by
      apply mul_nonneg (Nat.cast_nonneg _)
      exact sub_nonneg.mpr (by exact_mod_cast (Nat.mod_lt (n.choose 2) hn).le)
    nlinarith
  · rename_i h
    let k := n/2
    have he : n = 2*k := by dsimp [k]; omega
    have hk : 0 < k := by omega
    have hr : n.choose 2 % n = k := by simpa only [he] using even_remainder k hk
    rw [hr] at hsum
    have hnreal : (n:ℝ) = 2*(k:ℝ) := by exact_mod_cast he
    unfold loss at hsum
    rw [hnreal] at hsum ⊢
    nlinarith
