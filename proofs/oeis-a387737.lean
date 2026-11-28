import OMAStatements.S_oeis_a387737
import Mathlib.Data.Fin.Rev
import Mathlib.Data.Int.Interval

/-! Adding i − (r−1−i) to smaller part i opens two places between
adjacent parts. Reversing the indices pairs opposite displacements,
so that their sum is zero. The exceptional case is a balanced two-part
partition. -/

open Finset OMA.S_oeis_a387737
namespace OMA.Partition387737

lemma offsetFormula {r : ℕ} (i : Fin r) :
    (i.val : ℤ) - (i.rev.val : ℤ) = 2 * (i.val : ℤ) + 1 - (r : ℤ) := by
  have h := i.isLt
  change (i.val : ℤ) - ((r - (i.val + 1) : ℕ) : ℤ) = _
  omega

def offset {r : ℕ} (i : Fin r) : ℤ := (i.val : ℤ) - (i.rev.val : ℤ)

lemma offset_sum (r : ℕ) : ∑ i : Fin r, offset i = 0 := by
  simp only [offset, sum_sub_distrib]
  have e := Equiv.sum_comp (Fin.revPerm (n := r)) (fun i : Fin r => (i.val : ℤ))
  change (∑ i : Fin r, (i.rev.val : ℤ)) = _ at e
  omega

lemma forward {n r : ℕ} (hr : 2 ≤ r) (f : Fin r → ℤ) (h : A n r f) :
    B n r (fun i => f i + offset i) := by
  obtain ⟨hL, hmin, hmono, hsum⟩ := h
  have eqsum : ∑ i, (f i + offset i) = ∑ i, f i := by rw [sum_add_distrib, offset_sum, add_zero]
  have eqL : largest n (fun i => f i + offset i) = largest n f := by simp only [largest, eqsum]
  unfold B
  rw [eqsum, eqL]
  refine ⟨by omega, ?_, ?_, ?_, hsum⟩
  · intro i
    have hi := hmin i
    simp only [offset, offsetFormula]
    omega
  · intro i j hij
    have hm := hmono hij
    simp only [offset, offsetFormula]
    omega
  · intro i
    let : Nontrivial (Fin r) := Fin.nontrivial_iff_two_le.mpr hr
    obtain ⟨j, hji⟩ := exists_ne i
    have hadd := Finset.add_le_sum (s := (univ : Finset (Fin r))) (f := f)
      (fun k _ => by have := hmin k; omega) (mem_univ i) (mem_univ j) (Ne.symm hji)
    have hj := hmin j
    have hi := i.isLt
    simp only [offset, offsetFormula]
    omega

lemma backward {n r : ℕ} (hr : 2 ≤ r) (g : Fin r → ℤ) (h : B n r g) :
    A n r (fun i => g i - offset i) := by
  obtain ⟨hL, hmin, hgap, _, hsum⟩ := h
  have eqsum : ∑ i, (g i - offset i) = ∑ i, g i := by rw [sum_sub_distrib, offset_sum, sub_zero]
  have eqL : largest n (fun i => g i - offset i) = largest n g := by simp only [largest, eqsum]
  let z : Fin r := ⟨0, by omega⟩
  have hz : (z.val : ℤ) = 0 := rfl
  have lower : ∀ i, (r : ℤ) + 1 ≤ g i - offset i := by
    intro i
    have hh := hgap z i (show z.val ≤ i.val from Nat.zero_le _)
    have hm := hmin z
    simp only [offset, offsetFormula]
    omega
  unfold A
  rw [eqL, eqsum]
  refine ⟨?_, lower, ?_, hsum⟩
  · have hzsum := Finset.single_le_sum (s := (univ : Finset (Fin r)))
      (f := fun i => g i - offset i) (fun k _ => by have := lower k; omega) (mem_univ z)
    rw [eqsum] at hzsum
    have hh := lower z
    omega
  · intro i j hij
    have hh := hgap i j hij
    simp only [offset, offsetFormula]
    omega

lemma regular (n r : ℕ) (hr : 2 ≤ r) : countA n r = countB n r := by
  apply Nat.card_congr
  exact {
    toFun := fun f => ⟨fun i => f.val i + offset i, forward hr f.val f.property⟩
    invFun := fun g => ⟨fun i => g.val i - offset i, backward hr g.val g.property⟩
    left_inv := fun f => Subtype.ext (funext fun i => add_sub_cancel_right (f.val i) (offset i))
    right_inv := fun g => Subtype.ext (funext fun i => sub_add_cancel (g.val i) (offset i)) }

lemma zeroCounts (n : ℕ) (hn : 4 ≤ n) : countA n 0 = countB n 0 := by
  unfold countA countB
  apply Nat.card_congr
  apply Equiv.subtypeEquivRight
  intro f
  have hm : Monotone f := fun i => Fin.elim0 i
  simp [A, B, largest, hm]
  omega

lemma countInterval {P : (Fin 1 → ℤ) → Prop} {h : ℤ}
    (hp : ∀ f, P f ↔ f 0 ∈ Finset.Icc (2 : ℤ) h) :
    Nat.card {f // P f} = (h + 1 - 2).toNat := by
  let e : {f // P f} ≃ ↥(Finset.Icc (2 : ℤ) h) :=
    { toFun := fun f => ⟨f.val 0, (hp f.val).mp f.property⟩
      invFun := fun v => ⟨fun _ => v.val, (hp (fun _ => v.val)).mpr v.property⟩
      left_inv := fun f => by
        apply Subtype.ext
        funext i
        exact congrArg f.val (Subsingleton.elim 0 i)
      right_inv := fun _ => rfl }
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_coe, Int.card_Icc]

lemma oneCounts (n : ℕ) (hn : 4 ≤ n) : countA n 1 = countB n 1 + 1 := by
  have hA : countA n 1 = ((n : ℤ) / 2 + 1 - 2).toNat := by
    apply countInterval
    intro f
    have hm : Monotone f := fun i j _ => by rw [Subsingleton.elim i j]
    simp [A, largest, Fin.forall_fin_one, hm]
    omega
  have hB : countB n 1 = (((n : ℤ) - 2) / 2 + 1 - 2).toNat := by
    apply countInterval
    intro f
    simp [B, largest, Fin.forall_fin_one]
    omega
  omega

end OMA.Partition387737

open OMA.Partition387737

theorem OMA.solution : type_of% @OMA.S_oeis_a387737.main := by
  intro n hn
  calc
    (∑ r ∈ range n, countA n r) = ∑ r ∈ range n, (countB n r + if r = 1 then 1 else 0) := by
      apply sum_congr rfl
      intro r _
      by_cases h : r = 1
      · simpa [h] using oneCounts n hn
      by_cases hz : r = 0
      · simpa [hz] using zeroCounts n hn
      simpa [h] using regular n r (by omega)
    _ = _ := by rw [sum_add_distrib]; simp [show 1 < n by omega]
