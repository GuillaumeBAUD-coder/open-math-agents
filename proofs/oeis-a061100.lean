import OMAStatements.S_oeis_a061100

-- Problem: A061100, closed form for the squares with digital root 4.
-- Credit: @bnb9001

namespace OMA_A061100_Proof

def x (k : ℕ) : ℕ := 9 * (k / 2) + if k % 2 = 0 then 2 else 7

lemma dr_iff (m : ℕ) : OMA.S_oeis_a061100.digitalRoot m = 4 ↔ m % 9 = 4 := by
  unfold OMA.S_oeis_a061100.digitalRoot
  by_cases h : m = 0
  · subst h
    simp
  · rw [if_neg h]
    constructor <;> intro h2 <;> omega

lemma x_strictMono : StrictMono x :=
  strictMono_nat_of_lt_succ fun k => by unfold x; split_ifs <;> omega

lemma f_strictMono : StrictMono (fun k => x k ^ 2) :=
  fun _ _ h => Nat.pow_lt_pow_left (x_strictMono h) two_ne_zero

lemma sq_mod_nine (y : ℕ) : y * y % 9 = 4 ↔ y % 9 = 2 ∨ y % 9 = 7 := by
  rw [Nat.mul_mod]
  have := Nat.mod_lt y (show 9 > 0 by norm_num)
  generalize y % 9 = r at *
  interval_cases r <;> omega

lemma maps (k : ℕ) : IsSquare (x k ^ 2) ∧ OMA.S_oeis_a061100.digitalRoot (x k ^ 2) = 4 := by
  refine ⟨⟨x k, sq (x k)⟩, ?_⟩
  rw [dr_iff, sq, sq_mod_nine]
  unfold x
  split_ifs <;> omega

lemma surj (m : ℕ) (hm : IsSquare m ∧ OMA.S_oeis_a061100.digitalRoot m = 4) : ∃ k, x k ^ 2 = m := by
  obtain ⟨⟨y, rfl⟩, hd⟩ := hm
  rw [dr_iff, sq_mod_nine] at hd
  rcases hd with hd | hd
  · refine ⟨2 * (y / 9), ?_⟩
    have : x (2 * (y / 9)) = y := by unfold x; split_ifs <;> omega
    rw [this, sq]
  · refine ⟨2 * (y / 9) + 1, ?_⟩
    have : x (2 * (y / 9) + 1) = y := by unfold x; split_ifs <;> omega
    rw [this, sq]

lemma nth_eq (k : ℕ) : Nat.nth (fun m => IsSquare m ∧ OMA.S_oeis_a061100.digitalRoot m = 4) k = x k ^ 2 := by
  have hinf : (Set.ofPred (fun m => IsSquare m ∧ OMA.S_oeis_a061100.digitalRoot m = 4)).Infinite :=
    Set.infinite_of_injective_forall_mem f_strictMono.injective (fun k => maps k)
  have hk : ∀ hf : (Set.ofPred (fun m => IsSquare m ∧ OMA.S_oeis_a061100.digitalRoot m = 4)).Finite,
      k < hf.toFinset.card := fun hf => absurd hf hinf
  refine (Nat.eq_nth_of_strictMonoOn_of_mapsTo_of_surjOn (fun k => x k ^ 2) ?_ ?_ ?_ hk).symm
  · intro m hm
    obtain ⟨j, hj⟩ := surj m hm
    exact ⟨j, fun hf => absurd hf hinf, hj⟩
  · intro j _
    exact maps j
  · exact f_strictMono.strictMonoOn _

end OMA_A061100_Proof

open OMA_A061100_Proof OMA.S_oeis_a061100 in
theorem OMA.solution : type_of% @OMA.S_oeis_a061100.main := by
  intro n hn
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  have ha : a (k + 1) = x k ^ 2 := by
    unfold a
    rw [Nat.add_sub_cancel]
    exact nth_eq k
  rw [ha]
  rcases Nat.even_or_odd' k with ⟨q, rfl | rfl⟩
  · have hx : x (2 * q) = 9 * q + 2 := by unfold x; split_ifs <;> omega
    rw [hx]
    refine ⟨fun ⟨r, hr⟩ => by omega, fun _ => ?_⟩
    push_cast
    ring
  · have hx : x (2 * q + 1) = 9 * q + 7 := by unfold x; split_ifs <;> omega
    rw [hx]
    refine ⟨fun _ => ?_, fun ⟨r, hr⟩ => by omega⟩
    push_cast
    ring
