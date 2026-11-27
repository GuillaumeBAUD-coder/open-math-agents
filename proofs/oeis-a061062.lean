import OMAStatements.S_oeis_a061062

-- Credit: @yuka30240. The counterexample 20879 is due to T. D. Noe.
open OMA.S_oeis_a061062

-- Factor out each squared factorial in turn, starting at the high end of the sum.
private def horner (p : ℕ) : ℕ → ℕ → ℕ
  | 0, x => x
  | n + 1, x => horner p n ((1 + (n + 1)^2 * x) % p)

private lemma horner_spec (p n x : ℕ) :
    horner p n x ≡ (∑ k ∈ Finset.range n, k.factorial^2) + n.factorial^2 * x [MOD p] := by
  induction n generalizing x with
  | zero => simp [horner, Nat.ModEq.refl]
  | succ n ih =>
    refine (ih _).trans ?_
    calc
      _ ≡ _ + n.factorial^2 * (1 + (n + 1)^2 * x) [MOD p] :=
        (Nat.ModEq.refl _).add ((Nat.ModEq.refl _).mul (Nat.mod_modEq _ _))
      _ = _ := by
        rw [Finset.sum_range_succ, Nat.factorial_succ]
        ring

private lemma sum_residue (p n : ℕ) : a n ≡ horner p n 1 [MOD p] := by
  simpa only [a, Finset.sum_range_succ, mul_one] using (horner_spec p n 1).symm

set_option maxRecDepth 150000 in
private lemma checksum : horner 20879 20878 1 = 0 := by decide +kernel

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a061062.main) := by
  intro h
  apply h 20879 (by norm_num) (by decide)
  apply Nat.modEq_zero_iff_dvd.mp
  calc
    a 20878 ≡ horner 20879 20878 1 [MOD 20879] := sum_residue _ _
    _ = 0 := checksum
