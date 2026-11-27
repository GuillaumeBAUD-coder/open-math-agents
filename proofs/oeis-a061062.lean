import OMAStatements.S_oeis_a061062

-- Credit: @anmolspace. T. D. Noe reported the counterexample on OEIS in 2004.

open OMA.S_oeis_a061062

private def scan (p : ℕ) : ℕ → ℕ → ℕ → ℕ → ℕ × ℕ
  | 0, _, f, s => (f, s)
  | len+1, k, f, s =>
    let g := (k+1)*f % p
    scan p len (k+1) g ((s+g^2) % p)

private lemma a_succ (k : ℕ) : a (k+1) = a k + (k+1).factorial^2 := by
  unfold a
  rw [Finset.sum_range_succ]

private lemma scan_eq (p len k : ℕ) :
    scan p len k (k.factorial % p) (a k % p) =
      ((k + len).factorial % p, a (k + len) % p) := by
  induction len generalizing k with
  | zero => rfl
  | succ len ih =>
    rw [scan]
    have hf : ((k+1)*(k.factorial % p)) % p = (k+1).factorial % p :=
      (Nat.ModEq.refl (k+1)).mul (Nat.mod_modEq _ _)
    have hs : ((a k % p) + ((k+1).factorial % p)^2) % p = a (k+1) % p := by
      rw [a_succ]
      exact (Nat.mod_modEq _ _).add ((Nat.mod_modEq _ _).pow 2)
    rw [hf, hs, ih, show k+1+len=k+(len+1) by omega]

set_option maxRecDepth 150000 in
set_option maxHeartbeats 3000000 in
private lemma checksum : (scan 20879 20878 0 1 1).2 = 0 := by decide +kernel

private lemma scan_sum (p len k : ℕ) :
    (scan p len k (k.factorial % p) (a k % p)).2 = a (k+len) % p :=
  congrArg Prod.snd (scan_eq p len k)

set_option maxRecDepth 150000 in
theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a061062.main) := by
  intro h
  have f0 : (0 : ℕ).factorial % 20879 = 1 := by decide
  have s0 : a 0 % 20879 = 1 := by decide
  have correct := scan_sum 20879 20878 0
  simp only [f0, s0, Nat.zero_add] at correct
  have residue : a 20878 % 20879 = 0 := by
    calc
      _ = (scan 20879 20878 0 1 1).2 := correct.symm
      _ = 0 := checksum
  apply h 20879 (by norm_num) (by decide)
  rw [show 20879-1=20878 by decide]
  exact Nat.dvd_of_mod_eq_zero residue
