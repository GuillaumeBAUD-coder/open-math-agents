import OMAStatements.S_oeis_a045798

namespace OMA.P_oeis_a045798

private def f (k : ℕ) : ℕ :=
  20 * (k / 4) +
    if k % 4 = 0 then 11
    else if k % 4 = 1 then 13
    else if k % 4 = 2 then 17
    else 19

private lemma gcd_mod20_ten (k : ℕ) : Nat.gcd k 10 = Nat.gcd (k % 20) 10 := by
  have hdvd : (10 : ℕ) ∣ 20 * (k / 20) := dvd_mul_of_dvd_left (by decide : (10 : ℕ) ∣ 20) _
  have hsplit : k % 20 + 20 * (k / 20) = k := Nat.mod_add_div k 20
  apply Nat.dvd_antisymm
  · apply Nat.dvd_gcd _ (Nat.gcd_dvd_right k 10)
    have hg10 : Nat.gcd k 10 ∣ 20 * (k / 20) := dvd_trans (Nat.gcd_dvd_right k 10) hdvd
    have hgk : Nat.gcd k 10 ∣ k % 20 + 20 * (k / 20) := by
      rw [hsplit]
      exact Nat.gcd_dvd_left k 10
    exact (Nat.dvd_add_left hg10).mp hgk
  · apply Nat.dvd_gcd _ (Nat.gcd_dvd_right (k % 20) 10)
    have hg10 : Nat.gcd (k % 20) 10 ∣ 20 * (k / 20) :=
      dvd_trans (Nat.gcd_dvd_right (k % 20) 10) hdvd
    conv_rhs => rw [← hsplit]
    exact dvd_add (Nat.gcd_dvd_left (k % 20) 10) hg10

private lemma oddish_iff (k : ℕ) :
    OMA.S_oeis_a045798.oddish k ↔ k % 20 = 11 ∨ k % 20 = 13 ∨ k % 20 = 17 ∨ k % 20 = 19 := by
  have hdec : ∀ r : Fin 20,
      (Nat.Coprime r.1 10 ∧ (r.1 / 10 % 10) % 2 = 1 ↔
        r.1 = 11 ∨ r.1 = 13 ∨ r.1 = 17 ∨ r.1 = 19) := by decide
  have hred : OMA.S_oeis_a045798.oddish k ↔
      Nat.Coprime (k % 20) 10 ∧ ((k % 20) / 10 % 10) % 2 = 1 := by
    rw [OMA.S_oeis_a045798.oddish, Nat.coprime_iff_gcd_eq_one,
      Nat.coprime_iff_gcd_eq_one, gcd_mod20_ten]
    have htens : (k / 10 % 10) % 2 = ((k % 20) / 10 % 10) % 2 := by omega
    rw [htens]
  rw [hred]
  exact hdec ⟨k % 20, Nat.mod_lt k (by decide)⟩

private lemma f_oddish (k : ℕ) : OMA.S_oeis_a045798.oddish (f k) := by
  rw [oddish_iff]
  dsimp [f]
  split_ifs <;> omega

private lemma f_strictMono : StrictMono f := by
  intro a b hab
  dsimp [f]
  split_ifs <;> omega

private lemma f_add_four (k : ℕ) : f (k + 4) = f k + 20 := by
  dsimp [f]
  rw [Nat.add_mod_right, Nat.add_div_right _ (by decide)]
  omega

private lemma nth_oddish_eq (n : ℕ) : Nat.nth OMA.S_oeis_a045798.oddish n = f n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rw [Nat.nth_eq_sInf]
    have hmem : f n ∈ {x | OMA.S_oeis_a045798.oddish x ∧
        ∀ k < n, Nat.nth OMA.S_oeis_a045798.oddish k < x} := by
      refine ⟨f_oddish n, fun k hk => ?_⟩
      rw [ih k hk]
      exact f_strictMono hk
    apply le_antisymm
    · exact Nat.sInf_le hmem
    · refine le_csInf ⟨f n, hmem⟩ ?_
      rintro x ⟨hx_od, hx_gt⟩
      rw [oddish_iff] at hx_od
      cases n with
      | zero =>
        change f 0 ≤ x
        dsimp [f]
        omega
      | succ m =>
        have hlt : f m < x := by
          rw [← ih m (Nat.lt_succ_self m)]
          exact hx_gt m (Nat.lt_succ_self m)
        dsimp [f] at hlt ⊢
        split_ifs at hlt ⊢ <;> omega

end OMA.P_oeis_a045798

theorem OMA.solution : type_of% @OMA.S_oeis_a045798.main := by
  intro n hn
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hn
  have ha : ∀ m : ℕ, OMA.S_oeis_a045798.a m = OMA.P_oeis_a045798.f (m - 1) :=
    fun m => OMA.P_oeis_a045798.nth_oddish_eq (m - 1)
  rw [ha, ha, ha, ha]
  have h1 : k + 6 - 1 = (k + 1) + 4 := by omega
  have h2 : k + 6 - 1 - 1 = k + 4 := by omega
  have h3 : k + 6 - 4 - 1 = k + 1 := by omega
  have h4 : k + 6 - 5 - 1 = k := by omega
  rw [h2, h1, h3, h4, OMA.P_oeis_a045798.f_add_four, OMA.P_oeis_a045798.f_add_four]
  omega
