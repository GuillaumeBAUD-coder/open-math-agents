import OMAReductions.R_HardyLittlewood_second_hardy_littlewood_conjecture_R1

/-!
# Proof of `HardyLittlewood.second_hardy_littlewood_conjecture.R1.H1`

Proves the second Hardy–Littlewood inequality `π(x + y) ≤ π(x) + π(y)` whenever `2 ≤ x`, `2 ≤ y`,
and `min x y ≤ 26`.

By symmetry we assume `x ≤ 26`. For `y ≤ 30`, the inequality holds by finite verification on
`2 ≤ x ≤ 26`, `2 ≤ y ≤ 30`. For `y > 30`, every prime `p ∈ (y, y + x]` exceeds `30` and is
therefore coprime to `30`, so `π(x + y) - π(y)` is at most the number of integers in
`[y % 30 + 1, y % 30 + x]` coprime to `30`, which is verified to be at most `π(x)` for all
`2 ≤ x ≤ 26` and all residues `r < 30`.
-/

open Finset

namespace HardyLittlewoodH1Proof

private def primeCountList (n : ℕ) : ℕ :=
  ((Finset.range (n + 1)).filter Nat.Prime).card

private lemma primeCountList_eq_primeCounting (n : ℕ) :
    primeCountList n = Nat.primeCounting n := by
  unfold primeCountList Nat.primeCounting Nat.primeCounting'
  rw [Nat.count_eq_card_filter_range]

private lemma wheel30_bound :
    ∀ x : Fin 27, 2 ≤ x.val → ∀ r : Fin 30,
      ((Finset.Icc 1 x.val).filter (fun k => Nat.Coprime (r.val + k) 30)).card ≤
        primeCountList x.val := by
  decide

private lemma small_y_bound :
    ∀ x : Fin 27, 2 ≤ x.val → ∀ y : Fin 31, 2 ≤ y.val →
      primeCountList (x.val + y.val) ≤ primeCountList x.val + primeCountList y.val := by
  decide

private lemma second_hl_of_le_26 {x y : ℕ} (hx2 : 2 ≤ x) (hx26 : x ≤ 26) (hy2 : 2 ≤ y) :
    Nat.primeCounting (x + y) ≤ Nat.primeCounting x + Nat.primeCounting y := by
  by_cases hy30 : y ≤ 30
  · rw [← primeCountList_eq_primeCounting, ← primeCountList_eq_primeCounting,
      ← primeCountList_eq_primeCounting]
    exact small_y_bound ⟨x, by omega⟩ hx2 ⟨y, by omega⟩ hy2
  · have hy_gt : 30 < y := by omega
    rw [← primeCountList_eq_primeCounting, ← primeCountList_eq_primeCounting,
      ← primeCountList_eq_primeCounting]
    unfold primeCountList
    have hsplit : (Finset.range (x + y + 1)).filter Nat.Prime =
        (Finset.range (y + 1)).filter Nat.Prime ∪
        (Finset.Icc (y + 1) (y + x)).filter Nat.Prime := by
      ext p
      by_cases hp : p.Prime <;> simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_union,
        Finset.mem_Icc, hp, and_true, and_false, or_self]
      omega
    have hdisj : Disjoint ((Finset.range (y + 1)).filter Nat.Prime)
        ((Finset.Icc (y + 1) (y + x)).filter Nat.Prime) := by
      rw [Finset.disjoint_left]
      intro p hp1 hp2
      have h1 := (Finset.mem_range.mp (Finset.mem_filter.mp hp1).1)
      have h2 := (Finset.mem_Icc.mp (Finset.mem_filter.mp hp2).1).1
      omega
    rw [hsplit, Finset.card_union_of_disjoint hdisj, add_comm]
    have hinterval : ((Finset.Icc (y + 1) (y + x)).filter Nat.Prime).card ≤
        ((Finset.Icc 1 x).filter (fun k => Nat.Coprime (y % 30 + k) 30)).card := by
      refine Finset.card_le_card_of_injOn (fun p => p - y) ?_ ?_
      · intro p hp
        dsimp only
        have hpIcc := Finset.mem_Icc.mp (Finset.mem_filter.mp hp).1
        have hpPrime := (Finset.mem_filter.mp hp).2
        refine Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨by omega, by omega⟩, ?_⟩
        have hp30 : 30 < p := by omega
        have hcop_p : Nat.Coprime p 30 := by
          rw [Nat.Prime.coprime_iff_not_dvd hpPrime]
          intro hdvd
          have hle := Nat.le_of_dvd (by norm_num : 0 < 30) hdvd
          omega
        have hmod : (y % 30 + (p - y)) % 30 = p % 30 := by
          have h1 : y + (p - y) = p := by omega
          calc (y % 30 + (p - y)) % 30 = (y + (p - y)) % 30 := by rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
            _ = p % 30 := by rw [h1]
        rw [Nat.coprime_iff_gcd_eq_one, Nat.gcd_comm, Nat.gcd_rec, hmod, ← Nat.gcd_rec, Nat.gcd_comm]
        exact hcop_p.gcd_eq_one
      · intro p₁ hp₁ p₂ hp₂ heq
        dsimp only at heq
        have h1 := (Finset.mem_Icc.mp (Finset.mem_filter.mp hp₁).1).1
        have h2 := (Finset.mem_Icc.mp (Finset.mem_filter.mp hp₂).1).1
        omega
    have hw := wheel30_bound ⟨x, by omega⟩ hx2 ⟨y % 30, Nat.mod_lt y (by norm_num)⟩
    have hfin : ((Finset.Icc (y + 1) (y + x)).filter Nat.Prime).card ≤ primeCountList x :=
      hinterval.trans hw
    unfold primeCountList at hfin
    omega

end HardyLittlewoodH1Proof

theorem OMA.solution : OMA.R_HardyLittlewood_second_hardy_littlewood_conjecture_R1.H1 := by
  intro x y hx hy hle
  unfold HardyLittlewood.SecondHardyLittlewoodConjectureFor
  rcases hle with hx26 | hy26
  · exact HardyLittlewoodH1Proof.second_hl_of_le_26 hx hx26 hy
  · rw [add_comm x y, add_comm (Nat.primeCounting x)]
    exact HardyLittlewoodH1Proof.second_hl_of_le_26 hy hy26 hx
