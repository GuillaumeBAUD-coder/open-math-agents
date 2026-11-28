import OMAReductions.R_HardyLittlewood_second_hardy_littlewood_conjecture_R1

/-!
Proof of `HardyLittlewood.second_hardy_littlewood_conjecture.R1.H1`:
`π(x + y) <= π(x) + π(y)` whenever `2 <= x`, `2 <= y`, and `x <= 26 ∨ y <= 26`.
For `x >= 4` and `2 <= y <= 26`, every prime in `(x, x + y]` is strictly greater than `3`
and therefore coprime to `6`. The count of integers coprime to `6` in `(x, x + y]` depends
only on `x % 6` and `y`, and is checked to be at most `π(y)` for all `r < 6` and `2 <= y <= 26`.
-/

namespace HardyLittlewoodR1H1

open Finset

private lemma primeCounting_eq_card_filter (n : ℕ) :
    Nat.primeCounting n = ((Finset.range (n + 1)).filter Nat.Prime).card := by
  rw [Nat.primeCounting, Nat.primeCounting', Nat.count_eq_card_filter_range]

private lemma primeCounting_add_eq (x y : ℕ) :
    Nat.primeCounting (x + y) =
      Nat.primeCounting x + ((Finset.Ioc x (x + y)).filter Nat.Prime).card := by
  rw [primeCounting_eq_card_filter, primeCounting_eq_card_filter]
  have hsplit : Finset.range (x + y + 1) = Finset.range (x + 1) ∪ Finset.Ioc x (x + y) := by
    ext m
    simp only [mem_range, mem_union, mem_Ioc]
    omega
  have hdisj : Disjoint (Finset.range (x + 1)) (Finset.Ioc x (x + y)) := by
    rw [Finset.disjoint_left]
    intro m hm1 hm2
    simp only [mem_range] at hm1
    simp only [mem_Ioc] at hm2
    omega
  rw [hsplit, Finset.filter_union,
    Finset.card_union_of_disjoint (Finset.disjoint_filter_filter hdisj)]

private lemma coprime_six_of_prime_gt_three {p : ℕ} (hp : p.Prime) (h3 : 3 < p) :
    p.Coprime 6 := by
  have h2 : ¬ 2 ∣ p := by
    intro h
    rcases (Nat.dvd_prime hp).mp h with h1 | h1 <;> omega
  have h3' : ¬ 3 ∣ p := by
    intro h
    rcases (Nat.dvd_prime hp).mp h with h1 | h1 <;> omega
  have hc2 : p.Coprime 2 := (Nat.prime_two.coprime_iff_not_dvd.mpr h2).symm
  have hc3 : p.Coprime 3 := (Nat.prime_three.coprime_iff_not_dvd.mpr h3').symm
  simpa using hc2.mul_right hc3

private lemma card_Ioc_coprime_six (x y : ℕ) :
    ((Finset.Ioc x (x + y)).filter (fun m => m.Coprime 6)).card =
      ((Finset.Icc 1 y).filter (fun k => (x % 6 + k).Coprime 6)).card := by
  refine Finset.card_bij (fun m _ => m - x) ?_ ?_ ?_
  · intro m hm
    simp only [mem_filter, mem_Ioc, mem_Icc] at hm ⊢
    obtain ⟨⟨h1, h2⟩, hcop⟩ := hm
    refine ⟨⟨by omega, by omega⟩, ?_⟩
    have hmod : (x % 6 + (m - x)) % 6 = m % 6 := by omega
    rw [Nat.coprime_iff_gcd_eq_one, Nat.gcd_comm _ 6, Nat.gcd_rec] at hcop ⊢
    rwa [hmod]
  · intro m₁ hm₁ m₂ hm₂ heq
    simp only [mem_filter, mem_Ioc] at hm₁ hm₂
    omega
  · intro k hk
    simp only [mem_filter, mem_Icc, mem_Ioc] at hk ⊢
    obtain ⟨⟨hk1, hk2⟩, hcop⟩ := hk
    refine ⟨x + k, ⟨⟨by omega, by omega⟩, ?_⟩, by omega⟩
    have hmod : (x + k) % 6 = (x % 6 + k) % 6 := by omega
    rw [Nat.coprime_iff_gcd_eq_one, Nat.gcd_comm _ 6, Nat.gcd_rec] at hcop ⊢
    rwa [hmod]

private lemma small_xy :
    ∀ x ∈ Finset.Icc 2 3, ∀ y ∈ Finset.Icc 2 26,
      Nat.primeCounting (x + y) ≤ Nat.primeCounting x + Nat.primeCounting y := by
  decide

private lemma window_coprime_six_le :
    ∀ r ∈ Finset.range 6, ∀ y ∈ Finset.Icc 2 26,
      ((Finset.Icc 1 y).filter (fun k => (r + k).Coprime 6)).card ≤ Nat.primeCounting y := by
  decide

private lemma main_le_26 {x y : ℕ} (hx : 2 ≤ x) (hy : 2 ≤ y) (hy26 : y ≤ 26) :
    HardyLittlewood.SecondHardyLittlewoodConjectureFor x y := by
  unfold HardyLittlewood.SecondHardyLittlewoodConjectureFor
  by_cases hx3 : x ≤ 3
  · exact small_xy x (Finset.mem_Icc.mpr ⟨hx, hx3⟩) y (Finset.mem_Icc.mpr ⟨hy, hy26⟩)
  · rw [primeCounting_add_eq]
    have hsub : (Finset.Ioc x (x + y)).filter Nat.Prime ⊆
        (Finset.Ioc x (x + y)).filter (fun m => m.Coprime 6) := by
      intro m hm
      simp only [mem_filter, mem_Ioc] at hm ⊢
      exact ⟨hm.1, coprime_six_of_prime_gt_three hm.2 (by omega)⟩
    have h1 : ((Finset.Ioc x (x + y)).filter Nat.Prime).card ≤
        ((Finset.Ioc x (x + y)).filter (fun m => m.Coprime 6)).card :=
      Finset.card_le_card hsub
    rw [card_Ioc_coprime_six] at h1
    have h2 := window_coprime_six_le (x % 6) (Finset.mem_range.mpr (Nat.mod_lt x (by decide)))
      y (Finset.mem_Icc.mpr ⟨hy, hy26⟩)
    omega

theorem main_proof : OMA.R_HardyLittlewood_second_hardy_littlewood_conjecture_R1.H1 := by
  intro x y hx hy hxy
  rcases hxy with hx26 | hy26
  · have h := main_le_26 hy hx hx26
    unfold HardyLittlewood.SecondHardyLittlewoodConjectureFor at h ⊢
    rwa [Nat.add_comm, Nat.add_comm (Nat.primeCounting x)]
  · exact main_le_26 hx hy hy26

end HardyLittlewoodR1H1

theorem OMA.solution : OMA.R_HardyLittlewood_second_hardy_littlewood_conjecture_R1.H1 :=
  HardyLittlewoodR1H1.main_proof
