import OMAStatements.S_oeis_a242533
import Mathlib.Tactic

namespace OMA.P_oeis_a242533

open OMA.S_oeis_a242533

private lemma odd_parity_flip {a b : ℕ}
    (hcop : Nat.Coprime (Int.natAbs ((a : ℤ) - (b : ℤ))) (a + b)) :
    a % 2 ≠ b % 2 := by
  intro heq
  have h2_sum : 2 ∣ a + b := by omega
  have h2_diff : 2 ∣ Int.natAbs ((a : ℤ) - (b : ℤ)) := by omega
  have h2_gcd : 2 ∣ Nat.gcd (Int.natAbs ((a : ℤ) - (b : ℤ))) (a + b) :=
    Nat.dvd_gcd h2_diff h2_sum
  rw [hcop.gcd_eq_one] at h2_gcd
  exact absurd (Nat.le_of_dvd (by norm_num) h2_gcd) (by norm_num)

private lemma no_valid_cycle_of_odd {m : ℕ} (hm : Odd m) (σ : Equiv.Perm (Fin m)) :
    ¬ IsValidCycle m σ := by
  intro hvalid
  have hm_pos : 0 < m := by rcases hm with ⟨k, rfl⟩; omega
  have hstep : ∀ i : Fin m,
      ((σ ⟨(i.val + 1) % m, Nat.mod_lt _ hm_pos⟩).val + 1) % 2 =
      1 - ((σ i).val + 1) % 2 := by
    intro i
    have hne := odd_parity_flip (hvalid i)
    omega
  have hind : ∀ k : ℕ, (hk : k < m) →
      ((σ ⟨k, hk⟩).val + 1) % 2 = (((σ ⟨0, hm_pos⟩).val + 1) + k) % 2 := by
    intro k
    induction k with
    | zero =>
      intro _
      simp
    | succ k ih =>
      intro hk
      have hk' : k < m := Nat.lt_of_succ_lt hk
      have hs := hstep ⟨k, hk'⟩
      have hmod : (k + 1) % m = k + 1 := Nat.mod_eq_of_lt hk
      have hfin : (⟨(k + 1) % m, Nat.mod_lt _ hm_pos⟩ : Fin m) = ⟨k + 1, hk⟩ :=
        Fin.ext hmod
      rw [hfin] at hs
      have hprev := ih hk'
      omega
  have hlast_lt : m - 1 < m := by omega
  have hlast := hind (m - 1) hlast_lt
  have hwrap := hstep ⟨m - 1, hlast_lt⟩
  have hmod0 : ((m - 1) + 1) % m = 0 := by
    rw [Nat.sub_add_cancel hm_pos, Nat.mod_self]
  have hfin0 : (⟨((m - 1) + 1) % m, Nat.mod_lt _ hm_pos⟩ : Fin m) = ⟨0, hm_pos⟩ :=
    Fin.ext hmod0
  rw [hfin0] at hwrap
  rcases hm with ⟨t, rfl⟩
  omega

private theorem prove_main : type_of% @OMA.S_oeis_a242533.main := by
  intro m hm
  unfold NPC
  classical
  have hempty : IsEmpty {σ : Equiv.Perm (Fin m) // IsValidCycle m σ} :=
    ⟨fun x => no_valid_cycle_of_odd hm x.1 x.2⟩
  rw [Finset.card_eq_zero, Finset.image_eq_empty]
  exact Finset.univ_eq_empty

end OMA.P_oeis_a242533

theorem OMA.solution : type_of% @OMA.S_oeis_a242533.main :=
  OMA.P_oeis_a242533.prove_main
