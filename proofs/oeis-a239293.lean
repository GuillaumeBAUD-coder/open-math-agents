import OMAStatements.S_oeis_a239293

open OMA.S_oeis_a239293

lemma key_modeq (n : ℕ) :
    n ^ (n + 1) ≡ n [MOD (n + 1)] ↔ ((-1 : ZMod (n + 1)) ^ (n + 1) = -1) := by
  rw [← ZMod.natCast_eq_natCast_iff]
  push_cast
  have h : ((n : ZMod (n + 1))) = -1 := by
    rw [eq_neg_iff_add_eq_zero]
    exact_mod_cast ZMod.natCast_self (n + 1)
  rw [h]

theorem OMA.solution : type_of% @OMA.S_oeis_a239293.main := by
  intro n hn
  constructor
  · intro ha
    have hne : {c : ℕ | n < c ∧ IsComposite c ∧ n ^ c ≡ n [MOD c]}.Nonempty := by
      by_contra hcon
      rw [Set.not_nonempty_iff_eq_empty] at hcon
      unfold a at ha
      rw [hcon, Nat.sInf_empty] at ha
      omega
    have hmem := Nat.sInf_mem hne
    unfold a at ha
    rw [ha] at hmem
    obtain ⟨-, hcomp, hmod⟩ := hmem
    refine ⟨?_, hcomp⟩
    by_contra hodd
    rw [Nat.not_odd_iff_even] at hodd
    rw [key_modeq, hodd.neg_one_pow] at hmod
    have h2 : ((2 : ℕ) : ZMod (n + 1)) = 0 := by
      have : (1 : ZMod (n + 1)) + 1 = 0 := by
        calc (1 : ZMod (n + 1)) + 1 = 1 - (-1) := by ring
          _ = 0 := by rw [← hmod]; ring
      exact_mod_cast this
    rw [ZMod.natCast_eq_zero_iff] at h2
    have hle := Nat.le_of_dvd (by norm_num) h2
    have : n + 1 = 2 := by omega
    exact hcomp.2 (this ▸ Nat.prime_two)
  · rintro ⟨hodd, hcomp⟩
    have hmem : n + 1 ∈ {c : ℕ | n < c ∧ IsComposite c ∧ n ^ c ≡ n [MOD c]} := by
      refine ⟨by omega, hcomp, ?_⟩
      rw [key_modeq, hodd.neg_one_pow]
    apply le_antisymm (Nat.sInf_le hmem)
    exact le_csInf ⟨_, hmem⟩ (fun c hc => hc.1)
