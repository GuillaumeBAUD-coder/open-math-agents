import OMAReductions.R_Erdos142_erdos_142_variants_lower_R1_H2_R3_H1_R1

-- Step Erdos142.erdos_142.variants.lower.R1.H2.R3.H1.R1.H2
-- Embed an interval extremizer in ZMod p (2N < p ≤ 4N) via Bertrand's postulate
-- and direction-reversing symmetry so only one ℕ-induction is needed.
-- Credit: @DPS0340

open Finset

theorem OMA.solution : OMA.R_Erdos142_erdos_142_variants_lower_R1_H2_R3_H1_R1.H2 := by
  classical
  intro k N hk hN
  obtain ⟨S, hS, hf, hcard⟩ := Nat.sSup_mem
    (s := {card S | (S) (_ : S ⊆ Icc 1 N) (_ : (S : Set ℕ).IsAPOfLengthFree k)})
    ⟨0, ∅, empty_subset _, fun T hT h => (Set.not_isAPOfLength_empty
      (Nat.cast_pos.mpr (by omega)) (Set.subset_empty_iff.mp (by simpa using hT) ▸ h)).elim, rfl⟩
    ⟨N, by rintro _ ⟨U, hU, -, rfl⟩; simpa using card_le_card hU⟩
  obtain ⟨p, hp, hlo, hhi⟩ := Nat.exists_prime_lt_and_le_two_mul (2 * N) (by omega)
  have : NeZero p := ⟨hp.ne_zero⟩
  have hci : ∀ {u v : ℕ}, u < p → v < p → (u : ZMod p) = (v : ZMod p) → u = v := fun hu hv e => by
    have := congrArg ZMod.val e; rwa [ZMod.val_natCast_of_lt hu, ZMod.val_natCast_of_lt hv] at this
  have hinj : Set.InjOn (Nat.cast : ℕ → ZMod p) (S : Set ℕ) := fun x hx y hy =>
    hci (by have := (mem_Icc.mp (hS hx)).2; omega) (by have := (mem_Icc.mp (hS hy)).2; omega)
  refine ⟨p, hp, S.image Nat.cast, hlo, by omega,
    by change sSup _ = _; rw [← hcard, card_image_of_injOn hinj], ?_⟩
  intro a d hAP
  choose x hxS hxEq using fun i : Fin k => mem_image.mp (hAP i)
  have hxle : ∀ i : Fin k, x i ≤ N := fun i => (mem_Icc.mp (hS (hxS i))).2
  have hmid : ∀ i (hi : i + 2 < k), x ⟨i, by omega⟩ + x ⟨i + 2, hi⟩ = 2 * x ⟨i + 1, by omega⟩ := fun i hi => by
    apply hci (by have := hxle ⟨i, by omega⟩; have := hxle ⟨i + 2, hi⟩; omega)
              (by have := hxle ⟨i + 1, by omega⟩; omega)
    push_cast; rw [hxEq ⟨i, by omega⟩, hxEq ⟨i + 2, hi⟩, hxEq ⟨i + 1, by omega⟩]
    simp only [Nat.cast_add, Nat.cast_ofNat]; ring
  by_cases h01 : x ⟨0, by omega⟩ = x ⟨1, by omega⟩
  · have h0 := hxEq ⟨0, by omega⟩; have h1 := hxEq ⟨1, by omega⟩
    rw [h01] at h0; have : a + d = a := by simpa using h1.symm.trans h0
    simpa using congrArg (· - a) this
  · exfalso
    have hkill : ∀ (y : Fin k → ℕ), (∀ i, y i ∈ S) → y ⟨0, by omega⟩ < y ⟨1, by omega⟩ →
        (∀ i (hi : i + 2 < k), y ⟨i, by omega⟩ + y ⟨i + 2, hi⟩ = 2 * y ⟨i + 1, by omega⟩) → False := by
      intro y hyS hlt hymid
      let s := y ⟨1, by omega⟩ - y ⟨0, by omega⟩
      have hlin : ∀ n (hn : n < k), y ⟨n, hn⟩ = y ⟨0, by omega⟩ + n * s := by
        intro n; induction n using Nat.strong_induction_on with
        | h n ih =>
          intro hn; match n with
          | 0 => simp
          | 1 => simp [s]; omega
          | m + 2 =>
            have := ih m (by omega) (by omega); have := ih (m + 1) (by omega) (by omega)
            have := hymid m hn
            have : (m + 1) * s = m * s + s := by ring
            have : (m + 2) * s = m * s + 2 * s := by ring
            omega
      have hs : 0 < s := by omega
      let T := (range k).image (fun i => y ⟨0, by omega⟩ + i * s)
      have hcT : T.card = k := by
        rw [card_image_of_injective _ fun i j e => Nat.eq_of_mul_eq_mul_right hs (Nat.add_left_cancel e), card_range]
      exact (Nat.one_lt_cast.mpr (by omega : 1 < k)).not_ge (hf (T : Set ℕ) (by
        rintro _ h; obtain ⟨i, hi, rfl⟩ := mem_image.mp h
        rw [← hlin i (mem_range.mp hi)]; exact hyS ⟨i, mem_range.mp hi⟩)
        ⟨y ⟨0, by omega⟩, s, by simp [hcT], by ext u; simp [T]⟩)
    rcases lt_or_gt_of_ne h01 with hlt | hgt
    · exact hkill x hxS hlt hmid
    · have hdec : ∀ n (hn : n + 1 < k), x ⟨n + 1, hn⟩ < x ⟨n, by omega⟩ := by
        intro n; induction n with
        | zero => intro _; exact hgt
        | succ m ih =>
          intro hn; change x ⟨m + 2, hn⟩ < x ⟨m + 1, by omega⟩
          have := hmid m hn; have := ih (by omega); omega
      refine hkill (fun i => x ⟨k - 1 - i.val, by omega⟩) (fun _ => hxS _)
        (by convert hdec (k - 2) (by omega) using 2 <;> ext <;> dsimp <;> omega) fun i hi => ?_
      simpa [show k - 1 - (i + 2) + 2 = k - 1 - i by omega,
             show k - 1 - (i + 2) + 1 = k - 1 - (i + 1) by omega, add_comm] using hmid (k - 1 - (i + 2)) (by omega)
