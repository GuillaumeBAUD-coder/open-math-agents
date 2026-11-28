import OMAReductions.R_Erdos142_erdos_142_variants_lower_R1_H2_R3_H1_R1

theorem OMA.solution : OMA.R_Erdos142_erdos_142_variants_lower_R1_H2_R3_H1_R1.H2 := by
  intro k N hk hN
  obtain ⟨p, hp, hp1, hp2⟩ := Nat.exists_prime_lt_and_le_two_mul (2 * N) (by omega)
  let _ : NeZero p := ⟨hp.ne_zero⟩
  obtain ⟨S, hSI, hSF, hSc⟩ : Erdos142.r k N ∈ _ := Nat.sSup_mem
    ⟨0, ∅, by simp, fun t ht h =>
      (Set.not_isAPOfLength_empty (by norm_cast; omega) ((by simpa using ht : t = ∅) ▸ h)).elim, rfl⟩
    ⟨N, by rintro _ ⟨S, hS, _, rfl⟩; exact (S.card_mono hS).trans (by simp)⟩
  have val_s {s} (hs : s ∈ S) : (s : ZMod p).val = s :=
    have := Finset.mem_Icc.mp (hSI hs); ZMod.val_natCast_of_lt (by omega)
  refine ⟨p, hp, S.image Nat.cast, hp1, by omega, ?_, ?_⟩
  · rw [← hSc, Finset.card_image_of_injOn fun x hx y hy h => by
      simpa [val_s hx, val_s hy] using congrArg ZMod.val h]
  · intro a d had
    let x (n : ℕ) := (a + n * d).val
    have hxS {n} (hn : n < k) : x n ∈ S ∧ 1 ≤ x n ∧ x n ≤ N := by
      rcases Finset.mem_image.mp (had ⟨n, hn⟩) with ⟨s, hs, e⟩
      simpa [x, ← e, val_s hs] using ⟨hs, Finset.mem_Icc.mp (hSI hs)⟩
    have hlin : ∀ n < k, (x n : ℤ) = x 0 + n * ((x 1 : ℤ) - x 0) := by
      intro n; induction n using Nat.strongRecOn with | ind n ih =>
      rcases n with _ | _ | n <;> intro hn
      · simp
      · simp
      · have hz : (((x n : ℤ) + x (n + 2) - 2 * x (n + 1) : ℤ) : ZMod p) = 0 := by
          push_cast [x, ZMod.natCast_zmod_val]; ring
        rcases (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp hz with ⟨q, hq⟩
        have := hxS (by omega : n < k); have := hxS (by omega : n + 1 < k); have := hxS hn
        have h2 : (x n : ℤ) + x (n + 2) = 2 * x (n + 1) := by
          rcases lt_trichotomy q 0 with _ | rfl | _ <;> nlinarith
        have i0 := ih n (by omega) (by omega); have i1 := ih (n + 1) (by omega) (by omega)
        change (x n : ℤ) + x (n + 2) = 2 * x (n + 1) at h2
        push_cast at i1 ⊢; nlinarith
    by_contra hd
    have h01 : x 0 ≠ x 1 := fun h => hd <| by
      have : (x 0 : ZMod p) = x 1 := congrArg _ h
      simpa [x, ZMod.natCast_zmod_val] using this.symm
    obtain ⟨a₀, b, hb, hm⟩ : ∃ a₀ b, 0 < b ∧ ∀ n < k, a₀ + n * b ∈ S := by
      rcases lt_or_gt_of_ne h01 with hlt | hgt
      · refine ⟨x 0, x 1 - x 0, by omega, fun n hn => ?_⟩
        convert (hxS hn).1 using 1; have := hlin n hn; zify [hlt.le]; linarith
      · refine ⟨x (k - 1), x 0 - x 1, by omega, fun n hn => ?_⟩
        convert (hxS (by omega : k - 1 - n < k)).1 using 1
        have h1 := hlin (k - 1) (by omega); have h2 := hlin (k - 1 - n) (by omega)
        rw [Nat.cast_sub (by omega)] at h2; zify [hgt.le]; nlinarith
    let T := (Finset.range k).image fun n => a₀ + n * b
    have hc : ENat.card (T : Set ℕ) = k := by
      simp [T, Finset.card_image_of_injective _ fun u v (h : a₀ + u * b = a₀ + v * b) => by nlinarith]
    have hle := hSF T (fun z hz => by
      rcases Finset.mem_image.mp hz with ⟨n, hn, rfl⟩
      exact hm n (Finset.mem_range.mp hn)) ⟨a₀, b, hc, by ext; simp [T, Nat.cast_lt]⟩
    norm_cast at hle; omega
