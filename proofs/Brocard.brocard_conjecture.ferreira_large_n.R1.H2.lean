import OMAReductions.R_Brocard_brocard_conjecture_ferreira_large_n_R1

/-! Adapted from the proof of Oppermann.oppermann_implies_brocard in
google-deepmind/formal-conjectures, FormalConjectures/Wikipedia/Oppermann.lean, commit
9097e2f90e66d2f6244209cb1c07f7120d17ec53. Copyright 2025 The Formal Conjectures Authors.
Used under the Apache License, Version 2.0. The change is that Oppermann's conjecture is
only assumed from X on and is used at the three points p, p + 1, p + 2 above X. -/

theorem OMA.solution : OMA.R_Brocard_brocard_conjecture_ferreira_large_n_R1.H2 := by
  intro X P n hn hXn
  obtain ⟨prev, hprev_def⟩ : ∃ prev, prev = n.nth Nat.Prime := ⟨_, rfl⟩
  obtain ⟨next, hnext_def⟩ : ∃ next, next = (n + 1).nth Nat.Prime := ⟨_, rfl⟩
  rw [← hprev_def] at hXn ⊢
  rw [← hnext_def]
  have hprev_prime : prev.Prime := hprev_def ▸ Nat.prime_nth_prime n
  have hnext_prime : next.Prime := hnext_def ▸ Nat.prime_nth_prime (n + 1)
  have hprev_ge : 3 ≤ prev := by
    rw [hprev_def, ← Nat.nth_prime_one_eq_three]
    exact (Nat.nth_le_nth Nat.infinite_setOfPred_prime).mpr hn
  have hlt : prev < next := by
    rw [hprev_def, hnext_def]
    exact Nat.nth_strictMono Nat.infinite_setOfPred_prime (Nat.lt_succ_self n)
  have hgap : prev + 2 ≤ next := by
    rcases hprev_prime.odd_of_ne_two (by omega) with ⟨k, hk⟩
    rcases hnext_prime.odd_of_ne_two (by omega) with ⟨m, hm⟩
    omega
  obtain ⟨_, p1, hp1mem, hp1p⟩ := P prev hXn
  obtain ⟨⟨p2, hp2mem, hp2p⟩, p3, hp3mem, hp3p⟩ := P (prev + 1) (by omega)
  obtain ⟨p4, hp4mem, hp4p⟩ := (P (prev + 2) (by omega)).1
  simp only [Finset.mem_Ioo, show prev + 1 - 1 = prev from rfl,
    show prev + 2 - 1 = prev + 1 from rfl, show prev + 1 + 1 = prev + 2 from rfl]
    at hp1mem hp2mem hp3mem hp4mem
  have hsq : (prev + 2) ^ 2 ≤ next ^ 2 := Nat.pow_le_pow_left hgap 2
  have hsq1 : (prev + 1) ^ 2 ≤ next ^ 2 := Nat.pow_le_pow_left (by omega) 2
  have hb0 : prev * (prev + 1) < (prev + 1) ^ 2 := by nlinarith
  have hb1 : (prev + 1) * (prev + 2) < (prev + 2) ^ 2 := by nlinarith
  have h12 : p1 < p2 := by linarith [hp1mem.2, hp2mem.1]
  have h23 : p2 < p3 := by linarith [hp2mem.2, hp3mem.1]
  have h34 : p3 < p4 := by linarith [hp3mem.2, hp4mem.1]
  refine ((show ({p1, p2, p3, p4} : Finset ℕ).card = 4 from ?_) ▸
    Finset.card_le_card (s := {p1, p2, p3, p4}) ?_)
  · simp [Finset.card_insert_of_notMem, h12.ne, (h12.trans h23).ne,
      (h12.trans (h23.trans h34)).ne, h23.ne, (h23.trans h34).ne, h34.ne]
  · intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl <;>
      refine Finset.mem_filter.mpr ⟨Finset.mem_Ioo.mpr ⟨?_, ?_⟩, by assumption⟩ <;>
      linarith [hp1mem.1, hp1mem.2, hp2mem.1, hp2mem.2, hp3mem.1, hp3mem.2,
        hp4mem.1, hp4mem.2, hb0, hb1, hsq, hsq1]
