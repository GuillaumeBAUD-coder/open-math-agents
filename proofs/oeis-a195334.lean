import OMAStatements.S_oeis_a195334

-- Problem: A195334: Numbers the sum of whose even divisors is 2 times a prime.
-- Upstream: formal-conjectures statements/oeis-a195334.lean:0 (declaration OMA.S_oeis_a195334.main)
-- Credit: @marcelopierry (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

namespace OMA.P_oeis_a195334

open OMA.S_oeis_a195334

lemma evenDivSum_double (m : ℕ) : evenDivSum (2 * m) = 2 * ∑ d ∈ m.divisors, d := by
  unfold evenDivSum
  have h : (2 * m).divisors.filter Even = m.divisors.image (fun e => 2 * e) := by
    ext d
    simp only [Finset.mem_filter, Nat.mem_divisors, Finset.mem_image]
    constructor
    · rintro ⟨⟨hd, hne⟩, ⟨e, rfl⟩⟩
      refine ⟨e, ⟨?_, by omega⟩, by ring⟩
      rw [show e + e = 2 * e by ring] at hd
      exact (Nat.mul_dvd_mul_iff_left (by norm_num)).mp hd
    · rintro ⟨e, ⟨he, hne⟩, rfl⟩
      exact ⟨⟨Nat.mul_dvd_mul_left 2 he, by omega⟩, ⟨e, by ring⟩⟩
  rw [h, Finset.sum_image (fun x _ y _ hxy => by omega), Finset.mul_sum]

lemma evenDivSum_odd (k : ℕ) (hk : ¬ 2 ∣ k) : evenDivSum k = 0 := by
  unfold evenDivSum
  apply Finset.sum_eq_zero
  intro d hd
  simp only [Finset.mem_filter, Nat.mem_divisors] at hd
  exact absurd (dvd_trans (even_iff_two_dvd.mp hd.2) hd.1.1) hk

lemma key (m : ℕ) : InA195334 (2 * m) ↔ InA023194 m := by
  unfold InA195334 InA023194
  rw [evenDivSum_double]
  constructor
  · rintro ⟨q, hq, h⟩
    rw [Nat.mul_left_cancel (by norm_num) h]
    exact hq
  · intro h
    exact ⟨_, h, rfl⟩

lemma even_of (k : ℕ) (h : InA195334 k) : k ∈ Set.range (fun i => 2 * i) := by
  by_cases hk : 2 ∣ k
  · obtain ⟨m, rfl⟩ := hk
    exact ⟨m, rfl⟩
  · obtain ⟨q, hq, h⟩ := h
    rw [evenDivSum_odd k hk] at h
    have := hq.two_le
    omega

lemma solve : ∀ n : ℕ, 1 ≤ n → Nat.nth InA195334 (n - 1) = 2 * Nat.nth InA023194 (n - 1) := by
  intro n _
  have hPQ : (fun i => InA195334 (2 * i)) = InA023194 := funext fun i => propext (key i)
  have hsm : StrictMono (fun i : ℕ => 2 * i) := fun a b h => by
    dsimp only
    omega
  by_cases hc : ∀ hf : (Set.ofPred InA195334).Finite, n - 1 < hf.toFinset.card
  · have := Nat.nth_comp_of_strictMono (p := InA195334) hsm even_of hc
    rw [hPQ] at this
    exact this.symm
  · simp only [not_forall, not_lt] at hc
    obtain ⟨hf, hle⟩ := hc
    have himg : Set.ofPred InA195334 = (fun i => 2 * i) '' Set.ofPred InA023194 := by
      ext k
      constructor
      · intro hk
        obtain ⟨m, rfl⟩ := even_of k hk
        exact ⟨m, (key m).mp hk, rfl⟩
      · rintro ⟨m, hm, rfl⟩
        exact (key m).mpr hm
    have hinj : Set.InjOn (fun i : ℕ => 2 * i) (Set.ofPred InA023194) :=
      fun a _ b _ h => by simpa using h
    have hfQ : (Set.ofPred InA023194).Finite := by
      rw [himg] at hf
      exact Set.Finite.of_finite_image hf hinj
    have hcard : hfQ.toFinset.card = hf.toFinset.card := by
      rw [← Set.ncard_eq_toFinset_card _ hfQ, ← Set.ncard_eq_toFinset_card _ hf, himg,
        Set.ncard_image_of_injOn hinj]
    rw [Nat.nth_of_card_le hf hle, Nat.nth_of_card_le hfQ (hcard ▸ hle)]

end OMA.P_oeis_a195334

theorem OMA.solution : type_of% @OMA.S_oeis_a195334.main := OMA.P_oeis_a195334.solve
