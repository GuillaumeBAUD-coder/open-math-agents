import OMAStatements.S_mse_4989540

-- Problem: Conjecture: the integer cosets of ideals are Noetherian
-- Upstream: formal-conjectures statements/mse-4989540.lean:0 (declaration OMA.S_mse_4989540.main)
-- Credit: @amtamaddon (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

open OMA.S_mse_4989540

def OMA.Cn (n : ℕ) : Finset (ℤ × ℤ) :=
  (Finset.range n).image (fun k => ((2:ℤ)^k, (2:ℤ)^(k+1)))

def OMA.Sn (n : ℕ) : Set ℤ := {x | ∃ c ∈ OMA.Cn n, c.2 ∣ x - c.1}

theorem OMA.Cn_ne (n : ℕ) : ∀ c ∈ OMA.Cn n, c.2 ≠ 0 := by
  intro c hc
  simp only [OMA.Cn, Finset.mem_image, Finset.mem_range] at hc
  obtain ⟨k, hk, rfl⟩ := hc
  dsimp only
  positivity

theorem OMA.solution : type_of% @OMA.S_mse_4989540.main := by
  refine ⟨OMA.Sn, ?_, ?_, ?_⟩
  · apply strictMono_nat_of_lt_succ
    intro n
    show OMA.Sn n ⊂ OMA.Sn (n+1)
    refine ⟨?_, ?_⟩
    · rintro x ⟨c, hc, hx⟩
      refine ⟨c, ?_, hx⟩
      simp only [OMA.Cn, Finset.mem_image, Finset.mem_range] at hc ⊢
      obtain ⟨k, hk, rfl⟩ := hc
      exact ⟨k, by omega, rfl⟩
    · intro h
      have h1 : (2:ℤ)^n ∈ OMA.Sn (n+1) := by
        refine ⟨((2:ℤ)^n, (2:ℤ)^(n+1)), ?_, ?_⟩
        · simp only [OMA.Cn, Finset.mem_image, Finset.mem_range]
          exact ⟨n, by omega, rfl⟩
        · simp
      obtain ⟨c, hc, hx⟩ := h h1
      simp only [OMA.Cn, Finset.mem_image, Finset.mem_range] at hc
      obtain ⟨k, hk, rfl⟩ := hc
      dsimp only at hx
      have h2 : (2:ℤ)^(k+1) ∣ (2:ℤ)^n := pow_dvd_pow 2 (by omega)
      have h3 : (2:ℤ)^(k+1) ∣ (2:ℤ)^k := by
        have h5 := dvd_sub h2 hx
        simpa using h5
      have h4 := Int.le_of_dvd (by positivity) h3
      have h6 : (2:ℤ)^(k+1) = 2 * 2^k := by ring
      have h7 : (0:ℤ) < 2^k := by positivity
      linarith
  · intro n
    exact ⟨OMA.Cn n, OMA.Cn_ne n, rfl⟩
  · intro n
    refine ⟨(OMA.Cn n : Set (ℤ × ℤ)), ?_, rfl⟩
    intro c hc
    exact OMA.Cn_ne n c (Finset.mem_coe.1 hc)
