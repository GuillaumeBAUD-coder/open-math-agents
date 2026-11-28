import FormalConjectures.ErdosProblems.«292»

/-! For n = p^k, every other denominator has p-adic valuation below k, so the rest of the sum has valuation above -k and the total has valuation -k, not 0. -/

open Finset

theorem OMA.solution : type_of% @Erdos292.erdos_292.variants.prime_pow := by
  rintro _ ⟨S, hS, hn, hsum⟩ hpow
  obtain ⟨p, k, hp, hk, rfl⟩ := (isPrimePow_nat_iff _).mp hpow
  have := Fact.mk hp
  let F (d : ℕ) : ℚ := 1 / (max 1 d : ℕ)
  have hF d : 0 < F d := by positivity
  have hv {d} (h : d ∈ S) : padicValRat p (F d) = -padicValNat p d := by
    dsimp only [F]
    rw [max_eq_right (mem_Icc.1 (hS h)).1, one_div, padicValRat.inv, padicValRat.of_nat]
  have hs : F (p ^ k) + ∑ d ∈ S.erase (p ^ k), F d = 1 := by
    rw [add_sum_erase _ _ hn, ← hsum]
    exact sum_congr rfl fun d h => by simp [F, (mem_Icc.1 (hS h)).1]
  have key : padicValRat p (F (p ^ k)) = -k := by rw [hv hn, padicValNat.prime_pow]
  rcases (S.erase (p ^ k)).eq_empty_or_nonempty with he | hne
  · rw [he, sum_empty, add_zero] at hs
    rw [hs, padicValRat.one] at key
    omega
  have h := padicValRat.add_eq_of_lt (by rw [hs]; norm_num) (hF _).ne'
    (sum_pos (fun d _ => hF d) hne).ne' (padicValRat.lt_sum_of_lt hne (fun d hd => by
      obtain ⟨h1, h2⟩ := mem_Icc.1 (hS (mem_of_mem_erase hd))
      have : ¬p ^ k ∣ d := fun h => ne_of_mem_erase hd (le_antisymm h2 (Nat.le_of_dvd h1 h))
      rw [padicValNat_dvd_iff_le (by omega)] at this
      rw [key, hv (mem_of_mem_erase hd)]
      omega) hF)
  rw [hs, padicValRat.one, key] at h
  omega
