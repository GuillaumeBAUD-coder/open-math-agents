import OMAReductions.R_OeisA51903_conjecture1_R1

/-!
A Lehmer witness `φ(n) ∣ n - 1` is squarefree: if `p^(k+1) ∣ n` is the maximal prime power
then `p^k ∣ φ(n) ∣ n - 1` and `p^k ∣ n`, hence `p^k ∣ 1`, so `k = 0`.
-/

theorem OMA.solution : OMA.R_OeisA51903_conjecture1_R1.H1 := by
  intro n hn hφ
  obtain ⟨p, k, hp, he, hpk⟩ := OMA.R_OeisA51903_conjecture1_R1.attains hn
  have h1 : p ^ k ∣ 1 := OMA.R_OeisA51903_conjecture1_R1.strip (by omega) hp hpk hφ
  have hk : k = 0 := by
    rcases k with _ | k
    · rfl
    · exact absurd (Nat.eq_one_of_dvd_one h1) (Nat.one_lt_pow (by omega) hp.one_lt).ne'
  rw [he, hk]
