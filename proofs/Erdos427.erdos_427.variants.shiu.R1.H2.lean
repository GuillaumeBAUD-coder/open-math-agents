import OMAReductions.R_Erdos427_erdos_427_variants_shiu_R1
/-! A counting bound for a Boolean interval without a long run. -/
open Finset

lemma trailing_run_bound (good : ℕ → Bool) (l k : ℕ) (hk : 1 ≤ k) (n : ℕ)
    (hno : ¬ ∃ m : ℕ, l ≤ m ∧ m+k ≤ l+n ∧ ∀ i ∈ Ico m (m+k), good i = true) :
    ∃ t : ℕ, t < k ∧ t ≤ n ∧
      (∀ i, l+n-t ≤ i → i < l+n → good i = true) ∧
      ((Ico l (l+n)).filter (fun i => good i = true)).card ≤
        (k-1) * ((Ico l (l+n)).filter (fun i => good i = false)).card + t := by
  induction n with
  | zero =>
    refine ⟨0, by omega, by omega, ?_, ?_⟩
    · intro i h1 h2; omega
    · simp
  | succ n ih =>
    have hno' : ¬ ∃ m : ℕ, l ≤ m ∧ m+k ≤ l+n ∧ ∀ i ∈ Ico m (m+k), good i = true := by
      rintro ⟨m,hl,hr,hg⟩
      exact hno ⟨m,hl,by omega,hg⟩
    obtain ⟨t,htk,htn,htrail,hcount⟩ := ih hno'
    have htkl : t ≤ k-1 := by omega
    have heq : Ico l (l+(n+1)) = insert (l+n) (Ico l (l+n)) := by
      ext i
      simp only [mem_Ico, mem_insert]
      omega
    have hnt : l+n ∉ ((Ico l (l+n)).filter (fun i => good i = true)) := by simp
    have hnf : l+n ∉ ((Ico l (l+n)).filter (fun i => good i = false)) := by simp
    cases hg : good (l+n) with
    | false =>
      refine ⟨0, by omega, by omega, ?_, ?_⟩
      · intro i h1 h2; omega
      · rw [heq]
        simp only [filter_insert, hg, Bool.false_eq_true, ↓reduceIte]
        rw [card_insert_of_notMem hnf]
        simp only [Nat.add_zero]
        nlinarith
    | true =>
      have htk' : t+1 < k := by
        by_contra hn
        have hkt : k = t+1 := by omega
        apply hno
        refine ⟨l+n-t, by omega, by omega, ?_⟩
        intro i hi
        have hb := mem_Ico.mp hi
        by_cases hlt : i < l+n
        · exact htrail i hb.1 hlt
        · have hi' : i = l+n := by omega
          simpa [hi'] using hg
      refine ⟨t+1, htk', by omega, ?_, ?_⟩
      · intro i h1 h2
        by_cases hlt : i < l+n
        · apply htrail i (by omega) hlt
        · have hi' : i = l+n := by omega
          simpa [hi'] using hg
      · rw [heq]
        simp only [filter_insert, hg, Bool.true_eq_false, ↓reduceIte]
        rw [card_insert_of_notMem hnt]
        omega

 theorem bool_run (good : ℕ → Bool) (l r k : ℕ) (hk : 1 ≤ k)
    (hc : (k - 1) * (((Ico l r).filter (fun i => good i = false)).card + 1) <
        ((Ico l r).filter (fun i => good i = true)).card) :
    ∃ m : ℕ, l ≤ m ∧ m + k ≤ r ∧ ∀ i ∈ Ico m (m + k), good i = true := by
  by_contra hno
  have hlr : l ≤ r := by
    by_contra hn
    have he : Ico l r = ∅ := by ext i; simp; omega
    simp [he] at hc
  have hr : l+(r-l) = r := by omega
  obtain ⟨t,ht,_,_,hbound⟩ := trailing_run_bound good l k hk (r-l) (by simpa [hr] using hno)
  rw [hr] at hbound
  have ht' : t ≤ k-1 := by omega
  nlinarith

theorem OMA.solution : OMA.R_Erdos427_erdos_427_variants_shiu_R1.H2 := by
  exact bool_run
