import OMAReductions.R_Erdos824_erdos_824_variants_squarefree_R1

-- Step Erdos824.erdos_824.variants.squarefree.R1.H2: hypothesis H2 of reduction Erdos824.erdos_824.variants.squarefree.R1
-- Credit: @ishaanzee
-- Proof: each product is a positive s-smooth number at most (Y+1)^k <= x; such a number is
-- determined by its exponents at q <= s, each at most log2 x.

open Finset

namespace E824Aux

lemma fact_le_log {m q : ℕ} (hm : m ≠ 0) (hq : q.Prime) : m.factorization q ≤ Nat.log 2 m := by
  have h1 : q ^ (m.factorization q) ∣ m := Nat.ordProj_dvd m q
  have h2 : 2 ^ (m.factorization q) ≤ m :=
    le_trans (Nat.pow_le_pow_left hq.two_le _) (Nat.le_of_dvd (Nat.pos_of_ne_zero hm) h1)
  exact Nat.le_log_of_pow_le (by norm_num) h2

/-- At most `(log₂ x + 1) ^ (s + 1)` positive `s`-smooth numbers are `≤ x`. -/
lemma smooth_card (s x : ℕ) (U : Finset ℕ)
    (hU : ∀ m ∈ U, m ≠ 0 ∧ m ≤ x ∧ ∀ q ∈ m.primeFactors, q ≤ s) :
    U.card ≤ (Nat.log 2 x + 1) ^ (s + 1) := by
  let F : ℕ → (Fin (s + 1) → ℕ) := fun m q => m.factorization q
  have hmaps : ∀ m ∈ U, F m ∈ Fintype.piFinset (fun _ : Fin (s + 1) => range (Nat.log 2 x + 1)) := by
    intro m hm
    rw [Fintype.mem_piFinset]
    intro q
    rw [mem_range]
    by_cases hq : (q : ℕ).Prime
    · have h1 := fact_le_log (hU m hm).1 hq
      have h2 := Nat.log_mono_right (b := 2) (hU m hm).2.1
      simp only [F]
      omega
    · simp [F, Nat.factorization_eq_zero_of_not_prime _ hq]
  have hzero : ∀ m ∈ U, ∀ p, s < p → m.factorization p = 0 := by
    intro m hm p hp
    by_contra hne
    have : p ∈ m.primeFactors := by
      rw [← Nat.support_factorization]
      exact Finsupp.mem_support_iff.2 hne
    have := (hU m hm).2.2 p this
    omega
  have hinj : Set.InjOn F U := by
    intro m hm m' hm' h
    apply Nat.eq_of_factorization_eq (hU m hm).1 (hU m' hm').1
    intro p
    by_cases hps : p ≤ s
    · have := congrFun h ⟨p, by omega⟩
      simpa [F] using this
    · rw [hzero m hm p (by omega), hzero m' hm' p (by omega)]
  calc U.card ≤ (Fintype.piFinset (fun _ : Fin (s + 1) => range (Nat.log 2 x + 1))).card :=
        Finset.card_le_card_of_injOn F hmaps hinj
    _ = (Nat.log 2 x + 1) ^ (s + 1) := by simp [Fintype.card_piFinset]

end E824Aux

theorem OMA.solution : OMA.R_Erdos824_erdos_824_variants_squarefree_R1.H2 := by
  unfold OMA.R_Erdos824_erdos_824_variants_squarefree_R1.H2
  intro P Y s k x hY hs hx
  apply E824Aux.smooth_card
  intro m hm
  obtain ⟨T, hT, rfl⟩ := mem_image.1 hm
  obtain ⟨hTP, hTk⟩ := mem_powersetCard.1 hT
  refine ⟨Finset.prod_ne_zero_iff.2 (fun p _ => by omega), ?_, ?_⟩
  · calc ∏ p ∈ T, (p + 1) ≤ (Y + 1) ^ T.card :=
          Finset.prod_le_pow_card _ _ _ (fun p hp => by have := hY p (hTP hp); omega)
      _ = (Y + 1) ^ k := by rw [hTk]
      _ ≤ x := hx
  · intro q hq
    rw [Nat.mem_primeFactors] at hq
    obtain ⟨hqp, hqd, -⟩ := hq
    obtain ⟨p, hp, hqp'⟩ := (Nat.Prime.prime hqp).dvd_finset_prod_iff _ |>.1 hqd
    exact hs p (hTP hp) q (Nat.mem_primeFactors.2 ⟨hqp, hqp', by omega⟩)
