import OMAStatements.S_oeis_a269679

open OMA.S_oeis_a269679 PowerSeries
open scoped BigOperators

private def previous {n : ℕ} (a : Alphabet n) : Alphabet n :=
  if h : 0 < a.val then ⟨a.val-1, by omega⟩ else ⟨n, by omega⟩

private theorem next_ne {n : ℕ} (hn : 1 ≤ n) (a : Alphabet n) : cyclicNext a ≠ a := by
  intro h
  have hv := congrArg Fin.val h
  simp only [cyclicNext] at hv
  split_ifs at hv <;> simp at hv <;> omega

private theorem next_previous {n : ℕ} (a : Alphabet n) : cyclicNext (previous a) = a := by
  apply Fin.ext
  unfold previous
  split_ifs with h
  · simp [cyclicNext, show a.val - 1 < n by have := a.isLt; omega, Nat.sub_add_cancel h]
  · simp [cyclicNext, show a.val = 0 by omega]

private theorem next_inj {n : ℕ} : Function.Injective (@cyclicNext n) := by
  intro a b h
  have hv := congrArg Fin.val h
  simp only [cyclicNext] at hv
  have ha := a.isLt
  have hb := b.isLt
  apply Fin.ext
  split_ifs at hv <;> simp at hv <;> omega

private theorem previous_ne {n : ℕ} (hn : 1 ≤ n) (a : Alphabet n) : previous a ≠ a :=
  fun h => next_ne hn a (by simpa only [h] using next_previous a)

private theorem next_ne_previous {n : ℕ} (hn : 2 ≤ n) (a : Alphabet n) :
    cyclicNext a ≠ previous a := by
  intro h
  have hv := congrArg Fin.val h
  have ha := a.isLt
  simp only [cyclicNext, previous] at hv
  split_ifs at hv <;> simp at hv <;> omega

private def excluded {n : ℕ} (a : Alphabet n) : Finset (Alphabet n) :=
  {a, cyclicNext a, previous a}

private theorem notallowed_count (n : ℕ) (hn : 2 ≤ n) :
    ((Finset.univ : Finset (Word n)).filter (fun w => ¬ allowed w)).card =
      (n+1)*(n+1) + (n+1)*n + (n+1)*(n-2) := by
  let U : Finset (Alphabet n) := Finset.univ
  let P := U ×ˢ U
  let Q := U.sigma (fun b => U.erase b)
  let R := U.sigma (fun b => U \ excluded b)
  let T := P.disjSum (Q.disjSum R)
  let f : (Alphabet n × Alphabet n) ⊕ ((Σ _ : Alphabet n, Alphabet n) ⊕
      (Σ _ : Alphabet n, Alphabet n)) → Word n
    | .inl (b,d) => (b,b,b,d)
    | .inr (.inl ⟨b,a⟩) => (a,b,b,b)
    | .inr (.inr ⟨b,c⟩) => (b,b,c,c)
  have hnxt (a b : Alphabet n) : a = cyclicNext b ↔ b = previous a := by
    constructor
    · intro h
      exact next_inj (h.symm.trans (next_previous a).symm)
    · intro h
      rw [h, next_previous]
  have hchar (a b c d : Alphabet n) :
      ¬ allowed (a,b,c,d) ↔
      (a=b ∧ b=c) ∨ (a≠b ∧ b=c ∧ c=d) ∨
      (a=b ∧ c=d ∧ c∉excluded b) := by
    simp only [allowed, two, allowedPair, excluded, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · intro h
      have ht : (a=b ∧ b=c) ∨ (b=c ∧ c=d) ∨ (a=b ∧ c=d) := by tauto
      rcases ht with h₁ | h₂ | h₃
      · exact Or.inl h₁
      · by_cases h₄ : a=b
        · exact Or.inl ⟨h₄,h₂.1⟩
        · exact Or.inr (Or.inl ⟨h₄,h₂⟩)
      · by_cases h₄ : b=c
        · exact Or.inl ⟨h₃.1,h₄⟩
        · right
          right
          refine ⟨h₃.1,h₃.2,?_⟩
          intro he
          rw [h₃.1] at h
          exact he.elim (fun e => h₄ e.symm) (fun e => h (Or.inr
            ⟨rfl,h₃.2,e.imp_right ((hnxt b c).mpr)⟩))
    · rintro (⟨h₁,h₂⟩ | ⟨h₁,h₂,h₃⟩ | ⟨h₁,h₂,he⟩)
      · subst a
        subst c
        rintro (h | ⟨_,_,hc | hc⟩)
        · exact h (Or.inl ⟨rfl,rfl⟩)
        · exact next_ne (by omega) b hc.symm
        · exact next_ne (by omega) b hc.symm
      · rintro (h | ⟨h',_⟩)
        · exact h (Or.inr (Or.inl ⟨h₂,h₃⟩))
        · exact h₁ h'
      · rintro (h | ⟨_,_,hc | hc⟩)
        · exact h (Or.inr (Or.inr ⟨h₁,h₂⟩))
        · exact he (Or.inr (Or.inl (by simpa [h₁] using hc)))
        · exact he (Or.inr (Or.inr ((hnxt b c).mp (by simpa [h₁] using hc))))
  have hb : T.card = ((Finset.univ : Finset (Word n)).filter (fun w => ¬ allowed w)).card := by
    refine Finset.card_bij (fun x _ => f x) ?_ ?_ ?_
    · rintro (⟨b,d⟩ | ⟨b,a⟩ | ⟨b,c⟩) h
      · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (hchar _ _ _ _).mpr (Or.inl ⟨rfl,rfl⟩)⟩
      · have ha : a ≠ b := by simpa [T,Q,U] using h
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (hchar _ _ _ _).mpr (Or.inr (Or.inl ⟨ha,rfl,rfl⟩))⟩
      · have hc : c ∉ excluded b := by simpa [T,R,U] using h
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (hchar _ _ _ _).mpr (Or.inr (Or.inr ⟨rfl,rfl,hc⟩))⟩
    · rintro (⟨b,d⟩ | ⟨b,a⟩ | ⟨b,c⟩) h (⟨v,w⟩ | ⟨v,u⟩ | ⟨v,z⟩) h' hf <;>
        simp [T,P,Q,R,U,excluded,f] at h h' hf ⊢ <;> grind
    · rintro ⟨a,b,c,d⟩ h
      rcases (hchar a b c d).mp (Finset.mem_filter.mp h).2 with h₁ | h₁ | h₁
      · obtain ⟨rfl,rfl⟩ := h₁
        exact ⟨.inl (a,d), by simp [T,P,U], rfl⟩
      · obtain ⟨hne,rfl,rfl⟩ := h₁
        exact ⟨.inr (.inl ⟨b,a⟩), by simp [T,Q,U,hne], rfl⟩
      · obtain ⟨rfl,rfl,hne⟩ := h₁
        exact ⟨.inr (.inr ⟨a,c⟩), by simp [T,R,U,hne], rfl⟩
  have hc (a : Alphabet n) : (U \ excluded a).card = n - 2 := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _)]
    have h₁ := next_ne (show 1 ≤ n by omega) a
    have h₂ := previous_ne (show 1 ≤ n by omega) a
    have h₃ := next_ne_previous hn a
    have he : (excluded a).card = 3 := by
      unfold excluded
      rw [Finset.card_insert_of_notMem (by simp [h₁.symm,h₂.symm]),
        Finset.card_insert_of_notMem (by simp [h₃]), Finset.card_singleton]
    simp [he]
  rw [← hb]
  unfold T
  rw [Finset.card_disjSum, Finset.card_disjSum, Finset.card_product, Finset.card_sigma,
    Finset.card_sigma]
  simp only [hc, U, Finset.card_univ, Fintype.card_fin, Finset.card_erase_of_mem,
    Finset.mem_univ, Nat.add_sub_cancel, Finset.sum_const, Nat.nsmul_eq_mul, add_assoc]

private def model (n : ℕ) : ℤ :=
  (n : ℤ)^4 + 4*(n : ℤ)^3 + 3*(n : ℤ)^2 + 2*(n : ℤ) + 2

private theorem term_model (n : ℕ) (hn : 2 ≤ n) : terms n = model n := by
  have hb := notallowed_count n hn
  let s := (Finset.univ : Finset (Word n)).filter allowed
  have hx : Finset.univ \ s = (Finset.univ : Finset (Word n)).filter (fun w => ¬ allowed w) := by
    ext w
    simp [s]
  have hs := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ s)
  rw [hx, hb] at hs
  have he : (Finset.univ : Finset (Word n)).card = (n+1)^4 := by
    simp [Word, Alphabet]
    ring
  rw [he] at hs
  change _ + count n = _ at hs
  have hz := congrArg (fun x : ℕ => (x : ℤ)) hs
  push_cast [Nat.cast_sub hn] at hz
  have ht : terms n = (count n : ℤ) := by
    cases n with
    | zero => omega
    | succ n => rfl
  rw [ht]
  unfold model
  linarith only [hz]

private theorem term_rec (n : ℕ) :
    terms (n+7) = 5*terms (n+6) - 10*terms (n+5) +
      10*terms (n+4) - 5*terms (n+3) + terms (n+2) := by
  rw [term_model _ (by omega), term_model _ (by omega), term_model _ (by omega),
    term_model _ (by omega), term_model _ (by omega), term_model _ (by omega)]
  unfold model
  push_cast
  ring

theorem OMA.solution : type_of% @OMA.S_oeis_a269679.main := by
  refine ⟨?_, term_rec, ?_⟩
  · intro n
    rw [term_model _ (by omega)]
    unfold model
    push_cast
    rfl
  · have h0 : terms 0 = 0 := rfl
    have h1 : terms 1 = 10 := by decide +kernel
    have h2 : terms 2 = 66 := by rw [term_model _ (by decide)]; decide
    have h3 : terms 3 = 224 := by rw [term_model _ (by decide)]; decide
    have h4 : terms 4 = 570 := by rw [term_model _ (by decide)]; decide
    have h5 : terms 5 = 1212 := by rw [term_model _ (by decide)]; decide
    have h6 : terms 6 = 2282 := by rw [term_model _ (by decide)]; decide
    have hD : (1-X : PowerSeries ℤ)^5 = 1 - C 5 * X^1 + C 10 * X^2 -
        C 10 * X^3 + C 5 * X^4 - X^5 := by simp; ring
    have hR : (2*X*(5+8*X-3*X^2+5*X^3-4*X^4+X^5) : PowerSeries ℤ) =
        C 10 * X^1 + C 16 * X^2 - C 6 * X^3 + C 10 * X^4 - C 8 * X^5 + C 2 * X^6 := by
      simp
      ring
    rw [hD, hR]
    ext d
    simp only [add_mul, sub_mul, one_mul, mul_assoc, map_add, map_sub, coeff_C_mul,
      coeff_X_pow_mul', coeff_X_pow, coeff_mk]
    by_cases hd : d < 7
    · interval_cases d <;> norm_num [h0,h1,h2,h3,h4,h5,h6]
    · have h1d : 1 ≤ d := by omega
      have h2d : 2 ≤ d := by omega
      have h3d : 3 ≤ d := by omega
      have h4d : 4 ≤ d := by omega
      have h5d : 5 ≤ d := by omega
      simp [h1d,h2d,h3d,h4d,h5d,show d ≠ 1 by omega,show d ≠ 2 by omega,
        show d ≠ 3 by omega,show d ≠ 4 by omega,show d ≠ 5 by omega,show d ≠ 6 by omega]
      have he := term_rec (d-7)
      rw [show d-7+7=d by omega, show d-7+6=d-1 by omega, show d-7+5=d-2 by omega,
        show d-7+4=d-3 by omega, show d-7+3=d-4 by omega, show d-7+2=d-5 by omega] at he
      linarith