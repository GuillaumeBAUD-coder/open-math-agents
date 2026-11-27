import OMAStatements.S_oeis_a280321

namespace OMA.P_oeis_a280321

open OMA.S_oeis_a280321

def S (n : ℕ) : Finset (ℕ × ℕ) :=
  ((Finset.range (n + 1)) ×ˢ (Finset.range (n + 1))).filter (fun p => p.1 * p.2 = 0)

lemma S_eq (n : ℕ) : S n = (Finset.range (n + 1)).image (fun d => ((0 : ℕ), d)) ∪
    (Finset.Icc 1 n).image (fun a => (a, (0 : ℕ))) := by
  ext ⟨a, d⟩
  simp only [S, Finset.mem_filter, Finset.mem_product, Finset.mem_range, Finset.mem_union,
    Finset.mem_image, Finset.mem_Icc, Prod.mk.injEq, Nat.mul_eq_zero]
  constructor
  · rintro ⟨⟨ha, hd⟩, h | h⟩
    · left; exact ⟨d, hd, h.symm, rfl⟩
    · by_cases ha0 : a = 0
      · left; exact ⟨d, hd, ha0.symm, rfl⟩
      · right; exact ⟨a, ⟨by omega, by omega⟩, rfl, h.symm⟩
  · rintro (⟨x, hx, h1, h2⟩ | ⟨x, hx, h1, h2⟩)
    · subst h1 h2; exact ⟨⟨by omega, hx⟩, Or.inl rfl⟩
    · subst h1 h2; exact ⟨⟨by omega, by omega⟩, Or.inr rfl⟩

lemma S_card (n : ℕ) : (S n).card = 2 * n + 1 := by
  have hdisj : Disjoint ((Finset.range (n + 1)).image (fun d => ((0 : ℕ), d)))
      ((Finset.Icc 1 n).image (fun a => (a, (0 : ℕ)))) := by
    rw [Finset.disjoint_left]
    rintro ⟨a, d⟩ h1 h2
    simp only [Finset.mem_image, Finset.mem_range, Finset.mem_Icc, Prod.mk.injEq] at h1 h2
    obtain ⟨x, _, h1a, _⟩ := h1
    obtain ⟨y, hy, h2a, _⟩ := h2
    omega
  rw [S_eq, Finset.card_union_of_disjoint hdisj,
    Finset.card_image_of_injective _ (fun x y h => by simpa using h),
    Finset.card_image_of_injective _ (fun x y h => by simpa using h),
    Finset.card_range, Nat.card_Icc]
  omega

lemma key {n : ℕ} (hn : 1 < n) (a b c d : ℕ) :
    ((a : ℤ) * d - b * c = n * (a * d + b * c)) ↔ (a * d = 0 ∧ b * c = 0) := by
  constructor
  · intro h
    have hx : (0 : ℤ) ≤ a * d := by positivity
    have hy : (0 : ℤ) ≤ b * c := by positivity
    have hn' : (2 : ℤ) ≤ n := by exact_mod_cast hn
    have h1 : (a : ℤ) * d = 0 := by
      nlinarith [mul_nonneg (sub_nonneg.2 hn') hx, mul_nonneg (sub_nonneg.2 hn') hy]
    have h2 : (b : ℤ) * c = 0 := by
      nlinarith [mul_nonneg (sub_nonneg.2 hn') hx, mul_nonneg (sub_nonneg.2 hn') hy]
    exact ⟨by exact_mod_cast h1, by exact_mod_cast h2⟩
  · rintro ⟨h1, h2⟩
    have h1' : (a : ℤ) * d = 0 := by exact_mod_cast h1
    have h2' : (b : ℤ) * c = 0 := by exact_mod_cast h2
    rw [h1', h2']
    ring

end OMA.P_oeis_a280321

open OMA.S_oeis_a280321 OMA.P_oeis_a280321

theorem OMA.solution : type_of% @OMA.S_oeis_a280321.main := by
  have hval : ∀ n : ℕ, 1 < n → a n = (1 + 2 * n) ^ 2 := by
    intro n hn
    unfold a
    trans (S n ×ˢ S n).card
    · refine Finset.card_bij' (fun t _ => ((t.1, t.2.2.2), (t.2.1, t.2.2.1)))
        (fun p _ => (p.1.1, p.2.1, p.2.2, p.1.2)) (fun t ht => ?_) (fun p hp => ?_)
        (fun t _ => rfl) (fun p _ => rfl)
      · obtain ⟨x, y, z, w⟩ := t
        rw [Finset.mem_filter] at ht
        simp only [Finset.mem_product, Finset.mem_range] at ht
        obtain ⟨⟨hx, hy, hz, hw⟩, hP⟩ := ht
        rw [key hn] at hP
        simp only [S, Finset.mem_product, Finset.mem_filter, Finset.mem_range]
        exact ⟨⟨⟨hx, hw⟩, hP.1⟩, ⟨⟨hy, hz⟩, hP.2⟩⟩
      · obtain ⟨⟨x, w⟩, ⟨y, z⟩⟩ := p
        simp only [S, Finset.mem_product, Finset.mem_filter, Finset.mem_range] at hp
        obtain ⟨⟨⟨hx, hw⟩, h1⟩, ⟨⟨hy, hz⟩, h2⟩⟩ := hp
        rw [Finset.mem_filter]
        simp only [Finset.mem_product, Finset.mem_range]
        exact ⟨⟨hx, hy, hz, hw⟩, (key hn x y z w).2 ⟨h1, h2⟩⟩
    · rw [Finset.card_product, S_card]
      ring
  refine ⟨hval, fun n hn => ?_⟩
  rw [hval n (by omega), hval (n - 1) (by omega), hval (n - 2) (by omega),
    hval (n - 3) (by omega)]
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
  rw [show m + 3 - 1 = m + 2 by omega, show m + 3 - 2 = m + 1 by omega,
    show m + 3 - 3 = m by omega]
  push_cast
  ring
