import OMAStatements.S_oeis_a097083

-- Problem: A097083: Positive values of k such that there is exactly one permutation p of (1,2,3,...,k) such that i+p(i) is a Fibonacci number for 1<=i<=k
-- Upstream: statements/oeis-a097083.lean (declaration OMA.S_oeis_a097083.main)
-- Credit: @Coglizer
--
-- Proof outline. Write a(0) = 1, a(1) = 2, a(n+2) = F(n+5) - 1 - a(n).
-- * Uniqueness for k = a(n+2): with F = F(n+5), every i >= F(n+4) is forced to F - i. If some
--   l <= a(n) were sent above a(n), following l -> F(n+4) - l -> its mirror gives a valid
--   permutation of {1..a(n)} containing a pair with sum F(n+2), which the induction excludes.
--   Hence p preserves {1..a(n)} and is the reflection i -> F - i above it.
-- * Converse: if two Fibonacci numbers lie in (k, 2k], two reflections give two permutations;
--   otherwise uniqueness descends to F - 1 - k, and arithmetic leaves a(n), 6 or 10; the last
--   two have two explicit permutations.
-- * a(n) = floor(F(n+4)/sqrt 5) follows from 5 a(n) + r = L(n+4) with 1 <= r <= 4 and Cassini.

namespace A097083

open OMA.S_oeis_a097083

/-- A valid Fibonacci-sum permutation of `{1..k}`, as a function `ℕ → ℕ` vanishing outside. -/
def Val (k : ℕ) (f : ℕ → ℕ) : Prop :=
  (∀ i, 1 ≤ i → i ≤ k → 1 ≤ f i ∧ f i ≤ k ∧ IsFib (i + f i)) ∧
  (∀ i j, 1 ≤ i → i ≤ k → 1 ≤ j → j ≤ k → f i = f j → i = j) ∧
  (∀ i, (i = 0 ∨ k < i) → f i = 0)

lemma Val.surj {k : ℕ} {f : ℕ → ℕ} (h : Val k f) (j : ℕ) (h1 : 1 ≤ j) (h2 : j ≤ k) :
    ∃ i, 1 ≤ i ∧ i ≤ k ∧ f i = j := by
  obtain ⟨hr, hi, -⟩ := h
  have hsub : (Finset.Icc 1 k).image f ⊆ Finset.Icc 1 k := by
    intro x hx
    obtain ⟨i, hi', rfl⟩ := Finset.mem_image.1 hx
    rw [Finset.mem_Icc] at hi' ⊢
    exact ⟨(hr i hi'.1 hi'.2).1, (hr i hi'.1 hi'.2).2.1⟩
  have hcard : ((Finset.Icc 1 k).image f).card = (Finset.Icc 1 k).card := by
    apply Finset.card_image_of_injOn
    intro a ha b hb hab
    rw [Finset.mem_coe, Finset.mem_Icc] at ha hb
    exact hi a b ha.1 ha.2 hb.1 hb.2 hab
  have heq := Finset.eq_of_subset_of_card_le hsub (le_of_eq hcard.symm)
  have hj : j ∈ (Finset.Icc 1 k).image f := by rw [heq]; exact Finset.mem_Icc.2 ⟨h1, h2⟩
  obtain ⟨i, hi', rfl⟩ := Finset.mem_image.1 hj
  rw [Finset.mem_Icc] at hi'
  exact ⟨i, hi'.1, hi'.2, rfl⟩

lemma fib_between {t r : ℕ} (h1 : Nat.fib t < Nat.fib r) (h2 : Nat.fib r < Nat.fib (t + 2)) :
    r = t + 1 := by
  by_contra hne
  rcases Nat.lt_or_ge r (t + 1) with h | h
  · have := Nat.fib_mono (show r ≤ t by omega)
    omega
  · have := Nat.fib_mono (show t + 2 ≤ r by omega)
    omega

lemma fib_between2 {t r : ℕ} (h1 : Nat.fib t < Nat.fib r) (h2 : Nat.fib r < Nat.fib (t + 3)) :
    r = t + 1 ∨ r = t + 2 := by
  by_contra hne
  rcases Nat.lt_or_ge r (t + 1) with h | h
  · have := Nat.fib_mono (show r ≤ t by omega)
    omega
  · have := Nat.fib_mono (show t + 3 ≤ r by omega)
    omega

/-- The core forcing step. -/
lemma step (t k K : ℕ) (p : ℕ → ℕ)
    (hK : K + k + 1 = Nat.fib (t + 3)) (h1 : Nat.fib (t + 2) ≤ K)
    (h2 : 2 * K < Nat.fib (t + 4))
    (h3 : Nat.fib t ≤ k + 1) (h4 : 2 * k < Nat.fib (t + 2))
    (hI : ∀ q, Val k q → ∀ i, 1 ≤ i → i ≤ k → i + q i ≠ Nat.fib t)
    (hp : Val K p) :
    (∀ i, 1 ≤ i → i ≤ k → p i ≤ k) ∧
      (∀ i, k < i → i ≤ K → p i = Nat.fib (t + 3) - i) := by
  have e2 : Nat.fib (t + 2) = Nat.fib t + Nat.fib (t + 1) := Nat.fib_add_two
  have e3 : Nat.fib (t + 3) = Nat.fib (t + 1) + Nat.fib (t + 2) := Nat.fib_add_two
  have e4 : Nat.fib (t + 4) = Nat.fib (t + 2) + Nat.fib (t + 3) := Nat.fib_add_two
  have hb : 1 ≤ Nat.fib (t + 1) := Nat.fib_pos.2 (by omega)
  obtain ⟨hr, hinj, hout⟩ := id hp
  have S1 : ∀ i j, Nat.fib (t + 2) ≤ i → i ≤ K → 1 ≤ j → j ≤ K → IsFib (i + j) →
      i + j = Nat.fib (t + 3) := by
    intro i j hi hiK hj hjK hf
    obtain ⟨r, hr'⟩ := hf
    have hlt : Nat.fib r < Nat.fib (t + 2 + 2) := by
      show Nat.fib r < Nat.fib (t + 4)
      omega
    have : r = t + 2 + 1 := fib_between (by omega) hlt
    rw [← hr', this]
  have P1 : ∀ i, Nat.fib (t + 2) ≤ i → i ≤ K → i + p i = Nat.fib (t + 3) := by
    intro i hi hiK
    have := hr i (by omega) hiK
    exact S1 i (p i) hi hiK this.1 this.2.1 this.2.2
  have P2 : ∀ j, 1 ≤ j → j ≤ K → Nat.fib (t + 2) ≤ p j → j + p j = Nat.fib (t + 3) := by
    intro j hj hjK hpj
    have := hr j hj hjK
    have h' := S1 (p j) j hpj this.2.1 hj hjK (by rw [add_comm]; exact this.2.2)
    omega
  -- images of small elements avoid the forced block
  have P3 : ∀ j, 1 ≤ j → j ≤ K → j < Nat.fib (t + 2) → ¬ (k + 1 ≤ p j ∧ p j ≤ Nat.fib (t + 1)) := by
    intro j hj hjK hjs ⟨ha, hb'⟩
    have hi1 : Nat.fib (t + 2) ≤ Nat.fib (t + 3) - p j := by omega
    have hi2 : Nat.fib (t + 3) - p j ≤ K := by omega
    have h5 := P1 _ hi1 hi2
    have h6 : p (Nat.fib (t + 3) - p j) = p j := by omega
    have := hinj _ _ (by omega) hi2 hj hjK h6
    omega
  have P4 : ∀ j, 1 ≤ j → j ≤ k → k < p j →
      Nat.fib (t + 1) < p j ∧ j + p j = Nat.fib (t + 2) := by
    intro j hj hjk hpj
    have hjK : j ≤ K := by omega
    have hrj := hr j hj hjK
    have hlt : p j < Nat.fib (t + 2) := by
      by_contra hge
      have := P2 j hj hjK (by omega)
      omega
    have hgt : Nat.fib (t + 1) < p j := by
      by_contra hle
      exact P3 j hj hjK (by omega) ⟨by omega, by omega⟩
    refine ⟨hgt, ?_⟩
    obtain ⟨r, hr'⟩ := hrj.2.2
    have : r = t + 1 + 1 := fib_between (by omega) (by
      show Nat.fib r < Nat.fib (t + 3)
      omega)
    rw [← hr', this]
  have P5 : ∀ h, Nat.fib (t + 1) < h → h < Nat.fib (t + 2) →
      h + p h = Nat.fib (t + 2) ∨ h + p h = Nat.fib (t + 3) := by
    intro h hh1 hh2
    have hhK : h ≤ K := by omega
    have hrh := hr h (by omega) hhK
    have hlt : p h < Nat.fib (t + 2) := by
      by_contra hge
      have := P2 h (by omega) hhK (by omega)
      omega
    obtain ⟨r, hr'⟩ := hrh.2.2
    have : r = t + 1 + 1 ∨ r = t + 1 + 2 := fib_between2 (by omega) (by
      show Nat.fib r < Nat.fib (t + 4)
      omega)
    rcases this with h' | h'
    · left; rw [← hr', h']
    · right; rw [← hr', h']
  -- detours
  have D : ∀ i, 1 ≤ i → i ≤ k → k < p i →
      i < Nat.fib t ∧ i + p (Nat.fib (t + 1) + i) = Nat.fib t ∧ 1 ≤ p (Nat.fib (t + 1) + i) := by
    intro i hi hik hpi
    obtain ⟨hgt, hsum⟩ := P4 i hi hik hpi
    have hia : i < Nat.fib t := by omega
    have hhK : Nat.fib (t + 1) + i ≤ K := by omega
    have hrh := hr (Nat.fib (t + 1) + i) (by omega) hhK
    rcases P5 (Nat.fib (t + 1) + i) (by omega) (by omega) with h' | h'
    · exact ⟨hia, by omega, hrh.1⟩
    · exfalso
      have h6 : p (Nat.fib (t + 1) + i) = p i := by omega
      have := hinj _ _ (by omega) hhK hi (by omega) h6
      omega
  have hq : Val k (fun i => if 1 ≤ i ∧ i ≤ k then (if p i ≤ k then p i else Nat.fib t - i) else 0) := by
    refine ⟨?_, ?_, ?_⟩
    · intro i hi hik
      have hrj := hr i hi (by omega)
      simp only [if_pos (And.intro hi hik)]
      by_cases hc : p i ≤ k
      · simp only [if_pos hc]
        exact ⟨hrj.1, hc, hrj.2.2⟩
      · simp only [if_neg hc]
        obtain ⟨d1, d2, d3⟩ := D i hi hik (by omega)
        exact ⟨by omega, by omega, ⟨t, by omega⟩⟩
    · intro i j hi hik hj hjk hij
      simp only [if_pos (And.intro hi hik), if_pos (And.intro hj hjk)] at hij
      by_cases hc : p i ≤ k <;> by_cases hc' : p j ≤ k
      · simp only [if_pos hc, if_pos hc'] at hij
        exact hinj i j hi (by omega) hj (by omega) hij
      · simp only [if_pos hc, if_neg hc'] at hij
        obtain ⟨d1, d2, d3⟩ := D j hj hjk (by omega)
        have h6 : p i = p (Nat.fib (t + 1) + j) := by omega
        have := hinj _ _ hi (by omega) (by omega) (by omega) h6
        omega
      · simp only [if_neg hc, if_pos hc'] at hij
        obtain ⟨d1, d2, d3⟩ := D i hi hik (by omega)
        have h6 : p j = p (Nat.fib (t + 1) + i) := by omega
        have := hinj _ _ hj (by omega) (by omega) (by omega) h6
        omega
      · simp only [if_neg hc, if_neg hc'] at hij
        obtain ⟨d1, d2, d3⟩ := D i hi hik (by omega)
        obtain ⟨d1', d2', d3'⟩ := D j hj hjk (by omega)
        omega
    · intro i hi
      have : ¬ (1 ≤ i ∧ i ≤ k) := by omega
      simp only [if_neg this]
  have L1 : ∀ i, 1 ≤ i → i ≤ k → p i ≤ k := by
    intro i hi hik
    by_contra hc
    obtain ⟨d1, d2, d3⟩ := D i hi hik (by omega)
    have := hI _ hq i hi hik
    simp only [if_pos (And.intro hi hik), if_neg hc] at this
    omega
  refine ⟨L1, ?_⟩
  intro i hki hiK
  rcases Nat.lt_or_ge i (Nat.fib (t + 2)) with hlt | hge
  · rcases Nat.lt_or_ge (Nat.fib (t + 1)) i with hgt | hle
    · rcases P5 i hgt hlt with h' | h'
      · exfalso
        have hri := hr i (by omega) hiK
        obtain ⟨j, hj1, hj2, hj3⟩ := hq.surj (p i) hri.1 (by omega)
        simp only [if_pos (And.intro hj1 hj2), if_pos (L1 j hj1 hj2)] at hj3
        have := hinj _ _ hj1 (by omega) (by omega) hiK hj3
        omega
      · omega
    · obtain ⟨j, hj1, hj2, hj3⟩ := hp.surj (Nat.fib (t + 3) - i) (by omega) (by omega)
      have := P2 j hj1 hj2 (by omega)
      have hji : j = i := by omega
      rw [← hji]
      omega
  · have := P1 i hge hiK
    omega

/-- The sequence. -/
def A : ℕ → ℕ
  | 0 => 1
  | 1 => 2
  | (n + 2) => Nat.fib (n + 5) - 1 - A n

lemma A_bounds (n : ℕ) : Nat.fib (n + 2) ≤ A n ∧ A n < Nat.fib (n + 3) ∧
    Nat.fib (n + 3) ≤ 2 * A n ∧ 2 * A n < Nat.fib (n + 4) := by
  induction n using Nat.twoStepInduction with
  | zero => simp [A, Nat.fib_add_two]
  | one => simp [A, Nat.fib_add_two]
  | more n ih _ =>
    have e4 : Nat.fib (n + 4) = Nat.fib (n + 2) + Nat.fib (n + 3) := Nat.fib_add_two
    have e5 : Nat.fib (n + 5) = Nat.fib (n + 3) + Nat.fib (n + 4) := Nat.fib_add_two
    have e6 : Nat.fib (n + 6) = Nat.fib (n + 4) + Nat.fib (n + 5) := Nat.fib_add_two
    have hpos : 1 ≤ Nat.fib (n + 3) := Nat.fib_pos.2 (by omega)
    have hA : A (n + 2) = Nat.fib (n + 5) - 1 - A n := rfl
    refine ⟨?_, ?_, ?_, ?_⟩
    · show Nat.fib (n + 4) ≤ A (n + 2)
      omega
    · show A (n + 2) < Nat.fib (n + 5)
      omega
    · show Nat.fib (n + 5) ≤ 2 * A (n + 2)
      omega
    · show 2 * A (n + 2) < Nat.fib (n + 6)
      omega

lemma not_isFib_four : ¬ IsFib 4 := by
  rintro ⟨r, hr⟩
  rcases Nat.lt_or_ge r 5 with h | h
  · interval_cases r <;> simp [Nat.fib_add_two] at hr
  · have := Nat.fib_mono h
    have h5 : Nat.fib 5 = 5 := by decide
    omega

lemma uniq_inv (n : ℕ) : (∀ p p', Val (A n) p → Val (A n) p' → p = p') ∧
    (∀ p, Val (A n) p → ∀ i, 1 ≤ i → i ≤ A n → i + p i ≠ Nat.fib (n + 2)) := by
  induction n using Nat.twoStepInduction with
  | zero =>
    have hA : A 0 = 1 := rfl
    rw [hA]
    have key : ∀ p, Val 1 p → ∀ i, p i = if i = 1 then 1 else 0 := by
      intro p hp i
      by_cases hi : i = 1
      · subst hi
        have := hp.1 1 le_rfl le_rfl
        simp only [if_pos]
        omega
      · simp only [if_neg hi]
        exact hp.2.2 i (by omega)
    refine ⟨fun p p' hp hp' => funext fun i => by rw [key p hp, key p' hp'], ?_⟩
    intro p hp i hi1 hi2
    have hi : i = 1 := by omega
    subst hi
    rw [key p hp]
    simp [Nat.fib_add_two]
  | one =>
    have hA : A 1 = 2 := rfl
    rw [hA]
    have key : ∀ p, Val 2 p → ∀ i, p i = if i = 1 then 2 else if i = 2 then 1 else 0 := by
      intro p hp i
      have h1 := hp.1 1 (by omega) (by omega)
      have h2 := hp.1 2 (by omega) (by omega)
      have h21 : p 2 = 1 := by
        by_contra hne
        have : p 2 = 2 := by omega
        rw [this] at h2
        exact not_isFib_four h2.2.2
      have h12 : p 1 = 2 := by
        by_contra hne
        have h11 : p 1 = p 2 := by omega
        have := hp.2.1 1 2 (by omega) (by omega) (by omega) (by omega) h11
        omega
      by_cases hi : i = 1
      · subst hi; simp only [if_pos]; exact h12
      · by_cases hi2 : i = 2
        · subst hi2; simp only [if_neg hi, if_pos]; exact h21
        · simp only [if_neg hi, if_neg hi2]
          exact hp.2.2 i (by omega)
    refine ⟨fun p p' hp hp' => funext fun i => by rw [key p hp, key p' hp'], ?_⟩
    intro p hp i hi1 hi2
    rw [key p hp]
    have h3 : Nat.fib 3 = 2 := by decide
    show i + _ ≠ Nat.fib 3
    rw [h3]
    by_cases hi : i = 1
    · subst hi; simp
    · have hi' : i = 2 := by omega
      subst hi'; simp
  | more n ih _ =>
    obtain ⟨ihU, ihI⟩ := ih
    obtain ⟨b1, b2, b3, b4⟩ := A_bounds n
    obtain ⟨c1, c2, c3, c4⟩ := A_bounds (n + 2)
    have e4 : Nat.fib (n + 4) = Nat.fib (n + 2) + Nat.fib (n + 3) := Nat.fib_add_two
    have e5 : Nat.fib (n + 5) = Nat.fib (n + 3) + Nat.fib (n + 4) := Nat.fib_add_two
    have e6 : Nat.fib (n + 6) = Nat.fib (n + 4) + Nat.fib (n + 5) := Nat.fib_add_two
    have hpos : 1 ≤ Nat.fib (n + 3) := Nat.fib_pos.2 (by omega)
    have hA : A (n + 2) = Nat.fib (n + 5) - 1 - A n := rfl
    have st : ∀ p, Val (A (n + 2)) p →
        (∀ i, 1 ≤ i → i ≤ A n → p i ≤ A n) ∧
          (∀ i, A n < i → i ≤ A (n + 2) → p i = Nat.fib (n + 5) - i) := by
      intro p hp
      exact step (n + 2) (A n) (A (n + 2)) p
        (by show A (n + 2) + A n + 1 = Nat.fib (n + 5); omega)
        (by show Nat.fib (n + 4) ≤ A (n + 2); omega)
        (by show 2 * A (n + 2) < Nat.fib (n + 6); omega)
        (by omega)
        (by show 2 * A n < Nat.fib (n + 4); omega)
        ihI hp
    have restr : ∀ p, Val (A (n + 2)) p →
        Val (A n) (fun i => if 1 ≤ i ∧ i ≤ A n then p i else 0) := by
      intro p hp
      obtain ⟨s1, s2⟩ := st p hp
      refine ⟨?_, ?_, ?_⟩
      · intro i hi hik
        have := hp.1 i hi (by omega)
        simp only [if_pos (And.intro hi hik)]
        exact ⟨this.1, s1 i hi hik, this.2.2⟩
      · intro i j hi hik hj hjk hij
        simp only [if_pos (And.intro hi hik), if_pos (And.intro hj hjk)] at hij
        exact hp.2.1 i j hi (by omega) hj (by omega) hij
      · intro i hi
        have : ¬ (1 ≤ i ∧ i ≤ A n) := by omega
        simp only [if_neg this]
    refine ⟨?_, ?_⟩
    · intro p p' hp hp'
      obtain ⟨s1, s2⟩ := st p hp
      obtain ⟨s1', s2'⟩ := st p' hp'
      have hres := ihU _ _ (restr p hp) (restr p' hp')
      funext i
      by_cases hi : 1 ≤ i ∧ i ≤ A n
      · have := congr_fun hres i
        simp only [if_pos hi] at this
        exact this
      · by_cases hi' : i = 0 ∨ A (n + 2) < i
        · rw [hp.2.2 i hi', hp'.2.2 i hi']
        · rw [s2 i (by omega) (by omega), s2' i (by omega) (by omega)]
    · intro p hp i hi1 hi2
      obtain ⟨s1, s2⟩ := st p hp
      show i + p i ≠ Nat.fib (n + 4)
      by_cases hi : i ≤ A n
      · have := s1 i hi1 hi
        omega
      · have := s2 i (by omega) hi2
        omega

end A097083

namespace A097083

open OMA.S_oeis_a097083

/-- Extend a valid permutation of `{1..F-1-k}` by the reflection `i ↦ F - i`. -/
def Ext (k F : ℕ) (q : ℕ → ℕ) : ℕ → ℕ :=
  fun i => if i ≤ F - 1 - k then q i else if i ≤ k then F - i else 0

lemma ext_val (k F : ℕ) (q : ℕ → ℕ) (hF : IsFib F) (h1 : k < F) (h2 : F ≤ 2 * k)
    (hq : Val (F - 1 - k) q) : Val k (Ext k F q) := by
  obtain ⟨qr, qi, qo⟩ := hq
  refine ⟨?_, ?_, ?_⟩
  · intro i hi hik
    unfold Ext
    by_cases hc : i ≤ F - 1 - k
    · simp only [if_pos hc]
      have := qr i hi hc
      exact ⟨this.1, by omega, this.2.2⟩
    · simp only [if_neg hc, if_pos hik]
      refine ⟨by omega, by omega, ?_⟩
      have : i + (F - i) = F := by omega
      rw [this]
      exact hF
  · intro i j hi hik hj hjk hij
    unfold Ext at hij
    by_cases hc : i ≤ F - 1 - k <;> by_cases hc' : j ≤ F - 1 - k
    · simp only [if_pos hc, if_pos hc'] at hij
      exact qi i j hi hc hj hc' hij
    · simp only [if_pos hc, if_neg hc', if_pos hjk] at hij
      have := qr i hi hc
      omega
    · simp only [if_neg hc, if_pos hc', if_pos hik] at hij
      have := qr j hj hc'
      omega
    · simp only [if_neg hc, if_neg hc', if_pos hik, if_pos hjk] at hij
      omega
  · intro i hi
    unfold Ext
    rcases hi with hi | hi
    · subst hi
      simp only [Nat.zero_le, if_true]
      exact qo 0 (Or.inl rfl)
    · have hc : ¬ i ≤ F - 1 - k := by omega
      have hc' : ¬ i ≤ k := by omega
      simp only [if_neg hc, if_neg hc']

lemma ext_top (k F : ℕ) (q : ℕ → ℕ) (hk : 1 ≤ k) (h2 : F ≤ 2 * k) :
    Ext k F q k = F - k := by
  unfold Ext
  have hc : ¬ k ≤ F - 1 - k := by omega
  simp only [if_neg hc, if_pos le_rfl]

lemma ext_inj (k F : ℕ) (q q' : ℕ → ℕ) (h1 : k < F)
    (hq : Val (F - 1 - k) q) (hq' : Val (F - 1 - k) q') (h : Ext k F q = Ext k F q') : q = q' := by
  funext i
  by_cases hc : i ≤ F - 1 - k
  · have := congr_fun h i
    unfold Ext at this
    simp only [if_pos hc] at this
    exact this
  · rw [hq.2.2 i (Or.inr (by omega)), hq'.2.2 i (Or.inr (by omega))]

lemma lt_fib (k : ℕ) : k < Nat.fib (k + 2) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have e : Nat.fib (k + 3) = Nat.fib (k + 1) + Nat.fib (k + 2) := Nat.fib_add_two
    have hpos : 1 ≤ Nat.fib (k + 1) := Nat.fib_pos.2 (by omega)
    show k + 1 < Nat.fib (k + 3)
    omega

lemma exists_fib (k : ℕ) (hk : 1 ≤ k) :
    ∃ s, k < Nat.fib (s + 3) ∧ Nat.fib (s + 3) ≤ 2 * k ∧ Nat.fib (s + 2) ≤ k := by
  have hex : ∃ r, k < Nat.fib r := ⟨k + 2, lt_fib k⟩
  have hspec := Nat.find_spec hex
  have hmin := fun m (hm : m < Nat.find hex) => Nat.find_min hex hm
  have h0 : Nat.fib 0 = 0 := rfl
  have h1 : Nat.fib 1 = 1 := rfl
  have h2 : Nat.fib 2 = 1 := rfl
  have h3 : 3 ≤ Nat.find hex := by
    by_contra hlt
    have : Nat.find hex = 0 ∨ Nat.find hex = 1 ∨ Nat.find hex = 2 := by omega
    rcases this with h | h | h <;> rw [h] at hspec <;> omega
  obtain ⟨s, hs⟩ : ∃ s, Nat.find hex = s + 3 := ⟨Nat.find hex - 3, by omega⟩
  rw [hs] at hspec
  have hm := hmin (s + 2) (by omega)
  have e : Nat.fib (s + 3) = Nat.fib (s + 1) + Nat.fib (s + 2) := Nat.fib_add_two
  have hle : Nat.fib (s + 1) ≤ Nat.fib (s + 2) := Nat.fib_mono (by omega)
  exact ⟨s, hspec, by omega, by omega⟩

lemma exists_val : ∀ k, ∃ f, Val k f := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    rcases Nat.eq_zero_or_pos k with hk | hk
    · subst hk
      refine ⟨fun _ => 0, ?_, ?_, ?_⟩
      · intro i hi hik; omega
      · intro i j hi hik; omega
      · intro i _; rfl
    · obtain ⟨s, hs1, hs2, hs3⟩ := exists_fib k hk
      obtain ⟨q, hq⟩ := ih (Nat.fib (s + 3) - 1 - k) (by omega)
      exact ⟨_, ext_val k _ q ⟨s + 3, rfl⟩ hs1 hs2 hq⟩

def g6a : ℕ → ℕ := fun i =>
  if i = 1 then 1 else if i = 2 then 6 else if i = 3 then 5 else if i = 4 then 4
  else if i = 5 then 3 else if i = 6 then 2 else 0

def g6b : ℕ → ℕ := fun i =>
  if i = 1 then 4 else if i = 2 then 6 else if i = 3 then 5 else if i = 4 then 1
  else if i = 5 then 3 else if i = 6 then 2 else 0

def g10a : ℕ → ℕ := fun i =>
  if i = 1 then 2 else if i = 2 then 1 else if i = 3 then 10 else if i = 4 then 9
  else if i = 5 then 8 else if i = 6 then 7 else if i = 7 then 6 else if i = 8 then 5
  else if i = 9 then 4 else if i = 10 then 3 else 0

def g10b : ℕ → ℕ := fun i =>
  if i = 1 then 7 else if i = 2 then 6 else if i = 3 then 10 else if i = 4 then 9
  else if i = 5 then 8 else if i = 6 then 2 else if i = 7 then 1 else if i = 8 then 5
  else if i = 9 then 4 else if i = 10 then 3 else 0

lemma isFib_small (m : ℕ) (h : m = 2 ∨ m = 3 ∨ m = 5 ∨ m = 8 ∨ m = 13) : IsFib m := by
  rcases h with h | h | h | h | h <;> subst h
  · exact ⟨3, by decide⟩
  · exact ⟨4, by decide⟩
  · exact ⟨5, by decide⟩
  · exact ⟨6, by decide⟩
  · exact ⟨7, by decide⟩

lemma val_g6a : Val 6 g6a := by
  refine ⟨?_, ?_, ?_⟩
  · intro i h1 h2
    interval_cases i <;> exact ⟨by decide, by decide, isFib_small _ (by decide)⟩
  · intro i j hi1 hi2 hj1 hj2 h
    interval_cases i <;> interval_cases j <;> first | rfl | exact absurd h (by decide)
  · intro i hi
    unfold g6a
    split_ifs <;> omega

lemma val_g6b : Val 6 g6b := by
  refine ⟨?_, ?_, ?_⟩
  · intro i h1 h2
    interval_cases i <;> exact ⟨by decide, by decide, isFib_small _ (by decide)⟩
  · intro i j hi1 hi2 hj1 hj2 h
    interval_cases i <;> interval_cases j <;> first | rfl | exact absurd h (by decide)
  · intro i hi
    unfold g6b
    split_ifs <;> omega

lemma val_g10a : Val 10 g10a := by
  refine ⟨?_, ?_, ?_⟩
  · intro i h1 h2
    interval_cases i <;> exact ⟨by decide, by decide, isFib_small _ (by decide)⟩
  · intro i j hi1 hi2 hj1 hj2 h
    interval_cases i <;> interval_cases j <;> first | rfl | exact absurd h (by decide)
  · intro i hi
    unfold g10a
    split_ifs <;> omega

lemma val_g10b : Val 10 g10b := by
  refine ⟨?_, ?_, ?_⟩
  · intro i h1 h2
    interval_cases i <;> exact ⟨by decide, by decide, isFib_small _ (by decide)⟩
  · intro i j hi1 hi2 hj1 hj2 h
    interval_cases i <;> interval_cases j <;> first | rfl | exact absurd h (by decide)
  · intro i hi
    unfold g10b
    split_ifs <;> omega

lemma A_bound2 (n : ℕ) : 2 * A (n + 2) + 2 ≤ Nat.fib (n + 6) := by
  obtain ⟨b1, b2, b3, b4⟩ := A_bounds n
  have e4 : Nat.fib (n + 4) = Nat.fib (n + 2) + Nat.fib (n + 3) := Nat.fib_add_two
  have e5 : Nat.fib (n + 5) = Nat.fib (n + 3) + Nat.fib (n + 4) := Nat.fib_add_two
  have e6 : Nat.fib (n + 6) = Nat.fib (n + 4) + Nat.fib (n + 5) := Nat.fib_add_two
  have hA : A (n + 2) = Nat.fib (n + 5) - 1 - A n := rfl
  omega

/-- The arithmetic behind the converse direction. -/
lemma numeric (s j k : ℕ) (h0 : Nat.fib (s + 3) = k + A j + 1) (h1 : Nat.fib (s + 2) ≤ k)
    (h2 : 2 * k < Nat.fib (s + 4)) : k = A (j + 2) ∨ k = 6 ∨ k = 10 := by
  obtain ⟨b1, b2, b3, b4⟩ := A_bounds j
  have e3 : Nat.fib (s + 3) = Nat.fib (s + 1) + Nat.fib (s + 2) := Nat.fib_add_two
  have e4 : Nat.fib (s + 4) = Nat.fib (s + 2) + Nat.fib (s + 3) := Nat.fib_add_two
  have f5 : Nat.fib (j + 5) = Nat.fib (j + 3) + Nat.fib (j + 4) := Nat.fib_add_two
  have f6 : Nat.fib (j + 6) = Nat.fib (j + 4) + Nat.fib (j + 5) := Nat.fib_add_two
  have f4 : Nat.fib (j + 4) = Nat.fib (j + 2) + Nat.fib (j + 3) := Nat.fib_add_two
  have hlow : j + 2 ≤ s := by
    by_contra hlt
    have := Nat.fib_mono (show s + 1 ≤ j + 2 by omega)
    omega
  have hhigh : s ≤ j + 3 := by
    by_contra hlt
    have := Nat.fib_mono (show j + 5 ≤ s + 1 by omega)
    have hpos : 1 ≤ Nat.fib (j + 3) := Nat.fib_pos.2 (by omega)
    omega
  have hA : A (j + 2) = Nat.fib (j + 5) - 1 - A j := rfl
  rcases (show s = j + 2 ∨ s = j + 3 by omega) with hs | hs
  · subst hs
    left
    have e : Nat.fib (j + 2 + 3) = Nat.fib (j + 5) := rfl
    omega
  · subst hs
    right
    have e : Nat.fib (j + 3 + 3) = Nat.fib (j + 6) := rfl
    have e' : Nat.fib (j + 3 + 1) = Nat.fib (j + 4) := rfl
    have e'' : Nat.fib (j + 3 + 2) = Nat.fib (j + 5) := rfl
    rcases (show j = 0 ∨ j = 1 ∨ 2 ≤ j by omega) with hj | hj | hj
    · subst hj
      have hA0 : A 0 = 1 := rfl
      have h6 : Nat.fib (0 + 3 + 3) = 8 := by decide
      omega
    · subst hj
      have hA1 : A 1 = 2 := rfl
      have h7 : Nat.fib (1 + 3 + 3) = 13 := by decide
      omega
    · exfalso
      obtain ⟨m, rfl⟩ : ∃ m, j = m + 2 := ⟨j - 2, by omega⟩
      have := A_bound2 m
      have e7 : Nat.fib (m + 2 + 4) = Nat.fib (m + 6) := rfl
      omega

lemma converse : ∀ k, 1 ≤ k → (∀ f g, Val k f → Val k g → f = g) → ∃ n, A n = k := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk hU
    obtain ⟨s, hs1, hs2, hs3⟩ := exists_fib k hk
    have e4 : Nat.fib (s + 4) = Nat.fib (s + 2) + Nat.fib (s + 3) := Nat.fib_add_two
    have e3 : Nat.fib (s + 3) = Nat.fib (s + 1) + Nat.fib (s + 2) := Nat.fib_add_two
    by_cases hB : Nat.fib (s + 4) ≤ 2 * k
    · exfalso
      obtain ⟨q1, hq1⟩ := exists_val (Nat.fib (s + 3) - 1 - k)
      obtain ⟨q2, hq2⟩ := exists_val (Nat.fib (s + 4) - 1 - k)
      have v1 := ext_val k _ q1 ⟨s + 3, rfl⟩ hs1 hs2 hq1
      have v2 := ext_val k _ q2 ⟨s + 4, rfl⟩ (by omega) hB hq2
      have := congr_fun (hU _ _ v1 v2) k
      rw [ext_top k _ q1 hk hs2, ext_top k _ q2 hk hB] at this
      have hpos : 1 ≤ Nat.fib (s + 2) := Nat.fib_pos.2 (by omega)
      omega
    · have hU' : ∀ f g, Val (Nat.fib (s + 3) - 1 - k) f → Val (Nat.fib (s + 3) - 1 - k) g → f = g := by
        intro f g hf hg
        exact ext_inj k _ f g hs1 hf hg
          (hU _ _ (ext_val k _ f ⟨s + 3, rfl⟩ hs1 hs2 hf) (ext_val k _ g ⟨s + 3, rfl⟩ hs1 hs2 hg))
      rcases Nat.eq_zero_or_pos (Nat.fib (s + 3) - 1 - k) with h0 | hpos
      · -- k = fib (s+3) - 1
        have hs : s ≤ 1 := by
          by_contra hlt
          have := Nat.fib_mono (show 3 ≤ s + 1 by omega)
          have h3 : Nat.fib 3 = 2 := by decide
          omega
        rcases (show s = 0 ∨ s = 1 by omega) with rfl | rfl
        · refine ⟨0, ?_⟩
          have h3 : Nat.fib (0 + 3) = 2 := by decide
          show 1 = k
          omega
        · refine ⟨1, ?_⟩
          have h3 : Nat.fib (1 + 3) = 3 := by decide
          show 2 = k
          omega
      · obtain ⟨j, hj⟩ := ih _ (by omega) hpos hU'
        rcases numeric s j k (by omega) hs3 (by omega) with h | h | h
        · exact ⟨j + 2, h.symm⟩
        · exfalso
          subst h
          have := congr_fun (hU _ _ val_g6a val_g6b) 1
          exact absurd this (by decide)
        · exfalso
          subst h
          have := congr_fun (hU _ _ val_g10a val_g10b) 1
          exact absurd this (by decide)

/-! ### The closed form `⌊F(n+4)/√5⌋` -/

lemma cassini (m : ℕ) :
    ((Nat.fib (m + 1) : ℤ) ^ 2 - Nat.fib (m + 1) * Nat.fib m - (Nat.fib m : ℤ) ^ 2 = 1) ∨
    ((Nat.fib (m + 1) : ℤ) ^ 2 - Nat.fib (m + 1) * Nat.fib m - (Nat.fib m : ℤ) ^ 2 = -1) := by
  induction m with
  | zero => left; simp
  | succ m ih =>
    have e : (Nat.fib (m + 1 + 1) : ℤ) = Nat.fib m + Nat.fib (m + 1) := by
      have : Nat.fib (m + 2) = Nat.fib m + Nat.fib (m + 1) := Nat.fib_add_two
      exact_mod_cast this
    rw [e]
    rcases ih with h | h
    · right; linear_combination (-1 : ℤ) * h
    · left; linear_combination (-1 : ℤ) * h

lemma lucas_rel (n : ℕ) : ∃ r, 1 ≤ r ∧ r ≤ 4 ∧ 5 * A n + r = Nat.fib (n + 5) + Nat.fib (n + 3) := by
  induction n using Nat.twoStepInduction with
  | zero => exact ⟨2, by decide, by decide, by decide⟩
  | one => exact ⟨1, by decide, by decide, by decide⟩
  | more n ih _ =>
    obtain ⟨r, hr1, hr2, hr⟩ := ih
    obtain ⟨b1, b2, b3, b4⟩ := A_bounds n
    have e4 : Nat.fib (n + 4) = Nat.fib (n + 2) + Nat.fib (n + 3) := Nat.fib_add_two
    have e5 : Nat.fib (n + 5) = Nat.fib (n + 3) + Nat.fib (n + 4) := Nat.fib_add_two
    have e6 : Nat.fib (n + 6) = Nat.fib (n + 4) + Nat.fib (n + 5) := Nat.fib_add_two
    have e7 : Nat.fib (n + 7) = Nat.fib (n + 5) + Nat.fib (n + 6) := Nat.fib_add_two
    have hA : A (n + 2) = Nat.fib (n + 5) - 1 - A n := rfl
    refine ⟨5 - r, by omega, by omega, ?_⟩
    show 5 * A (n + 2) + (5 - r) = Nat.fib (n + 7) + Nat.fib (n + 5)
    omega

lemma sq_bounds (n : ℕ) : 5 * (A n) ^ 2 < (Nat.fib (n + 4)) ^ 2 ∧
    (Nat.fib (n + 4)) ^ 2 < 5 * (A n + 1) ^ 2 := by
  obtain ⟨r, hr1, hr2, hr⟩ := lucas_rel n
  have e5 : Nat.fib (n + 5) = Nat.fib (n + 3) + Nat.fib (n + 4) := Nat.fib_add_two
  have hc := cassini (n + 4)
  have h5 : 5 ≤ Nat.fib (n + 5) := by
    have := Nat.fib_mono (show 5 ≤ n + 5 by omega)
    have h : Nat.fib 5 = 5 := by decide
    omega
  have hle : Nat.fib (n + 4) ≤ Nat.fib (n + 5) := Nat.fib_mono (by omega)
  -- work in ℤ
  have hrZ : (5 : ℤ) * A n + r = 2 * Nat.fib (n + 5) - Nat.fib (n + 4) := by
    have : 5 * A n + r + Nat.fib (n + 4) = 2 * Nat.fib (n + 5) := by omega
    have h' : ((5 * A n + r + Nat.fib (n + 4) : ℕ) : ℤ) = ((2 * Nat.fib (n + 5) : ℕ) : ℤ) := by
      rw [this]
    push_cast at h'
    linarith
  have hr1' : (1 : ℤ) ≤ r := by exact_mod_cast hr1
  have hr2' : (r : ℤ) ≤ 4 := by exact_mod_cast hr2
  have h5' : (5 : ℤ) ≤ Nat.fib (n + 5) := by exact_mod_cast h5
  have hle' : (Nat.fib (n + 4) : ℤ) ≤ Nat.fib (n + 5) := by exact_mod_cast hle
  have hA0 : (0 : ℤ) ≤ A n := by positivity
  have hF0 : (0 : ℤ) ≤ Nat.fib (n + 4) := by positivity
  have key : (5 : ℤ) * (A n) ^ 2 < (Nat.fib (n + 4) : ℤ) ^ 2 ∧
      (Nat.fib (n + 4) : ℤ) ^ 2 < 5 * ((A n : ℤ) + 1) ^ 2 := by
    generalize (Nat.fib (n + 5) : ℤ) = y at *
    generalize (Nat.fib (n + 4) : ℤ) = x at *
    generalize (A n : ℤ) = a at *
    generalize (r : ℤ) = ρ at *
    have hL : 2 * y - x = 5 * a + ρ := by linarith
    have hsq : 5 * x ^ 2 = (5 * a + ρ) ^ 2 - 4 ∨ 5 * x ^ 2 = (5 * a + ρ) ^ 2 + 4 := by
      rcases hc with h | h
      · left; rw [← hL]; linear_combination (-4 : ℤ) * h
      · right; rw [← hL]; linear_combination (-4 : ℤ) * h
    have hLge : 5 ≤ 5 * a + ρ := by linarith
    constructor
    · rcases hsq with h | h <;> nlinarith
    · rcases hsq with h | h <;> nlinarith
  constructor
  · exact_mod_cast key.1
  · exact_mod_cast key.2

lemma floor_eq (n : ℕ) : Nat.floor ((Nat.fib (n + 4) : ℝ) / Real.sqrt 5) = A n := by
  obtain ⟨h1, h2⟩ := sq_bounds n
  have s5 : (0 : ℝ) < Real.sqrt 5 := Real.sqrt_pos.2 (by norm_num)
  have s5sq : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have h1' : (5 : ℝ) * (A n : ℝ) ^ 2 < (Nat.fib (n + 4) : ℝ) ^ 2 := by exact_mod_cast h1
  have h2' : (Nat.fib (n + 4) : ℝ) ^ 2 < 5 * ((A n : ℝ) + 1) ^ 2 := by exact_mod_cast h2
  have hA0 : (0 : ℝ) ≤ A n := by positivity
  have hF0 : (0 : ℝ) ≤ Nat.fib (n + 4) := by positivity
  rw [Nat.floor_eq_iff (by positivity)]
  constructor
  · rw [le_div_iff₀ s5]
    by_contra hlt
    push Not at hlt
    have : (Nat.fib (n + 4) : ℝ) ^ 2 < ((A n : ℝ) * Real.sqrt 5) ^ 2 :=
      pow_lt_pow_left₀ hlt hF0 (by norm_num)
    rw [mul_pow, s5sq] at this
    linarith
  · rw [div_lt_iff₀ s5]
    by_contra hge
    push Not at hge
    have : (((A n : ℝ) + 1) * Real.sqrt 5) ^ 2 ≤ (Nat.fib (n + 4) : ℝ) ^ 2 :=
      pow_le_pow_left₀ (by positivity) hge 2
    rw [mul_pow, s5sq] at this
    linarith

/-! ### Bridge to `Equiv.Perm (Fin k)` -/

def toF {k : ℕ} (p : Equiv.Perm (Fin k)) : ℕ → ℕ :=
  fun i => if h : 1 ≤ i ∧ i ≤ k then (p ⟨i - 1, by omega⟩).val + 1 else 0

lemma toF_apply {k : ℕ} (p : Equiv.Perm (Fin k)) (i : Fin k) :
    toF p (i.val + 1) = (p i).val + 1 := by
  unfold toF
  have h : 1 ≤ i.val + 1 ∧ i.val + 1 ≤ k := ⟨by omega, by omega⟩
  rw [dif_pos h]
  have : (⟨i.val + 1 - 1, by omega⟩ : Fin k) = i := Fin.ext (by simp)
  rw [this]

lemma toF_val {k : ℕ} (p : Equiv.Perm (Fin k))
    (hp : ∀ i : Fin k, IsFib ((i.val + 1) + ((p i).val + 1))) : Val k (toF p) := by
  refine ⟨?_, ?_, ?_⟩
  · intro i hi hik
    obtain ⟨m, rfl⟩ : ∃ m, i = m + 1 := ⟨i - 1, by omega⟩
    have := toF_apply p ⟨m, by omega⟩
    simp only at this
    rw [this]
    exact ⟨by omega, by omega, hp ⟨m, by omega⟩⟩
  · intro i j hi hik hj hjk hij
    obtain ⟨m, rfl⟩ : ∃ m, i = m + 1 := ⟨i - 1, by omega⟩
    obtain ⟨m', rfl⟩ : ∃ m', j = m' + 1 := ⟨j - 1, by omega⟩
    have e1 := toF_apply p ⟨m, by omega⟩
    have e2 := toF_apply p ⟨m', by omega⟩
    simp only at e1 e2
    rw [e1, e2] at hij
    have h' : p ⟨m, by omega⟩ = p ⟨m', by omega⟩ := Fin.ext (by omega)
    have := p.injective h'
    have := congr_arg Fin.val this
    simp only at this
    omega
  · intro i hi
    unfold toF
    have : ¬ (1 ≤ i ∧ i ≤ k) := by omega
    rw [dif_neg this]

lemma toF_inj {k : ℕ} (p p' : Equiv.Perm (Fin k)) (h : toF p = toF p') : p = p' := by
  apply Equiv.ext
  intro i
  have := congr_fun h (i.val + 1)
  rw [toF_apply, toF_apply] at this
  exact Fin.ext (by omega)

lemma ofF {k : ℕ} (f : ℕ → ℕ) (hf : Val k f) :
    ∃ p : Equiv.Perm (Fin k), (∀ i : Fin k, IsFib ((i.val + 1) + ((p i).val + 1))) ∧ toF p = f := by
  obtain ⟨hr, hi, ho⟩ := id hf
  have hb : ∀ i : Fin k, f (i.val + 1) - 1 < k := by
    intro i
    have := hr (i.val + 1) (by omega) (by omega)
    omega
  have hinj : Function.Injective (fun i : Fin k => (⟨f (i.val + 1) - 1, hb i⟩ : Fin k)) := by
    intro i j hij
    have h' := congr_arg Fin.val hij
    simp only at h'
    have h1 := hr (i.val + 1) (by omega) (by omega)
    have h2 := hr (j.val + 1) (by omega) (by omega)
    have := hi (i.val + 1) (j.val + 1) (by omega) (by omega) (by omega) (by omega) (by omega)
    exact Fin.ext (by omega)
  have hbij := Finite.injective_iff_bijective.1 hinj
  have hpv : ∀ i : Fin k, ((Equiv.ofBijective _ hbij) i).val + 1 = f (i.val + 1) := by
    intro i
    have h1 := hr (i.val + 1) (by omega) (by omega)
    rw [Equiv.ofBijective_apply]
    simp only
    omega
  refine ⟨Equiv.ofBijective _ hbij, ?_, ?_⟩
  · intro i
    rw [hpv i]
    exact (hr (i.val + 1) (by omega) (by omega)).2.2
  · funext j
    by_cases hj : 1 ≤ j ∧ j ≤ k
    · obtain ⟨m, rfl⟩ : ∃ m, j = m + 1 := ⟨j - 1, by omega⟩
      have e := toF_apply (Equiv.ofBijective _ hbij) ⟨m, by omega⟩
      have e' := hpv ⟨m, by omega⟩
      simp only at e e'
      rw [e, e']
    · rw [(toF_val _ (fun i => by rw [hpv i]; exact (hr (i.val + 1) (by omega) (by omega)).2.2)).2.2 j
        (by omega), ho j (by omega)]

lemma bridge (k : ℕ) : HasUniqueFibPerm k ↔ ∀ f g, Val k f → Val k g → f = g := by
  constructor
  · rintro ⟨p, hp, hpu⟩ f g hf hg
    obtain ⟨pf, hpf, rfl⟩ := ofF f hf
    obtain ⟨pg, hpg, rfl⟩ := ofF g hg
    rw [hpu pf hpf, hpu pg hpg]
  · intro hU
    obtain ⟨f, hf⟩ := exists_val k
    obtain ⟨p, hp, rfl⟩ := ofF f hf
    exact ⟨p, hp, fun p' hp' => toF_inj _ _ (hU _ _ (toF_val p' hp') hf)⟩

lemma final :
    {k : ℕ | 0 < k ∧ HasUniqueFibPerm k} =
      Set.range (fun n : ℕ => Nat.floor ((Nat.fib (n + 4) : ℝ) / Real.sqrt 5)) := by
  ext k
  simp only [Set.mem_ofPred_eq, Set.mem_range]
  constructor
  · rintro ⟨hk, hU⟩
    obtain ⟨n, hn⟩ := converse k hk ((bridge k).1 hU)
    exact ⟨n, by rw [floor_eq, hn]⟩
  · rintro ⟨n, hn⟩
    rw [floor_eq] at hn
    subst hn
    have hpos : 1 ≤ Nat.fib (n + 2) := Nat.fib_pos.2 (by omega)
    exact ⟨by have := (A_bounds n).1; omega, (bridge _).2 (uniq_inv n).1⟩

end A097083

theorem OMA.solution : type_of% @OMA.S_oeis_a097083.main := A097083.final
