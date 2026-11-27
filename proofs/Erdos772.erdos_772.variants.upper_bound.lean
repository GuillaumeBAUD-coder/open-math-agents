import FormalConjectures.ErdosProblems.«772»

-- Problem: Erdős Problem 772 — upper bound
-- Upstream: formal-conjectures FormalConjectures/ErdosProblems/772.lean:90 (declaration Erdos772.erdos_772.variants.upper_bound)
-- Credit: @senamakel (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

open Filter Finset AdditiveCombinatorics

namespace OMA772

open Erdos772

lemma pow2_sidon_le {a b c d : ℕ} (hab : a ≤ b) (hcd : c ≤ d)
    (h : 2 ^ a + 2 ^ b = 2 ^ c + 2 ^ d) : a = c ∧ b = d := by
  have key : ∀ a b c d : ℕ, a ≤ b → c ≤ d → a < c → 2 ^ a + 2 ^ b ≠ 2 ^ c + 2 ^ d := by
    intro a b c d hab hcd hac h
    obtain ⟨l, rfl⟩ := Nat.exists_eq_add_of_le hab
    obtain ⟨i, rfl⟩ := Nat.exists_eq_add_of_lt hac
    obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hcd
    have h2 : 2 ^ a * (1 + 2 ^ l) = 2 ^ a * (2 * 2 ^ i + 2 * 2 ^ i * 2 ^ j) := by
      rw [mul_add, mul_add, ← pow_add, mul_one]
      rw [h]; ring
    have h3 := Nat.eq_of_mul_eq_mul_left (by positivity) h2
    have hP : 1 ≤ 2 ^ i := Nat.one_le_two_pow
    have hQ : 1 ≤ 2 ^ j := Nat.one_le_two_pow
    have h4 : 1 + 2 ^ l = 2 * (2 ^ i + 2 ^ i * 2 ^ j) := by rw [h3]; ring
    have h5 : 2 ≤ 2 ^ i + 2 ^ i * 2 ^ j := by nlinarith
    rcases l with _ | l
    · rw [pow_zero] at h4
      generalize 2 ^ i + 2 ^ i * 2 ^ j = R at h4 h5
      omega
    · rw [pow_succ] at h4
      generalize 2 ^ i + 2 ^ i * 2 ^ j = R at h4 h5
      generalize 2 ^ l = L at h4
      omega
  rcases lt_trichotomy a c with hac | hac | hac
  · exact absurd h (key a b c d hab hcd hac)
  · subst hac
    exact ⟨rfl, Nat.pow_right_injective le_rfl (Nat.add_left_cancel h)⟩
  · exact absurd h.symm (key c d a b hcd hab hac)

lemma pow2_sidon {a b c d : ℕ} (h : 2 ^ a + 2 ^ b = 2 ^ c + 2 ^ d) :
    (a = c ∧ b = d) ∨ (a = d ∧ b = c) := by
  rcases le_total a b with hab | hab <;> rcases le_total c d with hcd | hcd
  · exact Or.inl (pow2_sidon_le hab hcd h)
  · have := pow2_sidon_le hab hcd (by rw [h, add_comm])
    exact Or.inr ⟨this.1, this.2⟩
  · have := pow2_sidon_le hab hcd (by rw [add_comm, h])
    exact Or.inr ⟨this.2, this.1⟩
  · have := pow2_sidon_le hab hcd (by rw [add_comm, h, add_comm])
    exact Or.inl ⟨this.2, this.1⟩

/-- The encoding of the grid point `(a, b)`. -/
def x (m a b : ℕ) : ℕ := 2 ^ a + 2 ^ (m + 1) * 2 ^ b

lemma decode {T u v u' v' : ℕ} (hu : u < T) (hu' : u' < T) (h : u + T * v = u' + T * v') :
    u = u' ∧ v = v' := by
  have hT : 0 < T := by omega
  have h1 := congrArg (· % T) h
  have h2 := congrArg (· / T) h
  simp only [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hu, Nat.mod_eq_of_lt hu'] at h1
  simp only [Nat.add_mul_div_left _ _ hT, Nat.div_eq_of_lt hu, Nat.div_eq_of_lt hu',
    zero_add] at h2
  exact ⟨h1, h2⟩

lemma small {m a a' : ℕ} (ha : a < m) (ha' : a' < m) : 2 ^ a + 2 ^ a' < 2 ^ (m + 1) := by
  have h1 : 2 ^ a < 2 ^ m := Nat.pow_lt_pow_right (by norm_num) ha
  have h2 : 2 ^ a' < 2 ^ m := Nat.pow_lt_pow_right (by norm_num) ha'
  rw [pow_succ]
  omega

lemma x_add_eq {m a b a' b' c d c' d' : ℕ} (ha : a < m) (ha' : a' < m) (hc : c < m)
    (hc' : c' < m) (h : x m a b + x m a' b' = x m c d + x m c' d') :
    2 ^ a + 2 ^ a' = 2 ^ c + 2 ^ c' ∧ 2 ^ b + 2 ^ b' = 2 ^ d + 2 ^ d' := by
  have e1 : x m a b + x m a' b' = (2 ^ a + 2 ^ a') + 2 ^ (m + 1) * (2 ^ b + 2 ^ b') := by
    unfold x; ring
  have e2 : x m c d + x m c' d' = (2 ^ c + 2 ^ c') + 2 ^ (m + 1) * (2 ^ d + 2 ^ d') := by
    unfold x; ring
  rw [e1, e2] at h
  exact decode (small ha ha') (small hc hc') h

lemma x_inj {m a b c d : ℕ} (ha : a < m) (hc : c < m) (h : x m a b = x m c d) :
    a = c ∧ b = d := by
  have := x_add_eq ha ha hc hc (by rw [h])
  rcases pow2_sidon this.1 with h1 | h1 <;> rcases pow2_sidon this.2 with h2 | h2 <;>
    exact ⟨h1.1, h2.1⟩

/-- The grid image. -/
def grid (m : ℕ) : Finset ℕ :=
  ((range m) ×ˢ (range (m * m))).image (fun p => x m p.1 p.2)

lemma mem_grid {m y : ℕ} (hy : y ∈ grid m) : ∃ a < m, ∃ b, y = x m a b := by
  unfold grid at hy
  obtain ⟨⟨a, b⟩, hp, rfl⟩ := Finset.mem_image.1 hy
  exact ⟨a, (Finset.mem_range.1 (Finset.mem_product.1 hp).1), b, rfl⟩

lemma card_grid (m : ℕ) : #(grid m) = m * (m * m) := by
  unfold grid
  rw [Finset.card_image_of_injOn, Finset.card_product, Finset.card_range, Finset.card_range]
  rintro ⟨a, b⟩ hp ⟨c, d⟩ hq h
  simp only [Finset.coe_product, Set.mem_prod, Finset.coe_range, Set.mem_Iio] at hp hq
  have h' : x m a b = x m c d := h
  obtain ⟨h1, h2⟩ := x_inj hp.1 hq.1 h'
  rw [h1, h2]

lemma card4 {m s : ℕ} (F : Finset (ℕ × ℕ))
    (hmem : ∀ p ∈ F, p.1 + p.2 = s ∧ p.1 ∈ grid m ∧ p.2 ∈ grid m) : #F ≤ 4 := by
  classical
  rcases F.eq_empty_or_nonempty with hF | ⟨p0, hp0⟩
  · rw [hF]; simp
  obtain ⟨hs0, g1, g2⟩ := hmem p0 hp0
  obtain ⟨a, ha, b, hb⟩ := mem_grid g1
  obtain ⟨a', ha', b', hb'⟩ := mem_grid g2
  have hsub : F ⊆ {(x m a b, x m a' b'), (x m a b', x m a' b), (x m a' b, x m a b'),
      (x m a' b', x m a b)} := by
    intro p hp
    obtain ⟨hs, h1, h2⟩ := hmem p hp
    obtain ⟨c, hc, d, hd⟩ := mem_grid h1
    obtain ⟨c', hc', d', hd'⟩ := mem_grid h2
    have heq : x m c d + x m c' d' = x m a b + x m a' b' := by
      rw [← hd, ← hd', hs, ← hb, ← hb', hs0]
    obtain ⟨e1, e2⟩ := x_add_eq hc hc' ha ha' heq
    have hp' : p = (x m c d, x m c' d') := by
      rw [← hd, ← hd']
    simp only [Finset.mem_insert, Finset.mem_singleton, hp', Prod.mk.injEq]
    rcases pow2_sidon e1 with ⟨r1, r2⟩ | ⟨r1, r2⟩ <;>
      rcases pow2_sidon e2 with ⟨r3, r4⟩ | ⟨r3, r4⟩ <;> subst r1 r2 r3 r4 <;> simp
  exact (Finset.card_le_card hsub).trans Finset.card_le_four

lemma sumRep_le {m : ℕ} {A : Finset ℕ} (hA : A ⊆ grid m) (s : ℕ) :
    sumRep (A : Set ℕ) s ≤ 4 := by
  rw [sumRep_def]
  apply card4 (m := m)
  intro p hp
  simp only [Finset.mem_filter, Finset.HasAntidiagonal.mem_antidiagonal, Finset.mem_coe] at hp
  exact ⟨hp.1, hA hp.2.1, hA hp.2.2⟩

lemma card_filter_prod {α β : Type*} (Y : Finset β) (X : Finset α) (q : β → α → Prop)
    [∀ b a, Decidable (q b a)] :
    #((Y ×ˢ X).filter (fun p => q p.1 p.2)) = ∑ y ∈ Y, #(X.filter (fun x => q y x)) := by
  rw [Finset.card_filter, Finset.sum_product]
  refine Finset.sum_congr rfl (fun y _ => ?_)
  rw [Finset.card_filter]

lemma kst {α β : Type*} [DecidableEq α] (X : Finset α) (Y : Finset β) (R : α → β → Prop)
    [∀ a b, Decidable (R a b)] (k : ℕ)
    (h : ∀ x ∈ X, ∀ x' ∈ X, x ≠ x' → #(Y.filter (fun y => R x y ∧ R x' y)) ≤ k) :
    (∑ y ∈ Y, #(X.filter (fun x => R x y))) ^ 2 ≤
      #Y * (∑ y ∈ Y, #(X.filter (fun x => R x y)) + #X * #X * k) := by
  refine (sq_sum_le_card_mul_sum_sq).trans (Nat.mul_le_mul_left _ ?_)
  have key : ∑ y ∈ Y, #(X.filter (fun x => R x y)) ^ 2
      = ∑ x ∈ X, ∑ x' ∈ X, #(Y.filter (fun y => R x y ∧ R x' y)) := by
    simp only [Finset.card_filter, sq, Finset.sum_mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun x _ => ?_)
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun x' _ => ?_)
    refine Finset.sum_congr rfl (fun y _ => ?_)
    by_cases h1 : R x y <;> by_cases h2 : R x' y <;> simp [h1, h2]
  have hswap : ∑ y ∈ Y, #(X.filter (fun x => R x y)) =
      ∑ x ∈ X, #(Y.filter (fun y => R x y)) := by
    simp only [Finset.card_filter]
    rw [Finset.sum_comm]
  rw [key, hswap]
  have hx : ∀ x ∈ X, ∑ x' ∈ X, #(Y.filter (fun y => R x y ∧ R x' y)) ≤
      #(Y.filter (fun y => R x y)) + #X * k := by
    intro x hxX
    rw [← Finset.add_sum_erase X _ hxX]
    refine Nat.add_le_add (le_of_eq (by simp)) ?_
    calc ∑ x' ∈ X.erase x, #(Y.filter (fun y => R x y ∧ R x' y))
        ≤ ∑ x' ∈ X.erase x, k := by
          refine Finset.sum_le_sum (fun x' hx' => ?_)
          exact h x hxX x' (Finset.mem_of_mem_erase hx') (Finset.ne_of_mem_erase hx').symm
      _ ≤ #X * k := by
          rw [Finset.sum_const, smul_eq_mul]
          exact Nat.mul_le_mul_right _ (Finset.card_erase_le)
  calc ∑ x ∈ X, ∑ x' ∈ X, #(Y.filter (fun y => R x y ∧ R x' y))
      ≤ ∑ x ∈ X, (#(Y.filter (fun y => R x y)) + #X * k) := Finset.sum_le_sum hx
    _ = ∑ x ∈ X, #(Y.filter (fun y => R x y)) + #X * #X * k := by
        rw [Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, mul_assoc]

lemma arith (e m : ℕ) (h : e ^ 2 ≤ m * m * (e + m * m * 1)) : e ≤ 2 * (m * m) := by
  by_contra hc
  push Not at hc
  nlinarith

lemma sidon_le {m : ℕ} {S : Finset ℕ} (hS : S ⊆ grid m) (hsid : IsSidon (S : Set ℕ)) :
    #S ≤ 2 * (m * m) := by
  classical
  set e := ∑ b ∈ range (m * m), #((range m).filter (fun a => x m a b ∈ S)) with he
  have hSe : #S ≤ e := by
    have hsub : S ⊆ (((range (m * m)) ×ˢ (range m)).filter
        (fun p => x m p.2 p.1 ∈ S)).image (fun p => x m p.2 p.1) := by
      intro y hy
      have hg := hS hy
      unfold grid at hg
      obtain ⟨⟨a, b⟩, hp, rfl⟩ := Finset.mem_image.1 hg
      rw [Finset.mem_product] at hp
      exact Finset.mem_image.2 ⟨(b, a), Finset.mem_filter.2
        ⟨Finset.mem_product.2 ⟨hp.2, hp.1⟩, hy⟩, rfl⟩
    calc #S ≤ #((((range (m * m)) ×ˢ (range m)).filter
          (fun p => x m p.2 p.1 ∈ S)).image (fun p => x m p.2 p.1)) := Finset.card_le_card hsub
      _ ≤ #(((range (m * m)) ×ˢ (range m)).filter (fun p => x m p.2 p.1 ∈ S)) :=
          Finset.card_image_le
      _ = e := card_filter_prod (range (m * m)) (range m) (fun b a => x m a b ∈ S)
  have hk := kst (range m) (range (m * m)) (fun a b => x m a b ∈ S) 1 (by
    intro a ha a' ha' haa'
    rw [Finset.card_le_one]
    intro b hb b' hb'
    simp only [Finset.mem_filter] at hb hb'
    have ham := Finset.mem_range.1 ha
    have ham' := Finset.mem_range.1 ha'
    by_contra hbb
    have hsum : x m a b + x m a' b' = x m a b' + x m a' b := by unfold x; ring
    rcases hsid _ hb.2.1 _ hb'.2.1 _ hb'.2.2 _ hb.2.2 hsum with h | h
    · exact hbb (x_inj ham ham h.1).2
    · exact haa' (x_inj ham ham' h.1).1)
  rw [Finset.card_range, Finset.card_range] at hk
  exact hSe.trans (arith e m hk)

lemma H_le (k n : ℕ) (hk : 4 ≤ k) (m : ℕ) (hm : n ≤ m * (m * m)) : H k n ≤ 2 * (m * m) := by
  obtain ⟨A, hAg, hAn⟩ := Finset.exists_subset_card_eq (s := grid m) (n := n)
    (by rw [card_grid]; exact hm)
  unfold H
  apply csSup_le'
  rintro r ⟨_, hr⟩
  obtain ⟨S, hSA, hsid, hrS⟩ := hr A hAn (fun s => (sumRep_le hAg s).trans hk)
  exact hrS.trans (sidon_le (hSA.trans hAg) hsid)

end OMA772

theorem OMA.solution : type_of% @Erdos772.erdos_772.variants.upper_bound := by
  refine ⟨8, fun k hk => ?_⟩
  filter_upwards [Filter.eventually_ge_atTop 1] with n hn
  set y : ℝ := (n : ℝ) ^ (1 / 3 : ℝ) with hy
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hy0 : 0 ≤ y := Real.rpow_nonneg hn0 _
  have hy3 : y ^ 3 = n := by
    rw [hy, ← Real.rpow_natCast, ← Real.rpow_mul hn0]
    norm_num
  have hy2 : y ^ 2 = (n : ℝ) ^ (2 / 3 : ℝ) := by
    rw [hy, ← Real.rpow_natCast, ← Real.rpow_mul hn0]
    norm_num
  have hy1 : 1 ≤ y := by
    by_contra hlt
    push Not at hlt
    have : y ^ 3 < 1 := by
      calc y ^ 3 ≤ y ^ 1 := pow_le_pow_of_le_one hy0 hlt.le (by norm_num)
        _ < 1 := by simpa using hlt
    rw [hy3] at this
    have : (1 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  set m := ⌈y⌉₊ with hm
  have hm1 : y ≤ (m : ℝ) := Nat.le_ceil y
  have hm2 : (m : ℝ) < y + 1 := Nat.ceil_lt_add_one hy0
  have hcube : n ≤ m * (m * m) := by
    have : (n : ℝ) ≤ (m : ℝ) * ((m : ℝ) * m) := by
      rw [← hy3]
      have := pow_le_pow_left₀ hy0 hm1 3
      nlinarith [this]
    exact_mod_cast this
  have hH := OMA772.H_le k n hk m hcube
  have hHR : (Erdos772.H k n : ℝ) ≤ 2 * ((m : ℝ) * m) := by exact_mod_cast hH
  rw [← hy2]
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  nlinarith
