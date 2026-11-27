import FormalConjectures.ErdosProblems.«539»

-- Problem: Erdős Problem 539 — isBigO sq cube root
-- Upstream: formal-conjectures FormalConjectures/ErdosProblems/539.lean:111 (declaration Erdos539.erdos_539.variants.isBigO_sq_cube_root)
-- Credit: @senamakel (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.
--
-- Construction (Granville-Roesler style): A is n elements of {2^x 3^(m-x+j) : x <= m, j < w}
-- with m = w^2 and w = ceil(n^(1/3)). Every cofactor a/(a,b) is 2^d 3^e with (d,e) in
-- [0,m] x {0}, [0,w) x [0,w) or {0} x [0,m+w), so there are at most 3w^2+w+1 = O(n^(2/3)).

open Finset Filter Erdos539

namespace OMA539

lemma gcd_two_pow (x x' : ℕ) : Nat.gcd (2^x) (2^x') = 2^(min x x') := by
  rcases le_total x x' with h | h
  · rw [min_eq_left h]; exact Nat.gcd_eq_left (pow_dvd_pow 2 h)
  · rw [min_eq_right h]; exact Nat.gcd_eq_right (pow_dvd_pow 2 h)

lemma gcd_three_pow (x x' : ℕ) : Nat.gcd (3^x) (3^x') = 3^(min x x') := by
  rcases le_total x x' with h | h
  · rw [min_eq_left h]; exact Nat.gcd_eq_left (pow_dvd_pow 3 h)
  · rw [min_eq_right h]; exact Nat.gcd_eq_right (pow_dvd_pow 3 h)

lemma cop (a b : ℕ) : Nat.Coprime (2^a) (3^b) :=
  Nat.Coprime.pow a b (by norm_num)

lemma gcd_23 (x y x' y' : ℕ) :
    Nat.gcd (2^x*3^y) (2^x'*3^y') = 2^(min x x') * 3^(min y y') := by
  rw [Nat.Coprime.gcd_mul _ (cop x' y')]
  have h1 : Nat.gcd (2^x*3^y) (2^x') = 2^(min x x') := by
    rw [Nat.Coprime.gcd_mul_right_cancel _ ((cop x' y).symm)]
    exact gcd_two_pow x x'
  have h2 : Nat.gcd (2^x*3^y) (3^y') = 3^(min y y') := by
    rw [mul_comm, Nat.Coprime.gcd_mul_right_cancel _ (cop x y')]
    exact gcd_three_pow y y'
  rw [h1, h2]

lemma cof_23 (x y x' y' : ℕ) :
    (2^x*3^y) / Nat.gcd (2^x*3^y) (2^x'*3^y') = 2^(x-x') * 3^(y-y') := by
  rw [gcd_23]
  apply Nat.div_eq_of_eq_mul_left (by positivity)
  have e1 : x = (x - x') + min x x' := by omega
  have e2 : y = (y - y') + min y y' := by omega
  conv_lhs => rw [e1, e2]
  rw [pow_add, pow_add]; ring

lemma inj_23 {x y x' y' : ℕ} (h : 2^x*3^y = 2^x'*3^y') : x = x' ∧ y = y' := by
  have h2 := congrArg (fun n => n.factorization 2) h
  have h3 := congrArg (fun n => n.factorization 3) h
  simp [Nat.factorization_mul, Nat.prime_two, Nat.prime_three] at h2 h3
  exact ⟨h2, h3⟩

lemma key (n w : ℕ) (hn : n ≤ w^3) : cofactorThreshold n ≤ 3 * w^2 + w + 1 := by
  set m := w^2 with hm
  let f : ℕ × ℕ → ℕ := fun p => 2^p.1 * 3^(m - p.1 + p.2)
  let D := range (m+1) ×ˢ range w
  have hinj : Set.InjOn f D := by
    rintro ⟨x, j⟩ hx ⟨x', j'⟩ hx' he
    simp only [D, coe_product, Set.mem_prod, mem_coe, mem_range] at hx hx'
    obtain ⟨h1, h2⟩ := inj_23 he
    simp only [Prod.mk.injEq]; omega
  have hcard : n ≤ #(D.image f) := by
    rw [card_image_of_injOn hinj]
    simp only [D, card_product, card_range]
    calc n ≤ w^3 := hn
      _ ≤ (m+1)*w := by rw [hm]; nlinarith
  obtain ⟨A, hAsub, hAcard⟩ := exists_subset_card_eq hcard
  let T : Finset (ℕ × ℕ) := (range (m+1) ×ˢ {0}) ∪ (range w ×ˢ range w) ∪ ({0} ×ˢ range (m+w))
  let g : ℕ × ℕ → ℕ := fun p => 2^p.1 * 3^p.2
  have hsub : ((A ×ˢ A).image fun (p : ℕ × ℕ) ↦ p.1 / p.1.gcd p.2) ⊆ T.image g := by
    intro c hc
    simp only [mem_image, mem_product, Prod.exists] at hc
    obtain ⟨a, b, ⟨ha, hb⟩, rfl⟩ := hc
    have ha' := hAsub ha
    have hb' := hAsub hb
    simp only [D, f, mem_image, mem_product, mem_range, Prod.exists] at ha' hb'
    obtain ⟨x, j, ⟨hx, hj⟩, rfl⟩ := ha'
    obtain ⟨x', j', ⟨hx', hj'⟩, rfl⟩ := hb'
    rw [cof_23]
    simp only [T, g, mem_image, mem_union, mem_product, mem_range, mem_singleton, Prod.exists]
    refine ⟨x - x', (m - x + j) - (m - x' + j'), ?_, rfl⟩
    omega
  have hle : #((A ×ˢ A).image fun (p : ℕ × ℕ) ↦ p.1 / p.1.gcd p.2) ≤ 3 * w^2 + w + 1 := by
    refine (card_le_card hsub).trans (card_image_le.trans ?_)
    have u1 := card_union_le ((range (m+1) ×ˢ {0}) ∪ (range w ×ˢ range w)) ({0} ×ˢ range (m+w))
    have u2 := card_union_le (range (m+1) ×ˢ ({0} : Finset ℕ)) (range w ×ˢ range w)
    simp only [card_product, card_range, card_singleton] at u1 u2
    simp only [T]
    rw [hm] at u1 u2 ⊢; nlinarith
  apply csSup_le ⟨0, by intro B _; exact Nat.zero_le _⟩
  intro k hk
  exact (hk A hAcard).trans hle

end OMA539

open OMA539 in
theorem OMA.solution : type_of% @Erdos539.erdos_539.variants.isBigO_sq_cube_root := by
  refine Asymptotics.IsBigO.of_bound 15 ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  set t : ℝ := (n : ℝ) ^ ((1 : ℝ) / 3) with ht
  have t1 : 1 ≤ t := Real.one_le_rpow hn' (by norm_num)
  have t3 : t ^ 3 = n := by
    rw [ht, ← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]; norm_num
  have t2 : t ^ 2 = (n : ℝ) ^ ((2 : ℝ) / 3) := by
    rw [ht, ← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]; norm_num
  set w := ⌈t⌉₊ with hw
  have hw1 : t ≤ w := Nat.le_ceil t
  have hw2 : (w : ℝ) < t + 1 := Nat.ceil_lt_add_one (by linarith)
  have hnw : n ≤ w^3 := by
    have : (n : ℝ) ≤ (w : ℝ)^3 := by rw [← t3]; exact pow_le_pow_left₀ (by linarith) hw1 3
    exact_mod_cast this
  have hk := key n w hnw
  have hk' : (cofactorThreshold n : ℝ) ≤ 3 * (w : ℝ)^2 + w + 1 := by exact_mod_cast hk
  rw [Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (by positivity), ← t2]
  nlinarith
