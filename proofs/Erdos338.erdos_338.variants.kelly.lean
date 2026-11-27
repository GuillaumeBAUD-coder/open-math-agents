import FormalConjectures.ErdosProblems.«338»

-- Problem: Erdős Problem 338 — kelly
-- Upstream: formal-conjectures FormalConjectures/ErdosProblems/338.lean:174 (declaration Erdos338.erdos_338.variants.kelly)
-- Credit: @rorcores (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

/-!
Kelly's theorem: a basis of order 2 has restricted order at most 4.

Write `T` for a threshold beyond which every number is an element of `A` or a sum of two elements
of `A`, and call `m` good if it is a sum of at most four distinct elements of `A`. A bad `m ≥ T`
is `2 * a` with `a ∈ A`. For such a bad `m = 2 * a` with `a ≥ T`:

* (above)  if `b ∈ A`, `a < b` and `m - b ≥ T`, then `m - b` is not in `A`, is not a sum of two
  distinct elements of `A`, and so is twice an element of `A`; in particular `b` is even;
* (odd_compl)  if `o ∈ A` is odd and `o < a`, then `m - 2 * o ∈ A`;
* (half_mem)  if `o ∈ A` is odd, `v ∈ A` is even, `v ≥ T` and `o + 2 * v, 2 * o + v < a`, then
  `o + v / 2 ∈ A` and `o + v ∉ A`;
* (no_mult_four)  hence `A` has no element `v ≥ T` divisible by 4 that is small compared to `a`
  (apply half_mem to `o, v` and then to `o + v / 2, v`);
* (diff_mem)  if `x < y` are odd elements of `A` with `2 * y - x ≥ T` and `2 * y ≤ a`, then
  `2 * (y - x) ∈ A`, which is divisible by 4.

So if `A` has two odd elements that are at least `T / 2` apart, bad numbers are bounded. Otherwise
the odd elements of `A` are bounded, so every large odd number is an odd element plus a large even
element; if all large even elements are 2 mod 4, both residues mod 4 occur among the odd elements,
and half_mem applied to two odd elements of different residues and one even element produces two
large even elements that differ by 2 mod 4, a contradiction again.
-/

namespace OMA.Kelly

/-- `Good A m`: `m` is a sum of at most four distinct elements of `A`. -/
def Good (A : Set ℕ) (m : ℕ) : Prop :=
  ∃ S : Finset ℕ, (∀ x ∈ S, x ∈ A) ∧ S.card ≤ 4 ∧ ∑ x ∈ S, x = m

/-- `Rep A T`: every `n ≥ T` is an element of `A` or a sum of two elements of `A`. -/
def Rep (A : Set ℕ) (T : ℕ) : Prop :=
  ∀ n, T ≤ n → (n ∈ A ∨ ∃ x ∈ A, ∃ y ∈ A, x + y = n)

lemma good1 {A : Set ℕ} {m : ℕ} (h : m ∈ A) : Good A m :=
  ⟨{m}, by simpa using h, by simp, by simp⟩

lemma good2 {A : Set ℕ} {x y m : ℕ} (hx : x ∈ A) (hy : y ∈ A) (hxy : x ≠ y)
    (hm : x + y = m) : Good A m := by
  refine ⟨{x, y}, ?_, ?_, ?_⟩
  · intro z hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl <;> assumption
  · rw [Finset.card_pair hxy]; omega
  · rw [Finset.sum_pair hxy]; exact hm

lemma good3 {A : Set ℕ} {x y z m : ℕ} (hx : x ∈ A) (hy : y ∈ A) (hz : z ∈ A)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) (hm : x + y + z = m) : Good A m := by
  refine ⟨{x, y, z}, ?_, ?_, ?_⟩
  · intro w hw
    simp only [Finset.mem_insert, Finset.mem_singleton] at hw
    rcases hw with rfl | rfl | rfl <;> assumption
  · exact le_trans Finset.card_le_three (by norm_num)
  · rw [Finset.sum_insert (by simp [hxy, hxz]), Finset.sum_pair hyz]; omega

lemma good4 {A : Set ℕ} {x y z w m : ℕ} (hx : x ∈ A) (hy : y ∈ A) (hz : z ∈ A) (hw : w ∈ A)
    (hxy : x ≠ y) (hxz : x ≠ z) (hxw : x ≠ w) (hyz : y ≠ z) (hyw : y ≠ w) (hzw : z ≠ w)
    (hm : x + y + z + w = m) : Good A m := by
  refine ⟨{x, y, z, w}, ?_, ?_, ?_⟩
  · intro u hu
    simp only [Finset.mem_insert, Finset.mem_singleton] at hu
    rcases hu with rfl | rfl | rfl | rfl <;> assumption
  · exact Finset.card_le_four
  · rw [Finset.sum_insert (by simp [hxy, hxz, hxw]), Finset.sum_insert (by simp [hyz, hyw]),
      Finset.sum_pair hzw]
    omega

/-- A basis of order 2 has a threshold `T ≥ 1` beyond which every number is an element or a sum
of two elements. -/
lemma rep_of_hasOrder {A : Set ℕ} (hA : Erdos338.HasOrder A 2) : ∃ T : ℕ, 1 ≤ T ∧ Rep A T := by
  obtain ⟨T₀, hT₀⟩ := Filter.eventually_atTop.1 hA
  refine ⟨T₀ + 1, by omega, fun n hn => ?_⟩
  obtain ⟨S, hS, hcard, hsum⟩ := hT₀ n (by omega)
  have h3 : S.card = 0 ∨ S.card = 1 ∨ S.card = 2 := by omega
  rcases h3 with h | h | h
  · rw [Multiset.card_eq_zero] at h
    subst h
    simp at hsum
    omega
  · obtain ⟨x, rfl⟩ := Multiset.card_eq_one.1 h
    left
    simp at hsum
    subst hsum
    exact hS x (by simp)
  · obtain ⟨x, y, rfl⟩ := Multiset.card_eq_two.1 h
    right
    exact ⟨x, hS x (by simp), y, hS y (by simp), by simpa using hsum⟩

/-- If `2 * a` is bad, `b ∈ A` lies above `a` and `n = 2 * a - b ≥ T`, then `n` is not in `A`,
is not a sum of two distinct elements of `A`, and is twice an element of `A`. -/
lemma above {A : Set ℕ} {T a : ℕ} (hT : Rep A T) (hbad : ¬ Good A (2 * a))
    {b n : ℕ} (hb : b ∈ A) (hab : a < b) (hn : b + n = 2 * a) (hTn : T ≤ n) :
    n ∉ A ∧ (∀ x ∈ A, ∀ y ∈ A, x ≠ y → x + y ≠ n) ∧ ∃ c ∈ A, c + c = n := by
  have h1 : n ∉ A := fun h => hbad (good2 hb h (by omega) hn)
  have h2 : ∀ x ∈ A, ∀ y ∈ A, x ≠ y → x + y ≠ n := by
    intro x hx y hy hxy hsum
    exact hbad (good3 hb hx hy (by omega) (by omega) hxy (by omega))
  refine ⟨h1, h2, ?_⟩
  rcases hT n hTn with h | ⟨x, hx, y, hy, hxy⟩
  · exact absurd h h1
  · by_cases hne : x = y
    · subst hne
      exact ⟨x, hx, hxy⟩
    · exact absurd hxy (h2 x hx y hy hne)

/-- If `2 * a` is bad and `o < a` is an odd element of `A`, then `2 * a - 2 * o ∈ A`. -/
lemma odd_compl {A : Set ℕ} {T a : ℕ} (hT : Rep A T) (hTa : T ≤ a) (hbad : ¬ Good A (2 * a))
    {o e : ℕ} (ho : o ∈ A) (hodd : o % 2 = 1) (hoa : o < a) (he : e + 2 * o = 2 * a) :
    e ∈ A := by
  rcases hT (e + o) (by omega) with h | ⟨x, hx, y, hy, hxy⟩
  · exact absurd (good2 ho h (by omega) (by omega)) hbad
  · by_cases h1 : x = o
    · have : y = e := by omega
      exact this ▸ hy
    · by_cases h2 : y = o
      · have : x = e := by omega
        exact this ▸ hx
      · exact absurd (good3 ho hx hy (Ne.symm h1) (Ne.symm h2) (by omega) (by omega)) hbad

/-- If `2 * a` is bad, `o ∈ A` is odd, `v ∈ A` is even with `v ≥ T`, and `o + 2 * v`, `2 * o + v`
are below `a`, then `o + v / 2 ∈ A` and `o + v ∉ A`. -/
lemma half_mem {A : Set ℕ} {T a : ℕ} (hT : Rep A T) (hT1 : 1 ≤ T) (hTa : T ≤ a)
    (hbad : ¬ Good A (2 * a)) {o v : ℕ} (ho : o ∈ A) (hodd : o % 2 = 1) (hv : v ∈ A)
    (hev : v % 2 = 0) (hTv : T ≤ v) (h1 : o + 2 * v < a) (h2 : 2 * o + v < a) :
    o + v / 2 ∈ A ∧ o + v ∉ A := by
  obtain ⟨n, hn⟩ : ∃ n, n + o + v = 2 * a := ⟨2 * a - o - v, by omega⟩
  have keyv : ∀ y ∈ A, y + o + 2 * v = 2 * a → False := by
    intro y hy hsum
    obtain ⟨-, -, c, -, hc⟩ :=
      above hT hbad hy (by omega) (n := o + 2 * v) (by omega) (by omega)
    omega
  have keyo : ∀ y ∈ A, y + 2 * o + v = 2 * a → o + v / 2 ∈ A ∧ o + v ∉ A := by
    intro y hy hsum
    obtain ⟨-, hdist, c, hc, hcc⟩ :=
      above hT hbad hy (by omega) (n := 2 * o + v) (by omega) (by omega)
    refine ⟨?_, ?_⟩
    · have : c = o + v / 2 := by omega
      exact this ▸ hc
    · intro hov
      exact hdist o ho (o + v) hov (by omega) (by omega)
  rcases hT n (by omega) with h | ⟨x, hx, y, hy, hxy⟩
  · exact absurd (good3 ho hv h (by omega) (by omega) (by omega) (by omega)) hbad
  · by_cases hxo : x = o
    · exact keyo y hy (by omega)
    · by_cases hxv : x = v
      · exact (keyv y hy (by omega)).elim
      · by_cases hyo : y = o
        · exact keyo x hx (by omega)
        · by_cases hyv : y = v
          · exact (keyv x hx (by omega)).elim
          · exact absurd (good4 ho hv hx hy (by omega) (Ne.symm hxo) (Ne.symm hyo)
              (Ne.symm hxv) (Ne.symm hyv) (by omega) (by omega)) hbad

/-- If `2 * a` is bad, then `A` has no element `v ≥ T` divisible by 4 that is small compared
to `a`. -/
lemma no_mult_four {A : Set ℕ} {T a : ℕ} (hT : Rep A T) (hT1 : 1 ≤ T) (hTa : T ≤ a)
    (hbad : ¬ Good A (2 * a)) {o v : ℕ} (ho : o ∈ A) (hodd : o % 2 = 1) (hv : v ∈ A)
    (hv4 : v % 4 = 0) (hTv : T ≤ v) (h : 2 * o + 3 * v < a) : False := by
  obtain ⟨hw, hov⟩ :=
    half_mem hT hT1 hTa hbad ho hodd hv (by omega) hTv (by omega) (by omega)
  obtain ⟨hw2, -⟩ :=
    half_mem hT hT1 hTa hbad hw (by omega) hv (by omega) hTv (by omega) (by omega)
  have : o + v / 2 + v / 2 = o + v := by omega
  exact hov (this ▸ hw2)

/-- If `2 * a` is bad and `x < y` are odd elements of `A` with `2 * y - x ≥ T` and `2 * y ≤ a`,
then `2 * (y - x) ∈ A`. -/
lemma diff_mem {A : Set ℕ} {T a : ℕ} (hT : Rep A T) (hTa : T ≤ a) (hbad : ¬ Good A (2 * a))
    {x y : ℕ} (hx : x ∈ A) (hy : y ∈ A) (hxo : x % 2 = 1) (hyo : y % 2 = 1) (hxy : x < y)
    (hTxy : T + x ≤ 2 * y) (hya : 2 * y ≤ a) : 2 * y - 2 * x ∈ A := by
  obtain ⟨e, he⟩ : ∃ e, e + 2 * y = 2 * a := ⟨2 * a - 2 * y, by omega⟩
  have heA : e ∈ A := odd_compl hT hTa hbad hy hyo (by omega) he
  rcases hT (2 * y - x) (by omega) with h | ⟨p, hp, q, hq, hpq⟩
  · exact absurd (good3 heA hx h (by omega) (by omega) (by omega) (by omega)) hbad
  · by_cases hpx : p = x
    · have : q = 2 * y - 2 * x := by omega
      exact this ▸ hq
    · by_cases hqx : q = x
      · have : p = 2 * y - 2 * x := by omega
        exact this ▸ hp
      · exact absurd (good4 heA hx hp hq (by omega) (by omega) (by omega) (Ne.symm hpx)
          (Ne.symm hqx) (by omega) (by omega)) hbad

theorem main (A : Set ℕ) (hA : Erdos338.HasOrder A 2) : Erdos338.HasRestrictedOrder A 4 := by
  obtain ⟨T, hT1, hT⟩ := rep_of_hasOrder hA
  -- a bad number beyond `T` is twice a natural number
  have hdouble : ∀ m, T ≤ m → ¬ Good A m → ∃ a, m = 2 * a := by
    intro m hm hbad
    rcases hT m hm with h | ⟨x, hx, y, hy, hxy⟩
    · exact absurd (good1 h) hbad
    · by_cases hne : x = y
      · exact ⟨x, by omega⟩
      · exact absurd (good2 hx hy hne hxy) hbad
  -- `A` has an odd element
  obtain ⟨o₁, ho₁, ho₁odd⟩ : ∃ o ∈ A, o % 2 = 1 := by
    rcases hT (2 * T + 1) (by omega) with h | ⟨x, hx, y, hy, hxy⟩
    · exact ⟨_, h, by omega⟩
    · by_cases hx2 : x % 2 = 1
      · exact ⟨x, hx, hx2⟩
      · exact ⟨y, hy, by omega⟩
  -- it is enough to bound the `a` for which `2 * a` is bad
  suffices h : ∃ M, ∀ a, M ≤ a → Good A (2 * a) by
    obtain ⟨M, hM⟩ := h
    unfold Erdos338.HasRestrictedOrder
    refine Filter.eventually_atTop.2 ⟨2 * M + T, fun m hm => ?_⟩
    by_contra hbad
    have hbad' : ¬ Good A m := hbad
    obtain ⟨a, rfl⟩ := hdouble m (by omega) hbad'
    exact hbad' (hM a (by omega))
  by_cases h1 : ∃ x ∈ A, ∃ y ∈ A, x % 2 = 1 ∧ y % 2 = 1 ∧ x < y ∧ T + 2 * x ≤ 2 * y
  · -- two odd elements far apart
    obtain ⟨x, hx, y, hy, hxo, hyo, hxy, hTxy⟩ := h1
    refine ⟨6 * y + T, fun a ha => ?_⟩
    by_contra hbad
    have hv := diff_mem hT (by omega) hbad hx hy hxo hyo hxy (by omega) (by omega)
    exact no_mult_four hT hT1 (by omega) hbad hx hxo hv (by omega) (by omega) (by omega)
  · -- all odd elements are below `o₁ + T`
    have hB : ∀ o ∈ A, o % 2 = 1 → o < o₁ + T := by
      intro o ho hodd
      by_contra hcon
      exact h1 ⟨o₁, ho₁, o, ho, ho₁odd, hodd, by omega, by omega⟩
    by_cases h2 : ∃ v ∈ A, v % 4 = 0 ∧ T ≤ v
    · obtain ⟨v, hv, hv4, hTv⟩ := h2
      refine ⟨2 * o₁ + 3 * v + T + 1, fun a ha => ?_⟩
      by_contra hbad
      exact no_mult_four hT hT1 (by omega) hbad ho₁ ho₁odd hv hv4 hTv (by omega)
    · -- every even element beyond `T` is 2 mod 4
      have h2' : ∀ v ∈ A, v % 2 = 0 → T ≤ v → v % 4 = 2 := by
        intro v hv hev hTv
        by_contra hcon
        exact h2 ⟨v, hv, by omega, hTv⟩
      -- a large odd number is an odd element plus a large even element
      have split : ∀ n, n % 2 = 1 → o₁ + 3 * T ≤ n →
          ∃ p ∈ A, ∃ q ∈ A, p % 2 = 1 ∧ q % 4 = 2 ∧ 2 * T ≤ q ∧ p + q = n := by
        intro n hn hbig
        rcases hT n (by omega) with h | ⟨x, hx, y, hy, hxy⟩
        · have := hB n h hn
          omega
        · by_cases hx2 : x % 2 = 1
          · have hxB := hB x hx hx2
            exact ⟨x, hx, y, hy, hx2, h2' y hy (by omega) (by omega), by omega, hxy⟩
          · have hy2 : y % 2 = 1 := by omega
            have hyB := hB y hy hy2
            exact ⟨y, hy, x, hx, hy2, h2' x hx (by omega) (by omega), by omega, by omega⟩
      obtain ⟨p, hp, q, hq, hp2, hq4, hTq, hpq⟩ :=
        split (4 * (o₁ + 3 * T) + 1) (by omega) (by omega)
      obtain ⟨p', hp', q', hq', hp2', hq4', hTq', hpq'⟩ :=
        split (4 * (o₁ + 3 * T) + 3) (by omega) (by omega)
      refine ⟨2 * p + 2 * p' + 3 * q + T + 1, fun a ha => ?_⟩
      by_contra hbad
      obtain ⟨hw, -⟩ :=
        half_mem hT hT1 (by omega) hbad hp hp2 hq (by omega) (by omega) (by omega) (by omega)
      obtain ⟨hw', -⟩ :=
        half_mem hT hT1 (by omega) hbad hp' hp2' hq (by omega) (by omega) (by omega) (by omega)
      have e1 := h2' _ hw (by omega) (by omega)
      have e2 := h2' _ hw' (by omega) (by omega)
      omega

end OMA.Kelly

theorem OMA.solution : type_of% @Erdos338.erdos_338.variants.kelly :=
  OMA.Kelly.main
