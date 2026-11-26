import FormalConjectures.ErdosProblems.«1186»

-- Problem: Erdős Problem 1186 — probabilistic
-- Credit: @luciusacarr (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.
-- Averaging over all colourings of {0..n}: some colouring has at most the average number of
-- monochromatic progressions.

open Finset Filter

namespace OMA

/-- Extend a colouring of `{0..n}` to all of `ℕ`. -/
def ext (n : ℕ) (g : Fin (n + 1) → Bool) : ℕ → Bool :=
  fun x => if h : x < n + 1 then g ⟨x, h⟩ else true

theorem ext_apply (n : ℕ) (g : Fin (n + 1) → Bool) (x : ℕ) (h : x < n + 1) :
    ext n g x = g ⟨x, h⟩ := dif_pos h

/-- At most `2 * 2^(n+1-k)` colourings make a given `k`-term progression monochromatic. -/
theorem mono_card (n k a d : ℕ) (hd : 1 ≤ d) (hk : 1 ≤ k) (h : a + (k - 1) * d ≤ n) :
    (univ.filter (fun g : Fin (n + 1) → Bool =>
      ∀ i < k, ext n g (a + i * d) = ext n g a)).card * 2 ^ k ≤ 2 * 2 ^ (n + 1) := by
  classical
  have hlt : ∀ i : Fin k, a + (i : ℕ) * d < n + 1 := by
    intro i
    have : (i : ℕ) * d ≤ (k - 1) * d := Nat.mul_le_mul_right d (by have := i.2; omega)
    omega
  have ha : a < n + 1 := by omega
  set S : Finset (Fin (n + 1)) := (univ : Finset (Fin k)).image (fun i : Fin k => ⟨a + i.val * d, hlt i⟩)
    with hS
  have hScard : S.card = k := by
    rw [hS, card_image_of_injective, card_univ, Fintype.card_fin]
    intro i j hij
    simp only [Fin.mk.injEq] at hij
    have : (i : ℕ) * d = (j : ℕ) * d := by omega
    exact Fin.ext (Nat.eq_of_mul_eq_mul_right hd this)
  let Φ : (Fin (n + 1) → Bool) → Bool × ((Sᶜ : Finset (Fin (n + 1))) → Bool) :=
    fun g => (g ⟨a, ha⟩, fun j => g j.1)
  have hinj : Set.InjOn Φ ((univ.filter (fun g : Fin (n + 1) → Bool =>
      ∀ i < k, ext n g (a + i * d) = ext n g a) : Finset _) : Set (Fin (n + 1) → Bool)) := by
    intro g hg g' hg' hΦ
    simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hg hg'
    simp only [Φ, Prod.mk.injEq] at hΦ
    obtain ⟨h0, hrest⟩ := hΦ
    funext x
    by_cases hx : x ∈ S
    · rw [hS, mem_image] at hx
      obtain ⟨i, -, rfl⟩ := hx
      have e1 := hg i i.2
      have e2 := hg' i i.2
      rw [ext_apply n g _ (hlt i), ext_apply n g _ ha] at e1
      rw [ext_apply n g' _ (hlt i), ext_apply n g' _ ha] at e2
      rw [e1, e2, h0]
    · exact congrFun hrest ⟨x, mem_compl.mpr hx⟩
  have hcard := Finset.card_le_card_of_injOn (t := (univ : Finset (Bool × ((Sᶜ : Finset (Fin (n + 1))) → Bool))))
    Φ (fun g _ => mem_univ _) hinj
  rw [card_univ, Fintype.card_prod, Fintype.card_bool, Fintype.card_fun, Fintype.card_bool,
    Fintype.card_coe, card_compl, Fintype.card_fin, hScard] at hcard
  have hkn : k ≤ n + 1 := by
    have := Finset.card_le_univ S
    rw [hScard, Fintype.card_fin] at this
    exact this
  calc _ ≤ (2 * 2 ^ (n + 1 - k)) * 2 ^ k := Nat.mul_le_mul_right _ hcard
    _ = 2 * 2 ^ (n + 1) := by rw [mul_assoc, ← pow_add, Nat.sub_add_cancel hkn]

/-- The set of progressions. -/
def aps (m n : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.Icc 1 n ×ˢ Finset.Icc 1 n).filter (fun p : ℕ × ℕ => p.1 + m * p.2 ≤ n)

theorem lt_pairs (n : ℕ) :
    ((Finset.Icc 1 n ×ˢ Finset.Icc 1 n).filter (fun p : ℕ × ℕ => p.1 < p.2)).card * 2 ≤ n * n := by
  set L := (Finset.Icc 1 n ×ˢ Finset.Icc 1 n).filter (fun p : ℕ × ℕ => p.1 < p.2) with hL
  set L' := (Finset.Icc 1 n ×ˢ Finset.Icc 1 n).filter (fun p : ℕ × ℕ => p.2 < p.1) with hL'
  have hswap : L'.card = L.card := by
    apply card_bij (fun p _ => (p.2, p.1))
    · intro p hp
      simp only [hL, hL', mem_filter, mem_product] at hp ⊢
      exact ⟨⟨hp.1.2, hp.1.1⟩, hp.2⟩
    · intro p _ q _ h
      rw [Prod.mk.injEq] at h
      exact Prod.ext h.2 h.1
    · intro q hq
      simp only [hL, mem_filter, mem_product] at hq
      exact ⟨(q.2, q.1), by simp only [hL', mem_filter, mem_product]; exact ⟨⟨hq.1.2, hq.1.1⟩, hq.2⟩, rfl⟩
  have hdisj : Disjoint L L' := by
    rw [disjoint_left]
    intro p hp hp'
    simp only [hL, hL', mem_filter] at hp hp'
    omega
  have hsub : L ∪ L' ⊆ Finset.Icc 1 n ×ˢ Finset.Icc 1 n := by
    intro p hp
    rw [mem_union] at hp
    rcases hp with hp | hp
    · exact (mem_filter.mp hp).1
    · exact (mem_filter.mp hp).1
  have hc := card_le_card hsub
  rw [card_union_of_disjoint hdisj, hswap, card_product, Nat.card_Icc] at hc
  simp only [Nat.add_sub_cancel] at hc
  omega

theorem aps_card (m n : ℕ) (hm : 1 ≤ m) : (aps m n).card * m * 2 ≤ n * n := by
  set L := (Finset.Icc 1 n ×ˢ Finset.Icc 1 n).filter (fun p : ℕ × ℕ => p.1 < p.2) with hL
  have hle : (aps m n ×ˢ Finset.range m).card ≤ L.card := by
    apply Finset.card_le_card_of_injOn (fun x : (ℕ × ℕ) × ℕ => (x.1.1, x.1.1 + m * x.1.2 - x.2))
    · rintro ⟨⟨a, d⟩, j⟩ hx
      simp only [coe_product, Set.mem_prod, mem_coe, aps, mem_filter, mem_product, mem_Icc,
        mem_range] at hx
      obtain ⟨⟨⟨⟨ha1, han⟩, hd1, hdn⟩, hadn⟩, hj⟩ := hx
      have hmd : m ≤ m * d := Nat.le_mul_of_pos_right m hd1
      rw [mem_coe, hL]
      simp only [mem_filter, mem_product, mem_Icc]
      omega
    · rintro ⟨⟨a, d⟩, j⟩ hx ⟨⟨a', d'⟩, j'⟩ hx' hF
      simp only [coe_product, Set.mem_prod, mem_coe, aps, mem_filter, mem_product, mem_Icc,
        mem_range] at hx hx'
      obtain ⟨⟨⟨⟨ha1, han⟩, hd1, hdn⟩, hadn⟩, hj⟩ := hx
      obtain ⟨⟨⟨⟨ha1', han'⟩, hd1', hdn'⟩, hadn'⟩, hj'⟩ := hx'
      simp only [Prod.mk.injEq] at hF
      obtain ⟨haa, hy⟩ := hF
      subst haa
      have hmd : m ≤ m * d := Nat.le_mul_of_pos_right m hd1
      have hmd' : m ≤ m * d' := Nat.le_mul_of_pos_right m hd1'
      have hdd : d = d' := by
        rcases lt_trichotomy d d' with hlt | heq | hgt
        · exfalso
          have h1 : m * (d + 1) ≤ m * d' := Nat.mul_le_mul_left m hlt
          have h2 : m * (d + 1) = m * d + m := by ring
          omega
        · exact heq
        · exfalso
          have h1 : m * (d' + 1) ≤ m * d := Nat.mul_le_mul_left m hgt
          have h2 : m * (d' + 1) = m * d' + m := by ring
          omega
      subst hdd
      have hjj : j = j' := by omega
      rw [hjj]
  rw [card_product, card_range] at hle
  have := lt_pairs n
  calc (aps m n).card * m * 2 ≤ L.card * 2 := Nat.mul_le_mul_right 2 hle
    _ ≤ n * n := this

/-- The key bound on the minimum. -/
theorem min_bound (k n : ℕ) (hk : 2 ≤ k) :
    Erdos1186.minMonoCount k n * 2 ^ k * (k - 1) ≤ n * n := by
  classical
  have hsum : ∀ g : Fin (n + 1) → Bool, Erdos1186.monoCount k n (ext n g) =
      ∑ p ∈ aps (k - 1) n, if (∀ i < k, ext n g (p.1 + i * p.2) = ext n g p.1) then 1 else 0 := by
    intro g
    unfold Erdos1186.monoCount aps
    rw [← Finset.filter_filter, card_filter]
  have htotal : (∑ g : Fin (n + 1) → Bool, Erdos1186.monoCount k n (ext n g)) * 2 ^ k ≤
      (aps (k - 1) n).card * (2 * 2 ^ (n + 1)) := by
    simp only [hsum]
    rw [Finset.sum_comm, Finset.sum_mul]
    calc _ ≤ ∑ _p ∈ aps (k - 1) n, 2 * 2 ^ (n + 1) := by
          apply Finset.sum_le_sum
          intro p hp
          simp only [aps, mem_filter, mem_product, mem_Icc] at hp
          rw [← card_filter]
          exact mono_card n k p.1 p.2 hp.1.2.1 (by omega) hp.2
      _ = _ := by rw [Finset.sum_const, smul_eq_mul]
  have hmin : 2 ^ (n + 1) * Erdos1186.minMonoCount k n ≤
      ∑ g : Fin (n + 1) → Bool, Erdos1186.monoCount k n (ext n g) := by
    have : ∑ _g : Fin (n + 1) → Bool, Erdos1186.minMonoCount k n ≤
        ∑ g : Fin (n + 1) → Bool, Erdos1186.monoCount k n (ext n g) :=
      Finset.sum_le_sum (fun g _ => Erdos1186.minMonoCount_le k n (ext n g))
    rw [Finset.sum_const, card_univ, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin,
      smul_eq_mul] at this
    exact this
  have h1 : 2 ^ (n + 1) * (Erdos1186.minMonoCount k n * 2 ^ k) ≤
      2 ^ (n + 1) * ((aps (k - 1) n).card * 2) := by
    calc 2 ^ (n + 1) * (Erdos1186.minMonoCount k n * 2 ^ k)
        = (2 ^ (n + 1) * Erdos1186.minMonoCount k n) * 2 ^ k := by ring
      _ ≤ (∑ g : Fin (n + 1) → Bool, Erdos1186.monoCount k n (ext n g)) * 2 ^ k :=
          Nat.mul_le_mul_right _ hmin
      _ ≤ (aps (k - 1) n).card * (2 * 2 ^ (n + 1)) := htotal
      _ = 2 ^ (n + 1) * ((aps (k - 1) n).card * 2) := by ring
  have h2 : Erdos1186.minMonoCount k n * 2 ^ k ≤ (aps (k - 1) n).card * 2 :=
    Nat.le_of_mul_le_mul_left h1 (by positivity)
  have h3 := aps_card (k - 1) n (by omega)
  calc Erdos1186.minMonoCount k n * 2 ^ k * (k - 1)
      ≤ (aps (k - 1) n).card * 2 * (k - 1) := Nat.mul_le_mul_right _ h2
    _ = (aps (k - 1) n).card * (k - 1) * 2 := by ring
    _ ≤ n * n := h3

end OMA

theorem OMA.solution : type_of% @Erdos1186.erdos_1186.variants.probabilistic := by
  intro k hk
  have hk1 : (0 : ℝ) < (k : ℝ) - 1 := by
    have : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
    linarith
  have hpos : (0 : ℝ) < ((k : ℝ) - 1) * 2 ^ k := by positivity
  have hbound : ∀ n : ℕ, (Erdos1186.minMonoCount k n : ℝ) / (n : ℝ) ^ 2 ≤
      1 / (((k : ℝ) - 1) * 2 ^ k) := by
    intro n
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn
      simp only [Nat.cast_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, div_zero]
      positivity
    · have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
      have h := OMA.min_bound k n hk
      have hR : (Erdos1186.minMonoCount k n : ℝ) * 2 ^ k * ((k : ℝ) - 1) ≤ (n : ℝ) * (n : ℝ) := by
        have h' : ((Erdos1186.minMonoCount k n * 2 ^ k * (k - 1) : ℕ) : ℝ) ≤ ((n * n : ℕ) : ℝ) := by
          exact_mod_cast h
        rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_mul, Nat.cast_pow, Nat.cast_sub (by omega)] at h'
        simpa using h'
      rw [div_le_div_iff₀ (by positivity) hpos]
      nlinarith [hR]
  unfold Erdos1186.δ
  apply liminf_le_of_le
  · exact ⟨0, Filter.eventually_map.mpr (Filter.Eventually.of_forall (fun n => by positivity))⟩
  · intro b hb
    obtain ⟨n, hn⟩ := hb.exists
    exact hn.trans (hbound n)
