import FormalConjectures.ErdosProblems.«338»

-- Problem: Erdős Problem 338 — kelly
-- Upstream: formal-conjectures FormalConjectures/ErdosProblems/338.lean:174 (declaration Erdos338.erdos_338.variants.kelly)
-- Credit: @senamakel (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.
--
-- Argument. Let every m >= m0 be a + b with a, b in A or 0. Odd m have a != b, so they are fine.
-- (Q) Suppose some odd c in A and even d (in A or 0) with c + 2d >= m0 have 2c + d a sum of at
-- most 3 distinct elements of A. For large even n, write n - c - d = a + b (odd, so a != b,
-- a large). If b is not c or d, then n = a + b + c + d is a sum of 4 distinct elements; if b = c then
-- n = a + (2c + d); if b = d then n = a + (c + 2d) with c + 2d odd. Either way at most 4.
-- (not Q) is impossible. For odd c != c' and even d, writing 2c + d - c' = p + q with p odd forces
-- p = c', so 2c + d - 2c' is in A or 0; hence the even part of A is closed under adding
-- 2(c - c'). If A has infinitely many odd elements, two of them, x < y, agree mod 2(o2 - o1),
-- so y - x is in A, and 2x + (y - x) = x + y contradicts (not Q). Otherwise the odd elements are
-- bounded; then for large even d the even number 2c + d must be y + y with y even, and
-- y + 2s, y - 2s (in A by the closure) give a representation with distinct summands.

open Filter Erdos338

namespace OMA338

variable {A : Set ℕ}

def A0 (A : Set ℕ) (x : ℕ) : Prop := x = 0 ∨ x ∈ A

-- sums of at most k distinct elements
def Dk (A : Set ℕ) (k s : ℕ) : Prop :=
  ∃ T : Finset ℕ, (∀ x ∈ T, x ∈ A) ∧ T.card ≤ k ∧ ∑ x ∈ T, x = s

lemma mk (k : ℕ) (l : List ℕ) (hl : l.Nodup) (hA : ∀ x ∈ l, A0 A x) (hlen : l.length ≤ k) :
    Dk A k l.sum := by
  classical
  refine ⟨l.toFinset.erase 0, ?_, ?_, ?_⟩
  · intro x hx
    rcases hA x (List.mem_toFinset.mp (Finset.mem_of_mem_erase hx)) with h | h
    · exact absurd h (Finset.ne_of_mem_erase hx)
    · exact h
  · exact (Finset.card_erase_le).trans ((List.toFinset_card_le l).trans hlen)
  · rw [Finset.sum_erase (f := fun x => x) _ rfl, List.sum_toFinset _ hl]; simp

lemma rep_of (hA : HasOrder A 2) : ∃ m0, ∀ m ≥ m0, ∃ a b, A0 A a ∧ A0 A b ∧ a + b = m := by
  obtain ⟨m0, hm0⟩ := eventually_atTop.mp hA
  refine ⟨m0, fun m hm => ?_⟩
  obtain ⟨S, hS, hc, hs⟩ := hm0 m hm
  rcases (show S.card = 0 ∨ S.card = 1 ∨ S.card = 2 by omega) with h | h | h
  · rw [Multiset.card_eq_zero] at h; subst h
    exact ⟨0, 0, Or.inl rfl, Or.inl rfl, by simpa using hs⟩
  · obtain ⟨a, rfl⟩ := Multiset.card_eq_one.mp h
    exact ⟨a, 0, Or.inr (hS a (by simp)), Or.inl rfl, by simpa using hs⟩
  · obtain ⟨a, b, rfl⟩ := Multiset.card_eq_two.mp h
    exact ⟨a, b, Or.inr (hS a (by simp)), Or.inr (hS b (by simp)), by simpa using hs⟩

lemma lift {k s w : ℕ} (hs : Dk A k s) (hw : w ∈ A) (hlt : s < w) : Dk A (k + 1) (w + s) := by
  classical
  obtain ⟨T, hT, hc, hsum⟩ := hs
  have hnot : w ∉ T := by
    intro hm
    have := Finset.single_le_sum (f := fun x => x) (fun _ _ => Nat.zero_le _) hm
    omega
  refine ⟨insert w T, ?_, ?_, ?_⟩
  · intro x hx
    rcases Finset.mem_insert.mp hx with rfl | h
    · exact hw
    · exact hT x h
  · rw [Finset.card_insert_of_notMem hnot]; omega
  · rw [Finset.sum_insert hnot, hsum]

lemma Dk_mono {k k' s : ℕ} (h : Dk A k s) (hk : k ≤ k') : Dk A k' s := by
  obtain ⟨T, a, b, c⟩ := h; exact ⟨T, a, b.trans hk, c⟩

lemma A0_mem {x : ℕ} (h : A0 A x) (hx : x ≠ 0) : x ∈ A := h.resolve_left hx

lemma odd_rep {m a b : ℕ} (ha : A0 A a) (hb : A0 A b) (hab : a + b = m) (hm : Odd m) :
    ∃ p q, p ∈ A ∧ Odd p ∧ A0 A q ∧ Even q ∧ p + q = m := by
  rcases Nat.even_or_odd a with h | h
  · have hbo : Odd b := by
      rcases Nat.even_or_odd b with h' | h'
      · exfalso; have := h.add h'; rw [hab] at this; exact (Nat.not_even_iff_odd.mpr hm) this
      · exact h'
    exact ⟨b, a, A0_mem hb (by rintro rfl; simp at hbo), hbo, ha, h, by omega⟩
  · have hbe : Even b := by
      rcases Nat.even_or_odd b with h' | h'
      · exact h'
      · exfalso; have := h.add_odd h'; rw [hab] at this; exact (Nat.not_even_iff_odd.mpr hm) this
    exact ⟨a, b, A0_mem ha (by rintro rfl; simp at h), h, hb, hbe, hab⟩


lemma pairD {a b : ℕ} (ha : A0 A a) (hb : A0 A b) (hab : a ≠ b) : Dk A 3 (a + b) := by
  have := mk (A := A) 3 [a, b] (by simp [hab]) (by simp [ha, hb]) (by simp)
  simpa using this

lemma tripD {a b c : ℕ} (ha : A0 A a) (hb : A0 A b) (hc : A0 A c) (hab : a ≠ b) (hac : a ≠ c)
    (hbc : b ≠ c) : Dk A 3 (a + b + c) := by
  have := mk (A := A) 3 [a, b, c] (by simp [hab, hac, hbc]) (by simp [ha, hb, hc]) (by simp)
  simp at this; simpa [add_assoc] using this

section core
variable (m0 : ℕ) (hrep : ∀ m ≥ m0, ∃ a b, A0 A a ∧ A0 A b ∧ a + b = m)

def NotQ (A : Set ℕ) (m0 : ℕ) : Prop :=
  ∀ c d, c ∈ A → Odd c → A0 A d → Even d → m0 ≤ c + 2 * d → ¬ Dk A 3 (2 * c + d)

include hrep in
lemma step (hQ : NotQ A m0) {c c' d : ℕ} (hc : c ∈ A) (hco : Odd c) (hc' : c' ∈ A)
    (hc'o : Odd c') (hne : c' ≠ c) (hd : A0 A d) (hde : Even d) (h1 : m0 ≤ c + 2 * d)
    (h2 : c' + m0 ≤ 2 * c + d) : ∃ q, A0 A q ∧ Even q ∧ 2 * c' + q = 2 * c + d := by
  obtain ⟨a, b, ha, hb, hab⟩ := hrep (2 * c + d - c') (by omega)
  have hodd : Odd (2 * c + d - c') := by
    obtain ⟨k, hk⟩ := hde; obtain ⟨j, hj⟩ := hc'o
    exact ⟨c + k - j - 1, by omega⟩
  obtain ⟨p, q, hp, hpo, hq, hqe, hpq⟩ := odd_rep ha hb hab hodd
  by_cases hpc : p = c'
  · subst hpc; exact ⟨q, hq, hqe, by omega⟩
  · exfalso
    apply hQ c d hc hco hd hde h1
    have hq1 : c' ≠ q := fun h => by subst h; exact (Nat.not_even_iff_odd.mpr hc'o) hqe
    have hq2 : p ≠ q := fun h => by subst h; exact (Nat.not_even_iff_odd.mpr hpo) hqe
    have := tripD (Or.inr hc') (Or.inr hp) hq (Ne.symm hpc) hq1 hq2
    have e : c' + p + q = 2 * c + d := by omega
    rwa [e] at this

lemma notmem (hQ : NotQ A m0) {c e : ℕ} (hc : c ∈ A) (hco : Odd c) (he : A0 A e)
    (hee : Even e) (hpos : 0 < e) (h1 : m0 ≤ c + 2 * e) : c + e ∉ A := by
  intro hm
  apply hQ c e hc hco he hee h1
  have := pairD (A := A) (Or.inr hc) (Or.inr hm) (by omega)
  rwa [show c + (c + e) = 2 * c + e by ring] at this

include hrep in
lemma ap (hQ : NotQ A m0) {o1 o2 : ℕ} (h1 : o1 ∈ A) (h1o : Odd o1) (h2 : o2 ∈ A) (h2o : Odd o2)
    (hlt : o1 < o2) (hm : m0 ≤ o1) : ∀ j, A0 A (2 * (o2 - o1) * j) := by
  intro j
  induction j with
  | zero => exact Or.inl (by simp)
  | succ j ih =>
    have hev : Even (2 * (o2 - o1) * j) := ⟨(o2 - o1) * j, by ring⟩
    obtain ⟨q, hq, -, hq'⟩ := step m0 hrep hQ h2 h2o h1 h1o (by omega) ih hev (by omega) (by omega)
    have : q = 2 * (o2 - o1) * (j + 1) := by
      have : 2 * (o2 - o1) * (j + 1) = 2 * (o2 - o1) * j + 2 * (o2 - o1) := by ring
      omega
    rwa [this] at hq


include hrep in
lemma finite_odd (hQ : NotQ A m0) : {x | x ∈ A ∧ Odd x ∧ m0 ≤ x}.Finite := by
  by_contra hinf
  rw [Set.not_finite] at hinf
  obtain ⟨o1, ho1⟩ := hinf.nonempty
  obtain ⟨o2, ho2, hlt⟩ := hinf.exists_gt o1
  set δ := o2 - o1
  have hδ : 0 < δ := by omega
  obtain ⟨x, hx, y, hy, hxy, hmod⟩ := hinf.exists_ne_map_eq_of_mapsTo
    (f := fun x => x % (2 * δ)) (t := (Finset.range (2 * δ) : Set ℕ))
    (fun x _ => by simp only [Finset.coe_range, Set.mem_Iio]; exact Nat.mod_lt _ (by omega))
    (Finset.finite_toSet _)
  -- order them
  have key : ∀ x y : ℕ, x ∈ {x | x ∈ A ∧ Odd x ∧ m0 ≤ x} → y ∈ {x | x ∈ A ∧ Odd x ∧ m0 ≤ x} →
      x < y → x % (2 * δ) = y % (2 * δ) → False := by
    intro x y hx hy hxy hmod
    have hdvd : 2 * δ ∣ y - x := Nat.dvd_of_mod_eq_zero (Nat.sub_mod_eq_zero_of_mod_eq hmod.symm)
    obtain ⟨k, hk⟩ := hdvd
    have he := ap m0 hrep hQ ho1.1 ho1.2.1 ho2.1 ho2.2.1 hlt ho1.2.2 k
    rw [← hk] at he
    apply notmem m0 hQ hx.1 hx.2.1 he ⟨k * δ, by rw [hk]; ring⟩ (by omega) (by have := hx.2.2; omega)
    rw [show x + (y - x) = y by omega]; exact hy.1
  rcases lt_or_gt_of_ne hxy with h | h
  · exact key x y hx hy h hmod
  · exact key y x hy hx h hmod.symm

include hrep in
lemma only_odd (c : ℕ) (hall : ∀ o ∈ A, Odd o → o = c) {z : ℕ} (hz : Even z)
    (hc : Odd c) (hzc : m0 ≤ z + c) : A0 A z := by
  obtain ⟨a, b, ha, hb, hab⟩ := hrep (z + c) hzc
  obtain ⟨p, q, hp, hpo, hq, -, hpq⟩ := odd_rep ha hb hab (hz.add_odd hc)
  have := hall p hp hpo
  subst this
  rwa [show z = q by omega]

include hrep in
lemma no_notQ : ¬ NotQ A m0 := by
  intro hQ
  obtain ⟨B1, hB1⟩ := (finite_odd m0 hrep hQ).bddAbove
  set B := B1 + m0 + 1
  have hB : ∀ x ∈ A, Odd x → x < B := by
    intro x hx hxo
    by_cases h : m0 ≤ x
    · have := hB1 ⟨hx, hxo, h⟩; omega
    · omega
  -- an odd element
  obtain ⟨a, b, ha, hb, hab⟩ := hrep (2 * m0 + 1) (by omega)
  obtain ⟨c, -, hc, hco, -, -, -⟩ := odd_rep ha hb hab ⟨m0, rfl⟩
  -- a large even element
  set L := 2 * (m0 + B) + 4
  obtain ⟨a', b', ha', hb', hab'⟩ := hrep (2 * (L + B) + 1) (by omega)
  obtain ⟨p, d, hp, hpo, hd, hde, hpd⟩ := odd_rep ha' hb' hab' ⟨L + B, rfl⟩
  have hpB := hB p hp hpo
  have hcB := hB c hc hco
  have hdL : L ≤ d := by omega
  have hQcd := hQ c d hc hco hd hde (by omega)
  obtain ⟨u, v, hu, hv, huv⟩ := hrep (2 * c + d) (by omega)
  by_cases hne : u = v
  · subst hne
    set y := u
    have hy0 : y ≠ 0 := by omega
    have hyA : y ∈ A := A0_mem hu hy0
    have hye : Even y := by
      rcases Nat.even_or_odd y with h | h
      · exact h
      · have := hB y hyA h; omega
    by_cases hall : ∀ o ∈ A, Odd o → o = c
    · have q1 := only_odd m0 hrep c hall (z := y + 2) (hye.add even_two) hco (by omega)
      have q2 := only_odd m0 hrep c hall (z := y - 2)
        (by obtain ⟨k, hk⟩ := hye; exact ⟨k - 1, by omega⟩) hco (by omega)
      apply hQcd
      have := pairD q1 q2 (by omega)
      rwa [show y + 2 + (y - 2) = 2 * c + d by omega] at this
    · push Not at hall
      obtain ⟨o, hoA, hoo, hoc⟩ := hall
      have hoB := hB o hoA hoo
      -- lo / hi
      have main : ∀ lo hi : ℕ, lo ∈ A → Odd lo → hi ∈ A → Odd hi → lo < hi → lo < B → hi < B →
          False := by
        intro lo hi hlo hloo hhi hhio hlt hloB hhiB
        obtain ⟨q1, hq1, -, e1⟩ := step m0 hrep hQ hhi hhio hlo hloo (by omega) hu hye
          (by omega) (by omega)
        obtain ⟨q2, hq2, -, e2⟩ := step m0 hrep hQ hlo hloo hhi hhio (by omega) hu hye
          (by omega) (by omega)
        apply hQcd
        have := pairD hq1 hq2 (by omega)
        rwa [show q1 + q2 = 2 * c + d by omega] at this
      rcases lt_or_gt_of_ne hoc with h | h
      · exact main o c hoA hoo hc hco h hoB hcB
      · exact main c o hc hco hoA hoo h hcB hoB
  · apply hQcd
    have := pairD hu hv hne
    rwa [huv] at this

end core

lemma odd_ne {a b : ℕ} (h : Odd (a + b)) : a ≠ b := by
  rintro rfl; exact (Nat.not_even_iff_odd.mpr h) ⟨a, rfl⟩

theorem kelly (hA : HasOrder A 2) : HasRestrictedOrder A 4 := by
  obtain ⟨m0, hrep⟩ := rep_of hA
  have hQ := no_notQ m0 hrep
  unfold NotQ at hQ
  push Not at hQ
  obtain ⟨c, d, hc, hco, hd, hde, hcd, hD⟩ := hQ
  have hcdne : c ≠ d := fun h => by subst h; exact (Nat.not_even_iff_odd.mpr hco) hde
  unfold HasRestrictedOrder
  rw [eventually_atTop]
  refine ⟨m0 + 6 * (c + d) + 2, fun n hn => ?_⟩
  rcases Nat.even_or_odd n with hne | hno
  · have hmo : Odd (n - c - d) := by
      obtain ⟨k, hk⟩ := hne; obtain ⟨j, hj⟩ := hco; obtain ⟨i, hi⟩ := hde
      exact ⟨k - j - i - 1, by omega⟩
    obtain ⟨a, b, ha, hb, hab⟩ := hrep (n - c - d) (by omega)
    have hne' := odd_ne (show Odd (a + b) by rw [hab]; exact hmo)
    -- big / small
    have gen : ∀ x y : ℕ, A0 A x → A0 A y → x + y = n - c - d → y < x → Dk A 4 n := by
      intro x y hx hy hxy hlt
      have hxbig : 2 * c + 2 * d < x := by omega
      have hxA : x ∈ A := A0_mem hx (by omega)
      by_cases hyc : y = c
      · subst hyc
        have := lift hD hxA (by omega)
        rwa [show x + (2 * y + d) = n by omega] at this
      by_cases hyd : y = d
      · subst hyd
        obtain ⟨p, q, hp, hq, hpq⟩ := hrep (c + 2 * y) hcd
        have hodd : Odd (c + 2 * y) := hco.add_even ⟨y, by ring⟩
        have h3 := pairD hp hq (odd_ne (by rw [hpq]; exact hodd))
        rw [hpq] at h3
        have := lift h3 hxA (by omega)
        rwa [show x + (c + 2 * y) = n by omega] at this
      have := mk (A := A) 4 [x, y, c, d]
        (by simp; omega) (by simp [hx, hy, hd]; exact Or.inr hc) (by simp)
      simp at this
      rwa [show x + (y + (c + d)) = n by omega] at this
    rcases lt_or_gt_of_ne hne' with h | h
    · exact gen b a hb ha (by omega) h
    · exact gen a b ha hb hab h
  · obtain ⟨a, b, ha, hb, hab⟩ := hrep n (by omega)
    have := pairD ha hb (odd_ne (by rw [hab]; exact hno))
    rw [hab] at this
    exact Dk_mono this (by norm_num)

end OMA338

theorem OMA.solution : type_of% @Erdos338.erdos_338.variants.kelly :=
  fun _ hA => OMA338.kelly hA
