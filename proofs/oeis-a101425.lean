import OMAStatements.S_oeis_a101425

-- Problem: A101425: Number of different cuboids with volume p^5 X q^n, where p,q are distinct prime numbers.
-- Upstream: formal-conjectures statements/oeis-a101425.lean:0 (declaration OMA.S_oeis_a101425.main)
-- Credit: @eltociear (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

-- Proof: sorted side triples of V = p^5 q^n correspond to 3-element multisets of divisors with
-- product V; via (a, b) ↦ p^a q^b these are the 3-multisets of exponent pairs summing to (5, n),
-- counted again as lex-sorted triples. The first coordinates (0,0,5), (0,1,4), (0,2,3), (1,1,3),
-- (1,2,2) give 2 * C(n+2, 2) + 3 * g(n) with g(n) = ∑_{u ≤ n} (n + 1 - 2u).

open Finset

namespace A101425Proof

def g (n : ℕ) : ℕ := ∑ u ∈ range (n + 1), (n + 1 - 2 * u)

lemma g_step (n : ℕ) : g (n + 2) = g n + (n + 3) := by
  unfold g
  rw [Finset.sum_range_succ', Finset.sum_range_succ]
  have : ∀ i ∈ range (n + 1), (n + 2 + 1 - 2 * (i + 1)) = n + 1 - 2 * i := by
    intro i _; omega
  rw [Finset.sum_congr rfl this]
  omega

lemma g_even (m : ℕ) : g (2 * m) = (m + 1) ^ 2 := by
  induction m with
  | zero => simp [g, Finset.sum_range_succ]
  | succ m ih => rw [show 2 * (m + 1) = 2 * m + 2 by ring, g_step, ih]; ring

lemma g_odd (m : ℕ) : g (2 * m + 1) = (m + 1) * (m + 2) := by
  induction m with
  | zero => simp [g, Finset.sum_range_succ]
  | succ m ih => rw [show 2 * (m + 1) + 1 = (2 * m + 1) + 2 by ring, g_step, ih]; ring

def h (n : ℕ) : ℕ := ∑ u ∈ range (n + 1), (n + 1 - u)

lemma h_two (n : ℕ) : 2 * h n = (n + 1) * (n + 2) := by
  induction n with
  | zero => simp [h]
  | succ n ih =>
    unfold h at *
    rw [Finset.sum_range_succ']
    have : ∀ i ∈ range (n + 1), (n + 1 + 1 - (i + 1)) = n + 1 - i := by intro i _; omega
    rw [Finset.sum_congr rfl this, mul_add, ih]; ring_nf; omega

lemma L1 (n : ℕ) : (∑ b1 ∈ range (n + 1), ∑ b2 ∈ range (n + 1),
    if b1 + b2 ≤ n then 1 else 0) = h n := by
  unfold h
  refine Finset.sum_congr rfl fun b1 hb1 => ?_
  rw [Finset.sum_boole]
  have : (range (n + 1)).filter (fun b2 => b1 + b2 ≤ n) = range (n + 1 - b1) := by
    ext x; simp at hb1 ⊢; omega
  simp [this]

lemma L2 (n : ℕ) : (∑ b1 ∈ range (n + 1), ∑ b2 ∈ range (n + 1),
    if b1 ≤ b2 ∧ b1 + b2 ≤ n then 1 else 0) = g n := by
  unfold g
  refine Finset.sum_congr rfl fun b1 hb1 => ?_
  rw [Finset.sum_boole]
  have : (range (n + 1)).filter (fun b2 => b1 ≤ b2 ∧ b1 + b2 ≤ n) = Ico b1 (n + 1 - b1) := by
    ext x; simp at hb1 ⊢; omega
  simp [this]; omega

lemma L3 (n : ℕ) : (∑ b1 ∈ range (n + 1), ∑ b2 ∈ range (n + 1),
    if b1 + 2 * b2 ≤ n then 1 else 0) = g n := by
  rw [Finset.sum_comm]
  unfold g
  refine Finset.sum_congr rfl fun b2 hb2 => ?_
  rw [Finset.sum_boole]
  have : (range (n + 1)).filter (fun b1 => b1 + 2 * b2 ≤ n) = range (n + 1 - 2 * b2) := by
    ext x; simp at hb2 ⊢; omega
  simp [this]


def ms {α : Type*} (t : α × α × α) : Multiset α := {t.1, t.2.1, t.2.2}

lemma ms_12 {α : Type*} (x y z : α) : ms (y, x, z) = ms (x, y, z) := by
  simp [ms, Multiset.insert_eq_cons, Multiset.cons_swap]

lemma ms_23 {α : Type*} (x y z : α) : ms (x, z, y) = ms (x, y, z) := by
  simp only [ms]; exact congrArg (insert x) (Multiset.pair_comm z y)

lemma sorted_inj {α : Type*} [LinearOrder α] {x y z x' y' z' : α}
    (h1 : x ≤ y) (h2 : y ≤ z) (h1' : x' ≤ y') (h2' : y' ≤ z')
    (h : ms (x, y, z) = ms (x', y', z')) : (x, y, z) = (x', y', z') := by
  have hx : x ∈ ms (x', y', z') := h ▸ by simp [ms]
  have hx' : x' ∈ ms (x, y, z) := h ▸ by simp [ms]
  have hz : z ∈ ms (x', y', z') := h ▸ by simp [ms]
  have hz' : z' ∈ ms (x, y, z) := h ▸ by simp [ms]
  simp only [ms, Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton] at hx hx' hz hz'
  have ex : x = x' := by
    apply le_antisymm
    · rcases hx' with e | e | e <;> rw [e] <;> first | exact le_rfl | exact h1 | exact h1.trans h2
    · rcases hx with e | e | e <;> rw [e] <;> first | exact le_rfl | exact h1' | exact h1'.trans h2'
  have ez : z = z' := by
    apply le_antisymm
    · rcases hz with e | e | e <;> rw [e] <;> first | exact le_rfl | exact h2' | exact h1'.trans h2'
    · rcases hz' with e | e | e <;> rw [e] <;> first | exact le_rfl | exact h2 | exact h1.trans h2
  subst ex ez
  simp [ms, Multiset.insert_eq_cons] at h
  rw [h]

lemma card_sorted {α : Type*} [LinearOrder α] (T : Finset (α × α × α))
    (h12 : ∀ t ∈ T, (t.2.1, t.1, t.2.2) ∈ T) (h23 : ∀ t ∈ T, (t.1, t.2.2, t.2.1) ∈ T) :
    #(T.filter (fun t => t.1 ≤ t.2.1 ∧ t.2.1 ≤ t.2.2)) = #(T.image ms) := by
  classical
  rw [← Finset.card_image_of_injOn (f := ms)]
  · congr 1
    ext m
    simp only [mem_image, mem_filter]
    constructor
    · rintro ⟨t, ⟨ht, _⟩, rfl⟩; exact ⟨t, ht, rfl⟩
    · rintro ⟨⟨x, y, z⟩, ht, rfl⟩
      have s12 := h12 _ ht
      have s23 := h23 _ ht
      have s123 := h23 _ s12
      have s231 := h12 _ s23
      have s321 := h12 _ s123
      simp only at s12 s23 s123 s231 s321
      rcases le_total x y with hxy | hxy <;> rcases le_total y z with hyz | hyz <;>
        rcases le_total x z with hxz | hxz <;>
        first
        | exact ⟨_, ⟨ht, ‹_›, ‹_›⟩, rfl⟩
        | exact ⟨_, ⟨s12, ‹_›, ‹_›⟩, ms_12 x y z⟩
        | exact ⟨_, ⟨s23, ‹_›, ‹_›⟩, ms_23 x y z⟩
        | exact ⟨_, ⟨s123, ‹_›, ‹_›⟩, by rw [ms_23, ms_12]⟩
        | exact ⟨_, ⟨s231, ‹_›, ‹_›⟩, by rw [ms_12, ms_23]⟩
        | exact ⟨_, ⟨s321, ‹_›, ‹_›⟩, by rw [ms_12, ms_23, ms_12]⟩
  · rintro ⟨x, y, z⟩ hs ⟨x', y', z'⟩ ht h
    rw [Finset.mem_coe, Finset.mem_filter] at hs ht
    exact sorted_inj hs.2.1 hs.2.2 ht.2.1 ht.2.2 h


lemma pq_inj {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) {a b c d : ℕ}
    (h : p ^ a * q ^ b = p ^ c * q ^ d) : a = c ∧ b = d := by
  have key : ∀ a b, (p ^ a * q ^ b).factorization p = a ∧ (p ^ a * q ^ b).factorization q = b := by
    intro a b
    rw [Nat.factorization_mul (pow_ne_zero _ hp.ne_zero) (pow_ne_zero _ hq.ne_zero),
      Nat.factorization_pow, Nat.factorization_pow, hp.factorization, hq.factorization]
    simp [hpq, Ne.symm hpq]
  have h1 := key a b
  have h2 := key c d
  rw [h] at h1
  exact ⟨h1.1.symm.trans h2.1, h1.2.symm.trans h2.2⟩

lemma dvd_form {p q : ℕ} (hp : p.Prime) (hq : q.Prime) {n x : ℕ} (hx : x ∣ p ^ 5 * q ^ n) :
    ∃ a ≤ 5, ∃ b ≤ n, x = p ^ a * q ^ b := by
  obtain ⟨d1, d2, h1, h2, rfl⟩ := dvd_mul.mp hx
  obtain ⟨a, ha, rfl⟩ := (Nat.dvd_prime_pow hp).mp h1
  obtain ⟨b, hb, rfl⟩ := (Nat.dvd_prime_pow hq).mp h2
  exact ⟨a, ha, b, hb, rfl⟩


abbrev L := ℕ ×ₗ ℕ

def F (n : ℕ) (r : ℕ × ℕ × ℕ × ℕ) : L × L × L :=
  (toLex (r.1, r.2.2.1), toLex (r.2.1, r.2.2.2), toLex (5 - r.1 - r.2.1, n - r.2.2.1 - r.2.2.2))

def Q (n : ℕ) : Finset (ℕ × ℕ × ℕ × ℕ) :=
  (range 6 ×ˢ range 6 ×ˢ range (n + 1) ×ˢ range (n + 1)).filter
    (fun r => r.1 + r.2.1 ≤ 5 ∧ r.2.2.1 + r.2.2.2 ≤ n)

def E (n : ℕ) : Finset (L × L × L) := (Q n).image (F n)

lemma F_inj (n : ℕ) : Function.Injective (F n) := by
  rintro ⟨a1, a2, b1, b2⟩ ⟨c1, c2, d1, d2⟩ h
  simp only [F, Prod.mk.injEq, toLex_inj] at h
  obtain ⟨⟨rfl, rfl⟩, ⟨rfl, rfl⟩, -⟩ := h
  rfl

lemma mem_E {n a1 b1 a2 b2 a3 b3 : ℕ} :
    (toLex (a1, b1), toLex (a2, b2), toLex (a3, b3)) ∈ E n ↔
      a1 + a2 + a3 = 5 ∧ b1 + b2 + b3 = n := by
  constructor
  · intro h
    obtain ⟨⟨c1, c2, d1, d2⟩, hr, he⟩ := mem_image.mp h
    simp only [Q, mem_filter, mem_product, mem_range] at hr
    simp only [F, Prod.mk.injEq, toLex_inj] at he
    omega
  · rintro ⟨hA, hB⟩
    refine mem_image.mpr ⟨(a1, a2, b1, b2), ?_, ?_⟩
    · simp only [Q, mem_filter, mem_product, mem_range]; omega
    · have e1 : 5 - a1 - a2 = a3 := by omega
      have e2 : n - b1 - b2 = b3 := by omega
      simp only [F, e1, e2]

lemma E_form {n : ℕ} {t : L × L × L} (ht : t ∈ E n) :
    ∃ a1 b1 a2 b2 a3 b3 : ℕ, t = (toLex (a1, b1), toLex (a2, b2), toLex (a3, b3)) ∧
      a1 + a2 + a3 = 5 ∧ b1 + b2 + b3 = n := by
  obtain ⟨⟨a1, a2, b1, b2⟩, hr, rfl⟩ := mem_image.mp ht
  refine ⟨a1, b1, a2, b2, 5 - a1 - a2, n - b1 - b2, rfl, ?_⟩
  simp only [Q, mem_filter, mem_product, mem_range] at hr
  omega

lemma E_12 (n : ℕ) : ∀ t ∈ E n, (t.2.1, t.1, t.2.2) ∈ E n := by
  intro t ht
  obtain ⟨a1, b1, a2, b2, a3, b3, rfl, hA, hB⟩ := E_form ht
  exact mem_E.mpr ⟨by omega, by omega⟩

lemma E_23 (n : ℕ) : ∀ t ∈ E n, (t.1, t.2.2, t.2.1) ∈ E n := by
  intro t ht
  obtain ⟨a1, b1, a2, b2, a3, b3, rfl, hA, hB⟩ := E_form ht
  exact mem_E.mpr ⟨by omega, by omega⟩

def φ (p q : ℕ) (e : L) : ℕ := p ^ (ofLex e).1 * q ^ (ofLex e).2

def Φ (p q : ℕ) (t : L × L × L) : ℕ × ℕ × ℕ := (φ p q t.1, φ p q t.2.1, φ p q t.2.2)

def TV (V : ℕ) : Finset (ℕ × ℕ × ℕ) :=
  (V.divisors ×ˢ V.divisors ×ˢ V.divisors).filter (fun t => t.1 * t.2.1 * t.2.2 = V)

lemma TV_12 (V : ℕ) : ∀ t ∈ TV V, (t.2.1, t.1, t.2.2) ∈ TV V := by
  intro t ht
  simp only [TV, mem_filter, mem_product] at ht ⊢
  exact ⟨⟨ht.1.2.1, ht.1.1, ht.1.2.2⟩, by rw [← ht.2]; ring⟩

lemma TV_23 (V : ℕ) : ∀ t ∈ TV V, (t.1, t.2.2, t.2.1) ∈ TV V := by
  intro t ht
  simp only [TV, mem_filter, mem_product] at ht ⊢
  exact ⟨⟨ht.1.1, ht.1.2.2, ht.1.2.1⟩, by rw [← ht.2]; ring⟩

lemma TV_eq {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) (n : ℕ) :
    TV (p ^ 5 * q ^ n) = (E n).image (Φ p q) := by
  have hV : p ^ 5 * q ^ n ≠ 0 := mul_ne_zero (pow_ne_zero _ hp.ne_zero) (pow_ne_zero _ hq.ne_zero)
  ext ⟨x, y, z⟩
  simp only [TV, mem_filter, mem_product, Nat.mem_divisors, mem_image]
  constructor
  · rintro ⟨⟨⟨hx, -⟩, ⟨hy, -⟩, ⟨hz, -⟩⟩, hprod⟩
    obtain ⟨a1, -, b1, -, rfl⟩ := dvd_form hp hq hx
    obtain ⟨a2, -, b2, -, rfl⟩ := dvd_form hp hq hy
    obtain ⟨a3, -, b3, -, rfl⟩ := dvd_form hp hq hz
    have : p ^ (a1 + a2 + a3) * q ^ (b1 + b2 + b3) = p ^ 5 * q ^ n := by rw [← hprod]; ring
    obtain ⟨hA, hB⟩ := pq_inj hp hq hpq this
    exact ⟨(toLex (a1, b1), toLex (a2, b2), toLex (a3, b3)), mem_E.mpr ⟨hA, hB⟩, rfl⟩
  · rintro ⟨t, ht, he⟩
    obtain ⟨a1, b1, a2, b2, a3, b3, rfl, hA, hB⟩ := E_form ht
    simp only [Φ, φ, Prod.mk.injEq, ofLex_toLex] at he
    obtain ⟨rfl, rfl, rfl⟩ := he
    have hprod : p ^ a1 * q ^ b1 * (p ^ a2 * q ^ b2) * (p ^ a3 * q ^ b3) = p ^ 5 * q ^ n := by
      rw [← hA, ← hB]; ring
    exact ⟨⟨⟨Dvd.intro (p ^ a2 * q ^ b2 * (p ^ a3 * q ^ b3)) (by rw [← hprod]; ring), hV⟩,
      ⟨Dvd.intro (p ^ a1 * q ^ b1 * (p ^ a3 * q ^ b3)) (by rw [← hprod]; ring), hV⟩,
      ⟨Dvd.intro (p ^ a1 * q ^ b1 * (p ^ a2 * q ^ b2)) (by rw [← hprod]; ring), hV⟩⟩, hprod⟩

lemma φ_inj {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) :
    Function.Injective (φ p q) := by
  intro e e' h
  have := pq_inj hp hq hpq h
  exact ofLex.injective (Prod.ext this.1 this.2)

def W (n a1 a2 b1 b2 : ℕ) : ℕ :=
  if (a1 = 0 ∧ a2 = 0) ∨ (a1 = 1 ∧ a2 = 1) then (if b1 ≤ b2 ∧ b1 + b2 ≤ n then 1 else 0)
  else if (a1 = 0 ∧ a2 = 1) ∨ (a1 = 0 ∧ a2 = 2) then (if b1 + b2 ≤ n then 1 else 0)
  else if a1 = 1 ∧ a2 = 2 then (if b1 + 2 * b2 ≤ n then 1 else 0) else 0

def Wsum (n a1 a2 : ℕ) : ℕ :=
  if (a1 = 0 ∧ a2 = 0) ∨ (a1 = 1 ∧ a2 = 1) then g n
  else if (a1 = 0 ∧ a2 = 1) ∨ (a1 = 0 ∧ a2 = 2) then h n
  else if a1 = 1 ∧ a2 = 2 then g n else 0

lemma point (n : ℕ) (r : ℕ × ℕ × ℕ × ℕ) :
    (if (r.1 + r.2.1 ≤ 5 ∧ r.2.2.1 + r.2.2.2 ≤ n) ∧
        ((F n r).1 ≤ (F n r).2.1 ∧ (F n r).2.1 ≤ (F n r).2.2) then 1 else 0)
      = W n r.1 r.2.1 r.2.2.1 r.2.2.2 := by
  obtain ⟨a1, a2, b1, b2⟩ := r
  simp only [F, Prod.Lex.toLex_le_toLex, W]
  split_ifs <;> omega

lemma inner (n a1 a2 : ℕ) :
    (∑ b1 ∈ range (n + 1), ∑ b2 ∈ range (n + 1), W n a1 a2 b1 b2) = Wsum n a1 a2 := by
  by_cases c1 : (a1 = 0 ∧ a2 = 0) ∨ (a1 = 1 ∧ a2 = 1)
  · simp only [W, Wsum, c1, if_true]; exact L2 n
  by_cases c2 : (a1 = 0 ∧ a2 = 1) ∨ (a1 = 0 ∧ a2 = 2)
  · simp only [W, Wsum, c1, c2, if_true, if_false]; exact L1 n
  by_cases c3 : a1 = 1 ∧ a2 = 2
  · simp only [W, Wsum, c1, c2, c3, if_true, if_false]; exact L3 n
  · simp [W, Wsum, c1, c2, c3]

lemma count (n : ℕ) :
    #((Q n).filter (fun r => (F n r).1 ≤ (F n r).2.1 ∧ (F n r).2.1 ≤ (F n r).2.2)) =
      2 * h n + 3 * g n := by
  rw [Q, filter_filter, card_filter, Finset.sum_congr rfl (fun r _ => point n r)]
  simp only [Finset.sum_product, inner]
  simp [Finset.sum_range_succ, Wsum]
  ring

lemma cuboids_count {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) (n : ℕ) :
    OMA.S_oeis_a101425.cuboids (p ^ 5 * q ^ n) = 2 * h n + 3 * g n := by
  have e1 : OMA.S_oeis_a101425.cuboids (p ^ 5 * q ^ n) =
      #((TV (p ^ 5 * q ^ n)).filter (fun t => t.1 ≤ t.2.1 ∧ t.2.1 ≤ t.2.2)) := by
    unfold OMA.S_oeis_a101425.cuboids TV
    rw [filter_filter]
    congr 1
    exact Finset.filter_congr (fun t _ => by tauto)
  rw [e1, card_sorted _ (TV_12 _) (TV_23 _), TV_eq hp hq hpq, image_image]
  have e2 : (ms ∘ Φ p q) = (Multiset.map (φ p q)) ∘ ms := by
    funext t; simp [ms, Φ, Multiset.insert_eq_cons]
  rw [e2, ← image_image, card_image_of_injective _ (Multiset.map_injective (φ_inj hp hq hpq)),
    ← card_sorted _ (E_12 n) (E_23 n), E, filter_image, card_image_of_injective _ (F_inj n)]
  exact count n

theorem final : ∀ p q : ℕ, p.Prime → q.Prime → p ≠ q → ∀ n : ℕ,
    8 * (OMA.S_oeis_a101425.cuboids (p ^ 5 * q ^ n) : ℤ) = 37 + 3 * (-1) ^ n + 48 * n + 14 * n ^ 2 := by
  intro p q hp hq hpq n
  rw [cuboids_count hp hq hpq n]
  have H : (2 * h n : ℤ) = (n + 1) * (n + 2) := by exact_mod_cast h_two n
  rcases Nat.even_or_odd' n with ⟨m, rfl | rfl⟩
  · rw [g_even, pow_mul]; push_cast at H ⊢; norm_num; linear_combination 8 * H
  · rw [g_odd, pow_succ, pow_mul]; push_cast at H ⊢; norm_num; linear_combination 8 * H


end A101425Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a101425.main := A101425Proof.final
