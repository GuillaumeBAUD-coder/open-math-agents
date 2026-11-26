import FormalConjectures.ErdosProblems.«818»

-- Problem: Erdős Problem 818 — solymosi
-- Upstream: formal-conjectures FormalConjectures/ErdosProblems/818.lean:57 (declaration Erdos818.erdos_818.variants.solymosi)
-- Credit: @niclorusso (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

/-!
Solymosi's argument (Bounding multiplicative energy by the sumset, Adv. Math. 2009).

For a finite set `B` of integers of one sign, the points of `B × B` lie on lines through the
origin. Sorting the slopes of a family of lines that each carry at least `t` points, the sums of
a point on one line and a point on the next line are all distinct and lie in `(B + B) × (B + B)`,
which gives `(#S - 1) * t ^ 2 ≤ #(B + B) ^ 2`. Summing over dyadic classes of line sizes bounds
the multiplicative energy by `8 * (log₂ #B + 1) * #(B + B) ^ 2`, and Cauchy-Schwarz turns this
into the lower bound for `#(B * B)`.
-/

namespace OMA.Solymosi

open Finset
open scoped Pointwise

/-- The slope of the line through the origin and the point `p`. -/
def slope (p : ℤ × ℤ) : ℚ := (p.2 : ℚ) / (p.1 : ℚ)

/-- The points of `B × B` on the line of slope `l`. -/
def line (B : Finset ℤ) (l : ℚ) : Finset (ℤ × ℤ) := (B ×ˢ B).filter (fun p => slope p = l)

/-- The slopes of the points of `B × B`. -/
def slopes (B : Finset ℤ) : Finset ℚ := (B ×ˢ B).image slope

/-- The point-wise sum of two points. -/
def padd (pq : (ℤ × ℤ) × (ℤ × ℤ)) : ℤ × ℤ := (pq.1.1 + pq.2.1, pq.1.2 + pq.2.2)

section Core

variable {B : Finset ℤ}

lemma ne_zero_of_mem (hB : ∀ a ∈ B, ∀ b ∈ B, 0 < a * b) {a : ℤ} (ha : a ∈ B) : a ≠ 0 := by
  intro h
  have := hB a ha a ha
  rw [h] at this
  simp at this

lemma mem_line {l : ℚ} {p : ℤ × ℤ} :
    p ∈ line B l ↔ p.1 ∈ B ∧ p.2 ∈ B ∧ slope p = l := by
  simp [line, and_assoc]

lemma eq_of_mem_line (hB : ∀ a ∈ B, ∀ b ∈ B, 0 < a * b) {l : ℚ} {p : ℤ × ℤ}
    (hp : p ∈ line B l) : (p.2 : ℚ) = l * p.1 := by
  rw [mem_line] at hp
  obtain ⟨h1, -, h3⟩ := hp
  have h0 : (p.1 : ℚ) ≠ 0 := by exact_mod_cast ne_zero_of_mem hB h1
  rw [← h3, slope, div_mul_cancel₀ _ h0]

lemma card_line_le (hB : ∀ a ∈ B, ∀ b ∈ B, 0 < a * b) (l : ℚ) : #(line B l) ≤ #B := by
  apply card_le_card_of_injOn Prod.fst
  · intro p hp
    exact (mem_line.1 hp).1
  · intro p hp q hq hpq
    have e1 := eq_of_mem_line hB hp
    have e2 := eq_of_mem_line hB hq
    have h1 : (p.1 : ℚ) = q.1 := by exact_mod_cast hpq
    have h2 : (p.2 : ℚ) = q.2 := by rw [e1, e2, h1]
    exact Prod.ext hpq (by exact_mod_cast h2)

lemma line_nonempty {l : ℚ} (hl : l ∈ slopes B) : (line B l).Nonempty := by
  obtain ⟨p, hp, rfl⟩ := mem_image.1 hl
  exact ⟨p, mem_filter.2 ⟨hp, rfl⟩⟩

/-- The sum of a point on the line of slope `l` and a point on the line of slope `m`, with
`l < m`, has slope strictly between `l` and `m`. -/
lemma slope_padd (hB : ∀ a ∈ B, ∀ b ∈ B, 0 < a * b) {l m : ℚ} (hlm : l < m)
    {p q : ℤ × ℤ} (hp : p ∈ line B l) (hq : q ∈ line B m) :
    l < slope (padd (p, q)) ∧ slope (padd (p, q)) < m := by
  have e1 := eq_of_mem_line hB hp
  have e2 := eq_of_mem_line hB hq
  have hpq : (0 : ℚ) < (p.1 : ℚ) * q.1 := by
    exact_mod_cast hB p.1 (mem_line.1 hp).1 q.1 (mem_line.1 hq).1
  simp only [slope, padd]
  push_cast
  rw [e1, e2]
  rcases lt_or_gt_of_ne (show (p.1 : ℚ) + q.1 ≠ 0 by nlinarith [sq_nonneg ((p.1 : ℚ) - q.1)])
    with hD | hD
  · have hx : (p.1 : ℚ) < 0 := by nlinarith
    have hy : (q.1 : ℚ) < 0 := by nlinarith
    constructor
    · rw [lt_div_iff_of_neg hD]; nlinarith
    · rw [div_lt_iff_of_neg hD]; nlinarith
  · have hx : (0 : ℚ) < p.1 := by nlinarith
    have hy : (0 : ℚ) < q.1 := by nlinarith
    constructor
    · rw [lt_div_iff₀ hD]; nlinarith
    · rw [div_lt_iff₀ hD]; nlinarith

lemma padd_injOn (hB : ∀ a ∈ B, ∀ b ∈ B, 0 < a * b) {l m : ℚ} (hlm : l ≠ m) :
    Set.InjOn padd ((line B l ×ˢ line B m : Finset _) : Set ((ℤ × ℤ) × (ℤ × ℤ))) := by
  rintro ⟨p1, q1⟩ h1 ⟨p2, q2⟩ h2 heq
  simp only [coe_product, Set.mem_prod, mem_coe] at h1 h2
  have e1 := eq_of_mem_line hB h1.1
  have e2 := eq_of_mem_line hB h2.1
  have f1 := eq_of_mem_line hB h1.2
  have f2 := eq_of_mem_line hB h2.2
  simp only [padd, Prod.mk.injEq] at heq
  have g1 : (p1.1 : ℚ) + q1.1 = p2.1 + q2.1 := by exact_mod_cast heq.1
  have g2 : (p1.2 : ℚ) + q1.2 = p2.2 + q2.2 := by exact_mod_cast heq.2
  have k : (l - m) * ((p1.1 : ℚ) - p2.1) = 0 := by
    linear_combination g2 - e1 + e2 - f1 + f2 - m * g1
  have ka : (p1.1 : ℚ) = p2.1 := by
    have := (mul_eq_zero.1 k).resolve_left (sub_ne_zero.2 hlm)
    linarith
  have kb : (q1.1 : ℚ) = q2.1 := by linarith
  have kc : (p1.2 : ℚ) = p2.2 := by rw [e1, e2, ka]
  have kd : (q1.2 : ℚ) = q2.2 := by rw [f1, f2, kb]
  have ha : p1 = p2 := Prod.ext (by exact_mod_cast ka) (by exact_mod_cast kc)
  have hb : q1 = q2 := Prod.ext (by exact_mod_cast kb) (by exact_mod_cast kd)
  rw [ha, hb]

/-- The next slope of `S` after `l` (or `l` itself if there is none). -/
def nextSlope (S : Finset ℚ) (l : ℚ) : ℚ :=
  if h : (S.filter (fun m => l < m)).Nonempty then (S.filter (fun m => l < m)).min' h else l

lemma nextSlope_spec {S : Finset ℚ} {l : ℚ} (h : (S.filter (fun m => l < m)).Nonempty) :
    nextSlope S l ∈ S ∧ l < nextSlope S l ∧ ∀ m ∈ S, l < m → nextSlope S l ≤ m := by
  have hmem := min'_mem _ h
  rw [mem_filter] at hmem
  refine ⟨?_, ?_, ?_⟩
  · rw [nextSlope, dif_pos h]; exact hmem.1
  · rw [nextSlope, dif_pos h]; exact hmem.2
  · intro m hm hlm
    rw [nextSlope, dif_pos h]
    exact min'_le _ _ (mem_filter.2 ⟨hm, hlm⟩)

/-- Solymosi's cone argument: if every line with slope in `S` carries at least `t` points,
then `(#S - 1) * t ^ 2 ≤ #(B + B) ^ 2`. -/
lemma cone_bound (hB : ∀ a ∈ B, ∀ b ∈ B, 0 < a * b) (S : Finset ℚ) (t : ℕ)
    (ht : ∀ l ∈ S, t ≤ #(line B l)) : (#S - 1) * t ^ 2 ≤ #(B + B) ^ 2 := by
  rcases S.eq_empty_or_nonempty with hS | hS
  · simp [hS]
  set M := S.max' hS with hM
  set T := S.erase M with hT
  have hTcard : #T = #S - 1 := card_erase_of_mem (max'_mem S hS)
  have hnext : ∀ l ∈ T, (S.filter (fun m => l < m)).Nonempty := by
    intro l hl
    refine ⟨M, mem_filter.2 ⟨max'_mem S hS, ?_⟩⟩
    have h1 := mem_erase.1 hl
    exact lt_of_le_of_ne (le_max' S l h1.2) h1.1
  let Z : ℚ → Finset (ℤ × ℤ) := fun l => (line B l ×ˢ line B (nextSlope S l)).image padd
  have hZsub : T.biUnion Z ⊆ (B + B) ×ˢ (B + B) := by
    intro z hz
    obtain ⟨l, -, hz⟩ := mem_biUnion.1 hz
    obtain ⟨⟨p, q⟩, hpq, rfl⟩ := mem_image.1 hz
    rw [mem_product] at hpq
    have hp := mem_line.1 hpq.1
    have hq := mem_line.1 hpq.2
    exact mem_product.2 ⟨add_mem_add hp.1 hq.1, add_mem_add hp.2.1 hq.2.1⟩
  have hZcard : ∀ l ∈ T, t ^ 2 ≤ #(Z l) := by
    intro l hl
    obtain ⟨hs, hls, -⟩ := nextSlope_spec (hnext l hl)
    rw [card_image_of_injOn (padd_injOn hB (ne_of_lt hls)), card_product, sq]
    exact Nat.mul_le_mul (ht l (mem_of_mem_erase hl)) (ht _ hs)
  have hslopeZ : ∀ l ∈ T, ∀ z ∈ Z l, l < slope z ∧ slope z < nextSlope S l := by
    intro l hl z hz
    obtain ⟨-, hls, -⟩ := nextSlope_spec (hnext l hl)
    obtain ⟨⟨p, q⟩, hpq, rfl⟩ := mem_image.1 hz
    rw [mem_product] at hpq
    exact slope_padd hB hls hpq.1 hpq.2
  have hdisj : (T : Set ℚ).PairwiseDisjoint Z := by
    intro l1 hl1 l2 hl2 hne
    rw [Function.onFun, disjoint_left]
    intro z hz1 hz2
    have s1 := hslopeZ l1 hl1 z hz1
    have s2 := hslopeZ l2 hl2 z hz2
    rcases lt_or_gt_of_ne hne with h | h
    · have := (nextSlope_spec (hnext l1 hl1)).2.2 l2 (mem_of_mem_erase hl2) h
      linarith [s1.2, s2.1]
    · have := (nextSlope_spec (hnext l2 hl2)).2.2 l1 (mem_of_mem_erase hl1) h
      linarith [s2.2, s1.1]
  calc (#S - 1) * t ^ 2 = ∑ _l ∈ T, t ^ 2 := by rw [sum_const, smul_eq_mul, hTcard]
    _ ≤ ∑ l ∈ T, #(Z l) := sum_le_sum hZcard
    _ = #(T.biUnion Z) := (card_biUnion hdisj).symm
    _ ≤ #((B + B) ×ˢ (B + B)) := card_le_card hZsub
    _ = #(B + B) ^ 2 := by rw [card_product, sq]

/-- The multiplicative energy is the number of pairs of points of `B × B` with equal slopes. -/
lemma mulEnergy_le (hB : ∀ a ∈ B, ∀ b ∈ B, 0 < a * b) :
    mulEnergy B B ≤ ∑ l ∈ slopes B, #(line B l) ^ 2 := by
  have h1 : mulEnergy B B = #{x ∈ (B ×ˢ B) ×ˢ (B ×ˢ B) | slope x.1 = slope x.2} := by
    unfold mulEnergy
    apply card_nbij' (fun x => ((x.1.2, x.1.1), x.2)) (fun x => ((x.1.2, x.1.1), x.2))
    · rintro ⟨⟨a1, a2⟩, ⟨b1, b2⟩⟩ hx
      simp only [coe_filter, Set.mem_setOf_eq, mem_product] at hx ⊢
      obtain ⟨⟨⟨ha1, ha2⟩, hb1, hb2⟩, he⟩ := hx
      refine ⟨⟨⟨ha2, ha1⟩, hb1, hb2⟩, ?_⟩
      have h0 : (a2 : ℚ) ≠ 0 := by exact_mod_cast ne_zero_of_mem hB ha2
      have h0' : (b1 : ℚ) ≠ 0 := by exact_mod_cast ne_zero_of_mem hB hb1
      simp only [slope]
      rw [div_eq_div_iff h0 h0']
      exact_mod_cast (by linarith [he] : a1 * b1 = b2 * a2)
    · rintro ⟨⟨a1, a2⟩, ⟨b1, b2⟩⟩ hx
      simp only [coe_filter, Set.mem_setOf_eq, mem_product] at hx ⊢
      obtain ⟨⟨⟨ha1, ha2⟩, hb1, hb2⟩, he⟩ := hx
      refine ⟨⟨⟨ha2, ha1⟩, hb1, hb2⟩, ?_⟩
      have h0 : (a1 : ℚ) ≠ 0 := by exact_mod_cast ne_zero_of_mem hB ha1
      have h0' : (b1 : ℚ) ≠ 0 := by exact_mod_cast ne_zero_of_mem hB hb1
      simp only [slope] at he
      rw [div_eq_div_iff h0 h0'] at he
      have he' : ((a2 * b1 : ℤ) : ℚ) = ((b2 * a1 : ℤ) : ℚ) := by push_cast; exact he
      have := Int.cast_injective he'
      linarith
    · intro x _
      rfl
    · intro x _
      rfl
  rw [h1, card_eq_sum_card_fiberwise (f := fun x => slope x.1) (t := slopes B)]
  · apply le_of_eq
    apply sum_congr rfl
    intro l _
    rw [sq, ← card_product]
    congr 1
    ext ⟨p, q⟩
    simp only [mem_filter, mem_product, line]
    constructor
    · rintro ⟨⟨⟨hp, hq⟩, he⟩, hl⟩
      exact ⟨⟨hp, hl⟩, hq, he ▸ hl⟩
    · rintro ⟨⟨hp, hl⟩, hq, hl'⟩
      exact ⟨⟨⟨hp, hq⟩, hl.trans hl'.symm⟩, hl⟩
  · intro x hx
    simp only [coe_filter, Set.mem_setOf_eq, mem_product] at hx
    exact mem_coe.2 (mem_image.2 ⟨x.1, mem_product.2 hx.1.1, rfl⟩)

/-- One dyadic class of lines contributes at most `8 * #(B + B) ^ 2` to the energy. -/
lemma dyadic_bound (hB : ∀ a ∈ B, ∀ b ∈ B, 0 < a * b) (k : ℕ) :
    ∑ l ∈ (slopes B).filter (fun l => Nat.log 2 #(line B l) = k), #(line B l) ^ 2 ≤
      8 * #(B + B) ^ 2 := by
  set S := (slopes B).filter (fun l => Nat.log 2 #(line B l) = k) with hS
  have hlo : ∀ l ∈ S, 2 ^ k ≤ #(line B l) := by
    intro l hl
    rw [mem_filter] at hl
    rw [← hl.2]
    exact Nat.pow_log_le_self 2 (line_nonempty hl.1).card_pos.ne'
  have hhi : ∀ l ∈ S, #(line B l) ^ 2 ≤ 4 * (2 ^ k) ^ 2 := by
    intro l hl
    rw [mem_filter] at hl
    have := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) #(line B l)
    rw [hl.2, pow_succ] at this
    nlinarith
  have hsum : ∑ l ∈ S, #(line B l) ^ 2 ≤ #S * (4 * (2 ^ k) ^ 2) := by
    calc ∑ l ∈ S, #(line B l) ^ 2 ≤ ∑ _l ∈ S, 4 * (2 ^ k) ^ 2 := sum_le_sum hhi
      _ = #S * (4 * (2 ^ k) ^ 2) := by rw [sum_const, smul_eq_mul]
  have hcone := cone_bound hB S (2 ^ k) hlo
  rcases Nat.lt_or_ge #S 2 with hS2 | hS2
  · rcases S.eq_empty_or_nonempty with hSe | ⟨l, hl⟩
    · rw [hSe, sum_empty]; exact Nat.zero_le _
    · have hBne : B.Nonempty := by
        obtain ⟨p, hp⟩ := line_nonempty (mem_filter.1 hl).1
        exact ⟨p.1, (mem_line.1 hp).1⟩
      have hkB : 2 ^ k ≤ #(B + B) :=
        (hlo l hl).trans ((card_line_le hB l).trans (card_le_card_add_left hBne))
      have hsq : (2 ^ k) ^ 2 ≤ #(B + B) ^ 2 := Nat.pow_le_pow_left hkB 2
      calc ∑ l ∈ S, #(line B l) ^ 2 ≤ #S * (4 * (2 ^ k) ^ 2) := hsum
        _ ≤ 1 * (4 * #(B + B) ^ 2) := Nat.mul_le_mul (by omega) (by omega)
        _ ≤ 8 * #(B + B) ^ 2 := by omega
  · calc ∑ l ∈ S, #(line B l) ^ 2 ≤ #S * (4 * (2 ^ k) ^ 2) := hsum
      _ ≤ 8 * ((#S - 1) * (2 ^ k) ^ 2) := by
          rw [← mul_assoc, ← mul_assoc]
          exact Nat.mul_le_mul_right _ (by omega)
      _ ≤ 8 * #(B + B) ^ 2 := Nat.mul_le_mul_left 8 hcone

/-- Solymosi's energy bound. -/
lemma mulEnergy_bound (hB : ∀ a ∈ B, ∀ b ∈ B, 0 < a * b) :
    mulEnergy B B ≤ (Nat.log 2 #B + 1) * (8 * #(B + B) ^ 2) := by
  refine (mulEnergy_le hB).trans ?_
  have hmaps : ∀ l ∈ slopes B, Nat.log 2 #(line B l) ∈ range (Nat.log 2 #B + 1) := by
    intro l _
    exact mem_range.2 (Nat.lt_succ_of_le (Nat.log_mono_right (card_line_le hB l)))
  rw [← sum_fiberwise_of_maps_to hmaps]
  calc ∑ k ∈ range (Nat.log 2 #B + 1),
        ∑ l ∈ (slopes B).filter (fun l => Nat.log 2 #(line B l) = k), #(line B l) ^ 2
      ≤ ∑ _k ∈ range (Nat.log 2 #B + 1), 8 * #(B + B) ^ 2 :=
        sum_le_sum fun k _ => dyadic_bound hB k
    _ = (Nat.log 2 #B + 1) * (8 * #(B + B) ^ 2) := by rw [sum_const, card_range, smul_eq_mul]

lemma core (hB : ∀ a ∈ B, ∀ b ∈ B, 0 < a * b) :
    #B ^ 4 ≤ #(B * B) * ((Nat.log 2 #B + 1) * (8 * #(B + B) ^ 2)) := by
  have h := le_card_mul_mul_mulEnergy B B
  calc #B ^ 4 = #B ^ 2 * #B ^ 2 := by ring
    _ ≤ #(B * B) * mulEnergy B B := h
    _ ≤ #(B * B) * ((Nat.log 2 #B + 1) * (8 * #(B + B) ^ 2)) :=
        Nat.mul_le_mul_left _ (mulEnergy_bound hB)

end Core

/-- A set of at least two integers has a quarter of its elements of one sign. -/
lemma exists_one_sign (A : Finset ℤ) (hA : 2 ≤ #A) :
    ∃ B ⊆ A, #A ≤ 4 * #B ∧ ∀ a ∈ B, ∀ b ∈ B, 0 < a * b := by
  set P := A.filter (fun a => 0 < a)
  set N := A.filter (fun a => a < 0)
  have hsub : A ⊆ P ∪ N ∪ {0} := by
    intro a ha
    simp only [P, N, mem_union, mem_filter, mem_singleton]
    rcases lt_trichotomy a 0 with h | h | h
    · exact Or.inl (Or.inr ⟨ha, h⟩)
    · exact Or.inr h
    · exact Or.inl (Or.inl ⟨ha, h⟩)
  have hcard : #A ≤ #P + #N + 1 :=
    (card_le_card hsub).trans ((card_union_le _ _).trans
      (by rw [card_singleton]; exact Nat.add_le_add_right (card_union_le _ _) 1))
  rcases le_total #N #P with h | h
  · refine ⟨P, filter_subset _ _, by omega, ?_⟩
    intro a ha b hb
    exact mul_pos (mem_filter.1 ha).2 (mem_filter.1 hb).2
  · refine ⟨N, filter_subset _ _, by omega, ?_⟩
    intro a ha b hb
    exact mul_pos_of_neg_of_neg (mem_filter.1 ha).2 (mem_filter.1 hb).2

/-- `Nat.log 2 n + 1 ≤ 3 * log n` for `n ≥ 2`. -/
lemma natLog_le (n : ℕ) (hn : 2 ≤ n) :
    ((Nat.log 2 n : ℕ) : ℝ) + 1 ≤ 3 * Real.log n := by
  have h2 : (2 : ℝ) ^ (Nat.log 2 n) ≤ n := by
    exact_mod_cast Nat.pow_log_le_self 2 (by omega : n ≠ 0)
  have hL : ((Nat.log 2 n : ℕ) : ℝ) * Real.log 2 ≤ Real.log n := by
    rw [← Real.log_pow]
    exact Real.log_le_log (by positivity) h2
  have hl2 : Real.log 2 ≤ Real.log n :=
    Real.log_le_log (by norm_num) (by exact_mod_cast hn)
  have hlog2 := Real.log_two_gt_d9
  have hL0 : (0 : ℝ) ≤ (Nat.log 2 n : ℕ) := Nat.cast_nonneg _
  nlinarith

end OMA.Solymosi

open Finset OMA.Solymosi in
open scoped Pointwise in
theorem OMA.solution : type_of% @Erdos818.erdos_818.variants.solymosi := by
  intro K hK
  refine ⟨1 / (6144 * K ^ 2), by positivity, ?_⟩
  intro A hA hAK
  obtain ⟨B, hBA, hAB, hB⟩ := exists_one_sign A hA
  have hc := core hB
  -- Pass from `B` to `A`.
  have hmul : #(B * B) ≤ #(A * A) := card_le_card (mul_subset_mul hBA hBA)
  have hadd : #(B + B) ≤ #(A + A) := card_le_card (add_subset_add hBA hBA)
  have hlog : Nat.log 2 #B ≤ Nat.log 2 #A := Nat.log_mono_right (card_le_card hBA)
  have hnat : #A ^ 4 ≤ 256 * (#(A * A) * ((Nat.log 2 #A + 1) * (8 * #(A + A) ^ 2))) := by
    calc #A ^ 4 ≤ (4 * #B) ^ 4 := Nat.pow_le_pow_left hAB 4
      _ = 256 * #B ^ 4 := by ring
      _ ≤ 256 * (#(B * B) * ((Nat.log 2 #B + 1) * (8 * #(B + B) ^ 2))) :=
          Nat.mul_le_mul_left _ hc
      _ ≤ 256 * (#(A * A) * ((Nat.log 2 #A + 1) * (8 * #(A + A) ^ 2))) := by
          gcongr
  -- Real arithmetic.
  set n : ℝ := (#A : ℝ) with hn
  set X : ℝ := (#(A * A) : ℝ) with hX
  set s : ℝ := (#(A + A) : ℝ) with hs
  set L : ℝ := ((Nat.log 2 #A : ℕ) : ℝ) with hL
  have hreal : n ^ 4 ≤ 256 * (X * ((L + 1) * (8 * s ^ 2))) := by
    have := (Nat.cast_le (α := ℝ)).2 hnat
    push_cast at this
    exact this
  have hn2 : (2 : ℝ) ≤ n := by rw [hn]; exact_mod_cast hA
  have hnpos : (0 : ℝ) < n := by linarith
  have hX0 : (0 : ℝ) ≤ X := Nat.cast_nonneg _
  have hs0 : (0 : ℝ) ≤ s := Nat.cast_nonneg _
  have hL0 : (0 : ℝ) ≤ L := Nat.cast_nonneg _
  have hsK : s ^ 2 ≤ (K * n) ^ 2 := pow_le_pow_left₀ hs0 hAK 2
  have hLlog : L + 1 ≤ 3 * Real.log n := natLog_le #A hA
  have hlogpos : 0 < Real.log n := Real.log_pos (by linarith)
  -- n ^ 4 ≤ 6144 K^2 n^2 X log n
  have h1 : n ^ 4 ≤ 2048 * X * (L + 1) * (K * n) ^ 2 := by
    have : X * ((L + 1) * (8 * s ^ 2)) ≤ X * ((L + 1) * (8 * (K * n) ^ 2)) := by gcongr
    nlinarith
  have h2 : n ^ 4 ≤ (6144 * K ^ 2 * X * Real.log n) * n ^ 2 := by
    have : 2048 * X * (L + 1) * (K * n) ^ 2 ≤ 2048 * X * (3 * Real.log n) * (K * n) ^ 2 := by
      gcongr
    nlinarith
  have h3 : n ^ 2 ≤ 6144 * K ^ 2 * X * Real.log n := by
    have hn2pos : 0 < n ^ 2 := by positivity
    have : n ^ 2 * n ^ 2 ≤ (6144 * K ^ 2 * X * Real.log n) * n ^ 2 := by nlinarith
    exact le_of_mul_le_mul_right this hn2pos
  rw [div_le_iff₀ hlogpos]
  rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ (by positivity)]
  nlinarith
