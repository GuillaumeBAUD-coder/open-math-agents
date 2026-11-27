import OMAStatements.S_oeis_a007335

/-!
Classify the multiplicative Ulam sequence from 2 and 3 in exponent coordinates.
The elements are the two boundary families, together with the powers whose
two exponents are odd. The lattice classification is Theorem 1 of Kravitz and
Steinerberger, Ulam Sequences and Ulam Sets (Integers 18, 2018, A80).
The reciprocal sum was conjectured by Amiram Eldar in OEIS A007335.
-/

namespace A007335Proof

private def good (a b : ℕ) : Prop :=
  a = 1 ∨ b = 1 ∨ (a % 2 = 1 ∧ b % 2 = 1)

private def encode (a b : ℕ) : ℕ := 2 ^ a * 3 ^ b

private theorem encode_pos (a b : ℕ) : 0 < encode a b := by
  unfold encode
  positivity

private theorem encode_mul (a b c d : ℕ) :
    encode a b * encode c d = encode (a + c) (b + d) := by
  simp only [encode, pow_add]
  ac_rfl

private theorem encode_injective {a b c d : ℕ} (h : encode a b = encode c d) :
    a = c ∧ b = d := by
  have p2 : Nat.Prime 2 := Nat.prime_two
  have p3 : Nat.Prime 3 := Nat.prime_three
  have htwo (i j : ℕ) : (encode i j).factorization 2 = i := by
    simp [encode, Nat.factorization_mul, Nat.factorization_pow, p2.factorization,
      p3.factorization]
  have hthree (i j : ℕ) : (encode i j).factorization 3 = j := by
    simp [encode, Nat.factorization_mul, Nat.factorization_pow, p2.factorization,
      p3.factorization]
  exact ⟨(htwo a b).symm.trans (h ▸ htwo c d), (hthree a b).symm.trans (h ▸ hthree c d)⟩

private theorem good_rep_unique {a b i j k l : ℕ}
    (ha : 1 ≤ a) (hb : 1 ≤ b) (hab : good a b)
    (hi : good i j) (hk : good k l) (h₁ : i + k = a) (h₂ : j + l = b) :
    (i = 1 ∧ j = b - 1 ∧ k = a - 1 ∧ l = 1) ∨
      (i = a - 1 ∧ j = 1 ∧ k = 1 ∧ l = b - 1) := by
  unfold good at *
  omega

private theorem second_rep {a b : ℕ} (ha : 2 ≤ a) (hb : 2 ≤ b)
    (hnot : ¬ good a b) :
    ∃ i j k l : ℕ, good i j ∧ good k l ∧ i + k = a ∧ j + l = b ∧
      (i ≠ k ∨ j ≠ l) ∧
      ¬ (i = 1 ∧ j = b - 1) ∧ ¬ (i = a - 1 ∧ j = 1) := by
  unfold good at *
  by_cases ha2 : a = 2
  · by_cases hb2 : b = 2
    · -- The other pair at (2,2) is supplied separately below.
      subst a
      subst b
      exact ⟨1, 0, 1, 2, by omega⟩
    · exact ⟨1, 0, 1, b, by omega⟩
  by_cases hb2 : b = 2
  · exact ⟨0, 1, a, 1, by omega⟩
  by_cases hoa : a % 2 = 1
  · exact ⟨0, 1, a, b - 1, by omega⟩
  by_cases hob : b % 2 = 1
  · exact ⟨1, 0, a - 1, b, by omega⟩
  exact ⟨1, 1, a - 1, b - 1, by omega⟩

private def member (n : ℕ) : Prop := ∃ a b, good a b ∧ encode a b = n

private theorem member_two : member 2 := ⟨1, 0, by simp [good], by decide⟩

private theorem member_three : member 3 := ⟨0, 1, by simp [good], by decide⟩

open OMA.S_oeis_a007335

private def rep (m : ℕ) (t : ℕ × ℕ) : Prop :=
  member t.1 ∧ member t.2 ∧ t.1 < t.2 ∧ t.1 * t.2 = m

private def ordered (x y : ℕ) : ℕ × ℕ :=
  if x < y then (x, y) else (y, x)

private theorem rep_ordered {m x y : ℕ} (hx : member x) (hy : member y)
    (hne : x ≠ y) (hm : x * y = m) : rep m (ordered x y) := by
  unfold rep ordered
  split
  next h => exact ⟨hx, hy, h, hm⟩
  next h => exact ⟨hy, hx, by omega, by rwa [Nat.mul_comm]⟩

private theorem ordered_comm (x y : ℕ) : ordered x y = ordered y x := by
  unfold ordered
  by_cases hxy : x < y
  · rw [if_pos hxy, if_neg (by omega)]
  · by_cases hyx : y < x
    · rw [if_neg hxy, if_pos hyx]
    · have : x = y := by omega
      subst y
      rfl

private theorem ordered_eq_imp {x y z w : ℕ} (h : ordered x y = ordered z w) :
    (x = z ∧ y = w) ∨ (x = w ∧ y = z) := by
  by_cases hxy : x < y <;> by_cases hzw : z < w <;>
    simp_all [ordered, Prod.mk.injEq, eq_comm, and_comm]

private theorem nat_value_ne {a b c d : ℕ} (h : a ≠ c ∨ b ≠ d) :
    encode a b ≠ encode c d := by
  intro he
  obtain ⟨ha, hb⟩ := encode_injective he
  exact h.elim (fun hn => hn ha) (fun hn => hn hb)

private theorem canonical_ne {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b)
    (h : a ≠ 2 ∨ b ≠ 2) : encode 1 (b - 1) ≠ encode (a - 1) 1 := by
  apply nat_value_ne
  omega

private theorem canonical_rep {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b)
    (h : a ≠ 2 ∨ b ≠ 2) :
    rep (encode a b) (ordered (encode 1 (b - 1)) (encode (a - 1) 1)) := by
  refine rep_ordered ⟨1, b - 1, by simp [good], rfl⟩
    ⟨a - 1, 1, by simp [good], rfl⟩ (canonical_ne ha hb h) ?_
  rw [encode_mul, show 1 + (a - 1) = a by omega, show b - 1 + 1 = b by omega]

private theorem good_unique {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) (h : good a b) :
    ∃! t, rep (encode a b) t := by
  have hne : a ≠ 2 ∨ b ≠ 2 := by unfold good at h; omega
  refine ⟨_, canonical_rep ha hb hne, ?_⟩
  rintro ⟨x, y⟩ ⟨⟨i, j, hi, rfl⟩, ⟨k, l, hk, rfl⟩, hxy, hp⟩
  have ⟨h₁, h₂⟩ := encode_injective ((encode_mul i j k l).symm.trans hp)
  change encode i j < encode k l at hxy
  have hpairs := good_rep_unique ha hb h hi hk h₁ h₂
  rcases hpairs with ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩
  · simp [ordered, hxy]
  · rw [ordered_comm]
    simp [ordered, hxy]

private theorem bad_not_unique {a b : ℕ} (ha : 2 ≤ a) (hb : 2 ≤ b) (h : ¬ good a b) :
    ¬ (∃! t, rep (encode a b) t) := by
  rintro ⟨t, -, ht⟩
  by_cases h22 : a = 2 ∧ b = 2
  · obtain ⟨rfl, rfl⟩ := h22
    have h₁ : rep (encode 2 2) (2, 18) :=
      ⟨member_two, ⟨1, 2, by simp [good], by decide⟩, by decide, by decide⟩
    have h₂ : rep (encode 2 2) (3, 12) :=
      ⟨member_three, ⟨2, 1, by simp [good], by decide⟩, by decide, by decide⟩
    have he := (ht _ h₁).trans (ht _ h₂).symm
    simp at he
  · have hne : a ≠ 2 ∨ b ≠ 2 := by omega
    obtain ⟨i, j, k, l, hi, hk, h₁, h₂, hd, hl, hr⟩ := second_rep ha hb h
    have hm : encode i j * encode k l = encode a b := by rw [encode_mul, h₁, h₂]
    have hother := rep_ordered ⟨i, j, hi, rfl⟩ ⟨k, l, hk, rfl⟩ (nat_value_ne hd) hm
    have hc := canonical_rep (by omega : 1 ≤ a) (by omega : 1 ≤ b) hne
    have he := (ht _ hother).trans (ht _ hc).symm
    rcases ordered_eq_imp he with ⟨he, _⟩ | ⟨he, _⟩
    · exact hl (encode_injective he)
    · exact hr (encode_injective he)

private theorem encode_axis {a b : ℕ} (h : good a b) (ha : a = 0 ∨ b = 0) :
    encode a b = 2 ∨ encode a b = 3 := by
  unfold good at h
  have he : (a = 0 ∧ b = 1) ∨ (a = 1 ∧ b = 0) := by omega
  rcases he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide

private theorem global_iff {m : ℕ} (hm : 3 < m) :
    UniquePair {n | member n} m ↔ member m := by
  change (∃! t, rep m t) ↔ member m
  constructor
  · rintro ⟨⟨x, y⟩, hr, hunique⟩
    have hfull := hr
    obtain ⟨⟨i, j, hi, hx⟩, ⟨k, l, hk, hy⟩, hlt, hprod⟩ := hr
    change x < y at hlt
    change x * y = m at hprod
    change encode i j = x at hx
    change encode k l = y at hy
    subst x
    subst y
    rw [encode_mul] at hprod
    subst m
    have ha : 1 ≤ i + k := by
      by_contra! hn
      have h₁ : j = 1 := by unfold good at hi; omega
      have h₂ : l = 1 := by unfold good at hk; omega
      have he : i = k := by omega
      exact hlt.ne (by rw [he, h₁, h₂])
    have hb : 1 ≤ j + l := by
      by_contra! hn
      have h₁ : i = 1 := by unfold good at hi; omega
      have h₂ : k = 1 := by unfold good at hk; omega
      have he : j = l := by omega
      exact hlt.ne (by rw [he, h₁, h₂])
    by_cases hgood : good (i + k) (j + l)
    · exact ⟨_, _, hgood, rfl⟩
    · have h₂ : 2 ≤ i + k ∧ 2 ≤ j + l := by unfold good at hgood; omega
      exact (bad_not_unique h₂.1 h₂.2 hgood ⟨_, hfull, hunique⟩).elim
  · rintro ⟨a, b, h, rfl⟩
    have hab : 1 ≤ a ∧ 1 ≤ b := by
      by_contra! hn
      have hz : a = 0 ∨ b = 0 := by omega
      rcases encode_axis h hz with he | he <;> omega
    exact good_unique hab.1 hab.2 h

private theorem member_ge_two {m : ℕ} (hm : member m) : 2 ≤ m := by
  obtain ⟨a, b, h, rfl⟩ := hm
  have hp : 1 ≤ a ∨ 1 ≤ b := by unfold good at h; omega
  unfold encode
  rcases hp with ha | hb
  · have htwo : 2 ≤ 2 ^ a := by
      simpa using Nat.pow_le_pow_right (by decide : 0 < 2) ha
    have hthree : 1 ≤ 3 ^ b := Nat.pow_pos (by decide)
    simpa using Nat.mul_le_mul htwo hthree
  · have htwo : 1 ≤ 2 ^ a := Nat.pow_pos (by decide)
    have hthree : 3 ≤ 3 ^ b := by
      simpa using Nat.pow_le_pow_right (by decide : 0 < 3) hb
    have h := Nat.mul_le_mul htwo hthree
    omega

private theorem member_infinite : Set.Infinite {m | member m} := by
  apply Set.infinite_of_injective_forall_mem (f := fun b : ℕ => encode 1 b)
  · intro b c h
    exact (encode_injective h).2
  · intro b
    exact ⟨1, b, by simp [good], rfl⟩

private noncomputable def sequence : ℕ → ℕ := Nat.nth member

private theorem sequence_mono : StrictMono sequence := Nat.nth_strictMono member_infinite

private theorem sequence_mem (n : ℕ) : member (sequence n) :=
  Nat.nth_mem_of_infinite member_infinite n

private theorem sequence_range : Set.range sequence = {m | member m} :=
  Nat.range_nth_of_infinite member_infinite

private theorem sequence_two : sequence 0 = 2 := by
  apply le_antisymm
  · exact (Nat.isLeast_nth_of_infinite member_infinite 0).2
      ⟨member_two, by omega⟩
  · exact member_ge_two (sequence_mem 0)

private theorem sequence_three : sequence 1 = 3 := by
  apply le_antisymm
  · apply (Nat.isLeast_nth_of_infinite member_infinite 1).2
    refine ⟨member_three, ?_⟩
    intro k hk
    have : k = 0 := by omega
    change sequence k < 3
    simp [this, sequence_two]
  · have h := sequence_mono (show 0 < 1 by decide)
    rw [sequence_two] at h
    exact h

private theorem member_prefix {k m : ℕ} (hm : member m) (h : m < sequence (k + 1)) :
    m ∈ sequence '' Set.Iic k := by
  obtain ⟨i, rfl⟩ : m ∈ Set.range sequence := by rw [sequence_range]; exact hm
  have hi : i < k + 1 := sequence_mono.lt_iff_lt.mp h
  exact ⟨i, by change i ≤ k; omega, rfl⟩

private theorem prefix_member {k m : ℕ} (hm : m ∈ sequence '' Set.Iic k) : member m := by
  obtain ⟨i, -, rfl⟩ := hm
  exact sequence_mem i

private theorem prefix_iff {k m : ℕ} (hm : m ≤ sequence (k + 1)) :
    UniquePair (sequence '' Set.Iic k) m ↔ UniquePair {n | member n} m := by
  apply existsUnique_congr
  rintro ⟨x, y⟩
  constructor
  · rintro ⟨hx, hy, hxy, hmul⟩
    exact ⟨prefix_member hx, prefix_member hy, hxy, hmul⟩
  · rintro ⟨hx, hy, hxy, hmul⟩
    change member x at hx
    change member y at hy
    change x * y = m at hmul
    have htwo := member_ge_two hx
    have hthree := member_ge_two hy
    have hltx : x < m := by
      have h := Nat.mul_le_mul_left x hthree
      omega
    have hlty : y < m := by
      have h := Nat.mul_le_mul_right y htwo
      omega
    exact ⟨member_prefix hx (hltx.trans_le hm), member_prefix hy (hlty.trans_le hm),
      hxy, hmul⟩

private theorem sequence_greedy : IsMU sequence := by
  refine ⟨sequence_two, sequence_three, fun n => ?_⟩
  have hstep : sequence (n + 1) < sequence (n + 2) := sequence_mono (by omega)
  have hthree : 3 ≤ sequence (n + 1) := by
    rw [← sequence_three]
    exact sequence_mono.monotone (by omega)
  constructor
  · exact ⟨hstep, (prefix_iff le_rfl).mpr
      ((global_iff (hthree.trans_lt hstep)).mpr (sequence_mem (n + 2)))⟩
  · intro m hm
    change sequence (n + 1) < m ∧ UniquePair (sequence '' Set.Iic (n + 1)) m at hm
    by_contra! hmlt
    have hmem := (global_iff (hthree.trans_lt hm.1)).mp
      ((prefix_iff hmlt.le).mp hm.2)
    obtain ⟨i, rfl⟩ : m ∈ Set.range sequence := by rw [sequence_range]; exact hmem
    have hi : i < n + 2 := sequence_mono.lt_iff_lt.mp hmlt
    have hi' : n + 1 < i := sequence_mono.lt_iff_lt.mp hm.1
    omega

private abbrev Family := ℕ ⊕ (Unit ⊕ (ℕ ⊕ (ℕ × ℕ)))

private def coordinates : Family → ℕ × ℕ
  | .inl b => (1, b)
  | .inr (.inl _) => (0, 1)
  | .inr (.inr (.inl a)) => (a + 2, 1)
  | .inr (.inr (.inr (a, b))) => (2 * a + 3, 2 * b + 3)

private theorem coordinates_injective : Function.Injective coordinates := by
  intro s t h
  have ha := congrArg Prod.fst h
  have hb := congrArg Prod.snd h
  rcases s with a | (⟨⟩ | (a | ⟨a, b⟩)) <;>
    rcases t with c | (⟨⟩ | (c | ⟨c, d⟩)) <;>
    simp_all [coordinates, Prod.mk.injEq]

private def indexed (i : Family) : {m : ℕ // member m} :=
  ⟨encode (coordinates i).1 (coordinates i).2, by
    refine ⟨_, _, ?_, rfl⟩
    rcases i with a | (⟨⟩ | (a | ⟨a, b⟩)) <;> simp [coordinates, good]⟩

private theorem indexed_bijective : Function.Bijective indexed := by
  constructor
  · intro s t h
    apply coordinates_injective
    exact Prod.ext ((encode_injective (congrArg Subtype.val h)).1)
      ((encode_injective (congrArg Subtype.val h)).2)
  · rintro ⟨n, a, b, hg, rfl⟩
    have go (i : Family) (hi : coordinates i = (a, b)) :
        indexed i = ⟨encode a b, ⟨a, b, hg, rfl⟩⟩ := by
      apply Subtype.ext
      change encode (coordinates i).1 (coordinates i).2 = encode a b
      rw [hi]
    by_cases ha : a = 1
    · exact ⟨.inl b, go _ (by simp [coordinates, ha])⟩
    by_cases hb : b = 1
    · by_cases h0 : a = 0
      · exact ⟨.inr (.inl ()), go _ (by simp [coordinates, h0, hb])⟩
      · exact ⟨.inr (.inr (.inl (a - 2))), go _ (by
          simp [coordinates, hb]; omega)⟩
    have ho : a % 2 = 1 ∧ b % 2 = 1 := by unfold good at hg; omega
    exact ⟨.inr (.inr (.inr ((a - 3) / 2, (b - 3) / 2))), go _ (by
      simp [coordinates, Prod.mk.injEq]; omega)⟩

private theorem geometric_progression (x : ℝ) (t u : ℕ) (h₀ : 0 ≤ x)
    (h₁ : x ^ t < 1) : HasSum (fun n : ℕ => x ^ (t * n + u)) (x ^ u * (1 - x ^ t)⁻¹) := by
  have h := (hasSum_geometric_of_lt_one (pow_nonneg h₀ _) h₁).mul_left (x ^ u)
  have hfun : (fun n : ℕ => x ^ (t * n + u)) = (fun n => x ^ u * (x ^ t) ^ n) := by
    funext n
    rw [pow_add, pow_mul, mul_comm]
  rw [hfun]
  exact h

private theorem inv_encode (a b : ℕ) : (encode a b : ℝ)⁻¹ = (1 / 2 : ℝ)^a * (1 / 3 : ℝ)^b := by
  simp [encode, Nat.cast_mul, Nat.cast_pow, one_div, ← inv_pow, mul_comm]

private theorem indexed_sum : HasSum (fun i : Family => ((indexed i).val : ℝ)⁻¹) (181 / 144) := by
  have hleft : HasSum (fun b : ℕ => (encode 1 b : ℝ)⁻¹) (3/4) := by
    have h := (hasSum_geometric_of_lt_one (by norm_num : 0 ≤ (1/3 : ℝ))
      (by norm_num : (1/3 : ℝ) < 1)).mul_left (1/2 : ℝ)
    have hfun : (fun b : ℕ => (encode 1 b : ℝ)⁻¹) = (fun b => (1/2 : ℝ) * (1/3)^b) := by
      funext b
      rw [inv_encode, pow_one]
    rw [hfun]
    rw [show (1/2 : ℝ) * (1 - 1/3)⁻¹ = 3/4 by norm_num] at h
    exact h
  have hseed : HasSum (fun _ : Unit => (encode 0 1 : ℝ)⁻¹) (1/3) := by
    convert (hasSum_fintype (fun _ : Unit => (encode 0 1 : ℝ)⁻¹)) using 1
    norm_num [inv_encode]
  have hright : HasSum (fun a : ℕ => (encode (a + 2) 1 : ℝ)⁻¹) (1/6) := by
    have h := (geometric_progression (1/2 : ℝ) 1 2 (by norm_num)
      (by norm_num)).mul_right (1/3 : ℝ)
    have hfun : (fun a : ℕ => (encode (a + 2) 1 : ℝ)⁻¹) =
        (fun a => (1/2 : ℝ)^(1*a+2) * (1/3)) := by
      funext a
      rw [inv_encode, pow_one, one_mul]
    rw [hfun]
    rw [show (1/2 : ℝ)^2 * (1 - (1/2)^1)⁻¹ * (1/3) = 1/6 by norm_num] at h
    exact h
  have htwo : HasSum (fun a : ℕ => (1/2 : ℝ) ^ (2*a+3)) (1/6) := by
    convert geometric_progression (1/2 : ℝ) 2 3 (by norm_num) (by norm_num) using 1
    norm_num
  have hthree : HasSum (fun b : ℕ => (1/3 : ℝ) ^ (2*b+3)) (1/24) := by
    convert geometric_progression (1/3 : ℝ) 2 3 (by norm_num) (by norm_num) using 1
    norm_num
  have hinterior : HasSum (fun p : ℕ × ℕ =>
      (encode (2*p.1+3) (2*p.2+3) : ℝ)⁻¹) (1/144) := by
    have h := htwo.mul hthree (htwo.summable.mul_of_nonneg hthree.summable
      (fun _ => by positivity) (fun _ => by positivity))
    simp only [inv_encode]
    rw [show (1/6 : ℝ) * (1/24) = 1/144 by norm_num] at h
    exact h
  have hr : HasSum (fun i : ℕ ⊕ (ℕ × ℕ) =>
      ((indexed (.inr (.inr i))).val : ℝ)⁻¹) ((1:ℝ)/6 + 1/144) :=
    HasSum.sum hright hinterior
  have hs : HasSum (fun i : Unit ⊕ (ℕ ⊕ (ℕ × ℕ)) =>
      ((indexed (.inr i)).val : ℝ)⁻¹) ((1:ℝ)/3 + (1/6 + 1/144)) :=
    HasSum.sum hseed hr
  convert (HasSum.sum hleft hs : HasSum (fun i : Family =>
    ((indexed i).val : ℝ)⁻¹) (3/4 + (1/3 + (1/6 + 1/144)))) using 1
  norm_num

private theorem sequence_sum : HasSum (fun n : ℕ => (sequence n : ℝ)⁻¹) (181/144) := by
  let e := Equiv.ofBijective indexed indexed_bijective
  have hm : HasSum (fun m : {m : ℕ // member m} => (m.val : ℝ)⁻¹) (181/144) :=
    e.hasSum_iff.mp indexed_sum
  let e' : ℕ ≃ {m : ℕ // member m} :=
    (@Nat.Subtype.orderIsoOfNat {m : ℕ | member m} member_infinite.to_subtype).toEquiv
  have h := e'.hasSum_iff.mpr hm
  rw [sequence, Nat.nth_eq_orderIsoOfNat member_infinite]
  exact h

theorem finished : type_of% @OMA.S_oeis_a007335.main :=
  ⟨sequence, sequence_greedy, sequence_sum⟩

end A007335Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a007335.main := A007335Proof.finished
