import OMAStatements.S_oeis_a084013
import Mathlib

/-!
# OEIS A084013 : no term is zero

For every `n >= 1` there is an `n`-digit multiple of `n` that is a
decimal palindrome - for `10 | n` the OEIS rule tolerates the
trailing zeros, which is exactly the `if 10 | n` dichotomy of the
statement's `qualifies`.

Proof = the kernel-verified chain from the DemosMathNT project
(section `A084013src`, identical to the sibling port in
`proofs/oeis-a084017.lean`), plus a repunit-scaling section `Join`
for the strict-palindrome clause `~ 10 | n` : the corpus' strict
coverage is completed by repeating a `2 ^ a` / `5 ^ b` palindromic
block `h` times, `h` a repunit order over `10 ^ |w|` found by
pigeonhole on the coprime part `m` - so `c * m | val (copies w h)`,
and two copies around a zero-run hit length `n`.

The bridge is a definitional cast, no re-proof:
`qualifies n x` unfolds to positivity, divisibility, digit-length
and the palindrome clause; `a n != 0` follows since `Nat.find`
of the exhibited witness qualifies, hence is positive.
-/

namespace OMA.A084013Port

section A084013src





theorem ofDigits_replicate_nine (t : ℕ) :
    Nat.ofDigits 10 (List.replicate t 9) = 10 ^ t - 1 := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [List.replicate_succ, Nat.ofDigits_cons, ih, pow_succ]
    have h : 1 ≤ 10 ^ t := Nat.one_le_pow t 10 (by norm_num)
    omega

theorem digits_ten_pow_sub_one (t : ℕ) (_ht : 0 < t) :
    Nat.digits 10 (10 ^ t - 1) = List.replicate t 9 := by
  rw [← ofDigits_replicate_nine t]
  apply Nat.digits_ofDigits 10 (by norm_num) _
  · intro l hl
    have : l = 9 := List.eq_of_mem_replicate hl
    omega
  · intro hne
    have h9 : (List.replicate t 9).getLast hne = 9 := by
      have := List.getLast_mem hne
      exact List.eq_of_mem_replicate this
    rw [h9]; norm_num


theorem dropWhile_self_of_head?_nine {l : List ℕ}
    (h : l.head? = some 9) : l.dropWhile (· = 0) = l := by
  cases l with
  | nil => simp at h
  | cons x xs =>
    simp only [List.head?_cons, Option.some.injEq] at h; subst h
    rw [List.dropWhile_cons_of_neg (by norm_num)]


theorem dropWhile_zero_prefix (z : ℕ) {l : List ℕ}
    (h : l.head? = some 9) :
    (List.replicate z 0 ++ l).dropWhile (· = 0) = l := by
  rw [List.dropWhile_append_of_pos
      (fun a ha => by simp [List.mem_replicate.mp ha])]
  exact dropWhile_self_of_head?_nine h


theorem pal_digits_large (m L t : ℕ) (hdvd : m ∣ 10 ^ t - 1) (ht : 0 < t)
    (hL : 2 * t ≤ L) :
    ∃ P : ℕ, m ∣ P ∧ Nat.digits 10 P =
      List.replicate t 9 ++ List.replicate (L - 2 * t) 0 ++
        List.replicate t 9 := by
  obtain ⟨k, rfl⟩ : ∃ k, L = 2 * t + k := ⟨L - 2 * t, by omega⟩
  have h2tk : 2 * t + k - 2 * t = k := by omega
  set X := 10 ^ t - 1 with hX
  have hXpos : 0 < X := by
    have : 1 < 10 ^ t := one_lt_pow₀ (by norm_num) ht.ne'
    omega
  have hdX : Nat.digits 10 X = List.replicate t 9 := digits_ten_pow_sub_one t ht
  have hP : X * (10 ^ (t + k) + 1) = X + 10 ^ (t + k) * X := by ring
  refine ⟨X * (10 ^ (t + k) + 1), hdvd.mul_right _, ?_⟩
  rw [h2tk]
  have h := Nat.digits_append_zeroes_append_digits (b := 10) (k := k)
      (m := X) (n := X) (by norm_num) hXpos
  rw [hdX, List.length_replicate] at h
  rw [hP, ← h]


theorem dropWhile_self_of_head_ne_zero {l : List ℕ} {x : ℕ}
    (h : l.head? = some x) (hx : x ≠ 0) :
    l.dropWhile (· = 0) = l := by
  cases l with
  | nil => simp at h
  | cons y ys =>
    simp only [List.head?_cons, Option.some.injEq] at h; subst h
    rw [List.dropWhile_cons_of_neg (by simp [hx])]


theorem dropWhile_zero_prefix' (z : ℕ) {l : List ℕ} {x : ℕ}
    (h : l.head? = some x) (hx : x ≠ 0) :
    (List.replicate z 0 ++ l).dropWhile (· = 0) = l := by
  rw [List.dropWhile_append_of_pos
      (fun a ha => by simp [List.mem_replicate.mp ha])]
  exact dropWhile_self_of_head_ne_zero h hx


theorem pal_head?_ne_zero {l : List ℕ} (hp : List.Palindrome l)
    (hgl : l.getLast? ≠ some 0) : l.head? ≠ some 0 := by
  rw [List.Palindrome.iff_reverse_eq] at hp
  have h : l.head? = l.getLast? := by
    conv_lhs => rw [← hp]
    exact List.head?_reverse
  rw [h]; exact hgl


theorem digits_getLast?_ne_zero (P : ℕ) (hP : 0 < P) :
    (Nat.digits 10 P).getLast? ≠ some 0 := by
  have hne : Nat.digits 10 P ≠ [] := Nat.digits_ne_nil_iff_ne_zero.mpr hP.ne'
  have hg := Nat.getLast_digit_ne_zero 10 hP.ne'
  rw [List.getLast?_eq_some_getLast hne]
  simp [hg]


theorem strict_to_relaxed (N : ℕ) (hN : 0 < N)
    (hpal : List.Palindrome (Nat.digits 10 N)) :
    List.Palindrome ((Nat.digits 10 N).dropWhile (· = 0)) := by
  have hgl : (Nat.digits 10 N).getLast? ≠ some 0 :=
    digits_getLast?_ne_zero N hN
  have hh : (Nat.digits 10 N).head? ≠ some 0 := pal_head?_ne_zero hpal hgl
  cases hx : (Nat.digits 10 N).head? with
  | none =>
    exfalso
    rw [List.head?_eq_none_iff] at hx
    exact (Nat.digits_ne_nil_iff_ne_zero.mpr hN.ne') hx
  | some x =>
    have hd : (Nat.digits 10 N).dropWhile (· = 0) = Nat.digits 10 N :=
      dropWhile_self_of_head_ne_zero hx (by
        intro h0; rw [h0] at hx; exact hh hx)
    rwa [hd]

open scoped Pointwise


theorem mem_finset_sum {ι α : Type*} [DecidableEq ι] [DecidableEq α]
    [AddCommMonoid α] {s : Finset ι} {f : ι → Finset α} {x : α} :
    x ∈ s.sum f ↔ ∃ g : ι → α, (∀ i ∈ s, g i ∈ f i) ∧ s.sum g = x := by
  induction s using Finset.induction generalizing x with
  | empty =>
    rw [Finset.sum_empty]
    constructor
    · intro hx
      have hx0 : x = 0 := Finset.mem_singleton.mp hx
      subst hx0
      exact ⟨0, by simp, by simp⟩
    · rintro ⟨g, -, hx⟩
      exact Finset.mem_singleton.mpr hx.symm
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    constructor
    · intro hx
      rw [Finset.mem_add] at hx
      obtain ⟨y, hy, z, hz, rfl⟩ := hx
      obtain ⟨g, hg, hzsum⟩ := ih.mp hz
      subst hzsum
      refine ⟨fun i => if i = a then y else g i, ?_, ?_⟩
      · intro i hi
        rw [Finset.mem_insert] at hi
        rcases hi with rfl | hi
        · simpa using hy
        · have hia : i ≠ a := fun h => ha (h ▸ hi)
          simpa [hia] using hg i hi
      · rw [Finset.sum_insert ha]
        simp only [ite_true]
        congr 1
        apply Finset.sum_congr rfl
        intro i hi
        have hia : i ≠ a := fun h => ha (h ▸ hi)
        simp [hia]
    · rintro ⟨g, hg, rfl⟩
      rw [Finset.sum_insert ha]
      apply Finset.add_mem_add (hg a (Finset.mem_insert_self a s))
      exact ih.mpr ⟨g, fun i hi => hg i (Finset.mem_insert_of_mem hi), rfl⟩


theorem exists_nsmul_eq_of_isUnit {m : ℕ} [NeZero m] {w : ZMod m}
    (hw : IsUnit w) (c : ZMod m) : ∃ k : ℕ, k • w = c := by
  obtain ⟨u, hu⟩ := hw
  refine ⟨(c * (u⁻¹ : (ZMod m)ˣ)).val, ?_⟩
  have hvw : ((u⁻¹ : (ZMod m)ˣ) : ZMod m) * w = 1 := by
    rw [← hu]; exact Units.inv_mul u
  rw [nsmul_eq_mul]
  have hcast : (((c * (u⁻¹ : (ZMod m)ˣ)).val : ℕ) : ZMod m) =
      c * (u⁻¹ : (ZMod m)ˣ) := by
    rw [ZMod.natCast_val]; exact ZMod.cast_id _ _
  rw [hcast, mul_assoc, hvw, mul_one]


theorem eq_univ_of_add_unit_closed {m : ℕ} [NeZero m] {w : ZMod m}
    (hw : IsUnit w) {B : Finset (ZMod m)} (hB : B.Nonempty)
    (hcl : ∀ b ∈ B, b + w ∈ B) : B = Finset.univ := by
  obtain ⟨b₀, hb₀⟩ := hB
  apply Finset.eq_univ_of_forall
  intro c
  obtain ⟨k, hk⟩ := exists_nsmul_eq_of_isUnit hw (c - b₀)
  have hstep : ∀ j : ℕ, b₀ + j • w ∈ B := by
    intro j
    induction j with
    | zero => simpa using hb₀
    | succ j ihj =>
      have h : b₀ + (j + 1) • w = (b₀ + j • w) + w := by
        rw [add_nsmul, one_nsmul]; abel
      rw [h]; exact hcl _ ihj
  have : c = b₀ + k • w := by rw [hk]; abel
  rw [this]; exact hstep k


theorem card_add_pair_unit {m : ℕ} [NeZero m] {w : ZMod m}
    (hw : IsUnit w) {B : Finset (ZMod m)} (hB : B.Nonempty) :
    min m (B.card + 1) ≤ (B + {0, w}).card := by
  have hBw : B + ({0, w} : Finset (ZMod m)) =
      B ∪ (Finset.image (· + w) B) := by
    ext x
    rw [Finset.mem_add, Finset.mem_union]
    constructor
    · rintro ⟨y, hy, z, hz, rfl⟩
      simp only [Finset.mem_insert, Finset.mem_singleton] at hz
      rcases hz with rfl | rfl
      · exact Or.inl (by simpa using hy)
      · exact Or.inr (Finset.mem_image.mpr ⟨y, hy, rfl⟩)
    · rintro (hx | hx)
      · exact ⟨x, hx, 0, by simp, by simp⟩
      · obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
        exact ⟨y, hy, w, by simp, rfl⟩
  rw [hBw]
  by_cases hsub : Finset.image (· + w) B ⊆ B
  · 
    have hcl : ∀ b ∈ B, b + w ∈ B := by
      intro b hb
      exact hsub (Finset.mem_image.mpr ⟨b, hb, rfl⟩)
    have huniv := eq_univ_of_add_unit_closed hw hB hcl
    rw [Finset.union_eq_left.mpr hsub, huniv, Finset.card_univ, ZMod.card]
    exact min_le_left _ _
  · 
    rw [Finset.not_subset] at hsub
    obtain ⟨y, hy, hyB⟩ := hsub
    have hy' : y ∈ B ∪ Finset.image (· + w) B :=
      Finset.mem_union_right _ hy
    have hcard : B.card + 1 ≤ (B ∪ Finset.image (· + w) B).card := by
      have h1 : Finset.card (insert y B) = B.card + 1 :=
        Finset.card_insert_of_notMem hyB
      have h2 : insert y B ⊆ B ∪ Finset.image (· + w) B :=
        Finset.insert_subset hy' (Finset.subset_union_left)
      rw [← h1]; exact Finset.card_le_card h2
    rcases lt_or_ge m (B.card + 1) with h | h
    · 
      exact le_trans (min_le_left _ _) (le_trans (le_of_lt h) hcard)
    · 
      exact le_trans (min_le_right _ _) hcard


theorem add_singleton_zero {m : ℕ} {B : Finset (ZMod m)} :
    B + ({0} : Finset (ZMod m)) = B := by
  ext x
  rw [Finset.mem_add]
  constructor
  · rintro ⟨y, hy, z, hz, rfl⟩
    simp only [Finset.mem_singleton] at hz
    rw [hz]; simpa using hy
  · intro hx
    exact ⟨x, hx, 0, Finset.mem_singleton_self 0, by simp⟩


theorem smul_range_succ {m : ℕ} {w : ZMod m} (r : ℕ) :
    (Finset.range (r + 2)).image (· • w) =
      (Finset.range (r + 1)).image (· • w) + ({0, w} : Finset (ZMod m)) := by
  ext x
  simp only [Finset.mem_image, Finset.mem_range, Finset.mem_add,
    Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨i, hi, rfl⟩
    rcases Nat.eq_zero_or_pos i with hi0 | hi1
    · exact ⟨0, ⟨0, by simp, by simp⟩, 0, Or.inl rfl,
        by simp [hi0]⟩
    · obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hi1.ne'
      refine ⟨j • w, ⟨j, by omega, rfl⟩, w, Or.inr rfl, ?_⟩
      rw [succ_nsmul]
  · rintro ⟨y, ⟨j, hj, rfl⟩, z, hz, rfl⟩
    rcases hz with rfl | rfl
    · exact ⟨j, by omega, by simp⟩
    · exact ⟨j + 1, by omega, by rw [succ_nsmul]⟩


theorem card_add_smul_range {m : ℕ} [NeZero m] {w : ZMod m}
    (hw : IsUnit w) {B : Finset (ZMod m)} (hB : B.Nonempty) (r : ℕ) :
    min m (B.card + r) ≤
      (B + (Finset.range (r + 1)).image (· • w)).card := by
  induction r with
  | zero =>
    have h1 : (Finset.range 1).image (· • w) = ({0} : Finset (ZMod m)) := by
      ext x
      simp only [Finset.mem_image, Finset.mem_range, Finset.mem_singleton]
      constructor
      · rintro ⟨i, hi, rfl⟩
        interval_cases i; simp
      · intro hx
        exact ⟨0, by simp, by simpa using hx.symm⟩
    rw [h1, add_singleton_zero]
    exact min_le_right _ _
  | succ r ih =>
    have hBr : (B + (Finset.range (r + 1)).image (· • w)).Nonempty := by
      obtain ⟨b, hb⟩ := hB
      refine ⟨b + 0 • w, Finset.mem_add.mpr ?_⟩
      exact ⟨b, hb, 0 • w,
        Finset.mem_image.mpr
          ⟨0, Finset.mem_range.mpr (Nat.succ_pos r), rfl⟩, rfl⟩
    rw [smul_range_succ]
    have hassoc : B + ((Finset.range (r + 1)).image (· • w) +
        ({0, w} : Finset (ZMod m))) =
        (B + (Finset.range (r + 1)).image (· • w)) + {0, w} :=
      (add_assoc _ _ _).symm
    rw [hassoc]
    have hstep := card_add_pair_unit hw hBr
    have hmin : min m (B.card + (r + 1)) ≤
        min m ((B + (Finset.range (r + 1)).image (· • w)).card + 1) := by
      by_cases hge : m ≤ (B + (Finset.range (r + 1)).image (· • w)).card + 1
      · rw [min_eq_left hge]; exact min_le_left _ _
      · have hlt : (B + (Finset.range (r + 1)).image (· • w)).card + 1 < m :=
          by omega
        rw [min_eq_right hlt.le]
        rcases lt_or_ge (B.card + r) m with h2 | h2
        · have hBT : B.card + r ≤
              (B + (Finset.range (r + 1)).image (· • w)).card := by
            have h := ih; rwa [min_eq_right h2.le] at h
          rw [min_eq_right (by omega)]
          omega
        · have hBT : m ≤
              (B + (Finset.range (r + 1)).image (· • w)).card := by
            have h := ih; rwa [min_eq_left h2] at h
          omega
    refine le_trans hmin ?_
    exact hstep


theorem card_add_smul_range' {m : ℕ} [NeZero m] {w : ZMod m}
    (hw : IsUnit w) {B : Finset (ZMod m)} (hB : B.Nonempty)
    {r : ℕ} (hr : 1 ≤ r) :
    min m (B.card + r - 1) ≤
      (B + (Finset.range r).image (· • w)).card := by
  have h := card_add_smul_range hw hB (r - 1)
  rw [Nat.sub_add_cancel hr] at h
  rwa [Nat.add_sub_assoc hr]


theorem zero_mem_interval {m : ℕ} (w : ZMod m) :
    (0 : ZMod m) ∈ (Finset.range 10).image (· • w) :=
  Finset.mem_image.mpr ⟨0, Finset.mem_range.mpr (by norm_num), by simp⟩


theorem card_sum_intervals {m : ℕ} [NeZero m] {w : ℕ → ZMod m}
    {U : Finset ℕ} (hw : ∀ i ∈ U, IsUnit (w i)) :
    min m (1 + 9 * U.card) ≤
      (U.sum fun i => (Finset.range 10).image (· • w i)).card := by
  induction U using Finset.induction with
  | empty =>
    rw [Finset.sum_empty]
    have hm1 : 1 ≤ m := Nat.one_le_iff_ne_zero.mpr (NeZero.ne m)
    simp [hm1]
  | insert a U ha ih =>
    set S := U.sum fun i => (Finset.range 10).image (· • w i)
      with hS_def
    have hS : S.Nonempty := by
      refine ⟨0, ?_⟩
      rw [hS_def, mem_finset_sum]
      exact ⟨0, fun i _ => zero_mem_interval _, by simp⟩
    have hstep : min m (S.card + 9) ≤
        (S + (Finset.range 10).image (· • w a)).card := by
      have h := card_add_smul_range'
        (hw a (Finset.mem_insert_self a U)) hS (r := 10) (by norm_num)
      have h9 : S.card + 10 - 1 = S.card + 9 := by omega
      rwa [h9] at h
    have hih : min m (1 + 9 * U.card) ≤ S.card := by
      have h := ih (fun i hi => hw i (Finset.mem_insert_of_mem hi))
      rwa [hS_def]
    rw [Finset.card_insert_of_notMem ha, Finset.sum_insert ha,
      show (Finset.range 10).image (· • w a) + S =
        S + (Finset.range 10).image (· • w a) from add_comm _ _]
    have hmin : min m (1 + 9 * (U.card + 1)) ≤ min m (S.card + 9) := by
      by_cases hge : m ≤ S.card + 9
      · rw [min_eq_left hge]; exact min_le_left _ _
      · have hlt : S.card + 1 ≤ m := by omega
        rcases lt_or_ge (1 + 9 * U.card) m with h2 | h2
        · have hS2 : 1 + 9 * U.card ≤ S.card := by
            rwa [min_eq_right h2.le] at hih
          rw [min_eq_right (by omega)]; omega
        · have hS2 : m ≤ S.card := by
            rwa [min_eq_left h2] at hih
          omega
    exact le_trans hmin hstep

section DeadCount


theorem coprime_10_of_prime_pow {m p k : ℕ} (hp : p.Prime) (hk : 0 < k)
    (hm : m = p ^ k) (h10 : Nat.Coprime m 10) : Nat.Coprime 10 p := by
  have hpm : p ∣ m := by rw [hm]; exact dvd_pow_self p (by omega)
  exact Nat.coprime_comm.mp (h10.coprime_dvd_left hpm)



theorem dead_weight_eq_neg_one {m p k : ℕ} (hp : p.Prime) (hk : 0 < k)
    (hm : m = p ^ k) (h10 : Nat.Coprime m 10)
    {i : ℕ} (hi : i < (m - 1) / 2)
    (hpdvd : p ∣ 10 ^ i + 10 ^ (m - 1 - i)) :
    (10 : ZMod p) ^ (m - 1 - 2 * i) = -1 := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hcop_p : Nat.Coprime 10 p := coprime_10_of_prime_pow hp hk hm h10
  subst hm
  
  have hcast : ((10 ^ i + 10 ^ (p ^ k - 1 - i) : ℕ) : ZMod p) = 0 :=
    (CharP.cast_eq_zero_iff (ZMod p) p _).mpr hpdvd
  
  have hsplit : i + (p ^ k - 1 - 2 * i) = p ^ k - 1 - i := by omega
  have hnat : 10 ^ i * (1 + 10 ^ (p ^ k - 1 - 2 * i)) =
      10 ^ i + 10 ^ (p ^ k - 1 - i) := by
    rw [mul_add, mul_one, ← pow_add, hsplit]
  rw [← hnat] at hcast
  push_cast at hcast
  
  have h10ne : (10 : ZMod p) ≠ 0 := by
    have hpd : ¬ p ∣ 10 :=
      (hp.coprime_iff_not_dvd).mp (Nat.coprime_comm.mp hcop_p)
    exact fun h =>
      hpd ((CharP.cast_eq_zero_iff (ZMod p) p 10).mp (by exact_mod_cast h))
  have h1e : (10 : ZMod p) ^ (p ^ k - 1 - 2 * i) + 1 = 0 := by
    rw [add_comm]
    exact (mul_eq_zero.mp hcast).resolve_left (pow_ne_zero i h10ne)
  exact eq_neg_of_add_eq_zero_left h1e


theorem four_dvd_orderOf {p e : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {u : (ZMod p)ˣ} (he : 2 ∣ e) (hu : u ^ e = -1) : 4 ∣ orderOf u := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hne1 : (-1 : (ZMod p)ˣ) ≠ 1 := by
    intro h
    have h1 : (-1 : ZMod p) = 1 := by simpa using congrArg Units.val h
    have hr2 : ringChar (ZMod p) = 2 := neg_one_eq_one_iff.mp h1
    exact hp2 ((ZMod.ringChar_zmod_n p) ▸ hr2)
  have hpow1 : u ^ (2 * e) = 1 := by rw [pow_mul', hu]; simp
  have h2e : orderOf u ∣ 2 * e := orderOf_dvd_of_pow_eq_one hpow1
  have hne : ¬ orderOf u ∣ e :=
    mt orderOf_dvd_iff_pow_eq_one.mp (fun heq => hne1 ((heq ▸ hu).symm))
  set g := Nat.gcd (orderOf u) e with hg
  have hgpos : 0 < g := Nat.gcd_pos_of_pos_left e (orderOf_pos u)
  have hs : orderOf u = g * (orderOf u / g) := by
    rw [mul_comm]; exact (Nat.div_mul_cancel (Nat.gcd_dvd_left _ _)).symm
  have ht : e = g * (e / g) := by
    rw [mul_comm]; exact (Nat.div_mul_cancel (Nat.gcd_dvd_right _ _)).symm
  have hcop : Nat.Coprime (orderOf u / g) (e / g) :=
    Nat.coprime_div_gcd_div_gcd hgpos
  have hs2 : orderOf u / g ∣ 2 := by
    have h1 : g * (orderOf u / g) ∣ 2 * (g * (e / g)) := by
      rw [← hs, ← ht]; exact h2e
    rcases h1 with ⟨c, hc⟩
    have h2 : orderOf u / g ∣ 2 * (e / g) := by
      refine ⟨c, Nat.eq_of_mul_eq_mul_left hgpos ?_⟩
      calc g * (2 * (e / g)) = 2 * (g * (e / g)) := by ring
        _ = g * (orderOf u / g) * c := hc
        _ = g * ((orderOf u / g) * c) := by ring
    exact hcop.dvd_of_dvd_mul_right h2
  have hs_eq : orderOf u / g = 2 := by
    rcases (Nat.dvd_prime Nat.prime_two).mp hs2 with h1 | h2
    · exfalso
      exact hne ⟨e / g, by rw [hs, h1, mul_one]; exact ht⟩
    · exact h2
  have htodd : Odd (e / g) := Nat.coprime_two_left.mp (hs_eq ▸ hcop)
  have hge : 2 ∣ g := by
    rcases Nat.even_or_odd g with hgE | hgO
    · exact even_iff_two_dvd.mp hgE
    · exfalso
      have hte : Odd e := ht.symm ▸ (hgO.mul htodd)
      exact (Nat.not_even_iff_odd.mpr hte) (even_iff_two_dvd.mpr he)
  obtain ⟨c, hc⟩ := hge
  exact ⟨c, by rw [hs, hs_eq, hc]; ring⟩


theorem dead_count {m p k : ℕ} (hp : p.Prime) (hk : 0 < k)
    (hm : m = p ^ k) (h10 : Nat.Coprime m 10) :
    ((Finset.range ((m - 1) / 2)).filter fun i =>
        p ∣ 10 ^ i + 10 ^ (m - 1 - i)).card
      ≤ (m - 1) / 4 + 1 := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hcop_p : Nat.Coprime 10 p := coprime_10_of_prime_pow hp hk hm h10
  have hmodd : Odd m := Nat.coprime_two_right.mp (h10.coprime_dvd_right ⟨5, rfl⟩)
  have hp2 : p ≠ 2 := by
    intro h2
    have h2m : 2 ∣ m := by rw [hm, h2]; exact dvd_pow_self 2 (by omega)
    exact (Nat.not_even_iff_odd.mpr hmodd) (even_iff_two_dvd.mpr h2m)
  set u : (ZMod p)ˣ := ZMod.unitOfCoprime 10 hcop_p with hu
  set ord := orderOf u with hord
  set dead := (Finset.range ((m - 1) / 2)).filter (fun i =>
    p ∣ 10 ^ i + 10 ^ (m - 1 - i)) with hdead_def
  have hval : ∀ i ∈ dead, u ^ (m - 1 - 2 * i) = -1 := fun i hi => by
    have him := Finset.mem_filter.mp hi
    have h10e := dead_weight_eq_neg_one hp hk hm h10
      (Finset.mem_range.mp him.1) him.2
    rw [← Units.val_eq_neg_one, Units.val_pow_eq_pow_val, hu,
      ZMod.coe_unitOfCoprime]
    exact h10e
  by_cases hde : dead.Nonempty
  · 
    have hdiff : ∀ i₁ ∈ dead, ∀ i₂ ∈ dead, i₁ ≤ i₂ →
        ord ∣ 2 * (i₂ - i₁) := by
      intro i₁ h₁ i₂ h₂ hle
      have hb1 : 2 * i₁ ≤ m - 1 := by
        have := Finset.mem_range.mp (Finset.mem_filter.mp h₁).1; omega
      have hb2 : 2 * i₂ ≤ m - 1 := by
        have := Finset.mem_range.mp (Finset.mem_filter.mp h₂).1; omega
      have hpow : u ^ (m - 1 - 2 * i₁ - (m - 1 - 2 * i₂)) = 1 := by
        rw [pow_sub u (by omega : m - 1 - 2 * i₂ ≤ m - 1 - 2 * i₁),
          hval i₁ h₁, hval i₂ h₂]
        exact mul_inv_cancel (-1)
      have hd : ord ∣ m - 1 - 2 * i₁ - (m - 1 - 2 * i₂) :=
        orderOf_dvd_of_pow_eq_one hpow
      have heq : m - 1 - 2 * i₁ - (m - 1 - 2 * i₂) = 2 * (i₂ - i₁) := by omega
      rwa [heq] at hd
    have halve : ∀ x, ord ∣ 2 * x → ord / 2 ∣ x := by
      intro x ⟨c, hc⟩
      have h2o : 2 ∣ ord := dvd_trans ⟨2, rfl⟩ (by
        obtain ⟨i₀, hi₀⟩ := hde
        have he₀ : 2 ∣ m - 1 - 2 * i₀ := by
          rcases hmodd with ⟨a, ha⟩; exact ⟨a - i₀, by omega⟩
        exact four_dvd_orderOf hp hp2 he₀ (hval i₀ hi₀))
      refine ⟨c, Nat.eq_of_mul_eq_mul_left two_pos ?_⟩
      calc 2 * x = ord * c := hc
        _ = (2 * (ord / 2)) * c := by rw [Nat.mul_div_cancel' h2o]
        _ = 2 * (ord / 2 * c) := by ring
    have h4 : 4 ∣ ord := by
      obtain ⟨i₀, hi₀⟩ := hde
      have he₀ : 2 ∣ m - 1 - 2 * i₀ := by
        rcases hmodd with ⟨a, ha⟩; exact ⟨a - i₀, by omega⟩
      exact four_dvd_orderOf hp hp2 he₀ (hval i₀ hi₀)
    
    have hcong : ∀ {a b : ℕ}, a ∈ dead → b ∈ dead → a ≤ b →
        a / (ord / 2) = b / (ord / 2) → a = b := by
      intro a b ha hb hle hq
      have hd : ord / 2 ∣ b - a := halve _ (hdiff a ha b hb hle)
      have hm1 : a % (ord / 2) = b % (ord / 2) :=
        (Nat.modEq_iff_dvd' hle).mpr hd
      have h1e := Nat.div_add_mod a (ord / 2)
      have h2e := Nat.div_add_mod b (ord / 2)
      rw [hq, hm1] at h1e
      exact h1e.symm.trans h2e
    have hinj : (↑dead : Set ℕ).InjOn (fun i => i / (ord / 2)) := by
      intro i₁ h₁ i₂ h₂ hq
      rcases le_total i₁ i₂ with hle | hle
      · exact hcong (Finset.mem_coe.mp h₁) (Finset.mem_coe.mp h₂) hle hq
      · exact (hcong (Finset.mem_coe.mp h₂) (Finset.mem_coe.mp h₁) hle
          hq.symm).symm
    have hsub : Set.MapsTo (fun i => i / (ord / 2)) ↑dead
        ↑(Finset.range (((m - 1) / 2) / (ord / 2) + 1)) := by
      intro i hi
      have hi2 : i < (m - 1) / 2 :=
        Finset.mem_range.mp (Finset.mem_filter.mp (Finset.mem_coe.mp hi)).1
      have hord2 : 0 < ord / 2 := by
        have : 4 ≤ ord := Nat.le_of_dvd (orderOf_pos u) h4; omega
      have : i / (ord / 2) ≤ ((m - 1) / 2) / (ord / 2) :=
        Nat.div_le_div_right hi2.le
      simpa using Nat.lt_succ_of_le this
    have hcard := Finset.card_le_card_of_injOn _ hsub hinj
    rw [Finset.card_range] at hcard
    
    have hdiv : (m - 1) / 2 / (ord / 2) = (m - 1) / ord := by
      rw [Nat.div_div_eq_div_mul]
      congr 1
      exact Nat.mul_div_cancel' (dvd_trans ⟨2, rfl⟩ h4)
    rw [hdiv] at hcard
    have hle4 : (m - 1) / ord ≤ (m - 1) / 4 :=
      Nat.div_le_div_left (Nat.le_of_dvd (orderOf_pos u) h4) (by norm_num)
    omega
  · rw [Finset.not_nonempty_iff_eq_empty.mp hde, Finset.card_empty]
    exact Nat.zero_le _


section PalDiag


theorem pal_diag_extract {m p k : ℕ} (hp : p.Prime) (hk : 0 < k)
    (hm : m = p ^ k) (h10 : Nat.Coprime m 10) (hm21 : 21 ≤ m) :
    ∃ U : Finset ℕ, ∃ d : ℕ → ℕ,
      (∀ i ∈ U, d i < 10) ∧ U ⊆ Finset.range ((m - 1) / 2) ∧
      (0 : ℕ) ∉ U ∧
      ((U.sum fun i => d i • ((10 ^ i + 10 ^ (m - 1 - i) : ℕ) : ZMod m))
        = -((10 ^ 0 + 10 ^ (m - 1 - 0) : ℕ) : ZMod m)) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hmpos : 0 < m := by omega
  haveI : NeZero m := ⟨hmpos.ne'⟩
  have hcop_p : Nat.Coprime 10 p := coprime_10_of_prime_pow hp hk hm h10
  have hmodd : Odd m := Nat.coprime_two_right.mp (h10.coprime_dvd_right ⟨5, rfl⟩)
  have hp2 : p ≠ 2 := by
    intro h2
    have h2m : 2 ∣ m := by rw [hm, h2]; exact dvd_pow_self 2 (by omega)
    exact (Nat.not_even_iff_odd.mpr hmodd) (even_iff_two_dvd.mpr h2m)
  set j := (m - 1) / 2 with hj
  set w : ℕ → ZMod m := fun i =>
    ((10 ^ i + 10 ^ (m - 1 - i) : ℕ) : ZMod m) with hw
  set dead := (Finset.range j).filter (fun i =>
    p ∣ 10 ^ i + 10 ^ (m - 1 - i)) with hdead_def
  set Ufull := (Finset.range j).filter (fun i =>
    ¬ p ∣ 10 ^ i + 10 ^ (m - 1 - i)) with hU_def
  have hcards : dead.card + Ufull.card = j := by
    rw [hdead_def, hU_def,
      Finset.card_filter_add_card_filter_not (s := Finset.range j)
        (p := fun i => p ∣ 10 ^ i + 10 ^ (m - 1 - i))]
    exact Finset.card_range j
  have hdead_bound : dead.card ≤ (m - 1) / 4 + 1 := by
    rw [hdead_def, hj]
    exact dead_count hp hk hm h10
  
  have hpow : (10 : ZMod p) ^ (m - 1) = 1 := by
    have hpm1 : p - 1 ∣ m - 1 := by
      have hmod : p ≡ 1 [MOD p - 1] :=
        ((Nat.modEq_iff_dvd' hp.one_lt.le).mpr (dvd_refl _)).symm
      have h := hmod.pow k
      rw [← hm, one_pow] at h
      exact (Nat.modEq_iff_dvd' (by omega : 1 ≤ m)).mp h.symm
    rcases hpm1 with ⟨t, ht⟩
    have hfermat : (10 : ZMod p) ^ (p - 1) = 1 := by
      have hmeq : 10 ^ Nat.totient p ≡ 1 [MOD p] :=
        Nat.ModEq.pow_totient hcop_p
      rw [Nat.totient_prime hp] at hmeq
      have hcast : ((10 ^ (p - 1) : ℕ) : ZMod p) = ((1 : ℕ) : ZMod p) :=
        (ZMod.natCast_eq_natCast_iff _ _ _).mpr hmeq
      push_cast at hcast
      exact hcast
    calc (10 : ZMod p) ^ (m - 1) = (10 : ZMod p) ^ ((p - 1) * t) := by
          rw [ht]
      _ = ((10 : ZMod p) ^ (p - 1)) ^ t := pow_mul _ _ _
      _ = 1 := by rw [hfermat, one_pow]
  
  have h0U : (0 : ℕ) ∈ Ufull := by
    rw [hU_def, Finset.mem_filter, Finset.mem_range]
    refine ⟨by omega, ?_⟩
    intro hpd
    have hcast : ((10 ^ 0 + 10 ^ (m - 1 - 0) : ℕ) : ZMod p) = 0 :=
      (CharP.cast_eq_zero_iff (ZMod p) p _).mpr hpd
    push_cast at hcast
    rw [Nat.sub_zero] at hcast
    rw [hpow] at hcast
    
    have h2d : p ∣ 2 := by
      have : ((2 : ℕ) : ZMod p) = 0 := by
        rw [← hcast]; push_cast; ring
      exact (CharP.cast_eq_zero_iff (ZMod p) p _).mp this
    exact hp2 ((Nat.dvd_prime Nat.prime_two).mp h2d |>.resolve_left hp.ne_one)
  
  set U := Ufull.erase 0 with hU'
  have hUcard : U.card = Ufull.card - 1 := Finset.card_erase_of_mem h0U
  have hUnit : ∀ i ∈ U, IsUnit (w i) := by
    intro i hi
    have hif := Finset.mem_filter.mp
      (Finset.mem_of_mem_erase hi)
    have hnp := hif.2
    have hc_p : (10 ^ i + 10 ^ (m - 1 - i)).Coprime p := by
      rw [Nat.coprime_comm, hp.coprime_iff_not_dvd]
      exact hnp
    have hc_m : (10 ^ i + 10 ^ (m - 1 - i)).Coprime (p ^ k) :=
      (Nat.coprime_pow_right_iff hk _ _).mpr hc_p
    rw [ZMod.isUnit_iff_coprime]
    exact hm.symm ▸ hc_m
  
  set S := U.sum fun i => (Finset.range 10).image (· • w i) with hS
  have hgrow : min m (1 + 9 * U.card) ≤ S.card := card_sum_intervals hUnit
  have hcover : 1 + 9 * U.card ≥ m := by
      omega
  have hmin : min m (1 + 9 * U.card) = m := min_eq_left hcover
  have hSm : m ≤ S.card := by
    rw [hmin] at hgrow
    exact hgrow
  have hS_univ : S = Finset.univ := by
    have hcard : S.card = Fintype.card (ZMod m) := by
      have hz : Fintype.card (ZMod m) = m := ZMod.card m
      have hle : S.card ≤ Fintype.card (ZMod m) :=
        Finset.card_le_univ S
      rw [hz] at hle
      omega
    exact Finset.eq_univ_of_card S hcard
  
  have hmem : (-(w 0)) ∈ S := hS_univ ▸ Finset.mem_univ _
  rw [hS] at hmem
  rw [mem_finset_sum] at hmem
  rcases hmem with ⟨g, hgmem, hgsum⟩
  have hd_ex : ∀ i, ∃ d : ℕ, d < 10 ∧
      (i ∈ U → d • w i = g i) := by
    intro i
    by_cases hi : i ∈ U
    · have h := hgmem i hi
      rw [Finset.mem_image] at h
      rcases h with ⟨d0, hd0, hd0eq⟩
      exact ⟨d0, Finset.mem_range.mp hd0, fun _ => hd0eq⟩
    · exact ⟨0, by norm_num, fun h' => absurd h' hi⟩
  choose d hd1 hd2 using hd_ex
  refine ⟨U, d, fun i hi => hd1 i, fun i hi =>
    Finset.mem_of_mem_erase hi |>
      (Finset.mem_filter.mp · |>.1), by
        rw [hU', Finset.mem_erase]; exact fun h => h.1 rfl, ?_⟩
  have hcongr : (U.sum fun i => d i • w i) = U.sum g :=
    Finset.sum_congr rfl (fun i hi => hd2 i hi)
  rw [hcongr]
  exact hgsum

end PalDiag


theorem ofDigits_append' {α : Type*} [Semiring α] (b : α) (l1 l2 : List ℕ) :
    Nat.ofDigits b (l1 ++ l2) =
      Nat.ofDigits b l1 + b ^ l1.length * Nat.ofDigits b l2 := by
  induction l1 with
  | nil =>
    show Nat.ofDigits b l2 =
        Nat.ofDigits b [] + b ^ (0 : ℕ) * Nat.ofDigits b l2
    rw [show Nat.ofDigits b [] = (0 : α) from rfl, pow_zero, one_mul,
      zero_add]
  | cons d t ih =>
    rw [List.cons_append]
    show (d : α) + b * Nat.ofDigits b (t ++ l2) =
      (d : α) + b * Nat.ofDigits b t
        + b ^ (t.length + 1) * Nat.ofDigits b l2
    rw [ih, mul_add, ← mul_assoc, ← pow_succ', ← add_assoc]

theorem ofDigits_singleton' {α : Type*} [Semiring α] (b : α) (d : ℕ) :
    Nat.ofDigits b [d] = (d : α) := by simp [Nat.ofDigits]


theorem ofDigits_zmod_range (m : ℕ) (g : ℕ → ℕ) (j : ℕ) :
    Nat.ofDigits (10 : ZMod m) ((List.range j).map g) =
      ∑ i ∈ Finset.range j, (g i : ZMod m) * (10 : ZMod m) ^ i := by
  induction j with
  | zero => simp [Nat.ofDigits]
  | succ n ih =>
    rw [List.range_succ, List.map_append, List.map_singleton,
      ofDigits_append', ofDigits_singleton', List.length_map,
      List.length_range, Finset.sum_range_succ, ih]
    ring


theorem ofDigits_zmod_rev (m : ℕ) (g : ℕ → ℕ) (j : ℕ) :
    Nat.ofDigits (10 : ZMod m) ((List.range j).map g).reverse =
      ∑ i ∈ Finset.range j, (g i : ZMod m) * (10 : ZMod m) ^ (j - 1 - i) := by
  have hrw : ((List.range j).map g).reverse =
      (List.range j).map (fun i => g (j - 1 - i)) := by
    apply List.ext_getElem (by simp)
    intro i h1 h2
    simp only [List.getElem_reverse, List.length_map, List.length_range,
      List.getElem_map, List.getElem_range]
  rw [hrw, ofDigits_zmod_range m (fun i => g (j - 1 - i)) j]
  have hr : ∑ i ∈ Finset.range j,
      (g (j - 1 - i) : ZMod m) * (10 : ZMod m) ^ i =
      ∑ i ∈ Finset.range j,
        (g i : ZMod m) * (10 : ZMod m) ^ (j - 1 - i) := by
    rw [← Finset.sum_range_reflect]
    refine Finset.sum_congr rfl (fun i hi => ?_)
    rw [Finset.mem_range] at hi
    rw [show j - 1 - (j - 1 - i) = i by omega]
  exact hr


theorem pal_diag {m p k : ℕ} (hp : p.Prime) (hk : 0 < k)
    (hm : m = p ^ k) (h10 : Nat.Coprime m 10) (hm21 : 21 ≤ m) :
    ∃ P : ℕ, m ∣ P ∧ (Nat.digits 10 P).length = m ∧
      List.Palindrome (Nat.digits 10 P) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hmodd : Odd m := Nat.coprime_two_right.mp (h10.coprime_dvd_right ⟨5, rfl⟩)
  obtain ⟨U, d, hd_lt, hUsub, h0U, hsum⟩ :=
    pal_diag_extract hp hk hm h10 hm21
  set j := (m - 1) / 2 with hj
  set g : ℕ → ℕ := fun i =>
    if i = 0 then 1 else if i ∈ U then d i else 0 with hg
  set Llo := (List.range j).map g with hLlo
  set L := Llo ++ [0] ++ Llo.reverse with hL
  have hg_lt : ∀ i, g i < 10 := by
    intro i
    by_cases h0 : i = 0
    · subst h0; simp [hg]
    · by_cases hiU : i ∈ U
      · have hgi : g i = d i := by simp [hg, h0, hiU]
        rw [hgi]; exact hd_lt i hiU
      · have hgi : g i = 0 := by simp [hg, h0, hiU]
        rw [hgi]; norm_num
  have hLlen : L.length = m := by
    rw [hL, List.length_append, List.length_append, List.length_singleton,
      List.length_reverse, hLlo, List.length_map, List.length_range]
    rcases hmodd with ⟨a, ha⟩; omega
  have hLlo_mem : ∀ x ∈ Llo, x < 10 := by
    intro x hx
    have hx2 : x ∈ (List.range j).map g := hx
    obtain ⟨i, -, rfl⟩ := List.mem_map.mp hx2
    exact hg_lt i
  have hLlt : ∀ l ∈ L, l < 10 := by
    intro l hl
    have hl' : l ∈ (Llo ++ [0]) ++ Llo.reverse := hL ▸ hl
    rcases List.mem_append.mp hl' with hl | hl
    · rcases List.mem_append.mp hl with hl | hl
      · exact hLlo_mem l hl
      · have h0 : l = 0 := List.mem_singleton.mp hl
        subst h0; norm_num
    · exact hLlo_mem l (List.mem_reverse.mp hl)
  have hLlast : ∀ h : L ≠ [], L.getLast h ≠ 0 := by
    intro h
    show (Llo ++ [0] ++ Llo.reverse).getLast h ≠ 0
    have hrev_ne : Llo.reverse ≠ [] := by
      intro hcon
      have h0 : (Llo.reverse).length = 0 :=
        List.length_eq_zero_iff.mpr hcon
      rw [List.length_reverse, hLlo, List.length_map,
        List.length_range] at h0
      rcases hmodd with ⟨a, ha⟩; omega
    rw [List.getLast_append_of_right_ne_nil _ _ hrev_ne,
      List.getLast_reverse, List.head_eq_getElem]
    have hjpos : 0 < j := by rcases hmodd with ⟨a, ha⟩; omega
    show ((List.range j).map g)[0]'(
        by rw [List.length_map, List.length_range]; exact hjpos) ≠ 0
    rw [List.getElem_map, List.getElem_range]
    simp [hg]
  set P := Nat.ofDigits 10 L with hP
  have hdig : Nat.digits 10 P = L :=
    Nat.digits_ofDigits 10 (by norm_num) L hLlt hLlast
  refine ⟨P, ?_, by rw [hdig, hLlen], ?_⟩
  · have hPdec : Nat.ofDigits 10 L =
        Nat.ofDigits 10 Llo +
          10 ^ (j + 1) * Nat.ofDigits 10 Llo.reverse := by
      rw [hL, Nat.ofDigits_append, Nat.ofDigits_append_zero]
      have hlen' : (Llo ++ [0]).length = j + 1 := by
        rw [List.length_append, hLlo, List.length_map, List.length_range,
          List.length_singleton]
      rw [hlen']
    have hPz : ((Nat.ofDigits 10 L : ℕ) : ZMod m) = 0 := by
      rw [hPdec, hLlo]
      push_cast
      rw [ofDigits_zmod_range m g j, ofDigits_zmod_rev m g j]
      have hjoin : (∑ i ∈ Finset.range j, (g i : ZMod m) * (10 : ZMod m)^i)
          + (10 : ZMod m)^(j+1) *
            (∑ i ∈ Finset.range j, (g i : ZMod m) * (10 : ZMod m)^(j-1-i))
          = ∑ i ∈ Finset.range j,
              (g i : ZMod m) * ((10 : ZMod m)^i + (10 : ZMod m)^(m-1-i)) := by
        rw [Finset.mul_sum, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl (fun i hi => ?_)
        rw [Finset.mem_range] at hi
        have hexp : j + 1 + (j - 1 - i) = m - 1 - i := by
          rcases hmodd with ⟨a, ha⟩; omega
        calc (g i : ZMod m) * (10 : ZMod m) ^ i
            + (10 : ZMod m) ^ (j + 1)
              * ((g i : ZMod m) * (10 : ZMod m) ^ (j - 1 - i))
            = (g i : ZMod m) * (10 : ZMod m) ^ i
              + (g i : ZMod m)
                * (10 : ZMod m) ^ (j + 1 + (j - 1 - i)) := by
              rw [pow_add]; ring
          _ = (g i : ZMod m)
              * ((10 : ZMod m) ^ i + (10 : ZMod m) ^ (m - 1 - i)) := by
              rw [hexp, ← mul_add]
      rw [hjoin]
      have hsplit : ∑ i ∈ Finset.range j,
          (g i : ZMod m) * ((10 : ZMod m)^i + (10 : ZMod m)^(m-1-i))
          = ∑ i ∈ (insert 0 U : Finset ℕ),
              (g i : ZMod m) * ((10 : ZMod m)^i + (10 : ZMod m)^(m-1-i)) := by
        symm
        apply Finset.sum_subset
        · apply Finset.insert_subset
          · rw [Finset.mem_range]
            rcases hmodd with ⟨a, ha⟩; omega
          · intro i hi
            exact hUsub hi
        · intro i _ hi
          have hne0 : i ≠ 0 := by
            intro h0; subst h0; exact hi (Finset.mem_insert_self 0 U)
          have hniU : i ∉ U := fun h' => hi (Finset.mem_insert_of_mem h')
          have hgi : g i = 0 := by simp [hg, hne0, hniU]
          rw [hgi]; simp
      rw [hsplit, Finset.sum_insert h0U]
      have hg0 : (g 0 : ZMod m) = 1 := by simp [hg]
      rw [hg0, one_mul]
      have hcongr : ∑ i ∈ U,
          (g i : ZMod m) * ((10 : ZMod m)^i + (10 : ZMod m)^(m-1-i))
          = U.sum fun i => d i • ((10 ^ i + 10 ^ (m - 1 - i) : ℕ) : ZMod m) := by
        refine Finset.sum_congr rfl (fun i hi => ?_)
        have hne : i ≠ 0 := fun h0 => h0U (h0 ▸ hi)
        have hgi : g i = d i := by simp [hg, hne, hi]
        rw [hgi, nsmul_eq_mul]
        push_cast
        ring
      rw [hcongr, hsum]
      push_cast
      ring
    haveI : NeZero m := ⟨by omega⟩
    exact (CharP.cast_eq_zero_iff (ZMod m) m _).mp hPz
  · rw [hdig, hL, List.Palindrome.iff_reverse_eq, List.reverse_append,
      List.reverse_append, List.reverse_reverse, List.reverse_singleton,
      List.append_assoc]


theorem exists_coprime_split {m : ℕ} (h10 : Nat.Coprime m 10)
    (hpp : ¬ IsPrimePow m) (hm : 2 ≤ m) :
    ∃ u v : ℕ, 3 ≤ u ∧ 3 ≤ v ∧ Nat.Coprime u v ∧ u * v = m := by
  have hn0 : m ≠ 0 := by omega
  have hnt : m.primeFactors.Nontrivial :=
    (Nat.not_isPrimePow_iff_nontrivial_of_two_le hm).mp hpp
  obtain ⟨p, hpm, q, hqm, hpq⟩ := hnt
  simp only [Finset.mem_coe, Nat.mem_primeFactors] at hpm hqm
  obtain ⟨hpp', hpd, -⟩ := hpm
  obtain ⟨hpq', hqd, -⟩ := hqm
  haveI : Fact p.Prime := ⟨hpp'⟩
  haveI : Fact q.Prime := ⟨hpq'⟩
  have hc10m : Nat.Coprime 10 m := h10.symm
  have hp_ne2 : p ≠ 2 := by
    intro h; subst h
    have h210 : (2 : ℕ) ∣ 10 := by norm_num
    have hc2 : Nat.Coprime m 2 :=
      (Nat.Coprime.coprime_dvd_left h210 hc10m).symm
    have hg : (2 : ℕ) ∣ Nat.gcd m 2 := Nat.dvd_gcd hpd (dvd_refl 2)
    have hc2' : Nat.gcd m 2 = 1 := hc2
    rw [hc2'] at hg; norm_num at hg
  have hq_ne2 : q ≠ 2 := by
    intro h; subst h
    have h210 : (2 : ℕ) ∣ 10 := by norm_num
    have hc2 : Nat.Coprime m 2 :=
      (Nat.Coprime.coprime_dvd_left h210 hc10m).symm
    have hg : (2 : ℕ) ∣ Nat.gcd m 2 := Nat.dvd_gcd hqd (dvd_refl 2)
    have hc2' : Nat.gcd m 2 = 1 := hc2
    rw [hc2'] at hg; norm_num at hg
  set a := padicValNat p m with ha_def
  set u := p ^ a with hu_def
  set v := m.divMaxPow p with hv_def
  have huv : v * u = m := Nat.divMaxPow_mul_pow_padicValNat p m
  have ha : 1 ≤ a := one_le_padicValNat_of_dvd hn0 hpd
  have hu3 : 3 ≤ u := by
    calc u = p ^ a := rfl
      _ ≥ p ^ 1 := pow_le_pow_right₀ (by have := hpp'.two_le; omega) ha
      _ = p := pow_one p
      _ ≥ 3 := by have := hpp'.two_le; omega
  have hqu : ¬ q ∣ u := by
    intro h
    have hqp : q ∣ p := hpq'.dvd_of_dvd_pow h
    have : q = p := (Nat.prime_dvd_prime_iff_eq hpq' hpp').mp hqp
    exact hpq this.symm
  have hqdvd : q ∣ v := by
    have h : q ∣ v * u := by rwa [huv]
    exact ((Nat.Prime.dvd_mul hpq').mp h).resolve_right hqu
  have hvpos : 0 < v := by
    rcases Nat.eq_zero_or_pos v with h | h
    · rw [h, zero_mul] at huv; exact absurd huv.symm hn0
    · exact h
  have hv3 : 3 ≤ v := le_trans
      (by have := hpq'.two_le; omega : 3 ≤ q) (Nat.le_of_dvd hvpos hqdvd)
  have hpcv : Nat.Coprime p v :=
    (hpp'.coprime_iff_not_dvd).mpr (Nat.not_dvd_divMaxPow hpp'.one_lt hn0)
  exact ⟨u, v, hu3, hv3, Nat.Coprime.pow_left a hpcv, by rw [mul_comm]; exact huv⟩


theorem totient_half_dvd_sub_one {m : ℕ} (h10 : Nat.Coprime m 10)
    (hpp : ¬ IsPrimePow m) (hm : 2 ≤ m) :
    m ∣ 10 ^ (m.totient / 2) - 1 := by
  obtain ⟨u, v, hu3, hv3, hcop, huv⟩ := exists_coprime_split h10 hpp hm
  have hudm : u ∣ m := ⟨v, huv.symm⟩
  have hvdm : v ∣ m := ⟨u, by rw [mul_comm]; exact huv.symm⟩
  have hc10u : Nat.Coprime 10 u :=
    (Nat.Coprime.coprime_dvd_left hudm h10).symm
  have hc10v : Nat.Coprime 10 v :=
    (Nat.Coprime.coprime_dvd_left hvdm h10).symm
  have hφm : m.totient = u.totient * v.totient := by
    rw [← huv]; exact Nat.totient_mul hcop
  obtain ⟨cv, hcv⟩ := Nat.totient_even (by omega : 2 < v)
  obtain ⟨cu, hcu⟩ := Nat.totient_even (by omega : 2 < u)
  set φu := u.totient
  set φv := v.totient
  have hφhalf : m.totient / 2 = φu * cv := by
    rw [hφm, hcv]
    have h1 : φu * (cv + cv) / 2 = φu * cv := by
      rw [show cv + cv = cv * 2 from by ring, ← mul_assoc,
        Nat.mul_div_cancel _ (by norm_num : 0 < 2)]
    exact h1
  have hφhalf' : m.totient / 2 = φv * cu := by
    rw [hφm, hcv, hcu]
    have h1 : (cu + cu) * (cv + cv) / 2 = (cv + cv) * cu := by
      have : (cu + cu) * (cv + cv) = ((cv + cv) * cu) * 2 := by ring
      rw [this, Nat.mul_div_cancel _ (by norm_num : 0 < 2)]
    exact h1
  have hMu : (10 : ℕ) ^ (m.totient / 2) ≡ 1 [MOD u] := by
    have h1 : (10 : ℕ) ^ φu ≡ 1 [MOD u] := Nat.ModEq.pow_totient hc10u
    rw [hφhalf, pow_mul]
    have := h1.pow cv
    simpa using this
  have hMv : (10 : ℕ) ^ (m.totient / 2) ≡ 1 [MOD v] := by
    have h1 : (10 : ℕ) ^ φv ≡ 1 [MOD v] := Nat.ModEq.pow_totient hc10v
    rw [hφhalf', pow_mul]
    have := h1.pow cu
    simpa using this
  have hle : 1 ≤ 10 ^ (m.totient / 2) := Nat.one_le_pow _ _ (by norm_num)
  have hdu : u ∣ 10 ^ (m.totient / 2) - 1 := (Nat.modEq_iff_dvd' hle).mp hMu.symm
  have hdv : v ∣ 10 ^ (m.totient / 2) - 1 := (Nat.modEq_iff_dvd' hle).mp hMv.symm
  have h := hcop.mul_dvd_of_dvd_of_dvd hdu hdv
  rwa [huv] at h



theorem wit013_spec (n : ℕ) (h1 : 1 ≤ n) (h23 : n ≤ 23)
    (h10 : ¬ 10 ∣ n) :
    ∃ N : ℕ, 0 < N ∧ n ∣ N ∧ (Nat.digits 10 N).length = n ∧
      List.Palindrome (Nat.digits 10 N) := by
  interval_cases n
  · exact ⟨1, by norm_num, by norm_num, by decide,
      List.Palindrome.iff_reverse_eq.mpr (by decide)⟩
  · exact ⟨22, by norm_num, by norm_num, by decide,
      List.Palindrome.iff_reverse_eq.mpr (by decide)⟩
  · exact ⟨111, by norm_num, by norm_num, by decide,
      List.Palindrome.iff_reverse_eq.mpr (by decide)⟩
  · exact ⟨2112, by norm_num, by norm_num, by decide,
      List.Palindrome.iff_reverse_eq.mpr (by decide)⟩
  · exact ⟨50005, by norm_num, by norm_num, by decide,
      List.Palindrome.iff_reverse_eq.mpr (by decide)⟩
  · exact ⟨201102, by norm_num, by norm_num, by decide,
      List.Palindrome.iff_reverse_eq.mpr (by decide)⟩
  · exact ⟨1002001, by norm_num, by norm_num, by decide,
      List.Palindrome.iff_reverse_eq.mpr (by decide)⟩
  · exact ⟨21100112, by norm_num, by norm_num, by decide,
      List.Palindrome.iff_reverse_eq.mpr (by decide)⟩
  · exact ⟨100070001, by norm_num, by norm_num, by decide,
      List.Palindrome.iff_reverse_eq.mpr (by decide)⟩
  · exact absurd (by decide : 10 ∣ 10) h10
  · exact ⟨10000200001, by norm_num, by norm_num, by decide,
      List.Palindrome.iff_reverse_eq.mpr (by decide)⟩
  · exact ⟨210000000012, by norm_num, by norm_num, by decide,
      List.Palindrome.iff_reverse_eq.mpr (by decide)⟩
  · exact ⟨1000029200001, by norm_num, by norm_num, by decide,
      List.Palindrome.iff_reverse_eq.mpr (by decide)⟩
  · exact ⟨20000055000002, by norm_num, by norm_num, by decide,
      List.Palindrome.iff_reverse_eq.mpr (by decide)⟩
  · exact ⟨500000020000005, by norm_num, by norm_num, by decide,
      List.Palindrome.iff_reverse_eq.mpr (by decide)⟩
  · exact ⟨2110000000000112, by norm_num, by norm_num, by decide,
      List.Palindrome.iff_reverse_eq.mpr (by decide)⟩
  · exact ⟨10000000200000001, by norm_num, by norm_num, by decide,
      List.Palindrome.iff_reverse_eq.mpr (by decide)⟩
  · exact ⟨200000007700000002, by norm_num, by norm_num, by decide,
      List.Palindrome.iff_reverse_eq.mpr (by decide)⟩
  · exact ⟨1000000002000000001, by norm_num, by norm_num, by decide,
      List.Palindrome.iff_reverse_eq.mpr (by decide)⟩
  · exact absurd (by decide : 10 ∣ 20) h10
  · exact ⟨100000000010000000001, by norm_num, by norm_num, by decide,
      List.Palindrome.iff_reverse_eq.mpr (by decide)⟩
  · exact ⟨2000000000000000000002, by norm_num, by norm_num, by decide,
      List.Palindrome.iff_reverse_eq.mpr (by decide)⟩
  · exact ⟨10000000000200000000001, by norm_num, by norm_num, by decide,
      List.Palindrome.iff_reverse_eq.mpr (by decide)⟩


theorem A084013_relaxed (n : ℕ) (hn : 1 ≤ n) (h10 : 10 ∣ n) :
    ∃ N : ℕ, 0 < N ∧ n ∣ N ∧ (Nat.digits 10 N).length = n ∧
      List.Palindrome ((Nat.digits 10 N).dropWhile (· = 0)) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  set a := padicValNat 2 n
  set q1 := Nat.divMaxPow n 2
  set b := padicValNat 5 q1
  set m := Nat.divMaxPow q1 5
  have hn0 : n ≠ 0 := by omega
  have hq1 : q1 * 2 ^ a = n := Nat.divMaxPow_mul_pow_padicValNat 2 n
  have hmq : m * 5 ^ b = q1 := Nat.divMaxPow_mul_pow_padicValNat 5 q1
  have hq10 : q1 ≠ 0 := by
    intro h; rw [h, zero_mul] at hq1; exact hn0 hq1.symm
  have hdecomp : n = 2 ^ a * 5 ^ b * m := by
    rw [← hmq] at hq1; rw [← hq1]; ring
  have h2q1 : ¬ 2 ∣ q1 := Nat.not_dvd_divMaxPow (by norm_num) hn0
  have h5m : ¬ 5 ∣ m := Nat.not_dvd_divMaxPow (by norm_num) hq10
  have hmq1 : m ∣ q1 := ⟨5 ^ b, hmq.symm⟩
  have h2m : ¬ 2 ∣ m := fun h => h2q1 (h.trans hmq1)
  have h2 : Nat.Coprime m 2 :=
    ((Nat.prime_two.coprime_iff_not_dvd).mpr h2m).symm
  have h5 : Nat.Coprime m 5 :=
    ((Nat.prime_five.coprime_iff_not_dvd).mpr h5m).symm
  have hc10 : Nat.Coprime m 10 := by
    have hc : Nat.Coprime m (2 * 5) := Nat.Coprime.mul_right h2 h5
    rwa [show (2 : ℕ) * 5 = 10 from rfl] at hc
  have hm0 : m ≠ 0 := by
    intro hmz; rw [hmz, zero_mul] at hmq; exact hq10 hmq.symm
  have hmpos : 0 < m := Nat.pos_of_ne_zero hm0
  have h2n : 2 ∣ n := (show 2 ∣ 10 from by norm_num).trans h10
  have h5n : 5 ∣ n := (show 5 ∣ 10 from by norm_num).trans h10
  have ha1 : 1 ≤ a := one_le_padicValNat_of_dvd hn0 h2n
  have hcop52 : Nat.Coprime 5 (2 ^ a) :=
    Nat.Coprime.pow_right a (by norm_num : Nat.Coprime 5 2)
  have h5q1 : 5 ∣ q1 := by
    have h5nq : 5 ∣ q1 * 2 ^ a := by rwa [hq1]
    exact hcop52.dvd_of_dvd_mul_right h5nq
  have hb1 : 1 ≤ b := one_le_padicValNat_of_dvd hq10 h5q1
  have hpa : a + 1 ≤ 2 ^ a := a.lt_two_pow_self
  have hpb : b + 1 ≤ 2 ^ b := b.lt_two_pow_self
  have h2a5 : 2 ^ a * 5 ≤ n := by
    have h1 : (5 : ℕ) ≤ 5 ^ b := by
      rw [← pow_one 5]; exact pow_le_pow_right₀ (by norm_num) hb1
    have h2 : 5 ≤ 5 ^ b * m := le_trans h1 (Nat.le_mul_of_pos_right _ hmpos)
    calc 2 ^ a * 5 ≤ 2 ^ a * (5 ^ b * m) := Nat.mul_le_mul_left _ h2
      _ = n := by rw [hdecomp]; ring
  have h5b2 : 5 ^ b * 2 ≤ n := by
    have h1 : (2 : ℕ) ≤ 2 ^ a := by
      rw [← pow_one 2]; exact pow_le_pow_right₀ (by norm_num) ha1
    have h2 : 2 ≤ 2 ^ a * m := le_trans h1 (Nat.le_mul_of_pos_right _ hmpos)
    calc 5 ^ b * 2 ≤ 5 ^ b * (2 ^ a * m) := Nat.mul_le_mul_left _ h2
      _ = n := by rw [hdecomp]; ring
  have h10m : 10 * m ≤ n := by
    calc 10 * m = (2 * 5) * m := by ring
      _ ≤ (2 ^ a * 5 ^ b) * m :=
          Nat.mul_le_mul_right _
            (Nat.mul_le_mul (pow_le_pow_right₀ (by norm_num : (1:ℕ) ≤ 2) ha1)
              (pow_le_pow_right₀ (by norm_num : (1:ℕ) ≤ 5) hb1))
      _ = n := by rw [hdecomp]
  have htpos : 0 < m.totient := Nat.totient_pos.mpr hmpos
  have hT : m ∣ 10 ^ m.totient - 1 := by
    have h1 : 1 ≤ 10 ^ m.totient := Nat.one_le_pow _ _ (by norm_num)
    exact (Nat.modEq_iff_dvd' h1).mp (Nat.ModEq.pow_totient hc10.symm).symm
  have htot : m.totient ≤ m := Nat.totient_le m
  have hbound : 2 * m.totient ≤ n - max a b := by
    have ha : (a + 1) * 5 ≤ n := le_trans (Nat.mul_le_mul_right _ hpa) h2a5
    have hb : (b + 1) * 2 ≤ n := le_trans
      (Nat.mul_le_mul_right _
        (le_trans hpb (Nat.pow_le_pow_left (by norm_num) b))) h5b2
    have hm10 : m * 10 ≤ n := by rw [mul_comm]; exact h10m
    omega
  obtain ⟨P, hmP, hdigP⟩ :=
    pal_digits_large m (n - max a b) m.totient hT htpos hbound
  have hPpos : 0 < P := by
    rcases Nat.eq_zero_or_pos P with h | h
    · rw [h] at hdigP; simp at hdigP; omega
    · exact h
  have hhead : (Nat.digits 10 P).head? = some 9 := by
    rw [hdigP]
    rw [show List.replicate m.totient 9 = 9 :: List.replicate (m.totient - 1) 9
        from by
          nth_rewrite 1 [(Nat.sub_add_cancel htpos).symm]
          rw [List.replicate_succ],
        List.cons_append]
    simp
  refine ⟨P * 10 ^ max a b, by positivity, ?_, ?_, ?_⟩
  · rw [hdecomp]
    have h2a : 2 ^ a ∣ 10 ^ max a b := by
      rw [show (10 : ℕ) = 2 * 5 from rfl, Nat.mul_pow]
      exact dvd_mul_of_dvd_left (pow_dvd_pow 2 (le_max_left a b)) _
    have h5b : 5 ^ b ∣ 10 ^ max a b := by
      rw [show (10 : ℕ) = 2 * 5 from rfl, Nat.mul_pow]
      exact dvd_mul_of_dvd_right (pow_dvd_pow 5 (le_max_right a b)) _
    have hc25 : Nat.Coprime (2 ^ a) (5 ^ b) :=
      Nat.Coprime.pow_right b (Nat.Coprime.pow_left a (by norm_num))
    have h25 : 2 ^ a * 5 ^ b ∣ P * 10 ^ max a b :=
      hc25.mul_dvd_of_dvd_of_dvd (dvd_mul_of_dvd_right h2a P)
        (dvd_mul_of_dvd_right h5b P)
    have hcR : Nat.Coprime (2 ^ a * 5 ^ b) m :=
      (Nat.Coprime.mul_right (Nat.Coprime.pow_right a h2)
        (Nat.Coprime.pow_right b h5)).symm
    exact hcR.mul_dvd_of_dvd_of_dvd h25 (dvd_mul_of_dvd_left hmP _)
  · rw [mul_comm, Nat.digits_base_pow_mul (by norm_num) hPpos,
        List.length_append, List.length_replicate, hdigP,
        List.length_append, List.length_append, List.length_replicate,
        List.length_replicate]
    omega
  · have hdN : Nat.digits 10 (P * 10 ^ max a b) =
        List.replicate (max a b) 0 ++ Nat.digits 10 P := by
      rw [mul_comm]; exact Nat.digits_base_pow_mul (by norm_num) hPpos
    rw [hdN, dropWhile_zero_prefix _ hhead, hdigP,
        List.Palindrome.iff_reverse_eq, List.reverse_append,
        List.reverse_append, List.reverse_replicate, List.reverse_replicate,
        List.append_assoc]


theorem A084013_strict (n : ℕ) (hn : 1 ≤ n) (h10 : ¬ 10 ∣ n) :
    ∃ N : ℕ, 0 < N ∧ n ∣ N ∧ (Nat.digits 10 N).length = n ∧
      List.Palindrome ((Nat.digits 10 N).dropWhile (· = 0)) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  set a := padicValNat 2 n
  set q1 := Nat.divMaxPow n 2
  set b := padicValNat 5 q1
  set m := Nat.divMaxPow q1 5
  have hn0 : n ≠ 0 := by omega
  have hq1 : q1 * 2 ^ a = n := Nat.divMaxPow_mul_pow_padicValNat 2 n
  have hmq : m * 5 ^ b = q1 := Nat.divMaxPow_mul_pow_padicValNat 5 q1
  have hq10 : q1 ≠ 0 := by
    intro h; rw [h, zero_mul] at hq1; exact hn0 hq1.symm
  have hdecomp : n = 2 ^ a * 5 ^ b * m := by
    rw [← hmq] at hq1; rw [← hq1]; ring
  have h2q1 : ¬ 2 ∣ q1 := Nat.not_dvd_divMaxPow (by norm_num) hn0
  have h5m : ¬ 5 ∣ m := Nat.not_dvd_divMaxPow (by norm_num) hq10
  have hmq1 : m ∣ q1 := ⟨5 ^ b, hmq.symm⟩
  have hq1n : q1 ∣ n := ⟨2 ^ a, hq1.symm⟩
  have h2m : ¬ 2 ∣ m := fun h => h2q1 (h.trans hmq1)
  have h2 : Nat.Coprime m 2 :=
    ((Nat.prime_two.coprime_iff_not_dvd).mpr h2m).symm
  have h5 : Nat.Coprime m 5 :=
    ((Nat.prime_five.coprime_iff_not_dvd).mpr h5m).symm
  have hc10 : Nat.Coprime m 10 := by
    have hc : Nat.Coprime m (2 * 5) := Nat.Coprime.mul_right h2 h5
    rwa [show (2 : ℕ) * 5 = 10 from rfl] at hc
  have hm0 : m ≠ 0 := by
    intro hmz; rw [hmz, zero_mul] at hmq; exact hq10 hmq.symm
  have hmpos : 0 < m := Nat.pos_of_ne_zero hm0
  have h2or5 : ¬ 2 ∣ n ∨ ¬ 5 ∣ n := by
    by_contra h
    push_neg at h
    have hcop : Nat.Coprime 2 5 := by decide
    have hd : (2 : ℕ) * 5 ∣ n :=
      Nat.Coprime.mul_dvd_of_dvd_of_dvd hcop h.1 h.2
    rw [show (2 : ℕ) * 5 = 10 from rfl] at hd
    exact h10 hd
  have hab : max a b = a + b := by
    rcases h2or5 with h | h
    · have ha0 : a = 0 := padicValNat.eq_zero_of_not_dvd h
      simp [ha0]
    · have hb0 : b = 0 :=
        padicValNat.eq_zero_of_not_dvd (fun hd => h (hd.trans hq1n))
      simp [hb0]
  set z := a + b with hz
  set L := n - z with hL
  have h5b2b : 2 ^ b ≤ 5 ^ b := Nat.pow_le_pow_left (by norm_num) b
  have hpow : 2 ^ (a + b) ≤ n := by
    calc 2 ^ (a + b) = 2 ^ a * 2 ^ b := by rw [pow_add]
      _ ≤ 2 ^ a * 5 ^ b := Nat.mul_le_mul_left _ h5b2b
      _ ≤ 2 ^ a * (5 ^ b * m) :=
          Nat.mul_le_mul_left _ (Nat.le_mul_of_pos_right _ hmpos)
      _ = n := by rw [hdecomp]; ring
  have hzpos : a + b < 2 ^ (a + b) := (a + b).lt_two_pow_self
  have hzn : z ≤ n := by
    have : a + b ≤ n := le_trans (Nat.le_of_lt hzpos) hpow
    omega
  have hL1 : 1 ≤ L := by omega
  by_cases hbig : 20 ≤ L
  · rcases Nat.eq_zero_or_pos (a + b) with hab0 | hab1
    · 
      have ha0 : a = 0 := by omega
      have hb0 : b = 0 := by omega
      have hnm : n = m := by
        have := hdecomp; rw [ha0, hb0] at this; simpa using this
      have hLm : L = m := by
        have hz0 : z = 0 := by omega
        omega
      have hm20 : m ≠ 20 := by
        intro h; rw [h] at hc10; norm_num [Nat.Coprime] at hc10
      have hm21 : 21 ≤ m := by omega
      by_cases hpp : IsPrimePow m
      · 
        obtain ⟨p, k, hp, hk, hpk⟩ := (isPrimePow_nat_iff m).mp hpp
        obtain ⟨P, hmP, hdlen, hpal⟩ :=
          pal_diag hp hk hpk.symm hc10 hm21
        have hPpos : 0 < P := by
          rcases Nat.eq_zero_or_pos P with h0 | hp
          · rw [h0, Nat.digits_zero, List.length_nil] at hdlen; omega
          · exact hp
        rw [← hnm] at hmP
        refine ⟨P, hPpos, hmP, ?_, strict_to_relaxed P hPpos hpal⟩
        rw [hnm]; exact hdlen
      · 
        have hT2 : m ∣ 10 ^ (m.totient / 2) - 1 :=
          totient_half_dvd_sub_one hc10 hpp (by omega)
        obtain ⟨c2, hc2⟩ := Nat.totient_even (by omega : 2 < m)
        have htp : 0 < m.totient := Nat.totient_pos.mpr hmpos
        have ht2pos : 0 < m.totient / 2 := by omega
        have hb2' : 2 * (m.totient / 2) ≤ m := by
          have htl : m.totient < m := Nat.totient_lt _ (by omega)
          omega
        obtain ⟨P, hmP, hdigP⟩ :=
          pal_digits_large m m (m.totient / 2) hT2 ht2pos hb2'
        have hPpos : 0 < P := by
          rcases Nat.eq_zero_or_pos P with h0 | hp
          · rw [h0] at hdigP; simp at hdigP; omega
          · exact hp
        have hhead : (Nat.digits 10 P).head? = some 9 := by
          rw [hdigP]
          rw [show List.replicate (m.totient / 2) 9 =
              9 :: List.replicate (m.totient / 2 - 1) 9 from by
                nth_rewrite 1 [(Nat.sub_add_cancel ht2pos).symm]
                rw [List.replicate_succ],
              List.cons_append]
          simp
        rw [← hnm] at hmP
        refine ⟨P, hPpos, hmP, ?_, ?_⟩
        · rw [hnm, hdigP, List.length_append, List.length_append,
            List.length_replicate, List.length_replicate]
          omega
        · rw [dropWhile_self_of_head?_nine hhead, hdigP,
            List.Palindrome.iff_reverse_eq, List.reverse_append,
            List.reverse_append, List.reverse_replicate,
            List.reverse_replicate, List.append_assoc]
    · 
      have hT : m ∣ 10 ^ m.totient - 1 := by
        have h1 : 1 ≤ 10 ^ m.totient := Nat.one_le_pow _ _ (by norm_num)
        exact (Nat.modEq_iff_dvd' h1).mp (Nat.ModEq.pow_totient hc10.symm).symm
      have htpos : 0 < m.totient := Nat.totient_pos.mpr hmpos
      have hb2 : 2 * m.totient ≤ L := by
        rcases Nat.eq_or_lt_of_le hmpos with hm1 | hm2ge
        · rw [← hm1, Nat.totient_one]; omega
        · have htm1 : m.totient ≤ m - 1 := by
            have h := Nat.totient_lt _ hm2ge; omega
          have hge : a + b + 2 * m ≤ 2 ^ a * 5 ^ b * m + 2 := by
            rcases h2or5 with h2n | h5n
            · have ha0 : a = 0 := padicValNat.eq_zero_of_not_dvd h2n
              rw [ha0]; simp only [pow_zero, one_mul]
              have hb1 : 1 ≤ b := by omega
              have h5ge : b + 1 ≤ 5 ^ b := le_trans b.lt_two_pow_self
                (Nat.pow_le_pow_left (by norm_num) b)
              have hbm : b + m ≤ b * m + 2 := by
                rcases Nat.eq_or_lt_of_le hb1 with hb1e | hb2e
                · rw [← hb1e]; omega
                · nlinarith
              have h5m : (b + 1) * m ≤ 5 ^ b * m :=
                Nat.mul_le_mul_right m h5ge
              nlinarith
            · have hb0 : b = 0 :=
                padicValNat.eq_zero_of_not_dvd (fun hd => h5n (hd.trans hq1n))
              rw [hb0]; simp only [pow_zero, mul_one]
              have ha1 : 1 ≤ a := by omega
              have h2ge : a + 1 ≤ 2 ^ a := a.lt_two_pow_self
              have ham : a + m ≤ a * m + 2 := by
                rcases Nat.eq_or_lt_of_le ha1 with ha1e | ha2e
                · rw [← ha1e]; omega
                · nlinarith
              have h2m : (a + 1) * m ≤ 2 ^ a * m :=
                Nat.mul_le_mul_right m h2ge
              nlinarith
          omega
      obtain ⟨P, hmP, hdigP⟩ :=
        pal_digits_large m L m.totient hT htpos hb2
      have hPpos : 0 < P := by
        rcases Nat.eq_zero_or_pos P with h0 | hp
        · rw [h0] at hdigP; simp at hdigP; omega
        · exact hp
      have hhead : (Nat.digits 10 P).head? = some 9 := by
        rw [hdigP]
        rw [show List.replicate m.totient 9 = 9 :: List.replicate (m.totient - 1) 9
            from by
              nth_rewrite 1 [(Nat.sub_add_cancel htpos).symm]
              rw [List.replicate_succ],
            List.cons_append]
        simp
      refine ⟨P * 10 ^ z, by positivity, ?_, ?_, ?_⟩
      · rw [hdecomp]
        have h2a : 2 ^ a ∣ 10 ^ z := by
          rw [hz, show (10 : ℕ) = 2 * 5 from rfl, Nat.mul_pow]
          exact dvd_mul_of_dvd_left (pow_dvd_pow 2 (Nat.le_add_right a b)) _
        have h5b : 5 ^ b ∣ 10 ^ z := by
          rw [hz, show (10 : ℕ) = 2 * 5 from rfl, Nat.mul_pow]
          exact dvd_mul_of_dvd_right (pow_dvd_pow 5 (Nat.le_add_left b a)) _
        have hc25 : Nat.Coprime (2 ^ a) (5 ^ b) :=
          Nat.Coprime.pow_right b (Nat.Coprime.pow_left a (by norm_num))
        have h25 : 2 ^ a * 5 ^ b ∣ P * 10 ^ z :=
          hc25.mul_dvd_of_dvd_of_dvd (dvd_mul_of_dvd_right h2a P)
            (dvd_mul_of_dvd_right h5b P)
        have hcR : Nat.Coprime (2 ^ a * 5 ^ b) m :=
          (Nat.Coprime.mul_right (Nat.Coprime.pow_right a h2)
            (Nat.Coprime.pow_right b h5)).symm
        exact hcR.mul_dvd_of_dvd_of_dvd h25 (dvd_mul_of_dvd_left hmP _)
      · rw [mul_comm, Nat.digits_base_pow_mul (by norm_num) hPpos,
            List.length_append, List.length_replicate, hdigP,
            List.length_append, List.length_append, List.length_replicate,
            List.length_replicate]
        omega
      · have hdN : Nat.digits 10 (P * 10 ^ z) =
            List.replicate z 0 ++ Nat.digits 10 P := by
          rw [mul_comm]; exact Nat.digits_base_pow_mul (by norm_num) hPpos
        rw [hdN, dropWhile_zero_prefix _ hhead, hdigP,
            List.Palindrome.iff_reverse_eq, List.reverse_append,
            List.reverse_append, List.reverse_replicate, List.reverse_replicate,
            List.append_assoc]
  · have hk : ∀ k : ℕ, 5 ≤ k → k + 20 ≤ 2 ^ k := by
      intro k hk5
      induction' k, hk5 using Nat.le_induction with k' hk' ih
      · norm_num
      · calc k' + 1 + 20 ≤ 2 * (k' + 20) := by omega
          _ ≤ 2 * 2 ^ k' := Nat.mul_le_mul_left _ ih
          _ = 2 ^ (k' + 1) := (pow_succ' 2 k').symm
    have hab4 : a + b ≤ 4 := by
      by_contra h4
      push_neg at h4
      have := hk (a + b) (by omega)
      omega
    have hn23 : n ≤ 23 := by omega
    obtain ⟨N, hNpos, hdvN, hlenN, hpalN⟩ := wit013_spec n hn hn23 h10
    exact ⟨N, hNpos, hdvN, hlenN, strict_to_relaxed N hNpos hpalN⟩


theorem A084013 (n : ℕ) (hn : 1 ≤ n) :
    ∃ N : ℕ, 0 < N ∧ n ∣ N ∧
      (Nat.digits 10 N).length = n ∧
      List.Palindrome ((Nat.digits 10 N).dropWhile (· = 0)) := by
  by_cases h10 : 10 ∣ n
  · exact A084013_relaxed n hn h10
  · exact A084013_strict n hn h10




theorem no_strict_pal_mul_ten_dvd {n N : ℕ} (hn : 1 ≤ n) (h10 : 10 ∣ n)
    (hlen : (Nat.digits 10 N).length = n)
    (hpal : List.Palindrome (Nat.digits 10 N)) : ¬ n ∣ N := by
  intro hdvd
  have hN0 : N ≠ 0 := by
    intro h; rw [h, Nat.digits_zero, List.length_nil] at hlen
    omega
  have h10N : 10 ∣ N := h10.trans hdvd
  have hlast : (Nat.digits 10 N).head? = some 0 := by
    rw [Nat.digits_eq_cons_digits_div (by norm_num) hN0, List.head?_cons,
      Nat.mod_eq_zero_of_dvd h10N]
  have hne : (Nat.digits 10 N).getLast? ≠ some 0 :=
    digits_getLast?_ne_zero N (Nat.pos_of_ne_zero hN0)
  rw [List.Palindrome.iff_reverse_eq] at hpal
  have heq : (Nat.digits 10 N).head? = (Nat.digits 10 N).getLast? := by
    conv_lhs => rw [← hpal]
    exact List.head?_reverse
  rw [hlast] at heq
  exact hne heq.symm


theorem strict_pal_exists_coprime {m : ℕ} (hm : 1 ≤ m)
    (hcop : Nat.Coprime m 10) :
    ∃ P : ℕ, 0 < P ∧ m ∣ P ∧ (Nat.digits 10 P).length = m ∧
      List.Palindrome (Nat.digits 10 P) := by
  rcases le_total m 23 with h23 | h23
  · have h10 : ¬ 10 ∣ m := by
      intro h; rw [Nat.Coprime] at hcop
      have := Nat.dvd_gcd h (dvd_refl 10); rw [hcop] at this
      omega
    obtain ⟨P, hP, hdv, hlen, hpal⟩ := wit013_spec m hm h23 h10
    exact ⟨P, hP, hdv, hlen, hpal⟩
  · have hm21 : 21 ≤ m := by omega
    by_cases hpp : IsPrimePow m
    · obtain ⟨p, k, hp, hk, hpk⟩ := (isPrimePow_nat_iff m).mp hpp
      obtain ⟨P, hmP, hdlen, hpal⟩ := pal_diag hp hk hpk.symm hcop hm21
      have hPpos : 0 < P := by
        rcases Nat.eq_zero_or_pos P with h0 | hp'
        · rw [h0, Nat.digits_zero, List.length_nil] at hdlen; omega
        · exact hp'
      exact ⟨P, hPpos, hmP, hdlen, hpal⟩
    · have hT2 : m ∣ 10 ^ (m.totient / 2) - 1 :=
        totient_half_dvd_sub_one hcop hpp (by omega)
      obtain ⟨c2, hc2⟩ := Nat.totient_even (by omega : 2 < m)
      have htp : 0 < m.totient := Nat.totient_pos.mpr (by omega)
      have ht2pos : 0 < m.totient / 2 := by omega
      have hb2' : 2 * (m.totient / 2) ≤ m := by
        have htl : m.totient < m := Nat.totient_lt _ (by omega)
        omega
      obtain ⟨P, hmP, hdigP⟩ :=
        pal_digits_large m m (m.totient / 2) hT2 ht2pos hb2'
      have hPpos : 0 < P := by
        rcases Nat.eq_zero_or_pos P with h0 | hp'
        · rw [h0] at hdigP; simp at hdigP; omega
        · exact hp'
      refine ⟨P, hPpos, hmP, ?_, ?_⟩
      · rw [hdigP, List.length_append, List.length_append,
          List.length_replicate, List.length_replicate]
        omega
      · rw [hdigP, List.Palindrome.iff_reverse_eq, List.reverse_append,
          List.reverse_append, List.reverse_replicate,
          List.reverse_replicate, List.append_assoc]


theorem digits_rev_of_digits_ne_zero {e : ℕ} (heu : e % 10 ≠ 0) :
    Nat.digits 10 (Nat.ofDigits 10 (Nat.digits 10 e).reverse) =
      (Nat.digits 10 e).reverse := by
  have he0 : e ≠ 0 := by
    intro h; rw [h] at heu; simp at heu
  have hne : Nat.digits 10 e ≠ [] := Nat.digits_ne_nil_iff_ne_zero.mpr he0
  have hcon := Nat.digits_eq_cons_digits_div (b := 10) (by norm_num) he0
  have hg : ((Nat.digits 10 e).reverse).getLast? ≠ some 0 := by
    rw [List.getLast?_eq_head?_reverse, List.reverse_reverse, hcon,
      List.head?_cons]
    simp [heu]
  apply Nat.digits_ofDigits 10 (by norm_num)
  · intro l hl
    rw [List.mem_reverse] at hl
    exact Nat.digits_lt_base (by norm_num) hl
  · intro hne2 h0
    have h2 : ((Nat.digits 10 e).reverse).getLast? = some 0 := by
      rw [List.getLast?_eq_some_getLast hne2, h0]
    exact hg h2

theorem ofDigits_replicate_zero (s : ℕ) :
    Nat.ofDigits 10 (List.replicate s 0) = 0 := by
  induction s with
  | zero => simp
  | succ s ih => simp [List.replicate_succ, Nat.ofDigits_cons, ih]


theorem strict_pal_sandwich {n z e d : ℕ} (hz : 1 ≤ z) (hnz : 2 * z ≤ n)
    (hez : (Nat.digits 10 e).length = z) (heu : e % 10 ≠ 0)
    (hde : d ∣ e) (hd10 : d ∣ 10 ^ (n - z)) :
    ∃ N : ℕ, 0 < N ∧ d ∣ N ∧ (Nat.digits 10 N).length = n ∧
      List.Palindrome (Nat.digits 10 N) := by
  have he0 : e ≠ 0 := fun h => by subst h; simp at heu
  have hrev_ne : (Nat.digits 10 e).reverse ≠ [] := by
    simpa using Nat.digits_ne_nil_iff_ne_zero.mpr he0
  set rev_e := Nat.ofDigits 10 (Nat.digits 10 e).reverse with hrev_e
  have hdrev : Nat.digits 10 rev_e = (Nat.digits 10 e).reverse :=
    digits_rev_of_digits_ne_zero heu
  have hBne : Nat.digits 10 rev_e ≠ [] := by
    rw [hdrev]; exact hrev_ne
  have hlen_rev : (Nat.digits 10 rev_e).length = z := by
    rw [hdrev, List.length_reverse, hez]
  set L := Nat.digits 10 e ++ List.replicate (n - 2 * z) 0 ++
    Nat.digits 10 rev_e with hL
  have hlast0 : L.getLast? ≠ some 0 := by
    have hgl : L.getLast? = (Nat.digits 10 rev_e).getLast? := by
      rw [hL, List.getLast?_append, List.getLast?_eq_some_getLast hBne]
      simp
    rw [hgl, hdrev, List.getLast?_eq_head?_reverse,
      List.reverse_reverse,
      Nat.digits_eq_cons_digits_div (b := 10) (by norm_num) he0,
      List.head?_cons]
    simp [heu]
  have hdig : Nat.digits 10 (Nat.ofDigits 10 L) = L := by
    apply Nat.digits_ofDigits 10 (by norm_num)
    · intro l hl
      rw [hL, List.mem_append, List.mem_append] at hl
      rcases hl with (hl | hl) | hl
      · exact Nat.digits_lt_base (by norm_num) hl
      · rcases List.mem_replicate.mp hl with ⟨_, rfl⟩
        norm_num
      · exact Nat.digits_lt_base (by norm_num) hl
    · intro hne2 h0
      exact hlast0 (by rw [List.getLast?_eq_some_getLast hne2, h0])
  have hof : Nat.ofDigits 10 L = rev_e * 10 ^ (n - z) + e := by
    rw [hL, ofDigits_append', ofDigits_append', ofDigits_replicate_zero,
      Nat.ofDigits_digits, Nat.ofDigits_digits, List.length_append,
      List.length_replicate, hez]
    have hz2 : z + (n - 2 * z) = n - z := by omega
    rw [hz2]; ring
  refine ⟨Nat.ofDigits 10 L, ?_, ?_, ?_, ?_⟩
  · rcases Nat.eq_zero_or_pos (Nat.ofDigits 10 L) with h | h
    · rw [h, Nat.digits_zero] at hdig
      have hLne : L ≠ [] := by
        rw [hL]
        exact fun h2 => hBne ((List.append_eq_nil_iff.mp h2).2)
      exact absurd hdig.symm hLne
    · exact h
  · rw [hof]
    exact dvd_add (dvd_mul_of_dvd_right hd10 rev_e) hde
  · rw [hdig, hL, List.length_append, List.length_append,
      List.length_replicate, hlen_rev, hez]; omega
  · rw [hdig, List.Palindrome.iff_reverse_eq, hL]
    simp only [List.reverse_append, List.reverse_replicate, hdrev,
      List.reverse_reverse, List.append_assoc]



theorem two_mul_le_pow {c : ℕ} (hc : 2 ≤ c) : ∀ a : ℕ, 1 ≤ a → 2 * a ≤ c ^ a := by
  intro a ha
  induction a with
  | zero => omega
  | succ k ih =>
    rcases Nat.eq_zero_or_pos k with hk | hk
    · subst hk
      calc 2 * 1 = 2 := rfl
        _ ≤ c ^ 1 := by rw [pow_one]; exact hc
    · have hih := ih (by omega)
      have hca : 2 ≤ c ^ k :=
        le_trans hc (Nat.le_self_pow (by omega : k ≠ 0) c)
      calc 2 * (k + 1) = 2 * k + 2 := by ring
        _ ≤ c ^ k + c ^ k := Nat.add_le_add hih hca
        _ = 2 * c ^ k := by ring
        _ ≤ c * c ^ k := Nat.mul_le_mul_right _ hc
        _ = c ^ (k + 1) := (pow_succ' c k).symm

theorem ten_pow_split (k : ℕ) : 10 ^ k = 2 ^ k * 5 ^ k := by
  rw [show (10 : ℕ) = 2 * 5 by norm_num, mul_pow]


theorem pow_dvd_ten_pow {c : ℕ} (hcd : c ∣ 10) {a : ℕ} (ha : 1 ≤ a)
    (h2a : 2 * a ≤ c ^ a) : c ^ a ∣ 10 ^ (c ^ a - a) := by
  have hle : a ≤ c ^ a - a := by omega
  exact Nat.dvd_trans (Nat.pow_dvd_pow c hle)
    (pow_dvd_pow_of_dvd hcd (c ^ a - a))


theorem exists_e_two_pow {a : ℕ} (ha : 1 ≤ a) :
    ∃ e : ℕ, 2 ^ a ∣ e ∧ 10 ^ (a - 1) ≤ e ∧ e < 10 ^ a ∧ e % 10 ≠ 0 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : a ≠ 0)
  have hk : (k + 1) - 1 = k := Nat.add_sub_cancel k 1
  refine ⟨2 * 10 ^ k + 2 ^ (k + 1), ?_, ?_, ?_, ?_⟩
  · have h1 : 2 ^ (k + 1) ∣ 2 * 10 ^ k := by
      use 5 ^ k
      rw [ten_pow_split, pow_succ']; ring
    exact Nat.dvd_add h1 (dvd_refl _)
  · rw [hk]
    exact Nat.le_add_right_of_le (Nat.le_mul_of_pos_left _ (by norm_num : 0 < 2))
  · have h2 : 2 ^ (k + 1) = 2 * 2 ^ k := pow_succ' 2 k
    have h3 : 2 ^ k ≤ 10 ^ k :=
      pow_le_pow_left₀ (by norm_num : (0 : ℕ) ≤ 2) (by norm_num : (2 : ℕ) ≤ 10) k
    rw [h2]
    calc 2 * 10 ^ k + 2 * 2 ^ k
        ≤ 2 * 10 ^ k + 2 * 10 ^ k :=
          Nat.add_le_add_left (Nat.mul_le_mul (le_refl 2) h3) _
      _ = 4 * 10 ^ k := by ring
      _ < 10 * 10 ^ k :=
          Nat.mul_lt_mul_of_pos_right (by norm_num : 4 < 10) (by positivity)
      _ = 10 ^ (k + 1) := by rw [pow_succ]; exact mul_comm _ _
  · rcases k with _ | k'
    · norm_num
    · intro hmod
      have h10e : 10 ∣ 2 * 10 ^ (k' + 1) + 2 ^ (k' + 1 + 1) :=
        Nat.dvd_of_mod_eq_zero hmod
      have h10p : 10 ∣ 2 * 10 ^ (k' + 1) := by
        use 2 * 10 ^ k'
        rw [pow_succ]; ring
      have h10q : 10 ∣ 2 ^ (k' + 1 + 1) :=
        (Nat.dvd_add_iff_right h10p).mpr h10e
      have h5 : 5 ∣ 2 ^ (k' + 1 + 1) := Nat.dvd_trans ⟨2, rfl⟩ h10q
      exact absurd (Nat.prime_five.dvd_of_dvd_pow h5) (by norm_num)


theorem exists_e_five_pow {b : ℕ} (hb : 1 ≤ b) :
    ∃ e : ℕ, 5 ^ b ∣ e ∧ 10 ^ (b - 1) ≤ e ∧ e < 10 ^ b ∧ e % 10 ≠ 0 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : b ≠ 0)
  rcases k with _ | k'
  · exact ⟨5, by norm_num⟩
  · refine ⟨5 * 10 ^ (k' + 1) + 5 ^ (k' + 1 + 1), ?_, ?_, ?_, ?_⟩
    · have h1 : 5 ^ (k' + 1 + 1) ∣ 5 * 10 ^ (k' + 1) := by
        use 2 ^ (k' + 1)
        rw [ten_pow_split, pow_succ']; ring
      exact Nat.dvd_add h1 (dvd_refl _)
    · have hk : (k' + 1 + 1) - 1 = k' + 1 := Nat.add_sub_cancel _ _
      rw [hk]
      exact Nat.le_add_right_of_le
        (Nat.le_mul_of_pos_left _ (by norm_num : 0 < 5))
    · have h2 : 5 ^ (k' + 1 + 1) = 5 * 5 ^ (k' + 1) := pow_succ' 5 _
      have h3 : 5 ^ (k' + 1) < 10 ^ (k' + 1) :=
        pow_lt_pow_left₀ (by norm_num : (5 : ℕ) < 10) (by norm_num) (by omega)
      rw [h2]
      calc 5 * 10 ^ (k' + 1) + 5 * 5 ^ (k' + 1)
          < 5 * 10 ^ (k' + 1) + 5 * 10 ^ (k' + 1) :=
            Nat.add_lt_add_left
              (Nat.mul_lt_mul_of_pos_left h3 (by norm_num : 0 < 5)) _
        _ = 10 * 10 ^ (k' + 1) := by ring
        _ = 10 ^ (k' + 1 + 1) := by rw [pow_succ]; exact mul_comm _ _
    · intro hmod
      have h10e : 10 ∣ 5 * 10 ^ (k' + 1) + 5 ^ (k' + 1 + 1) :=
        Nat.dvd_of_mod_eq_zero hmod
      have h10p : 10 ∣ 5 * 10 ^ (k' + 1) := by
        use 5 * 10 ^ k'
        rw [pow_succ]; ring
      have h10q : 10 ∣ 5 ^ (k' + 1 + 1) :=
        (Nat.dvd_add_iff_right h10p).mpr h10e
      have h2 : 2 ∣ 5 ^ (k' + 1 + 1) := Nat.dvd_trans ⟨5, rfl⟩ h10q
      exact absurd (Nat.prime_two.dvd_of_dvd_pow h2) (by norm_num)


theorem strict_pal_exists_pow_two (a : ℕ) (ha : 1 ≤ a) :
    ∃ N : ℕ, 0 < N ∧ 2 ^ a ∣ N ∧ (Nat.digits 10 N).length = 2 ^ a ∧
      List.Palindrome (Nat.digits 10 N) := by
  obtain ⟨e, hde, hge, hlt, hmod⟩ := exists_e_two_pow ha
  have he0 : e ≠ 0 := by
    have hpos : 0 < 10 ^ (a - 1) := by positivity
    omega
  have hez : (Nat.digits 10 e).length = a := by
    rw [Nat.length_digits 10 e (by norm_num) he0]
    have hlog : Nat.log 10 e = a - 1 := by
      apply Nat.log_eq_of_pow_le_of_lt_pow hge
      rw [Nat.sub_add_cancel ha]; exact hlt
    rw [hlog]; exact Nat.sub_add_cancel ha
  exact strict_pal_sandwich ha
    (two_mul_le_pow (by norm_num : (2 : ℕ) ≤ 2) a ha) hez hmod hde
    (pow_dvd_ten_pow ⟨5, rfl⟩ ha (two_mul_le_pow (by norm_num) a ha))


theorem strict_pal_exists_pow_five (b : ℕ) (hb : 1 ≤ b) :
    ∃ N : ℕ, 0 < N ∧ 5 ^ b ∣ N ∧ (Nat.digits 10 N).length = 5 ^ b ∧
      List.Palindrome (Nat.digits 10 N) := by
  obtain ⟨e, hde, hge, hlt, hmod⟩ := exists_e_five_pow hb
  have he0 : e ≠ 0 := by
    have hpos : 0 < 10 ^ (b - 1) := by positivity
    omega
  have hez : (Nat.digits 10 e).length = b := by
    rw [Nat.length_digits 10 e (by norm_num) he0]
    have hlog : Nat.log 10 e = b - 1 := by
      apply Nat.log_eq_of_pow_le_of_lt_pow hge
      rw [Nat.sub_add_cancel hb]; exact hlt
    rw [hlog]; exact Nat.sub_add_cancel hb
  exact strict_pal_sandwich hb
    (two_mul_le_pow (by norm_num : (2 : ℕ) ≤ 5) b hb) hez hmod hde
    (pow_dvd_ten_pow ⟨2, rfl⟩ hb (two_mul_le_pow (by norm_num) b hb))

theorem dead_weight_eq_neg_one_L {p L i : ℕ} (hp : p.Prime)
    (hcop : Nat.Coprime 10 p) (hi : 2 * i < L)
    (hpdvd : p ∣ 10 ^ i + 10 ^ (L - 1 - i)) :
    (10 : ZMod p) ^ (L - 1 - 2 * i) = -1 := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hcast : ((10 ^ i + 10 ^ (L - 1 - i) : ℕ) : ZMod p) = 0 :=
    (CharP.cast_eq_zero_iff (ZMod p) p _).mpr hpdvd
  have hsplit : i + (L - 1 - 2 * i) = L - 1 - i := by omega
  have hnat : 10 ^ i * (1 + 10 ^ (L - 1 - 2 * i)) =
      10 ^ i + 10 ^ (L - 1 - i) := by
    rw [mul_add, mul_one, ← pow_add, hsplit]
  rw [← hnat] at hcast
  push_cast at hcast
  have h10ne : (10 : ZMod p) ≠ 0 := by
    have hpd : ¬ p ∣ 10 :=
      (hp.coprime_iff_not_dvd).mp (Nat.coprime_comm.mp hcop)
    exact fun h =>
      hpd ((CharP.cast_eq_zero_iff (ZMod p) p 10).mp (by exact_mod_cast h))
  have h1e : (10 : ZMod p) ^ (L - 1 - 2 * i) + 1 = 0 := by
    rw [add_comm]
    exact (mul_eq_zero.mp hcast).resolve_left (pow_ne_zero i h10ne)
  exact eq_neg_of_add_eq_zero_left h1e


theorem ord_two_mod_four {p e : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {u : (ZMod p)ˣ} (he : Odd e) (hu : u ^ e = -1) :
    2 ∣ orderOf u ∧ Odd (orderOf u / 2) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hne1 : (-1 : (ZMod p)ˣ) ≠ 1 := by
    intro h
    have h1 : (-1 : ZMod p) = 1 := by simpa using congrArg Units.val h
    have hr2 : ringChar (ZMod p) = 2 := neg_one_eq_one_iff.mp h1
    exact hp2 ((ZMod.ringChar_zmod_n p) ▸ hr2)
  have hpow1 : u ^ (2 * e) = 1 := by rw [pow_mul', hu]; simp
  have h2e : orderOf u ∣ 2 * e := orderOf_dvd_of_pow_eq_one hpow1
  have hne : ¬ orderOf u ∣ e :=
    mt orderOf_dvd_iff_pow_eq_one.mp (fun heq => hne1 ((heq ▸ hu).symm))
  have h2dvd : 2 ∣ orderOf u := by
    rcases Nat.even_or_odd (orderOf u) with hE | hO
    · exact even_iff_two_dvd.mp hE
    · exfalso
      have hc : Nat.Coprime (orderOf u) 2 :=
        Nat.coprime_comm.mp (Nat.coprime_two_left.mpr hO)
      have : orderOf u ∣ e := hc.dvd_of_dvd_mul_left h2e
      exact hne this
  have hhalf : orderOf u / 2 ∣ e := by
    have h2ord : orderOf u = 2 * (orderOf u / 2) :=
      (Nat.mul_div_cancel' h2dvd).symm
    have h2x : 2 * (orderOf u / 2) ∣ 2 * e := by
      rw [← h2ord]; exact h2e
    exact (Nat.mul_dvd_mul_iff_left two_pos).mp h2x
  refine ⟨h2dvd, ?_⟩
  rcases hhalf with ⟨c, hc⟩
  have hoddmul : Odd (orderOf u / 2 * c) := hc ▸ he
  exact (Nat.odd_mul.mp hoddmul).1


theorem dead_count_even {p L : ℕ} (hp : p.Prime)
    (hcop : Nat.Coprime 10 p) (hp11 : p ≠ 11) (hL : Even L) :
    ((Finset.range (L / 2)).filter fun i =>
        p ∣ 10 ^ i + 10 ^ (L - 1 - i)).card ≤ L / 6 + 1 := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := by
    intro h2
    rw [h2] at hcop
    exact absurd hcop (by decide : ¬ Nat.Coprime 10 2)
  set u : (ZMod p)ˣ := ZMod.unitOfCoprime 10 hcop with hu
  set ord := orderOf u with hord
  set dead := (Finset.range (L / 2)).filter (fun i =>
    p ∣ 10 ^ i + 10 ^ (L - 1 - i)) with hdead_def
  have hval : ∀ i ∈ dead, u ^ (L - 1 - 2 * i) = -1 := fun i hi => by
    have him := Finset.mem_filter.mp hi
    have h10e := dead_weight_eq_neg_one_L hp hcop
      (by have := Finset.mem_range.mp him.1; omega : 2 * i < L) him.2
    rw [← Units.val_eq_neg_one, Units.val_pow_eq_pow_val, hu,
      ZMod.coe_unitOfCoprime]
    exact h10e
  by_cases hde : dead.Nonempty
  · have hL2 : 2 ≤ L := by
      obtain ⟨i₀, hi₀⟩ := hde
      have := Finset.mem_range.mp (Finset.mem_filter.mp hi₀).1; omega
    have hLo : Odd (L - 1) := by
      rcases hL with ⟨r, hr⟩
      refine ⟨r - 1, by omega⟩
    have hdiff : ∀ i₁ ∈ dead, ∀ i₂ ∈ dead, i₁ ≤ i₂ →
        ord ∣ 2 * (i₂ - i₁) := by
      intro i₁ h₁ i₂ h₂ hle
      have hb1 : 2 * i₁ ≤ L - 1 := by
        have := Finset.mem_range.mp (Finset.mem_filter.mp h₁).1; omega
      have hb2 : 2 * i₂ ≤ L - 1 := by
        have := Finset.mem_range.mp (Finset.mem_filter.mp h₂).1; omega
      have hpow : u ^ (L - 1 - 2 * i₁ - (L - 1 - 2 * i₂)) = 1 := by
        rw [pow_sub u (by omega : L - 1 - 2 * i₂ ≤ L - 1 - 2 * i₁),
          hval i₁ h₁, hval i₂ h₂]
        exact mul_inv_cancel (-1)
      have hd : ord ∣ L - 1 - 2 * i₁ - (L - 1 - 2 * i₂) :=
        orderOf_dvd_of_pow_eq_one hpow
      have heq : L - 1 - 2 * i₁ - (L - 1 - 2 * i₂) = 2 * (i₂ - i₁) := by
        omega
      rwa [heq] at hd
    obtain ⟨i₀, hi₀⟩ := hde
    have hi₀b : 2 * i₀ ≤ L - 1 := by
      have := Finset.mem_range.mp (Finset.mem_filter.mp hi₀).1; omega
    have hio : Odd (L - 1 - 2 * i₀) := by
      rcases hL with ⟨r, hr⟩
      refine ⟨r - 1 - i₀, by omega⟩
    obtain ⟨h2d, hodd⟩ := ord_two_mod_four hp hp2 hio (hval i₀ hi₀)
    have hord6 : 6 ≤ ord := by
      have hord2' : ord = 2 * (ord / 2) := (Nat.mul_div_cancel' h2d).symm
      have hhalf1 : ord / 2 ≠ 1 := by
        intro h1
        have hordeq : ord = 2 := by omega
        have hu2 : u ^ 2 = 1 := hordeq ▸ pow_orderOf_eq_one u
        rcases hio with ⟨j, hj⟩
        have hv := hval i₀ hi₀
        rw [hj, pow_add, pow_mul, hu2, one_pow, one_mul, pow_one] at hv
        have hv' : (u : ZMod p) = -1 := congrArg Units.val hv
        rw [hu, ZMod.coe_unitOfCoprime] at hv'
        have h11 : p ∣ 11 := by
          have h0 : ((10 + 1 : ℕ) : ZMod p) = 0 := by
            rw [Nat.cast_add, Nat.cast_one, hv']
            ring
          exact (CharP.cast_eq_zero_iff (ZMod p) p _).mp h0
        have h11p : p = 11 := by
          rcases (Nat.dvd_prime (by norm_num : Nat.Prime 11)).mp h11
            with h1' | h11'
          · exact absurd h1' hp.ne_one
          · exact h11'
        exact hp11 h11p
      have hge3 : 3 ≤ ord / 2 := by
        rcases hodd with ⟨j, hj⟩
        omega
      omega
    have halve : ∀ x, ord ∣ 2 * x → ord / 2 ∣ x := by
      intro x ⟨c, hc⟩
      refine ⟨c, Nat.eq_of_mul_eq_mul_left two_pos ?_⟩
      calc 2 * x = ord * c := hc
        _ = (2 * (ord / 2)) * c := by rw [Nat.mul_div_cancel' h2d]
        _ = 2 * (ord / 2 * c) := by ring
    have hcong : ∀ {a b : ℕ}, a ∈ dead → b ∈ dead → a ≤ b →
        a / (ord / 2) = b / (ord / 2) → a = b := by
      intro a b ha hb hle hq
      have hd : ord / 2 ∣ b - a := halve _ (hdiff a ha b hb hle)
      have hm1 : a % (ord / 2) = b % (ord / 2) :=
        (Nat.modEq_iff_dvd' hle).mpr hd
      have h1e := Nat.div_add_mod a (ord / 2)
      have h2e := Nat.div_add_mod b (ord / 2)
      rw [hq, hm1] at h1e
      exact h1e.symm.trans h2e
    have hinj : (↑dead : Set ℕ).InjOn (fun i => i / (ord / 2)) := by
      intro i₁ h₁ i₂ h₂ hq
      rcases le_total i₁ i₂ with hle | hle
      · exact hcong (Finset.mem_coe.mp h₁) (Finset.mem_coe.mp h₂) hle hq
      · exact (hcong (Finset.mem_coe.mp h₂) (Finset.mem_coe.mp h₁) hle
          hq.symm).symm
    have hsub : Set.MapsTo (fun i => i / (ord / 2)) ↑dead
        ↑(Finset.range ((L / 2) / (ord / 2) + 1)) := by
      intro i hi
      have hi2 : i < L / 2 :=
        Finset.mem_range.mp (Finset.mem_filter.mp (Finset.mem_coe.mp hi)).1
      have hord2 : 0 < ord / 2 := by omega
      have : i / (ord / 2) ≤ (L / 2) / (ord / 2) :=
        Nat.div_le_div_right hi2.le
      simpa using Nat.lt_succ_of_le this
    have hcard := Finset.card_le_card_of_injOn _ hsub hinj
    rw [Finset.card_range] at hcard
    have hdiv : (L / 2) / (ord / 2) = L / ord := by
      rw [Nat.div_div_eq_div_mul]
      congr 1
      exact Nat.mul_div_cancel' h2d
    rw [hdiv] at hcard
    have hle6 : L / ord ≤ L / 6 :=
      Nat.div_le_div_left hord6 (by norm_num)
    omega
  · rw [Finset.not_nonempty_iff_eq_empty.mp hde, Finset.card_empty]
    exact Nat.zero_le _


theorem pal_window_extract {m p k L : ℕ} (hp : p.Prime) (hk : 0 < k)
    (hm : m = p ^ k) (h10 : Nat.Coprime m 10) (hp11 : p ≠ 11)
    (hL : Even L) (hbound : m + 13 ≤ 3 * L) (t : ZMod m) :
    ∃ U : Finset ℕ, ∃ d : ℕ → ℕ,
      (∀ i, d i < 10) ∧ U ⊆ Finset.range (L / 2) ∧
      (∀ i, i ∉ U → d i = 0) ∧
      ((U.sum fun i => d i • ((10 ^ i + 10 ^ (L - 1 - i) : ℕ) : ZMod m))
        = t) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hmpos : 0 < m := by
    rw [hm]; exact pow_pos hp.pos k
  haveI : NeZero m := ⟨hmpos.ne'⟩
  have hcop_p : Nat.Coprime 10 p := coprime_10_of_prime_pow hp hk hm h10
  set j := L / 2 with hj
  set w : ℕ → ZMod m := fun i =>
    ((10 ^ i + 10 ^ (L - 1 - i) : ℕ) : ZMod m) with hw
  set dead := (Finset.range j).filter (fun i =>
    p ∣ 10 ^ i + 10 ^ (L - 1 - i)) with hdead_def
  set U := (Finset.range j).filter (fun i =>
    ¬ p ∣ 10 ^ i + 10 ^ (L - 1 - i)) with hU_def
  have hcards : dead.card + U.card = j := by
    rw [hdead_def, hU_def,
      Finset.card_filter_add_card_filter_not (s := Finset.range j)
        (p := fun i => p ∣ 10 ^ i + 10 ^ (L - 1 - i))]
    exact Finset.card_range j
  have hdead_bound : dead.card ≤ L / 6 + 1 := by
    rw [hdead_def, hj]
    exact dead_count_even hp hcop_p hp11 hL
  have hUnit : ∀ i ∈ U, IsUnit (w i) := by
    intro i hi
    have hif := Finset.mem_filter.mp hi
    have hnp := hif.2
    have hc_p : (10 ^ i + 10 ^ (L - 1 - i)).Coprime p := by
      rw [Nat.coprime_comm, hp.coprime_iff_not_dvd]
      exact hnp
    have hc_m : (10 ^ i + 10 ^ (L - 1 - i)).Coprime (p ^ k) :=
      (Nat.coprime_pow_right_iff hk _ _).mpr hc_p
    rw [ZMod.isUnit_iff_coprime]
    exact hm.symm ▸ hc_m
  set S := U.sum fun i => (Finset.range 10).image (· • w i) with hS
  have hgrow : min m (1 + 9 * U.card) ≤ S.card := card_sum_intervals hUnit
  have hcover : m ≤ 1 + 9 * U.card := by
    rw [hj] at hcards
    omega
  have hmin : min m (1 + 9 * U.card) = m := min_eq_left hcover
  have hSm : m ≤ S.card := by
    rw [hmin] at hgrow
    exact hgrow
  have hS_univ : S = Finset.univ := by
    have hcard : S.card = Fintype.card (ZMod m) := by
      have hz : Fintype.card (ZMod m) = m := ZMod.card m
      have hle : S.card ≤ Fintype.card (ZMod m) :=
        Finset.card_le_univ S
      omega
    exact Finset.eq_univ_of_card S hcard
  have hmem : t ∈ S := hS_univ ▸ Finset.mem_univ t
  rw [hS] at hmem
  rw [mem_finset_sum] at hmem
  rcases hmem with ⟨g, hgmem, hgsum⟩
  have hd_ex : ∀ i, ∃ d : ℕ, d < 10 ∧ (i ∈ U → d • w i = g i) ∧
      (i ∉ U → d = 0) := by
    intro i
    by_cases hi : i ∈ U
    · have h := hgmem i hi
      rw [Finset.mem_image] at h
      rcases h with ⟨d0, hd0, hd0eq⟩
      exact ⟨d0, Finset.mem_range.mp hd0, fun _ => hd0eq,
        fun h' => absurd hi h'⟩
    · exact ⟨0, by norm_num, fun h' => absurd h' hi, fun _ => rfl⟩
  choose d hd1 hd2 hd3 using hd_ex
  refine ⟨U, d, fun i => hd1 i, fun i hi => (Finset.mem_filter.mp hi).1,
    fun i hi => hd3 i hi, ?_⟩
  have hcongr : (U.sum fun i => d i • w i) = U.sum g :=
    Finset.sum_congr rfl (fun i hi => hd2 i hi)
  rw [hcongr]
  exact hgsum


theorem strict_pal_sandwich_block {n z e : ℕ} (hz : 1 ≤ z)
    (hnz : 2 * z ≤ n) (hez : (Nat.digits 10 e).length = z)
    (heu : e % 10 ≠ 0)
    (W : List ℕ) (hWlen : W.length = n - 2 * z)
    (hWpal : List.Palindrome W) (hWd : ∀ x ∈ W, x < 10) :
    ∃ N : ℕ, 0 < N ∧
      N = Nat.ofDigits 10 (Nat.digits 10 e).reverse * 10 ^ (n - z) +
          Nat.ofDigits 10 W * 10 ^ z + e ∧
      (Nat.digits 10 N).length = n ∧
      List.Palindrome (Nat.digits 10 N) := by
  have he0 : e ≠ 0 := fun h => by subst h; simp at heu
  have hrev_ne : (Nat.digits 10 e).reverse ≠ [] := by
    simpa using Nat.digits_ne_nil_iff_ne_zero.mpr he0
  set rev_e := Nat.ofDigits 10 (Nat.digits 10 e).reverse with hrev_e
  have hdrev : Nat.digits 10 rev_e = (Nat.digits 10 e).reverse :=
    digits_rev_of_digits_ne_zero heu
  have hBne : Nat.digits 10 rev_e ≠ [] := by
    rw [hdrev]; exact hrev_ne
  have hlen_rev : (Nat.digits 10 rev_e).length = z := by
    rw [hdrev, List.length_reverse, hez]
  set L := Nat.digits 10 e ++ W ++ Nat.digits 10 rev_e with hL
  have hlast0 : L.getLast? ≠ some 0 := by
    have hgl : L.getLast? = (Nat.digits 10 rev_e).getLast? := by
      rw [hL, List.getLast?_append, List.getLast?_eq_some_getLast hBne]
      simp
    rw [hgl, hdrev, List.getLast?_eq_head?_reverse,
      List.reverse_reverse,
      Nat.digits_eq_cons_digits_div (b := 10) (by norm_num) he0,
      List.head?_cons]
    simp [heu]
  have hdig : Nat.digits 10 (Nat.ofDigits 10 L) = L := by
    apply Nat.digits_ofDigits 10 (by norm_num)
    · intro l hl
      rw [hL, List.mem_append, List.mem_append] at hl
      rcases hl with (hl | hl) | hl
      · exact Nat.digits_lt_base (by norm_num) hl
      · exact hWd l hl
      · exact Nat.digits_lt_base (by norm_num) hl
    · intro hne2 h0
      exact hlast0 (by rw [List.getLast?_eq_some_getLast hne2, h0])
  have hof : Nat.ofDigits 10 L =
      rev_e * 10 ^ (n - z) + Nat.ofDigits 10 W * 10 ^ z + e := by
    rw [hL, ofDigits_append', ofDigits_append', Nat.ofDigits_digits,
      Nat.ofDigits_digits, List.length_append, hWlen, hez]
    have hz2 : z + (n - 2 * z) = n - z := by omega
    rw [hz2]; ring
  refine ⟨Nat.ofDigits 10 L, ?_, ?_, ?_, ?_⟩
  · rcases Nat.eq_zero_or_pos (Nat.ofDigits 10 L) with h | h
    · rw [h, Nat.digits_zero] at hdig
      have hLne : L ≠ [] := by
        rw [hL]
        exact fun h2 => hBne ((List.append_eq_nil_iff.mp h2).2)
      exact absurd hdig.symm hLne
    · exact h
  · rw [hof]
  · rw [hdig, hL, List.length_append, List.length_append,
      hWlen, hlen_rev, hez]; omega
  · rw [hdig, List.Palindrome.iff_reverse_eq, hL]
    have hWr : W.reverse = W :=
      (List.Palindrome.iff_reverse_eq).mp hWpal
    rw [List.reverse_append, List.reverse_append, hdrev,
      List.reverse_reverse, hWr]
    simp only [List.append_assoc]


theorem strict_pal_exists_two_pow_mul {a m p k : ℕ} (ha : 1 ≤ a)
    (hp : p.Prime) (hk : 0 < k) (hm : m = p ^ k)
    (h10 : Nat.Coprime m 10) (hp11 : p ≠ 11)
    (hmb : 7 ≤ m ∨ 2 ≤ a) :
    ∃ N : ℕ, 0 < N ∧ (2 ^ a * m) ∣ N ∧
      (Nat.digits 10 N).length = 2 ^ a * m ∧
      List.Palindrome (Nat.digits 10 N) := by
  obtain ⟨a', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : a ≠ 0)
  have ha' : 1 ≤ a' + 1 := Nat.succ_pos a'
  set n := 2 ^ (a' + 1) * m with hn
  set z := a' + 1 with hz
  set L := n - 2 * z with hL
  have hmodd : Odd m := Nat.coprime_two_right.mp
    (h10.coprime_dvd_right ⟨5, rfl⟩)
  have hm2 : 2 ≤ m := by
    rw [hm]; exact hp.two_le.trans (Nat.le_self_pow hk.ne' p)
  have hm3 : 3 ≤ m := by rcases hmodd with ⟨t, ht⟩; omega
  have hmpos : 0 < m := by omega
  haveI : NeZero m := ⟨hmpos.ne'⟩
  have h2am : Nat.Coprime (2 ^ (a' + 1)) m :=
    ((h10.coprime_dvd_right ⟨5, rfl⟩).symm).pow_left _
  obtain ⟨e, he2, helo, hehi, heu⟩ := exists_e_two_pow ha'
  have he0 : e ≠ 0 := by
    have hpos : 0 < 10 ^ ((a' + 1) - 1) := by positivity
    omega
  have hez : (Nat.digits 10 e).length = z := by
    rw [hz, Nat.length_digits 10 e (by norm_num) he0]
    have hlog : Nat.log 10 e = (a' + 1) - 1 := by
      apply Nat.log_eq_of_pow_le_of_lt_pow helo
      rw [Nat.sub_add_cancel ha']; exact hehi
    rw [hlog]; exact Nat.sub_add_cancel ha'
  have hpow : 2 ^ (a' + 1) * m = 2 * (2 ^ a' * m) := by
    rw [pow_succ']; ring
  have hYc : a' + 1 ≤ 2 ^ a' * m := by
    have h1 : a' + 1 ≤ 2 ^ a' :=
      Nat.succ_le_of_lt
        (Nat.lt_pow_self (by norm_num : (1 : ℕ) < 2) : a' < 2 ^ a')
    calc a' + 1 ≤ 2 ^ a' := h1
      _ = 2 ^ a' * 1 := (mul_one _).symm
      _ ≤ 2 ^ a' * m := Nat.mul_le_mul_left _ hmpos
  have hY1 : m ≤ 2 ^ a' * m :=
    Nat.le_mul_of_pos_left _ (pow_pos (by norm_num) a')
  have hY2 : 3 * a' + 3 ≤ 2 ^ a' * m := by
    have h1 : a' + 1 ≤ 2 ^ a' :=
      Nat.succ_le_of_lt
        (Nat.lt_pow_self (by norm_num : (1 : ℕ) < 2) : a' < 2 ^ a')
    calc 3 * a' + 3 = (a' + 1) * 3 := by ring
      _ ≤ 2 ^ a' * m := Nat.mul_le_mul h1 hm3
  have hLe : Even L := by
    have hL' : L = 2 * (2 ^ a' * m) - 2 * (a' + 1) := by
      rw [hL, hn, hz]; rw [hpow]
    refine ⟨2 ^ a' * m - (a' + 1), ?_⟩
    omega
  have hbound : m + 13 ≤ 3 * L := by
    have h7 : 7 ≤ m + 6 * a' := by
      rcases hmb with hm7 | ha2
      · omega
      · omega
    have hL' : L = 2 * (2 ^ a' * m) - 2 * (a' + 1) := by
      rw [hL, hn, hz]; rw [hpow]
    omega
  have h2zn : 2 * z ≤ n := by
    rw [hz, hn]
    calc 2 * (a' + 1) ≤ 2 ^ (a' + 1) :=
        two_mul_le_pow (le_refl 2) _ ha'
      _ = 2 ^ (a' + 1) * 1 := (mul_one _).symm
      _ ≤ 2 ^ (a' + 1) * m := Nat.mul_le_mul_left _ hmpos
  set u : (ZMod m)ˣ := ZMod.unitOfCoprime 10 h10.symm
  set trev : ZMod m :=
    ↑(Nat.ofDigits 10 (Nat.digits 10 e).reverse) * (10 : ZMod m) ^ (n - z)
    with htrev
  set t : ZMod m := -(↑e + trev) * (↑((u ^ z)⁻¹) : ZMod m) with ht
  have htz : (10 : ZMod m) ^ z * t = -(↑e + trev) := by
    have hu10 : (↑u : ZMod m) = 10 := ZMod.coe_unitOfCoprime 10 _
    have h1 : (10 : ZMod m) ^ z * (↑((u ^ z)⁻¹) : ZMod m) = 1 := by
      rw [← hu10, ← Units.val_pow_eq_pow_val]
      exact Units.mul_inv _
    rw [ht, mul_left_comm, h1, mul_one]
  obtain ⟨U, d, hd_lt, hUsub, hd0, hsum⟩ :=
    pal_window_extract hp hk hm h10 hp11 hLe hbound t
  push_cast at hsum
  set j := L / 2 with hj
  set Db := (List.range j).map d with hDb
  set W := Db ++ Db.reverse with hW
  have h2j : 2 * j = L := by
    obtain ⟨r, hr⟩ := hLe
    rw [hj]; omega
  have hWlen : W.length = n - 2 * z := by
    rw [hW, List.length_append, List.length_reverse, hDb,
      List.length_map, List.length_range, ← two_mul, h2j]
  have hWpal : List.Palindrome W :=
    List.Palindrome.iff_reverse_eq.mpr (by
      rw [hW, List.reverse_append, List.reverse_reverse])
  have hWd : ∀ x ∈ W, x < 10 := by
    intro x hx
    rw [hW, List.mem_append, List.mem_reverse] at hx
    rcases hx with hx | hx
    · obtain ⟨i, -, rfl⟩ := List.mem_map.mp hx
      exact hd_lt i
    · obtain ⟨i, -, rfl⟩ := List.mem_map.mp hx
      exact hd_lt i
  have hMz : Nat.ofDigits (10 : ZMod m) W =
      ∑ i ∈ Finset.range j, (d i : ZMod m) *
        ((10 : ZMod m) ^ i + (10 : ZMod m) ^ (L - 1 - i)) := by
    rw [hW, hDb, ofDigits_append', List.length_map, List.length_range,
      ofDigits_zmod_range, ofDigits_zmod_rev, Finset.mul_sum,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun i hi => ?_)
    rw [Finset.mem_range] at hi
    calc (d i : ZMod m) * (10 : ZMod m) ^ i
        + (10 : ZMod m) ^ j *
          ((d i : ZMod m) * (10 : ZMod m) ^ (j - 1 - i))
        = (d i : ZMod m) * ((10 : ZMod m) ^ i
            + (10 : ZMod m) ^ (j + (j - 1 - i))) := by
          rw [pow_add]; ring
      _ = (d i : ZMod m) * ((10 : ZMod m) ^ i
            + (10 : ZMod m) ^ (L - 1 - i)) := by
          rw [show j + (j - 1 - i) = L - 1 - i by omega]
  have hsumU : ∑ i ∈ U, (d i : ZMod m) *
      ((10 : ZMod m) ^ i + (10 : ZMod m) ^ (L - 1 - i)) = t := by
    rw [← hsum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    simp only [nsmul_eq_mul, Nat.cast_add, Nat.cast_pow]
  have hMt : Nat.ofDigits (10 : ZMod m) W = t := by
    rw [hMz]
    have hsp : ∑ i ∈ Finset.range j, (d i : ZMod m) *
        ((10 : ZMod m) ^ i + (10 : ZMod m) ^ (L - 1 - i)) =
        ∑ i ∈ U, (d i : ZMod m) *
          ((10 : ZMod m) ^ i + (10 : ZMod m) ^ (L - 1 - i)) := by
      apply (Finset.sum_subset hUsub ?_).symm
      intro i _ hiU
      rw [hd0 i hiU]; simp
    rw [hsp]; exact hsumU
  obtain ⟨N, hNpos, hNeq, hNlen, hNpal⟩ :=
    strict_pal_sandwich_block (by omega) h2zn hez heu W hWlen
      hWpal hWd
  refine ⟨N, hNpos, ?_, hNlen, hNpal⟩
  have h2a10 : ∀ b : ℕ, a' + 1 ≤ b → 2 ^ (a' + 1) ∣ 10 ^ b := by
    intro b hb
    exact Nat.dvd_trans (Nat.pow_dvd_pow 2 hb)
      (pow_dvd_pow_of_dvd (⟨5, rfl⟩ : (2 : ℕ) ∣ 10) b)
  have hmN : m ∣ N := by
    have hcast : ((N : ℕ) : ZMod m) = 0 := by
      rw [hNeq]; push_cast
      rw [hMt]
      rw [mul_comm t ((10 : ZMod m) ^ z), htz, htrev]
      ring
    exact (CharP.cast_eq_zero_iff (ZMod m) m N).mp hcast
  have h2aN : 2 ^ (a' + 1) ∣ N := by
    rw [hNeq]
    apply Nat.dvd_add
    apply Nat.dvd_add
    · exact dvd_mul_of_dvd_right (h2a10 (n - z) (by omega)) _
    · exact dvd_mul_of_dvd_right (h2a10 z (by omega)) _
    · exact he2
  exact h2am.mul_dvd_of_dvd_of_dvd h2aN hmN


theorem dead_count_odd {p L : ℕ} (hp : p.Prime)
    (hcop : Nat.Coprime 10 p) (hL : Odd L) :
    ((Finset.range (L / 2)).filter fun i =>
        p ∣ 10 ^ i + 10 ^ (L - 1 - i)).card ≤ L / 4 + 1 := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := by
    intro h2
    rw [h2] at hcop
    exact absurd hcop (by decide : ¬ Nat.Coprime 10 2)
  set u : (ZMod p)ˣ := ZMod.unitOfCoprime 10 hcop with hu
  set ord := orderOf u with hord
  set dead := (Finset.range (L / 2)).filter (fun i =>
    p ∣ 10 ^ i + 10 ^ (L - 1 - i)) with hdead_def
  have hval : ∀ i ∈ dead, u ^ (L - 1 - 2 * i) = -1 := fun i hi => by
    have him := Finset.mem_filter.mp hi
    have h10e := dead_weight_eq_neg_one_L hp hcop
      (by have := Finset.mem_range.mp him.1; omega : 2 * i < L) him.2
    rw [← Units.val_eq_neg_one, Units.val_pow_eq_pow_val, hu,
      ZMod.coe_unitOfCoprime]
    exact h10e
  by_cases hde : dead.Nonempty
  · obtain ⟨i₀, hi₀⟩ := hde
    have hi₀b : 2 * i₀ ≤ L - 1 := by
      have := Finset.mem_range.mp (Finset.mem_filter.mp hi₀).1
      rcases hL with ⟨r, hr⟩; omega
    have he0e : Even (L - 1 - 2 * i₀) := by
      rcases hL with ⟨r, hr⟩
      refine ⟨r - i₀, by omega⟩
    obtain ⟨x, hx⟩ := he0e
    have hu2x : u ^ (2 * x) = -1 := by
      have hxx : 2 * x = L - 1 - 2 * i₀ := by omega
      rw [hxx]; exact hval i₀ hi₀
    have hu4x : u ^ (4 * x) = 1 := by
      rw [show (4 : ℕ) * x = 2 * x * 2 by ring, pow_mul, hu2x]
      simp [pow_two]
    have hord4x : ord ∣ 4 * x := orderOf_dvd_of_pow_eq_one hu4x
    have hord2x : ¬ ord ∣ 2 * x := by
      intro hd
      have h1 : u ^ (2 * x) = 1 :=
        (orderOf_dvd_iff_pow_eq_one).mp hd
      have hne : (1 : (ZMod p)ˣ) ≠ -1 := by
        intro heq
        have hv : (1 : ZMod p) = -1 := by
          simpa using congrArg Units.val heq
        have h2z : (2 : ZMod p) = 0 := by
          have h2 : (1 : ZMod p) + 1 = 0 := by
            have h := congrArg (· + (1 : ZMod p)) hv
            simpa using h
          have h22 : (2 : ZMod p) = 1 + 1 := by norm_num
          rw [h22]; exact h2
        have hp2' : p ∣ 2 :=
          (CharP.cast_eq_zero_iff (ZMod p) p 2).mp
            (by exact_mod_cast h2z)
        rcases (Nat.dvd_prime Nat.prime_two).mp hp2' with h1' | h2'
        · exact hp.ne_one h1'
        · exact hp2 h2'
      exact hne (h1.symm.trans hu2x)
    obtain ⟨q, hq⟩ := hord4x
    have hqodd : Odd q := by
      by_contra hne
      rw [Nat.not_odd_iff_even] at hne
      obtain ⟨q', hq'⟩ := hne
      rw [hq'] at hq
      have h2x : 2 * x = ord * q' := by
        refine Nat.eq_of_mul_eq_mul_left (by norm_num : 0 < 2) ?_
        calc 2 * (2 * x) = 4 * x := by ring
          _ = ord * (q' + q') := hq
          _ = 2 * (ord * q') := by ring
      exact hord2x ⟨q', h2x⟩
    have h4ord : 4 ∣ ord := by
      have hc4q : Nat.Coprime 4 q := by
        have h2q : Nat.Coprime q 2 := Nat.coprime_two_right.mpr hqodd
        have h2q' : Nat.Coprime 2 q := h2q.symm
        have h4q : Nat.Coprime (2 ^ 2) q := h2q'.pow_left 2
        exact h4q
      have h4oq : 4 ∣ q * ord :=
        ⟨x, by rw [mul_comm]; exact hq.symm⟩
      exact hc4q.dvd_of_dvd_mul_left h4oq
    have hord4 : 4 ≤ ord :=
      Nat.le_of_dvd (Nat.pos_of_ne_zero (orderOf_pos _).ne') h4ord
    have h2d : 2 ∣ ord :=
      Nat.dvd_trans (⟨2, rfl⟩ : (2 : ℕ) ∣ 4) h4ord
    have hdiff : ∀ i₁ ∈ dead, ∀ i₂ ∈ dead, i₁ ≤ i₂ →
        ord ∣ 2 * (i₂ - i₁) := by
      intro i₁ h₁ i₂ h₂ hle
      have hpow : u ^ (L - 1 - 2 * i₁ - (L - 1 - 2 * i₂)) = 1 := by
        rw [pow_sub u (by
          have := Finset.mem_range.mp (Finset.mem_filter.mp h₂).1
          omega : L - 1 - 2 * i₂ ≤ L - 1 - 2 * i₁),
          hval i₁ h₁, hval i₂ h₂]
        exact mul_inv_cancel (-1)
      have hd : ord ∣ L - 1 - 2 * i₁ - (L - 1 - 2 * i₂) :=
        orderOf_dvd_of_pow_eq_one hpow
      have heq : L - 1 - 2 * i₁ - (L - 1 - 2 * i₂) =
          2 * (i₂ - i₁) := by
        have h1b : 2 * i₁ ≤ L - 1 := by
          have := Finset.mem_range.mp (Finset.mem_filter.mp h₁).1; omega
        have h2b : 2 * i₂ ≤ L - 1 := by
          have := Finset.mem_range.mp (Finset.mem_filter.mp h₂).1; omega
        omega
      rwa [heq] at hd
    have halve : ∀ x, ord ∣ 2 * x → ord / 2 ∣ x := by
      intro x ⟨c, hc⟩
      refine ⟨c, Nat.eq_of_mul_eq_mul_left two_pos ?_⟩
      calc 2 * x = ord * c := hc
        _ = (2 * (ord / 2)) * c := by rw [Nat.mul_div_cancel' h2d]
        _ = 2 * (ord / 2 * c) := by ring
    have hcong : ∀ {a b : ℕ}, a ∈ dead → b ∈ dead → a ≤ b →
        a / (ord / 2) = b / (ord / 2) → a = b := by
      intro a b ha hb hle hq'
      have hd : ord / 2 ∣ b - a := halve _ (hdiff a ha b hb hle)
      have hm1 : a % (ord / 2) = b % (ord / 2) :=
        (Nat.modEq_iff_dvd' hle).mpr hd
      have h1e := Nat.div_add_mod a (ord / 2)
      have h2e := Nat.div_add_mod b (ord / 2)
      rw [hq', hm1] at h1e
      exact h1e.symm.trans h2e
    have hinj : (↑dead : Set ℕ).InjOn (fun i => i / (ord / 2)) := by
      intro i₁ h₁ i₂ h₂ hq'
      rcases le_total i₁ i₂ with hle | hle
      · exact hcong (Finset.mem_coe.mp h₁) (Finset.mem_coe.mp h₂) hle hq'
      · exact (hcong (Finset.mem_coe.mp h₂) (Finset.mem_coe.mp h₁) hle
          hq'.symm).symm
    have hsub : Set.MapsTo (fun i => i / (ord / 2)) ↑dead
        ↑(Finset.range ((L / 2) / (ord / 2) + 1)) := by
      intro i hi
      have hi2 : i < L / 2 :=
        Finset.mem_range.mp (Finset.mem_filter.mp (Finset.mem_coe.mp hi)).1
      have hord2 : 0 < ord / 2 := by omega
      have : i / (ord / 2) ≤ (L / 2) / (ord / 2) :=
        Nat.div_le_div_right hi2.le
      simpa using Nat.lt_succ_of_le this
    have hcard := Finset.card_le_card_of_injOn _ hsub hinj
    rw [Finset.card_range] at hcard
    have hdiv : (L / 2) / (ord / 2) = L / ord := by
      rw [Nat.div_div_eq_div_mul]
      congr 1
      exact Nat.mul_div_cancel' h2d
    rw [hdiv] at hcard
    have hle4 : L / ord ≤ L / 4 :=
      Nat.div_le_div_left hord4 (by norm_num)
    omega
  · rw [Finset.not_nonempty_iff_eq_empty.mp hde, Finset.card_empty]
    exact Nat.zero_le _

open Classical in

theorem dead_union_bound_even {m L : ℕ} (hm : 0 < m)
    (h10 : Nat.Coprime m 10) (h11 : ¬ 11 ∣ m) (hL : Even L) :
    ((Finset.range (L / 2)).filter (fun i =>
      ¬ IsUnit ((10 ^ i + 10 ^ (L - 1 - i) : ℕ) : ZMod m))).card
      ≤ (m.primeFactors.filter (fun p =>
          orderOf (10 : ZMod p) % 4 = 2)).card * (L / 6 + 1) := by
  classical
  have hm' : m ≠ 0 := hm.ne'
  have hL2 : 2 * (L / 2) = L := Nat.two_mul_div_two_of_even hL
  have hsub : (Finset.range (L / 2)).filter (fun i =>
        ¬ IsUnit ((10 ^ i + 10 ^ (L - 1 - i) : ℕ) : ZMod m))
      ⊆ (m.primeFactors.filter (fun p =>
          orderOf (10 : ZMod p) % 4 = 2)).biUnion (fun p =>
          (Finset.range (L / 2)).filter (fun i =>
            p ∣ 10 ^ i + 10 ^ (L - 1 - i))) := by
    intro i hi
    rw [Finset.mem_filter] at hi
    obtain ⟨hiL, hid⟩ := hi
    have hiLt : i < L / 2 := Finset.mem_range.mp hiL
    have h2i : 2 * i < L := by omega
    have hnc : ¬ Nat.Coprime (10 ^ i + 10 ^ (L - 1 - i)) m := by
      rwa [ZMod.isUnit_iff_coprime] at hid
    obtain ⟨p, hpp, hpw, hpm⟩ :=
      Nat.Prime.not_coprime_iff_dvd.mp hnc
    have hpmem : p ∈ m.primeFactors :=
      Nat.mem_primeFactors.mpr ⟨hpp, hpm, hm'⟩
    have hcop : Nat.Coprime 10 p := (h10.coprime_dvd_left hpm).symm
    have hp2 : p ≠ 2 := by
      intro h2; subst h2
      have hg1 : Nat.gcd m 10 = 1 := h10
      have hdvd : (2 : ℕ) ∣ Nat.gcd m 10 :=
        Nat.dvd_gcd hpm (by norm_num)
      rw [hg1] at hdvd
      omega
    have hp11 : p ≠ 11 := fun h => h11 (h ▸ hpm)
    have hneg : (10 : ZMod p) ^ (L - 1 - 2 * i) = -1 :=
      dead_weight_eq_neg_one_L hpp hcop h2i hpw
    have hL0 : L % 2 = 0 := Nat.even_iff.mp hL
    have hodd : Odd (L - 1 - 2 * i) := by
      apply Nat.odd_iff.mpr
      omega
    set u : (ZMod p)ˣ := ZMod.unitOfCoprime 10 hcop with hu
    have hupow : u ^ (L - 1 - 2 * i) = -1 := by
      apply Units.val_eq_neg_one.mp
      rw [Units.val_pow_eq_pow_val]
      conv_lhs => rw [hu]
      rw [ZMod.coe_unitOfCoprime]
      exact hneg
    have hord := ord_two_mod_four hpp hp2 hodd hupow
    obtain ⟨h2d, hod⟩ := hord
    obtain ⟨a, ha⟩ := h2d
    obtain ⟨b, hb⟩ := hod
    have hord4 : orderOf u % 4 = 2 := by omega
    have hordZ : orderOf (10 : ZMod p) % 4 = 2 := by
      have hcoe : ((u : (ZMod p)ˣ) : ZMod p) = (10 : ZMod p) := by
        rw [hu]; exact ZMod.coe_unitOfCoprime 10 hcop
      rw [← hcoe, orderOf_units]
      exact hord4
    rw [Finset.mem_biUnion]
    exact ⟨p, Finset.mem_filter.mpr ⟨hpmem, hordZ⟩,
      Finset.mem_filter.mpr ⟨hiL, hpw⟩⟩
  calc ((Finset.range (L / 2)).filter (fun i =>
        ¬ IsUnit ((10 ^ i + 10 ^ (L - 1 - i) : ℕ) : ZMod m))).card
      ≤ ((m.primeFactors.filter (fun p =>
          orderOf (10 : ZMod p) % 4 = 2)).biUnion (fun p =>
          (Finset.range (L / 2)).filter (fun i =>
            p ∣ 10 ^ i + 10 ^ (L - 1 - i)))).card :=
        Finset.card_le_card hsub
    _ ≤ ∑ p ∈ m.primeFactors.filter (fun p =>
          orderOf (10 : ZMod p) % 4 = 2),
          ((Finset.range (L / 2)).filter (fun i =>
            p ∣ 10 ^ i + 10 ^ (L - 1 - i))).card :=
        Finset.card_biUnion_le
    _ ≤ ∑ _p ∈ m.primeFactors.filter (fun p =>
          orderOf (10 : ZMod p) % 4 = 2), (L / 6 + 1) := by
        apply Finset.sum_le_sum
        intro p hp
        rw [Finset.mem_filter] at hp
        obtain ⟨hpmem, -⟩ := hp
        obtain ⟨hpp, hpm, -⟩ := Nat.mem_primeFactors.mp hpmem
        exact dead_count_even hpp
          (h10.coprime_dvd_left hpm).symm
          (fun h => h11 (h ▸ hpm)) hL
    _ = (m.primeFactors.filter (fun p =>
          orderOf (10 : ZMod p) % 4 = 2)).card * (L / 6 + 1) := by
        rw [Finset.sum_const, smul_eq_mul]

open Classical in

theorem dead_union_bound_odd {m L : ℕ} (hm : 0 < m)
    (h10 : Nat.Coprime m 10) (hL : Odd L) :
    ((Finset.range (L / 2)).filter (fun i =>
      ¬ IsUnit ((10 ^ i + 10 ^ (L - 1 - i) : ℕ) : ZMod m))).card
      ≤ (m.primeFactors.filter (fun p =>
          4 ∣ orderOf (10 : ZMod p))).card * (L / 4 + 1) := by
  classical
  have hm' : m ≠ 0 := hm.ne'
  have hL0 : L % 2 = 1 := Nat.odd_iff.mp hL
  have hsub : (Finset.range (L / 2)).filter (fun i =>
        ¬ IsUnit ((10 ^ i + 10 ^ (L - 1 - i) : ℕ) : ZMod m))
      ⊆ (m.primeFactors.filter (fun p =>
          4 ∣ orderOf (10 : ZMod p))).biUnion (fun p =>
          (Finset.range (L / 2)).filter (fun i =>
            p ∣ 10 ^ i + 10 ^ (L - 1 - i))) := by
    intro i hi
    rw [Finset.mem_filter] at hi
    obtain ⟨hiL, hid⟩ := hi
    have hiLt : i < L / 2 := Finset.mem_range.mp hiL
    have h2i : 2 * i < L := by omega
    have hnc : ¬ Nat.Coprime (10 ^ i + 10 ^ (L - 1 - i)) m := by
      rwa [ZMod.isUnit_iff_coprime] at hid
    obtain ⟨p, hpp, hpw, hpm⟩ :=
      Nat.Prime.not_coprime_iff_dvd.mp hnc
    have hpmem : p ∈ m.primeFactors :=
      Nat.mem_primeFactors.mpr ⟨hpp, hpm, hm'⟩
    have hcop : Nat.Coprime 10 p := (h10.coprime_dvd_left hpm).symm
    have hp2 : p ≠ 2 := by
      intro h2; subst h2
      have hg1 : Nat.gcd m 10 = 1 := h10
      have hdvd : (2 : ℕ) ∣ Nat.gcd m 10 :=
        Nat.dvd_gcd hpm (by norm_num)
      rw [hg1] at hdvd
      omega
    have hneg : (10 : ZMod p) ^ (L - 1 - 2 * i) = -1 :=
      dead_weight_eq_neg_one_L hpp hcop h2i hpw
    have heven : 2 ∣ L - 1 - 2 * i := by
      have hmod : (L - 1 - 2 * i) % 2 = 0 := by omega
      exact Nat.dvd_of_mod_eq_zero hmod
    set u : (ZMod p)ˣ := ZMod.unitOfCoprime 10 hcop with hu
    have hupow : u ^ (L - 1 - 2 * i) = -1 := by
      apply Units.val_eq_neg_one.mp
      rw [Units.val_pow_eq_pow_val]
      conv_lhs => rw [hu]
      rw [ZMod.coe_unitOfCoprime]
      exact hneg
    have hord : 4 ∣ orderOf u :=
      four_dvd_orderOf hpp hp2 heven hupow
    have hordZ : 4 ∣ orderOf (10 : ZMod p) := by
      have hcoe : ((u : (ZMod p)ˣ) : ZMod p) = (10 : ZMod p) := by
        rw [hu]; exact ZMod.coe_unitOfCoprime 10 hcop
      rw [← hcoe, orderOf_units]
      exact hord
    rw [Finset.mem_biUnion]
    exact ⟨p, Finset.mem_filter.mpr ⟨hpmem, hordZ⟩,
      Finset.mem_filter.mpr ⟨hiL, hpw⟩⟩
  calc ((Finset.range (L / 2)).filter (fun i =>
        ¬ IsUnit ((10 ^ i + 10 ^ (L - 1 - i) : ℕ) : ZMod m))).card
      ≤ ((m.primeFactors.filter (fun p =>
          4 ∣ orderOf (10 : ZMod p))).biUnion (fun p =>
          (Finset.range (L / 2)).filter (fun i =>
            p ∣ 10 ^ i + 10 ^ (L - 1 - i)))).card :=
        Finset.card_le_card hsub
    _ ≤ ∑ p ∈ m.primeFactors.filter (fun p =>
          4 ∣ orderOf (10 : ZMod p)),
          ((Finset.range (L / 2)).filter (fun i =>
            p ∣ 10 ^ i + 10 ^ (L - 1 - i))).card :=
        Finset.card_biUnion_le
    _ ≤ ∑ _p ∈ m.primeFactors.filter (fun p =>
          4 ∣ orderOf (10 : ZMod p)), (L / 4 + 1) := by
        apply Finset.sum_le_sum
        intro p hp
        rw [Finset.mem_filter] at hp
        obtain ⟨hpmem, -⟩ := hp
        obtain ⟨hpp, hpm, -⟩ := Nat.mem_primeFactors.mp hpmem
        exact dead_count_odd hpp
          (h10.coprime_dvd_left hpm).symm hL
    _ = (m.primeFactors.filter (fun p =>
          4 ∣ orderOf (10 : ZMod p))).card * (L / 4 + 1) := by
        rw [Finset.sum_const, smul_eq_mul]

open Classical in

theorem dead_union_bound_even' {m L : ℕ} (hm : 0 < m)
    (h10 : Nat.Coprime m 10) (h11 : ¬ 11 ∣ m) (hL : Even L)
    (D : Finset ℕ) (hD : ∀ i, i ∈ D ↔ i ∈ Finset.range (L / 2) ∧
      ¬ IsUnit ((10 ^ i + 10 ^ (L - 1 - i) : ℕ) : ZMod m)) :
    D.card ≤ (m.primeFactors.filter (fun p =>
        orderOf (10 : ZMod p) % 4 = 2)).card * (L / 6 + 1) := by
  calc D.card ≤ ((Finset.range (L / 2)).filter (fun i =>
          ¬ IsUnit ((10 ^ i + 10 ^ (L - 1 - i) : ℕ) : ZMod m))).card :=
        Finset.card_le_card (fun i hi =>
          Finset.mem_filter.mpr ((hD i).mp hi))
    _ ≤ _ := dead_union_bound_even hm h10 h11 hL

open Classical in

theorem pal_window_extract_composite {m L : ℕ} (hm : 0 < m)
    (h10 : Nat.Coprime m 10) (h11 : ¬ 11 ∣ m)
    (hω : (m.primeFactors.filter (fun p =>
        orderOf (10 : ZMod p) % 4 = 2)).card ≤ 2)
    (hL : Even L) (hbound : 2 * m + 34 ≤ 3 * L) (t : ZMod m) :
    ∃ U : Finset ℕ, ∃ d : ℕ → ℕ,
      (∀ i, d i < 10) ∧ U ⊆ Finset.range (L / 2) ∧
      (∀ i, i ∉ U → d i = 0) ∧
      ((U.sum fun i => d i •
          ((10 ^ i + 10 ^ (L - 1 - i) : ℕ) : ZMod m)) = t) := by
  haveI : NeZero m := ⟨hm.ne'⟩
  set dead := (Finset.range (L / 2)).filter (fun i =>
    ¬ IsUnit ((10 ^ i + 10 ^ (L - 1 - i) : ℕ) : ZMod m)) with hd_def
  set U := (Finset.range (L / 2)).filter (fun i =>
    IsUnit ((10 ^ i + 10 ^ (L - 1 - i) : ℕ) : ZMod m)) with hU_def
  have hdead : dead.card ≤ 2 * (L / 6 + 1) :=
    le_trans (dead_union_bound_even' hm h10 h11 hL dead (fun i => by
      rw [hd_def]; exact Finset.mem_filter))
      (Nat.mul_le_mul_right _ hω)
  have hsd : dead.card = L / 2 - U.card := by
    have hset : dead = Finset.range (L / 2) \ U := by
      ext x
      rw [hd_def, hU_def]
      simp only [Finset.mem_sdiff, Finset.mem_filter, Finset.mem_range]
      tauto
    rw [hset, Finset.card_sdiff_of_subset (Finset.filter_subset _ _),
      Finset.card_range]
  have hL0 : L % 2 = 0 := Nat.even_iff.mp hL
  have hcover : m ≤ 1 + 9 * U.card := by omega
  have hUnit : ∀ i ∈ U,
      IsUnit (((10 ^ i + 10 ^ (L - 1 - i) : ℕ) : ZMod m)) := by
    intro i hi
    exact (Finset.mem_filter.mp hi).2
  set S := U.sum fun i => (Finset.range 10).image
    (· • ((10 ^ i + 10 ^ (L - 1 - i) : ℕ) : ZMod m)) with hS
  have hgrow : min m (1 + 9 * U.card) ≤ S.card :=
    card_sum_intervals hUnit
  have hmin : min m (1 + 9 * U.card) = m := min_eq_left hcover
  have hSm : m ≤ S.card := by
    rw [hmin] at hgrow
    exact hgrow
  have hS_univ : S = Finset.univ := by
    have hcard : S.card = Fintype.card (ZMod m) := by
      have hz : Fintype.card (ZMod m) = m := ZMod.card m
      have hle : S.card ≤ Fintype.card (ZMod m) :=
        Finset.card_le_univ S
      omega
    exact Finset.eq_univ_of_card S hcard
  have hmem : t ∈ S := hS_univ ▸ Finset.mem_univ t
  rw [hS] at hmem
  rw [mem_finset_sum] at hmem
  rcases hmem with ⟨g, hgmem, hgsum⟩
  have hd_ex : ∀ i, ∃ d : ℕ, d < 10 ∧
      (i ∈ U → d • ((10 ^ i + 10 ^ (L - 1 - i) : ℕ) : ZMod m) = g i) ∧
      (i ∉ U → d = 0) := by
    intro i
    by_cases hi : i ∈ U
    · have h := hgmem i hi
      rw [Finset.mem_image] at h
      rcases h with ⟨d0, hd0, hd0eq⟩
      exact ⟨d0, Finset.mem_range.mp hd0, fun _ => hd0eq,
        fun h' => absurd hi h'⟩
    · exact ⟨0, by norm_num, fun h' => absurd h' hi, fun _ => rfl⟩
  choose d hd1 hd2 hd3 using hd_ex
  refine ⟨U, d, fun i => hd1 i,
    fun i hi => (Finset.mem_filter.mp hi).1,
    fun i hi => hd3 i hi, ?_⟩
  have hcongr : (U.sum fun i => d i •
        ((10 ^ i + 10 ^ (L - 1 - i) : ℕ) : ZMod m)) = U.sum g :=
    Finset.sum_congr rfl (fun i hi => hd2 i hi)
  rw [hcongr]
  exact hgsum

open Classical in

theorem dead_union_bound_odd' {m L : ℕ} (hm : 0 < m)
    (h10 : Nat.Coprime m 10) (hL : Odd L)
    (D : Finset ℕ) (hD : ∀ i, i ∈ D ↔ i ∈ Finset.range (L / 2) ∧
      ¬ IsUnit ((10 ^ i + 10 ^ (L - 1 - i) : ℕ) : ZMod m)) :
    D.card ≤ (m.primeFactors.filter (fun p =>
        4 ∣ orderOf (10 : ZMod p))).card * (L / 4 + 1) := by
  calc D.card ≤ ((Finset.range (L / 2)).filter (fun i =>
          ¬ IsUnit ((10 ^ i + 10 ^ (L - 1 - i) : ℕ) : ZMod m))).card :=
        Finset.card_le_card (fun i hi =>
          Finset.mem_filter.mpr ((hD i).mp hi))
    _ ≤ _ := dead_union_bound_odd hm h10 hL


theorem pal_window_extract_odd {m p k L : ℕ} (hp : p.Prime) (hk : 0 < k)
    (hm : m = p ^ k) (h10 : Nat.Coprime m 10)
    (hL : Odd L) (hbound : 4 * m + 50 ≤ 9 * L) (t : ZMod m) :
    ∃ U : Finset ℕ, ∃ d : ℕ → ℕ,
      (∀ i, d i < 10) ∧ U ⊆ Finset.range (L / 2) ∧
      (∀ i, i ∉ U → d i = 0) ∧
      ((U.sum fun i => d i • ((10 ^ i + 10 ^ (L - 1 - i) : ℕ) : ZMod m))
        = t) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hmpos : 0 < m := by
    rw [hm]; exact pow_pos hp.pos k
  haveI : NeZero m := ⟨hmpos.ne'⟩
  have hcop_p : Nat.Coprime 10 p := coprime_10_of_prime_pow hp hk hm h10
  set j := L / 2 with hj
  set w : ℕ → ZMod m := fun i =>
    ((10 ^ i + 10 ^ (L - 1 - i) : ℕ) : ZMod m) with hw
  set dead := (Finset.range j).filter (fun i =>
    p ∣ 10 ^ i + 10 ^ (L - 1 - i)) with hdead_def
  set U := (Finset.range j).filter (fun i =>
    ¬ p ∣ 10 ^ i + 10 ^ (L - 1 - i)) with hU_def
  have hcards : dead.card + U.card = j := by
    rw [hdead_def, hU_def,
      Finset.card_filter_add_card_filter_not (s := Finset.range j)
        (p := fun i => p ∣ 10 ^ i + 10 ^ (L - 1 - i))]
    exact Finset.card_range j
  have hdead_bound : dead.card ≤ L / 4 + 1 := by
    rw [hdead_def, hj]
    exact dead_count_odd hp hcop_p hL
  have hUnit : ∀ i ∈ U, IsUnit (w i) := by
    intro i hi
    have hif := Finset.mem_filter.mp hi
    have hnp := hif.2
    have hc_p : (10 ^ i + 10 ^ (L - 1 - i)).Coprime p := by
      rw [Nat.coprime_comm, hp.coprime_iff_not_dvd]
      exact hnp
    have hc_m : (10 ^ i + 10 ^ (L - 1 - i)).Coprime (p ^ k) :=
      (Nat.coprime_pow_right_iff hk _ _).mpr hc_p
    rw [ZMod.isUnit_iff_coprime]
    exact hm.symm ▸ hc_m
  set S := U.sum fun i => (Finset.range 10).image (· • w i) with hS
  have hgrow : min m (1 + 9 * U.card) ≤ S.card := card_sum_intervals hUnit
  have hLj : L = 2 * j + 1 := by
    rcases hL with ⟨r, hr⟩
    rw [hj]; omega
  have hcover : m ≤ 1 + 9 * U.card := by
    omega
  have hmin : min m (1 + 9 * U.card) = m := min_eq_left hcover
  have hSm : m ≤ S.card := by
    rw [hmin] at hgrow
    exact hgrow
  have hS_univ : S = Finset.univ := by
    have hcard : S.card = Fintype.card (ZMod m) := by
      have hz : Fintype.card (ZMod m) = m := ZMod.card m
      have hle : S.card ≤ Fintype.card (ZMod m) :=
        Finset.card_le_univ S
      omega
    exact Finset.eq_univ_of_card S hcard
  have hmem : t ∈ S := hS_univ ▸ Finset.mem_univ t
  rw [hS] at hmem
  rw [mem_finset_sum] at hmem
  rcases hmem with ⟨g, hgmem, hgsum⟩
  have hd_ex : ∀ i, ∃ d : ℕ, d < 10 ∧ (i ∈ U → d • w i = g i) ∧
      (i ∉ U → d = 0) := by
    intro i
    by_cases hi : i ∈ U
    · have h := hgmem i hi
      rw [Finset.mem_image] at h
      rcases h with ⟨d0, hd0, hd0eq⟩
      exact ⟨d0, Finset.mem_range.mp hd0, fun _ => hd0eq,
        fun h' => absurd hi h'⟩
    · exact ⟨0, by norm_num, fun h' => absurd h' hi, fun _ => rfl⟩
  choose d hd1 hd2 hd3 using hd_ex
  refine ⟨U, d, fun i => hd1 i, fun i hi => (Finset.mem_filter.mp hi).1,
    fun i hi => hd3 i hi, ?_⟩
  have hcongr : (U.sum fun i => d i • w i) = U.sum g :=
    Finset.sum_congr rfl (fun i hi => hd2 i hi)
  rw [hcongr]
  exact hgsum


theorem strict_pal_exists_five_pow_mul {b m p k : ℕ} (hb : 1 ≤ b)
    (hp : p.Prime) (hk : 0 < k) (hm : m = p ^ k)
    (h10 : Nat.Coprime m 10) :
    ∃ N : ℕ, 0 < N ∧ (5 ^ b * m) ∣ N ∧
      (Nat.digits 10 N).length = 5 ^ b * m ∧
      List.Palindrome (Nat.digits 10 N) := by
  obtain ⟨b', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : b ≠ 0)
  have hb' : 1 ≤ b' + 1 := Nat.succ_pos b'
  set n := 5 ^ (b' + 1) * m with hn
  set z := b' + 1 with hz
  set L := n - 2 * z with hL
  have hmodd : Odd m := Nat.coprime_two_right.mp
    (h10.coprime_dvd_right ⟨5, rfl⟩)
  have hm2 : 2 ≤ m := by
    rw [hm]; exact hp.two_le.trans (Nat.le_self_pow hk.ne' p)
  have hm3 : 3 ≤ m := by rcases hmodd with ⟨t, ht⟩; omega
  have hmpos : 0 < m := by omega
  haveI : NeZero m := ⟨hmpos.ne'⟩
  have h5bm : Nat.Coprime (5 ^ (b' + 1)) m :=
    ((h10.coprime_dvd_right ⟨2, rfl⟩).symm).pow_left _
  obtain ⟨e, he5, helo, hehi, heu⟩ := exists_e_five_pow hb'
  have he0 : e ≠ 0 := by
    have hpos : 0 < 10 ^ ((b' + 1) - 1) := by positivity
    omega
  have hez : (Nat.digits 10 e).length = z := by
    rw [hz, Nat.length_digits 10 e (by norm_num) he0]
    have hlog : Nat.log 10 e = (b' + 1) - 1 := by
      apply Nat.log_eq_of_pow_le_of_lt_pow helo
      rw [Nat.sub_add_cancel hb']; exact hehi
    rw [hlog]; exact Nat.sub_add_cancel hb'
  have hpow : 5 ^ (b' + 1) * m = 5 * (5 ^ b' * m) := by
    rw [pow_succ']; ring
  have hnod : Odd n := by
    have h5o : Odd (5 ^ (b' + 1)) := (by norm_num : Odd (5 : ℕ)).pow
    exact h5o.mul hmodd
  have h2zn : 2 * z ≤ n := by
    rw [hz, hn]
    calc 2 * (b' + 1) ≤ 5 ^ (b' + 1) :=
        two_mul_le_pow (by norm_num) _ hb'
      _ = 5 ^ (b' + 1) * 1 := (mul_one _).symm
      _ ≤ 5 ^ (b' + 1) * m := Nat.mul_le_mul_left _ hmpos
  have hLo : Odd L := by
    rcases hnod with ⟨t, ht⟩
    refine ⟨t - z, by rw [hL]; omega⟩
  have hbound : 4 * m + 50 ≤ 9 * L := by
    have hY1 : m ≤ 5 ^ b' * m :=
      Nat.le_mul_of_pos_left _ (pow_pos (by norm_num) b')
    have hY2 : 3 * b' + 3 ≤ 5 ^ b' * m := by
      have h1 : b' + 1 ≤ 5 ^ b' :=
        Nat.succ_le_of_lt
          (Nat.lt_pow_self (by norm_num : (1 : ℕ) < 5) : b' < 5 ^ b')
      calc 3 * b' + 3 = (b' + 1) * 3 := by ring
        _ ≤ 5 ^ b' * m := Nat.mul_le_mul h1 hm3
    have hL' : L = 5 * (5 ^ b' * m) - 2 * (b' + 1) := by
      rw [hL, hn, hz]; rw [hpow]
    omega
  set u : (ZMod m)ˣ := ZMod.unitOfCoprime 10 h10.symm
  set trev : ZMod m :=
    ↑(Nat.ofDigits 10 (Nat.digits 10 e).reverse) * (10 : ZMod m) ^ (n - z)
    with htrev
  set t : ZMod m := -(↑e + trev) * (↑((u ^ z)⁻¹) : ZMod m) with ht
  have htz : (10 : ZMod m) ^ z * t = -(↑e + trev) := by
    have hu10 : (↑u : ZMod m) = 10 := ZMod.coe_unitOfCoprime 10 _
    have h1 : (10 : ZMod m) ^ z * (↑((u ^ z)⁻¹) : ZMod m) = 1 := by
      rw [← hu10, ← Units.val_pow_eq_pow_val]
      exact Units.mul_inv _
    rw [ht, mul_left_comm, h1, mul_one]
  obtain ⟨U, d, hd_lt, hUsub, hd0, hsum⟩ :=
    pal_window_extract_odd hp hk hm h10 hLo hbound t
  push_cast at hsum
  set j := L / 2 with hj
  set Db := (List.range j).map d with hDb
  set W := Db ++ [0] ++ Db.reverse with hW
  have hLj : L = 2 * j + 1 := by
    rcases hLo with ⟨r, hr⟩
    rw [hj]; omega
  have hWlen : W.length = n - 2 * z := by
    rw [hW, List.length_append, List.length_append, List.length_reverse,
      List.length_singleton, hDb, List.length_map, List.length_range]
    omega
  have hWpal : List.Palindrome W :=
    List.Palindrome.iff_reverse_eq.mpr (by
      rw [hW, List.reverse_append, List.reverse_append,
        List.reverse_reverse, List.reverse_singleton,
        ← List.append_assoc])
  have hWd : ∀ x ∈ W, x < 10 := by
    intro x hx
    simp only [hW, hDb, List.mem_append, List.mem_reverse,
      List.mem_singleton, List.mem_map, List.mem_range] at hx
    rcases hx with (⟨i, hi, rfl⟩ | rfl) | ⟨i, hi, rfl⟩
    · exact hd_lt i
    · norm_num
    · exact hd_lt i
  have hMz : Nat.ofDigits (10 : ZMod m) W =
      ∑ i ∈ Finset.range j, (d i : ZMod m) *
        ((10 : ZMod m) ^ i + (10 : ZMod m) ^ (L - 1 - i)) := by
    rw [hW, hDb, ofDigits_append', ofDigits_append',
      ofDigits_singleton', Nat.cast_zero, mul_zero, add_zero,
      ofDigits_zmod_range, ofDigits_zmod_rev,
      List.length_append, List.length_map, List.length_range,
      List.length_singleton, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun i hi => ?_)
    rw [Finset.mem_range] at hi
    calc (d i : ZMod m) * (10 : ZMod m) ^ i
        + (10 : ZMod m) ^ (j + 1) *
          ((d i : ZMod m) * (10 : ZMod m) ^ (j - 1 - i))
        = (d i : ZMod m) * (10 : ZMod m) ^ i
            + (d i : ZMod m) * (10 : ZMod m) ^ (j + 1 + (j - 1 - i))
          := by rw [pow_add]; ring
      _ = (d i : ZMod m) * ((10 : ZMod m) ^ i
            + (10 : ZMod m) ^ (L - 1 - i)) := by
          rw [show j + 1 + (j - 1 - i) = L - 1 - i by omega]; ring
  have hsumU : ∑ i ∈ U, (d i : ZMod m) *
      ((10 : ZMod m) ^ i + (10 : ZMod m) ^ (L - 1 - i)) = t := by
    rw [← hsum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    simp only [nsmul_eq_mul, Nat.cast_add, Nat.cast_pow]
  have hMt : Nat.ofDigits (10 : ZMod m) W = t := by
    rw [hMz]
    have hsp : ∑ i ∈ Finset.range j, (d i : ZMod m) *
        ((10 : ZMod m) ^ i + (10 : ZMod m) ^ (L - 1 - i)) =
        ∑ i ∈ U, (d i : ZMod m) *
          ((10 : ZMod m) ^ i + (10 : ZMod m) ^ (L - 1 - i)) := by
      apply (Finset.sum_subset hUsub ?_).symm
      intro i _ hiU
      rw [hd0 i hiU]; simp
    rw [hsp]; exact hsumU
  obtain ⟨N, hNpos, hNeq, hNlen, hNpal⟩ :=
    strict_pal_sandwich_block (by omega) h2zn hez heu W hWlen
      hWpal hWd
  refine ⟨N, hNpos, ?_, hNlen, hNpal⟩
  have h5a10 : ∀ c : ℕ, b' + 1 ≤ c → 5 ^ (b' + 1) ∣ 10 ^ c := by
    intro c hc
    exact Nat.dvd_trans (Nat.pow_dvd_pow 5 hc)
      (pow_dvd_pow_of_dvd (⟨2, rfl⟩ : (5 : ℕ) ∣ 10) c)
  have hmN : m ∣ N := by
    have hcast : ((N : ℕ) : ZMod m) = 0 := by
      rw [hNeq]; push_cast
      rw [hMt]
      rw [mul_comm t ((10 : ZMod m) ^ z), htz, htrev]
      ring
    exact (CharP.cast_eq_zero_iff (ZMod m) m N).mp hcast
  have h5bN : 5 ^ (b' + 1) ∣ N := by
    rw [hNeq]
    apply Nat.dvd_add
    apply Nat.dvd_add
    · exact dvd_mul_of_dvd_right (h5a10 (n - z) (by omega)) _
    · exact dvd_mul_of_dvd_right (h5a10 z (by omega)) _
    · exact he5
  exact h5bm.mul_dvd_of_dvd_of_dvd h5bN hmN
end DeadCount

end A084013src

section Join

/- Residual-class toolkit. For `n = c * m` with `c = 2 ^ a` or
   `5 ^ b` and `m` coprime to 10, a short palindromic block `w`
   divisible by `c` is repeated `h` times; `h` is a repunit order
   over the base `10 ^ |w|` found by a pigeonhole on remainders,
   so `m` divides the repunit factor of `val (copies w h)`. Two
   such copies sandwiching a run of zeros reach any prescribed
   length `>= c * m`. This discharges the strict-palindrome clause
   for every `n` with `~ 10 | n`, the class the corpus left to its
   covering-system branch. -/

/-- Value of a little-endian decimal word. -/
private def val (w : List ℕ) : ℕ := Nat.ofDigits 10 w

/-- A legal decimal word: palindromic, every entry < 10, nonzero
    head. The little-endian head is the units digit; by mirroring it
    equals the leading digit, so `val w` has exactly `w.length`
    digits. -/
private structure Word (w : List ℕ) : Prop where
  mirror : w.reverse = w
  bounded : ∀ d ∈ w, d < 10
  first : w.head! ≠ 0

private theorem Word.ne_nil {w : List ℕ} (h : Word w) : w ≠ [] := by
  rintro rfl; exact h.first rfl

private theorem Word.digits {w : List ℕ} (h : Word w) :
    Nat.digits 10 (val w) = w := by
  apply Nat.digits_ofDigits 10 (by norm_num) _ h.bounded
  intro hn
  have hl : w.getLast hn = w.head! := by
    calc
      _ = w.reverse.getLast (by simpa only [h.mirror] using hn) := by
          simp only [h.mirror]
      _ = w.head hn := List.getLast_reverse _
      _ = w.head! := by
        cases w with
        | nil => exact False.elim (hn rfl)
        | cons _ _ => rfl
  exact hl ▸ h.first

/-- rep b n : the repunit sum of `b ^ i` over `i < n`. -/
private def rep (b n : ℕ) : ℕ := ∑ i ∈ Finset.range n, b ^ i

private theorem rep_add (b i h : ℕ) :
    rep b (i + h) = rep b i + b ^ i * rep b h := by
  simp [rep, Finset.sum_range_add, pow_add, Finset.mul_sum]

private theorem rep_step (b h : ℕ) : rep b (h + 1) = 1 + b * rep b h := by
  simpa [rep, Nat.add_comm 1 h] using rep_add b 1 h

/-- Pigeonhole: among `m + 1` repunit remainders mod `m` two agree;
    cancelling the common power of the base yields a repunit of
    length `<= m` divisible by `m`, for `gcd m b = 1`. -/
private theorem rep_dvd {b m : ℕ} (hm : 0 < m) (hc : m.Coprime b) :
    ∃ h : ℕ, 0 < h ∧ h ≤ m ∧ m ∣ rep b h := by
  let f := fun j => rep b j % m
  have maps : Set.MapsTo f (Finset.range (m + 1)) (Finset.range m) :=
    fun j _ => Finset.mem_range.mpr (Nat.mod_lt _ hm)
  obtain ⟨u, hu, v, hv, ne, eq⟩ :=
    Finset.exists_ne_map_eq_of_card_lt_of_maps_to
      (show (Finset.range m).card < (Finset.range (m + 1)).card by simp)
      maps
  have he : ∃ i j : ℕ, i < j ∧ j ≤ m ∧ rep b j ≡ rep b i [MOD m] := by
    rcases lt_or_gt_of_ne ne with h | h
    · exact ⟨u, v, h, by have := Finset.mem_range.mp hv; omega, eq.symm⟩
    · exact ⟨v, u, h, by have := Finset.mem_range.mp hu; omega, eq⟩
  obtain ⟨i, j, hij, hjm, hh⟩ := he
  refine ⟨j - i, by omega, by omega, ?_⟩
  have hx := rep_add b i (j - i)
  rw [show i + (j - i) = j by omega] at hx
  rw [hx, Nat.add_comm, Nat.add_modEq_right_iff] at hh
  exact (hc.pow_right i).dvd_of_dvd_mul_left hh

/-- copies w h : the block `w` repeated `h` times. -/
private def copies (w : List ℕ) (h : ℕ) : List ℕ :=
  (List.replicate h w).flatten

private theorem copies_succ (w : List ℕ) (h : ℕ) :
    copies w (h + 1) = w ++ copies w h := by
  simp [copies, List.replicate_succ]

private theorem copies_len (w : List ℕ) (h : ℕ) :
    (copies w h).length = w.length * h := by
  induction h with
  | zero => simp [copies]
  | succ h ih =>
    rw [copies_succ, List.length_append, ih, Nat.mul_succ]; omega

private theorem copies_val (w : List ℕ) (h : ℕ) :
    val (copies w h) = val w * rep (10 ^ w.length) h := by
  induction h with
  | zero => simp [copies, val, rep]
  | succ h ih =>
    rw [copies_succ,
      show val (w ++ copies w h) = val w + 10 ^ w.length * val (copies w h)
        from Nat.ofDigits_append, ih, rep_step]
    ring

private theorem copies_pal {w : List ℕ} (hw : Word w) {h : ℕ}
    (hh : 0 < h) : Word (copies w h) := by
  refine ⟨?_, ?_, ?_⟩
  · simp [copies, List.reverse_flatten, hw.mirror]
  · intro d hd
    obtain ⟨v, hv, hd⟩ := List.mem_flatten.mp hd
    exact hw.bounded d (by simpa only [List.eq_of_mem_replicate hv] using hd)
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hh.ne'
    rw [copies_succ, List.head!_append _ (Word.ne_nil hw)]
    exact hw.first

/-- Two copies of a block sandwiching `g` zeros: a larger word of
    any length `>= 2 * |w|`, still divisible by `n` whenever
    `n | val w`. -/
private theorem padded {n L : ℕ} {w : List ℕ} (hw : Word w)
    (hd : n ∣ val w) (hl : 2 * w.length ≤ L) :
    ∃ w' : List ℕ, Word w' ∧ w'.length = L ∧ n ∣ val w' := by
  let g := L - 2 * w.length
  let z := List.replicate g 0
  let P := w ++ z ++ w
  have hp : Word P := by
    refine ⟨?_, ?_, ?_⟩
    · simp [P, z, List.reverse_append, hw.mirror, List.append_assoc]
    · intro d hdm
      simp only [P, List.mem_append] at hdm
      rcases hdm with (h | h) | h
      · exact hw.bounded _ h
      · have := List.eq_of_mem_replicate h; omega
      · exact hw.bounded _ h
    · rw [show P = w ++ (z ++ w) by simp [P],
        List.head!_append _ (Word.ne_nil hw)]
      exact hw.first
  refine ⟨P, hp, by simp [P, z, g]; omega, ?_⟩
  have hval : val P = val w + 10 ^ (w.length + g) * val w := by
    simp [P, z, val, Nat.ofDigits_append, Nat.ofDigits_replicate_zero,
      pow_add, Nat.mul_assoc]
  rw [hval]; exact dvd_add hd (dvd_mul_of_dvd_right hd _)

/-- Short c : a word of length `<= c / 2` whose value `c` divides. -/
private def Short (c : ℕ) : Prop :=
  ∃ w : List ℕ, Word w ∧ c ∣ val w ∧ 2 * w.length ≤ c

private theorem short_digit {c : ℕ} (hc : 2 ≤ c) (hb : c < 10) :
    Short c := by
  refine ⟨[c],
    ⟨by simp, by simpa using hb, by simpa using (show c ≠ 0 by omega)⟩,
    ?_, by simpa using hc⟩
  simp [val]

/-- For `c = p ^ e` with `p` in {2, 5}: the decimal digits of `c`
    padded out to `e` entries form `low`; `w = low ++ low.reverse`
    is a `2 e`-digit palindromic word, and `c | val w` because the
    reversed half sits above a factor `10 ^ e` divisible by `p ^ e`. -/
private theorem short_pow {p e : ℕ} (h0 : 0 < p) (hp10 : p < 10)
    (hp : p ∣ 10) (he : 0 < e) (hbound : 4 * e ≤ p ^ e)
    (h10 : ¬ 10 ∣ p ^ e) : Short (p ^ e) := by
  let c := p ^ e
  let ds := Nat.digits 10 c
  have cpos : 0 < c := by dsimp only [c]; positivity
  have dsne : ds ≠ [] := Nat.digits_ne_nil_iff_ne_zero.mpr cpos.ne'
  have dshead : ds.head! ≠ 0 := by
    change (Nat.digits 10 c).head! ≠ 0
    rw [Nat.head!_digits (by norm_num)]
    exact fun h => h10 (Nat.dvd_of_mod_eq_zero h)
  have dlen : ds.length ≤ e :=
    (Nat.digits_length_le_iff (by norm_num) c).mpr
      (pow_lt_pow_left₀ hp10 (Nat.zero_le p) he.ne')
  let low := ds ++ List.replicate (e - ds.length) 0
  have llen : low.length = e := by simp [low]; omega
  have lne : low ≠ [] := by
    intro h; rw [h] at llen; simp at llen; omega
  have lhead : low.head! ≠ 0 := by
    dsimp only [low]; rw [List.head!_append _ dsne]; exact dshead
  have lb : ∀ x ∈ low, x < 10 := by
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · exact Nat.digits_lt_base (by norm_num) hx
    · have := List.eq_of_mem_replicate hx; omega
  let w := low ++ low.reverse
  have hw : Word w := by
    refine ⟨by simp [w, List.reverse_append], ?_, ?_⟩
    · intro d hd
      rcases List.mem_append.mp hd with h | h
      · exact lb d h
      · exact lb d (List.mem_reverse.mp h)
    · dsimp only [w]; rw [List.head!_append _ lne]; exact lhead
  have eq : val low = c := by
    simp [low, val, ds, Nat.ofDigits_append_replicate_zero,
      Nat.ofDigits_digits]
  refine ⟨w, hw, ?_, by simp [w, llen]; omega⟩
  rw [show val w = val low + 10 ^ low.length * val low.reverse from
    Nat.ofDigits_append]
  change c ∣ val low + 10 ^ low.length * val low.reverse
  rw [eq, llen]
  exact dvd_add dvd_rfl
    (dvd_mul_of_dvd_left (pow_dvd_pow_of_dvd hp e) _)

private theorem four_pow {e : ℕ} (he : 4 ≤ e) : 4 * e ≤ 2 ^ e := by
  induction e, he using Nat.le_induction with
  | base => decide
  | succ e he ih => rw [pow_succ]; omega

private theorem five_pow {e : ℕ} (he : 1 ≤ e) : 4 * e ≤ 5 ^ e := by
  induction e, he using Nat.le_induction with
  | base => decide
  | succ e he ih => rw [pow_succ]; omega

private theorem not_ten_dvd_two_pow (a : ℕ) : ¬ 10 ∣ 2 ^ a := by
  intro h
  have h5 : (5 : ℕ) ∣ 2 ^ a := (show (5 : ℕ) ∣ 10 by norm_num).trans h
  have := Nat.prime_five.dvd_of_dvd_pow h5
  norm_num at this

private theorem not_ten_dvd_five_pow (b : ℕ) : ¬ 10 ∣ 5 ^ b := by
  intro h
  have h2 : (2 : ℕ) ∣ 5 ^ b := (show (2 : ℕ) ∣ 10 by norm_num).trans h
  have := Nat.prime_two.dvd_of_dvd_pow h2
  norm_num at this

private theorem short_two {a : ℕ} (ha : 1 ≤ a) : Short (2 ^ a) := by
  by_cases h4 : 4 ≤ a
  · exact short_pow (by norm_num) (by norm_num) (by norm_num) (by omega)
      (four_pow h4) (not_ten_dvd_two_pow a)
  · interval_cases a <;> exact short_digit (by decide) (by decide)

private theorem short_five {b : ℕ} (hb : 1 ≤ b) : Short (5 ^ b) :=
  short_pow (by norm_num) (by norm_num) (by norm_num) (by omega)
    (five_pow hb) (not_ten_dvd_five_pow b)

/-- Join: `c * m` divides the value of `copies w h` for a `c`-block
    `w` and `m | rep (10 ^ |w|) h`; padding reaches length `L`. -/
private theorem join {c m L : ℕ} (hm : 0 < m) (hL : c * m ≤ L)
    (s : Short c) (cop : m.Coprime 10) :
    ∃ w' : List ℕ, Word w' ∧ w'.length = L ∧ (c * m) ∣ val w' := by
  obtain ⟨w, hw, hc, le⟩ := s
  obtain ⟨h, hp, hb, hd⟩ := rep_dvd hm (cop.pow_right w.length)
  apply padded (w := copies w h) (copies_pal hw hp)
  · rw [copies_val]; exact Nat.mul_dvd_mul hc hd
  · rw [copies_len, ← Nat.mul_assoc]
    exact (Nat.mul_le_mul le hb).trans hL

/-- Strict existence for `~ 10 | n`: an `n`-digit decimal palindrome
    divisible by `n`. Small `n` by the corpus table; `gcd (n, 10) = 1`
    by the corpus coprime construction; `2 | n` or `5 | n` via the
    repunit join on `n = 2 ^ a * m` resp. `5 ^ b * m`. -/
private theorem strict_exists (n : ℕ) (hn : 1 ≤ n) (h10 : ¬ 10 ∣ n) :
    ∃ N : ℕ, 0 < N ∧ n ∣ N ∧ (Nat.digits 10 N).length = n ∧
      List.Palindrome (Nat.digits 10 N) := by
  rcases le_total n 23 with h23 | h23
  · exact wit013_spec n hn h23 h10
  by_cases hcop : Nat.Coprime n 10
  · exact strict_pal_exists_coprime hn hcop
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  set a := padicValNat 2 n with ha
  set q1 := Nat.divMaxPow n 2 with hq1d
  set b := padicValNat 5 q1 with hb
  set m := Nat.divMaxPow q1 5 with hm
  have hn0 : n ≠ 0 := by omega
  have hq1 : q1 * 2 ^ a = n := Nat.divMaxPow_mul_pow_padicValNat 2 n
  have hmq : m * 5 ^ b = q1 := Nat.divMaxPow_mul_pow_padicValNat 5 q1
  have hq10 : q1 ≠ 0 := by
    intro h; rw [h, zero_mul] at hq1; exact hn0 hq1.symm
  have hdecomp : n = 2 ^ a * 5 ^ b * m := by
    rw [← hmq] at hq1; rw [← hq1]; ring
  have h2q1 : ¬ 2 ∣ q1 := Nat.not_dvd_divMaxPow (by norm_num) hn0
  have h5m : ¬ 5 ∣ m := Nat.not_dvd_divMaxPow (by norm_num) hq10
  have hmq1 : m ∣ q1 := ⟨5 ^ b, hmq.symm⟩
  have hq1n : q1 ∣ n := ⟨2 ^ a, hq1.symm⟩
  have h2m : ¬ 2 ∣ m := fun h => h2q1 (h.trans hmq1)
  have h2c : Nat.Coprime m 2 :=
    ((Nat.prime_two.coprime_iff_not_dvd).mpr h2m).symm
  have h5c : Nat.Coprime m 5 :=
    ((Nat.prime_five.coprime_iff_not_dvd).mpr h5m).symm
  have hc10 : Nat.Coprime m 10 := by
    have hc : Nat.Coprime m (2 * 5) := Nat.Coprime.mul_right h2c h5c
    rwa [show (2 : ℕ) * 5 = 10 from rfl] at hc
  have hm0 : m ≠ 0 := by
    intro hmz; rw [hmz, zero_mul] at hmq; exact hq10 hmq.symm
  have hmpos : 0 < m := Nat.pos_of_ne_zero hm0
  have ofWord : ∀ w : List ℕ, Word w → n ∣ val w → w.length = n →
      ∃ N : ℕ, 0 < N ∧ n ∣ N ∧ (Nat.digits 10 N).length = n ∧
        List.Palindrome (Nat.digits 10 N) := by
    intro w hw hd hwl
    have hdw : Nat.digits 10 (val w) = w := hw.digits
    have hne : Nat.digits 10 (val w) ≠ [] := hdw.symm ▸ hw.ne_nil
    exact ⟨val w, Nat.pos_of_ne_zero
      (Nat.digits_ne_nil_iff_ne_zero.mp hne), hd,
      by rw [hdw]; exact hwl,
      by rw [hdw]; exact List.Palindrome.iff_reverse_eq.mpr hw.mirror⟩
  have hd25 : 2 ∣ n ∨ 5 ∣ n := by
    by_contra h
    push_neg at h
    exact hcop (by
      have h2n : Nat.Coprime n 2 :=
        ((Nat.prime_two.coprime_iff_not_dvd).mpr h.1).symm
      have h5n : Nat.Coprime n 5 :=
        ((Nat.prime_five.coprime_iff_not_dvd).mpr h.2).symm
      have hc : Nat.Coprime n (2 * 5) := Nat.Coprime.mul_right h2n h5n
      rwa [show (2 : ℕ) * 5 = 10 from rfl] at hc)
  rcases hd25 with h2n | h5n
  · -- n = 2 ^ a * m
    have hb0 : b = 0 :=
      padicValNat.eq_zero_of_not_dvd (fun hd =>
        h10 ((by norm_num : Nat.Coprime 2 5).mul_dvd_of_dvd_of_dvd h2n
          (hd.trans hq1n)))
    have ha1 : 1 ≤ a := one_le_padicValNat_of_dvd hn0 h2n
    have hnm : n = 2 ^ a * m := by rw [hdecomp, hb0]; ring
    obtain ⟨w, hw, hwl, hdvd⟩ :=
      join hmpos (le_of_eq hnm.symm) (short_two ha1) hc10
    exact ofWord w hw (hnm.symm ▸ hdvd) hwl
  · -- n = 5 ^ b * m
    have ha0 : a = 0 :=
      padicValNat.eq_zero_of_not_dvd (fun hd =>
        h10 ((by norm_num : Nat.Coprime 5 2).mul_dvd_of_dvd_of_dvd h5n
          hd))
    have h5q1 : 5 ∣ q1 := by
      have hq : q1 = n := by
        have h := hq1; rw [ha0] at h; simpa using h
      rwa [hq]
    have hb1 : 1 ≤ b := one_le_padicValNat_of_dvd hq10 h5q1
    have hnm : n = 5 ^ b * m := by rw [hdecomp, ha0]; ring
    obtain ⟨w, hw, hwl, hdvd⟩ :=
      join hmpos (le_of_eq hnm.symm) (short_five hb1) hc10
    exact ofWord w hw (hnm.symm ▸ hdvd) hwl

/-- Witness for the catalogue predicate: `A084013_relaxed` for
    `10 | n` (trailing zeros tolerated), `strict_exists` otherwise.
    The `· == 0` / `· = 0` predicates coincide on naturals. -/
private theorem witness (n : ℕ) (hn : 0 < n) :
    ∃ x : ℕ, OMA.S_oeis_a084013.qualifies n x := by
  have hpred : (fun d : ℕ => (d == 0)) = fun d => decide (d = 0) := by
    funext d; rcases d with _ | d <;> rfl
  by_cases h10 : 10 ∣ n
  · obtain ⟨N, hNpos, hdvd, hlen, hrel⟩ :=
      A084013_relaxed n hn h10
    refine ⟨N, hNpos, hdvd, hlen, ?_⟩
    rw [if_pos h10]
    show ((Nat.digits 10 N).dropWhile (· == 0)).reverse =
      (Nat.digits 10 N).dropWhile (· == 0)
    rw [hpred]
    exact List.Palindrome.iff_reverse_eq.mp hrel
  · obtain ⟨N, hNpos, hdvd, hlen, hstr⟩ := strict_exists n hn h10
    refine ⟨N, hNpos, hdvd, hlen, ?_⟩
    rw [if_neg h10]
    exact List.Palindrome.iff_reverse_eq.mp hstr

private theorem main_pos (n : ℕ) (hn : 0 < n) :
    OMA.S_oeis_a084013.a n ≠ 0 := by
  classical
  have h := witness n hn
  rw [OMA.S_oeis_a084013.a, dif_pos h]
  exact (Nat.find_spec h).1.ne'

end Join

end OMA.A084013Port

/-- `main_pos` is the union of the two cases of `witness`: for every
    `0 < n` some `x` satisfies `qualifies n x`, so `a n = Nat.find`
    of that existence is positive, i.e. no entry of A084013 is 0. -/
theorem OMA.solution : type_of% @OMA.S_oeis_a084013.main := by
  intro n hn
  exact OMA.A084013Port.main_pos n hn
