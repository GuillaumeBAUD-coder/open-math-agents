import OMAReductions.R_Erdos1191_erdos_1191_parts_i_R1

/-!
# Dyadic counts in a finite Sidon set

Partition the positive integers into consecutive buckets of width `w`. Distinct
ordered pairs in the same bucket have distinct nonzero signed differences, all
between `-w` and `w`. This bounds the sum of the squared bucket sizes.
Grouping the buckets in ranges with endpoints `4^j` then bounds the sum of
the squared normalized prefix counts by Cauchy–Schwarz.
-/

open Finset

private def bucket (s : Finset ℕ) (w i : ℕ) := s.filter fun x => (x-1)/w = i

private lemma bucket_sum (s : Finset ℕ) {w : ℕ} (hw : 0 < w) (hpos : ∀ x ∈ s, 0 < x)
    (b : ℕ) :
    ∑ i ∈ range b, (bucket s w i).card = (s.filter (· ≤ b*w)).card := by
  let t := s.filter (· ≤ b*w)
  have ht : ∀ x ∈ t, (x-1)/w ∈ range b := by
    intro x hx
    obtain ⟨hx, hxb⟩ := mem_filter.mp hx
    rw [mem_range, Nat.div_lt_iff_lt_mul hw]
    have := hpos x hx
    omega
  rw [card_eq_sum_card_fiberwise (s := t) ht]
  apply sum_congr rfl
  intro i hi
  congr 1
  ext x
  simp only [bucket, t, mem_filter]
  constructor
  · rintro ⟨hx, he⟩
    have hdiv : (x-1)/w < b := he ▸ mem_range.mp hi
    have := (Nat.div_lt_iff_lt_mul hw).mp hdiv
    exact ⟨⟨hx, by omega⟩, he⟩
  · tauto

private lemma bucket_energy (s : Finset ℕ) {w : ℕ} (hw : 0 < w)
    (hpos : ∀ x ∈ s, 0 < x) (hs : IsSidon (s : Set ℕ)) (b : ℕ) :
    ∑ i ∈ range b, (bucket s w i).card ^ 2 ≤ s.card + 2*w+1 := by
  let T := (range b).sigma fun i => bucket s w i ×ˢ bucket s w i
  let label (u : Σ _ : ℕ, ℕ × ℕ) : ℕ ⊕ ℤ :=
    if u.2.1 = u.2.2 then Sum.inl u.2.1 else Sum.inr ((u.2.1 : ℤ) - u.2.2)
  let U := s.disjSum (Icc (-(w : ℤ)) w)
  have maps : Set.MapsTo label (T : Set _) (U : Set _) := by
    rintro ⟨i,a,c⟩ h
    simp only [T, mem_coe, mem_sigma, mem_product, bucket, mem_filter] at h
    change (if a = c then Sum.inl a else Sum.inr ((a : ℤ)-c)) ∈ U
    split_ifs with he
    · exact inl_mem_disjSum.mpr h.2.1.1
    · apply inr_mem_disjSum.mpr
      have ha := Nat.mod_add_div (a-1) w
      have hc := Nat.mod_add_div (c-1) w
      rw [h.2.1.2] at ha
      rw [h.2.2.2] at hc
      have := Nat.mod_lt (a-1) hw
      have := Nat.mod_lt (c-1) hw
      have := hpos a h.2.1.1
      have := hpos c h.2.2.1
      exact mem_Icc.mpr ⟨by omega, by omega⟩
  have inj : Set.InjOn label (T : Set _) := by
    rintro ⟨i,a,c⟩ hu ⟨j,d,e⟩ hv heq
    simp only [T, mem_coe, mem_sigma, mem_product, bucket, mem_filter] at hu hv
    change (if a = c then Sum.inl a else Sum.inr ((a : ℤ)-c)) =
      (if d = e then Sum.inl d else Sum.inr ((d : ℤ)-e)) at heq
    split_ifs at heq with h1 h2 h2
    · simp only [Sum.inl.injEq] at heq
      obtain rfl : a = d := heq
      obtain rfl : i = j := hu.2.1.2.symm.trans hv.2.1.2
      congr 2 <;> omega
    · simp only [Sum.inr.injEq] at heq
      have hsum : a + e = d + c := by omega
      obtain ⟨had, hec⟩ | ⟨hac, _⟩ :=
        hs a hu.2.1.1 d hv.2.1.1 e hv.2.2.1 c hu.2.2.1 hsum
      · subst d; subst e
        obtain rfl : i = j := hu.2.1.2.symm.trans hv.2.1.2
        rfl
      · contradiction
  have h := card_le_card_of_injOn label maps inj
  simp only [T, U, card_sigma, card_product, card_disjSum, Int.card_Icc, ← sq] at h
  omega

private noncomputable def scaled (f : ℕ → ℝ) (j : ℕ) : ℝ :=
  (∑ i ∈ range (4^j), f i) / 2^j

private lemma scale_energy (f : ℕ → ℝ) (j : ℕ) :
    (∑ k ∈ range (j+1), (scaled f k)^2) + (scaled f j)^2 ≤
      4 * ∑ i ∈ range (4^j), (f i)^2 := by
  induction j with
  | zero => simp [scaled]; nlinarith [sq_nonneg (f 0)]
  | succ j ih =>
    let u := Ico (4^j) (4^(j+1))
    let d := (∑ i ∈ u, f i) / (2:ℝ)^(j+1)
    have hab : 4^j ≤ (4:ℕ)^(j+1) := by rw [pow_succ]; omega
    have hsplit (g : ℕ → ℝ) : ∑ i ∈ range (4^j), g i + ∑ i ∈ u, g i =
        ∑ i ∈ range (4^(j+1)), g i := sum_range_add_sum_Ico _ hab
    have hs : scaled f (j+1) = scaled f j / 2 + d := by
      unfold scaled d
      rw [← hsplit, pow_succ]
      field_simp
    have hcs := sq_sum_le_card_mul_sum_sq (s := u) (f := f)
    have hcard : (u.card : ℝ) ≤ (2^(j+1) : ℝ)^2 := by
      rw [← pow_mul, mul_comm (j+1) 2, pow_mul]
      norm_num
      exact_mod_cast (show u.card ≤ 4^(j+1) by simp [u])
    have hd : d^2 ≤ ∑ i ∈ u, (f i)^2 := by
      unfold d
      rw [div_pow, div_le_iff₀ (by positivity)]
      calc
        _ ≤ _ := hcs
        _ ≤ _ := mul_le_mul_of_nonneg_right hcard (by positivity)
        _ = _ := mul_comm _ _
    rw [sum_range_succ, ← hsplit, hs]
    nlinarith [sq_nonneg (scaled f j / 2 - d)]

private lemma four_pow (j : ℕ) : (4:ℕ)^j = 2^(2*j) := by rw [pow_mul]; norm_num

theorem OMA.solution : OMA.R_Erdos1191_erdos_1191_parts_i_R1.H1 := by
  intro R s hR hsub hs
  let M := 2^R
  let J := R / 2
  have hM : 0 < M := pow_pos (by decide) _
  have hpos (x) (hx : x ∈ s) : 0 < x := (hsub hx).1
  have hupper (x) (hx : x ∈ s) : x ≤ M^2 := by
    simpa [M, ← pow_mul, mul_comm R 2] using (hsub hx).2
  have hcard : s.card ≤ 3*M := by
    have he := bucket_energy s (w := M^2) (by positivity) hpos hs 1
    have hb := bucket_sum s (w := M^2) (by positivity) hpos 1
    simp only [sum_range_one, one_mul, filter_eq_self.mpr hupper] at hb
    simp only [sum_range_one, hb] at he
    by_contra! hc
    have he' : (s.card:ℤ)^2 ≤ s.card + 2*(M:ℤ)^2+1 := by exact_mod_cast he
    have h1 : 0 ≤ (s.card:ℤ)-3*M-1 := by omega
    have h2 : 0 ≤ (s.card:ℤ)+3*M := by positivity
    nlinarith [mul_nonneg h1 h2, (show (1:ℤ) ≤ M by exact_mod_cast hM)]
  let f (i : ℕ) := ((bucket s M i).card : ℝ)
  have he := bucket_energy s hM hpos hs (4^J)
  have he' : ∑ i ∈ range (4^J), (f i)^2 ≤ 6*(M:ℝ) := by
    dsimp [f]
    exact_mod_cast (show ∑ i ∈ range (4^J), (bucket s M i).card^2 ≤ 6*M by omega)
  have henergy : ∑ j ∈ range (J+1), (scaled f j)^2 ≤ 24*(M:ℝ) := by
    linarith [scale_energy f J, sq_nonneg (scaled f J)]
  by_contra! hn
  have hterm (j : ℕ) (hj : j ∈ range (J+1)) :
      256*(M:ℝ) ≤ (scaled f j)^2 * R := by
    have hsmall : 2*j ≤ R := by simp only [mem_range, J] at hj; omega
    have hk : R+2*j ∈ Set.Icc R (2*R) := ⟨by omega, by omega⟩
    have h := hn (R+2*j) hk
    let c := (s.filter (· ≤ 2^(R+2*j))).card
    have hc : 512*(M*4^j) < c^2 * (R+2*j) := by
      simpa [c,M,pow_add,← four_pow] using h
    have hc' : 256*(M*4^j) ≤ c^2*R := by
      have hm := Nat.mul_le_mul_left (c^2) (show R+2*j ≤ 2*R by omega)
      nlinarith
    have hsum : ∑ i ∈ range (4^j), f i = (c:ℝ) := by
      dsimp only [f]
      have hh := bucket_sum s hM hpos (4^j)
      have hx : 4^j*M = 2^(R+2*j) := by rw [pow_add, ← four_pow, mul_comm]
      rw [hx] at hh
      exact_mod_cast hh
    rw [scaled, hsum, div_pow, div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
    have hpow : ((2:ℝ)^j)^2 = 4^j := by rw [← pow_mul, mul_comm j 2,pow_mul]; norm_num
    rw [hpow, mul_assoc]
    exact_mod_cast hc'
  have ht := sum_le_sum hterm
  simp only [sum_const, card_range, nsmul_eq_mul, ← sum_mul] at ht
  have hj : (R:ℝ) ≤ 2*((J+1:ℕ):ℝ) := by exact_mod_cast (show R ≤ 2*(J+1) by dsimp [J]; omega)
  have hu := mul_le_mul_of_nonneg_right henergy (Nat.cast_nonneg R)
  have hl := mul_le_mul_of_nonneg_left hj (show 0 ≤ 128*(M:ℝ) by positivity)
  nlinarith [mul_pos (show 0 < (M:ℝ) by exact_mod_cast hM)
    (show 0 < (R:ℝ) by exact_mod_cast (show 0 < R by omega))]
