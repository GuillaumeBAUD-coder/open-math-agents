import FormalConjectures.ErdosProblems.«1100»

-- Problem: Erdős Problem 1100, part (ii) (answer no; Erdős and Tenenbaum 1989, Theorem 4)
-- Upstream: formal-conjectures FormalConjectures/ErdosProblems/1100.lean (declaration Erdos1100.erdos_1100.parts.ii)

/-!
# Many coprime consecutive divisors

Following the argument of Erdős and Tenenbaum for their Theorem 4. Let `n` be squarefree and
`d_0 < d_1 < ⋯` its divisors. For a consecutive pair `(d_i, d_{i+1})` with `g = gcd > 1`, the
divisor `d_i / g` has a successor at most `d_{i+1} / g`; iterating gives an index `h` with
`(d_h, d_{h+1}) = 1`, `d_h ∣ d_i` and `d_{h+1}/d_h ≤ d_{i+1}/d_i`. The indices sent to a fixed `h`
are at most `2^(k - ω(d_h))` (they are multiples of `d_h`) and at most `1 + (d_h + 1) log n`
(their divisors grow by the factor `1 + 1/d_h`). With `n` the primorial of `P`, splitting on
`ω(d_h) ≥ r` gives `2^k - 1 ≤ τ_⊥(n) (2^(k-r) + 1 + (P^r + 1) log n)`. Choosing
`r ≈ k log 2 / (2 log P)` and Chebyshev's bound `π(P) ≫ P / log P` gives
`τ_⊥(n) ≥ exp((log n)^(1/8))` for all large `P`.
-/

open Real
namespace E1100

/-- facts about the sorted divisors -/
structure Sorted (n N : ℕ) (a : ℕ → ℕ) : Prop where
  dvd : ∀ i < N, a i ∣ n
  mono : ∀ i j, i < j → j < N → a i < a j
  surj : ∀ x, x ∣ n → ∃ j < N, a j = x
  next : ∀ k x, x ∣ n → a k < x → a (k + 1) ≤ x
  npos : 0 < n

lemma Sorted.pos {n N : ℕ} {a : ℕ → ℕ} (hs : Sorted n N a) {i : ℕ} (hi : i < N) : 0 < a i :=
  Nat.pos_of_dvd_of_pos (hs.dvd i hi) hs.npos

lemma exists_good {n N : ℕ} {a : ℕ → ℕ} (hs : Sorted n N a) :
    ∀ i, i + 1 < N → ∃ h, h + 1 < N ∧ Nat.Coprime (a h) (a (h + 1)) ∧ a h ∣ a i ∧
      a (h + 1) * a i ≤ a (i + 1) * a h := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro hi
    by_cases hc : Nat.Coprime (a i) (a (i + 1))
    · exact ⟨i, hi, hc, dvd_rfl, le_rfl⟩
    set g := Nat.gcd (a i) (a (i + 1)) with hg
    have hai := hs.pos (show i < N by omega)
    have hai1 := hs.pos hi
    have hlt := hs.mono i (i + 1) (by omega) hi
    have hg1 : 1 < g := by
      have : g ≠ 1 := hc
      have : 0 < g := Nat.gcd_pos_of_pos_left _ hai
      omega
    have hgi : g ∣ a i := Nat.gcd_dvd_left _ _
    have hgi1 : g ∣ a (i + 1) := Nat.gcd_dvd_right _ _
    obtain ⟨u, hu⟩ := hgi
    obtain ⟨v, hv⟩ := hgi1
    have hupos : 0 < u := by
      rcases Nat.eq_zero_or_pos u with h | h
      · rw [h, mul_zero] at hu; omega
      · exact h
    have hudvd : u ∣ n := dvd_trans (Dvd.intro_left g hu.symm) (hs.dvd i (by omega))
    have hvdvd : v ∣ n := dvd_trans (Dvd.intro_left g hv.symm) (hs.dvd (i + 1) hi)
    obtain ⟨j, hjN, hj⟩ := hs.surj u hudvd
    have hult : u < a i := by rw [hu]; nlinarith
    have hji : j < i := by
      by_contra hcon
      rcases (show i = j ∨ i < j by omega) with h | h
      · subst h; omega
      · have := hs.mono i j h hjN; omega
    have huv : u < v := by
      rw [hu, hv] at hlt; exact Nat.lt_of_mul_lt_mul_left hlt
    have hnext : a (j + 1) ≤ v := hs.next j v hvdvd (by rw [hj]; exact huv)
    obtain ⟨h, hh1, hcop, hdvd, hratio⟩ := ih j hji (by omega)
    refine ⟨h, hh1, hcop, ?_, ?_⟩
    · rw [hu, ← hj]; exact Dvd.dvd.mul_left hdvd g
    · -- a(h+1) * a j ≤ a(j+1) * a h, and a(j+1) * a i ≤ a(i+1) * a j
      have hah := hs.pos (show h < N by omega)
      have hajpos : 0 < a j := hs.pos hjN
      have h2 : a (j + 1) * a i ≤ a (i + 1) * a j := by
        rw [hu, hv, hj]; nlinarith
      have h3 : a (h + 1) * a i * a j ≤ a (i + 1) * a h * a j := by
        calc a (h + 1) * a i * a j = (a (h + 1) * a j) * a i := by ring
          _ ≤ (a (j + 1) * a h) * a i := Nat.mul_le_mul_right _ hratio
          _ = (a (j + 1) * a i) * a h := by ring
          _ ≤ (a (i + 1) * a j) * a h := Nat.mul_le_mul_right _ h2
          _ = a (i + 1) * a h * a j := by ring
      exact Nat.le_of_mul_le_mul_right h3 hajpos

lemma chain_pow (S : Finset ℕ) (f : ℕ → ℝ) (c : ℝ) (hc : 1 ≤ c)
    (hf : ∀ x ∈ S, ∀ y ∈ S, x < y → c * f x ≤ f y) (hpos : ∀ x ∈ S, 0 < f x) (hne : S.Nonempty) :
    c ^ (S.card - 1) * f (S.min' hne) ≤ f (S.max' hne) := by
  induction S using Finset.induction_on_max with
  | empty => exact absurd hne (by simp)
  | insert m S hlt ih =>
    by_cases hS : S.Nonempty
    · have hmS : m ∉ S := fun hm => lt_irrefl _ (hlt m hm)
      have hmin : (insert m S).min' hne = S.min' hS := by
        apply le_antisymm
        · exact Finset.min'_le _ _ (Finset.mem_insert_of_mem (Finset.min'_mem _ _))
        · apply Finset.le_min'; intro y hy
          rcases Finset.mem_insert.mp hy with rfl | hy
          · exact (Finset.min'_le _ _ (Finset.min'_mem S hS)).trans
              (hlt _ (Finset.min'_mem S hS)).le
          · exact Finset.min'_le _ _ hy
      have hmax : (insert m S).max' hne = m := by
        apply le_antisymm
        · apply Finset.max'_le; intro y hy
          rcases Finset.mem_insert.mp hy with rfl | hy
          · exact le_rfl
          · exact (hlt y hy).le
        · exact Finset.le_max' _ _ (Finset.mem_insert_self _ _)
      have ih' := ih (fun x hx y hy hxy => hf x (Finset.mem_insert_of_mem hx) y
        (Finset.mem_insert_of_mem hy) hxy) (fun x hx => hpos x (Finset.mem_insert_of_mem hx)) hS
      rw [hmin, hmax, Finset.card_insert_of_notMem hmS]
      have hcard : S.card + 1 - 1 = (S.card - 1) + 1 := by
        have := hS.card_pos; omega
      rw [hcard, pow_succ]
      have hstep : c * f (S.max' hS) ≤ f m :=
        hf _ (Finset.mem_insert_of_mem (Finset.max'_mem _ _)) m (Finset.mem_insert_self _ _)
          (hlt _ (Finset.max'_mem _ _))
      have h0 : 0 ≤ c := by linarith
      calc c ^ (S.card - 1) * c * f (S.min' hS) = c * (c ^ (S.card - 1) * f (S.min' hS)) := by ring
        _ ≤ c * f (S.max' hS) := mul_le_mul_of_nonneg_left ih' h0
        _ ≤ f m := hstep
    · have hS0 : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hS
      subst hS0
      simp

lemma card_le_of_chain (S : Finset ℕ) (f : ℕ → ℝ) (c M : ℝ) (hc : 1 < c) (hM : 1 ≤ M)
    (hf : ∀ x ∈ S, ∀ y ∈ S, x < y → c * f x ≤ f y) (hlow : ∀ x ∈ S, 1 ≤ f x)
    (hup : ∀ x ∈ S, f x ≤ M) :
    (S.card : ℝ) ≤ 1 + Real.log M / Real.log c := by
  have hlc : 0 < Real.log c := Real.log_pos hc
  have hlM : 0 ≤ Real.log M := Real.log_nonneg hM
  rcases S.eq_empty_or_nonempty with h | hne
  · subst h; simp; positivity
  have key := chain_pow S f c hc.le hf (fun x hx => by linarith [hlow x hx]) hne
  have h1 := hlow _ (Finset.min'_mem S hne)
  have h2 := hup _ (Finset.max'_mem S hne)
  have hcp : c ^ (S.card - 1) ≤ M := by
    have : c ^ (S.card - 1) * 1 ≤ c ^ (S.card - 1) * f (S.min' hne) :=
      mul_le_mul_of_nonneg_left h1 (by positivity)
    linarith
  have hlog := Real.log_le_log (by positivity) hcp
  rw [Real.log_pow] at hlog
  have hcard : ((S.card - 1 : ℕ) : ℝ) = (S.card : ℝ) - 1 := by
    have := hne.card_pos; push_cast [Nat.cast_sub (show 1 ≤ S.card by omega)]; ring
  rw [hcard] at hlog
  rw [← sub_le_iff_le_add', le_div_iff₀ hlc]
  linarith

lemma sqfree_count (n m : ℕ) (hn : Squarefree n) (hmn : m ∣ n) :
    ((n.divisors.filter (fun d => m ∣ d)).card : ℕ) ≤ 2 ^ (n.primeFactors.card - m.primeFactors.card) := by
  have hn0 : n ≠ 0 := hn.ne_zero
  have hsub : m.primeFactors ⊆ n.primeFactors := Nat.primeFactors_mono hmn hn0
  calc (n.divisors.filter (fun d => m ∣ d)).card
      ≤ (n.primeFactors \ m.primeFactors).powerset.card := by
        apply Finset.card_le_card_of_injOn (fun d => d.primeFactors \ m.primeFactors)
        · intro d hd
          simp only [Finset.coe_filter, Set.mem_ofPred_eq, Nat.mem_divisors] at hd
          simp only [Finset.coe_powerset, Set.mem_preimage, Set.mem_powerset_iff, Finset.coe_subset]
          exact Finset.sdiff_subset_sdiff (Nat.primeFactors_mono hd.1.1 hn0) le_rfl
        · intro d hd e he hde
          simp only [Finset.coe_filter, Set.mem_ofPred_eq, Nat.mem_divisors] at hd he
          have hd0 : d ≠ 0 := ne_zero_of_dvd_ne_zero hn0 hd.1.1
          have he0 : e ≠ 0 := ne_zero_of_dvd_ne_zero hn0 he.1.1
          have hsd : Squarefree d := hn.squarefree_of_dvd hd.1.1
          have hse : Squarefree e := hn.squarefree_of_dvd he.1.1
          have h1 : d.primeFactors = e.primeFactors := by
            have hmd : m.primeFactors ⊆ d.primeFactors := Nat.primeFactors_mono hd.2 hd0
            have hme : m.primeFactors ⊆ e.primeFactors := Nat.primeFactors_mono he.2 he0
            simp only at hde
            rw [← Finset.sdiff_union_of_subset hmd, ← Finset.sdiff_union_of_subset hme, hde]
          rw [← Nat.prod_primeFactors_of_squarefree hsd, ← Nat.prod_primeFactors_of_squarefree hse, h1]
    _ = 2 ^ (n.primeFactors.card - m.primeFactors.card) := by
        rw [Finset.card_powerset, Finset.card_sdiff_of_subset hsub]

lemma sqfree_le_pow (m P : ℕ) (hm : Squarefree m) (hP : ∀ p ∈ m.primeFactors, p ≤ P) :
    m ≤ P ^ m.primeFactors.card := by
  conv_lhs => rw [← Nat.prod_primeFactors_of_squarefree hm]
  exact Finset.prod_le_pow_card _ _ _ hP

open Classical in
noncomputable def psi {n N : ℕ} {a : ℕ → ℕ} (hs : Sorted n N a) (i : ℕ) : ℕ :=
  if hi : i + 1 < N then Classical.choose (exists_good hs i hi) else 0

lemma psi_spec {n N : ℕ} {a : ℕ → ℕ} (hs : Sorted n N a) (i : ℕ) (hi : i + 1 < N) :
    psi hs i + 1 < N ∧ Nat.Coprime (a (psi hs i)) (a (psi hs i + 1)) ∧ a (psi hs i) ∣ a i ∧
      a (psi hs i + 1) * a i ≤ a (i + 1) * a (psi hs i) := by
  unfold psi; rw [dif_pos hi]; exact Classical.choose_spec (exists_good hs i hi)

lemma fiber_chain {n N : ℕ} {a : ℕ → ℕ} (hs : Sorted n N a) (h : ℕ) (hh : h + 1 < N) :
    ((((Finset.range (N - 1)).filter (fun i => psi hs i = h)).card : ℕ) : ℝ) ≤
      1 + (a h + 1) * Real.log n := by
  set F := (Finset.range (N - 1)).filter (fun i => psi hs i = h)
  have hah : 0 < a h := hs.pos (by omega)
  have hlt : a h < a (h + 1) := hs.mono h (h + 1) (by omega) hh
  set c : ℝ := ((a h : ℝ) + 1) / a h
  have hahR : (0 : ℝ) < a h := by exact_mod_cast hah
  have hc : 1 < c := by rw [lt_div_iff₀ hahR]; linarith
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hs.npos
  have key := card_le_of_chain F (fun i => (a i : ℝ)) c n hc hn1 ?_ ?_ ?_
  · have hlc : 1 / ((a h : ℝ) + 1) ≤ Real.log c := by
      have := Real.one_sub_inv_le_log_of_pos (show 0 < c by linarith)
      have e : 1 - c⁻¹ = 1 / ((a h : ℝ) + 1) := by
        simp only [c]; field_simp; ring
      linarith
    have hln : 0 ≤ Real.log n := Real.log_nonneg hn1
    have hpos : 0 < 1 / ((a h : ℝ) + 1) := by positivity
    have : Real.log n / Real.log c ≤ ((a h : ℝ) + 1) * Real.log n := by
      rw [div_le_iff₀ (lt_of_lt_of_le hpos hlc)]
      calc Real.log n = ((a h : ℝ) + 1) * Real.log n * (1 / ((a h : ℝ) + 1)) := by
            field_simp
        _ ≤ ((a h : ℝ) + 1) * Real.log n * Real.log c := by gcongr
    linarith
  · intro x hx y hy hxy
    have hx' := Finset.mem_filter.mp hx
    have hy' := Finset.mem_filter.mp hy
    have hxN : x + 1 < N := by have := Finset.mem_range.mp hx'.1; omega
    have hyN : y + 1 < N := by have := Finset.mem_range.mp hy'.1; omega
    have hsp := psi_spec hs x hxN
    rw [hx'.2] at hsp
    have h1 : a (x + 1) ≤ a y := by
      rcases (show x + 1 = y ∨ x + 1 < y by omega) with e | e
      · rw [e]
      · exact (hs.mono _ _ e (by omega)).le
    have h2 : (a h + 1) * a x ≤ a (x + 1) * a h := by
      calc (a h + 1) * a x ≤ a (h + 1) * a x := Nat.mul_le_mul_right _ hlt
        _ ≤ _ := hsp.2.2.2
    have h2R : ((a h : ℝ) + 1) * a x ≤ a (x + 1) * a h := by exact_mod_cast h2
    have h1R : (a (x + 1) : ℝ) ≤ a y := by exact_mod_cast h1
    simp only [c]
    rw [div_mul_eq_mul_div, div_le_iff₀ hahR]
    nlinarith
  · intro x hx
    have := Finset.mem_range.mp (Finset.mem_filter.mp hx).1
    have : 0 < a x := hs.pos (by omega)
    exact_mod_cast this
  · intro x hx
    have := Finset.mem_range.mp (Finset.mem_filter.mp hx).1
    exact_mod_cast Nat.le_of_dvd hs.npos (hs.dvd x (by omega))

lemma fiber_div {n N : ℕ} {a : ℕ → ℕ} (hs : Sorted n N a) (h : ℕ) :
    ((Finset.range (N - 1)).filter (fun i => psi hs i = h)).card ≤
      (n.divisors.filter (fun d => a h ∣ d)).card := by
  apply Finset.card_le_card_of_injOn a
  · intro i hi
    simp only [Finset.coe_filter, Finset.mem_range, Set.mem_ofPred_eq] at hi
    have hsp := psi_spec hs i (by omega)
    rw [hi.2] at hsp
    simp only [Finset.coe_filter, Nat.mem_divisors, Set.mem_ofPred_eq]
    exact ⟨⟨hs.dvd i (by omega), hs.npos.ne'⟩, hsp.2.2.1⟩
  · intro i hi j hj hij
    simp only [Finset.coe_filter, Finset.mem_range, Set.mem_ofPred_eq] at hi hj
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with h1 | h1
    · have := hs.mono i j h1 (by omega); omega
    · have := hs.mono j i h1 (by omega); omega

lemma main_count {n N : ℕ} {a : ℕ → ℕ} (hs : Sorted n N a) (hsq : Squarefree n) (P r : ℕ)
    (hP : ∀ p ∈ n.primeFactors, p ≤ P) (hP1 : 1 ≤ P) :
    ((N - 1 : ℕ) : ℝ) ≤ ((((Finset.range (N - 1)).filter
      (fun i => Nat.Coprime (a i) (a (i + 1)))).card : ℕ) : ℝ) *
      ((2 : ℝ) ^ (n.primeFactors.card - r) + 1 + ((P : ℝ) ^ r + 1) * Real.log n) := by
  set G := (Finset.range (N - 1)).filter (fun i => Nat.Coprime (a i) (a (i + 1)))
  set B : ℝ := (2 : ℝ) ^ (n.primeFactors.card - r) + 1 + ((P : ℝ) ^ r + 1) * Real.log n
  have hmaps : ∀ i ∈ Finset.range (N - 1), psi hs i ∈ G := by
    intro i hi
    have hsp := psi_spec hs i (by have := Finset.mem_range.mp hi; omega)
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hsp.2.1⟩
  have hcard := Finset.card_eq_sum_card_fiberwise hmaps
  have hln : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast hs.npos)
  have hfib : ∀ h ∈ G, ((((Finset.range (N - 1)).filter (fun i => psi hs i = h)).card : ℕ) : ℝ) ≤ B := by
    intro h hG
    have hh : h + 1 < N := by have := Finset.mem_range.mp (Finset.mem_filter.mp hG).1; omega
    have hdvd : a h ∣ n := hs.dvd h (by omega)
    set s := (a h).primeFactors.card
    by_cases hrs : r ≤ s
    · have h1 := (fiber_div hs h).trans (sqfree_count n (a h) hsq hdvd)
      have h2 : 2 ^ (n.primeFactors.card - s) ≤ 2 ^ (n.primeFactors.card - r) :=
        Nat.pow_le_pow_right (by norm_num) (by omega)
      have h3 : ((((Finset.range (N - 1)).filter (fun i => psi hs i = h)).card : ℕ) : ℝ) ≤
          (2 : ℝ) ^ (n.primeFactors.card - r) := by exact_mod_cast h1.trans h2
      have : (0 : ℝ) ≤ ((P : ℝ) ^ r + 1) * Real.log n := by positivity
      simp only [B]; linarith
    · have hsqh : Squarefree (a h) := hsq.squarefree_of_dvd hdvd
      have hPh : ∀ p ∈ (a h).primeFactors, p ≤ P := fun p hp =>
        hP p (Nat.primeFactors_mono hdvd hsq.ne_zero hp)
      have h1 := sqfree_le_pow (a h) P hsqh hPh
      have h2 : P ^ s ≤ P ^ r := Nat.pow_le_pow_right hP1 (by omega)
      have h3 : (a h : ℝ) ≤ (P : ℝ) ^ r := by exact_mod_cast h1.trans h2
      have h4 := fiber_chain hs h hh
      have h5 : ((a h : ℝ) + 1) * Real.log n ≤ ((P : ℝ) ^ r + 1) * Real.log n := by gcongr
      have : (0 : ℝ) ≤ (2 : ℝ) ^ (n.primeFactors.card - r) := by positivity
      simp only [B]; linarith
  calc ((N - 1 : ℕ) : ℝ) = (((Finset.range (N - 1)).card : ℕ) : ℝ) := by simp
    _ = ∑ h ∈ G, ((((Finset.range (N - 1)).filter (fun i => psi hs i = h)).card : ℕ) : ℝ) := by
        rw [hcard]; push_cast; rfl
    _ ≤ ∑ h ∈ G, B := Finset.sum_le_sum hfib
    _ = (G.card : ℝ) * B := by rw [Finset.sum_const, nsmul_eq_mul]

lemma sorted_nth (n : ℕ) (hn : 0 < n) : Sorted n n.divisors.card (Nat.nth (· ∣ n)) := by
  have hf : (Set.ofPred (· ∣ n)).Finite :=
    (Set.finite_Iic n).subset fun d hd => Nat.le_of_dvd hn hd
  have hcard : hf.toFinset.card = n.divisors.card := by
    congr 1
    ext d
    simp [hn.ne']
  refine ⟨?_, ?_, ?_, ?_, hn⟩
  · intro i hi; exact Nat.nth_mem_of_lt_card hf (by rw [hcard]; exact hi)
  · intro i j hij hj; exact Nat.nth_lt_nth_of_lt_card hf hij (by rw [hcard]; exact hj)
  · intro x hx
    obtain ⟨j, hj, hjx⟩ := Nat.exists_lt_card_finite_nth_eq hf hx
    exact ⟨j, by rw [← hcard]; exact hj, hjx⟩
  · intro k x hx hkx
    by_contra hc
    push Not at hc
    have := Nat.le_nth_of_lt_nth_succ hc hx
    omega

lemma tauPerp_eq (n : ℕ) : Erdos1100.tauPerp n = ((Finset.range (n.divisors.card - 1)).filter
    (fun i => Nat.Coprime (Nat.nth (· ∣ n) i) (Nat.nth (· ∣ n) (i + 1)))).card := by
  unfold Erdos1100.tauPerp
  rw [Finset.card_filter, Finset.card_filter]
  exact Fin.sum_univ_eq_sum_range
    (fun i => if Nat.Coprime (Nat.nth (· ∣ n) i) (Nat.nth (· ∣ n) (i + 1)) then 1 else 0) _

lemma divisors_card_sqfree (n : ℕ) (hn : Squarefree n) :
    n.divisors.card = 2 ^ n.primeFactors.card := by
  rw [Nat.card_divisors hn.ne_zero]
  rw [Finset.prod_congr rfl (g := fun _ => 2)]
  · simp
  · intro p hp
    have h1 := Squarefree.natFactorization_le_one p hn
    have h2 : 0 < n.factorization p := Nat.Prime.factorization_pos_of_dvd
      (Nat.prime_of_mem_primeFactors hp) hn.ne_zero (Nat.dvd_of_mem_primeFactors hp)
    omega

lemma tau_lower (P r : ℕ) (hP1 : 1 ≤ P) :
    (2 : ℝ) ^ (Nat.primeCounting P) - 1 ≤ (Erdos1100.tauPerp (primorial P) : ℝ) *
      ((2 : ℝ) ^ (Nat.primeCounting P - r) + 1 + ((P : ℝ) ^ r + 1) * (Real.log 4 * P)) := by
  set n := primorial P
  have hn : 0 < n := primorial_pos P
  have hsq : Squarefree n := squarefree_primorial P
  have hpf : n.primeFactors = P.primesLE := primeFactors_primorial P
  have hk : n.primeFactors.card = Nat.primeCounting P := by
    rw [hpf, Nat.primesLE_card_eq_primeCounting]
  have hP : ∀ p ∈ n.primeFactors, p ≤ P := by
    intro p hp; rw [hpf] at hp; exact Nat.le_of_mem_primesLE hp
  have hmc := main_count (sorted_nth n hn) hsq P r hP hP1
  rw [← tauPerp_eq, divisors_card_sqfree n hsq, hk] at hmc
  have hlog : Real.log n ≤ Real.log 4 * P := by
    have h := Chebyshev.theta_le_log4_mul_x (x := (P : ℝ)) (by positivity)
    rwa [Chebyshev.theta_eq_log_primorial, Nat.floor_natCast] at h
  have hpow : (1 : ℕ) ≤ 2 ^ Nat.primeCounting P := Nat.one_le_two_pow
  have hc : (((2 ^ Nat.primeCounting P - 1 : ℕ)) : ℝ) = (2 : ℝ) ^ Nat.primeCounting P - 1 := by
    push_cast [Nat.cast_sub hpow]; ring
  rw [hc] at hmc
  refine hmc.trans ?_
  gcongr

lemma log2_bounds : (0.69 : ℝ) < log 2 ∧ log 2 < 0.7 := by
  constructor
  · have := Real.log_two_gt_d9; linarith
  · have := Real.log_two_lt_d9; linarith

lemma glue_C1 (P k r : ℕ) (L : ℝ) (hPge : 4 ≤ (P : ℝ)) (hPexp : (P : ℝ) = exp L) (hrk : r ≤ k)
    (hrL : (r : ℝ) * L ≤ k * log 2 / 2) (hrk4 : (r : ℝ) ≤ k / 4) (h2L : 2 * L ≤ k * log 2 / 4) :
    ((P : ℝ) ^ r + 1) * (log 4 * P) ≤ (2 : ℝ) ^ (k - r) := by
  have hl4 : log 4 ≤ 2 := by
    have : log 4 = 2 * log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
    have := log2_bounds.2
    linarith
  have hPr1 : (1 : ℝ) ≤ (P : ℝ) ^ r := one_le_pow₀ (by linarith)
  have e1 : ((P : ℝ) ^ r + 1) * (log 4 * P) ≤ (P : ℝ) ^ (r + 2) := by
    rw [pow_add]
    have : (log 4 * P) * 2 ≤ (P : ℝ) ^ 2 := by nlinarith [Real.log_nonneg (show (1:ℝ) ≤ 4 by norm_num)]
    nlinarith
  refine e1.trans ?_
  have h2exp : (2 : ℝ) = exp (log 2) := (Real.exp_log (by norm_num)).symm
  rw [hPexp, ← Real.exp_nat_mul, h2exp, ← Real.exp_nat_mul]
  apply Real.exp_le_exp.mpr
  push_cast [Nat.cast_sub hrk]
  have hrl2 : (r : ℝ) * log 2 ≤ k / 4 * log 2 :=
    mul_le_mul_of_nonneg_right hrk4 (Real.log_nonneg (by norm_num))
  have e2 : ((r : ℝ) + 2) * L = r * L + 2 * L := by ring
  have e3 : ((k : ℝ) - r) * log 2 = k * log 2 - r * log 2 := by ring
  have e4 : (k : ℝ) / 4 * log 2 = k * log 2 / 4 := by ring
  rw [e2, e3]
  linarith

lemma glue_C2 (k r : ℕ) (τ X : ℝ) (hrk : r ≤ k) (hk1 : 1 ≤ k) (hX0 : 0 ≤ X)
    (hX : X ≤ (2 : ℝ) ^ (k - r)) (h : (2 : ℝ) ^ k - 1 ≤ τ * ((2 : ℝ) ^ (k - r) + 1 + X)) :
    (2 : ℝ) ^ r / 6 ≤ τ := by
  have hA : (2 : ℝ) ^ k = 2 ^ (k - r) * 2 ^ r := by
    rw [← pow_add, Nat.sub_add_cancel hrk]
  have hB1 : (1 : ℝ) ≤ 2 ^ (k - r) := one_le_pow₀ (by norm_num)
  have hBle : (2 : ℝ) ^ (k - r) + 1 + X ≤ 3 * 2 ^ (k - r) := by linarith
  have hBpos : (0 : ℝ) < 2 ^ (k - r) + 1 + X := by positivity
  have hkpos : (2 : ℝ) ≤ 2 ^ k := by
    calc (2 : ℝ) = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ k := pow_le_pow_right₀ (by norm_num) hk1
  have hτpos : 0 < τ := by
    by_contra hc; push Not at hc
    have : τ * ((2 : ℝ) ^ (k - r) + 1 + X) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hc hBpos.le
    linarith
  have h3 : (2 : ℝ) ^ k / 2 ≤ τ * (3 * 2 ^ (k - r)) := by
    have := mul_le_mul_of_nonneg_left hBle hτpos.le
    linarith
  rw [hA] at h3
  rw [div_le_iff₀ (by norm_num)]
  have hpos : (0 : ℝ) < 2 ^ (k - r) := by positivity
  have : (2 : ℝ) ^ r * 2 ^ (k - r) ≤ (τ * 6) * 2 ^ (k - r) := by nlinarith
  exact le_of_mul_le_mul_right this hpos

lemma glue_C3 (y t : ℝ) (r : ℕ) (hy0 : 0 ≤ y) (hy : y ≤ log 4 * t ^ 8) (ht5 : 5 ≤ t)
    (hr : (log 2 / 2) * (t ^ 6 / 128) - 1 ≤ r) : exp (y ^ (1 / 8 : ℝ)) ≤ (2 : ℝ) ^ r / 6 := by
  have ht0 : 0 ≤ t := by linarith
  have hy8 : y ^ (1 / 8 : ℝ) ≤ 2 * t := by
    have h1 : y ^ (1 / 8 : ℝ) ≤ (log 4 * t ^ 8) ^ (1 / 8 : ℝ) :=
      Real.rpow_le_rpow hy0 hy (by norm_num)
    have h2 : (log 4 * t ^ 8) ^ (1 / 8 : ℝ) = (log 4) ^ (1 / 8 : ℝ) * t := by
      rw [Real.mul_rpow (Real.log_nonneg (by norm_num)) (by positivity), ← Real.rpow_natCast,
        ← Real.rpow_mul ht0]
      norm_num
    have h3 : (log 4) ^ (1 / 8 : ℝ) ≤ 2 := by
      have hl : log 4 ≤ 256 := by
        have := Real.log_le_sub_one_of_pos (show (0:ℝ) < 4 by norm_num); linarith
      calc (log 4) ^ (1 / 8 : ℝ) ≤ (256 : ℝ) ^ (1 / 8 : ℝ) :=
            Real.rpow_le_rpow (Real.log_nonneg (by norm_num)) hl (by norm_num)
        _ = 2 := by
            rw [show (256 : ℝ) = 2 ^ (8 : ℝ) by norm_num, ← Real.rpow_mul (by norm_num)]; norm_num
    rw [h2] at h1
    nlinarith
  have h2exp : (2 : ℝ) = exp (log 2) := (Real.exp_log (by norm_num)).symm
  rw [h2exp, ← Real.exp_nat_mul, le_div_iff₀ (by norm_num),
    show (6 : ℝ) = exp (log 6) from (Real.exp_log (by norm_num)).symm, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hl6 : log 6 < 3 := by
    have h6 : log 6 = log 2 + log 3 := by
      rw [show (6:ℝ) = 2 * 3 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
    have := Real.log_le_sub_one_of_pos (show (0:ℝ) < 3 by norm_num)
    have := log2_bounds.2
    linarith
  obtain ⟨hl2, hl2'⟩ := log2_bounds
  have h5 : (5 : ℝ) ^ 5 ≤ t ^ 5 := pow_le_pow_left₀ (by norm_num) ht5 5
  have ht6 : t ^ 6 = t * t ^ 5 := by ring
  have hr' : (0.69 / 2) * (t ^ 6 / 128) - 1 ≤ r := by
    have : (0.69 / 2) * (t ^ 6 / 128) ≤ (log 2 / 2) * (t ^ 6 / 128) := by
      have : 0 ≤ t ^ 6 := by positivity
      nlinarith
    linarith
  have hbig : 2 * t + 3 ≤ ((0.69 / 2) * (t ^ 6 / 128) - 1) * 0.69 := by
    rw [ht6]; nlinarith
  have hr0 : (0 : ℝ) ≤ ((0.69 / 2) * (t ^ 6 / 128) - 1) := by nlinarith
  have : ((0.69 / 2) * (t ^ 6 / 128) - 1) * 0.69 ≤ (r : ℝ) * log 2 := by
    apply mul_le_mul hr' hl2.le (by norm_num) (by positivity)
  linarith

lemma setup_t (P : ℕ) (hP : 390625 ≤ P) :
    ∃ t : ℝ, 5 ≤ t ∧ (P : ℝ) = t ^ 8 ∧ log (P : ℝ) ≤ 8 * t := by
  have hPR : (390625 : ℝ) ≤ P := by exact_mod_cast hP
  have hP0 : (0 : ℝ) < P := by linarith
  refine ⟨(P : ℝ) ^ (1 / 8 : ℝ), ?_, ?_, ?_⟩
  · have hPt : (P : ℝ) = ((P : ℝ) ^ (1 / 8 : ℝ)) ^ 8 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hP0.le]; norm_num
    have : (5 : ℝ) ^ 8 ≤ ((P : ℝ) ^ (1 / 8 : ℝ)) ^ 8 := by rw [← hPt]; norm_num; linarith
    exact le_of_pow_le_pow_left₀ (by norm_num) (by positivity) this
  · rw [← Real.rpow_natCast, ← Real.rpow_mul hP0.le]; norm_num
  · have := Real.log_le_rpow_div hP0.le (show (0 : ℝ) < 1 / 8 by norm_num)
    linarith

lemma setup_k (P k : ℕ) (t : ℝ) (ht5 : 5 ≤ t) (hPt : (P : ℝ) = t ^ 8) (hL8 : log (P : ℝ) ≤ 8 * t)
    (hk : ((P : ℝ) * log 2 - log ((P : ℝ) + 1)) / log P ≤ k) :
    t ^ 8 / 2 ≤ (k : ℝ) * log P ∧ 2 * log 2 ≤ log (P : ℝ) := by
  have hP0 : (0 : ℝ) < P := by rw [hPt]; positivity
  obtain ⟨hl2, hl2'⟩ := log2_bounds
  have hL4 : 2 * log 2 ≤ log (P : ℝ) := by
    rw [← Real.log_rpow (by norm_num : (0:ℝ) < 2)]
    apply Real.log_le_log (by norm_num)
    rw [hPt]; norm_num
    nlinarith [pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 5) ht5 8]
  have hLpos : 0 < log (P : ℝ) := by linarith
  have hlogP1 : log ((P : ℝ) + 1) ≤ log 2 + log P := by
    rw [← Real.log_mul (by norm_num) hP0.ne']
    exact Real.log_le_log (by linarith) (by nlinarith [pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 5) ht5 8])
  refine ⟨?_, hL4⟩
  rw [div_le_iff₀ hLpos] at hk
  have h7 : (5 : ℝ) ^ 7 ≤ t ^ 7 := pow_le_pow_left₀ (by norm_num) ht5 7
  have ht8 : t ^ 8 = t * t ^ 7 := by ring
  have : (P : ℝ) * (log 2 - 1 / 2) ≥ log 2 + 8 * t := by
    rw [hPt, ht8]; nlinarith
  rw [← hPt]
  linarith

lemma real_glue (P k : ℕ) (τ : ℝ) (hP : 390625 ≤ P)
    (hk : ((P : ℝ) * log 2 - log ((P : ℝ) + 1)) / log P ≤ k)
    (htau : ∀ r : ℕ, (2 : ℝ) ^ k - 1 ≤ τ * ((2 : ℝ) ^ (k - r) + 1 + ((P : ℝ) ^ r + 1) * (log 4 * P)))
    (y : ℝ) (hy0 : 0 ≤ y) (hy : y ≤ log 4 * P) : exp (y ^ (1 / 8 : ℝ)) ≤ τ := by
  obtain ⟨t, ht5, hPt, hL8⟩ := setup_t P hP
  obtain ⟨hkL, hL4⟩ := setup_k P k t ht5 hPt hL8 hk
  have hP0 : (0 : ℝ) < P := by rw [hPt]; positivity
  set L := log (P : ℝ) with hL
  have hLpos : 0 < L := by have := log2_bounds.1; linarith
  have hk0 : (0 : ℝ) ≤ k := by positivity
  obtain ⟨hl2, hl2'⟩ := log2_bounds
  have hk7 : t ^ 7 / 16 ≤ (k : ℝ) := by
    have h1 : (k : ℝ) * L ≤ k * (8 * t) := mul_le_mul_of_nonneg_left hL8 hk0
    have h2 : t ^ 7 / 16 * (8 * t) ≤ k * (8 * t) := by
      have : t ^ 7 / 16 * (8 * t) = t ^ 8 / 2 := by ring
      linarith
    exact le_of_mul_le_mul_right h2 (by linarith)
  have hkL2 : t ^ 6 / 128 ≤ (k : ℝ) / L := by
    rw [le_div_iff₀ hLpos]
    have hL2 : L ^ 2 ≤ 64 * t ^ 2 := by nlinarith
    have : t ^ 6 / 128 * L ^ 2 ≤ t ^ 6 / 128 * (64 * t ^ 2) :=
      mul_le_mul_of_nonneg_left hL2 (by positivity)
    have e : t ^ 6 / 128 * (64 * t ^ 2) = t ^ 8 / 2 := by ring
    nlinarith
  set r : ℕ := ⌊(k : ℝ) * log 2 / (2 * L)⌋₊ with hr
  have hr1 : (r : ℝ) ≤ (k : ℝ) * log 2 / (2 * L) := Nat.floor_le (by positivity)
  have hr2 : (k : ℝ) * log 2 / (2 * L) < r + 1 := Nat.lt_floor_add_one _
  clear_value r
  have hrL : (r : ℝ) * L ≤ k * log 2 / 2 := by
    rw [le_div_iff₀ (by positivity)] at hr1; nlinarith
  have hrk4 : (r : ℝ) ≤ k / 4 := by
    have : (k : ℝ) * log 2 / (2 * L) ≤ k / 4 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith
    linarith
  have hrk : r ≤ k := by
    have : (r : ℝ) ≤ k := by linarith
    exact_mod_cast this
  have h2L : 2 * L ≤ k * log 2 / 4 := by
    have h6 : (5 : ℝ) ^ 6 ≤ t ^ 6 := pow_le_pow_left₀ (by norm_num) ht5 6
    have ht7 : t ^ 7 = t * t ^ 6 := by ring
    have hklog : t ^ 7 / 16 * 0.69 ≤ (k : ℝ) * log 2 := mul_le_mul hk7 hl2.le (by norm_num) hk0
    have : 16 * t ≤ t ^ 7 / 16 * 0.69 / 4 := by rw [ht7]; nlinarith
    linarith
  have hC1 := glue_C1 P k r L (by rw [hPt]; nlinarith [pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 5) ht5 8])
    (Real.exp_log hP0).symm hrk hrL hrk4 h2L
  have hk1 : 1 ≤ k := by
    have : (1 : ℝ) ≤ k := by nlinarith [pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 5) ht5 7]
    exact_mod_cast this
  have hC2 := glue_C2 k r τ _ hrk hk1 (by positivity) hC1 (htau r)
  have hr3 : (log 2 / 2) * (t ^ 6 / 128) - 1 ≤ r := by
    have e : (k : ℝ) * log 2 / (2 * L) = (log 2 / 2) * (k / L) := by field_simp
    rw [e] at hr2
    have : (log 2 / 2) * (t ^ 6 / 128) ≤ (log 2 / 2) * (k / L) :=
      mul_le_mul_of_nonneg_left hkL2 (by positivity)
    linarith
  have hC3 := glue_C3 y t r hy0 (by rw [← hPt]; exact hy) ht5 hr3
  exact hC3.trans hC2

theorem final : ¬ ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in Filter.atTop,
    (Erdos1100.tauPerp n : ℝ) < Real.exp (Real.log n ^ ε) := by
  intro H
  obtain ⟨N0, hN0⟩ := Filter.eventually_atTop.mp (H (1 / 8) (by norm_num))
  set P := max N0 390625 with hPdef
  have hP : 390625 ≤ P := le_max_right _ _
  have hN : N0 ≤ primorial P := (le_max_left _ _).trans le_primorial_self
  have hlt := hN0 (primorial P) hN
  have hlog : Real.log (primorial P : ℕ) ≤ Real.log 4 * P := by
    have h := Chebyshev.theta_le_log4_mul_x (x := (P : ℝ)) (by positivity)
    rwa [Chebyshev.theta_eq_log_primorial, Nat.floor_natCast] at h
  have hlog0 : 0 ≤ Real.log (primorial P : ℕ) :=
    Real.log_nonneg (by exact_mod_cast primorial_pos P)
  have key := real_glue P (Nat.primeCounting P) (Erdos1100.tauPerp (primorial P)) hP
    (Chebyshev.pi_ge P) (fun r => tau_lower P r (by omega)) _ hlog0 hlog
  linarith

end E1100

theorem OMA.solution : type_of% @Erdos1100.erdos_1100.parts.ii := E1100.final
