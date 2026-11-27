import FormalConjectures.ErdosProblems.«1100»

/-!
The counting inequality for coprime consecutive divisors is Steven Enamakel's
formalization in PR 1763 of the argument of Erdős and Tenenbaum (1989),
https://www.renyi.hu/~p_erdos/1989-37.pdf, Theorem 4.
The Chebyshev prime-window estimates are from dk8827's PR 1252.
We choose a prescribed number of primes in a window of size comparable to
log x, and optimize the cutoff in the counting inequality to obtain the
leading constant (log 2)² uniformly for all sufficiently large real x.
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

end E1100

namespace OMA.Erdos1100

open Filter Asymptotics Finset
open scoped Classical

def primesInWindow (L : ℕ) : Finset ℕ :=
  (Nat.primesLE (8 * L)) \ Nat.primesLE L

theorem prime_window_member {L p : ℕ} (h : p ∈ primesInWindow L) :
    p.Prime ∧ L ≤ p ∧ p ≤ 8 * L := by
  obtain ⟨hp, hnp⟩ := Finset.mem_sdiff.mp h
  obtain ⟨hhi, hprime⟩ := Nat.mem_primesLE.mp hp
  exact ⟨hprime, le_of_not_ge fun hlo => hnp (Nat.mem_primesLE.mpr ⟨hlo, hprime⟩), hhi⟩

private theorem prime_window_sum (L : ℕ) :
    ∑ p ∈ primesInWindow L, Real.log p =
      Chebyshev.theta (8 * (L : ℝ)) - Chebyshev.theta (L : ℝ) := by
  have hsub : Nat.primesLE L ⊆ Nat.primesLE (8 * L) :=
    Nat.primesLE_mono (by omega)
  have h := Finset.sum_sdiff (f := fun p : ℕ => Real.log p) hsub
  change (∑ p ∈ primesInWindow L, Real.log p) + (∑ p ∈ Nat.primesLE L, Real.log p) =
    ∑ p ∈ Nat.primesLE (8 * L), Real.log p at h
  rw [← Chebyshev.theta_eq_sum_primesLE_log, ← Chebyshev.theta_eq_sum_primesLE_log] at h
  push_cast at h
  linarith

private theorem theta_window_lower :
    ∀ᶠ L : ℕ in atTop,
      (L : ℝ) ≤ Chebyshev.theta (8 * (L : ℝ)) - Chebyshev.theta (L : ℝ) := by
  have hT : Tendsto (fun L : ℕ => 8 * (L : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.const_mul_atTop (by norm_num : (0 : ℝ) < 8)
  have hT' : Tendsto (fun L : ℕ => 8 * (L : ℝ) + 1) atTop atTop :=
    tendsto_atTop_add_const_right _ _ hT
  have hlog := hT.eventually
    ((isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2)).bound
      (by norm_num : (0 : ℝ) < 1 / 16))
  have hlog' := hT'.eventually
    (Real.isLittleO_log_id_atTop.bound (by norm_num : (0 : ℝ) < 1 / 8))
  filter_upwards [eventually_ge_atTop (1 : ℕ), hlog, hlog'] with L hL hn1 hn2
  have h1 : (1 : ℝ) ≤ (L : ℝ) := by exact_mod_cast hL
  have h8 : (0 : ℝ) ≤ 8 * (L : ℝ) := by positivity
  have hlogSmall : Real.log (8 * (L : ℝ)) ≤ (1 / 16) * Real.sqrt (8 * (L : ℝ)) := by
    change ‖Real.log _‖ ≤ (1 / 16) * ‖(8 * (L : ℝ)) ^ ((1 : ℝ) / 2)‖ at hn1
    rw [← Real.sqrt_eq_rpow, Real.norm_of_nonneg (Real.sqrt_nonneg _), Real.norm_eq_abs] at hn1
    exact (le_abs_self _).trans hn1
  have hlogSmall' : Real.log (8 * (L : ℝ) + 1) ≤ (1 / 8) * (8 * (L : ℝ) + 1) := by
    change ‖Real.log _‖ ≤ (1 / 8) * ‖8 * (L : ℝ) + 1‖ at hn2
    exact (le_abs_self _).trans (by simpa [Real.norm_eq_abs, abs_of_nonneg (by positivity :
      (0 : ℝ) ≤ 8 * (L : ℝ) + 1)] using hn2)
  have hmul := mul_le_mul_of_nonneg_left hlogSmall (Real.sqrt_nonneg (8 * (L : ℝ)))
  have hsq := Real.sq_sqrt h8
  have hmul' : 2 * Real.sqrt (8 * (L : ℝ)) * Real.log (8 * (L : ℝ)) ≤ L := by
    nlinarith only [hmul, hsq]
  have hlower := Chebyshev.theta_ge (8 * L)
  push_cast at hlower
  have hupper := Chebyshev.theta_le_log4_mul_x (x := (L : ℝ)) (by positivity)
  have hlog2 : (2 / 3 : ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hlog4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, Real.log_pow]
    norm_num
  rw [hlog4] at hupper
  nlinarith only [hlower, hupper, hlogSmall', hmul', h1,
    mul_le_mul_of_nonneg_right hlog2 (by positivity : (0 : ℝ) ≤ (L : ℝ))]

theorem prime_window_large :
    ∀ᶠ L : ℕ in atTop,
      8 ≤ L ∧
      (L : ℝ) / (2 * Real.log (L : ℝ)) ≤ (primesInWindow L).card := by
  filter_upwards [eventually_ge_atTop (8 : ℕ), theta_window_lower] with L hL htheta
  have h8 : (8 : ℝ) ≤ (L : ℝ) := by exact_mod_cast hL
  have hlog : 0 < Real.log (L : ℝ) := Real.log_pos (by linarith)
  have hlog8 : Real.log (8 * (L : ℝ)) ≤ 2 * Real.log (L : ℝ) := by
    rw [Real.log_mul (by norm_num : (8 : ℝ) ≠ 0) (by positivity : (L : ℝ) ≠ 0)]
    linarith [Real.log_le_log (by norm_num : (0 : ℝ) < 8) h8]
  have hsum : (∑ p ∈ primesInWindow L, Real.log p) ≤
      ((primesInWindow L).card : ℝ) * (2 * Real.log (L : ℝ)) := by
    rw [← nsmul_eq_mul, ← sum_const]
    apply sum_le_sum
    intro p hp
    obtain ⟨hprime, _, hupper⟩ := prime_window_member hp
    exact (Real.log_le_log (by exact_mod_cast hprime.pos)
      (by exact_mod_cast hupper : (p : ℝ) ≤ 8 * (L : ℝ))).trans hlog8
  exact ⟨hL, (div_le_iff₀ (by positivity)).mpr ((htheta.trans_eq (prime_window_sum L).symm).trans hsum)⟩

end OMA.Erdos1100

open Real Filter Finset
open scoped Topology
namespace ETMax

/-- Balancing the two terms in the divisor-counting inequality gives at least
2^r / 8 coprime consecutive pairs when all prime factors are at most P. -/
private lemma finite_count (n P k r : ℕ) (hn : Squarefree n)
    (hk : n.primeFactors.card = k) (hk1 : 1 ≤ k) (hrk : r ≤ k)
    (hP : ∀ p ∈ n.primeFactors, p ≤ P) (hP1 : 1 ≤ P)
    (T : ℝ) (hlogP : log P ≤ T) (hlogn : log n ≤ exp T)
    (hcut : (r : ℝ) * T + T ≤ ((k : ℝ) - r) * log 2) :
    (2 : ℝ)^r ≤ 8 * _root_.Erdos1100.tauPerp n := by
  have hn0 : 0 < n := Nat.pos_of_ne_zero hn.ne_zero
  have h := E1100.main_count (E1100.sorted_nth n hn0) hn P r hP hP1
  rw [← E1100.tauPerp_eq, E1100.divisors_card_sqfree n hn, hk] at h
  have hpow : (1 : ℕ) ≤ 2^k := Nat.one_le_two_pow
  push_cast [Nat.cast_sub hpow] at h
  let B := (2 : ℝ)^(k-r)
  have hB : 1 ≤ B := one_le_pow₀ (by norm_num)
  have hp : 0 < (P : ℝ) := by exact_mod_cast (show 0 < P by omega)
  have hprod : (P : ℝ)^r * exp T ≤ B := by
    apply (log_le_log_iff (by positivity) (by dsimp [B]; positivity)).mp
    rw [Real.log_mul (by positivity) (exp_pos T).ne', Real.log_pow, Real.log_exp]
    dsimp [B]
    rw [Real.log_pow, Nat.cast_sub hrk]
    linarith [mul_le_mul_of_nonneg_left hlogP (Nat.cast_nonneg r)]
  have hPpow : 1 ≤ (P : ℝ)^r := one_le_pow₀ (by exact_mod_cast hP1)
  have heB : exp T ≤ B := by nlinarith [mul_nonneg (sub_nonneg.mpr hPpow) (exp_nonneg T)]
  have hbound : B + 1 + ((P : ℝ)^r + 1) * log n ≤ 4 * B := by
    have hh := mul_le_mul_of_nonneg_left hlogn (by positivity : 0 ≤ (P : ℝ)^r + 1)
    nlinarith
  have h1 : (2 : ℝ)^k - 1 ≤ (_root_.Erdos1100.tauPerp n : ℝ) * (4 * B) :=
    h.trans (mul_le_mul_of_nonneg_left hbound (Nat.cast_nonneg _))
  have h2 : (2 : ℝ) ≤ 2^k := by
    simpa using pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hk1
  have heq : B * (2 : ℝ)^r = 2^k := by
    dsimp [B]
    rw [← pow_add, Nat.sub_add_cancel hrk]
  apply le_of_mul_le_mul_left (a := B)
  · nlinarith only [h1, h2, heq]
  · positivity

private lemma ratio (a : ℝ) : Tendsto (fun t : ℝ => t / (t+a)) atTop (𝓝 1) := by
  have h := (tendsto_const_nhds (x := a)).mul (tendsto_inv_atTop_zero (𝕜 := ℝ))
  have h' : Tendsto (fun t : ℝ => (1 + a * t⁻¹)⁻¹) atTop (𝓝 1) := by
    simpa using ((tendsto_const_nhds (x := (1 : ℝ))).add h).inv₀ (by simp)
  apply h'.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
  field_simp

/-- At t = log log x the cutoff grows like (log 2) exp(t) / t².
The constant losses from taking floors disappear at this scale. -/
private lemma scales (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ t : ℝ in atTop,
      let b := log 2
      let T := t + log 64
      let s := b * exp t / (T * (T+b))
      1 ≤ t ∧ 5 ≤ s ∧ (b^2-δ)*exp t/t^2 ≤ (s-5)*b-log 8 := by
  let b := log 2
  let c := log 64
  have hb : 0 < b := Real.log_pos (by norm_num)
  have h := ((tendsto_const_nhds (x := b^2)).mul (ratio c)).mul (ratio (c+b))
  have he := (tendsto_const_nhds (x := 5*b+log 8)).mul (tendsto_pow_mul_exp_neg_atTop_nhds_zero 2)
  have hh : Tendsto (fun t : ℝ =>
      b^2*(t/(t+c))*(t/(t+(c+b))) - (5*b+log 8)*(t^2*exp (-t))) atTop (𝓝 (b^2)) := by
    simpa using h.sub he
  let η := min δ (b^2/2)
  have hη : 0 < η := lt_min hδ (by positivity)
  filter_upwards [hh.eventually (lt_mem_nhds (show b^2-η < b^2 by linarith)), eventually_ge_atTop (1 : ℝ)] with t ht ht1
  dsimp only at ht ⊢
  change b^2-η < _ at ht
  have hc : 0 < c := Real.log_pos (by norm_num)
  have ht0 : 0 < t := by linarith
  let T := t+c
  let s := b*exp t/(T*(T+b))
  have hid : b^2*(t/(t+c))*(t/(t+(c+b))) - (5*b+log 8)*(t^2*exp (-t)) =
      ((s-5)*b-log 8) * t^2 / exp t := by
    dsimp [s,T]
    rw [exp_neg, ← add_assoc]
    field_simp [show t+c ≠ 0 by positivity, show t+c+b ≠ 0 by positivity]
    ring
  rw [hid] at ht
  have hlow : (b^2-η)*exp t/t^2 < (s-5)*b-log 8 := by
    apply (div_lt_iff₀ (by positivity)).mpr
    exact (lt_div_iff₀ (exp_pos t)).mp ht
  have hy : 0 < b^2-η := by
    have := min_le_right δ (b^2/2)
    dsimp [η]; linarith
  have hpos : 0 < (s-5)*b-log 8 := lt_trans (by positivity) hlow
  have hs : 5 ≤ s := by
    have hmul : 0 < (s-5)*b := by linarith [Real.log_pos (by norm_num : (1:ℝ)<8)]
    exact le_of_lt (by linarith [(pos_of_mul_pos_left hmul hb.le)])
  refine ⟨ht1, hs, le_trans ?_ hlow.le⟩
  gcongr
  exact min_le_left _ _

open OMA.Erdos1100 in
private theorem maximum (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ x : ℝ in atTop, ∃ n : ℕ, (n : ℝ) ≤ x ∧
      exp (((log 2)^2-δ)*log x/(log (log x))^2) ≤ (_root_.Erdos1100.tauPerp n : ℝ) := by
  have hw : Tendsto (fun x : ℝ => ⌈4 * log x⌉₊) atTop atTop :=
    tendsto_nat_ceil_atTop.comp (Real.tendsto_log_atTop.const_mul_atTop (by norm_num))
  filter_upwards [hw.eventually prime_window_large,
    (Real.tendsto_log_atTop.comp Real.tendsto_log_atTop).eventually (scales δ hδ),
    eventually_ge_atTop (exp 1)] with x hwindow hscale hx
  let u := log x
  let t := log u
  let c := log 64
  let b := log 2
  let T := t+c
  let L := ⌈4*u⌉₊
  let P := 8*L
  -- With k primes of logarithm at most T, their product is at most x.
  let k := ⌊u/T⌋₊
  let s := b*u/(T*(T+b))
  let r := ⌊s-4⌋₊
  have hx0 : 0 < x := (exp_pos _).trans_le hx
  have hu1 : 1 ≤ u := (Real.le_log_iff_exp_le hx0).mpr hx
  have hu : 0 < u := by linarith
  have het : exp t = u := exp_log hu
  have hc : 0 < c := log_pos (by norm_num)
  have hb : 0 < b := log_pos (by norm_num)
  change 1 ≤ t ∧ 5 ≤ b * exp t / (T*(T+b)) ∧
    (b^2-δ)*exp t/t^2 ≤ (b*exp t/(T*(T+b))-5)*b-log 8 at hscale
  rw [het] at hscale
  obtain ⟨ht, hs, hgoal⟩ := hscale
  change 5 ≤ s at hs
  change (b^2-δ)*u/t^2 ≤ (s-5)*b-log 8 at hgoal
  have hT : 0 < T := by dsimp [T]; linarith
  obtain ⟨hL8, hcard⟩ := hwindow
  change 8 ≤ L at hL8
  change (L : ℝ)/(2*log L) ≤ ((primesInWindow L).card : ℝ) at hcard
  have hLlo : 4*u ≤ (L : ℝ) := Nat.le_ceil _
  have hLhi : (L : ℝ) < 4*u+1 := Nat.ceil_lt_add_one (by positivity)
  have hP1 : 1 ≤ P := by dsimp [P]; omega
  have hLP : L ≤ P := by dsimp [P]; omega
  have hLpos : 0 < (L : ℝ) := by exact_mod_cast (show 0 < L by omega)
  have hlogLpos : 0 < log L := log_pos (by exact_mod_cast (show 1 < L by omega))
  have hlogP : log P ≤ T := by
    have hPu : (P : ℝ) ≤ 64*u := by dsimp [P]; push_cast; linarith
    have h := log_le_log (by exact_mod_cast (show 0 < P by omega)) hPu
    rwa [log_mul (by norm_num) hu.ne', add_comm] at h
  have hlogL : log L ≤ T := (log_le_log hLpos (by exact_mod_cast hLP)).trans hlogP
  have hklo : u/T < (k : ℝ) + 1 := Nat.lt_floor_add_one _
  have hkhi : (k : ℝ) ≤ u/T := Nat.floor_le (by positivity)
  have hkcard : k ≤ (primesInWindow L).card := by
    apply (Nat.cast_le (α := ℝ)).mp
    apply hkhi.trans (le_trans ?_ hcard)
    apply (div_le_div_iff₀ hT (by positivity)).mpr
    nlinarith [mul_le_mul_of_nonneg_left hlogL hu.le,
      mul_le_mul_of_nonneg_right hLlo hT.le, mul_pos hu hT]
  obtain ⟨S, hS, hSk⟩ := Finset.exists_subset_card_eq hkcard
  have hprime {p} (hp : p ∈ S) := (prime_window_member (hS hp)).1
  let n := ∏ p ∈ S, p
  have hfac : n.primeFactors = S := Nat.primeFactors_prod fun _ hp => hprime hp
  have hsf : Squarefree n := by
    apply Finset.squarefree_prod_of_pairwise_isCoprime
    · intro p hp q hq hne
      exact Nat.coprime_iff_isRelPrime.mp ((hprime hp).coprime_iff_not_dvd.mpr
        (fun h => hne (((hprime hq).eq_one_or_self_of_dvd p h).resolve_left (hprime hp).ne_one)))
    · exact fun _ hp => (hprime hp).squarefree
  have hmax : ∀ p ∈ n.primeFactors, p ≤ P := by
    rw [hfac]
    exact fun _ hp => (prime_window_member (hS hp)).2.2
  have hln : log n ≤ u := by
    dsimp [n]
    rw [Nat.cast_prod, log_prod (fun p hp => by exact_mod_cast (hprime hp).ne_zero)]
    calc
      _ ≤ ∑ _p ∈ S, T := Finset.sum_le_sum fun p hp =>
        (log_le_log (by exact_mod_cast (hprime hp).pos)
          (by exact_mod_cast (prime_window_member (hS hp)).2.2)).trans hlogP
      _ = (k : ℝ)*T := by simp [hSk]
      _ ≤ u := (le_div_iff₀ hT).mp hkhi
  have hn0 : 0 < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hsf.ne_zero
  have hnx : (n : ℝ) ≤ x := (log_le_log_iff hn0 hx0).mp hln
  have hr1 : 1 ≤ r := (Nat.one_le_floor_iff _).mpr (by linarith)
  have hrhi : (r : ℝ) ≤ s-4 := Nat.floor_le (by linarith)
  have hrlo : s-4 < (r : ℝ)+1 := Nat.lt_floor_add_one _
  have hscaleid : s*(T+b) = b*(u/T) := by
    dsimp [s]
    field_simp
  have hcut : (r : ℝ)*T+T ≤ ((k : ℝ)-r)*b := by
    nlinarith [mul_le_mul_of_nonneg_right hrhi (by positivity : 0 ≤ T+b),
      mul_lt_mul_of_pos_left hklo hb]
  have hrk : r ≤ k := by
    apply (Nat.cast_le (α := ℝ)).mp
    by_contra! h
    nlinarith [mul_pos (sub_pos.mpr h) hb, mul_nonneg (Nat.cast_nonneg r : 0 ≤ (r:ℝ)) hT.le]
  have hlogn : log n ≤ exp T := by
    apply hln.trans
    rw [← het]
    exact exp_le_exp.mpr (by dsimp [T]; linarith)
  have hcount := finite_count n P k r hsf (hfac ▸ hSk) (hr1.trans hrk) hrk hmax hP1
    T hlogP hlogn hcut
  refine ⟨n, hnx, ?_⟩
  calc
    exp (((log 2)^2-δ)*log x/(log (log x))^2) ≤ exp ((r : ℝ)*b-log 8) := by
      apply exp_le_exp.mpr
      apply hgoal.trans
      nlinarith [mul_le_mul_of_nonneg_right (show s-5 ≤ (r : ℝ) by linarith) hb.le]
    _ = (2 : ℝ)^r / 8 := by rw [exp_sub, Real.exp_nat_mul, exp_log (by norm_num : (0:ℝ)<2), exp_log (by norm_num : (0:ℝ)<8)]
    _ ≤ _ := (div_le_iff₀ (by norm_num)).mpr (by linarith)

end ETMax

theorem OMA.solution : type_of% @Erdos1100.erdos_1100.variants.erdos_tenenbaum_max := ETMax.maximum
