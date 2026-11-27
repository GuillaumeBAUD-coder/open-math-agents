import FormalConjectures.GreensOpenProblems.«25»

-- Problem: Green's Open Problem 25, lower variant (Erdos-Sarkozy-Sos 1989): k = o(log log N)
-- Upstream: formal-conjectures FormalConjectures/GreensOpenProblems/25.lean (declaration Green25.green_25.variants.lower_ess89)
-- Own proof: set of evens avoiding S is dense; Hilbert cube lemma (Szemeredi style, with distinct generators)
-- gives k+1 elements a_j with all pairwise sums outside S, forcing k+1 distinct parts. Known result (ESS89), not an open problem.

open Finset


lemma OMA.pairs_count (A : Finset ℕ) (M : ℕ) (hA : A ⊆ range M) :
    2 * ∑ d ∈ Ico 1 M, (A.filter (fun a => a + d ∈ A)).card = A.card * (A.card - 1) := by
  have h1 : ∑ d ∈ Ico 1 M, (A.filter (fun a => a + d ∈ A)).card
      = ∑ a ∈ A, (A.filter (fun b => a < b)).card := by
    simp only [card_filter]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro a ha
    rw [← card_filter, ← card_filter]
    apply Finset.card_bij (fun d _ => a + d)
    · intro d hd
      simp only [mem_filter, mem_Ico] at hd ⊢
      exact ⟨hd.2, by omega⟩
    · intro d1 _ d2 _ h
      omega
    · intro b hb
      simp only [mem_filter] at hb
      refine ⟨b - a, ?_, by omega⟩
      have := hA hb.1
      simp only [mem_range] at this
      simp only [mem_filter, mem_Ico]
      refine ⟨⟨by omega, by omega⟩, ?_⟩
      have : a + (b - a) = b := by omega
      rw [this]; exact hb.1
  have h2 : ∑ a ∈ A, (A.filter (fun b => a < b)).card = ∑ b ∈ A, (A.filter (fun a => a < b)).card := by
    simp only [card_filter]
    rw [Finset.sum_comm]
  have h3 : ∀ a ∈ A, (A.filter (fun b => a < b)).card + (A.filter (fun b => b < a)).card = A.card - 1 := by
    intro a ha
    have := Finset.card_filter_add_card_filter_not (s := A.erase a) (fun b => a < b)
    rw [Finset.card_erase_of_mem ha] at this
    rw [← this]
    congr 1
    · congr 1; ext b; simp only [mem_filter, mem_erase]; constructor
      · rintro ⟨h, h'⟩; exact ⟨⟨by omega, h⟩, h'⟩
      · rintro ⟨⟨_, h⟩, h'⟩; exact ⟨h, h'⟩
    · congr 1; ext b; simp only [mem_filter, mem_erase]; constructor
      · rintro ⟨h, h'⟩; exact ⟨⟨by omega, h⟩, by omega⟩
      · rintro ⟨⟨h1, h⟩, h'⟩; exact ⟨h, by omega⟩
  have h4 : ∑ a ∈ A, ((A.filter (fun b => a < b)).card + (A.filter (fun b => b < a)).card)
      = A.card * (A.card - 1) := by
    rw [Finset.sum_congr rfl h3]; simp
  rw [Finset.sum_add_distrib, ← h2] at h4
  rw [h1]; omega
lemma OMA.cube_lemma (R : ℕ) : ∀ (r : ℕ) (A F : Finset ℕ) (M : ℕ), 0 < M → A ⊆ range M → F.card + r ≤ R →
    (4*R+6) * (8*M)^(2^r - 1) ≤ A.card ^ (2^r) →
    ∃ (x : ℕ) (ds : ℕ → ℕ), (∀ i < r, 0 < ds i ∧ ds i ∉ F) ∧ Set.InjOn ds (Set.Iio r) ∧
      ∀ I ⊆ range r, x + ∑ i ∈ I, ds i ∈ A := by
  intro r
  induction r with
  | zero =>
    intro A F M hM hA hF h
    simp only [pow_zero, Nat.sub_self, pow_one, mul_one] at h
    have : A.Nonempty := by
      rw [← Finset.card_pos]; omega
    obtain ⟨x, hx⟩ := this
    refine ⟨x, fun _ => 1, by simp, by simp [Set.InjOn], ?_⟩
    intro I hI
    have : I = ∅ := by simpa using hI
    simp [this, hx]
  | succ r ih =>
    intro A F M hMpos hA hF h
    set n := A.card with hn
    set q := 2 ^ r with hq
    have hqpos : 0 < q := by positivity
    have h2q : 2 ^ (r+1) = 2 * q := by rw [pow_succ]; ring
    rw [h2q] at h
    have hnM : n ≤ M := by
      have := Finset.card_le_card hA; simpa using this
    have hK : 4*R+6 ≤ n := by
      by_contra hlt
      push_neg at hlt
      have hX : 0 < (8*M)^(2*q-1) := by apply pow_pos; omega
      have h1 : n ^ (2*q) ≤ n * (8*M)^(2*q-1) := by
        have : 2*q = (2*q-1) + 1 := by omega
        rw [this, pow_succ, mul_comm]
        apply Nat.mul_le_mul_left
        calc n ^ (2*q-1) ≤ M ^ (2*q-1) := Nat.pow_le_pow_left hnM _
          _ ≤ (8*M)^(2*q-1) := Nat.pow_le_pow_left (by omega) _
      have : (4*R+6) * (8*M)^(2*q-1) ≤ n * (8*M)^(2*q-1) := le_trans h h1
      have := Nat.le_of_mul_le_mul_right this hX
      omega
    -- pair counting
    have hpc := OMA.pairs_count A M hA
    set c : ℕ → ℕ := fun d => (A.filter (fun a => a + d ∈ A)).card with hc
    have hcle : ∀ d, c d ≤ n := fun d => Finset.card_le_card (Finset.filter_subset _ _)
    set G := (Ico 1 M).filter (fun d => n * (n-1) ≤ 4 * M * c d) with hG
    have hbad : 4 * ∑ d ∈ (Ico 1 M).filter (fun d => ¬ (n * (n-1) ≤ 4 * M * c d)), c d ≤ n * (n-1) := by
      have h1 : 4 * M * ∑ d ∈ (Ico 1 M).filter (fun d => ¬ (n * (n-1) ≤ 4 * M * c d)), c d
          ≤ M * (n * (n-1)) := by
        rw [Finset.mul_sum]
        calc ∑ d ∈ (Ico 1 M).filter (fun d => ¬ (n * (n-1) ≤ 4 * M * c d)), 4 * M * c d
            ≤ ∑ d ∈ (Ico 1 M).filter (fun d => ¬ (n * (n-1) ≤ 4 * M * c d)), (n * (n-1)) := by
              apply Finset.sum_le_sum; intro d hd
              simp only [mem_filter] at hd; omega
          _ = ((Ico 1 M).filter (fun d => ¬ (n * (n-1) ≤ 4 * M * c d))).card * (n*(n-1)) := by simp
          _ ≤ M * (n * (n-1)) := by
              apply Nat.mul_le_mul_right
              calc _ ≤ (Ico 1 M).card := Finset.card_le_card (Finset.filter_subset _ _)
                _ ≤ M := by simp
      have : M * (4 * ∑ d ∈ (Ico 1 M).filter (fun d => ¬ (n * (n-1) ≤ 4 * M * c d)), c d) ≤ M * (n * (n-1)) := by
        calc _ = 4 * M * ∑ d ∈ (Ico 1 M).filter (fun d => ¬ (n * (n-1) ≤ 4 * M * c d)), c d := by ring
          _ ≤ _ := h1
      exact Nat.le_of_mul_le_mul_left this hMpos
    have hsplit : ∑ d ∈ G, c d + ∑ d ∈ (Ico 1 M).filter (fun d => ¬ (n * (n-1) ≤ 4 * M * c d)), c d = ∑ d ∈ Ico 1 M, c d := Finset.sum_filter_add_sum_filter_not (Ico 1 M) (fun d => n * (n-1) ≤ 4 * M * c d) c
    have hGsum : n * (n-1) ≤ 4 * ∑ d ∈ G, c d := by
      have : 2 * ∑ d ∈ Ico 1 M, c d = n * (n-1) := hpc
      omega
    have hGsum2 : ∑ d ∈ G, c d ≤ G.card * n := by
      calc ∑ d ∈ G, c d ≤ ∑ d ∈ G, n := Finset.sum_le_sum (fun d _ => hcle d)
        _ = G.card * n := by simp
    have hGcard : 4 * R + 2 ≤ 4 * G.card := by
      have h1 : n * (n-1) ≤ 4 * (G.card * n) := le_trans hGsum (by omega)
      have h2 : n * (n-1) ≤ n * (4 * G.card) := by nlinarith
      have := Nat.le_of_mul_le_mul_left h2 (by omega)
      omega
    have hex : ∃ d ∈ G, d ∉ F := by
      by_contra hno
      push_neg at hno
      have : G ⊆ F := hno
      have := Finset.card_le_card this
      omega
    obtain ⟨d, hdG, hdF⟩ := hex
    have hdG' := hdG
    simp only [hG, mem_filter, mem_Ico] at hdG'
    obtain ⟨⟨hd1, hdM⟩, hdc⟩ := hdG'
    set A' := A.filter (fun a => a + d ∈ A) with hA'
    have hA'sub : A' ⊆ A := Finset.filter_subset _ _
    have hA'card : A'.card = c d := rfl
    have hF' : (insert d F).card + r ≤ R := by
      have := Finset.card_insert_le d F
      omega
    have hn2 : 2 ≤ n := by omega
    have hn8 : n * n ≤ 8 * M * c d := by
      have : n * n ≤ 2 * (n * (n-1)) := by
        have : n = (n-1) + 1 := by omega
        nlinarith
      nlinarith [this, hdc]
    have hIH : (4*R+6) * (8*M)^(q - 1) ≤ A'.card ^ q := by
      have hpos : 0 < (8*M)^q := by apply pow_pos; omega
      have h1 : (n*n)^q ≤ (8*M*c d)^q := Nat.pow_le_pow_left hn8 _
      have h2 : n^(2*q) = (n*n)^q := by rw [pow_mul']; ring_nf
      have h3 : (8*M*c d)^q = (8*M)^q * (c d)^q := mul_pow _ _ _
      have h4 : (8*M)^(2*q-1) = (8*M)^(q-1) * (8*M)^q := by
        rw [← pow_add]; congr 1; omega
      have : (4*R+6) * (8*M)^(q-1) * (8*M)^q ≤ (c d)^q * (8*M)^q := by
        calc (4*R+6) * (8*M)^(q-1) * (8*M)^q = (4*R+6) * (8*M)^(2*q-1) := by rw [h4]; ring
          _ ≤ n^(2*q) := h
          _ ≤ (8*M)^q * (c d)^q := by rw [h2]; exact le_trans h1 (by rw [h3])
          _ = (c d)^q * (8*M)^q := by ring
      rw [hA'card]
      exact Nat.le_of_mul_le_mul_right this hpos
    obtain ⟨x, ds', hds'1, hds'2, hds'3⟩ := ih A' (insert d F) M hMpos (hA'sub.trans hA) hF' hIH
    refine ⟨x, fun i => if i = r then d else ds' i, ?_, ?_, ?_⟩
    · intro i hi
      by_cases hir : i = r
      · simp only [hir, if_true]
        exact ⟨by omega, hdF⟩
      · simp only [hir, if_false]
        have := hds'1 i (by omega)
        exact ⟨this.1, fun hh => this.2 (mem_insert_of_mem hh)⟩
    · intro i hi j hj hij
      simp only [Set.mem_Iio] at hi hj
      by_cases hir : i = r <;> by_cases hjr : j = r
      · omega
      · simp only [hir, hjr, if_true, if_false] at hij
        have := (hds'1 j (by omega)).2
        exfalso; apply this; rw [← hij]; exact mem_insert_self _ _
      · simp only [hir, hjr, if_true, if_false] at hij
        have := (hds'1 i (by omega)).2
        exfalso; apply this; rw [hij]; exact mem_insert_self _ _
      · simp only [hir, hjr, if_false] at hij
        exact hds'2 (by simp; omega) (by simp; omega) hij
    · intro I hI
      by_cases hrI : r ∈ I
      · have hJ : I.erase r ⊆ range r := by
          intro i hi
          have h1 := hI (mem_of_mem_erase hi)
          have h2 := ne_of_mem_erase hi
          simp only [mem_range] at h1 ⊢; omega
        have h1 := hds'3 _ hJ
        have hs : ∑ i ∈ I, (fun i => if i = r then d else ds' i) i
            = d + ∑ i ∈ I.erase r, ds' i := by
          rw [← Finset.add_sum_erase I _ hrI]
          simp only [if_true]
          congr 1
          apply Finset.sum_congr rfl
          intro i hi
          simp [ne_of_mem_erase hi]
        rw [hs]
        have h2 := (Finset.mem_filter.mp h1).2
        have : x + (d + ∑ i ∈ I.erase r, ds' i) = x + ∑ i ∈ I.erase r, ds' i + d := by ring
        rw [this]; exact h2
      · have hJ : I ⊆ range r := by
          intro i hi
          have h1 := hI hi
          have h2 : i ≠ r := fun h => hrI (h ▸ hi)
          simp only [mem_range] at h1 ⊢; omega
        have h1 := hds'3 _ hJ
        have hs : ∑ i ∈ I, (fun i => if i = r then d else ds' i) i = ∑ i ∈ I, ds' i := by
          apply Finset.sum_congr rfl
          intro i hi
          have : i ≠ r := fun h => hrI (h ▸ hi)
          simp [this]
        rw [hs]
        exact hA'sub h1
lemma OMA.key (N k : ℕ) (hN5 : 5 ≤ N)
    (hnum : (4*(k+1)+6) * 24^(2^(k+1)) ≤ N+1)
    (P : Finpartition (Icc 1 N)) (hk : P.parts.card = k)
    (hS : 10 * (P.parts.biUnion Finset.restrictedSumset).card < N) : False := by
  set S := P.parts.biUnion Finset.restrictedSumset with hSdef
  set R := k + 1 with hR
  set A : Finset ℕ := (range (N+1)).filter (fun m => Even m ∧ m ∉ S) with hA
  have hAsub : A ⊆ range (N+1) := Finset.filter_subset _ _
  have hAcard : N + 1 ≤ 3 * A.card := by
    have h1 : ((range (N/2+1)).image (fun i => 2*i)).card = N/2+1 := by
      rw [Finset.card_image_of_injective _ (fun a b h => by simpa using h)]; simp
    have h2 := Finset.le_card_sdiff S ((range (N/2+1)).image (fun i => 2*i))
    have h3 : ((range (N/2+1)).image (fun i => 2*i)) \ S ⊆ A := by
      intro m hm
      simp only [mem_sdiff, mem_image, mem_range] at hm
      obtain ⟨⟨i, hi, rfl⟩, hmS⟩ := hm
      simp only [hA, mem_filter, mem_range]
      exact ⟨by omega, ⟨i, by ring⟩, hmS⟩
    have h4 := Finset.card_le_card h3
    omega
  have hq : 0 < 2^R := by positivity
  have hineq : (4*R+6) * (8*(N+1))^(2^R - 1) ≤ A.card ^ (2^R) := by
    set q := 2^R with hqdef
    have hM : (4*R+6) * 24^q ≤ N+1 := hnum
    have h1 : (4*R+6) * (8*(N+1))^(q-1) * 3^q ≤ (N+1)^q := by
      have e1 : (8*(N+1))^(q-1) * 3^q ≤ 24^q * (N+1)^(q-1) := by
        have : (8*(N+1))^(q-1) * 3^q = 8^(q-1) * 3^(q-1) * 3 * (N+1)^(q-1) := by
          rw [mul_pow]
          have : 3^q = 3^(q-1) * 3 := by rw [← pow_succ]; congr 1; omega
          rw [this]; ring
        rw [this]
        have : 24^q = 8^(q-1)*3^(q-1)*24 := by
          have : 24^q = 24^(q-1) * 24 := by rw [← pow_succ]; congr 1; omega
          rw [this, show (24:ℕ) = 8*3 by norm_num, mul_pow]
        rw [this]
        nlinarith [Nat.zero_le (8^(q-1)*3^(q-1)*(N+1)^(q-1))]
      calc (4*R+6) * (8*(N+1))^(q-1) * 3^q = (4*R+6) * ((8*(N+1))^(q-1) * 3^q) := by ring
        _ ≤ (4*R+6) * (24^q * (N+1)^(q-1)) := Nat.mul_le_mul_left _ e1
        _ = ((4*R+6) * 24^q) * (N+1)^(q-1) := by ring
        _ ≤ (N+1) * (N+1)^(q-1) := Nat.mul_le_mul_right _ hM
        _ = (N+1)^q := by rw [← pow_succ']; congr 1; omega
    have h2 : (N+1)^q ≤ (3 * A.card)^q := Nat.pow_le_pow_left hAcard _
    rw [mul_pow] at h2
    have : (4*R+6) * (8*(N+1))^(q-1) * 3^q ≤ A.card^q * 3^q := by
      calc _ ≤ (N+1)^q := h1
        _ ≤ 3^q * A.card^q := by rw [mul_pow] at *; exact h2
        _ = A.card^q * 3^q := by ring
    exact Nat.le_of_mul_le_mul_right this (by positivity)
  obtain ⟨x, ds, hds1, hds2, hds3⟩ :=
    OMA.cube_lemma R R A ∅ (N+1) (by omega) hAsub (by simp) hineq
  have hx : x ∈ A := by simpa using hds3 ∅ (by simp)
  have hxeven : Even x := (Finset.mem_filter.mp hx).2.1
  obtain ⟨y, hy⟩ := hxeven
  have hsingle : ∀ j < R, x + ds j ≤ N := by
    intro j hj
    have := hds3 {j} (by simpa using hj)
    have h2 := hAsub this
    simp only [sum_singleton, mem_range] at h2; omega
  have hpair : ∀ i < R, ∀ j < R, i ≠ j → x + ds i + ds j ∈ A := by
    intro i hi j hj hij
    have := hds3 {i, j} (by intro t ht; simp at ht; rcases ht with rfl | rfl <;> simpa)
    rw [Finset.sum_pair hij] at this
    rwa [← add_assoc] at this
  set a : ℕ → ℕ := fun j => y + ds j with ha
  have hamem : ∀ j < R, a j ∈ Icc 1 N := by
    intro j hj
    have := hsingle j hj
    have := (hds1 j hj).1
    simp only [ha, mem_Icc]; omega
  have hinj : Set.InjOn (fun j => P.part (a j)) (Set.Iio R) := by
    intro i hi j hj hij
    simp only [Set.mem_Iio] at hi hj
    by_contra hne
    have hpi := (P.part_mem).2 (hamem i hi)
    have hai : a i ∈ P.part (a i) := (P.mem_part_self).2 (hamem i hi)
    have haj : a j ∈ P.part (a j) := (P.mem_part_self).2 (hamem j hj)
    simp only at hij
    rw [← hij] at haj
    have hne' : a i ≠ a j := by
      intro h
      apply hne
      apply hds2 (by simpa using hi) (by simpa using hj)
      simp only [ha] at h; omega
    have hmem : a i + a j ∈ S := by
      rw [hSdef, mem_biUnion]
      refine ⟨P.part (a i), hpi, ?_⟩
      simp only [Finset.restrictedSumset, mem_image, mem_offDiag]
      exact ⟨(a i, a j), ⟨hai, haj, hne'⟩, rfl⟩
    have := hpair i hi j hj hne
    have h2 := (Finset.mem_filter.mp this).2.2
    apply h2
    have : x + ds i + ds j = a i + a j := by simp only [ha]; omega
    rw [this]; exact hmem
  have hle : (range R).card ≤ P.parts.card := by
    apply Finset.card_le_card_of_injOn (fun j => P.part (a j))
    · intro j hj
      simp only [coe_range, Set.mem_Iio] at hj
      exact (P.part_mem).2 (hamem j hj)
    · simpa using hinj
  simp at hle
  omega
lemma OMA.arith_bound (k N : ℕ) (hN : 400 ≤ Real.log N)
    (hk : (k:ℝ) ≤ 1/2 * Real.log (Real.log N)) :
    (4*(k+1)+6) * 24^(2^(k+1)) ≤ N+1 := by
  set L := Real.log N with hL
  have hLpos : 0 < L := by linarith
  set s := Real.sqrt L with hs
  have hs2 : s^2 = L := Real.sq_sqrt hLpos.le
  have hs20 : 20 ≤ s := by
    rw [hs]; apply Real.le_sqrt_of_sq_le; linarith
  have hspos : 0 < s := by linarith
  have hlogL : Real.log L = 2 * Real.log s := by
    rw [← hs2, Real.log_pow]; norm_num
  have hlogs : Real.log s ≤ s - 1 := Real.log_le_sub_one_of_pos hspos
  have hk2 : (k:ℝ) ≤ Real.log s := by rw [hlogL] at hk; linarith
  have hkpos : (0:ℝ) ≤ k := Nat.cast_nonneg k
  have hlog2 : Real.log 2 ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (show (0:ℝ) < 2 by norm_num); linarith
  have hlog2p : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have ht : ((2:ℝ)^(k+1)) ≤ 3 * s := by
    have h1 : ((2:ℝ)^(k+1)) = Real.exp (((k:ℝ)+1) * Real.log 2) := by
      have := Real.exp_log (show (0:ℝ) < 2^(k+1) by positivity)
      rw [Real.log_pow] at this
      push_cast at this
      exact this.symm
    rw [h1]
    have h2 : ((k:ℝ)+1) * Real.log 2 ≤ Real.log s + 1 := by
      nlinarith
    calc Real.exp (((k:ℝ)+1) * Real.log 2) ≤ Real.exp (Real.log s + 1) := Real.exp_le_exp.2 h2
      _ = s * Real.exp 1 := by rw [Real.exp_add, Real.exp_log hspos]
      _ ≤ s * 3 := by
        apply mul_le_mul_of_nonneg_left _ hspos.le
        have := Real.exp_one_lt_d9; linarith
      _ = 3 * s := by ring
  have hlog24 : Real.log 24 ≤ 4 := by
    rw [Real.log_le_iff_le_exp (by norm_num)]
    have h1 : Real.exp 4 = (Real.exp 1)^4 := by rw [← Real.exp_nat_mul]; norm_num
    rw [h1]
    have := Real.exp_one_gt_d9
    have h3 : (2.7:ℝ)^4 ≤ (Real.exp 1)^4 := by
      apply pow_le_pow_left₀ (by norm_num); linarith
    nlinarith
  have hpos : (0:ℝ) < (4*((k:ℝ)+1)+6) * (24:ℝ)^(2^(k+1)) := by positivity
  have hmain : Real.log ((4*((k:ℝ)+1)+6) * (24:ℝ)^(2^(k+1))) ≤ L := by
    rw [Real.log_mul (by positivity) (by positivity), Real.log_pow]
    have h1 : Real.log (4*((k:ℝ)+1)+6) ≤ 4*((k:ℝ)+1)+6 - 1 :=
      Real.log_le_sub_one_of_pos (by positivity)
    have h2 : ((2^(k+1) : ℕ) : ℝ) * Real.log 24 ≤ 3 * s * 4 := by
      push_cast
      have : (0:ℝ) ≤ Real.log 24 := Real.log_nonneg (by norm_num)
      calc (2:ℝ)^(k+1) * Real.log 24 ≤ (3*s) * Real.log 24 :=
            mul_le_mul_of_nonneg_right ht this
        _ ≤ 3*s*4 := mul_le_mul_of_nonneg_left hlog24 (by positivity)
    nlinarith
  have hle : (4*((k:ℝ)+1)+6) * (24:ℝ)^(2^(k+1)) ≤ N := by
    have hNpos : (0:ℝ) < N := by
      rcases Nat.eq_zero_or_pos N with h | h
      · exfalso; rw [h] at hL; simp at hL; linarith
      · exact_mod_cast h
    rwa [← Real.log_le_log_iff hpos hNpos]
  have : ((4*(k+1)+6) * 24^(2^(k+1)) : ℕ) ≤ N := by exact_mod_cast hle
  omega

theorem OMA.solution : type_of% @Green25.green_25.variants.lower_ess89 := by
  intro k hk
  obtain ⟨hk1, hlo⟩ := hk
  have h2 : ∀ᶠ N : ℕ in Filter.atTop, 400 ≤ Real.log (N:ℝ) :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop 400
  have h1 : ∀ᶠ N in Filter.atTop, (k N : ℝ) ≤ 1/2 * Real.log (Real.log N) := by
    have := hlo.def (show (0:ℝ) < 1/2 by norm_num)
    filter_upwards [this, h2] with N hN hL
    have h0 : 0 ≤ Real.log (Real.log N) := Real.log_nonneg (by linarith)
    simp only [Green25.bestLower, Real.norm_eq_abs, abs_of_nonneg h0, Nat.abs_cast] at hN
    exact hN
  filter_upwards [hk1, h1, h2, Filter.eventually_ge_atTop 5] with N hk1' hlog hL h5
  refine ⟨hk1'.1, hk1'.2, ?_⟩
  intro P hP
  by_contra hcon
  have hcon' : 10 * (P.parts.biUnion Finset.restrictedSumset).card < N := by omega
  exact OMA.key N (k N) h5 (OMA.arith_bound (k N) N hL hlog) P hP hcon'
