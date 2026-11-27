import OMAReductions.R_Erdos69_erdos_69_R1_H1_R1

-- Step Erdos69.erdos_69.R1.H1.R1.H1 (Erdős Problem 69): existence of the cube of primes
-- Credit: @chris01-dev

/-!
Existence of the data of the Tao–Teräväinen argument at every large scale: a cube of primes in
`[exp (l ^ 3) / 8, exp (l ^ 3)]` with distinct near shifts, and its progression.

* `primes_dense`: Chebyshev bounds give at least `P / (4 log P)` primes in `[P / 8, P]`.
* `cube_greedy`, `cube_exists`: a greedy form of the Hilbert cube lemma. Each new side is a
  popular difference of the current set, chosen outside a small forbidden set that makes all
  subset sums (with the weights of every near shift) injective; the base point is then chosen
  to avoid the collisions between different shifts.
* `cube_data`: the family `p E`, the shifts `s E`, the symmetry of `p E * h - s E`.
* `crt_exists`: the residue class, by the Chinese remainder theorem.
* `numeric`: the hierarchy of scales in terms of `l = log log log x`.
-/

namespace E69S1

/-- Counting pairs of a set of integers in `[0, M]` by their difference. -/
lemma sum_card_shift (A : Finset ℤ) (M : ℕ) (hA : ∀ a ∈ A, 0 ≤ a ∧ a ≤ M) :
    ∑ d ∈ Finset.Icc (-(M : ℤ)) M, (A.filter (fun a => a + d ∈ A)).card = A.card ^ 2 := by
  rw [sq, ← Finset.card_product,
    Finset.card_eq_sum_card_fiberwise (f := fun x : ℤ × ℤ => x.2 - x.1)
      (t := Finset.Icc (-(M : ℤ)) M) (s := A ×ˢ A)]
  · refine Finset.sum_congr rfl fun d _ => ?_
    refine Finset.card_bij' (fun a _ => (a, a + d)) (fun x _ => x.1) ?_ ?_ ?_ ?_
    · intro a ha
      obtain ⟨ha1, ha2⟩ := Finset.mem_filter.mp ha
      exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨ha1, ha2⟩, by simp⟩
    · intro x hx
      obtain ⟨hx1, hx2⟩ := Finset.mem_filter.mp hx
      obtain ⟨h1, h2⟩ := Finset.mem_product.mp hx1
      refine Finset.mem_filter.mpr ⟨h1, ?_⟩
      have : x.1 + d = x.2 := by
        have h3 : x.2 - x.1 = d := hx2
        omega
      rw [this]
      exact h2
    · intro a _
      rfl
    · intro x hx
      obtain ⟨_, hx2⟩ := Finset.mem_filter.mp hx
      have h3 : x.2 - x.1 = d := hx2
      ext
      · rfl
      · show x.1 + d = x.2
        omega
  · intro x hx
    obtain ⟨h1, h2⟩ := Finset.mem_product.mp hx
    have a1 := hA _ h1
    have a2 := hA _ h2
    rw [Finset.mem_coe, Finset.mem_Icc]
    show -(M : ℤ) ≤ x.2 - x.1 ∧ x.2 - x.1 ≤ M
    constructor <;> omega

/-- A popular difference avoiding a small forbidden set. -/
lemma exists_good_shift (A F : Finset ℤ) (M : ℕ) (hA : ∀ a ∈ A, 0 ≤ a ∧ a ≤ M)
    (hF : 2 * F.card ≤ A.card) :
    ∃ d, d ∉ F ∧ |d| ≤ M ∧
      A.card ^ 2 ≤ 2 * (2 * M + 1) * (A.filter (fun a => a + d ∈ A)).card := by
  classical
  rcases Finset.eq_empty_or_nonempty A with hAe | hAne
  · subst hAe
    have hF0 : F = ∅ := by
      rw [← Finset.card_eq_zero]
      simpa using hF
    exact ⟨0, by simp [hF0], by simp, by simp⟩
  by_contra hcon
  push Not at hcon
  have hsum := sum_card_shift A M hA
  have hApos : 0 < A.card := Finset.card_pos.mpr hAne
  have hbound : ∀ d ∈ Finset.Icc (-(M : ℤ)) M,
      2 * (2 * M + 1) * (A.filter (fun a => a + d ∈ A)).card
        ≤ (if d ∈ F then 2 * (2 * M + 1) * A.card else 0) + (A.card ^ 2 - 1) := by
    intro d hd
    by_cases hdF : d ∈ F
    · rw [if_pos hdF]
      have : (A.filter (fun a => a + d ∈ A)).card ≤ A.card := Finset.card_filter_le _ _
      have := Nat.mul_le_mul_left (2 * (2 * M + 1)) this
      omega
    · rw [if_neg hdF, zero_add]
      have hdM : |d| ≤ M := by
        rw [abs_le]
        exact Finset.mem_Icc.mp hd
      have := hcon d hdF hdM
      omega
  have h1 : 2 * (2 * M + 1) * A.card ^ 2
      ≤ ∑ d ∈ Finset.Icc (-(M : ℤ)) M,
        ((if d ∈ F then 2 * (2 * M + 1) * A.card else 0) + (A.card ^ 2 - 1)) := by
    have e : 2 * (2 * M + 1) * A.card ^ 2 = ∑ d ∈ Finset.Icc (-(M : ℤ)) M,
        2 * (2 * M + 1) * (A.filter (fun a => a + d ∈ A)).card := by
      rw [← hsum, Finset.mul_sum]
    rw [e]
    exact Finset.sum_le_sum hbound
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.sum_ite_mem, Finset.sum_const] at h1
  have hcI : (Finset.Icc (-(M : ℤ)) M).card = 2 * M + 1 := by
    rw [Int.card_Icc]
    omega
  have hcF : (Finset.Icc (-(M : ℤ)) M ∩ F).card ≤ F.card :=
    Finset.card_le_card Finset.inter_subset_right
  rw [hcI, smul_eq_mul, smul_eq_mul] at h1
  have h2 : (Finset.Icc (-(M : ℤ)) M ∩ F).card * (2 * (2 * M + 1) * A.card)
      ≤ F.card * (2 * (2 * M + 1) * A.card) := Nat.mul_le_mul_right _ hcF
  have h3 : F.card * (2 * (2 * M + 1) * A.card) ≤ (2 * M + 1) * A.card ^ 2 := by
    have : 2 * F.card * ((2 * M + 1) * A.card) ≤ A.card * ((2 * M + 1) * A.card) :=
      Nat.mul_le_mul_right _ hF
    nlinarith
  have h4 : 1 ≤ A.card ^ 2 := Nat.one_le_pow _ _ hApos
  have h5 : (2 * M + 1) * (A.card ^ 2 - 1) + (2 * M + 1) = (2 * M + 1) * A.card ^ 2 := by
    have : A.card ^ 2 - 1 + 1 = A.card ^ 2 := Nat.sub_add_cancel h4
    calc (2 * M + 1) * (A.card ^ 2 - 1) + (2 * M + 1)
        = (2 * M + 1) * (A.card ^ 2 - 1 + 1) := by ring
      _ = (2 * M + 1) * A.card ^ 2 := by rw [this]
  nlinarith

/-- Greedy construction of a Hilbert cube inside a dense set of integers, with each side
avoiding a forbidden set that depends only on the earlier sides. -/
lemma cube_greedy (M f : ℕ) (Forb : ℕ → (ℕ → ℤ) → Finset ℤ)
    (hForb : ∀ k v, (Forb k v).card ≤ f)
    (hdep : ∀ k v v', (∀ i < k, v i = v' i) → Forb k v = Forb k v')
    (A : Finset ℤ) (hA : ∀ a ∈ A, 0 ≤ a ∧ a ≤ M) (K : ℕ)
    (hsize : ∀ k ≤ K, 2 * f * (2 * (2 * M + 1)) ^ (2 ^ k - 1) ≤ A.card ^ (2 ^ k)) :
    ∃ (v : ℕ → ℤ) (A' : Finset ℤ), A' ⊆ A ∧ 2 * f ≤ A'.card ∧
      (∀ k < K, v k ∉ Forb k v ∧ |v k| ≤ M) ∧
      ∀ a ∈ A', ∀ E ⊆ Finset.range K, a + ∑ k ∈ E, v k ∈ A := by
  classical
  have key : ∀ K, (∀ k ≤ K, 2 * f * (2 * (2 * M + 1)) ^ (2 ^ k - 1) ≤ A.card ^ (2 ^ k)) →
      ∃ (v : ℕ → ℤ) (A' : Finset ℤ), A' ⊆ A ∧
        A.card ^ (2 ^ K) ≤ (2 * (2 * M + 1)) ^ (2 ^ K - 1) * A'.card ∧
        (∀ k < K, v k ∉ Forb k v ∧ |v k| ≤ M) ∧
        ∀ a ∈ A', ∀ E ⊆ Finset.range K, a + ∑ k ∈ E, v k ∈ A := by
    intro K
    induction K with
    | zero =>
      intro _
      refine ⟨fun _ => 0, A, subset_rfl, by simp, by simp, ?_⟩
      intro a ha E hE
      have : E = ∅ := by simpa using hE
      simpa [this] using ha
    | succ K ih =>
      intro hs
      obtain ⟨v, A', hsub, hcard, hforb, hcube⟩ := ih (fun k hk => hs k (by omega))
      have hsK := hs K (by omega)
      have hc0 : 0 < (2 * (2 * M + 1)) ^ (2 ^ K - 1) := by positivity
      have h2f : 2 * (Forb K v).card ≤ A'.card := by
        have h1 : 2 * f * (2 * (2 * M + 1)) ^ (2 ^ K - 1)
            ≤ (2 * (2 * M + 1)) ^ (2 ^ K - 1) * A'.card := hsK.trans hcard
        have h2 : 2 * f ≤ A'.card := by
          by_contra hlt
          push Not at hlt
          have := Nat.mul_lt_mul_of_pos_left hlt hc0
          nlinarith
        have := hForb K v
        omega
      obtain ⟨d, hdF, hdM, hdcard⟩ := exists_good_shift A' (Forb K v) M
        (fun a ha => hA a (hsub ha)) h2f
      refine ⟨Function.update v K d, A'.filter (fun a => a + d ∈ A'),
        (Finset.filter_subset _ _).trans hsub, ?_, ?_, ?_⟩
      · have e : 2 ^ (K + 1) - 1 = 2 * (2 ^ K - 1) + 1 := by
          have : 1 ≤ 2 ^ K := Nat.one_le_two_pow
          rw [pow_succ]
          omega
        have e1 : A.card ^ 2 ^ (K + 1) = (A.card ^ 2 ^ K) ^ 2 := by
          rw [pow_succ 2 K, pow_mul]
        have e2 : (2 * (2 * M + 1)) ^ (2 ^ (K + 1) - 1)
            = ((2 * (2 * M + 1)) ^ (2 ^ K - 1)) ^ 2 * (2 * (2 * M + 1)) := by
          rw [e, pow_succ, mul_comm 2 (2 ^ K - 1), pow_mul]
        rw [e1, e2]
        calc (A.card ^ 2 ^ K) ^ 2
            ≤ ((2 * (2 * M + 1)) ^ (2 ^ K - 1) * A'.card) ^ 2 := Nat.pow_le_pow_left hcard 2
          _ = ((2 * (2 * M + 1)) ^ (2 ^ K - 1)) ^ 2 * A'.card ^ 2 := by ring
          _ ≤ ((2 * (2 * M + 1)) ^ (2 ^ K - 1)) ^ 2
              * (2 * (2 * M + 1) * (A'.filter (fun a => a + d ∈ A')).card) :=
            Nat.mul_le_mul_left _ hdcard
          _ = ((2 * (2 * M + 1)) ^ (2 ^ K - 1)) ^ 2 * (2 * (2 * M + 1))
              * (A'.filter (fun a => a + d ∈ A')).card := by ring
      · intro k hk
        have hagree : ∀ i < k, Function.update v K d i = v i := by
          intro i hi
          exact Function.update_of_ne (by omega) _ _
        rw [hdep k (Function.update v K d) v hagree]
        rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hlt | heq
        · rw [Function.update_of_ne (by omega)]
          exact hforb k hlt
        · subst heq
          rw [Function.update_self]
          exact ⟨hdF, hdM⟩
      · intro a ha E hE
        obtain ⟨haA, had⟩ := Finset.mem_filter.mp ha
        by_cases hKE : K ∈ E
        · have hE' : E.erase K ⊆ Finset.range K := by
            intro i hi
            have h1 := Finset.mem_of_mem_erase hi
            have h2 := Finset.ne_of_mem_erase hi
            have := Finset.mem_range.mp (hE h1)
            exact Finset.mem_range.mpr (by omega)
          have hsumE : ∑ k ∈ E, Function.update v K d k = d + ∑ k ∈ E.erase K, v k := by
            rw [← Finset.add_sum_erase E _ hKE, Function.update_self]
            congr 1
            refine Finset.sum_congr rfl fun i hi => ?_
            exact Function.update_of_ne (Finset.ne_of_mem_erase hi) _ _
          rw [hsumE, ← add_assoc]
          exact hcube (a + d) had _ hE'
        · have hE' : E ⊆ Finset.range K := by
            intro i hi
            have := Finset.mem_range.mp (hE hi)
            have hne : i ≠ K := fun h => hKE (by rw [← h]; exact hi)
            exact Finset.mem_range.mpr (by omega)
          have hsumE : ∑ k ∈ E, Function.update v K d k = ∑ k ∈ E, v k := by
            refine Finset.sum_congr rfl fun i hi => ?_
            exact Function.update_of_ne (fun h => hKE (by rw [← h]; exact hi)) _ _
          rw [hsumE]
          exact hcube a haA _ hE'
  obtain ⟨v, A', hsub, hcard, hforb, hcube⟩ := key K hsize
  refine ⟨v, A', hsub, ?_, hforb, hcube⟩
  have hsK := hsize K le_rfl
  have hc0 : 0 < (2 * (2 * M + 1)) ^ (2 ^ K - 1) := by positivity
  by_contra hlt
  push Not at hlt
  have := Nat.mul_lt_mul_of_pos_left hlt hc0
  have h1 := hsK.trans hcard
  nlinarith



/-- Subset sums with nonzero coefficients are injective when each new term avoids all
differences of earlier subset sums. -/
lemma inj_of_forb (c : ℕ → ℤ) (v : ℕ → ℤ) (K : ℕ)
    (hv : ∀ k < K, ∀ E ∈ (Finset.range k).powerset, ∀ E' ∈ (Finset.range k).powerset,
      c k * v k ≠ ∑ j ∈ E', c j * v j - ∑ j ∈ E, c j * v j) :
    Set.InjOn (fun E : Finset ℕ => ∑ j ∈ E, c j * v j)
      ((Finset.range K).powerset : Set (Finset ℕ)) := by
  classical
  induction K with
  | zero =>
    intro E hE E' hE' _
    have h1 : E = ∅ := by simpa using hE
    have h2 : E' = ∅ := by simpa using hE'
    rw [h1, h2]
  | succ n ih =>
    have ih' := ih (fun k hk => hv k (by omega))
    have herase : ∀ E : Finset ℕ, E ⊆ Finset.range (n + 1) → E.erase n ⊆ Finset.range n := by
      intro E hE i hi
      have h1 := Finset.mem_range.mp (hE (Finset.mem_of_mem_erase hi))
      have h2 := Finset.ne_of_mem_erase hi
      exact Finset.mem_range.mpr (by omega)
    have hnot : ∀ E : Finset ℕ, E ⊆ Finset.range (n + 1) → n ∉ E → E ⊆ Finset.range n := by
      intro E hE hn i hi
      have h1 := Finset.mem_range.mp (hE hi)
      have h2 : i ≠ n := fun h => hn (by rw [← h]; exact hi)
      exact Finset.mem_range.mpr (by omega)
    intro E hE E' hE' heq
    have hE1 : E ⊆ Finset.range (n + 1) := Finset.mem_powerset.mp (Finset.mem_coe.mp hE)
    have hE1' : E' ⊆ Finset.range (n + 1) := Finset.mem_powerset.mp (Finset.mem_coe.mp hE')
    have heq' : ∑ j ∈ E, c j * v j = ∑ j ∈ E', c j * v j := heq
    by_cases h1 : n ∈ E
    · by_cases h2 : n ∈ E'
      · rw [← Finset.add_sum_erase E _ h1, ← Finset.add_sum_erase E' _ h2] at heq'
        have h3 : E.erase n = E'.erase n :=
          ih' (Finset.mem_coe.mpr (Finset.mem_powerset.mpr (herase E hE1)))
            (Finset.mem_coe.mpr (Finset.mem_powerset.mpr (herase E' hE1')))
            (by simpa using heq')
        rw [← Finset.insert_erase h1, ← Finset.insert_erase h2, h3]
      · exfalso
        rw [← Finset.add_sum_erase E _ h1] at heq'
        exact hv n (by omega) (E.erase n) (Finset.mem_powerset.mpr (herase E hE1)) E'
          (Finset.mem_powerset.mpr (hnot E' hE1' h2)) (by linarith)
    · by_cases h2 : n ∈ E'
      · exfalso
        rw [← Finset.add_sum_erase E' _ h2] at heq'
        exact hv n (by omega) (E'.erase n) (Finset.mem_powerset.mpr (herase E' hE1')) E
          (Finset.mem_powerset.mpr (hnot E hE1 h1)) (by linarith)
      · exact ih' (Finset.mem_coe.mpr (Finset.mem_powerset.mpr (hnot E hE1 h1)))
          (Finset.mem_coe.mpr (Finset.mem_powerset.mpr (hnot E' hE1' h2))) heq

/-- A generic Hilbert cube inside a dense set of integers: distinct vertices and distinct
near shifts. -/
lemma cube_exists (K H M : ℕ) (A : Finset ℤ) (hA : ∀ a ∈ A, 0 ≤ a ∧ a ≤ M)
    (hsize : ∀ k ≤ K, 2 * (4 ^ K * (H + 1) ^ 2) * (2 * (2 * M + 1)) ^ (2 ^ k - 1)
      ≤ A.card ^ (2 ^ k)) :
    ∃ (a : ℤ) (v : ℕ → ℤ), (∀ k < K, |v k| ≤ M) ∧
      (∀ E ∈ (Finset.range K).powerset, a + ∑ k ∈ E, v k ∈ A) ∧
      Set.InjOn (fun E : Finset ℕ => ∑ k ∈ E, v k)
        ((Finset.range K).powerset : Set (Finset ℕ)) ∧
      Set.InjOn (fun x : Finset ℕ × ℕ => a * (x.2 : ℤ) + ∑ k ∈ x.1, ((x.2 : ℤ) - (k + 1)) * v k)
        (((Finset.range K).powerset ×ˢ Finset.Ico (K + 1) (K + H + 1) :
          Finset (Finset ℕ × ℕ)) : Set (Finset ℕ × ℕ)) := by
  classical
  obtain ⟨T, hT⟩ : ∃ T : Finset ℕ, T = insert 0 (Finset.Ico (K + 1) (K + H + 1)) := ⟨_, rfl⟩
  have hTcard : T.card ≤ H + 1 := by
    rw [hT]
    refine (Finset.card_insert_le _ _).trans ?_
    rw [Nat.card_Ico]
    omega
  obtain ⟨c, hc⟩ : ∃ c : ℕ → ℕ → ℤ, ∀ m k, c m k = if m = 0 then 1 else (m : ℤ) - (k + 1) :=
    ⟨_, fun _ _ => rfl⟩
  have hcne : ∀ m ∈ T, ∀ k < K, c m k ≠ 0 := by
    intro m hm k hk
    rw [hc]
    split_ifs with h0
    · exact one_ne_zero
    · rw [hT] at hm
      rcases Finset.mem_insert.mp hm with h | h
      · exact absurd h h0
      · have := (Finset.mem_Ico.mp h).1
        have : ((k : ℤ) + 1) < m := by exact_mod_cast (by omega : k + 1 < m)
        omega
  obtain ⟨Forb, hForbdef⟩ : ∃ Forb : ℕ → (ℕ → ℤ) → Finset ℤ, ∀ k v, Forb k v =
      if k < K then (T ×ˢ ((Finset.range k).powerset ×ˢ (Finset.range k).powerset)).image
        (fun x => (∑ j ∈ x.2.2, c x.1 j * v j - ∑ j ∈ x.2.1, c x.1 j * v j) / c x.1 k)
      else ∅ := ⟨_, fun _ _ => rfl⟩
  have hf1 : 1 ≤ 4 ^ K * (H + 1) ^ 2 := Nat.one_le_iff_ne_zero.mpr (by positivity)
  have hForb : ∀ k v, (Forb k v).card ≤ 4 ^ K * (H + 1) ^ 2 := by
    intro k v
    rw [hForbdef]
    split_ifs with hk
    · refine Finset.card_image_le.trans ?_
      rw [Finset.card_product, Finset.card_product, Finset.card_powerset, Finset.card_range]
      have h1 : 2 ^ k * 2 ^ k ≤ 4 ^ K := by
        rw [← pow_add, show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_mul]
        exact Nat.pow_le_pow_right (by norm_num) (by omega)
      calc T.card * (2 ^ k * 2 ^ k) ≤ (H + 1) * 4 ^ K := Nat.mul_le_mul hTcard h1
        _ ≤ 4 ^ K * (H + 1) ^ 2 := by nlinarith [Nat.one_le_two_pow (n := K), hf1]
    · simp
  have hdep : ∀ k v v', (∀ i < k, v i = v' i) → Forb k v = Forb k v' := by
    intro k v v' hvv
    rw [hForbdef, hForbdef]
    split_ifs with hk
    · refine Finset.image_congr ?_
      intro x hx
      obtain ⟨_, hx2⟩ := Finset.mem_product.mp (Finset.mem_coe.mp hx)
      obtain ⟨hxa, hxb⟩ := Finset.mem_product.mp hx2
      have e1 : ∑ j ∈ x.2.2, c x.1 j * v j = ∑ j ∈ x.2.2, c x.1 j * v' j :=
        Finset.sum_congr rfl fun j hj => by
          rw [hvv j (Finset.mem_range.mp (Finset.mem_powerset.mp hxb hj))]
      have e2 : ∑ j ∈ x.2.1, c x.1 j * v j = ∑ j ∈ x.2.1, c x.1 j * v' j :=
        Finset.sum_congr rfl fun j hj => by
          rw [hvv j (Finset.mem_range.mp (Finset.mem_powerset.mp hxa hj))]
      show (∑ j ∈ x.2.2, c x.1 j * v j - ∑ j ∈ x.2.1, c x.1 j * v j) / c x.1 k
        = (∑ j ∈ x.2.2, c x.1 j * v' j - ∑ j ∈ x.2.1, c x.1 j * v' j) / c x.1 k
      rw [e1, e2]
    · rfl
  obtain ⟨v, A', hsub, h2f, hforb, hcube⟩ :=
    cube_greedy M (4 ^ K * (H + 1) ^ 2) Forb hForb hdep A hA K hsize
  have hmode : ∀ m ∈ T, Set.InjOn (fun E : Finset ℕ => ∑ j ∈ E, c m j * v j)
      ((Finset.range K).powerset : Set (Finset ℕ)) := by
    intro m hm
    refine inj_of_forb (c m) v K ?_
    intro k hk E hE E' hE' heq
    apply (hforb k hk).1
    rw [hForbdef, if_pos hk]
    refine Finset.mem_image.mpr ⟨(m, E, E'), ?_, ?_⟩
    · exact Finset.mem_product.mpr ⟨hm, Finset.mem_product.mpr ⟨hE, hE'⟩⟩
    · show (∑ j ∈ E', c m j * v j - ∑ j ∈ E, c m j * v j) / c m k = v k
      rw [← heq]
      exact Int.mul_ediv_cancel_left _ (hcne m hm k hk)
  -- the base point avoids the collisions between different shifts
  obtain ⟨S, hS⟩ : ∃ S : Finset (Finset ℕ × ℕ),
      S = (Finset.range K).powerset ×ˢ Finset.Ico (K + 1) (K + H + 1) := ⟨_, rfl⟩
  obtain ⟨Fa, hFa⟩ : ∃ Fa : Finset ℤ, Fa = (S ×ˢ S).image (fun y =>
      (∑ k ∈ y.2.1, ((y.2.2 : ℤ) - (k + 1)) * v k - ∑ k ∈ y.1.1, ((y.1.2 : ℤ) - (k + 1)) * v k)
        / ((y.1.2 : ℤ) - y.2.2)) := ⟨_, rfl⟩
  have hScard : S.card = 2 ^ K * H := by
    rw [hS, Finset.card_product, Finset.card_powerset, Finset.card_range, Nat.card_Ico]
    congr 1
    omega
  have hFacard : Fa.card ≤ 4 ^ K * (H + 1) ^ 2 := by
    rw [hFa]
    refine Finset.card_image_le.trans ?_
    rw [Finset.card_product, hScard]
    have : (2 ^ K * H) * (2 ^ K * H) = 4 ^ K * H ^ 2 := by
      rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_mul]
      ring
    rw [this]
    exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 2)
  obtain ⟨a, haA', haFa⟩ : ∃ a ∈ A', a ∉ Fa :=
    Finset.exists_mem_notMem_of_card_lt_card (by omega)
  refine ⟨a, v, fun k hk => (hforb k hk).2, ?_, ?_, ?_⟩
  · intro E hE
    exact hcube a haA' E (Finset.mem_powerset.mp hE)
  · have h0 := hmode 0 (by rw [hT]; exact Finset.mem_insert_self _ _)
    intro E hE E' hE' heq
    refine h0 hE hE' ?_
    have e : ∀ F : Finset ℕ, ∑ j ∈ F, c 0 j * v j = ∑ j ∈ F, v j := by
      intro F
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [hc, if_pos rfl, one_mul]
    show ∑ j ∈ E, c 0 j * v j = ∑ j ∈ E', c 0 j * v j
    rw [e, e]
    exact heq
  · rw [← hS]
    intro x hx x' hx' heq
    have hx1 := Finset.mem_coe.mp hx
    have hx1' := Finset.mem_coe.mp hx'
    have hxp := hx1
    have hxp' := hx1'
    rw [hS] at hxp hxp'
    obtain ⟨hxE, hxh⟩ := Finset.mem_product.mp hxp
    obtain ⟨hxE', hxh'⟩ := Finset.mem_product.mp hxp'
    have heq' : a * (x.2 : ℤ) + ∑ k ∈ x.1, ((x.2 : ℤ) - (k + 1)) * v k
        = a * (x'.2 : ℤ) + ∑ k ∈ x'.1, ((x'.2 : ℤ) - (k + 1)) * v k := heq
    by_cases hh : x.2 = x'.2
    · have hmT : x.2 ∈ T := by
        rw [hT]
        exact Finset.mem_insert_of_mem hxh
      have hne0 : x.2 ≠ 0 := by
        have := (Finset.mem_Ico.mp hxh).1
        omega
      have e : ∀ F : Finset ℕ, ∑ j ∈ F, c x.2 j * v j = ∑ j ∈ F, ((x.2 : ℤ) - (j + 1)) * v j := by
        intro F
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [hc, if_neg hne0]
      have h1 : x.1 = x'.1 := by
        refine hmode x.2 hmT (Finset.mem_coe.mpr hxE) (Finset.mem_coe.mpr hxE') ?_
        show ∑ j ∈ x.1, c x.2 j * v j = ∑ j ∈ x'.1, c x.2 j * v j
        rw [e, e]
        rw [← hh] at heq'
        linarith
      exact Prod.ext h1 hh
    · exfalso
      apply haFa
      rw [hFa]
      refine Finset.mem_image.mpr ⟨(x, x'), Finset.mem_product.mpr ⟨hx1, hx1'⟩, ?_⟩
      show (∑ k ∈ x'.1, ((x'.2 : ℤ) - (k + 1)) * v k - ∑ k ∈ x.1, ((x.2 : ℤ) - (k + 1)) * v k)
        / ((x.2 : ℤ) - x'.2) = a
      have hne : ((x.2 : ℤ) - x'.2) ≠ 0 := by
        intro h0
        apply hh
        have : (x.2 : ℤ) = x'.2 := by linarith
        exact_mod_cast this
      refine Int.ediv_eq_of_eq_mul_right hne ?_
      linarith


/-- Simultaneous congruences modulo distinct primes together with divisibility by a
coprime modulus. -/
lemma crt_exists (C : Finset (Finset ℕ)) (p : Finset ℕ → ℕ) (s : Finset ℕ → ℤ) (m : ℕ)
    (hp : ∀ E ∈ C, (p E).Prime) (hinj : Set.InjOn p (C : Set (Finset ℕ)))
    (hm : ∀ E ∈ C, Nat.Coprime (p E) m) :
    ∃ b : ℕ, (∀ E ∈ C, (b : ℤ) ≡ s E [ZMOD p E]) ∧ m ∣ b := by
  classical
  have pp : Set.Pairwise (C : Set (Finset ℕ)) (Function.onFun Nat.Coprime p) := by
    intro E hE E' hE' hne
    exact (Nat.coprime_primes (hp E hE) (hp E' hE')).mpr (fun h => hne (hinj hE hE' h))
  obtain ⟨b0, hb0⟩ := Nat.chineseRemainderOfFinset (fun E => (s E % (p E : ℤ)).toNat) p C
    (fun E hE => (hp E hE).ne_zero) pp
  have hco : Nat.Coprime (∏ E ∈ C, p E) m := Nat.Coprime.prod_left hm
  obtain ⟨b, hb1, hb2⟩ := Nat.chineseRemainder hco b0 0
  refine ⟨b, fun E hE => ?_, (Nat.modEq_zero_iff_dvd).mp hb2⟩
  have h1 : b ≡ b0 [MOD p E] := hb1.of_dvd (Finset.dvd_prod_of_mem p hE)
  have h2 : b ≡ (s E % (p E : ℤ)).toNat [MOD p E] := h1.trans (hb0 E hE)
  have h3 : (b : ℤ) ≡ (((s E % (p E : ℤ)).toNat : ℕ) : ℤ) [ZMOD p E] :=
    Int.natCast_modEq_iff.mpr h2
  have hpos : (0 : ℤ) < p E := by exact_mod_cast (hp E hE).pos
  rw [Int.toNat_of_nonneg (Int.emod_nonneg _ hpos.ne')] at h3
  exact h3.trans (Int.mod_modEq _ _)

/-- Chebyshev: a positive proportion (in the logarithmic sense) of primes in `[P / 8, P]`. -/
lemma primes_dense (P : ℝ) (hP : (2 : ℝ) ^ 20 ≤ P) :
    P ≤ 4 * (((Finset.Icc 0 ⌊P⌋₊).filter (fun n : ℕ => n.Prime ∧ P ≤ 8 * n)).card : ℝ)
      * Real.log P := by
  classical
  have hP0 : (0 : ℝ) < P := lt_of_lt_of_le (by norm_num) hP
  have hP1 : (1 : ℝ) ≤ P := le_trans (by norm_num) hP
  have h1 := Chebyshev.theta_ge' hP1
  have h2 := Chebyshev.theta_le_log4_mul_x (x := P / 8) (by positivity)
  have hlogP : 0 ≤ Real.log P := Real.log_nonneg hP1
  have h3 : Chebyshev.theta P ≤ Chebyshev.theta (P / 8)
      + (((Finset.Icc 0 ⌊P⌋₊).filter (fun n : ℕ => n.Prime ∧ P ≤ 8 * n)).card : ℝ)
        * Real.log P := by
    rw [Chebyshev.theta, Chebyshev.theta]
    have hsub : (Finset.Ioc 0 ⌊P⌋₊).filter (fun p => p.Prime)
        ⊆ (Finset.Ioc 0 ⌊P / 8⌋₊).filter (fun p => p.Prime)
          ∪ (Finset.Icc 0 ⌊P⌋₊).filter (fun n : ℕ => n.Prime ∧ P ≤ 8 * n) := by
      intro p hp
      obtain ⟨hp1, hp2⟩ := Finset.mem_filter.mp hp
      obtain ⟨hp3, hp4⟩ := Finset.mem_Ioc.mp hp1
      by_cases hle : p ≤ ⌊P / 8⌋₊
      · exact Finset.mem_union_left _
          (Finset.mem_filter.mpr ⟨Finset.mem_Ioc.mpr ⟨hp3, hle⟩, hp2⟩)
      · refine Finset.mem_union_right _
          (Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨Nat.zero_le _, hp4⟩, hp2, ?_⟩)
        have : P / 8 < p := Nat.lt_of_floor_lt (not_le.mp hle)
        linarith
    have hnn : ∀ p : ℕ, 0 ≤ Real.log (p : ℝ) := fun p => Real.log_natCast_nonneg p
    have hun := Finset.sum_union_inter
      (s₁ := (Finset.Ioc 0 ⌊P / 8⌋₊).filter (fun p => p.Prime))
      (s₂ := (Finset.Icc 0 ⌊P⌋₊).filter (fun n : ℕ => n.Prime ∧ P ≤ 8 * n))
      (f := fun p : ℕ => Real.log (p : ℝ))
    have hinter : 0 ≤ ∑ p ∈ (Finset.Ioc 0 ⌊P / 8⌋₊).filter (fun p => p.Prime)
        ∩ (Finset.Icc 0 ⌊P⌋₊).filter (fun n : ℕ => n.Prime ∧ P ≤ 8 * n), Real.log (p : ℝ) :=
      Finset.sum_nonneg fun p _ => hnn p
    have hcardle : ∑ p ∈ (Finset.Icc 0 ⌊P⌋₊).filter (fun n : ℕ => n.Prime ∧ P ≤ 8 * n),
        Real.log (p : ℝ)
        ≤ (((Finset.Icc 0 ⌊P⌋₊).filter (fun n : ℕ => n.Prime ∧ P ≤ 8 * n)).card : ℝ)
          * Real.log P := by
      rw [← nsmul_eq_mul]
      refine Finset.sum_le_card_nsmul _ _ _ fun p hp => ?_
      obtain ⟨hp1, hp2, _⟩ := Finset.mem_filter.mp hp
      have hpP : (p : ℝ) ≤ P :=
        (Nat.cast_le.mpr (Finset.mem_Icc.mp hp1).2).trans (Nat.floor_le hP0.le)
      exact Real.log_le_log (by exact_mod_cast hp2.pos) hpP
    have hle := Finset.sum_le_sum_of_subset_of_nonneg hsub
      (f := fun p : ℕ => Real.log (p : ℝ)) (fun p _ _ => hnn p)
    linarith
  -- numerics
  have hlog2 := Real.log_two_gt_d9
  have hlog2' := Real.log_two_lt_d9
  have hlog4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    norm_num
  obtain ⟨u, hu⟩ : ∃ u : ℝ, u = P ^ (1 / 4 : ℝ) := ⟨_, rfl⟩
  have hu0 : 0 < u := by rw [hu]; exact Real.rpow_pos_of_pos hP0 _
  have hu4 : u ^ 4 = P := by
    rw [hu, ← Real.rpow_natCast, ← Real.rpow_mul hP0.le]
    norm_num
  have hu32 : 32 ≤ u := by
    by_contra hcon
    rw [not_le] at hcon
    have : u ^ 4 < 32 ^ 4 := pow_lt_pow_left₀ hcon hu0.le (by norm_num)
    rw [hu4] at this
    norm_num at this hP
    linarith
  have hlogle : Real.log P ≤ 4 * u := by
    have := Real.log_le_rpow_div hP0.le (by norm_num : (0 : ℝ) < 1 / 4)
    rw [← hu] at this
    linarith
  have hsqrt : Real.sqrt P = u ^ 2 := by
    rw [← hu4, show u ^ 4 = (u ^ 2) ^ 2 by ring, Real.sqrt_sq (by positivity)]
  have hlogP2 : Real.log (P + 2) ≤ Real.log 2 + Real.log P := by
    rw [← Real.log_mul (by norm_num) hP0.ne']
    exact Real.log_le_log (by linarith) (by linarith)
  rw [hsqrt] at h1
  have hu2 : 1024 ≤ u ^ 2 := by nlinarith
  have hu3 : 1024 * u ≤ u ^ 3 := by nlinarith
  have hu4' : 32 * u ^ 3 ≤ u ^ 4 := by nlinarith [pow_pos hu0 3]
  have hmain : 2 * u ^ 2 * Real.log P ≤ 8 * u ^ 3 := by
    have : 2 * u ^ 2 * Real.log P ≤ 2 * u ^ 2 * (4 * u) :=
      mul_le_mul_of_nonneg_left hlogle (by positivity)
    nlinarith
  have hPl : 0.6931471803 * P ≤ P * Real.log 2 := by nlinarith
  have hPl' : P * Real.log 2 ≤ 0.6931471808 * P := by nlinarith
  rw [hlog4] at h2
  have h2' : Chebyshev.theta (P / 8) ≤ P * Real.log 2 / 4 := by linarith
  have h1' : P * Real.log 2 - Real.log 2 - Real.log (P + 2) - 2 * u ^ 2 * Real.log P
      ≤ Chebyshev.theta P := by linarith
  linarith


/-- From a generic cube of primes `a + ∑ k ∈ E, v k` to the family `p`, the shifts `s` and all
the structural properties of the near shifts `p E * h - s E`. -/
lemma cube_data (K H M : ℕ) (a : ℤ) (v : ℕ → ℤ)
    (hv : ∀ k < K, |v k| ≤ M)
    (hvert : ∀ E ∈ (Finset.range K).powerset, ∃ q : ℕ, q ≤ M ∧ a + ∑ k ∈ E, v k = q)
    (hinj1 : Set.InjOn (fun E : Finset ℕ => ∑ k ∈ E, v k)
      ((Finset.range K).powerset : Set (Finset ℕ)))
    (hinj2 : Set.InjOn
      (fun x : Finset ℕ × ℕ => a * (x.2 : ℤ) + ∑ k ∈ x.1, ((x.2 : ℤ) - (k + 1)) * v k)
      (((Finset.range K).powerset ×ˢ Finset.Ico (K + 1) (K + H + 1) :
        Finset (Finset ℕ × ℕ)) : Set (Finset ℕ × ℕ))) :
    ∃ (p : Finset ℕ → ℕ) (s : Finset ℕ → ℤ),
      (∀ E ∈ (Finset.range K).powerset, (p E : ℤ) = a + ∑ k ∈ E, v k) ∧
      (∀ E ∈ (Finset.range K).powerset, |s E| ≤ K ^ 2 * M) ∧
      (∀ E ∈ (Finset.range K).powerset, ∀ k < K,
        (p (symmDiff E {k}) : ℤ) * ((k + 1 : ℕ) : ℤ) - s (symmDiff E {k})
          = (p E : ℤ) * ((k + 1 : ℕ) : ℤ) - s E) ∧
      Set.InjOn p ((Finset.range K).powerset : Set (Finset ℕ)) ∧
      Set.InjOn (fun x : Finset ℕ × ℕ => (p x.1 : ℤ) * (x.2 : ℤ) - s x.1)
        (((Finset.range K).powerset ×ˢ Finset.Ico (K + 1) (K + H + 1) :
          Finset (Finset ℕ × ℕ)) : Set (Finset ℕ × ℕ)) := by
  classical
  refine ⟨fun E => (a + ∑ k ∈ E, v k).toNat, fun E => ∑ k ∈ E, ((k : ℤ) + 1) * v k, ?_⟩
  have hp : ∀ E ∈ (Finset.range K).powerset,
      (((a + ∑ k ∈ E, v k).toNat : ℕ) : ℤ) = a + ∑ k ∈ E, v k := by
    intro E hE
    obtain ⟨q, _, hq⟩ := hvert E hE
    rw [hq]
    simp
  have hr : ∀ E ∈ (Finset.range K).powerset, ∀ h : ℕ,
      (((a + ∑ k ∈ E, v k).toNat : ℕ) : ℤ) * (h : ℤ) - ∑ k ∈ E, ((k : ℤ) + 1) * v k
        = a * (h : ℤ) + ∑ k ∈ E, ((h : ℤ) - (k + 1)) * v k := by
    intro E hE h
    rw [hp E hE, add_mul, Finset.sum_mul, add_sub_assoc, ← Finset.sum_sub_distrib]
    congr 1
    refine Finset.sum_congr rfl fun k _ => ?_
    ring
  have hsymm : ∀ E ∈ (Finset.range K).powerset, ∀ k < K,
      symmDiff E {k} ∈ (Finset.range K).powerset := by
    intro E hE k hk
    rw [Finset.mem_powerset] at hE ⊢
    intro i hi
    rcases Finset.mem_symmDiff.mp hi with ⟨hi, _⟩ | ⟨hi, _⟩
    · exact hE hi
    · rw [Finset.mem_singleton] at hi
      rw [hi]
      exact Finset.mem_range.mpr hk
  refine ⟨hp, ?_, ?_, ?_, ?_⟩
  · intro E hE
    have hEsub := Finset.mem_powerset.mp hE
    calc |∑ k ∈ E, ((k : ℤ) + 1) * v k| ≤ ∑ k ∈ E, |((k : ℤ) + 1) * v k| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _k ∈ E, (K : ℤ) * M := by
          refine Finset.sum_le_sum fun k hk => ?_
          have hkK := Finset.mem_range.mp (hEsub hk)
          rw [abs_mul]
          have h1 : |(k : ℤ) + 1| ≤ K := by
            rw [abs_of_nonneg (by positivity)]
            exact_mod_cast hkK
          exact mul_le_mul h1 (hv k hkK) (abs_nonneg _) (by positivity)
      _ = E.card * ((K : ℤ) * M) := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ K * ((K : ℤ) * M) := by
          have hc : (E.card : ℤ) ≤ K := by
            have := Finset.card_le_card hEsub
            rw [Finset.card_range] at this
            exact_mod_cast this
          exact mul_le_mul_of_nonneg_right hc (by positivity)
      _ = K ^ 2 * M := by ring
  · intro E hE k hk
    rw [hr E hE, hr _ (hsymm E hE k hk)]
    congr 1
    have hg : (((k + 1 : ℕ) : ℤ) - ((k : ℤ) + 1)) * v k = 0 := by
      push_cast
      ring
    have e1 := Finset.sum_erase (symmDiff E {k})
      (f := fun j : ℕ => (((k + 1 : ℕ) : ℤ) - ((j : ℤ) + 1)) * v j) (a := k) hg
    have e2 := Finset.sum_erase E
      (f := fun j : ℕ => (((k + 1 : ℕ) : ℤ) - ((j : ℤ) + 1)) * v j) (a := k) hg
    have e3 : (symmDiff E {k}).erase k = E.erase k := by
      ext j
      simp only [Finset.mem_erase, Finset.mem_symmDiff, Finset.mem_singleton]
      constructor
      · rintro ⟨hne, h | h⟩
        · exact ⟨hne, h.1⟩
        · exact absurd h.1 hne
      · rintro ⟨hne, h⟩
        exact ⟨hne, Or.inl ⟨h, hne⟩⟩
    rw [← e1, ← e2, e3]
  · intro E hE E' hE' heq
    have h1 : (((a + ∑ k ∈ E, v k).toNat : ℕ) : ℤ) = (((a + ∑ k ∈ E', v k).toNat : ℕ) : ℤ) := by
      exact_mod_cast heq
    rw [hp E (Finset.mem_coe.mp hE), hp E' (Finset.mem_coe.mp hE')] at h1
    exact hinj1 hE hE' (by simpa using h1)
  · intro x hx x' hx' heq
    have hxE := (Finset.mem_product.mp (Finset.mem_coe.mp hx)).1
    have hxE' := (Finset.mem_product.mp (Finset.mem_coe.mp hx')).1
    refine hinj2 hx hx' ?_
    have h1 := hr x.1 hxE x.2
    have h2 := hr x'.1 hxE' x'.2
    show a * (x.2 : ℤ) + ∑ k ∈ x.1, ((x.2 : ℤ) - (k + 1)) * v k
      = a * (x'.2 : ℤ) + ∑ k ∈ x'.1, ((x'.2 : ℤ) - (k + 1)) * v k
    rw [← h1, ← h2]
    exact heq


lemma exp_half_big (l : ℝ) (hl : 6 * 10 ^ 12 ≤ l) : 3 * l ^ 11 ≤ Real.exp (l / 2) := by
  have hl0 : 0 < l := lt_of_lt_of_le (by norm_num) hl
  have h := Real.pow_div_factorial_le_exp (x := l / 2) (by positivity) 12
  have hf : ((Nat.factorial 12 : ℕ) : ℝ) = 479001600 := by norm_num [Nat.factorial]
  rw [hf] at h
  have h2 : 3 * l ^ 11 ≤ (l / 2) ^ 12 / 479001600 := by
    rw [le_div_iff₀ (by norm_num)]
    have e : (l / 2) ^ 12 = l ^ 11 * l / 4096 := by ring
    rw [e]
    have h11 : 0 < l ^ 11 := by positivity
    have hl' : 3 * 479001600 * 4096 ≤ l := by linarith
    have := mul_le_mul_of_nonneg_left hl' h11.le
    linarith
  linarith

/-- All the size comparisons at scale `l = log log log x`. -/
lemma numeric (l : ℝ) (hl : 6 * 10 ^ 12 ≤ l) (K H M : ℕ)
    (hK : K = ⌊2 * Real.log l / Real.log 2⌋₊) (hH : H = ⌊l ^ 2⌋₊)
    (hM : M = ⌊Real.exp (l ^ 3)⌋₊) :
    0 < K ∧ (2 : ℝ) ^ K ≤ l ^ 2 ∧ l ^ 2 < 2 ^ (K + 1) ∧
    (M : ℝ) ≤ Real.exp (l ^ 3) ∧
    (((K + H + K ^ 2) * M : ℕ) : ℝ) ≤ Real.exp (Real.exp (l / 2)) ∧
    ((M ^ (2 ^ K) * (2 * ((K + H + K ^ 2) * M)) ^ ((2 ^ K * H) * (2 ^ K * H)) : ℕ) : ℝ)
      ≤ Real.exp (Real.exp (l / 2)) ∧
    ∀ N : ℕ, Real.exp (l ^ 3) ≤ 4 * N * l ^ 3 →
      ∀ k ≤ K, 2 * (4 ^ K * (H + 1) ^ 2) * (2 * (2 * M + 1)) ^ (2 ^ k - 1) ≤ N ^ (2 ^ k) := by
  have hl0 : 0 < l := lt_of_lt_of_le (by norm_num) hl
  have hl1 : 1 ≤ l := le_trans (by norm_num) hl
  have hE3 := exp_half_big l hl
  have hlogl : 0 < Real.log l := Real.log_pos (lt_of_lt_of_le (by norm_num) hl)
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hKle : (K : ℝ) ≤ 2 * Real.log l / Real.log 2 := by
    rw [hK]
    exact Nat.floor_le (by positivity)
  have hKlt : 2 * Real.log l / Real.log 2 < K + 1 := by
    rw [hK]
    exact Nat.lt_floor_add_one _
  have hF1 : (2 : ℝ) ^ K ≤ l ^ 2 := by
    rw [← Real.log_le_log_iff (by positivity) (by positivity), Real.log_pow, Real.log_pow]
    have := (le_div_iff₀ hlog2).mp hKle
    push_cast
    linarith
  have hF2 : l ^ 2 < (2 : ℝ) ^ (K + 1) := by
    rw [← Real.log_lt_log_iff (by positivity) (by positivity), Real.log_pow, Real.log_pow]
    have := (div_lt_iff₀ hlog2).mp hKlt
    push_cast
    linarith
  have hK0 : 0 < K := by
    rcases Nat.eq_zero_or_pos K with h | h
    · rw [h] at hF2
      norm_num at hF2
      nlinarith
    · exact h
  have hMP : (M : ℝ) ≤ Real.exp (l ^ 3) := by
    rw [hM]
    exact Nat.floor_le (Real.exp_pos _).le
  have hMlow : Real.exp (l ^ 3) < M + 1 := by
    rw [hM]
    exact Nat.lt_floor_add_one _
  have hHle : (H : ℝ) ≤ l ^ 2 := by
    rw [hH]
    exact Nat.floor_le (by positivity)
  have hKl2 : (K : ℝ) ≤ l ^ 2 := by
    have h1 : (K : ℝ) < (2 : ℝ) ^ K := by exact_mod_cast Nat.lt_two_pow_self
    linarith
  have hl2 : 1 ≤ l ^ 2 := one_le_pow₀ hl1
  have hl4 : l ^ 2 ≤ l ^ 4 := pow_le_pow_right₀ hl1 (by norm_num)
  have hK2 : (K : ℝ) ^ 2 ≤ l ^ 4 := by
    have := pow_le_pow_left₀ (Nat.cast_nonneg K) hKl2 2
    calc (K : ℝ) ^ 2 ≤ (l ^ 2) ^ 2 := this
      _ = l ^ 4 := by ring
  have hP0 : 0 < Real.exp (l ^ 3) := Real.exp_pos _
  have hl3 : l ≤ l ^ 3 := by
    calc l = l ^ 1 := (pow_one l).symm
      _ ≤ l ^ 3 := pow_le_pow_right₀ hl1 (by norm_num)
  have hexp1 : Real.exp (l / 2) ≤ Real.exp (l ^ 3) := Real.exp_le_exp.mpr (by linarith)
  have hpow11 : ∀ j : ℕ, j ≤ 11 → l ^ j ≤ l ^ 11 := fun j hj => pow_le_pow_right₀ hl1 hj
  have hl11 : 0 < l ^ 11 := by positivity
  have hpow10 : ∀ j : ℕ, j ≤ 10 → 8 * l ^ j ≤ l ^ 11 := by
    intro j hj
    have h1 : l ^ (j + 1) ≤ l ^ 11 := pow_le_pow_right₀ hl1 (by omega)
    have h2 : 0 < l ^ j := by positivity
    have h3 : (8 : ℝ) ≤ l := le_trans (by norm_num) hl
    have h4 : 8 * l ^ j ≤ l ^ j * l := by nlinarith
    rw [pow_succ] at h1
    linarith
  -- the largest shift
  have hRM : (((K + H + K ^ 2) * M : ℕ) : ℝ) ≤ 3 * l ^ 4 * Real.exp (l ^ 3) := by
    push_cast
    have h1 : (K : ℝ) + H + (K : ℝ) ^ 2 ≤ 3 * l ^ 4 := by linarith
    exact mul_le_mul h1 hMP (Nat.cast_nonneg _) (by positivity)
  have h6 : 6 * l ^ 4 ≤ Real.exp (l / 2) := by
    have := hpow10 4 (by norm_num)
    have h0 : 0 < l ^ 4 := by positivity
    linarith
  have h2RM : (2 : ℝ) * (((K + H + K ^ 2) * M : ℕ) : ℝ) ≤ Real.exp (2 * l ^ 3) := by
    have e : Real.exp (2 * l ^ 3) = Real.exp (l ^ 3) * Real.exp (l ^ 3) := by
      rw [← Real.exp_add]
      ring_nf
    rw [e]
    calc (2 : ℝ) * (((K + H + K ^ 2) * M : ℕ) : ℝ) ≤ 6 * l ^ 4 * Real.exp (l ^ 3) := by linarith
      _ ≤ Real.exp (l ^ 3) * Real.exp (l ^ 3) :=
        mul_le_mul_of_nonneg_right (h6.trans hexp1) hP0.le
  have h2l3 : 2 * l ^ 3 ≤ Real.exp (l / 2) := by
    have := hpow10 3 (by norm_num)
    have h0 : 0 < l ^ 3 := by positivity
    linarith
  have h3l11 : Real.exp (3 * l ^ 11) ≤ Real.exp (Real.exp (l / 2)) := Real.exp_le_exp.mpr hE3
  refine ⟨hK0, hF1, hF2, hMP, ?_, ?_, ?_⟩
  · have h1 : (((K + H + K ^ 2) * M : ℕ) : ℝ) ≤ Real.exp (2 * l ^ 3) := by
      have h0 : (0 : ℝ) ≤ (((K + H + K ^ 2) * M : ℕ) : ℝ) := Nat.cast_nonneg _
      linarith
    exact h1.trans (Real.exp_le_exp.mpr h2l3)
  · have hn : (((2 ^ K * H) * (2 ^ K * H) : ℕ) : ℝ) ≤ l ^ 8 := by
      push_cast
      have h1 : (2 : ℝ) ^ K * H ≤ l ^ 2 * l ^ 2 :=
        mul_le_mul hF1 hHle (Nat.cast_nonneg _) (by positivity)
      have h0 : (0 : ℝ) ≤ (2 : ℝ) ^ K * H := by positivity
      calc (2 : ℝ) ^ K * H * ((2 : ℝ) ^ K * H) ≤ (l ^ 2 * l ^ 2) * (l ^ 2 * l ^ 2) :=
            mul_le_mul h1 h1 h0 (by positivity)
        _ = l ^ 8 := by ring
    have hA : ((M ^ (2 ^ K) : ℕ) : ℝ) ≤ Real.exp (l ^ 5) := by
      push_cast
      calc (M : ℝ) ^ (2 ^ K) ≤ (Real.exp (l ^ 3)) ^ (2 ^ K) :=
            pow_le_pow_left₀ (Nat.cast_nonneg _) hMP _
        _ = Real.exp (((2 ^ K : ℕ) : ℝ) * l ^ 3) := (Real.exp_nat_mul _ _).symm
        _ ≤ Real.exp (l ^ 5) := by
            refine Real.exp_le_exp.mpr ?_
            push_cast
            calc (2 : ℝ) ^ K * l ^ 3 ≤ l ^ 2 * l ^ 3 :=
                  mul_le_mul_of_nonneg_right hF1 (by positivity)
              _ = l ^ 5 := by ring
    have hB : (((2 * ((K + H + K ^ 2) * M)) ^ ((2 ^ K * H) * (2 ^ K * H)) : ℕ) : ℝ)
        ≤ Real.exp (2 * l ^ 11) := by
      rw [Nat.cast_pow, Nat.cast_mul, Nat.cast_ofNat]
      calc ((2 : ℝ) * (((K + H + K ^ 2) * M : ℕ) : ℝ)) ^ ((2 ^ K * H) * (2 ^ K * H))
          ≤ (Real.exp (2 * l ^ 3)) ^ ((2 ^ K * H) * (2 ^ K * H)) :=
            pow_le_pow_left₀ (by positivity) h2RM _
        _ = Real.exp ((((2 ^ K * H) * (2 ^ K * H) : ℕ) : ℝ) * (2 * l ^ 3)) :=
            (Real.exp_nat_mul _ _).symm
        _ ≤ Real.exp (2 * l ^ 11) := by
            refine Real.exp_le_exp.mpr ?_
            calc (((2 ^ K * H) * (2 ^ K * H) : ℕ) : ℝ) * (2 * l ^ 3) ≤ l ^ 8 * (2 * l ^ 3) :=
                  mul_le_mul_of_nonneg_right hn (by positivity)
              _ = 2 * l ^ 11 := by ring
    rw [Nat.cast_mul]
    calc ((M ^ (2 ^ K) : ℕ) : ℝ)
          * (((2 * ((K + H + K ^ 2) * M)) ^ ((2 ^ K * H) * (2 ^ K * H)) : ℕ) : ℝ)
        ≤ Real.exp (l ^ 5) * Real.exp (2 * l ^ 11) :=
          mul_le_mul hA hB (Nat.cast_nonneg _) (Real.exp_pos _).le
      _ = Real.exp (l ^ 5 + 2 * l ^ 11) := (Real.exp_add _ _).symm
      _ ≤ Real.exp (3 * l ^ 11) := by
          refine Real.exp_le_exp.mpr ?_
          have := hpow11 5 (by norm_num)
          linarith
      _ ≤ Real.exp (Real.exp (l / 2)) := h3l11
  · intro N hN k hk
    have hP2 : 2 ≤ Real.exp (l ^ 3) := by
      have := Real.add_one_le_exp (l ^ 3)
      linarith
    have hc1 : Real.exp (l ^ 3) ≤ 2 * (2 * (M : ℝ) + 1) := by linarith
    have hc2 : 2 * (2 * (M : ℝ) + 1) ≤ 5 * Real.exp (l ^ 3) := by linarith
    have hc0 : (0 : ℝ) < 2 * (2 * (M : ℝ) + 1) := by positivity
    have hg1 : (1 : ℝ) ≤ 20 * l ^ 3 := by nlinarith [pow_pos hl0 3, one_le_pow₀ (n := 3) hl1]
    have hg0 : (0 : ℝ) < 20 * l ^ 3 := by positivity
    have hNg : 2 * (2 * (M : ℝ) + 1) / (20 * l ^ 3) ≤ N := by
      rw [div_le_iff₀ hg0]
      nlinarith
    have hpow : (2 * (2 * (M : ℝ) + 1) / (20 * l ^ 3)) ^ (2 ^ k) ≤ (N : ℝ) ^ (2 ^ k) :=
      pow_le_pow_left₀ (by positivity) hNg _
    have h4K : (4 : ℝ) ^ K ≤ l ^ 4 := by
      have e : (4 : ℝ) ^ K = ((2 : ℝ) ^ K) ^ 2 := by
        rw [show (4 : ℝ) = 2 ^ 2 by norm_num, ← pow_mul, ← pow_mul, mul_comm]
      rw [e]
      calc ((2 : ℝ) ^ K) ^ 2 ≤ (l ^ 2) ^ 2 := pow_le_pow_left₀ (by positivity) hF1 2
        _ = l ^ 4 := by ring
    have hH1 : ((H : ℝ) + 1) ^ 2 ≤ 4 * l ^ 4 := by
      have h1 : (H : ℝ) + 1 ≤ 2 * l ^ 2 := by linarith
      calc ((H : ℝ) + 1) ^ 2 ≤ (2 * l ^ 2) ^ 2 := pow_le_pow_left₀ (by positivity) h1 2
        _ = 4 * l ^ 4 := by ring
    have hf : 2 * ((4 : ℝ) ^ K * ((H : ℝ) + 1) ^ 2) ≤ 8 * l ^ 8 := by
      have := mul_le_mul h4K hH1 (by positivity) (by positivity)
      calc 2 * ((4 : ℝ) ^ K * ((H : ℝ) + 1) ^ 2) ≤ 2 * (l ^ 4 * (4 * l ^ 4)) := by linarith
        _ = 8 * l ^ 8 := by ring
    have hglog : Real.log (20 * l ^ 3) ≤ l / 2 := by
      rw [Real.log_le_iff_le_exp hg0]
      have := hpow10 3 (by norm_num)
      have h0 : 0 < l ^ 3 := by positivity
      linarith
    have hglog0 : 0 ≤ Real.log (20 * l ^ 3) := Real.log_nonneg hg1
    have hgk : (20 * l ^ 3) ^ (2 ^ k) ≤ Real.exp (l ^ 3 / 2) := by
      calc (20 * l ^ 3) ^ (2 ^ k) ≤ (20 * l ^ 3) ^ (2 ^ K) :=
            pow_le_pow_right₀ hg1 (Nat.pow_le_pow_right (by norm_num) hk)
        _ = (Real.exp (Real.log (20 * l ^ 3))) ^ (2 ^ K) := by rw [Real.exp_log hg0]
        _ = Real.exp (((2 ^ K : ℕ) : ℝ) * Real.log (20 * l ^ 3)) := (Real.exp_nat_mul _ _).symm
        _ ≤ Real.exp (l ^ 3 / 2) := by
            refine Real.exp_le_exp.mpr ?_
            push_cast
            calc (2 : ℝ) ^ K * Real.log (20 * l ^ 3) ≤ l ^ 2 * (l / 2) :=
                  mul_le_mul hF1 hglog hglog0 (by positivity)
              _ = l ^ 3 / 2 := by ring
    have h8 : 8 * l ^ 8 ≤ Real.exp (l ^ 3 / 2) := by
      have h1 := hpow10 8 (by norm_num)
      have h2 : Real.exp (l / 2) ≤ Real.exp (l ^ 3 / 2) := Real.exp_le_exp.mpr (by linarith)
      linarith
    have key : 2 * ((4 : ℝ) ^ K * ((H : ℝ) + 1) ^ 2) * (20 * l ^ 3) ^ (2 ^ k)
        ≤ 2 * (2 * (M : ℝ) + 1) := by
      have e : Real.exp (l ^ 3) = Real.exp (l ^ 3 / 2) * Real.exp (l ^ 3 / 2) := by
        rw [← Real.exp_add]
        ring_nf
      calc 2 * ((4 : ℝ) ^ K * ((H : ℝ) + 1) ^ 2) * (20 * l ^ 3) ^ (2 ^ k)
          ≤ Real.exp (l ^ 3 / 2) * Real.exp (l ^ 3 / 2) :=
            mul_le_mul (hf.trans h8) hgk (by positivity) (Real.exp_pos _).le
        _ = Real.exp (l ^ 3) := e.symm
        _ ≤ 2 * (2 * (M : ℝ) + 1) := hc1
    have hk1 : 1 ≤ 2 ^ k := Nat.one_le_two_pow
    have hreal : 2 * ((4 : ℝ) ^ K * ((H : ℝ) + 1) ^ 2) * (2 * (2 * (M : ℝ) + 1)) ^ (2 ^ k - 1)
        ≤ (N : ℝ) ^ (2 ^ k) := by
      refine le_trans ?_ hpow
      rw [div_pow, le_div_iff₀ (by positivity)]
      have e : (2 * (2 * (M : ℝ) + 1)) ^ (2 ^ k)
          = (2 * (2 * (M : ℝ) + 1)) ^ (2 ^ k - 1) * (2 * (2 * (M : ℝ) + 1)) := by
        rw [← pow_succ, Nat.sub_add_cancel hk1]
      rw [e]
      have hcp : (0 : ℝ) ≤ (2 * (2 * (M : ℝ) + 1)) ^ (2 ^ k - 1) := by positivity
      calc 2 * ((4 : ℝ) ^ K * ((H : ℝ) + 1) ^ 2) * (2 * (2 * (M : ℝ) + 1)) ^ (2 ^ k - 1)
            * (20 * l ^ 3) ^ (2 ^ k)
          = (2 * (2 * (M : ℝ) + 1)) ^ (2 ^ k - 1)
            * (2 * ((4 : ℝ) ^ K * ((H : ℝ) + 1) ^ 2) * (20 * l ^ 3) ^ (2 ^ k)) := by ring
        _ ≤ (2 * (2 * (M : ℝ) + 1)) ^ (2 ^ k - 1) * (2 * (2 * (M : ℝ) + 1)) :=
          mul_le_mul_of_nonneg_left key hcp
    exact_mod_cast hreal


end E69S1

open E69S1

theorem OMA.solution : OMA.R_Erdos69_erdos_69_R1_H1_R1.H1 := by
  classical
  intro η hη
  obtain ⟨L0, hL0⟩ : ∃ L0 : ℝ, L0 = max (6 * 10 ^ 12) (2 / η) := ⟨_, rfl⟩
  refine ⟨⌈Real.exp (Real.exp (Real.exp L0))⌉₊, fun x hx => ?_⟩
  have hxr : Real.exp (Real.exp (Real.exp L0)) ≤ x :=
    (Nat.le_ceil _).trans (by exact_mod_cast hx)
  have hx0 : (0 : ℝ) < x := lt_of_lt_of_le (Real.exp_pos _) hxr
  have h1 : Real.exp (Real.exp L0) ≤ Real.log x := (Real.le_log_iff_exp_le hx0).mpr hxr
  have h1pos : 0 < Real.log x := lt_of_lt_of_le (Real.exp_pos _) h1
  have h2 : Real.exp L0 ≤ Real.log (Real.log x) := (Real.le_log_iff_exp_le h1pos).mpr h1
  have h2pos : 0 < Real.log (Real.log x) := lt_of_lt_of_le (Real.exp_pos _) h2
  have h3 : L0 ≤ Real.log (Real.log (Real.log x)) := (Real.le_log_iff_exp_le h2pos).mpr h2
  obtain ⟨l, hl⟩ : ∃ l : ℝ, l = Real.log (Real.log (Real.log x)) := ⟨_, rfl⟩
  have hlL : L0 ≤ l := by rw [hl]; exact h3
  have hl6 : 6 * 10 ^ 12 ≤ l := by rw [hL0] at hlL; exact (le_max_left _ _).trans hlL
  have hlη : 2 / η ≤ l := by rw [hL0] at hlL; exact (le_max_right _ _).trans hlL
  have hl0 : 0 < l := lt_of_lt_of_le (by norm_num) hl6
  have hl1 : 1 ≤ l := le_trans (by norm_num) hl6
  have hexpl : Real.exp l = Real.log (Real.log x) := by rw [hl, Real.exp_log h2pos]
  have hB : Real.exp (l / 2) = Real.sqrt (Real.log (Real.log x)) := by
    rw [← hexpl]
    have e : Real.exp l = (Real.exp (l / 2)) ^ 2 := by
      rw [← Real.exp_nat_mul]
      congr 1
      push_cast
      ring
    rw [e, Real.sqrt_sq (Real.exp_pos _).le]
  obtain ⟨K, hK⟩ : ∃ K : ℕ, K = ⌊2 * Real.log l / Real.log 2⌋₊ := ⟨_, rfl⟩
  obtain ⟨H, hH⟩ : ∃ H : ℕ, H = ⌊l ^ 2⌋₊ := ⟨_, rfl⟩
  obtain ⟨M, hM⟩ : ∃ M : ℕ, M = ⌊Real.exp (l ^ 3)⌋₊ := ⟨_, rfl⟩
  obtain ⟨hK0, hF1, hF2, hMP, hRM, hQb, hsz⟩ := numeric l hl6 K H M hK hH hM
  have hl3 : l ≤ l ^ 3 := by
    calc l = l ^ 1 := (pow_one l).symm
      _ ≤ l ^ 3 := pow_le_pow_right₀ hl1 (by norm_num)
  have hP20 : (2 : ℝ) ^ 20 ≤ Real.exp (l ^ 3) := by
    have h := Real.add_one_le_exp (l ^ 3)
    norm_num
    linarith
  have hdense := primes_dense (Real.exp (l ^ 3)) hP20
  rw [Real.log_exp] at hdense
  obtain ⟨Pr, hPr⟩ : ∃ Pr : Finset ℕ, Pr = (Finset.Icc 0 ⌊Real.exp (l ^ 3)⌋₊).filter
      (fun n : ℕ => n.Prime ∧ Real.exp (l ^ 3) ≤ 8 * n) := ⟨_, rfl⟩
  rw [← hPr] at hdense
  have hA : ∀ a ∈ Pr.image (Nat.cast : ℕ → ℤ), 0 ≤ a ∧ a ≤ M := by
    intro a ha
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp ha
    rw [hPr] at hq
    have := (Finset.mem_Icc.mp (Finset.mem_filter.mp hq).1).2
    rw [← hM] at this
    exact ⟨by positivity, by exact_mod_cast this⟩
  have hcardA : (Pr.image (Nat.cast : ℕ → ℤ)).card = Pr.card :=
    Finset.card_image_of_injective _ Nat.cast_injective
  have hsize := hsz Pr.card hdense
  rw [← hcardA] at hsize
  obtain ⟨a, v, hv, hvert, hinj1, hinj2⟩ :=
    cube_exists K H M (Pr.image (Nat.cast : ℕ → ℤ)) hA hsize
  have hvert' : ∀ E ∈ (Finset.range K).powerset, ∃ q : ℕ, q ≤ M ∧ a + ∑ k ∈ E, v k = q ∧
      q.Prime ∧ Real.exp (l ^ 3) ≤ 8 * q := by
    intro E hE
    obtain ⟨q, hq, hqe⟩ := Finset.mem_image.mp (hvert E hE)
    rw [hPr] at hq
    obtain ⟨hq1, hq2, hq3⟩ := Finset.mem_filter.mp hq
    have hqM := (Finset.mem_Icc.mp hq1).2
    rw [← hM] at hqM
    exact ⟨q, hqM, hqe.symm, hq2, hq3⟩
  obtain ⟨p, s, hp, hs, hsym, hpinj, hrinj⟩ := cube_data K H M a v hv
    (fun E hE => by
      obtain ⟨q, e1, e2, _⟩ := hvert' E hE
      exact ⟨q, e1, e2⟩) hinj1 hinj2
  have hpE : ∀ E ∈ (Finset.range K).powerset,
      (p E).Prime ∧ Real.exp (l ^ 3) ≤ 8 * (p E : ℝ) ∧ p E ≤ M := by
    intro E hE
    obtain ⟨q, hqM, hqe, hqp, hq8⟩ := hvert' E hE
    have hpq : p E = q := by
      have := hp E hE
      rw [hqe] at this
      exact_mod_cast this
    rw [hpq]
    exact ⟨hqp, hq8, hqM⟩
  have hM8 : ∀ E ∈ (Finset.range K).powerset, (M : ℤ) ≤ 8 * (p E : ℤ) := by
    intro E hE
    have : (M : ℝ) ≤ 8 * (p E : ℝ) := hMP.trans (hpE E hE).2.1
    exact_mod_cast this
  have hrabs : ∀ y ∈ (Finset.range K).powerset ×ˢ Finset.Ico (K + 1) (K + H + 1),
      |(p y.1 : ℤ) * (y.2 : ℤ) - s y.1| ≤ (((K + H + K ^ 2) * M : ℕ) : ℤ) := by
    intro y hy
    obtain ⟨hyE, hyh⟩ := Finset.mem_product.mp hy
    have hh : (y.2 : ℤ) ≤ K + H := by
      have := (Finset.mem_Ico.mp hyh).2
      exact_mod_cast (by omega : y.2 ≤ K + H)
    have hpM : (p y.1 : ℤ) ≤ M := by exact_mod_cast (hpE y.1 hyE).2.2
    have e1 : |(p y.1 : ℤ) * (y.2 : ℤ)| ≤ (M : ℤ) * (K + H) := by
      rw [abs_of_nonneg (by positivity)]
      exact mul_le_mul hpM hh (by positivity) (by positivity)
    have e2 := hs y.1 hyE
    calc |(p y.1 : ℤ) * (y.2 : ℤ) - s y.1| ≤ |(p y.1 : ℤ) * (y.2 : ℤ)| + |s y.1| := abs_sub _ _
      _ ≤ (M : ℤ) * (K + H) + K ^ 2 * M := add_le_add e1 e2
      _ = (((K + H + K ^ 2) * M : ℕ) : ℤ) := by
          push_cast
          ring
  obtain ⟨W, hWdef⟩ : ∃ W : ℕ,
      W = ∏ y ∈ ((Finset.range K).powerset ×ˢ Finset.Ico (K + 1) (K + H + 1)).offDiag,
        ((p y.1.1 : ℤ) * (y.1.2 : ℤ) - s y.1.1
          - ((p y.2.1 : ℤ) * (y.2.2 : ℤ) - s y.2.1)).natAbs := ⟨_, rfl⟩
  have hW0 : W ≠ 0 := by
    rw [hWdef, Finset.prod_ne_zero_iff]
    intro y hy
    obtain ⟨hy1, hy2, hne⟩ := Finset.mem_offDiag.mp hy
    rw [Int.natAbs_ne_zero, sub_ne_zero]
    intro heq
    exact hne (hrinj (Finset.mem_coe.mpr hy1) (Finset.mem_coe.mpr hy2) heq)
  have hM1 : 1 ≤ M := by
    have e1 := (hpE ∅ (Finset.empty_mem_powerset _)).1.pos
    have e2 := (hpE ∅ (Finset.empty_mem_powerset _)).2.2
    omega
  have hRMpos : 1 ≤ 2 * ((K + H + K ^ 2) * M) := by
    have : 1 ≤ (K + H + K ^ 2) * M := Nat.one_le_iff_ne_zero.mpr
      (Nat.mul_ne_zero (by omega) (by omega))
    omega
  have hWle : W ≤ (2 * ((K + H + K ^ 2) * M)) ^ ((2 ^ K * H) * (2 ^ K * H)) := by
    rw [hWdef]
    refine (Finset.prod_le_pow_card _ _ (2 * ((K + H + K ^ 2) * M)) ?_).trans ?_
    · intro y hy
      obtain ⟨hy1, hy2, _⟩ := Finset.mem_offDiag.mp hy
      have a1 := hrabs y.1 hy1
      have a2 := hrabs y.2 hy2
      have b1 : ((p y.1.1 : ℤ) * (y.1.2 : ℤ) - s y.1.1).natAbs ≤ (K + H + K ^ 2) * M := by
        have : ((((p y.1.1 : ℤ) * (y.1.2 : ℤ) - s y.1.1).natAbs : ℕ) : ℤ)
            ≤ (((K + H + K ^ 2) * M : ℕ) : ℤ) := by
          rw [Int.natCast_natAbs]
          exact a1
        exact_mod_cast this
      have b2 : ((p y.2.1 : ℤ) * (y.2.2 : ℤ) - s y.2.1).natAbs ≤ (K + H + K ^ 2) * M := by
        have : ((((p y.2.1 : ℤ) * (y.2.2 : ℤ) - s y.2.1).natAbs : ℕ) : ℤ)
            ≤ (((K + H + K ^ 2) * M : ℕ) : ℤ) := by
          rw [Int.natCast_natAbs]
          exact a2
        exact_mod_cast this
      have := Int.natAbs_sub_le ((p y.1.1 : ℤ) * (y.1.2 : ℤ) - s y.1.1)
        ((p y.2.1 : ℤ) * (y.2.2 : ℤ) - s y.2.1)
      omega
    · refine Nat.pow_le_pow_right hRMpos ?_
      rw [Finset.offDiag_card, Finset.card_product, Finset.card_powerset, Finset.card_range,
        Nat.card_Ico]
      have : K + H + 1 - (K + 1) = H := by omega
      rw [this]
      exact Nat.sub_le _ _
  obtain ⟨Wf, hWf⟩ : ∃ Wf : ℕ,
      Wf = ∏ ℓ ∈ W.primeFactors \ ((Finset.range K).powerset).image p,
        ℓ ^ W.factorization ℓ := ⟨_, rfl⟩
  have hWfdvd : Wf ∣ W := by
    have hWeq : W = ∏ ℓ ∈ W.primeFactors, ℓ ^ W.factorization ℓ :=
      (Nat.prod_factorization_pow_eq_self hW0).symm.trans
        (Nat.prod_factorization_eq_prod_primeFactors _)
    have h := Finset.prod_dvd_prod_of_subset (W.primeFactors \ ((Finset.range K).powerset).image p)
      W.primeFactors (fun ℓ => ℓ ^ W.factorization ℓ) Finset.sdiff_subset
    rw [← hWeq, ← hWf] at h
    exact h
  have hWfle : Wf ≤ W := Nat.le_of_dvd (Nat.pos_of_ne_zero hW0) hWfdvd
  have hco : ∀ E ∈ (Finset.range K).powerset, Nat.Coprime (p E) Wf := by
    intro E hE
    rw [hWf]
    refine Nat.Coprime.prod_right fun ℓ hℓ => Nat.Coprime.pow_right _ ?_
    obtain ⟨hℓ1, hℓ2⟩ := Finset.mem_sdiff.mp hℓ
    refine (Nat.coprime_primes (hpE E hE).1 (Nat.prime_of_mem_primeFactors hℓ1)).mpr ?_
    intro h
    exact hℓ2 (Finset.mem_image.mpr ⟨E, hE, h⟩)
  obtain ⟨b, hb1, hb2⟩ := crt_exists ((Finset.range K).powerset) p s Wf
    (fun E hE => (hpE E hE).1) hpinj hco
  have hQle : (∏ E ∈ (Finset.range K).powerset, p E) * Wf
      ≤ M ^ (2 ^ K) * (2 * ((K + H + K ^ 2) * M)) ^ ((2 ^ K * H) * (2 ^ K * H)) := by
    have e1 : ∏ E ∈ (Finset.range K).powerset, p E ≤ M ^ (2 ^ K) := by
      have := Finset.prod_le_pow_card (Finset.range K).powerset p M (fun E hE => (hpE E hE).2.2)
      rwa [Finset.card_powerset, Finset.card_range] at this
    exact Nat.mul_le_mul e1 (hWfle.trans hWle)
  have hQB : (((∏ E ∈ (Finset.range K).powerset, p E) * Wf : ℕ) : ℝ)
      ≤ Real.exp (Real.sqrt (Real.log (Real.log x))) := by
    rw [← hB]
    exact (Nat.cast_le.mpr hQle).trans hQb
  have hcast : ∀ z : ℤ, |z| ≤ (((K + H + K ^ 2) * M : ℕ) : ℤ) →
      |(z : ℝ)| ≤ Real.exp (Real.sqrt (Real.log (Real.log x))) := by
    intro z hz
    rw [← hB, ← Int.cast_abs]
    have : ((|z| : ℤ) : ℝ) ≤ (((K + H + K ^ 2) * M : ℕ) : ℝ) := by exact_mod_cast hz
    exact this.trans hRM
  have hsB : ∀ E ∈ (Finset.range K).powerset,
      |((s E : ℤ) : ℝ)| ≤ Real.exp (Real.sqrt (Real.log (Real.log x))) := by
    intro E hE
    refine hcast _ ((hs E hE).trans ?_)
    push_cast
    have : (0 : ℤ) ≤ ((K : ℤ) + H) * M := by positivity
    linarith
  have hrB : ∀ y ∈ (Finset.range K).powerset ×ˢ Finset.Ico (K + 1) (K + H + 1),
      |(((p y.1 : ℤ) * (y.2 : ℤ) - s y.1 : ℤ) : ℝ)|
        ≤ Real.exp (Real.sqrt (Real.log (Real.log x))) := fun y hy => hcast _ (hrabs y hy)
  have hKη : 1 / (2 : ℝ) ^ K ≤ η := by
    have h2K : l ^ 2 < 2 * (2 : ℝ) ^ K := by
      have e : (2 : ℝ) ^ (K + 1) = 2 * 2 ^ K := by ring
      rw [e] at hF2
      exact hF2
    have hll : l ≤ l ^ 2 := by nlinarith
    have hlη' : 2 ≤ l * η := (div_le_iff₀ hη).mp hlη
    have h2Kpos : (0 : ℝ) < 2 ^ K := by positivity
    rw [div_le_iff₀ h2Kpos]
    have a1 : l * η ≤ l ^ 2 * η := mul_le_mul_of_nonneg_right hll hη.le
    have a2 : l ^ 2 * η < 2 * (2 : ℝ) ^ K * η := mul_lt_mul_of_pos_right h2K hη
    linarith
  have hEall : ∀ E ∈ (Finset.range K).powerset,
      (p E).Prime ∧ Real.exp (l ^ 3) ≤ 8 * (p E : ℝ) ∧ (p E : ℝ) ≤ Real.exp (l ^ 3) ∧
      |s E| ≤ 8 * (K : ℤ) ^ 2 * (p E : ℤ) ∧ (b : ℤ) ≡ s E [ZMOD (p E : ℤ)] ∧
      ∀ k < K, (p (symmDiff E {k}) : ℤ) * ((k + 1 : ℕ) : ℤ) - s (symmDiff E {k})
        = (p E : ℤ) * ((k + 1 : ℕ) : ℤ) - s E := by
    intro E hE
    refine ⟨(hpE E hE).1, (hpE E hE).2.1, ?_, ?_, hb1 E hE, hsym E hE⟩
    · exact (Nat.cast_le.mpr (hpE E hE).2.2).trans hMP
    · calc |s E| ≤ (K : ℤ) ^ 2 * M := hs E hE
        _ ≤ (K : ℤ) ^ 2 * (8 * (p E : ℤ)) := mul_le_mul_of_nonneg_left (hM8 E hE) (by positivity)
        _ = 8 * (K : ℤ) ^ 2 * (p E : ℤ) := by ring
  refine ⟨K, H, (∏ E ∈ (Finset.range K).powerset, p E) * Wf, b, p, s, ?_⟩
  subst hWf
  subst hWdef
  subst hl
  intro l B C r S W
  exact ⟨hK, hH, hEall, hpinj, hW0, rfl, hb2, hKη, hQB, hsB, hrB⟩
