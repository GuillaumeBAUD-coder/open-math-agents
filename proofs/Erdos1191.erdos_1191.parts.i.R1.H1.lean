import OMAReductions.R_Erdos1191_erdos_1191_parts_i_R1
import Mathlib.Tactic

/-!
# Finite dyadic scale bound for Sidon sets (Erdos Problem 1191, step H1)

For any Sidon set `S ⊆ [1, 2 ^ (2 * R)]` with `16 ≤ R`, partitioning each dyadic shell
`(2 ^ (R + m), 2 ^ (R + 1 + m)]` (`0 ≤ m < R`) into `2 ^ m` intervals of length `2 ^ R`
bounds the weighted sum of squared shell counts via the distinctness of small positive
differences `b - a ≤ 2 ^ R`. A telescoping recurrence then bounds
`∑ m ∈ range (R + 1), 2 ^ (R - m) * |S ∩ [1, 2 ^ (R + m)]| ^ 2 ≤ 36 * 2 ^ (2 * R)`,
yielding an index `k ∈ [R, 2 * R]` with `|S ∩ [1, 2 ^ k]| ^ 2 * k ≤ 512 * 2 ^ k`.
-/

namespace Erdos1191H1

def ltPairs (T : Finset ℕ) : Finset (ℕ × ℕ) :=
  (T ×ˢ T).filter (fun p => p.1 < p.2)

lemma two_mul_card_ltPairs_add_card (T : Finset ℕ) :
    2 * (ltPairs T).card + T.card = T.card ^ 2 := by
  set L := (T ×ˢ T).filter (fun p => p.1 < p.2)
  set G := (T ×ˢ T).filter (fun p => p.2 < p.1)
  set E := (T ×ˢ T).filter (fun p => p.1 = p.2)
  have hdisj_LG : Disjoint L G :=
    Finset.disjoint_filter.mpr (fun _ _ h1 h2 => by omega)
  have hdisj_LGE : Disjoint (L ∪ G) E := by
    rw [Finset.disjoint_union_left]
    exact ⟨Finset.disjoint_filter.mpr (fun _ _ h1 h2 => by omega),
      Finset.disjoint_filter.mpr (fun _ _ h1 h2 => by omega)⟩
  have hunion : (L ∪ G) ∪ E = T ×ˢ T := by
    ext ⟨a, b⟩
    simp only [L, G, E, Finset.mem_union, Finset.mem_filter, Finset.mem_product]
    constructor
    · rintro ((⟨h, _⟩ | ⟨h, _⟩) | ⟨h, _⟩) <;> exact h
    · intro h
      rcases lt_trichotomy a b with hab | hab | hab
      · exact Or.inl (Or.inl ⟨h, hab⟩)
      · exact Or.inr ⟨h, hab⟩
      · exact Or.inl (Or.inr ⟨h, hab⟩)
  have hGL : G.card = L.card := by
    apply le_antisymm
    · refine Finset.card_le_card_of_injOn Prod.swap ?_ ?_
      · intro ⟨a, b⟩ hp
        simp only [G, L, Finset.mem_coe, Finset.mem_filter, Finset.mem_product, Prod.swap] at hp ⊢
        exact ⟨⟨hp.1.2, hp.1.1⟩, hp.2⟩
      · intro ⟨a1, b1⟩ _ ⟨a2, b2⟩ _ h
        simp only [Prod.swap, Prod.mk.injEq] at h
        exact Prod.ext h.2 h.1
    · refine Finset.card_le_card_of_injOn Prod.swap ?_ ?_
      · intro ⟨a, b⟩ hp
        simp only [G, L, Finset.mem_coe, Finset.mem_filter, Finset.mem_product, Prod.swap] at hp ⊢
        exact ⟨⟨hp.1.2, hp.1.1⟩, hp.2⟩
      · intro ⟨a1, b1⟩ _ ⟨a2, b2⟩ _ h
        simp only [Prod.swap, Prod.mk.injEq] at h
        exact Prod.ext h.2 h.1
  have hET : E.card = T.card := by
    apply le_antisymm
    · refine Finset.card_le_card_of_injOn Prod.fst ?_ ?_
      · intro ⟨a, b⟩ hp
        simp only [E, Finset.mem_coe, Finset.mem_filter, Finset.mem_product] at hp ⊢
        exact hp.1.1
      · intro ⟨a1, b1⟩ hp1 ⟨a2, b2⟩ hp2 h
        simp only [E, Finset.mem_coe, Finset.mem_filter] at hp1 hp2
        dsimp only at h
        exact Prod.ext h (by omega)
    · refine Finset.card_le_card_of_injOn (fun a => (a, a)) ?_ ?_
      · intro a ha
        simp [E] at ha ⊢
        exact ha
      · intro a1 _ a2 _ h
        exact (Prod.mk.inj h).1
  have hprod : (T ×ˢ T).card = T.card ^ 2 := by
    rw [Finset.card_product, sq]
  rw [← hunion, Finset.card_union_of_disjoint hdisj_LGE,
    Finset.card_union_of_disjoint hdisj_LG, hGL, hET] at hprod
  change 2 * L.card + T.card = T.card ^ 2
  omega

def diffPairs (S : Finset ℕ) (M : ℕ) : Finset (ℕ × ℕ) :=
  (ltPairs S).filter (fun p => p.2 - p.1 ≤ M)

lemma card_diffPairs_le {S : Finset ℕ} (hSid : IsSidon (↑S : Set ℕ)) (M : ℕ) :
    (diffPairs S M).card ≤ M := by
  have hle : (diffPairs S M).card ≤ (Finset.range M).card := by
    refine Finset.card_le_card_of_injOn (fun p => p.2 - p.1 - 1) ?_ ?_
    · intro ⟨a, b⟩ hp
      simp only [diffPairs, ltPairs, Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at hp ⊢
      omega
    · intro ⟨a1, b1⟩ hp1 ⟨a2, b2⟩ hp2 heq
      simp only [diffPairs, ltPairs, Finset.mem_coe, Finset.mem_filter,
        Finset.mem_product] at hp1 hp2
      dsimp only at heq
      have hlt1 : a1 < b1 := hp1.1.2
      have hlt2 : a2 < b2 := hp2.1.2
      have hsum : b1 + a2 = b2 + a1 := by omega
      have hb1 : b1 ∈ (↑S : Set ℕ) := Finset.mem_coe.mpr hp1.1.1.2
      have hb2 : b2 ∈ (↑S : Set ℕ) := Finset.mem_coe.mpr hp2.1.1.2
      have ha2 : a2 ∈ (↑S : Set ℕ) := Finset.mem_coe.mpr hp2.1.1.1
      have ha1 : a1 ∈ (↑S : Set ℕ) := Finset.mem_coe.mpr hp1.1.1.1
      rcases hSid b1 hb1 b2 hb2 a2 ha2 a1 ha1 hsum with ⟨rfl, rfl⟩ | ⟨h1, h2⟩
      · rfl
      · omega
  simpa only [Finset.card_range] using hle

lemma int_quad_bound {s M : ℤ} (hM : 2 ≤ M) (h : s ^ 2 ≤ 2 * M ^ 2 + s) : s ≤ 2 * M := by
  by_contra hgt
  have hgt' : 2 * M < s := lt_of_not_ge hgt
  nlinarith

lemma card_sidon_le {R : ℕ} {S : Finset ℕ} (hR : 1 ≤ R)
    (hS_sub : (↑S : Set ℕ) ⊆ Set.Icc 1 (2 ^ (2 * R))) (hSid : IsSidon (↑S : Set ℕ)) :
    S.card ≤ 2 * 2 ^ R := by
  have hsub : ltPairs S ⊆ diffPairs S (2 ^ (2 * R)) := by
    intro ⟨a, b⟩ hp
    simp only [diffPairs, ltPairs, Finset.mem_filter, Finset.mem_product] at hp ⊢
    have hb : b ∈ Set.Icc 1 (2 ^ (2 * R)) := hS_sub (Finset.mem_coe.mpr hp.1.2)
    rw [Set.mem_Icc] at hb
    exact ⟨hp, by omega⟩
  have hlt_le : (ltPairs S).card ≤ 2 ^ (2 * R) :=
    (Finset.card_le_card hsub).trans (card_diffPairs_le hSid (2 ^ (2 * R)))
  have hsq_eq := two_mul_card_ltPairs_add_card S
  have hpow_sq : 2 ^ (2 * R) = (2 ^ R) ^ 2 := by
    rw [mul_comm 2 R, pow_mul]
  have hsq_le : S.card ^ 2 ≤ 2 * (2 ^ R) ^ 2 + S.card := by
    rw [← hpow_sq]
    omega
  have h2R_ge : 2 ≤ 2 ^ R := by
    have h1 : 2 ^ 1 ≤ 2 ^ R := Nat.pow_le_pow_right (by decide) hR
    simpa using h1
  have hint := int_quad_bound (s := (S.card : ℤ)) (M := ((2 ^ R : ℕ) : ℤ))
    (by exact_mod_cast h2R_ge) (by exact_mod_cast hsq_le)
  exact_mod_cast hint

lemma card_prefix_R_sq_le {R : ℕ} {S : Finset ℕ}
    (hS_sub : (↑S : Set ℕ) ⊆ Set.Icc 1 (2 ^ (2 * R))) (hSid : IsSidon (↑S : Set ℕ)) :
    (S.filter (· ≤ 2 ^ R)).card ^ 2 ≤ 3 * 2 ^ R := by
  set T := S.filter (· ≤ 2 ^ R)
  have hT_card : T.card ≤ 2 ^ R := by
    have hle : T.card ≤ (Finset.range (2 ^ R)).card := by
      refine Finset.card_le_card_of_injOn (fun x => x - 1) ?_ ?_
      · intro x hx
        simp only [T, Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at hx ⊢
        have hxS : x ∈ Set.Icc 1 (2 ^ (2 * R)) := hS_sub (Finset.mem_coe.mpr hx.1)
        rw [Set.mem_Icc] at hxS
        omega
      · intro x1 hx1 x2 hx2 heq
        simp only [T, Finset.mem_coe, Finset.mem_filter] at hx1 hx2
        dsimp only at heq
        have hx1S := (Set.mem_Icc.mp (hS_sub (Finset.mem_coe.mpr hx1.1))).1
        have hx2S := (Set.mem_Icc.mp (hS_sub (Finset.mem_coe.mpr hx2.1))).1
        omega
    simpa only [Finset.card_range] using hle
  have hsub : ltPairs T ⊆ diffPairs S (2 ^ R) := by
    intro ⟨a, b⟩ hp
    simp only [T, diffPairs, ltPairs, Finset.mem_filter, Finset.mem_product] at hp ⊢
    exact ⟨⟨⟨hp.1.1.1, hp.1.2.1⟩, hp.2⟩, by omega⟩
  have hlt_le : (ltPairs T).card ≤ 2 ^ R :=
    (Finset.card_le_card hsub).trans (card_diffPairs_le hSid (2 ^ R))
  have hsq_eq := two_mul_card_ltPairs_add_card T
  omega

lemma int_cs_step {K A B x : ℤ} (hK : 0 < K) (hih : A ^ 2 ≤ K * B) :
    (A + x) ^ 2 ≤ (K + 1) * (B + x ^ 2) := by
  have hprod : K * (A + x) ^ 2 ≤ K * ((K + 1) * (B + x ^ 2)) := by
    have hid : K * ((K + 1) * (B + x ^ 2)) - K * (A + x) ^ 2 =
        (K + 1) * (K * B - A ^ 2) + (A - K * x) ^ 2 := by ring
    have hsq : 0 ≤ (A - K * x) ^ 2 := sq_nonneg _
    nlinarith
  exact le_of_mul_le_mul_left hprod hK

lemma sq_sum_range_le (K : ℕ) (f : ℕ → ℕ) :
    (∑ j ∈ Finset.range K, f j) ^ 2 ≤ K * ∑ j ∈ Finset.range K, f j ^ 2 := by
  induction K with
  | zero => simp
  | succ K ih =>
    rcases Nat.eq_zero_or_pos K with rfl | hKpos
    · simp
    · rw [Finset.sum_range_succ, Finset.sum_range_succ]
      have hint := int_cs_step
        (K := (K : ℤ))
        (A := ((∑ j ∈ Finset.range K, f j : ℕ) : ℤ))
        (B := ((∑ j ∈ Finset.range K, f j ^ 2 : ℕ) : ℤ))
        (x := (f K : ℤ))
        (by exact_mod_cast hKpos)
        (by exact_mod_cast ih)
      exact_mod_cast hint

def shell (S : Finset ℕ) (R m : ℕ) : Finset ℕ :=
  S.filter (fun x => 2 ^ (R + m) < x ∧ x ≤ 2 ^ (R + 1 + m))

def slice (S : Finset ℕ) (R m j : ℕ) : Finset ℕ :=
  S.filter (fun x => 2 ^ (R + m) + j * 2 ^ R < x ∧ x ≤ 2 ^ (R + m) + (j + 1) * 2 ^ R)

lemma shell_pow_eq (R m : ℕ) : 2 ^ (R + 1 + m) = 2 ^ (R + m) + 2 ^ m * 2 ^ R := by
  have h1 : R + 1 + m = (R + m) + 1 := by omega
  have h2 : 2 ^ m * 2 ^ R = 2 ^ (R + m) := by
    rw [← pow_add, add_comm m R]
  rw [h1, pow_add, h2]
  ring

lemma shell_eq_biUnion_slice (S : Finset ℕ) (R m : ℕ) :
    shell S R m = (Finset.range (2 ^ m)).biUnion (slice S R m) := by
  ext x
  simp only [shell, slice, Finset.mem_biUnion, Finset.mem_range, Finset.mem_filter]
  have hpow := shell_pow_eq R m
  constructor
  · rintro ⟨hxS, hlow, hhigh⟩
    let u := x - 1 - 2 ^ (R + m)
    have hu_eq : x = 2 ^ (R + m) + 1 + u := by omega
    have hu_lt : u < 2 ^ m * 2 ^ R := by omega
    let j := u / 2 ^ R
    have h2R_pos : 0 < 2 ^ R := by positivity
    have hdiv : 2 ^ R * j + u % 2 ^ R = u := Nat.div_add_mod u (2 ^ R)
    have hmod : u % 2 ^ R < 2 ^ R := Nat.mod_lt u h2R_pos
    have hj_lt : j < 2 ^ m := by
      by_contra hge
      have hle1 : 2 ^ m ≤ j := Nat.le_of_not_lt hge
      have hle2 : 2 ^ m * 2 ^ R ≤ j * 2 ^ R := Nat.mul_le_mul_right (2 ^ R) hle1
      have hcomm : j * 2 ^ R = 2 ^ R * j := mul_comm j (2 ^ R)
      omega
    have hj1 : (j + 1) * 2 ^ R = 2 ^ R * j + 2 ^ R := by ring
    have hj0 : j * 2 ^ R = 2 ^ R * j := mul_comm j (2 ^ R)
    refine ⟨j, hj_lt, hxS, ?_, ?_⟩ <;> omega
  · rintro ⟨j, hj_lt, hxS, hlow, hhigh⟩
    have hj_mul : (j + 1) * 2 ^ R ≤ 2 ^ m * 2 ^ R :=
      Nat.mul_le_mul_right (2 ^ R) (by omega)
    exact ⟨hxS, by omega, by omega⟩

lemma pairwiseDisjoint_slice (S : Finset ℕ) (R m : ℕ) :
    ((Finset.range (2 ^ m) : Set ℕ)).PairwiseDisjoint (slice S R m) := by
  intro j1 _ j2 _ hne
  rw [Function.onFun, Finset.disjoint_left]
  intro x hx1 hx2
  simp only [slice, Finset.mem_filter] at hx1 hx2
  rcases lt_trichotomy j1 j2 with hlt | rfl | hlt
  · have hmul : (j1 + 1) * 2 ^ R ≤ j2 * 2 ^ R := Nat.mul_le_mul_right (2 ^ R) hlt
    omega
  · exact hne rfl
  · have hmul : (j2 + 1) * 2 ^ R ≤ j1 * 2 ^ R := Nat.mul_le_mul_right (2 ^ R) hlt
    omega

lemma card_shell_eq_sum_slice (S : Finset ℕ) (R m : ℕ) :
    (shell S R m).card = ∑ j ∈ Finset.range (2 ^ m), (slice S R m j).card := by
  rw [shell_eq_biUnion_slice, Finset.card_biUnion (pairwiseDisjoint_slice S R m)]

lemma pairwiseDisjoint_shell (S : Finset ℕ) (R : ℕ) :
    ((Finset.range R : Set ℕ)).PairwiseDisjoint (shell S R) := by
  intro m1 _ m2 _ hne
  rw [Function.onFun, Finset.disjoint_left]
  intro x hx1 hx2
  simp only [shell, Finset.mem_filter] at hx1 hx2
  rcases lt_trichotomy m1 m2 with hlt | rfl | hlt
  · have hpow : 2 ^ (R + 1 + m1) ≤ 2 ^ (R + m2) :=
      Nat.pow_le_pow_right (by decide) (by omega)
    omega
  · exact hne rfl
  · have hpow : 2 ^ (R + 1 + m2) ≤ 2 ^ (R + m1) :=
      Nat.pow_le_pow_right (by decide) (by omega)
    omega

lemma sum_card_shell_le (S : Finset ℕ) (R : ℕ) :
    ∑ m ∈ Finset.range R, (shell S R m).card ≤ S.card := by
  rw [← Finset.card_biUnion (pairwiseDisjoint_shell S R)]
  apply Finset.card_le_card
  intro x hx
  simp only [shell, Finset.mem_biUnion, Finset.mem_filter] at hx
  rcases hx with ⟨_, _, hxS, _⟩
  exact hxS

lemma slice_subset_shell {S : Finset ℕ} {R m j : ℕ} (hj : j ∈ Finset.range (2 ^ m)) :
    slice S R m j ⊆ shell S R m := by
  rw [shell_eq_biUnion_slice]
  exact Finset.subset_biUnion_of_mem (slice S R m) hj

lemma sum_ltPairs_slice_le {R : ℕ} {S : Finset ℕ} (hSid : IsSidon (↑S : Set ℕ)) :
    ∑ m ∈ Finset.range R, ∑ j ∈ Finset.range (2 ^ m), (ltPairs (slice S R m j)).card ≤
      2 ^ R := by
  set U : ℕ → Finset (ℕ × ℕ) := fun m =>
    (Finset.range (2 ^ m)).biUnion (fun j => ltPairs (slice S R m j))
  have hU_card : ∀ m, (U m).card =
      ∑ j ∈ Finset.range (2 ^ m), (ltPairs (slice S R m j)).card := by
    intro m
    apply Finset.card_biUnion
    intro j1 hj1 j2 hj2 hne
    rw [Function.onFun, Finset.disjoint_left]
    intro p hp1 hp2
    simp only [ltPairs, Finset.mem_filter, Finset.mem_product] at hp1 hp2
    exact Finset.disjoint_left.mp (pairwiseDisjoint_slice S R m hj1 hj2 hne) hp1.1.1 hp2.1.1
  have hU_disj : ((Finset.range R : Set ℕ)).PairwiseDisjoint U := by
    intro m1 hm1 m2 hm2 hne
    rw [Function.onFun, Finset.disjoint_left]
    intro p hp1 hp2
    simp only [U, Finset.mem_biUnion, ltPairs, Finset.mem_filter, Finset.mem_product] at hp1 hp2
    rcases hp1 with ⟨j1, hj1, ⟨hp1a, _⟩, _⟩
    rcases hp2 with ⟨j2, hj2, ⟨hp2a, _⟩, _⟩
    have hs1 := slice_subset_shell hj1 hp1a
    have hs2 := slice_subset_shell hj2 hp2a
    exact Finset.disjoint_left.mp (pairwiseDisjoint_shell S R hm1 hm2 hne) hs1 hs2
  have hsub : (Finset.range R).biUnion U ⊆ diffPairs S (2 ^ R) := by
    intro ⟨a, b⟩ hp
    simp only [U, Finset.mem_biUnion, ltPairs, slice, diffPairs,
      Finset.mem_filter, Finset.mem_product] at hp ⊢
    rcases hp with ⟨m, _, j, _, ⟨⟨haS, haL, _⟩, ⟨hbS, _, hbH⟩⟩, hab⟩
    have hstep : (j + 1) * 2 ^ R = j * 2 ^ R + 2 ^ R := by ring
    exact ⟨⟨⟨haS, hbS⟩, hab⟩, by omega⟩
  calc
    ∑ m ∈ Finset.range R, ∑ j ∈ Finset.range (2 ^ m), (ltPairs (slice S R m j)).card
        = ∑ m ∈ Finset.range R, (U m).card :=
          Finset.sum_congr rfl (fun m _ => (hU_card m).symm)
    _ = ((Finset.range R).biUnion U).card := (Finset.card_biUnion hU_disj).symm
    _ ≤ (diffPairs S (2 ^ R)).card := Finset.card_le_card hsub
    _ ≤ 2 ^ R := card_diffPairs_le hSid (2 ^ R)

lemma sum_weighted_shell_sq_le {R : ℕ} {S : Finset ℕ} (hR : 1 ≤ R)
    (hS_sub : (↑S : Set ℕ) ⊆ Set.Icc 1 (2 ^ (2 * R))) (hSid : IsSidon (↑S : Set ℕ)) :
    ∑ m ∈ Finset.range R, 2 ^ (R - 1 - m) * (shell S R m).card ^ 2 ≤ 2 * 2 ^ (2 * R) := by
  have hsum_sq_slice :
      ∑ m ∈ Finset.range R, ∑ j ∈ Finset.range (2 ^ m), (slice S R m j).card ^ 2 ≤
        4 * 2 ^ R := by
    have heq : ∑ m ∈ Finset.range R, ∑ j ∈ Finset.range (2 ^ m), (slice S R m j).card ^ 2 =
        2 * (∑ m ∈ Finset.range R, ∑ j ∈ Finset.range (2 ^ m),
          (ltPairs (slice S R m j)).card) +
        ∑ m ∈ Finset.range R, (shell S R m).card := by
      simp_rw [← two_mul_card_ltPairs_add_card, Finset.sum_add_distrib, ← Finset.mul_sum,
        ← card_shell_eq_sum_slice]
    have h1 := sum_ltPairs_slice_le (R := R) hSid
    have h2 := (sum_card_shell_le S R).trans (card_sidon_le hR hS_sub hSid)
    omega
  have hterm : ∀ m ∈ Finset.range R,
      2 ^ (R - 1 - m) * (shell S R m).card ^ 2 ≤
        2 ^ (R - 1) * ∑ j ∈ Finset.range (2 ^ m), (slice S R m j).card ^ 2 := by
    intro m hm
    rw [Finset.mem_range] at hm
    have hcs : (shell S R m).card ^ 2 ≤
        2 ^ m * ∑ j ∈ Finset.range (2 ^ m), (slice S R m j).card ^ 2 := by
      rw [card_shell_eq_sum_slice]
      exact sq_sum_range_le (2 ^ m) (fun j => (slice S R m j).card)
    calc
      2 ^ (R - 1 - m) * (shell S R m).card ^ 2
          ≤ 2 ^ (R - 1 - m) * (2 ^ m * ∑ j ∈ Finset.range (2 ^ m), (slice S R m j).card ^ 2) :=
            Nat.mul_le_mul_left _ hcs
      _ = (2 ^ (R - 1 - m) * 2 ^ m) * ∑ j ∈ Finset.range (2 ^ m), (slice S R m j).card ^ 2 := by
            ring
      _ = 2 ^ (R - 1) * ∑ j ∈ Finset.range (2 ^ m), (slice S R m j).card ^ 2 := by
            rw [← pow_add, show R - 1 - m + m = R - 1 by omega]
  calc
    ∑ m ∈ Finset.range R, 2 ^ (R - 1 - m) * (shell S R m).card ^ 2
        ≤ ∑ m ∈ Finset.range R,
            2 ^ (R - 1) * ∑ j ∈ Finset.range (2 ^ m), (slice S R m j).card ^ 2 :=
          Finset.sum_le_sum hterm
    _ = 2 ^ (R - 1) *
          ∑ m ∈ Finset.range R, ∑ j ∈ Finset.range (2 ^ m), (slice S R m j).card ^ 2 := by
          rw [Finset.mul_sum]
    _ ≤ 2 ^ (R - 1) * (4 * 2 ^ R) := Nat.mul_le_mul_left _ hsum_sq_slice
    _ = 2 * 2 ^ (2 * R) := by
          have hexp : 2 * R = (R - 1) + R + 1 := by omega
          rw [hexp, pow_add, pow_add]
          ring

def prefCard (S : Finset ℕ) (k : ℕ) : ℕ :=
  (S.filter (· ≤ 2 ^ k)).card

lemma prefCard_step (S : Finset ℕ) (R m : ℕ) :
    prefCard S (R + (m + 1)) = prefCard S (R + m) + (shell S R m).card := by
  have hdisj : Disjoint (S.filter (· ≤ 2 ^ (R + m))) (shell S R m) :=
    Finset.disjoint_filter.mpr (fun _ _ h1 h2 => by omega)
  have hunion : S.filter (· ≤ 2 ^ (R + (m + 1))) =
      S.filter (· ≤ 2 ^ (R + m)) ∪ shell S R m := by
    ext x
    simp only [shell, Finset.mem_union, Finset.mem_filter]
    have hpow : 2 ^ (R + m) ≤ 2 ^ (R + 1 + m) :=
      Nat.pow_le_pow_right (by decide) (by omega)
    have heq : R + (m + 1) = R + 1 + m := by omega
    rw [heq]
    constructor
    · intro ⟨hxS, hle⟩
      by_cases h : x ≤ 2 ^ (R + m)
      · exact Or.inl ⟨hxS, h⟩
      · exact Or.inr ⟨hxS, by omega, hle⟩
    · rintro (⟨hxS, hle⟩ | ⟨hxS, _, hle⟩)
      · exact ⟨hxS, by omega⟩
      · exact ⟨hxS, hle⟩
  simp only [prefCard]
  rw [hunion, Finset.card_union_of_disjoint hdisj]

lemma four_mul_add_sq_le (a b : ℕ) : 4 * (a + b) ^ 2 ≤ 6 * a ^ 2 + 12 * b ^ 2 := by
  have hint : 4 * ((a : ℤ) + (b : ℤ)) ^ 2 ≤ 6 * (a : ℤ) ^ 2 + 12 * (b : ℤ) ^ 2 := by
    nlinarith [sq_nonneg ((a : ℤ) - 2 * (b : ℤ))]
  exact_mod_cast hint

lemma telescope_bound {K : ℕ} (W E : ℕ → ℕ)
    (hstep : ∀ m < K, 4 * W (m + 1) ≤ 3 * W m + E m) :
    (∑ m ∈ Finset.range (K + 1), W m) + 3 * W K ≤ 4 * W 0 + ∑ m ∈ Finset.range K, E m := by
  induction K with
  | zero =>
    simp
    omega
  | succ K ih =>
    have ih' := ih (fun m hm => hstep m (by omega))
    have hk := hstep K (by omega)
    rw [Finset.sum_range_succ W (K + 1), Finset.sum_range_succ E K]
    omega

end Erdos1191H1

theorem prove_Erdos1191_H1 :
    ∀ (R : ℕ) (S : Finset ℕ), 16 ≤ R → (↑S : Set ℕ) ⊆ Set.Icc 1 (2 ^ (2 * R)) →
      IsSidon (↑S : Set ℕ) →
        ∃ k ∈ Set.Icc R (2 * R), (S.filter (· ≤ 2 ^ k)).card ^ 2 * k ≤ 512 * 2 ^ k := by
  intro R S hR16 hS_sub hSid
  have hR1 : 1 ≤ R := by omega
  set W : ℕ → ℕ := fun m => 2 ^ (R - m) * (Erdos1191H1.prefCard S (R + m)) ^ 2
  set E : ℕ → ℕ := fun m => 12 * (2 ^ (R - 1 - m) * (Erdos1191H1.shell S R m).card ^ 2)
  have hstep : ∀ m < R, 4 * W (m + 1) ≤ 3 * W m + E m := by
    intro m hm
    set a := Erdos1191H1.prefCard S (R + m)
    set b := (Erdos1191H1.shell S R m).card
    have hsq := Erdos1191H1.four_mul_add_sq_le a b
    have hmul := Nat.mul_le_mul_left (2 ^ (R - 1 - m)) hsq
    have hsub1 : R - (m + 1) = R - 1 - m := by omega
    have hpow_m : 2 ^ (R - m) = 2 * 2 ^ (R - 1 - m) := by
      have he : R - m = (R - 1 - m) + 1 := by omega
      rw [he, pow_add]
      ring
    have hW1 : 4 * W (m + 1) = 2 ^ (R - 1 - m) * (4 * (a + b) ^ 2) := by
      simp only [W, hsub1, Erdos1191H1.prefCard_step]
      ring
    have hW0 : 3 * W m + E m = 2 ^ (R - 1 - m) * (6 * a ^ 2 + 12 * b ^ 2) := by
      simp only [W, E, hpow_m]
      ring
    rw [hW1, hW0]
    exact hmul
  have htele := Erdos1191H1.telescope_bound W E hstep
  have hW0_le : W 0 ≤ 3 * 2 ^ (2 * R) := by
    have hp := Erdos1191H1.card_prefix_R_sq_le hS_sub hSid
    have h0 : W 0 = 2 ^ R * (S.filter (· ≤ 2 ^ R)).card ^ 2 := by
      simp [W, Erdos1191H1.prefCard]
    calc
      W 0 = 2 ^ R * (S.filter (· ≤ 2 ^ R)).card ^ 2 := h0
      _ ≤ 2 ^ R * (3 * 2 ^ R) := Nat.mul_le_mul_left _ hp
      _ = 3 * 2 ^ (2 * R) := by
            have he : 2 * R = R + R := by omega
            rw [he, pow_add]
            ring
  have hE_sum : ∑ m ∈ Finset.range R, E m ≤ 24 * 2 ^ (2 * R) := by
    have hshell := Erdos1191H1.sum_weighted_shell_sq_le hR1 hS_sub hSid
    have heq : ∑ m ∈ Finset.range R, E m =
        12 * ∑ m ∈ Finset.range R, 2 ^ (R - 1 - m) * (Erdos1191H1.shell S R m).card ^ 2 := by
      simp only [E, ← Finset.mul_sum]
    rw [heq]
    omega
  have hTotal_le : ∑ m ∈ Finset.range (R + 1), W m ≤ 36 * 2 ^ (2 * R) := by
    omega
  by_contra hcontra
  push Not at hcontra
  have hterm_gt : ∀ m ∈ Finset.range (R + 1), 36 * 2 ^ (2 * R) + 1 ≤ (R + 1) * W m := by
    intro m hm
    rw [Finset.mem_range] at hm
    have hk_mem : R + m ∈ Set.Icc R (2 * R) := by
      rw [Set.mem_Icc]
      omega
    have hk_gt : 512 * 2 ^ (R + m) < (Erdos1191H1.prefCard S (R + m)) ^ 2 * (R + m) :=
      hcontra (R + m) hk_mem
    have hk_le : (Erdos1191H1.prefCard S (R + m)) ^ 2 * (R + m) ≤
        (Erdos1191H1.prefCard S (R + m)) ^ 2 * (2 * (R + 1)) :=
      Nat.mul_le_mul_left _ (by omega)
    have hpos_pow : 0 < 2 ^ (R - m) := by positivity
    have hmul_lt : 2 ^ (R - m) * (512 * 2 ^ (R + m)) <
        2 ^ (R - m) * ((Erdos1191H1.prefCard S (R + m)) ^ 2 * (2 * (R + 1))) :=
      Nat.mul_lt_mul_of_pos_left (lt_of_lt_of_le hk_gt hk_le) hpos_pow
    have hlhs : 2 ^ (R - m) * (512 * 2 ^ (R + m)) = 512 * 2 ^ (2 * R) := by
      have he : (R - m) + (R + m) = 2 * R := by omega
      calc
        2 ^ (R - m) * (512 * 2 ^ (R + m)) = 512 * (2 ^ (R - m) * 2 ^ (R + m)) := by ring
        _ = 512 * 2 ^ (2 * R) := by rw [← pow_add, he]
    have hrhs : 2 ^ (R - m) * ((Erdos1191H1.prefCard S (R + m)) ^ 2 * (2 * (R + 1))) =
        2 * ((R + 1) * W m) := by
      simp only [W]
      ring
    rw [hlhs, hrhs] at hmul_lt
    omega
  have hsum_gt : ∑ m ∈ Finset.range (R + 1), (36 * 2 ^ (2 * R) + 1) ≤
      ∑ m ∈ Finset.range (R + 1), (R + 1) * W m :=
    Finset.sum_le_sum hterm_gt
  rw [Finset.sum_const, Finset.card_range, smul_eq_mul, ← Finset.mul_sum] at hsum_gt
  have hsum_le : (R + 1) * ∑ m ∈ Finset.range (R + 1), W m ≤ (R + 1) * (36 * 2 ^ (2 * R)) :=
    Nat.mul_le_mul_left (R + 1) hTotal_le
  have hexpand : (R + 1) * (36 * 2 ^ (2 * R) + 1) =
      (R + 1) * (36 * 2 ^ (2 * R)) + (R + 1) := by ring
  omega

theorem OMA.solution : OMA.R_Erdos1191_erdos_1191_parts_i_R1.H1 :=
  prove_Erdos1191_H1
