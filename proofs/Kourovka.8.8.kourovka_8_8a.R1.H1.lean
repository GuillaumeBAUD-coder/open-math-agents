import OMAReductions.R_Kourovka_8_8_kourovka_8_8a_R1
import Mathlib

/-!
# Proof of `Kourovka.8.8.kourovka_8_8a.R1.H1`

Maximal cyclic / primitive root theorem for torsion-free Gromov-hyperbolic 2-generated quotients
`Q = FreeGroup (Fin 2) / N` (Gromov 1987; Bridson-Haefliger III.Gamma.3.10): every nontrivial
element `g != 1` is an integer power `c ^ r` of a primitive element `c` of `Q`.

## Elementary Metric Proof
Let `d` be the word metric on `Q` induced by `FreeGroup (Fin 2)`.
1. Establish geodesic segments `gamma : Nat -> Q` with `d (gamma i) (gamma j) = |i - j|` for
   `i, j <= L`, finite metric balls `|Ball(1, R)| <= (R + 1) * 4 ^ R`, and unboundedness of
   `d 1 (g ^ N)` for `g != 1` using torsion-freeness.
2. Prove the 4-delta thin-triangle inequality directly from the 4-point delta-hyperbolicity
   inequality, and apply it twice to commuting quadrilaterals `(1, v, u * v, u)` to show that
   every commuting element `u` shifts the middle of a geodesic `[1, v]` into the 8-delta
   neighborhood of `[1, v]` by the signed displacement `s(u) = d 1 (u * v) - d 1 v`.
3. For any `h ^ n = g` (`n >= 1`), choosing `N` so that `L = d 1 (g ^ N)` dominates
   `max_{k <= n} d 1 (h ^ k)`, the shift `s(k) = d 1 (h ^ k * g ^ N) - L` is a 24-delta
   quasi-morphism on `{0, ..., n}` with `|s(n)| <= d 1 g`.
4. By a 4-line doubling argument at the extremum of `|s(k)|`, `|s(k)| <= 72 * delta + 2 * d 1 g`
   for all `0 <= k <= n`, forcing all `n + 1` distinct conjugates `p⁻¹ * h ^ k * p` (where `p` is
   the midpoint of `[1, g ^ N]`) into `Ball(1, 80 * delta + 2 * d 1 g)`.
5. This yields a uniform upper bound on root exponents `n` depending only on `g` and `delta`;
   taking a maximal root exponent `r >= 1` produces a primitive `c` with `g = c ^ r`.

Attribution: Gromov (1987), Bridson-Haefliger (1999) III.Gamma.3.10.
-/

namespace Kourovka88R1H1

open FreeGroup

private abbrev F2 := FreeGroup (Fin 2)

private noncomputable def wd (N : Subgroup F2) [N.Normal] (u v : F2 ⧸ N) : ℕ :=
  sInf {k : ℕ | ∃ s : F2, s.toWord.length = k ∧ QuotientGroup.mk s = u⁻¹ * v}

private lemma red_length_le {L₁ L₂ : List (Fin 2 × Bool)} (hred : FreeGroup.Red L₁ L₂) :
    L₂.length ≤ L₁.length := by
  induction hred with
  | refl => exact le_rfl
  | tail _ hstep ih =>
    cases hstep with
    | not =>
      simp only [List.length_append, List.length_cons] at ih ⊢
      omega

private lemma toWord_mk_length_le (L : List (Fin 2 × Bool)) :
    (FreeGroup.mk L).toWord.length ≤ L.length := by
  rw [FreeGroup.toWord_mk]
  exact red_length_le FreeGroup.reduce.red

private lemma wd_set_nonempty (N : Subgroup F2) [N.Normal] (u v : F2 ⧸ N) :
    {k : ℕ | ∃ s : F2, s.toWord.length = k ∧ QuotientGroup.mk s = u⁻¹ * v}.Nonempty := by
  obtain ⟨s, hs⟩ := QuotientGroup.mk_surjective (u⁻¹ * v)
  exact ⟨s.toWord.length, s, rfl, hs⟩

private lemma wd_spec (N : Subgroup F2) [N.Normal] (u v : F2 ⧸ N) :
    ∃ s : F2, s.toWord.length = wd N u v ∧ QuotientGroup.mk s = u⁻¹ * v :=
  Nat.sInf_mem (wd_set_nonempty N u v)

private lemma wd_le_of_mk {N : Subgroup F2} [N.Normal] {u v : F2 ⧸ N} {s : F2}
    (hs : QuotientGroup.mk s = u⁻¹ * v) : wd N u v ≤ s.toWord.length :=
  Nat.sInf_le ⟨s, rfl, hs⟩

private lemma wd_le_of_mk_list {N : Subgroup F2} [N.Normal] {u v : F2 ⧸ N}
    {L : List (Fin 2 × Bool)} (hL : QuotientGroup.mk (FreeGroup.mk L) = u⁻¹ * v) :
    wd N u v ≤ L.length :=
  (wd_le_of_mk hL).trans (toWord_mk_length_le L)

private lemma wd_self (N : Subgroup F2) [N.Normal] (u : F2 ⧸ N) : wd N u u = 0 := by
  have h0 : wd N u u ≤ (1 : F2).toWord.length :=
    wd_le_of_mk (by simp)
  simpa using h0

private lemma wd_left_mul (N : Subgroup F2) [N.Normal] (x u v : F2 ⧸ N) :
    wd N (x * u) (x * v) = wd N u v := by
  unfold wd
  have heq : (x * u)⁻¹ * (x * v) = u⁻¹ * v := by group
  rw [heq]

private lemma wd_symm (N : Subgroup F2) [N.Normal] (u v : F2 ⧸ N) :
    wd N u v = wd N v u := by
  have hle : ∀ a b : F2 ⧸ N, wd N a b ≤ wd N b a := by
    intro a b
    obtain ⟨s, hslen, hsmk⟩ := wd_spec N b a
    have hinv : QuotientGroup.mk s⁻¹ = a⁻¹ * b := by
      rw [QuotientGroup.mk_inv, hsmk]
      group
    have hsinv_eq : s⁻¹ = FreeGroup.mk (FreeGroup.invRev s.toWord) := by
      conv_lhs => rw [← FreeGroup.mk_toWord (x := s)]
      rfl
    have hlen : wd N a b ≤ (FreeGroup.invRev s.toWord).length := by
      apply wd_le_of_mk_list
      rw [← hsinv_eq]
      exact hinv
    rw [FreeGroup.invRev_length, hslen] at hlen
    exact hlen
  exact le_antisymm (hle u v) (hle v u)

private lemma wd_triangle (N : Subgroup F2) [N.Normal] (u v w : F2 ⧸ N) :
    wd N u w ≤ wd N u v + wd N v w := by
  obtain ⟨s₁, hs₁len, hs₁mk⟩ := wd_spec N u v
  obtain ⟨s₂, hs₂len, hs₂mk⟩ := wd_spec N v w
  have hmul : s₁ * s₂ = FreeGroup.mk (s₁.toWord ++ s₂.toWord) := by
    conv_lhs => rw [← FreeGroup.mk_toWord (x := s₁), ← FreeGroup.mk_toWord (x := s₂)]
    rfl
  have hmk : QuotientGroup.mk (FreeGroup.mk (s₁.toWord ++ s₂.toWord)) = u⁻¹ * w := by
    rw [← hmul, QuotientGroup.mk_mul, hs₁mk, hs₂mk]
    group
  calc wd N u w ≤ (s₁.toWord ++ s₂.toWord).length := wd_le_of_mk_list hmk
    _ = s₁.toWord.length + s₂.toWord.length := List.length_append
    _ = wd N u v + wd N v w := by rw [hs₁len, hs₂len]

private lemma exists_geodesic (N : Subgroup F2) [N.Normal] (u v : F2 ⧸ N) :
    ∃ γ : ℕ → F2 ⧸ N,
      γ 0 = u ∧ γ (wd N u v) = v ∧
      ∀ i j : ℕ, i ≤ wd N u v → j ≤ wd N u v →
        (wd N (γ i) (γ j) : ℤ) = |(i : ℤ) - (j : ℤ)| := by
  obtain ⟨s, hslen, hsmk⟩ := wd_spec N u v
  let L := s.toWord
  have hLlen : L.length = wd N u v := hslen
  let γ : ℕ → F2 ⧸ N := fun i => u * QuotientGroup.mk (FreeGroup.mk (L.take i))
  have h0 : γ 0 = u := by
    change u * QuotientGroup.mk (FreeGroup.mk []) = u
    change u * QuotientGroup.mk (1 : F2) = u
    simp
  have hEnd : γ (wd N u v) = v := by
    dsimp [γ]
    rw [← hLlen, List.take_length]
    change u * QuotientGroup.mk (FreeGroup.mk s.toWord) = v
    rw [FreeGroup.mk_toWord, hsmk]
    group
  have hdist_le : ∀ i j : ℕ, i ≤ j → j ≤ wd N u v → wd N (γ i) (γ j) ≤ j - i := by
    intro i j hij hj
    let seg := (L.drop i).take (j - i)
    have happ : L.take i ++ seg = L.take j := by
      have h1 : L.take i ++ L.drop i = L := List.take_append_drop i L
      have h2 := congrArg (List.take j) h1
      rw [List.take_append, List.length_take_of_le (by omega : i ≤ L.length),
        List.take_take, Nat.min_eq_right hij] at h2
      exact h2
    have hmul : FreeGroup.mk (L.take i) * FreeGroup.mk seg = FreeGroup.mk (L.take j) := by
      change FreeGroup.mk (L.take i ++ seg) = FreeGroup.mk (L.take j)
      rw [happ]
    have hmk : QuotientGroup.mk (FreeGroup.mk seg) = (γ i)⁻¹ * γ j := by
      dsimp [γ]
      have hq : (QuotientGroup.mk (FreeGroup.mk (L.take i)) : F2 ⧸ N) *
          (QuotientGroup.mk (FreeGroup.mk seg) : F2 ⧸ N) =
          (QuotientGroup.mk (FreeGroup.mk (L.take j)) : F2 ⧸ N) := by
        rw [← QuotientGroup.mk_mul, hmul]
      calc (QuotientGroup.mk (FreeGroup.mk seg) : F2 ⧸ N)
          = (QuotientGroup.mk (FreeGroup.mk (L.take i)) : F2 ⧸ N)⁻¹ *
              ((QuotientGroup.mk (FreeGroup.mk (L.take i)) : F2 ⧸ N) *
                (QuotientGroup.mk (FreeGroup.mk seg) : F2 ⧸ N)) := by group
        _ = (QuotientGroup.mk (FreeGroup.mk (L.take i)) : F2 ⧸ N)⁻¹ *
              (QuotientGroup.mk (FreeGroup.mk (L.take j)) : F2 ⧸ N) := by rw [hq]
        _ = (u * (QuotientGroup.mk (FreeGroup.mk (L.take i)) : F2 ⧸ N))⁻¹ *
              (u * (QuotientGroup.mk (FreeGroup.mk (L.take j)) : F2 ⧸ N)) := by group
    have hseglen : seg.length = j - i := by
      dsimp [seg]
      rw [List.length_take_of_le]
      rw [List.length_drop]
      omega
    exact (wd_le_of_mk_list hmk).trans (by omega)
  have hdist_eq : ∀ i j : ℕ, i ≤ j → j ≤ wd N u v → wd N (γ i) (γ j) = j - i := by
    intro i j hij hj
    have h1 : wd N (γ 0) (γ i) ≤ i := by simpa using hdist_le 0 i (Nat.zero_le i) (by omega)
    have h2 : wd N (γ i) (γ j) ≤ j - i := hdist_le i j hij hj
    have h3 : wd N (γ j) (γ (wd N u v)) ≤ wd N u v - j := hdist_le j (wd N u v) hj le_rfl
    have ht1 : wd N (γ 0) (γ j) ≤ wd N (γ 0) (γ i) + wd N (γ i) (γ j) :=
      wd_triangle N (γ 0) (γ i) (γ j)
    have ht2 : wd N (γ 0) (γ (wd N u v)) ≤ wd N (γ 0) (γ j) + wd N (γ j) (γ (wd N u v)) :=
      wd_triangle N (γ 0) (γ j) (γ (wd N u v))
    rw [h0] at h1 ht1 ht2
    rw [hEnd] at h3 ht2
    omega
  refine ⟨γ, h0, hEnd, ?_⟩
  intro i j hi hj
  rcases le_total i j with hij | hji
  · have h := hdist_eq i j hij hj
    have hsub : (i : ℤ) - (j : ℤ) ≤ 0 := by omega
    rw [abs_of_nonpos hsub, h]
    omega
  · have h := hdist_eq j i hji hi
    rw [wd_symm N (γ i) (γ j), h]
    have hsub : 0 ≤ (i : ℤ) - (j : ℤ) := by omega
    rw [abs_of_nonneg hsub]
    omega

private lemma ball_card_le (N : Subgroup F2) [N.Normal] (R : ℕ) :
    ∃ B : Finset (F2 ⧸ N), (∀ x : F2 ⧸ N, wd N 1 x ≤ R → x ∈ B) ∧
      B.card ≤ (R + 1) * 4 ^ R := by
  classical
  let α := Σ k : Fin (R + 1), Fin k.val → Fin 2 × Bool
  let φ : α → F2 ⧸ N := fun p => QuotientGroup.mk (FreeGroup.mk (List.ofFn p.2))
  let B : Finset (F2 ⧸ N) := Finset.univ.image φ
  refine ⟨B, ?_, ?_⟩
  · intro x hx
    obtain ⟨s, hslen, hsmk⟩ := wd_spec N 1 x
    rw [inv_one, one_mul] at hsmk
    let k : Fin (R + 1) := ⟨s.toWord.length, by omega⟩
    let f : Fin k.val → Fin 2 × Bool := fun i => s.toWord[i.val]
    refine Finset.mem_image.mpr ⟨⟨k, f⟩, Finset.mem_univ _, ?_⟩
    dsimp [φ]
    have hof : List.ofFn f = s.toWord := List.ofFn_getElem (xs := s.toWord)
    rw [hof, FreeGroup.mk_toWord, hsmk]
  · calc B.card ≤ (Finset.univ : Finset α).card := Finset.card_image_le
      _ = ∑ k : Fin (R + 1), Fintype.card (Fin k.val → Fin 2 × Bool) := by
            rw [Finset.card_univ, Fintype.card_sigma]
      _ = ∑ k : Fin (R + 1), 4 ^ k.val := by
            refine Finset.sum_congr rfl fun k _ => ?_
            simp
      _ ≤ ∑ _k : Fin (R + 1), 4 ^ R := by
            refine Finset.sum_le_sum fun k _ => ?_
            exact Nat.pow_le_pow_right (by decide) (by omega)
      _ = (R + 1) * 4 ^ R := by
            simp

private lemma exists_pow_large_wd (N : Subgroup F2) [N.Normal]
    (htf : ∀ g : F2 ⧸ N, ∀ n : ℕ, n ≠ 0 → g ^ n = 1 → g = 1)
    {g : F2 ⧸ N} (hg : g ≠ 1) (M : ℕ) :
    ∃ K : ℕ, M ≤ wd N 1 (g ^ K) := by
  by_contra h
  push Not at h
  obtain ⟨B, hBmem, _⟩ := ball_card_le N M
  let f : Fin (B.card + 1) → F2 ⧸ N := fun i => g ^ i.val
  have hmaps : Set.MapsTo f (Finset.univ : Finset (Fin (B.card + 1))) (B : Set (F2 ⧸ N)) := by
    intro i _
    exact hBmem (g ^ i.val) (le_of_lt (h i.val))
  have hlt : B.card < (Finset.univ : Finset (Fin (B.card + 1))).card := by simp
  obtain ⟨i, -, j, -, hij, hfeq⟩ := Finset.exists_ne_map_eq_of_card_lt_of_maps_to hlt hmaps
  have hpow : ∀ a b : ℕ, a < b → g ^ a = g ^ b → False := by
    intro a b hab heq
    have h1 : g ^ (b - a) = 1 := by
      have hsplit : g ^ a * g ^ (b - a) = g ^ a * 1 := by
        rw [← pow_add, Nat.add_sub_cancel' hab.le, mul_one, heq]
      exact mul_left_cancel hsplit
    exact hg (htf g (b - a) (by omega) h1)
  rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hij) with hlt' | hgt'
  · exact hpow i.val j.val hlt' hfeq
  · exact hpow j.val i.val hgt' hfeq.symm

private lemma thin_triangle {N : Subgroup F2} [N.Normal] {δ : ℕ}
    (hhyp : ∀ x y z w : F2 ⧸ N,
      wd N x y + wd N z w ≤ max (wd N x z + wd N y w) (wd N x w + wd N y z) + 2 * δ)
    {x y z p q : F2 ⧸ N}
    (hp : wd N x p + wd N p y = wd N x y)
    (hq : wd N x q + wd N q z = wd N x z)
    (heq : wd N x p = wd N x q)
    (hgrom : 2 * wd N x p + wd N y z ≤ wd N x y + wd N x z) :
    wd N p q ≤ 4 * δ := by
  have h1 := hhyp p z x y
  rw [wd_symm N p x, wd_symm N z y, wd_symm N z x] at h1
  have hstep1 : wd N p z + wd N x p ≤ wd N x z + 2 * δ := by omega
  have h2 := hhyp p q x z
  rw [wd_symm N p x, wd_symm N q x] at h2
  omega

private lemma comm_shift_on_geodesic {N : Subgroup F2} [N.Normal] {δ : ℕ}
    (hhyp : ∀ x y z w : F2 ⧸ N,
      wd N x y + wd N z w ≤ max (wd N x z + wd N y w) (wd N x w + wd N y z) + 2 * δ)
    {u v : F2 ⧸ N} (hcomm : u * v = v * u)
    {γ : ℕ → F2 ⧸ N}
    (hγ0 : γ 0 = 1) (hγL : γ (wd N 1 v) = v)
    (hγd : ∀ i j : ℕ, i ≤ wd N 1 v → j ≤ wd N 1 v →
      (wd N (γ i) (γ j) : ℤ) = |(i : ℤ) - (j : ℤ)|)
    {t : ℕ} (ht1 : 3 * wd N 1 u ≤ t) (ht2 : t + 3 * wd N 1 u ≤ wd N 1 v) :
    let L := wd N 1 v
    let L' := wd N 1 (u * v)
    let t' := ((t : ℤ) + (L' : ℤ) - (L : ℤ)).toNat
    wd N (u * γ t) (γ t') ≤ 8 * δ := by
  intro L L' t'
  have hA : wd N v (u * v) = wd N 1 u := by
    rw [hcomm, ← mul_one v]
    conv_lhs => rw [mul_one v]
    rw [← wd_left_mul N v 1 u, mul_one]
  have hL_le : L ≤ L' + wd N 1 u := by
    have htri := wd_triangle N 1 (u * v) v
    rw [wd_symm N (u * v) v, hA] at htri
    exact htri
  have hL'_le : L' ≤ L + wd N 1 u := by
    have htri := wd_triangle N 1 v (u * v)
    rw [hA] at htri
    exact htri
  have ht'_eq : (t' : ℤ) = (t : ℤ) + (L' : ℤ) - (L : ℤ) := by
    dsimp [t']
    omega
  have ht'_le_L' : t' ≤ L' := by omega
  have ht'_le_L : t' ≤ L := by omega
  have ht_le_L : t ≤ L := by omega
  obtain ⟨η, hη0, hηL', hηd⟩ := exists_geodesic N 1 (u * v)
  change η 0 = 1 at hη0
  change η L' = u * v at hηL'
  have hηd' : ∀ i j : ℕ, i ≤ L' → j ≤ L' → (wd N (η i) (η j) : ℤ) = |(i : ℤ) - (j : ℤ)| := hηd
  -- Step 1: thin triangle at apex `u * v` with sides `[u * v, u]` and `[u * v, 1]`
  have hduv_u : wd N (u * v) u = L := by
    rw [wd_symm N (u * v) u]
    have hlm := wd_left_mul N u 1 v
    rw [mul_one] at hlm
    exact hlm
  have hduv_ugt : wd N (u * v) (u * γ t) = L - t := by
    rw [wd_left_mul N u v (γ t), ← hγL]
    have h := hγd L t le_rfl ht_le_L
    rw [abs_of_nonneg (by omega : (0 : ℤ) ≤ (L : ℤ) - (t : ℤ))] at h
    change wd N (γ L) (γ t) = L - t
    omega
  have hugt_u : wd N (u * γ t) u = t := by
    rw [wd_symm N (u * γ t) u]
    have hlm := wd_left_mul N u 1 (γ t)
    rw [mul_one] at hlm
    rw [hlm, ← hγ0]
    have h := hγd 0 t (Nat.zero_le _) ht_le_L
    simp only [Nat.cast_zero, zero_sub, abs_neg, abs_of_nonneg (Int.natCast_nonneg t)] at h
    exact_mod_cast h
  have hduv_eta : wd N (u * v) (η t') = L' - t' := by
    rw [← hηL']
    have h := hηd' L' t' le_rfl ht'_le_L'
    rw [abs_of_nonneg (by omega : (0 : ℤ) ≤ (L' : ℤ) - (t' : ℤ))] at h
    omega
  have heta_1 : wd N (η t') 1 = t' := by
    rw [wd_symm N (η t') 1, ← hη0]
    have h := hηd' 0 t' (Nat.zero_le _) ht'_le_L'
    simp only [Nat.cast_zero, zero_sub, abs_neg, abs_of_nonneg (Int.natCast_nonneg t')] at h
    exact_mod_cast h
  have htri1 : wd N (u * γ t) (η t') ≤ 4 * δ := by
    refine thin_triangle hhyp (x := u * v) (y := u) (z := 1) (p := u * γ t) (q := η t') ?_ ?_ ?_ ?_
    · rw [hduv_ugt, hugt_u, hduv_u]; omega
    · rw [hduv_eta, heta_1, wd_symm N (u * v) 1]; change L' - t' + t' = L'; omega
    · rw [hduv_ugt, hduv_eta]; omega
    · rw [hduv_ugt, hduv_u, wd_symm N (u * v) 1, wd_symm N u 1]
      change 2 * (L - t) + wd N 1 u ≤ L + L'
      omega
  -- Step 2: thin triangle at apex `1` with sides `[1, u * v]` and `[1, v]`
  have h1_gt' : wd N 1 (γ t') = t' := by
    rw [← hγ0]
    have h := hγd 0 t' (Nat.zero_le _) ht'_le_L
    simp only [Nat.cast_zero, zero_sub, abs_neg, abs_of_nonneg (Int.natCast_nonneg t')] at h
    exact_mod_cast h
  have hgt'_v : wd N (γ t') v = L - t' := by
    rw [← hγL]
    have h := hγd t' L ht'_le_L le_rfl
    rw [abs_of_nonpos (by omega : (t' : ℤ) - (L : ℤ) ≤ 0)] at h
    change wd N (γ t') (γ L) = L - t'
    omega
  have htri2 : wd N (η t') (γ t') ≤ 4 * δ := by
    refine thin_triangle hhyp (x := 1) (y := u * v) (z := v) (p := η t') (q := γ t') ?_ ?_ ?_ ?_
    · rw [wd_symm N 1 (η t'), heta_1, wd_symm N (η t') (u * v), hduv_eta]
      change t' + (L' - t') = L'; omega
    · rw [h1_gt', hgt'_v]; change t' + (L - t') = L; omega
    · rw [wd_symm N 1 (η t'), heta_1, h1_gt']
    · rw [wd_symm N 1 (η t'), heta_1, wd_symm N (u * v) v, hA]
      change 2 * t' + wd N 1 u ≤ L' + L
      omega
  have hcomb := wd_triangle N (u * γ t) (η t') (γ t')
  omega

private lemma quasimorphism_abs_bound {n : ℕ} {C D : ℤ} {s : ℕ → ℤ}
    (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hsn : |s n| ≤ D)
    (hqm : ∀ a b : ℕ, a + b ≤ n → |s (a + b) - (s a + s b)| ≤ C) :
    ∀ k : ℕ, k ≤ n → |s k| ≤ 3 * C + 2 * D := by
  have hne : (Finset.range (n + 1)).Nonempty := ⟨0, Finset.mem_range.mpr (Nat.succ_pos n)⟩
  obtain ⟨k₀, hk₀mem, hk₀max⟩ := Finset.exists_max_image (Finset.range (n + 1)) (fun k => |s k|) hne
  have hk₀le : k₀ ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk₀mem)
  set S : ℤ := |s k₀|
  let k₁ : ℕ := min k₀ (n - k₀)
  have hk₁half : 2 * k₁ ≤ n := by dsimp [k₁]; omega
  have hk₁lb : S - C - D ≤ |s k₁| := by
    by_cases hle : k₀ ≤ n - k₀
    · have hk₁eq : k₁ = k₀ := min_eq_left hle
      rw [hk₁eq]
      dsimp [S]
      linarith
    · have hk₁eq : k₁ = n - k₀ := min_eq_right (le_of_not_ge hle)
      have hadd : k₀ + k₁ = n := by omega
      have hq := hqm k₀ k₁ (by omega)
      rw [hadd] at hq
      have htri : |s k₀| ≤ |s n - (s k₀ + s k₁)| + |s n| + |s k₁| := by
        have h1 : s k₀ = s n - (s n - (s k₀ + s k₁)) - s k₁ := by ring
        have h2 := abs_sub (s n - (s n - (s k₀ + s k₁))) (s k₁)
        have h3 := abs_sub (s n) (s n - (s k₀ + s k₁))
        rw [← h1] at h2
        linarith
      dsimp [S]
      linarith
  have h2k₁mem : 2 * k₁ ∈ Finset.range (n + 1) := Finset.mem_range.mpr (by omega)
  have h2k₁le : |s (2 * k₁)| ≤ S := hk₀max (2 * k₁) h2k₁mem
  have hdbl := hqm k₁ k₁ (by omega)
  have h2eq : k₁ + k₁ = 2 * k₁ := by omega
  rw [h2eq] at hdbl
  have h2lb : 2 * |s k₁| - C ≤ |s (2 * k₁)| := by
    have h1 : s k₁ + s k₁ = s (2 * k₁) - (s (2 * k₁) - (s k₁ + s k₁)) := by ring
    have h2 : |s k₁ + s k₁| ≤ |s (2 * k₁)| + |s (2 * k₁) - (s k₁ + s k₁)| := by
      conv_lhs => rw [h1]
      exact abs_sub _ _
    have h3 : |s k₁ + s k₁| = 2 * |s k₁| := by
      rw [← two_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℤ) < 2)]
    linarith
  have hS : S ≤ 3 * C + 2 * D := by linarith
  intro k hk
  exact (hk₀max k (Finset.mem_range.mpr (by omega))).trans hS

private lemma root_exponent_bound (N : Subgroup F2) [N.Normal] {δ : ℕ}
    (hhyp : ∀ x y z w : F2 ⧸ N,
      wd N x y + wd N z w ≤ max (wd N x z + wd N y w) (wd N x w + wd N y z) + 2 * δ)
    (htf : ∀ g : F2 ⧸ N, ∀ n : ℕ, n ≠ 0 → g ^ n = 1 → g = 1)
    {g : F2 ⧸ N} (hg : g ≠ 1) :
    ∀ (h : F2 ⧸ N) (n : ℕ), 1 ≤ n → h ^ n = g →
      n ≤ (80 * δ + 2 * wd N 1 g + 1) * 4 ^ (80 * δ + 2 * wd N 1 g) := by
  intro h n hn hpow
  have hhne : h ≠ 1 := by
    intro hh1
    rw [hh1, one_pow] at hpow
    exact hg hpow.symm
  let D : ℕ := wd N 1 g
  let Mh : ℕ := (Finset.range (n + 1)).sup (fun k => wd N 1 (h ^ k))
  have hMh_ge : ∀ k : ℕ, k ≤ n → wd N 1 (h ^ k) ≤ Mh := fun k hk =>
    Finset.le_sup (f := fun k => wd N 1 (h ^ k)) (Finset.mem_range.mpr (by omega))
  obtain ⟨K, hK⟩ := exists_pow_large_wd N htf hg (10 * Mh + 20)
  let L : ℕ := wd N 1 (g ^ K)
  have hL_ge : 10 * Mh + 20 ≤ L := hK
  obtain ⟨γ, hγ0, hγL, hγd⟩ := exists_geodesic N 1 (g ^ K)
  let t₀ : ℕ := L / 2
  let p : F2 ⧸ N := γ t₀
  let s : ℕ → ℤ := fun k => (wd N 1 (h ^ k * g ^ K) : ℤ) - (L : ℤ)
  have hcomm : ∀ k : ℕ, h ^ k * g ^ K = g ^ K * h ^ k := by
    intro k
    rw [← hpow, ← pow_mul, ← pow_add, ← pow_add, add_comm]
  have hs_bound : ∀ k : ℕ, k ≤ n → |s k| ≤ (Mh : ℤ) := by
    intro k hk
    have hA : wd N (g ^ K) (h ^ k * g ^ K) = wd N 1 (h ^ k) := by
      rw [hcomm k]
      have hlm := wd_left_mul N (g ^ K) 1 (h ^ k)
      rw [mul_one] at hlm
      exact hlm
    have h1 := wd_triangle N 1 (g ^ K) (h ^ k * g ^ K)
    have h2 := wd_triangle N 1 (h ^ k * g ^ K) (g ^ K)
    rw [hA] at h1
    rw [wd_symm N (h ^ k * g ^ K) (g ^ K), hA] at h2
    have hmk : wd N 1 (h ^ k) ≤ Mh := hMh_ge k hk
    dsimp [s, L] at *
    rw [abs_le]
    omega
  have hshift : ∀ k : ℕ, k ≤ n → ∀ t : ℕ, 3 * Mh ≤ t → t + 3 * Mh ≤ L →
      wd N (h ^ k * γ t) (γ ((t : ℤ) + s k).toNat) ≤ 8 * δ := by
    intro k hk t ht1 ht2
    have hmk : wd N 1 (h ^ k) ≤ Mh := hMh_ge k hk
    have hcs := comm_shift_on_geodesic hhyp (hcomm k) hγ0 hγL hγd (t := t) (by omega) (by omega)
    have hidx : ((t : ℤ) + (wd N 1 (h ^ k * g ^ K) : ℤ) - (wd N 1 (g ^ K) : ℤ)).toNat =
        ((t : ℤ) + s k).toNat := by
      dsimp only [s, L]
      ring_nf
    rw [← hidx]
    exact hcs
  have hsn : |s n| ≤ (D : ℤ) := by
    have hA : wd N (g ^ K) (h ^ n * g ^ K) = D := by
      rw [hcomm n, hpow]
      have hlm := wd_left_mul N (g ^ K) 1 g
      rw [mul_one] at hlm
      exact hlm
    have h1 := wd_triangle N 1 (g ^ K) (h ^ n * g ^ K)
    have h2 := wd_triangle N 1 (h ^ n * g ^ K) (g ^ K)
    rw [hA] at h1
    rw [wd_symm N (h ^ n * g ^ K) (g ^ K), hA] at h2
    dsimp [s, L] at *
    rw [abs_le]
    omega
  have hqm : ∀ a b : ℕ, a + b ≤ n → |s (a + b) - (s a + s b)| ≤ (24 * δ : ℤ) := by
    intro a b hab
    have ha : a ≤ n := by omega
    have hb : b ≤ n := by omega
    have hsb := hs_bound b hb
    have hsa := hs_bound a ha
    have hsab := hs_bound (a + b) hab
    have ht₀1 : 3 * Mh ≤ t₀ := by dsimp [t₀]; omega
    have ht₀2 : t₀ + 3 * Mh ≤ L := by dsimp [t₀]; omega
    let tb : ℕ := ((t₀ : ℤ) + s b).toNat
    have htb_eq : (tb : ℤ) = (t₀ : ℤ) + s b := by
      dsimp [tb, t₀]
      have := (abs_le.mp hsb).1
      omega
    have htb1 : 3 * Mh ≤ tb := by
      have := (abs_le.mp hsb).1
      dsimp [t₀] at htb_eq
      omega
    have htb2 : tb + 3 * Mh ≤ L := by
      have := (abs_le.mp hsb).2
      dsimp [t₀] at htb_eq
      omega
    let tab : ℕ := ((t₀ : ℤ) + s (a + b)).toNat
    let tz : ℕ := ((tb : ℤ) + s a).toNat
    have htab_eq : (tab : ℤ) = (t₀ : ℤ) + s (a + b) := by
      dsimp [tab, t₀]
      have := (abs_le.mp hsab).1
      omega
    have htz_eq : (tz : ℤ) = (t₀ : ℤ) + s b + s a := by
      have := (abs_le.mp hsa).1
      have := (abs_le.mp hsb).1
      dsimp [tz]
      omega
    have htab_le : tab ≤ L := by
      have := (abs_le.mp hsab).2
      dsimp [t₀] at htab_eq
      omega
    have htz_le : tz ≤ L := by
      have := (abs_le.mp hsa).2
      have := (abs_le.mp hsb).2
      dsimp [t₀] at htz_eq
      omega
    have h1 : wd N (h ^ b * p) (γ tb) ≤ 8 * δ := hshift b hb t₀ ht₀1 ht₀2
    have h1' : wd N (h ^ (a + b) * p) (h ^ a * γ tb) ≤ 8 * δ := by
      rw [pow_add, mul_assoc, wd_left_mul]
      exact h1
    have h2 : wd N (h ^ a * γ tb) (γ tz) ≤ 8 * δ := hshift a ha tb htb1 htb2
    have h3 : wd N (h ^ (a + b) * p) (γ tab) ≤ 8 * δ := hshift (a + b) hab t₀ ht₀1 ht₀2
    have htri1 := wd_triangle N (γ tab) (h ^ (a + b) * p) (h ^ a * γ tb)
    have htri2 := wd_triangle N (γ tab) (h ^ a * γ tb) (γ tz)
    rw [wd_symm N (γ tab) (h ^ (a + b) * p)] at htri1
    have hdist_le : wd N (γ tab) (γ tz) ≤ 24 * δ := by omega
    have hdist_eq := hγd tab tz htab_le htz_le
    have hdiff : (tab : ℤ) - (tz : ℤ) = s (a + b) - (s a + s b) := by linarith
    rw [hdiff] at hdist_eq
    omega
  have hs_unif := quasimorphism_abs_bound (C := (24 * δ : ℤ)) (D := (D : ℤ))
    (by positivity) (by positivity) hsn hqm
  let R : ℕ := 80 * δ + 2 * D
  obtain ⟨B, hBmem, hBcard⟩ := ball_card_le N R
  let f : Fin (n + 1) → F2 ⧸ N := fun k => p⁻¹ * (h ^ k.val * p)
  have hmaps : Set.MapsTo f (Finset.univ : Finset (Fin (n + 1))) (B : Set (F2 ⧸ N)) := by
    intro k _
    have hk : k.val ≤ n := Nat.lt_succ_iff.mp k.isLt
    have hsk := hs_unif k.val hk
    have hsk_m := hs_bound k.val hk
    have ht₀1 : 3 * Mh ≤ t₀ := by dsimp [t₀]; omega
    have ht₀2 : t₀ + 3 * Mh ≤ L := by dsimp [t₀]; omega
    let tk : ℕ := ((t₀ : ℤ) + s k.val).toNat
    have htk_eq : (tk : ℤ) = (t₀ : ℤ) + s k.val := by
      dsimp [tk, t₀]
      have := (abs_le.mp hsk_m).1
      omega
    have htk_le : tk ≤ L := by
      have := (abs_le.mp hsk_m).2
      dsimp [t₀] at htk_eq
      omega
    have ht₀_le : t₀ ≤ L := by dsimp [t₀]; omega
    have hsh : wd N (h ^ k.val * p) (γ tk) ≤ 8 * δ := hshift k.val hk t₀ ht₀1 ht₀2
    have hpg := hγd t₀ tk ht₀_le htk_le
    have hpdiff : (t₀ : ℤ) - (tk : ℤ) = -s k.val := by linarith
    rw [hpdiff, abs_neg] at hpg
    have htri := wd_triangle N p (γ tk) (h ^ k.val * p)
    rw [wd_symm N (γ tk) (h ^ k.val * p)] at htri
    have hconj : wd N 1 (f k) = wd N p (h ^ k.val * p) := by
      dsimp [f]
      rw [← wd_left_mul N p 1 (p⁻¹ * (h ^ k.val * p)), mul_one, mul_inv_cancel_left]
    apply hBmem (f k)
    rw [hconj]
    have : (wd N p (γ tk) : ℤ) ≤ 72 * δ + 2 * (D : ℤ) := by
      rw [hpg]
      have h1 : 3 * (24 * (δ : ℤ)) + 2 * (D : ℤ) = 72 * (δ : ℤ) + 2 * (D : ℤ) := by ring
      linarith
    have hptk : wd N p (γ tk) ≤ 72 * δ + 2 * D := by exact_mod_cast this
    dsimp [R]
    omega
  have hinj : Set.InjOn f (Finset.univ : Finset (Fin (n + 1))) := by
    intro a _ b _ hfab
    have heq : h ^ a.val = h ^ b.val := by
      dsimp [f] at hfab
      have h1 : h ^ a.val * p = h ^ b.val * p := mul_left_cancel hfab
      exact mul_right_cancel h1
    by_contra hne
    have hpow' : ∀ i j : ℕ, i < j → h ^ i = h ^ j → False := by
      intro i j hij hijeq
      have h1 : h ^ (j - i) = 1 := by
        have hsplit : h ^ i * h ^ (j - i) = h ^ i * 1 := by
          rw [← pow_add, Nat.add_sub_cancel' hij.le, mul_one, hijeq]
        exact mul_left_cancel hsplit
      exact hhne (htf h (j - i) (by omega) h1)
    rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hne) with hlt | hgt
    · exact hpow' a.val b.val hlt heq
    · exact hpow' b.val a.val hgt heq.symm
  have hcard_le : n + 1 ≤ B.card := by
    have h := Finset.card_le_card_of_injOn f hmaps hinj
    simpa using h
  dsimp only [R, D] at hBcard
  omega

end Kourovka88R1H1

theorem OMA.solution : OMA.R_Kourovka_8_8_kourovka_8_8a_R1.H1 := by
  intro N _ hhypEx htf g hg
  obtain ⟨δ, hhyp⟩ := hhypEx
  let M : ℕ := (80 * δ + 2 * Kourovka88R1H1.wd N 1 g + 1) *
    4 ^ (80 * δ + 2 * Kourovka88R1H1.wd N 1 g)
  have hbound : ∀ (h : Kourovka88R1H1.F2 ⧸ N) (n : ℕ), 1 ≤ n → h ^ n = g → n ≤ M :=
    Kourovka88R1H1.root_exponent_bound N hhyp htf hg
  let S : Set ℕ := {n : ℕ | 1 ≤ n ∧ ∃ h : Kourovka88R1H1.F2 ⧸ N, h ^ n = g}
  have hne : S.Nonempty := ⟨1, le_rfl, g, pow_one g⟩
  have hbdd : BddAbove S := ⟨M, fun n ⟨hn, h, hpow⟩ => hbound h n hn hpow⟩
  let r : ℕ := sSup S
  have hrmem : r ∈ S := Nat.sSup_mem hne hbdd
  obtain ⟨hr1, c, hcr⟩ := hrmem
  have hcne : c ≠ 1 := by
    intro hc1
    rw [hc1, one_pow] at hcr
    exact hg hcr.symm
  refine ⟨c, (r : ℤ), ?_, ?_⟩
  · intro h m hm
    by_cases hm0 : m = 0
    · subst hm0
      simp only [zpow_zero] at hm
      exact (hcne hm.symm).elim
    · have hmnat : 1 ≤ m.natAbs := Int.natAbs_pos.mpr hm0
      have hpow_abs : (if 0 ≤ m then h else h⁻¹) ^ (m.natAbs * r) = g := by
        rw [pow_mul]
        have hstep : (if 0 ≤ m then h else h⁻¹) ^ m.natAbs = c := by
          split_ifs with hpos
          · have hm_eq : ((m.natAbs : ℕ) : ℤ) = m := Int.natAbs_of_nonneg hpos
            rw [← zpow_natCast, hm_eq]
            exact hm
          · have hneg : m < 0 := lt_of_not_ge hpos
            have hm_eq : -((m.natAbs : ℕ) : ℤ) = m := by omega
            rw [inv_pow, ← zpow_natCast, ← zpow_neg, hm_eq]
            exact hm
        rw [hstep, hcr]
      have hle : m.natAbs * r ≤ r :=
        le_csSup hbdd ⟨Nat.mul_pos hmnat hr1, if 0 ≤ m then h else h⁻¹, hpow_abs⟩
      have hm1 : m.natAbs = 1 := by nlinarith
      omega
  · rw [zpow_natCast, hcr]
