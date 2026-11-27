import FormalConjectures.ErdosProblems.«272»

-- Problem: Erdős Problem 272 — isBigO sq
-- Upstream: formal-conjectures FormalConjectures/ErdosProblems/272.lean:61 (declaration Erdos272.erdos_272.variants.isBigO_sq)
-- Credit: @DomTheDeveloper (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

/-!
Original proof (written for this submission): every admissible family has at most `20 N²` members.

Fix a member `K` of minimum size `k`.  Every other member `S` with at least two elements meets `K`
in some `z`; let `u` be an element of `S` nearest to `z`, `D = |u - z|`, and let `P` be the part of
`S` reachable from `z` inside the residue class of `z` mod `D` without leaving `S`.

* Uniqueness: if `v ∈ S \ P`, no other member contains `z, u, v`.  Indeed the intersection would be
  an arithmetic progression through `z, u, v`; as no point of `S` lies strictly between `z` and
  `u`, its difference is `D`, and then every class point between `z` and `v` lies in `S`, so `v ∈ P`.
* `S = P` (runs): `S` is a full segment of a class mod `D`.  Runs with the same `D` meet, so they
  share the class, and a run is determined by `D` and its two end points: at most
  `∑_D (N / D + 1)² ≤ 8 N²` of them.
* `|S| ≤ 4 |S \ P|`: the triples `(z, u, v)`, `v ∈ S \ P`, are distinct for distinct `S`, lie in
  `K × [N] × [N]`, and each `S` has at least `k / 4` of them: at most `4 N²` such `S`.
* `|S| > 4 |S \ P|`: then `P` has more than `3k/4` points of one class mod `D`, so `k D ≤ 2N`, and
  `S ↦ (z, u, v_S)` is injective with at most `k (4N/k + 1) N ≤ 5 N²` values.
Together with `K` and the at most `N + 1` members with at most one element this gives `20 N²`.
-/

/-- `X` is a nonempty arithmetic progression, phrased without extended naturals:
`X = {a + n * d : n ∈ I}` for a downward closed index set `I ∋ 0`. -/
def OMA.APSet (X : Finset ℕ) : Prop :=
  ∃ a d : ℕ, ∃ I : ℕ → Prop, (∀ n m, I n → m ≤ n → I m) ∧ I 0 ∧
    ∀ x, x ∈ X ↔ ∃ n, I n ∧ x = a + n * d

theorem OMA.apSet_of_isAP (X : Finset ℕ) (l : ℕ∞) (hl : 0 < l)
    (h : (SetLike.coe X).IsAPOfLength l) : OMA.APSet X := by
  obtain ⟨a, d, -, hX⟩ := h
  refine ⟨a, d, fun n => (n : ℕ∞) < l, ?_, ?_, ?_⟩
  · intro n m hn hmn
    have hn' : (n : ℕ∞) < l := hn
    show (m : ℕ∞) < l
    exact lt_of_le_of_lt (by exact_mod_cast hmn) hn'
  · show ((0 : ℕ) : ℕ∞) < l
    exact_mod_cast hl
  · intro x
    have hx : x ∈ X ↔ x ∈ (SetLike.coe X : Set ℕ) := Iff.rfl
    rw [hx, hX]
    constructor
    · rintro ⟨n, hn, rfl⟩
      exact ⟨n, hn, by rw [smul_eq_mul]⟩
    · rintro ⟨n, hn, rfl⟩
      exact ⟨n, hn, by rw [smul_eq_mul]⟩

/-- If `z ≠ u` lie in a progression and no progression point is strictly between them, then
the common difference is `|u - z|`. -/
theorem OMA.ap_gap (a d : ℕ) (I : ℕ → Prop) (hI : ∀ n m, I n → m ≤ n → I m) (z u : ℕ)
    (hz : ∃ n, I n ∧ z = a + n * d) (hu : ∃ n, I n ∧ u = a + n * d) (hzu : z ≠ u)
    (hadj : ∀ n, I n → ¬ (min z u < a + n * d ∧ a + n * d < max z u)) :
    0 < d ∧ max z u - min z u = d := by
  obtain ⟨i, hIi, hzi⟩ := hz
  obtain ⟨j, hIj, huj⟩ := hu
  have hd : 0 < d := by
    rcases Nat.eq_zero_or_pos d with h0 | h0
    · exfalso
      apply hzu
      simp [hzi, huj, h0]
    · exact h0
  refine ⟨hd, ?_⟩
  rcases lt_trichotomy i j with hij | hij | hij
  · obtain ⟨t, ht⟩ := Nat.exists_eq_add_of_lt hij
    have hu' : u = z + t * d + d := by rw [hzi, huj, ht]; ring
    rcases Nat.eq_zero_or_pos t with ht0 | ht0
    · rw [ht0, Nat.zero_mul] at hu'
      omega
    · exfalso
      have hw : a + (i + 1) * d = z + d := by rw [hzi]; ring
      have htd : d ≤ t * d := Nat.le_mul_of_pos_left d ht0
      refine hadj (i + 1) (hI j (i + 1) hIj (by omega)) ⟨?_, ?_⟩
      · rw [hw]; omega
      · rw [hw]; omega
  · exfalso
    apply hzu
    rw [hzi, huj, hij]
  · obtain ⟨t, ht⟩ := Nat.exists_eq_add_of_lt hij
    have hz' : z = u + t * d + d := by rw [hzi, huj, ht]; ring
    rcases Nat.eq_zero_or_pos t with ht0 | ht0
    · rw [ht0, Nat.zero_mul] at hz'
      omega
    · exfalso
      have hw : a + (j + 1) * d = u + d := by rw [huj]; ring
      have htd : d ≤ t * d := Nat.le_mul_of_pos_left d ht0
      refine hadj (j + 1) (hI i (j + 1) hIi (by omega)) ⟨?_, ?_⟩
      · rw [hw]; omega
      · rw [hw]; omega

/-- Class points between two points of a progression belong to the progression. -/
theorem OMA.ap_fill (a d : ℕ) (hd : 0 < d) (I : ℕ → Prop) (hI : ∀ n m, I n → m ≤ n → I m)
    (z v y : ℕ) (hz : ∃ n, I n ∧ z = a + n * d) (hv : ∃ n, I n ∧ v = a + n * d)
    (hy1 : min z v ≤ y) (hy2 : y ≤ max z v) (hmod : y % d = z % d) :
    ∃ n, I n ∧ y = a + n * d := by
  obtain ⟨i, hIi, hzi⟩ := hz
  obtain ⟨h, hIh, hvh⟩ := hv
  have hza : a ≤ z := by rw [hzi]; exact Nat.le_add_right _ _
  have hva : a ≤ v := by rw [hvh]; exact Nat.le_add_right _ _
  have hay : a ≤ y := by omega
  have hmod' : a % d = y % d := by rw [hmod, hzi, Nat.add_mul_mod_self_right]
  obtain ⟨n, hn⟩ := (Nat.modEq_iff_dvd' hay).mp hmod'
  have hyn : y = a + n * d := by rw [Nat.mul_comm n d]; omega
  refine ⟨n, ?_, hyn⟩
  rcases le_total i h with hih | hih
  · have hzv : z ≤ v := by
      rw [hzi, hvh]; exact Nat.add_le_add_left (Nat.mul_le_mul_right d hih) a
    have hnd : n * d ≤ h * d := by omega
    exact hI h n hIh (Nat.le_of_mul_le_mul_right hnd hd)
  · have hvz : v ≤ z := by
      rw [hzi, hvh]; exact Nat.add_le_add_left (Nat.mul_le_mul_right d hih) a
    have hnd : n * d ≤ i * d := by omega
    exact hI i n hIi (Nat.le_of_mul_le_mul_right hnd hd)

/-- The part of `S` reachable from `z` inside the residue class of `z` mod `d`. -/
def OMA.runPart (S : Finset ℕ) (z d : ℕ) : Finset ℕ :=
  S.filter (fun x => x % d = z % d ∧
    ∀ y ∈ Finset.Icc (min z x) (max z x), y % d = z % d → y ∈ S)

theorem OMA.mem_runPart (S : Finset ℕ) (z d x : ℕ) :
    x ∈ OMA.runPart S z d ↔ x ∈ S ∧ x % d = z % d ∧
      ∀ y, min z x ≤ y → y ≤ max z x → y % d = z % d → y ∈ S := by
  unfold OMA.runPart
  rw [Finset.mem_filter]
  constructor
  · rintro ⟨h1, h2, h3⟩
    exact ⟨h1, h2, fun y hy1 hy2 hy3 => h3 y (Finset.mem_Icc.mpr ⟨hy1, hy2⟩) hy3⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨h1, h2, fun y hy hy3 => h3 y (Finset.mem_Icc.mp hy).1 (Finset.mem_Icc.mp hy).2 hy3⟩

/-- Uniqueness of the triple `(z, u, v)`. -/
theorem OMA.triple_unique (S T : Finset ℕ) (hAP : OMA.APSet (S ∩ T)) (z u v : ℕ)
    (hzu : z ≠ u) (hadj : ∀ w ∈ S, ¬ (min z u < w ∧ w < max z u))
    (hvS : v ∈ S) (hvR : v ∉ OMA.runPart S z (max z u - min z u))
    (hz : z ∈ S ∩ T) (hu : u ∈ S ∩ T) (hv : v ∈ S ∩ T) : False := by
  obtain ⟨a, d, I, hI, -, hX⟩ := hAP
  have hz' := (hX z).mp hz
  have hu' := (hX u).mp hu
  have hv' := (hX v).mp hv
  obtain ⟨hd, hgap⟩ := OMA.ap_gap a d I hI z u hz' hu' hzu (fun n hn hbtw =>
    hadj (a + n * d) (Finset.mem_of_mem_inter_left ((hX _).mpr ⟨n, hn, rfl⟩)) hbtw)
  rw [hgap] at hvR
  apply hvR
  rw [OMA.mem_runPart]
  refine ⟨hvS, ?_, ?_⟩
  · obtain ⟨i, -, hzi⟩ := hz'
    obtain ⟨h, -, hvh⟩ := hv'
    rw [hzi, hvh, Nat.add_mul_mod_self_right, Nat.add_mul_mod_self_right]
  · intro y hy1 hy2 hy3
    exact Finset.mem_of_mem_inter_left
      ((hX y).mpr (OMA.ap_fill a d hd I hI z v y hz' hv' hy1 hy2 hy3))

/-- An element of `S` nearest to `z`. -/
theorem OMA.exists_adjacent (S : Finset ℕ) (z : ℕ) (hz : z ∈ S) (h2 : 2 ≤ S.card) :
    ∃ u, u ∈ S ∧ z ≠ u ∧ ∀ w ∈ S, ¬ (min z u < w ∧ w < max z u) := by
  have hne : (S.erase z).Nonempty := by
    rw [← Finset.card_pos, Finset.card_erase_of_mem hz]
    omega
  obtain ⟨u, hu, hmin⟩ := Finset.exists_min_image (S.erase z) (fun x => max z x - min z x) hne
  obtain ⟨huz, huS⟩ := Finset.mem_erase.mp hu
  refine ⟨u, huS, fun h => huz h.symm, ?_⟩
  intro w hw hbtw
  have hwz : w ≠ z := by
    intro h
    rw [h] at hbtw
    omega
  have h3 : max z u - min z u ≤ max z w - min z w := hmin w (Finset.mem_erase.mpr ⟨hwz, hw⟩)
  omega

/-- `∑_{d ≤ D+1} ⌊N/d⌋² ≤ (2 - 1/(D+1)) N²`, cleared of denominators. -/
theorem OMA.sum_sq_bound (N : ℕ) : ∀ D : ℕ,
    (D + 1) * (∑ d ∈ Finset.range (D + 1), (N / (d + 1)) ^ 2) + N ^ 2
      ≤ 2 * (D + 1) * N ^ 2 := by
  intro D
  induction D with
  | zero =>
    have h : (∑ d ∈ Finset.range (0 + 1), (N / (d + 1)) ^ 2) = N ^ 2 := by simp
    rw [h]
    omega
  | succ D ih =>
    rw [Finset.sum_range_succ]
    have hq : (D + 1 + 1) * (N / (D + 1 + 1)) ≤ N := Nat.mul_div_le N (D + 1 + 1)
    generalize (∑ d ∈ Finset.range (D + 1), (N / (d + 1)) ^ 2) = F at ih ⊢
    generalize N / (D + 1 + 1) = q at hq ⊢
    have h2 : ((D + 1 + 1) * q) ^ 2 ≤ N ^ 2 := Nat.pow_le_pow_left hq 2
    have key : (D + 1) * ((D + 1 + 1) * (F + q ^ 2) + N ^ 2)
        ≤ (D + 1) * (2 * (D + 1 + 1) * N ^ 2) := by
      nlinarith [Nat.mul_le_mul_left (D + 1 + 1) ih, h2, Nat.zero_le ((D + 1 + 1) * q ^ 2)]
    exact Nat.le_of_mul_le_mul_left key (Nat.succ_pos D)

theorem OMA.sum_bound8 (N : ℕ) :
    ∑ e ∈ Finset.range N, (N / (e + 1) + 1) ^ 2 ≤ 8 * N ^ 2 := by
  rcases Nat.eq_zero_or_pos N with h0 | hpos
  · subst h0
    simp
  · obtain ⟨D, rfl⟩ : ∃ D, N = D + 1 := ⟨N - 1, by omega⟩
    have h1 := OMA.sum_sq_bound (D + 1) D
    have h2 : ∑ e ∈ Finset.range (D + 1), ((D + 1) / (e + 1) + 1) ^ 2
        ≤ ∑ e ∈ Finset.range (D + 1), 4 * ((D + 1) / (e + 1)) ^ 2 := by
      apply Finset.sum_le_sum
      intro e he
      have he' : e + 1 ≤ D + 1 := by
        have := Finset.mem_range.mp he
        omega
      have hq : 1 ≤ (D + 1) / (e + 1) := (Nat.one_le_div_iff (Nat.succ_pos e)).mpr he'
      generalize (D + 1) / (e + 1) = q at hq ⊢
      nlinarith [Nat.mul_le_mul_right q hq]
    rw [← Finset.mul_sum] at h2
    have h3 : (D + 1) * (∑ e ∈ Finset.range (D + 1), ((D + 1) / (e + 1)) ^ 2)
        ≤ (D + 1) * (2 * (D + 1) ^ 2) := by
      nlinarith [h1]
    have h4 := Nat.le_of_mul_le_mul_left h3 (Nat.succ_pos D)
    omega

/-- A set of points `≤ N` in one residue class mod `d` has at most `N / d + 1` elements. -/
theorem OMA.card_class_le (N d r : ℕ) (P : Finset ℕ) (hP : ∀ x ∈ P, x ≤ N ∧ x % d = r) :
    P.card ≤ N / d + 1 := by
  have h := Finset.card_le_card_of_injOn (fun x => x / d)
    (s := P) (t := Finset.range (N / d + 1))
    (fun x hx => Finset.mem_coe.mpr (Finset.mem_range.mpr
      (Nat.lt_succ_of_le (Nat.div_le_div_right (hP x (Finset.mem_coe.mp hx)).1))))
    (fun x hx y hy hxy => by
      have h1 := Nat.div_add_mod x d
      have h2 := Nat.div_add_mod y d
      have hxy' : x / d = y / d := hxy
      rw [(hP x (Finset.mem_coe.mp hx)).2, hxy'] at h1
      rw [(hP y (Finset.mem_coe.mp hy)).2] at h2
      omega)
  rwa [Finset.card_range] at h

/-- Counting the members that are full segments of a residue class. -/
theorem OMA.card_runs (N : ℕ) (F : Finset (Finset ℕ)) (d : Finset ℕ → ℕ)
    (hsub : ∀ S ∈ F, S ⊆ Finset.Icc 1 N) (hne : ∀ S ∈ F, S.Nonempty)
    (hd : ∀ S ∈ F, 1 ≤ d S ∧ d S ≤ N)
    (hcong : ∀ S ∈ F, ∀ x ∈ S, ∀ x' ∈ S, x % d S = x' % d S)
    (hconv : ∀ S ∈ F, ∀ x ∈ S, ∀ x' ∈ S, ∀ y, x ≤ y → y ≤ x' → y % d S = x % d S → y ∈ S)
    (hint : ∀ S ∈ F, ∀ T ∈ F, S ≠ T → ∃ x, x ∈ S ∧ x ∈ T) :
    F.card ≤ ∑ e ∈ Finset.range N, (N / (e + 1) + 1) ^ 2 := by
  have hlohi : ∀ S : Finset ℕ, ∃ lo hi : ℕ, S ∈ F →
      lo ∈ S ∧ hi ∈ S ∧ ∀ x ∈ S, lo ≤ x ∧ x ≤ hi := by
    intro S
    by_cases hS : S ∈ F
    · have hSne := hne S hS
      exact ⟨S.min' hSne, S.max' hSne, fun _ => ⟨S.min'_mem hSne, S.max'_mem hSne,
        fun x hx => ⟨S.min'_le x hx, S.le_max' x hx⟩⟩⟩
    · exact ⟨0, 0, fun h => absurd h hS⟩
  choose lo hi hlh using hlohi
  have hsubset : ∀ S ∈ F, ∀ T ∈ F, d S = d T → lo S = lo T → hi S = hi T → S ⊆ T := by
    intro S hS T hT hdd hll hhh x hx
    obtain ⟨hloS, -, hbS⟩ := hlh S hS
    obtain ⟨hloT, hhiT, -⟩ := hlh T hT
    refine hconv T hT (lo T) hloT (hi T) hhiT x ?_ ?_ ?_
    · rw [← hll]; exact (hbS x hx).1
    · rw [← hhh]; exact (hbS x hx).2
    · rw [← hdd, ← hll]; exact hcong S hS x hx (lo S) hloS
  have hmaps : ∀ S ∈ F, (d S - 1, lo S / d S, hi S / d S) ∈
      (Finset.range N).biUnion (fun e => ({e} : Finset ℕ) ×ˢ
        (Finset.range (N / (e + 1) + 1) ×ˢ Finset.range (N / (e + 1) + 1))) := by
    intro S hS
    obtain ⟨hd1, hd2⟩ := hd S hS
    obtain ⟨hlo, hhi, -⟩ := hlh S hS
    have hloN := (Finset.mem_Icc.mp (hsub S hS hlo)).2
    have hhiN := (Finset.mem_Icc.mp (hsub S hS hhi)).2
    have e1 : d S - 1 + 1 = d S := by omega
    refine Finset.mem_biUnion.mpr ⟨d S - 1, Finset.mem_range.mpr (by omega), ?_⟩
    refine Finset.mem_product.mpr ⟨Finset.mem_singleton_self _, Finset.mem_product.mpr ⟨?_, ?_⟩⟩
    · refine Finset.mem_range.mpr ?_
      show lo S / d S < N / (d S - 1 + 1) + 1
      rw [e1]
      exact Nat.lt_succ_of_le (Nat.div_le_div_right hloN)
    · refine Finset.mem_range.mpr ?_
      show hi S / d S < N / (d S - 1 + 1) + 1
      rw [e1]
      exact Nat.lt_succ_of_le (Nat.div_le_div_right hhiN)
  have hinj : Set.InjOn (fun S => (d S - 1, lo S / d S, hi S / d S)) (F : Set (Finset ℕ)) := by
    intro S hS T hT hcode
    have hS' : S ∈ F := Finset.mem_coe.mp hS
    have hT' : T ∈ F := Finset.mem_coe.mp hT
    by_contra hne'
    have h1 : d S - 1 = d T - 1 := congrArg Prod.fst hcode
    have h2 : lo S / d S = lo T / d T := congrArg (fun p => p.2.1) hcode
    have h3 : hi S / d S = hi T / d T := congrArg (fun p => p.2.2) hcode
    have hdd : d S = d T := by
      have a1 := (hd S hS').1
      have a2 := (hd T hT').1
      omega
    obtain ⟨x, hxS, hxT⟩ := hint S hS' T hT' hne'
    obtain ⟨hloS, hhiS, -⟩ := hlh S hS'
    obtain ⟨hloT, hhiT, -⟩ := hlh T hT'
    have m1 : lo S % d S = lo T % d S := by
      rw [hcong S hS' (lo S) hloS x hxS, hdd, hcong T hT' x hxT (lo T) hloT]
    have m2 : hi S % d S = hi T % d S := by
      rw [hcong S hS' (hi S) hhiS x hxS, hdd, hcong T hT' x hxT (hi T) hhiT]
    rw [← hdd] at h2 h3
    have hll : lo S = lo T := by
      have e1 := Nat.div_add_mod (lo S) (d S)
      have e2 := Nat.div_add_mod (lo T) (d S)
      rw [h2, m1] at e1
      omega
    have hhh : hi S = hi T := by
      have e1 := Nat.div_add_mod (hi S) (d S)
      have e2 := Nat.div_add_mod (hi T) (d S)
      rw [h3, m2] at e1
      omega
    exact hne' (Finset.Subset.antisymm (hsubset S hS' T hT' hdd hll hhh)
      (hsubset T hT' S hS' hdd.symm hll.symm hhh.symm))
  calc F.card ≤ ((Finset.range N).biUnion (fun e => ({e} : Finset ℕ) ×ˢ
          (Finset.range (N / (e + 1) + 1) ×ˢ Finset.range (N / (e + 1) + 1)))).card :=
        Finset.card_le_card_of_injOn (fun S => (d S - 1, lo S / d S, hi S / d S))
          (fun S hS => Finset.mem_coe.mpr (hmaps S (Finset.mem_coe.mp hS))) hinj
    _ ≤ ∑ e ∈ Finset.range N, (({e} : Finset ℕ) ×ˢ
          (Finset.range (N / (e + 1) + 1) ×ˢ Finset.range (N / (e + 1) + 1))).card :=
        Finset.card_biUnion_le
    _ = ∑ e ∈ Finset.range N, (N / (e + 1) + 1) ^ 2 := by
        refine Finset.sum_congr rfl fun e _ => ?_
        rw [Finset.card_product, Finset.card_product, Finset.card_singleton, Finset.card_range,
          one_mul, sq]

/-- Double counting of the triples `(z S, u S, v)`, `v ∈ R S`. -/
theorem OMA.card_caseI (N : ℕ) (K : Finset ℕ) (F : Finset (Finset ℕ)) (z u : Finset ℕ → ℕ)
    (R : Finset ℕ → Finset ℕ)
    (hz : ∀ S ∈ F, z S ∈ K) (hu : ∀ S ∈ F, u S ∈ Finset.Icc 1 N)
    (hR : ∀ S ∈ F, R S ⊆ Finset.Icc 1 N)
    (huniq : ∀ S ∈ F, ∀ T ∈ F, S ≠ T → z S = z T → u S = u T → ∀ v ∈ R S, v ∉ R T)
    (hbig : ∀ S ∈ F, K.card ≤ 4 * (R S).card) :
    F.card ≤ 4 * (N * N) := by
  rcases Finset.eq_empty_or_nonempty F with hF | ⟨S0, hS0⟩
  · rw [hF]
    simp
  have hk : 0 < K.card := Finset.card_pos.mpr ⟨z S0, hz S0 hS0⟩
  have hdisj : ∀ S ∈ F, ∀ T ∈ F, S ≠ T →
      Disjoint ((R S).image (fun v => (z S, u S, v))) ((R T).image (fun v => (z T, u T, v))) := by
    intro S hS T hT hST
    rw [Finset.disjoint_left]
    intro t ht ht'
    obtain ⟨v, hv, hvt⟩ := Finset.mem_image.mp ht
    obtain ⟨v', hv', hvt'⟩ := Finset.mem_image.mp ht'
    have he : (z T, u T, v') = (z S, u S, v) := hvt'.trans hvt.symm
    have h1 : z T = z S := congrArg Prod.fst he
    have h2 : u T = u S := congrArg (fun p => p.2.1) he
    have h3 : v' = v := congrArg (fun p => p.2.2) he
    rw [h3] at hv'
    exact huniq S hS T hT hST h1.symm h2.symm v hv hv'
  have hcard : (F.biUnion (fun S => (R S).image (fun v => (z S, u S, v)))).card
      = ∑ S ∈ F, (R S).card := by
    rw [Finset.card_biUnion (fun S hS T hT hST =>
      hdisj S (Finset.mem_coe.mp hS) T (Finset.mem_coe.mp hT) hST)]
    refine Finset.sum_congr rfl fun S _ => ?_
    exact Finset.card_image_of_injective _ (fun v v' h => congrArg (fun p => p.2.2) h)
  have hsubset : F.biUnion (fun S => (R S).image (fun v => (z S, u S, v)))
      ⊆ K ×ˢ (Finset.Icc 1 N ×ˢ Finset.Icc 1 N) := by
    intro t ht
    obtain ⟨S, hS, htS⟩ := Finset.mem_biUnion.mp ht
    obtain ⟨v, hv, hvt⟩ := Finset.mem_image.mp htS
    rw [← hvt]
    exact Finset.mem_product.mpr ⟨hz S hS, Finset.mem_product.mpr ⟨hu S hS, hR S hS hv⟩⟩
  have h1 : ∑ S ∈ F, (R S).card ≤ K.card * (N * N) := by
    rw [← hcard]
    refine le_trans (Finset.card_le_card hsubset) (le_of_eq ?_)
    rw [Finset.card_product, Finset.card_product, Nat.card_Icc]
    simp
  have h2 := Finset.card_nsmul_le_sum F (fun S => 4 * (R S).card) K.card hbig
  rw [smul_eq_mul, ← Finset.mul_sum] at h2
  have h3 : F.card * K.card ≤ 4 * (N * N) * K.card := by
    calc F.card * K.card ≤ 4 * ∑ S ∈ F, (R S).card := h2
      _ ≤ 4 * (K.card * (N * N)) := Nat.mul_le_mul_left 4 h1
      _ = 4 * (N * N) * K.card := by ring
  exact Nat.le_of_mul_le_mul_right h3 hk

/-- An injection into triples `(z, u, v)` with `u` close to `z`. -/
theorem OMA.card_caseII (N q : ℕ) (K : Finset ℕ) (F : Finset (Finset ℕ))
    (z u v : Finset ℕ → ℕ)
    (hz : ∀ S ∈ F, z S ∈ K)
    (hu : ∀ S ∈ F, z S ≤ u S + q ∧ u S ≤ z S + q)
    (hv : ∀ S ∈ F, v S ∈ Finset.Icc 1 N)
    (hinj : ∀ S ∈ F, ∀ T ∈ F, z S = z T → u S = u T → v S = v T → S = T) :
    F.card ≤ K.card * ((2 * q + 1) * N) := by
  have hmaps : ∀ S ∈ F, (z S, u S + q - z S, v S) ∈
      K ×ˢ (Finset.range (2 * q + 1) ×ˢ Finset.Icc 1 N) := by
    intro S hS
    obtain ⟨h1, h2⟩ := hu S hS
    exact Finset.mem_product.mpr ⟨hz S hS, Finset.mem_product.mpr
      ⟨Finset.mem_range.mpr (by show u S + q - z S < 2 * q + 1; omega), hv S hS⟩⟩
  have hinj' : Set.InjOn (fun S => (z S, u S + q - z S, v S)) (F : Set (Finset ℕ)) := by
    intro S hS T hT he
    have hS' : S ∈ F := Finset.mem_coe.mp hS
    have hT' : T ∈ F := Finset.mem_coe.mp hT
    have h1 : z S = z T := congrArg Prod.fst he
    have h2 : u S + q - z S = u T + q - z T := congrArg (fun p => p.2.1) he
    have h3 : v S = v T := congrArg (fun p => p.2.2) he
    obtain ⟨a1, -⟩ := hu S hS'
    obtain ⟨a2, -⟩ := hu T hT'
    exact hinj S hS' T hT' h1 (by omega) h3
  calc F.card ≤ (K ×ˢ (Finset.range (2 * q + 1) ×ˢ Finset.Icc 1 N)).card :=
        Finset.card_le_card_of_injOn (fun S => (z S, u S + q - z S, v S))
          (fun S hS => Finset.mem_coe.mpr (hmaps S (Finset.mem_coe.mp hS))) hinj'
    _ = K.card * ((2 * q + 1) * N) := by
        rw [Finset.card_product, Finset.card_product, Finset.card_range, Nat.card_Icc]
        simp

/-- Members with at most one element. -/
theorem OMA.card_small (N : ℕ) (F : Finset (Finset ℕ)) (hsub : ∀ S ∈ F, S ⊆ Finset.Icc 1 N)
    (hsmall : ∀ S ∈ F, S.card ≤ 1) : F.card ≤ N + 1 := by
  have hsubset : F ⊆ insert ∅ ((Finset.Icc 1 N).image (fun x => ({x} : Finset ℕ))) := by
    intro S hS
    rcases Nat.eq_zero_or_pos S.card with h0 | hpos
    · rw [Finset.card_eq_zero.mp h0]
      exact Finset.mem_insert_self _ _
    · have h1 : S.card = 1 := by
        have := hsmall S hS
        omega
      obtain ⟨x, hx⟩ := Finset.card_eq_one.mp h1
      refine Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨x, ?_, hx.symm⟩)
      exact hsub S hS (by rw [hx]; exact Finset.mem_singleton_self x)
  calc F.card ≤ (insert ∅ ((Finset.Icc 1 N).image (fun x => ({x} : Finset ℕ)))).card :=
        Finset.card_le_card hsubset
    _ ≤ ((Finset.Icc 1 N).image (fun x => ({x} : Finset ℕ))).card + 1 :=
        Finset.card_insert_le _ _
    _ ≤ (Finset.Icc 1 N).card + 1 := Nat.add_le_add_right Finset.card_image_le 1
    _ = N + 1 := by rw [Nat.card_Icc]; simp

/-- Simonovits–Sós: an admissible family in `[1, N]` has at most `20 N²` members. -/
theorem OMA.family_bound (N : ℕ) (hN : 1 ≤ N) (A : Finset (Finset ℕ))
    (hA : Erdos272.IsArithInterSet N A) : A.card ≤ 20 * N ^ 2 := by
  obtain ⟨hpow, hpair⟩ := hA
  have hsubA : ∀ S ∈ A, S ⊆ Finset.Icc 1 N := fun S hS => Finset.mem_powerset.mp (hpow hS)
  have hAP : ∀ S ∈ A, ∀ T ∈ A, S ≠ T → OMA.APSet (S ∩ T) := by
    intro S hS T hT hST
    obtain ⟨l, hl, hl'⟩ := hpair (Finset.mem_coe.mpr hS) (Finset.mem_coe.mpr hT) hST
    exact OMA.apSet_of_isAP (S ∩ T) l hl hl'
  have hmeet : ∀ S ∈ A, ∀ T ∈ A, S ≠ T → ∃ x, x ∈ S ∧ x ∈ T := by
    intro S hS T hT hST
    obtain ⟨a, d, I, -, hI0, hX⟩ := hAP S hS T hT hST
    have ha : a ∈ S ∩ T := (hX a).mpr ⟨0, hI0, by simp⟩
    exact ⟨a, Finset.mem_of_mem_inter_left ha, Finset.mem_of_mem_inter_right ha⟩
  rcases Finset.eq_empty_or_nonempty A with hAe | hAne
  · rw [hAe]
    simp
  obtain ⟨K, hKA, hKmin⟩ := Finset.exists_min_image A Finset.card hAne
  have hKN : K.card ≤ N := by
    have h := Finset.card_le_card (hsubA K hKA)
    rwa [Nat.card_Icc, Nat.add_sub_cancel] at h
  -- the choice of `z` and `u`
  have hch : ∀ S : Finset ℕ, ∃ z u : ℕ, S ∈ A → S ≠ K → 2 ≤ S.card →
      z ∈ S ∧ z ∈ K ∧ u ∈ S ∧ z ≠ u ∧ ∀ w ∈ S, ¬ (min z u < w ∧ w < max z u) := by
    intro S
    by_cases h : S ∈ A ∧ S ≠ K ∧ 2 ≤ S.card
    · obtain ⟨hS, hSK, h2⟩ := h
      obtain ⟨a, haS, haK⟩ := hmeet S hS K hKA hSK
      obtain ⟨u, hu1, hu2, hu3⟩ := OMA.exists_adjacent S a haS h2
      exact ⟨a, u, fun _ _ _ => ⟨haS, haK, hu1, hu2, hu3⟩⟩
    · exact ⟨0, 0, fun h1 h2 h3 => absurd ⟨h1, h2, h3⟩ h⟩
  choose z u hzu using hch
  obtain ⟨D, hD⟩ : ∃ D : Finset ℕ → ℕ, ∀ S, D S = max (z S) (u S) - min (z S) (u S) :=
    ⟨fun S => max (z S) (u S) - min (z S) (u S), fun _ => rfl⟩
  obtain ⟨R, hR⟩ : ∃ R : Finset ℕ → Finset ℕ, ∀ S, R S = S \ OMA.runPart S (z S) (D S) :=
    ⟨fun S => S \ OMA.runPart S (z S) (D S), fun _ => rfl⟩
  have hRS : ∀ S, R S ⊆ S := fun S => by rw [hR]; exact Finset.sdiff_subset
  have hPS : ∀ S, OMA.runPart S (z S) (D S) ⊆ S := fun S => by
    unfold OMA.runPart
    exact Finset.filter_subset _ _
  have hbasic : ∀ S ∈ A, S ≠ K → 2 ≤ S.card →
      z S ∈ S ∧ z S ∈ K ∧ u S ∈ S ∧ 1 ≤ D S ∧ D S ≤ N ∧ z S ≤ u S + D S ∧ u S ≤ z S + D S := by
    intro S hS hSK h2
    obtain ⟨h1, h2', h3, h4, -⟩ := hzu S hS hSK h2
    have hz1 := Finset.mem_Icc.mp (hsubA S hS h1)
    have hu1 := Finset.mem_Icc.mp (hsubA S hS h3)
    have hDS := hD S
    refine ⟨h1, h2', h3, ?_, ?_, ?_, ?_⟩ <;> omega
  -- uniqueness of the triples
  have huniq : ∀ S ∈ A, S ≠ K → 2 ≤ S.card → ∀ T ∈ A, T ≠ S → ∀ v ∈ R S,
      ¬ (z S ∈ T ∧ u S ∈ T ∧ v ∈ T) := by
    intro S hS hSK h2 T hT hTS v hv hT3
    obtain ⟨hzT, huT, hvT⟩ := hT3
    obtain ⟨h1, -, h3, h4, h5⟩ := hzu S hS hSK h2
    rw [hR, Finset.mem_sdiff, hD] at hv
    exact OMA.triple_unique S T (hAP S hS T hT (Ne.symm hTS)) (z S) (u S) v h4 h5 hv.1 hv.2
      (Finset.mem_inter.mpr ⟨h1, hzT⟩) (Finset.mem_inter.mpr ⟨h3, huT⟩)
      (Finset.mem_inter.mpr ⟨hv.1, hvT⟩)
  have hall : ∀ S, R S = ∅ → ∀ y ∈ S, y ∈ OMA.runPart S (z S) (D S) := by
    intro S hRe y hy
    by_contra hny
    have h : y ∈ R S := by
      rw [hR]
      exact Finset.mem_sdiff.mpr ⟨hy, hny⟩
    rw [hRe] at h
    exact Finset.notMem_empty y h
  -- the pieces of the family
  obtain ⟨A0, m0⟩ : ∃ X : Finset (Finset ℕ), ∀ S, S ∈ X ↔ S ∈ A ∧ S.card ≤ 1 :=
    ⟨A.filter (fun S => S.card ≤ 1), fun S => Finset.mem_filter⟩
  obtain ⟨A1, m1⟩ : ∃ X : Finset (Finset ℕ), ∀ S, S ∈ X ↔
      S ∈ A ∧ (S ≠ K ∧ 2 ≤ S.card ∧ R S = ∅) :=
    ⟨A.filter (fun S => S ≠ K ∧ 2 ≤ S.card ∧ R S = ∅), fun S => Finset.mem_filter⟩
  obtain ⟨AI, mI⟩ : ∃ X : Finset (Finset ℕ), ∀ S, S ∈ X ↔
      S ∈ A ∧ (S ≠ K ∧ 2 ≤ S.card ∧ R S ≠ ∅ ∧ S.card ≤ 4 * (R S).card) :=
    ⟨A.filter (fun S => S ≠ K ∧ 2 ≤ S.card ∧ R S ≠ ∅ ∧ S.card ≤ 4 * (R S).card),
      fun S => Finset.mem_filter⟩
  obtain ⟨AII, mII⟩ : ∃ X : Finset (Finset ℕ), ∀ S, S ∈ X ↔
      S ∈ A ∧ (S ≠ K ∧ 2 ≤ S.card ∧ R S ≠ ∅ ∧ 4 * (R S).card < S.card) :=
    ⟨A.filter (fun S => S ≠ K ∧ 2 ≤ S.card ∧ R S ≠ ∅ ∧ 4 * (R S).card < S.card),
      fun S => Finset.mem_filter⟩
  have hcover : A ⊆ insert K (A0 ∪ (A1 ∪ (AI ∪ AII))) := by
    intro S hS
    by_cases h1 : S = K
    · exact Finset.mem_insert.mpr (Or.inl h1)
    refine Finset.mem_insert_of_mem ?_
    by_cases h2 : S.card ≤ 1
    · exact Finset.mem_union_left _ ((m0 S).mpr ⟨hS, h2⟩)
    refine Finset.mem_union_right _ ?_
    have h2' : 2 ≤ S.card := by omega
    by_cases h3 : R S = ∅
    · exact Finset.mem_union_left _ ((m1 S).mpr ⟨hS, h1, h2', h3⟩)
    refine Finset.mem_union_right _ ?_
    by_cases h4 : S.card ≤ 4 * (R S).card
    · exact Finset.mem_union_left _ ((mI S).mpr ⟨hS, h1, h2', h3, h4⟩)
    · exact Finset.mem_union_right _ ((mII S).mpr ⟨hS, h1, h2', h3, by omega⟩)
  -- members with at most one element
  have c0 : A0.card ≤ N + 1 :=
    OMA.card_small N A0 (fun S hS => hsubA S ((m0 S).mp hS).1) (fun S hS => ((m0 S).mp hS).2)
  -- runs
  have c1 : A1.card ≤ 8 * N ^ 2 := by
    refine le_trans (OMA.card_runs N A1 D ?_ ?_ ?_ ?_ ?_ ?_) (OMA.sum_bound8 N)
    · intro S hS
      exact hsubA S ((m1 S).mp hS).1
    · intro S hS
      obtain ⟨-, -, h2, -⟩ := (m1 S).mp hS
      exact Finset.card_pos.mp (by omega)
    · intro S hS
      obtain ⟨hSA, hSK, h2, -⟩ := (m1 S).mp hS
      obtain ⟨-, -, -, h4, h5, -⟩ := hbasic S hSA hSK h2
      exact ⟨h4, h5⟩
    · intro S hS x hx x' hx'
      obtain ⟨-, -, -, hRe⟩ := (m1 S).mp hS
      have e1 := ((OMA.mem_runPart S (z S) (D S) x).mp (hall S hRe x hx)).2.1
      have e2 := ((OMA.mem_runPart S (z S) (D S) x').mp (hall S hRe x' hx')).2.1
      rw [e1, e2]
    · intro S hS x hx x' hx' y hy1 hy2 hy3
      obtain ⟨-, -, -, hRe⟩ := (m1 S).mp hS
      obtain ⟨-, e1, f1⟩ := (OMA.mem_runPart S (z S) (D S) x).mp (hall S hRe x hx)
      obtain ⟨-, -, f2⟩ := (OMA.mem_runPart S (z S) (D S) x').mp (hall S hRe x' hx')
      have hyz : y % D S = z S % D S := by rw [hy3, e1]
      rcases le_total (z S) y with hzy | hyz'
      · exact f2 y (by omega) (by omega) hyz
      · exact f1 y (by omega) (by omega) hyz
    · intro S hS T hT hST
      exact hmeet S ((m1 S).mp hS).1 T ((m1 T).mp hT).1 hST
  -- many points outside the run
  have cI : AI.card ≤ 4 * (N * N) := by
    refine OMA.card_caseI N K AI z u R ?_ ?_ ?_ ?_ ?_
    · intro S hS
      obtain ⟨hSA, hSK, h2, -⟩ := (mI S).mp hS
      exact (hbasic S hSA hSK h2).2.1
    · intro S hS
      obtain ⟨hSA, hSK, h2, -⟩ := (mI S).mp hS
      exact hsubA S hSA (hbasic S hSA hSK h2).2.2.1
    · intro S hS
      exact (hRS S).trans (hsubA S ((mI S).mp hS).1)
    · intro S hS T hT hST hzz huu v hv hvT
      obtain ⟨hSA, hSK, h2, -⟩ := (mI S).mp hS
      obtain ⟨hTA, hTK, h2T, -⟩ := (mI T).mp hT
      have hbT := hbasic T hTA hTK h2T
      refine huniq S hSA hSK h2 T hTA (Ne.symm hST) v hv ⟨?_, ?_, hRS T hvT⟩
      · rw [hzz]; exact hbT.1
      · rw [huu]; exact hbT.2.2.1
    · intro S hS
      obtain ⟨hSA, -, -, -, h4⟩ := (mI S).mp hS
      exact le_trans (hKmin S hSA) h4
  -- few points outside the run
  have hvch : ∀ S : Finset ℕ, ∃ v : ℕ, R S ≠ ∅ → v ∈ R S := by
    intro S
    by_cases h : R S = ∅
    · exact ⟨0, fun h' => absurd h h'⟩
    · obtain ⟨v, hv⟩ := Finset.nonempty_iff_ne_empty.mpr h
      exact ⟨v, fun _ => hv⟩
  choose v hv using hvch
  have cII : AII.card ≤ K.card * ((2 * (2 * N / K.card) + 1) * N) := by
    refine OMA.card_caseII N (2 * N / K.card) K AII z u v ?_ ?_ ?_ ?_
    · intro S hS
      obtain ⟨hSA, hSK, h2, -⟩ := (mII S).mp hS
      exact (hbasic S hSA hSK h2).2.1
    · intro S hS
      obtain ⟨hSA, hSK, h2, hRne, h4⟩ := (mII S).mp hS
      obtain ⟨hzS, hzK, huS, hD1, hDN, hzu1, hzu2⟩ := hbasic S hSA hSK h2
      have hkpos : 0 < K.card := Finset.card_pos.mpr ⟨z S, hzK⟩
      have hr : 1 ≤ (R S).card := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hRne)
      have hcardRP : (R S).card + (OMA.runPart S (z S) (D S)).card = S.card := by
        rw [hR]
        exact Finset.card_sdiff_add_card_eq_card (hPS S)
      have hPle : (OMA.runPart S (z S) (D S)).card ≤ N / D S + 1 :=
        OMA.card_class_le N (D S) (z S % D S) _ (fun x hx =>
          ⟨(Finset.mem_Icc.mp (hsubA S hSA (hPS S hx))).2,
           ((OMA.mem_runPart S (z S) (D S) x).mp hx).2.1⟩)
      have hkS := hKmin S hSA
      have hmul : ((OMA.runPart S (z S) (D S)).card - 1) * D S ≤ N := by
        have h' : (OMA.runPart S (z S) (D S)).card - 1 ≤ N / D S := by omega
        exact le_trans (Nat.mul_le_mul_right _ h') (Nat.div_mul_le_self N (D S))
      have hk2 : K.card ≤ 2 * ((OMA.runPart S (z S) (D S)).card - 1) := by omega
      have hkD : D S * K.card ≤ 2 * N := by
        calc D S * K.card ≤ D S * (2 * ((OMA.runPart S (z S) (D S)).card - 1)) :=
              Nat.mul_le_mul_left _ hk2
          _ = 2 * (((OMA.runPart S (z S) (D S)).card - 1) * D S) := by ring
          _ ≤ 2 * N := Nat.mul_le_mul_left 2 hmul
      have hDq : D S ≤ 2 * N / K.card := (Nat.le_div_iff_mul_le hkpos).mpr hkD
      exact ⟨by omega, by omega⟩
    · intro S hS
      obtain ⟨hSA, -, -, hRne, -⟩ := (mII S).mp hS
      exact hsubA S hSA (hRS S (hv S hRne))
    · intro S hS T hT hzz huu hvv
      by_contra hne
      obtain ⟨hSA, hSK, h2, hRne, -⟩ := (mII S).mp hS
      obtain ⟨hTA, hTK, h2T, hRneT, -⟩ := (mII T).mp hT
      have hbT := hbasic T hTA hTK h2T
      refine huniq S hSA hSK h2 T hTA (Ne.symm hne) (v S) (hv S hRne) ⟨?_, ?_, ?_⟩
      · rw [hzz]; exact hbT.1
      · rw [huu]; exact hbT.2.2.1
      · rw [hvv]; exact hRS T (hv T hRneT)
  have hq : K.card * (2 * (2 * N / K.card) + 1) ≤ 5 * N := by
    have h1 : K.card * (2 * N / K.card) ≤ 2 * N := Nat.mul_div_le _ _
    have h2 : K.card * (2 * (2 * N / K.card) + 1)
        = 2 * (K.card * (2 * N / K.card)) + K.card := by ring
    omega
  have cII' : AII.card ≤ 5 * (N * N) := by
    calc AII.card ≤ K.card * ((2 * (2 * N / K.card) + 1) * N) := cII
      _ = K.card * (2 * (2 * N / K.card) + 1) * N := by ring
      _ ≤ 5 * N * N := Nat.mul_le_mul_right N hq
      _ = 5 * (N * N) := by ring
  -- total
  have t1 := Finset.card_le_card hcover
  have t2 := Finset.card_insert_le K (A0 ∪ (A1 ∪ (AI ∪ AII)))
  have t3 := Finset.card_union_le A0 (A1 ∪ (AI ∪ AII))
  have t4 := Finset.card_union_le A1 (AI ∪ AII)
  have t5 := Finset.card_union_le AI AII
  have hsq : N ^ 2 = N * N := sq N
  have hNN : N ≤ N * N := Nat.le_mul_self N
  rw [hsq] at c1 ⊢
  omega

theorem OMA.solution : type_of% @Erdos272.erdos_272.variants.isBigO_sq := by
  refine Asymptotics.IsBigO.of_bound 20 (Filter.eventually_atTop.mpr ⟨1, fun N hN => ?_⟩)
  have hle : Erdos272.maxArithInterCard N ≤ 20 * N ^ 2 := by
    unfold Erdos272.maxArithInterCard
    refine csSup_le ⟨0, ∅, ?_, Finset.card_empty⟩ ?_
    · refine ⟨Finset.empty_subset _, ?_⟩
      intro S hS
      exact absurd (Finset.mem_coe.mp hS) (Finset.notMem_empty S)
    · rintro b ⟨A, hA, rfl⟩
      exact OMA.family_bound N hN A hA
  have hreal : (Erdos272.maxArithInterCard N : ℝ) ≤ 20 * (N : ℝ) ^ 2 := by exact_mod_cast hle
  have e1 : ‖(Erdos272.maxArithInterCard N : ℝ)‖ = (Erdos272.maxArithInterCard N : ℝ) :=
    Real.norm_of_nonneg (Nat.cast_nonneg _)
  have e2 : ‖(N : ℝ) ^ 2‖ = (N : ℝ) ^ 2 := Real.norm_of_nonneg (by positivity)
  show ‖(Erdos272.maxArithInterCard N : ℝ)‖ ≤ 20 * ‖(N : ℝ) ^ 2‖
  rw [e1, e2]
  exact hreal
