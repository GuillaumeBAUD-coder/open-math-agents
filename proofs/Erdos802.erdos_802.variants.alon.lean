import FormalConjectures.ErdosProblems.«802»

-- Problem: Erdős Problem 802 — alon
-- Upstream: formal-conjectures FormalConjectures/ErdosProblems/802.lean:105 (declaration Erdos802.erdos_802.variants.alon)
-- Credit: @rorcores (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

/-!
Alon's theorem on locally sparse graphs: if every neighbourhood of `G` is `q`-colourable then
`G` has an independent set of size at least `c_q * (log t / t) * n`, `t` the average degree.

Proof (counting over all independent sets, after Alon and Spencer).  Restrict to the set `S` of
vertices of degree at most `D = ⌊2t⌋`; it has at least `n / 2` vertices.  For an independent
`I ⊆ S` and `v ∈ S` put `X_v(I) = D * [v ∈ I] + |I ∩ N(v)|`, so that `∑_v X_v(I) ≤ 2 * D * |I|`.
Group the independent sets by `J = I \ N[v]`.  With `F` the neighbours of `v` in `S` having no
neighbour in `J`, the group consists of `J ∪ {v}` and of the sets `J ∪ B`, `B ⊆ F` independent.
`F` contains an independent set `C` with `|F| ≤ q * |C|`, hence there are at least `2 ^ |C|`
such `B`.  If `F` is large, a binomial tail estimate shows that fewer than half of them have less
than `2k` elements, so the average of `X_v` over the group is at least `k / 4`; if `F` is small
the group has at most `2 ^ |F| + 1` members and the term `D` from `J ∪ {v}` suffices.  Here `k`
is of order `log D`.  Averaging over `v` and `I` gives `k * |S| ≤ 8 * D * α(G)`.
-/

namespace OMA

open Finset Classical

/-- A single term of the binomial expansion of `(t + 1) ^ x`. -/
theorem a802_choose_mul_pow (t x s : ℕ) : x.choose s * t ^ x ≤ t ^ s * (t + 1) ^ x := by
  induction x generalizing s with
  | zero =>
    cases s with
    | zero => simp
    | succ s => simp
  | succ x ih =>
    cases s with
    | zero =>
      simp only [Nat.choose_zero_right, one_mul, pow_zero]
      exact Nat.pow_le_pow_left (Nat.le_succ t) _
    | succ s =>
      rw [Nat.choose_succ_succ]
      have h1 := ih s
      have h2 := ih (s + 1)
      calc (x.choose s + x.choose (s + 1)) * t ^ (x + 1)
          = t * (x.choose s * t ^ x) + t * (x.choose (s + 1) * t ^ x) := by ring
        _ ≤ t * (t ^ s * (t + 1) ^ x) + t * (t ^ (s + 1) * (t + 1) ^ x) :=
            Nat.add_le_add (Nat.mul_le_mul_left _ h1) (Nat.mul_le_mul_left _ h2)
        _ = t ^ (s + 1) * (t + 1) ^ (x + 1) := by ring

/-- The number of subsets of `F` with fewer than `s` elements, weighted by `t ^ |F|`. -/
theorem a802_small_count {V : Type*} (F : Finset V) (t s : ℕ) (ht : 2 ≤ t) :
    (F.powerset.filter (fun A => A.card < s)).card * t ^ F.card ≤ t ^ s * (t + 1) ^ F.card := by
  induction s with
  | zero => simp
  | succ s ih =>
    have hsub : F.powerset.filter (fun A => A.card < s + 1) ⊆
        F.powerset.filter (fun A => A.card < s) ∪ F.powersetCard s := by
      intro A hA
      rw [mem_filter, mem_powerset] at hA
      rw [mem_union, mem_filter, mem_powerset, mem_powersetCard]
      rcases Nat.lt_or_ge A.card s with h | h
      · exact Or.inl ⟨hA.1, h⟩
      · exact Or.inr ⟨hA.1, by omega⟩
    have hc : (F.powerset.filter (fun A => A.card < s + 1)).card ≤
        (F.powerset.filter (fun A => A.card < s)).card + F.card.choose s := by
      calc (F.powerset.filter (fun A => A.card < s + 1)).card
          ≤ (F.powerset.filter (fun A => A.card < s) ∪ F.powersetCard s).card := card_le_card hsub
        _ ≤ (F.powerset.filter (fun A => A.card < s)).card + (F.powersetCard s).card :=
            card_union_le _ _
        _ = (F.powerset.filter (fun A => A.card < s)).card + F.card.choose s := by
            rw [card_powersetCard]
    have h1 := a802_choose_mul_pow t F.card s
    calc (F.powerset.filter (fun A => A.card < s + 1)).card * t ^ F.card
        ≤ ((F.powerset.filter (fun A => A.card < s)).card + F.card.choose s) * t ^ F.card :=
          Nat.mul_le_mul_right _ hc
      _ = (F.powerset.filter (fun A => A.card < s)).card * t ^ F.card +
            F.card.choose s * t ^ F.card := by ring
      _ ≤ t ^ s * (t + 1) ^ F.card + t ^ s * (t + 1) ^ F.card := Nat.add_le_add ih h1
      _ = 2 * (t ^ s * (t + 1) ^ F.card) := by ring
      _ ≤ t * (t ^ s * (t + 1) ^ F.card) := Nat.mul_le_mul_right _ ht
      _ = t ^ (s + 1) * (t + 1) ^ F.card := by ring

/-- A Bernoulli type inequality. -/
theorem a802_bern (t ρ : ℕ) (h : ρ ≤ t) : (t + 1) ^ ρ * (t - ρ) ≤ t ^ (ρ + 1) := by
  induction ρ with
  | zero => simp
  | succ ρ ih =>
    have ih' := ih (by omega)
    have h2 : (t + 1) * (t - (ρ + 1)) ≤ t * (t - ρ) := by
      obtain ⟨m, rfl⟩ : ∃ m, t = ρ + 1 + m := ⟨t - (ρ + 1), by omega⟩
      have e1 : ρ + 1 + m - (ρ + 1) = m := by omega
      have e2 : ρ + 1 + m - ρ = m + 1 := by omega
      rw [e1, e2]
      nlinarith
    calc (t + 1) ^ (ρ + 1) * (t - (ρ + 1)) = (t + 1) ^ ρ * ((t + 1) * (t - (ρ + 1))) := by ring
      _ ≤ (t + 1) ^ ρ * (t * (t - ρ)) := Nat.mul_le_mul_left _ h2
      _ = t * ((t + 1) ^ ρ * (t - ρ)) := by ring
      _ ≤ t * t ^ (ρ + 1) := Nat.mul_le_mul_left _ ih'
      _ = t ^ (ρ + 1 + 1) := by ring

theorem a802_pow_le_two (t ρ : ℕ) (ht : 0 < t) (h : 2 * ρ ≤ t) : (t + 1) ^ ρ ≤ 2 * t ^ ρ := by
  have h1 := a802_bern t ρ (by omega)
  have h3 : (t + 1) ^ ρ * t ≤ 2 * t ^ ρ * t := by
    calc (t + 1) ^ ρ * t ≤ (t + 1) ^ ρ * (2 * (t - ρ)) := Nat.mul_le_mul_left _ (by omega)
      _ = 2 * ((t + 1) ^ ρ * (t - ρ)) := by ring
      _ ≤ 2 * t ^ (ρ + 1) := Nat.mul_le_mul_left _ h1
      _ = 2 * t ^ ρ * t := by ring
  exact Nat.le_of_mul_le_mul_right h3 ht

/-- If `F` is large compared with `s`, fewer than `2 ^ (m - 1)` subsets of `F` have fewer than
`s` elements, where `|F| ≤ q * m`. -/
theorem a802_small_sets {V : Type*} (F : Finset V) (q s lam m : ℕ) (hq : 1 ≤ q)
    (hlam : 4 * q ≤ 2 ^ lam) (hm : F.card ≤ q * m) (hx : 2 * q * (lam * s + 2) ≤ F.card) :
    2 * (F.powerset.filter (fun A => A.card < s)).card ≤ 2 ^ m := by
  obtain ⟨x, hxdef⟩ : ∃ x, x = F.card := ⟨_, rfl⟩
  obtain ⟨N, hN⟩ : ∃ N, N = (F.powerset.filter (fun A => A.card < s)).card := ⟨_, rfl⟩
  obtain ⟨t, ht⟩ : ∃ t, t = 4 * q := ⟨_, rfl⟩
  rw [← hxdef] at hm hx
  rw [← hN]
  have ht2 : 2 ≤ t := by omega
  have htpos : 0 < t := by omega
  have h0 : N * t ^ x ≤ t ^ s * (t + 1) ^ x := by
    rw [hN, hxdef]; exact a802_small_count F t s ht2
  obtain ⟨w, hw⟩ : ∃ w, w = x / (2 * q) := ⟨_, rfl⟩
  obtain ⟨ρ, hρ⟩ : ∃ ρ, ρ = x % (2 * q) := ⟨_, rfl⟩
  have hxw : x = 2 * q * w + ρ := by rw [hw, hρ]; exact (Nat.div_add_mod x (2 * q)).symm
  have hρlt : ρ < 2 * q := by rw [hρ]; exact Nat.mod_lt _ (by omega)
  have hA : (t + 1) ^ (2 * q) ≤ 2 * t ^ (2 * q) := a802_pow_le_two t (2 * q) htpos (by omega)
  have hB : (t + 1) ^ ρ ≤ 2 * t ^ ρ := a802_pow_le_two t ρ htpos (by omega)
  have hC : (t + 1) ^ x ≤ 2 ^ (w + 1) * t ^ x := by
    calc (t + 1) ^ x = ((t + 1) ^ (2 * q)) ^ w * (t + 1) ^ ρ := by rw [hxw, pow_add, pow_mul]
      _ ≤ (2 * t ^ (2 * q)) ^ w * (2 * t ^ ρ) := Nat.mul_le_mul (Nat.pow_le_pow_left hA w) hB
      _ = 2 ^ (w + 1) * t ^ x := by rw [hxw]; ring
  have hD : N * t ^ x ≤ (t ^ s * 2 ^ (w + 1)) * t ^ x := by
    calc N * t ^ x ≤ t ^ s * (t + 1) ^ x := h0
      _ ≤ t ^ s * (2 ^ (w + 1) * t ^ x) := Nat.mul_le_mul_left _ hC
      _ = (t ^ s * 2 ^ (w + 1)) * t ^ x := by ring
  have hE : N ≤ t ^ s * 2 ^ (w + 1) := Nat.le_of_mul_le_mul_right hD (by positivity)
  have hF : t ^ s ≤ 2 ^ (lam * s) := by
    rw [pow_mul, ht]; exact Nat.pow_le_pow_left hlam s
  have hw1 : lam * s + 2 ≤ w := by
    rw [hw, Nat.le_div_iff_mul_le (by omega)]
    calc (lam * s + 2) * (2 * q) = 2 * q * (lam * s + 2) := by ring
      _ ≤ x := hx
  have hw2 : 2 * w ≤ m := by
    have h5 : q * (2 * w) ≤ q * m := by
      calc q * (2 * w) = 2 * q * w := by ring
        _ ≤ x := by omega
        _ ≤ q * m := hm
    exact Nat.le_of_mul_le_mul_left h5 (by omega)
  calc 2 * N ≤ 2 * (t ^ s * 2 ^ (w + 1)) := Nat.mul_le_mul_left _ hE
    _ ≤ 2 * (2 ^ (lam * s) * 2 ^ (w + 1)) :=
        Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ hF)
    _ = 2 ^ (lam * s + w + 2) := by ring
    _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) (by omega)

/-- A set of neighbours of `v` contains an independent set of proportional size when the
neighbourhood of `v` is `q`-colourable. -/
theorem a802_colour_class {V : Type*} (G : SimpleGraph V) (v : V) (q : ℕ)
    (hcol : (G.induce (G.neighborSet v)).Colorable q) (F : Finset V)
    (hF : ∀ u ∈ F, G.Adj v u) :
    ∃ C ⊆ F, (∀ a ∈ C, ∀ b ∈ C, ¬ G.Adj a b) ∧ F.card ≤ q * C.card := by
  obtain ⟨c⟩ := hcol
  rcases Nat.eq_zero_or_pos q with hq0 | hqpos
  · subst hq0
    have hFe : F = ∅ := by
      by_contra hne
      obtain ⟨u, hu⟩ := Finset.nonempty_iff_ne_empty.mpr hne
      exact (c ⟨u, hF u hu⟩).elim0
    exact ⟨∅, by simp, by simp, by simp [hFe]⟩
  · obtain ⟨f, hf⟩ : ∃ f : V → Fin q, ∀ u (h : G.Adj v u), f u = c ⟨u, h⟩ :=
      ⟨fun u => if h : G.Adj v u then c ⟨u, h⟩ else ⟨0, hqpos⟩, fun u h => by simp [h]⟩
    obtain ⟨y, -, hy⟩ := Finset.exists_max_image (Finset.univ : Finset (Fin q))
      (fun y => (F.filter (fun u => f u = y)).card) ⟨⟨0, hqpos⟩, Finset.mem_univ _⟩
    refine ⟨F.filter (fun u => f u = y), Finset.filter_subset _ _, ?_, ?_⟩
    · intro a ha b hb hab
      rw [Finset.mem_filter] at ha hb
      have hva := hF a ha.1
      have hvb := hF b hb.1
      have hadj : (G.induce (G.neighborSet v)).Adj ⟨a, hva⟩ ⟨b, hvb⟩ := hab
      exact c.valid hadj (by rw [← hf a hva, ← hf b hvb, ha.2, hb.2])
    · have hsum : F.card = ∑ y' : Fin q, (F.filter (fun u => f u = y')).card :=
        Finset.card_eq_sum_card_fiberwise (fun u _ => Finset.mem_coe.mpr (Finset.mem_univ (f u)))
      calc F.card = ∑ y' : Fin q, (F.filter (fun u => f u = y')).card := hsum
        _ ≤ ∑ _y' : Fin q, (F.filter (fun u => f u = y)).card :=
            Finset.sum_le_sum fun y' _ => hy y' (Finset.mem_univ _)
        _ = q * (F.filter (fun u => f u = y)).card := by simp

/-- Independence of a finite set of vertices. -/
abbrev Ind {V : Type*} (G : SimpleGraph V) (I : Finset V) : Prop :=
  ∀ a ∈ I, ∀ b ∈ I, ¬ G.Adj a b

/-- The averaging step: among the independent subsets `I` of `S` with a prescribed part `J`
outside the closed neighbourhood of `v`, the quantity `Δ * [v ∈ I] + |I ∩ N(v)|` is at least
`k / 4` on average. -/
theorem a802_fiber {V : Type*} (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) (v : V)
    (hv : v ∈ S) (Δ k q lam : ℕ) (hq : 1 ≤ q) (hlam : 4 * q ≤ 2 ^ lam)
    (hcol : (G.induce (G.neighborSet v)).Colorable q)
    (H1 : k * 2 ^ (2 * q * (lam * (2 * k) + 2)) ≤ 4 * Δ) (J : Finset V) :
    k * ((S.powerset.filter (Ind G)).filter
        (fun I => I.filter (fun u => u ≠ v ∧ ¬ G.Adj v u) = J)).card
      ≤ 4 * ∑ I ∈ (S.powerset.filter (Ind G)).filter
          (fun I => I.filter (fun u => u ≠ v ∧ ¬ G.Adj v u) = J),
          ((if v ∈ I then Δ else 0) + (I.filter (G.Adj v)).card) := by
  obtain ⟨Φ, hΦ⟩ : ∃ Φ, Φ = (S.powerset.filter (Ind G)).filter
      (fun I => I.filter (fun u => u ≠ v ∧ ¬ G.Adj v u) = J) := ⟨_, rfl⟩
  rw [← hΦ]
  rcases Φ.eq_empty_or_nonempty with h0 | ⟨I0, hI0⟩
  · rw [h0]; simp
  have memΦ : ∀ I, I ∈ Φ ↔
      (I ⊆ S ∧ Ind G I ∧ I.filter (fun u => u ≠ v ∧ ¬ G.Adj v u) = J) := by
    intro I; rw [hΦ, mem_filter, mem_filter, mem_powerset, and_assoc]
  obtain ⟨hI0S, hI0ind, hI0J⟩ := (memΦ I0).mp hI0
  have hJmem : ∀ u ∈ J, u ∈ I0 ∧ u ≠ v ∧ ¬ G.Adj v u := by
    intro u hu; rw [← hI0J, mem_filter] at hu; exact hu
  have hJS : J ⊆ S := fun u hu => hI0S (hJmem u hu).1
  have hJind : Ind G J := fun a ha b hb => hI0ind a (hJmem a ha).1 b (hJmem b hb).1
  have hvJ : v ∉ J := fun h => (hJmem v h).2.1 rfl
  -- the free part of the neighbourhood of `v`
  obtain ⟨F, hFdef⟩ : ∃ F, F = (S.filter (G.Adj v)).filter (fun u => ∀ j ∈ J, ¬ G.Adj u j) :=
    ⟨_, rfl⟩
  have hFmem : ∀ u, u ∈ F ↔ (u ∈ S ∧ G.Adj v u ∧ ∀ j ∈ J, ¬ G.Adj u j) := by
    intro u; rw [hFdef, mem_filter, mem_filter, and_assoc]
  -- every independent `B ⊆ F` gives the member `J ∪ B`
  have hput : ∀ B, B ⊆ F → Ind G B →
      (J ∪ B ∈ Φ ∧ v ∉ J ∪ B ∧ (J ∪ B).filter (G.Adj v) = B) := by
    intro B hBF hBind
    have hBv : ∀ u ∈ B, G.Adj v u := fun u hu => ((hFmem u).mp (hBF hu)).2.1
    have hvB : v ∉ B := fun h => G.irrefl (hBv v h)
    refine ⟨(memΦ _).mpr ⟨?_, ?_, ?_⟩, ?_, ?_⟩
    · exact union_subset hJS (fun u hu => ((hFmem u).mp (hBF hu)).1)
    · intro a ha b hb
      rw [mem_union] at ha hb
      rcases ha with ha | ha <;> rcases hb with hb | hb
      · exact hJind a ha b hb
      · exact fun h => ((hFmem b).mp (hBF hb)).2.2 a ha h.symm
      · exact ((hFmem a).mp (hBF ha)).2.2 b hb
      · exact hBind a ha b hb
    · ext u
      simp only [mem_filter, mem_union]
      constructor
      · rintro ⟨hu | hu, -, hnadj⟩
        · exact hu
        · exact absurd (hBv u hu) hnadj
      · intro hu
        exact ⟨Or.inl hu, (hJmem u hu).2.1, (hJmem u hu).2.2⟩
    · rw [mem_union]
      rintro (h | h)
      · exact hvJ h
      · exact hvB h
    · ext u
      simp only [mem_filter, mem_union]
      constructor
      · rintro ⟨hu | hu, hadj⟩
        · exact absurd hadj (hJmem u hu).2.2
        · exact hu
      · intro hu
        exact ⟨Or.inr hu, hBv u hu⟩
  -- the member containing `v`
  have hvmem : insert v J ∈ Φ := by
    refine (memΦ _).mpr ⟨insert_subset hv hJS, ?_, ?_⟩
    · intro a ha b hb
      rw [mem_insert] at ha hb
      rcases ha with ha | ha <;> rcases hb with hb | hb
      · rw [ha, hb]; exact G.irrefl
      · rw [ha]; exact (hJmem b hb).2.2
      · rw [hb]; exact fun h => (hJmem a ha).2.2 h.symm
      · exact hJind a ha b hb
    · ext u
      simp only [mem_filter, mem_insert]
      constructor
      · rintro ⟨hu | hu, hne, -⟩
        · exact absurd hu hne
        · exact hu
      · intro hu
        exact ⟨Or.inr hu, (hJmem u hu).2.1, (hJmem u hu).2.2⟩
  -- members not containing `v`
  have hsplit : ∀ I ∈ Φ, v ∉ I → (I.filter (G.Adj v) ⊆ F ∧ I = J ∪ I.filter (G.Adj v)) := by
    intro I hI hvI
    obtain ⟨hIS, hIind, hIJ⟩ := (memΦ I).mp hI
    refine ⟨?_, ?_⟩
    · intro u hu
      rw [mem_filter] at hu
      refine (hFmem u).mpr ⟨hIS hu.1, hu.2, fun j hj => ?_⟩
      have hjI : j ∈ I := by rw [← hIJ, mem_filter] at hj; exact hj.1
      exact hIind u hu.1 j hjI
    · ext u
      constructor
      · intro hu
        rw [mem_union]
        by_cases hadj : G.Adj v u
        · exact Or.inr (mem_filter.mpr ⟨hu, hadj⟩)
        · left
          rw [← hIJ, mem_filter]
          exact ⟨hu, fun h => hvI (h ▸ hu), hadj⟩
      · intro hu
        rw [mem_union] at hu
        rcases hu with hu | hu
        · rw [← hIJ, mem_filter] at hu; exact hu.1
        · exact (mem_filter.mp hu).1
  obtain ⟨Φ0, hΦ0⟩ : ∃ Φ0, Φ0 = Φ.filter (fun I => v ∉ I) := ⟨_, rfl⟩
  have hΦ0mem : ∀ I, I ∈ Φ0 ↔ (I ∈ Φ ∧ v ∉ I) := by
    intro I; rw [hΦ0, mem_filter]
  have hAinj : Set.InjOn (fun I : Finset V => I.filter (G.Adj v)) (Φ0 : Set (Finset V)) := by
    intro I hI I' hI' h
    rw [mem_coe, hΦ0mem] at hI hI'
    calc I = J ∪ I.filter (G.Adj v) := (hsplit I hI.1 hI.2).2
      _ = J ∪ I'.filter (G.Adj v) := by rw [show I.filter (G.Adj v) = I'.filter (G.Adj v) from h]
      _ = I' := ((hsplit I' hI'.1 hI'.2).2).symm
  have hcard_le : Φ0.card ≤ 2 ^ F.card := by
    rw [← card_powerset]
    refine card_le_card_of_injOn (fun I : Finset V => I.filter (G.Adj v)) ?_ hAinj
    intro I hI
    rw [mem_coe, hΦ0mem] at hI
    exact mem_coe.mpr (mem_powerset.mpr (hsplit I hI.1 hI.2).1)
  have hNle : (Φ0.filter (fun I => (I.filter (G.Adj v)).card < 2 * k)).card ≤
      (F.powerset.filter (fun B => B.card < 2 * k)).card := by
    refine card_le_card_of_injOn (fun I : Finset V => I.filter (G.Adj v)) ?_ ?_
    · intro I hI
      rw [mem_coe, mem_filter, hΦ0mem] at hI
      rw [mem_coe, mem_filter, mem_powerset]
      exact ⟨(hsplit I hI.1.1 hI.1.2).1, hI.2⟩
    · exact hAinj.mono (fun I hI => by
        rw [mem_coe, mem_filter] at hI; exact mem_coe.mpr hI.1)
  have hsum_ge : 2 * k * (Φ0.card - (Φ0.filter (fun I => (I.filter (G.Adj v)).card < 2 * k)).card)
      ≤ ∑ I ∈ Φ0, (I.filter (G.Adj v)).card := by
    have h1 : (Φ0.filter (fun I => ¬ (I.filter (G.Adj v)).card < 2 * k)).card =
        Φ0.card - (Φ0.filter (fun I => (I.filter (G.Adj v)).card < 2 * k)).card := by
      have := card_filter_add_card_filter_not (s := Φ0)
        (fun I => (I.filter (G.Adj v)).card < 2 * k)
      omega
    calc 2 * k * (Φ0.card - (Φ0.filter (fun I => (I.filter (G.Adj v)).card < 2 * k)).card)
        = ∑ _I ∈ Φ0.filter (fun I => ¬ (I.filter (G.Adj v)).card < 2 * k), 2 * k := by
          rw [sum_const, smul_eq_mul, h1, mul_comm]
      _ ≤ ∑ I ∈ Φ0.filter (fun I => ¬ (I.filter (G.Adj v)).card < 2 * k),
            (I.filter (G.Adj v)).card :=
          sum_le_sum fun I hI => by
            have := (mem_filter.mp hI).2
            omega
      _ ≤ ∑ I ∈ Φ0, (I.filter (G.Adj v)).card :=
          sum_le_sum_of_subset (filter_subset _ _)
  have hSig : Δ + ∑ I ∈ Φ0, (I.filter (G.Adj v)).card ≤
      ∑ I ∈ Φ, ((if v ∈ I then Δ else 0) + (I.filter (G.Adj v)).card) := by
    have hdisj : Disjoint Φ0 {insert v J} := by
      rw [disjoint_singleton_right, hΦ0mem]
      exact fun h => h.2 (mem_insert_self v J)
    have hsub : Φ0 ∪ {insert v J} ⊆ Φ := by
      intro I hI
      rw [mem_union, mem_singleton] at hI
      rcases hI with hI | hI
      · exact ((hΦ0mem I).mp hI).1
      · rw [hI]; exact hvmem
    have h1 : ∑ I ∈ Φ0, (I.filter (G.Adj v)).card ≤
        ∑ I ∈ Φ0, ((if v ∈ I then Δ else 0) + (I.filter (G.Adj v)).card) :=
      sum_le_sum fun I _ => Nat.le_add_left _ _
    have h2 : Δ ≤ ∑ I ∈ ({insert v J} : Finset (Finset V)),
        ((if v ∈ I then Δ else 0) + (I.filter (G.Adj v)).card) := by
      rw [sum_singleton, if_pos (mem_insert_self v J)]
      exact Nat.le_add_right _ _
    calc Δ + ∑ I ∈ Φ0, (I.filter (G.Adj v)).card
        ≤ ∑ I ∈ Φ0, ((if v ∈ I then Δ else 0) + (I.filter (G.Adj v)).card) +
          ∑ I ∈ ({insert v J} : Finset (Finset V)),
            ((if v ∈ I then Δ else 0) + (I.filter (G.Adj v)).card) := by omega
      _ = ∑ I ∈ Φ0 ∪ {insert v J}, ((if v ∈ I then Δ else 0) + (I.filter (G.Adj v)).card) :=
          (sum_union hdisj).symm
      _ ≤ ∑ I ∈ Φ, ((if v ∈ I then Δ else 0) + (I.filter (G.Adj v)).card) :=
          sum_le_sum_of_subset hsub
  have hΦle : Φ.card ≤ Φ0.card + 1 := by
    have hsub : Φ ⊆ Φ0 ∪ {insert v J} := by
      intro I hI
      rw [mem_union, mem_singleton]
      by_cases hvI : v ∈ I
      · right
        obtain ⟨-, hIind, hIJ⟩ := (memΦ I).mp hI
        ext u
        rw [mem_insert]
        constructor
        · intro hu
          by_cases huv : u = v
          · exact Or.inl huv
          · right
            rw [← hIJ, mem_filter]
            exact ⟨hu, huv, fun hadj => hIind v hvI u hu hadj⟩
        · rintro (huv | hu)
          · rw [huv]; exact hvI
          · rw [← hIJ, mem_filter] at hu; exact hu.1
      · left; exact (hΦ0mem I).mpr ⟨hI, hvI⟩
    calc Φ.card ≤ (Φ0 ∪ {insert v J}).card := card_le_card hsub
      _ ≤ Φ0.card + ({insert v J} : Finset (Finset V)).card := card_union_le _ _
      _ = Φ0.card + 1 := by rw [card_singleton]
  have hk4 : k ≤ 4 * Δ := by
    calc k = k * 1 := (mul_one k).symm
      _ ≤ k * 2 ^ (2 * q * (lam * (2 * k) + 2)) := Nat.mul_le_mul_left _ Nat.one_le_two_pow
      _ ≤ 4 * Δ := H1
  rcases Nat.lt_or_ge F.card (2 * q * (lam * (2 * k) + 2)) with hx | hx
  · -- few free neighbours: the group is small
    have h1 : Φ.card ≤ 2 ^ (2 * q * (lam * (2 * k) + 2)) := by
      have h2 : (1 : ℕ) ≤ 2 ^ F.card := Nat.one_le_two_pow
      calc Φ.card ≤ Φ0.card + 1 := hΦle
        _ ≤ 2 ^ F.card + 2 ^ F.card := by omega
        _ = 2 ^ (F.card + 1) := by ring
        _ ≤ 2 ^ (2 * q * (lam * (2 * k) + 2)) := Nat.pow_le_pow_right (by norm_num) hx
    calc k * Φ.card ≤ k * 2 ^ (2 * q * (lam * (2 * k) + 2)) := Nat.mul_le_mul_left _ h1
      _ ≤ 4 * Δ := H1
      _ ≤ 4 * (Δ + ∑ I ∈ Φ0, (I.filter (G.Adj v)).card) := by omega
      _ ≤ 4 * ∑ I ∈ Φ, ((if v ∈ I then Δ else 0) + (I.filter (G.Adj v)).card) :=
          Nat.mul_le_mul_left _ hSig
  · -- many free neighbours: most independent subsets are large
    obtain ⟨C, hCF, hCind, hCcard⟩ := a802_colour_class G v q hcol F
      (fun u hu => ((hFmem u).mp hu).2.1)
    have hsmall := a802_small_sets F q (2 * k) lam C.card hq hlam hCcard hx
    have hbig : 2 ^ C.card ≤ Φ0.card := by
      rw [← card_powerset]
      refine card_le_card_of_injOn (fun B : Finset V => J ∪ B) ?_ ?_
      · intro B hB
        rw [mem_coe, mem_powerset] at hB
        have hB' := hput B (hB.trans hCF) (fun a ha b hb => hCind a (hB ha) b (hB hb))
        exact mem_coe.mpr ((hΦ0mem _).mpr ⟨hB'.1, hB'.2.1⟩)
      · intro B hB B' hB' h
        rw [mem_coe, mem_powerset] at hB hB'
        have e1 := (hput B (hB.trans hCF) (fun a ha b hb => hCind a (hB ha) b (hB hb))).2.2
        have e2 := (hput B' (hB'.trans hCF) (fun a ha b hb => hCind a (hB' ha) b (hB' hb))).2.2
        calc B = (J ∪ B).filter (G.Adj v) := e1.symm
          _ = (J ∪ B').filter (G.Adj v) := by rw [show J ∪ B = J ∪ B' from h]
          _ = B' := e2
    have hN : 2 * (Φ0.filter (fun I => (I.filter (G.Adj v)).card < 2 * k)).card ≤ Φ0.card :=
      le_trans (le_trans (Nat.mul_le_mul_left 2 hNle) hsmall) hbig
    have hki : k * Φ0.card ≤ ∑ I ∈ Φ0, (I.filter (G.Adj v)).card := by
      refine le_trans ?_ hsum_ge
      have h3 : Φ0.card ≤
          2 * (Φ0.card - (Φ0.filter (fun I => (I.filter (G.Adj v)).card < 2 * k)).card) := by
        omega
      calc k * Φ0.card
          ≤ k * (2 * (Φ0.card -
              (Φ0.filter (fun I => (I.filter (G.Adj v)).card < 2 * k)).card)) :=
            Nat.mul_le_mul_left _ h3
        _ = 2 * k * (Φ0.card -
              (Φ0.filter (fun I => (I.filter (G.Adj v)).card < 2 * k)).card) := by ring
    calc k * Φ.card ≤ k * (Φ0.card + 1) := Nat.mul_le_mul_left _ hΦle
      _ = k * Φ0.card + k := by ring
      _ ≤ ∑ I ∈ Φ0, (I.filter (G.Adj v)).card + 4 * Δ := Nat.add_le_add hki hk4
      _ ≤ 4 * (Δ + ∑ I ∈ Φ0, (I.filter (G.Adj v)).card) := by omega
      _ ≤ 4 * ∑ I ∈ Φ, ((if v ∈ I then Δ else 0) + (I.filter (G.Adj v)).card) :=
          Nat.mul_le_mul_left _ hSig

/-- Double counting over all independent subsets of `S`. -/
theorem a802_main {V : Type*} (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V)
    (Δ k q lam : ℕ) (hq : 1 ≤ q) (hlam : 4 * q ≤ 2 ^ lam)
    (hcol : ∀ v, (G.induce (G.neighborSet v)).Colorable q)
    (hdeg : ∀ v ∈ S, (S.filter (G.Adj v)).card ≤ Δ)
    (H1 : k * 2 ^ (2 * q * (lam * (2 * k) + 2)) ≤ 4 * Δ) :
    ∃ I ⊆ S, Ind G I ∧ k * S.card ≤ 8 * Δ * I.card := by
  obtain ⟨𝓘, h𝓘⟩ : ∃ 𝓘, 𝓘 = S.powerset.filter (Ind G) := ⟨_, rfl⟩
  have hmem : ∀ I, I ∈ 𝓘 ↔ (I ⊆ S ∧ Ind G I) := by
    intro I; rw [h𝓘, mem_filter, mem_powerset]
  have hne : 𝓘.Nonempty :=
    ⟨∅, (hmem ∅).mpr ⟨empty_subset _, fun a ha => absurd ha (notMem_empty a)⟩⟩
  -- a largest independent subset of `S`
  obtain ⟨I, hI𝓘, hImax⟩ := exists_max_image 𝓘 Finset.card hne
  obtain ⟨hIS, hIind⟩ := (hmem I).mp hI𝓘
  refine ⟨I, hIS, hIind, ?_⟩
  have hv : ∀ v ∈ S, k * 𝓘.card ≤
      4 * ∑ I' ∈ 𝓘, ((if v ∈ I' then Δ else 0) + (I'.filter (G.Adj v)).card) := by
    intro v hv
    have hmaps : (𝓘 : Set (Finset V)).MapsTo
        (fun I' => I'.filter (fun u => u ≠ v ∧ ¬ G.Adj v u))
        (𝓘.image (fun I' => I'.filter (fun u => u ≠ v ∧ ¬ G.Adj v u)) : Finset (Finset V)) :=
      fun I' hI' => mem_coe.mpr (mem_image_of_mem _ hI')
    rw [card_eq_sum_card_fiberwise hmaps, ← sum_fiberwise_of_maps_to hmaps, mul_sum, mul_sum]
    refine sum_le_sum (fun J _ => ?_)
    have h := a802_fiber G S v hv Δ k q lam hq hlam (hcol v) H1 J
    rw [← h𝓘] at h
    exact h
  have hI : ∀ I' ∈ 𝓘, ∑ v ∈ S, ((if v ∈ I' then Δ else 0) + (I'.filter (G.Adj v)).card)
      ≤ 2 * Δ * I.card := by
    intro I' hI'
    obtain ⟨hI'S, -⟩ := (hmem I').mp hI'
    have hle : I'.card ≤ I.card := hImax I' hI'
    rw [sum_add_distrib]
    have h1 : ∑ v ∈ S, (if v ∈ I' then Δ else 0) = I'.card * Δ := by
      rw [← sum_filter, filter_mem_eq_inter, inter_eq_right.mpr hI'S]; simp
    have h2 : ∑ v ∈ S, (I'.filter (G.Adj v)).card = ∑ u ∈ I', (S.filter (G.Adj u)).card := by
      simp only [card_filter]
      rw [sum_comm]
      refine sum_congr rfl fun u _ => sum_congr rfl fun w _ => ?_
      simp only [SimpleGraph.adj_comm]
    have h3 : ∑ u ∈ I', (S.filter (G.Adj u)).card ≤ I'.card * Δ := by
      calc ∑ u ∈ I', (S.filter (G.Adj u)).card ≤ ∑ _u ∈ I', Δ :=
            sum_le_sum fun u hu => hdeg u (hI'S hu)
        _ = I'.card * Δ := by simp
    have h4 : I'.card * Δ ≤ I.card * Δ := Nat.mul_le_mul_right Δ hle
    rw [h1, h2]
    calc I'.card * Δ + ∑ u ∈ I', (S.filter (G.Adj u)).card ≤ I.card * Δ + I.card * Δ := by omega
      _ = 2 * Δ * I.card := by ring
  have htot : S.card * (k * 𝓘.card) ≤ 4 * (𝓘.card * (2 * Δ * I.card)) := by
    calc S.card * (k * 𝓘.card) = ∑ _v ∈ S, k * 𝓘.card := by simp
      _ ≤ ∑ v ∈ S, 4 * ∑ I' ∈ 𝓘, ((if v ∈ I' then Δ else 0) + (I'.filter (G.Adj v)).card) :=
          sum_le_sum hv
      _ = 4 * ∑ I' ∈ 𝓘, ∑ v ∈ S, ((if v ∈ I' then Δ else 0) + (I'.filter (G.Adj v)).card) := by
          rw [← mul_sum, sum_comm]
      _ ≤ 4 * ∑ _I' ∈ 𝓘, 2 * Δ * I.card := Nat.mul_le_mul_left 4 (sum_le_sum hI)
      _ = 4 * (𝓘.card * (2 * Δ * I.card)) := by simp
  have hpos : 0 < 𝓘.card := card_pos.mpr hne
  have hfin : (k * S.card) * 𝓘.card ≤ (8 * Δ * I.card) * 𝓘.card := by
    calc (k * S.card) * 𝓘.card = S.card * (k * 𝓘.card) := by ring
      _ ≤ 4 * (𝓘.card * (2 * Δ * I.card)) := htot
      _ = (8 * Δ * I.card) * 𝓘.card := by ring
  exact Nat.le_of_mul_le_mul_right hfin hpos

/-- A maximum independent subset of `S` dominates `S`. -/
theorem a802_greedy {V : Type*} (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) (Δ : ℕ)
    (hdeg : ∀ v ∈ S, (S.filter (G.Adj v)).card ≤ Δ) :
    ∃ I ⊆ S, Ind G I ∧ S.card ≤ (Δ + 1) * I.card := by
  obtain ⟨𝓘, h𝓘⟩ : ∃ 𝓘, 𝓘 = S.powerset.filter (Ind G) := ⟨_, rfl⟩
  have hmem : ∀ I, I ∈ 𝓘 ↔ (I ⊆ S ∧ Ind G I) := by
    intro I; rw [h𝓘, mem_filter, mem_powerset]
  have hne : 𝓘.Nonempty :=
    ⟨∅, (hmem ∅).mpr ⟨empty_subset _, fun a ha => absurd ha (notMem_empty a)⟩⟩
  obtain ⟨I, hI𝓘, hImax⟩ := exists_max_image 𝓘 Finset.card hne
  obtain ⟨hIS, hIind⟩ := (hmem I).mp hI𝓘
  refine ⟨I, hIS, hIind, ?_⟩
  have hcover : S ⊆ I ∪ I.biUnion (fun u => S.filter (G.Adj u)) := by
    intro v hvS
    by_contra hcon
    rw [mem_union, not_or, mem_biUnion] at hcon
    obtain ⟨hvI, hnadj⟩ := hcon
    have hind : Ind G (insert v I) := by
      intro a ha b hb
      rw [mem_insert] at ha hb
      rcases ha with ha | ha <;> rcases hb with hb | hb
      · rw [ha, hb]; exact G.irrefl
      · rw [ha]; exact fun h => hnadj ⟨b, hb, mem_filter.mpr ⟨hvS, h.symm⟩⟩
      · rw [hb]; exact fun h => hnadj ⟨a, ha, mem_filter.mpr ⟨hvS, h⟩⟩
      · exact hIind a ha b hb
    have h1 := hImax (insert v I) ((hmem _).mpr ⟨insert_subset hvS hIS, hind⟩)
    rw [card_insert_of_notMem hvI] at h1
    omega
  calc S.card ≤ (I ∪ I.biUnion (fun u => S.filter (G.Adj u))).card := card_le_card hcover
    _ ≤ I.card + (I.biUnion (fun u => S.filter (G.Adj u))).card := card_union_le _ _
    _ ≤ I.card + ∑ u ∈ I, (S.filter (G.Adj u)).card := Nat.add_le_add_left card_biUnion_le _
    _ ≤ I.card + ∑ _u ∈ I, Δ :=
        Nat.add_le_add_left (sum_le_sum fun u hu => hdeg u (hIS hu)) _
    _ = (Δ + 1) * I.card := by rw [sum_const, smul_eq_mul]; ring

/-- The bound for a graph on an arbitrary finite vertex type. -/
theorem a802_core {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (q lam : ℕ) (hq : 1 ≤ q) (hlam : 4 * q ≤ 2 ^ lam)
    (hcol : ∀ v, (G.induce (G.neighborSet v)).Colorable q) :
    (1 / (40 * ((4 * q * lam + 4 * q + 1 : ℕ) : ℝ))) *
      (Real.log G.averageDegree / G.averageDegree) * Fintype.card V ≤ G.indepNum := by
  obtain ⟨M, hM⟩ : ∃ M : ℕ, M = 4 * q * lam + 4 * q + 1 := ⟨_, rfl⟩
  rw [← hM]
  have hMpos : 0 < M := by omega
  have hMR : (0 : ℝ) < M := by exact_mod_cast hMpos
  have hM0 : (M : ℝ) ≠ 0 := hMR.ne'
  have havg0 : (0 : ℚ) ≤ G.averageDegree := by
    unfold SimpleGraph.averageDegree; positivity
  obtain ⟨t, htdef⟩ : ∃ t : ℝ, t = (G.averageDegree : ℝ) := ⟨_, rfl⟩
  rw [← htdef]
  have ht0 : 0 ≤ t := by rw [htdef]; exact_mod_cast havg0
  have hα0 : (0 : ℝ) ≤ G.indepNum := by positivity
  have hn0 : (0 : ℝ) ≤ Fintype.card V := by positivity
  rcases le_or_gt t 1 with ht1 | ht1
  · -- the left side is not positive
    have hlog : Real.log t / t ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg (Real.log_nonpos ht0 ht1) ht0
    have hc : 0 ≤ (1 / (40 * (M : ℝ))) := by positivity
    have h1 : (1 / (40 * (M : ℝ))) * (Real.log t / t) * Fintype.card V ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos hc hlog) hn0
    exact le_trans h1 hα0
  · have htpos : 0 < t := by linarith
    have htne : t ≠ 0 := htpos.ne'
    obtain ⟨D, hD⟩ : ∃ D : ℕ, D = ⌊2 * t⌋₊ := ⟨_, rfl⟩
    have hDle : (D : ℝ) ≤ 2 * t := by rw [hD]; exact Nat.floor_le (by linarith)
    have hDlt : 2 * t < D + 1 := by rw [hD]; exact Nat.lt_floor_add_one _
    have hD2 : 2 ≤ D := by rw [hD]; exact Nat.le_floor (by push_cast; linarith)
    have hn : (0 : ℝ) < Fintype.card V := by
      rw [Nat.cast_pos, Fintype.card_pos_iff]
      by_contra hemp
      rw [not_nonempty_iff] at hemp
      have h0 : G.averageDegree = 0 := by simp [SimpleGraph.averageDegree]
      rw [htdef, h0] at ht1
      norm_num at ht1
    have hsum : (∑ v, (G.degree v : ℝ)) = t * Fintype.card V := by
      rw [htdef, SimpleGraph.averageDegree]; push_cast; field_simp
    -- the vertices of small degree
    obtain ⟨S, hS⟩ : ∃ S : Finset V, S = univ.filter (fun v => G.degree v ≤ D) := ⟨_, rfl⟩
    have hSmem : ∀ v, v ∈ S ↔ G.degree v ≤ D := by
      intro v; rw [hS, mem_filter]; simp
    have hSn : Fintype.card V ≤ 2 * S.card := by
      have hc : S.card + (univ.filter (fun v => ¬ G.degree v ≤ D)).card = Fintype.card V := by
        rw [hS, card_filter_add_card_filter_not, card_univ]
      have h1 : ((univ.filter (fun v => ¬ G.degree v ≤ D)).card : ℝ) * (2 * t) ≤
          t * Fintype.card V := by
        rw [← hsum]
        calc ((univ.filter (fun v => ¬ G.degree v ≤ D)).card : ℝ) * (2 * t)
            = ∑ _v ∈ univ.filter (fun v => ¬ G.degree v ≤ D), (2 * t) := by simp
          _ ≤ ∑ v ∈ univ.filter (fun v => ¬ G.degree v ≤ D), (G.degree v : ℝ) := by
              refine sum_le_sum fun v hv => ?_
              have h := (mem_filter.mp hv).2
              have h' : (D : ℝ) + 1 ≤ G.degree v := by
                exact_mod_cast (by omega : D + 1 ≤ G.degree v)
              linarith
          _ ≤ ∑ v, (G.degree v : ℝ) :=
              sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun _ _ _ => by positivity)
      have h2 : ((univ.filter (fun v => ¬ G.degree v ≤ D)).card : ℝ) * 2 ≤ Fintype.card V := by
        nlinarith
      have h3 : (Fintype.card V : ℝ) ≤ 2 * S.card := by
        have h4 : ((S.card + (univ.filter (fun v => ¬ G.degree v ≤ D)).card : ℕ) : ℝ) =
            Fintype.card V := by rw [hc]
        push_cast at h4; linarith
      exact_mod_cast h3
    have hdeg : ∀ v ∈ S, (S.filter (G.Adj v)).card ≤ D := by
      intro v hv
      calc (S.filter (G.Adj v)).card ≤ (univ.filter (G.Adj v)).card :=
            card_le_card (filter_subset_filter _ (subset_univ _))
        _ = G.degree v := by
            rw [← SimpleGraph.card_neighborFinset_eq_degree]
            congr 1
            ext w
            simp
        _ ≤ D := (hSmem v).mp hv
    -- the gain `k`, of order `log D`
    obtain ⟨l, hl⟩ : ∃ l, l = Nat.log 2 D := ⟨_, rfl⟩
    obtain ⟨k, hk⟩ : ∃ k, k = l / M := ⟨_, rfl⟩
    have hD0 : D ≠ 0 := by omega
    have h2l : 2 ^ l ≤ D := by rw [hl]; exact Nat.pow_log_le_self 2 hD0
    have hDl : D < 2 ^ (l + 1) := by rw [hl]; exact Nat.lt_pow_succ_log_self (by norm_num) D
    have hkM : k * M ≤ l := by rw [hk]; exact Nat.div_mul_le_self l M
    have hlk : l < M * (k + 1) := by rw [hk]; exact Nat.lt_mul_div_succ l hMpos
    have H1 : k * 2 ^ (2 * q * (lam * (2 * k) + 2)) ≤ 4 * D := by
      rcases Nat.eq_zero_or_pos k with hk0 | hk1
      · rw [hk0]; simp
      · have hkk : k ≤ 2 ^ k := Nat.lt_two_pow_self.le
        have e3 : 4 * q ≤ 4 * q * k := Nat.le_mul_of_pos_right _ hk1
        have hexp : k + 2 * q * (lam * (2 * k) + 2) ≤ l := by
          calc k + 2 * q * (lam * (2 * k) + 2) = k * (4 * q * lam + 1) + 4 * q := by ring
            _ ≤ k * (4 * q * lam + 1) + 4 * q * k := Nat.add_le_add_left e3 _
            _ = k * M := by rw [hM]; ring
            _ ≤ l := hkM
        calc k * 2 ^ (2 * q * (lam * (2 * k) + 2))
            ≤ 2 ^ k * 2 ^ (2 * q * (lam * (2 * k) + 2)) := Nat.mul_le_mul_right _ hkk
          _ = 2 ^ (k + 2 * q * (lam * (2 * k) + 2)) := by rw [pow_add]
          _ ≤ 2 ^ l := Nat.pow_le_pow_right (by norm_num) hexp
          _ ≤ D := h2l
          _ ≤ 4 * D := by omega
    obtain ⟨I, -, hIind, hIk⟩ := a802_main G S D k q lam hq hlam hcol hdeg H1
    obtain ⟨I', -, hI'ind, hI'g⟩ := a802_greedy G S D hdeg
    have hα : ∀ I : Finset V, Ind G I → I.card ≤ G.indepNum := by
      intro I hI
      have hind : G.IsIndepSet (I : Set V) := fun a ha b hb _ => hI a ha b hb
      exact hind.card_le_indepNum
    have hIα := hα I hIind
    have hI'α := hα I' hI'ind
    have key : (k + 1) * Fintype.card V ≤ 20 * D * G.indepNum := by
      have a1 : k * S.card ≤ 8 * D * G.indepNum := le_trans hIk (Nat.mul_le_mul_left _ hIα)
      have a2 : S.card ≤ (D + 1) * G.indepNum := le_trans hI'g (Nat.mul_le_mul_left _ hI'α)
      calc (k + 1) * Fintype.card V ≤ (k + 1) * (2 * S.card) := Nat.mul_le_mul_left _ hSn
        _ = 2 * (k * S.card) + 2 * S.card := by ring
        _ ≤ 2 * (8 * D * G.indepNum) + 2 * ((D + 1) * G.indepNum) :=
            Nat.add_le_add (Nat.mul_le_mul_left _ a1) (Nat.mul_le_mul_left _ a2)
        _ = (18 * D + 2) * G.indepNum := by ring
        _ ≤ 20 * D * G.indepNum := Nat.mul_le_mul_right _ (by omega)
    have hlogt : Real.log t ≤ ((k : ℝ) + 1) * M := by
      have h1 : t < (2 : ℝ) ^ l := by
        have h2 : (D : ℝ) + 1 ≤ (2 : ℝ) ^ (l + 1) := by
          exact_mod_cast Nat.succ_le_of_lt hDl
        have h3 : (2 : ℝ) ^ (l + 1) = 2 * 2 ^ l := by ring
        linarith
      have h4 : Real.log t < Real.log ((2 : ℝ) ^ l) := Real.log_lt_log htpos h1
      have h5 : Real.log ((2 : ℝ) ^ l) = l * Real.log 2 := by rw [Real.log_pow]
      have h6 : Real.log 2 ≤ 1 := by
        have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
        linarith
      have h7 : (l : ℝ) * Real.log 2 ≤ l := by
        have h : (0 : ℝ) ≤ l := by positivity
        nlinarith
      have h8 : (l : ℝ) < (M : ℝ) * ((k : ℝ) + 1) := by exact_mod_cast hlk
      linarith
    have keyR : ((k : ℝ) + 1) * Fintype.card V ≤ 20 * D * G.indepNum := by
      exact_mod_cast key
    rw [show (1 / (40 * (M : ℝ))) * (Real.log t / t) * (Fintype.card V : ℝ) =
      (Real.log t * Fintype.card V) / (40 * M * t) by field_simp]
    rw [div_le_iff₀ (by positivity)]
    calc Real.log t * Fintype.card V ≤ (((k : ℝ) + 1) * M) * Fintype.card V :=
          mul_le_mul_of_nonneg_right hlogt hn0
      _ = M * (((k : ℝ) + 1) * Fintype.card V) := by ring
      _ ≤ M * (20 * D * G.indepNum) := mul_le_mul_of_nonneg_left keyR hMR.le
      _ ≤ M * (20 * (2 * t) * G.indepNum) := by
          have h9 : (20 : ℝ) * D * G.indepNum ≤ 20 * (2 * t) * G.indepNum := by
            have h10 : (20 : ℝ) * D ≤ 20 * (2 * t) := by linarith
            exact mul_le_mul_of_nonneg_right h10 hα0
          exact mul_le_mul_of_nonneg_left h9 hMR.le
      _ = G.indepNum * (40 * M * t) := by ring

end OMA

theorem OMA.solution : type_of% @Erdos802.erdos_802.variants.alon := by
  classical
  intro r
  obtain ⟨q, hq, hqr⟩ : ∃ q, 1 ≤ q ∧ r - 2 ≤ q := ⟨r - 2 + 1, by omega, by omega⟩
  have hlam : 4 * q ≤ 2 ^ (4 * q) := Nat.lt_two_pow_self.le
  refine ⟨1 / (40 * ((4 * q * (4 * q) + 4 * q + 1 : ℕ) : ℝ)), by positivity, ?_⟩
  intro n G hcol
  have h := OMA.a802_core G q (4 * q) hq hlam (fun v => (hcol v).mono hqr)
  simpa using h
