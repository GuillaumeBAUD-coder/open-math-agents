import OMAReductions.R_Erdos562_erdos_562_R1
import Mathlib

/-! The Erdős--Rado upper bound for hypergraph Ramsey numbers: the (r-1)-fold iterated logarithm
of R_r(n) is O(n).

Stepping up. Given a 2-colouring of the (r+1)-subsets of N = 2 ^ ((M^(r-1) + 1) (M + 1)) points,
choose vertices one at a time, each time the least remaining candidate v, and keep the largest
class of candidates w with the same colour pattern on the sets T ∪ {v, w}, T an (r-1)-subset of
the vertices chosen so far. There are at most 2 ^ (M^(r-1)) patterns, so M + 1 vertices can be
chosen, and the colour of an (r+1)-subset of them depends only on its r smallest elements. If
every colouring of the r-subsets of M points has a monochromatic n-set, this gives a
monochromatic (n+1)-set: R_{r+1}(n+1) <= 2 ^ ((M^(r-1) + 1) (M + 1)).

Towers. Starting from R_1(n) <= 2 n, the bound on R_2 is exponential in n, and each further
step adds one exponential: log log R_{r+1} <= (r + 2) log M, and an additive constant survives
any number of further logarithms once the arguments are above the corresponding tower. -/

open Finset

namespace ER562

/-- `Ram r n m`: every 2-colouring of the subsets of `Fin m` has a set of size `n` all of whose
`r`-subsets have the same colour. -/
def Ram (r n m : ℕ) : Prop :=
  ∀ c : Finset (Fin m) → Bool, ∃ S : Finset (Fin m), S.card = n ∧
    ∃ color : Bool, ∀ e : Finset (Fin m), e ⊆ S → e.card = r → c e = color

/-- End-homogeneity: the colour of `insert x T` for an `r`-subset `T` of `L` does not depend on
the element `x` of `L ∪ S` lying above `T`. -/
def EndHom {N : ℕ} (χ : Finset (Fin N) → Bool) (r : ℕ) (L S : Finset (Fin N)) : Prop :=
  ∀ T : Finset (Fin N), T ⊆ L → T.card = r → ∀ x ∈ L ∪ S, ∀ x' ∈ L ∪ S,
    (∀ t ∈ T, t < x) → (∀ t ∈ T, t < x') → χ (insert x T) = χ (insert x' T)

lemma greedy {N : ℕ} (χ : Finset (Fin N) → Bool) (r K M : ℕ) (hr : 1 ≤ r)
    (hK : ∀ i ≤ M, i.choose (r - 1) ≤ K) (hN : N = 2 ^ ((K + 1) * (M + 1))) :
    ∀ i ≤ M + 1, ∃ L S : Finset (Fin N), L.card = i ∧ 2 ^ ((K + 1) * (M + 1 - i)) ≤ S.card ∧
      (∀ a ∈ L, ∀ b ∈ S, a < b) ∧ EndHom χ r L S := by
  intro i
  induction i with
  | zero =>
    intro _
    refine ⟨∅, univ, rfl, ?_, ?_, ?_⟩
    · rw [Finset.card_univ, Fintype.card_fin, Nat.sub_zero]
      exact hN.ge
    · intro a ha
      simp at ha
    · intro T hT hcard
      have hT0 : T = ∅ := Finset.subset_empty.mp hT
      rw [hT0, Finset.card_empty] at hcard
      omega
  | succ i ih =>
    intro hi
    obtain ⟨L, S, hL, hS, hLS, hEH⟩ := ih (by omega)
    have hpos : 0 < S.card := lt_of_lt_of_le (by positivity) hS
    have hSne : S.Nonempty := Finset.card_pos.mp hpos
    obtain ⟨v, hvdef⟩ : ∃ v, v = S.min' hSne := ⟨_, rfl⟩
    have hvS : v ∈ S := by
      rw [hvdef]
      exact Finset.min'_mem S hSne
    have hvmin : ∀ b ∈ S, v ≤ b := by
      intro b hb
      rw [hvdef]
      exact Finset.min'_le S b hb
    have hvL : v ∉ L := fun h => lt_irrefl v (hLS v h v hvS)
    obtain ⟨τ, hτ⟩ : ∃ τ : Fin N → Finset (Finset (Fin N)), ∀ w, τ w =
        (L.powersetCard (r - 1)).filter (fun T => χ (insert w (insert v T)) = true) :=
      ⟨_, fun _ => rfl⟩
    have hmaps : ∀ w ∈ S.erase v, τ w ∈ (L.powersetCard (r - 1)).powerset := by
      intro w _
      rw [hτ]
      exact Finset.mem_powerset.mpr (Finset.filter_subset _ _)
    have hcardt : ((L.powersetCard (r - 1)).powerset).card ≤ 2 ^ K := by
      rw [Finset.card_powerset, Finset.card_powersetCard, hL]
      exact Nat.pow_le_pow_right (by norm_num) (hK i (by omega))
    obtain ⟨a, ha⟩ : ∃ a, a = (K + 1) * (M - i) := ⟨_, rfl⟩
    have hexp : (K + 1) * (M + 1 - i) = a + K + 1 := by
      have h1 : M + 1 - i = (M - i) + 1 := by omega
      rw [ha, h1]
      ring
    have hexp' : (K + 1) * (M + 1 - (i + 1)) = a := by
      have h1 : M + 1 - (i + 1) = M - i := by omega
      rw [ha, h1]
    rw [hexp] at hS
    have h1a : 1 ≤ 2 ^ a := Nat.one_le_two_pow
    have h1K : 1 ≤ 2 ^ K := Nat.one_le_two_pow
    have h2 : 2 ^ K * (2 ^ a - 1) + 2 ^ K = 2 ^ (a + K) := by
      calc 2 ^ K * (2 ^ a - 1) + 2 ^ K = 2 ^ K * ((2 ^ a - 1) + 1) := by ring
        _ = 2 ^ K * 2 ^ a := by rw [Nat.sub_add_cancel h1a]
        _ = 2 ^ (a + K) := by rw [pow_add]; ring
    have h3 : 2 ^ (a + K + 1) = 2 * 2 ^ (a + K) := by
      rw [pow_succ]
      ring
    have hlt : ((L.powersetCard (r - 1)).powerset).card * (2 ^ a - 1) < (S.erase v).card := by
      rw [Finset.card_erase_of_mem hvS]
      have h1 : ((L.powersetCard (r - 1)).powerset).card * (2 ^ a - 1) ≤ 2 ^ K * (2 ^ a - 1) :=
        Nat.mul_le_mul_right _ hcardt
      have h4 : 1 ≤ 2 ^ (a + K) := Nat.one_le_two_pow
      omega
    obtain ⟨y, hy, hfiber⟩ :=
      Finset.exists_lt_card_fiber_of_mul_lt_card_of_maps_to hmaps hlt
    refine ⟨insert v L, (S.erase v).filter (fun w => τ w = y), ?_, ?_, ?_, ?_⟩
    · rw [Finset.card_insert_of_notMem hvL, hL]
    · rw [hexp']
      omega
    · intro a' ha' b hb
      rw [Finset.mem_filter, Finset.mem_erase] at hb
      rcases Finset.mem_insert.mp ha' with rfl | h
      · exact lt_of_le_of_ne (hvmin b hb.1.2) (Ne.symm hb.1.1)
      · exact hLS a' h b hb.1.2
    · intro T hT hcard x hx x' hx' hTx hTx'
      have hsubU : insert v L ∪ (S.erase v).filter (fun w => τ w = y) ⊆ L ∪ S := by
        intro z hz
        rcases Finset.mem_union.mp hz with h | h
        · rcases Finset.mem_insert.mp h with rfl | h'
          · exact Finset.mem_union_right _ hvS
          · exact Finset.mem_union_left _ h'
        · exact Finset.mem_union_right _ (Finset.mem_of_mem_erase (Finset.mem_filter.mp h).1)
      by_cases hvT : v ∈ T
      · have hxS : ∀ z ∈ insert v L ∪ (S.erase v).filter (fun w => τ w = y),
            (∀ t ∈ T, t < z) → τ z = y := by
          intro z hz hTz
          have hvz : v < z := hTz v hvT
          rcases Finset.mem_union.mp hz with h | h
          · rcases Finset.mem_insert.mp h with rfl | h'
            · exact absurd hvz (lt_irrefl _)
            · exact absurd (hLS z h' v hvS) (not_lt.mpr hvz.le)
          · exact (Finset.mem_filter.mp h).2
        have hτx := hxS x hx hTx
        have hτx' := hxS x' hx' hTx'
        have hT0 : T.erase v ∈ L.powersetCard (r - 1) := by
          rw [Finset.mem_powersetCard]
          refine ⟨?_, ?_⟩
          · intro t ht
            rcases Finset.mem_insert.mp (hT (Finset.mem_of_mem_erase ht)) with h | h
            · exact absurd h (Finset.ne_of_mem_erase ht)
            · exact h
          · rw [Finset.card_erase_of_mem hvT, hcard]
        have hins : insert v (T.erase v) = T := Finset.insert_erase hvT
        have hmem : T.erase v ∈ τ x ↔ T.erase v ∈ τ x' := by rw [hτx, hτx']
        rw [hτ, hτ, Finset.mem_filter, Finset.mem_filter, hins] at hmem
        have hiff : (χ (insert x T) = true) ↔ (χ (insert x' T) = true) := by
          constructor
          · intro h
            exact (hmem.mp ⟨hT0, h⟩).2
          · intro h
            exact (hmem.mpr ⟨hT0, h⟩).2
        exact Bool.eq_iff_iff.mpr hiff
      · have hTL : T ⊆ L := by
          intro t ht
          rcases Finset.mem_insert.mp (hT ht) with h | h
          · exact absurd (h ▸ ht) hvT
          · exact h
        exact hEH T hTL hcard x (hsubU hx) x' (hsubU hx') hTx hTx'


/-- The Erdős--Rado stepping-up inequality. -/
lemma step (r n M : ℕ) (hr : 1 ≤ r) (hM : Ram r n M) :
    Ram (r + 1) (n + 1) (2 ^ ((M ^ (r - 1) + 1) * (M + 1))) := by
  intro χ
  obtain ⟨L, S, hL, -, -, hEH⟩ := greedy χ r (M ^ (r - 1)) M hr
    (fun i hi => (Nat.choose_le_pow i (r - 1)).trans (Nat.pow_le_pow_left hi _)) rfl
    (M + 1) le_rfl
  have hLne : L.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨vl, hvldef⟩ : ∃ vl, vl = L.max' hLne := ⟨_, rfl⟩
  have hvlL : vl ∈ L := by
    rw [hvldef]
    exact Finset.max'_mem L hLne
  have hvlmax : ∀ t ∈ L, t ≤ vl := by
    intro t ht
    rw [hvldef]
    exact Finset.le_max' L t ht
  have hL0 : (L.erase vl).card = M := by
    rw [Finset.card_erase_of_mem hvlL, hL]
    rfl
  obtain ⟨emb, hemb⟩ : ∃ emb : Fin M ↪ Fin (2 ^ ((M ^ (r - 1) + 1) * (M + 1))),
      ∀ j, emb j ∈ L.erase vl :=
    ⟨((L.erase vl).orderEmbOfFin hL0).toEmbedding,
      fun j => Finset.orderEmbOfFin_mem (L.erase vl) hL0 j⟩
  obtain ⟨S', hS'card, b, hb⟩ := hM (fun T => χ (insert vl (T.map emb)))
  have hmapL : ∀ t ∈ S'.map emb, t ∈ L ∧ t ≠ vl := by
    intro t ht
    obtain ⟨j, _, rfl⟩ := Finset.mem_map.mp ht
    exact ⟨Finset.mem_of_mem_erase (hemb j), Finset.ne_of_mem_erase (hemb j)⟩
  refine ⟨insert vl (S'.map emb), ?_, b, ?_⟩
  · rw [Finset.card_insert_of_notMem, Finset.card_map, hS'card]
    intro h
    exact (hmapL vl h).2 rfl
  · intro e he hecard
    have hene : e.Nonempty := Finset.card_pos.mp (by omega)
    obtain ⟨x, hxdef⟩ : ∃ x, x = e.max' hene := ⟨_, rfl⟩
    have hxe : x ∈ e := by
      rw [hxdef]
      exact Finset.max'_mem e hene
    have hxmax : ∀ t ∈ e, t ≤ x := by
      intro t ht
      rw [hxdef]
      exact Finset.le_max' e t ht
    have hHL : ∀ t ∈ insert vl (S'.map emb), t ∈ L := by
      intro t ht
      rcases Finset.mem_insert.mp ht with h | h
      · rw [h]
        exact hvlL
      · exact (hmapL t h).1
    have hxL : x ∈ L := hHL x (he hxe)
    have hT : ∀ t ∈ e.erase x, t ∈ S'.map emb := by
      intro t ht
      have hte : t ∈ e := Finset.mem_of_mem_erase ht
      rcases Finset.mem_insert.mp (he hte) with h | h
      · exfalso
        have h1 : t ≤ x := hxmax t hte
        have h2 : x ≤ t := by
          rw [h]
          exact hvlmax x hxL
        exact (Finset.ne_of_mem_erase ht) (le_antisymm h1 h2)
      · exact h
    obtain ⟨u, huS, hu⟩ := Finset.subset_map_iff.mp
      (show e.erase x ⊆ S'.map emb from fun t ht => hT t ht)
    have hTcard : (e.erase x).card = r := by
      rw [Finset.card_erase_of_mem hxe, hecard]
      rfl
    have hucard : u.card = r := by
      rw [hu, Finset.card_map] at hTcard
      exact hTcard
    have hcu : χ (insert vl (u.map emb)) = b := hb u huS hucard
    have hins : insert x (e.erase x) = e := Finset.insert_erase hxe
    have hTx : ∀ t ∈ e.erase x, t < x := fun t ht =>
      lt_of_le_of_ne (hxmax t (Finset.mem_of_mem_erase ht)) (Finset.ne_of_mem_erase ht)
    have hTvl : ∀ t ∈ e.erase x, t < vl := fun t ht =>
      lt_of_le_of_ne (hvlmax t (hmapL t (hT t ht)).1) (hmapL t (hT t ht)).2
    have hTL : e.erase x ⊆ L := fun t ht => (hmapL t (hT t ht)).1
    have hkey := hEH (e.erase x) hTL hTcard x (Finset.mem_union_left _ hxL) vl
      (Finset.mem_union_left _ hvlL) hTx hTvl
    rw [hins] at hkey
    rw [hkey, hu]
    exact hcu

/-- The pigeonhole principle: the case `r = 1`. -/
lemma ram_one (n : ℕ) : Ram 1 n (2 * n) := by
  intro c
  classical
  by_cases h : n ≤ (univ.filter (fun v : Fin (2 * n) => c {v} = true)).card
  · obtain ⟨S, hS, hcard⟩ := Finset.exists_subset_card_eq h
    refine ⟨S, hcard, true, ?_⟩
    intro e he hec
    obtain ⟨v, rfl⟩ := Finset.card_eq_one.mp hec
    exact (Finset.mem_filter.mp (hS (he (Finset.mem_singleton_self v)))).2
  · have hsplit := Finset.card_filter_add_card_filter_not
      (s := (univ : Finset (Fin (2 * n)))) (fun v : Fin (2 * n) => c {v} = true)
    rw [Finset.card_univ, Fintype.card_fin] at hsplit
    have h' : n ≤ (univ.filter (fun v : Fin (2 * n) => ¬ c {v} = true)).card := by omega
    obtain ⟨S, hS, hcard⟩ := Finset.exists_subset_card_eq h'
    refine ⟨S, hcard, false, ?_⟩
    intro e he hec
    obtain ⟨v, rfl⟩ := Finset.card_eq_one.mp hec
    have := (Finset.mem_filter.mp (hS (he (Finset.mem_singleton_self v)))).2
    simpa using this


lemma ram_le {r n m : ℕ} (h : Ram r n m) : n ≤ m := by
  obtain ⟨S, hS, -⟩ := h (fun _ => true)
  have h1 := Finset.card_le_univ S
  rw [Fintype.card_fin, hS] at h1
  exact h1

lemma one_le_tower (k : ℕ) : (1 : ℝ) ≤ Real.exp^[k] 1 := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    linarith [Real.add_one_le_exp (Real.exp^[k] 1)]

lemma tower_le_succ (k : ℕ) : Real.exp^[k] 1 ≤ Real.exp^[k + 1] 1 := by
  rw [Function.iterate_succ_apply']
  linarith [Real.add_one_le_exp (Real.exp^[k] 1)]

lemma tower_mono {j k : ℕ} (h : j ≤ k) : Real.exp^[j] 1 ≤ Real.exp^[k] 1 :=
  monotone_nat_of_le_succ tower_le_succ h

/-- Iterated logarithms are monotone above the corresponding tower. -/
lemma ilog_mono (k : ℕ) : ∀ x y : ℝ, Real.exp^[k] 1 ≤ x → x ≤ y →
    1 ≤ Real.log^[k] x ∧ Real.log^[k] x ≤ Real.log^[k] y := by
  induction k with
  | zero =>
    intro x y hx hxy
    simpa using ⟨hx, hxy⟩
  | succ k ih =>
    intro x y hx hxy
    rw [Function.iterate_succ_apply'] at hx
    have hxpos : 0 < x := lt_of_lt_of_le (Real.exp_pos _) hx
    have h1 : Real.exp^[k] 1 ≤ Real.log x := (Real.le_log_iff_exp_le hxpos).mpr hx
    have h2 : Real.log x ≤ Real.log y := Real.log_le_log hxpos hxy
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply]
    exact ih _ _ h1 h2

/-- An additive constant survives further logarithms. -/
lemma ilog_shift (k : ℕ) : ∀ a : ℝ, 0 ≤ a → ∀ x y : ℝ, Real.exp^[k] 1 ≤ x →
    Real.exp^[k] 1 ≤ y → Real.log x ≤ a + Real.log y →
    Real.log^[k + 1] x ≤ a + Real.log^[k + 1] y := by
  induction k with
  | zero =>
    intro a ha x y _ _ h
    simpa using h
  | succ k ih =>
    intro a ha x y hx hy h
    rw [Function.iterate_succ_apply'] at hx hy
    have hxpos : 0 < x := lt_of_lt_of_le (Real.exp_pos _) hx
    have hypos : 0 < y := lt_of_lt_of_le (Real.exp_pos _) hy
    have hx1 : Real.exp^[k] 1 ≤ Real.log x := (Real.le_log_iff_exp_le hxpos).mpr hx
    have hy1 : Real.exp^[k] 1 ≤ Real.log y := (Real.le_log_iff_exp_le hypos).mpr hy
    have hly1 : 1 ≤ Real.log y := (one_le_tower k).trans hy1
    have hlxpos : 0 < Real.log x := lt_of_lt_of_le one_pos ((one_le_tower k).trans hx1)
    have hkey : Real.log (Real.log x) ≤ a + Real.log (Real.log y) := by
      have h1 : Real.log (Real.log x) ≤ Real.log (a + Real.log y) := Real.log_le_log hlxpos h
      have h2 : a + Real.log y ≤ Real.log y * Real.exp a := by
        nlinarith [mul_nonneg (sub_nonneg.mpr hly1) ha,
          mul_nonneg (le_trans zero_le_one hly1) (sub_nonneg.mpr (Real.add_one_le_exp a))]
      have h3 : Real.log (a + Real.log y) ≤ Real.log (Real.log y * Real.exp a) :=
        Real.log_le_log (by linarith) h2
      rw [Real.log_mul (by linarith) (Real.exp_pos a).ne', Real.log_exp] at h3
      linarith
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply]
    exact ih a ha _ _ hx1 hy1 hkey

/-- The tower bound for `r`-sets: some `m` with the Ramsey property has `(r-1)`-fold iterated
logarithm at most `C * n`. -/
def Bound (r : ℕ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∃ n0 : ℕ, ∀ n : ℕ, n0 ≤ n → ∃ m : ℕ, Ram r n m ∧
    Real.log^[r - 1] (m : ℝ) ≤ C * n

lemma log_two_pow (E : ℕ) : Real.log ((2 ^ E : ℕ) : ℝ) = E * Real.log 2 := by
  push_cast
  rw [Real.log_pow]

lemma log_two_le_one : Real.log 2 ≤ 1 := by
  have := Real.log_two_lt_d9
  linarith

lemma bound_two : Bound 2 := by
  refine ⟨4, by norm_num, 1, ?_⟩
  intro n hn
  have hstep := step 1 (n - 1) (2 * (n - 1)) le_rfl (ram_one (n - 1))
  rw [Nat.sub_add_cancel hn] at hstep
  refine ⟨_, hstep, ?_⟩
  show Real.log^[1] _ ≤ _
  rw [Function.iterate_one, log_two_pow]
  have hl := log_two_le_one
  have hl0 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hE : (((2 * (n - 1)) ^ (1 - 1) + 1) * (2 * (n - 1) + 1) : ℕ) ≤ 4 * n := by
    simp only [Nat.sub_self, pow_zero]
    omega
  have hE' : ((((2 * (n - 1)) ^ (1 - 1) + 1) * (2 * (n - 1) + 1) : ℕ) : ℝ) ≤ 4 * n := by
    exact_mod_cast hE
  calc ((((2 * (n - 1)) ^ (1 - 1) + 1) * (2 * (n - 1) + 1) : ℕ) : ℝ) * Real.log 2
      ≤ ((((2 * (n - 1)) ^ (1 - 1) + 1) * (2 * (n - 1) + 1) : ℕ) : ℝ) * 1 :=
        mul_le_mul_of_nonneg_left hl (Nat.cast_nonneg _)
    _ ≤ 4 * n := by rw [mul_one]; exact hE'


lemma bound_three : Bound 3 := by
  obtain ⟨C, hC, n0, h⟩ := bound_two
  refine ⟨4 * C, by positivity, max (n0 + 1) 3, ?_⟩
  intro n hn
  have hn1 : n0 + 1 ≤ n := le_trans (le_max_left _ _) hn
  have hn3 : 3 ≤ n := le_trans (le_max_right _ _) hn
  obtain ⟨M, hM, hMlog⟩ := h (n - 1) (by omega)
  have hstep := step 2 (n - 1) M (by norm_num) hM
  rw [Nat.sub_add_cancel (by omega : 1 ≤ n)] at hstep
  refine ⟨_, hstep, ?_⟩
  have hM2 : 2 ≤ M := le_trans (by omega) (ram_le hM)
  have hMlog' : Real.log (M : ℝ) ≤ C * ((n - 1 : ℕ) : ℝ) := hMlog
  obtain ⟨E, hE⟩ : ∃ E : ℕ, E = (M ^ (2 - 1) + 1) * (M + 1) := ⟨_, rfl⟩
  rw [← hE]
  show Real.log^[2] _ ≤ _
  rw [Function.iterate_succ_apply, Function.iterate_one, log_two_pow]
  have hE_le : E ≤ M ^ 4 := by
    rw [hE]
    have h1 : M + 1 ≤ M ^ 2 := by nlinarith
    calc (M ^ (2 - 1) + 1) * (M + 1) = (M + 1) * (M + 1) := by norm_num
      _ ≤ M ^ 2 * M ^ 2 := Nat.mul_le_mul h1 h1
      _ = M ^ 4 := by ring
  have hE_pos : 1 ≤ E := by
    rw [hE]
    exact Nat.one_le_iff_ne_zero.mpr (by positivity)
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hl2' := log_two_le_one
  have hMpos : (0 : ℝ) < M := by exact_mod_cast (by omega : 0 < M)
  have hEr : (1 : ℝ) ≤ E := by exact_mod_cast hE_pos
  have hpos : 0 < (E : ℝ) * Real.log 2 := by positivity
  have hle : (E : ℝ) * Real.log 2 ≤ (M : ℝ) ^ 4 := by
    have h1 : (E : ℝ) ≤ (M : ℝ) ^ 4 := by exact_mod_cast hE_le
    nlinarith
  have h2 := Real.log_le_log hpos hle
  rw [Real.log_pow] at h2
  have hn' : ((n - 1 : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast Nat.sub_le n 1
  have h3 : C * ((n - 1 : ℕ) : ℝ) ≤ C * n := mul_le_mul_of_nonneg_left hn' hC
  push_cast at h2
  linarith

lemma bound_succ (k : ℕ) (hB : Bound (k + 3)) : Bound (k + 4) := by
  obtain ⟨C, hC, n0, h⟩ := hB
  have hk5 : (1 : ℝ) ≤ (k : ℝ) + 5 := by linarith [Nat.cast_nonneg (α := ℝ) k]
  have ha : 0 ≤ Real.log ((k : ℝ) + 5) := Real.log_nonneg hk5
  refine ⟨C + Real.log ((k : ℝ) + 5), by linarith,
    max (n0 + 1) (⌈Real.exp^[k + 4] 1⌉₊ + 3), ?_⟩
  intro n hn
  have hn1 : n0 + 1 ≤ n := le_trans (le_max_left _ _) hn
  have hn2 : ⌈Real.exp^[k + 4] 1⌉₊ + 3 ≤ n := le_trans (le_max_right _ _) hn
  obtain ⟨M, hM, hMlog⟩ := h (n - 1) (by omega)
  have hstep := step (k + 3) (n - 1) M (by omega) hM
  rw [Nat.sub_add_cancel (by omega : 1 ≤ n)] at hstep
  refine ⟨_, hstep, ?_⟩
  have hMn : n - 1 ≤ M := ram_le hM
  have hMtower : Real.exp^[k + 4] 1 ≤ (M : ℝ) := by
    have h1 : Real.exp^[k + 4] 1 ≤ (⌈Real.exp^[k + 4] 1⌉₊ : ℝ) := Nat.le_ceil _
    have h2 : ((⌈Real.exp^[k + 4] 1⌉₊ : ℕ) : ℝ) ≤ (M : ℝ) := by
      exact_mod_cast (by omega : ⌈Real.exp^[k + 4] 1⌉₊ ≤ M)
    linarith
  have hM2 : 2 ≤ M := by omega
  have e1 : k + 4 - 1 = k + 3 := by omega
  have e2 : k + 3 - 1 = k + 2 := by omega
  rw [e2] at hMlog
  obtain ⟨E, hE⟩ : ∃ E : ℕ, E = (M ^ (k + 3 - 1) + 1) * (M + 1) := ⟨_, rfl⟩
  rw [← hE, e1]
  have hE_le : E ≤ M ^ (k + 5) := by
    rw [hE, e2]
    have hpos : 1 ≤ M ^ (k + 2) := Nat.one_le_pow _ _ (by omega)
    have h1 : M ^ (k + 2) + 1 ≤ M ^ (k + 2) * M := by nlinarith
    have h2 : M + 1 ≤ M ^ 2 := by nlinarith
    calc (M ^ (k + 2) + 1) * (M + 1) ≤ (M ^ (k + 2) * M) * M ^ 2 := Nat.mul_le_mul h1 h2
      _ = M ^ (k + 5) := by ring
  have hE_ge : M + 1 ≤ E := by
    rw [hE]
    exact Nat.le_mul_of_pos_left _ (by positivity)
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hl2' := log_two_le_one
  have hMpos : (0 : ℝ) < M := by exact_mod_cast (by omega : 0 < M)
  have hmM : (M : ℝ) ≤ ((2 ^ E : ℕ) : ℝ) := by
    have h1 : M ≤ 2 ^ E := le_trans (by omega) (Nat.lt_two_pow_self (n := E)).le
    exact_mod_cast h1
  have hmpos : (0 : ℝ) < ((2 ^ E : ℕ) : ℝ) := lt_of_lt_of_le hMpos hmM
  -- towers below m and M
  have tm2 : Real.exp^[k + 2] 1 ≤ ((2 ^ E : ℕ) : ℝ) :=
    ((tower_mono (by omega : k + 2 ≤ k + 4)).trans hMtower).trans hmM
  rw [Function.iterate_succ_apply'] at tm2
  have lm1 : Real.exp^[k + 1] 1 ≤ Real.log ((2 ^ E : ℕ) : ℝ) :=
    (Real.le_log_iff_exp_le hmpos).mpr tm2
  have hlogm_pos : 0 < Real.log ((2 ^ E : ℕ) : ℝ) :=
    lt_of_lt_of_le one_pos ((one_le_tower (k + 1)).trans lm1)
  rw [Function.iterate_succ_apply'] at lm1
  have lm2 : Real.exp^[k] 1 ≤ Real.log (Real.log ((2 ^ E : ℕ) : ℝ)) :=
    (Real.le_log_iff_exp_le hlogm_pos).mpr lm1
  have hllm_pos : 0 < Real.log (Real.log ((2 ^ E : ℕ) : ℝ)) :=
    lt_of_lt_of_le one_pos ((one_le_tower k).trans lm2)
  have tM1 : Real.exp^[k + 1] 1 ≤ (M : ℝ) := (tower_mono (by omega : k + 1 ≤ k + 4)).trans hMtower
  rw [Function.iterate_succ_apply'] at tM1
  have lM1 : Real.exp^[k] 1 ≤ Real.log (M : ℝ) := (Real.le_log_iff_exp_le hMpos).mpr tM1
  have hlogM_pos : 0 < Real.log (M : ℝ) := lt_of_lt_of_le one_pos ((one_le_tower k).trans lM1)
  -- log m ≤ M ^ (k + 5)
  have hlm_le : Real.log ((2 ^ E : ℕ) : ℝ) ≤ (M : ℝ) ^ (k + 5) := by
    rw [log_two_pow]
    have h1 : (E : ℝ) ≤ (M : ℝ) ^ (k + 5) := by exact_mod_cast hE_le
    have h0 : (0 : ℝ) ≤ E := Nat.cast_nonneg _
    nlinarith
  have hllm_le : Real.log (Real.log ((2 ^ E : ℕ) : ℝ)) ≤ ((k : ℝ) + 5) * Real.log (M : ℝ) := by
    have h1 := Real.log_le_log hlogm_pos hlm_le
    rw [Real.log_pow] at h1
    have hcast : ((k + 5 : ℕ) : ℝ) = (k : ℝ) + 5 := by push_cast; ring
    rw [hcast] at h1
    exact h1
  have hkey : Real.log (Real.log (Real.log ((2 ^ E : ℕ) : ℝ))) ≤
      Real.log ((k : ℝ) + 5) + Real.log (Real.log (M : ℝ)) := by
    have h1 := Real.log_le_log hllm_pos hllm_le
    rw [Real.log_mul (by linarith) hlogM_pos.ne'] at h1
    exact h1
  have hshift := ilog_shift k (Real.log ((k : ℝ) + 5)) ha _ _ lm2 lM1 hkey
  have em : Real.log^[k + 3] ((2 ^ E : ℕ) : ℝ) =
      Real.log^[k + 1] (Real.log (Real.log ((2 ^ E : ℕ) : ℝ))) := by
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply]
  have eM : Real.log^[k + 2] (M : ℝ) = Real.log^[k + 1] (Real.log (M : ℝ)) := by
    rw [Function.iterate_succ_apply]
  rw [em]
  rw [eM] at hMlog
  have hn' : ((n - 1 : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast Nat.sub_le n 1
  have hn1' : (1 : ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
  have h3 : C * ((n - 1 : ℕ) : ℝ) ≤ C * n := mul_le_mul_of_nonneg_left hn' hC
  have h4 : Real.log ((k : ℝ) + 5) * 1 ≤ Real.log ((k : ℝ) + 5) * n :=
    mul_le_mul_of_nonneg_left hn1' ha
  linarith

lemma bound_ge_three : ∀ r, 3 ≤ r → Bound r := by
  intro r hr
  induction r, hr using Nat.le_induction with
  | base => exact bound_three
  | succ r hr ih =>
    obtain ⟨k, rfl⟩ : ∃ k, r = k + 3 := ⟨r - 3, by omega⟩
    exact bound_succ k ih

/-- Erdős--Rado: the `(r-1)`-fold iterated logarithm of the hypergraph Ramsey number `R_r(n)`
is `O(n)`. -/
theorem upper : ∀ r ≥ 3,
    (fun n : ℕ ↦ Real.log^[r - 1] (Combinatorics.hypergraphRamsey r n : ℝ)) =O[Filter.atTop]
      (fun n : ℕ ↦ (n : ℝ)) := by
  intro r hr
  obtain ⟨C, hC, n0, h⟩ := bound_ge_three r hr
  apply Asymptotics.IsBigO.of_bound C
  filter_upwards [Filter.eventually_ge_atTop (max n0 (⌈Real.exp^[r - 1] 1⌉₊))] with n hn
  obtain ⟨m, hm, hlog⟩ := h n (le_trans (le_max_left _ _) hn)
  have hR_le : Combinatorics.hypergraphRamsey r n ≤ m := by
    unfold Combinatorics.hypergraphRamsey
    exact Nat.sInf_le hm
  have hR_mem : Ram r n (Combinatorics.hypergraphRamsey r n) := by
    unfold Combinatorics.hypergraphRamsey
    exact Nat.sInf_mem (s := {m | Ram r n m}) ⟨m, hm⟩
  have hnR : n ≤ Combinatorics.hypergraphRamsey r n := ram_le hR_mem
  have htower : Real.exp^[r - 1] 1 ≤ (Combinatorics.hypergraphRamsey r n : ℝ) := by
    have h1 : Real.exp^[r - 1] 1 ≤ (⌈Real.exp^[r - 1] 1⌉₊ : ℝ) := Nat.le_ceil _
    have h2 : ((⌈Real.exp^[r - 1] 1⌉₊ : ℕ) : ℝ) ≤ (Combinatorics.hypergraphRamsey r n : ℝ) := by
      exact_mod_cast (le_trans (le_trans (le_max_right _ _) hn) hnR)
    linarith
  have hRm : (Combinatorics.hypergraphRamsey r n : ℝ) ≤ (m : ℝ) := by exact_mod_cast hR_le
  obtain ⟨h1, h2⟩ := ilog_mono (r - 1) _ _ htower hRm
  rw [Real.norm_of_nonneg (by linarith), Real.norm_of_nonneg (Nat.cast_nonneg n)]
  linarith

end ER562

theorem OMA.solution : OMA.R_Erdos562_erdos_562_R1.H1 := by
  unfold OMA.R_Erdos562_erdos_562_R1.H1
  exact ER562.upper
