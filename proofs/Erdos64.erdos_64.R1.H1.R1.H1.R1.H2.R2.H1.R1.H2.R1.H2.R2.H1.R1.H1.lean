import OMAReductions.R_Erdos64_erdos_64_R1_H1_R1_H1_R1_H2_R2_H1_R1_H2_R1_H2_R2_H1_R1
import Mathlib

/-!
# Odd-order nilpotent regular three-matching graphs contain dyadic cycles

Every finite nilpotent group `A` of odd order with distinct nonidentity shifts `a, b`
admits a simple cycle of length `2^k` (`k ≥ 2`) in its three-matching Haar graph on `Bool × A`.

## Method (explicit prime-plane theta compression)
1. By strong induction on `Nat.card A`, reduce to the case `Subgroup.closure {a, b} = ⊤`.
2. If `γ₃(A) = (⊤ : Subgroup A).lowerCentralSeries 2` is a 3-group, `nilpotent_third_term`
   from the parent reduction resolves the case directly.
3. Otherwise some odd prime `p ≥ 5` divides `Nat.card γ₃(A)`. Projecting onto the Sylow
   `p`-subgroup `P` (which is non-cyclic) and intersecting two maximal subgroups containing
   `π a` and `π b` respectively produces a surjective homomorphism
   `f : A →* Multiplicative (ZMod p × ZMod p)` with `f a = ofAdd (1, 0)` and `f b = ofAdd (0, 1)`.
4. For the unique power of two `L = 2^r` with `p < L < 2 * p`, we construct an explicit
   closed-form balanced theta `Θ(L, L, L)` on the hexagonal torus `Bool × (ZMod p × ZMod p)`
   (two uniform cases: `m = p - L/2 ≥ 2` and `m = 1`).
5. Lifting the three arms to `Bool × A` either closes immediately to a `2^(r+1)`-cycle
   (if two arm endpoints coincide) or subdivides a `2^k`-cycle of `Bool × f.ker`
   (from the induction hypothesis, since `Nat.card f.ker = Nat.card A / p^2 < Nat.card A`)
   into a simple `2^(k+r)`-cycle of `Bool × A`.
-/

namespace Erdos64NilpotentOddProof

open SimpleGraph
open scoped commutatorElement
open OMA.R_Erdos64_erdos_64_R1_H1_R1_H1_R1_H2_R2 (adj_mod cycle_from_period)
open OMA.R_Erdos64_erdos_64_R1_H1_R1_H1_R1_H2_R2_H1_R1_H2_R1_H2_R2_H1_R1 (nilpotent_third_term)

/- ## Section 1: General balanced theta compression -/

private def rightGraph {A : Type*} [Mul A] (a b : A) : SimpleGraph (Bool × A) :=
  SimpleGraph.fromRel fun u v =>
    u.1 = false ∧ v.1 = true ∧ (v.2 = u.2 ∨ v.2 = u.2 * a ∨ v.2 = u.2 * b)

private def leftGraph {A : Type*} [Mul A] (a b : A) : SimpleGraph (Bool × A) :=
  SimpleGraph.fromRel fun u v =>
    u.1 = false ∧ v.1 = true ∧ (v.2 = u.2 ∨ v.2 = a * u.2 ∨ v.2 = b * u.2)

private lemma rightGraph_iso_leftGraph {A : Type*} [Group A] (a b : A) :
    Nonempty (rightGraph a b ≃g leftGraph a b) := by
  let e : (Bool × A) ≃ (Bool × A) :=
    { toFun := fun z => (!z.1, z.2⁻¹)
      invFun := fun z => (!z.1, z.2⁻¹)
      left_inv := fun ⟨s, x⟩ => by simp
      right_inv := fun ⟨s, x⟩ => by simp }
  have rot (x y c : A) : x⁻¹ = c * y⁻¹ ↔ y = x * c := by
    constructor
    · intro h
      calc y = x * (x⁻¹ * y) := by group
           _ = x * c := by rw [h]; group
    · rintro rfl; simp
  refine ⟨⟨e, ?_⟩⟩
  rintro ⟨s, x⟩ ⟨t, y⟩
  cases s <;> cases t <;> simp [e, rightGraph, leftGraph, SimpleGraph.fromRel, rot] <;> tauto

private lemma rightGraph_adj_iff_step {A : Type*} [Group A] (a b : A) (u v : Bool × A) :
    (rightGraph a b).Adj u v ↔
      ∃ i : Fin 3,
        let S : Fin 3 → A := ![1, a, b]
        v = (!u.1, if u.1 then u.2 * (S i)⁻¹ else u.2 * S i) := by
  rcases u with ⟨s, x⟩
  rcases v with ⟨t, y⟩
  cases s <;> cases t
  · simp [rightGraph, SimpleGraph.fromRel]
  · constructor
    · intro h
      have h' : y = x ∨ y = x * a ∨ y = x * b := by
        simpa [rightGraph, SimpleGraph.fromRel] using h
      rcases h' with rfl | rfl | rfl
      · exact ⟨0, by simp⟩
      · exact ⟨1, by simp⟩
      · exact ⟨2, by simp⟩
    · rintro ⟨i, hi⟩
      have h' : y = x * (![1, a, b] : Fin 3 → A) i := by simpa using congrArg Prod.snd hi
      refine ⟨by simp, .inl ⟨rfl, rfl, ?_⟩⟩
      fin_cases i
      · exact .inl (by simpa using h')
      · exact .inr (.inl (by simpa using h'))
      · exact .inr (.inr (by simpa using h'))
  · constructor
    · intro h
      have h' : x = y ∨ x = y * a ∨ x = y * b := by
        simpa [rightGraph, SimpleGraph.fromRel] using h
      rcases h' with rfl | rfl | rfl
      · exact ⟨0, by simp⟩
      · exact ⟨1, by simp⟩
      · exact ⟨2, by simp⟩
    · rintro ⟨i, hi⟩
      have h' : y = x * ((![1, a, b] : Fin 3 → A) i)⁻¹ := by simpa using congrArg Prod.snd hi
      refine ⟨by simp, .inr ⟨rfl, rfl, ?_⟩⟩
      fin_cases i
      · exact .inl (by simpa using h'.symm)
      · exact .inr (.inl (by rw [h']; simp))
      · exact .inr (.inr (by rw [h']; simp))
  · simp [rightGraph, SimpleGraph.fromRel]

/-- A balanced theta of arm length `L = 2^r` (`r ≥ 2`) in the quotient right-shift graph
`rightGraph (f a) (f b)` compresses `rightGraph a b` into `rightGraph d₁ d₂` on `f.ker`,
multiplying cycle lengths by `2^r` (or immediately yielding a `2^(r+1)`-cycle on collision). -/
private theorem theta_compress {A Q : Type} [Group A] [Group Q]
    (f : A →* Q) (a b : A)
    (r : ℕ) (hr : 2 ≤ r) (target : Q) (htarget : target ≠ 1)
    (P : Fin 3 → ℕ → Bool × Q)
    (hP0 : ∀ c, P c 0 = (false, 1))
    (hPL : ∀ c, P c (2 ^ r) = (false, target))
    (hPadj : ∀ c t, t < 2 ^ r → (rightGraph (f a) (f b)).Adj (P c t) (P c (t + 1)))
    (hPavoid : ∀ c t, 0 < t → t < 2 ^ r → P c t ≠ (false, 1) ∧ P c t ≠ (false, target))
    (hPinj : ∀ c₁ t₁ c₂ t₂, 0 < t₁ → t₁ < 2 ^ r → 0 < t₂ → t₂ < 2 ^ r →
      P c₁ t₁ = P c₂ t₂ → c₁ = c₂ ∧ t₁ = t₂)
    (recurse : ∀ d₁ d₂ : f.ker, d₁ ≠ 1 → d₂ ≠ 1 → d₁ ≠ d₂ →
      ∃ k : ℕ, 2 ≤ k ∧ cycleGraph (2 ^ k) ⊑ rightGraph d₁ d₂) :
    ∃ k : ℕ, 2 ≤ k ∧ cycleGraph (2 ^ k) ⊑ rightGraph a b := by
  classical
  set L := 2 ^ r with hL_def
  have hL4 : 4 ≤ L := by
    have := Nat.pow_le_pow_right (by decide : 0 < 2) hr
    simpa [hL_def] using this
  let S : Fin 3 → A := ![1, a, b]
  let SQ : Fin 3 → Q := ![1, f a, f b]
  have hfS (i : Fin 3) : f (S i) = SQ i := by
    fin_cases i <;> simp [S, SQ]
  have hstepQ (c : Fin 3) (t : ℕ) (ht : t < L) :
      ∃ i : Fin 3, P c (t + 1) =
        (!(P c t).1, if (P c t).1 then (P c t).2 * (SQ i)⁻¹ else (P c t).2 * SQ i) := by
    simpa [SQ] using (rightGraph_adj_iff_step (f a) (f b) (P c t) (P c (t + 1))).mp (hPadj c t ht)
  let dir (c : Fin 3) (t : ℕ) : Fin 3 :=
    if ht : t < L then (hstepQ c t ht).choose else 0
  have hdir (c : Fin 3) (t : ℕ) (ht : t < L) :
      P c (t + 1) =
        (!(P c t).1, if (P c t).1 then (P c t).2 * (SQ (dir c t))⁻¹ else (P c t).2 * SQ (dir c t)) := by
    simpa [dir, ht] using (hstepQ c t ht).choose_spec
  let lift : Fin 3 → ℕ → A := fun c =>
    Nat.rec 1 (fun t prev =>
      if (P c t).1 then prev * (S (dir c t))⁻¹ else prev * S (dir c t))
  have hlift_proj (c : Fin 3) (t : ℕ) (ht : t ≤ L) : f (lift c t) = (P c t).2 := by
    induction t with
    | zero => simp [lift, hP0]
    | succ t ih =>
      have ht' : t < L := by omega
      have hspec := hdir c t ht'
      have hsnd := congrArg Prod.snd hspec
      dsimp only [lift]
      rw [hsnd]
      split_ifs with hside
      · rw [map_mul, map_inv, hfS, ih (by omega)]
      · rw [map_mul, hfS, ih (by omega)]
  have hlift_adj (c : Fin 3) (g : A) (t : ℕ) (ht : t < L) :
      (rightGraph a b).Adj ((P c t).1, g * lift c t) ((P c (t + 1)).1, g * lift c (t + 1)) := by
    rw [rightGraph_adj_iff_step]
    refine ⟨dir c t, ?_⟩
    have hspec := hdir c t ht
    have hfst := congrArg Prod.fst hspec
    refine Prod.ext hfst ?_
    dsimp only [lift]
    split_ifs <;> simp [S, mul_assoc]
  let r₁ : A := lift 0 L
  have hfr₁ : f r₁ = target := by
    simpa [r₁, hPL] using hlift_proj 0 L le_rfl
  let d : Fin 3 → f.ker := fun c =>
    ⟨lift c L * r₁⁻¹, by
      change f (lift c L * r₁⁻¹) = 1
      rw [map_mul, map_inv, hlift_proj c L le_rfl, hPL, hfr₁, mul_inv_cancel]⟩
  have hd0 : d 0 = 1 := by
    apply Subtype.ext
    change lift 0 L * r₁⁻¹ = 1
    simp [r₁]
  have hliftL (c : Fin 3) : lift c L = (d c : A) * r₁ := by
    simp [d, mul_assoc]
  by_cases hdinj : Function.Injective d
  · -- Case 2: All three lifted endpoints are distinct -> subdivide a cycle in `f.ker`!
    have hd1 : d 1 ≠ 1 := fun h => (by decide : (1 : Fin 3) ≠ 0) (hdinj (h.trans hd0.symm))
    have hd2 : d 2 ≠ 1 := fun h => (by decide : (2 : Fin 3) ≠ 0) (hdinj (h.trans hd0.symm))
    have hd12 : d 1 ≠ d 2 := fun h => (by decide : (1 : Fin 3) ≠ 2) (hdinj h)
    obtain ⟨k, hk, ⟨γ⟩⟩ := recurse (d 1) (d 2) hd1 hd2 hd12
    set N := 2 ^ k with hN_def
    have hN4 : 4 ≤ N := by
      have := Nat.pow_le_pow_right (by decide : 0 < 2) hk
      simpa [hN_def] using this
    let idx (m : ℕ) : Fin N := ⟨m % N, Nat.mod_lt _ (by omega)⟩
    let next (i : Fin N) : Fin N := idx (i.val + 1)
    have hsucc (m : ℕ) : next (idx m) = idx (m + 1) := Fin.ext (Nat.mod_add_mod m N 1)
    have hnotflip (i : Fin N) : next (next i) ≠ i := by
      intro eq
      have hv := congrArg Fin.val eq
      dsimp only [next, idx] at hv
      have hi := i.isLt
      by_cases h1 : i.val + 1 < N
      · rw [Nat.mod_eq_of_lt h1] at hv
        by_cases h2 : i.val + 1 + 1 < N
        · rw [Nat.mod_eq_of_lt h2] at hv; omega
        · have : i.val + 1 + 1 = N := by omega
          rw [this, Nat.mod_self] at hv; omega
      · have h1' : i.val + 1 = N := by omega
        rw [h1', Nat.mod_self, Nat.zero_add, Nat.mod_eq_of_lt (by omega)] at hv
        omega
    have hγedge (i : Fin N) : (rightGraph (d 1) (d 2)).Adj (γ i) (γ (next i)) :=
      γ.toHom.map_adj ((adj_mod (by omega) i (next i)).mpr (.inl rfl))
    -- Extract edge color `col i : Fin 3` and `false`-side base `base i : f.ker` for each edge `i`
    have hedge_info (i : Fin N) :
        ∃ c : Fin 3,
          (γ i).1 = !(γ (next i)).1 ∧
          ((γ i).1 = false → (γ (next i)).2 = (γ i).2 * d c) ∧
          ((γ i).1 = true → (γ i).2 = (γ (next i)).2 * d c) := by
      have h := (rightGraph_adj_iff_step (d 1) (d 2) (γ i) (γ (next i))).mp (hγedge i)
      obtain ⟨c, hc⟩ := h
      have hSc : (![1, d 1, d 2] : Fin 3 → f.ker) c = d c := by
        fin_cases c <;> simp [hd0]
      refine ⟨c, ?_, ?_, ?_⟩
      · have h1 := congrArg Prod.fst hc
        cases hgi : (γ i).1 <;> cases hgn : (γ (next i)).1 <;> simp [hgi, hgn] at h1 ⊢
      · intro h0
        have h2 := congrArg Prod.snd hc
        simpa [h0, hSc] using h2
      · intro h1
        have h2 := congrArg Prod.snd hc
        simp only [h1, ↓reduceIte, hSc] at h2
        rw [h2]; simp
    let col (i : Fin N) : Fin 3 := (hedge_info i).choose
    have hcol_side (i : Fin N) : (γ i).1 = !(γ (next i)).1 := (hedge_info i).choose_spec.1
    have hcol_false (i : Fin N) (h : (γ i).1 = false) :
        (γ (next i)).2 = (γ i).2 * d (col i) := (hedge_info i).choose_spec.2.1 h
    have hcol_true (i : Fin N) (h : (γ i).1 = true) :
        (γ i).2 = (γ (next i)).2 * d (col i) := (hedge_info i).choose_spec.2.2 h
    let base (i : Fin N) : f.ker := if (γ i).1 then (γ (next i)).2 else (γ i).2
    -- Define the periodic lifted vertex sequence `v : ℕ → Bool × A` of period `N * L`
    let stepPos (i : Fin N) (t : ℕ) : ℕ := if (γ i).1 then L - t else t
    let v (m : ℕ) : Bool × A :=
      let i := idx (m / L)
      let t := m % L
      ((P (col i) (stepPos i t)).1, (base i : A) * lift (col i) (stepPos i t))
    -- Endpoint value of edge `i` at `t = 0` and `t = L`
    have hv_zero (i : Fin N) :
        ((P (col i) (stepPos i 0)).1, (base i : A) * lift (col i) (stepPos i 0)) =
        (false, if (γ i).1 then ((γ i).2 : A) * r₁ else ((γ i).2 : A)) := by
      cases hgi : (γ i).1
      · simp [stepPos, base, hgi, hP0, lift]
      · simp only [stepPos, base, hgi, ↓reduceIte, Nat.sub_zero, hPL, hliftL, ← mul_assoc]
        have hmul := hcol_true i hgi
        have hcoe : ((γ (next i)).2 : A) * (d (col i) : A) = ((γ i).2 : A) := by
          rw [← Subgroup.coe_mul, ← hmul]
        rw [hcoe]
    have hv_L (i : Fin N) :
        ((P (col i) (stepPos i L)).1, (base i : A) * lift (col i) (stepPos i L)) =
        (false, if (γ (next i)).1 then ((γ (next i)).2 : A) * r₁ else ((γ (next i)).2 : A)) := by
      have hns := hcol_side i
      cases hgi : (γ i).1
      · have hgn : (γ (next i)).1 = true := by
          cases hgn' : (γ (next i)).1 <;> simp [hgi, hgn'] at hns ⊢
        simp only [stepPos, base, hgi, hgn, Bool.false_eq_true, ↓reduceIte, hPL, hliftL, ← mul_assoc]
        have hmul := hcol_false i hgi
        have hcoe : ((γ i).2 : A) * (d (col i) : A) = ((γ (next i)).2 : A) := by
          rw [← Subgroup.coe_mul, ← hmul]
        rw [hcoe]
      · have hgn : (γ (next i)).1 = false := by
          cases hgn' : (γ (next i)).1 <;> simp [hgi, hgn'] at hns ⊢
        simp [stepPos, base, hgi, hgn, hP0, lift]
    have hv_adj (m : ℕ) : (rightGraph a b).Adj (v m) (v (m + 1)) := by
      have hLpos : 0 < L := by omega
      set q := m / L
      set t := m % L
      have ht : t < L := Nat.mod_lt m hLpos
      have hm_eq : m = L * q + t := (Nat.div_add_mod m L).symm
      by_cases ht1 : t + 1 < L
      · have hdiv : (m + 1) / L = q := by
          rw [hm_eq, add_assoc, Nat.mul_add_div hLpos, Nat.div_eq_of_lt ht1, add_zero]
        have hmod : (m + 1) % L = t + 1 := by
          rw [hm_eq, add_assoc, Nat.mul_add_mod, Nat.mod_eq_of_lt ht1]
        dsimp only [v]
        rw [hdiv, hmod]
        change (rightGraph a b).Adj
          ((P (col (idx q)) (stepPos (idx q) t)).1, (base (idx q) : A) * lift (col (idx q)) (stepPos (idx q) t))
          ((P (col (idx q)) (stepPos (idx q) (t + 1))).1, (base (idx q) : A) * lift (col (idx q)) (stepPos (idx q) (t + 1)))
        cases hside : (γ (idx q)).1
        · simp only [stepPos, hside, Bool.false_eq_true, ↓reduceIte]
          exact hlift_adj (col (idx q)) (base (idx q) : A) t ht
        · simp only [stepPos, hside, ↓reduceIte]
          have hsub : L - t = (L - (t + 1)) + 1 := by omega
          rw [hsub]
          exact (hlift_adj (col (idx q)) (base (idx q) : A) (L - (t + 1)) (by omega)).symm
      · have ht_last : t + 1 = L := by omega
        have hdiv : (m + 1) / L = q + 1 := by
          rw [hm_eq, add_assoc, ht_last, show L * q + L = L * (q + 1) by ring,
            Nat.mul_div_cancel_left _ hLpos]
        have hmod : (m + 1) % L = 0 := by
          rw [hm_eq, add_assoc, ht_last, show L * q + L = L * (q + 1) by ring,
            Nat.mul_mod_right]
        dsimp only [v]
        rw [hdiv, hmod, ← hsucc q]
        rw [hv_zero (next (idx q)), ← hv_L (idx q)]
        change (rightGraph a b).Adj
          ((P (col (idx q)) (stepPos (idx q) t)).1, (base (idx q) : A) * lift (col (idx q)) (stepPos (idx q) t))
          ((P (col (idx q)) (stepPos (idx q) L)).1, (base (idx q) : A) * lift (col (idx q)) (stepPos (idx q) L))
        cases hside : (γ (idx q)).1
        · simp only [stepPos, hside, Bool.false_eq_true, ↓reduceIte]
          rw [← ht_last]
          exact hlift_adj (col (idx q)) (base (idx q) : A) t ht
        · simp only [stepPos, hside, ↓reduceIte]
          have hsub1 : L - t = 1 := by omega
          have hsub2 : L - L = 0 := Nat.sub_self L
          rw [hsub1, hsub2]
          exact (hlift_adj (col (idx q)) (base (idx q) : A) 0 (by omega)).symm
    have hv_close : v (N * L) = v 0 := by
      have hLpos : 0 < L := by omega
      have hdiv : (N * L) / L = N := Nat.mul_div_cancel N hLpos
      have hmod : (N * L) % L = 0 := Nat.mul_mod_left N L
      have h0div : 0 / L = 0 := Nat.zero_div L
      have h0mod : 0 % L = 0 := Nat.zero_mod L
      have hidxN : idx N = idx 0 := Fin.ext (by simp [idx])
      dsimp only [v]
      rw [hdiv, hmod, h0div, h0mod, hidxN]
    have hv_proj (m : ℕ) : ((v m).1, f (v m).2) = P (col (idx (m / L))) (stepPos (idx (m / L)) (m % L)) := by
      have hLpos : 0 < L := by omega
      have hmt : m % L < L := Nat.mod_lt m hLpos
      have hle : stepPos (idx (m / L)) (m % L) ≤ L := by
        dsimp only [stepPos]; split_ifs <;> omega
      dsimp only [v]
      refine Prod.ext rfl ?_
      rw [map_mul, (base (idx (m / L))).property, one_mul, hlift_proj _ _ hle]
    have hv_inj (m₁ m₂ : ℕ) (hm₁ : m₁ < N * L) (hm₂ : m₂ < N * L) (heq : v m₁ = v m₂) :
        m₁ = m₂ := by
      have hLpos : 0 < L := by omega
      set q₁ := m₁ / L with hq₁_def
      set t₁ := m₁ % L with ht₁_def
      set q₂ := m₂ / L with hq₂_def
      set t₂ := m₂ % L with ht₂_def
      have hm₁_eq : m₁ = L * q₁ + t₁ := (Nat.div_add_mod m₁ L).symm
      have hm₂_eq : m₂ = L * q₂ + t₂ := (Nat.div_add_mod m₂ L).symm
      have hq₁ : q₁ < N := (Nat.div_lt_iff_lt_mul hLpos).mpr hm₁
      have hq₂ : q₂ < N := (Nat.div_lt_iff_lt_mul hLpos).mpr hm₂
      have ht₁ : t₁ < L := Nat.mod_lt m₁ hLpos
      have ht₂ : t₂ < L := Nat.mod_lt m₂ hLpos
      have hpeq : P (col (idx q₁)) (stepPos (idx q₁) t₁) = P (col (idx q₂)) (stepPos (idx q₂) t₂) := by
        rw [← hv_proj m₁, ← hv_proj m₂, heq]
      by_cases hz₁ : t₁ = 0
      · by_cases hz₂ : t₂ = 0
        · -- Both are junction vertices
          have h1 : v m₁ = (false, if (γ (idx q₁)).1 then ((γ (idx q₁)).2 : A) * r₁ else ((γ (idx q₁)).2 : A)) := by
            change ((P (col (idx q₁)) (stepPos (idx q₁) t₁)).1,
              (base (idx q₁) : A) * lift (col (idx q₁)) (stepPos (idx q₁) t₁)) = _
            rw [hz₁]; exact hv_zero (idx q₁)
          have h2 : v m₂ = (false, if (γ (idx q₂)).1 then ((γ (idx q₂)).2 : A) * r₁ else ((γ (idx q₂)).2 : A)) := by
            change ((P (col (idx q₂)) (stepPos (idx q₂) t₂)).1,
              (base (idx q₂) : A) * lift (col (idx q₂)) (stepPos (idx q₂) t₂)) = _
            rw [hz₂]; exact hv_zero (idx q₂)
          have hsnd := congrArg Prod.snd (h1.symm.trans (heq.trans h2))
          have hfp := congrArg f hsnd
          have hker1 : f ((γ (idx q₁)).2 : A) = 1 := (γ (idx q₁)).2.property
          have hker2 : f ((γ (idx q₂)).2 : A) = 1 := (γ (idx q₂)).2.property
          have hside_eq : (γ (idx q₁)).1 = (γ (idx q₂)).1 := by
            cases hs1 : (γ (idx q₁)).1 <;> cases hs2 : (γ (idx q₂)).1
            · rfl
            · simp only [hs1, hs2, Bool.false_eq_true, ↓reduceIte, map_mul, hker1, hker2, hfr₁, one_mul] at hfp
              exact (htarget hfp.symm).elim
            · simp only [hs1, hs2, Bool.false_eq_true, ↓reduceIte, map_mul, hker1, hker2, hfr₁, one_mul] at hfp
              exact (htarget hfp).elim
            · rfl
          have hval_eq : (γ (idx q₁)).2 = (γ (idx q₂)).2 := by
            apply Subtype.ext
            cases hs1 : (γ (idx q₁)).1
            · simpa [hs1, ← hside_eq] using hsnd
            · have hs2 : (γ (idx q₂)).1 = true := hside_eq.symm.trans hs1
              simp only [hs1, hs2, ↓reduceIte] at hsnd
              exact mul_right_cancel hsnd
          have hi_eq : idx q₁ = idx q₂ := γ.injective (Prod.ext hside_eq hval_eq)
          have hq_eq : q₁ = q₂ := by
            simpa [idx, Nat.mod_eq_of_lt hq₁, Nat.mod_eq_of_lt hq₂] using congrArg Fin.val hi_eq
          rw [hm₁_eq, hm₂_eq, hq_eq, hz₁, hz₂]
        · -- `t₁ = 0` (junction) vs `0 < t₂ < L` (interior) -> impossible by `hPavoid`
          have hst₂_pos : 0 < stepPos (idx q₂) t₂ := by
            dsimp only [stepPos]; split_ifs <;> omega
          have hst₂_lt : stepPos (idx q₂) t₂ < L := by
            dsimp only [stepPos]; split_ifs <;> omega
          have hav := hPavoid (col (idx q₂)) (stepPos (idx q₂) t₂) hst₂_pos hst₂_lt
          rw [← hpeq, hz₁] at hav
          cases hs1 : (γ (idx q₁)).1
          · simp [stepPos, hs1, hP0] at hav
          · simp [stepPos, hs1, hPL] at hav
      · by_cases hz₂ : t₂ = 0
        · -- `0 < t₁ < L` (interior) vs `t₂ = 0` (junction) -> impossible by `hPavoid`
          have hst₁_pos : 0 < stepPos (idx q₁) t₁ := by
            dsimp only [stepPos]; split_ifs <;> omega
          have hst₁_lt : stepPos (idx q₁) t₁ < L := by
            dsimp only [stepPos]; split_ifs <;> omega
          have hav := hPavoid (col (idx q₁)) (stepPos (idx q₁) t₁) hst₁_pos hst₁_lt
          rw [hpeq, hz₂] at hav
          cases hs2 : (γ (idx q₂)).1
          · simp [stepPos, hs2, hP0] at hav
          · simp [stepPos, hs2, hPL] at hav
        · -- Both interior (`0 < t₁, t₂ < L`)
          have hst₁_pos : 0 < stepPos (idx q₁) t₁ := by dsimp only [stepPos]; split_ifs <;> omega
          have hst₁_lt : stepPos (idx q₁) t₁ < L := by dsimp only [stepPos]; split_ifs <;> omega
          have hst₂_pos : 0 < stepPos (idx q₂) t₂ := by dsimp only [stepPos]; split_ifs <;> omega
          have hst₂_lt : stepPos (idx q₂) t₂ < L := by dsimp only [stepPos]; split_ifs <;> omega
          obtain ⟨hcol_eq, hsp_eq⟩ := hPinj _ _ _ _ hst₁_pos hst₁_lt hst₂_pos hst₂_lt hpeq
          have hsnd := congrArg Prod.snd heq
          dsimp only [v] at hsnd
          change (base (idx q₁) : A) * lift (col (idx q₁)) (stepPos (idx q₁) t₁) =
            (base (idx q₂) : A) * lift (col (idx q₂)) (stepPos (idx q₂) t₂) at hsnd
          rw [hcol_eq, hsp_eq] at hsnd
          have hbase_eq : base (idx q₁) = base (idx q₂) := Subtype.ext (mul_right_cancel hsnd)
          -- Hence edges `idx q₁` and `idx q₂` have the exact same two endpoints in `γ`!
          have hend_eq :
              (γ (idx q₁) = γ (idx q₂) ∧ γ (next (idx q₁)) = γ (next (idx q₂))) ∨
              (γ (idx q₁) = γ (next (idx q₂)) ∧ γ (next (idx q₁)) = γ (idx q₂)) := by
            have hs1' := hcol_side (idx q₁)
            have hs2' := hcol_side (idx q₂)
            cases h1 : (γ (idx q₁)).1 <;> cases h2 : (γ (idx q₂)).1
            · left
              have hn1 : (γ (next (idx q₁))).1 = true := by
                cases h : (γ (next (idx q₁))).1 <;> simp [h1, h] at hs1' ⊢
              have hn2 : (γ (next (idx q₂))).1 = true := by
                cases h : (γ (next (idx q₂))).1 <;> simp [h2, h] at hs2' ⊢
              have hb : (γ (idx q₁)).2 = (γ (idx q₂)).2 := by simpa [base, h1, h2] using hbase_eq
              refine ⟨Prod.ext (h1.trans h2.symm) hb, Prod.ext (hn1.trans hn2.symm) ?_⟩
              rw [hcol_false _ h1, hcol_false _ h2, hb, hcol_eq]
            · right
              have hn1 : (γ (next (idx q₁))).1 = true := by
                cases h : (γ (next (idx q₁))).1 <;> simp [h1, h] at hs1' ⊢
              have hn2 : (γ (next (idx q₂))).1 = false := by
                cases h : (γ (next (idx q₂))).1 <;> simp [h2, h] at hs2' ⊢
              have hb : (γ (idx q₁)).2 = (γ (next (idx q₂))).2 := by simpa [base, h1, h2] using hbase_eq
              refine ⟨Prod.ext (h1.trans hn2.symm) hb, Prod.ext (hn1.trans h2.symm) ?_⟩
              rw [hcol_false _ h1, hcol_true _ h2, hb, hcol_eq]
            · right
              have hn1 : (γ (next (idx q₁))).1 = false := by
                cases h : (γ (next (idx q₁))).1 <;> simp [h1, h] at hs1' ⊢
              have hn2 : (γ (next (idx q₂))).1 = true := by
                cases h : (γ (next (idx q₂))).1 <;> simp [h2, h] at hs2' ⊢
              have hb : (γ (next (idx q₁))).2 = (γ (idx q₂)).2 := by simpa [base, h1, h2] using hbase_eq
              refine ⟨Prod.ext (h1.trans hn2.symm) ?_, Prod.ext (hn1.trans h2.symm) hb⟩
              rw [hcol_true _ h1, hcol_false _ h2, hb, hcol_eq]
            · left
              have hn1 : (γ (next (idx q₁))).1 = false := by
                cases h : (γ (next (idx q₁))).1 <;> simp [h1, h] at hs1' ⊢
              have hn2 : (γ (next (idx q₂))).1 = false := by
                cases h : (γ (next (idx q₂))).1 <;> simp [h2, h] at hs2' ⊢
              have hb : (γ (next (idx q₁))).2 = (γ (next (idx q₂))).2 := by
                simpa [base, h1, h2] using hbase_eq
              refine ⟨Prod.ext (h1.trans h2.symm) ?_, Prod.ext (hn1.trans hn2.symm) hb⟩
              rw [hcol_true _ h1, hcol_true _ h2, hb, hcol_eq]
          rcases hend_eq with ⟨e1, _⟩ | ⟨e1, e2⟩
          · have hi_eq : idx q₁ = idx q₂ := γ.injective e1
            have hq_eq : q₁ = q₂ := by
              simpa [idx, Nat.mod_eq_of_lt hq₁, Nat.mod_eq_of_lt hq₂] using congrArg Fin.val hi_eq
            have ht_eq : t₁ = t₂ := by
              rw [hi_eq] at hsp_eq
              dsimp only [stepPos] at hsp_eq
              split_ifs at hsp_eq <;> omega
            rw [hm₁_eq, hm₂_eq, hq_eq, ht_eq]
          · have e1' := γ.injective e1
            have e2' := γ.injective e2
            exact (hnotflip (idx q₁) ((congrArg next e2').trans e1'.symm)).elim
    refine ⟨k + r, by omega, ?_⟩
    rw [pow_add]
    exact cycle_from_period (rightGraph a b) (N * L) (by nlinarith) v hv_adj hv_close hv_inj
  · -- Case 1: Two lifted arms collide at the endpoint -> immediate `2^(r+1)`-cycle!
    rw [Function.Injective] at hdinj
    push Not at hdinj
    obtain ⟨c₁, c₂, hdeq, hcne⟩ := hdinj
    have hL_eq : lift c₁ L = lift c₂ L := by
      rw [hliftL c₁, hliftL c₂, hdeq]
    let w (m : ℕ) : Bool × A :=
      if m ≤ L then ((P c₁ m).1, lift c₁ m) else ((P c₂ (2 * L - m)).1, lift c₂ (2 * L - m))
    have hw_proj (m : ℕ) (hm : m ≤ 2 * L) :
        ((w m).1, f (w m).2) = if m ≤ L then P c₁ m else P c₂ (2 * L - m) := by
      dsimp only [w]
      split_ifs with h
      · exact Prod.ext rfl (hlift_proj c₁ m h)
      · exact Prod.ext rfl (hlift_proj c₂ (2 * L - m) (by omega))
    have hw_adj (m : ℕ) : (rightGraph a b).Adj (w (m % (2 * L))) (w ((m + 1) % (2 * L))) := by
      have h2Lpos : 0 < 2 * L := by omega
      set t := m % (2 * L)
      have ht : t < 2 * L := Nat.mod_lt m h2Lpos
      have hnext_mod : (m + 1) % (2 * L) = if t + 1 < 2 * L then t + 1 else 0 := by
        by_cases hlt : t + 1 < 2 * L
        · rw [if_pos hlt, ← Nat.mod_add_mod, Nat.mod_eq_of_lt hlt]
        · have heq : t + 1 = 2 * L := by omega
          rw [if_neg hlt, ← Nat.mod_add_mod, heq, Nat.mod_self]
      rw [hnext_mod]
      by_cases h1 : t < L
      · have hle1 : t ≤ L := by omega
        have hle2 : t + 1 ≤ L := by omega
        have hlt2 : t + 1 < 2 * L := by omega
        rw [if_pos hlt2]
        dsimp only [w]
        rw [if_pos hle1, if_pos hle2]
        simpa using hlift_adj c₁ 1 t h1
      · by_cases h2 : t = L
        · have hlt2 : t + 1 < 2 * L := by omega
          rw [if_pos hlt2]
          dsimp only [w]
          rw [if_pos (by omega : t ≤ L), if_neg (by omega : ¬ t + 1 ≤ L)]
          have hL1 : 2 * L - (t + 1) = L - 1 := by omega
          rw [hL1, h2, hL_eq]
          have hPeq : (P c₁ L).1 = (P c₂ L).1 := by rw [hPL c₁, hPL c₂]
          rw [hPeq, show L = (L - 1) + 1 by omega]
          simpa using (hlift_adj c₂ 1 (L - 1) (by omega)).symm
        · by_cases h3 : t + 1 < 2 * L
          · rw [if_pos h3]
            dsimp only [w]
            rw [if_neg (by omega : ¬ t ≤ L), if_neg (by omega : ¬ t + 1 ≤ L)]
            have hsub : 2 * L - t = (2 * L - (t + 1)) + 1 := by omega
            rw [hsub]
            simpa using (hlift_adj c₂ 1 (2 * L - (t + 1)) (by omega)).symm
          · have hlast : t = 2 * L - 1 := by omega
            rw [if_neg h3]
            dsimp only [w]
            rw [if_neg (by omega : ¬ t ≤ L), if_pos (by omega : 0 ≤ L)]
            have hsub : 2 * L - t = 1 := by omega
            rw [hsub]
            have hP0eq : (P c₁ 0).1 = (P c₂ 0).1 := by rw [hP0 c₁, hP0 c₂]
            rw [hP0eq]
            change (rightGraph a b).Adj ((P c₂ 1).1, lift c₂ 1) ((P c₂ 0).1, lift c₂ 0)
            simpa using (hlift_adj c₂ 1 0 (by omega)).symm
    let w' (m : ℕ) := w (m % (2 * L))
    have hw'_close : w' (2 * L) = w' 0 := by simp [w']
    have hw'_inj (i j : ℕ) (hi : i < 2 * L) (hj : j < 2 * L) (heq : w' i = w' j) : i = j := by
      have heq' : w i = w j := by
        simpa [w', Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt hj] using heq
      have hpeq : (if i ≤ L then P c₁ i else P c₂ (2 * L - i)) =
          (if j ≤ L then P c₁ j else P c₂ (2 * L - j)) := by
        rw [← hw_proj i (by omega), ← hw_proj j (by omega), heq']
      by_cases hi0 : i = 0
      · by_cases hj0 : j = 0
        · omega
        · by_cases hjL : j = L
          · subst hi0; subst hjL
            simp only [le_refl, ↓reduceIte, Nat.zero_le, hP0, hPL, Prod.mk.injEq, true_and] at hpeq
            exact (htarget hpeq.symm).elim
          · subst hi0
            simp only [Nat.zero_le, ↓reduceIte, hP0] at hpeq
            split_ifs at hpeq with hjle
            · exact ((hPavoid c₁ j (by omega) (by omega)).1 hpeq.symm).elim
            · exact ((hPavoid c₂ (2 * L - j) (by omega) (by omega)).1 hpeq.symm).elim
      · by_cases hiL : i = L
        · by_cases hj0 : j = 0
          · subst hiL; subst hj0
            simp only [le_refl, ↓reduceIte, Nat.zero_le, hP0, hPL, Prod.mk.injEq, true_and] at hpeq
            exact (htarget hpeq).elim
          · by_cases hjL : j = L
            · omega
            · subst hiL
              simp only [le_refl, ↓reduceIte, hPL] at hpeq
              split_ifs at hpeq with hjle
              · exact ((hPavoid c₁ j (by omega) (by omega)).2 hpeq.symm).elim
              · exact ((hPavoid c₂ (2 * L - j) (by omega) (by omega)).2 hpeq.symm).elim
        · by_cases hj0 : j = 0
          · subst hj0
            simp only [Nat.zero_le, ↓reduceIte, hP0] at hpeq
            split_ifs at hpeq with hile
            · exact ((hPavoid c₁ i (by omega) (by omega)).1 hpeq).elim
            · exact ((hPavoid c₂ (2 * L - i) (by omega) (by omega)).1 hpeq).elim
          · by_cases hjL : j = L
            · subst hjL
              simp only [le_refl, ↓reduceIte, hPL] at hpeq
              split_ifs at hpeq with hile
              · exact ((hPavoid c₁ i (by omega) (by omega)).2 hpeq).elim
              · exact ((hPavoid c₂ (2 * L - i) (by omega) (by omega)).2 hpeq).elim
            · split_ifs at hpeq with hile hjle
              · exact (hPinj c₁ i c₁ j (by omega) (by omega) (by omega) (by omega) hpeq).2
              · exact (hcne (hPinj c₁ i c₂ (2 * L - j) (by omega) (by omega) (by omega) (by omega) hpeq).1).elim
              · exact (hcne (hPinj c₂ (2 * L - i) c₁ j (by omega) (by omega) (by omega) (by omega) hpeq).1.symm).elim
              · have := (hPinj c₂ (2 * L - i) c₂ (2 * L - j) (by omega) (by omega) (by omega) (by omega) hpeq).2
                omega
    refine ⟨r + 1, by omega, ?_⟩
    rw [pow_succ']
    exact cycle_from_period (rightGraph a b) (2 * L) (by omega) w' hw_adj hw'_close hw'_inj

/- ## Section 2: Explicit balanced theta `Θ(2^r, 2^r, 2^r)` on `ZMod p × ZMod p` (`p ≥ 5` odd) -/

private lemma exists_pow_two_between {p : ℕ} (hp : 5 ≤ p) (hodd : Odd p) :
    ∃ r : ℕ, 3 ≤ r ∧ p < 2 ^ r ∧ 2 ^ r < 2 * p := by
  let r := Nat.log 2 p + 1
  have h1 : 2 ^ Nat.log 2 p ≤ p := Nat.pow_log_le_self 2 (by omega)
  have h2 : p < 2 ^ r := Nat.lt_pow_succ_log_self (by decide) p
  have hne : 2 ^ Nat.log 2 p ≠ p := by
    intro eq
    have hlog : 1 ≤ Nat.log 2 p := by
      have := Nat.le_log_of_pow_le (by decide : 1 < 2) (by omega : 2 ^ 1 ≤ p)
      exact this
    have heven : Even (2 ^ Nat.log 2 p) :=
      even_iff_two_dvd.mpr (dvd_pow_self 2 (by omega))
    rw [eq] at heven
    exact Nat.not_even_iff_odd.mpr hodd heven
  have h3 : 2 ^ r < 2 * p := by
    change 2 ^ (Nat.log 2 p + 1) < 2 * p
    rw [pow_succ']
    omega
  have h4 : 3 ≤ r := by
    have := Nat.le_log_of_pow_le (by decide : 1 < 2) (by omega : 2 ^ 2 ≤ p)
    omega
  exact ⟨r, h4, h2, h3⟩

private lemma zmod_ne_of_sub_bounds {p : ℕ} [NeZero p] {u v : ℤ}
    (hne : u ≠ v) (hlo : -(p : ℤ) < u - v) (hhi : u - v < (p : ℤ)) :
    (u : ZMod p) ≠ (v : ZMod p) := by
  intro h
  have hdvd : (p : ℤ) ∣ (u - v) := (ZMod.intCast_eq_intCast_iff_dvd_sub v u p).mp h.symm
  obtain ⟨k, hk⟩ := hdvd
  have hk0 : k = 0 := by
    have hp : (0 : ℤ) < p := by exact_mod_cast NeZero.pos p
    nlinarith
  rw [hk0, mul_zero] at hk
  exact hne (sub_eq_zero.mp hk)

private lemma zmod_eq_of_sub_bounds {p : ℕ} [NeZero p] {u v : ℤ}
    (hlo : -(p : ℤ) < u - v) (hhi : u - v < (p : ℤ)) (heq : (u : ZMod p) = (v : ZMod p)) :
    u = v := by
  by_contra hne
  exact zmod_ne_of_sub_bounds hne hlo hhi heq

private def hexPt (p : ℕ) (s : Bool) (x y : ℤ) :
    Bool × Multiplicative (ZMod p × ZMod p) :=
  (s, Multiplicative.ofAdd ((x : ZMod p), (y : ZMod p)))

private lemma hexPt_adj_0 {p : ℕ} (x y : ℤ) :
    (rightGraph (Multiplicative.ofAdd ((1 : ZMod p), (0 : ZMod p)))
      (Multiplicative.ofAdd ((0 : ZMod p), (1 : ZMod p)))).Adj
      (hexPt p false x y) (hexPt p true x y) :=
  ⟨by simp [hexPt], .inl ⟨rfl, rfl, .inl rfl⟩⟩

private lemma hexPt_adj_x {p : ℕ} (x y : ℤ) :
    (rightGraph (Multiplicative.ofAdd ((1 : ZMod p), (0 : ZMod p)))
      (Multiplicative.ofAdd ((0 : ZMod p), (1 : ZMod p)))).Adj
      (hexPt p false x y) (hexPt p true (x + 1) y) := by
  refine ⟨by simp [hexPt], .inl ⟨rfl, rfl, .inr (.inl ?_)⟩⟩
  change Multiplicative.ofAdd (((x + 1 : ℤ) : ZMod p), (y : ZMod p)) =
    Multiplicative.ofAdd ((x : ZMod p) + 1, (y : ZMod p) + 0)
  simp

private lemma hexPt_adj_y {p : ℕ} (x y : ℤ) :
    (rightGraph (Multiplicative.ofAdd ((1 : ZMod p), (0 : ZMod p)))
      (Multiplicative.ofAdd ((0 : ZMod p), (1 : ZMod p)))).Adj
      (hexPt p false x y) (hexPt p true x (y + 1)) := by
  refine ⟨by simp [hexPt], .inl ⟨rfl, rfl, .inr (.inr ?_)⟩⟩
  change Multiplicative.ofAdd ((x : ZMod p), ((y + 1 : ℤ) : ZMod p)) =
    Multiplicative.ofAdd ((x : ZMod p) + 0, (y : ZMod p) + 1)
  simp

private lemma hexPt_eq_iff {p : ℕ} {s₁ s₂ : Bool} {x₁ y₁ x₂ y₂ : ℤ} :
    hexPt p s₁ x₁ y₁ = hexPt p s₂ x₂ y₂ ↔
      s₁ = s₂ ∧ (x₁ : ZMod p) = (x₂ : ZMod p) ∧ (y₁ : ZMod p) = (y₂ : ZMod p) := by
  simp [hexPt]

set_option maxHeartbeats 800000 in
/-- Explicit closed-form `Θ(2^r, 2^r, 2^r)` on the hexagonal torus `ZMod p × ZMod p`
for every odd `p ≥ 5` with `p < 2^r < 2 * p`. -/
private theorem hex_theta_exists {p r : ℕ} [NeZero p]
    (hp : 5 ≤ p) (hodd : Odd p) (hr : 3 ≤ r) (hlo : p < 2 ^ r) (hhi : 2 ^ r < 2 * p) :
    ∃ (target : Multiplicative (ZMod p × ZMod p))
      (P : Fin 3 → ℕ → Bool × Multiplicative (ZMod p × ZMod p)),
      target ≠ 1 ∧
      (∀ c, P c 0 = (false, 1)) ∧
      (∀ c, P c (2 ^ r) = (false, target)) ∧
      (∀ c t, t < 2 ^ r →
        (rightGraph (Multiplicative.ofAdd ((1 : ZMod p), (0 : ZMod p)))
          (Multiplicative.ofAdd ((0 : ZMod p), (1 : ZMod p)))).Adj (P c t) (P c (t + 1))) ∧
      (∀ c t, 0 < t → t < 2 ^ r → P c t ≠ (false, 1) ∧ P c t ≠ (false, target)) ∧
      (∀ c₁ t₁ c₂ t₂, 0 < t₁ → t₁ < 2 ^ r → 0 < t₂ → t₂ < 2 ^ r →
        P c₁ t₁ = P c₂ t₂ → c₁ = c₂ ∧ t₁ = t₂) := by
  set L := 2 ^ r with hL_def
  have hL_even : 2 ∣ L := dvd_pow_self 2 (by omega)
  have hL8 : 8 ≤ L := by
    have := Nat.pow_le_pow_right (by decide : 0 < 2) hr
    simpa [hL_def] using this
  have hL_div : 2 * (L / 2) = L := Nat.mul_div_cancel' hL_even
  set m := p - L / 2 with hm_def
  have hm_pos : 1 ≤ m := by omega
  have hG_def := rightGraph (Multiplicative.ofAdd ((1 : ZMod p), (0 : ZMod p)))
    (Multiplicative.ofAdd ((0 : ZMod p), (1 : ZMod p)))
  by_cases hm1 : m = 1
  · -- Case A: `m = 1`, i.e., `L = 2 * p - 2` (Fermat-type modulus `p = 2^(r-1) + 1`).
    have hL_eq : L = 2 * p - 2 := by omega
    have h4L : 4 ∣ L := by
      have : 2 ^ 2 ∣ 2 ^ r := Nat.pow_dvd_pow 2 (by omega)
      simpa [hL_def] using this
    set k := (p - 1) / 2 with hk_def
    have hk2 : 2 ≤ k := by omega
    have hp_eq : p = 2 * k + 1 := by omega
    have hL_4k : L = 4 * k := by omega
    -- Integer coordinates `(side, x, y)` for the three arms from `(false, 0, 0)` to `(false, 1, 1)`
    let raw0 (t : ℕ) : Bool × ℤ × ℤ :=
      if t < 2 * p - 3 then
        if t % 2 = 0 then (false, -((t / 2 : ℕ) : ℤ), 0) else (true, -((t / 2 : ℕ) : ℤ), 0)
      else if t = 2 * p - 3 then (true, 2, 1)
      else (false, 1, 1)
    let raw1 (t : ℕ) : Bool × ℤ × ℤ :=
      if t = 0 then (false, 0, 0)
      else if t < L then
        if t % 2 = 1 then (true, 1, -((t / 2 : ℕ) : ℤ))
        else (false, 1, -((t / 2 : ℕ) : ℤ))
      else (false, 1, 1)
    let raw2 (t : ℕ) : Bool × ℤ × ℤ :=
      if t = 0 then (false, 0, 0)
      else if t = 1 then (true, 0, 1)
      else if t ≤ 2 * k then
        if t % 2 = 0 then (false, -1, ((t / 2 : ℕ) : ℤ))
        else (true, -1, ((t / 2 + 1 : ℕ) : ℤ))
      else if t ≤ 4 * k - 2 then
        if t % 2 = 1 then (true, 0, ((2 * k - t / 2 : ℕ) : ℤ))
        else (false, 0, ((2 * k - t / 2 : ℕ) : ℤ))
      else if t = 4 * k - 1 then (true, 1, 1)
      else (false, 1, 1)
    let raw : Fin 3 → ℕ → Bool × ℤ × ℤ := fun c =>
      match c with
      | ⟨0, _⟩ => raw0
      | ⟨1, _⟩ => raw1
      | ⟨2, _⟩ => raw2
    let P (c : Fin 3) (t : ℕ) := hexPt p (raw c t).1 (raw c t).2.1 (raw c t).2.2
    let target : Multiplicative (ZMod p × ZMod p) := Multiplicative.ofAdd ((1 : ZMod p), (1 : ZMod p))
    have htarget : target ≠ 1 := by
      intro h
      have h1 : ((1 : ℤ) : ZMod p) = ((0 : ℤ) : ZMod p) := by
        simpa [target] using congrArg (fun z => (Multiplicative.toAdd z).1) h
      exact zmod_ne_of_sub_bounds (by omega) (by omega) (by omega) h1
    have hP0 : ∀ c, P c 0 = (false, 1) := by
      intro c; fin_cases c <;> simp [P, raw, raw0, raw1, raw2, hexPt, show 0 < 2 * p - 3 by omega]
    have hPL : ∀ c, P c L = (false, target) := by
      intro c; fin_cases c
      · simp [P, raw, raw0, hexPt, target, show ¬ (L < 2 * p - 3) by omega,
          show L ≠ 2 * p - 3 by omega]
      · simp [P, raw, raw1, hexPt, target, show L ≠ 0 by omega]
      · simp [P, raw, raw2, hexPt, target, show L ≠ 0 by omega, show L ≠ 1 by omega,
          show ¬ (L ≤ 2 * k) by omega, show ¬ (L ≤ 4 * k - 2) by omega,
          show L ≠ 4 * k - 1 by omega]
    have hPadj : ∀ c t, t < L →
        (rightGraph (Multiplicative.ofAdd ((1 : ZMod p), (0 : ZMod p)))
          (Multiplicative.ofAdd ((0 : ZMod p), (1 : ZMod p)))).Adj (P c t) (P c (t + 1)) := by
      intro c t ht
      fin_cases c
      · -- arm 0
        dsimp only [P, raw]
        by_cases h1 : t < 2 * p - 4
        · have h1a : t < 2 * p - 3 := by omega
          have h1b : t + 1 < 2 * p - 3 := by omega
          simp only [raw0, h1a, h1b, ↓reduceIte]
          by_cases he : t % 2 = 0
          · have ho : (t + 1) % 2 ≠ 0 := by omega
            have hd : (t + 1) / 2 = t / 2 := by omega
            simp only [he, ho, ↓reduceIte, hd]
            exact hexPt_adj_0 _ _
          · have he2 : (t + 1) % 2 = 0 := by omega
            have hd : (t + 1) / 2 = t / 2 + 1 := by omega
            simp only [he, he2, ↓reduceIte, hd]
            have hstep : -((t / 2 : ℕ) : ℤ) = -((t / 2 + 1 : ℕ) : ℤ) + 1 := by push_cast; ring
            rw [hstep]
            exact (hexPt_adj_x _ _).symm
        · by_cases h2 : t = 2 * p - 4
          · have h2a : t < 2 * p - 3 := by omega
            have h2b : ¬ (t + 1 < 2 * p - 3) := by omega
            have h2c : t + 1 = 2 * p - 3 := by omega
            have he : t % 2 = 0 := by omega
            have hd : t / 2 = p - 2 := by omega
            simp only [raw0, h2a, h2b, h2c, he, hd, ↓reduceIte]
            have hmod : ((-((p - 2 : ℕ) : ℤ) : ℤ) : ZMod p) = ((2 : ℤ) : ZMod p) := by
              have h1 : ((-((p - 2 : ℕ) : ℤ) : ℤ) : ZMod p) = ((-(p - 2 : ℤ) : ℤ) : ZMod p) := by
                congr 1; omega
              rw [h1]
              exact (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ p).mpr ⟨1, by omega⟩
            have hpt : hexPt p false (-((p - 2 : ℕ) : ℤ)) 0 = hexPt p false 2 0 := by
              rw [hexPt_eq_iff]; exact ⟨rfl, hmod, rfl⟩
            rw [hpt]
            simpa using hexPt_adj_y (p := p) 2 0
          · have h3 : t = 2 * p - 3 := by omega
            have h3a : ¬ (t < 2 * p - 3) := by omega
            have h3b : ¬ (t + 1 < 2 * p - 3) := by omega
            have h3c : t + 1 ≠ 2 * p - 3 := by omega
            simp only [raw0, h3a, h3b, h3c, h3, ↓reduceIte]
            simpa using (hexPt_adj_x (p := p) 1 1).symm
      · -- arm 1
        dsimp only [P, raw]
        by_cases h0 : t = 0
        · subst h0
          simp only [raw1, ↓reduceIte, show (1 : ℕ) ≠ 0 by omega, show (1 : ℕ) < L by omega,
            show (1 : ℕ) % 2 = 1 by decide, show (1 : ℕ) / 2 = 0 by decide, Nat.cast_zero, neg_zero]
          simpa using hexPt_adj_x (p := p) 0 0
        · by_cases hlast : t + 1 = L
          · have hlt : t < L := by omega
            have ho : t % 2 = 1 := by omega
            have hd : t / 2 = p - 2 := by omega
            simp only [raw1, h0, hlt, ho, hd, hlast, show L ≠ 0 by omega, lt_irrefl, ↓reduceIte]
            have hmod : ((-((p - 2 : ℕ) : ℤ) : ℤ) : ZMod p) = ((2 : ℤ) : ZMod p) := by
              have h1 : ((-((p - 2 : ℕ) : ℤ) : ℤ) : ZMod p) = ((-(p - 2 : ℤ) : ℤ) : ZMod p) := by
                congr 1; omega
              rw [h1]
              exact (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ p).mpr ⟨1, by omega⟩
            have hpt : hexPt p true 1 (-((p - 2 : ℕ) : ℤ)) = hexPt p true 1 2 := by
              rw [hexPt_eq_iff]; exact ⟨rfl, rfl, hmod⟩
            rw [hpt]
            simpa using (hexPt_adj_y (p := p) 1 1).symm
          · have hlt1 : t < L := by omega
            have hlt2 : t + 1 < L := by omega
            have h0' : t + 1 ≠ 0 := by omega
            simp only [raw1, h0, h0', hlt1, hlt2, ↓reduceIte]
            by_cases ho : t % 2 = 1
            · have he : (t + 1) % 2 ≠ 1 := by omega
              have hd : (t + 1) / 2 = t / 2 + 1 := by omega
              simp only [ho, he, ↓reduceIte, hd]
              have hstep : -((t / 2 : ℕ) : ℤ) = -((t / 2 + 1 : ℕ) : ℤ) + 1 := by push_cast; ring
              rw [hstep]
              exact (hexPt_adj_y _ _).symm
            · have ho2 : (t + 1) % 2 = 1 := by omega
              have hd : (t + 1) / 2 = t / 2 := by omega
              simp only [ho, ho2, ↓reduceIte, hd]
              exact hexPt_adj_0 _ _
      · -- arm 2
        dsimp only [P, raw]
        by_cases h0 : t = 0
        · subst h0; simp only [raw2, ↓reduceIte, show (1 : ℕ) ≠ 0 by omega]
          simpa using hexPt_adj_y (p := p) 0 0
        · by_cases h1 : t = 1
          · subst h1
            simp only [raw2, show (1 : ℕ) ≠ 0 by omega, show (2 : ℕ) ≠ 0 by omega,
              show (2 : ℕ) ≠ 1 by omega, show 2 ≤ 2 * k by omega,
              show (2 : ℕ) % 2 = 0 by decide, show (2 : ℕ) / 2 = 1 by decide, Nat.cast_one, ↓reduceIte]
            simpa using (hexPt_adj_x (p := p) (-1) 1).symm
          · by_cases h2 : t < 2 * k
            · have h2a : t ≤ 2 * k := by omega
              have h2b : t + 1 ≤ 2 * k := by omega
              simp only [raw2, h0, h1, h2a, h2b, show t + 1 ≠ 0 by omega, show t + 1 ≠ 1 by omega,
                ↓reduceIte]
              by_cases he : t % 2 = 0
              · have ho : (t + 1) % 2 ≠ 0 := by omega
                have hd : (t + 1) / 2 = t / 2 := by omega
                simp only [he, ho, ↓reduceIte, hd]
                push_cast
                exact hexPt_adj_y _ _
              · have he2 : (t + 1) % 2 = 0 := by omega
                have hd : (t + 1) / 2 = t / 2 + 1 := by omega
                simp only [he, he2, ↓reduceIte, hd]
                exact (hexPt_adj_0 _ _).symm
            · by_cases h3 : t = 2 * k
              · subst h3
                simp only [raw2, show 2 * k ≠ 0 by omega, show 2 * k ≠ 1 by omega,
                  show 2 * k + 1 ≠ 0 by omega, show 2 * k + 1 ≠ 1 by omega,
                  le_refl, show ¬ (2 * k + 1 ≤ 2 * k) by omega,
                  show 2 * k + 1 ≤ 4 * k - 2 by omega,
                  show (2 * k) % 2 = 0 by omega, show (2 * k + 1) % 2 = 1 by omega,
                  show (2 * k) / 2 = k by omega, show (2 * k + 1) / 2 = k by omega,
                  show 2 * k - k = k by omega, ↓reduceIte]
                simpa using hexPt_adj_x (p := p) (-1) (k : ℤ)
              · by_cases h4 : t < 4 * k - 2
                · have h4a : ¬ (t ≤ 2 * k) := by omega
                  have h4b : t ≤ 4 * k - 2 := by omega
                  have h4c : ¬ (t + 1 ≤ 2 * k) := by omega
                  have h4d : t + 1 ≤ 4 * k - 2 := by omega
                  simp only [raw2, h0, h1, h4a, h4b, h4c, h4d, show t + 1 ≠ 0 by omega,
                    show t + 1 ≠ 1 by omega, ↓reduceIte]
                  by_cases ho : t % 2 = 1
                  · have he : (t + 1) % 2 ≠ 1 := by omega
                    have hd : (t + 1) / 2 = t / 2 + 1 := by omega
                    simp only [ho, he, ↓reduceIte, hd]
                    have hstep : ((2 * k - t / 2 : ℕ) : ℤ) = ((2 * k - (t / 2 + 1) : ℕ) : ℤ) + 1 := by
                      omega
                    rw [hstep]
                    exact (hexPt_adj_y _ _).symm
                  · have ho2 : (t + 1) % 2 = 1 := by omega
                    have hd : (t + 1) / 2 = t / 2 := by omega
                    simp only [ho, ho2, ↓reduceIte, hd]
                    exact hexPt_adj_0 _ _
                · by_cases h5 : t = 4 * k - 2
                  · subst h5
                    rw [show 4 * k - 2 + 1 = 4 * k - 1 by omega]
                    have he : (4 * k - 2) % 2 ≠ 1 := by omega
                    have hd : 2 * k - (4 * k - 2) / 2 = 1 := by omega
                    simp only [raw2, show 4 * k - 2 ≠ 0 by omega, show 4 * k - 2 ≠ 1 by omega,
                      show 4 * k - 1 ≠ 0 by omega, show 4 * k - 1 ≠ 1 by omega,
                      show ¬ (4 * k - 2 ≤ 2 * k) by omega, le_refl,
                      show ¬ (4 * k - 1 ≤ 2 * k) by omega, show ¬ (4 * k - 1 ≤ 4 * k - 2) by omega,
                      he, hd, Nat.cast_one, ↓reduceIte]
                    simpa using hexPt_adj_x (p := p) 0 1
                  · have h6 : t = 4 * k - 1 := by omega
                    subst h6
                    rw [show 4 * k - 1 + 1 = 4 * k by omega]
                    simp only [raw2, show 4 * k - 1 ≠ 0 by omega, show 4 * k - 1 ≠ 1 by omega,
                      show 4 * k ≠ 0 by omega, show 4 * k ≠ 1 by omega,
                      show ¬ (4 * k - 1 ≤ 2 * k) by omega, show ¬ (4 * k - 1 ≤ 4 * k - 2) by omega,
                      show ¬ (4 * k ≤ 2 * k) by omega, show ¬ (4 * k ≤ 4 * k - 2) by omega,
                      show 4 * k ≠ 4 * k - 1 by omega, ↓reduceIte]
                    exact (hexPt_adj_0 (p := p) 1 1).symm
    -- Coordinate bounds for interior vertices of each arm in Case A (`m = 1`)
    have h0_info (t : ℕ) (ht0 : 0 < t) (htL : t < L) :
        (t < 2 * p - 3 ∧ (raw0 t).2.2 = 0 ∧ -(p - 2 : ℤ) ≤ (raw0 t).2.1 ∧ (raw0 t).2.1 ≤ 0 ∧
          (raw0 t).1 = decide (t % 2 = 1) ∧ (raw0 t).2.1 = -((t / 2 : ℕ) : ℤ)) ∨
        (t = 2 * p - 3 ∧ raw0 t = (true, 2, 1)) := by
      by_cases h1 : t < 2 * p - 3
      · left; simp only [raw0, h1, ↓reduceIte]
        by_cases he : t % 2 = 0
        · simp [he, show t % 2 ≠ 1 by omega]; omega
        · simp [he, show t % 2 = 1 by omega]; omega
      · right; refine ⟨by omega, ?_⟩; simp [raw0, h1, show t = 2 * p - 3 by omega]
    have h1_info (t : ℕ) (ht0 : 0 < t) (htL : t < L) :
        (raw1 t).2.1 = 1 ∧ (raw1 t).1 = decide (t % 2 = 1) ∧
        (raw1 t).2.2 = -((t / 2 : ℕ) : ℤ) ∧ -(p - 2 : ℤ) ≤ (raw1 t).2.2 ∧ (raw1 t).2.2 ≤ 0 := by
      simp only [raw1, show t ≠ 0 by omega, htL, ↓reduceIte]
      by_cases ho : t % 2 = 1
      · simp [ho]; omega
      · simp [ho]; omega
    have h2_info (t : ℕ) (ht0 : 0 < t) (htL : t < L) :
        1 ≤ (raw2 t).2.2 ∧ (raw2 t).2.2 ≤ (k : ℤ) ∧
        -1 ≤ (raw2 t).2.1 ∧ (raw2 t).2.1 ≤ 1 ∧
        ((raw2 t).2.1 = 1 → t = 4 * k - 1 ∧ raw2 t = (true, 1, 1)) ∧
        ((raw2 t).2.1 = -1 → 2 ≤ t ∧ t ≤ 2 * k) ∧
        ((raw2 t).2.1 = 0 → t = 1 ∨ (2 * k < t ∧ t ≤ 4 * k - 2)) := by
      by_cases h1 : t = 1
      · subst h1; simp [raw2]; omega
      · by_cases h2 : t ≤ 2 * k
        · simp only [raw2, show t ≠ 0 by omega, h1, h2, ↓reduceIte]
          split_ifs <;> (dsimp only; refine ⟨by omega, by omega, by omega, by omega,
            by intro h; norm_num at h, fun _ => ⟨by omega, trivial⟩, by intro h; norm_num at h⟩)
        · by_cases h3 : t ≤ 4 * k - 2
          · simp only [raw2, show t ≠ 0 by omega, h1, h2, h3, ↓reduceIte]
            split_ifs <;> (dsimp only; refine ⟨by omega, by omega, by omega, by omega,
              by intro h; norm_num at h, by intro h; norm_num at h, fun _ => Or.inr ⟨by omega, trivial⟩⟩)
          · have h4 : t = 4 * k - 1 := by omega
            subst h4
            simp only [raw2, show 4 * k - 1 ≠ 0 by omega, h1, h2, h3, ↓reduceIte]
            exact ⟨by omega, by omega, by omega, by omega, fun _ => ⟨trivial, trivial⟩,
              by intro h; norm_num at h, by intro h; norm_num at h⟩
    have hPavoid : ∀ c t, 0 < t → t < L → P c t ≠ (false, 1) ∧ P c t ≠ (false, target) := by
      intro c t ht0 htL
      have h0pt : (false, (1 : Multiplicative (ZMod p × ZMod p))) = hexPt p false 0 0 := by
        simp [hexPt]; rfl
      have htpt : (false, target) = hexPt p false 1 1 := by simp [hexPt, target]
      rw [h0pt, htpt]
      fin_cases c
      · dsimp only [P, raw]
        rcases h0_info t ht0 htL with ⟨_, hy, hxlo, hxhi, hs, hx⟩ | ⟨_, hr⟩
        · constructor
          · intro h; rw [hexPt_eq_iff] at h
            have hs' : t % 2 ≠ 1 := by simpa [hs] using h.1
            have hx0 := zmod_eq_of_sub_bounds (by omega) (by omega) h.2.1
            omega
          · intro h; rw [hexPt_eq_iff] at h
            exact zmod_ne_of_sub_bounds (by omega) (by omega) (by omega) h.2.2
        · rw [hr]; constructor <;> (intro h; rw [hexPt_eq_iff] at h; exact Bool.noConfusion h.1)
      · dsimp only [P, raw]
        obtain ⟨hx, _, _, hylo, hyhi⟩ := h1_info t ht0 htL
        constructor
        · intro h; rw [hexPt_eq_iff] at h
          exact zmod_ne_of_sub_bounds (by omega) (by omega) (by omega) h.2.1
        · intro h; rw [hexPt_eq_iff] at h
          exact zmod_ne_of_sub_bounds (by omega) (by omega) (by omega) h.2.2
      · dsimp only [P, raw]
        obtain ⟨hylo, hyhi, hxlo, hxhi, hx1, _, _⟩ := h2_info t ht0 htL
        constructor
        · intro h; rw [hexPt_eq_iff] at h
          exact zmod_ne_of_sub_bounds (by omega) (by omega) (by omega) h.2.2
        · intro h; rw [hexPt_eq_iff] at h
          have hxeq : (raw2 t).2.1 = 1 := zmod_eq_of_sub_bounds (by omega) (by omega) h.2.1
          have htrue := (hx1 hxeq).2
          rw [htrue] at h
          exact Bool.noConfusion h.1
    have hPinj : ∀ c₁ t₁ c₂ t₂, 0 < t₁ → t₁ < L → 0 < t₂ → t₂ < L →
        P c₁ t₁ = P c₂ t₂ → c₁ = c₂ ∧ t₁ = t₂ := by
      intro c₁ t₁ c₂ t₂ ht₁0 ht₁L ht₂0 ht₂L heq
      rw [hexPt_eq_iff] at heq
      obtain ⟨hs, hx, hy⟩ := heq
      fin_cases c₁ <;> fin_cases c₂
      · -- (0, 0)
        refine ⟨rfl, ?_⟩
        dsimp only [raw] at hs hx hy
        rcases h0_info t₁ ht₁0 ht₁L with ⟨_, hy1, hx1lo, hx1hi, hs1, hx1⟩ | ⟨ht1, hr1⟩ <;>
        rcases h0_info t₂ ht₂0 ht₂L with ⟨_, hy2, hx2lo, hx2hi, hs2, hx2⟩ | ⟨ht2, hr2⟩
        · have hxeq := zmod_eq_of_sub_bounds (by omega) (by omega) hx
          have hseq : decide (t₁ % 2 = 1) = decide (t₂ % 2 = 1) := by rwa [hs1, hs2] at hs
          have hmod : t₁ % 2 = t₂ % 2 := by
            by_cases h1 : t₁ % 2 = 1 <;> by_cases h2 : t₂ % 2 = 1 <;> simp [h1, h2] at hseq <;> omega
          omega
        · rw [hr2] at hy; dsimp only at hy; exact (zmod_ne_of_sub_bounds (by omega) (by omega) (by omega) hy).elim
        · rw [hr1] at hy; dsimp only at hy; exact (zmod_ne_of_sub_bounds (by omega) (by omega) (by omega) hy).elim
        · omega
      · -- (0, 1)
        dsimp only [raw] at hs hx hy
        obtain ⟨hx2, _, _, hy2lo, hy2hi⟩ := h1_info t₂ ht₂0 ht₂L
        rcases h0_info t₁ ht₁0 ht₁L with ⟨_, _, hx1lo, hx1hi, _, _⟩ | ⟨_, hr1⟩
        · exact (zmod_ne_of_sub_bounds (by omega) (by omega) (by omega) hx).elim
        · rw [hr1] at hy; dsimp only at hy; exact (zmod_ne_of_sub_bounds (by omega) (by omega) (by omega) hy).elim
      · -- (0, 2)
        dsimp only [raw] at hs hx hy
        obtain ⟨hy2lo, hy2hi, hx2lo, hx2hi, _, _, _⟩ := h2_info t₂ ht₂0 ht₂L
        rcases h0_info t₁ ht₁0 ht₁L with ⟨_, hy1, _, _, _, _⟩ | ⟨_, hr1⟩
        · exact (zmod_ne_of_sub_bounds (by omega) (by omega) (by omega) hy).elim
        · rw [hr1] at hx; dsimp only at hx; exact (zmod_ne_of_sub_bounds (by omega) (by omega) (by omega) hx).elim
      · -- (1, 0)
        dsimp only [raw] at hs hx hy
        obtain ⟨hx1, _, _, hy1lo, hy1hi⟩ := h1_info t₁ ht₁0 ht₁L
        rcases h0_info t₂ ht₂0 ht₂L with ⟨_, _, hx2lo, hx2hi, _, _⟩ | ⟨_, hr2⟩
        · exact (zmod_ne_of_sub_bounds (by omega) (by omega) (by omega) hx).elim
        · rw [hr2] at hy; dsimp only at hy; exact (zmod_ne_of_sub_bounds (by omega) (by omega) (by omega) hy).elim
      · -- (1, 1)
        refine ⟨rfl, ?_⟩
        dsimp only [raw] at hs hx hy
        obtain ⟨_, hs1, hy1, hy1lo, hy1hi⟩ := h1_info t₁ ht₁0 ht₁L
        obtain ⟨_, hs2, hy2, hy2lo, hy2hi⟩ := h1_info t₂ ht₂0 ht₂L
        have hyeq := zmod_eq_of_sub_bounds (by omega) (by omega) hy
        have hseq : decide (t₁ % 2 = 1) = decide (t₂ % 2 = 1) := by rwa [hs1, hs2] at hs
        have hmod : t₁ % 2 = t₂ % 2 := by
          by_cases h1 : t₁ % 2 = 1 <;> by_cases h2 : t₂ % 2 = 1 <;> simp [h1, h2] at hseq <;> omega
        omega
      · -- (1, 2)
        dsimp only [raw] at hs hx hy
        obtain ⟨hx1, _, _, hy1lo, hy1hi⟩ := h1_info t₁ ht₁0 ht₁L
        obtain ⟨hy2lo, hy2hi, hx2lo, hx2hi, hx2_1, _, _⟩ := h2_info t₂ ht₂0 ht₂L
        have hxeq : (raw1 t₁).2.1 = (raw2 t₂).2.1 := zmod_eq_of_sub_bounds (by omega) (by omega) hx
        have hr2 := (hx2_1 (hxeq.symm.trans hx1)).2
        rw [hr2] at hy; dsimp only at hy
        exact (zmod_ne_of_sub_bounds (by omega) (by omega) (by omega) hy).elim
      · -- (2, 0)
        dsimp only [raw] at hs hx hy
        obtain ⟨hy1lo, hy1hi, hx1lo, hx1hi, _, _, _⟩ := h2_info t₁ ht₁0 ht₁L
        rcases h0_info t₂ ht₂0 ht₂L with ⟨_, hy2, _, _, _, _⟩ | ⟨_, hr2⟩
        · exact (zmod_ne_of_sub_bounds (by omega) (by omega) (by omega) hy).elim
        · rw [hr2] at hx; dsimp only at hx; exact (zmod_ne_of_sub_bounds (by omega) (by omega) (by omega) hx).elim
      · -- (2, 1)
        dsimp only [raw] at hs hx hy
        obtain ⟨hy1lo, hy1hi, hx1lo, hx1hi, hx1_1, _, _⟩ := h2_info t₁ ht₁0 ht₁L
        obtain ⟨hx2, _, _, hy2lo, hy2hi⟩ := h1_info t₂ ht₂0 ht₂L
        have hxeq : (raw2 t₁).2.1 = (raw1 t₂).2.1 := zmod_eq_of_sub_bounds (by omega) (by omega) hx
        have hr1 := (hx1_1 (hxeq.trans hx2)).2
        rw [hr1] at hy; dsimp only at hy
        exact (zmod_ne_of_sub_bounds (by omega) (by omega) (by omega) hy).elim
      · -- (2, 2)
        refine ⟨rfl, ?_⟩
        dsimp only [raw] at hs hx hy
        obtain ⟨hy1lo, hy1hi, hx1lo, hx1hi, hx1_1, hx1_m1, hx1_0⟩ := h2_info t₁ ht₁0 ht₁L
        obtain ⟨hy2lo, hy2hi, hx2lo, hx2hi, hx2_1, hx2_m1, hx2_0⟩ := h2_info t₂ ht₂0 ht₂L
        have hxeq := zmod_eq_of_sub_bounds (by omega) (by omega) hx
        have hyeq := zmod_eq_of_sub_bounds (by omega) (by omega) hy
        have hcol_cases : (raw2 t₁).2.1 = 1 ∨ (raw2 t₁).2.1 = 0 ∨ (raw2 t₁).2.1 = -1 := by omega
        rcases hcol_cases with hc1 | hc0 | hcm1
        · have ht1 := (hx1_1 hc1).1
          have ht2 := (hx2_1 (hxeq.symm.trans hc1)).1
          omega
        · rcases hx1_0 hc0 with rfl | ⟨h1a, h1b⟩ <;>
          rcases hx2_0 (hxeq.symm.trans hc0) with rfl | ⟨h2a, h2b⟩
          · rfl
          · simp only [raw2, show (1 : ℕ) ≠ 0 by omega, show t₂ ≠ 0 by omega,
              show t₂ ≠ 1 by omega, show ¬ (t₂ ≤ 2 * k) by omega, h2b, ↓reduceIte] at hs hyeq
            by_cases ho : t₂ % 2 = 1
            · simp only [ho, ↓reduceIte] at hyeq; omega
            · simp only [ho, ↓reduceIte] at hs; exact Bool.noConfusion hs
          · simp only [raw2, show (1 : ℕ) ≠ 0 by omega, show t₁ ≠ 0 by omega,
              show t₁ ≠ 1 by omega, show ¬ (t₁ ≤ 2 * k) by omega, h1b, ↓reduceIte] at hs hyeq
            by_cases ho : t₁ % 2 = 1
            · simp only [ho, ↓reduceIte] at hyeq; omega
            · simp only [ho, ↓reduceIte] at hs; exact Bool.noConfusion hs
          · simp only [raw2, show t₁ ≠ 0 by omega, show t₁ ≠ 1 by omega,
              show ¬ (t₁ ≤ 2 * k) by omega, h1b, show t₂ ≠ 0 by omega, show t₂ ≠ 1 by omega,
              show ¬ (t₂ ≤ 2 * k) by omega, h2b, ↓reduceIte] at hs hyeq
            by_cases ho1 : t₁ % 2 = 1 <;> by_cases ho2 : t₂ % 2 = 1 <;>
              simp only [ho1, ho2, ↓reduceIte] at hs hyeq <;> first | exact Bool.noConfusion hs | exact Bool.noConfusion hs | omega
        · have ⟨h1a, h1b⟩ := hx1_m1 hcm1
          have ⟨h2a, h2b⟩ := hx2_m1 (hxeq.symm.trans hcm1)
          simp only [raw2, show t₁ ≠ 0 by omega, show t₁ ≠ 1 by omega, h1b,
            show t₂ ≠ 0 by omega, show t₂ ≠ 1 by omega, h2b, ↓reduceIte] at hs hyeq
          by_cases he1 : t₁ % 2 = 0 <;> by_cases he2 : t₂ % 2 = 0 <;>
            simp only [he1, he2, ↓reduceIte] at hs hyeq <;> first | exact Bool.noConfusion hs | exact Bool.noConfusion hs | omega
    exact ⟨target, P, htarget, hP0, hPL, hPadj, hPavoid, hPinj⟩
  · -- Case B: `m ≥ 2`, endpoint `(false, (0, m))` where `m = p - L / 2` (`2 ≤ m ≤ p - 4`).
    have hm2 : 2 ≤ m := by omega
    have hL_ge_p1 : p + 1 ≤ L := by omega
    have hpar : 2 ∣ (L - p - 1) := by
      obtain ⟨j, hj⟩ := hodd
      omega
    set a := (L - p - 1) / 2 with ha_def
    have ha_eq : 2 * a = L - p - 1 := Nat.mul_div_cancel' hpar
    have ham : a + m = (p - 1) / 2 := by omega
    -- `arm0`: straight down in col `0` from `(false, 0, 0)` to `(false, 0, -(L/2))`
    let raw0 (t : ℕ) : Bool × ℤ × ℤ :=
      if t % 2 = 0 then (false, 0, -((t / 2 : ℕ) : ℤ))
      else (true, 0, -((t / 2 : ℕ) : ℤ))
    -- `arm1`: cols `1, 2` (if `a = 0`, straight up in col `1`; else down to `-a` in col `1`, up in col `2` to `m-1`, exit via col `1`)
    let raw1 (t : ℕ) : Bool × ℤ × ℤ :=
      if t = 0 then (false, 0, 0)
      else if t = L then (false, 0, (m : ℤ))
      else if a = 0 then
        if t % 2 = 1 then (true, 1, ((t / 2 : ℕ) : ℤ))
        else (false, 1, ((t / 2 - 1 : ℕ) : ℤ))
      else if t ≤ 2 * a then
        if t % 2 = 1 then (true, 1, -((t / 2 : ℕ) : ℤ))
        else (false, 1, -((t / 2 : ℕ) : ℤ))
      else if t ≤ L - 3 then
        if t % 2 = 1 then (true, 2, ((t / 2 : ℕ) : ℤ) - (2 * a : ℤ))
        else (false, 2, ((t / 2 - 1 : ℕ) : ℤ) - (2 * a : ℤ))
      else if t = L - 2 then (false, 1, (m : ℤ) - 1)
      else (true, 1, (m : ℤ))
    -- `arm2`: `(true, 0, 1)`, cols `-1, -2`, `(true, 0, m)`
    let raw2 (t : ℕ) : Bool × ℤ × ℤ :=
      if t = 0 then (false, 0, 0)
      else if t = 1 then (true, 0, 1)
      else if t = L - 1 then (true, 0, (m : ℤ))
      else if t = L then (false, 0, (m : ℤ))
      else if a = 0 then
        if t % 2 = 0 then (false, -1, ((t / 2 : ℕ) : ℤ))
        else (true, -1, ((t / 2 + 1 : ℕ) : ℤ))
      else if t ≤ 2 * a + 1 then
        if t % 2 = 0 then (false, -1, 2 - ((t / 2 : ℕ) : ℤ))
        else (true, -1, 2 - ((t / 2 : ℕ) : ℤ))
      else if t ≤ L - 4 then
        if t % 2 = 0 then (false, -2, ((t / 2 : ℕ) : ℤ) - (2 * a - 1 : ℤ))
        else (true, -2, ((t / 2 + 1 : ℕ) : ℤ) - (2 * a - 1 : ℤ))
      else if t = L - 3 then (true, -1, (m : ℤ))
      else (false, -1, (m : ℤ))
    let raw : Fin 3 → ℕ → Bool × ℤ × ℤ := fun c =>
      match c with
      | ⟨0, _⟩ => raw0
      | ⟨1, _⟩ => raw1
      | ⟨2, _⟩ => raw2
    let P (c : Fin 3) (t : ℕ) := hexPt p (raw c t).1 (raw c t).2.1 (raw c t).2.2
    let target : Multiplicative (ZMod p × ZMod p) := Multiplicative.ofAdd ((0 : ZMod p), ((m : ℤ) : ZMod p))
    have htarget : target ≠ 1 := by
      intro h
      have h1 : ((m : ℤ) : ZMod p) = ((0 : ℤ) : ZMod p) := by
        simpa [target] using congrArg (fun z => (Multiplicative.toAdd z).2) h
      exact zmod_ne_of_sub_bounds (by omega) (by omega) (by omega) h1
    have hmod_m : ((-((L / 2 : ℕ) : ℤ) : ℤ) : ZMod p) = ((m : ℤ) : ZMod p) := by
      exact (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ p).mpr ⟨1, by omega⟩
    have hP0 : ∀ c, P c 0 = (false, 1) := by
      intro c; fin_cases c <;> simp [P, raw, raw0, raw1, raw2, hexPt]
    have hPL : ∀ c, P c L = (false, target) := by
      intro c; fin_cases c
      · simp only [P, raw, raw0, show L % 2 = 0 by omega, ↓reduceIte]
        have ht : (false, target) = hexPt p false 0 (m : ℤ) := by simp [hexPt, target]
        rw [ht, hexPt_eq_iff]; exact ⟨rfl, rfl, hmod_m⟩
      · simp [P, raw, raw1, hexPt, target, show L ≠ 0 by omega]
      · simp [P, raw, raw2, hexPt, target, show L ≠ 0 by omega, show L ≠ 1 by omega,
          show L ≠ L - 1 by omega]
    have hPadj : ∀ c t, t < L →
        (rightGraph (Multiplicative.ofAdd ((1 : ZMod p), (0 : ZMod p)))
          (Multiplicative.ofAdd ((0 : ZMod p), (1 : ZMod p)))).Adj (P c t) (P c (t + 1)) := by
      intro c t ht
      fin_cases c
      · -- arm 0
        dsimp only [P, raw]
        by_cases he : t % 2 = 0
        · have ho : (t + 1) % 2 ≠ 0 := by omega
          have hd : (t + 1) / 2 = t / 2 := by omega
          simp only [raw0, he, ho, hd, ↓reduceIte]
          exact hexPt_adj_0 _ _
        · have he2 : (t + 1) % 2 = 0 := by omega
          have hd : (t + 1) / 2 = t / 2 + 1 := by omega
          simp only [raw0, he, he2, hd, ↓reduceIte]
          have hstep : -((t / 2 : ℕ) : ℤ) = -((t / 2 + 1 : ℕ) : ℤ) + 1 := by push_cast; ring
          rw [hstep]
          exact (hexPt_adj_y _ _).symm
      · -- arm 1
        dsimp only [P, raw]
        by_cases ha0 : a = 0
        · have hL_m : L = 2 * m + 2 := by omega
          by_cases h0 : t = 0
          · subst h0
            simp only [raw1, ha0, ↓reduceIte, show (1 : ℕ) ≠ 0 by omega, show (1 : ℕ) ≠ L by omega,
              show (1 : ℕ) % 2 = 1 by decide, show (1 : ℕ) / 2 = 0 by decide, Nat.cast_zero]
            simpa using hexPt_adj_x (p := p) 0 0
          · by_cases hlast : t + 1 = L
            · have ho : t % 2 = 1 := by omega
              have hd : t / 2 = m := by omega
              simp only [raw1, ha0, h0, show t ≠ L by omega, hlast, show L ≠ 0 by omega,
                ho, hd, ↓reduceIte]
              simpa using (hexPt_adj_x (p := p) 0 (m : ℤ)).symm
            · simp only [raw1, ha0, h0, show t ≠ L by omega, show t + 1 ≠ 0 by omega,
                hlast, ↓reduceIte]
              by_cases ho : t % 2 = 1
              · have he : (t + 1) % 2 ≠ 1 := by omega
                have hd : (t + 1) / 2 - 1 = t / 2 := by omega
                simp only [ho, he, hd, ↓reduceIte]
                exact (hexPt_adj_0 _ _).symm
              · have ho2 : (t + 1) % 2 = 1 := by omega
                have hd : (t + 1) / 2 = (t / 2 - 1) + 1 := by omega
                simp only [ho, ho2, hd, ↓reduceIte]
                push_cast
                exact hexPt_adj_y _ _
        · -- `a ≥ 1`
          have ha1 : 1 ≤ a := by omega
          have h2a_lt : 2 * a ≤ L - 3 := by omega
          by_cases h0 : t = 0
          · subst h0
            simp only [raw1, ha0, ↓reduceIte, show (1 : ℕ) ≠ 0 by omega, show (1 : ℕ) ≠ L by omega,
              show 1 ≤ 2 * a by omega, show (1 : ℕ) % 2 = 1 by decide, show (1 : ℕ) / 2 = 0 by decide,
              Nat.cast_zero, neg_zero]
            simpa using hexPt_adj_x (p := p) 0 0
          · by_cases h1 : t < 2 * a
            · simp only [raw1, ha0, h0, show t ≠ L by omega, show t + 1 ≠ 0 by omega,
                show t + 1 ≠ L by omega, show t ≤ 2 * a by omega, show t + 1 ≤ 2 * a by omega,
                ↓reduceIte]
              by_cases ho : t % 2 = 1
              · have he : (t + 1) % 2 ≠ 1 := by omega
                have hd : (t + 1) / 2 = t / 2 + 1 := by omega
                simp only [ho, he, hd, ↓reduceIte]
                have hstep : -((t / 2 : ℕ) : ℤ) = -((t / 2 + 1 : ℕ) : ℤ) + 1 := by push_cast; ring
                rw [hstep]
                exact (hexPt_adj_y _ _).symm
              · have ho2 : (t + 1) % 2 = 1 := by omega
                have hd : (t + 1) / 2 = t / 2 := by omega
                simp only [ho, ho2, hd, ↓reduceIte]
                exact hexPt_adj_0 _ _
            · by_cases h2 : t = 2 * a
              · subst h2
                simp only [raw1, ha0, show 2 * a ≠ 0 by omega, show 2 * a ≠ L by omega,
                  show 2 * a + 1 ≠ 0 by omega, show 2 * a + 1 ≠ L by omega,
                  le_refl, show ¬ (2 * a + 1 ≤ 2 * a) by omega, show 2 * a + 1 ≤ L - 3 by omega,
                  show (2 * a) % 2 ≠ 1 by omega, show (2 * a + 1) % 2 = 1 by omega,
                  show (2 * a) / 2 = a by omega, show (2 * a + 1) / 2 = a by omega, ↓reduceIte]
                have hyeq : ((a : ℤ) - (2 * a : ℤ)) = -(a : ℤ) := by ring
                rw [hyeq]
                simpa using hexPt_adj_x (p := p) 1 (-(a : ℤ))
              · by_cases h3 : t < L - 3
                · simp only [raw1, ha0, h0, show t ≠ L by omega, show t + 1 ≠ 0 by omega,
                    show t + 1 ≠ L by omega, show ¬ (t ≤ 2 * a) by omega,
                    show ¬ (t + 1 ≤ 2 * a) by omega, show t ≤ L - 3 by omega,
                    show t + 1 ≤ L - 3 by omega, ↓reduceIte]
                  by_cases ho : t % 2 = 1
                  · have he : (t + 1) % 2 ≠ 1 := by omega
                    have hd : (t + 1) / 2 - 1 = t / 2 := by omega
                    simp only [ho, he, hd, ↓reduceIte]
                    exact (hexPt_adj_0 _ _).symm
                  · have ho2 : (t + 1) % 2 = 1 := by omega
                    have hd : (t + 1) / 2 = (t / 2 - 1) + 1 := by omega
                    simp only [ho, ho2, hd, ↓reduceIte]
                    have hstep : (((t / 2 - 1 + 1 : ℕ) : ℤ) - (2 * a : ℤ)) =
                        (((t / 2 - 1 : ℕ) : ℤ) - (2 * a : ℤ)) + 1 := by push_cast; ring
                    rw [hstep]
                    exact hexPt_adj_y _ _
                · by_cases h4 : t = L - 3
                  · subst h4
                    rw [show L - 3 + 1 = L - 2 by omega]
                    have ho : (L - 3) % 2 = 1 := by omega
                    have hyeq : (((L - 3) / 2 : ℕ) : ℤ) - (2 * a : ℤ) = (m : ℤ) - 1 := by omega
                    simp only [raw1, ha0, show L - 3 ≠ 0 by omega, show L - 3 ≠ L by omega,
                      show L - 2 ≠ 0 by omega, show L - 2 ≠ L by omega,
                      show ¬ (L - 3 ≤ 2 * a) by omega, le_refl,
                      show ¬ (L - 2 ≤ 2 * a) by omega, show ¬ (L - 2 ≤ L - 3) by omega,
                      ho, hyeq, ↓reduceIte]
                    simpa using (hexPt_adj_x (p := p) 1 ((m : ℤ) - 1)).symm
                  · by_cases h5 : t = L - 2
                    · subst h5
                      rw [show L - 2 + 1 = L - 1 by omega]
                      simp only [raw1, ha0, show L - 2 ≠ 0 by omega, show L - 2 ≠ L by omega,
                        show L - 1 ≠ 0 by omega, show L - 1 ≠ L by omega,
                        show ¬ (L - 2 ≤ 2 * a) by omega, show ¬ (L - 2 ≤ L - 3) by omega,
                        show ¬ (L - 1 ≤ 2 * a) by omega, show ¬ (L - 1 ≤ L - 3) by omega,
                        show L - 1 ≠ L - 2 by omega, ↓reduceIte]
                      simpa [sub_add_cancel] using hexPt_adj_y (p := p) 1 ((m : ℤ) - 1)
                    · have h6 : t = L - 1 := by omega
                      subst h6
                      rw [show L - 1 + 1 = L by omega]
                      simp only [raw1, ha0, show L - 1 ≠ 0 by omega, show L - 1 ≠ L by omega,
                        show L ≠ 0 by omega,
                        show ¬ (L - 1 ≤ 2 * a) by omega, show ¬ (L - 1 ≤ L - 3) by omega,
                        show L - 1 ≠ L - 2 by omega, ↓reduceIte]
                      simpa using (hexPt_adj_x (p := p) 0 (m : ℤ)).symm
      · -- arm 2
        dsimp only [P, raw]
        by_cases h0 : t = 0
        · subst h0
          simp only [raw2, ↓reduceIte, show (1 : ℕ) ≠ 0 by omega]
          simpa using hexPt_adj_y (p := p) 0 0
        · by_cases hlast : t = L - 1
          · subst hlast
            simp only [raw2, show L - 1 ≠ 0 by omega, show L - 1 ≠ 1 by omega,
              show L - 1 + 1 = L by omega, show L ≠ 0 by omega, show L ≠ 1 by omega,
              show L ≠ L - 1 by omega, ↓reduceIte]
            exact (hexPt_adj_0 (p := p) 0 (m : ℤ)).symm
          · by_cases ha0 : a = 0
            · have hL_m : L = 2 * m + 2 := by omega
              by_cases h1 : t = 1
              · subst h1
                simp only [raw2, ha0, show (1 : ℕ) ≠ 0 by omega, show (2 : ℕ) ≠ 0 by omega,
                  show (2 : ℕ) ≠ 1 by omega, show 2 ≠ L - 1 by omega, show 2 ≠ L by omega,
                  show (2 : ℕ) % 2 = 0 by decide, show (2 : ℕ) / 2 = 1 by decide, Nat.cast_one, ↓reduceIte]
                simpa using (hexPt_adj_x (p := p) (-1) 1).symm
              · by_cases hpen : t = L - 2
                · subst hpen
                  have he : (L - 2) % 2 = 0 := by omega
                  have hd : (L - 2) / 2 = m := by omega
                  simp only [raw2, ha0, show L - 2 ≠ 0 by omega, show L - 2 ≠ 1 by omega,
                    show L - 2 ≠ L - 1 by omega, show L - 2 ≠ L by omega,
                    show L - 2 + 1 = L - 1 by omega, show L - 1 ≠ 0 by omega, show L - 1 ≠ 1 by omega,
                    he, hd, ↓reduceIte]
                  simpa using hexPt_adj_x (p := p) (-1) (m : ℤ)
                · simp only [raw2, ha0, h0, h1, hlast, show t ≠ L by omega,
                    show t + 1 ≠ 0 by omega, show t + 1 ≠ 1 by omega,
                    show t + 1 ≠ L - 1 by omega, show t + 1 ≠ L by omega, ↓reduceIte]
                  by_cases he : t % 2 = 0
                  · have ho : (t + 1) % 2 ≠ 0 := by omega
                    have hd : (t + 1) / 2 = t / 2 := by omega
                    simp only [he, ho, hd, ↓reduceIte]
                    push_cast; exact hexPt_adj_y _ _
                  · have he2 : (t + 1) % 2 = 0 := by omega
                    have hd : (t + 1) / 2 = t / 2 + 1 := by omega
                    simp only [he, he2, hd, ↓reduceIte]
                    exact (hexPt_adj_0 _ _).symm
            · -- `a ≥ 1`
              have ha1 : 1 ≤ a := by omega
              have h2a1_lt : 2 * a + 1 ≤ L - 4 := by omega
              by_cases h1 : t = 1
              · subst h1
                simp only [raw2, ha0, show (1 : ℕ) ≠ 0 by omega, show (2 : ℕ) ≠ 0 by omega,
                  show (2 : ℕ) ≠ 1 by omega, show 2 ≠ L - 1 by omega, show 2 ≠ L by omega,
                  show 2 ≤ 2 * a + 1 by omega, show (2 : ℕ) % 2 = 0 by decide,
                  show (2 : ℕ) / 2 = 1 by decide, Nat.cast_one, ↓reduceIte]
                have h21 : (2 : ℤ) - 1 = 1 := by ring
                rw [h21]
                simpa using (hexPt_adj_x (p := p) (-1) 1).symm
              · by_cases h2 : t < 2 * a + 1
                · simp only [raw2, ha0, h0, h1, hlast, show t ≠ L by omega,
                    show t + 1 ≠ 0 by omega, show t + 1 ≠ 1 by omega,
                    show t + 1 ≠ L - 1 by omega, show t + 1 ≠ L by omega,
                    show t ≤ 2 * a + 1 by omega, show t + 1 ≤ 2 * a + 1 by omega, ↓reduceIte]
                  by_cases he : t % 2 = 0
                  · have ho : (t + 1) % 2 ≠ 0 := by omega
                    have hd : (t + 1) / 2 = t / 2 := by omega
                    simp only [he, ho, hd, ↓reduceIte]
                    exact hexPt_adj_0 _ _
                  · have he2 : (t + 1) % 2 = 0 := by omega
                    have hd : (t + 1) / 2 = t / 2 + 1 := by omega
                    simp only [he, he2, hd, ↓reduceIte]
                    have hstep : 2 - ((t / 2 : ℕ) : ℤ) = (2 - ((t / 2 + 1 : ℕ) : ℤ)) + 1 := by
                      push_cast; ring
                    rw [hstep]
                    exact (hexPt_adj_y _ _).symm
                · by_cases h3 : t = 2 * a + 1
                  · subst h3
                    simp only [raw2, ha0, show 2 * a + 1 ≠ 0 by omega, show 2 * a + 1 ≠ 1 by omega,
                      show 2 * a + 1 ≠ L - 1 by omega, show 2 * a + 1 ≠ L by omega,
                      show 2 * a + 1 + 1 ≠ 0 by omega, show 2 * a + 1 + 1 ≠ 1 by omega,
                      show 2 * a + 1 + 1 ≠ L - 1 by omega, show 2 * a + 1 + 1 ≠ L by omega,
                      le_refl, show ¬ (2 * a + 1 + 1 ≤ 2 * a + 1) by omega,
                      show 2 * a + 1 + 1 ≤ L - 4 by omega,
                      show (2 * a + 1) % 2 ≠ 0 by omega, show (2 * a + 1 + 1) % 2 = 0 by omega,
                      show (2 * a + 1) / 2 = a by omega, show (2 * a + 1 + 1) / 2 = a + 1 by omega,
                      ↓reduceIte]
                    have hyeq : (((a + 1 : ℕ) : ℤ) - (2 * a - 1 : ℤ)) = 2 - (a : ℤ) := by
                      push_cast; ring
                    rw [hyeq]
                    simpa using (hexPt_adj_x (p := p) (-2) (2 - (a : ℤ))).symm
                  · by_cases h4 : t < L - 4
                    · simp only [raw2, ha0, h0, h1, hlast, show t ≠ L by omega,
                        show t + 1 ≠ 0 by omega, show t + 1 ≠ 1 by omega,
                        show t + 1 ≠ L - 1 by omega, show t + 1 ≠ L by omega,
                        show ¬ (t ≤ 2 * a + 1) by omega, show ¬ (t + 1 ≤ 2 * a + 1) by omega,
                        show t ≤ L - 4 by omega, show t + 1 ≤ L - 4 by omega, ↓reduceIte]
                      by_cases he : t % 2 = 0
                      · have ho : (t + 1) % 2 ≠ 0 := by omega
                        have hd : (t + 1) / 2 = t / 2 := by omega
                        simp only [he, ho, hd, ↓reduceIte]
                        have hstep : (((t / 2 + 1 : ℕ) : ℤ) - (2 * a - 1 : ℤ)) =
                            (((t / 2 : ℕ) : ℤ) - (2 * a - 1 : ℤ)) + 1 := by push_cast; ring
                        rw [hstep]
                        exact hexPt_adj_y _ _
                      · have he2 : (t + 1) % 2 = 0 := by omega
                        have hd : (t + 1) / 2 = t / 2 + 1 := by omega
                        simp only [he, he2, hd, ↓reduceIte]
                        exact (hexPt_adj_0 _ _).symm
                    · by_cases h5 : t = L - 4
                      · subst h5
                        rw [show L - 4 + 1 = L - 3 by omega]
                        have he : (L - 4) % 2 = 0 := by omega
                        have hyeq : (((L - 4) / 2 : ℕ) : ℤ) - (2 * a - 1 : ℤ) = (m : ℤ) := by omega
                        simp only [raw2, ha0, show L - 4 ≠ 0 by omega, show L - 4 ≠ 1 by omega,
                          show L - 4 ≠ L - 1 by omega, show L - 4 ≠ L by omega,
                          show L - 3 ≠ 0 by omega, show L - 3 ≠ 1 by omega,
                          show L - 3 ≠ L - 1 by omega, show L - 3 ≠ L by omega,
                          show ¬ (L - 4 ≤ 2 * a + 1) by omega, le_refl,
                          show ¬ (L - 3 ≤ 2 * a + 1) by omega,
                          show ¬ (L - 3 ≤ L - 4) by omega,
                          he, hyeq, ↓reduceIte]
                        simpa using hexPt_adj_x (p := p) (-2) (m : ℤ)
                      · by_cases h6 : t = L - 3
                        · subst h6
                          rw [show L - 3 + 1 = L - 2 by omega]
                          simp only [raw2, ha0, show L - 3 ≠ 0 by omega, show L - 3 ≠ 1 by omega,
                            show L - 3 ≠ L - 1 by omega, show L - 3 ≠ L by omega,
                            show L - 2 ≠ 0 by omega, show L - 2 ≠ 1 by omega,
                            show L - 2 ≠ L - 1 by omega, show L - 2 ≠ L by omega,
                            show ¬ (L - 3 ≤ 2 * a + 1) by omega, show ¬ (L - 3 ≤ L - 4) by omega,
                            show ¬ (L - 2 ≤ 2 * a + 1) by omega, show ¬ (L - 2 ≤ L - 4) by omega,
                            show L - 2 ≠ L - 3 by omega, ↓reduceIte]
                          exact (hexPt_adj_0 (p := p) (-1) (m : ℤ)).symm
                        · have h7 : t = L - 2 := by omega
                          subst h7
                          rw [show L - 2 + 1 = L - 1 by omega]
                          simp only [raw2, ha0, show L - 2 ≠ 0 by omega, show L - 2 ≠ 1 by omega,
                            show L - 2 ≠ L - 1 by omega, show L - 2 ≠ L by omega,
                            show L - 1 ≠ 0 by omega, show L - 1 ≠ 1 by omega,
                            show ¬ (L - 2 ≤ 2 * a + 1) by omega, show ¬ (L - 2 ≤ L - 4) by omega,
                            show L - 2 ≠ L - 3 by omega, ↓reduceIte]
                          simpa using hexPt_adj_x (p := p) (-1) (m : ℤ)
    -- Coordinate bounds for interior vertices in Case B (`m ≥ 2`)
    -- Notice: x ∈ {-2, -1, 0, 1, 2} (all 5 distinct mod p since p ≥ 5!).
    -- And inside each column x, all y-coordinates span strictly less than p!
    have h0_info (t : ℕ) (ht0 : 0 < t) (htL : t < L) :
        (raw0 t).2.1 = 0 ∧ (raw0 t).1 = decide (t % 2 = 1) ∧
        (raw0 t).2.2 = -((t / 2 : ℕ) : ℤ) ∧ -(L / 2 - 1 : ℤ) ≤ (raw0 t).2.2 ∧ (raw0 t).2.2 ≤ 0 := by
      dsimp only [raw0]
      by_cases he : t % 2 = 0
      · simp [he, show t % 2 ≠ 1 by omega]; omega
      · simp [he, show t % 2 = 1 by omega]; omega
    have h1_info (t : ℕ) (ht0 : 0 < t) (htL : t < L) :
        ((raw1 t).2.1 = 1 ∨ (raw1 t).2.1 = 2) ∧
        -(a : ℤ) ≤ (raw1 t).2.2 ∧ (raw1 t).2.2 ≤ (m : ℤ) := by
      simp only [raw1, show t ≠ 0 by omega, show t ≠ L by omega, ↓reduceIte]
      by_cases ha0 : a = 0
      · simp only [ha0, ↓reduceIte]; split_ifs <;> (dsimp only; omega)
      · simp only [ha0, ↓reduceIte]
        by_cases h1 : t ≤ 2 * a
        · simp only [h1, ↓reduceIte]; split_ifs <;> (dsimp only; omega)
        · by_cases h2 : t ≤ L - 3
          · simp only [h1, h2, ↓reduceIte]; split_ifs <;> (dsimp only; omega)
          · by_cases h3 : t = L - 2
            · simp only [h1, h2, ↓reduceIte]; simp only [h3, ↓reduceIte]
              exact ⟨Or.inl trivial, by omega, by omega⟩
            · simp only [h1, h2, ↓reduceIte]; simp only [h3, ↓reduceIte]
              exact ⟨Or.inl trivial, by omega, by omega⟩
    have h2_info (t : ℕ) (ht0 : 0 < t) (htL : t < L) :
        (t = 1 ∧ raw2 t = (true, 0, 1)) ∨
        (t = L - 1 ∧ raw2 t = (true, 0, (m : ℤ))) ∨
        (2 ≤ t ∧ t ≤ L - 2 ∧ ((raw2 t).2.1 = -1 ∨ (raw2 t).2.1 = -2) ∧
          1 - (a : ℤ) ≤ (raw2 t).2.2 ∧ (raw2 t).2.2 ≤ (m : ℤ)) := by
      by_cases h1 : t = 1
      · left; exact ⟨h1, by simp [raw2, h1]⟩
      · by_cases h2 : t = L - 1
        · right; left; exact ⟨h2, by simp [raw2, h2, show L - 1 ≠ 0 by omega, show L - 1 ≠ 1 by omega]⟩
        · right; right
          refine ⟨by omega, by omega, ?_⟩
          simp only [raw2, show t ≠ 0 by omega, h1, h2, show t ≠ L by omega, ↓reduceIte]
          by_cases ha0 : a = 0
          · simp only [ha0, ↓reduceIte]; split_ifs <;> (dsimp only; omega)
          · simp only [ha0, ↓reduceIte]
            by_cases h3 : t ≤ 2 * a + 1
            · simp only [h3, ↓reduceIte]; split_ifs <;> (dsimp only; omega)
            · by_cases h4 : t ≤ L - 4
              · simp only [h3, h4, ↓reduceIte]; split_ifs <;> (dsimp only; omega)
              · by_cases h5 : t = L - 3
                · simp only [h3, h4, ↓reduceIte]; simp only [h5, ↓reduceIte]
                  exact ⟨Or.inl trivial, by omega, by omega⟩
                · simp only [h3, h4, ↓reduceIte]; simp only [h5, ↓reduceIte]
                  exact ⟨Or.inl trivial, by omega, by omega⟩
    have hPavoid : ∀ c t, 0 < t → t < L → P c t ≠ (false, 1) ∧ P c t ≠ (false, target) := by
      intro c t ht0 htL
      have h0pt : (false, (1 : Multiplicative (ZMod p × ZMod p))) = hexPt p false 0 0 := by
        simp [hexPt]; rfl
      have htpt : (false, target) = hexPt p false 0 (m : ℤ) := by simp [hexPt, target]
      rw [h0pt, htpt]
      fin_cases c
      · dsimp only [P, raw]
        obtain ⟨_, hs, hy, hylo, hyhi⟩ := h0_info t ht0 htL
        constructor
        · intro h; rw [hexPt_eq_iff] at h
          have hs' : t % 2 ≠ 1 := by simpa [hs] using h.1
          have hy0 := zmod_eq_of_sub_bounds (by omega) (by omega) h.2.2
          omega
        · intro h; rw [hexPt_eq_iff] at h
          exact zmod_ne_of_sub_bounds (by omega) (by omega) (by omega) (h.2.2.trans hmod_m.symm)
      · dsimp only [P, raw]
        obtain ⟨hx, _, _⟩ := h1_info t ht0 htL
        constructor <;> (intro h; rw [hexPt_eq_iff] at h; exact zmod_ne_of_sub_bounds (by omega) (by omega) (by omega) h.2.1)
      · dsimp only [P, raw]
        rcases h2_info t ht0 htL with ⟨_, hr⟩ | ⟨_, hr⟩ | ⟨_, _, hx, _, _⟩
        · rw [hr]; constructor <;> (intro h; rw [hexPt_eq_iff] at h; exact Bool.noConfusion h.1)
        · rw [hr]; constructor <;> (intro h; rw [hexPt_eq_iff] at h; exact Bool.noConfusion h.1)
        · constructor <;> (intro h; rw [hexPt_eq_iff] at h; exact zmod_ne_of_sub_bounds (by omega) (by omega) (by omega) h.2.1)
    -- Helper: `raw1` is injective on `0 < t < L`
    have h1_inj (t₁ t₂ : ℕ) (ht₁0 : 0 < t₁) (ht₁L : t₁ < L) (ht₂0 : 0 < t₂) (ht₂L : t₂ < L)
        (hs : (raw1 t₁).1 = (raw1 t₂).1) (hx : ((raw1 t₁).2.1 : ZMod p) = ((raw1 t₂).2.1 : ZMod p))
        (hy : ((raw1 t₁).2.2 : ZMod p) = ((raw1 t₂).2.2 : ZMod p)) : t₁ = t₂ := by
      obtain ⟨hx1, hy1lo, hy1hi⟩ := h1_info t₁ ht₁0 ht₁L
      obtain ⟨hx2, hy2lo, hy2hi⟩ := h1_info t₂ ht₂0 ht₂L
      have hxeq := zmod_eq_of_sub_bounds (by omega) (by omega) hx
      have hyeq := zmod_eq_of_sub_bounds (by omega) (by omega) hy
      simp only [raw1, show t₁ ≠ 0 by omega, show t₁ ≠ L by omega,
        show t₂ ≠ 0 by omega, show t₂ ≠ L by omega, ↓reduceIte] at hs hxeq hyeq
      by_cases ha0 : a = 0
      · simp only [ha0, ↓reduceIte] at hs hyeq
        by_cases ho1 : t₁ % 2 = 1 <;> by_cases ho2 : t₂ % 2 = 1 <;>
          simp only [ho1, ho2, ↓reduceIte] at hs hyeq <;>
          ((try dsimp only at hs hyeq); first | exact Bool.noConfusion hs | omega)
      · simp only [ha0, ↓reduceIte] at hs hxeq hyeq
        by_cases h1a : t₁ ≤ 2 * a <;> by_cases h2a : t₂ ≤ 2 * a
        · simp only [h1a, h2a, ↓reduceIte] at hs hyeq
          by_cases ho1 : t₁ % 2 = 1 <;> by_cases ho2 : t₂ % 2 = 1 <;>
            simp only [ho1, ho2, ↓reduceIte] at hs hyeq <;>
            ((try dsimp only at hs hyeq); first | exact Bool.noConfusion hs | omega)
        · simp only [h1a, h2a, ↓reduceIte] at hs hxeq hyeq
          by_cases h2b : t₂ ≤ L - 3
          · simp only [h2b, ↓reduceIte] at hxeq; split_ifs at hxeq <;> (dsimp only at hxeq; omega)
          · by_cases h2c : t₂ = L - 2
            · simp only [h2b, h2c, ↓reduceIte] at hs hyeq; split_ifs at hs hyeq <;>
                ((try dsimp only at hs hyeq); first | exact Bool.noConfusion hs | omega)
            · simp only [h2b, h2c, ↓reduceIte] at hs hyeq; split_ifs at hs hyeq <;>
                ((try dsimp only at hs hyeq); first | exact Bool.noConfusion hs | omega)
        · simp only [h1a, h2a, ↓reduceIte] at hs hxeq hyeq
          by_cases h1b : t₁ ≤ L - 3
          · simp only [h1b, ↓reduceIte] at hxeq; split_ifs at hxeq <;> (dsimp only at hxeq; omega)
          · by_cases h1c : t₁ = L - 2
            · simp only [h1b, h1c, ↓reduceIte] at hs hyeq; split_ifs at hs hyeq <;>
                ((try dsimp only at hs hyeq); first | exact Bool.noConfusion hs | omega)
            · simp only [h1b, h1c, ↓reduceIte] at hs hyeq; split_ifs at hs hyeq <;>
                ((try dsimp only at hs hyeq); first | exact Bool.noConfusion hs | omega)
        · simp only [h1a, h2a, ↓reduceIte] at hs hxeq hyeq
          by_cases h1b : t₁ ≤ L - 3 <;> by_cases h2b : t₂ ≤ L - 3
          · simp only [h1b, h2b, ↓reduceIte] at hs hyeq
            by_cases ho1 : t₁ % 2 = 1 <;> by_cases ho2 : t₂ % 2 = 1 <;>
              simp only [ho1, ho2, ↓reduceIte] at hs hyeq <;>
              ((try dsimp only at hs hyeq); first | exact Bool.noConfusion hs | omega)
          · simp only [h1b, h2b, ↓reduceIte] at hxeq; split_ifs at hxeq <;> (dsimp only at hxeq; omega)
          · simp only [h1b, h2b, ↓reduceIte] at hxeq; split_ifs at hxeq <;> (dsimp only at hxeq; omega)
          · simp only [h1b, h2b, ↓reduceIte] at hs hyeq
            by_cases h1c : t₁ = L - 2 <;> by_cases h2c : t₂ = L - 2 <;>
              simp only [h1c, h2c, ↓reduceIte] at hs <;>
              ((try dsimp only at hs); first | exact Bool.noConfusion hs | omega)
    -- Helper: `raw2` is injective on `0 < t < L`
    have h2_inj (t₁ t₂ : ℕ) (ht₁0 : 0 < t₁) (ht₁L : t₁ < L) (ht₂0 : 0 < t₂) (ht₂L : t₂ < L)
        (hs : (raw2 t₁).1 = (raw2 t₂).1) (hx : ((raw2 t₁).2.1 : ZMod p) = ((raw2 t₂).2.1 : ZMod p))
        (hy : ((raw2 t₁).2.2 : ZMod p) = ((raw2 t₂).2.2 : ZMod p)) : t₁ = t₂ := by
      rcases h2_info t₁ ht₁0 ht₁L with ⟨ht1, hr1⟩ | ⟨ht1, hr1⟩ | ⟨h1lo, h1hi, hx1, hy1lo, hy1hi⟩ <;>
      rcases h2_info t₂ ht₂0 ht₂L with ⟨ht2, hr2⟩ | ⟨ht2, hr2⟩ | ⟨h2lo, h2hi, hx2, hy2lo, hy2hi⟩
      · omega
      · rw [hr1, hr2] at hy; dsimp only at hy; exact (zmod_ne_of_sub_bounds (by omega) (by omega) (by omega) hy).elim
      · rw [hr1] at hx; dsimp only at hx; exact (zmod_ne_of_sub_bounds (by omega) (by omega) (by omega) hx).elim
      · rw [hr1, hr2] at hy; dsimp only at hy; exact (zmod_ne_of_sub_bounds (by omega) (by omega) (by omega) hy).elim
      · omega
      · rw [hr1] at hx; dsimp only at hx; exact (zmod_ne_of_sub_bounds (by omega) (by omega) (by omega) hx).elim
      · rw [hr2] at hx; dsimp only at hx; exact (zmod_ne_of_sub_bounds (by omega) (by omega) (by omega) hx).elim
      · rw [hr2] at hx; dsimp only at hx; exact (zmod_ne_of_sub_bounds (by omega) (by omega) (by omega) hx).elim
      · have hxeq := zmod_eq_of_sub_bounds (by omega) (by omega) hx
        have hyeq := zmod_eq_of_sub_bounds (by omega) (by omega) hy
        simp only [raw2, show t₁ ≠ 0 by omega, show t₁ ≠ 1 by omega, show t₁ ≠ L - 1 by omega,
          show t₁ ≠ L by omega, show t₂ ≠ 0 by omega, show t₂ ≠ 1 by omega, show t₂ ≠ L - 1 by omega,
          show t₂ ≠ L by omega, ↓reduceIte] at hs hxeq hyeq
        by_cases ha0 : a = 0
        · simp only [ha0, ↓reduceIte] at hs hyeq
          by_cases he1 : t₁ % 2 = 0 <;> by_cases he2 : t₂ % 2 = 0 <;>
            simp only [he1, he2, ↓reduceIte] at hs hyeq <;>
            ((try dsimp only at hs hyeq); first | exact Bool.noConfusion hs | omega)
        · simp only [ha0, ↓reduceIte] at hs hxeq hyeq
          by_cases h1a : t₁ ≤ 2 * a + 1 <;> by_cases h2a : t₂ ≤ 2 * a + 1
          · simp only [h1a, h2a, ↓reduceIte] at hs hyeq
            by_cases he1 : t₁ % 2 = 0 <;> by_cases he2 : t₂ % 2 = 0 <;>
              simp only [he1, he2, ↓reduceIte] at hs hyeq <;>
              ((try dsimp only at hs hyeq); first | exact Bool.noConfusion hs | omega)
          · simp only [h1a, h2a, ↓reduceIte] at hs hxeq hyeq
            by_cases h2b : t₂ ≤ L - 4
            · simp only [h2b, ↓reduceIte] at hxeq; split_ifs at hxeq <;> (dsimp only at hxeq; omega)
            · by_cases h2c : t₂ = L - 3
              · simp only [h2b, h2c, ↓reduceIte] at hs hyeq; split_ifs at hs hyeq <;>
                  ((try dsimp only at hs hyeq); first | exact Bool.noConfusion hs | omega)
              · simp only [h2b, h2c, ↓reduceIte] at hs hyeq; split_ifs at hs hyeq <;>
                  ((try dsimp only at hs hyeq); first | exact Bool.noConfusion hs | omega)
          · simp only [h1a, h2a, ↓reduceIte] at hs hxeq hyeq
            by_cases h1b : t₁ ≤ L - 4
            · simp only [h1b, ↓reduceIte] at hxeq; split_ifs at hxeq <;> (dsimp only at hxeq; omega)
            · by_cases h1c : t₁ = L - 3
              · simp only [h1b, h1c, ↓reduceIte] at hs hyeq; split_ifs at hs hyeq <;>
                  ((try dsimp only at hs hyeq); first | exact Bool.noConfusion hs | omega)
              · simp only [h1b, h1c, ↓reduceIte] at hs hyeq; split_ifs at hs hyeq <;>
                  ((try dsimp only at hs hyeq); first | exact Bool.noConfusion hs | omega)
          · simp only [h1a, h2a, ↓reduceIte] at hs hxeq hyeq
            by_cases h1b : t₁ ≤ L - 4 <;> by_cases h2b : t₂ ≤ L - 4
            · simp only [h1b, h2b, ↓reduceIte] at hs hyeq
              by_cases he1 : t₁ % 2 = 0 <;> by_cases he2 : t₂ % 2 = 0 <;>
                simp only [he1, he2, ↓reduceIte] at hs hyeq <;>
                ((try dsimp only at hs hyeq); first | exact Bool.noConfusion hs | omega)
            · simp only [h1b, h2b, ↓reduceIte] at hxeq; split_ifs at hxeq <;> (dsimp only at hxeq; omega)
            · simp only [h1b, h2b, ↓reduceIte] at hxeq; split_ifs at hxeq <;> (dsimp only at hxeq; omega)
            · simp only [h1b, h2b, ↓reduceIte] at hs hyeq
              by_cases h1c : t₁ = L - 3 <;> by_cases h2c : t₂ = L - 3 <;>
                simp only [h1c, h2c, ↓reduceIte] at hs <;>
                ((try dsimp only at hs); first | exact Bool.noConfusion hs | omega)
    have hPinj : ∀ c₁ t₁ c₂ t₂, 0 < t₁ → t₁ < L → 0 < t₂ → t₂ < L →
        P c₁ t₁ = P c₂ t₂ → c₁ = c₂ ∧ t₁ = t₂ := by
      intro c₁ t₁ c₂ t₂ ht₁0 ht₁L ht₂0 ht₂L heq
      rw [hexPt_eq_iff] at heq
      obtain ⟨hs, hx, hy⟩ := heq
      fin_cases c₁ <;> fin_cases c₂
      · -- (0, 0)
        refine ⟨rfl, ?_⟩
        dsimp only [raw] at hs hx hy
        obtain ⟨_, hs1, hy1, hy1lo, hy1hi⟩ := h0_info t₁ ht₁0 ht₁L
        obtain ⟨_, hs2, hy2, hy2lo, hy2hi⟩ := h0_info t₂ ht₂0 ht₂L
        have hyeq := zmod_eq_of_sub_bounds (by omega) (by omega) hy
        have hseq : decide (t₁ % 2 = 1) = decide (t₂ % 2 = 1) := by rwa [hs1, hs2] at hs
        have hmod : t₁ % 2 = t₂ % 2 := by
          by_cases h1 : t₁ % 2 = 1 <;> by_cases h2 : t₂ % 2 = 1 <;> simp [h1, h2] at hseq <;> omega
        omega
      · -- (0, 1)
        dsimp only [raw] at hs hx hy
        obtain ⟨hx1, _, _, _, _⟩ := h0_info t₁ ht₁0 ht₁L
        obtain ⟨hx2, _, _⟩ := h1_info t₂ ht₂0 ht₂L
        exact (zmod_ne_of_sub_bounds (by omega) (by omega) (by omega) hx).elim
      · -- (0, 2)
        dsimp only [raw] at hs hx hy
        obtain ⟨hx1, _, _, hy1lo, hy1hi⟩ := h0_info t₁ ht₁0 ht₁L
        rcases h2_info t₂ ht₂0 ht₂L with ⟨_, hr2⟩ | ⟨_, hr2⟩ | ⟨_, _, hx2, _, _⟩
        · rw [hr2] at hy; dsimp only at hy; exact (zmod_ne_of_sub_bounds (by omega) (by omega) (by omega) hy).elim
        · rw [hr2] at hy; dsimp only at hy
          exact (zmod_ne_of_sub_bounds (by omega) (by omega) (by omega) (hy.trans hmod_m.symm)).elim
        · exact (zmod_ne_of_sub_bounds (by omega) (by omega) (by omega) hx).elim
      · -- (1, 0)
        dsimp only [raw] at hs hx hy
        obtain ⟨hx1, _, _⟩ := h1_info t₁ ht₁0 ht₁L
        obtain ⟨hx2, _, _, _, _⟩ := h0_info t₂ ht₂0 ht₂L
        exact (zmod_ne_of_sub_bounds (by omega) (by omega) (by omega) hx).elim
      · -- (1, 1)
        exact ⟨rfl, h1_inj t₁ t₂ ht₁0 ht₁L ht₂0 ht₂L hs hx hy⟩
      · -- (1, 2)
        dsimp only [raw] at hs hx hy
        obtain ⟨hx1, _, _⟩ := h1_info t₁ ht₁0 ht₁L
        rcases h2_info t₂ ht₂0 ht₂L with ⟨_, hr2⟩ | ⟨_, hr2⟩ | ⟨_, _, hx2, _, _⟩
        · rw [hr2] at hx; dsimp only at hx; exact (zmod_ne_of_sub_bounds (by omega) (by omega) (by omega) hx).elim
        · rw [hr2] at hx; dsimp only at hx; exact (zmod_ne_of_sub_bounds (by omega) (by omega) (by omega) hx).elim
        · exact (zmod_ne_of_sub_bounds (by omega) (by omega) (by omega) hx).elim
      · -- (2, 0)
        dsimp only [raw] at hs hx hy
        obtain ⟨hx2, _, _, hy2lo, hy2hi⟩ := h0_info t₂ ht₂0 ht₂L
        rcases h2_info t₁ ht₁0 ht₁L with ⟨_, hr1⟩ | ⟨_, hr1⟩ | ⟨_, _, hx1, _, _⟩
        · rw [hr1] at hy; dsimp only at hy; exact (zmod_ne_of_sub_bounds (by omega) (by omega) (by omega) hy).elim
        · rw [hr1] at hy; dsimp only at hy
          exact (zmod_ne_of_sub_bounds (by omega) (by omega) (by omega) (hmod_m.trans hy)).elim
        · exact (zmod_ne_of_sub_bounds (by omega) (by omega) (by omega) hx).elim
      · -- (2, 1)
        dsimp only [raw] at hs hx hy
        obtain ⟨hx2, _, _⟩ := h1_info t₂ ht₂0 ht₂L
        rcases h2_info t₁ ht₁0 ht₁L with ⟨_, hr1⟩ | ⟨_, hr1⟩ | ⟨_, _, hx1, _, _⟩
        · rw [hr1] at hx; dsimp only at hx; exact (zmod_ne_of_sub_bounds (by omega) (by omega) (by omega) hx).elim
        · rw [hr1] at hx; dsimp only at hx; exact (zmod_ne_of_sub_bounds (by omega) (by omega) (by omega) hx).elim
        · exact (zmod_ne_of_sub_bounds (by omega) (by omega) (by omega) hx).elim
      · -- (2, 2)
        exact ⟨rfl, h2_inj t₁ t₂ ht₁0 ht₁L ht₂0 ht₂L hs hx hy⟩
    exact ⟨target, P, htarget, hP0, hPL, hPadj, hPavoid, hPinj⟩

/- ## Section 3: Prime-plane quotient `A →* Multiplicative (ZMod p × ZMod p)` -/

private lemma sylow_p_projection {A : Type*} [Group A] [Finite A] [Group.IsNilpotent A]
    {p : ℕ} (hp : p.Prime) (divides : p ∣ Nat.card A) (P : Sylow p A) :
    ∃ f : A →* P, Function.Surjective f ∧ ¬ p ∣ Nat.card f.ker := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  let i : (Nat.card A).primeFactors :=
    ⟨p, Nat.mem_primeFactors.mpr ⟨hp, divides, Nat.card_pos.ne'⟩⟩
  let e := Sylow.directProductOfNormal (G := A) (fun _ => inferInstance)
  let f₁ := Pi.evalMonoidHom (fun j : (Nat.card A).primeFactors => ∀ R : Sylow j A, R) i
  let f₂ := Pi.evalMonoidHom (fun R : Sylow p A => R) P
  let f : A →* P := f₂.comp (f₁.comp e.symm.toMonoidHom)
  have fs : Function.Surjective f := by
    intro x
    refine ⟨e (Pi.mulSingle i (Pi.mulSingle P x)), ?_⟩
    simp [f, f₁, f₂, Pi.evalMonoidHom]
  refine ⟨f, fs, ?_⟩
  have index : f.ker.index = Nat.card P := by
    rw [Subgroup.index_ker, MonoidHom.range_eq_top.mpr fs, Subgroup.card_top]
  have cards : Nat.card P * Nat.card f.ker = Nat.card P * P.index := by
    rw [← index, Subgroup.index_mul_card, index, Subgroup.card_mul_index]
  have eq := Nat.eq_of_mul_eq_mul_left (Nat.card_pos (α := P)) cards
  exact eq ▸ P.not_dvd_index

private lemma maximal_card_p {A : Type*} [Group A] [Finite A] {p : ℕ} (hp : p.Prime)
    (pgrp : IsPGroup p A) (M : Subgroup A) [M.Normal] (max : IsCoatom M) :
    Nat.card (A ⧸ M) = p := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  let f := QuotientGroup.mk' M
  have proper : M ≠ ⊤ := max.1
  have nontrivial : Nontrivial (A ⧸ M) := by
    obtain ⟨x, h⟩ := SetLike.exists_not_mem_of_ne_top M proper
    exact ⟨f x, 1, fun eq => h ((QuotientGroup.eq_one_iff x).mp eq)⟩
  have pg := pgrp.to_quotient M
  have dv : p ∣ Nat.card (A ⧸ M) := (pg.card_eq_or_dvd).resolve_left
    (ne_of_gt (Finite.one_lt_card_iff_nontrivial.mpr nontrivial))
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' p dv
  let C := Subgroup.zpowers x
  let J := C.comap f
  have le : M ≤ J := by
    intro z hz
    change f z ∈ C
    have id : f z = 1 := (QuotientGroup.eq_one_iff z).mpr hz
    rw [id]; exact C.one_mem
  have top : J = ⊤ := by
    apply max.2
    apply lt_of_le_of_ne le
    intro eq
    obtain ⟨z, hz⟩ := QuotientGroup.mk_surjective x
    have mem : z ∈ J := by
      change f z ∈ C
      change f z = x at hz
      rw [hz]; exact Subgroup.mem_zpowers x
    have val := (QuotientGroup.eq_one_iff z).mpr (eq ▸ mem)
    have xeq : x = 1 := hz ▸ val
    simp [xeq] at hx
    exact hp.ne_one hx.symm
  have ctop : C = ⊤ := by
    apply Subgroup.comap_injective (f := f) QuotientGroup.mk_surjective
    simpa [J] using top
  exact (orderOf_eq_card_of_zpowers_eq_top ctop).symm.trans hx

/-- Identify a group of prime order `p` with `Multiplicative (ZMod p)` sending a chosen
nonidentity element `g` to `Multiplicative.ofAdd 1`. -/
private noncomputable def primeOrderEquivZMod {Q : Type*} [Group Q] [Finite Q]
    {p : ℕ} (hp : p.Prime) (hcard : Nat.card Q = p) (g : Q) (hg : g ≠ 1) :
    Q ≃* Multiplicative (ZMod p) := by
  classical
  have : NeZero p := ⟨hp.ne_zero⟩
  have hord : orderOf g = p := by
    have hdvd : orderOf g ∣ p := hcard ▸ orderOf_dvd_natCard g
    rcases hp.eq_one_or_self_of_dvd _ hdvd with h1 | hp'
    · exact (hg (orderOf_eq_one_iff.mp h1)).elim
    · exact hp'
  let fwd : Multiplicative (ZMod p) →* Q :=
    { toFun := fun x => g ^ x.toAdd.val
      map_one' := by simp
      map_mul' := fun x y => by
        change g ^ (x.toAdd + y.toAdd).val = g ^ x.toAdd.val * g ^ y.toAdd.val
        rw [ZMod.val_add, ← pow_add]
        have hm : ∀ k : ℕ, g ^ (k % p) = g ^ k := by
          intro k; rw [← hord, pow_mod_orderOf]
        exact hm (x.toAdd.val + y.toAdd.val) }
  have hinj : Function.Injective fwd := by
    intro x y h
    have hxy : x.toAdd.val = y.toAdd.val :=
      pow_injOn_Iio_orderOf (hord ▸ x.toAdd.val_lt) (hord ▸ y.toAdd.val_lt) h
    exact Multiplicative.toAdd.injective (ZMod.val_injective p hxy)
  let _ : Fintype Q := Fintype.ofFinite Q
  have hcard_eq : Fintype.card (Multiplicative (ZMod p)) = Fintype.card Q := by
    rw [Fintype.card_of_bijective Multiplicative.toAdd.bijective, ZMod.card p,
      ← Nat.card_eq_fintype_card, hcard]
  have hbij : Function.Bijective fwd :=
    (Fintype.bijective_iff_injective_and_card fwd).mpr ⟨hinj, hcard_eq⟩
  exact (MulEquiv.ofBijective fwd hbij).symm

private lemma primeOrderEquivZMod_apply {Q : Type*} [Group Q] [Finite Q]
    {p : ℕ} (hp : p.Prime) (hcard : Nat.card Q = p) (g : Q) (hg : g ≠ 1) :
    primeOrderEquivZMod hp hcard g hg g = Multiplicative.ofAdd (1 : ZMod p) := by
  have : NeZero p := ⟨hp.ne_zero⟩
  have : Fact (1 < p) := ⟨hp.one_lt⟩
  apply (primeOrderEquivZMod hp hcard g hg).symm.injective
  rw [MulEquiv.symm_apply_apply]
  change g = g ^ (1 : ZMod p).val
  rw [ZMod.val_one, pow_one]

/-- Every 2-generated finite nilpotent group with a prime `p` dividing `|γ₃(A)|`
surjects onto `Multiplicative (ZMod p × ZMod p)` sending `a ↦ (1, 0)` and `b ↦ (0, 1)`. -/
private lemma prime_plane_quotient {A : Type} [Group A] [Fintype A] [Group.IsNilpotent A]
    (a b : A) (gen : Subgroup.closure ({a, b} : Set A) = ⊤)
    {p : ℕ} (hp : p.Prime) (hdvd : p ∣ Nat.card ((⊤ : Subgroup A).lowerCentralSeries 2)) :
    ∃ f : A →* Multiplicative (ZMod p × ZMod p),
      Function.Surjective f ∧
      f a = Multiplicative.ofAdd ((1 : ZMod p), (0 : ZMod p)) ∧
      f b = Multiplicative.ofAdd ((0 : ZMod p), (1 : ZMod p)) ∧
      Nat.card f.ker < Nat.card A := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  let D := (⊤ : Subgroup A).lowerCentralSeries 2
  have hdvdA : p ∣ Nat.card A := hdvd.trans D.card_subgroup_dvd_card
  let P : Sylow p A := default
  obtain ⟨π, hπs, hπker⟩ := sylow_p_projection hp hdvdA P
  have hP_noncyclic : ¬ IsCyclic P := by
    intro hcyc
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' p hdvd
    have hcomm : (⊤ : Subgroup P).lowerCentralSeries 1 = ⊥ :=
      Subgroup.lowerCentralSeries_one_eq_bot_iff.mpr inferInstance
    have htriv : (⊤ : Subgroup P).lowerCentralSeries 2 ≤ ⊥ := by
      rw [← hcomm]; exact (⊤ : Subgroup P).lowerCentralSeries_antitone (by decide)
    have hmap : D.map π ≤ (⊤ : Subgroup P).lowerCentralSeries 2 := by
      change ((⊤ : Subgroup A).lowerCentralSeries 2).map π ≤ _
      rw [Subgroup.map_lowerCentralSeries]
      exact Subgroup.lowerCentralSeries_mono 2 le_top
    have hid : π (x : A) = 1 := htriv (hmap (Subgroup.mem_map_of_mem π x.property))
    have hordx : orderOf (x : A) = p := by
      have hmk : orderOf (⟨x.1, x.2⟩ : D) = orderOf (x : A) := Subgroup.orderOf_mk x.1 x.2
      exact hmk.symm.trans hx
    exact hπker (hordx ▸ π.ker.orderOf_dvd_natCard (show (x : A) ∈ π.ker from hid))
  have hgenP : Subgroup.closure ({π a, π b} : Set P) = ⊤ := by
    rw [← Set.image_pair, ← MonoidHom.map_closure, gen, ← MonoidHom.range_eq_map,
      MonoidHom.range_eq_top.mpr hπs]
  have hza : Subgroup.zpowers (π a) ≠ ⊤ := fun h => hP_noncyclic ⟨π a, fun y =>
    Subgroup.mem_zpowers_iff.mp (h ▸ Subgroup.mem_top y)⟩
  have hzb : Subgroup.zpowers (π b) ≠ ⊤ := fun h => hP_noncyclic ⟨π b, fun y =>
    Subgroup.mem_zpowers_iff.mp (h ▸ Subgroup.mem_top y)⟩
  obtain ⟨M₁, hM₁, haM₁⟩ := (eq_top_or_exists_le_coatom _).resolve_left hza
  obtain ⟨M₂, hM₂, hbM₂⟩ := (eq_top_or_exists_le_coatom _).resolve_left hzb
  have : M₁.Normal :=
    ((Group.isNilpotent_of_finite_tfae (G := P)).out 0 2 rfl rfl).mp P.isPGroup'.isNilpotent M₁ hM₁
  have : M₂.Normal :=
    ((Group.isNilpotent_of_finite_tfae (G := P)).out 0 2 rfl rfl).mp P.isPGroup'.isNilpotent M₂ hM₂
  have hcard1 : Nat.card (P ⧸ M₁) = p := maximal_card_p hp P.isPGroup' M₁ hM₁
  have hcard2 : Nat.card (P ⧸ M₂) = p := maximal_card_p hp P.isPGroup' M₂ hM₂
  have ha_mem : π a ∈ M₁ := haM₁ (Subgroup.mem_zpowers _)
  have hb_mem : π b ∈ M₂ := hbM₂ (Subgroup.mem_zpowers _)
  have hb_nmem : π b ∉ M₁ := by
    intro hb1
    apply hM₁.1
    apply top_unique
    rw [← hgenP, Subgroup.closure_le]
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl <;> assumption
  have ha_nmem : π a ∉ M₂ := by
    intro ha2
    apply hM₂.1
    apply top_unique
    rw [← hgenP, Subgroup.closure_le]
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl <;> assumption
  let q₁ := QuotientGroup.mk' M₁
  let q₂ := QuotientGroup.mk' M₂
  have hqa2 : q₂ (π a) ≠ 1 := fun h => ha_nmem ((QuotientGroup.eq_one_iff _).mp h)
  have hqb1 : q₁ (π b) ≠ 1 := fun h => hb_nmem ((QuotientGroup.eq_one_iff _).mp h)
  let e₂ := primeOrderEquivZMod hp hcard2 (q₂ (π a)) hqa2
  let e₁ := primeOrderEquivZMod hp hcard1 (q₁ (π b)) hqb1
  let f₁ : A →* Multiplicative (ZMod p) := e₂.toMonoidHom.comp (q₂.comp π)
  let f₂ : A →* Multiplicative (ZMod p) := e₁.toMonoidHom.comp (q₁.comp π)
  let prodEquiv : Multiplicative (ZMod p) × Multiplicative (ZMod p) →* Multiplicative (ZMod p × ZMod p) :=
    { toFun := fun z => Multiplicative.ofAdd (z.1.toAdd, z.2.toAdd)
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  let f : A →* Multiplicative (ZMod p × ZMod p) := prodEquiv.comp (f₁.prod f₂)
  have hfa : f a = Multiplicative.ofAdd ((1 : ZMod p), (0 : ZMod p)) := by
    have h1 : f₁ a = Multiplicative.ofAdd (1 : ZMod p) :=
      primeOrderEquivZMod_apply hp hcard2 (q₂ (π a)) hqa2
    have h2 : f₂ a = 1 := by
      change e₁ (QuotientGroup.mk (π a)) = 1
      rw [(QuotientGroup.eq_one_iff (π a)).mpr ha_mem, map_one]
    simp [f, prodEquiv, h1, h2]
  have hfb : f b = Multiplicative.ofAdd ((0 : ZMod p), (1 : ZMod p)) := by
    have h1 : f₁ b = 1 := by
      change e₂ (QuotientGroup.mk (π b)) = 1
      rw [(QuotientGroup.eq_one_iff (π b)).mpr hb_mem, map_one]
    have h2 : f₂ b = Multiplicative.ofAdd (1 : ZMod p) :=
      primeOrderEquivZMod_apply hp hcard1 (q₁ (π b)) hqb1
    simp [f, prodEquiv, h1, h2]
  have hf_surj : Function.Surjective f := by
    intro z
    rcases hxy : z.toAdd with ⟨x, y⟩
    refine ⟨a ^ x.val * b ^ y.val, ?_⟩
    rw [map_mul, map_pow, map_pow, hfa, hfb]
    apply Multiplicative.toAdd.injective
    simp only [toAdd_mul, toAdd_pow, toAdd_ofAdd, Prod.smul_mk, nsmul_eq_mul,
      mul_one, mul_zero, Prod.mk_add_mk, add_zero, zero_add, ZMod.natCast_zmod_val, hxy]
  have hker_lt : Nat.card f.ker < Nat.card A := by
    have hidx : f.ker.index = Nat.card (Multiplicative (ZMod p × ZMod p)) := by
      rw [Subgroup.index_ker, MonoidHom.range_eq_top.mpr hf_surj, Subgroup.card_top]
    have hcardQ : Nat.card (Multiplicative (ZMod p × ZMod p)) = p * p := by
      rw [Nat.card_eq_fintype_card, Fintype.card_of_bijective Multiplicative.toAdd.bijective,
        Fintype.card_prod, ZMod.card p]
    have hgt1 : 1 < f.ker.index := by
      rw [hidx, hcardQ]
      have := hp.two_le
      nlinarith
    have hpos : 0 < Nat.card f.ker := Nat.card_pos
    rw [← f.ker.card_mul_index]
    nlinarith
  exact ⟨f, hf_surj, hfa, hfb, hker_lt⟩

/- ## Section 4: Strong induction for all odd-order nilpotent groups -/

private lemma large_prime_of_not_three {A : Type*} [Group A] [Finite A]
    (odd : Odd (Nat.card A)) (notThree : ¬ IsPGroup 3 A) :
    ∃ p : ℕ, p.Prime ∧ 5 ≤ p ∧ p ∣ Nat.card A := by
  by_contra missing
  apply notThree
  apply (isPGroup_iff_primeFactors_card_subset (by decide : 3 ≠ 0)).mpr
  intro p hp
  have prime := Nat.prime_of_mem_primeFactors hp
  have divides := Nat.dvd_of_mem_primeFactors hp
  have low := prime.two_le
  have upper : p < 5 := by by_contra! h; exact missing ⟨p, prime, h, divides⟩
  have notTwo : p ≠ 2 := by
    rintro rfl
    exact Nat.not_even_iff_odd.mpr odd (even_iff_two_dvd.mpr divides)
  have notFour : p ≠ 4 := by rintro rfl; norm_num at prime
  have eq : p = 3 := by omega
  simpa using eq

private theorem nilpotent_odd_right (n : ℕ) :
    ∀ (A : Type) [Group A] [Fintype A] [Group.IsNilpotent A] (a b : A),
      Nat.card A = n → Odd (Nat.card A) → a ≠ 1 → b ≠ 1 → a ≠ b →
      ∃ k : ℕ, 2 ≤ k ∧ cycleGraph (2 ^ k) ⊑ rightGraph a b := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro A _ _ _ a b hsize hodd ha hb hab
    classical
    by_cases hgen : Subgroup.closure ({a, b} : Set A) ≠ ⊤
    · let H := Subgroup.closure ({a, b} : Set A)
      have hsmall : Nat.card H < n := by
        rw [← hsize]
        exact lt_of_le_of_ne H.card_le_card_group (fun e => hgen (H.card_eq_iff_eq_top.mp e))
      let a' : H := ⟨a, Subgroup.subset_closure (by simp)⟩
      let b' : H := ⟨b, Subgroup.subset_closure (by simp)⟩
      obtain ⟨k, hk, cyc⟩ := ih _ hsmall H a' b' rfl (hodd.of_dvd_nat H.card_subgroup_dvd_card)
        (fun h => ha (congrArg Subtype.val h)) (fun h => hb (congrArg Subtype.val h))
        (fun h => hab (congrArg Subtype.val h))
      let emb : (Bool × H) ↪ (Bool × A) :=
        (Function.Embedding.refl Bool).prodMap ⟨Subtype.val, Subtype.coe_injective⟩
      have hle : rightGraph a' b' ⊑ rightGraph a b := by
        refine ⟨⟨⟨emb, ?_⟩, emb.injective⟩⟩
        intro u v huv
        have hdir : ∀ u v : Bool × H,
            u.1 = false ∧ v.1 = true ∧ (v.2 = u.2 ∨ v.2 = u.2 * a' ∨ v.2 = u.2 * b') →
            (emb u).1 = false ∧ (emb v).1 = true ∧
              ((emb v).2 = (emb u).2 ∨ (emb v).2 = (emb u).2 * a ∨ (emb v).2 = (emb u).2 * b) := by
          intro u v ⟨h1, h2, h3⟩
          refine ⟨h1, h2, ?_⟩
          rcases h3 with h3 | h3 | h3
          · exact .inl (congrArg Subtype.val h3)
          · exact .inr (.inl (congrArg Subtype.val h3))
          · exact .inr (.inr (congrArg Subtype.val h3))
        refine ⟨fun eq => huv.ne (emb.injective eq), ?_⟩
        rcases huv.2 with h | h
        · exact .inl (hdir u v h)
        · exact .inr (hdir v u h)
      exact ⟨k, hk, cyc.trans hle⟩
    · push Not at hgen
      let D := (⊤ : Subgroup A).lowerCentralSeries 2
      by_cases h3 : IsPGroup 3 D
      · let P : Sylow 3 A := default
        obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp P.isPGroup'
        have hedge (x y : A) (h : y = x ∨ y = a * x ∨ y = b * x) :
            (leftGraph a b).Adj (false, x) (true, y) := ⟨by simp, .inl ⟨rfl, rfl, h⟩⟩
        obtain ⟨k, hk, _, cyc⟩ := nilpotent_third_term hodd h3 P m hm a b ⟨ha, hb, hab⟩
          (leftGraph a b) (fun x => hedge x x (.inl rfl))
          (fun x => hedge x _ (.inr (.inl rfl))) (fun x => hedge x _ (.inr (.inr rfl)))
        exact ⟨k, hk, cyc.trans (rightGraph_iso_leftGraph a b).some.symm.isContained⟩
      · obtain ⟨p, hp, hp5, hdvd⟩ :=
          large_prime_of_not_three (hodd.of_dvd_nat D.card_subgroup_dvd_card) h3
        have hp_odd : Odd p := hp.odd_of_ne_two (by omega)
        have : NeZero p := ⟨hp.ne_zero⟩
        obtain ⟨f, _, hfa, hfb, hker_lt⟩ := prime_plane_quotient a b hgen hp hdvd
        obtain ⟨r, hr, hlo, hhi⟩ := exists_pow_two_between hp5 hp_odd
        obtain ⟨target, P, htarget, hP0, hPL, hPadj, hPavoid, hPinj⟩ :=
          hex_theta_exists hp5 hp_odd hr hlo hhi
        have hPadj' : ∀ c t, t < 2 ^ r → (rightGraph (f a) (f b)).Adj (P c t) (P c (t + 1)) := by
          rw [hfa, hfb]; exact hPadj
        exact theta_compress f a b r (by omega) target htarget P hP0 hPL hPadj' hPavoid hPinj
          (fun d₁ d₂ hd₁ hd₂ hd₁₂ =>
            ih _ (hsize ▸ hker_lt) f.ker d₁ d₂ rfl
              (hodd.of_dvd_nat f.ker.card_subgroup_dvd_card) hd₁ hd₂ hd₁₂)

end Erdos64NilpotentOddProof

theorem OMA.solution :
    OMA.R_Erdos64_erdos_64_R1_H1_R1_H1_R1_H2_R2_H1_R1_H2_R1_H2_R2_H1_R1.H1 := by
  intro A _ _ a b _ ha hb hab hodd _ _ _ _ hnil _
  let _ : Group.IsNilpotent A := hnil
  obtain ⟨k, hk, cyc⟩ := Erdos64NilpotentOddProof.nilpotent_odd_right (Nat.card A) A a b
    rfl hodd ha hb hab
  exact ⟨k, hk, cyc.trans (Erdos64NilpotentOddProof.rightGraph_iso_leftGraph a b).some.isContained⟩
