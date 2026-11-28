import OMAStatements.S_oeis_a250881
import Mathlib

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace OMA.S_oeis_a250881

section fastvec
/-! Fast transfer-vector kit.  States are `Fin N`; the (sparse) transition relation is given by an explicit
adjacency list `adj : List (List ℕ)`; vectors are `List ℕ`; one step is a fold over the lists.  Only Nat.add
on literals is evaluated by the kernel. -/

def Chain {S : Type} (R : S → S → Prop) (n : ℕ) :=
  {y : Fin (n + 1) → S // ∀ i : Fin n, R (y i.castSucc) (y i.succ)}

def chainEquiv {S S' : Type} {R : S → S → Prop} {R' : S' → S' → Prop} (e : S ≃ S')
    (h : ∀ a b, R a b ↔ R' (e a) (e b)) (n : ℕ) : Chain R n ≃ Chain R' n where
  toFun y := ⟨fun i => e (y.1 i), fun i => (h _ _).1 (y.2 i)⟩
  invFun y := ⟨fun i => e.symm (y.1 i), fun i => (h _ _).2 (by simpa using y.2 i)⟩
  left_inv y := by apply Subtype.ext; funext i; simp
  right_inv y := by apply Subtype.ext; funext i; simp

section generic
variable {S : Type} [Fintype S] [DecidableEq S] (R : S → S → Prop) [DecidableRel R]

instance (n : ℕ) : Fintype (Chain R n) := by unfold Chain; infer_instance

def V : ℕ → S → ℕ
  | 0, _ => 1
  | n + 1, s => ∑ t, if R s t then V n t else 0

theorem cardStart (n : ℕ) (s : S) :
    Fintype.card {y : Chain R n // y.1 0 = s} = V R n s := by
  induction n generalizing s with
  | zero =>
    simp only [V]
    rw [Fintype.card_eq_one_iff]
    refine ⟨⟨⟨fun _ => s, fun i => i.elim0⟩, rfl⟩, ?_⟩
    rintro ⟨⟨y, hy⟩, h0⟩
    apply Subtype.ext; apply Subtype.ext
    funext j
    have : j = 0 := Fin.ext (by have := j.2; omega)
    subst this; exact h0
  | succ n ih =>
    have e : {y : Chain R (n + 1) // y.1 0 = s} ≃
        Σ t : S, {z : Chain R n // z.1 0 = t ∧ R s t} :=
      { toFun := fun y => ⟨y.1.1 1, ⟨⟨fun j => y.1.1 j.succ, fun i => y.1.2 i.succ⟩, rfl, by
          have h := y.1.2 0
          have h0 : y.1.1 (Fin.castSucc 0) = s := y.2
          rw [h0] at h
          exact h⟩⟩
        invFun := fun p => ⟨⟨Fin.cons s p.2.1.1, by
          intro i
          refine Fin.cases ?_ (fun j => ?_) i
          · have h2 := p.2.2.2
            rw [← p.2.2.1] at h2
            simpa using h2
          · simpa using p.2.1.2 j⟩, rfl⟩
        left_inv := by
          rintro ⟨⟨y, hy⟩, h0⟩
          apply Subtype.ext; apply Subtype.ext
          funext j
          refine Fin.cases ?_ (fun k => ?_) j
          · simpa using h0.symm
          · simp
        right_inv := by
          rintro ⟨t, ⟨⟨z, hz⟩, h1, h2⟩⟩
          simp only [Fin.cons_succ]
          have : (Fin.cons s z : Fin (n + 2) → S) 1 = t := by
            have : (1 : Fin (n + 2)) = Fin.succ 0 := rfl
            rw [this, Fin.cons_succ]; exact h1
          subst this
          rfl }
    rw [Fintype.card_congr e, Fintype.card_sigma]
    simp only [V]
    apply Finset.sum_congr rfl
    intro t _
    by_cases h : R s t
    · simp only [h, if_true, and_true]
      exact ih t
    · simp only [h, if_false, and_false]
      simp [Fintype.card_eq_zero_iff]

theorem cardChain (n : ℕ) : Fintype.card (Chain R n) = ∑ s, V R n s := by
  rw [← Fintype.card_congr (Equiv.sigmaFiberEquiv (fun y : Chain R n => y.1 0)), Fintype.card_sigma]
  apply Finset.sum_congr rfl
  intro s _
  exact cardStart R n s

theorem rec_gen (m : ℕ) (c : ℕ → ℤ)
    (h0 : ∀ s, ∑ j ∈ Finset.range (m + 1), c j * (V R j s : ℤ) = 0) :
    ∀ n s, ∑ j ∈ Finset.range (m + 1), c j * (V R (n + j) s : ℤ) = 0 := by
  intro n
  induction n with
  | zero => simpa using h0
  | succ n ih =>
    intro s
    have : ∀ j, (V R (n + 1 + j) s : ℤ) = ∑ t, if R s t then (V R (n + j) t : ℤ) else 0 := by
      intro j
      rw [show n + 1 + j = (n + j) + 1 by omega]
      simp [V]
    simp only [this, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_eq_zero
    intro t _
    by_cases h : R s t
    · have := ih t
      simp only [h, if_true]
      simpa [← Finset.mul_sum] using this
    · simp [h]

theorem rec_total (m : ℕ) (c : ℕ → ℤ)
    (h0 : ∀ s, ∑ j ∈ Finset.range (m + 1), c j * (V R j s : ℤ) = 0) (n : ℕ) :
    ∑ j ∈ Finset.range (m + 1), c j * (∑ s, (V R (n + j) s : ℤ)) = 0 := by
  have h := Finset.sum_eq_zero (s := (Finset.univ : Finset S)) (fun s _ => rec_gen R m c h0 n s)
  rw [Finset.sum_comm] at h
  simpa [Finset.mul_sum] using h
end generic

/-- one transfer step: new[s] = sum of old[t] over the neighbours t of s -/
def stepL (adj : List (List ℕ)) (v : List ℕ) : List ℕ :=
  adj.map fun l => (l.map fun t => v.getD t 0).sum

def iterL (adj : List (List ℕ)) (N : ℕ) : ℕ → List ℕ
  | 0 => List.replicate N 1
  | n + 1 => stepL adj (iterL adj N n)

theorem length_iterL (adj : List (List ℕ)) (N : ℕ) (hlen : adj.length = N) (n : ℕ) :
    (iterL adj N n).length = N := by
  cases n <;> simp [iterL, stepL, hlen]

theorem V_eq_iterL (N : ℕ) (R : Fin N → Fin N → Prop) [DecidableRel R] (adj : List (List ℕ))
    (hlen : adj.length = N) (hnd : ∀ s : Fin N, (adj.getD s []).Nodup)
    (hmem : ∀ s t : Fin N, R s t ↔ t.val ∈ adj.getD s [])
    (hlt : ∀ s : Fin N, ∀ t ∈ adj.getD s [], t < N) :
    ∀ n (s : Fin N), V R n s = (iterL adj N n).getD s 0 := by
  intro n
  induction n with
  | zero => intro s; simp [V, iterL, List.getD_eq_getElem?_getD]
  | succ n ih =>
    intro s
    have hs : (s : ℕ) < adj.length := by rw [hlen]; exact s.2
    have e1 : (iterL adj N (n + 1)).getD s 0 =
        ((adj.getD s []).map fun t => (iterL adj N n).getD t 0).sum := by
      simp [iterL, stepL, List.getD_eq_getElem?_getD, List.getElem?_map, hs,
        List.getElem?_eq_getElem hs]
    rw [e1, ← List.sum_toFinset _ (hnd s)]
    simp only [V]
    have : ∀ t : Fin N, (if R s t then V R n t else 0) =
        if t.val ∈ (adj.getD s []).toFinset then (iterL adj N n).getD t 0 else 0 := by
      intro t
      by_cases h : R s t
      · have := (hmem s t).1 h
        rw [if_pos h, if_pos (List.mem_toFinset.2 this), ih t]
      · rw [if_neg h, if_neg (by rw [List.mem_toFinset]; exact mt (hmem s t).2 h)]
    simp only [this]
    set F := (adj.getD s []).toFinset with hF
    set g : ℕ → ℕ := fun x => (iterL adj N n).getD x 0 with hg
    rw [show (∑ t : Fin N, if t.val ∈ F then (iterL adj N n).getD t 0 else 0) =
        ∑ t : Fin N, (fun x : ℕ => if x ∈ F then g x else 0) t.val from rfl,
      Fin.sum_univ_eq_sum_range (fun x : ℕ => if x ∈ F then g x else 0) N,
      Finset.sum_ite_mem, Finset.inter_eq_right.2]
    intro t ht
    exact Finset.mem_range.2 (hlt s t (List.mem_toFinset.1 ht))
theorem sum_getD (l : List ℕ) (N : ℕ) (h : l.length = N) : ∑ s : Fin N, l.getD s 0 = l.sum := by
  subst h
  rw [← Fin.sum_univ_getElem l]
  apply Finset.sum_congr rfl
  intro i _
  simp [List.getD_eq_getElem?_getD]

theorem testBit_foldl_land (l : List ℕ) : ∀ (init t : ℕ),
    (l.foldl (· &&& ·) init).testBit t = true ↔ (init.testBit t = true ∧ ∀ x ∈ l, x.testBit t = true) := by
  induction l with
  | nil => intro init t; simp
  | cons x l ih =>
    intro init t
    simp only [List.foldl_cons, ih, Nat.testBit_and, Bool.and_eq_true, List.mem_cons, forall_eq_or_imp]
    tauto

/-- the adjacency lists `adj` describe the relation `R` on `Fin N` (sorted/duplicate-free not needed, only nodup) -/
structure AdjOK (N : ℕ) (R : Fin N → Fin N → Prop) (adj : List (List ℕ)) : Prop where
  len : adj.length = N
  nodup : ∀ s : Fin N, (adj.getD s []).Nodup
  mem : ∀ s t : Fin N, R s t ↔ t.val ∈ adj.getD s []
  lt : ∀ s : Fin N, ∀ t ∈ adj.getD s [], t < N

theorem testBit_foldl_lor (l : List ℕ) : ∀ (init t : ℕ),
    (l.foldl (fun a x => a ||| 2 ^ x) init).testBit t = true ↔ (init.testBit t = true ∨ t ∈ l) := by
  induction l with
  | nil => intro init t; simp
  | cons x l ih =>
    intro init t
    simp only [List.foldl_cons, ih, Nat.testBit_or, Bool.or_eq_true, Nat.testBit_two_pow, decide_eq_true_eq,
      List.mem_cons]
    constructor
    · rintro ((h | h) | h)
      · exact Or.inl h
      · exact Or.inr (Or.inl h.symm)
      · exact Or.inr (Or.inr h)
    · rintro (h | h | h)
      · exact Or.inl (Or.inl h)
      · exact Or.inl (Or.inr h.symm)
      · exact Or.inr h

/-- build `AdjOK` from a bitmask description of the relation and an explicit literal adjacency list -/
theorem adjOK_of_mask (N : ℕ) (R : Fin N → Fin N → Prop) (mask : ℕ → ℕ) (adj : List (List ℕ))
    (hR : ∀ s t : Fin N, R s t ↔ (mask s).testBit t = true)
    (hlen : adj.length = N)
    (hadj : ∀ s < N, (adj.getD s []).foldl (fun a x => a ||| 2 ^ x) 0 = mask s)
    (hnd : ∀ s < N, (adj.getD s []).Nodup)
    (hlt : ∀ s < N, ∀ t ∈ adj.getD s [], t < N) : AdjOK N R adj where
  len := hlen
  nodup := fun s => hnd s s.2
  mem := fun s t => by
    rw [hR, ← hadj s s.2, testBit_foldl_lor]
    simp
  lt := fun s => hlt s s.2

theorem V_eq_iterL' (N : ℕ) (R : Fin N → Fin N → Prop) [DecidableRel R] (adj : List (List ℕ))
    (H : AdjOK N R adj) (n : ℕ) (s : Fin N) :
    V R n s = (iterL adj N n).getD s 0 :=
  V_eq_iterL N R adj H.len H.nodup H.mem H.lt n s

theorem sum_V_eq (N : ℕ) (R : Fin N → Fin N → Prop) [DecidableRel R] (adj : List (List ℕ))
    (H : AdjOK N R adj) (n : ℕ) :
    ∑ s, V R n s = (iterL adj N n).sum := by
  simp only [V_eq_iterL' N R adj H n]
  exact sum_getD _ N (length_iterL _ N H.len n)

/-- linear combination of the vectors `f j` (j in L) with natural coefficients `c j`, as a list fold -/
def comb (N : ℕ) (c : ℕ → ℕ) (f : ℕ → List ℕ) (L : List ℕ) : List ℕ :=
  L.foldl (fun acc j => List.zipWith (· + ·) acc ((f j).map (c j * ·))) (List.replicate N 0)

theorem foldl_comb_getD (N : ℕ) (c : ℕ → ℕ) (f : ℕ → List ℕ) (hf : ∀ j, (f j).length = N) (L : List ℕ) :
    ∀ (acc : List ℕ), acc.length = N → ∀ s < N,
      (L.foldl (fun acc j => List.zipWith (· + ·) acc ((f j).map (c j * ·))) acc).getD s 0 =
        acc.getD s 0 + (L.map fun j => c j * (f j).getD s 0).sum := by
  induction L with
  | nil => intro acc _ s _; simp
  | cons j L ih =>
    intro acc hacc s hs
    have hl : (List.zipWith (· + ·) acc ((f j).map (c j * ·))).length = N := by simp [hacc, hf]
    rw [List.foldl_cons, ih _ hl s hs]
    have h1 : s < acc.length := by omega
    have h2 : s < (f j).length := by rw [hf]; exact hs
    simp [List.getD_eq_getElem?_getD, List.getElem?_zipWith, List.getElem?_map, List.getElem?_eq_getElem h1,
      List.getElem?_eq_getElem h2]
    ring

theorem comb_getD (N : ℕ) (c : ℕ → ℕ) (f : ℕ → List ℕ) (hf : ∀ j, (f j).length = N) (L : List ℕ)
    (s : ℕ) (hs : s < N) :
    (comb N c f L).getD s 0 = (L.map fun j => c j * (f j).getD s 0).sum := by
  unfold comb
  rw [foldl_comb_getD N c f hf L _ (by simp) s hs]
  simp [List.getD_eq_getElem?_getD, hs]

theorem sum_range_eq_list (K : ℕ) (g : ℕ → ℕ) :
    ∑ j ∈ Finset.range K, g j = ((List.range K).map g).sum := by
  induction K with
  | zero => simp
  | succ K ih => rw [Finset.sum_range_succ, ih, List.range_succ, List.map_append, List.sum_append]; simp

/-- componentwise recurrence from a kernel-checked equality of two Nat vectors (positive/negative parts) -/
theorem h0_of_chk (N : ℕ) (R : Fin N → Fin N → Prop) [DecidableRel R] (adj : List (List ℕ))
    (H : AdjOK N R adj) (K : ℕ) (cp cn : ℕ → ℕ)
    (chk : comb N cp (iterL adj N) (List.range (K + 1)) = comb N cn (iterL adj N) (List.range (K + 1)))
    (s : Fin N) :
    ∑ j ∈ Finset.range (K + 1), ((cp j : ℤ) - cn j) * (V R j s : ℤ) = 0 := by
  have hf : ∀ j, (iterL adj N j).length = N := length_iterL adj N H.len
  have h := congrArg (fun l => l.getD s 0) chk
  simp only [comb_getD N _ _ hf _ s s.2] at h
  simp only [V_eq_iterL' N R adj H, sub_mul, Finset.sum_sub_distrib]
  rw [sub_eq_zero]
  have h' : ∑ j ∈ Finset.range (K + 1), cp j * (iterL adj N j).getD s 0 =
      ∑ j ∈ Finset.range (K + 1), cn j * (iterL adj N j).getD s 0 := by
    rw [sum_range_eq_list, sum_range_eq_list]; exact h
  exact_mod_cast h'
/-! Packed vectors: a vector of N naturals below 2^128 is one big Nat (digit t = bits 128t..128t+127), so a lookup is
two GMP operations instead of a linear list walk. -/
def dg (v t : ℕ) : ℕ := (v >>> (128 * t)) % 2 ^ 128

def pack : List ℕ → ℕ
  | [] => 0
  | x :: l => x + 2 ^ 128 * pack l

theorem dg_pack (l : List ℕ) (h : ∀ x ∈ l, x < 2 ^ 128) : ∀ t, dg (pack l) t = l.getD t 0 := by
  induction l with
  | nil => intro t; simp [dg, pack]
  | cons x l ih =>
    intro t
    have hx : x < 2 ^ 128 := h x (by simp)
    have hl : ∀ y ∈ l, y < 2 ^ 128 := fun y hy => h y (by simp [hy])
    have hd : (x + 2 ^ 128 * pack l) / 2 ^ 128 = pack l := by
      rw [Nat.add_mul_div_left _ _ (by positivity), Nat.div_eq_of_lt hx, zero_add]
    cases t with
    | zero =>
      simp only [dg, pack, Nat.mul_zero, Nat.shiftRight_zero, Nat.add_mul_mod_self_left]
      rw [Nat.mod_eq_of_lt hx]; simp
    | succ t =>
      have : dg (pack (x :: l)) (t + 1) = dg (pack l) t := by
        simp only [dg, pack, show 128 * (t + 1) = 128 + 128 * t by ring, Nat.shiftRight_add]
        rw [show (x + 2 ^ 128 * pack l) >>> 128 = pack l by rw [Nat.shiftRight_eq_div_pow]; exact hd]
      rw [this, ih hl t]; simp

def stepP (adj : List (List ℕ)) (v : ℕ) : ℕ := pack (adj.map fun l => (l.map fun t => dg v t).sum)

def iterP (adj : List (List ℕ)) (N : ℕ) : ℕ → ℕ
  | 0 => pack (List.replicate N 1)
  | n + 1 => stepP adj (iterP adj N n)

def unpackN (N v : ℕ) : List ℕ := (List.range N).map (dg v)

theorem iterL_bound (adj : List (List ℕ)) (N Δ : ℕ) (hΔ : ∀ l ∈ adj, l.length ≤ Δ) (h1 : 1 ≤ Δ) :
    ∀ n, ∀ x ∈ iterL adj N n, x ≤ Δ ^ n := by
  intro n
  induction n with
  | zero =>
    intro x hx
    have := List.eq_of_mem_replicate (show x ∈ List.replicate N 1 from hx)
    rw [this]; simp
  | succ n ih =>
    intro x hx
    simp only [iterL, stepL, List.mem_map] at hx
    obtain ⟨l, hl, rfl⟩ := hx
    have hv : ∀ t, (iterL adj N n).getD t 0 ≤ Δ ^ n := by
      intro t
      by_cases ht : t < (iterL adj N n).length
      · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem ht]
        exact ih _ (List.getElem_mem ht)
      · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]; simp
    calc (l.map fun t => (iterL adj N n).getD t 0).sum
        ≤ (l.map fun t => (iterL adj N n).getD t 0).length • Δ ^ n :=
          List.sum_le_card_nsmul _ _ (by intro y hy; obtain ⟨t, _, rfl⟩ := List.mem_map.1 hy; exact hv t)
      _ ≤ Δ * Δ ^ n := by
          simp only [List.length_map, smul_eq_mul]
          exact Nat.mul_le_mul_right _ (hΔ l hl)
      _ = Δ ^ (n + 1) := by ring

theorem iterP_eq (adj : List (List ℕ)) (N Δ : ℕ) (hΔ : ∀ l ∈ adj, l.length ≤ Δ) (h1 : 1 ≤ Δ) (K : ℕ)
    (hK : Δ ^ K < 2 ^ 128) : ∀ n ≤ K, iterP adj N n = pack (iterL adj N n) := by
  intro n
  induction n with
  | zero => intro _; rfl
  | succ n ih =>
    intro hn
    have hb : ∀ x ∈ iterL adj N n, x < 2 ^ 128 := fun x hx =>
      lt_of_le_of_lt ((iterL_bound adj N Δ hΔ h1 n x hx).trans (Nat.pow_le_pow_right h1 (by omega))) hK
    simp only [iterP, stepP, iterL, stepL, ih (by omega)]
    congr 1
    apply List.map_congr_left
    intro l _
    congr 1
    apply List.map_congr_left
    intro t _
    exact dg_pack _ hb t

theorem unpack_iterP (adj : List (List ℕ)) (N Δ : ℕ) (hlen : adj.length = N) (hΔ : ∀ l ∈ adj, l.length ≤ Δ)
    (h1 : 1 ≤ Δ) (K : ℕ) (hK : Δ ^ K < 2 ^ 128) (n : ℕ) (hn : n ≤ K) :
    unpackN N (iterP adj N n) = iterL adj N n := by
  have hb : ∀ x ∈ iterL adj N n, x < 2 ^ 128 := fun x hx =>
    lt_of_le_of_lt ((iterL_bound adj N Δ hΔ h1 n x hx).trans (Nat.pow_le_pow_right h1 hn)) hK
  apply List.ext_getElem
  · simp [unpackN, length_iterL adj N hlen n]
  · intro i h1' h2'
    simp only [unpackN, List.getElem_map, List.getElem_range]
    rw [iterP_eq adj N Δ hΔ h1 K hK n hn, dg_pack _ hb, List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem h2']
    simp
/-- same as `h0_of_chk`, with the vectors computed in packed form (fast kernel evaluation) -/
theorem h0_of_chkP (N : ℕ) (R : Fin N → Fin N → Prop) [DecidableRel R] (adj : List (List ℕ))
    (H : AdjOK N R adj) (Δ : ℕ) (hΔ : ∀ l ∈ adj, l.length ≤ Δ) (h1 : 1 ≤ Δ) (Kb : ℕ) (hKb : Δ ^ Kb < 2 ^ 128)
    (K : ℕ) (hle : K ≤ Kb) (cp cn : ℕ → ℕ)
    (chk : comb N cp (fun j => unpackN N (iterP adj N j)) (List.range (K + 1)) =
      comb N cn (fun j => unpackN N (iterP adj N j)) (List.range (K + 1)))
    (s : Fin N) :
    ∑ j ∈ Finset.range (K + 1), ((cp j : ℤ) - cn j) * (V R j s : ℤ) = 0 := by
  have hf : ∀ j, (unpackN N (iterP adj N j)).length = N := by intro j; simp [unpackN]
  have h := congrArg (fun l => l.getD s 0) chk
  simp only [comb_getD N _ _ hf _ s s.2] at h
  have e : ∀ c : ℕ → ℕ, ((List.range (K + 1)).map fun j => c j * (unpackN N (iterP adj N j)).getD s 0).sum =
      ((List.range (K + 1)).map fun j => c j * (iterL adj N j).getD s 0).sum := by
    intro c
    congr 1
    apply List.map_congr_left
    intro j hj
    rw [unpack_iterP adj N Δ H.len hΔ h1 Kb hKb j (by simp at hj; omega)]
  rw [e, e] at h
  simp only [V_eq_iterL' N R adj H, sub_mul, Finset.sum_sub_distrib]
  rw [sub_eq_zero]
  have h' : ∑ j ∈ Finset.range (K + 1), cp j * (iterL adj N j).getD s 0 =
      ∑ j ∈ Finset.range (K + 1), cn j * (iterL adj N j).getD s 0 := by
    rw [sum_range_eq_list, sum_range_eq_list]; exact h
  exact_mod_cast h'
end fastvec

open PowerSeries in
theorem gf_gen (b : ℕ → ℚ) (m q : ℕ) (d p : ℕ → ℚ) (D N : PowerSeries ℚ)
    (hD : D = ∑ j ∈ Finset.range (m + 1), C (d j) * X ^ j)
    (hN : N = ∑ j ∈ Finset.range (q + 1), C (p j) * X ^ j) (hD0 : d 0 ≠ 0) (hp : ∀ n, q < n → p n = 0)
    (hb : ∀ n, ∑ j ∈ Finset.range (m + 1), d j * (if j ≤ n then b (n - j) else 0) =
      if n ≤ q then p n else 0) :
    mk b = N * D⁻¹ := by
  have hc : constantCoeff D ≠ 0 := by
    rw [hD]
    simp only [map_sum, map_mul, map_pow, constantCoeff_C, constantCoeff_X]
    rw [Finset.sum_eq_single 0]
    · simpa using hD0
    · intro j _ hj; simp [hj]
    · intro h; exfalso; exact h (by simp)
  rw [eq_mul_inv_iff_mul_eq hc, hD, hN]
  ext n
  simp only [Finset.mul_sum, map_sum]
  have : ∀ j ∈ Finset.range (m + 1), coeff n (mk b * (C (d j) * X ^ j)) =
      d j * (if j ≤ n then b (n - j) else 0) := by
    intro j _
    rw [mul_left_comm, coeff_C_mul, coeff_mul_X_pow']
    simp
  rw [Finset.sum_congr rfl this, hb n]
  simp only [coeff_C_mul, coeff_X_pow]
  rw [Finset.sum_eq_single n]
  · by_cases h : n ≤ q
    · simp [h]
    · simp [h, hp n (by omega)]
  · intro j _ hj; simp [Ne.symm hj]
  · intro h; simp at h; simp [hp n (by omega)]

section fastvec2
def incB : ℕ → List ℕ → Bool
  | _, [] => true
  | p, x :: r => decide (p ≤ x) && incB (x + 1) r

theorem incB_ge : ∀ (l : List ℕ) (p : ℕ), incB p l = true → ∀ y ∈ l, p ≤ y
  | [], p, _, y, hy => by simp at hy
  | x :: r, p, h, y, hy => by
    simp only [incB, Bool.and_eq_true, decide_eq_true_eq] at h
    rcases List.mem_cons.1 hy with rfl | hy
    · exact h.1
    · have := incB_ge r (x + 1) h.2 y hy
      omega

theorem incB_nodup : ∀ (l : List ℕ) (p : ℕ), incB p l = true → l.Nodup
  | [], p, _ => List.nodup_nil
  | x :: r, p, h => by
    simp only [incB, Bool.and_eq_true, decide_eq_true_eq] at h
    refine List.nodup_cons.2 ⟨?_, incB_nodup r _ h.2⟩
    intro hx
    have := incB_ge r (x + 1) h.2 x hx
    omega

def chkA (N : ℕ) (mask : ℕ → ℕ) : ℕ → List (List ℕ) → Bool
  | _, [] => true
  | s, l :: r => (l.foldl (fun a x => a ||| 2 ^ x) 0 == mask s) && incB 0 l &&
      l.all (fun x => decide (x < N)) && chkA N mask (s + 1) r

theorem chkA_sound (N : ℕ) (mask : ℕ → ℕ) : ∀ (adj : List (List ℕ)) (s0 : ℕ), chkA N mask s0 adj = true →
    ∀ i < adj.length, (adj.getD i []).foldl (fun a x => a ||| 2 ^ x) 0 = mask (s0 + i) ∧
      (adj.getD i []).Nodup ∧ ∀ t ∈ adj.getD i [], t < N := by
  intro adj
  induction adj with
  | nil => intro s0 _ i hi; simp at hi
  | cons l r ih =>
    intro s0 h i hi
    simp only [chkA, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
    cases i with
    | zero =>
      simp only [List.getD_cons_zero, Nat.add_zero]
      exact ⟨h1, incB_nodup _ _ h2, h3⟩
    | succ i =>
      have := ih (s0 + 1) h4 i (by simpa using hi)
      simp only [List.getD_cons_succ]
      rw [show s0 + (i + 1) = s0 + 1 + i by omega]
      exact this

theorem adjOK_of_chk (N : ℕ) (R : Fin N → Fin N → Prop) (mask : ℕ → ℕ) (adj : List (List ℕ))
    (hR : ∀ s t : Fin N, R s t ↔ (mask s).testBit t = true)
    (hlen : adj.length = N) (hc : chkA N mask 0 adj = true) : AdjOK N R adj where
  len := hlen
  nodup := fun s => (chkA_sound N mask adj 0 hc s (by rw [hlen]; exact s.2)).2.1
  mem := fun s t => by
    have h := (chkA_sound N mask adj 0 hc s (by rw [hlen]; exact s.2)).1
    rw [zero_add] at h
    rw [hR, ← h, testBit_foldl_lor]
    simp
  lt := fun s => (chkA_sound N mask adj 0 hc s (by rw [hlen]; exact s.2)).2.2
end fastvec2


def PO (u v : Fin 5 → Fin 4) : Prop :=
  ∀ j : Fin 4, (((v j.castSucc : Fin 4) : ℕ) : ℤ) - ((u j.castSucc : Fin 4) : ℕ) ≤ (((v j.succ : Fin 4) : ℕ) : ℤ) - ((u j.succ : Fin 4) : ℕ) ∧ ((u j.succ : Fin 4) : ℕ) + ((u j.castSucc : Fin 4) : ℕ) ≤ ((v j.succ : Fin 4) : ℕ) + ((v j.castSucc : Fin 4) : ℕ)

theorem adjall {L : ℕ} (P : Fin (L + 1) → Fin (L + 1) → Prop) :
    (∀ i j : Fin (L + 1), (j : ℕ) = i + 1 → P i j) ↔ ∀ i : Fin L, P i.castSucc i.succ := by
  constructor
  · intro h i
    exact h _ _ (by simp)
  · intro h i j hij
    have hi : (i : ℕ) < L := by have := j.2; omega
    have := h ⟨i, hi⟩
    have e : j = (⟨i, hi⟩ : Fin L).succ := Fin.ext (by simp [hij])
    subst e
    exact this

theorem blk_iff (u v : Fin 5 → Fin 4) : BlockOK u v ↔ PO u v := by
  have := adjall (L := 4) (fun i j => (((v i : ℕ) : ℤ) - (u i : ℕ) ≤ ((v j : ℕ) : ℤ) - (u j : ℕ)) ∧ (u j : ℕ) + (u i : ℕ) ≤ (v j : ℕ) + (v i : ℕ))
  unfold BlockOK PO
  rw [← this]

theorem aeq (n : ℕ) : a n = Nat.card (Chain PO n) := by
  unfold a Chain Good
  apply Nat.card_congr
  apply Equiv.subtypeEquivRight
  intro x
  rw [adjall (L := n) (fun i j => BlockOK (x i) (x j))]
  simp only [blk_iff]

abbrev St := Fin 5 → Fin 4
def N : ℕ := 4 ^ 5
def e0 : St ≃ Fin N := finFunctionFinEquiv
def RN : Fin N → Fin N → Prop := fun i j => PO (e0.symm i) (e0.symm j)
instance : DecidableRel RN := fun i j => by unfold RN PO; infer_instance

def dig (x j : ℕ) : ℕ := x / 4 ^ j % 4
abbrev loc (a b c d : ℕ) : Prop := (c : ℤ) - a ≤ (d : ℤ) - b ∧ b + a ≤ d + c
instance (a b c d : ℕ) : Decidable (loc a b c d) := by unfold loc; infer_instance
def tabL : List ℕ := [173586357316277123608786391666010947078781111168761886364842129636720553256243327199220647797959430639391194421792044603128189141074923297291063985020165744483856413577766274109554905906560678751401702026259117266465964955051703572175947135853118004042633457948139246798231504848293811360132542670251781912369, 80800868208597508778628845197042057760663965654573254606640062113102520767938298161853374654899464118991593414900309189642134911576981094562437078155433734762669277008054287545567378966572136238385748248060058440938377454781103023372176464241864760782538378617916746791117510892864248469905092790805083484944, 34409495206703121609149926471744146270701004385217507665185121508241377665433799977671399092580760385273986549311158286083342623941528070688186132142237940279159540018639088232332876213901442048285946021987553404506077091009443112614767163479425297367468815228922721066939776501904166648780876017377069773056, 11235753536882651954008139256079721231249307554356737196795141716976776380549812237606987458801880942130281322224051685251703713940090798592060777842363409070745972250984192075863796314743328015766839517383690907593821090941858975547679073789200097099581653952301296674919110694499319722050898291388430946304, 179382535837623081513771547488300119676835258351954216857231810898432449860760356803240072724826709553141508004277254859704568522802318770295220338433474798040127468110561586086190697315997361392347827978464131643357015727795880333731671228362048620539561200819529051454995196473654422339794053434339612622706, 173539724550132835258391338353668819329530320585650542484874962300492866440210771826164173484775926738996610734663673294864205019215308662628938732768378591663006149532779279171740041517559058493523763483340288471195189818687931208263761944384754624733382264560153621299336576898634024144489265016210374850336, 80054743950288895172307992199568013772651316324791752527165384733459531711417412192949785643963401712678254420846368257418388961823146939968433042126839289629065052288262368540529548742546212112338731561358797716605975272960745200777213400748050691834519284410146738808798663698307653019612650326142570492416, 22471507073765303908016278512159442462498615108713474393590283433953552761099624475213974917603761884260562644448103370503407427880181597184121555684726818141491944501968384151727592629486656031533679034767381815187642181883717951095358147578400194199163307904602593349838221388998639444101796582776861892608, 179695249681178897510538375582829682230634677556347934640541050682547526156508081069618782824998441591081657435608685985710109104684440438029472030004282764015241003471062610963302140865772932533411651148625689446937507818705883244672207218208720693554539791774256187153467066253725936609401915349676107038692, 178543146047025891206660587866141820190321027855950027017822798846334087172174360088223535087523639346039001635966571310952854329329255346376965797901306047264822715300795677205523138313968196750544934205925213328483063273247977783312337781931507792973039719835787792474886493379778252458215055661594285506112, 160109487900577790344615984399136027545302632649583505054330769466919063422834824385899571287926803425356508841692736514836777923646293879936866084253678579258130104576524737081059097485092424224677463122717595433211950545921490401554426801496101383669038568820293477617597327396615306039225300652285140984832, 44943014147530607816032557024318884924997230217426948787180566867907105522199248950427949835207523768521125288896206741006814855760363194368243111369453636282983889003936768303455185258973312063067358069534763630375284363767435902190716295156800388398326615809205186699676442777997278888203593165553723785216, 178916208176180198009821014364878842184327352520840778057560137536155581700434803072675329592991670549195671132993541777064727304206172423673967815915603269831624827660691636708042053425981158813568442549275843690649264364158156694609819313678414827447049266939672796466045916977056550183361276893925542002376, 166078481967046699195182808378928379449403827287835521690128188504062975875001912137128283375415302675863220794124263972626745521676967116688898372482434140326963902334860089121361739277299817233053596616327681227871168000484352982314131309446613935253191322482453541476148104953068069641564840369585244925056, 140446919211033149425101740700996515390616344429459214959939271462209704756872652970087343235023511776628516527800646065646296424251134982400759723029542613384324653137302400948297453934291600197085493967296136344922763636773237194345988422365001213744770674403766208436488883681241496525636228642355386828800, 89886028295061215632065114048637769849994460434853897574361133735814211044398497900855899670415047537042250577792413482013629711520726388736486222738907272565967778007873536606910370517946624126134716139069527260750568727534871804381432590313600776796653231618410373399352885555994557776407186331107447570432, 179766741823881399488329593543172672349141274954893914540740845398490433166009096418814837196952880925853348598727744535544628114293077077877025326783195375086568557834080752002862477444638673952821248241803031787577830733668948720678807007270157761161255047311637223024284626134303230611325367892477839605775, 11232849704094924507520872391723542329767058145171052900709878168128389932285537898985312932538405945711721216439140027501098956305470922073446881513005566485878351185678558308755290995308210122536000521937018781102064321422483613209032872248408938419494734939257530915181671783228890118227507681476110909440, 699481446608269830356559205445470841882741706136049258136572916008886381358495258941323066312821596009757221451934001402653668608831949411683145172289485592559466993324783458521632082457117958555352064356566880292651190199501950970316176499691798233906853893984411502973336159055756832606820086631125483520, 41145930515952665126650047246620744119875955538919413184513996895789186454794392750087781467299166346766844355172183356557468430893823729409913179373334417419038489699458680347212248807714910903906114451291715532319601692929316737880844172075724535174905576719921939927871372580589293708735614069180989440, 179769313446991137294951925440821679805712967926674234962068937325393014985289833187208692781861189521497271592287900118422439000195761046910851663876655418415917343694049979783306878927808705032399222681226588171567520469117930194785882503421181208034453953704898260143184037945688518082027068937178212925680, 179766741823871819308664116717076216212237656740250185058542399655730498314650391358704925483450530065849027174795419507715317474602065522916274638510405198687908470128990377513050892026465041344668862584128199929408566705872370694508748625721023220383024123694586155107034142729428570024907173165142004203520, 11232849076248269950831597334374154214243743253715707543369680653037971288190718535811256842472444702502882387586116205799016166172205014316340235936005103898370510382895994016693325568121602247789539144156361800214738644884960532262939668167144496277684567880470505987501249917472698615417857000167188725760, 658334888255242642026400755945931905918015288622710610952223950332626983276710284001404503476786661548269509682754933704919494894301179670558610869973350678704615835191338885555395980923438574462497831220667448517113627086869067806093506753211592562798489227518751038845941961289428699339769825106895831040, 179769313486221409502296819100862708443061715090139516166793531612628586474858998307776069050229602410359154683456200323749949621358181765977271119738585115177006850829509587190627148835260843993185394338456149335226128919490884949241458219158620672464584842451313645702165856514702075656294214004461131534080, 179769312818991199863615021165928993499731761600919217889553607926143638719455732862276049275757614518219289980517675851451385975006310259781734005935012133449848099609821423654259546809843975427214590780648621459971970347835158695118855194553764113440949008773294148539495881601937757196526302618495924305920, 179725585219972319213305557349986467427899892059451320693914890448607540611051496572980109479559115240046118201377859292784258658755280229061443774976081662373928166126335904267093209089945635964632626306501788803435818318159368516207034690674311940442953086087528095800019998679563177846685712002675019612160, 10533358212083882272422412095134910494688244617963369775235583205322031732427364544022472055628586584772312154924078939278711918308818874728937773919573610859273853363061422168886335694775017191399965299530679176273818033389905084897496108051385481004775827640300016621535071380630859189436317201710333296640, 179769312858231615773408100857013330256951968781635176974387370270836789884711659072474427781386737095919842407320989840307766149389639379016553171283574662361567339659995333922513419649043138419386244616759912521277428202618753887677986019808843141074812144214468337597475907968547519165451905786077731942400, 179728156879869383412576192253080188611397687460545904359363912258962306823431608133913854389736367423449961183363432984515367044612438402170264058369976420806044094323719244552903598846291490926138429696072782517921789415853908071404798607533466953297397358879182199579027960816923573355014902644020283965440, 179069661226083245672751421245246392206207650752598468642328946615280526275418621897928905432027678139025979561481540229197887453026851734375030276206462218008744197077650393038589407576725774435730904224174751728875676542734194525553551389634307909864637501483645277687341705431510893051274188404954989854720, 168533731393342116358758593522158567915011913887413916403769331285152507718837832704359552890057385356356994478785263028459390692941101995663004382713177773748381653808982754702181371116400275062399444792490866820381088534238481358359937728822167696076413242244800265944561142090093747030981075227365332746240, 179769313486231590763185353769193322059222300781592621861952024945890690199784745504146656508192294171826295033281041335686112766121450966404709974995239462752065088845545980135915311317949652546099865648644971734712785797348792611192411968762755874098209032123875797943673195465861324254831398530343753547775, 2743062034396834596313958994602257636696249594197154953170570978636169831322422515930522978433219718920095327759063630359292795778211993537944149031873847242734265507120343953175512056517025893144262027861691598866346064817090686203019953568498487070963147979265447453069444394237928893109524028131901440, 41855804958468253213147889020335036313001606846958984187092300231508443254579182723815832122761893159445508189955732934136990249691255627211065815197607144405828565483363904099635199827823156778801916506734050088632630974779324617654135582933550511277359746405651899649924071713951368067688609873920, 638659153737098939730958914789400465953273527112488818273288249673450592449383250193185010905102294950681950472938916533706644964298200285766210147251559536549193586962524260308936515274741658942652457657929909736325910264692414377697792033031431753657793197833173899709668362140228395246551040, 179769313486231590772930519078902473361269411424229805498503667171354683518212374847489579375933765821306901450304278349272816562622178364144058185513868979397388626340148691273544215942802500844987352714568746955301633079594200218559910128206349105277371170005781097253576608815314695753522241828595083182080, 179769313486231590763185353769193322059222300781592619985101456648634107566455467231839155953754746747232476557575609962987820764304892773813716524235975919887161762893179475883498272311928545295880043676280065664968811228005631330673558226062449932939443465838782975676816122779328153871555126664462933688320, 2743062034396834596313958994567635854598273772275577514797769806245425586805551911437377624190508441002523119687620864044540709537472773749202609550556591963031940404066930406036216716225154917930304059127975164266558013299463728407273843940830958340104480094098596093290597863555185219824269131943772160, 41855166299314516114208123439638148936713733872844067194358218730599258026762780684660572874676784001887892306194524833952998684380246853927974348210278205787287950915175989923606463465045469360465671465070094564479854855106882068656802498676747911407717135013194884691372825781222008110877968957440, 179769313486231590772930519078902473361797697894230655396550874393545944171494341625309649808320416349114428865924843844586771504557600022869674169760910464632496605797790269688904560131236443354111629072151229486311162190908942495813404841591297683991245076889726800038375448355690377808960430272857956679680, 179769313486231590772930519078902438739487313448284882642221365362782834906387004032528750611471504929541360046945765751241870760578227981577480484878842467837739309723822951456928778048177458567759357850115826497749656818125002508003232774846561656888488251494695849657101245330929774616095954208288585809920, 179769313486230952104031616667984583366952469939852248009786642022100211256888650067959979978949161189541355171847920946023019940247815700427742219505276810889261246320930351089989498714531752701480406819010980365373145959593654904899098636506297685777087207446845593569892621585952618566403301831067052277760, 2743020178591876128060743577740125728716471263090708787649460222728552974041925594949915303914817716347724910178764379517943721779543857819023726884308792494475703151176973675633473189645219880007478245134833717377751767784284623251492208553279351122016150160224739963133809510398165523554498573594787840, 179769313486231590772930519078902438740015599918285734417147778912172501233150069286997601388039274617082730864779814336316375861816510547506728833706075431114674967678265167995219390034555866470162174244371776948398406125372744993318585524415441503502067486279526597416605202847086490477343874027704706662400, 179769313486230952113776781977693734669527858991478473105504630836141238083083427124619339970435354354507909204885603404761480652041336574322476579380357424467553899655565033411378783808437026577462504867219878318330935021415007333733932505563746985903494934537297706036497120746947469507045585909435533885440, 179769313444375785814462117164063771184938479750801155137002888348536017847207678596259616369366202899199319894823399264104592417058612851720481355581749415219337979245643934872355336527717683056643005121682689543772968240928226627109306930438513926916705246054668432525329203097948306517741532547409216798720, 179766570424197193928588891110776879757162660697912691107395025156738447706811635790637649357361493858564499713475502376087959750544186266027538965090061024917959681715534146806315298956589130056170094273156462502068339853510877069409793379747715555132450416900488558223937340073454175751667618519108015882240, 179769313486231590772930519078902473361797697894230657273430081157732675805499410614616176613472471203806076151292252327479799154261926375891666550468539706578078184787908492517480552329283277021502728703543691294647711084363008372613489079954969122972694258182868432066582822554155027898467361283937744715775, 9745314011399999080353382387875188310876226857595007526866353939120647981831277122977152563326757935648805841815488257317038819203841596980946427504817486560073691038580423154685303395863878483935677262670630800874044646712033152753900198307263764989911497201281271137894038198730295869440, 528294531135665246352339784916516606517294807943820813192811729538211400001467973457300559276518383187049817145104798887264558855266974616624154253759595087392487408786619078083013825038416429411832573729318187734509424340296083559172247691845609954336615907167064555520, 28638903918474961202866265841374129555572759683708149974184563685194367394213852121319233313138251489098481100390353242123909130059942303494273445997449765229068587032938030963062346285458128870694774722600146802650667554413021114864465940252658237440, 179769313486231590772930519078902473361797697894230657273430081157732675805500963132708477322407536021120113879871393357658789768814416622492847430639474110969959963482268386429115945691006857189411070247696162398918067647896493089301343400068500988234275161835090917664532250648398885048430687286021775687680, 179769313486231590772930519078902473361797697894230657273430081157732675805499410614616176613472471203806076151292252327479799154261926375891666550468539706578078184787908492517480552329283277021502728703543691292511724048442098290334259463022733203793560720834903569972811199397575866157265948524815077867520, 9745314011399999080353382387875188310876226857595007526866353939120647981831277122977152563326757935648805841815488009986637346099307549886233337800224551002749588032586636570995031091032149673493963632112689549096802233982669384338854999626122782630980760252429819450113102010558195957760, 528294531135665246323700880998041645314428542102446683637238969854503250027283409772106191882304283735329110727432500303452988050283685817176142117705866200207941657957440504548218643368447228950757431646732209627902988284519816491362466345160298892874179793791263703040, 179769313486231590772930519078902473361797697894230657273430081157732675805500963132708477322407536021120113879871393357658789768814416622492847430639474124377767893424865485276302219601246094119453082952085005766702163646421552799078891404371275122566923090063320209056401145172546718476833787143694403502080, 179769313486231590772930519078902473361797697894230657273430081157732675805500963132708477322407536021120113879871393357658789768814416375162445957534940063875246873777675450871791842685013070566318791746469954378333300953115848114839383423043242666473641081264880933755092227740579965792929732450825713745920, 179769313486231590772930519078902473361797697894230657273401442253814200844296544348774802483916898444122368001318063201353987164672493882598741616864076575268280385070184659656863742129902253480585763740733822669301267476640913015826145665610957313042706501593772885891854130010324767619746255360353275740160, 9745314011399999079825087856739523064523887072678490920349059131176827168638465393438941163325285399750887660343751480288784774871945965367695639736809967882280738721493533452962402971491048564184068075802791937820661365017183686541598335322717403873989341904337241070592290009094176112640, 179769313486231590772930519078902473361797697894230657273430081157732675805500963132708477322407536021120113879871393357658789768814416375162445957534940077283054803720272549718978116595252307496360804450858797748253383987561817907011953133515568915396439328378989633567011715974374069096676973913322186342400, 179769313486231590772930519078902473361797697894230657273401442253814200844298096866867103192851963261436405729897204231532977779224984129199922497035010993067970093707141651688846685106258180068614316297665082002129386487445921048160317696785657786360161847141473901945593619380753540605412820414226696765440, 179769313486231590772930519078902473361269403363094992027077741372816159198983668324764656509214640129407477705893809528363363127479249681199353915817151400090767324559722692923848349688899844200531236120628416647577455141025074680698283287572306468571153464098728279832363045418780247133620369903552529694720, 179769313486231590763185205067502474281444315506355468962553854300137668278633056675495528631641109918654498813989383098433484852583007954309388260774271030331189906128552831856770941901289621089582293296594952120485351088863244502600227512615432362217604147069117332627119507135375438757753527739632310026240]
def tab (j a b : ℕ) : ℕ := tabL.getD ((j * 4 + a) * 4 + b) 0
/-- bitmask (over the 1024 states) of the neighbours of s: AND of the per-column-pair masks -/
def mask (s : ℕ) : ℕ := ((List.range 4).map fun j => tab j (dig s j) (dig s (j + 1))).foldl (· &&& ·) (2 ^ N - 1)
def adjLit : List (List ℕ) := [[0, 256, 320, 336, 340, 341, 512, 576, 592, 596, 597, 640, 656, 660, 661, 672, 676, 677, 680, 681, 682, 768, 832, 848, 852, 853, 896, 912, 916, 917, 928, 932, 933, 936, 937, 938, 960, 976, 980, 981, 992, 996, 997, 1000, 1001, 1002, 1008, 1012, 1013, 1016, 1017, 1018, 1020, 1021, 1022, 1023], [1, 257, 321, 337, 340, 341, 342, 513, 577, 593, 596, 597, 598, 641, 657, 660, 661, 662, 673, 676, 677, 678, 680, 681, 682, 683, 769, 833, 849, 852, 853, 854, 897, 913, 916, 917, 918, 929, 932, 933, 934, 936, 937, 938, 939, 961, 977, 980, 981, 982, 993, 996, 997, 998, 1000, 1001, 1002, 1003, 1009, 1012, 1013, 1014, 1016, 1017, 1018, 1019, 1020, 1021, 1022, 1023], [2, 258, 322, 338, 341, 342, 343, 514, 578, 594, 597, 598, 599, 642, 658, 661, 662, 663, 674, 677, 678, 679, 680, 681, 682, 683, 770, 834, 850, 853, 854, 855, 898, 914, 917, 918, 919, 930, 933, 934, 935, 936, 937, 938, 939, 962, 978, 981, 982, 983, 994, 997, 998, 999, 1000, 1001, 1002, 1003, 1010, 1013, 1014, 1015, 1016, 1017, 1018, 1019, 1020, 1021, 1022, 1023], [3, 259, 323, 339, 342, 343, 515, 579, 595, 598, 599, 643, 659, 662, 663, 675, 678, 679, 681, 682, 683, 771, 835, 851, 854, 855, 899, 915, 918, 919, 931, 934, 935, 937, 938, 939, 963, 979, 982, 983, 995, 998, 999, 1001, 1002, 1003, 1011, 1014, 1015, 1017, 1018, 1019, 1020, 1021, 1022, 1023], [4, 260, 324, 340, 344, 345, 516, 580, 596, 600, 601, 644, 660, 664, 665, 676, 680, 681, 684, 685, 686, 772, 836, 852, 856, 857, 900, 916, 920, 921, 932, 936, 937, 940, 941, 942, 964, 980, 984, 985, 996, 1000, 1001, 1004, 1005, 1006, 1012, 1016, 1017, 1020, 1021, 1022], [5, 261, 325, 341, 344, 345, 346, 517, 581, 597, 600, 601, 602, 645, 661, 664, 665, 666, 677, 680, 681, 682, 684, 685, 686, 687, 773, 837, 853, 856, 857, 858, 901, 917, 920, 921, 922, 933, 936, 937, 938, 940, 941, 942, 943, 965, 981, 984, 985, 986, 997, 1000, 1001, 1002, 1004, 1005, 1006, 1007, 1013, 1016, 1017, 1018, 1020, 1021, 1022, 1023], [6, 262, 326, 342, 345, 346, 347, 518, 582, 598, 601, 602, 603, 646, 662, 665, 666, 667, 678, 681, 682, 683, 684, 685, 686, 687, 774, 838, 854, 857, 858, 859, 902, 918, 921, 922, 923, 934, 937, 938, 939, 940, 941, 942, 943, 966, 982, 985, 986, 987, 998, 1001, 1002, 1003, 1004, 1005, 1006, 1007, 1014, 1017, 1018, 1019, 1020, 1021, 1022, 1023], [7, 263, 327, 343, 346, 347, 519, 583, 599, 602, 603, 647, 663, 666, 667, 679, 682, 683, 685, 686, 687, 775, 839, 855, 858, 859, 903, 919, 922, 923, 935, 938, 939, 941, 942, 943, 967, 983, 986, 987, 999, 1002, 1003, 1005, 1006, 1007, 1015, 1018, 1019, 1021, 1022, 1023], [8, 264, 328, 344, 348, 349, 520, 584, 600, 604, 605, 648, 664, 668, 669, 680, 684, 685, 776, 840, 856, 860, 861, 904, 920, 924, 925, 936, 940, 941, 968, 984, 988, 989, 1000, 1004, 1005, 1016, 1020, 1021], [9, 265, 329, 345, 348, 349, 350, 521, 585, 601, 604, 605, 606, 649, 665, 668, 669, 670, 681, 684, 685, 686, 777, 841, 857, 860, 861, 862, 905, 921, 924, 925, 926, 937, 940, 941, 942, 969, 985, 988, 989, 990, 1001, 1004, 1005, 1006, 1017, 1020, 1021, 1022], [10, 266, 330, 346, 349, 350, 351, 522, 586, 602, 605, 606, 607, 650, 666, 669, 670, 671, 682, 685, 686, 687, 778, 842, 858, 861, 862, 863, 906, 922, 925, 926, 927, 938, 941, 942, 943, 970, 986, 989, 990, 991, 1002, 1005, 1006, 1007, 1018, 1021, 1022, 1023], [11, 267, 331, 347, 350, 351, 523, 587, 603, 606, 607, 651, 667, 670, 671, 683, 686, 687, 779, 843, 859, 862, 863, 907, 923, 926, 927, 939, 942, 943, 971, 987, 990, 991, 1003, 1006, 1007, 1019, 1022, 1023], [12, 268, 332, 348, 524, 588, 604, 652, 668, 684, 780, 844, 860, 908, 924, 940, 972, 988, 1004, 1020], [13, 269, 333, 349, 525, 589, 605, 653, 669, 685, 781, 845, 861, 909, 925, 941, 973, 989, 1005, 1021], [14, 270, 334, 350, 526, 590, 606, 654, 670, 686, 782, 846, 862, 910, 926, 942, 974, 990, 1006, 1022], [15, 271, 335, 351, 527, 591, 607, 655, 671, 687, 783, 847, 863, 911, 927, 943, 975, 991, 1007, 1023], [16, 272, 336, 352, 356, 357, 528, 592, 608, 612, 613, 656, 672, 676, 677, 688, 692, 693, 696, 697, 698, 784, 848, 864, 868, 869, 912, 928, 932, 933, 944, 948, 949, 952, 953, 954, 976, 992, 996, 997, 1008, 1012, 1013, 1016, 1017, 1018], [17, 273, 337, 353, 356, 357, 358, 529, 593, 609, 612, 613, 614, 657, 673, 676, 677, 678, 689, 692, 693, 694, 696, 697, 698, 699, 785, 849, 865, 868, 869, 870, 913, 929, 932, 933, 934, 945, 948, 949, 950, 952, 953, 954, 955, 977, 993, 996, 997, 998, 1009, 1012, 1013, 1014, 1016, 1017, 1018, 1019], [18, 274, 338, 354, 357, 358, 359, 530, 594, 610, 613, 614, 615, 658, 674, 677, 678, 679, 690, 693, 694, 695, 696, 697, 698, 699, 786, 850, 866, 869, 870, 871, 914, 930, 933, 934, 935, 946, 949, 950, 951, 952, 953, 954, 955, 978, 994, 997, 998, 999, 1010, 1013, 1014, 1015, 1016, 1017, 1018, 1019], [19, 275, 339, 355, 358, 359, 531, 595, 611, 614, 615, 659, 675, 678, 679, 691, 694, 695, 697, 698, 699, 787, 851, 867, 870, 871, 915, 931, 934, 935, 947, 950, 951, 953, 954, 955, 979, 995, 998, 999, 1011, 1014, 1015, 1017, 1018, 1019], [20, 276, 340, 356, 360, 361, 532, 596, 612, 616, 617, 660, 676, 680, 681, 692, 696, 697, 700, 701, 702, 788, 852, 868, 872, 873, 916, 932, 936, 937, 948, 952, 953, 956, 957, 958, 980, 996, 1000, 1001, 1012, 1016, 1017, 1020, 1021, 1022], [21, 277, 341, 357, 360, 361, 362, 533, 597, 613, 616, 617, 618, 661, 677, 680, 681, 682, 693, 696, 697, 698, 700, 701, 702, 703, 789, 853, 869, 872, 873, 874, 917, 933, 936, 937, 938, 949, 952, 953, 954, 956, 957, 958, 959, 981, 997, 1000, 1001, 1002, 1013, 1016, 1017, 1018, 1020, 1021, 1022, 1023], [22, 278, 342, 358, 361, 362, 363, 534, 598, 614, 617, 618, 619, 662, 678, 681, 682, 683, 694, 697, 698, 699, 700, 701, 702, 703, 790, 854, 870, 873, 874, 875, 918, 934, 937, 938, 939, 950, 953, 954, 955, 956, 957, 958, 959, 982, 998, 1001, 1002, 1003, 1014, 1017, 1018, 1019, 1020, 1021, 1022, 1023], [23, 279, 343, 359, 362, 363, 535, 599, 615, 618, 619, 663, 679, 682, 683, 695, 698, 699, 701, 702, 703, 791, 855, 871, 874, 875, 919, 935, 938, 939, 951, 954, 955, 957, 958, 959, 983, 999, 1002, 1003, 1015, 1018, 1019, 1021, 1022, 1023], [24, 280, 344, 360, 364, 365, 536, 600, 616, 620, 621, 664, 680, 684, 685, 696, 700, 701, 792, 856, 872, 876, 877, 920, 936, 940, 941, 952, 956, 957, 984, 1000, 1004, 1005, 1016, 1020, 1021], [25, 281, 345, 361, 364, 365, 366, 537, 601, 617, 620, 621, 622, 665, 681, 684, 685, 686, 697, 700, 701, 702, 793, 857, 873, 876, 877, 878, 921, 937, 940, 941, 942, 953, 956, 957, 958, 985, 1001, 1004, 1005, 1006, 1017, 1020, 1021, 1022], [26, 282, 346, 362, 365, 366, 367, 538, 602, 618, 621, 622, 623, 666, 682, 685, 686, 687, 698, 701, 702, 703, 794, 858, 874, 877, 878, 879, 922, 938, 941, 942, 943, 954, 957, 958, 959, 986, 1002, 1005, 1006, 1007, 1018, 1021, 1022, 1023], [27, 283, 347, 363, 366, 367, 539, 603, 619, 622, 623, 667, 683, 686, 687, 699, 702, 703, 795, 859, 875, 878, 879, 923, 939, 942, 943, 955, 958, 959, 987, 1003, 1006, 1007, 1019, 1022, 1023], [28, 284, 348, 364, 540, 604, 620, 668, 684, 700, 796, 860, 876, 924, 940, 956, 988, 1004, 1020], [29, 285, 349, 365, 541, 605, 621, 669, 685, 701, 797, 861, 877, 925, 941, 957, 989, 1005, 1021], [30, 286, 350, 366, 542, 606, 622, 670, 686, 702, 798, 862, 878, 926, 942, 958, 990, 1006, 1022], [31, 287, 351, 367, 543, 607, 623, 671, 687, 703, 799, 863, 879, 927, 943, 959, 991, 1007, 1023], [32, 288, 352, 368, 372, 373, 544, 608, 624, 628, 629, 672, 688, 692, 693, 800, 864, 880, 884, 885, 928, 944, 948, 949, 992, 1008, 1012, 1013], [33, 289, 353, 369, 372, 373, 374, 545, 609, 625, 628, 629, 630, 673, 689, 692, 693, 694, 801, 865, 881, 884, 885, 886, 929, 945, 948, 949, 950, 993, 1009, 1012, 1013, 1014], [34, 290, 354, 370, 373, 374, 375, 546, 610, 626, 629, 630, 631, 674, 690, 693, 694, 695, 802, 866, 882, 885, 886, 887, 930, 946, 949, 950, 951, 994, 1010, 1013, 1014, 1015], [35, 291, 355, 371, 374, 375, 547, 611, 627, 630, 631, 675, 691, 694, 695, 803, 867, 883, 886, 887, 931, 947, 950, 951, 995, 1011, 1014, 1015], [36, 292, 356, 372, 376, 377, 548, 612, 628, 632, 633, 676, 692, 696, 697, 804, 868, 884, 888, 889, 932, 948, 952, 953, 996, 1012, 1016, 1017], [37, 293, 357, 373, 376, 377, 378, 549, 613, 629, 632, 633, 634, 677, 693, 696, 697, 698, 805, 869, 885, 888, 889, 890, 933, 949, 952, 953, 954, 997, 1013, 1016, 1017, 1018], [38, 294, 358, 374, 377, 378, 379, 550, 614, 630, 633, 634, 635, 678, 694, 697, 698, 699, 806, 870, 886, 889, 890, 891, 934, 950, 953, 954, 955, 998, 1014, 1017, 1018, 1019], [39, 295, 359, 375, 378, 379, 551, 615, 631, 634, 635, 679, 695, 698, 699, 807, 871, 887, 890, 891, 935, 951, 954, 955, 999, 1015, 1018, 1019], [40, 296, 360, 376, 380, 381, 552, 616, 632, 636, 637, 680, 696, 700, 701, 808, 872, 888, 892, 893, 936, 952, 956, 957, 1000, 1016, 1020, 1021], [41, 297, 361, 377, 380, 381, 382, 553, 617, 633, 636, 637, 638, 681, 697, 700, 701, 702, 809, 873, 889, 892, 893, 894, 937, 953, 956, 957, 958, 1001, 1017, 1020, 1021, 1022], [42, 298, 362, 378, 381, 382, 383, 554, 618, 634, 637, 638, 639, 682, 698, 701, 702, 703, 810, 874, 890, 893, 894, 895, 938, 954, 957, 958, 959, 1002, 1018, 1021, 1022, 1023], [43, 299, 363, 379, 382, 383, 555, 619, 635, 638, 639, 683, 699, 702, 703, 811, 875, 891, 894, 895, 939, 955, 958, 959, 1003, 1019, 1022, 1023], [44, 300, 364, 380, 556, 620, 636, 684, 700, 812, 876, 892, 940, 956, 1004, 1020], [45, 301, 365, 381, 557, 621, 637, 685, 701, 813, 877, 893, 941, 957, 1005, 1021], [46, 302, 366, 382, 558, 622, 638, 686, 702, 814, 878, 894, 942, 958, 1006, 1022], [47, 303, 367, 383, 559, 623, 639, 687, 703, 815, 879, 895, 943, 959, 1007, 1023], [48, 304, 368, 560, 624, 688, 816, 880, 944, 1008], [49, 305, 369, 561, 625, 689, 817, 881, 945, 1009], [50, 306, 370, 562, 626, 690, 818, 882, 946, 1010], [51, 307, 371, 563, 627, 691, 819, 883, 947, 1011], [52, 308, 372, 564, 628, 692, 820, 884, 948, 1012], [53, 309, 373, 565, 629, 693, 821, 885, 949, 1013], [54, 310, 374, 566, 630, 694, 822, 886, 950, 1014], [55, 311, 375, 567, 631, 695, 823, 887, 951, 1015], [56, 312, 376, 568, 632, 696, 824, 888, 952, 1016], [57, 313, 377, 569, 633, 697, 825, 889, 953, 1017], [58, 314, 378, 570, 634, 698, 826, 890, 954, 1018], [59, 315, 379, 571, 635, 699, 827, 891, 955, 1019], [60, 316, 380, 572, 636, 700, 828, 892, 956, 1020], [61, 317, 381, 573, 637, 701, 829, 893, 957, 1021], [62, 318, 382, 574, 638, 702, 830, 894, 958, 1022], [63, 319, 383, 575, 639, 703, 831, 895, 959, 1023], [64, 320, 384, 400, 404, 405, 576, 640, 656, 660, 661, 704, 720, 724, 725, 736, 740, 741, 744, 745, 746, 832, 896, 912, 916, 917, 960, 976, 980, 981, 992, 996, 997, 1000, 1001, 1002], [65, 321, 385, 401, 404, 405, 406, 577, 641, 657, 660, 661, 662, 705, 721, 724, 725, 726, 737, 740, 741, 742, 744, 745, 746, 747, 833, 897, 913, 916, 917, 918, 961, 977, 980, 981, 982, 993, 996, 997, 998, 1000, 1001, 1002, 1003], [66, 322, 386, 402, 405, 406, 407, 578, 642, 658, 661, 662, 663, 706, 722, 725, 726, 727, 738, 741, 742, 743, 744, 745, 746, 747, 834, 898, 914, 917, 918, 919, 962, 978, 981, 982, 983, 994, 997, 998, 999, 1000, 1001, 1002, 1003], [67, 323, 387, 403, 406, 407, 579, 643, 659, 662, 663, 707, 723, 726, 727, 739, 742, 743, 745, 746, 747, 835, 899, 915, 918, 919, 963, 979, 982, 983, 995, 998, 999, 1001, 1002, 1003], [68, 324, 388, 404, 408, 409, 580, 644, 660, 664, 665, 708, 724, 728, 729, 740, 744, 745, 748, 749, 750, 836, 900, 916, 920, 921, 964, 980, 984, 985, 996, 1000, 1001, 1004, 1005, 1006], [69, 325, 389, 405, 408, 409, 410, 581, 645, 661, 664, 665, 666, 709, 725, 728, 729, 730, 741, 744, 745, 746, 748, 749, 750, 751, 837, 901, 917, 920, 921, 922, 965, 981, 984, 985, 986, 997, 1000, 1001, 1002, 1004, 1005, 1006, 1007], [70, 326, 390, 406, 409, 410, 411, 582, 646, 662, 665, 666, 667, 710, 726, 729, 730, 731, 742, 745, 746, 747, 748, 749, 750, 751, 838, 902, 918, 921, 922, 923, 966, 982, 985, 986, 987, 998, 1001, 1002, 1003, 1004, 1005, 1006, 1007], [71, 327, 391, 407, 410, 411, 583, 647, 663, 666, 667, 711, 727, 730, 731, 743, 746, 747, 749, 750, 751, 839, 903, 919, 922, 923, 967, 983, 986, 987, 999, 1002, 1003, 1005, 1006, 1007], [72, 328, 392, 408, 412, 413, 584, 648, 664, 668, 669, 712, 728, 732, 733, 744, 748, 749, 840, 904, 920, 924, 925, 968, 984, 988, 989, 1000, 1004, 1005], [73, 329, 393, 409, 412, 413, 414, 585, 649, 665, 668, 669, 670, 713, 729, 732, 733, 734, 745, 748, 749, 750, 841, 905, 921, 924, 925, 926, 969, 985, 988, 989, 990, 1001, 1004, 1005, 1006], [74, 330, 394, 410, 413, 414, 415, 586, 650, 666, 669, 670, 671, 714, 730, 733, 734, 735, 746, 749, 750, 751, 842, 906, 922, 925, 926, 927, 970, 986, 989, 990, 991, 1002, 1005, 1006, 1007], [75, 331, 395, 411, 414, 415, 587, 651, 667, 670, 671, 715, 731, 734, 735, 747, 750, 751, 843, 907, 923, 926, 927, 971, 987, 990, 991, 1003, 1006, 1007], [76, 332, 396, 412, 588, 652, 668, 716, 732, 748, 844, 908, 924, 972, 988, 1004], [77, 333, 397, 413, 589, 653, 669, 717, 733, 749, 845, 909, 925, 973, 989, 1005], [78, 334, 398, 414, 590, 654, 670, 718, 734, 750, 846, 910, 926, 974, 990, 1006], [79, 335, 399, 415, 591, 655, 671, 719, 735, 751, 847, 911, 927, 975, 991, 1007], [80, 336, 400, 416, 420, 421, 592, 656, 672, 676, 677, 720, 736, 740, 741, 752, 756, 757, 760, 761, 762, 848, 912, 928, 932, 933, 976, 992, 996, 997, 1008, 1012, 1013, 1016, 1017, 1018], [81, 337, 401, 417, 420, 421, 422, 593, 657, 673, 676, 677, 678, 721, 737, 740, 741, 742, 753, 756, 757, 758, 760, 761, 762, 763, 849, 913, 929, 932, 933, 934, 977, 993, 996, 997, 998, 1009, 1012, 1013, 1014, 1016, 1017, 1018, 1019], [82, 338, 402, 418, 421, 422, 423, 594, 658, 674, 677, 678, 679, 722, 738, 741, 742, 743, 754, 757, 758, 759, 760, 761, 762, 763, 850, 914, 930, 933, 934, 935, 978, 994, 997, 998, 999, 1010, 1013, 1014, 1015, 1016, 1017, 1018, 1019], [83, 339, 403, 419, 422, 423, 595, 659, 675, 678, 679, 723, 739, 742, 743, 755, 758, 759, 761, 762, 763, 851, 915, 931, 934, 935, 979, 995, 998, 999, 1011, 1014, 1015, 1017, 1018, 1019], [84, 340, 404, 420, 424, 425, 596, 660, 676, 680, 681, 724, 740, 744, 745, 756, 760, 761, 764, 765, 766, 852, 916, 932, 936, 937, 980, 996, 1000, 1001, 1012, 1016, 1017, 1020, 1021, 1022], [85, 341, 405, 421, 424, 425, 426, 597, 661, 677, 680, 681, 682, 725, 741, 744, 745, 746, 757, 760, 761, 762, 764, 765, 766, 767, 853, 917, 933, 936, 937, 938, 981, 997, 1000, 1001, 1002, 1013, 1016, 1017, 1018, 1020, 1021, 1022, 1023], [86, 342, 406, 422, 425, 426, 427, 598, 662, 678, 681, 682, 683, 726, 742, 745, 746, 747, 758, 761, 762, 763, 764, 765, 766, 767, 854, 918, 934, 937, 938, 939, 982, 998, 1001, 1002, 1003, 1014, 1017, 1018, 1019, 1020, 1021, 1022, 1023], [87, 343, 407, 423, 426, 427, 599, 663, 679, 682, 683, 727, 743, 746, 747, 759, 762, 763, 765, 766, 767, 855, 919, 935, 938, 939, 983, 999, 1002, 1003, 1015, 1018, 1019, 1021, 1022, 1023], [88, 344, 408, 424, 428, 429, 600, 664, 680, 684, 685, 728, 744, 748, 749, 760, 764, 765, 856, 920, 936, 940, 941, 984, 1000, 1004, 1005, 1016, 1020, 1021], [89, 345, 409, 425, 428, 429, 430, 601, 665, 681, 684, 685, 686, 729, 745, 748, 749, 750, 761, 764, 765, 766, 857, 921, 937, 940, 941, 942, 985, 1001, 1004, 1005, 1006, 1017, 1020, 1021, 1022], [90, 346, 410, 426, 429, 430, 431, 602, 666, 682, 685, 686, 687, 730, 746, 749, 750, 751, 762, 765, 766, 767, 858, 922, 938, 941, 942, 943, 986, 1002, 1005, 1006, 1007, 1018, 1021, 1022, 1023], [91, 347, 411, 427, 430, 431, 603, 667, 683, 686, 687, 731, 747, 750, 751, 763, 766, 767, 859, 923, 939, 942, 943, 987, 1003, 1006, 1007, 1019, 1022, 1023], [92, 348, 412, 428, 604, 668, 684, 732, 748, 764, 860, 924, 940, 988, 1004, 1020], [93, 349, 413, 429, 605, 669, 685, 733, 749, 765, 861, 925, 941, 989, 1005, 1021], [94, 350, 414, 430, 606, 670, 686, 734, 750, 766, 862, 926, 942, 990, 1006, 1022], [95, 351, 415, 431, 607, 671, 687, 735, 751, 767, 863, 927, 943, 991, 1007, 1023], [96, 352, 416, 432, 436, 437, 608, 672, 688, 692, 693, 736, 752, 756, 757, 864, 928, 944, 948, 949, 992, 1008, 1012, 1013], [97, 353, 417, 433, 436, 437, 438, 609, 673, 689, 692, 693, 694, 737, 753, 756, 757, 758, 865, 929, 945, 948, 949, 950, 993, 1009, 1012, 1013, 1014], [98, 354, 418, 434, 437, 438, 439, 610, 674, 690, 693, 694, 695, 738, 754, 757, 758, 759, 866, 930, 946, 949, 950, 951, 994, 1010, 1013, 1014, 1015], [99, 355, 419, 435, 438, 439, 611, 675, 691, 694, 695, 739, 755, 758, 759, 867, 931, 947, 950, 951, 995, 1011, 1014, 1015], [100, 356, 420, 436, 440, 441, 612, 676, 692, 696, 697, 740, 756, 760, 761, 868, 932, 948, 952, 953, 996, 1012, 1016, 1017], [101, 357, 421, 437, 440, 441, 442, 613, 677, 693, 696, 697, 698, 741, 757, 760, 761, 762, 869, 933, 949, 952, 953, 954, 997, 1013, 1016, 1017, 1018], [102, 358, 422, 438, 441, 442, 443, 614, 678, 694, 697, 698, 699, 742, 758, 761, 762, 763, 870, 934, 950, 953, 954, 955, 998, 1014, 1017, 1018, 1019], [103, 359, 423, 439, 442, 443, 615, 679, 695, 698, 699, 743, 759, 762, 763, 871, 935, 951, 954, 955, 999, 1015, 1018, 1019], [104, 360, 424, 440, 444, 445, 616, 680, 696, 700, 701, 744, 760, 764, 765, 872, 936, 952, 956, 957, 1000, 1016, 1020, 1021], [105, 361, 425, 441, 444, 445, 446, 617, 681, 697, 700, 701, 702, 745, 761, 764, 765, 766, 873, 937, 953, 956, 957, 958, 1001, 1017, 1020, 1021, 1022], [106, 362, 426, 442, 445, 446, 447, 618, 682, 698, 701, 702, 703, 746, 762, 765, 766, 767, 874, 938, 954, 957, 958, 959, 1002, 1018, 1021, 1022, 1023], [107, 363, 427, 443, 446, 447, 619, 683, 699, 702, 703, 747, 763, 766, 767, 875, 939, 955, 958, 959, 1003, 1019, 1022, 1023], [108, 364, 428, 444, 620, 684, 700, 748, 764, 876, 940, 956, 1004, 1020], [109, 365, 429, 445, 621, 685, 701, 749, 765, 877, 941, 957, 1005, 1021], [110, 366, 430, 446, 622, 686, 702, 750, 766, 878, 942, 958, 1006, 1022], [111, 367, 431, 447, 623, 687, 703, 751, 767, 879, 943, 959, 1007, 1023], [112, 368, 432, 624, 688, 752, 880, 944, 1008], [113, 369, 433, 625, 689, 753, 881, 945, 1009], [114, 370, 434, 626, 690, 754, 882, 946, 1010], [115, 371, 435, 627, 691, 755, 883, 947, 1011], [116, 372, 436, 628, 692, 756, 884, 948, 1012], [117, 373, 437, 629, 693, 757, 885, 949, 1013], [118, 374, 438, 630, 694, 758, 886, 950, 1014], [119, 375, 439, 631, 695, 759, 887, 951, 1015], [120, 376, 440, 632, 696, 760, 888, 952, 1016], [121, 377, 441, 633, 697, 761, 889, 953, 1017], [122, 378, 442, 634, 698, 762, 890, 954, 1018], [123, 379, 443, 635, 699, 763, 891, 955, 1019], [124, 380, 444, 636, 700, 764, 892, 956, 1020], [125, 381, 445, 637, 701, 765, 893, 957, 1021], [126, 382, 446, 638, 702, 766, 894, 958, 1022], [127, 383, 447, 639, 703, 767, 895, 959, 1023], [128, 384, 448, 464, 468, 469, 640, 704, 720, 724, 725, 896, 960, 976, 980, 981], [129, 385, 449, 465, 468, 469, 470, 641, 705, 721, 724, 725, 726, 897, 961, 977, 980, 981, 982], [130, 386, 450, 466, 469, 470, 471, 642, 706, 722, 725, 726, 727, 898, 962, 978, 981, 982, 983], [131, 387, 451, 467, 470, 471, 643, 707, 723, 726, 727, 899, 963, 979, 982, 983], [132, 388, 452, 468, 472, 473, 644, 708, 724, 728, 729, 900, 964, 980, 984, 985], [133, 389, 453, 469, 472, 473, 474, 645, 709, 725, 728, 729, 730, 901, 965, 981, 984, 985, 986], [134, 390, 454, 470, 473, 474, 475, 646, 710, 726, 729, 730, 731, 902, 966, 982, 985, 986, 987], [135, 391, 455, 471, 474, 475, 647, 711, 727, 730, 731, 903, 967, 983, 986, 987], [136, 392, 456, 472, 476, 477, 648, 712, 728, 732, 733, 904, 968, 984, 988, 989], [137, 393, 457, 473, 476, 477, 478, 649, 713, 729, 732, 733, 734, 905, 969, 985, 988, 989, 990], [138, 394, 458, 474, 477, 478, 479, 650, 714, 730, 733, 734, 735, 906, 970, 986, 989, 990, 991], [139, 395, 459, 475, 478, 479, 651, 715, 731, 734, 735, 907, 971, 987, 990, 991], [140, 396, 460, 476, 652, 716, 732, 908, 972, 988], [141, 397, 461, 477, 653, 717, 733, 909, 973, 989], [142, 398, 462, 478, 654, 718, 734, 910, 974, 990], [143, 399, 463, 479, 655, 719, 735, 911, 975, 991], [144, 400, 464, 480, 484, 485, 656, 720, 736, 740, 741, 912, 976, 992, 996, 997], [145, 401, 465, 481, 484, 485, 486, 657, 721, 737, 740, 741, 742, 913, 977, 993, 996, 997, 998], [146, 402, 466, 482, 485, 486, 487, 658, 722, 738, 741, 742, 743, 914, 978, 994, 997, 998, 999], [147, 403, 467, 483, 486, 487, 659, 723, 739, 742, 743, 915, 979, 995, 998, 999], [148, 404, 468, 484, 488, 489, 660, 724, 740, 744, 745, 916, 980, 996, 1000, 1001], [149, 405, 469, 485, 488, 489, 490, 661, 725, 741, 744, 745, 746, 917, 981, 997, 1000, 1001, 1002], [150, 406, 470, 486, 489, 490, 491, 662, 726, 742, 745, 746, 747, 918, 982, 998, 1001, 1002, 1003], [151, 407, 471, 487, 490, 491, 663, 727, 743, 746, 747, 919, 983, 999, 1002, 1003], [152, 408, 472, 488, 492, 493, 664, 728, 744, 748, 749, 920, 984, 1000, 1004, 1005], [153, 409, 473, 489, 492, 493, 494, 665, 729, 745, 748, 749, 750, 921, 985, 1001, 1004, 1005, 1006], [154, 410, 474, 490, 493, 494, 495, 666, 730, 746, 749, 750, 751, 922, 986, 1002, 1005, 1006, 1007], [155, 411, 475, 491, 494, 495, 667, 731, 747, 750, 751, 923, 987, 1003, 1006, 1007], [156, 412, 476, 492, 668, 732, 748, 924, 988, 1004], [157, 413, 477, 493, 669, 733, 749, 925, 989, 1005], [158, 414, 478, 494, 670, 734, 750, 926, 990, 1006], [159, 415, 479, 495, 671, 735, 751, 927, 991, 1007], [160, 416, 480, 496, 500, 501, 672, 736, 752, 756, 757, 928, 992, 1008, 1012, 1013], [161, 417, 481, 497, 500, 501, 502, 673, 737, 753, 756, 757, 758, 929, 993, 1009, 1012, 1013, 1014], [162, 418, 482, 498, 501, 502, 503, 674, 738, 754, 757, 758, 759, 930, 994, 1010, 1013, 1014, 1015], [163, 419, 483, 499, 502, 503, 675, 739, 755, 758, 759, 931, 995, 1011, 1014, 1015], [164, 420, 484, 500, 504, 505, 676, 740, 756, 760, 761, 932, 996, 1012, 1016, 1017], [165, 421, 485, 501, 504, 505, 506, 677, 741, 757, 760, 761, 762, 933, 997, 1013, 1016, 1017, 1018], [166, 422, 486, 502, 505, 506, 507, 678, 742, 758, 761, 762, 763, 934, 998, 1014, 1017, 1018, 1019], [167, 423, 487, 503, 506, 507, 679, 743, 759, 762, 763, 935, 999, 1015, 1018, 1019], [168, 424, 488, 504, 508, 509, 680, 744, 760, 764, 765, 936, 1000, 1016, 1020, 1021], [169, 425, 489, 505, 508, 509, 510, 681, 745, 761, 764, 765, 766, 937, 1001, 1017, 1020, 1021, 1022], [170, 426, 490, 506, 509, 510, 511, 682, 746, 762, 765, 766, 767, 938, 1002, 1018, 1021, 1022, 1023], [171, 427, 491, 507, 510, 511, 683, 747, 763, 766, 767, 939, 1003, 1019, 1022, 1023], [172, 428, 492, 508, 684, 748, 764, 940, 1004, 1020], [173, 429, 493, 509, 685, 749, 765, 941, 1005, 1021], [174, 430, 494, 510, 686, 750, 766, 942, 1006, 1022], [175, 431, 495, 511, 687, 751, 767, 943, 1007, 1023], [176, 432, 496, 688, 752, 944, 1008], [177, 433, 497, 689, 753, 945, 1009], [178, 434, 498, 690, 754, 946, 1010], [179, 435, 499, 691, 755, 947, 1011], [180, 436, 500, 692, 756, 948, 1012], [181, 437, 501, 693, 757, 949, 1013], [182, 438, 502, 694, 758, 950, 1014], [183, 439, 503, 695, 759, 951, 1015], [184, 440, 504, 696, 760, 952, 1016], [185, 441, 505, 697, 761, 953, 1017], [186, 442, 506, 698, 762, 954, 1018], [187, 443, 507, 699, 763, 955, 1019], [188, 444, 508, 700, 764, 956, 1020], [189, 445, 509, 701, 765, 957, 1021], [190, 446, 510, 702, 766, 958, 1022], [191, 447, 511, 703, 767, 959, 1023], [192, 448, 704, 960], [193, 449, 705, 961], [194, 450, 706, 962], [195, 451, 707, 963], [196, 452, 708, 964], [197, 453, 709, 965], [198, 454, 710, 966], [199, 455, 711, 967], [200, 456, 712, 968], [201, 457, 713, 969], [202, 458, 714, 970], [203, 459, 715, 971], [204, 460, 716, 972], [205, 461, 717, 973], [206, 462, 718, 974], [207, 463, 719, 975], [208, 464, 720, 976], [209, 465, 721, 977], [210, 466, 722, 978], [211, 467, 723, 979], [212, 468, 724, 980], [213, 469, 725, 981], [214, 470, 726, 982], [215, 471, 727, 983], [216, 472, 728, 984], [217, 473, 729, 985], [218, 474, 730, 986], [219, 475, 731, 987], [220, 476, 732, 988], [221, 477, 733, 989], [222, 478, 734, 990], [223, 479, 735, 991], [224, 480, 736, 992], [225, 481, 737, 993], [226, 482, 738, 994], [227, 483, 739, 995], [228, 484, 740, 996], [229, 485, 741, 997], [230, 486, 742, 998], [231, 487, 743, 999], [232, 488, 744, 1000], [233, 489, 745, 1001], [234, 490, 746, 1002], [235, 491, 747, 1003], [236, 492, 748, 1004], [237, 493, 749, 1005], [238, 494, 750, 1006], [239, 495, 751, 1007], [240, 496, 752, 1008], [241, 497, 753, 1009], [242, 498, 754, 1010], [243, 499, 755, 1011], [244, 500, 756, 1012], [245, 501, 757, 1013], [246, 502, 758, 1014], [247, 503, 759, 1015], [248, 504, 760, 1016], [249, 505, 761, 1017], [250, 506, 762, 1018], [251, 507, 763, 1019], [252, 508, 764, 1020], [253, 509, 765, 1021], [254, 510, 766, 1022], [255, 511, 767, 1023], [256, 512, 576, 592, 596, 597, 768, 832, 848, 852, 853, 896, 912, 916, 917, 928, 932, 933, 936, 937, 938], [257, 513, 577, 593, 596, 597, 598, 769, 833, 849, 852, 853, 854, 897, 913, 916, 917, 918, 929, 932, 933, 934, 936, 937, 938, 939], [258, 514, 578, 594, 597, 598, 599, 770, 834, 850, 853, 854, 855, 898, 914, 917, 918, 919, 930, 933, 934, 935, 936, 937, 938, 939], [259, 515, 579, 595, 598, 599, 771, 835, 851, 854, 855, 899, 915, 918, 919, 931, 934, 935, 937, 938, 939], [260, 516, 580, 596, 600, 601, 772, 836, 852, 856, 857, 900, 916, 920, 921, 932, 936, 937, 940, 941, 942], [261, 517, 581, 597, 600, 601, 602, 773, 837, 853, 856, 857, 858, 901, 917, 920, 921, 922, 933, 936, 937, 938, 940, 941, 942, 943], [262, 518, 582, 598, 601, 602, 603, 774, 838, 854, 857, 858, 859, 902, 918, 921, 922, 923, 934, 937, 938, 939, 940, 941, 942, 943], [263, 519, 583, 599, 602, 603, 775, 839, 855, 858, 859, 903, 919, 922, 923, 935, 938, 939, 941, 942, 943], [264, 520, 584, 600, 604, 605, 776, 840, 856, 860, 861, 904, 920, 924, 925, 936, 940, 941], [265, 521, 585, 601, 604, 605, 606, 777, 841, 857, 860, 861, 862, 905, 921, 924, 925, 926, 937, 940, 941, 942], [266, 522, 586, 602, 605, 606, 607, 778, 842, 858, 861, 862, 863, 906, 922, 925, 926, 927, 938, 941, 942, 943], [267, 523, 587, 603, 606, 607, 779, 843, 859, 862, 863, 907, 923, 926, 927, 939, 942, 943], [268, 524, 588, 604, 780, 844, 860, 908, 924, 940], [269, 525, 589, 605, 781, 845, 861, 909, 925, 941], [270, 526, 590, 606, 782, 846, 862, 910, 926, 942], [271, 527, 591, 607, 783, 847, 863, 911, 927, 943], [272, 528, 592, 608, 612, 613, 784, 848, 864, 868, 869, 912, 928, 932, 933, 944, 948, 949, 952, 953, 954], [273, 529, 593, 609, 612, 613, 614, 785, 849, 865, 868, 869, 870, 913, 929, 932, 933, 934, 945, 948, 949, 950, 952, 953, 954, 955], [274, 530, 594, 610, 613, 614, 615, 786, 850, 866, 869, 870, 871, 914, 930, 933, 934, 935, 946, 949, 950, 951, 952, 953, 954, 955], [275, 531, 595, 611, 614, 615, 787, 851, 867, 870, 871, 915, 931, 934, 935, 947, 950, 951, 953, 954, 955], [276, 532, 596, 612, 616, 617, 788, 852, 868, 872, 873, 916, 932, 936, 937, 948, 952, 953, 956, 957, 958], [277, 533, 597, 613, 616, 617, 618, 789, 853, 869, 872, 873, 874, 917, 933, 936, 937, 938, 949, 952, 953, 954, 956, 957, 958, 959], [278, 534, 598, 614, 617, 618, 619, 790, 854, 870, 873, 874, 875, 918, 934, 937, 938, 939, 950, 953, 954, 955, 956, 957, 958, 959], [279, 535, 599, 615, 618, 619, 791, 855, 871, 874, 875, 919, 935, 938, 939, 951, 954, 955, 957, 958, 959], [280, 536, 600, 616, 620, 621, 792, 856, 872, 876, 877, 920, 936, 940, 941, 952, 956, 957], [281, 537, 601, 617, 620, 621, 622, 793, 857, 873, 876, 877, 878, 921, 937, 940, 941, 942, 953, 956, 957, 958], [282, 538, 602, 618, 621, 622, 623, 794, 858, 874, 877, 878, 879, 922, 938, 941, 942, 943, 954, 957, 958, 959], [283, 539, 603, 619, 622, 623, 795, 859, 875, 878, 879, 923, 939, 942, 943, 955, 958, 959], [284, 540, 604, 620, 796, 860, 876, 924, 940, 956], [285, 541, 605, 621, 797, 861, 877, 925, 941, 957], [286, 542, 606, 622, 798, 862, 878, 926, 942, 958], [287, 543, 607, 623, 799, 863, 879, 927, 943, 959], [288, 544, 608, 624, 628, 629, 800, 864, 880, 884, 885, 928, 944, 948, 949], [289, 545, 609, 625, 628, 629, 630, 801, 865, 881, 884, 885, 886, 929, 945, 948, 949, 950], [290, 546, 610, 626, 629, 630, 631, 802, 866, 882, 885, 886, 887, 930, 946, 949, 950, 951], [291, 547, 611, 627, 630, 631, 803, 867, 883, 886, 887, 931, 947, 950, 951], [292, 548, 612, 628, 632, 633, 804, 868, 884, 888, 889, 932, 948, 952, 953], [293, 549, 613, 629, 632, 633, 634, 805, 869, 885, 888, 889, 890, 933, 949, 952, 953, 954], [294, 550, 614, 630, 633, 634, 635, 806, 870, 886, 889, 890, 891, 934, 950, 953, 954, 955], [295, 551, 615, 631, 634, 635, 807, 871, 887, 890, 891, 935, 951, 954, 955], [296, 552, 616, 632, 636, 637, 808, 872, 888, 892, 893, 936, 952, 956, 957], [297, 553, 617, 633, 636, 637, 638, 809, 873, 889, 892, 893, 894, 937, 953, 956, 957, 958], [298, 554, 618, 634, 637, 638, 639, 810, 874, 890, 893, 894, 895, 938, 954, 957, 958, 959], [299, 555, 619, 635, 638, 639, 811, 875, 891, 894, 895, 939, 955, 958, 959], [300, 556, 620, 636, 812, 876, 892, 940, 956], [301, 557, 621, 637, 813, 877, 893, 941, 957], [302, 558, 622, 638, 814, 878, 894, 942, 958], [303, 559, 623, 639, 815, 879, 895, 943, 959], [304, 560, 624, 816, 880, 944], [305, 561, 625, 817, 881, 945], [306, 562, 626, 818, 882, 946], [307, 563, 627, 819, 883, 947], [308, 564, 628, 820, 884, 948], [309, 565, 629, 821, 885, 949], [310, 566, 630, 822, 886, 950], [311, 567, 631, 823, 887, 951], [312, 568, 632, 824, 888, 952], [313, 569, 633, 825, 889, 953], [314, 570, 634, 826, 890, 954], [315, 571, 635, 827, 891, 955], [316, 572, 636, 828, 892, 956], [317, 573, 637, 829, 893, 957], [318, 574, 638, 830, 894, 958], [319, 575, 639, 831, 895, 959], [320, 576, 640, 656, 660, 661, 832, 896, 912, 916, 917, 960, 976, 980, 981, 992, 996, 997, 1000, 1001, 1002], [321, 577, 641, 657, 660, 661, 662, 833, 897, 913, 916, 917, 918, 961, 977, 980, 981, 982, 993, 996, 997, 998, 1000, 1001, 1002, 1003], [322, 578, 642, 658, 661, 662, 663, 834, 898, 914, 917, 918, 919, 962, 978, 981, 982, 983, 994, 997, 998, 999, 1000, 1001, 1002, 1003], [323, 579, 643, 659, 662, 663, 835, 899, 915, 918, 919, 963, 979, 982, 983, 995, 998, 999, 1001, 1002, 1003], [324, 580, 644, 660, 664, 665, 836, 900, 916, 920, 921, 964, 980, 984, 985, 996, 1000, 1001, 1004, 1005, 1006], [325, 581, 645, 661, 664, 665, 666, 837, 901, 917, 920, 921, 922, 965, 981, 984, 985, 986, 997, 1000, 1001, 1002, 1004, 1005, 1006, 1007], [326, 582, 646, 662, 665, 666, 667, 838, 902, 918, 921, 922, 923, 966, 982, 985, 986, 987, 998, 1001, 1002, 1003, 1004, 1005, 1006, 1007], [327, 583, 647, 663, 666, 667, 839, 903, 919, 922, 923, 967, 983, 986, 987, 999, 1002, 1003, 1005, 1006, 1007], [328, 584, 648, 664, 668, 669, 840, 904, 920, 924, 925, 968, 984, 988, 989, 1000, 1004, 1005], [329, 585, 649, 665, 668, 669, 670, 841, 905, 921, 924, 925, 926, 969, 985, 988, 989, 990, 1001, 1004, 1005, 1006], [330, 586, 650, 666, 669, 670, 671, 842, 906, 922, 925, 926, 927, 970, 986, 989, 990, 991, 1002, 1005, 1006, 1007], [331, 587, 651, 667, 670, 671, 843, 907, 923, 926, 927, 971, 987, 990, 991, 1003, 1006, 1007], [332, 588, 652, 668, 844, 908, 924, 972, 988, 1004], [333, 589, 653, 669, 845, 909, 925, 973, 989, 1005], [334, 590, 654, 670, 846, 910, 926, 974, 990, 1006], [335, 591, 655, 671, 847, 911, 927, 975, 991, 1007], [336, 592, 656, 672, 676, 677, 848, 912, 928, 932, 933, 976, 992, 996, 997, 1008, 1012, 1013, 1016, 1017, 1018], [337, 593, 657, 673, 676, 677, 678, 849, 913, 929, 932, 933, 934, 977, 993, 996, 997, 998, 1009, 1012, 1013, 1014, 1016, 1017, 1018, 1019], [338, 594, 658, 674, 677, 678, 679, 850, 914, 930, 933, 934, 935, 978, 994, 997, 998, 999, 1010, 1013, 1014, 1015, 1016, 1017, 1018, 1019], [339, 595, 659, 675, 678, 679, 851, 915, 931, 934, 935, 979, 995, 998, 999, 1011, 1014, 1015, 1017, 1018, 1019], [340, 596, 660, 676, 680, 681, 852, 916, 932, 936, 937, 980, 996, 1000, 1001, 1012, 1016, 1017, 1020, 1021, 1022], [341, 597, 661, 677, 680, 681, 682, 853, 917, 933, 936, 937, 938, 981, 997, 1000, 1001, 1002, 1013, 1016, 1017, 1018, 1020, 1021, 1022, 1023], [342, 598, 662, 678, 681, 682, 683, 854, 918, 934, 937, 938, 939, 982, 998, 1001, 1002, 1003, 1014, 1017, 1018, 1019, 1020, 1021, 1022, 1023], [343, 599, 663, 679, 682, 683, 855, 919, 935, 938, 939, 983, 999, 1002, 1003, 1015, 1018, 1019, 1021, 1022, 1023], [344, 600, 664, 680, 684, 685, 856, 920, 936, 940, 941, 984, 1000, 1004, 1005, 1016, 1020, 1021], [345, 601, 665, 681, 684, 685, 686, 857, 921, 937, 940, 941, 942, 985, 1001, 1004, 1005, 1006, 1017, 1020, 1021, 1022], [346, 602, 666, 682, 685, 686, 687, 858, 922, 938, 941, 942, 943, 986, 1002, 1005, 1006, 1007, 1018, 1021, 1022, 1023], [347, 603, 667, 683, 686, 687, 859, 923, 939, 942, 943, 987, 1003, 1006, 1007, 1019, 1022, 1023], [348, 604, 668, 684, 860, 924, 940, 988, 1004, 1020], [349, 605, 669, 685, 861, 925, 941, 989, 1005, 1021], [350, 606, 670, 686, 862, 926, 942, 990, 1006, 1022], [351, 607, 671, 687, 863, 927, 943, 991, 1007, 1023], [352, 608, 672, 688, 692, 693, 864, 928, 944, 948, 949, 992, 1008, 1012, 1013], [353, 609, 673, 689, 692, 693, 694, 865, 929, 945, 948, 949, 950, 993, 1009, 1012, 1013, 1014], [354, 610, 674, 690, 693, 694, 695, 866, 930, 946, 949, 950, 951, 994, 1010, 1013, 1014, 1015], [355, 611, 675, 691, 694, 695, 867, 931, 947, 950, 951, 995, 1011, 1014, 1015], [356, 612, 676, 692, 696, 697, 868, 932, 948, 952, 953, 996, 1012, 1016, 1017], [357, 613, 677, 693, 696, 697, 698, 869, 933, 949, 952, 953, 954, 997, 1013, 1016, 1017, 1018], [358, 614, 678, 694, 697, 698, 699, 870, 934, 950, 953, 954, 955, 998, 1014, 1017, 1018, 1019], [359, 615, 679, 695, 698, 699, 871, 935, 951, 954, 955, 999, 1015, 1018, 1019], [360, 616, 680, 696, 700, 701, 872, 936, 952, 956, 957, 1000, 1016, 1020, 1021], [361, 617, 681, 697, 700, 701, 702, 873, 937, 953, 956, 957, 958, 1001, 1017, 1020, 1021, 1022], [362, 618, 682, 698, 701, 702, 703, 874, 938, 954, 957, 958, 959, 1002, 1018, 1021, 1022, 1023], [363, 619, 683, 699, 702, 703, 875, 939, 955, 958, 959, 1003, 1019, 1022, 1023], [364, 620, 684, 700, 876, 940, 956, 1004, 1020], [365, 621, 685, 701, 877, 941, 957, 1005, 1021], [366, 622, 686, 702, 878, 942, 958, 1006, 1022], [367, 623, 687, 703, 879, 943, 959, 1007, 1023], [368, 624, 688, 880, 944, 1008], [369, 625, 689, 881, 945, 1009], [370, 626, 690, 882, 946, 1010], [371, 627, 691, 883, 947, 1011], [372, 628, 692, 884, 948, 1012], [373, 629, 693, 885, 949, 1013], [374, 630, 694, 886, 950, 1014], [375, 631, 695, 887, 951, 1015], [376, 632, 696, 888, 952, 1016], [377, 633, 697, 889, 953, 1017], [378, 634, 698, 890, 954, 1018], [379, 635, 699, 891, 955, 1019], [380, 636, 700, 892, 956, 1020], [381, 637, 701, 893, 957, 1021], [382, 638, 702, 894, 958, 1022], [383, 639, 703, 895, 959, 1023], [384, 640, 704, 720, 724, 725, 896, 960, 976, 980, 981], [385, 641, 705, 721, 724, 725, 726, 897, 961, 977, 980, 981, 982], [386, 642, 706, 722, 725, 726, 727, 898, 962, 978, 981, 982, 983], [387, 643, 707, 723, 726, 727, 899, 963, 979, 982, 983], [388, 644, 708, 724, 728, 729, 900, 964, 980, 984, 985], [389, 645, 709, 725, 728, 729, 730, 901, 965, 981, 984, 985, 986], [390, 646, 710, 726, 729, 730, 731, 902, 966, 982, 985, 986, 987], [391, 647, 711, 727, 730, 731, 903, 967, 983, 986, 987], [392, 648, 712, 728, 732, 733, 904, 968, 984, 988, 989], [393, 649, 713, 729, 732, 733, 734, 905, 969, 985, 988, 989, 990], [394, 650, 714, 730, 733, 734, 735, 906, 970, 986, 989, 990, 991], [395, 651, 715, 731, 734, 735, 907, 971, 987, 990, 991], [396, 652, 716, 732, 908, 972, 988], [397, 653, 717, 733, 909, 973, 989], [398, 654, 718, 734, 910, 974, 990], [399, 655, 719, 735, 911, 975, 991], [400, 656, 720, 736, 740, 741, 912, 976, 992, 996, 997], [401, 657, 721, 737, 740, 741, 742, 913, 977, 993, 996, 997, 998], [402, 658, 722, 738, 741, 742, 743, 914, 978, 994, 997, 998, 999], [403, 659, 723, 739, 742, 743, 915, 979, 995, 998, 999], [404, 660, 724, 740, 744, 745, 916, 980, 996, 1000, 1001], [405, 661, 725, 741, 744, 745, 746, 917, 981, 997, 1000, 1001, 1002], [406, 662, 726, 742, 745, 746, 747, 918, 982, 998, 1001, 1002, 1003], [407, 663, 727, 743, 746, 747, 919, 983, 999, 1002, 1003], [408, 664, 728, 744, 748, 749, 920, 984, 1000, 1004, 1005], [409, 665, 729, 745, 748, 749, 750, 921, 985, 1001, 1004, 1005, 1006], [410, 666, 730, 746, 749, 750, 751, 922, 986, 1002, 1005, 1006, 1007], [411, 667, 731, 747, 750, 751, 923, 987, 1003, 1006, 1007], [412, 668, 732, 748, 924, 988, 1004], [413, 669, 733, 749, 925, 989, 1005], [414, 670, 734, 750, 926, 990, 1006], [415, 671, 735, 751, 927, 991, 1007], [416, 672, 736, 752, 756, 757, 928, 992, 1008, 1012, 1013], [417, 673, 737, 753, 756, 757, 758, 929, 993, 1009, 1012, 1013, 1014], [418, 674, 738, 754, 757, 758, 759, 930, 994, 1010, 1013, 1014, 1015], [419, 675, 739, 755, 758, 759, 931, 995, 1011, 1014, 1015], [420, 676, 740, 756, 760, 761, 932, 996, 1012, 1016, 1017], [421, 677, 741, 757, 760, 761, 762, 933, 997, 1013, 1016, 1017, 1018], [422, 678, 742, 758, 761, 762, 763, 934, 998, 1014, 1017, 1018, 1019], [423, 679, 743, 759, 762, 763, 935, 999, 1015, 1018, 1019], [424, 680, 744, 760, 764, 765, 936, 1000, 1016, 1020, 1021], [425, 681, 745, 761, 764, 765, 766, 937, 1001, 1017, 1020, 1021, 1022], [426, 682, 746, 762, 765, 766, 767, 938, 1002, 1018, 1021, 1022, 1023], [427, 683, 747, 763, 766, 767, 939, 1003, 1019, 1022, 1023], [428, 684, 748, 764, 940, 1004, 1020], [429, 685, 749, 765, 941, 1005, 1021], [430, 686, 750, 766, 942, 1006, 1022], [431, 687, 751, 767, 943, 1007, 1023], [432, 688, 752, 944, 1008], [433, 689, 753, 945, 1009], [434, 690, 754, 946, 1010], [435, 691, 755, 947, 1011], [436, 692, 756, 948, 1012], [437, 693, 757, 949, 1013], [438, 694, 758, 950, 1014], [439, 695, 759, 951, 1015], [440, 696, 760, 952, 1016], [441, 697, 761, 953, 1017], [442, 698, 762, 954, 1018], [443, 699, 763, 955, 1019], [444, 700, 764, 956, 1020], [445, 701, 765, 957, 1021], [446, 702, 766, 958, 1022], [447, 703, 767, 959, 1023], [448, 704, 960], [449, 705, 961], [450, 706, 962], [451, 707, 963], [452, 708, 964], [453, 709, 965], [454, 710, 966], [455, 711, 967], [456, 712, 968], [457, 713, 969], [458, 714, 970], [459, 715, 971], [460, 716, 972], [461, 717, 973], [462, 718, 974], [463, 719, 975], [464, 720, 976], [465, 721, 977], [466, 722, 978], [467, 723, 979], [468, 724, 980], [469, 725, 981], [470, 726, 982], [471, 727, 983], [472, 728, 984], [473, 729, 985], [474, 730, 986], [475, 731, 987], [476, 732, 988], [477, 733, 989], [478, 734, 990], [479, 735, 991], [480, 736, 992], [481, 737, 993], [482, 738, 994], [483, 739, 995], [484, 740, 996], [485, 741, 997], [486, 742, 998], [487, 743, 999], [488, 744, 1000], [489, 745, 1001], [490, 746, 1002], [491, 747, 1003], [492, 748, 1004], [493, 749, 1005], [494, 750, 1006], [495, 751, 1007], [496, 752, 1008], [497, 753, 1009], [498, 754, 1010], [499, 755, 1011], [500, 756, 1012], [501, 757, 1013], [502, 758, 1014], [503, 759, 1015], [504, 760, 1016], [505, 761, 1017], [506, 762, 1018], [507, 763, 1019], [508, 764, 1020], [509, 765, 1021], [510, 766, 1022], [511, 767, 1023], [512, 768, 832, 848, 852, 853], [513, 769, 833, 849, 852, 853, 854], [514, 770, 834, 850, 853, 854, 855], [515, 771, 835, 851, 854, 855], [516, 772, 836, 852, 856, 857], [517, 773, 837, 853, 856, 857, 858], [518, 774, 838, 854, 857, 858, 859], [519, 775, 839, 855, 858, 859], [520, 776, 840, 856, 860, 861], [521, 777, 841, 857, 860, 861, 862], [522, 778, 842, 858, 861, 862, 863], [523, 779, 843, 859, 862, 863], [524, 780, 844, 860], [525, 781, 845, 861], [526, 782, 846, 862], [527, 783, 847, 863], [528, 784, 848, 864, 868, 869], [529, 785, 849, 865, 868, 869, 870], [530, 786, 850, 866, 869, 870, 871], [531, 787, 851, 867, 870, 871], [532, 788, 852, 868, 872, 873], [533, 789, 853, 869, 872, 873, 874], [534, 790, 854, 870, 873, 874, 875], [535, 791, 855, 871, 874, 875], [536, 792, 856, 872, 876, 877], [537, 793, 857, 873, 876, 877, 878], [538, 794, 858, 874, 877, 878, 879], [539, 795, 859, 875, 878, 879], [540, 796, 860, 876], [541, 797, 861, 877], [542, 798, 862, 878], [543, 799, 863, 879], [544, 800, 864, 880, 884, 885], [545, 801, 865, 881, 884, 885, 886], [546, 802, 866, 882, 885, 886, 887], [547, 803, 867, 883, 886, 887], [548, 804, 868, 884, 888, 889], [549, 805, 869, 885, 888, 889, 890], [550, 806, 870, 886, 889, 890, 891], [551, 807, 871, 887, 890, 891], [552, 808, 872, 888, 892, 893], [553, 809, 873, 889, 892, 893, 894], [554, 810, 874, 890, 893, 894, 895], [555, 811, 875, 891, 894, 895], [556, 812, 876, 892], [557, 813, 877, 893], [558, 814, 878, 894], [559, 815, 879, 895], [560, 816, 880], [561, 817, 881], [562, 818, 882], [563, 819, 883], [564, 820, 884], [565, 821, 885], [566, 822, 886], [567, 823, 887], [568, 824, 888], [569, 825, 889], [570, 826, 890], [571, 827, 891], [572, 828, 892], [573, 829, 893], [574, 830, 894], [575, 831, 895], [576, 832, 896, 912, 916, 917], [577, 833, 897, 913, 916, 917, 918], [578, 834, 898, 914, 917, 918, 919], [579, 835, 899, 915, 918, 919], [580, 836, 900, 916, 920, 921], [581, 837, 901, 917, 920, 921, 922], [582, 838, 902, 918, 921, 922, 923], [583, 839, 903, 919, 922, 923], [584, 840, 904, 920, 924, 925], [585, 841, 905, 921, 924, 925, 926], [586, 842, 906, 922, 925, 926, 927], [587, 843, 907, 923, 926, 927], [588, 844, 908, 924], [589, 845, 909, 925], [590, 846, 910, 926], [591, 847, 911, 927], [592, 848, 912, 928, 932, 933], [593, 849, 913, 929, 932, 933, 934], [594, 850, 914, 930, 933, 934, 935], [595, 851, 915, 931, 934, 935], [596, 852, 916, 932, 936, 937], [597, 853, 917, 933, 936, 937, 938], [598, 854, 918, 934, 937, 938, 939], [599, 855, 919, 935, 938, 939], [600, 856, 920, 936, 940, 941], [601, 857, 921, 937, 940, 941, 942], [602, 858, 922, 938, 941, 942, 943], [603, 859, 923, 939, 942, 943], [604, 860, 924, 940], [605, 861, 925, 941], [606, 862, 926, 942], [607, 863, 927, 943], [608, 864, 928, 944, 948, 949], [609, 865, 929, 945, 948, 949, 950], [610, 866, 930, 946, 949, 950, 951], [611, 867, 931, 947, 950, 951], [612, 868, 932, 948, 952, 953], [613, 869, 933, 949, 952, 953, 954], [614, 870, 934, 950, 953, 954, 955], [615, 871, 935, 951, 954, 955], [616, 872, 936, 952, 956, 957], [617, 873, 937, 953, 956, 957, 958], [618, 874, 938, 954, 957, 958, 959], [619, 875, 939, 955, 958, 959], [620, 876, 940, 956], [621, 877, 941, 957], [622, 878, 942, 958], [623, 879, 943, 959], [624, 880, 944], [625, 881, 945], [626, 882, 946], [627, 883, 947], [628, 884, 948], [629, 885, 949], [630, 886, 950], [631, 887, 951], [632, 888, 952], [633, 889, 953], [634, 890, 954], [635, 891, 955], [636, 892, 956], [637, 893, 957], [638, 894, 958], [639, 895, 959], [640, 896, 960, 976, 980, 981], [641, 897, 961, 977, 980, 981, 982], [642, 898, 962, 978, 981, 982, 983], [643, 899, 963, 979, 982, 983], [644, 900, 964, 980, 984, 985], [645, 901, 965, 981, 984, 985, 986], [646, 902, 966, 982, 985, 986, 987], [647, 903, 967, 983, 986, 987], [648, 904, 968, 984, 988, 989], [649, 905, 969, 985, 988, 989, 990], [650, 906, 970, 986, 989, 990, 991], [651, 907, 971, 987, 990, 991], [652, 908, 972, 988], [653, 909, 973, 989], [654, 910, 974, 990], [655, 911, 975, 991], [656, 912, 976, 992, 996, 997], [657, 913, 977, 993, 996, 997, 998], [658, 914, 978, 994, 997, 998, 999], [659, 915, 979, 995, 998, 999], [660, 916, 980, 996, 1000, 1001], [661, 917, 981, 997, 1000, 1001, 1002], [662, 918, 982, 998, 1001, 1002, 1003], [663, 919, 983, 999, 1002, 1003], [664, 920, 984, 1000, 1004, 1005], [665, 921, 985, 1001, 1004, 1005, 1006], [666, 922, 986, 1002, 1005, 1006, 1007], [667, 923, 987, 1003, 1006, 1007], [668, 924, 988, 1004], [669, 925, 989, 1005], [670, 926, 990, 1006], [671, 927, 991, 1007], [672, 928, 992, 1008, 1012, 1013], [673, 929, 993, 1009, 1012, 1013, 1014], [674, 930, 994, 1010, 1013, 1014, 1015], [675, 931, 995, 1011, 1014, 1015], [676, 932, 996, 1012, 1016, 1017], [677, 933, 997, 1013, 1016, 1017, 1018], [678, 934, 998, 1014, 1017, 1018, 1019], [679, 935, 999, 1015, 1018, 1019], [680, 936, 1000, 1016, 1020, 1021], [681, 937, 1001, 1017, 1020, 1021, 1022], [682, 938, 1002, 1018, 1021, 1022, 1023], [683, 939, 1003, 1019, 1022, 1023], [684, 940, 1004, 1020], [685, 941, 1005, 1021], [686, 942, 1006, 1022], [687, 943, 1007, 1023], [688, 944, 1008], [689, 945, 1009], [690, 946, 1010], [691, 947, 1011], [692, 948, 1012], [693, 949, 1013], [694, 950, 1014], [695, 951, 1015], [696, 952, 1016], [697, 953, 1017], [698, 954, 1018], [699, 955, 1019], [700, 956, 1020], [701, 957, 1021], [702, 958, 1022], [703, 959, 1023], [704, 960], [705, 961], [706, 962], [707, 963], [708, 964], [709, 965], [710, 966], [711, 967], [712, 968], [713, 969], [714, 970], [715, 971], [716, 972], [717, 973], [718, 974], [719, 975], [720, 976], [721, 977], [722, 978], [723, 979], [724, 980], [725, 981], [726, 982], [727, 983], [728, 984], [729, 985], [730, 986], [731, 987], [732, 988], [733, 989], [734, 990], [735, 991], [736, 992], [737, 993], [738, 994], [739, 995], [740, 996], [741, 997], [742, 998], [743, 999], [744, 1000], [745, 1001], [746, 1002], [747, 1003], [748, 1004], [749, 1005], [750, 1006], [751, 1007], [752, 1008], [753, 1009], [754, 1010], [755, 1011], [756, 1012], [757, 1013], [758, 1014], [759, 1015], [760, 1016], [761, 1017], [762, 1018], [763, 1019], [764, 1020], [765, 1021], [766, 1022], [767, 1023], [768], [769], [770], [771], [772], [773], [774], [775], [776], [777], [778], [779], [780], [781], [782], [783], [784], [785], [786], [787], [788], [789], [790], [791], [792], [793], [794], [795], [796], [797], [798], [799], [800], [801], [802], [803], [804], [805], [806], [807], [808], [809], [810], [811], [812], [813], [814], [815], [816], [817], [818], [819], [820], [821], [822], [823], [824], [825], [826], [827], [828], [829], [830], [831], [832], [833], [834], [835], [836], [837], [838], [839], [840], [841], [842], [843], [844], [845], [846], [847], [848], [849], [850], [851], [852], [853], [854], [855], [856], [857], [858], [859], [860], [861], [862], [863], [864], [865], [866], [867], [868], [869], [870], [871], [872], [873], [874], [875], [876], [877], [878], [879], [880], [881], [882], [883], [884], [885], [886], [887], [888], [889], [890], [891], [892], [893], [894], [895], [896], [897], [898], [899], [900], [901], [902], [903], [904], [905], [906], [907], [908], [909], [910], [911], [912], [913], [914], [915], [916], [917], [918], [919], [920], [921], [922], [923], [924], [925], [926], [927], [928], [929], [930], [931], [932], [933], [934], [935], [936], [937], [938], [939], [940], [941], [942], [943], [944], [945], [946], [947], [948], [949], [950], [951], [952], [953], [954], [955], [956], [957], [958], [959], [960], [961], [962], [963], [964], [965], [966], [967], [968], [969], [970], [971], [972], [973], [974], [975], [976], [977], [978], [979], [980], [981], [982], [983], [984], [985], [986], [987], [988], [989], [990], [991], [992], [993], [994], [995], [996], [997], [998], [999], [1000], [1001], [1002], [1003], [1004], [1005], [1006], [1007], [1008], [1009], [1010], [1011], [1012], [1013], [1014], [1015], [1016], [1017], [1018], [1019], [1020], [1021], [1022], [1023]]

def Tt : ℕ := 57897424992834222222036554968142421744201967607286209412385421652932311289071
theorem T_ok : ∀ a < 4, ∀ b < 4, ∀ c < 4, ∀ d < 4,
    (Tt.testBit (((a * 4 + b) * 4 + c) * 4 + d) = true ↔ loc a b c d) := by decide +kernel
def tabF (j a b : ℕ) : ℕ := ((List.range N).filter (fun t => Tt.testBit (((a * 4 + b) * 4 + dig t j) * 4 + dig t (j + 1)))).foldl (fun m x => m ||| 2 ^ x) 0
theorem tabL_eq : ∀ j < 4, ∀ a < 4, ∀ b < 4, tab j a b = tabF j a b := by decide +kernel

theorem tab_ok : ∀ j < 4, ∀ a < 4, ∀ b < 4, ∀ t < N,
    ((tab j a b).testBit t = true ↔ loc a b (dig t j) (dig t (j + 1))) := by
  intro j hj a ha b hb t ht
  rw [tabL_eq j hj a ha b hb]
  unfold tabF
  rw [testBit_foldl_lor]
  simp only [Nat.zero_testBit, Bool.false_eq_true, false_or, List.mem_filter, List.mem_range, decide_eq_true_eq]
  rw [← T_ok a ha b hb (dig t j) (Nat.mod_lt _ (by norm_num)) (dig t (j + 1)) (Nat.mod_lt _ (by norm_num))]
  simp [ht]

theorem RN_iff (s t : Fin N) :
    RN s t ↔ ∀ j < 4, loc (dig s j) (dig s (j + 1)) (dig t j) (dig t (j + 1)) := by
  constructor
  · intro h j hj
    exact h ⟨j, hj⟩
  · intro h j
    exact h j.1 j.2

theorem hR : ∀ s t : Fin N, RN s t ↔ (mask s).testBit t = true := by
  intro s t
  rw [RN_iff]
  unfold mask
  rw [testBit_foldl_land]
  simp only [List.mem_map, List.mem_range, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
  rw [Nat.testBit_two_pow_sub_one]
  simp only [decide_eq_true_eq, t.2, true_and]
  apply forall_congr'; intro j; apply forall_congr'; intro hj
  exact (tab_ok j hj _ (Nat.mod_lt _ (by norm_num)) _ (Nat.mod_lt _ (by norm_num)) t t.2).symm

theorem hAdj : AdjOK N RN adjLit :=
  adjOK_of_chk _ RN mask adjLit hR (by decide +kernel) (by decide +kernel)

theorem a_eq (n : ℕ) : a n = ∑ s, V RN n s := by
  rw [aeq n]
  rw [Nat.card_congr (chainEquiv e0 (R' := RN) (fun a b => by simp [RN]) n), Nat.card_eq_fintype_card, cardChain]

def Dg : ℕ := 70
theorem hDg : ∀ l ∈ adjLit, l.length ≤ Dg := by
  intro l hl
  revert l
  decide +kernel
theorem hKb : Dg ^ 4 < 2 ^ 128 := by decide +kernel
theorem hlenA : adjLit.length = N := by decide +kernel

theorem a_iter (n : ℕ) : a n = (iterL adjLit N n).sum := by
  rw [a_eq, sum_V_eq _ RN adjLit hAdj]

def cpf : ℕ → ℕ := fun j => [1, 0, 6, 0, 1].getD j 0
def cnf : ℕ → ℕ := fun j => [0, 4, 0, 4, 0].getD j 0

theorem chk : comb N cpf (fun j => unpackN N (iterP adjLit N j)) (List.range (4 + 1)) =
    comb N cnf (fun j => unpackN N (iterP adjLit N j)) (List.range (4 + 1)) := by
  decide +kernel

def cc : ℕ → ℤ := fun j => (cpf j : ℤ) - cnf j

theorem hrec (k : ℕ) : (a (k + 4) : ℤ) = (-1 : ℤ) * a (k + 0) + (4 : ℤ) * a (k + 1) + (-6 : ℤ) * a (k + 2) + (4 : ℤ) * a (k + 3) := by
  have h := rec_total RN 4 cc (h0_of_chkP _ RN adjLit hAdj Dg hDg (by decide +kernel) 4 hKb 4 (by omega) cpf cnf chk) k
  have e0 : cc 0 = 1 := by simp [cc, cpf, cnf]
  have e1 : cc 1 = -4 := by simp [cc, cpf, cnf]
  have e2 : cc 2 = 6 := by simp [cc, cpf, cnf]
  have e3 : cc 3 = -4 := by simp [cc, cpf, cnf]
  have e4 : cc 4 = 1 := by simp [cc, cpf, cnf]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, e0, e1, e2, e3, e4] at h
  simp only [a_eq]
  push_cast
  simp only [Nat.add_zero, zero_mul, zero_add] at h ⊢
  linarith

theorem v1 : a 1 = 8736 := by
  rw [a_iter, ← unpack_iterP adjLit N Dg hlenA hDg (by decide +kernel) 4 hKb 1 (by omega)]
  decide +kernel
theorem v2 : a 2 = 30360 := by
  rw [a_iter, ← unpack_iterP adjLit N Dg hlenA hDg (by decide +kernel) 4 hKb 2 (by omega)]
  decide +kernel
theorem v3 : a 3 = 73122 := by
  rw [a_iter, ← unpack_iterP adjLit N Dg hlenA hDg (by decide +kernel) 4 hKb 3 (by omega)]
  decide +kernel
theorem v4 : a 4 = 144248 := by
  rw [a_iter, ← unpack_iterP adjLit N Dg hlenA hDg (by decide +kernel) 4 hKb 4 (by omega)]
  decide +kernel

theorem closed (n : ℕ) (hn : 1 ≤ n) : (a n : ℚ) = (3613 / 3) * (n : ℚ) ^ 3 + 3343 * (n : ℚ) ^ 2 + (9494 / 3) * (n : ℚ) + 1024 := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    by_cases h : n ≤ 4
    · interval_cases n
      · rw [v1]; norm_num
      · rw [v2]; norm_num
      · rw [v3]; norm_num
      · rw [v4]; norm_num
    · obtain ⟨k, rfl⟩ : ∃ k, n = k + 4 := ⟨n - 4, by omega⟩
      have r : (a (k + 4) : ℚ) = (-1 : ℚ) * a (k + 0) + (4 : ℚ) * a (k + 1) + (-6 : ℚ) * a (k + 2) + (4 : ℚ) * a (k + 3) := by exact_mod_cast hrec k
      have i0 := ih (k + 0) (by omega) (by omega)
      have i1 := ih (k + 1) (by omega) (by omega)
      have i2 := ih (k + 2) (by omega) (by omega)
      have i3 := ih (k + 3) (by omega) (by omega)
      rw [r, i0, i1, i2, i3]
      push_cast
      ring

theorem gf : PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) = G := by
  unfold G
  apply gf_gen _ 4 4 (fun j => [(1 : ℚ), (-4 : ℚ), (6 : ℚ), (-4 : ℚ), (1 : ℚ)].getD j 0) (fun j => [(0 : ℚ), (8736 : ℚ), (-4584 : ℚ), (4098 : ℚ), (-1024 : ℚ)].getD j 0)
  · simp [Finset.sum_range_succ, map_ofNat PowerSeries.C]
    ring
  · simp [Finset.sum_range_succ, map_ofNat PowerSeries.C]
    ring
  · norm_num
  · intro n hn
    simp only [List.getD_eq_getElem?_getD]
    rcases n with _ | _ | _ | _ | _ | k <;> simp_all
  · intro n
    rcases n with _ | _ | _ | _ | _ | k
    · simp [Finset.sum_range_succ]
    · simp [Finset.sum_range_succ, v1, v2, v3, v4] <;> norm_num
    · simp [Finset.sum_range_succ, v1, v2, v3, v4] <;> norm_num
    · simp [Finset.sum_range_succ, v1, v2, v3, v4] <;> norm_num
    · simp [Finset.sum_range_succ, v1, v2, v3, v4] <;> norm_num
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero]
      have c0 := closed (k + 5) (by omega)
      have c1 := closed (k + 4) (by omega)
      have c2 := closed (k + 3) (by omega)
      have c3 := closed (k + 2) (by omega)
      have c4 := closed (k + 1) (by omega)
      simp [c0, c1, c2, c3, c4]
      ring

theorem recS (n : ℕ) (hn : 5 ≤ n) : (a n : ℤ) = 4 * (a (n - 1) : ℤ) - 6 * (a (n - 2) : ℤ) + 4 * (a (n - 3) : ℤ) - (a (n - 4) : ℤ) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 5 := ⟨n - 5, by omega⟩
  have e1 : k + 5 - 1 = k + 4 := by omega
  have e2 : k + 5 - 2 = k + 3 := by omega
  have e3 : k + 5 - 3 = k + 2 := by omega
  have e4 : k + 5 - 4 = k + 1 := by omega
  rw [e1, e2, e3, e4]
  have h : (a (k + 5) : ℚ) = 4 * (a (k + 4) : ℚ) - 6 * (a (k + 3) : ℚ) + 4 * (a (k + 2) : ℚ) - (a (k + 1) : ℚ) := by
    rw [closed (k + 5) (by omega), closed (k + 4) (by omega), closed (k + 3) (by omega), closed (k + 2) (by omega), closed (k + 1) (by omega)]
    push_cast
    ring_nf
  exact_mod_cast h

end OMA.S_oeis_a250881

theorem OMA.solution : type_of% @OMA.S_oeis_a250881.main := ⟨OMA.S_oeis_a250881.recS, OMA.S_oeis_a250881.gf, OMA.S_oeis_a250881.closed⟩
