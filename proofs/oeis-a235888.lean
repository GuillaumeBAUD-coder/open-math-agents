import OMAStatements.S_oeis_a235888
import Mathlib

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace OMA.S_oeis_a235888

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


instance (p q r s : Fin 4) : Decidable (Med4 p q r s) := by unfold Med4; infer_instance

abbrev St := Fin 4 → Fin 4
def N : ℕ := 4 ^ 4
def e0 : St ≃ Fin N := finFunctionFinEquiv
def RN : Fin N → Fin N → Prop := fun i j => BlockOK (e0.symm i) (e0.symm j)
instance : DecidableRel RN := fun i j => by unfold RN BlockOK; infer_instance

def dig (x j : ℕ) : ℕ := x / 4 ^ j % 4
abbrev loc (a b c d : ℕ) : Prop := (List.insertionSort (· ≤ ·) [a, b, c, d]).getD 0 0 + (List.insertionSort (· ≤ ·) [a, b, c, d]).getD 2 0 = (List.insertionSort (· ≤ ·) [a, b, c, d]).getD 1 0 + (List.insertionSort (· ≤ ·) [a, b, c, d]).getD 3 0
instance (a b c d : ℕ) : Decidable (loc a b c d) := by unfold loc; infer_instance
def tabL : List ℕ := [59764513900239876557599581413273342231431406596708508104595296850044428321825, 31803732452455810141516406960500226464619817257671933359429869720644485138, 459387246535472813155236989429447715600064027055261259636209229298198118660, 7251250999159924712265740786994051633933318334749200805950010296306942611464, 31803732452455810141516406960500226464619817257671933359429869720644485138, 59764513900239876557599581413273342231431406596708508104595296850044428321825, 1017719438478585924528525022736007246867834152245501867501755831060623524416, 14700391889135130020967583661742326899202048865768360308358695337542339797120, 459387246535472813155236989429447715600064027055261259636209229298198118660, 1017719438478585924528525022736007246867834152245501867501755831060623524416, 59764513900239876557599581413273342231431406596708508104595296850044428321825, 32567022031314749584912800727552231899770692871856059760056186593939952781312, 7251250999159924712265740786994051633933318334749200805950010296306942611464, 14700391889135130020967583661742326899202048865768360308358695337542339797120, 32567022031314749584912800727552231899770692871856059760056186593939952781312, 59764513900239876557599581413273342231431406596708508104595296850044428321825, 108555187186277865441535196849409010127346836132086376162984639895092723712015, 6172148594371015461799047869797654605997529359940902030714798320, 404399224111330260826781885301373677972643598869805694098287865368320, 26502705972061430075808334746856526392986594727767373468243207350260920320, 6172148594371015461799047869797654605997529359940902030714798320, 108555187186277865441535196849409010127346836132086376162984639895092723712015, 6471966884491181908871398419120945476138465346129391287758800363192320, 424043320821762239576703642161773205753842734328505375494806296716451512320, 404399224111330260826781885301373677972643598869805694098287865368320, 6471966884491181908871398419120945476138465346129391287758800363192320, 108555187186277865441535196849409010127346836132086376162984639895092723712015, 6786349147872225561276735468728164523587367438782972598952971849634750136320, 26502705972061430075808334746856526392986594727767373468243207350260920320, 424043320821762239576703642161773205753842734328505375494806296716451512320, 6786349147872225561276735468728164523587367438782972598952971849634750136320, 108555187186277865441535196849409010127346836132086376162984639895092723712015, 115790322390251417039241497490696967415476901660308427435695600276215410262015, 1208907372870559760056320, 22300404916163702203072254898322400419512320, 411369862228566123857978459849914418579267882499413100535480320, 1208907372870559760056320, 115790322390251417039241497490696967415476901660308427435695600276215410262015, 1461479336585709579798173669311374564197211832320, 26959535291011309493156476345064268510634978667209910163073212088320, 22300404916163702203072254898322400419512320, 1461479336585709579798173669311374564197211832320, 115790322390251417039241497490696967415476901660308427435695600276215410262015, 1766820104831723455949457249104477278338836778200718195928398366580408320, 411369862228566123857978459849914418579267882499413100535480320, 26959535291011309493156476345064268510634978667209910163073212088320, 1766820104831723455949457249104477278338836778200718195928398366580408320, 115790322390251417039241497490696967415476901660308427435695600276215410262015]
def tab (j a b : ℕ) : ℕ := tabL.getD ((j * 4 + a) * 4 + b) 0
/-- bitmask (over the 256 states) of the neighbours of s: AND of the per-column-pair masks -/
def mask (s : ℕ) : ℕ := ((List.range 3).map fun j => tab j (dig s j) (dig s (j + 1))).foldl (· &&& ·) (2 ^ N - 1)
def adjLit : List (List ℕ) := [[0, 85, 170, 255], [1, 84], [2, 168], [3, 252], [4, 81], [5, 80], [6], [7], [8, 162], [9], [10, 160], [11], [12, 243], [13], [14], [15, 240], [16, 69], [17, 68], [18], [19], [20, 65], [21, 64], [22], [23], [24], [25], [26], [27], [28], [29], [30], [31], [32, 138], [33], [34, 136], [35], [36], [37], [38], [39], [40, 130], [41], [42, 128], [43], [44], [45], [46], [47], [48, 207], [49], [50], [51, 204], [52], [53], [54], [55], [56], [57], [58], [59], [60, 195], [61], [62], [63, 192], [21, 64], [20, 65], [66], [67], [17, 68], [16, 69], [70], [71], [72], [73], [74], [75], [76], [77], [78], [79], [5, 80], [4, 81], [82], [83], [1, 84], [0, 85, 170, 255], [86, 169], [87, 253], [88], [89, 166], [90, 165], [91], [92], [93, 247], [94], [95, 245], [96], [97], [98], [99], [100], [101, 154], [102, 153], [103], [104], [105, 150], [106, 149], [107], [108], [109], [110], [111], [112], [113], [114], [115], [116], [117, 223], [118], [119, 221], [120], [121], [122], [123], [124], [125, 215], [126], [127, 213], [42, 128], [129], [40, 130], [131], [132], [133], [134], [135], [34, 136], [137], [32, 138], [139], [140], [141], [142], [143], [144], [145], [146], [147], [148], [106, 149], [105, 150], [151], [152], [102, 153], [101, 154], [155], [156], [157], [158], [159], [10, 160], [161], [8, 162], [163], [164], [90, 165], [89, 166], [167], [2, 168], [86, 169], [0, 85, 170, 255], [171, 254], [172], [173], [174, 251], [175, 250], [176], [177], [178], [179], [180], [181], [182], [183], [184], [185], [186, 239], [187, 238], [188], [189], [190, 235], [191, 234], [63, 192], [193], [194], [60, 195], [196], [197], [198], [199], [200], [201], [202], [203], [51, 204], [205], [206], [48, 207], [208], [209], [210], [211], [212], [127, 213], [214], [125, 215], [216], [217], [218], [219], [220], [119, 221], [222], [117, 223], [224], [225], [226], [227], [228], [229], [230], [231], [232], [233], [191, 234], [190, 235], [236], [237], [187, 238], [186, 239], [15, 240], [241], [242], [12, 243], [244], [95, 245], [246], [93, 247], [248], [249], [175, 250], [174, 251], [3, 252], [87, 253], [171, 254], [0, 85, 170, 255]]

def Tt : ℕ := 59764098895288494110966848158054725425867294195120340983151555958713428902945
theorem T_ok : ∀ a < 4, ∀ b < 4, ∀ c < 4, ∀ d < 4,
    (Tt.testBit (((a * 4 + b) * 4 + c) * 4 + d) = true ↔ loc a b c d) := by decide +kernel
def tabF (j a b : ℕ) : ℕ := ((List.range N).filter (fun t => Tt.testBit (((a * 4 + b) * 4 + dig t j) * 4 + dig t (j + 1)))).foldl (fun m x => m ||| 2 ^ x) 0
theorem tabL_eq : ∀ j < 3, ∀ a < 4, ∀ b < 4, tab j a b = tabF j a b := by decide +kernel

theorem tab_ok : ∀ j < 3, ∀ a < 4, ∀ b < 4, ∀ t < N,
    ((tab j a b).testBit t = true ↔ loc a b (dig t j) (dig t (j + 1))) := by
  intro j hj a ha b hb t ht
  rw [tabL_eq j hj a ha b hb]
  unfold tabF
  rw [testBit_foldl_lor]
  simp only [Nat.zero_testBit, Bool.false_eq_true, false_or, List.mem_filter, List.mem_range, decide_eq_true_eq]
  rw [← T_ok a ha b hb (dig t j) (Nat.mod_lt _ (by norm_num)) (dig t (j + 1)) (Nat.mod_lt _ (by norm_num))]
  simp [ht]


theorem RN_iff (s t : Fin N) :
    RN s t ↔ ∀ j < 3, loc (dig s j) (dig s (j + 1)) (dig t j) (dig t (j + 1)) := by
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
  show Nat.card (Chain BlockOK n) = _
  rw [Nat.card_congr (chainEquiv e0 (R' := RN) (fun a b => by simp [RN]) n), Nat.card_eq_fintype_card, cardChain]

def Dg : ℕ := 4
theorem hDg : ∀ l ∈ adjLit, l.length ≤ Dg := by
  intro l hl
  revert l
  decide +kernel
theorem hKb : Dg ^ 3 < 2 ^ 128 := by decide +kernel
theorem hlenA : adjLit.length = N := by decide +kernel

theorem a_iter (n : ℕ) : a n = (iterL adjLit N n).sum := by
  rw [a_eq, sum_V_eq _ RN adjLit hAdj]

def cpf : ℕ → ℕ := fun j => [0, 14, 0, 1].getD j 0
def cnf : ℕ → ℕ := fun j => [8, 0, 7, 0].getD j 0


theorem chkv : (comb N cpf (fun j => unpackN N (iterP adjLit N j)) (List.range (3 + 1)) =
    comb N cnf (fun j => unpackN N (iterP adjLit N j)) (List.range (3 + 1))) ∧
    ∀ i ∈ List.range (3 + 1), (unpackN N (iterP adjLit N i)).sum = [256, 352, 568, 1096].getD i 0 := by
  decide +kernel

def cc : ℕ → ℤ := fun j => (cpf j : ℤ) - cnf j

theorem hrec (k : ℕ) : (a (k + 3) : ℤ) = (8 : ℤ) * a (k + 0) + (-14 : ℤ) * a (k + 1) + (7 : ℤ) * a (k + 2) := by
  have h := rec_total RN 3 cc (h0_of_chkP _ RN adjLit hAdj Dg hDg (by decide +kernel) 3 hKb 3 (by omega) cpf cnf chkv.1) k
  have e0 : cc 0 = -8 := by simp [cc, cpf, cnf]
  have e1 : cc 1 = 14 := by simp [cc, cpf, cnf]
  have e2 : cc 2 = -7 := by simp [cc, cpf, cnf]
  have e3 : cc 3 = 1 := by simp [cc, cpf, cnf]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, e0, e1, e2, e3] at h
  simp only [a_eq]
  push_cast
  simp only [Nat.add_zero, zero_mul, zero_add] at h ⊢
  linarith

theorem v1 : a 1 = 352 := by
  rw [a_iter, ← unpack_iterP adjLit N Dg hlenA hDg (by decide +kernel) 3 hKb 1 (by omega)]
  exact (chkv.2 1 (by simp)).trans (by decide)
theorem v2 : a 2 = 568 := by
  rw [a_iter, ← unpack_iterP adjLit N Dg hlenA hDg (by decide +kernel) 3 hKb 2 (by omega)]
  exact (chkv.2 2 (by simp)).trans (by decide)
theorem v3 : a 3 = 1096 := by
  rw [a_iter, ← unpack_iterP adjLit N Dg hlenA hDg (by decide +kernel) 3 hKb 3 (by omega)]
  exact (chkv.2 3 (by simp)).trans (by decide)

theorem closed (n : ℕ) (hn : 1 ≤ n) : (a n : ℚ) = 4 * (42 + 21 * (2 : ℚ) ^ n + (4 : ℚ) ^ n) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    by_cases h : n ≤ 3
    · interval_cases n
      · rw [v1]; norm_num
      · rw [v2]; norm_num
      · rw [v3]; norm_num
    · obtain ⟨k, rfl⟩ : ∃ k, n = k + 3 := ⟨n - 3, by omega⟩
      have r : (a (k + 3) : ℚ) = (8 : ℚ) * a (k + 0) + (-14 : ℚ) * a (k + 1) + (7 : ℚ) * a (k + 2) := by exact_mod_cast hrec k
      have i0 := ih (k + 0) (by omega) (by omega)
      have i1 := ih (k + 1) (by omega) (by omega)
      have i2 := ih (k + 2) (by omega) (by omega)
      rw [r, i0, i1, i2]
      push_cast
      ring

theorem gf : PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) = G := by
  unfold G
  apply gf_gen _ 3 3 (fun j => [(1 : ℚ), (-7 : ℚ), (14 : ℚ), (-8 : ℚ)].getD j 0) (fun j => [(0 : ℚ), (352 : ℚ), (-1896 : ℚ), (2048 : ℚ)].getD j 0)
  · simp [Finset.sum_range_succ, map_ofNat PowerSeries.C]
    ring
  · simp [Finset.sum_range_succ, map_ofNat PowerSeries.C]
    ring
  · norm_num
  · intro n hn
    simp only [List.getD_eq_getElem?_getD]
    rcases n with _ | _ | _ | _ | k <;> simp_all
  · intro n
    rcases n with _ | _ | _ | _ | k
    · simp [Finset.sum_range_succ]
    · simp [Finset.sum_range_succ, v1, v2, v3] <;> norm_num
    · simp [Finset.sum_range_succ, v1, v2, v3] <;> norm_num
    · simp [Finset.sum_range_succ, v1, v2, v3] <;> norm_num
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero]
      have c0 := closed (k + 4) (by omega)
      have c1 := closed (k + 3) (by omega)
      have c2 := closed (k + 2) (by omega)
      have c3 := closed (k + 1) (by omega)
      simp [c0, c1, c2, c3]
      ring

theorem recS (n : ℕ) (hn : 4 ≤ n) : (a n : ℤ) = 7 * (a (n - 1) : ℤ) - 14 * (a (n - 2) : ℤ) + 8 * (a (n - 3) : ℤ) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 4 := ⟨n - 4, by omega⟩
  have e1 : k + 4 - 1 = k + 3 := by omega
  have e2 : k + 4 - 2 = k + 2 := by omega
  have e3 : k + 4 - 3 = k + 1 := by omega
  rw [e1, e2, e3]
  have h : (a (k + 4) : ℚ) = 7 * (a (k + 3) : ℚ) - 14 * (a (k + 2) : ℚ) + 8 * (a (k + 1) : ℚ) := by
    rw [closed (k + 4) (by omega), closed (k + 3) (by omega), closed (k + 2) (by omega), closed (k + 1) (by omega)]
    push_cast
    ring_nf
  exact_mod_cast h

end OMA.S_oeis_a235888

theorem OMA.solution : type_of% @OMA.S_oeis_a235888.main := by
  refine ⟨OMA.S_oeis_a235888.recS, OMA.S_oeis_a235888.gf, ?_⟩
  intro n hn
  have h := OMA.S_oeis_a235888.closed n hn
  have h2 : (OMA.S_oeis_a235888.a n : ℚ) = ((4 * (42 + 21 * 2 ^ n + 4 ^ n) : ℕ) : ℚ) := by rw [h]; push_cast; ring
  exact_mod_cast h2
