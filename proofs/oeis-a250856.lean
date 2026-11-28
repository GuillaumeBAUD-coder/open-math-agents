import OMAStatements.S_oeis_a250856
import Mathlib

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace OMA.S_oeis_a250856

def BB : ℕ := 64

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

section fastvec3
/-! Chunked packed vectors: chunk c is one Nat holding the BB digits (128 bits each) of states c*BB .. c*BB+BB-1. -/
def dgC (v : List ℕ) (t : ℕ) : ℕ := dg (v.getD (t / BB) 0) (t % BB)

def stepC (adjC : List (List (List ℕ))) (v : List ℕ) : List ℕ :=
  adjC.map fun ch => pack (ch.map fun l => (l.map fun t => dgC v t).sum)

def iterC (adjC : List (List (List ℕ))) (N : ℕ) : ℕ → List ℕ
  | 0 => List.replicate (N / BB) (pack (List.replicate BB 1))
  | n + 1 => stepC adjC (iterC adjC N n)

def unpackC (N : ℕ) (v : List ℕ) : List ℕ := (List.range N).map (dgC v)

theorem getD_map_zero {α : Type} (f : α → ℕ) (d : α) (hd : f d = 0) (l : List α) (i : ℕ) :
    (l.map f).getD i 0 = f (l.getD i d) := by
  rw [← hd, List.getD_map]

theorem flatten_getD {α : Type} (d : α) : ∀ (cs : List (List α)) (hB : 0 < BB), (∀ c ∈ cs, c.length = BB) →
    ∀ t, cs.flatten.getD t d = (cs.getD (t / BB) []).getD (t % BB) d
  | [], _, _, t => by simp
  | c :: r, hB, h, t => by
    have hc : c.length = BB := h c (by simp)
    have hr : ∀ x ∈ r, x.length = BB := fun x hx => h x (by simp [hx])
    by_cases ht : t < BB
    · rw [List.flatten_cons, List.getD_append _ _ _ _ (by omega), Nat.div_eq_of_lt ht, Nat.mod_eq_of_lt ht]
      simp
    · have e : t = (t - BB) + BB := by omega
      have h1 : t / BB = (t - BB) / BB + 1 := by
        conv_lhs => rw [e]
        rw [Nat.add_div_right _ hB]
      have h2 : t % BB = (t - BB) % BB := by
        conv_lhs => rw [e]
        rw [Nat.add_mod_right]
      rw [List.flatten_cons, List.getD_append_right _ _ _ _ (by omega), h1, h2, hc]
      simp only [List.getD_cons_succ]
      exact flatten_getD d r hB hr (t - BB)

theorem iterC_eq (adjC : List (List (List ℕ))) (N Δ : ℕ) (hB : 0 < BB) (hNB : N = N / BB * BB)
    (hch : ∀ ch ∈ adjC, ch.length = BB) (hΔ : ∀ l ∈ adjC.flatten, l.length ≤ Δ) (h1 : 1 ≤ Δ) (K : ℕ)
    (hK : Δ ^ K < 2 ^ 128) : ∀ n ≤ K, ∀ t, dgC (iterC adjC N n) t = (iterL adjC.flatten N n).getD t 0 := by
  intro n
  induction n with
  | zero =>
    intro _ t
    simp only [iterC, iterL, dgC]
    by_cases ht : t < N
    · have h1' : t / BB < N / BB := by
        rw [Nat.div_lt_iff_lt_mul hB]; omega
      rw [List.getD_eq_getElem?_getD, List.getElem?_replicate, if_pos h1', List.getD_eq_getElem?_getD,
        List.getElem?_replicate, if_pos ht]
      rw [Option.getD_some]
      have hb : ∀ x ∈ List.replicate BB 1, x < 2 ^ 128 := by
        intro x hx; rw [List.eq_of_mem_replicate hx]; norm_num
      rw [dg_pack _ hb, List.getD_eq_getElem?_getD, List.getElem?_replicate, if_pos (Nat.mod_lt _ hB)]
    · have h2 : ¬ t / BB < N / BB := by
        rw [Nat.div_lt_iff_lt_mul hB]; omega
      rw [List.getD_eq_getElem?_getD, List.getElem?_replicate, if_neg h2, List.getD_eq_getElem?_getD,
        List.getElem?_replicate, if_neg ht]
      simp [dg]
  | succ n ih =>
    intro hn t
    have ih' := ih (by omega)
    have hb : ∀ ch ∈ adjC, ∀ x ∈ ch.map (fun l => (l.map fun t => dgC (iterC adjC N n) t).sum), x < 2 ^ 128 := by
      intro ch hch' x hx
      obtain ⟨l, hl, rfl⟩ := List.mem_map.1 hx
      have hl' : l ∈ adjC.flatten := List.mem_flatten.2 ⟨ch, hch', hl⟩
      have hmem : (l.map fun t => dgC (iterC adjC N n) t).sum ∈ iterL adjC.flatten N (n + 1) := by
        simp only [iterL, stepL, List.mem_map]
        exact ⟨l, hl', by simp [ih']⟩
      have := iterL_bound adjC.flatten N Δ hΔ h1 (n + 1) _ hmem
      exact lt_of_le_of_lt (this.trans (Nat.pow_le_pow_right h1 hn)) hK
    show dg ((stepC adjC (iterC adjC N n)).getD (t / BB) 0) (t % BB) = _
    simp only [stepC]
    rw [getD_map_zero _ [] (by simp [pack]) _ _]
    set ch := adjC.getD (t / BB) [] with hch0
    have hchm : ch ∈ adjC ∨ ch = [] := by
      by_cases hh : t / BB < adjC.length
      · left
        rw [hch0, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hh]
        exact List.getElem_mem hh
      · right
        rw [hch0, List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]; rfl
    have hbc : ∀ x ∈ ch.map (fun l => (l.map fun t => dgC (iterC adjC N n) t).sum), x < 2 ^ 128 := by
      rcases hchm with h | h
      · exact hb ch h
      · intro x hx; rw [h] at hx; simp at hx
    rw [dg_pack _ hbc, getD_map_zero _ [] (by simp) _ _, hch0]
    rw [← flatten_getD [] adjC hB hch t]
    simp only [iterL, stepL]
    rw [getD_map_zero _ [] (by simp) _ _]
    congr 2
    funext s
    exact ih' s

theorem unpack_iterC (adjC : List (List (List ℕ))) (N Δ : ℕ) (hB : 0 < BB) (hNB : N = N / BB * BB)
    (hch : ∀ ch ∈ adjC, ch.length = BB) (hlen : adjC.flatten.length = N)
    (hΔ : ∀ l ∈ adjC.flatten, l.length ≤ Δ) (h1 : 1 ≤ Δ) (K : ℕ)
    (hK : Δ ^ K < 2 ^ 128) (n : ℕ) (hn : n ≤ K) :
    unpackC N (iterC adjC N n) = iterL adjC.flatten N n := by
  apply List.ext_getElem
  · simp [unpackC, length_iterL adjC.flatten N hlen n]
  · intro i h1' h2'
    simp only [unpackC, List.getElem_map, List.getElem_range]
    rw [iterC_eq adjC N Δ hB hNB hch hΔ h1 K hK n hn, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h2']
    simp

theorem h0_of_chkC (N : ℕ) (R : Fin N → Fin N → Prop) [DecidableRel R] (adjC : List (List (List ℕ)))
    (H : AdjOK N R adjC.flatten) (hB : 0 < BB) (hNB : N = N / BB * BB)
    (hch : ∀ ch ∈ adjC, ch.length = BB) (Δ : ℕ)
    (hΔ : ∀ l ∈ adjC.flatten, l.length ≤ Δ) (h1 : 1 ≤ Δ) (Kb : ℕ) (hKb : Δ ^ Kb < 2 ^ 128)
    (K : ℕ) (hle : K ≤ Kb) (cp cn : ℕ → ℕ)
    (chk : comb N cp (fun j => unpackC N (iterC adjC N j)) (List.range (K + 1)) =
      comb N cn (fun j => unpackC N (iterC adjC N j)) (List.range (K + 1)))
    (s : Fin N) :
    ∑ j ∈ Finset.range (K + 1), ((cp j : ℤ) - cn j) * (V R j s : ℤ) = 0 := by
  have hf : ∀ j, (unpackC N (iterC adjC N j)).length = N := by intro j; simp [unpackC]
  have h := congrArg (fun l => l.getD s 0) chk
  simp only [comb_getD N _ _ hf _ s s.2] at h
  have e : ∀ c : ℕ → ℕ, ((List.range (K + 1)).map fun j => c j * (unpackC N (iterC adjC N j)).getD s 0).sum =
      ((List.range (K + 1)).map fun j => c j * (iterL adjC.flatten N j).getD s 0).sum := by
    intro c
    congr 1
    apply List.map_congr_left
    intro j hj
    rw [unpack_iterC adjC N Δ hB hNB hch H.len hΔ h1 Kb hKb j (by simp at hj; omega)]
  rw [e, e] at h
  simp only [V_eq_iterL' N R adjC.flatten H, sub_mul, Finset.sum_sub_distrib]
  rw [sub_eq_zero]
  have h' : ∑ j ∈ Finset.range (K + 1), cp j * (iterL adjC.flatten N j).getD s 0 =
      ∑ j ∈ Finset.range (K + 1), cn j * (iterL adjC.flatten N j).getD s 0 := by
    rw [sum_range_eq_list, sum_range_eq_list]; exact h
  exact_mod_cast h'
end fastvec3


def PO (u v : Fin 5 → Fin 4) : Prop :=
  ∀ j : Fin 4, (((v j.castSucc : Fin 4) : ℕ) : ℤ) - ((u j.castSucc : Fin 4) : ℕ) ≤ (((v j.succ : Fin 4) : ℕ) : ℤ) - ((u j.succ : Fin 4) : ℕ) ∧ min ((u j.succ : Fin 4) : ℕ) ((u j.castSucc : Fin 4) : ℕ) ≤ min ((v j.succ : Fin 4) : ℕ) ((v j.castSucc : Fin 4) : ℕ)

theorem aeq (n : ℕ) : a n = Nat.card (Chain PO n) := by
  unfold a Chain
  apply Nat.card_congr
  exact Equiv.subtypeEquiv (Equiv.piComm _) (fun x => forall_comm)

abbrev St := Fin 5 → Fin 4
def N : ℕ := 4 ^ 5
def e0 : St ≃ Fin N := finFunctionFinEquiv
def RN : Fin N → Fin N → Prop := fun i j => PO (e0.symm i) (e0.symm j)
instance : DecidableRel RN := fun i j => by unfold RN PO; infer_instance

def dig (x j : ℕ) : ℕ := x / 4 ^ j % 4
abbrev loc (a b c d : ℕ) : Prop := (c : ℤ) - a ≤ (d : ℤ) - b ∧ min b a ≤ min d c
instance (a b c d : ℕ) : Decidable (loc a b c d) := by unfold loc; infer_instance
def tabL : List ℕ := [173586357316277123608786391666010947078781111168761886364842129636720553256243327199220647797959430639391194421792044603128189141074923297291063985020165744483856413577766274109554905906560678751401702026259117266465964955051703572175947135853118004042633457948139246798231504848293811360132542670251781912369, 80800868208597508778628845197042057760663965654573254606640062113102520767938298161853374654899464118991593414900309189642134911576981094562437078155433734762669277008054287545567378966572136238385748248060058440938377454781103023372176464241864760782538378617916746791117510892864248469905092790805083484944, 34409495206703121609149926471744146270701004385217507665185121508241377665433799977671399092580760385273986549311158286083342623941528070688186132142237940279159540018639088232332876213901442048285946021987553404506077091009443112614767163479425297367468815228922721066939776501904166648780876017377069773056, 11235753536882651954008139256079721231249307554356737196795141716976776380549812237606987458801880942130281322224051685251703713940090798592060777842363409070745972250984192075863796314743328015766839517383690907593821090941858975547679073789200097099581653952301296674919110694499319722050898291388430946304, 179385278941513922004971256506673186015026481327431354732523997212328196144056389472243394743249268606105895279990688466073038177029354925275345353271815218794295130701443174023709218750644515525164177304518180396020002500523161061020623298448422936969517153371763500013753721647163821587773069766930283626355, 161601736417195017557257690394084115521327931309146509213280124226205041535876596323706749309798928237983186829800618379284269823153962189124874156310867469525338554016108575091134757933144272476771496496120116881876754909562206046744352928483729521565076757235833493582235021785728496939810185581610166969888, 68818990413406243218299852943488292541402008770435015330370243016482755330867599955342798185161520770547973098622316572166685247883056141376372264284475880558319080037278176464665752427802884096571892043975106809012154182018886225229534326958850594734937630457845442133879553003808333297561752034754139546112, 22471507073765303908016278512159442462498615108713474393590283433953552761099624475213974917603761884260562644448103370503407427880181597184121555684726818141491944501968384151727592629486656031533679034767381815187642181883717951095358147578400194199163307904602593349838221388998639444101796582776861892608, 179747368655104866843332846931917942656267914090413554271092590646566705539132701780681901175027063597405015674163924506711032534998127382651847311932750758344426592697812781776154048124068861056922288343652615747534256500524217063162296549849832705723702890266710709769879044550404522321003225668898856108023, 167395171834650134971043137198000221781190855516861701830377619174021191857097593258722852218243648098769113136572395029492179550654321507148905494885836102327441945958022299130252027907933800984901273122271082506104818909579102081011124950906285821632048547554988849680240188237579708671492680013107326676576, 137637980826812486436599705886976585082804017540870030660740486032965510661735199910685596370323041541095946197244633144333370495766112282752744528568951761116638160074556352929331504855605768193143784087950213618024308364037772450459068653917701189469875260915690884267759106007616666595123504069508279092224, 44943014147530607816032557024318884924997230217426948787180566867907105522199248950427949835207523768521125288896206741006814855760363194368243111369453636282983889003936768303455185258973312063067358069534763630375284363767435902190716295156800388398326615809205186699676442777997278888203593165553723785216, 179769313486231590772930519078902473361797697894230657273430081157732675805500963132708477322407536021120113879871393357658789768814416622492847430639474124377767893424865485276302219601246094119453082952085005768838150682342462881473913110540827237163350510684586298239947245938479716304835356329624224137215, 167746289132677717844605891549752713069667396377935349867777467352676716118989774891148070576331206878210684427891896644656295291714949344604907394193409958860902757590865555132622771542769529985393986857189322846967125818671035173996989921962198324666410474240998265201331410446782812412806770584713215143648, 143255857595253812413603775515016445698428671318048399259138056891453898852010106029489090099723982012161086858356658986959222352736157682048774917490133465652011146200048448967263403012977432201027203846642059071821218909508701938232908190812301238019666087891841532605218661354866326456148953215202494565376, 89886028295061215632065114048637769849994460434853897574361133735814211044398497900855899670415047537042250577792413482013629711520726388736486222738907272565967778007873536606910370517946624126134716139069527260750568727534871804381432590313600776796653231618410373399352885555994557776407186331107447570432, 179766741823881399488329593543172672349141274954893914540740845398490433166009096418814837196952880925853348598727744535544628114293077077877025326783195375086568557834080752002862477444638673952821248241803031787577830733668948720678807007270157761161255047311637223024284626134303230611325367892477839605775, 11232849704094924507520872391723542329767058145171052900709878168128389932285537898985312932538405945711721216439140027501098956305470922073446881513005566485878351185678558308755290995308210122536000521937018781102064321422483613209032872248408938419494734939257530915181671783228890118227507681476110909440, 699481446608269830356559205445470841882741706136049258136572916008886381358495258941323066312821596009757221451934001402653668608831949411683145172289485592559466993324783458521632082457117958555352064356566880292651190199501950970316176499691798233906853893984411502973336159055756832606820086631125483520, 41145930515952665126650047246620744119875955538919413184513996895789186454794392750087781467299166346766844355172183356557468430893823729409913179373334417419038489699458680347212248807714910903906114451291715532319601692929316737880844172075724535174905576719921939927871372580589293708735614069180989440, 179769313446991137441131635611821666018938121711837038320927020521843001404180709466334379186666314906407475054781208208890843555037143640126210327695387932723505403264791775873675522771521694238994095079805370765092676781796688706436189506463455787806808169352908041656953622309992726005193927630660174807295, 179725595265518792120333958267576677276272930322736846411358050690054238916568606383765006920614495131387539463026240440017583300887534753175150104208089063774053618970856932940084655924931361960576008350992300497633029142759737811344525955974543014711915759028120494642906748531662241891640122903617774551040, 11191703145732317285704947287127533470123867298176788130185166656142182101735924143061169061005145536156115543230944022442458697741311190586930322756631769480951471893196535336346113319313887336885633029705070084682419043192031215525058823995068771742509662303750584047573378544892109321709121386098007736320, 658334888255242642026400755945931905918015288622710610952223950332626983276710284001404503476786661548269509682754933704919494894301179670558610869973350678704615835191338885555395980923438574462497831220667448517113627086869067806093506753211592562798489227518751038845941961289428699339769825106895831040, 179769313486230992020837658662958943991567793867388099390721308498588304028471723833896963240613959428926731507281454799073733138511314812383760429111095520497075891666468699126337035752842303906855738373391502689797893950147599161816428649384148489600483216436521217839729689748444063013382147827508357042175, 179728166888628527734260637600225891534467316517075116449814894670207024452486198965273566433445922953378410519186774665869325864169479823978596484020561392489581511269699219364999399752406554941230896811734117978745374188027341610696996406491447764999801430701234809055262394878484410514838943546088719646720, 179067250331717076571279156594040535521981876770828610082962666498274913627774786288978704976082328578497848691695104359079339163860979049390885164106108311695223550291144565381537813109022197390170128475281121354918704691072499448400941183921100347880154596860009344761174056718273749147345942177568123781120, 10533358212083882272422412095134910494688244617963369775235583205322031732427364544022472055628586584772312154924078939278711918308818874728937773919573610859273853363061422168886335694775017191399965299530679176273818033389905084897496108051385481004775827640300016621535071380630859189436317201710333296640, 179769313486231590772930519078902473361797697894230657273430081157732675805500963132708477322407536021120113879871393357658789768814416622492847430639474124377767893424865485276302219601246094119453082952085005768838150682342462881473913110540827237163350510684586298239947245938479716304835356329624224137215, 179728166927868344891960856875366698921457619670948517651939884355755803840712885876660430857281468938885580573400150096140649408249707133104328647840745317520608749561476343483288088743201927720805206069151905961010575310616073083598642770589848045070797271894343917713024865055058519192311338211554660188160, 179069821952374323612849572221993449318489369018049792546286698623080900451928210938525585462424034776394521619467302620539124005637909913373973283679819145096312240196750781549059513874572679572101622607434327087139474666178307530697058736681855080663603028458554339882419548679060035978202738153447447592960, 168533731393342116358758593522158567915011913887413916403769331285152507718837832704359552890057385356356994478785263028459390692941101995663004382713177773748381653808982754702181371116400275062399444792490866820381088534238481358359937728822167696076413242244800265944561142090093747030981075227365332746240, 179769313486231590763185353769193322059222300781592621861952024945890690199784745504146656508192294171826295033281041335686112766121450966404709974995239462752065088845545980135915311317949652546099865648644971734712785797348792611192411968762755874098209032123875797943673195465861324254831398530343753547775, 2743062034396834596313958994602257636696249594197154953170570978636169831322422515930522978433219718920095327759063630359292795778211993537944149031873847242734265507120343953175512056517025893144262027861691598866346064817090686203019953568498487070963147979265447453069444394237928893109524028131901440, 41855804958468253213147889020335036313001606846958984187092300231508443254579182723815832122761893159445508189955732934136990249691255627211065815197607144405828565483363904099635199827823156778801916506734050088632630974779324617654135582933550511277359746405651899649924071713951368067688609873920, 638659153737098939730958914789400465953273527112488818273288249673450592449383250193185010905102294950681950472938916533706644964298200285766210147251559536549193586962524260308936515274741658942652457657929909736325910264692414377697792033031431753657793197833173899709668362140228395246551040, 179769313486231590772930519078902473361269411424229805498503667171354683619956648026416539440922136597697006409064303481015528973619953676181307369816456905784193937026416207487015067305251743650494373405642221697817305455128883665883145981379982765372175446060877706268333084439968719657492448167995109277695, 179769313486230952104031616670253556478525413405304747010986539655900026065546282004022753914599487499147367400017994079226612664120901208502707750952884452899832824274638861315310358135899808933102356257943820623304855703852855211001115677065116848682640865969140364284359107820776907938825766707652292771840, 2743062033758175442576860054836676939808873306322303987685280987972137337132101318987994373997323430097420824736938913571601793003766128784904409264790381815780380867517736819073692455916218402655562400185322706608628103563137818142581429563133166307073048340440802895457423963845516857684040736697221120, 41855166299314516114208123439638148936713733872844067194358218730599258026762780684660572874676784001887892306194524833952998684380246853927974348210278205787287950915175989923606463465045469360465671465070094564479854855106882068656802498676747911407717135013194884691372825781222008110877968957440, 179769313486231590772930519078902473361797697894230657273401442690809194717510674054871969440625165275626824638637309107685630656577007888623210074922517693170241066978099339967036488610834052312439461235756861063159939801266507551917132171547151598243046189986188013385619058368334118783679361058848978763775, 179769313486230952113776781979962707780572524047941930647538181881357351573031130369037817769462128423099501478794222334155461721416554245116762691371758210259120537227566522640695224649625398329388853823700345079304572320618542490106976102426795766863571733094773881528632459468773732750044157425193446277120, 179769313444375785804717100553776459927314321003138514136942574827741992526289392041197199294288588314864571169960028639828495106294817016047495365577302462678983040533642400174813508790925289236434937458545308900303051395113800049792216567849495187100339296039128458556697736894579792785181293720189083320320, 2743020178591876128060743577740125728716471263090708787649460222728552974041925594949915303914817716347724910178764379517943721779543857819023726884308792494475703151176973675633473189645219880007478245134833717377751767784284623251492208553279351122016150160224739963133809510398165523554498573594787840, 179769313486231590772930519078902473361797697894230657273430081157732675805500963132708477322407536021120113879871393357658789768814416622492847430639474124377767893424865485276302219601246094119453082952085005768838150682342462881473913110540827237163350510684586298239947245938479716304835356329624224137215, 179769313486230952113776781979962707781100810517942782422435956963823536811803906545670160664247527365147583055394186669256807710417428077176373684482034742328529368735242593869720105645591764424778048501628150824275110746790329645865547913001999974556846647181206344433808229414784851090136081973834321756160, 179769313444375785814462265863485611229361423584763887457762788559316834113711392921224216390989382537783043626397746763465609829087464057882618732342106544187866862360601011267177912888864197017027840828826401108290302030763365322868478626331740279533472109043148108118126466109563525385731653249916689448960, 179766570424197193928588891110776879757162660697912691107395025156738447706811635790637649357361493858564499713475502376087959750544186266027538965090061024917959681715534146806315298956589130056170094273156462502068339853510877069409793379747715555132450416900488558223937340073454175751667618519108015882240, 179769313486231590772930519078902473361797697894230657273430081157732675805499410614616176613472471203806076151292252327479799154261926375891666550468539706578078184787908492517480552329283277021502728703543691294647711084363008372613489079954969122972694258182868432066582822554155027898467361283937744715775, 9745314011399999080353382387875188310876226857595007526866353939120647981831277122977152563326757935648805841815488257317038819203841596980946427504817486560073691038580423154685303395863878483935677262670630800874044646712033152753900198307263764989911497201281271137894038198730295869440, 528294531135665246352339784916516606517294807943820813192811729538211400001467973457300559276518383187049817145104798887264558855266974616624154253759595087392487408786619078083013825038416429411832573729318187734509424340296083559172247691845609954336615907167064555520, 28638903918474961202866265841374129555572759683708149974184563685194367394213852121319233313138251489098481100390353242123909130059942303494273445997449765229068587032938030963062346285458128870694774722600146802650667554413021114864465940252658237440, 179769313486231590772930519078902473361797697894230657273430081157732675805500963132708477322407536021120113879871393357658789768814416622492847430639474110969959963482268386429115945691006857189411070247696162398918067647896493089301343400068500988234275161835090917664532250648398885048449134030095485239295, 179769313486231590772930519078902473361797697894230657273401442253814200844296544348774802483916898444122368001318067763794604786867712276439945844050867407994266613982925203718032540193229548134318182952714512718976928866772129089873184320940147225686954284779127302905001418050890555095803512411439277015040, 9745314011399999080353382387875188310847587953676532565663487673279273852275704363293444413352573371963611474421274157865318112786169298397134856699834197760625678902526694267500757645034699908264895045079751518133739887697211255468160224903522635828330092698016798335248636070305537720320, 528294531135665246323700880998041645314428542102446683637238969854503250027283409772106191882304283735329110727432500303452988050283685817176142117705866200207941657957440504548218643368447228950757431646732209627902988284519816491362466345160298892874179793791263703040, 179769313486231590772930519078902473361797697894230657273430081157732675805500963132708477322407536021120113879871393357658789768814416622492847430639474124377767893424865485276302219601246094119453082952085005768838150682342462881358121021303511041746056627411285071150513050696046818681480127766175129010175, 179769313486231590772930519078902473361797697894230657273401442253814200844298096866867103192851963261436405729897208793973595401420202523041126724221801812386148392677285097629667933554953128302226524496866983823247285430305613806561038641053679090948535188431349788502610563778213473782340357294238958878720, 179769313486231590772930519078902473361269403363094992027077741372816159198982115806672355800279659474267864751290779791581880972790189598863412506136644074964827397019900973839687600012196387280377822082776382164753048833272465786875388233964225103414803513309253069400491663665164468726872075566562012037120, 9745314011399999079825087856739523064523887072678490920349059131176827168638465393438941163325285399750887660343751480288784774871945965367695639736809967882280738721493533452962402971491048564184068075802791937820661365017183686541598335322717403873989341904337241070592290009094176112640, 179769313486231590772930519078902473361797697894230657273430081157732675805500963132708477322407536021120113879871393357658789768814416622492847430639474124377767893424865485276302219601246094119453082952085005768838150682342462881473913110540827237163350510684586298239947245938479716304835356329624224137215, 179769313486231590772930519078902473361797697894230657273401442253814200844298096866867103192851963261436405729897208793973595401420202523041126724221801825793956322619882196476854207465192365232268537201255827193167368464751583598617816262288689144454039552272157261225095856769574679462732370193286336348160, 179769313486231590772930519078902473361269403363094992027077741372816159198983668324764656509214724291581902479869920821760871587342679845464593386307578479356709175714260867024484269078313076938364361935318798127661084809631504027152782643903915523226754495016146612731745860044232036032146627721388055592960, 179769313486231590763185205067502474281444315506355468962553854300137668278633056675495528631641109918654498813989383098433484852583007954309388260774271030331189906128552831856770941901289621089582293296594952120485351088863244502600227512615432362217604147069117332627119507135375438757753527739632310026240]
def tab (j a b : ℕ) : ℕ := tabL.getD ((j * 4 + a) * 4 + b) 0
/-- bitmask (over the 1024 states) of the neighbours of s: AND of the per-column-pair masks -/
def mask (s : ℕ) : ℕ := ((List.range 4).map fun j => tab j (dig s j) (dig s (j + 1))).foldl (· &&& ·) (2 ^ N - 1)
def adjC : List (List (List ℕ)) := [[[0, 256, 320, 336, 340, 341, 512, 576, 592, 596, 597, 640, 656, 660, 661, 672, 676, 677, 680, 681, 682, 768, 832, 848, 852, 853, 896, 912, 916, 917, 928, 932, 933, 936, 937, 938, 960, 976, 980, 981, 992, 996, 997, 1000, 1001, 1002, 1008, 1012, 1013, 1016, 1017, 1018, 1020, 1021, 1022, 1023], [0, 1, 256, 257, 320, 321, 336, 337, 340, 341, 342, 512, 513, 576, 577, 592, 593, 596, 597, 598, 640, 641, 656, 657, 660, 661, 662, 672, 673, 676, 677, 678, 680, 681, 682, 683, 768, 769, 832, 833, 848, 849, 852, 853, 854, 896, 897, 912, 913, 916, 917, 918, 928, 929, 932, 933, 934, 936, 937, 938, 939, 960, 961, 976, 977, 980, 981, 982, 992, 993, 996, 997, 998, 1000, 1001, 1002, 1003, 1008, 1009, 1012, 1013, 1014, 1016, 1017, 1018, 1019, 1020, 1021, 1022, 1023], [0, 1, 2, 256, 257, 258, 320, 321, 322, 336, 337, 338, 340, 341, 342, 343, 512, 513, 514, 576, 577, 578, 592, 593, 594, 596, 597, 598, 599, 640, 641, 642, 656, 657, 658, 660, 661, 662, 663, 672, 673, 674, 676, 677, 678, 679, 680, 681, 682, 683, 768, 769, 770, 832, 833, 834, 848, 849, 850, 852, 853, 854, 855, 896, 897, 898, 912, 913, 914, 916, 917, 918, 919, 928, 929, 930, 932, 933, 934, 935, 936, 937, 938, 939, 960, 961, 962, 976, 977, 978, 980, 981, 982, 983, 992, 993, 994, 996, 997, 998, 999, 1000, 1001, 1002, 1003, 1008, 1009, 1010, 1012, 1013, 1014, 1015, 1016, 1017, 1018, 1019, 1020, 1021, 1022, 1023], [0, 1, 2, 3, 256, 257, 258, 259, 320, 321, 322, 323, 336, 337, 338, 339, 340, 341, 342, 343, 512, 513, 514, 515, 576, 577, 578, 579, 592, 593, 594, 595, 596, 597, 598, 599, 640, 641, 642, 643, 656, 657, 658, 659, 660, 661, 662, 663, 672, 673, 674, 675, 676, 677, 678, 679, 680, 681, 682, 683, 768, 769, 770, 771, 832, 833, 834, 835, 848, 849, 850, 851, 852, 853, 854, 855, 896, 897, 898, 899, 912, 913, 914, 915, 916, 917, 918, 919, 928, 929, 930, 931, 932, 933, 934, 935, 936, 937, 938, 939, 960, 961, 962, 963, 976, 977, 978, 979, 980, 981, 982, 983, 992, 993, 994, 995, 996, 997, 998, 999, 1000, 1001, 1002, 1003, 1008, 1009, 1010, 1011, 1012, 1013, 1014, 1015, 1016, 1017, 1018, 1019, 1020, 1021, 1022, 1023], [4, 260, 324, 340, 344, 345, 516, 580, 596, 600, 601, 644, 660, 664, 665, 676, 680, 681, 684, 685, 686, 772, 836, 852, 856, 857, 900, 916, 920, 921, 932, 936, 937, 940, 941, 942, 964, 980, 984, 985, 996, 1000, 1001, 1004, 1005, 1006, 1012, 1016, 1017, 1020, 1021, 1022], [5, 261, 325, 341, 345, 346, 517, 581, 597, 601, 602, 645, 661, 665, 666, 677, 681, 682, 685, 686, 687, 773, 837, 853, 857, 858, 901, 917, 921, 922, 933, 937, 938, 941, 942, 943, 965, 981, 985, 986, 997, 1001, 1002, 1005, 1006, 1007, 1013, 1017, 1018, 1021, 1022, 1023], [5, 6, 261, 262, 325, 326, 341, 342, 345, 346, 347, 517, 518, 581, 582, 597, 598, 601, 602, 603, 645, 646, 661, 662, 665, 666, 667, 677, 678, 681, 682, 683, 685, 686, 687, 773, 774, 837, 838, 853, 854, 857, 858, 859, 901, 902, 917, 918, 921, 922, 923, 933, 934, 937, 938, 939, 941, 942, 943, 965, 966, 981, 982, 985, 986, 987, 997, 998, 1001, 1002, 1003, 1005, 1006, 1007, 1013, 1014, 1017, 1018, 1019, 1021, 1022, 1023], [5, 6, 7, 261, 262, 263, 325, 326, 327, 341, 342, 343, 345, 346, 347, 517, 518, 519, 581, 582, 583, 597, 598, 599, 601, 602, 603, 645, 646, 647, 661, 662, 663, 665, 666, 667, 677, 678, 679, 681, 682, 683, 685, 686, 687, 773, 774, 775, 837, 838, 839, 853, 854, 855, 857, 858, 859, 901, 902, 903, 917, 918, 919, 921, 922, 923, 933, 934, 935, 937, 938, 939, 941, 942, 943, 965, 966, 967, 981, 982, 983, 985, 986, 987, 997, 998, 999, 1001, 1002, 1003, 1005, 1006, 1007, 1013, 1014, 1015, 1017, 1018, 1019, 1021, 1022, 1023], [8, 264, 328, 344, 348, 349, 520, 584, 600, 604, 605, 648, 664, 668, 669, 680, 684, 685, 776, 840, 856, 860, 861, 904, 920, 924, 925, 936, 940, 941, 968, 984, 988, 989, 1000, 1004, 1005, 1016, 1020, 1021], [9, 265, 329, 345, 349, 350, 521, 585, 601, 605, 606, 649, 665, 669, 670, 681, 685, 686, 777, 841, 857, 861, 862, 905, 921, 925, 926, 937, 941, 942, 969, 985, 989, 990, 1001, 1005, 1006, 1017, 1021, 1022], [10, 266, 330, 346, 350, 351, 522, 586, 602, 606, 607, 650, 666, 670, 671, 682, 686, 687, 778, 842, 858, 862, 863, 906, 922, 926, 927, 938, 942, 943, 970, 986, 990, 991, 1002, 1006, 1007, 1018, 1022, 1023], [10, 11, 266, 267, 330, 331, 346, 347, 350, 351, 522, 523, 586, 587, 602, 603, 606, 607, 650, 651, 666, 667, 670, 671, 682, 683, 686, 687, 778, 779, 842, 843, 858, 859, 862, 863, 906, 907, 922, 923, 926, 927, 938, 939, 942, 943, 970, 971, 986, 987, 990, 991, 1002, 1003, 1006, 1007, 1018, 1019, 1022, 1023], [12, 268, 332, 348, 524, 588, 604, 652, 668, 684, 780, 844, 860, 908, 924, 940, 972, 988, 1004, 1020], [13, 269, 333, 349, 525, 589, 605, 653, 669, 685, 781, 845, 861, 909, 925, 941, 973, 989, 1005, 1021], [14, 270, 334, 350, 526, 590, 606, 654, 670, 686, 782, 846, 862, 910, 926, 942, 974, 990, 1006, 1022], [15, 271, 335, 351, 527, 591, 607, 655, 671, 687, 783, 847, 863, 911, 927, 943, 975, 991, 1007, 1023], [16, 272, 336, 352, 356, 357, 528, 592, 608, 612, 613, 656, 672, 676, 677, 688, 692, 693, 696, 697, 698, 784, 848, 864, 868, 869, 912, 928, 932, 933, 944, 948, 949, 952, 953, 954, 976, 992, 996, 997, 1008, 1012, 1013, 1016, 1017, 1018], [16, 17, 272, 273, 336, 337, 352, 353, 356, 357, 358, 528, 529, 592, 593, 608, 609, 612, 613, 614, 656, 657, 672, 673, 676, 677, 678, 688, 689, 692, 693, 694, 696, 697, 698, 699, 784, 785, 848, 849, 864, 865, 868, 869, 870, 912, 913, 928, 929, 932, 933, 934, 944, 945, 948, 949, 950, 952, 953, 954, 955, 976, 977, 992, 993, 996, 997, 998, 1008, 1009, 1012, 1013, 1014, 1016, 1017, 1018, 1019], [16, 17, 18, 272, 273, 274, 336, 337, 338, 352, 353, 354, 356, 357, 358, 359, 528, 529, 530, 592, 593, 594, 608, 609, 610, 612, 613, 614, 615, 656, 657, 658, 672, 673, 674, 676, 677, 678, 679, 688, 689, 690, 692, 693, 694, 695, 696, 697, 698, 699, 784, 785, 786, 848, 849, 850, 864, 865, 866, 868, 869, 870, 871, 912, 913, 914, 928, 929, 930, 932, 933, 934, 935, 944, 945, 946, 948, 949, 950, 951, 952, 953, 954, 955, 976, 977, 978, 992, 993, 994, 996, 997, 998, 999, 1008, 1009, 1010, 1012, 1013, 1014, 1015, 1016, 1017, 1018, 1019], [16, 17, 18, 19, 272, 273, 274, 275, 336, 337, 338, 339, 352, 353, 354, 355, 356, 357, 358, 359, 528, 529, 530, 531, 592, 593, 594, 595, 608, 609, 610, 611, 612, 613, 614, 615, 656, 657, 658, 659, 672, 673, 674, 675, 676, 677, 678, 679, 688, 689, 690, 691, 692, 693, 694, 695, 696, 697, 698, 699, 784, 785, 786, 787, 848, 849, 850, 851, 864, 865, 866, 867, 868, 869, 870, 871, 912, 913, 914, 915, 928, 929, 930, 931, 932, 933, 934, 935, 944, 945, 946, 947, 948, 949, 950, 951, 952, 953, 954, 955, 976, 977, 978, 979, 992, 993, 994, 995, 996, 997, 998, 999, 1008, 1009, 1010, 1011, 1012, 1013, 1014, 1015, 1016, 1017, 1018, 1019], [20, 276, 340, 356, 360, 361, 532, 596, 612, 616, 617, 660, 676, 680, 681, 692, 696, 697, 700, 701, 702, 788, 852, 868, 872, 873, 916, 932, 936, 937, 948, 952, 953, 956, 957, 958, 980, 996, 1000, 1001, 1012, 1016, 1017, 1020, 1021, 1022], [21, 277, 341, 357, 361, 362, 533, 597, 613, 617, 618, 661, 677, 681, 682, 693, 697, 698, 701, 702, 703, 789, 853, 869, 873, 874, 917, 933, 937, 938, 949, 953, 954, 957, 958, 959, 981, 997, 1001, 1002, 1013, 1017, 1018, 1021, 1022, 1023], [21, 22, 277, 278, 341, 342, 357, 358, 361, 362, 363, 533, 534, 597, 598, 613, 614, 617, 618, 619, 661, 662, 677, 678, 681, 682, 683, 693, 694, 697, 698, 699, 701, 702, 703, 789, 790, 853, 854, 869, 870, 873, 874, 875, 917, 918, 933, 934, 937, 938, 939, 949, 950, 953, 954, 955, 957, 958, 959, 981, 982, 997, 998, 1001, 1002, 1003, 1013, 1014, 1017, 1018, 1019, 1021, 1022, 1023], [21, 22, 23, 277, 278, 279, 341, 342, 343, 357, 358, 359, 361, 362, 363, 533, 534, 535, 597, 598, 599, 613, 614, 615, 617, 618, 619, 661, 662, 663, 677, 678, 679, 681, 682, 683, 693, 694, 695, 697, 698, 699, 701, 702, 703, 789, 790, 791, 853, 854, 855, 869, 870, 871, 873, 874, 875, 917, 918, 919, 933, 934, 935, 937, 938, 939, 949, 950, 951, 953, 954, 955, 957, 958, 959, 981, 982, 983, 997, 998, 999, 1001, 1002, 1003, 1013, 1014, 1015, 1017, 1018, 1019, 1021, 1022, 1023], [24, 280, 344, 360, 364, 365, 536, 600, 616, 620, 621, 664, 680, 684, 685, 696, 700, 701, 792, 856, 872, 876, 877, 920, 936, 940, 941, 952, 956, 957, 984, 1000, 1004, 1005, 1016, 1020, 1021], [25, 281, 345, 361, 365, 366, 537, 601, 617, 621, 622, 665, 681, 685, 686, 697, 701, 702, 793, 857, 873, 877, 878, 921, 937, 941, 942, 953, 957, 958, 985, 1001, 1005, 1006, 1017, 1021, 1022], [26, 282, 346, 362, 366, 367, 538, 602, 618, 622, 623, 666, 682, 686, 687, 698, 702, 703, 794, 858, 874, 878, 879, 922, 938, 942, 943, 954, 958, 959, 986, 1002, 1006, 1007, 1018, 1022, 1023], [26, 27, 282, 283, 346, 347, 362, 363, 366, 367, 538, 539, 602, 603, 618, 619, 622, 623, 666, 667, 682, 683, 686, 687, 698, 699, 702, 703, 794, 795, 858, 859, 874, 875, 878, 879, 922, 923, 938, 939, 942, 943, 954, 955, 958, 959, 986, 987, 1002, 1003, 1006, 1007, 1018, 1019, 1022, 1023], [28, 284, 348, 364, 540, 604, 620, 668, 684, 700, 796, 860, 876, 924, 940, 956, 988, 1004, 1020], [29, 285, 349, 365, 541, 605, 621, 669, 685, 701, 797, 861, 877, 925, 941, 957, 989, 1005, 1021], [30, 286, 350, 366, 542, 606, 622, 670, 686, 702, 798, 862, 878, 926, 942, 958, 990, 1006, 1022], [31, 287, 351, 367, 543, 607, 623, 671, 687, 703, 799, 863, 879, 927, 943, 959, 991, 1007, 1023], [32, 288, 352, 368, 372, 373, 544, 608, 624, 628, 629, 672, 688, 692, 693, 800, 864, 880, 884, 885, 928, 944, 948, 949, 992, 1008, 1012, 1013], [32, 33, 288, 289, 352, 353, 368, 369, 372, 373, 374, 544, 545, 608, 609, 624, 625, 628, 629, 630, 672, 673, 688, 689, 692, 693, 694, 800, 801, 864, 865, 880, 881, 884, 885, 886, 928, 929, 944, 945, 948, 949, 950, 992, 993, 1008, 1009, 1012, 1013, 1014], [32, 33, 34, 288, 289, 290, 352, 353, 354, 368, 369, 370, 372, 373, 374, 375, 544, 545, 546, 608, 609, 610, 624, 625, 626, 628, 629, 630, 631, 672, 673, 674, 688, 689, 690, 692, 693, 694, 695, 800, 801, 802, 864, 865, 866, 880, 881, 882, 884, 885, 886, 887, 928, 929, 930, 944, 945, 946, 948, 949, 950, 951, 992, 993, 994, 1008, 1009, 1010, 1012, 1013, 1014, 1015], [32, 33, 34, 35, 288, 289, 290, 291, 352, 353, 354, 355, 368, 369, 370, 371, 372, 373, 374, 375, 544, 545, 546, 547, 608, 609, 610, 611, 624, 625, 626, 627, 628, 629, 630, 631, 672, 673, 674, 675, 688, 689, 690, 691, 692, 693, 694, 695, 800, 801, 802, 803, 864, 865, 866, 867, 880, 881, 882, 883, 884, 885, 886, 887, 928, 929, 930, 931, 944, 945, 946, 947, 948, 949, 950, 951, 992, 993, 994, 995, 1008, 1009, 1010, 1011, 1012, 1013, 1014, 1015], [36, 292, 356, 372, 376, 377, 548, 612, 628, 632, 633, 676, 692, 696, 697, 804, 868, 884, 888, 889, 932, 948, 952, 953, 996, 1012, 1016, 1017], [37, 293, 357, 373, 377, 378, 549, 613, 629, 633, 634, 677, 693, 697, 698, 805, 869, 885, 889, 890, 933, 949, 953, 954, 997, 1013, 1017, 1018], [37, 38, 293, 294, 357, 358, 373, 374, 377, 378, 379, 549, 550, 613, 614, 629, 630, 633, 634, 635, 677, 678, 693, 694, 697, 698, 699, 805, 806, 869, 870, 885, 886, 889, 890, 891, 933, 934, 949, 950, 953, 954, 955, 997, 998, 1013, 1014, 1017, 1018, 1019], [37, 38, 39, 293, 294, 295, 357, 358, 359, 373, 374, 375, 377, 378, 379, 549, 550, 551, 613, 614, 615, 629, 630, 631, 633, 634, 635, 677, 678, 679, 693, 694, 695, 697, 698, 699, 805, 806, 807, 869, 870, 871, 885, 886, 887, 889, 890, 891, 933, 934, 935, 949, 950, 951, 953, 954, 955, 997, 998, 999, 1013, 1014, 1015, 1017, 1018, 1019], [40, 296, 360, 376, 380, 381, 552, 616, 632, 636, 637, 680, 696, 700, 701, 808, 872, 888, 892, 893, 936, 952, 956, 957, 1000, 1016, 1020, 1021], [41, 297, 361, 377, 381, 382, 553, 617, 633, 637, 638, 681, 697, 701, 702, 809, 873, 889, 893, 894, 937, 953, 957, 958, 1001, 1017, 1021, 1022], [42, 298, 362, 378, 382, 383, 554, 618, 634, 638, 639, 682, 698, 702, 703, 810, 874, 890, 894, 895, 938, 954, 958, 959, 1002, 1018, 1022, 1023], [42, 43, 298, 299, 362, 363, 378, 379, 382, 383, 554, 555, 618, 619, 634, 635, 638, 639, 682, 683, 698, 699, 702, 703, 810, 811, 874, 875, 890, 891, 894, 895, 938, 939, 954, 955, 958, 959, 1002, 1003, 1018, 1019, 1022, 1023], [44, 300, 364, 380, 556, 620, 636, 684, 700, 812, 876, 892, 940, 956, 1004, 1020], [45, 301, 365, 381, 557, 621, 637, 685, 701, 813, 877, 893, 941, 957, 1005, 1021], [46, 302, 366, 382, 558, 622, 638, 686, 702, 814, 878, 894, 942, 958, 1006, 1022], [47, 303, 367, 383, 559, 623, 639, 687, 703, 815, 879, 895, 943, 959, 1007, 1023], [48, 304, 368, 560, 624, 688, 816, 880, 944, 1008], [48, 49, 304, 305, 368, 369, 560, 561, 624, 625, 688, 689, 816, 817, 880, 881, 944, 945, 1008, 1009], [48, 49, 50, 304, 305, 306, 368, 369, 370, 560, 561, 562, 624, 625, 626, 688, 689, 690, 816, 817, 818, 880, 881, 882, 944, 945, 946, 1008, 1009, 1010], [48, 49, 50, 51, 304, 305, 306, 307, 368, 369, 370, 371, 560, 561, 562, 563, 624, 625, 626, 627, 688, 689, 690, 691, 816, 817, 818, 819, 880, 881, 882, 883, 944, 945, 946, 947, 1008, 1009, 1010, 1011], [52, 308, 372, 564, 628, 692, 820, 884, 948, 1012], [53, 309, 373, 565, 629, 693, 821, 885, 949, 1013], [53, 54, 309, 310, 373, 374, 565, 566, 629, 630, 693, 694, 821, 822, 885, 886, 949, 950, 1013, 1014], [53, 54, 55, 309, 310, 311, 373, 374, 375, 565, 566, 567, 629, 630, 631, 693, 694, 695, 821, 822, 823, 885, 886, 887, 949, 950, 951, 1013, 1014, 1015], [56, 312, 376, 568, 632, 696, 824, 888, 952, 1016], [57, 313, 377, 569, 633, 697, 825, 889, 953, 1017], [58, 314, 378, 570, 634, 698, 826, 890, 954, 1018], [58, 59, 314, 315, 378, 379, 570, 571, 634, 635, 698, 699, 826, 827, 890, 891, 954, 955, 1018, 1019], [60, 316, 380, 572, 636, 700, 828, 892, 956, 1020], [61, 317, 381, 573, 637, 701, 829, 893, 957, 1021], [62, 318, 382, 574, 638, 702, 830, 894, 958, 1022], [63, 319, 383, 575, 639, 703, 831, 895, 959, 1023]], [[64, 320, 384, 400, 404, 405, 576, 640, 656, 660, 661, 704, 720, 724, 725, 736, 740, 741, 744, 745, 746, 832, 896, 912, 916, 917, 960, 976, 980, 981, 992, 996, 997, 1000, 1001, 1002], [64, 65, 320, 321, 384, 385, 400, 401, 404, 405, 406, 576, 577, 640, 641, 656, 657, 660, 661, 662, 704, 705, 720, 721, 724, 725, 726, 736, 737, 740, 741, 742, 744, 745, 746, 747, 832, 833, 896, 897, 912, 913, 916, 917, 918, 960, 961, 976, 977, 980, 981, 982, 992, 993, 996, 997, 998, 1000, 1001, 1002, 1003], [64, 65, 66, 320, 321, 322, 384, 385, 386, 400, 401, 402, 404, 405, 406, 407, 576, 577, 578, 640, 641, 642, 656, 657, 658, 660, 661, 662, 663, 704, 705, 706, 720, 721, 722, 724, 725, 726, 727, 736, 737, 738, 740, 741, 742, 743, 744, 745, 746, 747, 832, 833, 834, 896, 897, 898, 912, 913, 914, 916, 917, 918, 919, 960, 961, 962, 976, 977, 978, 980, 981, 982, 983, 992, 993, 994, 996, 997, 998, 999, 1000, 1001, 1002, 1003], [64, 65, 66, 67, 320, 321, 322, 323, 384, 385, 386, 387, 400, 401, 402, 403, 404, 405, 406, 407, 576, 577, 578, 579, 640, 641, 642, 643, 656, 657, 658, 659, 660, 661, 662, 663, 704, 705, 706, 707, 720, 721, 722, 723, 724, 725, 726, 727, 736, 737, 738, 739, 740, 741, 742, 743, 744, 745, 746, 747, 832, 833, 834, 835, 896, 897, 898, 899, 912, 913, 914, 915, 916, 917, 918, 919, 960, 961, 962, 963, 976, 977, 978, 979, 980, 981, 982, 983, 992, 993, 994, 995, 996, 997, 998, 999, 1000, 1001, 1002, 1003], [68, 324, 388, 404, 408, 409, 580, 644, 660, 664, 665, 708, 724, 728, 729, 740, 744, 745, 748, 749, 750, 836, 900, 916, 920, 921, 964, 980, 984, 985, 996, 1000, 1001, 1004, 1005, 1006], [69, 325, 389, 405, 409, 410, 581, 645, 661, 665, 666, 709, 725, 729, 730, 741, 745, 746, 749, 750, 751, 837, 901, 917, 921, 922, 965, 981, 985, 986, 997, 1001, 1002, 1005, 1006, 1007], [69, 70, 325, 326, 389, 390, 405, 406, 409, 410, 411, 581, 582, 645, 646, 661, 662, 665, 666, 667, 709, 710, 725, 726, 729, 730, 731, 741, 742, 745, 746, 747, 749, 750, 751, 837, 838, 901, 902, 917, 918, 921, 922, 923, 965, 966, 981, 982, 985, 986, 987, 997, 998, 1001, 1002, 1003, 1005, 1006, 1007], [69, 70, 71, 325, 326, 327, 389, 390, 391, 405, 406, 407, 409, 410, 411, 581, 582, 583, 645, 646, 647, 661, 662, 663, 665, 666, 667, 709, 710, 711, 725, 726, 727, 729, 730, 731, 741, 742, 743, 745, 746, 747, 749, 750, 751, 837, 838, 839, 901, 902, 903, 917, 918, 919, 921, 922, 923, 965, 966, 967, 981, 982, 983, 985, 986, 987, 997, 998, 999, 1001, 1002, 1003, 1005, 1006, 1007], [72, 328, 392, 408, 412, 413, 584, 648, 664, 668, 669, 712, 728, 732, 733, 744, 748, 749, 840, 904, 920, 924, 925, 968, 984, 988, 989, 1000, 1004, 1005], [73, 329, 393, 409, 413, 414, 585, 649, 665, 669, 670, 713, 729, 733, 734, 745, 749, 750, 841, 905, 921, 925, 926, 969, 985, 989, 990, 1001, 1005, 1006], [74, 330, 394, 410, 414, 415, 586, 650, 666, 670, 671, 714, 730, 734, 735, 746, 750, 751, 842, 906, 922, 926, 927, 970, 986, 990, 991, 1002, 1006, 1007], [74, 75, 330, 331, 394, 395, 410, 411, 414, 415, 586, 587, 650, 651, 666, 667, 670, 671, 714, 715, 730, 731, 734, 735, 746, 747, 750, 751, 842, 843, 906, 907, 922, 923, 926, 927, 970, 971, 986, 987, 990, 991, 1002, 1003, 1006, 1007], [76, 332, 396, 412, 588, 652, 668, 716, 732, 748, 844, 908, 924, 972, 988, 1004], [77, 333, 397, 413, 589, 653, 669, 717, 733, 749, 845, 909, 925, 973, 989, 1005], [78, 334, 398, 414, 590, 654, 670, 718, 734, 750, 846, 910, 926, 974, 990, 1006], [79, 335, 399, 415, 591, 655, 671, 719, 735, 751, 847, 911, 927, 975, 991, 1007], [80, 336, 400, 416, 420, 421, 592, 656, 672, 676, 677, 720, 736, 740, 741, 752, 756, 757, 760, 761, 762, 848, 912, 928, 932, 933, 976, 992, 996, 997, 1008, 1012, 1013, 1016, 1017, 1018], [80, 81, 336, 337, 400, 401, 416, 417, 420, 421, 422, 592, 593, 656, 657, 672, 673, 676, 677, 678, 720, 721, 736, 737, 740, 741, 742, 752, 753, 756, 757, 758, 760, 761, 762, 763, 848, 849, 912, 913, 928, 929, 932, 933, 934, 976, 977, 992, 993, 996, 997, 998, 1008, 1009, 1012, 1013, 1014, 1016, 1017, 1018, 1019], [80, 81, 82, 336, 337, 338, 400, 401, 402, 416, 417, 418, 420, 421, 422, 423, 592, 593, 594, 656, 657, 658, 672, 673, 674, 676, 677, 678, 679, 720, 721, 722, 736, 737, 738, 740, 741, 742, 743, 752, 753, 754, 756, 757, 758, 759, 760, 761, 762, 763, 848, 849, 850, 912, 913, 914, 928, 929, 930, 932, 933, 934, 935, 976, 977, 978, 992, 993, 994, 996, 997, 998, 999, 1008, 1009, 1010, 1012, 1013, 1014, 1015, 1016, 1017, 1018, 1019], [80, 81, 82, 83, 336, 337, 338, 339, 400, 401, 402, 403, 416, 417, 418, 419, 420, 421, 422, 423, 592, 593, 594, 595, 656, 657, 658, 659, 672, 673, 674, 675, 676, 677, 678, 679, 720, 721, 722, 723, 736, 737, 738, 739, 740, 741, 742, 743, 752, 753, 754, 755, 756, 757, 758, 759, 760, 761, 762, 763, 848, 849, 850, 851, 912, 913, 914, 915, 928, 929, 930, 931, 932, 933, 934, 935, 976, 977, 978, 979, 992, 993, 994, 995, 996, 997, 998, 999, 1008, 1009, 1010, 1011, 1012, 1013, 1014, 1015, 1016, 1017, 1018, 1019], [84, 340, 404, 420, 424, 425, 596, 660, 676, 680, 681, 724, 740, 744, 745, 756, 760, 761, 764, 765, 766, 852, 916, 932, 936, 937, 980, 996, 1000, 1001, 1012, 1016, 1017, 1020, 1021, 1022], [85, 341, 405, 421, 425, 426, 597, 661, 677, 681, 682, 725, 741, 745, 746, 757, 761, 762, 765, 766, 767, 853, 917, 933, 937, 938, 981, 997, 1001, 1002, 1013, 1017, 1018, 1021, 1022, 1023], [85, 86, 341, 342, 405, 406, 421, 422, 425, 426, 427, 597, 598, 661, 662, 677, 678, 681, 682, 683, 725, 726, 741, 742, 745, 746, 747, 757, 758, 761, 762, 763, 765, 766, 767, 853, 854, 917, 918, 933, 934, 937, 938, 939, 981, 982, 997, 998, 1001, 1002, 1003, 1013, 1014, 1017, 1018, 1019, 1021, 1022, 1023], [85, 86, 87, 341, 342, 343, 405, 406, 407, 421, 422, 423, 425, 426, 427, 597, 598, 599, 661, 662, 663, 677, 678, 679, 681, 682, 683, 725, 726, 727, 741, 742, 743, 745, 746, 747, 757, 758, 759, 761, 762, 763, 765, 766, 767, 853, 854, 855, 917, 918, 919, 933, 934, 935, 937, 938, 939, 981, 982, 983, 997, 998, 999, 1001, 1002, 1003, 1013, 1014, 1015, 1017, 1018, 1019, 1021, 1022, 1023], [88, 344, 408, 424, 428, 429, 600, 664, 680, 684, 685, 728, 744, 748, 749, 760, 764, 765, 856, 920, 936, 940, 941, 984, 1000, 1004, 1005, 1016, 1020, 1021], [89, 345, 409, 425, 429, 430, 601, 665, 681, 685, 686, 729, 745, 749, 750, 761, 765, 766, 857, 921, 937, 941, 942, 985, 1001, 1005, 1006, 1017, 1021, 1022], [90, 346, 410, 426, 430, 431, 602, 666, 682, 686, 687, 730, 746, 750, 751, 762, 766, 767, 858, 922, 938, 942, 943, 986, 1002, 1006, 1007, 1018, 1022, 1023], [90, 91, 346, 347, 410, 411, 426, 427, 430, 431, 602, 603, 666, 667, 682, 683, 686, 687, 730, 731, 746, 747, 750, 751, 762, 763, 766, 767, 858, 859, 922, 923, 938, 939, 942, 943, 986, 987, 1002, 1003, 1006, 1007, 1018, 1019, 1022, 1023], [92, 348, 412, 428, 604, 668, 684, 732, 748, 764, 860, 924, 940, 988, 1004, 1020], [93, 349, 413, 429, 605, 669, 685, 733, 749, 765, 861, 925, 941, 989, 1005, 1021], [94, 350, 414, 430, 606, 670, 686, 734, 750, 766, 862, 926, 942, 990, 1006, 1022], [95, 351, 415, 431, 607, 671, 687, 735, 751, 767, 863, 927, 943, 991, 1007, 1023], [96, 352, 416, 432, 436, 437, 608, 672, 688, 692, 693, 736, 752, 756, 757, 864, 928, 944, 948, 949, 992, 1008, 1012, 1013], [96, 97, 352, 353, 416, 417, 432, 433, 436, 437, 438, 608, 609, 672, 673, 688, 689, 692, 693, 694, 736, 737, 752, 753, 756, 757, 758, 864, 865, 928, 929, 944, 945, 948, 949, 950, 992, 993, 1008, 1009, 1012, 1013, 1014], [96, 97, 98, 352, 353, 354, 416, 417, 418, 432, 433, 434, 436, 437, 438, 439, 608, 609, 610, 672, 673, 674, 688, 689, 690, 692, 693, 694, 695, 736, 737, 738, 752, 753, 754, 756, 757, 758, 759, 864, 865, 866, 928, 929, 930, 944, 945, 946, 948, 949, 950, 951, 992, 993, 994, 1008, 1009, 1010, 1012, 1013, 1014, 1015], [96, 97, 98, 99, 352, 353, 354, 355, 416, 417, 418, 419, 432, 433, 434, 435, 436, 437, 438, 439, 608, 609, 610, 611, 672, 673, 674, 675, 688, 689, 690, 691, 692, 693, 694, 695, 736, 737, 738, 739, 752, 753, 754, 755, 756, 757, 758, 759, 864, 865, 866, 867, 928, 929, 930, 931, 944, 945, 946, 947, 948, 949, 950, 951, 992, 993, 994, 995, 1008, 1009, 1010, 1011, 1012, 1013, 1014, 1015], [100, 356, 420, 436, 440, 441, 612, 676, 692, 696, 697, 740, 756, 760, 761, 868, 932, 948, 952, 953, 996, 1012, 1016, 1017], [101, 357, 421, 437, 441, 442, 613, 677, 693, 697, 698, 741, 757, 761, 762, 869, 933, 949, 953, 954, 997, 1013, 1017, 1018], [101, 102, 357, 358, 421, 422, 437, 438, 441, 442, 443, 613, 614, 677, 678, 693, 694, 697, 698, 699, 741, 742, 757, 758, 761, 762, 763, 869, 870, 933, 934, 949, 950, 953, 954, 955, 997, 998, 1013, 1014, 1017, 1018, 1019], [101, 102, 103, 357, 358, 359, 421, 422, 423, 437, 438, 439, 441, 442, 443, 613, 614, 615, 677, 678, 679, 693, 694, 695, 697, 698, 699, 741, 742, 743, 757, 758, 759, 761, 762, 763, 869, 870, 871, 933, 934, 935, 949, 950, 951, 953, 954, 955, 997, 998, 999, 1013, 1014, 1015, 1017, 1018, 1019], [104, 360, 424, 440, 444, 445, 616, 680, 696, 700, 701, 744, 760, 764, 765, 872, 936, 952, 956, 957, 1000, 1016, 1020, 1021], [105, 361, 425, 441, 445, 446, 617, 681, 697, 701, 702, 745, 761, 765, 766, 873, 937, 953, 957, 958, 1001, 1017, 1021, 1022], [106, 362, 426, 442, 446, 447, 618, 682, 698, 702, 703, 746, 762, 766, 767, 874, 938, 954, 958, 959, 1002, 1018, 1022, 1023], [106, 107, 362, 363, 426, 427, 442, 443, 446, 447, 618, 619, 682, 683, 698, 699, 702, 703, 746, 747, 762, 763, 766, 767, 874, 875, 938, 939, 954, 955, 958, 959, 1002, 1003, 1018, 1019, 1022, 1023], [108, 364, 428, 444, 620, 684, 700, 748, 764, 876, 940, 956, 1004, 1020], [109, 365, 429, 445, 621, 685, 701, 749, 765, 877, 941, 957, 1005, 1021], [110, 366, 430, 446, 622, 686, 702, 750, 766, 878, 942, 958, 1006, 1022], [111, 367, 431, 447, 623, 687, 703, 751, 767, 879, 943, 959, 1007, 1023], [112, 368, 432, 624, 688, 752, 880, 944, 1008], [112, 113, 368, 369, 432, 433, 624, 625, 688, 689, 752, 753, 880, 881, 944, 945, 1008, 1009], [112, 113, 114, 368, 369, 370, 432, 433, 434, 624, 625, 626, 688, 689, 690, 752, 753, 754, 880, 881, 882, 944, 945, 946, 1008, 1009, 1010], [112, 113, 114, 115, 368, 369, 370, 371, 432, 433, 434, 435, 624, 625, 626, 627, 688, 689, 690, 691, 752, 753, 754, 755, 880, 881, 882, 883, 944, 945, 946, 947, 1008, 1009, 1010, 1011], [116, 372, 436, 628, 692, 756, 884, 948, 1012], [117, 373, 437, 629, 693, 757, 885, 949, 1013], [117, 118, 373, 374, 437, 438, 629, 630, 693, 694, 757, 758, 885, 886, 949, 950, 1013, 1014], [117, 118, 119, 373, 374, 375, 437, 438, 439, 629, 630, 631, 693, 694, 695, 757, 758, 759, 885, 886, 887, 949, 950, 951, 1013, 1014, 1015], [120, 376, 440, 632, 696, 760, 888, 952, 1016], [121, 377, 441, 633, 697, 761, 889, 953, 1017], [122, 378, 442, 634, 698, 762, 890, 954, 1018], [122, 123, 378, 379, 442, 443, 634, 635, 698, 699, 762, 763, 890, 891, 954, 955, 1018, 1019], [124, 380, 444, 636, 700, 764, 892, 956, 1020], [125, 381, 445, 637, 701, 765, 893, 957, 1021], [126, 382, 446, 638, 702, 766, 894, 958, 1022], [127, 383, 447, 639, 703, 767, 895, 959, 1023]], [[128, 384, 448, 464, 468, 469, 640, 704, 720, 724, 725, 896, 960, 976, 980, 981], [128, 129, 384, 385, 448, 449, 464, 465, 468, 469, 470, 640, 641, 704, 705, 720, 721, 724, 725, 726, 896, 897, 960, 961, 976, 977, 980, 981, 982], [128, 129, 130, 384, 385, 386, 448, 449, 450, 464, 465, 466, 468, 469, 470, 471, 640, 641, 642, 704, 705, 706, 720, 721, 722, 724, 725, 726, 727, 896, 897, 898, 960, 961, 962, 976, 977, 978, 980, 981, 982, 983], [128, 129, 130, 131, 384, 385, 386, 387, 448, 449, 450, 451, 464, 465, 466, 467, 468, 469, 470, 471, 640, 641, 642, 643, 704, 705, 706, 707, 720, 721, 722, 723, 724, 725, 726, 727, 896, 897, 898, 899, 960, 961, 962, 963, 976, 977, 978, 979, 980, 981, 982, 983], [132, 388, 452, 468, 472, 473, 644, 708, 724, 728, 729, 900, 964, 980, 984, 985], [133, 389, 453, 469, 473, 474, 645, 709, 725, 729, 730, 901, 965, 981, 985, 986], [133, 134, 389, 390, 453, 454, 469, 470, 473, 474, 475, 645, 646, 709, 710, 725, 726, 729, 730, 731, 901, 902, 965, 966, 981, 982, 985, 986, 987], [133, 134, 135, 389, 390, 391, 453, 454, 455, 469, 470, 471, 473, 474, 475, 645, 646, 647, 709, 710, 711, 725, 726, 727, 729, 730, 731, 901, 902, 903, 965, 966, 967, 981, 982, 983, 985, 986, 987], [136, 392, 456, 472, 476, 477, 648, 712, 728, 732, 733, 904, 968, 984, 988, 989], [137, 393, 457, 473, 477, 478, 649, 713, 729, 733, 734, 905, 969, 985, 989, 990], [138, 394, 458, 474, 478, 479, 650, 714, 730, 734, 735, 906, 970, 986, 990, 991], [138, 139, 394, 395, 458, 459, 474, 475, 478, 479, 650, 651, 714, 715, 730, 731, 734, 735, 906, 907, 970, 971, 986, 987, 990, 991], [140, 396, 460, 476, 652, 716, 732, 908, 972, 988], [141, 397, 461, 477, 653, 717, 733, 909, 973, 989], [142, 398, 462, 478, 654, 718, 734, 910, 974, 990], [143, 399, 463, 479, 655, 719, 735, 911, 975, 991], [144, 400, 464, 480, 484, 485, 656, 720, 736, 740, 741, 912, 976, 992, 996, 997], [144, 145, 400, 401, 464, 465, 480, 481, 484, 485, 486, 656, 657, 720, 721, 736, 737, 740, 741, 742, 912, 913, 976, 977, 992, 993, 996, 997, 998], [144, 145, 146, 400, 401, 402, 464, 465, 466, 480, 481, 482, 484, 485, 486, 487, 656, 657, 658, 720, 721, 722, 736, 737, 738, 740, 741, 742, 743, 912, 913, 914, 976, 977, 978, 992, 993, 994, 996, 997, 998, 999], [144, 145, 146, 147, 400, 401, 402, 403, 464, 465, 466, 467, 480, 481, 482, 483, 484, 485, 486, 487, 656, 657, 658, 659, 720, 721, 722, 723, 736, 737, 738, 739, 740, 741, 742, 743, 912, 913, 914, 915, 976, 977, 978, 979, 992, 993, 994, 995, 996, 997, 998, 999], [148, 404, 468, 484, 488, 489, 660, 724, 740, 744, 745, 916, 980, 996, 1000, 1001], [149, 405, 469, 485, 489, 490, 661, 725, 741, 745, 746, 917, 981, 997, 1001, 1002], [149, 150, 405, 406, 469, 470, 485, 486, 489, 490, 491, 661, 662, 725, 726, 741, 742, 745, 746, 747, 917, 918, 981, 982, 997, 998, 1001, 1002, 1003], [149, 150, 151, 405, 406, 407, 469, 470, 471, 485, 486, 487, 489, 490, 491, 661, 662, 663, 725, 726, 727, 741, 742, 743, 745, 746, 747, 917, 918, 919, 981, 982, 983, 997, 998, 999, 1001, 1002, 1003], [152, 408, 472, 488, 492, 493, 664, 728, 744, 748, 749, 920, 984, 1000, 1004, 1005], [153, 409, 473, 489, 493, 494, 665, 729, 745, 749, 750, 921, 985, 1001, 1005, 1006], [154, 410, 474, 490, 494, 495, 666, 730, 746, 750, 751, 922, 986, 1002, 1006, 1007], [154, 155, 410, 411, 474, 475, 490, 491, 494, 495, 666, 667, 730, 731, 746, 747, 750, 751, 922, 923, 986, 987, 1002, 1003, 1006, 1007], [156, 412, 476, 492, 668, 732, 748, 924, 988, 1004], [157, 413, 477, 493, 669, 733, 749, 925, 989, 1005], [158, 414, 478, 494, 670, 734, 750, 926, 990, 1006], [159, 415, 479, 495, 671, 735, 751, 927, 991, 1007], [160, 416, 480, 496, 500, 501, 672, 736, 752, 756, 757, 928, 992, 1008, 1012, 1013], [160, 161, 416, 417, 480, 481, 496, 497, 500, 501, 502, 672, 673, 736, 737, 752, 753, 756, 757, 758, 928, 929, 992, 993, 1008, 1009, 1012, 1013, 1014], [160, 161, 162, 416, 417, 418, 480, 481, 482, 496, 497, 498, 500, 501, 502, 503, 672, 673, 674, 736, 737, 738, 752, 753, 754, 756, 757, 758, 759, 928, 929, 930, 992, 993, 994, 1008, 1009, 1010, 1012, 1013, 1014, 1015], [160, 161, 162, 163, 416, 417, 418, 419, 480, 481, 482, 483, 496, 497, 498, 499, 500, 501, 502, 503, 672, 673, 674, 675, 736, 737, 738, 739, 752, 753, 754, 755, 756, 757, 758, 759, 928, 929, 930, 931, 992, 993, 994, 995, 1008, 1009, 1010, 1011, 1012, 1013, 1014, 1015], [164, 420, 484, 500, 504, 505, 676, 740, 756, 760, 761, 932, 996, 1012, 1016, 1017], [165, 421, 485, 501, 505, 506, 677, 741, 757, 761, 762, 933, 997, 1013, 1017, 1018], [165, 166, 421, 422, 485, 486, 501, 502, 505, 506, 507, 677, 678, 741, 742, 757, 758, 761, 762, 763, 933, 934, 997, 998, 1013, 1014, 1017, 1018, 1019], [165, 166, 167, 421, 422, 423, 485, 486, 487, 501, 502, 503, 505, 506, 507, 677, 678, 679, 741, 742, 743, 757, 758, 759, 761, 762, 763, 933, 934, 935, 997, 998, 999, 1013, 1014, 1015, 1017, 1018, 1019], [168, 424, 488, 504, 508, 509, 680, 744, 760, 764, 765, 936, 1000, 1016, 1020, 1021], [169, 425, 489, 505, 509, 510, 681, 745, 761, 765, 766, 937, 1001, 1017, 1021, 1022], [170, 426, 490, 506, 510, 511, 682, 746, 762, 766, 767, 938, 1002, 1018, 1022, 1023], [170, 171, 426, 427, 490, 491, 506, 507, 510, 511, 682, 683, 746, 747, 762, 763, 766, 767, 938, 939, 1002, 1003, 1018, 1019, 1022, 1023], [172, 428, 492, 508, 684, 748, 764, 940, 1004, 1020], [173, 429, 493, 509, 685, 749, 765, 941, 1005, 1021], [174, 430, 494, 510, 686, 750, 766, 942, 1006, 1022], [175, 431, 495, 511, 687, 751, 767, 943, 1007, 1023], [176, 432, 496, 688, 752, 944, 1008], [176, 177, 432, 433, 496, 497, 688, 689, 752, 753, 944, 945, 1008, 1009], [176, 177, 178, 432, 433, 434, 496, 497, 498, 688, 689, 690, 752, 753, 754, 944, 945, 946, 1008, 1009, 1010], [176, 177, 178, 179, 432, 433, 434, 435, 496, 497, 498, 499, 688, 689, 690, 691, 752, 753, 754, 755, 944, 945, 946, 947, 1008, 1009, 1010, 1011], [180, 436, 500, 692, 756, 948, 1012], [181, 437, 501, 693, 757, 949, 1013], [181, 182, 437, 438, 501, 502, 693, 694, 757, 758, 949, 950, 1013, 1014], [181, 182, 183, 437, 438, 439, 501, 502, 503, 693, 694, 695, 757, 758, 759, 949, 950, 951, 1013, 1014, 1015], [184, 440, 504, 696, 760, 952, 1016], [185, 441, 505, 697, 761, 953, 1017], [186, 442, 506, 698, 762, 954, 1018], [186, 187, 442, 443, 506, 507, 698, 699, 762, 763, 954, 955, 1018, 1019], [188, 444, 508, 700, 764, 956, 1020], [189, 445, 509, 701, 765, 957, 1021], [190, 446, 510, 702, 766, 958, 1022], [191, 447, 511, 703, 767, 959, 1023]], [[192, 448, 704, 960], [192, 193, 448, 449, 704, 705, 960, 961], [192, 193, 194, 448, 449, 450, 704, 705, 706, 960, 961, 962], [192, 193, 194, 195, 448, 449, 450, 451, 704, 705, 706, 707, 960, 961, 962, 963], [196, 452, 708, 964], [197, 453, 709, 965], [197, 198, 453, 454, 709, 710, 965, 966], [197, 198, 199, 453, 454, 455, 709, 710, 711, 965, 966, 967], [200, 456, 712, 968], [201, 457, 713, 969], [202, 458, 714, 970], [202, 203, 458, 459, 714, 715, 970, 971], [204, 460, 716, 972], [205, 461, 717, 973], [206, 462, 718, 974], [207, 463, 719, 975], [208, 464, 720, 976], [208, 209, 464, 465, 720, 721, 976, 977], [208, 209, 210, 464, 465, 466, 720, 721, 722, 976, 977, 978], [208, 209, 210, 211, 464, 465, 466, 467, 720, 721, 722, 723, 976, 977, 978, 979], [212, 468, 724, 980], [213, 469, 725, 981], [213, 214, 469, 470, 725, 726, 981, 982], [213, 214, 215, 469, 470, 471, 725, 726, 727, 981, 982, 983], [216, 472, 728, 984], [217, 473, 729, 985], [218, 474, 730, 986], [218, 219, 474, 475, 730, 731, 986, 987], [220, 476, 732, 988], [221, 477, 733, 989], [222, 478, 734, 990], [223, 479, 735, 991], [224, 480, 736, 992], [224, 225, 480, 481, 736, 737, 992, 993], [224, 225, 226, 480, 481, 482, 736, 737, 738, 992, 993, 994], [224, 225, 226, 227, 480, 481, 482, 483, 736, 737, 738, 739, 992, 993, 994, 995], [228, 484, 740, 996], [229, 485, 741, 997], [229, 230, 485, 486, 741, 742, 997, 998], [229, 230, 231, 485, 486, 487, 741, 742, 743, 997, 998, 999], [232, 488, 744, 1000], [233, 489, 745, 1001], [234, 490, 746, 1002], [234, 235, 490, 491, 746, 747, 1002, 1003], [236, 492, 748, 1004], [237, 493, 749, 1005], [238, 494, 750, 1006], [239, 495, 751, 1007], [240, 496, 752, 1008], [240, 241, 496, 497, 752, 753, 1008, 1009], [240, 241, 242, 496, 497, 498, 752, 753, 754, 1008, 1009, 1010], [240, 241, 242, 243, 496, 497, 498, 499, 752, 753, 754, 755, 1008, 1009, 1010, 1011], [244, 500, 756, 1012], [245, 501, 757, 1013], [245, 246, 501, 502, 757, 758, 1013, 1014], [245, 246, 247, 501, 502, 503, 757, 758, 759, 1013, 1014, 1015], [248, 504, 760, 1016], [249, 505, 761, 1017], [250, 506, 762, 1018], [250, 251, 506, 507, 762, 763, 1018, 1019], [252, 508, 764, 1020], [253, 509, 765, 1021], [254, 510, 766, 1022], [255, 511, 767, 1023]], [[256, 512, 576, 592, 596, 597, 768, 832, 848, 852, 853, 896, 912, 916, 917, 928, 932, 933, 936, 937, 938], [256, 257, 512, 513, 576, 577, 592, 593, 596, 597, 598, 768, 769, 832, 833, 848, 849, 852, 853, 854, 896, 897, 912, 913, 916, 917, 918, 928, 929, 932, 933, 934, 936, 937, 938, 939], [256, 257, 258, 512, 513, 514, 576, 577, 578, 592, 593, 594, 596, 597, 598, 599, 768, 769, 770, 832, 833, 834, 848, 849, 850, 852, 853, 854, 855, 896, 897, 898, 912, 913, 914, 916, 917, 918, 919, 928, 929, 930, 932, 933, 934, 935, 936, 937, 938, 939], [256, 257, 258, 259, 512, 513, 514, 515, 576, 577, 578, 579, 592, 593, 594, 595, 596, 597, 598, 599, 768, 769, 770, 771, 832, 833, 834, 835, 848, 849, 850, 851, 852, 853, 854, 855, 896, 897, 898, 899, 912, 913, 914, 915, 916, 917, 918, 919, 928, 929, 930, 931, 932, 933, 934, 935, 936, 937, 938, 939], [260, 516, 580, 596, 600, 601, 772, 836, 852, 856, 857, 900, 916, 920, 921, 932, 936, 937, 940, 941, 942], [261, 517, 581, 597, 601, 602, 773, 837, 853, 857, 858, 901, 917, 921, 922, 933, 937, 938, 941, 942, 943], [261, 262, 517, 518, 581, 582, 597, 598, 601, 602, 603, 773, 774, 837, 838, 853, 854, 857, 858, 859, 901, 902, 917, 918, 921, 922, 923, 933, 934, 937, 938, 939, 941, 942, 943], [261, 262, 263, 517, 518, 519, 581, 582, 583, 597, 598, 599, 601, 602, 603, 773, 774, 775, 837, 838, 839, 853, 854, 855, 857, 858, 859, 901, 902, 903, 917, 918, 919, 921, 922, 923, 933, 934, 935, 937, 938, 939, 941, 942, 943], [264, 520, 584, 600, 604, 605, 776, 840, 856, 860, 861, 904, 920, 924, 925, 936, 940, 941], [265, 521, 585, 601, 605, 606, 777, 841, 857, 861, 862, 905, 921, 925, 926, 937, 941, 942], [266, 522, 586, 602, 606, 607, 778, 842, 858, 862, 863, 906, 922, 926, 927, 938, 942, 943], [266, 267, 522, 523, 586, 587, 602, 603, 606, 607, 778, 779, 842, 843, 858, 859, 862, 863, 906, 907, 922, 923, 926, 927, 938, 939, 942, 943], [268, 524, 588, 604, 780, 844, 860, 908, 924, 940], [269, 525, 589, 605, 781, 845, 861, 909, 925, 941], [270, 526, 590, 606, 782, 846, 862, 910, 926, 942], [271, 527, 591, 607, 783, 847, 863, 911, 927, 943], [272, 528, 592, 608, 612, 613, 784, 848, 864, 868, 869, 912, 928, 932, 933, 944, 948, 949, 952, 953, 954], [272, 273, 528, 529, 592, 593, 608, 609, 612, 613, 614, 784, 785, 848, 849, 864, 865, 868, 869, 870, 912, 913, 928, 929, 932, 933, 934, 944, 945, 948, 949, 950, 952, 953, 954, 955], [272, 273, 274, 528, 529, 530, 592, 593, 594, 608, 609, 610, 612, 613, 614, 615, 784, 785, 786, 848, 849, 850, 864, 865, 866, 868, 869, 870, 871, 912, 913, 914, 928, 929, 930, 932, 933, 934, 935, 944, 945, 946, 948, 949, 950, 951, 952, 953, 954, 955], [272, 273, 274, 275, 528, 529, 530, 531, 592, 593, 594, 595, 608, 609, 610, 611, 612, 613, 614, 615, 784, 785, 786, 787, 848, 849, 850, 851, 864, 865, 866, 867, 868, 869, 870, 871, 912, 913, 914, 915, 928, 929, 930, 931, 932, 933, 934, 935, 944, 945, 946, 947, 948, 949, 950, 951, 952, 953, 954, 955], [276, 532, 596, 612, 616, 617, 788, 852, 868, 872, 873, 916, 932, 936, 937, 948, 952, 953, 956, 957, 958], [277, 533, 597, 613, 617, 618, 789, 853, 869, 873, 874, 917, 933, 937, 938, 949, 953, 954, 957, 958, 959], [277, 278, 533, 534, 597, 598, 613, 614, 617, 618, 619, 789, 790, 853, 854, 869, 870, 873, 874, 875, 917, 918, 933, 934, 937, 938, 939, 949, 950, 953, 954, 955, 957, 958, 959], [277, 278, 279, 533, 534, 535, 597, 598, 599, 613, 614, 615, 617, 618, 619, 789, 790, 791, 853, 854, 855, 869, 870, 871, 873, 874, 875, 917, 918, 919, 933, 934, 935, 937, 938, 939, 949, 950, 951, 953, 954, 955, 957, 958, 959], [280, 536, 600, 616, 620, 621, 792, 856, 872, 876, 877, 920, 936, 940, 941, 952, 956, 957], [281, 537, 601, 617, 621, 622, 793, 857, 873, 877, 878, 921, 937, 941, 942, 953, 957, 958], [282, 538, 602, 618, 622, 623, 794, 858, 874, 878, 879, 922, 938, 942, 943, 954, 958, 959], [282, 283, 538, 539, 602, 603, 618, 619, 622, 623, 794, 795, 858, 859, 874, 875, 878, 879, 922, 923, 938, 939, 942, 943, 954, 955, 958, 959], [284, 540, 604, 620, 796, 860, 876, 924, 940, 956], [285, 541, 605, 621, 797, 861, 877, 925, 941, 957], [286, 542, 606, 622, 798, 862, 878, 926, 942, 958], [287, 543, 607, 623, 799, 863, 879, 927, 943, 959], [288, 544, 608, 624, 628, 629, 800, 864, 880, 884, 885, 928, 944, 948, 949], [288, 289, 544, 545, 608, 609, 624, 625, 628, 629, 630, 800, 801, 864, 865, 880, 881, 884, 885, 886, 928, 929, 944, 945, 948, 949, 950], [288, 289, 290, 544, 545, 546, 608, 609, 610, 624, 625, 626, 628, 629, 630, 631, 800, 801, 802, 864, 865, 866, 880, 881, 882, 884, 885, 886, 887, 928, 929, 930, 944, 945, 946, 948, 949, 950, 951], [288, 289, 290, 291, 544, 545, 546, 547, 608, 609, 610, 611, 624, 625, 626, 627, 628, 629, 630, 631, 800, 801, 802, 803, 864, 865, 866, 867, 880, 881, 882, 883, 884, 885, 886, 887, 928, 929, 930, 931, 944, 945, 946, 947, 948, 949, 950, 951], [292, 548, 612, 628, 632, 633, 804, 868, 884, 888, 889, 932, 948, 952, 953], [293, 549, 613, 629, 633, 634, 805, 869, 885, 889, 890, 933, 949, 953, 954], [293, 294, 549, 550, 613, 614, 629, 630, 633, 634, 635, 805, 806, 869, 870, 885, 886, 889, 890, 891, 933, 934, 949, 950, 953, 954, 955], [293, 294, 295, 549, 550, 551, 613, 614, 615, 629, 630, 631, 633, 634, 635, 805, 806, 807, 869, 870, 871, 885, 886, 887, 889, 890, 891, 933, 934, 935, 949, 950, 951, 953, 954, 955], [296, 552, 616, 632, 636, 637, 808, 872, 888, 892, 893, 936, 952, 956, 957], [297, 553, 617, 633, 637, 638, 809, 873, 889, 893, 894, 937, 953, 957, 958], [298, 554, 618, 634, 638, 639, 810, 874, 890, 894, 895, 938, 954, 958, 959], [298, 299, 554, 555, 618, 619, 634, 635, 638, 639, 810, 811, 874, 875, 890, 891, 894, 895, 938, 939, 954, 955, 958, 959], [300, 556, 620, 636, 812, 876, 892, 940, 956], [301, 557, 621, 637, 813, 877, 893, 941, 957], [302, 558, 622, 638, 814, 878, 894, 942, 958], [303, 559, 623, 639, 815, 879, 895, 943, 959], [304, 560, 624, 816, 880, 944], [304, 305, 560, 561, 624, 625, 816, 817, 880, 881, 944, 945], [304, 305, 306, 560, 561, 562, 624, 625, 626, 816, 817, 818, 880, 881, 882, 944, 945, 946], [304, 305, 306, 307, 560, 561, 562, 563, 624, 625, 626, 627, 816, 817, 818, 819, 880, 881, 882, 883, 944, 945, 946, 947], [308, 564, 628, 820, 884, 948], [309, 565, 629, 821, 885, 949], [309, 310, 565, 566, 629, 630, 821, 822, 885, 886, 949, 950], [309, 310, 311, 565, 566, 567, 629, 630, 631, 821, 822, 823, 885, 886, 887, 949, 950, 951], [312, 568, 632, 824, 888, 952], [313, 569, 633, 825, 889, 953], [314, 570, 634, 826, 890, 954], [314, 315, 570, 571, 634, 635, 826, 827, 890, 891, 954, 955], [316, 572, 636, 828, 892, 956], [317, 573, 637, 829, 893, 957], [318, 574, 638, 830, 894, 958], [319, 575, 639, 831, 895, 959]], [[320, 576, 640, 656, 660, 661, 832, 896, 912, 916, 917, 960, 976, 980, 981, 992, 996, 997, 1000, 1001, 1002], [320, 321, 576, 577, 640, 641, 656, 657, 660, 661, 662, 832, 833, 896, 897, 912, 913, 916, 917, 918, 960, 961, 976, 977, 980, 981, 982, 992, 993, 996, 997, 998, 1000, 1001, 1002, 1003], [320, 321, 322, 576, 577, 578, 640, 641, 642, 656, 657, 658, 660, 661, 662, 663, 832, 833, 834, 896, 897, 898, 912, 913, 914, 916, 917, 918, 919, 960, 961, 962, 976, 977, 978, 980, 981, 982, 983, 992, 993, 994, 996, 997, 998, 999, 1000, 1001, 1002, 1003], [320, 321, 322, 323, 576, 577, 578, 579, 640, 641, 642, 643, 656, 657, 658, 659, 660, 661, 662, 663, 832, 833, 834, 835, 896, 897, 898, 899, 912, 913, 914, 915, 916, 917, 918, 919, 960, 961, 962, 963, 976, 977, 978, 979, 980, 981, 982, 983, 992, 993, 994, 995, 996, 997, 998, 999, 1000, 1001, 1002, 1003], [324, 580, 644, 660, 664, 665, 836, 900, 916, 920, 921, 964, 980, 984, 985, 996, 1000, 1001, 1004, 1005, 1006], [325, 581, 645, 661, 665, 666, 837, 901, 917, 921, 922, 965, 981, 985, 986, 997, 1001, 1002, 1005, 1006, 1007], [325, 326, 581, 582, 645, 646, 661, 662, 665, 666, 667, 837, 838, 901, 902, 917, 918, 921, 922, 923, 965, 966, 981, 982, 985, 986, 987, 997, 998, 1001, 1002, 1003, 1005, 1006, 1007], [325, 326, 327, 581, 582, 583, 645, 646, 647, 661, 662, 663, 665, 666, 667, 837, 838, 839, 901, 902, 903, 917, 918, 919, 921, 922, 923, 965, 966, 967, 981, 982, 983, 985, 986, 987, 997, 998, 999, 1001, 1002, 1003, 1005, 1006, 1007], [328, 584, 648, 664, 668, 669, 840, 904, 920, 924, 925, 968, 984, 988, 989, 1000, 1004, 1005], [329, 585, 649, 665, 669, 670, 841, 905, 921, 925, 926, 969, 985, 989, 990, 1001, 1005, 1006], [330, 586, 650, 666, 670, 671, 842, 906, 922, 926, 927, 970, 986, 990, 991, 1002, 1006, 1007], [330, 331, 586, 587, 650, 651, 666, 667, 670, 671, 842, 843, 906, 907, 922, 923, 926, 927, 970, 971, 986, 987, 990, 991, 1002, 1003, 1006, 1007], [332, 588, 652, 668, 844, 908, 924, 972, 988, 1004], [333, 589, 653, 669, 845, 909, 925, 973, 989, 1005], [334, 590, 654, 670, 846, 910, 926, 974, 990, 1006], [335, 591, 655, 671, 847, 911, 927, 975, 991, 1007], [336, 592, 656, 672, 676, 677, 848, 912, 928, 932, 933, 976, 992, 996, 997, 1008, 1012, 1013, 1016, 1017, 1018], [336, 337, 592, 593, 656, 657, 672, 673, 676, 677, 678, 848, 849, 912, 913, 928, 929, 932, 933, 934, 976, 977, 992, 993, 996, 997, 998, 1008, 1009, 1012, 1013, 1014, 1016, 1017, 1018, 1019], [336, 337, 338, 592, 593, 594, 656, 657, 658, 672, 673, 674, 676, 677, 678, 679, 848, 849, 850, 912, 913, 914, 928, 929, 930, 932, 933, 934, 935, 976, 977, 978, 992, 993, 994, 996, 997, 998, 999, 1008, 1009, 1010, 1012, 1013, 1014, 1015, 1016, 1017, 1018, 1019], [336, 337, 338, 339, 592, 593, 594, 595, 656, 657, 658, 659, 672, 673, 674, 675, 676, 677, 678, 679, 848, 849, 850, 851, 912, 913, 914, 915, 928, 929, 930, 931, 932, 933, 934, 935, 976, 977, 978, 979, 992, 993, 994, 995, 996, 997, 998, 999, 1008, 1009, 1010, 1011, 1012, 1013, 1014, 1015, 1016, 1017, 1018, 1019], [340, 596, 660, 676, 680, 681, 852, 916, 932, 936, 937, 980, 996, 1000, 1001, 1012, 1016, 1017, 1020, 1021, 1022], [341, 597, 661, 677, 681, 682, 853, 917, 933, 937, 938, 981, 997, 1001, 1002, 1013, 1017, 1018, 1021, 1022, 1023], [341, 342, 597, 598, 661, 662, 677, 678, 681, 682, 683, 853, 854, 917, 918, 933, 934, 937, 938, 939, 981, 982, 997, 998, 1001, 1002, 1003, 1013, 1014, 1017, 1018, 1019, 1021, 1022, 1023], [341, 342, 343, 597, 598, 599, 661, 662, 663, 677, 678, 679, 681, 682, 683, 853, 854, 855, 917, 918, 919, 933, 934, 935, 937, 938, 939, 981, 982, 983, 997, 998, 999, 1001, 1002, 1003, 1013, 1014, 1015, 1017, 1018, 1019, 1021, 1022, 1023], [344, 600, 664, 680, 684, 685, 856, 920, 936, 940, 941, 984, 1000, 1004, 1005, 1016, 1020, 1021], [345, 601, 665, 681, 685, 686, 857, 921, 937, 941, 942, 985, 1001, 1005, 1006, 1017, 1021, 1022], [346, 602, 666, 682, 686, 687, 858, 922, 938, 942, 943, 986, 1002, 1006, 1007, 1018, 1022, 1023], [346, 347, 602, 603, 666, 667, 682, 683, 686, 687, 858, 859, 922, 923, 938, 939, 942, 943, 986, 987, 1002, 1003, 1006, 1007, 1018, 1019, 1022, 1023], [348, 604, 668, 684, 860, 924, 940, 988, 1004, 1020], [349, 605, 669, 685, 861, 925, 941, 989, 1005, 1021], [350, 606, 670, 686, 862, 926, 942, 990, 1006, 1022], [351, 607, 671, 687, 863, 927, 943, 991, 1007, 1023], [352, 608, 672, 688, 692, 693, 864, 928, 944, 948, 949, 992, 1008, 1012, 1013], [352, 353, 608, 609, 672, 673, 688, 689, 692, 693, 694, 864, 865, 928, 929, 944, 945, 948, 949, 950, 992, 993, 1008, 1009, 1012, 1013, 1014], [352, 353, 354, 608, 609, 610, 672, 673, 674, 688, 689, 690, 692, 693, 694, 695, 864, 865, 866, 928, 929, 930, 944, 945, 946, 948, 949, 950, 951, 992, 993, 994, 1008, 1009, 1010, 1012, 1013, 1014, 1015], [352, 353, 354, 355, 608, 609, 610, 611, 672, 673, 674, 675, 688, 689, 690, 691, 692, 693, 694, 695, 864, 865, 866, 867, 928, 929, 930, 931, 944, 945, 946, 947, 948, 949, 950, 951, 992, 993, 994, 995, 1008, 1009, 1010, 1011, 1012, 1013, 1014, 1015], [356, 612, 676, 692, 696, 697, 868, 932, 948, 952, 953, 996, 1012, 1016, 1017], [357, 613, 677, 693, 697, 698, 869, 933, 949, 953, 954, 997, 1013, 1017, 1018], [357, 358, 613, 614, 677, 678, 693, 694, 697, 698, 699, 869, 870, 933, 934, 949, 950, 953, 954, 955, 997, 998, 1013, 1014, 1017, 1018, 1019], [357, 358, 359, 613, 614, 615, 677, 678, 679, 693, 694, 695, 697, 698, 699, 869, 870, 871, 933, 934, 935, 949, 950, 951, 953, 954, 955, 997, 998, 999, 1013, 1014, 1015, 1017, 1018, 1019], [360, 616, 680, 696, 700, 701, 872, 936, 952, 956, 957, 1000, 1016, 1020, 1021], [361, 617, 681, 697, 701, 702, 873, 937, 953, 957, 958, 1001, 1017, 1021, 1022], [362, 618, 682, 698, 702, 703, 874, 938, 954, 958, 959, 1002, 1018, 1022, 1023], [362, 363, 618, 619, 682, 683, 698, 699, 702, 703, 874, 875, 938, 939, 954, 955, 958, 959, 1002, 1003, 1018, 1019, 1022, 1023], [364, 620, 684, 700, 876, 940, 956, 1004, 1020], [365, 621, 685, 701, 877, 941, 957, 1005, 1021], [366, 622, 686, 702, 878, 942, 958, 1006, 1022], [367, 623, 687, 703, 879, 943, 959, 1007, 1023], [368, 624, 688, 880, 944, 1008], [368, 369, 624, 625, 688, 689, 880, 881, 944, 945, 1008, 1009], [368, 369, 370, 624, 625, 626, 688, 689, 690, 880, 881, 882, 944, 945, 946, 1008, 1009, 1010], [368, 369, 370, 371, 624, 625, 626, 627, 688, 689, 690, 691, 880, 881, 882, 883, 944, 945, 946, 947, 1008, 1009, 1010, 1011], [372, 628, 692, 884, 948, 1012], [373, 629, 693, 885, 949, 1013], [373, 374, 629, 630, 693, 694, 885, 886, 949, 950, 1013, 1014], [373, 374, 375, 629, 630, 631, 693, 694, 695, 885, 886, 887, 949, 950, 951, 1013, 1014, 1015], [376, 632, 696, 888, 952, 1016], [377, 633, 697, 889, 953, 1017], [378, 634, 698, 890, 954, 1018], [378, 379, 634, 635, 698, 699, 890, 891, 954, 955, 1018, 1019], [380, 636, 700, 892, 956, 1020], [381, 637, 701, 893, 957, 1021], [382, 638, 702, 894, 958, 1022], [383, 639, 703, 895, 959, 1023]], [[384, 640, 704, 720, 724, 725, 896, 960, 976, 980, 981], [384, 385, 640, 641, 704, 705, 720, 721, 724, 725, 726, 896, 897, 960, 961, 976, 977, 980, 981, 982], [384, 385, 386, 640, 641, 642, 704, 705, 706, 720, 721, 722, 724, 725, 726, 727, 896, 897, 898, 960, 961, 962, 976, 977, 978, 980, 981, 982, 983], [384, 385, 386, 387, 640, 641, 642, 643, 704, 705, 706, 707, 720, 721, 722, 723, 724, 725, 726, 727, 896, 897, 898, 899, 960, 961, 962, 963, 976, 977, 978, 979, 980, 981, 982, 983], [388, 644, 708, 724, 728, 729, 900, 964, 980, 984, 985], [389, 645, 709, 725, 729, 730, 901, 965, 981, 985, 986], [389, 390, 645, 646, 709, 710, 725, 726, 729, 730, 731, 901, 902, 965, 966, 981, 982, 985, 986, 987], [389, 390, 391, 645, 646, 647, 709, 710, 711, 725, 726, 727, 729, 730, 731, 901, 902, 903, 965, 966, 967, 981, 982, 983, 985, 986, 987], [392, 648, 712, 728, 732, 733, 904, 968, 984, 988, 989], [393, 649, 713, 729, 733, 734, 905, 969, 985, 989, 990], [394, 650, 714, 730, 734, 735, 906, 970, 986, 990, 991], [394, 395, 650, 651, 714, 715, 730, 731, 734, 735, 906, 907, 970, 971, 986, 987, 990, 991], [396, 652, 716, 732, 908, 972, 988], [397, 653, 717, 733, 909, 973, 989], [398, 654, 718, 734, 910, 974, 990], [399, 655, 719, 735, 911, 975, 991], [400, 656, 720, 736, 740, 741, 912, 976, 992, 996, 997], [400, 401, 656, 657, 720, 721, 736, 737, 740, 741, 742, 912, 913, 976, 977, 992, 993, 996, 997, 998], [400, 401, 402, 656, 657, 658, 720, 721, 722, 736, 737, 738, 740, 741, 742, 743, 912, 913, 914, 976, 977, 978, 992, 993, 994, 996, 997, 998, 999], [400, 401, 402, 403, 656, 657, 658, 659, 720, 721, 722, 723, 736, 737, 738, 739, 740, 741, 742, 743, 912, 913, 914, 915, 976, 977, 978, 979, 992, 993, 994, 995, 996, 997, 998, 999], [404, 660, 724, 740, 744, 745, 916, 980, 996, 1000, 1001], [405, 661, 725, 741, 745, 746, 917, 981, 997, 1001, 1002], [405, 406, 661, 662, 725, 726, 741, 742, 745, 746, 747, 917, 918, 981, 982, 997, 998, 1001, 1002, 1003], [405, 406, 407, 661, 662, 663, 725, 726, 727, 741, 742, 743, 745, 746, 747, 917, 918, 919, 981, 982, 983, 997, 998, 999, 1001, 1002, 1003], [408, 664, 728, 744, 748, 749, 920, 984, 1000, 1004, 1005], [409, 665, 729, 745, 749, 750, 921, 985, 1001, 1005, 1006], [410, 666, 730, 746, 750, 751, 922, 986, 1002, 1006, 1007], [410, 411, 666, 667, 730, 731, 746, 747, 750, 751, 922, 923, 986, 987, 1002, 1003, 1006, 1007], [412, 668, 732, 748, 924, 988, 1004], [413, 669, 733, 749, 925, 989, 1005], [414, 670, 734, 750, 926, 990, 1006], [415, 671, 735, 751, 927, 991, 1007], [416, 672, 736, 752, 756, 757, 928, 992, 1008, 1012, 1013], [416, 417, 672, 673, 736, 737, 752, 753, 756, 757, 758, 928, 929, 992, 993, 1008, 1009, 1012, 1013, 1014], [416, 417, 418, 672, 673, 674, 736, 737, 738, 752, 753, 754, 756, 757, 758, 759, 928, 929, 930, 992, 993, 994, 1008, 1009, 1010, 1012, 1013, 1014, 1015], [416, 417, 418, 419, 672, 673, 674, 675, 736, 737, 738, 739, 752, 753, 754, 755, 756, 757, 758, 759, 928, 929, 930, 931, 992, 993, 994, 995, 1008, 1009, 1010, 1011, 1012, 1013, 1014, 1015], [420, 676, 740, 756, 760, 761, 932, 996, 1012, 1016, 1017], [421, 677, 741, 757, 761, 762, 933, 997, 1013, 1017, 1018], [421, 422, 677, 678, 741, 742, 757, 758, 761, 762, 763, 933, 934, 997, 998, 1013, 1014, 1017, 1018, 1019], [421, 422, 423, 677, 678, 679, 741, 742, 743, 757, 758, 759, 761, 762, 763, 933, 934, 935, 997, 998, 999, 1013, 1014, 1015, 1017, 1018, 1019], [424, 680, 744, 760, 764, 765, 936, 1000, 1016, 1020, 1021], [425, 681, 745, 761, 765, 766, 937, 1001, 1017, 1021, 1022], [426, 682, 746, 762, 766, 767, 938, 1002, 1018, 1022, 1023], [426, 427, 682, 683, 746, 747, 762, 763, 766, 767, 938, 939, 1002, 1003, 1018, 1019, 1022, 1023], [428, 684, 748, 764, 940, 1004, 1020], [429, 685, 749, 765, 941, 1005, 1021], [430, 686, 750, 766, 942, 1006, 1022], [431, 687, 751, 767, 943, 1007, 1023], [432, 688, 752, 944, 1008], [432, 433, 688, 689, 752, 753, 944, 945, 1008, 1009], [432, 433, 434, 688, 689, 690, 752, 753, 754, 944, 945, 946, 1008, 1009, 1010], [432, 433, 434, 435, 688, 689, 690, 691, 752, 753, 754, 755, 944, 945, 946, 947, 1008, 1009, 1010, 1011], [436, 692, 756, 948, 1012], [437, 693, 757, 949, 1013], [437, 438, 693, 694, 757, 758, 949, 950, 1013, 1014], [437, 438, 439, 693, 694, 695, 757, 758, 759, 949, 950, 951, 1013, 1014, 1015], [440, 696, 760, 952, 1016], [441, 697, 761, 953, 1017], [442, 698, 762, 954, 1018], [442, 443, 698, 699, 762, 763, 954, 955, 1018, 1019], [444, 700, 764, 956, 1020], [445, 701, 765, 957, 1021], [446, 702, 766, 958, 1022], [447, 703, 767, 959, 1023]], [[448, 704, 960], [448, 449, 704, 705, 960, 961], [448, 449, 450, 704, 705, 706, 960, 961, 962], [448, 449, 450, 451, 704, 705, 706, 707, 960, 961, 962, 963], [452, 708, 964], [453, 709, 965], [453, 454, 709, 710, 965, 966], [453, 454, 455, 709, 710, 711, 965, 966, 967], [456, 712, 968], [457, 713, 969], [458, 714, 970], [458, 459, 714, 715, 970, 971], [460, 716, 972], [461, 717, 973], [462, 718, 974], [463, 719, 975], [464, 720, 976], [464, 465, 720, 721, 976, 977], [464, 465, 466, 720, 721, 722, 976, 977, 978], [464, 465, 466, 467, 720, 721, 722, 723, 976, 977, 978, 979], [468, 724, 980], [469, 725, 981], [469, 470, 725, 726, 981, 982], [469, 470, 471, 725, 726, 727, 981, 982, 983], [472, 728, 984], [473, 729, 985], [474, 730, 986], [474, 475, 730, 731, 986, 987], [476, 732, 988], [477, 733, 989], [478, 734, 990], [479, 735, 991], [480, 736, 992], [480, 481, 736, 737, 992, 993], [480, 481, 482, 736, 737, 738, 992, 993, 994], [480, 481, 482, 483, 736, 737, 738, 739, 992, 993, 994, 995], [484, 740, 996], [485, 741, 997], [485, 486, 741, 742, 997, 998], [485, 486, 487, 741, 742, 743, 997, 998, 999], [488, 744, 1000], [489, 745, 1001], [490, 746, 1002], [490, 491, 746, 747, 1002, 1003], [492, 748, 1004], [493, 749, 1005], [494, 750, 1006], [495, 751, 1007], [496, 752, 1008], [496, 497, 752, 753, 1008, 1009], [496, 497, 498, 752, 753, 754, 1008, 1009, 1010], [496, 497, 498, 499, 752, 753, 754, 755, 1008, 1009, 1010, 1011], [500, 756, 1012], [501, 757, 1013], [501, 502, 757, 758, 1013, 1014], [501, 502, 503, 757, 758, 759, 1013, 1014, 1015], [504, 760, 1016], [505, 761, 1017], [506, 762, 1018], [506, 507, 762, 763, 1018, 1019], [508, 764, 1020], [509, 765, 1021], [510, 766, 1022], [511, 767, 1023]], [[512, 768, 832, 848, 852, 853], [512, 513, 768, 769, 832, 833, 848, 849, 852, 853, 854], [512, 513, 514, 768, 769, 770, 832, 833, 834, 848, 849, 850, 852, 853, 854, 855], [512, 513, 514, 515, 768, 769, 770, 771, 832, 833, 834, 835, 848, 849, 850, 851, 852, 853, 854, 855], [516, 772, 836, 852, 856, 857], [517, 773, 837, 853, 857, 858], [517, 518, 773, 774, 837, 838, 853, 854, 857, 858, 859], [517, 518, 519, 773, 774, 775, 837, 838, 839, 853, 854, 855, 857, 858, 859], [520, 776, 840, 856, 860, 861], [521, 777, 841, 857, 861, 862], [522, 778, 842, 858, 862, 863], [522, 523, 778, 779, 842, 843, 858, 859, 862, 863], [524, 780, 844, 860], [525, 781, 845, 861], [526, 782, 846, 862], [527, 783, 847, 863], [528, 784, 848, 864, 868, 869], [528, 529, 784, 785, 848, 849, 864, 865, 868, 869, 870], [528, 529, 530, 784, 785, 786, 848, 849, 850, 864, 865, 866, 868, 869, 870, 871], [528, 529, 530, 531, 784, 785, 786, 787, 848, 849, 850, 851, 864, 865, 866, 867, 868, 869, 870, 871], [532, 788, 852, 868, 872, 873], [533, 789, 853, 869, 873, 874], [533, 534, 789, 790, 853, 854, 869, 870, 873, 874, 875], [533, 534, 535, 789, 790, 791, 853, 854, 855, 869, 870, 871, 873, 874, 875], [536, 792, 856, 872, 876, 877], [537, 793, 857, 873, 877, 878], [538, 794, 858, 874, 878, 879], [538, 539, 794, 795, 858, 859, 874, 875, 878, 879], [540, 796, 860, 876], [541, 797, 861, 877], [542, 798, 862, 878], [543, 799, 863, 879], [544, 800, 864, 880, 884, 885], [544, 545, 800, 801, 864, 865, 880, 881, 884, 885, 886], [544, 545, 546, 800, 801, 802, 864, 865, 866, 880, 881, 882, 884, 885, 886, 887], [544, 545, 546, 547, 800, 801, 802, 803, 864, 865, 866, 867, 880, 881, 882, 883, 884, 885, 886, 887], [548, 804, 868, 884, 888, 889], [549, 805, 869, 885, 889, 890], [549, 550, 805, 806, 869, 870, 885, 886, 889, 890, 891], [549, 550, 551, 805, 806, 807, 869, 870, 871, 885, 886, 887, 889, 890, 891], [552, 808, 872, 888, 892, 893], [553, 809, 873, 889, 893, 894], [554, 810, 874, 890, 894, 895], [554, 555, 810, 811, 874, 875, 890, 891, 894, 895], [556, 812, 876, 892], [557, 813, 877, 893], [558, 814, 878, 894], [559, 815, 879, 895], [560, 816, 880], [560, 561, 816, 817, 880, 881], [560, 561, 562, 816, 817, 818, 880, 881, 882], [560, 561, 562, 563, 816, 817, 818, 819, 880, 881, 882, 883], [564, 820, 884], [565, 821, 885], [565, 566, 821, 822, 885, 886], [565, 566, 567, 821, 822, 823, 885, 886, 887], [568, 824, 888], [569, 825, 889], [570, 826, 890], [570, 571, 826, 827, 890, 891], [572, 828, 892], [573, 829, 893], [574, 830, 894], [575, 831, 895]], [[576, 832, 896, 912, 916, 917], [576, 577, 832, 833, 896, 897, 912, 913, 916, 917, 918], [576, 577, 578, 832, 833, 834, 896, 897, 898, 912, 913, 914, 916, 917, 918, 919], [576, 577, 578, 579, 832, 833, 834, 835, 896, 897, 898, 899, 912, 913, 914, 915, 916, 917, 918, 919], [580, 836, 900, 916, 920, 921], [581, 837, 901, 917, 921, 922], [581, 582, 837, 838, 901, 902, 917, 918, 921, 922, 923], [581, 582, 583, 837, 838, 839, 901, 902, 903, 917, 918, 919, 921, 922, 923], [584, 840, 904, 920, 924, 925], [585, 841, 905, 921, 925, 926], [586, 842, 906, 922, 926, 927], [586, 587, 842, 843, 906, 907, 922, 923, 926, 927], [588, 844, 908, 924], [589, 845, 909, 925], [590, 846, 910, 926], [591, 847, 911, 927], [592, 848, 912, 928, 932, 933], [592, 593, 848, 849, 912, 913, 928, 929, 932, 933, 934], [592, 593, 594, 848, 849, 850, 912, 913, 914, 928, 929, 930, 932, 933, 934, 935], [592, 593, 594, 595, 848, 849, 850, 851, 912, 913, 914, 915, 928, 929, 930, 931, 932, 933, 934, 935], [596, 852, 916, 932, 936, 937], [597, 853, 917, 933, 937, 938], [597, 598, 853, 854, 917, 918, 933, 934, 937, 938, 939], [597, 598, 599, 853, 854, 855, 917, 918, 919, 933, 934, 935, 937, 938, 939], [600, 856, 920, 936, 940, 941], [601, 857, 921, 937, 941, 942], [602, 858, 922, 938, 942, 943], [602, 603, 858, 859, 922, 923, 938, 939, 942, 943], [604, 860, 924, 940], [605, 861, 925, 941], [606, 862, 926, 942], [607, 863, 927, 943], [608, 864, 928, 944, 948, 949], [608, 609, 864, 865, 928, 929, 944, 945, 948, 949, 950], [608, 609, 610, 864, 865, 866, 928, 929, 930, 944, 945, 946, 948, 949, 950, 951], [608, 609, 610, 611, 864, 865, 866, 867, 928, 929, 930, 931, 944, 945, 946, 947, 948, 949, 950, 951], [612, 868, 932, 948, 952, 953], [613, 869, 933, 949, 953, 954], [613, 614, 869, 870, 933, 934, 949, 950, 953, 954, 955], [613, 614, 615, 869, 870, 871, 933, 934, 935, 949, 950, 951, 953, 954, 955], [616, 872, 936, 952, 956, 957], [617, 873, 937, 953, 957, 958], [618, 874, 938, 954, 958, 959], [618, 619, 874, 875, 938, 939, 954, 955, 958, 959], [620, 876, 940, 956], [621, 877, 941, 957], [622, 878, 942, 958], [623, 879, 943, 959], [624, 880, 944], [624, 625, 880, 881, 944, 945], [624, 625, 626, 880, 881, 882, 944, 945, 946], [624, 625, 626, 627, 880, 881, 882, 883, 944, 945, 946, 947], [628, 884, 948], [629, 885, 949], [629, 630, 885, 886, 949, 950], [629, 630, 631, 885, 886, 887, 949, 950, 951], [632, 888, 952], [633, 889, 953], [634, 890, 954], [634, 635, 890, 891, 954, 955], [636, 892, 956], [637, 893, 957], [638, 894, 958], [639, 895, 959]], [[640, 896, 960, 976, 980, 981], [640, 641, 896, 897, 960, 961, 976, 977, 980, 981, 982], [640, 641, 642, 896, 897, 898, 960, 961, 962, 976, 977, 978, 980, 981, 982, 983], [640, 641, 642, 643, 896, 897, 898, 899, 960, 961, 962, 963, 976, 977, 978, 979, 980, 981, 982, 983], [644, 900, 964, 980, 984, 985], [645, 901, 965, 981, 985, 986], [645, 646, 901, 902, 965, 966, 981, 982, 985, 986, 987], [645, 646, 647, 901, 902, 903, 965, 966, 967, 981, 982, 983, 985, 986, 987], [648, 904, 968, 984, 988, 989], [649, 905, 969, 985, 989, 990], [650, 906, 970, 986, 990, 991], [650, 651, 906, 907, 970, 971, 986, 987, 990, 991], [652, 908, 972, 988], [653, 909, 973, 989], [654, 910, 974, 990], [655, 911, 975, 991], [656, 912, 976, 992, 996, 997], [656, 657, 912, 913, 976, 977, 992, 993, 996, 997, 998], [656, 657, 658, 912, 913, 914, 976, 977, 978, 992, 993, 994, 996, 997, 998, 999], [656, 657, 658, 659, 912, 913, 914, 915, 976, 977, 978, 979, 992, 993, 994, 995, 996, 997, 998, 999], [660, 916, 980, 996, 1000, 1001], [661, 917, 981, 997, 1001, 1002], [661, 662, 917, 918, 981, 982, 997, 998, 1001, 1002, 1003], [661, 662, 663, 917, 918, 919, 981, 982, 983, 997, 998, 999, 1001, 1002, 1003], [664, 920, 984, 1000, 1004, 1005], [665, 921, 985, 1001, 1005, 1006], [666, 922, 986, 1002, 1006, 1007], [666, 667, 922, 923, 986, 987, 1002, 1003, 1006, 1007], [668, 924, 988, 1004], [669, 925, 989, 1005], [670, 926, 990, 1006], [671, 927, 991, 1007], [672, 928, 992, 1008, 1012, 1013], [672, 673, 928, 929, 992, 993, 1008, 1009, 1012, 1013, 1014], [672, 673, 674, 928, 929, 930, 992, 993, 994, 1008, 1009, 1010, 1012, 1013, 1014, 1015], [672, 673, 674, 675, 928, 929, 930, 931, 992, 993, 994, 995, 1008, 1009, 1010, 1011, 1012, 1013, 1014, 1015], [676, 932, 996, 1012, 1016, 1017], [677, 933, 997, 1013, 1017, 1018], [677, 678, 933, 934, 997, 998, 1013, 1014, 1017, 1018, 1019], [677, 678, 679, 933, 934, 935, 997, 998, 999, 1013, 1014, 1015, 1017, 1018, 1019], [680, 936, 1000, 1016, 1020, 1021], [681, 937, 1001, 1017, 1021, 1022], [682, 938, 1002, 1018, 1022, 1023], [682, 683, 938, 939, 1002, 1003, 1018, 1019, 1022, 1023], [684, 940, 1004, 1020], [685, 941, 1005, 1021], [686, 942, 1006, 1022], [687, 943, 1007, 1023], [688, 944, 1008], [688, 689, 944, 945, 1008, 1009], [688, 689, 690, 944, 945, 946, 1008, 1009, 1010], [688, 689, 690, 691, 944, 945, 946, 947, 1008, 1009, 1010, 1011], [692, 948, 1012], [693, 949, 1013], [693, 694, 949, 950, 1013, 1014], [693, 694, 695, 949, 950, 951, 1013, 1014, 1015], [696, 952, 1016], [697, 953, 1017], [698, 954, 1018], [698, 699, 954, 955, 1018, 1019], [700, 956, 1020], [701, 957, 1021], [702, 958, 1022], [703, 959, 1023]], [[704, 960], [704, 705, 960, 961], [704, 705, 706, 960, 961, 962], [704, 705, 706, 707, 960, 961, 962, 963], [708, 964], [709, 965], [709, 710, 965, 966], [709, 710, 711, 965, 966, 967], [712, 968], [713, 969], [714, 970], [714, 715, 970, 971], [716, 972], [717, 973], [718, 974], [719, 975], [720, 976], [720, 721, 976, 977], [720, 721, 722, 976, 977, 978], [720, 721, 722, 723, 976, 977, 978, 979], [724, 980], [725, 981], [725, 726, 981, 982], [725, 726, 727, 981, 982, 983], [728, 984], [729, 985], [730, 986], [730, 731, 986, 987], [732, 988], [733, 989], [734, 990], [735, 991], [736, 992], [736, 737, 992, 993], [736, 737, 738, 992, 993, 994], [736, 737, 738, 739, 992, 993, 994, 995], [740, 996], [741, 997], [741, 742, 997, 998], [741, 742, 743, 997, 998, 999], [744, 1000], [745, 1001], [746, 1002], [746, 747, 1002, 1003], [748, 1004], [749, 1005], [750, 1006], [751, 1007], [752, 1008], [752, 753, 1008, 1009], [752, 753, 754, 1008, 1009, 1010], [752, 753, 754, 755, 1008, 1009, 1010, 1011], [756, 1012], [757, 1013], [757, 758, 1013, 1014], [757, 758, 759, 1013, 1014, 1015], [760, 1016], [761, 1017], [762, 1018], [762, 763, 1018, 1019], [764, 1020], [765, 1021], [766, 1022], [767, 1023]], [[768], [768, 769], [768, 769, 770], [768, 769, 770, 771], [772], [773], [773, 774], [773, 774, 775], [776], [777], [778], [778, 779], [780], [781], [782], [783], [784], [784, 785], [784, 785, 786], [784, 785, 786, 787], [788], [789], [789, 790], [789, 790, 791], [792], [793], [794], [794, 795], [796], [797], [798], [799], [800], [800, 801], [800, 801, 802], [800, 801, 802, 803], [804], [805], [805, 806], [805, 806, 807], [808], [809], [810], [810, 811], [812], [813], [814], [815], [816], [816, 817], [816, 817, 818], [816, 817, 818, 819], [820], [821], [821, 822], [821, 822, 823], [824], [825], [826], [826, 827], [828], [829], [830], [831]], [[832], [832, 833], [832, 833, 834], [832, 833, 834, 835], [836], [837], [837, 838], [837, 838, 839], [840], [841], [842], [842, 843], [844], [845], [846], [847], [848], [848, 849], [848, 849, 850], [848, 849, 850, 851], [852], [853], [853, 854], [853, 854, 855], [856], [857], [858], [858, 859], [860], [861], [862], [863], [864], [864, 865], [864, 865, 866], [864, 865, 866, 867], [868], [869], [869, 870], [869, 870, 871], [872], [873], [874], [874, 875], [876], [877], [878], [879], [880], [880, 881], [880, 881, 882], [880, 881, 882, 883], [884], [885], [885, 886], [885, 886, 887], [888], [889], [890], [890, 891], [892], [893], [894], [895]], [[896], [896, 897], [896, 897, 898], [896, 897, 898, 899], [900], [901], [901, 902], [901, 902, 903], [904], [905], [906], [906, 907], [908], [909], [910], [911], [912], [912, 913], [912, 913, 914], [912, 913, 914, 915], [916], [917], [917, 918], [917, 918, 919], [920], [921], [922], [922, 923], [924], [925], [926], [927], [928], [928, 929], [928, 929, 930], [928, 929, 930, 931], [932], [933], [933, 934], [933, 934, 935], [936], [937], [938], [938, 939], [940], [941], [942], [943], [944], [944, 945], [944, 945, 946], [944, 945, 946, 947], [948], [949], [949, 950], [949, 950, 951], [952], [953], [954], [954, 955], [956], [957], [958], [959]], [[960], [960, 961], [960, 961, 962], [960, 961, 962, 963], [964], [965], [965, 966], [965, 966, 967], [968], [969], [970], [970, 971], [972], [973], [974], [975], [976], [976, 977], [976, 977, 978], [976, 977, 978, 979], [980], [981], [981, 982], [981, 982, 983], [984], [985], [986], [986, 987], [988], [989], [990], [991], [992], [992, 993], [992, 993, 994], [992, 993, 994, 995], [996], [997], [997, 998], [997, 998, 999], [1000], [1001], [1002], [1002, 1003], [1004], [1005], [1006], [1007], [1008], [1008, 1009], [1008, 1009, 1010], [1008, 1009, 1010, 1011], [1012], [1013], [1013, 1014], [1013, 1014, 1015], [1016], [1017], [1018], [1018, 1019], [1020], [1021], [1022], [1023]]]
abbrev adjLit : List (List ℕ) := adjC.flatten

def Tt : ℕ := 57897452600069728029183167543759469366977561481811458621493420924268564090095
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

def Dg : ℕ := 140
theorem hDg : ∀ l ∈ adjLit, l.length ≤ Dg := by
  intro l hl
  revert l
  decide +kernel
theorem hKb : Dg ^ 7 < 2 ^ 128 := by decide +kernel
theorem hlenA : adjLit.length = N := by decide +kernel

theorem a_iter (n : ℕ) : a n = (iterL adjLit N n).sum := by
  rw [a_eq, sum_V_eq _ RN adjLit hAdj]

def cpf : ℕ → ℕ := fun j => [0, 7, 0, 35, 0, 21, 0, 1].getD j 0
def cnf : ℕ → ℕ := fun j => [1, 0, 21, 0, 35, 0, 7, 0].getD j 0


theorem chkv : (comb N cpf (fun j => unpackN N (iterP adjLit N j)) (List.range (7 + 1)) =
    comb N cnf (fun j => unpackN N (iterP adjLit N j)) (List.range (7 + 1))) ∧
    ∀ i ∈ List.range (7 + 1), (unpackN N (iterP adjLit N i)).sum = [1024, 12311, 63631, 223933, 626416, 1499679, 3204951, 6279401].getD i 0 := by
  decide +kernel

def cc : ℕ → ℤ := fun j => (cpf j : ℤ) - cnf j

theorem hrec (k : ℕ) : (a (k + 7) : ℤ) = (1 : ℤ) * a (k + 0) + (-7 : ℤ) * a (k + 1) + (21 : ℤ) * a (k + 2) + (-35 : ℤ) * a (k + 3) + (35 : ℤ) * a (k + 4) + (-21 : ℤ) * a (k + 5) + (7 : ℤ) * a (k + 6) := by
  have h := rec_total RN 7 cc (h0_of_chkP _ RN adjLit hAdj Dg hDg (by decide +kernel) 7 hKb 7 (by omega) cpf cnf chkv.1) k
  have e0 : cc 0 = -1 := by simp [cc, cpf, cnf]
  have e1 : cc 1 = 7 := by simp [cc, cpf, cnf]
  have e2 : cc 2 = -21 := by simp [cc, cpf, cnf]
  have e3 : cc 3 = 35 := by simp [cc, cpf, cnf]
  have e4 : cc 4 = -35 := by simp [cc, cpf, cnf]
  have e5 : cc 5 = 21 := by simp [cc, cpf, cnf]
  have e6 : cc 6 = -7 := by simp [cc, cpf, cnf]
  have e7 : cc 7 = 1 := by simp [cc, cpf, cnf]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, e0, e1, e2, e3, e4, e5, e6, e7] at h
  simp only [a_eq]
  push_cast
  simp only [Nat.add_zero, zero_mul, zero_add] at h ⊢
  linarith

theorem v1 : a 1 = 12311 := by
  rw [a_iter, ← unpack_iterP adjLit N Dg hlenA hDg (by decide +kernel) 7 hKb 1 (by omega)]
  exact (chkv.2 1 (by simp)).trans (by decide)
theorem v2 : a 2 = 63631 := by
  rw [a_iter, ← unpack_iterP adjLit N Dg hlenA hDg (by decide +kernel) 7 hKb 2 (by omega)]
  exact (chkv.2 2 (by simp)).trans (by decide)
theorem v3 : a 3 = 223933 := by
  rw [a_iter, ← unpack_iterP adjLit N Dg hlenA hDg (by decide +kernel) 7 hKb 3 (by omega)]
  exact (chkv.2 3 (by simp)).trans (by decide)
theorem v4 : a 4 = 626416 := by
  rw [a_iter, ← unpack_iterP adjLit N Dg hlenA hDg (by decide +kernel) 7 hKb 4 (by omega)]
  exact (chkv.2 4 (by simp)).trans (by decide)
theorem v5 : a 5 = 1499679 := by
  rw [a_iter, ← unpack_iterP adjLit N Dg hlenA hDg (by decide +kernel) 7 hKb 5 (by omega)]
  exact (chkv.2 5 (by simp)).trans (by decide)
theorem v6 : a 6 = 3204951 := by
  rw [a_iter, ← unpack_iterP adjLit N Dg hlenA hDg (by decide +kernel) 7 hKb 6 (by omega)]
  exact (chkv.2 6 (by simp)).trans (by decide)
theorem v7 : a 7 = 6279401 := by
  rw [a_iter, ← unpack_iterP adjLit N Dg hlenA hDg (by decide +kernel) 7 hKb 7 (by omega)]
  exact (chkv.2 7 (by simp)).trans (by decide)

theorem closed (n : ℕ) (hn : 1 ≤ n) : (a n : ℚ) = 76 / 9 * (n : ℚ) ^ 6 + 1595 / 12 * (n : ℚ) ^ 5 + 28765 / 36 * (n : ℚ) ^ 4 + 31373 / 12 * (n : ℚ) ^ 3 + 155683 / 36 * (n : ℚ) ^ 2 + 10223 / 3 * (n : ℚ) + 1024 := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    by_cases h : n ≤ 7
    · interval_cases n
      · rw [v1]; norm_num
      · rw [v2]; norm_num
      · rw [v3]; norm_num
      · rw [v4]; norm_num
      · rw [v5]; norm_num
      · rw [v6]; norm_num
      · rw [v7]; norm_num
    · obtain ⟨k, rfl⟩ : ∃ k, n = k + 7 := ⟨n - 7, by omega⟩
      have r : (a (k + 7) : ℚ) = (1 : ℚ) * a (k + 0) + (-7 : ℚ) * a (k + 1) + (21 : ℚ) * a (k + 2) + (-35 : ℚ) * a (k + 3) + (35 : ℚ) * a (k + 4) + (-21 : ℚ) * a (k + 5) + (7 : ℚ) * a (k + 6) := by exact_mod_cast hrec k
      have i0 := ih (k + 0) (by omega) (by omega)
      have i1 := ih (k + 1) (by omega) (by omega)
      have i2 := ih (k + 2) (by omega) (by omega)
      have i3 := ih (k + 3) (by omega) (by omega)
      have i4 := ih (k + 4) (by omega) (by omega)
      have i5 := ih (k + 5) (by omega) (by omega)
      have i6 := ih (k + 6) (by omega) (by omega)
      rw [r, i0, i1, i2, i3, i4, i5, i6]
      push_cast
      ring

theorem gf : PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) = G := by
  unfold G
  apply gf_gen _ 7 7 (fun j => [(1 : ℚ), (-7 : ℚ), (21 : ℚ), (-35 : ℚ), (35 : ℚ), (-21 : ℚ), (7 : ℚ), (-1 : ℚ)].getD j 0) (fun j => [(0 : ℚ), (12311 : ℚ), (-22546 : ℚ), (37047 : ℚ), (-35749 : ℚ), (21160 : ℚ), (-7167 : ℚ), (1024 : ℚ)].getD j 0)
  · simp [Finset.sum_range_succ, map_ofNat PowerSeries.C]
    ring
  · simp [Finset.sum_range_succ, map_ofNat PowerSeries.C]
    ring
  · norm_num
  · intro n hn
    simp only [List.getD_eq_getElem?_getD]
    rcases n with _ | _ | _ | _ | _ | _ | _ | _ | k <;> simp_all
  · intro n
    rcases n with _ | _ | _ | _ | _ | _ | _ | _ | k
    · simp [Finset.sum_range_succ]
    · simp [Finset.sum_range_succ, v1, v2, v3, v4, v5, v6, v7] <;> norm_num
    · simp [Finset.sum_range_succ, v1, v2, v3, v4, v5, v6, v7] <;> norm_num
    · simp [Finset.sum_range_succ, v1, v2, v3, v4, v5, v6, v7] <;> norm_num
    · simp [Finset.sum_range_succ, v1, v2, v3, v4, v5, v6, v7] <;> norm_num
    · simp [Finset.sum_range_succ, v1, v2, v3, v4, v5, v6, v7] <;> norm_num
    · simp [Finset.sum_range_succ, v1, v2, v3, v4, v5, v6, v7] <;> norm_num
    · simp [Finset.sum_range_succ, v1, v2, v3, v4, v5, v6, v7] <;> norm_num
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero]
      have c0 := closed (k + 8) (by omega)
      have c1 := closed (k + 7) (by omega)
      have c2 := closed (k + 6) (by omega)
      have c3 := closed (k + 5) (by omega)
      have c4 := closed (k + 4) (by omega)
      have c5 := closed (k + 3) (by omega)
      have c6 := closed (k + 2) (by omega)
      have c7 := closed (k + 1) (by omega)
      simp [c0, c1, c2, c3, c4, c5, c6, c7]
      ring

theorem recS (n : ℕ) (hn : 8 ≤ n) : (a n : ℤ) = 7 * (a (n - 1) : ℤ) - 21 * (a (n - 2) : ℤ) + 35 * (a (n - 3) : ℤ) - 35 * (a (n - 4) : ℤ) + 21 * (a (n - 5) : ℤ) - 7 * (a (n - 6) : ℤ) + (a (n - 7) : ℤ) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 8 := ⟨n - 8, by omega⟩
  have e1 : k + 8 - 1 = k + 7 := by omega
  have e2 : k + 8 - 2 = k + 6 := by omega
  have e3 : k + 8 - 3 = k + 5 := by omega
  have e4 : k + 8 - 4 = k + 4 := by omega
  have e5 : k + 8 - 5 = k + 3 := by omega
  have e6 : k + 8 - 6 = k + 2 := by omega
  have e7 : k + 8 - 7 = k + 1 := by omega
  rw [e1, e2, e3, e4, e5, e6, e7]
  have h : (a (k + 8) : ℚ) = 7 * (a (k + 7) : ℚ) - 21 * (a (k + 6) : ℚ) + 35 * (a (k + 5) : ℚ) - 35 * (a (k + 4) : ℚ) + 21 * (a (k + 3) : ℚ) - 7 * (a (k + 2) : ℚ) + (a (k + 1) : ℚ) := by
    rw [closed (k + 8) (by omega), closed (k + 7) (by omega), closed (k + 6) (by omega), closed (k + 5) (by omega), closed (k + 4) (by omega), closed (k + 3) (by omega), closed (k + 2) (by omega), closed (k + 1) (by omega)]
    push_cast
    ring_nf
  exact_mod_cast h

end OMA.S_oeis_a250856

theorem OMA.solution : type_of% @OMA.S_oeis_a250856.main := ⟨OMA.S_oeis_a250856.closed, OMA.S_oeis_a250856.gf, OMA.S_oeis_a250856.recS⟩
