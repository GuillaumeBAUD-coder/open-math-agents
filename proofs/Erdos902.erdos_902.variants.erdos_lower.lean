import FormalConjectures.ErdosProblems.«902»

open Finset

namespace OMA

variable {V : Type*} [Fintype V] [DecidableEq V]

noncomputable def indeg (G : Digraph V) (v : V) : ℕ :=
  open Classical in (univ.filter fun x => G.Adj x v).card

theorem two_mul_indeg (G : Digraph V) (hT : G.IsTournament) :
    2 * ∑ v : V, indeg G v = Fintype.card V * (Fintype.card V - 1) := by
  classical
  have hTsum : ∑ v : V, indeg G v =
      ((univ : Finset (V × V)).filter fun p => G.Adj p.1 p.2).card := by
    classical
    simp only [indeg, card_filter]
    rw [Fintype.sum_prod_type_right]
  have hswap : ((univ : Finset (V × V)).filter fun p => G.Adj p.2 p.1).card =
      ((univ : Finset (V × V)).filter fun p => G.Adj p.1 p.2).card := by
    apply card_bij (fun p _ => (p.2, p.1))
    · intro p hp
      rw [mem_filter] at hp ⊢
      exact ⟨mem_univ _, hp.2⟩
    · intro p _ q _ h
      rw [Prod.mk.injEq] at h
      exact Prod.ext h.2 h.1
    · intro q hq
      rw [mem_filter] at hq
      exact ⟨(q.2, q.1), by rw [mem_filter]; exact ⟨mem_univ _, hq.2⟩, rfl⟩
  have hunion : ((univ : Finset (V × V)).filter fun p => G.Adj p.1 p.2) ∪
      ((univ : Finset (V × V)).filter fun p => G.Adj p.2 p.1) = univ.offDiag := by
    ext p
    simp only [mem_union, mem_filter, mem_univ, true_and, mem_offDiag]
    constructor
    · rintro (h | h)
      · exact fun e => hT.1 p.1 (by rw [← e] at h; exact h)
      · exact fun e => hT.1 p.1 (by rw [← e] at h; exact h)
    · intro hne
      by_cases h : G.Adj p.1 p.2
      · exact Or.inl h
      · exact Or.inr (by
          by_contra h'
          exact h ((hT.2 p.1 p.2 hne).2 h'))
  have hdisj : Disjoint ((univ : Finset (V × V)).filter fun p => G.Adj p.1 p.2)
      ((univ : Finset (V × V)).filter fun p => G.Adj p.2 p.1) := by
    rw [disjoint_left]
    intro p hp hq
    rw [mem_filter] at hp hq
    have hne : p.1 ≠ p.2 := fun e => hT.1 p.1 (by have := hp.2; rw [← e] at this; exact this)
    exact (hT.2 p.1 p.2 hne).1 hp.2 hq.2
  have hcard := card_union_of_disjoint hdisj
  rw [hunion, hswap, ← two_mul] at hcard
  rw [offDiag_card, card_univ] at hcard
  rw [hTsum]
  rw [← hcard]
  exact (Nat.mul_sub_one (Fintype.card V) (Fintype.card V)).symm

theorem exists_small_indeg (G : Digraph V) (hT : G.IsTournament) (hV : 0 < Fintype.card V) :
    ∃ ξ : V, indeg G ξ ≤ (Fintype.card V - 1) / 2 := by
  classical
  by_contra h
  push_neg at h
  let t := (Fintype.card V - 1) / 2
  have hge : ∑ v : V, (t + 1) ≤ ∑ v : V, indeg G v :=
    sum_le_sum fun v _ => by
      have hv : t < indeg G v := h v
      omega
  simp only [sum_const, card_univ, smul_eq_mul] at hge
  have h2 := two_mul_indeg G hT
  have hmul : 2 * (Fintype.card V * (t + 1)) ≤ Fintype.card V * (Fintype.card V - 1) := by
    have h2sum : 2 * (Fintype.card V * (t + 1)) ≤ 2 * ∑ v : V, indeg G v :=
      Nat.mul_le_mul_left 2 hge
    simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using h2sum.trans_eq h2
  have hlt : Fintype.card V * (Fintype.card V - 1) < 2 * (Fintype.card V * (t + 1)) := by
    have ht : Fintype.card V - 1 < 2 * (t + 1) := by omega
    have hmul' := Nat.mul_lt_mul_of_pos_left ht hV
    simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hmul'
  omega

theorem host_card_ge : ∀ k {V : Type*} [Fintype V] [DecidableEq V]
    (G : Digraph V), G.IsTournament → Erdos902.HasPropertyS G k →
    k ≤ Fintype.card V → 2 ^ (k + 1) - 1 ≤ Fintype.card V := by
  classical
  intro k
  induction k with
  | zero =>
    intro V _ _ G _ hS _
    have hm : Fintype.card V ≠ 0 := by
      intro h0
      rw [Fintype.card_eq_zero_iff] at h0
      obtain ⟨x, -, -⟩ := hS ∅ (by simp)
      exact h0.elim x
    omega
  | succ n ih =>
    intro V _ _ G hT hS hk
    by_contra hlt
    have hpos : 0 < Fintype.card V := by omega
    obtain ⟨ξ, hξ⟩ := exists_small_indeg G hT hpos
    let I : Finset V := univ.filter fun x => G.Adj x ξ
    have hIξ : ξ ∉ I := by
      simp [I]
      exact hT.1 ξ
    have hIle : I.card ≤ 2 ^ (n + 1) - 2 := by
      have hle : I.card ≤ (Fintype.card V - 1) / 2 := by simpa [indeg] using hξ
      have hm : Fintype.card V + 2 ≤ 2 ^ (n + 2) := by
        have hlt' : Fintype.card V < 2 ^ (n + 2) - 1 := lt_of_not_ge hlt
        have hstep : Fintype.card V + 1 ≤ 2 ^ (n + 2) - 1 := Nat.succ_le_of_lt hlt'
        exact (Nat.le_sub_iff_add_le Nat.one_le_two_pow).mp hstep
      have hdiv : (Fintype.card V - 1) / 2 ≤ (2 ^ (n + 2) - 3) / 2 :=
        Nat.div_le_div_right (by omega)
      have hpow : (2 ^ (n + 2) - 3) / 2 = 2 ^ (n + 1) - 2 := by
        set a := 2 ^ (n + 1)
        have ha : 2 ≤ a := by
          have : (1 : ℕ) ≤ n + 1 := by omega
          have : 2 ^ 1 ≤ 2 ^ (n + 1) := Nat.pow_le_pow_right (by decide) this
          simpa [a] using this
        have htwo : 2 ^ (n + 2) = 2 * a := by
          rw [pow_succ, mul_comm]
        have hrepr : 2 ^ (n + 2) - 3 = 2 * (a - 2) + 1 := by omega
        rw [hrepr, add_comm, Nat.add_mul_div_left 1 (a - 2) (by decide : 0 < 2)]
        simp
      exact le_trans (le_trans hle hdiv) (le_of_eq hpow)
    by_cases hbig : n + 1 ≤ I.card
    · let S := {x : V // x ∈ I}
      letI : Fintype S := Fintype.ofFinset I fun x => by simp
      let G' : Digraph S := ⟨fun a b => G.Adj a.1 b.1⟩
      have hT' : G'.IsTournament := by
        constructor
        · intro v hv
          exact hT.1 v.1 hv
        · intro u v huv
          have hne : u.1 ≠ v.1 := fun h => huv (Subtype.ext h)
          simpa using hT.2 u.1 v.1 hne
      have hS' : Erdos902.HasPropertyS G' n := by
        intro E hE
        let E' : Finset V := E.image Subtype.val
        have hE' : E'.card = n := by
          rw [card_image_of_injective _ Subtype.val_injective, hE]
        have hξE : ξ ∉ E' := by
          intro hmem
          obtain ⟨e, _, he⟩ := mem_image.mp hmem
          exact hIξ (he ▸ e.2)
        let Eξ := insert ξ E'
        have hcard : Eξ.card = n + 1 := by
          rw [card_insert_of_notMem hξE, hE']
        obtain ⟨q, hq, hdom⟩ := hS Eξ hcard
        have hqξ : G.Adj q ξ := hdom ξ (mem_insert_self _ _)
        have hqI : q ∈ I := by simpa [I] using hqξ
        refine ⟨⟨q, hqI⟩, ?_, ?_⟩
        · intro hqE
          exact hq (mem_insert_of_mem (mem_image.mpr ⟨⟨q, hqI⟩, hqE, rfl⟩))
        · intro e he
          exact hdom e.1 (mem_insert_of_mem (mem_image_of_mem _ he))
      have hcardS : Fintype.card S = I.card := Fintype.card_coe I
      have hlow := ih G' hT' hS' (by rw [hcardS]; omega)
      rw [hcardS] at hlow
      omega
    · have hN : I.card ≤ n := by omega
      have hIsub : I ⊆ univ.erase ξ := by
        intro x hx
        refine mem_erase.mpr ⟨?_, mem_univ _⟩
        intro hxξ
        rw [hxξ] at hx
        exact hIξ hx
      have hroom : n - I.card ≤ ((univ.erase ξ) \ I).card := by
        have hinter : I ∩ univ.erase ξ = I := Finset.inter_eq_left.mpr hIsub
        rw [card_sdiff, hinter, card_erase_of_mem (mem_univ _), card_univ]
        omega
      obtain ⟨extra, hextra, hcextra⟩ :=
        exists_subset_card_eq (s := (univ.erase ξ) \ I) (n := n - I.card) hroom
      let W := I ∪ extra
      have hdisj : Disjoint I extra := by
        rw [disjoint_left]
        intro x hxI hxE
        exact (mem_sdiff.mp (hextra hxE)).2 hxI
      have hW : W.card = n := by
        rw [card_union_of_disjoint hdisj, hcextra]
        omega
      have hξW : ξ ∉ W := by
        intro hξmem
        rcases mem_union.mp hξmem with hξI | hξE
        · exact hIξ hξI
        · exact (mem_erase.mp (mem_sdiff.mp (hextra hξE)).1).1 rfl
      let Eset := insert ξ W
      have hE : Eset.card = n + 1 := by rw [card_insert_of_notMem hξW, hW]
      obtain ⟨q, hq, hdom⟩ := hS Eset hE
      have hqI : q ∈ I := by
        have : G.Adj q ξ := hdom ξ (mem_insert_self _ _)
        simpa [I] using this
      exact hq (mem_insert_of_mem (mem_union_left _ hqI))

def trivialTournament : Digraph (Fin 1) := ⟨fun _ _ => False⟩

theorem trivialTournament_ok :
    trivialTournament.IsTournament ∧ Erdos902.HasPropertyS trivialTournament 0 := by
  constructor
  · constructor
    · intro _ hv
      exact hv
    · intro u v huv
      exact (huv (Subsingleton.elim u v)).elim
  · intro E hE
    have hE0 : E = ∅ := Finset.card_eq_zero.mp (by simpa using hE)
    refine ⟨0, by simp [hE0], ?_⟩
    intro e he
    simp [hE0] at he

end OMA

namespace OMACount

open Classical Finset

theorem binom_two_terms (a : ℕ) : ∀ k : ℕ, a ^ (k + 1) + (k + 1) * a ^ k ≤ (a + 1) ^ (k + 1) := by
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
      have expand : (a + 1) * (a ^ (k + 1) + (k + 1) * a ^ k)
          = (a ^ (k + 1 + 1) + (k + 1 + 1) * a ^ (k + 1)) + (k + 1) * a ^ k := by ring
      calc a ^ (k + 1 + 1) + (k + 1 + 1) * a ^ (k + 1)
          ≤ (a + 1) * (a ^ (k + 1) + (k + 1) * a ^ k) := by rw [expand]; exact Nat.le_add_right _ _
        _ ≤ (a + 1) * (a + 1) ^ (k + 1) := Nat.mul_le_mul_left _ ih
        _ = (a + 1) ^ (k + 1 + 1) := by ring

theorem two_mul_pow_le (a : ℕ) : 2 * a ^ (a + 1) ≤ (a + 1) ^ (a + 1) := by
  have h := binom_two_terms a a
  have hle : a ^ (a + 1) ≤ (a + 1) * a ^ a := by
    calc a ^ (a + 1) = a * a ^ a := by ring
      _ ≤ (a + 1) * a ^ a := Nat.mul_le_mul_right _ (Nat.le_succ a)
  omega

theorem pow_block (a u : ℕ) : 2 ^ u * a ^ ((a + 1) * u) ≤ (a + 1) ^ ((a + 1) * u) := by
  have h : (2 * a ^ (a + 1)) ^ u ≤ ((a + 1) ^ (a + 1)) ^ u :=
    Nat.pow_le_pow_left (two_mul_pow_le a) u
  calc 2 ^ u * a ^ ((a + 1) * u) = (2 * a ^ (a + 1)) ^ u := by
        rw [Nat.mul_pow, ← Nat.pow_mul]
    _ ≤ ((a + 1) ^ (a + 1)) ^ u := h
    _ = (a + 1) ^ ((a + 1) * u) := by rw [← Nat.pow_mul]

def M0 (n : ℕ) : ℕ := n + 3 * n ^ 2 * 2 ^ n

theorem M0_sub (n : ℕ) : M0 n - n = 3 * n ^ 2 * 2 ^ n := by simp [M0]

theorem M0_lt_pow (n : ℕ) (hn : 1 ≤ n) : M0 n < 8 ^ n := by
  induction n, hn using Nat.le_induction with
  | base => norm_num [M0]
  | succ n hn ih =>
      have hA : 6 * (n + 1) ^ 2 ≤ 24 * n ^ 2 := by nlinarith [hn]
      have hB : n + 1 ≤ 8 * n := by omega
      have hC : 6 * (n + 1) ^ 2 * 2 ^ n ≤ 24 * n ^ 2 * 2 ^ n := Nat.mul_le_mul_right _ hA
      simp only [M0] at ih ⊢
      calc (n + 1) + 3 * (n + 1) ^ 2 * 2 ^ (n + 1)
          = (n + 1) + 6 * (n + 1) ^ 2 * 2 ^ n := by ring
        _ ≤ 8 * n + 24 * n ^ 2 * 2 ^ n := Nat.add_le_add hB hC
        _ = 8 * (n + 3 * n ^ 2 * 2 ^ n) := by ring
        _ < 8 * 8 ^ n := by exact mul_lt_mul_of_pos_left ih (by norm_num)
        _ = 8 ^ (n + 1) := by ring

theorem n_le_M0_sub (n : ℕ) (hn : 1 ≤ n) : n ≤ M0 n - n := by
  rw [M0_sub]
  have h1 : 1 ≤ 2 ^ n := Nat.one_le_two_pow
  nlinarith [hn]

theorem good_M0 (n : ℕ) (hn : 1 ≤ n) :
    (Nat.choose (M0 n) n) * (2 ^ n - 1) ^ (M0 n - n) < (2 ^ n) ^ (M0 n - n) := by
  obtain ⟨a, ha⟩ : ∃ a, 2 ^ n = a + 1 := ⟨2 ^ n - 1, by
    have : 1 ≤ 2 ^ n := Nat.one_le_two_pow
    omega⟩
  have ha1 : 1 ≤ a := by
    have h2 : 2 ≤ 2 ^ n := by
      calc 2 = 2 ^ 1 := (pow_one 2).symm
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
    omega
  have hAsub : 2 ^ n - 1 = a := by omega
  rw [M0_sub, hAsub]
  set T := 3 * n ^ 2 * 2 ^ n with hT
  rw [ha]
  have htqu : T = (a + 1) * (n * (3 * n)) := by rw [hT, ← ha]; ring
  have hM : M0 n < 2 ^ (3 * n) := by
    have h8 : (2 : ℕ) ^ (3 * n) = 8 ^ n := by rw [Nat.pow_mul]
    rw [h8]; exact M0_lt_pow n hn
  have hMn : (M0 n) ^ n < 2 ^ (n * (3 * n)) := by
    have h1 : (M0 n) ^ n < (2 ^ (3 * n)) ^ n := Nat.pow_lt_pow_left hM (by omega)
    calc (M0 n) ^ n < (2 ^ (3 * n)) ^ n := h1
      _ = 2 ^ ((3 * n) * n) := by rw [← Nat.pow_mul]
      _ = 2 ^ (n * (3 * n)) := by rw [Nat.mul_comm]
  have hblock : 2 ^ (n * (3 * n)) * a ^ T ≤ (a + 1) ^ T := by
    rw [htqu]; exact pow_block a (n * (3 * n))
  have hapos : 0 < a ^ T := pow_pos (by omega) _
  calc Nat.choose (M0 n) n * a ^ T
      ≤ (M0 n) ^ n * a ^ T := Nat.mul_le_mul_right _ (Nat.choose_le_pow _ _)
    _ < 2 ^ (n * (3 * n)) * a ^ T := mul_lt_mul_of_pos_right hMn hapos
    _ ≤ (a + 1) ^ T := hblock

variable {m : ℕ}

abbrev Coord (m : ℕ) := Fin m × Fin m
abbrev Space (m : ℕ) := Coord m → Bool

def blockCoord (a b : Fin m) : Coord m := if a < b then (a, b) else (b, a)

def pat (a b : Fin m) : Bool := decide (a < b)

def beatsOf (c : Space m) (a b : Fin m) : Prop :=
  if a < b then c (a, b) = true else if b < a then c (b, a) = false else False

theorem beats_lt (c : Space m) {a b : Fin m} (h : a < b) :
    beatsOf c a b ↔ c (a, b) = true := by simp [beatsOf, h]

theorem beats_gt (c : Space m) {a b : Fin m} (h : a < b) :
    beatsOf c b a ↔ c (a, b) = false := by simp [beatsOf, lt_asymm h, h]

theorem beats_iff_coord (c : Space m) {a b : Fin m} (hab : a ≠ b) :
    beatsOf c a b ↔ c (blockCoord a b) = pat a b := by
  rcases lt_trichotomy a b with h | h | h
  · simp [blockCoord, pat, h, beats_lt c h]
  · exact absurd h hab
  · simp [blockCoord, pat, lt_asymm h, beats_gt c h]

def Bad (S : Finset (Fin m)) (c : Space m) : Prop :=
  ∀ v ∈ Sᶜ, ∃ s ∈ S, c (blockCoord v s) ≠ pat v s

def unblk (S : Finset (Fin m)) (x : Coord m) : Fin m × Fin m :=
  if x.1 ∈ S then (x.2, x.1) else (x.1, x.2)

theorem unblk_blockCoord {S : Finset (Fin m)} {v s : Fin m} (hv : v ∉ S) (hs : s ∈ S) :
    unblk S (blockCoord v s) = (v, s) := by
  by_cases h : v < s <;> simp [unblk, blockCoord, h, hv, hs]

def Blk (S : Finset (Fin m)) : Finset (Coord m) :=
  (Sᶜ ×ˢ S).image (fun p => blockCoord p.1 p.2)

theorem blk_injOn (S : Finset (Fin m)) :
    Set.InjOn (fun p : Fin m × Fin m => blockCoord p.1 p.2) ↑(Sᶜ ×ˢ S) := by
  rintro ⟨v, s⟩ hp ⟨v', s'⟩ hq hEq
  simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe, Finset.mem_compl] at hp hq
  have hcong := congrArg (unblk S) hEq
  rwa [unblk_blockCoord hp.1 hp.2, unblk_blockCoord hq.1 hq.2] at hcong

theorem blk_card (S : Finset (Fin m)) : (Blk S).card = (m - S.card) * S.card := by
  rw [Blk, Finset.card_image_of_injOn (blk_injOn S), Finset.card_product, Finset.card_compl,
    Fintype.card_fin]

def patRow (S : Finset (Fin m)) (v : Fin m) : {s // s ∈ S} → Bool := fun s => pat v s.1

abbrev Tgt (S : Finset (Fin m)) : Type :=
  ((v : {x // x ∈ Sᶜ}) → {g : {s // s ∈ S} → Bool // g ≠ patRow S v.1}) ×
    ({x : Coord m // x ∉ Blk S} → Bool)

def enc (S : Finset (Fin m)) (c : {c : Space m // Bad S c}) : Tgt S :=
  (fun v => ⟨fun s => c.1 (blockCoord v.1 s.1), by
      obtain ⟨s, hs, hne⟩ := c.2 v.1 v.2
      intro hEq
      exact hne (congrFun hEq ⟨s, hs⟩)⟩,
    fun x => c.1 x.1)

theorem enc_injective (S : Finset (Fin m)) : Function.Injective (enc S) := by
  intro c c' h
  apply Subtype.ext
  funext x
  by_cases hx : x ∈ Blk S
  · obtain ⟨p, hp, hpx⟩ := Finset.mem_image.mp hx
    simp only [Finset.mem_product] at hp
    have h1 := congrFun (congrArg Prod.fst h) ⟨p.1, hp.1⟩
    have h2 := congrFun (congrArg Subtype.val h1) ⟨p.2, hp.2⟩
    simpa [enc, hpx] using h2
  · exact congrFun (congrArg Prod.snd h) ⟨x, hx⟩

theorem card_row (S : Finset (Fin m)) (v : Fin m) :
    Fintype.card {g : {s // s ∈ S} → Bool // g ≠ patRow S v} = 2 ^ S.card - 1 := by
  have h1 : Fintype.card ({s // s ∈ S} → Bool) = 2 ^ S.card := by
    simp [Fintype.card_fun, Fintype.card_coe]
  have h2 := Fintype.card_subtype_compl (fun g : {s // s ∈ S} → Bool => g = patRow S v)
  simpa [h1, Fintype.card_subtype_eq, Ne] using h2

theorem card_tgt (S : Finset (Fin m)) :
    Fintype.card (Tgt S)
      = (2 ^ S.card - 1) ^ (m - S.card) * 2 ^ (m * m - (m - S.card) * S.card) := by
  have hcompl : Fintype.card {x : Coord m // x ∉ Blk S} = m * m - (m - S.card) * S.card := by
    rw [Fintype.card_subtype_compl]
    simp [Fintype.card_coe, blk_card]
  rw [Fintype.card_prod, Fintype.card_pi, Fintype.card_fun, hcompl]
  simp [card_row, Finset.prod_const, Fintype.card_coe, Finset.card_compl]

theorem card_bad_le (S : Finset (Fin m)) :
    (univ.filter (Bad S)).card
      ≤ (2 ^ S.card - 1) ^ (m - S.card) * 2 ^ (m * m - (m - S.card) * S.card) := by
  have h := Fintype.card_le_of_injective (enc S) (enc_injective S)
  rw [Fintype.card_subtype, card_tgt] at h
  exact h

theorem exists_dominating (n : ℕ)
    (hlt : (Nat.choose m n) * ((2 ^ n - 1) ^ (m - n) * 2 ^ (m * m - (m - n) * n)) < 2 ^ (m * m)) :
    ∃ c : Space m, ∀ S : Finset (Fin m), S.card = n → ∃ v, v ∉ S ∧ ∀ s ∈ S, beatsOf c v s := by
  by_contra hcon
  push_neg at hcon
  have hcover : (univ : Finset (Space m)) ⊆
      ((univ : Finset (Fin m)).powersetCard n).biUnion (fun S => univ.filter (Bad S)) := by
    intro c _
    obtain ⟨S, hS, hbad⟩ := hcon c
    refine Finset.mem_biUnion.mpr ⟨S, Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, hS⟩, ?_⟩
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    intro v hv
    have hvS : v ∉ S := Finset.mem_compl.mp hv
    obtain ⟨s, hs, hns⟩ := hbad v hvS
    refine ⟨s, hs, ?_⟩
    intro hEq
    have hne : v ≠ s := by rintro rfl; exact hvS hs
    exact hns ((beats_iff_coord c hne).mpr hEq)
  have h1 : (2 : ℕ) ^ (m * m) ≤
      ∑ S ∈ (univ : Finset (Fin m)).powersetCard n, (univ.filter (Bad S)).card := by
    have hcard : (univ : Finset (Space m)).card = 2 ^ (m * m) := by
      simp [Finset.card_univ, Fintype.card_fun, Fintype.card_prod]
    calc (2 : ℕ) ^ (m * m) = (univ : Finset (Space m)).card := hcard.symm
      _ ≤ _ := le_trans (Finset.card_le_card hcover) Finset.card_biUnion_le
  have h2 : ∑ S ∈ (univ : Finset (Fin m)).powersetCard n, (univ.filter (Bad S)).card
      ≤ (Nat.choose m n) * ((2 ^ n - 1) ^ (m - n) * 2 ^ (m * m - (m - n) * n)) := by
    calc ∑ S ∈ (univ : Finset (Fin m)).powersetCard n, (univ.filter (Bad S)).card
        ≤ ∑ _S ∈ (univ : Finset (Fin m)).powersetCard n,
            ((2 ^ n - 1) ^ (m - n) * 2 ^ (m * m - (m - n) * n)) := by
          refine Finset.sum_le_sum ?_
          intro S hSmem
          have hSc : S.card = n := (Finset.mem_powersetCard.mp hSmem).2
          simpa [hSc] using card_bad_le S
      _ = _ := by
          rw [Finset.sum_const, Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin,
            smul_eq_mul]
  omega

theorem beatsOf_tournament (c : Space m) : (⟨beatsOf c⟩ : Digraph (Fin m)).IsTournament := by
  constructor
  · intro v hv
    change beatsOf c v v at hv
    simp [beatsOf] at hv
  · intro u v huv
    constructor
    · intro hab hba
      change beatsOf c u v at hab
      change beatsOf c v u at hba
      rcases lt_trichotomy u v with h | h | h
      · rw [beats_lt c h] at hab
        rw [beats_gt c h] at hba
        simp [hab] at hba
      · exact huv h
      · rw [beats_gt c h] at hab
        rw [beats_lt c h] at hba
        simp [hba] at hab
    · intro hba
      change ¬ beatsOf c v u at hba
      rcases lt_trichotomy u v with h | h | h
      · cases hc : c (u, v)
        · exact (hba ((beats_gt c h).mpr hc)).elim
        · exact (beats_lt c h).mpr hc
      · exact (huv h).elim
      · cases hc : c (v, u)
        · exact (beats_gt c h).mpr hc
        · exact (hba ((beats_lt c h).mpr hc)).elim

theorem exists_host (n : ℕ) (hn : 1 ≤ n) :
    ∃ G : Digraph (Fin (M0 n)), G.IsTournament ∧ Erdos902.HasPropertyS G n := by
  have hMM : (M0 n - n) * n ≤ M0 n * M0 n := Nat.mul_le_mul (Nat.sub_le _ _) (by simp [M0])
  have hsplit : (2 : ℕ) ^ (M0 n * M0 n) =
      2 ^ ((M0 n - n) * n) * 2 ^ (M0 n * M0 n - (M0 n - n) * n) := by
    rw [← pow_add, Nat.add_sub_cancel' hMM]
  have hpos : 0 < (2 : ℕ) ^ (M0 n * M0 n - (M0 n - n) * n) := pow_pos (by norm_num) _
  have hlt : (Nat.choose (M0 n) n) *
      ((2 ^ n - 1) ^ (M0 n - n) * 2 ^ (M0 n * M0 n - (M0 n - n) * n)) < 2 ^ (M0 n * M0 n) := by
    rw [hsplit, ← Nat.mul_assoc]
    refine mul_lt_mul_of_pos_right ?_ hpos
    calc (Nat.choose (M0 n) n) * (2 ^ n - 1) ^ (M0 n - n) < (2 ^ n) ^ (M0 n - n) := good_M0 n hn
      _ = 2 ^ ((M0 n - n) * n) := by rw [← pow_mul, Nat.mul_comm]
  obtain ⟨c, hc⟩ := exists_dominating (m := M0 n) n hlt
  refine ⟨⟨beatsOf c⟩, beatsOf_tournament c, ?_⟩
  intro E hE
  obtain ⟨v, hv, hbeats⟩ := hc E hE
  exact ⟨v, hv, hbeats⟩

end OMACount

theorem OMA.solution : type_of% @Erdos902.erdos_902.variants.erdos_lower := by
  intro n
  let S : Set ℕ :=
    {m | n ≤ m ∧ ∃ G : Digraph (Fin m), G.IsTournament ∧ Erdos902.HasPropertyS G n}
  have hmem : ∀ m ∈ S, 2 ^ (n + 1) - 1 ≤ m := by
    intro m hm
    obtain ⟨hmn, G, hT, hS⟩ := hm
    simpa using OMA.host_card_ge n G hT hS (by simpa using hmn)
  have hne : S.Nonempty := by
    cases n with
    | zero =>
      exact ⟨1, by omega, OMA.trivialTournament, OMA.trivialTournament_ok.1,
        OMA.trivialTournament_ok.2⟩
    | succ k =>
      obtain ⟨G, hT, hS⟩ := OMACount.exists_host (k + 1) (Nat.succ_pos k)
      exact ⟨OMACount.M0 (k + 1), by simp [OMACount.M0], G, hT, hS⟩
  unfold Erdos902.f
  exact le_csInf hne hmem
