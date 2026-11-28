import OMAStatements.S_wp_teschner_s_bondage_number_conjecture

/-!
Teschner's bondage number conjecture is false: the 18-vertex cubic graph of Yousof Yavari,
*A Counterexample to Teschner's Bondage-Number Conjecture*, arXiv:2609.04257 (2026).
It has domination number at least 6, and after deleting any 4 = ⌊3Δ/2⌋ edges some 6-vertex set
still dominates. Both facts are checked by small search trees on bitmasks.
-/

open OMA.S_wp_teschner_s_bondage_number_conjecture SimpleGraph

namespace TeschnerCounter

def es : List (Fin 18 × Fin 18) := [(0, 6), (0, 10), (0, 16), (1, 8), (1, 11), (1, 12), (2, 4), (2, 5), (2, 13), (3, 4), (3, 5), (3, 9), (4, 16), (5, 11), (6, 7), (6, 13), (7, 8), (7, 14), (8, 13), (9, 10), (9, 14), (10, 15), (11, 15), (12, 15), (12, 17), (14, 17), (16, 17)]

def e (i : Fin 27) : Fin 18 × Fin 18 := es.getD i.val (0, 0)

def G : SimpleGraph (Fin 18) where
  Adj a b := (a, b) ∈ es ∨ (b, a) ∈ es
  symm := ⟨fun _ _ h => Or.symm h⟩
  loopless := ⟨fun a h => by
    have key : ∀ a : Fin 18, (a, a) ∉ es := by decide +kernel
    exact h.elim (key a) (key a)⟩

instance : DecidableRel G.Adj := fun a b =>
  inferInstanceAs (Decidable ((a, b) ∈ es ∨ (b, a) ∈ es))

/-- closed neighbourhoods as bitmasks -/
def nbl : List ℕ := [66625, 6402, 8244, 568, 65564, 2092, 8385, 16832, 8578, 17928, 34305, 34850, 167938, 8516, 148096, 39936, 196625, 217088]

def nb (u : Fin 18) : ℕ := nbl.getD u.val 0

lemma nb_spec : ∀ u v : Fin 18, (nb u).testBit v.val = true ↔ v = u ∨ G.Adj v u := by decide +kernel

def dom : ℕ → ℕ → Bool
  | k, cov =>
    match (List.finRange 18).find? (fun v => !cov.testBit v.val) with
    | none => true
    | some v =>
      match k with
      | 0 => false
      | k + 1 => (List.finRange 18).any fun u => (nb u).testBit v.val && dom k (cov ||| nb u)

lemma dom_sound (k : ℕ) : ∀ (cov : ℕ) (D : Finset (Fin 18)), D.card ≤ k →
    (∀ v : Fin 18, cov.testBit v.val = true ∨ v ∈ D ∨ ∃ w ∈ D, G.Adj v w) → dom k cov = true := by
  induction k with
  | zero =>
    intro cov D hD h
    have hD0 : D = ∅ := Finset.card_eq_zero.mp (by omega)
    unfold dom
    split
    · rfl
    · next v hv =>
      have hb := List.find?_some hv
      rcases h v with h1 | h1 | ⟨w, hw, _⟩
      · simp [h1] at hb
      · simp [hD0] at h1
      · simp [hD0] at hw
  | succ k ih =>
    intro cov D hD h
    unfold dom
    split
    · rfl
    · next v hv =>
      have hb := List.find?_some hv
      obtain ⟨u, hu, huv⟩ : ∃ u ∈ D, v = u ∨ G.Adj v u := by
        rcases h v with h1 | h1 | ⟨w, hw, ha⟩
        · simp [h1] at hb
        · exact ⟨v, h1, Or.inl rfl⟩
        · exact ⟨w, hw, Or.inr ha⟩
      refine List.any_eq_true.mpr ⟨u, List.mem_finRange u, ?_⟩
      rw [Bool.and_eq_true]
      refine ⟨(nb_spec u v).mpr huv, ih _ (D.erase u) ?_ fun x => ?_⟩
      · rw [Finset.card_erase_of_mem hu]; omega
      · rw [Nat.testBit_or, Bool.or_eq_true]
        rcases h x with h1 | h1 | ⟨w, hw, ha⟩
        · exact Or.inl (Or.inl h1)
        · by_cases hx : x = u
          · exact Or.inl (Or.inr ((nb_spec u x).mpr (Or.inl hx)))
          · exact Or.inr (Or.inl (Finset.mem_erase.mpr ⟨hx, h1⟩))
        · by_cases hwu : w = u
          · exact Or.inl (Or.inr ((nb_spec u x).mpr (Or.inr (hwu ▸ ha))))
          · exact Or.inr (Or.inr ⟨w, Finset.mem_erase.mpr ⟨hwu, hw⟩, ha⟩)

lemma no_five : dom 5 0 = false := by decide +kernel

/-- (dominating set as a bitmask, for each outside vertex a mask of edges into the set) -/
def T : List (ℕ × List ℕ) := [
  (4239, [2048, 2, 256, 131072, 8388608, 4, 16777216, 16, 576, 16385, 1152, 65544]),
  (17423, [1, 131072, 32, 256, 2097152, 8, 4, 33554432, 16, 576, 1152, 1574912]),
  (7568, [512, 64, 2, 8192, 16384, 524288, 262144, 131072, 4096, 16777216, 14680064, 56]),
  (91170, [1024, 4096, 32768, 131072, 32, 2097152, 384, 1572864, 6, 262152, 100663296, 8208]),
  (132174, [16384, 33554432, 8, 2097152, 67108864, 16, 576, 1152, 3, 526336, 16777248, 33024]),
  (4773, [32, 64, 65536, 8192, 256, 8388608, 4, 16777216, 3072, 16385, 524290, 1179648]),
  (26635, [256, 512, 131072, 2, 32, 4194304, 4, 33554432, 32769, 9216, 1050624, 262152]),
  (59401, [256, 512, 131072, 262144, 8388608, 4, 33554432, 16, 32769, 9216, 1050624, 2097154]),
  (59409, [512, 8192, 131072, 262144, 1048576, 8388608, 33554432, 16, 320, 32769, 2097154, 4100]),
  (17494, [512, 128, 32, 2097152, 8, 4096, 33554432, 16, 147456, 3, 1572864, 33024]),
  (57609, [256, 512, 1024, 4194304, 8, 8388608, 4, 33554432, 32769, 196608, 1050624, 2097154]),
  (4901, [64, 1, 65536, 8192, 1048576, 8388608, 4, 16777216, 3072, 524290, 262400, 40]),
  (6929, [64, 8192, 1, 65536, 262144, 1048576, 16777216, 2560, 524290, 12582912, 4100, 56]),
  (4905, [512, 128, 1, 65536, 8192, 262144, 1048576, 8388608, 4, 16777216, 524290, 40]),
  (4913, [65536, 1, 8192, 262144, 1048576, 8388608, 16777216, 192, 524290, 40, 4100, 3584]),
  (140426, [256, 512, 2, 1024, 2097152, 67108864, 16, 49152, 526336, 16777248, 33685504, 327688]),
  (4694, [1, 128, 16384, 524288, 1048576, 8388608, 8, 4096, 16777216, 16, 2560, 33024]),
  (18515, [64, 512, 8192, 1048576, 2, 32, 32768, 8, 4194304, 33554432, 147456, 4100]),
  (70433, [4096, 128, 1, 65536, 8192, 262144, 1048576, 8388608, 3072, 524290, 40, 83886080]),
  (83042, [128, 1024, 4096, 32, 32768, 8, 2097152, 147456, 1572864, 100663296, 8208, 7]),
  (133905, [64, 8192, 1, 65536, 16777216, 262144, 4194304, 2560, 524290, 34603008, 24, 67112964]),
  (173320, [256, 512, 2, 1024, 32768, 65536, 4194304, 8, 33554432, 67108864, 526336, 25165824]),
  (30729, [256, 512, 131072, 262144, 2, 4, 32769, 9216, 1050624, 12582912, 50331648, 48]),
  (132238, [16384, 2, 256, 2097152, 67108864, 16, 576, 1152, 526336, 16777248, 33685504, 65544]),
  (57355, [256, 512, 131072, 1024, 4, 33554432, 32769, 1050624, 2097154, 8388640, 262152, 4194320]),
  (49421, [1, 4194304, 8388608, 8, 4, 33554432, 576, 1152, 196608, 1050624, 2097154, 262400]),
  (26643, [512, 131072, 8192, 1048576, 2, 32, 4194304, 33554432, 320, 32769, 262152, 4100]),
  (66786, [128, 1024, 4096, 524288, 32, 32768, 131072, 2097152, 67108864, 65544, 8208, 7]),
  (18447, [1, 131072, 2, 32, 256, 8, 4194304, 4, 33554432, 576, 1050624, 9344]),
  (19538, [64, 512, 8192, 32, 32768, 8, 4096, 33554432, 3, 147456, 1572864, 6291456]),
  (20773, [1024, 64, 1, 1048576, 2, 8192, 8388608, 4, 196608, 262400, 40, 50331648]),
  (91146, [256, 32768, 1024, 131072, 32, 2097152, 16, 4608, 6, 262152, 100663296, 1574912]),
  (132246, [512, 16384, 2, 128, 524288, 256, 2097152, 16, 16777248, 33685504, 65544, 67112960]),
  (66702, [16384, 32, 256, 131072, 2097152, 67108864, 16, 1152, 526336, 6, 65544, 4672]),
  (49457, [1, 1048576, 8388608, 8, 262144, 33554432, 1536, 196608, 192, 2097154, 4202496, 4100]),
  (99232, [4096, 128, 16384, 4, 8388608, 8, 262144, 67108864, 3072, 2621440, 4202496, 1179648]),
  (99140, [2048, 128, 4194304, 8388608, 8, 1048576, 67108864, 4160, 81920, 2621440, 5, 295168]),
  (6789, [2048, 64, 65536, 256, 4, 16777216, 8320, 16385, 524290, 1179648, 12582912, 48]),
  (133765, [2048, 64, 65536, 16777216, 256, 4194304, 16, 8320, 16385, 524290, 67108868, 34734080]),
  (95264, [32, 1024, 4096, 32768, 131072, 262144, 8192, 384, 6, 1572864, 10485760, 117440512]),
  (172297, [256, 512, 1024, 65536, 2048, 4194304, 8, 33554432, 32769, 2097154, 25165824, 67108868]),
  (4743, [2048, 64, 128, 256, 8388608, 4, 16777216, 16, 16385, 524290, 1179648, 65544]),
  (140362, [256, 512, 16384, 1024, 33554432, 2097152, 67108864, 16, 3, 526336, 16777248, 262152]),
  (72324, [2048, 16384, 4, 65536, 524288, 256, 4160, 8320, 1179648, 12582912, 83886080, 48]),
  (142408, [256, 512, 16384, 262144, 16777216, 33554432, 67108864, 16, 9216, 3, 526336, 6291456]),
  (74914, [1024, 4096, 524288, 32, 131072, 2097152, 67108864, 384, 49152, 6, 8208, 327688]),
  (49671, [2048, 1, 64, 128, 131072, 256, 8, 4, 33554432, 8388640, 4194320, 2621442]),
  (133956, [64, 1, 2048, 524288, 16777216, 4194304, 67108864, 8320, 81920, 34603008, 24, 295168]),
  (70214, [2048, 16384, 128, 524288, 1048576, 8, 8388608, 16, 4160, 5, 33024, 83886080]),
  (164613, [2048, 64, 128, 1, 65536, 4194304, 8, 25165824, 262400, 34603008, 67108868, 2621442]),
  (133389, [1, 65536, 2048, 2, 16777216, 33554432, 4194304, 576, 262400, 67108868, 24, 9344]),
  (68166, [2048, 16384, 524288, 32, 8, 1048576, 4194304, 67108864, 8320, 4160, 5, 33024]),
  (4698, [64, 1, 16384, 1024, 524288, 32768, 1048576, 8388608, 8, 4096, 16777216, 16]),
  (6917, [2048, 64, 1, 65536, 1048576, 4, 16777216, 8320, 524290, 262400, 12582912, 56]),
  (4329, [32, 512, 128, 65536, 2048, 2, 8192, 32768, 131072, 8388608, 4, 16777216]),
  (22801, [512, 64, 8192, 1, 1048576, 2, 262144, 196608, 12582912, 4100, 50331648, 56]),
  (15504, [512, 2, 8192, 524288, 131072, 4096, 16777216, 320, 49152, 327680, 48, 14680064]),
  (122914, [1024, 4096, 32768, 4, 131072, 1048576, 2097152, 384, 262152, 8388640, 100663296, 4202512]),
  (142480, [512, 2, 8192, 524288, 16777216, 16, 320, 49152, 327680, 33685504, 6291456, 67112960]),
  (164137, [512, 128, 1, 65536, 2048, 8, 262144, 33554432, 2097154, 4202496, 25165824, 67108868]),
  (123144, [256, 1024, 32768, 4, 2097152, 8, 4194304, 8388608, 4608, 196608, 1050624, 100663296]),
  (76418, [256, 2048, 4096, 8192, 4, 524288, 32, 4194304, 67108864, 49152, 1179648, 327688]),
  (20777, [512, 128, 1, 2, 8192, 262144, 8388608, 4, 196608, 1050624, 40, 50331648]),
  (132262, [1024, 16384, 2, 64, 524288, 256, 2097152, 67108864, 16777248, 33685504, 65544, 8208]),
  (31760, [512, 2, 8192, 32768, 131072, 262144, 4096, 320, 1572864, 50331648, 48, 14680064]),
  (98886, [2048, 16384, 128, 8, 1048576, 67108864, 4160, 2621440, 5, 8388640, 33024, 4194320]),
  (7316, [512, 2, 16384, 65536, 524288, 256, 131072, 4096, 16777216, 8320, 48, 14680064]),
  (132401, [65536, 1, 524288, 8192, 16777216, 262144, 8, 33554432, 2097152, 1536, 192, 67112964]),
  (17522, [32, 32768, 2097152, 8, 4096, 33554432, 192, 1536, 147456, 3, 1572864, 8208]),
  (70820, [32, 1024, 16384, 65536, 524288, 8192, 256, 131072, 4160, 6, 10485760, 83886080]),
  (133714, [64, 1, 16384, 8192, 524288, 32768, 8, 4194304, 2560, 16777248, 34603008, 67112960]),
  (98446, [16384, 2048, 4, 2097152, 256, 131072, 67108864, 1152, 8388640, 65544, 4194320, 4672]),
  (28721, [32, 131072, 262144, 1048576, 2, 8192, 8388608, 1536, 32769, 4100, 50331648, 448]),
  (132210, [16384, 524288, 32768, 33554432, 8, 2097152, 192, 1536, 3, 16777248, 67112960, 8208]),
  (132452, [1024, 64, 524288, 8192, 16777216, 8, 33554432, 2097152, 67108864, 81920, 3, 295168]),
  (134480, [64, 512, 8192, 524288, 16777216, 33554432, 3, 81920, 294912, 6291456, 67112960, 24]),
  (4722, [1, 16384, 524288, 32768, 1048576, 8388608, 8, 4096, 16777216, 192, 8208, 3584]),
  (25650, [2, 131072, 32768, 32, 2097152, 4096, 33554432, 1536, 1572864, 262152, 8208, 448]),
  (4976, [1, 524288, 8192, 1048576, 8388608, 4096, 16777216, 81920, 192, 294912, 40, 3584])]

def set6 (d : ℕ) : Finset (Fin 18) := Finset.univ.filter fun v => d.testBit v.val

def Good (t : ℕ × List ℕ) : Prop :=
  (set6 t.1).card = 6 ∧
  (∀ x : Fin 18, x ∈ set6 t.1 ∨ ∃ B ∈ t.2, ∀ i : Fin 27, B.testBit i.val = true →
    ((e i).1 = x ∧ (e i).2 ∈ set6 t.1) ∨ ((e i).2 = x ∧ (e i).1 ∈ set6 t.1)) ∧
  ∀ B ∈ t.2, 0 < B

instance (t) : Decidable (Good t) := by unfold Good; infer_instance

set_option maxRecDepth 100000 in
lemma T_good : ∀ t ∈ T, Good t := by decide +kernel

def cnt (S : ℕ) : ℕ := ((List.finRange 27).filter fun i => S.testBit i.val).length

def chk : ℕ → ℕ → Bool
  | 0, _ => false
  | n + 1, S =>
    match T.find? (fun t => t.2.all fun B => (B &&& S) != B) with
    | none => false
    | some t => t.2.all fun B => decide (4 < cnt (S ||| B)) || chk n (S ||| B)

lemma e_inj : Function.Injective fun i : Fin 27 => s((e i).1, (e i).2) := by
  unfold Function.Injective; decide +kernel

lemma e_adj : ∀ i : Fin 27, G.Adj (e i).1 (e i).2 := by decide +kernel

lemma chk_sound (F : Finset (Sym2 (Fin 18))) (hF : F.card ≤ 4) (n : ℕ) :
    ∀ S : ℕ, chk n S = true → (∀ i : Fin 27, S.testBit i.val = true → s((e i).1, (e i).2) ∈ F) →
      ∃ D : Finset (Fin 18), IsDominatingSet (G.deleteEdges (F : Set (Sym2 (Fin 18)))) D ∧
        D.card = 6 := by
  induction n with
  | zero => intro S h; simp [chk] at h
  | succ n ih =>
    intro S h hS
    unfold chk at h
    split at h
    · simp at h
    · next t ht =>
      obtain ⟨hc, hx, hB⟩ := T_good t (List.mem_of_find?_eq_some ht)
      by_cases hs : ∀ B ∈ t.2, ∃ i : Fin 27, B.testBit i.val = true ∧ s((e i).1, (e i).2) ∉ F
      · refine ⟨set6 t.1, fun x => ?_, hc⟩
        rcases hx x with h1 | ⟨B, hBm, hj⟩
        · exact Or.inl h1
        · obtain ⟨i, hi, hiF⟩ := hs B hBm
          right
          rcases hj i hi with ⟨ha, hb⟩ | ⟨ha, hb⟩
          · refine ⟨_, hb, ?_⟩
            rw [deleteEdges_adj, ← ha]
            exact ⟨e_adj i, hiF⟩
          · refine ⟨_, hb, ?_⟩
            rw [deleteEdges_adj, ← ha, Sym2.eq_swap]
            exact ⟨(e_adj i).symm, hiF⟩
      · push Not at hs
        obtain ⟨B, hBm, hBF⟩ := hs
        have hS' : ∀ i : Fin 27, (S ||| B).testBit i.val = true → s((e i).1, (e i).2) ∈ F := by
          intro i hi
          rw [Nat.testBit_or, Bool.or_eq_true] at hi
          exact hi.elim (hS i) (hBF i)
        have hcnt : cnt (S ||| B) ≤ 4 := by
          have hnd : ((List.finRange 27).filter fun i => (S ||| B).testBit i.val).Nodup :=
            (List.nodup_finRange 27).filter _
          unfold cnt
          rw [← List.toFinset_card_of_nodup hnd]
          refine le_trans (Finset.card_le_card_of_injOn _ (fun i hi => ?_) e_inj.injOn) hF
          rw [Finset.mem_coe, List.mem_toFinset, List.mem_filter] at hi
          exact hS' i hi.2
        have hrec := List.all_eq_true.mp h B hBm
        rw [Bool.or_eq_true, decide_eq_true_eq] at hrec
        exact ih _ (hrec.resolve_left (by omega)) hS'

lemma chk_succ (n S : ℕ) (t : ℕ × List ℕ)
    (h : T.find? (fun t => t.2.all fun B => (B &&& S) != B) = some t)
    (hall : ∀ B ∈ t.2, (decide (4 < cnt (S ||| B)) || chk n (S ||| B)) = true) :
    chk (n + 1) S = true := by
  unfold chk
  rw [h]
  exact List.all_eq_true.mpr hall

set_option maxRecDepth 100000 in
lemma k0 : (decide (4 < cnt (0 ||| 2048)) || chk 4 (0 ||| 2048)) = true := by decide +kernel

set_option maxRecDepth 100000 in
lemma k1 : (decide (4 < cnt (0 ||| 2)) || chk 4 (0 ||| 2)) = true := by decide +kernel

set_option maxRecDepth 100000 in
lemma k2 : (decide (4 < cnt (0 ||| 256)) || chk 4 (0 ||| 256)) = true := by decide +kernel

set_option maxRecDepth 100000 in
lemma k3 : (decide (4 < cnt (0 ||| 131072)) || chk 4 (0 ||| 131072)) = true := by decide +kernel

set_option maxRecDepth 100000 in
lemma k4 : (decide (4 < cnt (0 ||| 8388608)) || chk 4 (0 ||| 8388608)) = true := by decide +kernel

set_option maxRecDepth 100000 in
lemma k5 : (decide (4 < cnt (0 ||| 4)) || chk 4 (0 ||| 4)) = true := by decide +kernel

set_option maxRecDepth 100000 in
lemma k6 : (decide (4 < cnt (0 ||| 16777216)) || chk 4 (0 ||| 16777216)) = true := by decide +kernel

set_option maxRecDepth 100000 in
lemma k7 : (decide (4 < cnt (0 ||| 16)) || chk 4 (0 ||| 16)) = true := by decide +kernel

set_option maxRecDepth 100000 in
lemma k8 : (decide (4 < cnt (0 ||| 576)) || chk 4 (0 ||| 576)) = true := by decide +kernel

set_option maxRecDepth 100000 in
lemma k9 : (decide (4 < cnt (0 ||| 16385)) || chk 4 (0 ||| 16385)) = true := by decide +kernel

set_option maxRecDepth 100000 in
lemma k10 : (decide (4 < cnt (0 ||| 1152)) || chk 4 (0 ||| 1152)) = true := by decide +kernel

set_option maxRecDepth 100000 in
lemma k11 : (decide (4 < cnt (0 ||| 65544)) || chk 4 (0 ||| 65544)) = true := by decide +kernel

lemma chk_ok : chk 5 0 = true := by
  refine chk_succ 4 0 (4239, [2048, 2, 256, 131072, 8388608, 4, 16777216, 16, 576, 16385, 1152, 65544]) (by decide +kernel) fun B hB => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hB
  rcases hB with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [k0, k1, k2, k3, k4, k5, k6, k7, k8, k9, k10, k11]

lemma maxDeg : G.maxDegree = 3 := by decide +kernel

end TeschnerCounter

open TeschnerCounter in
theorem OMA.disproof : ¬ (type_of% @OMA.S_wp_teschner_s_bondage_number_conjecture.main) := by
  intro h
  have hne : G.edgeFinset.Nonempty := ⟨s(0, 6), by rw [mem_edgeFinset, mem_edgeSet]; decide +kernel⟩
  obtain ⟨F, _, hlt, hcard⟩ := h 18 G hne
  have hdeg : G.maxDegree = 3 := by rw [← maxDeg]
  have hF : F.card ≤ 4 := by omega
  obtain ⟨D, hD, hD6⟩ := chk_sound F hF 5 0 chk_ok (by simp)
  have h6 : 6 ≤ dominationNumber G := by
    refine le_csInf ⟨_, Finset.univ, fun v => Or.inl (Finset.mem_univ v), rfl⟩ ?_
    rintro k ⟨D', hD', rfl⟩
    by_contra hk
    have := dom_sound 5 0 D' (by omega) fun v => Or.inr (hD' v)
    rw [no_five] at this
    exact Bool.noConfusion this
  have h6' : dominationNumber (G.deleteEdges (F : Set (Sym2 (Fin 18)))) ≤ 6 :=
    Nat.sInf_le ⟨D, hD, hD6⟩
  omega
