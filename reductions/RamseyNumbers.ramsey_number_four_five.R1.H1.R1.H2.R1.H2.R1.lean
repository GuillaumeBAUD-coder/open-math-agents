import OMAReductions.R_RamseyNumbers_ramsey_number_four_five_R1_H1_R1_H2_R1
import Mathlib

/-!
Canonical crossing matrices for the five six-vertex cases.

We certify explicit left and right automorphisms and move any crossing matrix
into the least binary encoding in its orbit. A clique in that representative
pulls back to the original matrix. A single left vertex also disposes of any
row that completes a red triangle or a blue four-clique in the right block.

The three remaining obligations concern an edge disjoint from a small star,
three disjoint edges, and a four-vertex path (with isolated vertices as needed).
Only these normalized, row-admissible finite obstructions remain open here.
The tables are certified automorphisms; their completeness is not asserted.

Credit: @Masselorc. The graph encodings and target come from the parent
reduction by @steveDOTdigital. Agent: chatgpt. Model: GPT-6 Astra Pro.
-/



namespace RamseyCrossReduction

theorem exists_minimal_relabel {n : Nat} (left : Fin n → Fin n → Bool)
    (right : Fin 16 → Fin 16 → Bool) (score : (Fin n → Fin 16 → Bool) → Nat)
    (rows : Fin n → Fin 16 → Bool) :
    ∃ (l : Equiv.Perm (Fin n)) (r : Equiv.Perm (Fin 16)),
      (∀ i j, left (l i) (l j) = left i j) ∧
      (∀ i j, right (r i) (r j) = right i j) ∧
      ∀ (l' : Equiv.Perm (Fin n)) (r' : Equiv.Perm (Fin 16)),
        (∀ i j, left (l' i) (l' j) = left i j) →
        (∀ i j, right (r' i) (r' j) = right i j) →
        score (fun i j => rows (l i) (r j)) ≤
          score (fun i j => rows (l (l' i)) (r (r' j))) := by
  classical
  let P (k : Nat) := ∃ (l : Equiv.Perm (Fin n)) (r : Equiv.Perm (Fin 16)),
    (∀ i j, left (l i) (l j) = left i j) ∧
    (∀ i j, right (r i) (r j) = right i j) ∧
    score (fun i j => rows (l i) (r j)) = k
  have exists_score : ∃ k, P k := ⟨score rows, 1, 1, fun _ _ => rfl,
    fun _ _ => rfl, rfl⟩
  obtain ⟨l, r, hl, hr, hscore⟩ := Nat.find_spec exists_score
  refine ⟨l, r, hl, hr, ?_⟩
  intro l' r' hl' hr'
  rw [hscore]
  exact Nat.find_min' exists_score
    ⟨l * l', r * r', fun i j => (hl (l' i) (l' j)).trans (hl' i j),
      fun i j => (hr (r' i) (r' j)).trans (hr' i j), rfl⟩

theorem preserves_of_injective {n mask : Nat} (f : Fin n → Fin n)
    (hinj : Function.Injective f)
    (h : ∀ i j : Fin n, i ≠ j →
      mask.testBit (max i.val j.val * (max i.val j.val - 1) / 2 + min i.val j.val) =
      mask.testBit (max (f i).val (f j).val * (max (f i).val (f j).val - 1) / 2 +
        min (f i).val (f j).val)) :
    ∀ i j : Fin n,
      (if f i = f j then false else
        mask.testBit (max (f i).val (f j).val * (max (f i).val (f j).val - 1) / 2 +
          min (f i).val (f j).val)) =
      (if i = j then false else
        mask.testBit (max i.val j.val * (max i.val j.val - 1) / 2 + min i.val j.val)) := by
  intro i j
  by_cases hij : i = j
  · subst j
    simp only [ite_true]
  · rw [if_neg hij, if_neg (hinj.ne hij)]
    exact (h i j hij).symm

end RamseyCrossReduction


namespace RamseyCrossReduction

theorem clique_map {n mask : Nat} {c : Bool} {s : Finset (Fin n)}
    (e : Equiv.Perm (Fin n))
    (he : ∀ i j,
      (if e i = e j then false else
        mask.testBit (max (e i).val (e j).val * (max (e i).val (e j).val - 1) / 2 +
          min (e i).val (e j).val)) =
      (if i = j then false else
        mask.testBit (max i.val j.val * (max i.val j.val - 1) / 2 + min i.val j.val)))
    (hs : ∀ i ∈ s, ∀ j ∈ s, i < j →
      mask.testBit (j.val * (j.val - 1) / 2 + i.val) = c) :
    ∀ i ∈ s.map e.toEmbedding, ∀ j ∈ s.map e.toEmbedding, i < j →
      mask.testBit (j.val * (j.val - 1) / 2 + i.val) = c := by
  intro i hi j hj hij
  obtain ⟨x, hx, rfl⟩ := Finset.mem_map.mp hi
  obtain ⟨y, hy, rfl⟩ := Finset.mem_map.mp hj
  have hne_image : e x ≠ e y := ne_of_lt hij
  have hne : x ≠ y := fun hxy => hne_image (congrArg e hxy)
  have hpres := he x y
  simp only [if_neg hne_image, if_neg hne] at hpres
  have hval : (e x).val ≤ (e y).val := Nat.le_of_lt hij
  rw [max_eq_right hval, min_eq_left hval] at hpres
  change mask.testBit ((e y).val * ((e y).val - 1) / 2 + (e x).val) = c
  rw [hpres]
  rcases lt_or_gt_of_ne hne with hxy | hyx
  · simpa only [max_eq_right (Nat.le_of_lt hxy), min_eq_left (Nat.le_of_lt hxy)]
      using hs x hx y hy hxy
  · simpa only [max_eq_left (Nat.le_of_lt hyx), min_eq_right (Nat.le_of_lt hyx)]
      using hs y hy x hx hyx

theorem clique_of_relabel {n left right : Nat}
    (rows : Fin n → Fin 16 → Bool)
    (l : Equiv.Perm (Fin n)) (r : Equiv.Perm (Fin 16))
    (hl : ∀ i j,
      (if l i = l j then false else
        left.testBit (max (l i).val (l j).val * (max (l i).val (l j).val - 1) / 2 +
          min (l i).val (l j).val)) =
      (if i = j then false else
        left.testBit (max i.val j.val * (max i.val j.val - 1) / 2 + min i.val j.val)))
    (hr : ∀ i j,
      (if r i = r j then false else
        right.testBit (max (r i).val (r j).val * (max (r i).val (r j).val - 1) / 2 +
          min (r i).val (r j).val)) =
      (if i = j then false else
        right.testBit (max i.val j.val * (max i.val j.val - 1) / 2 + min i.val j.val)))
    (h : ∃ (c : Bool) (s : Finset (Fin n)) (t : Finset (Fin 16)),
      s.card + t.card = (if c then 4 else 5) ∧
      (∀ i ∈ s, ∀ j ∈ s, i < j →
        left.testBit (j.val * (j.val - 1) / 2 + i.val) = c) ∧
      (∀ i ∈ t, ∀ j ∈ t, i < j →
        right.testBit (j.val * (j.val - 1) / 2 + i.val) = c) ∧
      ∀ i ∈ s, ∀ j ∈ t, rows (l i) (r j) = c) :
    ∃ (c : Bool) (s : Finset (Fin n)) (t : Finset (Fin 16)),
      s.card + t.card = (if c then 4 else 5) ∧
      (∀ i ∈ s, ∀ j ∈ s, i < j →
        left.testBit (j.val * (j.val - 1) / 2 + i.val) = c) ∧
      (∀ i ∈ t, ∀ j ∈ t, i < j →
        right.testBit (j.val * (j.val - 1) / 2 + i.val) = c) ∧
      ∀ i ∈ s, ∀ j ∈ t, rows i j = c := by
  obtain ⟨c, s, t, hsize, hleft, hright, hcross⟩ := h
  refine ⟨c, s.map l.toEmbedding, t.map r.toEmbedding, ?_,
    clique_map l hl hleft, clique_map r hr hright, ?_⟩
  · simpa only [Finset.card_map] using hsize
  · intro i hi j hj
    obtain ⟨x, hx, rfl⟩ := Finset.mem_map.mp hi
    obtain ⟨y, hy, rfl⟩ := Finset.mem_map.mp hj
    exact hcross x hx y hy

end RamseyCrossReduction


namespace RamseyCrossReduction

theorem row_restriction {n left right : Nat} (rows : Fin n → Fin 16 → Bool)
    (hnone : ¬ ∃ (c : Bool) (s : Finset (Fin n)) (t : Finset (Fin 16)),
      s.card + t.card = (if c then 4 else 5) ∧
      (∀ i ∈ s, ∀ j ∈ s, i < j →
        left.testBit (j.val * (j.val - 1) / 2 + i.val) = c) ∧
      (∀ i ∈ t, ∀ j ∈ t, i < j →
        right.testBit (j.val * (j.val - 1) / 2 + i.val) = c) ∧
      ∀ i ∈ s, ∀ j ∈ t, rows i j = c)
    (i : Fin n) (c : Bool) (t : Finset (Fin 16))
    (hcard : t.card = (if c then 3 else 4))
    (ht : ∀ j ∈ t, ∀ k ∈ t, j < k →
      right.testBit (k.val * (k.val - 1) / 2 + j.val) = c) :
    ¬ ∀ j ∈ t, rows i j = c := by
  intro hcross
  apply hnone
  refine ⟨c, {i}, t, ?_, ?_, ht, ?_⟩
  · rw [Finset.card_singleton, hcard]
    cases c <;> decide
  · intro x hx y hy hxy
    obtain rfl := Finset.mem_singleton.mp hx
    obtain rfl := Finset.mem_singleton.mp hy
    exact (lt_irrefl _ hxy).elim
  · intro x hx j hj
    obtain rfl := Finset.mem_singleton.mp hx
    exact hcross j hj

end RamseyCrossReduction


namespace RamseyAutPackedReduction

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem right_valid :
    ∀ code ∈ ([0xfedcba9876543210,0x98cfadeb35176402,0xc9ad8bfe43627051,0xbde8f9ac12450673,0xdfbae8c927304165,0xebf9dc8a61035724,0x8a9ecfbd50261347,0xac8b9edf04712536] : List Nat),
      Function.Bijective (fun i : Fin 16 => (Fin.ofNat 16 ((code >>> (4 * i.val)) % 16))) ∧
      ∀ i j : Fin 16, i ≠ j →
        (1057056059467516563339269255695059211 : Nat).testBit ((max i.val j.val) * (max i.val j.val - 1) / 2 + min i.val j.val) =
        (1057056059467516563339269255695059211 : Nat).testBit ((max ((Fin.ofNat 16 ((code >>> (4 * i.val)) % 16)).val) ((Fin.ofNat 16 ((code >>> (4 * j.val)) % 16)).val)) * (max ((Fin.ofNat 16 ((code >>> (4 * i.val)) % 16)).val) ((Fin.ofNat 16 ((code >>> (4 * j.val)) % 16)).val) - 1) / 2 + min ((Fin.ofNat 16 ((code >>> (4 * i.val)) % 16)).val) ((Fin.ofNat 16 ((code >>> (4 * j.val)) % 16)).val)) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem left_2112_valid :
    ∀ code ∈ ([181896,181448,50856,50408,153217,152769,136837,136389,165516,165068,34476,34028,22177,21729,5797,5349] : List Nat),
      Function.Bijective (fun i : Fin 6 => (Fin.ofNat 6 ((code >>> (3 * i.val)) % 8))) ∧
      ∀ i j : Fin 6, i ≠ j →
        (2112 : Nat).testBit ((max i.val j.val) * (max i.val j.val - 1) / 2 + min i.val j.val) =
        (2112 : Nat).testBit ((max ((Fin.ofNat 6 ((code >>> (3 * i.val)) % 8)).val) ((Fin.ofNat 6 ((code >>> (3 * j.val)) % 8)).val)) * (max ((Fin.ofNat 6 ((code >>> (3 * i.val)) % 8)).val) ((Fin.ofNat 6 ((code >>> (3 * j.val)) % 8)).val) - 1) / 2 + min ((Fin.ofNat 6 ((code >>> (3 * i.val)) % 8)).val) ((Fin.ofNat 6 ((code >>> (3 * j.val)) % 8)).val)) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem left_3136_valid :
    ∀ code ∈ ([181896,181448,5797,5349] : List Nat),
      Function.Bijective (fun i : Fin 6 => (Fin.ofNat 6 ((code >>> (3 * i.val)) % 8))) ∧
      ∀ i j : Fin 6, i ≠ j →
        (3136 : Nat).testBit ((max i.val j.val) * (max i.val j.val - 1) / 2 + min i.val j.val) =
        (3136 : Nat).testBit ((max ((Fin.ofNat 6 ((code >>> (3 * i.val)) % 8)).val) ((Fin.ofNat 6 ((code >>> (3 * j.val)) % 8)).val)) * (max ((Fin.ofNat 6 ((code >>> (3 * i.val)) % 8)).val) ((Fin.ofNat 6 ((code >>> (3 * j.val)) % 8)).val) - 1) / 2 + min ((Fin.ofNat 6 ((code >>> (3 * i.val)) % 8)).val) ((Fin.ofNat 6 ((code >>> (3 * j.val)) % 8)).val)) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem left_4232_valid :
    ∀ code ∈ ([181896,83784,153168,140904,169632,71520,55056,42792,178305,80193,145986,144453,176772,78660,47874,46341,120849,108585,117258,115725,119316,107052,104994,103461,180363,82251,151635,139371,168099,69987,53523,41259,166041,67929,133722,132189,164508,66396,35610,34077,22737,10473,19146,17613,21204,8940,6882,5349] : List Nat),
      Function.Bijective (fun i : Fin 6 => (Fin.ofNat 6 ((code >>> (3 * i.val)) % 8))) ∧
      ∀ i j : Fin 6, i ≠ j →
        (4232 : Nat).testBit ((max i.val j.val) * (max i.val j.val - 1) / 2 + min i.val j.val) =
        (4232 : Nat).testBit ((max ((Fin.ofNat 6 ((code >>> (3 * i.val)) % 8)).val) ((Fin.ofNat 6 ((code >>> (3 * j.val)) % 8)).val)) * (max ((Fin.ofNat 6 ((code >>> (3 * i.val)) % 8)).val) ((Fin.ofNat 6 ((code >>> (3 * j.val)) % 8)).val) - 1) / 2 + min ((Fin.ofNat 6 ((code >>> (3 * i.val)) % 8)).val) ((Fin.ofNat 6 ((code >>> (3 * j.val)) % 8)).val)) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem left_6208_valid :
    ∀ code ∈ ([181896,181840,165516,165460] : List Nat),
      Function.Bijective (fun i : Fin 6 => (Fin.ofNat 6 ((code >>> (3 * i.val)) % 8))) ∧
      ∀ i j : Fin 6, i ≠ j →
        (6208 : Nat).testBit ((max i.val j.val) * (max i.val j.val - 1) / 2 + min i.val j.val) =
        (6208 : Nat).testBit ((max ((Fin.ofNat 6 ((code >>> (3 * i.val)) % 8)).val) ((Fin.ofNat 6 ((code >>> (3 * j.val)) % 8)).val)) * (max ((Fin.ofNat 6 ((code >>> (3 * i.val)) % 8)).val) ((Fin.ofNat 6 ((code >>> (3 * j.val)) % 8)).val) - 1) / 2 + min ((Fin.ofNat 6 ((code >>> (3 * i.val)) % 8)).val) ((Fin.ofNat 6 ((code >>> (3 * j.val)) % 8)).val)) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem left_14400_valid :
    ∀ code ∈ ([181896,181448,181840,181336,180944,180888,165516,165068,165460,164956,164564,164508] : List Nat),
      Function.Bijective (fun i : Fin 6 => (Fin.ofNat 6 ((code >>> (3 * i.val)) % 8))) ∧
      ∀ i j : Fin 6, i ≠ j →
        (14400 : Nat).testBit ((max i.val j.val) * (max i.val j.val - 1) / 2 + min i.val j.val) =
        (14400 : Nat).testBit ((max ((Fin.ofNat 6 ((code >>> (3 * i.val)) % 8)).val) ((Fin.ofNat 6 ((code >>> (3 * j.val)) % 8)).val)) * (max ((Fin.ofNat 6 ((code >>> (3 * i.val)) % 8)).val) ((Fin.ofNat 6 ((code >>> (3 * j.val)) % 8)).val) - 1) / 2 + min ((Fin.ofNat 6 ((code >>> (3 * i.val)) % 8)).val) ((Fin.ofNat 6 ((code >>> (3 * j.val)) % 8)).val)) := by
  decide +kernel

end RamseyAutPackedReduction


namespace RamseyRowCount

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem red_triangle_catalog :
    ((List.range 16).flatMap fun i => (List.range 16).flatMap fun j =>
      ((List.range 16).filter fun k => decide (i < j ∧ j < k) &&
        (0xcb94e332f53ae143a3b6933356490b : Nat).testBit (j * (j - 1) / 2 + i) && (0xcb94e332f53ae143a3b6933356490b : Nat).testBit (k * (k - 1) / 2 + i) && (0xcb94e332f53ae143a3b6933356490b : Nat).testBit (k * (k - 1) / 2 + j)).map
        fun k => 2 ^ i + 2 ^ j + 2 ^ k) =
    ([259,2051,1029,2053,521,1033,769,1281,2561,290,16418,2178,32898,33026,18434,49154,1044,8212,8260,16452,17412,10244,18436,584,32840,4232,32904,4616,5128,33800,304,4144,4240,8336,1296,8464,5136,608,16480,800,4640,20512,8768,41024,49216,6272,10368,41088,8960,34048,41216,6656,10752,21504,50176,22528] : List Nat) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem blue_four_catalog :
    ((List.range 16).flatMap fun i => (List.range 16).flatMap fun j =>
      (List.range 16).flatMap fun k =>
      ((List.range 16).filter fun l => decide (i < j ∧ j < k ∧ k < l) &&
        !(0xcb94e332f53ae143a3b6933356490b : Nat).testBit (j * (j - 1) / 2 + i) && !(0xcb94e332f53ae143a3b6933356490b : Nat).testBit (k * (k - 1) / 2 + i) && !(0xcb94e332f53ae143a3b6933356490b : Nat).testBit (l * (l - 1) / 2 + i) &&
        !(0xcb94e332f53ae143a3b6933356490b : Nat).testBit (k * (k - 1) / 2 + j) && !(0xcb94e332f53ae143a3b6933356490b : Nat).testBit (l * (l - 1) / 2 + j) && !(0xcb94e332f53ae143a3b6933356490b : Nat).testBit (l * (l - 1) / 2 + k)).map
        fun l => 2 ^ i + 2 ^ j + 2 ^ k + 2 ^ l) =
    ([] : List Nat) := by
  decide +kernel

end RamseyRowCount


namespace RamseyScoreReduction

set_option maxHeartbeats 1000000 in
theorem score_injective : Function.Injective
    (fun r : Fin 6 → Fin 16 → Bool =>
      Nat.ofDigits 2 (List.ofFn (fun k : Fin 96 =>
        (r (Fin.ofNat 6 ((95 - k.val) / 16))
          (Fin.ofNat 16 (95 - k.val))).toNat))) := by
  intro r s h
  have hlist :
      List.ofFn (fun k : Fin 96 =>
        (r (Fin.ofNat 6 ((95 - k.val) / 16))
          (Fin.ofNat 16 (95 - k.val))).toNat) =
      List.ofFn (fun k : Fin 96 =>
        (s (Fin.ofNat 6 ((95 - k.val) / 16))
          (Fin.ofNat 16 (95 - k.val))).toNat) := by
    apply Nat.ofDigits_inj_of_len_eq (by decide) (by simp) _ _ h
    · intro d hd
      obtain ⟨k, rfl⟩ := List.mem_ofFn.mp hd
      exact Bool.toNat_lt _
    · intro d hd
      obtain ⟨k, rfl⟩ := List.mem_ofFn.mp hd
      exact Bool.toNat_lt _
  have hfun := List.ofFn_injective hlist
  funext i j
  have hi := i.isLt
  have hj := j.isLt
  let k : Fin 96 := ⟨95 - (16 * i.val + j.val), by omega⟩
  have hk : 95 - k.val = 16 * i.val + j.val := by
    dsimp [k]
    omega
  have hrow : Fin.ofNat 6 ((95 - k.val) / 16) = i := by
    apply Fin.ext
    change ((95 - k.val) / 16) % 6 = i.val
    rw [hk]
    omega
  have hcol : Fin.ofNat 16 (95 - k.val) = j := by
    apply Fin.ext
    change (95 - k.val) % 16 = j.val
    rw [hk]
    omega
  have hcell := congrFun hfun k
  rw [hrow, hcol] at hcell
  have hbool : ∀ a b : Bool, a.toNat = b.toNat → a = b := by decide
  exact hbool _ _ hcell

theorem score_lt (r : Fin 6 → Fin 16 → Bool) :
    Nat.ofDigits 2 (List.ofFn (fun k : Fin 96 =>
      (r (Fin.ofNat 6 ((95 - k.val) / 16))
        (Fin.ofNat 16 (95 - k.val))).toNat)) < 2 ^ 96 := by
  have h := Nat.ofDigits_lt_base_pow_length (b := 2)
    (l := List.ofFn (fun k : Fin 96 =>
      (r (Fin.ofNat 6 ((95 - k.val) / 16))
        (Fin.ofNat 16 (95 - k.val))).toNat)) (by decide) (by
      intro d hd
      obtain ⟨k, rfl⟩ := List.mem_ofFn.mp hd
      exact Bool.toNat_lt _)
  simpa only [List.length_ofFn] using h

end RamseyScoreReduction

namespace RamseyCrossReduction

theorem canonical_suffices (left right : Nat) (L R : List Nat)
    (score : (Fin 6 → Fin 16 → Bool) → Nat)
    (hL : ∀ a ∈ L,
    let f := fun i : Fin 6 => Fin.ofNat 6 ((a >>> (3*i.val)) % 8);
    Function.Bijective f ∧ ∀ i j : Fin 6, i ≠ j →
      left.testBit (max i.val j.val * (max i.val j.val-1)/2 + min i.val j.val) =
      left.testBit (max (f i).val (f j).val * (max (f i).val (f j).val-1)/2 + min (f i).val (f j).val))
    (hR : ∀ a ∈ R,
    let f := fun i : Fin 16 => Fin.ofNat 16 ((a >>> (4*i.val)) % 16);
    Function.Bijective f ∧ ∀ i j : Fin 16, i ≠ j →
      right.testBit (max i.val j.val * (max i.val j.val-1)/2 + min i.val j.val) =
      right.testBit (max (f i).val (f j).val * (max (f i).val (f j).val-1)/2 + min (f i).val (f j).val))
    (h : ∀ rows : Fin 6 → Fin 16 → Bool,
      (∀ a ∈ L, ∀ b ∈ R, score rows ≤
    score (fun i j => rows (Fin.ofNat 6 ((a >>> (3*i.val)) % 8))
      (Fin.ofNat 16 ((b >>> (4*j.val)) % 16)))) →
      (∀ (i : Fin 6) (c : Bool) (t : Finset (Fin 16)),
    t.card=(if c then 3 else 4) →
    (∀ j ∈ t, ∀ k ∈ t, j<k → (right : Nat).testBit (k.val*(k.val-1)/2+j.val)=c) →
    ¬ ∀ j ∈ t, rows i j=c) →
      ∃ (c : Bool) (s : Finset (Fin 6)) (t : Finset (Fin 16)),
    s.card+t.card = (if c then 4 else 5) ∧
    (∀ i ∈ s, ∀ j ∈ s, i<j → (left : Nat).testBit (j.val*(j.val-1)/2+i.val)=c) ∧
    (∀ i ∈ t, ∀ j ∈ t, i<j → (right : Nat).testBit (j.val*(j.val-1)/2+i.val)=c) ∧
    ∀ i ∈ s, ∀ j ∈ t, rows i j=c)
    (rows : Fin 6 → Fin 16 → Bool) :
    ∃ (c : Bool) (s : Finset (Fin 6)) (t : Finset (Fin 16)),
    s.card+t.card = (if c then 4 else 5) ∧
    (∀ i ∈ s, ∀ j ∈ s, i<j → (left : Nat).testBit (j.val*(j.val-1)/2+i.val)=c) ∧
    (∀ i ∈ t, ∀ j ∈ t, i<j → (right : Nat).testBit (j.val*(j.val-1)/2+i.val)=c) ∧
    ∀ i ∈ s, ∀ j ∈ t, rows i j=c := by
  classical
  obtain ⟨l, r, hl, hr, hmin⟩ := exists_minimal_relabel
    (fun i j : Fin 6 => if i=j then false else left.testBit (max i.val j.val * (max i.val j.val-1)/2 + min i.val j.val))
    (fun i j : Fin 16 => if i=j then false else right.testBit (max i.val j.val * (max i.val j.val-1)/2 + min i.val j.val)) score rows
  let rows' : Fin 6 → Fin 16 → Bool := fun i j => rows (l i) (r j)
  have hnorm : ∀ a ∈ L, ∀ b ∈ R, score rows' ≤
    score (fun i j => rows' (Fin.ofNat 6 ((a >>> (3*i.val)) % 8))
      (Fin.ofNat 16 ((b >>> (4*j.val)) % 16))) := by
    intro a ha b hb
    obtain ⟨habij, haedge⟩ := hL a ha
    obtain ⟨hbbij, hbedge⟩ := hR b hb
    exact hmin
      (Equiv.ofBijective (fun i : Fin 6 => Fin.ofNat 6 ((a >>> (3*i.val)) % 8)) habij)
      (Equiv.ofBijective (fun j : Fin 16 => Fin.ofNat 16 ((b >>> (4*j.val)) % 16)) hbbij)
      (preserves_of_injective _ habij.1 haedge)
      (preserves_of_injective _ hbbij.1 hbedge)
  have hc : ∃ (c : Bool) (s : Finset (Fin 6)) (t : Finset (Fin 16)),
    s.card+t.card = (if c then 4 else 5) ∧
    (∀ i ∈ s, ∀ j ∈ s, i<j → (left : Nat).testBit (j.val*(j.val-1)/2+i.val)=c) ∧
    (∀ i ∈ t, ∀ j ∈ t, i<j → (right : Nat).testBit (j.val*(j.val-1)/2+i.val)=c) ∧
    ∀ i ∈ s, ∀ j ∈ t, rows' i j=c := by
    by_cases hc : ∃ (c : Bool) (s : Finset (Fin 6)) (t : Finset (Fin 16)),
    s.card+t.card = (if c then 4 else 5) ∧
    (∀ i ∈ s, ∀ j ∈ s, i<j → (left : Nat).testBit (j.val*(j.val-1)/2+i.val)=c) ∧
    (∀ i ∈ t, ∀ j ∈ t, i<j → (right : Nat).testBit (j.val*(j.val-1)/2+i.val)=c) ∧
    ∀ i ∈ s, ∀ j ∈ t, rows' i j=c
    · exact hc
    · exact h rows' hnorm (row_restriction rows' hc)
  exact clique_of_relabel rows l r hl hr hc

end RamseyCrossReduction

namespace OMA.R_RamseyNumbers_ramsey_number_four_five_R1_H1_R1_H2_R1_H2_R1


def H1 : Prop :=
  ∀ m ∈ ([2112,6208,14400] : List Nat),
  let L : List Nat := if m=2112 then [181896,181448,50856,50408,153217,152769,136837,136389,165516,165068,34476,34028,22177,21729,5797,5349] else if m=6208 then [181896,181840,165516,165460] else [181896,181448,181840,181336,180944,180888,165516,165068,165460,164956,164564,164508];
  let R : List Nat := [0xfedcba9876543210,0x98cfadeb35176402,0xc9ad8bfe43627051,0xbde8f9ac12450673,0xdfbae8c927304165,0xebf9dc8a61035724,0x8a9ecfbd50261347,0xac8b9edf04712536];
  let score := fun r : Fin 6 → Fin 16 → Bool => Nat.ofDigits 2 (List.ofFn (fun k : Fin 96 => (r (Fin.ofNat 6 ((95-k.val)/16)) (Fin.ofNat 16 (95-k.val))).toNat));
  ∀ rows : Fin 6 → Fin 16 → Bool,
  (∀ a ∈ L, ∀ b ∈ R, score rows ≤
    score (fun i j => rows (Fin.ofNat 6 ((a >>> (3*i.val)) % 8))
      (Fin.ofNat 16 ((b >>> (4*j.val)) % 16)))) →
  (∀ (i : Fin 6) (c : Bool) (t : Finset (Fin 16)),
    t.card=(if c then 3 else 4) →
    (∀ j ∈ t, ∀ k ∈ t, j<k → (0xcb94e332f53ae143a3b6933356490b : Nat).testBit (k.val*(k.val-1)/2+j.val)=c) →
    ¬ ∀ j ∈ t, rows i j=c) →
  ∃ (c : Bool) (s : Finset (Fin 6)) (t : Finset (Fin 16)),
    s.card+t.card = (if c then 4 else 5) ∧
    (∀ i ∈ s, ∀ j ∈ s, i<j → (m : Nat).testBit (j.val*(j.val-1)/2+i.val)=c) ∧
    (∀ i ∈ t, ∀ j ∈ t, i<j → (0xcb94e332f53ae143a3b6933356490b : Nat).testBit (j.val*(j.val-1)/2+i.val)=c) ∧
    ∀ i ∈ s, ∀ j ∈ t, rows i j=c

def H2 : Prop :=
  ∀ m ∈ ([4232] : List Nat),
  let L : List Nat := [181896,83784,153168,140904,169632,71520,55056,42792,178305,80193,145986,144453,176772,78660,47874,46341,120849,108585,117258,115725,119316,107052,104994,103461,180363,82251,151635,139371,168099,69987,53523,41259,166041,67929,133722,132189,164508,66396,35610,34077,22737,10473,19146,17613,21204,8940,6882,5349];
  let R : List Nat := [0xfedcba9876543210,0x98cfadeb35176402,0xc9ad8bfe43627051,0xbde8f9ac12450673,0xdfbae8c927304165,0xebf9dc8a61035724,0x8a9ecfbd50261347,0xac8b9edf04712536];
  let score := fun r : Fin 6 → Fin 16 → Bool => Nat.ofDigits 2 (List.ofFn (fun k : Fin 96 => (r (Fin.ofNat 6 ((95-k.val)/16)) (Fin.ofNat 16 (95-k.val))).toNat));
  ∀ rows : Fin 6 → Fin 16 → Bool,
  (∀ a ∈ L, ∀ b ∈ R, score rows ≤
    score (fun i j => rows (Fin.ofNat 6 ((a >>> (3*i.val)) % 8))
      (Fin.ofNat 16 ((b >>> (4*j.val)) % 16)))) →
  (∀ (i : Fin 6) (c : Bool) (t : Finset (Fin 16)),
    t.card=(if c then 3 else 4) →
    (∀ j ∈ t, ∀ k ∈ t, j<k → (0xcb94e332f53ae143a3b6933356490b : Nat).testBit (k.val*(k.val-1)/2+j.val)=c) →
    ¬ ∀ j ∈ t, rows i j=c) →
  ∃ (c : Bool) (s : Finset (Fin 6)) (t : Finset (Fin 16)),
    s.card+t.card = (if c then 4 else 5) ∧
    (∀ i ∈ s, ∀ j ∈ s, i<j → (m : Nat).testBit (j.val*(j.val-1)/2+i.val)=c) ∧
    (∀ i ∈ t, ∀ j ∈ t, i<j → (0xcb94e332f53ae143a3b6933356490b : Nat).testBit (j.val*(j.val-1)/2+i.val)=c) ∧
    ∀ i ∈ s, ∀ j ∈ t, rows i j=c

def H3 : Prop :=
  ∀ m ∈ ([3136] : List Nat),
  let L : List Nat := [181896,181448,5797,5349];
  let R : List Nat := [0xfedcba9876543210,0x98cfadeb35176402,0xc9ad8bfe43627051,0xbde8f9ac12450673,0xdfbae8c927304165,0xebf9dc8a61035724,0x8a9ecfbd50261347,0xac8b9edf04712536];
  let score := fun r : Fin 6 → Fin 16 → Bool => Nat.ofDigits 2 (List.ofFn (fun k : Fin 96 => (r (Fin.ofNat 6 ((95-k.val)/16)) (Fin.ofNat 16 (95-k.val))).toNat));
  ∀ rows : Fin 6 → Fin 16 → Bool,
  (∀ a ∈ L, ∀ b ∈ R, score rows ≤
    score (fun i j => rows (Fin.ofNat 6 ((a >>> (3*i.val)) % 8))
      (Fin.ofNat 16 ((b >>> (4*j.val)) % 16)))) →
  (∀ (i : Fin 6) (c : Bool) (t : Finset (Fin 16)),
    t.card=(if c then 3 else 4) →
    (∀ j ∈ t, ∀ k ∈ t, j<k → (0xcb94e332f53ae143a3b6933356490b : Nat).testBit (k.val*(k.val-1)/2+j.val)=c) →
    ¬ ∀ j ∈ t, rows i j=c) →
  ∃ (c : Bool) (s : Finset (Fin 6)) (t : Finset (Fin 16)),
    s.card+t.card = (if c then 4 else 5) ∧
    (∀ i ∈ s, ∀ j ∈ s, i<j → (m : Nat).testBit (j.val*(j.val-1)/2+i.val)=c) ∧
    (∀ i ∈ t, ∀ j ∈ t, i<j → (0xcb94e332f53ae143a3b6933356490b : Nat).testBit (j.val*(j.val-1)/2+i.val)=c) ∧
    ∀ i ∈ s, ∀ j ∈ t, rows i j=c

theorem main : H1 → H2 → H3 → OMA.R_RamseyNumbers_ramsey_number_four_five_R1_H1_R1_H2_R1.H2 := by
  intro h1 h2 h3 p hp rows
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl
  · exact RamseyCrossReduction.canonical_suffices 2112 0xcb94e332f53ae143a3b6933356490b
      [181896,181448,50856,50408,153217,152769,136837,136389,165516,165068,34476,34028,22177,21729,5797,5349] [0xfedcba9876543210,0x98cfadeb35176402,0xc9ad8bfe43627051,0xbde8f9ac12450673,0xdfbae8c927304165,0xebf9dc8a61035724,0x8a9ecfbd50261347,0xac8b9edf04712536]
      (fun r : Fin 6 → Fin 16 → Bool => Nat.ofDigits 2 (List.ofFn (fun k : Fin 96 => (r (Fin.ofNat 6 ((95-k.val)/16)) (Fin.ofNat 16 (95-k.val))).toNat)))
      RamseyAutPackedReduction.left_2112_valid RamseyAutPackedReduction.right_valid
      (h1 2112 (by decide)) rows
  · exact RamseyCrossReduction.canonical_suffices 3136 0xcb94e332f53ae143a3b6933356490b
      [181896,181448,5797,5349] [0xfedcba9876543210,0x98cfadeb35176402,0xc9ad8bfe43627051,0xbde8f9ac12450673,0xdfbae8c927304165,0xebf9dc8a61035724,0x8a9ecfbd50261347,0xac8b9edf04712536]
      (fun r : Fin 6 → Fin 16 → Bool => Nat.ofDigits 2 (List.ofFn (fun k : Fin 96 => (r (Fin.ofNat 6 ((95-k.val)/16)) (Fin.ofNat 16 (95-k.val))).toNat)))
      RamseyAutPackedReduction.left_3136_valid RamseyAutPackedReduction.right_valid
      (h3 3136 (by decide)) rows
  · exact RamseyCrossReduction.canonical_suffices 4232 0xcb94e332f53ae143a3b6933356490b
      [181896,83784,153168,140904,169632,71520,55056,42792,178305,80193,145986,144453,176772,78660,47874,46341,120849,108585,117258,115725,119316,107052,104994,103461,180363,82251,151635,139371,168099,69987,53523,41259,166041,67929,133722,132189,164508,66396,35610,34077,22737,10473,19146,17613,21204,8940,6882,5349] [0xfedcba9876543210,0x98cfadeb35176402,0xc9ad8bfe43627051,0xbde8f9ac12450673,0xdfbae8c927304165,0xebf9dc8a61035724,0x8a9ecfbd50261347,0xac8b9edf04712536]
      (fun r : Fin 6 → Fin 16 → Bool => Nat.ofDigits 2 (List.ofFn (fun k : Fin 96 => (r (Fin.ofNat 6 ((95-k.val)/16)) (Fin.ofNat 16 (95-k.val))).toNat)))
      RamseyAutPackedReduction.left_4232_valid RamseyAutPackedReduction.right_valid
      (h2 4232 (by decide)) rows
  · exact RamseyCrossReduction.canonical_suffices 6208 0xcb94e332f53ae143a3b6933356490b
      [181896,181840,165516,165460] [0xfedcba9876543210,0x98cfadeb35176402,0xc9ad8bfe43627051,0xbde8f9ac12450673,0xdfbae8c927304165,0xebf9dc8a61035724,0x8a9ecfbd50261347,0xac8b9edf04712536]
      (fun r : Fin 6 → Fin 16 → Bool => Nat.ofDigits 2 (List.ofFn (fun k : Fin 96 => (r (Fin.ofNat 6 ((95-k.val)/16)) (Fin.ofNat 16 (95-k.val))).toNat)))
      RamseyAutPackedReduction.left_6208_valid RamseyAutPackedReduction.right_valid
      (h1 6208 (by decide)) rows
  · exact RamseyCrossReduction.canonical_suffices 14400 0xcb94e332f53ae143a3b6933356490b
      [181896,181448,181840,181336,180944,180888,165516,165068,165460,164956,164564,164508] [0xfedcba9876543210,0x98cfadeb35176402,0xc9ad8bfe43627051,0xbde8f9ac12450673,0xdfbae8c927304165,0xebf9dc8a61035724,0x8a9ecfbd50261347,0xac8b9edf04712536]
      (fun r : Fin 6 → Fin 16 → Bool => Nat.ofDigits 2 (List.ofFn (fun k : Fin 96 => (r (Fin.ofNat 6 ((95-k.val)/16)) (Fin.ofNat 16 (95-k.val))).toNat)))
      RamseyAutPackedReduction.left_14400_valid RamseyAutPackedReduction.right_valid
      (h1 14400 (by decide)) rows


end OMA.R_RamseyNumbers_ramsey_number_four_five_R1_H1_R1_H2_R1_H2_R1
