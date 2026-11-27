import OMAReductions.R_Erdos723_erdos_723_variants_leq_11_R1_H2_R2_H2_R1_H2_R1_H2_R1

/-! Split the large first-partition keys into four intervals. -/
-- Credit: @avivorly
namespace OMA.R_Erdos723_erdos_723_variants_leq_11_R1_H2_R2_H2_R1_H2_R1_H2_R1_H4_R1

def H1 : Prop :=
  let allowed (g : Fin 15) (p : Fin 60) := (0xfffc3ef80fafa00f3bbfb03bed00eeaeefc0bef00bdbdcf43b5efe00e7db781eef77db7007715f55fdd75f5f003c3740d75d7ddf5d5c1dd01e7d77fa4b5ea76c0beee5fa2a83ababebbbaf00cccf3cf3f3f3f033333cf3cfcfcffc003cf3cf3f3f3ffffc0000fcfcfcfffffffff000000:Nat).testBit (60*g.val+p.val) = true
  let required (g m : Fin 15) := (0x1fedbef6efdbf6f77bf5bff76df7edf6fdf6df8fffe3fff8fffe3fff8:Nat).testBit (15*g.val+m.val) = true
  let endpoints (p : Fin 60) := ((0x5000600220014008400880208011000a000c01040108011000a0202020401080110201020200840088005000604020404040804100220014200410081010082008400888008801040202040208011000a000c80044008401040201040108011000a400240042008201020202040108011:Nat) >>> (15*p.val)) &&& 32767
  let valid (s : Fin 15 → Fin 6 → Finset (Fin 60)) :=
    (∀ g i p, p∈s g i → allowed g p) ∧
    (∀ g i m, required g m → ∃! p, p∈s g i ∧ (endpoints p).testBit m.val = true) ∧
    (∀ g p, allowed g p → ∃! i, p∈s g i) ∧
    ∀ g h i j, g ≠ h → (s g i ∩ s h j).card ≤ 1
  let options := (List.finRange 60).filter fun p => decide (allowed 0 p)
  let catalogue : List Nat := Nat.rec (motive := fun _ => Nat → List Nat) (fun w : Nat => if w=0 then [0] else [])
    (fun _ (next : Nat → List Nat) w => if w=0 then [0] else options.flatMap fun p =>
      let e := endpoints p
      if e.testBit w.log2 && (e &&& w == e) then (next (w ^^^ e)).map (fun u => 2^p.val ||| u) else []) 60 32760
  let word (s : Finset (Fin 60)) := ((List.finRange 60).map fun p => if p∈s then 2^p.val else 0).foldr Nat.lor 0
  let key (s : Fin 15 → Fin 6 → Finset (Fin 60)) := ((List.range 344).map fun j =>
    if (List.finRange 6).any (fun i => catalogue.idxOf (word (s 0 i)) == j) then 2^j else 0).foldr Nat.lor 0
  ¬ ∃ s, valid s ∧ (∀ t, valid t → key s ≤ key t) ∧ 0x8000100000000000000800000000001000000000000000000000100000000000000010000 < key s ∧ key s ≤ 0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff

def H2 : Prop :=
  let allowed (g : Fin 15) (p : Fin 60) := (0xfffc3ef80fafa00f3bbfb03bed00eeaeefc0bef00bdbdcf43b5efe00e7db781eef77db7007715f55fdd75f5f003c3740d75d7ddf5d5c1dd01e7d77fa4b5ea76c0beee5fa2a83ababebbbaf00cccf3cf3f3f3f033333cf3cfcfcffc003cf3cf3f3f3ffffc0000fcfcfcfffffffff000000:Nat).testBit (60*g.val+p.val) = true
  let required (g m : Fin 15) := (0x1fedbef6efdbf6f77bf5bff76df7edf6fdf6df8fffe3fff8fffe3fff8:Nat).testBit (15*g.val+m.val) = true
  let endpoints (p : Fin 60) := ((0x5000600220014008400880208011000a000c01040108011000a0202020401080110201020200840088005000604020404040804100220014200410081010082008400888008801040202040208011000a000c80044008401040201040108011000a400240042008201020202040108011:Nat) >>> (15*p.val)) &&& 32767
  let valid (s : Fin 15 → Fin 6 → Finset (Fin 60)) :=
    (∀ g i p, p∈s g i → allowed g p) ∧
    (∀ g i m, required g m → ∃! p, p∈s g i ∧ (endpoints p).testBit m.val = true) ∧
    (∀ g p, allowed g p → ∃! i, p∈s g i) ∧
    ∀ g h i j, g ≠ h → (s g i ∩ s h j).card ≤ 1
  let options := (List.finRange 60).filter fun p => decide (allowed 0 p)
  let catalogue : List Nat := Nat.rec (motive := fun _ => Nat → List Nat) (fun w : Nat => if w=0 then [0] else [])
    (fun _ (next : Nat → List Nat) w => if w=0 then [0] else options.flatMap fun p =>
      let e := endpoints p
      if e.testBit w.log2 && (e &&& w == e) then (next (w ^^^ e)).map (fun u => 2^p.val ||| u) else []) 60 32760
  let word (s : Finset (Fin 60)) := ((List.finRange 60).map fun p => if p∈s then 2^p.val else 0).foldr Nat.lor 0
  let key (s : Fin 15 → Fin 6 → Finset (Fin 60)) := ((List.range 344).map fun j =>
    if (List.finRange 6).any (fun i => catalogue.idxOf (word (s 0 i)) == j) then 2^j else 0).foldr Nat.lor 0
  ¬ ∃ s, valid s ∧ (∀ t, valid t → key s ≤ key t) ∧ 0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff < key s ∧ key s ≤ 0x3fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff

def H3 : Prop :=
  let allowed (g : Fin 15) (p : Fin 60) := (0xfffc3ef80fafa00f3bbfb03bed00eeaeefc0bef00bdbdcf43b5efe00e7db781eef77db7007715f55fdd75f5f003c3740d75d7ddf5d5c1dd01e7d77fa4b5ea76c0beee5fa2a83ababebbbaf00cccf3cf3f3f3f033333cf3cfcfcffc003cf3cf3f3f3ffffc0000fcfcfcfffffffff000000:Nat).testBit (60*g.val+p.val) = true
  let required (g m : Fin 15) := (0x1fedbef6efdbf6f77bf5bff76df7edf6fdf6df8fffe3fff8fffe3fff8:Nat).testBit (15*g.val+m.val) = true
  let endpoints (p : Fin 60) := ((0x5000600220014008400880208011000a000c01040108011000a0202020401080110201020200840088005000604020404040804100220014200410081010082008400888008801040202040208011000a000c80044008401040201040108011000a400240042008201020202040108011:Nat) >>> (15*p.val)) &&& 32767
  let valid (s : Fin 15 → Fin 6 → Finset (Fin 60)) :=
    (∀ g i p, p∈s g i → allowed g p) ∧
    (∀ g i m, required g m → ∃! p, p∈s g i ∧ (endpoints p).testBit m.val = true) ∧
    (∀ g p, allowed g p → ∃! i, p∈s g i) ∧
    ∀ g h i j, g ≠ h → (s g i ∩ s h j).card ≤ 1
  let options := (List.finRange 60).filter fun p => decide (allowed 0 p)
  let catalogue : List Nat := Nat.rec (motive := fun _ => Nat → List Nat) (fun w : Nat => if w=0 then [0] else [])
    (fun _ (next : Nat → List Nat) w => if w=0 then [0] else options.flatMap fun p =>
      let e := endpoints p
      if e.testBit w.log2 && (e &&& w == e) then (next (w ^^^ e)).map (fun u => 2^p.val ||| u) else []) 60 32760
  let word (s : Finset (Fin 60)) := ((List.finRange 60).map fun p => if p∈s then 2^p.val else 0).foldr Nat.lor 0
  let key (s : Fin 15 → Fin 6 → Finset (Fin 60)) := ((List.range 344).map fun j =>
    if (List.finRange 6).any (fun i => catalogue.idxOf (word (s 0 i)) == j) then 2^j else 0).foldr Nat.lor 0
  ¬ ∃ s, valid s ∧ (∀ t, valid t → key s ≤ key t) ∧ 0x3fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff < key s ∧ key s ≤ 0x1ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff

def H4 : Prop :=
  let allowed (g : Fin 15) (p : Fin 60) := (0xfffc3ef80fafa00f3bbfb03bed00eeaeefc0bef00bdbdcf43b5efe00e7db781eef77db7007715f55fdd75f5f003c3740d75d7ddf5d5c1dd01e7d77fa4b5ea76c0beee5fa2a83ababebbbaf00cccf3cf3f3f3f033333cf3cfcfcffc003cf3cf3f3f3ffffc0000fcfcfcfffffffff000000:Nat).testBit (60*g.val+p.val) = true
  let required (g m : Fin 15) := (0x1fedbef6efdbf6f77bf5bff76df7edf6fdf6df8fffe3fff8fffe3fff8:Nat).testBit (15*g.val+m.val) = true
  let endpoints (p : Fin 60) := ((0x5000600220014008400880208011000a000c01040108011000a0202020401080110201020200840088005000604020404040804100220014200410081010082008400888008801040202040208011000a000c80044008401040201040108011000a400240042008201020202040108011:Nat) >>> (15*p.val)) &&& 32767
  let valid (s : Fin 15 → Fin 6 → Finset (Fin 60)) :=
    (∀ g i p, p∈s g i → allowed g p) ∧
    (∀ g i m, required g m → ∃! p, p∈s g i ∧ (endpoints p).testBit m.val = true) ∧
    (∀ g p, allowed g p → ∃! i, p∈s g i) ∧
    ∀ g h i j, g ≠ h → (s g i ∩ s h j).card ≤ 1
  let options := (List.finRange 60).filter fun p => decide (allowed 0 p)
  let catalogue : List Nat := Nat.rec (motive := fun _ => Nat → List Nat) (fun w : Nat => if w=0 then [0] else [])
    (fun _ (next : Nat → List Nat) w => if w=0 then [0] else options.flatMap fun p =>
      let e := endpoints p
      if e.testBit w.log2 && (e &&& w == e) then (next (w ^^^ e)).map (fun u => 2^p.val ||| u) else []) 60 32760
  let word (s : Finset (Fin 60)) := ((List.finRange 60).map fun p => if p∈s then 2^p.val else 0).foldr Nat.lor 0
  let key (s : Fin 15 → Fin 6 → Finset (Fin 60)) := ((List.range 344).map fun j =>
    if (List.finRange 6).any (fun i => catalogue.idxOf (word (s 0 i)) == j) then 2^j else 0).foldr Nat.lor 0
  ¬ ∃ s, valid s ∧ (∀ t, valid t → key s ≤ key t) ∧ 0x1ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff < key s ∧ key s ≤ 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff

set_option maxRecDepth 15000 in
theorem main : H1 → H2 → H3 → H4 → OMA.R_Erdos723_erdos_723_variants_leq_11_R1_H2_R2_H2_R1_H2_R1_H2_R1.H4 := by
  intro first second third fourth
  let allowed (g : Fin 15) (p : Fin 60) := (0xfffc3ef80fafa00f3bbfb03bed00eeaeefc0bef00bdbdcf43b5efe00e7db781eef77db7007715f55fdd75f5f003c3740d75d7ddf5d5c1dd01e7d77fa4b5ea76c0beee5fa2a83ababebbbaf00cccf3cf3f3f3f033333cf3cfcfcffc003cf3cf3f3f3ffffc0000fcfcfcfffffffff000000:Nat).testBit (60*g.val+p.val) = true
  let required (g m : Fin 15) := (0x1fedbef6efdbf6f77bf5bff76df7edf6fdf6df8fffe3fff8fffe3fff8:Nat).testBit (15*g.val+m.val) = true
  let endpoints (p : Fin 60) := ((0x5000600220014008400880208011000a000c01040108011000a0202020401080110201020200840088005000604020404040804100220014200410081010082008400888008801040202040208011000a000c80044008401040201040108011000a400240042008201020202040108011:Nat) >>> (15*p.val)) &&& 32767
  let valid (s : Fin 15 → Fin 6 → Finset (Fin 60)) :=
    (∀ g i p, p∈s g i → allowed g p) ∧
    (∀ g i m, required g m → ∃! p, p∈s g i ∧ (endpoints p).testBit m.val = true) ∧
    (∀ g p, allowed g p → ∃! i, p∈s g i) ∧
    ∀ g h i j, g ≠ h → (s g i ∩ s h j).card ≤ 1
  let options := (List.finRange 60).filter fun p => decide (allowed 0 p)
  let catalogue : List Nat := Nat.rec (motive := fun _ => Nat → List Nat) (fun w : Nat => if w=0 then [0] else [])
    (fun _ (next : Nat → List Nat) w => if w=0 then [0] else options.flatMap fun p =>
      let e := endpoints p
      if e.testBit w.log2 && (e &&& w == e) then (next (w ^^^ e)).map (fun u => 2^p.val ||| u) else []) 60 32760
  let word (s : Finset (Fin 60)) := ((List.finRange 60).map fun p => if p∈s then 2^p.val else 0).foldr Nat.lor 0
  let key (s : Fin 15 → Fin 6 → Finset (Fin 60)) := ((List.range 344).map fun j =>
    if (List.finRange 6).any (fun i => catalogue.idxOf (word (s 0 i)) == j) then 2^j else 0).foldr Nat.lor 0
  unfold OMA.R_Erdos723_erdos_723_variants_leq_11_R1_H2_R2_H2_R1_H2_R1_H2_R1.H4
  change ¬ ∃ s, valid s ∧ (∀ t, valid t → key s ≤ key t) ∧ 0x8000100000000000000800000000001000000000000000000000100000000000000010000 < key s
  rintro ⟨s, good, least, above⟩
  have bounded (f : Nat → Nat) (rows : List Nat) (small : ∀ j ∈ rows, f j < 2^344) :
      (rows.map f).foldr Nat.lor 0 < 2^344 := by
    induction rows with
    | nil => exact Nat.two_pow_pos _
    | cons i rows ih =>
      exact Nat.or_lt_two_pow (small i List.mem_cons_self)
        (ih fun j hj => small j (List.mem_cons_of_mem _ hj))
  have key_size : key s < 2^344 := by
    unfold key
    apply bounded
    intro j hj
    split
    · exact Nat.pow_lt_pow_right (by decide) (List.mem_range.mp hj)
    · exact Nat.two_pow_pos _
  have within : key s ≤ 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff := by
    have power : 2^344 = 0x100000000000000000000000000000000000000000000000000000000000000000000000000000000000000 := by rfl
    rw [power] at key_size
    omega
  by_cases small : key s ≤ 0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
  · exact first ⟨s, good, least, above, small⟩
  by_cases medium : key s ≤ 0x3fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
  · exact second ⟨s, good, least, Nat.lt_of_not_ge small, medium⟩
  by_cases large : key s ≤ 0x1ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
  · exact third ⟨s, good, least, Nat.lt_of_not_ge medium, large⟩
  exact fourth ⟨s, good, least, Nat.lt_of_not_ge large, within⟩

end OMA.R_Erdos723_erdos_723_variants_leq_11_R1_H2_R2_H2_R1_H2_R1_H2_R1_H4_R1
