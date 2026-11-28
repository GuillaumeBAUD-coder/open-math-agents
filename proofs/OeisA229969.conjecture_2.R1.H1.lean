import OMAReductions.R_OeisA229969_conjecture_2_R1

/-! Prime witnesses for ternary decompositions in the finite interval. -/

namespace OMA.TernaryPrimeWitnesses

private def coversHeads (P : ℕ) : ℕ → ℕ → Bool
  | _, 0 => true
  | a, width+1 => decide (a.gcd P ≠ 1) && coversHeads P (a+1) width

private theorem coversHeads_sound (P a width : ℕ) (h : coversHeads P a width = true) :
    ∀ d, a ≤ d → d < a+width → d.gcd P ≠ 1 := by
  induction width generalizing a with
  | zero => omega
  | succ width ih =>
    change (decide (a.gcd P ≠ 1) && coversHeads P (a+1) width) = true at h
    simp only [Bool.and_eq_true_iff, decide_eq_true_eq] at h
    intro d lo hi
    by_cases heq : d = a
    · exact heq ▸ h.1
    · exact ih (a+1) h.2 d (by omega) (by omega)

private theorem coversJoin {P a b c : ℕ}
    (left : ∀ d, a ≤ d → d < b → d.gcd P ≠ 1)
    (right : ∀ d, b ≤ d → d < c → d.gcd P ≠ 1) :
    ∀ d, a ≤ d → d < c → d.gcd P ≠ 1 := by
  intro d lo hi
  by_cases hm : d < b
  · exact left d lo hm
  · exact right d (by omega) hi

private theorem prime_of_covers {P b n : ℕ}
    (hcover : ∀ d, 2 ≤ d → d < b+1 → d.gcd P ≠ 1)
    (hn : 2 ≤ n) (hb : n < (b+1)^2) (hcop : n.gcd P = 1) : n.Prime := by
  by_contra h
  let d := n.minFac
  have hd : d.Prime := Nat.minFac_prime (by omega)
  have hsq : d^2 ≤ n := Nat.minFac_sq_le_self (by omega) h
  have hbound : d < b+1 := by
    by_contra! hbad
    have hh : (b+1)^2 ≤ d^2 := Nat.pow_le_pow_left hbad 2
    omega
  have hdiv : d ∣ P := by
    by_contra hnd
    exact hcover d hd.two_le hbound (hd.coprime_iff_not_dvd.mpr hnd)
  have hdg := Nat.dvd_gcd (Nat.minFac_dvd n) hdiv
  rw [hcop] at hdg
  exact hd.ne_one (Nat.dvd_one.mp hdg)

private def small : ℕ := 0x2eb2563692

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private def smallCovered2Checked : PLift (coversHeads small 2 30 = true) :=
  ⟨by decide +kernel⟩

private theorem smallCovered2 : ∀ d, 2 ≤ d → d < 32 → d.gcd small ≠ 1 :=
  coversHeads_sound small 2 30 smallCovered2Checked.down

private theorem smallCovers : ∀ d, 2 ≤ d → d < 32 → d.gcd small ≠ 1 :=
  smallCovered2

private def large : ℕ := 0x10e46263ecceb1482977d765f0ce17e03b92b3ae88d1202af8afe81c4219384e9ea88d2f8e3983bc57ccf4407b1aaded86c7f9414f0ced4572eef12dd45b6a1b6636e6ea3325ee61bde527d780510efbf2b58369a18025134160bc01cd81791cc36ecdd812864a839ae1e1fab419cd7157331f71566dc1a

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private def largeCovered2Checked : PLift (coversHeads large 2 256 = true) :=
  ⟨by decide +kernel⟩

private theorem largeCovered2 : ∀ d, 2 ≤ d → d < 258 → d.gcd large ≠ 1 :=
  coversHeads_sound large 2 256 largeCovered2Checked.down

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private def largeCovered258Checked : PLift (coversHeads large 258 256 = true) :=
  ⟨by decide +kernel⟩

private theorem largeCovered258 : ∀ d, 258 ≤ d → d < 514 → d.gcd large ≠ 1 :=
  coversHeads_sound large 258 256 largeCovered258Checked.down

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private def largeCovered514Checked : PLift (coversHeads large 514 174 = true) :=
  ⟨by decide +kernel⟩

private theorem largeCovered514 : ∀ d, 514 ≤ d → d < 688 → d.gcd large ≠ 1 :=
  coversHeads_sound large 514 174 largeCovered514Checked.down

private theorem largeCovers : ∀ d, 2 ≤ d → d < 688 → d.gcd large ≠ 1 :=
  (coversJoin largeCovered2 (coversJoin largeCovered258 largeCovered514))

private def checkPrime (n : ℕ) : Bool :=
  if n ≤ 31 then decide n.Prime
  else if n < 32^2 then decide (n.gcd small = 1)
  else decide (n < 688^2 ∧ n.gcd large = 1)

private theorem checkPrime_sound {n : ℕ} (h : checkPrime n = true) : n.Prime := by
  unfold checkPrime at h
  split at h
  · exact of_decide_eq_true h
  · rename_i largeEnough
    split at h
    · exact prime_of_covers smallCovers (by omega) (by assumption) (of_decide_eq_true h)
    · have h' := of_decide_eq_true h
      exact prime_of_covers largeCovers (by omega) h'.1 h'.2

private def Good (n : ℕ) : Prop :=
  ∃ x y z : ℕ, 0 < y ∧ 0 < z ∧ x + y + z = n ∧
    x ∈ ({3, 4, 6, 10, 15} : Finset ℕ) ∧
    (2*y-1).Prime ∧ (2*z-1).Prime ∧
    (2*x*y-1).Prime ∧ (2*x*z-1).Prime ∧ (2*y*z-1).Prime

private def checkWitness (n x y : ℕ) : Bool :=
  let z := n-x-y
  decide (0<y ∧ 0<z ∧ x+y+z=n ∧ x∈({3,4,6,10,15}:Finset ℕ)) &&
    [2*y-1,2*z-1,2*x*y-1,2*x*z-1,2*y*z-1].all checkPrime

private theorem checkWitness_sound {n x y : ℕ} (h : checkWitness n x y = true) : Good n := by
  let z := n-x-y
  simp only [checkWitness,Bool.and_eq_true_iff,decide_eq_true_eq] at h
  have primes := List.all_eq_true.mp h.2
  exact ⟨x,y,z,h.1.1,h.1.2.1,h.1.2.2.1,h.1.2.2.2,
    checkPrime_sound (primes (2*y-1) (by simp)),
    checkPrime_sound (primes (2*z-1) (by simp [z])),
    checkPrime_sound (primes (2*x*y-1) (by simp)),
    checkPrime_sound (primes (2*x*z-1) (by simp [z])),
    checkPrime_sound (primes (2*y*z-1) (by simp [z]))⟩

private def checkRows (first word : ℕ) : ℕ → Bool
  | 0 => true
  | count+1 =>
    let row := word%8192
    checkWitness first (row%16) (row/16) && checkRows (first+1) (word/8192) count

private theorem checkRows_sound {first word count : ℕ} (h : checkRows first word count = true) :
    ∀ n, first ≤ n → n < first+count → Good n := by
  induction count generalizing first word with
  | zero => omega
  | succ count ih =>
    rw [checkRows,Bool.and_eq_true_iff] at h
    intro n lo hi
    by_cases eq : n=first
    · subst n
      exact checkWitness_sound h.1
    · exact ih h.2 n (by omega) (by omega)

private theorem joinRows {a b c : ℕ}
    (left : ∀ n, a≤n → n<b → Good n) (right : ∀ n, b≤n → n<c → Good n) :
    ∀ n, a≤n → n<c → Good n := by
  intro n hlo hhi
  by_cases h : n<b
  · exact left n hlo h
  · exact right n (by omega) hhi

private def rows7Data : ℕ := 0x4030518110128073019808c0c8033011810c06616607983cc6260c309a028c14606603981980cc16301980cc1280940618c4c1e604402201cc12616316a00cc04606601981900662a303201cc0880a302180cc2a81540f1828c06610409b078c4481330198198268133033028c0c8044039824c1e6154019824c15403308201100860330118198066023019830c1480a302204180e6104022010c0660a303303cc0e6064061811006609302180cc0880a303980cc046064019808c06603302200cc08804301980cc046023

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private def rows7Checked : PLift (checkRows 7 rows7Data 125 = true) := ⟨by decide +kernel⟩

private theorem rows7 : ∀ n, 7 ≤ n → n < 132 → Good n :=
  checkRows_sound rows7Checked.down

private def rows132Data : ℕ := 0x331b3019014604418981cc9e846307980cc2c609407b058cc0c10402203cc5460430198dd04481e331981cc3c80f302180cc1862d4019824c26607327a028c2c6033011825096618401995cc0881e32b984cc06622402201cc2ac16303300cc15406607981909681e302180cc1480a3039950c0c8096019810c0661e309b0a0cae60aa01981108c60c30498b509682d32018c4c066064019830c2a80a309a13186ec4c41a18550066023033078c1280a303305500e6044052028c0662560aa0dd068604301980981461e3

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private def rows132Checked : PLift (checkRows 132 rows132Data 125 = true) := ⟨by decide +kernel⟩

private theorem rows132 : ∀ n, 132 ≤ n → n < 257 → Good n :=
  checkRows_sound rows132Checked.down

private def rows257Data : ℕ := 0x5b40b1ad1134834309b027c3082833a9aa4c5a6134022024c20807312b2bd08c603309d04110e61e6549858c08864309982a8e687243c3148d3e60c3083028c1264c42b981104480c3019808c0cc4f403998cc9660260199e1826646311204d00cc15632185503c60a304996d09e8463319855006613402203cc2082830320290146066169819096654302180cc0885262a180cca46184169858c12c396392118c1fe3130aa16d02680c33918550c6c734189950c1e6044019830c8060a3052028c0e66330398610066043

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private def rows257Checked : PLift (checkRows 257 rows257Data 125 = true) := ⟨by decide +kernel⟩

private theorem rows257 : ∀ n, 257 ≤ n → n < 382 → Good n :=
  checkRows_sound rows257Checked.down

private def rows382Data : ℕ := 0xaa3a981109e80f353213100c8d2305181989885b4669830d70603322b04d01468846e1ad1006602331980cc0882d3049a229a46366022010c066d9316a2bd15e61330f19c903c604466b21cd4c8463319a9902c6094691828c12603302203cce460430198dd01460732da0d0c26c03366980cc12c2d416981998e6b1327a334cf0606632181990e628309983d83c81e3079a2d82cc15639a078c98834303212cc266043019a9901e60ff099830c1480a3079ab985a81e4022010c066a641b2190d80646601981982684b3

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private def rows382Checked : PLift (checkRows 382 rows382Data 125 = true) := ⟨by decide +kernel⟩

private theorem rows382 : ∀ n, 382 ≤ n → n < 507 → Good n :=
  checkRows_sound rows382Checked.down

private def rows507Data : ℕ := 0x466169ae108c69330f5028c48c0440b18198a46064019808cfcc0f316a0b4c186a93051b711b862a30330a0c0c80330220c585464b4259830c9ece7403305980e65b40b189180666431b33f0cb68033391a3682c60a4051824cc660a30aa03cc0860334398dd00665733ca0b51ca8cd31a180cc2c6724033118d86c4b30b320510ecc94079a11844809331981cc308d2309980cc15416601981986260c3052028c2c63666698d900880430198b4c0881e42b9b94c146e540220c4ce46b4416a00cc0460660f184105061e3

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private def rows507Checked : PLift (checkRows 507 rows507Data 125 = true) := ⟨by decide +kernel⟩

private theorem rows507 : ∀ n, 507 ≤ n → n < 632 → Good n :=
  checkRows_sound rows507Checked.down

private def rows632Data : ℕ := 0x6333218250066e530aa00cc0880330f1a2d83c61046e1a74cb68af30f2078c2c646622b01105a80f3909830dca8734a22150c0e606607981cc06603361a00cc126e5329196d0088043019808c5a82a61a18c4d2660942d215cc0c82d302202905475a426201d80cc9d32630a989887830f1b1cc3c63741b21c8c15464327b26902c61331518b519a657314303cc26804406187982a81e40f181cc08603304d00cc5468843c18111b8657307b118c3c8033669a7cc0661543c18a8d8e60736e2334c08603303205500880aa

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private def rows632Checked : PLift (checkRows 632 rows632Data 125 = true) := ⟨by decide +kernel⟩

private theorem rows632 : ∀ n, 632 ≤ n → n < 757 → Good n :=
  checkRows_sound rows632Checked.down

private def rows757Data : ℕ := 0xe7415181106e82d304b028f1e8f03099950c9672c40199e0cf280c344202901261560b1b0d0268133019a4cdce803372a0c4cc860a40518b4cc66073392348c08603301993d19a681318980cee8cdc40f1950c686846169948ef662a3a5a474c9675fa151abd3026163319d6906c8f44bd9900d6261340f198cd5ec03308206100e6cda291ad10066023189830c0884b4169810c066a641b20a8c06602373a01100860330f18891b860ff909878e9683742019c8c495444439858e4260f3022528cf077b30518199e88073

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private def rows757Checked : PLift (checkRows 757 rows757Data 125 = true) := ⟨by decide +kernel⟩

private theorem rows757 : ∀ n, 757 ≤ n → n < 882 → Good n :=
  checkRows_sound rows757Checked.down

private def rows882Data : ℕ := 0x6615301900662a363981ccf28dc302180cc62c2d41698c4cc660c311221cd806c7303993d1868c730198290129c64039950fa26044019d28c2080a30336b8c0e60663218250066463409830c0880a3151aa4c0e6dc4022010c06602373a3710686033e898110b489331898b4c6e8dc30b18198506184e898a0f7874a30f2348d626884169a2119a6af32a1e04c2a803320183d9b880444399d4d4c80f302206101879b605182580880730499d4f02803339184180660a40518a8f7860a340a01100860330520190066633

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private def rows882Checked : PLift (checkRows 882 rows882Data 125 = true) := ⟨by decide +kernel⟩

private theorem rows882 : ∀ n, 882 ≤ n → n < 1007 → Good n :=
  checkRows_sound rows882Checked.down

theorem complete : ∀ n, 7 ≤ n → n < 1007 → Good n :=
  (joinRows (joinRows (joinRows rows7 rows132) (joinRows rows257 rows382)) (joinRows (joinRows rows507 rows632) (joinRows rows757 rows882)))

end OMA.TernaryPrimeWitnesses

theorem OMA.solution : OMA.R_OeisA229969_conjecture_2_R1.H1 := by
  intro n hlo hhi
  exact OMA.TernaryPrimeWitnesses.complete n (by omega) (by omega)