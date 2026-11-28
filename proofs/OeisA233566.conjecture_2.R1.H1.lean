import OMAReductions.R_OeisA233566_conjecture_2_R1

namespace OMA.PrimeTotientWitness

private def fastTotient : ℕ → ℕ → ℕ
  | _, 0 => 0
  | _, 1 => 1
  | 0, _ + 2 => 0
  | f + 1, n + 2 =>
    let p := (n + 2).minFac
    let r := (n + 2) / p
    (if p ∣ r then p else p - 1) * fastTotient f r

private theorem fastTotient_eq (f n : ℕ) (hn : n ≤ 2 ^ f) :
    fastTotient f n = n.totient := by
  induction f generalizing n with
  | zero =>
    have hsmall : n = 0 ∨ n = 1 := by
      rw [pow_zero] at hn
      omega
    rcases hsmall with rfl | rfl <;> simp [fastTotient]
  | succ f ih =>
    rcases n with _ | _ | n
    · simp [fastTotient]
    · simp [fastTotient]
    let p := (n + 2).minFac
    let r := (n + 2) / p
    have hp : p.Prime := Nat.minFac_prime (by omega)
    have hmul : p * r = n + 2 := by
      exact (Nat.mul_comm _ _).trans (Nat.div_mul_cancel (Nat.minFac_dvd _))
    have hbound : r ≤ 2 ^ f := by
      have h := Nat.mul_le_mul_right r hp.two_le
      rw [hmul] at h
      rw [pow_succ] at hn
      omega
    change (if p ∣ r then p else p-1) * fastTotient f r = (n+2).totient
    rw [ih r hbound, ← hmul]
    by_cases hdiv : p ∣ r
    · rw [if_pos hdiv, Nat.totient_mul_of_prime_of_dvd hp hdiv]
    · rw [if_neg hdiv, Nat.totient_mul_of_prime_of_not_dvd hp hdiv]

private def isPrime (n : ℕ) : Bool :=
  decide (2 ≤ n ∧ n.minFac = n)

private theorem isPrime_sound {n : ℕ} (h : isPrime n = true) : n.Prime :=
  Nat.prime_def_minFac.mpr (of_decide_eq_true h)

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

private def product128 : ℕ := 0x2bf2f5f313b1784cac2b5cf9532aa6cfa27dfc0f2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
private theorem coverCheck128_2 : coversHeads product128 2 127 = true := by decide +kernel

private theorem coverRange128_2 : ∀ d, 2 ≤ d → d < 129 → d.gcd product128 ≠ 1 :=
  coversHeads_sound product128 2 127 coverCheck128_2

private theorem cover128 : ∀ d, 2 ≤ d → d < 129 → d.gcd product128 ≠ 1 :=
  coverRange128_2

private def product512 : ℕ := 0x613a0497aa700632594668d2175f6874157ab081f7d649a3e936c6608f20575cb03949974ef1fb62db814d5fdf2c0d0e2d0abb2b26e8cc08403e32336e4bf96f1ffa1b71d1f4c342dc3812e17d7035b9e93905bff2c1a6de

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
private theorem coverCheck512_2 : coversHeads product512 2 400 = true := by decide +kernel

private theorem coverRange512_2 : ∀ d, 2 ≤ d → d < 402 → d.gcd product512 ≠ 1 :=
  coversHeads_sound product512 2 400 coverCheck512_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
private theorem coverCheck512_402 : coversHeads product512 402 111 = true := by decide +kernel

private theorem coverRange512_402 : ∀ d, 402 ≤ d → d < 513 → d.gcd product512 ≠ 1 :=
  coversHeads_sound product512 402 111 coverCheck512_402

private theorem cover512 : ∀ d, 2 ≤ d → d < 513 → d.gcd product512 ≠ 1 :=
  (coversJoin coverRange512_2 coverRange512_402)

private def product2048 : ℕ := 0x16564585b08dd5f22877a1318f86bdba7b0fc51815d34d06aafad397b90dcc208983465ef092dd5f060702d33a48c43ff82bfd1c2f3bd33339f9247351e6078ca7f3ce6091e985f04906d8dbd8431850a0ddbf985616af93522af8c99800a2aa0f5d0f3e2203ecc7cf46f27af897650509ee941d6c42f9f8052df7a69aa96f5d6f66c88bca6912855f86bc161e55552cc57a4a876094b64f0e4c61e60b9135466d35e4b21b8ba5382e3f149ce485384228cdff62f1f4e5426551974970db8cd22db8b45094fe86a3fc3225c4f2ec4efa418df4919e5a3bb3530f0fc3c6ebd6520d06dfa1bfc32147ed43d5a6242769f88c2e1c7dd3f74b6b3a8c88e7583b03b870ab7a661d32f204ea77715a9bbe7469cbfb0938d24eed9f79b3de4951c4841251853c4ad4f52e1c3cfcb4e492e9eda056d47b307234379669155a17ecf4da5cb78f5cdc320ba63682aa99ba22a7eaf50eb8a4bada77ffc26c26ecbcb997d4e2793fb4fefa23e

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
private theorem coverCheck2048_2 : coversHeads product2048 2 400 = true := by decide +kernel

private theorem coverRange2048_2 : ∀ d, 2 ≤ d → d < 402 → d.gcd product2048 ≠ 1 :=
  coversHeads_sound product2048 2 400 coverCheck2048_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
private theorem coverCheck2048_402 : coversHeads product2048 402 400 = true := by decide +kernel

private theorem coverRange2048_402 : ∀ d, 402 ≤ d → d < 802 → d.gcd product2048 ≠ 1 :=
  coversHeads_sound product2048 402 400 coverCheck2048_402

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
private theorem coverCheck2048_802 : coversHeads product2048 802 400 = true := by decide +kernel

private theorem coverRange2048_802 : ∀ d, 802 ≤ d → d < 1202 → d.gcd product2048 ≠ 1 :=
  coversHeads_sound product2048 802 400 coverCheck2048_802

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
private theorem coverCheck2048_1202 : coversHeads product2048 1202 400 = true := by decide +kernel

private theorem coverRange2048_1202 : ∀ d, 1202 ≤ d → d < 1602 → d.gcd product2048 ≠ 1 :=
  coversHeads_sound product2048 1202 400 coverCheck2048_1202

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
private theorem coverCheck2048_1602 : coversHeads product2048 1602 400 = true := by decide +kernel

private theorem coverRange2048_1602 : ∀ d, 1602 ≤ d → d < 2002 → d.gcd product2048 ≠ 1 :=
  coversHeads_sound product2048 1602 400 coverCheck2048_1602

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
private theorem coverCheck2048_2002 : coversHeads product2048 2002 47 = true := by decide +kernel

private theorem coverRange2048_2002 : ∀ d, 2002 ≤ d → d < 2049 → d.gcd product2048 ≠ 1 :=
  coversHeads_sound product2048 2002 47 coverCheck2048_2002

private theorem cover2048 : ∀ d, 2 ≤ d → d < 2049 → d.gcd product2048 ≠ 1 :=
  (coversJoin (coversJoin coverRange2048_2 (coversJoin coverRange2048_402 coverRange2048_802)) (coversJoin coverRange2048_1202 (coversJoin coverRange2048_1602 coverRange2048_2002)))

private def product8192 : ℕ := 0x444400e079f1f2b550fc47a5eff55819f4b7555520585896b48803944de393b7faa396d6b338dab060818be2db6beb79df80057fb0eeae56159df5aa8d546c661d701b36b12213ed38187dbac4988b1c659435c912124edcd97ba9ff047fbe0bfedf5d614d39f4d539309750a71e68578d140f2b8664e902bdcccfdd0f46b08b89cc112c0186173853ef96b03ddbfc25d1ae7395a7691bfc56ed0f129b2972439a553a9ca9158245e21a28762f3802296395053a0d996883d4c8d12dea0caa23b3dbe3286826d805be3e13b14dbc90f4ef3c55ec21d7fcff4a8a99a9154ffb5865e637f18f033e851ef079031d76325c5942883df6320085a2474f6054f5581907b2d53d585d345c4a4f65e16ad98237cfb5dd68f5f49e882fd041475105355d73b3eed1e3637909240272c18897d0deb4f05d9a72599f417374e6f5cf961256d06327e9893f964fa351dbbec4f8e2dc4eb9ebd1f2b7b5016b850dbb139dcc4f867ec107e21287c43ab27b6615bf6ad0eefb286ce008c6ab0092079b65b215912535989fd83496099d3e347162b79436521116f7a9caf39ad5b64e6a9d49123ac0529175bd265f5191bddc07e9c956e21a367cccaa69299968463157a5b1396c12af0fece7c6920420a35beb0c061e9a24ba604e09052be90c9eaad0c2c58420868e6b691e733621ba0eae08cb98fb59103b04870eeaa87376923e9919e90f35d60dccf69e307bdc6cbe352c763781d4a9850e683d4fc72d2128700e3747fe222ec762cfe9bf61a329175312e6a58fc0223d01068cd764f1136e59f6f7eaa681e8f15d1a355a99fef2d346aef3081ac5b56efda4f1449dc2a94427f5acd9d605e3f7644d5950f247b542cd0d1df78805dd741a8a04bd3ebaffa99e53c0dff3de7525363f93bf35fc41e4e75127853e85d2545d9502e4764492e9d512c4109270409aea7dfa44795e26288a9dfd9058fb04f95044b06d76703588533d2f4bbe803500a9af4f72e7db5b5d6ecf391a9b75ba3d6d4f044270183ae2640962adb3e5d91a4ee2eec23cc5820adf78665b126af3ea5931d0f0294bd9bb70ca0c0544cf143382d4857e7f7d5a312b9e3cfc25918cef104e63fd76f6cce0de58a0308be78aab3d5df4e9b466a37cb79435ea34dd950a9c2de255d2a1a769f1040d0edbffaaca189e987e869651dd70923733dc6c89ed8f5c83cfe77994e9733ecadbd1b3a3ca8c4c90355a0d6fcf118a0a0b0d686c99e181b1ade49e54522e1f8682ad4d58b3cf26e323bb210d8c5a1b3ef0deb396c7bcfaa22abadacf9d8de3295f79dd59e378cfa1c6103aa21a39f4bf78dc100a7e832e452b03c001e5c152eeb0bd58e8514fa26d1fecfb7033881d70f0edacb0307b174b05fb254538a2d82addee44a7232e6b8ebdfbf181a6acc58a7079abda2a0f6a81d112db3eee6fa38faf04ae36ac0c5ad7db82172802562a1fd5bd8da7fd02b8c6326297bf5ee3918d1bb823ed4ed35189b1ab0cdc39cef21123a0223d76fe92100d93e7d6acd584bc5db42daeb0f4b39b41cad8cc9d60fabc5620bef9f44662c5d3df4ed92a5ee97eaa66e6435851850f6c8b154e326d7a0fafba89dbd4ed2a2f76671291154003884022dfac5d83d84f687eee3c44f0f8b1d84e7f49979246a22d94f0b8ce5696a4fb20414d6c41f3ed62a3247566fda87a8b984f106f06877eb5eff083c117a1b4047da30e03d64d8573445bfc8eeaabb20069080cb160dc6dd1588b5b757a381891f5c7c101c7719d27c58438cdf9483bb15806aa55bd33a6ead713ab005c1c873ecc9fff1764a64cd4fbb76e84c6ab66c1bf67e9306cfe3e38eb4a963c9264aac25d08260aa2aaf7f8de06d37cac48277ca7a48c5d50d39aeffcb0ab06c9648f24365da150cba49363ce8c56cf78c6ca36e442c3ab0b447617f378afa81e6289b00452f62e4e232e32052ca1a93bda391edf2bf0a75f1f6ec1ba61168ecc07ca83b9d6316f6d3e35cc057e5564c52e333b48575d1b9cd36657ad77650de1015d2d36058475c047218a2e19af9d9c77a5022

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
private theorem coverCheck8192_2 : coversHeads product8192 2 400 = true := by decide +kernel

private theorem coverRange8192_2 : ∀ d, 2 ≤ d → d < 402 → d.gcd product8192 ≠ 1 :=
  coversHeads_sound product8192 2 400 coverCheck8192_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
private theorem coverCheck8192_402 : coversHeads product8192 402 400 = true := by decide +kernel

private theorem coverRange8192_402 : ∀ d, 402 ≤ d → d < 802 → d.gcd product8192 ≠ 1 :=
  coversHeads_sound product8192 402 400 coverCheck8192_402

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
private theorem coverCheck8192_802 : coversHeads product8192 802 400 = true := by decide +kernel

private theorem coverRange8192_802 : ∀ d, 802 ≤ d → d < 1202 → d.gcd product8192 ≠ 1 :=
  coversHeads_sound product8192 802 400 coverCheck8192_802

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
private theorem coverCheck8192_1202 : coversHeads product8192 1202 400 = true := by decide +kernel

private theorem coverRange8192_1202 : ∀ d, 1202 ≤ d → d < 1602 → d.gcd product8192 ≠ 1 :=
  coversHeads_sound product8192 1202 400 coverCheck8192_1202

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
private theorem coverCheck8192_1602 : coversHeads product8192 1602 400 = true := by decide +kernel

private theorem coverRange8192_1602 : ∀ d, 1602 ≤ d → d < 2002 → d.gcd product8192 ≠ 1 :=
  coversHeads_sound product8192 1602 400 coverCheck8192_1602

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
private theorem coverCheck8192_2002 : coversHeads product8192 2002 400 = true := by decide +kernel

private theorem coverRange8192_2002 : ∀ d, 2002 ≤ d → d < 2402 → d.gcd product8192 ≠ 1 :=
  coversHeads_sound product8192 2002 400 coverCheck8192_2002

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
private theorem coverCheck8192_2402 : coversHeads product8192 2402 400 = true := by decide +kernel

private theorem coverRange8192_2402 : ∀ d, 2402 ≤ d → d < 2802 → d.gcd product8192 ≠ 1 :=
  coversHeads_sound product8192 2402 400 coverCheck8192_2402

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
private theorem coverCheck8192_2802 : coversHeads product8192 2802 400 = true := by decide +kernel

private theorem coverRange8192_2802 : ∀ d, 2802 ≤ d → d < 3202 → d.gcd product8192 ≠ 1 :=
  coversHeads_sound product8192 2802 400 coverCheck8192_2802

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
private theorem coverCheck8192_3202 : coversHeads product8192 3202 400 = true := by decide +kernel

private theorem coverRange8192_3202 : ∀ d, 3202 ≤ d → d < 3602 → d.gcd product8192 ≠ 1 :=
  coversHeads_sound product8192 3202 400 coverCheck8192_3202

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
private theorem coverCheck8192_3602 : coversHeads product8192 3602 400 = true := by decide +kernel

private theorem coverRange8192_3602 : ∀ d, 3602 ≤ d → d < 4002 → d.gcd product8192 ≠ 1 :=
  coversHeads_sound product8192 3602 400 coverCheck8192_3602

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
private theorem coverCheck8192_4002 : coversHeads product8192 4002 400 = true := by decide +kernel

private theorem coverRange8192_4002 : ∀ d, 4002 ≤ d → d < 4402 → d.gcd product8192 ≠ 1 :=
  coversHeads_sound product8192 4002 400 coverCheck8192_4002

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
private theorem coverCheck8192_4402 : coversHeads product8192 4402 400 = true := by decide +kernel

private theorem coverRange8192_4402 : ∀ d, 4402 ≤ d → d < 4802 → d.gcd product8192 ≠ 1 :=
  coversHeads_sound product8192 4402 400 coverCheck8192_4402

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
private theorem coverCheck8192_4802 : coversHeads product8192 4802 400 = true := by decide +kernel

private theorem coverRange8192_4802 : ∀ d, 4802 ≤ d → d < 5202 → d.gcd product8192 ≠ 1 :=
  coversHeads_sound product8192 4802 400 coverCheck8192_4802

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
private theorem coverCheck8192_5202 : coversHeads product8192 5202 400 = true := by decide +kernel

private theorem coverRange8192_5202 : ∀ d, 5202 ≤ d → d < 5602 → d.gcd product8192 ≠ 1 :=
  coversHeads_sound product8192 5202 400 coverCheck8192_5202

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
private theorem coverCheck8192_5602 : coversHeads product8192 5602 400 = true := by decide +kernel

private theorem coverRange8192_5602 : ∀ d, 5602 ≤ d → d < 6002 → d.gcd product8192 ≠ 1 :=
  coversHeads_sound product8192 5602 400 coverCheck8192_5602

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
private theorem coverCheck8192_6002 : coversHeads product8192 6002 400 = true := by decide +kernel

private theorem coverRange8192_6002 : ∀ d, 6002 ≤ d → d < 6402 → d.gcd product8192 ≠ 1 :=
  coversHeads_sound product8192 6002 400 coverCheck8192_6002

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
private theorem coverCheck8192_6402 : coversHeads product8192 6402 400 = true := by decide +kernel

private theorem coverRange8192_6402 : ∀ d, 6402 ≤ d → d < 6802 → d.gcd product8192 ≠ 1 :=
  coversHeads_sound product8192 6402 400 coverCheck8192_6402

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
private theorem coverCheck8192_6802 : coversHeads product8192 6802 400 = true := by decide +kernel

private theorem coverRange8192_6802 : ∀ d, 6802 ≤ d → d < 7202 → d.gcd product8192 ≠ 1 :=
  coversHeads_sound product8192 6802 400 coverCheck8192_6802

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
private theorem coverCheck8192_7202 : coversHeads product8192 7202 400 = true := by decide +kernel

private theorem coverRange8192_7202 : ∀ d, 7202 ≤ d → d < 7602 → d.gcd product8192 ≠ 1 :=
  coversHeads_sound product8192 7202 400 coverCheck8192_7202

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
private theorem coverCheck8192_7602 : coversHeads product8192 7602 400 = true := by decide +kernel

private theorem coverRange8192_7602 : ∀ d, 7602 ≤ d → d < 8002 → d.gcd product8192 ≠ 1 :=
  coversHeads_sound product8192 7602 400 coverCheck8192_7602

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
private theorem coverCheck8192_8002 : coversHeads product8192 8002 191 = true := by decide +kernel

private theorem coverRange8192_8002 : ∀ d, 8002 ≤ d → d < 8193 → d.gcd product8192 ≠ 1 :=
  coversHeads_sound product8192 8002 191 coverCheck8192_8002

private theorem cover8192 : ∀ d, 2 ≤ d → d < 8193 → d.gcd product8192 ≠ 1 :=
  (coversJoin (coversJoin (coversJoin (coversJoin coverRange8192_2 coverRange8192_402) (coversJoin coverRange8192_802 (coversJoin coverRange8192_1202 coverRange8192_1602))) (coversJoin (coversJoin coverRange8192_2002 coverRange8192_2402) (coversJoin coverRange8192_2802 (coversJoin coverRange8192_3202 coverRange8192_3602)))) (coversJoin (coversJoin (coversJoin coverRange8192_4002 coverRange8192_4402) (coversJoin coverRange8192_4802 (coversJoin coverRange8192_5202 coverRange8192_5602))) (coversJoin (coversJoin coverRange8192_6002 (coversJoin coverRange8192_6402 coverRange8192_6802)) (coversJoin coverRange8192_7202 (coversJoin coverRange8192_7602 coverRange8192_8002)))))

private def product22424 : ℕ := 0x172dd0dc7531a388600330e4dada63e737a79f4efe97c2350e0eadf66323d283e8ab2a1114fa4e2e8ea8f2fa77e716c33f342729ef0caf233c405140fede84d2ed0a69946b0b7f201972a1fdfb7fd15116c1284beae1449bbdf2366f83fdc16c77ff77e9cddefd9fa22d7ceaf56fde91da4ccc552777f6314bb11b30648877104874ac3b38446ba32ecec2133b2dab3d249998869c20fcf0663cdd5900cc722d597c493d86b0e6437c2cd167495ed8ab5d99c7a16bb5d75b828c1095f01893ecc15dbea04c0fc25eefc1e0adf979170db2afaf6ef923ffe798b6e416987c30bded7f962dc63c345033b4ddaa7f975f2c0373600b2bff52e2a3008d3a9987a4ac7639c5ece7df2dae4d6ae471a2f88bf599e8db0b8aab7f3a1223099458eb75aca52bc8925bf4395086bb54a175b9681f69fb280f65719390c61a92c7b1dedfedb7f116eefdd1ede8c54b30bea7febc33a0b29dbd7a987f7505933a444651358773352691f90c266b0ae087eedb6c283bdd0331e4178f75cd2a908b23decf623ed6f4d15158d85541f0238ea252e1b0b29c0384cd11e9512ac7bb53336f65e94a3a13bd49e8aca699def7a54a90a3d54338e8533aebff21a0bbb7df90f21e309511f19a2e18567a086edd29359879832e12864a927a1f1c805de35b7720b1641c6aad76bc88ef1b9374b388a52b78d11e7aa0a228b99c1e445154d578c9737524ef05ba023d17bb4b1d7335838fe5f260be292707fc2e94dec66b787e699141e6ecb220e8e7610fff100f34c18b9d8c4289d1a9cf37682a7cda1024b9ebe7f50921b33328adab7585cab4007aab6c3fcce9379ab725e0a8d8a6f05180cb2c41743eb61f1ce00a9180e8160df0d11e5c201e3e904c6aed73e8b936928e0ca08b0393dacbf288d4a36ba807941c627e33ffe5ce82a8aa757474ecb8ce5cb946f7b7fba7a4ba33d6817602678d348e446989f758831e473a05db6085e1147d1fbe1bde06e9709cd82af368e7eb5a70455bced7fd18d9ba1a0d5e7b15a310b933b585b0ebe6b50c1456d7bc3b47f2440c4cade377bdaf69deda28830461dc48f3721d6757550b4b4b96bde6d74a4e13d78a738ed8f06fa664cd3e16e98c390b9f9e187bc4ae3290136bcf65098c788dc47309c08674aabb35b4d03c17a256fa380ab707c8c86c21bc0b9fa31eab2ff5a18d867dd5e9d81a2c9e25e0f61b8563f7da5ae6ca406ff1343c74be265ba25234e14c565476485adb93a6455121ae310ee690b5f627534f952f40e1c84be340012ee77e20aa917307f2a9e417dd65d82cde1e93cd675aee114fb0836b8e03897f6dfc87e3bc8ae30dee49777e14cd7d0869bfe9954a273023b55ff2762aeea51e421007ac9c967652d811653d52570f5a5e35758cc1f303e9e46d8edc2aa0691f56f2e616ed96ea7a078b9ef3a84ec26afde1c51c4c35decb78402f5d2013651799857f327833b1302ccd22f8208953d0e534788eb890f5f0cc9db88d8acbb8ccda7dba156296e7d84347fcb99a9dc2fdd5ba873b3b5197754dc7cc99681cb0f52db70d01610a4dfbe3efff7165715ca637c67ba8b0e63f021e81a5a2696878b9606fa34f00b823eaeaa18b4676b58cbb147d645670fd2a5667924b5fc51f8ea1020cff6d6fcf6d82c4b3b91c6df3a5c608c60c16f620a96155398da5aeed81e3b8f43eff823b31d181b2962c0b47649586dc31f548a6171a3892749c28b72a829d72d1cf843aef381f74f548d8bbaaf67356155585c48d92fbb7fc02fad9262483a4dc5746d25b1f6b370747a9cca47da1f98a42ddb77158d70794dc9f2183849ca5ec38e47db396f357ccacddb9be8f1a7dc91d17d12bc989fa148c5bef47185b3b48d94864132287f914be70ff990564df55d36a7d75379ff96828719efa6367d1f9d4296b81825189ff8ccee999abff507b6bcd33eacfbdeefff966f108764f09e3c42214c7158c367db26d6699f1fe18ad657150325db853f32a8a79d6be2af50427a6408d90053410f4624ea00d3d17c9ba4542cd97a1438cedd6a850cfc21caf24119a968bbc30b4e17d43370dc802957c67d7088663694581633c047dc247d2a700b8f2a8850417bffe4ced88d802b885408d13e40d0c9ac7211bc45b61db2f550fca113c2fb72687ae0259891527568caec3669b0021fc358c0c0939adaf3dda89dfafb076ebeef89aa3810689783f568cef685503739f251d2e09c1c1ec55ae06103657245cd4c68fb9a425210462f349154f84c39e680fa10136399f15966deb487332c23bdf90d723029a5013ed6f2cb4815f584c899608f353e859cc025027af0f1e2755ec7c9be48d80963b37330e27a58071b5a6692ac2f8ec0ce2e3ab10d31dbf84e30648d6a04f8d2d71022ad71c8e41f7883e90938522e6e055664b02022fb96f370f4ed75c9b8ab79ccc476c064287f9d15b2cf2efa75dfead0da9a9182459b7ae1858dbf135708f77c3502e997b59cb5440d3c9c45bb038a2b28e6991ff4918393c66b3f2ae4c1e7f0332425fc595381657026063709a5c08772e3f4ba74f36417f83ed3f736c2b40011fbf5460aad49c8ee52399bee462786f83a2882cdda748be71b6c83c6b929027673b596d374206b22b1a91a3518950fe582a7d815760d55dc3db6a7ef60a6e817c4262e1d8ea6331ff4a5e588e6c63e97bb2df81d57f826698523842e4052feeb4d49527bae18b8d61740ca8ace388cacdb082b8a032cfea4a966545cdce5670fbc09ce74535cfd9b0a071af8e9dc030b03c50a5e1505c2789489037e27d7ae449058946826090cf604378698a57d6878cc3f04300063708fdbd3549d3a0c99610126d6506c611816609a9f14026be312431cd5ed470cf9c1d0a3950ad779cdf5d612ff5ec3ac27f5f3894c57401885564e9c686f70d599bef002516324b022603c7757d73a51d045051162e8ac78f4d00f8bcc7c420c5c7b65fd5bfb19d5df5b35432b8c3b63252f998e42498a53fa08069e13ab624fa271552b1b749732d91d6a24f04e868b5850e036b6982c890d88bfb55114803d09122ddf8bcbc1bd0383099b7e44815c7b0c2dffc84b51c30771e907d4f738f0792b4d8223c80382acb7c806d5681296a92ff318b012bd61eefb12f91df4360f7d5dea8591f734027683fa88b3fe1124112e2af3d10e848dafca947953656a7ff2767d503635afbe9f609fe18d0fdc1ea4363089fc18520b3a69e2a14b65b5786c09651c16ec5bd3390fa3d7b926495eda4f1bd20f7898bb3d59b3c0ad7ed3eb7a19272488c69b095bce56abe29ac29d53f6adbcadaf96ed83a36be7cc66eb574e8e97049385bb2cca9a84378c931887fcb66356cdc45054a67589bfc9bd171d6369b87a3a0b3d77d13b555a7af90776d0416528eb0017bfe43db28c8811559951cf5f78629e97ea50d86629a6b11f88066602b5b0deb4d620917cfc80d52395a1d36b0756c459c969ff4bf34676a20ca18cf8f2d3dab460a2314985a4701002981915ac82cbff73356f8568f188db852d2257cda392e8c50afa1d4d8d27ef7567f50e50fcecda993520789ce6ff7281309b6c320c30634fa4b6f430ab49375c4f74bf81f6a1815fb2891b01f74ab4903f1347cebc8d0f73e4f7e7dd263c0307402a07abccba7064c0298de3f1fd416f39a8bc36ba3ff77040adc9dcc0f5076cd775d1dda220db37e2ffb48027987f4567443b1065b4b35c95fa24823d750224f8df33d928d981918f9f5ef7cf4fb8225759f81c30520e16bda914cd8557fbe9df5d557ca35833001a969d1fbde71c369a7f21d5215b91ccfad95044ac2415b91919b41ae9bd9b1a0048976b4e26574bf2b1fc5a8eab376b1180cdeedcc0c22fbd908bda9402c86ecab362cf3e47c2a1f186ec5c0aad4570d184e16da391c6a9b2f96ab0ca92cb1c3ed2be2105b7576c9ed62dbae577c31ae44aa44ab6505fcf7d384ef5a9999bd4952312f958328df92f2172aabdfb0b56468571dff8d843d771914c4fcf8d14668691b81a56062958c598bd249cbcd5ce53746d593cb218d5df7e41329e6c146301a5d2bdaf1f10484a79fdf6beb3e6aea091fb91e6ca49a5402154056d375023098d2deecb0cea370fa709970f04c1abde465afb3c043f295113537857c2faf87c14175bee589717b9b4b304cc8fd0015845f5f53a86520e812494e884c1e850a79faefb9d69071d4fa4a5b34d2f27a2a762e4a809f131a1cfe5b490adf1a17900b2180c86dded92c2db4974803b79d776b7b7456fbe948c712cc0863d1e09bec26f479f580ec25463caf9e43c34c8a81d9048011cb175c8259b6f7b531e2fcb0b6ba338307e3e57ecdbb7e7b6b0523970db895dcc79a91dd24a286df1d1239cf92e79267aa5ac45ca5ce70b65e7292add90ead63806a725924a025f28aff027d0419fe7482da9dd3311c91c22888e4456690f018590e6945c0a0ac8ca240c41c11940fac2d2cbbeed574a56ded7e039215a1bc5f73b446dcc2a474656bff26fa992b1d88e61807774d58d71b2a2f5f650bc10bfe6fac041568392730e6ecf221e7bf9562c3c6cdb718fd76f9ea7bb7512009b472d9ca7b7ac0b37363619d68d70e19aeb230bc44db4a19c6ef4de5d552035c95d58193c253775790c97f6cb249b188f3378f67ddbe188a28bf2b0acb423436f43089592d961f76d1ce069992b80ea594b1abda7efbcfe8bcde3f8fe3412d50961c084074cbd1cab64f2e3ffb3ab5ccd439499b8d4e9c4990b782eb2109fd8f06ac5c836614d55d5e7dacb73b77e824a954f669d49c9b54efddfb1ab57401ac2649b8c0256087e7ae0e88da3876022965362c93ddeaf877ac7c054e8d1adbd419d129b5ad3288f400766746b6eff1cfe08691106f4936cc99d88c80519236e355fb2702c2a5db786e789af2ac7de050eeaa891dd32cab3a3464a57df275f40fdb5d17abcb36c710578ad0a74eddda2d08d4f3ce88195ce0ccb59943fd14ec787cc173f32f90febdd017e3270aeee49e47d50cd8d722e630105a4f4d55dbff3f694d14bb2d35627e62b0d8eccf019ddeef476701238357f182b82afc9a08ab973f0fc9147ca5b32385347fbc97af352e6ccd52c469f65880ec784b56572a709284ed8055ab44c0db6095f8a7076c15be76429b337491686dbd549ebac5c6146e855cf273a8f7fe79e0500f77c5b8332e52ba5260418b86e479f236a207dae93b6fb565ae9772e24350600dded193b2ce23ad7049de86edca50e57cc2ac91d6e6c10d5e62f885ec6ae4261f892e7fc0087faa04c2dbc00605023cc7c12e8455190073465eb66d59edbd16d9dfd5bfc5c55680068fe8a9ca6c90548e3f565c618c37aa9c9a4fa4aab84ae96319198f958fbc0ccf0eaa3e1395a039bb808fd65aa77baa94e24ae89255116ba398b070b2d8659aed824e8bb4f4ad6292113206799565135a821f1db7522de83a3a188c877de0af83d2953b69116849604959a0510552a7950a9039912d4759de94551059e46f80dfca403a42e62ca2b1856d33ede352db247da9927b76311e029cbe923bb5cb3ec8f6d6a33cc402a90f663669ed03360fa7f2457d231159206b7658429344a17ca260c0504c21172c93afd198bddb4f39416e4850e9650f1a7c00849385fdc17d11ec962cebe15f78e3c6

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
private theorem coverCheck22424_2 : coversHeads product22424 2 400 = true := by decide +kernel

private theorem coverRange22424_2 : ∀ d, 2 ≤ d → d < 402 → d.gcd product22424 ≠ 1 :=
  coversHeads_sound product22424 2 400 coverCheck22424_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
private theorem coverCheck22424_402 : coversHeads product22424 402 400 = true := by decide +kernel

private theorem coverRange22424_402 : ∀ d, 402 ≤ d → d < 802 → d.gcd product22424 ≠ 1 :=
  coversHeads_sound product22424 402 400 coverCheck22424_402

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
private theorem coverCheck22424_802 : coversHeads product22424 802 400 = true := by decide +kernel

private theorem coverRange22424_802 : ∀ d, 802 ≤ d → d < 1202 → d.gcd product22424 ≠ 1 :=
  coversHeads_sound product22424 802 400 coverCheck22424_802

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
private theorem coverCheck22424_1202 : coversHeads product22424 1202 400 = true := by decide +kernel

private theorem coverRange22424_1202 : ∀ d, 1202 ≤ d → d < 1602 → d.gcd product22424 ≠ 1 :=
  coversHeads_sound product22424 1202 400 coverCheck22424_1202

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
private theorem coverCheck22424_1602 : coversHeads product22424 1602 400 = true := by decide +kernel

private theorem coverRange22424_1602 : ∀ d, 1602 ≤ d → d < 2002 → d.gcd product22424 ≠ 1 :=
  coversHeads_sound product22424 1602 400 coverCheck22424_1602

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
private theorem coverCheck22424_2002 : coversHeads product22424 2002 400 = true := by decide +kernel

private theorem coverRange22424_2002 : ∀ d, 2002 ≤ d → d < 2402 → d.gcd product22424 ≠ 1 :=
  coversHeads_sound product22424 2002 400 coverCheck22424_2002

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
private theorem coverCheck22424_2402 : coversHeads product22424 2402 400 = true := by decide +kernel

private theorem coverRange22424_2402 : ∀ d, 2402 ≤ d → d < 2802 → d.gcd product22424 ≠ 1 :=
  coversHeads_sound product22424 2402 400 coverCheck22424_2402

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
private theorem coverCheck22424_2802 : coversHeads product22424 2802 400 = true := by decide +kernel

private theorem coverRange22424_2802 : ∀ d, 2802 ≤ d → d < 3202 → d.gcd product22424 ≠ 1 :=
  coversHeads_sound product22424 2802 400 coverCheck22424_2802

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
private theorem coverCheck22424_3202 : coversHeads product22424 3202 400 = true := by decide +kernel

private theorem coverRange22424_3202 : ∀ d, 3202 ≤ d → d < 3602 → d.gcd product22424 ≠ 1 :=
  coversHeads_sound product22424 3202 400 coverCheck22424_3202

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
private theorem coverCheck22424_3602 : coversHeads product22424 3602 400 = true := by decide +kernel

private theorem coverRange22424_3602 : ∀ d, 3602 ≤ d → d < 4002 → d.gcd product22424 ≠ 1 :=
  coversHeads_sound product22424 3602 400 coverCheck22424_3602

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
private theorem coverCheck22424_4002 : coversHeads product22424 4002 400 = true := by decide +kernel

private theorem coverRange22424_4002 : ∀ d, 4002 ≤ d → d < 4402 → d.gcd product22424 ≠ 1 :=
  coversHeads_sound product22424 4002 400 coverCheck22424_4002

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
private theorem coverCheck22424_4402 : coversHeads product22424 4402 400 = true := by decide +kernel

private theorem coverRange22424_4402 : ∀ d, 4402 ≤ d → d < 4802 → d.gcd product22424 ≠ 1 :=
  coversHeads_sound product22424 4402 400 coverCheck22424_4402

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
private theorem coverCheck22424_4802 : coversHeads product22424 4802 400 = true := by decide +kernel

private theorem coverRange22424_4802 : ∀ d, 4802 ≤ d → d < 5202 → d.gcd product22424 ≠ 1 :=
  coversHeads_sound product22424 4802 400 coverCheck22424_4802

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
private theorem coverCheck22424_5202 : coversHeads product22424 5202 400 = true := by decide +kernel

private theorem coverRange22424_5202 : ∀ d, 5202 ≤ d → d < 5602 → d.gcd product22424 ≠ 1 :=
  coversHeads_sound product22424 5202 400 coverCheck22424_5202

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
private theorem coverCheck22424_5602 : coversHeads product22424 5602 400 = true := by decide +kernel

private theorem coverRange22424_5602 : ∀ d, 5602 ≤ d → d < 6002 → d.gcd product22424 ≠ 1 :=
  coversHeads_sound product22424 5602 400 coverCheck22424_5602

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
private theorem coverCheck22424_6002 : coversHeads product22424 6002 400 = true := by decide +kernel

private theorem coverRange22424_6002 : ∀ d, 6002 ≤ d → d < 6402 → d.gcd product22424 ≠ 1 :=
  coversHeads_sound product22424 6002 400 coverCheck22424_6002

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
private theorem coverCheck22424_6402 : coversHeads product22424 6402 400 = true := by decide +kernel

private theorem coverRange22424_6402 : ∀ d, 6402 ≤ d → d < 6802 → d.gcd product22424 ≠ 1 :=
  coversHeads_sound product22424 6402 400 coverCheck22424_6402

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
private theorem coverCheck22424_6802 : coversHeads product22424 6802 400 = true := by decide +kernel

private theorem coverRange22424_6802 : ∀ d, 6802 ≤ d → d < 7202 → d.gcd product22424 ≠ 1 :=
  coversHeads_sound product22424 6802 400 coverCheck22424_6802

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
private theorem coverCheck22424_7202 : coversHeads product22424 7202 400 = true := by decide +kernel

private theorem coverRange22424_7202 : ∀ d, 7202 ≤ d → d < 7602 → d.gcd product22424 ≠ 1 :=
  coversHeads_sound product22424 7202 400 coverCheck22424_7202

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
private theorem coverCheck22424_7602 : coversHeads product22424 7602 400 = true := by decide +kernel

private theorem coverRange22424_7602 : ∀ d, 7602 ≤ d → d < 8002 → d.gcd product22424 ≠ 1 :=
  coversHeads_sound product22424 7602 400 coverCheck22424_7602

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
private theorem coverCheck22424_8002 : coversHeads product22424 8002 400 = true := by decide +kernel

private theorem coverRange22424_8002 : ∀ d, 8002 ≤ d → d < 8402 → d.gcd product22424 ≠ 1 :=
  coversHeads_sound product22424 8002 400 coverCheck22424_8002

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
private theorem coverCheck22424_8402 : coversHeads product22424 8402 400 = true := by decide +kernel

private theorem coverRange22424_8402 : ∀ d, 8402 ≤ d → d < 8802 → d.gcd product22424 ≠ 1 :=
  coversHeads_sound product22424 8402 400 coverCheck22424_8402

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
private theorem coverCheck22424_8802 : coversHeads product22424 8802 400 = true := by decide +kernel

private theorem coverRange22424_8802 : ∀ d, 8802 ≤ d → d < 9202 → d.gcd product22424 ≠ 1 :=
  coversHeads_sound product22424 8802 400 coverCheck22424_8802

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
private theorem coverCheck22424_9202 : coversHeads product22424 9202 400 = true := by decide +kernel

private theorem coverRange22424_9202 : ∀ d, 9202 ≤ d → d < 9602 → d.gcd product22424 ≠ 1 :=
  coversHeads_sound product22424 9202 400 coverCheck22424_9202

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
private theorem coverCheck22424_9602 : coversHeads product22424 9602 400 = true := by decide +kernel

private theorem coverRange22424_9602 : ∀ d, 9602 ≤ d → d < 10002 → d.gcd product22424 ≠ 1 :=
  coversHeads_sound product22424 9602 400 coverCheck22424_9602

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
private theorem coverCheck22424_10002 : coversHeads product22424 10002 400 = true := by decide +kernel

private theorem coverRange22424_10002 : ∀ d, 10002 ≤ d → d < 10402 → d.gcd product22424 ≠ 1 :=
  coversHeads_sound product22424 10002 400 coverCheck22424_10002

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
private theorem coverCheck22424_10402 : coversHeads product22424 10402 400 = true := by decide +kernel

private theorem coverRange22424_10402 : ∀ d, 10402 ≤ d → d < 10802 → d.gcd product22424 ≠ 1 :=
  coversHeads_sound product22424 10402 400 coverCheck22424_10402

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
private theorem coverCheck22424_10802 : coversHeads product22424 10802 400 = true := by decide +kernel

private theorem coverRange22424_10802 : ∀ d, 10802 ≤ d → d < 11202 → d.gcd product22424 ≠ 1 :=
  coversHeads_sound product22424 10802 400 coverCheck22424_10802

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
private theorem coverCheck22424_11202 : coversHeads product22424 11202 400 = true := by decide +kernel

private theorem coverRange22424_11202 : ∀ d, 11202 ≤ d → d < 11602 → d.gcd product22424 ≠ 1 :=
  coversHeads_sound product22424 11202 400 coverCheck22424_11202

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
private theorem coverCheck22424_11602 : coversHeads product22424 11602 400 = true := by decide +kernel

private theorem coverRange22424_11602 : ∀ d, 11602 ≤ d → d < 12002 → d.gcd product22424 ≠ 1 :=
  coversHeads_sound product22424 11602 400 coverCheck22424_11602

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
private theorem coverCheck22424_12002 : coversHeads product22424 12002 400 = true := by decide +kernel

private theorem coverRange22424_12002 : ∀ d, 12002 ≤ d → d < 12402 → d.gcd product22424 ≠ 1 :=
  coversHeads_sound product22424 12002 400 coverCheck22424_12002

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
private theorem coverCheck22424_12402 : coversHeads product22424 12402 400 = true := by decide +kernel

private theorem coverRange22424_12402 : ∀ d, 12402 ≤ d → d < 12802 → d.gcd product22424 ≠ 1 :=
  coversHeads_sound product22424 12402 400 coverCheck22424_12402

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
private theorem coverCheck22424_12802 : coversHeads product22424 12802 400 = true := by decide +kernel

private theorem coverRange22424_12802 : ∀ d, 12802 ≤ d → d < 13202 → d.gcd product22424 ≠ 1 :=
  coversHeads_sound product22424 12802 400 coverCheck22424_12802

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
private theorem coverCheck22424_13202 : coversHeads product22424 13202 400 = true := by decide +kernel

private theorem coverRange22424_13202 : ∀ d, 13202 ≤ d → d < 13602 → d.gcd product22424 ≠ 1 :=
  coversHeads_sound product22424 13202 400 coverCheck22424_13202

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
private theorem coverCheck22424_13602 : coversHeads product22424 13602 400 = true := by decide +kernel

private theorem coverRange22424_13602 : ∀ d, 13602 ≤ d → d < 14002 → d.gcd product22424 ≠ 1 :=
  coversHeads_sound product22424 13602 400 coverCheck22424_13602

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
private theorem coverCheck22424_14002 : coversHeads product22424 14002 400 = true := by decide +kernel

private theorem coverRange22424_14002 : ∀ d, 14002 ≤ d → d < 14402 → d.gcd product22424 ≠ 1 :=
  coversHeads_sound product22424 14002 400 coverCheck22424_14002

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
private theorem coverCheck22424_14402 : coversHeads product22424 14402 400 = true := by decide +kernel

private theorem coverRange22424_14402 : ∀ d, 14402 ≤ d → d < 14802 → d.gcd product22424 ≠ 1 :=
  coversHeads_sound product22424 14402 400 coverCheck22424_14402

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
private theorem coverCheck22424_14802 : coversHeads product22424 14802 400 = true := by decide +kernel

private theorem coverRange22424_14802 : ∀ d, 14802 ≤ d → d < 15202 → d.gcd product22424 ≠ 1 :=
  coversHeads_sound product22424 14802 400 coverCheck22424_14802

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
private theorem coverCheck22424_15202 : coversHeads product22424 15202 400 = true := by decide +kernel

private theorem coverRange22424_15202 : ∀ d, 15202 ≤ d → d < 15602 → d.gcd product22424 ≠ 1 :=
  coversHeads_sound product22424 15202 400 coverCheck22424_15202

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
private theorem coverCheck22424_15602 : coversHeads product22424 15602 400 = true := by decide +kernel

private theorem coverRange22424_15602 : ∀ d, 15602 ≤ d → d < 16002 → d.gcd product22424 ≠ 1 :=
  coversHeads_sound product22424 15602 400 coverCheck22424_15602

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
private theorem coverCheck22424_16002 : coversHeads product22424 16002 400 = true := by decide +kernel

private theorem coverRange22424_16002 : ∀ d, 16002 ≤ d → d < 16402 → d.gcd product22424 ≠ 1 :=
  coversHeads_sound product22424 16002 400 coverCheck22424_16002

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
private theorem coverCheck22424_16402 : coversHeads product22424 16402 400 = true := by decide +kernel

private theorem coverRange22424_16402 : ∀ d, 16402 ≤ d → d < 16802 → d.gcd product22424 ≠ 1 :=
  coversHeads_sound product22424 16402 400 coverCheck22424_16402

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
private theorem coverCheck22424_16802 : coversHeads product22424 16802 400 = true := by decide +kernel

private theorem coverRange22424_16802 : ∀ d, 16802 ≤ d → d < 17202 → d.gcd product22424 ≠ 1 :=
  coversHeads_sound product22424 16802 400 coverCheck22424_16802

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
private theorem coverCheck22424_17202 : coversHeads product22424 17202 400 = true := by decide +kernel

private theorem coverRange22424_17202 : ∀ d, 17202 ≤ d → d < 17602 → d.gcd product22424 ≠ 1 :=
  coversHeads_sound product22424 17202 400 coverCheck22424_17202

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
private theorem coverCheck22424_17602 : coversHeads product22424 17602 400 = true := by decide +kernel

private theorem coverRange22424_17602 : ∀ d, 17602 ≤ d → d < 18002 → d.gcd product22424 ≠ 1 :=
  coversHeads_sound product22424 17602 400 coverCheck22424_17602

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
private theorem coverCheck22424_18002 : coversHeads product22424 18002 400 = true := by decide +kernel

private theorem coverRange22424_18002 : ∀ d, 18002 ≤ d → d < 18402 → d.gcd product22424 ≠ 1 :=
  coversHeads_sound product22424 18002 400 coverCheck22424_18002

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
private theorem coverCheck22424_18402 : coversHeads product22424 18402 400 = true := by decide +kernel

private theorem coverRange22424_18402 : ∀ d, 18402 ≤ d → d < 18802 → d.gcd product22424 ≠ 1 :=
  coversHeads_sound product22424 18402 400 coverCheck22424_18402

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
private theorem coverCheck22424_18802 : coversHeads product22424 18802 400 = true := by decide +kernel

private theorem coverRange22424_18802 : ∀ d, 18802 ≤ d → d < 19202 → d.gcd product22424 ≠ 1 :=
  coversHeads_sound product22424 18802 400 coverCheck22424_18802

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
private theorem coverCheck22424_19202 : coversHeads product22424 19202 400 = true := by decide +kernel

private theorem coverRange22424_19202 : ∀ d, 19202 ≤ d → d < 19602 → d.gcd product22424 ≠ 1 :=
  coversHeads_sound product22424 19202 400 coverCheck22424_19202

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
private theorem coverCheck22424_19602 : coversHeads product22424 19602 400 = true := by decide +kernel

private theorem coverRange22424_19602 : ∀ d, 19602 ≤ d → d < 20002 → d.gcd product22424 ≠ 1 :=
  coversHeads_sound product22424 19602 400 coverCheck22424_19602

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
private theorem coverCheck22424_20002 : coversHeads product22424 20002 400 = true := by decide +kernel

private theorem coverRange22424_20002 : ∀ d, 20002 ≤ d → d < 20402 → d.gcd product22424 ≠ 1 :=
  coversHeads_sound product22424 20002 400 coverCheck22424_20002

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
private theorem coverCheck22424_20402 : coversHeads product22424 20402 400 = true := by decide +kernel

private theorem coverRange22424_20402 : ∀ d, 20402 ≤ d → d < 20802 → d.gcd product22424 ≠ 1 :=
  coversHeads_sound product22424 20402 400 coverCheck22424_20402

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
private theorem coverCheck22424_20802 : coversHeads product22424 20802 400 = true := by decide +kernel

private theorem coverRange22424_20802 : ∀ d, 20802 ≤ d → d < 21202 → d.gcd product22424 ≠ 1 :=
  coversHeads_sound product22424 20802 400 coverCheck22424_20802

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
private theorem coverCheck22424_21202 : coversHeads product22424 21202 400 = true := by decide +kernel

private theorem coverRange22424_21202 : ∀ d, 21202 ≤ d → d < 21602 → d.gcd product22424 ≠ 1 :=
  coversHeads_sound product22424 21202 400 coverCheck22424_21202

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
private theorem coverCheck22424_21602 : coversHeads product22424 21602 400 = true := by decide +kernel

private theorem coverRange22424_21602 : ∀ d, 21602 ≤ d → d < 22002 → d.gcd product22424 ≠ 1 :=
  coversHeads_sound product22424 21602 400 coverCheck22424_21602

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
private theorem coverCheck22424_22002 : coversHeads product22424 22002 400 = true := by decide +kernel

private theorem coverRange22424_22002 : ∀ d, 22002 ≤ d → d < 22402 → d.gcd product22424 ≠ 1 :=
  coversHeads_sound product22424 22002 400 coverCheck22424_22002

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
private theorem coverCheck22424_22402 : coversHeads product22424 22402 23 = true := by decide +kernel

private theorem coverRange22424_22402 : ∀ d, 22402 ≤ d → d < 22425 → d.gcd product22424 ≠ 1 :=
  coversHeads_sound product22424 22402 23 coverCheck22424_22402

private theorem cover22424 : ∀ d, 2 ≤ d → d < 22425 → d.gcd product22424 ≠ 1 :=
  (coversJoin (coversJoin (coversJoin (coversJoin (coversJoin coverRange22424_2 (coversJoin coverRange22424_402 coverRange22424_802)) (coversJoin (coversJoin coverRange22424_1202 coverRange22424_1602) (coversJoin coverRange22424_2002 coverRange22424_2402))) (coversJoin (coversJoin coverRange22424_2802 (coversJoin coverRange22424_3202 coverRange22424_3602)) (coversJoin (coversJoin coverRange22424_4002 coverRange22424_4402) (coversJoin coverRange22424_4802 coverRange22424_5202)))) (coversJoin (coversJoin (coversJoin coverRange22424_5602 (coversJoin coverRange22424_6002 coverRange22424_6402)) (coversJoin (coversJoin coverRange22424_6802 coverRange22424_7202) (coversJoin coverRange22424_7602 coverRange22424_8002))) (coversJoin (coversJoin coverRange22424_8402 (coversJoin coverRange22424_8802 coverRange22424_9202)) (coversJoin (coversJoin coverRange22424_9602 coverRange22424_10002) (coversJoin coverRange22424_10402 coverRange22424_10802))))) (coversJoin (coversJoin (coversJoin (coversJoin coverRange22424_11202 (coversJoin coverRange22424_11602 coverRange22424_12002)) (coversJoin (coversJoin coverRange22424_12402 coverRange22424_12802) (coversJoin coverRange22424_13202 coverRange22424_13602))) (coversJoin (coversJoin coverRange22424_14002 (coversJoin coverRange22424_14402 coverRange22424_14802)) (coversJoin (coversJoin coverRange22424_15202 coverRange22424_15602) (coversJoin coverRange22424_16002 coverRange22424_16402)))) (coversJoin (coversJoin (coversJoin coverRange22424_16802 (coversJoin coverRange22424_17202 coverRange22424_17602)) (coversJoin (coversJoin coverRange22424_18002 coverRange22424_18402) (coversJoin coverRange22424_18802 coverRange22424_19202))) (coversJoin (coversJoin (coversJoin coverRange22424_19602 coverRange22424_20002) (coversJoin coverRange22424_20402 coverRange22424_20802)) (coversJoin (coversJoin coverRange22424_21202 coverRange22424_21602) (coversJoin coverRange22424_22002 coverRange22424_22402))))))

private def fastPrime (n : ℕ) : Bool :=
  if n ≤ 128 then isPrime n else
  if n < (128+1)^2 then n.gcd product128 == 1 else
  if n < (512+1)^2 then n.gcd product512 == 1 else
  if n < (2048+1)^2 then n.gcd product2048 == 1 else
  if n < (8192+1)^2 then n.gcd product8192 == 1 else
  if n < (22424+1)^2 then n.gcd product22424 == 1 else
  false

private theorem fastPrime_sound {n : ℕ} (h : fastPrime n = true) : n.Prime := by
  unfold fastPrime at h
  split at h
  · exact isPrime_sound h
  · split at h
    · exact prime_of_covers cover128 (by omega) (by assumption) (eq_of_beq h)
    · split at h
      · exact prime_of_covers cover512 (by omega) (by assumption) (eq_of_beq h)
      · split at h
        · exact prime_of_covers cover2048 (by omega) (by assumption) (eq_of_beq h)
        · split at h
          · exact prime_of_covers cover8192 (by omega) (by assumption) (eq_of_beq h)
          · split at h
            · exact prime_of_covers cover22424 (by omega) (by assumption) (eq_of_beq h)
            · contradiction

private def checkWitness (n p : ℕ) : Bool :=
  (decide (p < n) && fastPrime p) && fastPrime (p^2 * fastTotient 14 (n - p) - 1)

private theorem checkWitness_sound {n p : ℕ} (hn : n ≤ 10000)
    (h : checkWitness n p = true) : ∃ q < n, q.Prime ∧ (q^2 * (n-q).totient - 1).Prime := by
  simp only [checkWitness, Bool.and_eq_true_iff, decide_eq_true_eq] at h
  refine ⟨p, h.1.1, fastPrime_sound h.1.2, ?_⟩
  have hh : n - p ≤ 2^14 := (Nat.sub_le n p).trans (hn.trans (by decide))
  simpa only [fastTotient_eq 14 (n-p) hh] using fastPrime_sound h.2

private def checkBlock : ℕ → List ℕ → Bool
  | _, [] => true
  | n, p :: ps => checkWitness n p && checkBlock (n+1) ps

private theorem checkBlock_sound (n : ℕ) (ps : List ℕ) (h : checkBlock n ps = true)
    (k : ℕ) (hk : k < ps.length) (hn : n+k ≤ 10000) :
    ∃ p < n+k, p.Prime ∧ (p^2 * (n+k-p).totient - 1).Prime := by
  induction ps generalizing n k with
  | nil => simp at hk
  | cons p ps ih =>
    change (checkWitness n p && checkBlock (n+1) ps) = true at h
    rw [Bool.and_eq_true_iff] at h
    cases k with
    | zero => exact checkWitness_sound hn h.1
    | succ k =>
      have heq : n+(k+1) = (n+1)+k := by omega
      rw [heq] at hn ⊢
      exact ih (n+1) h.2 k (by simpa using hk) hn

private theorem checkedInterval (a width : ℕ) (table : List ℕ)
    (ht : table.length = width) (hc : checkBlock a table = true) :
    ∀ n, a ≤ n → n < a+width → n ≤ 10000 →
      ∃ p < n, p.Prime ∧ (p^2 * (n-p).totient - 1).Prime := by
  intro n hlo hhi hn
  have hpos : a + (n-a) = n := by omega
  have hk : n-a < table.length := by omega
  simpa only [hpos] using checkBlock_sound a table hc (n-a) hk (by omega)

private theorem joinIntervals {a b c : ℕ}
    (left : ∀ n, a ≤ n → n < b → n ≤ 10000 →
      ∃ p < n, p.Prime ∧ (p^2 * (n-p).totient - 1).Prime)
    (right : ∀ n, b ≤ n → n < c → n ≤ 10000 →
      ∃ p < n, p.Prime ∧ (p^2 * (n-p).totient - 1).Prime) :
    ∀ n, a ≤ n → n < c → n ≤ 10000 →
      ∃ p < n, p.Prime ∧ (p^2 * (n-p).totient - 1).Prime := by
  intro n lo hi hn
  by_cases h : n < b
  · exact left n lo h hn
  · exact right n (by omega) hi hn

private def roster000 : List ℕ := [2, 2, 2, 2, 3, 2, 2, 3, 2, 3, 7, 3, 2, 2, 2, 2, 3, 2, 2, 2, 2, 3, 3, 2, 2, 2, 2, 2, 3, 2, 3, 3, 2, 3, 11, 2, 3, 2, 11, 17, 5, 2, 2, 2, 3, 5, 3, 5, 2, 2, 2, 5, 5, 2, 5, 3, 5, 11, 3, 3, 2, 13, 3, 2, 2, 2, 2, 2, 5, 7, 37, 13, 5, 3, 5, 3, 2, 7, 2, 2, 5, 5, 3, 7, 7, 2, 2, 3, 3, 5, 13, 3, 2, 17, 11, 2, 2, 2, 2, 5, 3, 2, 19, 2, 2, 3, 3, 3, 2, 3, 3, 2, 3, 11, 13, 2, 3, 3, 2, 2, 2, 2, 13, 2, 5, 5, 2, 7, 7, 2, 3, 5, 2, 2, 3, 3, 19, 3, 11, 2, 2, 3, 2, 2, 3, 5, 3, 7, 3, 5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
private theorem arithmetic000 : checkBlock 3 roster000 = true := by decide +kernel

set_option maxRecDepth 100000 in
private theorem interval000 :
    ∀ n, 3 ≤ n → n < 153 → n ≤ 10000 →
      ∃ p < n, p.Prime ∧ (p^2 * (n-p).totient - 1).Prime :=
  checkedInterval 3 150 roster000 (by decide) arithmetic000

private def roster001 : List ℕ := [2, 11, 2, 2, 2, 2, 3, 2, 3, 7, 5, 3, 2, 5, 3, 3, 5, 2, 3, 7, 2, 3, 7, 2, 2, 67, 2, 5, 5, 2, 2, 3, 2, 11, 7, 2, 7, 2, 2, 3, 3, 3, 7, 2, 2, 3, 5, 2, 5, 7, 3, 3, 5, 3, 7, 3, 41, 2, 2, 2, 2, 3, 7, 3, 3, 3, 2, 2, 3, 7, 3, 7, 2, 2, 2, 17, 5, 5, 2, 7, 2, 11, 7, 3, 3, 2, 17, 2, 3, 3, 5, 2, 2, 2, 5, 3, 2, 2, 5, 5, 5, 5, 3, 2, 11, 3, 3, 11, 2, 2, 3, 3, 5, 3, 3, 2, 3, 3, 3, 3, 3, 7, 3, 17, 3, 7, 2, 5, 2, 2, 3, 2, 3, 7, 3, 2, 5, 2, 2, 3, 5, 53, 7, 5, 11, 3, 2, 3, 13, 23]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
private theorem arithmetic001 : checkBlock 153 roster001 = true := by decide +kernel

set_option maxRecDepth 100000 in
private theorem interval001 :
    ∀ n, 153 ≤ n → n < 303 → n ≤ 10000 →
      ∃ p < n, p.Prime ∧ (p^2 * (n-p).totient - 1).Prime :=
  checkedInterval 153 150 roster001 (by decide) arithmetic001

private def roster002 : List ℕ := [3, 2, 5, 5, 7, 2, 2, 2, 5, 2, 5, 2, 3, 41, 5, 13, 7, 3, 7, 31, 3, 3, 2, 2, 3, 2, 2, 23, 2, 5, 2, 3, 2, 7, 3, 2, 3, 3, 5, 11, 3, 2, 3, 5, 3, 3, 13, 11, 7, 2, 2, 5, 3, 2, 7, 19, 3, 23, 3, 2, 2, 2, 3, 3, 2, 2, 7, 37, 3, 11, 7, 2, 2, 3, 3, 7, 7, 2, 2, 13, 5, 3, 3, 5, 3, 7, 17, 3, 5, 2, 3, 3, 2, 3, 7, 2, 2, 7, 2, 7, 3, 5, 2, 19, 2, 5, 2, 5, 3, 3, 2, 3, 7, 7, 3, 5, 2, 2, 3, 2, 3, 2, 2, 5, 2, 3, 2, 7, 3, 5, 3, 13, 67, 2, 3, 2, 2, 29, 5, 13, 3, 3, 19, 5, 5, 2, 3, 3, 29, 2]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
private theorem arithmetic002 : checkBlock 303 roster002 = true := by decide +kernel

set_option maxRecDepth 100000 in
private theorem interval002 :
    ∀ n, 303 ≤ n → n < 453 → n ≤ 10000 →
      ∃ p < n, p.Prime ∧ (p^2 * (n-p).totient - 1).Prime :=
  checkedInterval 303 150 roster002 (by decide) arithmetic002

private def roster003 : List ℕ := [5, 7, 5, 3, 2, 3, 2, 2, 2, 3, 3, 2, 2, 3, 5, 5, 3, 7, 2, 17, 11, 11, 3, 3, 2, 5, 17, 5, 3, 13, 3, 7, 43, 5, 3, 2, 43, 3, 5, 5, 3, 3, 3, 2, 7, 17, 5, 3, 11, 3, 2, 17, 5, 3, 31, 7, 3, 11, 3, 29, 3, 7, 7, 5, 7, 3, 3, 2, 59, 7, 5, 3, 2, 2, 3, 5, 3, 7, 3, 17, 3, 2, 17, 5, 3, 13, 2, 3, 3, 3, 79, 5, 2, 5, 47, 5, 7, 2, 2, 5, 89, 5, 2, 2, 2, 2, 5, 2, 3, 17, 2, 3, 5, 11, 13, 7, 13, 19, 37, 17, 97, 19, 23, 5, 2, 17, 13, 2, 3, 7, 59, 11, 7, 2, 2, 3, 11, 3, 3, 37, 2, 2, 3, 2, 3, 7, 2, 53, 7, 3]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
private theorem arithmetic003 : checkBlock 453 roster003 = true := by decide +kernel

set_option maxRecDepth 100000 in
private theorem interval003 :
    ∀ n, 453 ≤ n → n < 603 → n ≤ 10000 →
      ∃ p < n, p.Prime ∧ (p^2 * (n-p).totient - 1).Prime :=
  checkedInterval 453 150 roster003 (by decide) arithmetic003

private def roster004 : List ℕ := [2, 3, 2, 17, 2, 7, 2, 2, 3, 3, 2, 3, 2, 2, 2, 3, 5, 29, 19, 7, 2, 11, 2, 3, 2, 7, 2, 29, 29, 5, 7, 3, 7, 3, 3, 5, 3, 37, 13, 3, 31, 5, 3, 13, 41, 2, 3, 2, 23, 13, 2, 11, 23, 2, 11, 2, 3, 2, 29, 5, 3, 2, 3, 23, 43, 2, 53, 2, 5, 29, 2, 3, 2, 3, 2, 7, 17, 5, 19, 17, 7, 13, 3, 2, 5, 7, 2, 83, 3, 5, 3, 7, 2, 73, 2, 3, 23, 5, 13, 37, 5, 2, 2, 2, 2, 13, 2, 3, 3, 19, 2, 3, 3, 3, 19, 2, 3, 3, 3, 29, 2, 2, 5, 2, 2, 3, 2, 2, 3, 2, 2, 3, 2, 7, 17, 3, 3, 3, 11, 2, 3, 13, 13, 5, 17, 2, 3, 2, 2, 13]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
private theorem arithmetic004 : checkBlock 603 roster004 = true := by decide +kernel

set_option maxRecDepth 100000 in
private theorem interval004 :
    ∀ n, 603 ≤ n → n < 753 → n ≤ 10000 →
      ∃ p < n, p.Prime ∧ (p^2 * (n-p).totient - 1).Prime :=
  checkedInterval 603 150 roster004 (by decide) arithmetic004

private def roster005 : List ℕ := [2, 2, 2, 5, 2, 2, 2, 2, 2, 2, 3, 37, 2, 7, 5, 13, 7, 3, 11, 3, 11, 41, 11, 3, 2, 3, 5, 11, 2, 5, 13, 3, 3, 7, 3, 2, 3, 2, 3, 23, 2, 3, 2, 2, 2, 2, 11, 2, 7, 2, 2, 3, 2, 41, 2, 2, 2, 7, 5, 2, 23, 7, 3, 2, 2, 5, 2, 3, 3, 2, 3, 2, 3, 23, 3, 5, 7, 3, 5, 3, 2, 3, 2, 2, 17, 2, 5, 37, 3, 3, 29, 3, 2, 3, 3, 2, 5, 2, 5, 2, 2, 3, 2, 2, 7, 43, 5, 3, 17, 67, 3, 11, 17, 2, 3, 17, 29, 2, 2, 3, 2, 3, 11, 2, 2, 2, 3, 3, 7, 2, 3, 3, 2, 3, 5, 13, 7, 2, 2, 3, 3, 5, 19, 3, 3, 7, 2, 3, 2, 3]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
private theorem arithmetic005 : checkBlock 753 roster005 = true := by decide +kernel

set_option maxRecDepth 100000 in
private theorem interval005 :
    ∀ n, 753 ≤ n → n < 903 → n ≤ 10000 →
      ∃ p < n, p.Prime ∧ (p^2 * (n-p).totient - 1).Prime :=
  checkedInterval 753 150 roster005 (by decide) arithmetic005

private def roster006 : List ℕ := [37, 3, 17, 47, 2, 17, 2, 13, 2, 2, 3, 2, 3, 2, 11, 2, 2, 2, 2, 13, 2, 3, 2, 3, 2, 2, 2, 3, 5, 5, 2, 3, 17, 5, 11, 2, 3, 2, 31, 2, 13, 7, 5, 3, 11, 23, 3, 3, 5, 2, 13, 5, 5, 23, 61, 19, 2, 3, 7, 5, 2, 3, 2, 7, 5, 3, 2, 2, 5, 89, 29, 17, 7, 3, 3, 29, 5, 3, 7, 3, 2, 17, 3, 2, 3, 7, 2, 3, 7, 5, 5, 5, 29, 3, 2, 3, 5, 3, 2, 41, 2, 2, 13, 2, 2, 3, 3, 2, 3, 5, 2, 2, 23, 7, 2, 3, 2, 3, 7, 3, 2, 13, 2, 3, 5, 13, 5, 3, 2, 5, 3, 5, 2, 11, 2, 3, 17, 11, 5, 3, 2, 37, 3, 5, 2, 2, 17, 3, 3, 3]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
private theorem arithmetic006 : checkBlock 903 roster006 = true := by decide +kernel

set_option maxRecDepth 100000 in
private theorem interval006 :
    ∀ n, 903 ≤ n → n < 1053 → n ≤ 10000 →
      ∃ p < n, p.Prime ∧ (p^2 * (n-p).totient - 1).Prime :=
  checkedInterval 903 150 roster006 (by decide) arithmetic006

private def roster007 : List ℕ := [7, 19, 2, 5, 2, 2, 3, 7, 17, 2, 7, 3, 5, 41, 2, 3, 5, 5, 2, 29, 17, 2, 3, 2, 2, 2, 13, 7, 3, 2, 3, 7, 13, 13, 2, 2, 5, 23, 5, 3, 5, 2, 3, 11, 17, 5, 5, 2, 17, 3, 2, 5, 19, 7, 3, 2, 2, 2, 3, 2, 3, 2, 3, 11, 3, 2, 2, 79, 5, 17, 11, 2, 3, 2, 2, 3, 5, 2, 41, 3, 2, 3, 2, 13, 19, 2, 2, 3, 5, 2, 3, 3, 2, 3, 5, 5, 103, 3, 11, 2, 17, 7, 13, 13, 7, 13, 17, 13, 11, 3, 2, 3, 29, 3, 23, 13, 3, 3, 23, 2, 2, 3, 263, 23, 3, 5, 3, 3, 2, 3, 5, 2, 3, 3, 17, 5, 7, 2, 19, 3, 2, 3, 17, 2, 47, 2, 2, 47, 3, 2]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
private theorem arithmetic007 : checkBlock 1053 roster007 = true := by decide +kernel

set_option maxRecDepth 100000 in
private theorem interval007 :
    ∀ n, 1053 ≤ n → n < 1203 → n ≤ 10000 →
      ∃ p < n, p.Prime ∧ (p^2 * (n-p).totient - 1).Prime :=
  checkedInterval 1053 150 roster007 (by decide) arithmetic007

private def roster008 : List ℕ := [2, 2, 3, 7, 7, 2, 7, 2, 2, 2, 2, 11, 7, 2, 2, 43, 5, 7, 3, 7, 2, 2, 3, 67, 2, 2, 3, 2, 3, 2, 2, 3, 13, 53, 7, 5, 2, 5, 23, 3, 7, 2, 13, 3, 11, 2, 2, 19, 37, 2, 13, 3, 2, 2, 7, 3, 2, 3, 29, 2, 3, 17, 2, 3, 5, 3, 3, 3, 5, 3, 2, 2, 2, 3, 5, 2, 3, 3, 3, 37, 2, 13, 5, 13, 7, 7, 2, 2, 3, 11, 3, 7, 17, 151, 3, 5, 13, 5, 5, 11, 13, 2, 29, 2, 2, 3, 3, 11, 7, 19, 2, 3, 2, 3, 29, 2, 3, 3, 5, 2, 2, 7, 2, 3, 2, 5, 2, 3, 3, 5, 37, 3, 2, 13, 5, 13, 37, 3, 13, 2, 3, 2, 3, 37, 17, 2, 2, 2, 2, 2]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
private theorem arithmetic008 : checkBlock 1203 roster008 = true := by decide +kernel

set_option maxRecDepth 100000 in
private theorem interval008 :
    ∀ n, 1203 ≤ n → n < 1353 → n ≤ 10000 →
      ∃ p < n, p.Prime ∧ (p^2 * (n-p).totient - 1).Prime :=
  checkedInterval 1203 150 roster008 (by decide) arithmetic008

private def roster009 : List ℕ := [13, 11, 5, 13, 31, 3, 13, 3, 13, 7, 11, 3, 5, 2, 3, 13, 7, 29, 7, 3, 5, 2, 13, 2, 5, 2, 3, 29, 2, 5, 2, 5, 13, 5, 23, 2, 7, 2, 5, 2, 2, 3, 2, 3, 2, 7, 2, 7, 2, 7, 2, 3, 2, 7, 19, 2, 2, 3, 47, 2, 7, 3, 5, 2, 3, 3, 31, 7, 2, 2, 2, 2, 3, 5, 2, 29, 3, 7, 2, 7, 23, 3, 47, 5, 3, 7, 2, 11, 23, 3, 7, 2, 3, 11, 5, 3, 2, 2, 2, 2, 3, 2, 2, 2, 37, 3, 2, 7, 3, 3, 5, 2, 3, 3, 13, 2, 23, 2, 17, 17, 2, 3, 2, 3, 2, 5, 2, 11, 2, 29, 13, 23, 2, 3, 2, 5, 13, 7, 13, 7, 2, 3, 11, 7, 19, 43, 17, 2, 7, 29]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
private theorem arithmetic009 : checkBlock 1353 roster009 = true := by decide +kernel

set_option maxRecDepth 100000 in
private theorem interval009 :
    ∀ n, 1353 ≤ n → n < 1503 → n ≤ 10000 →
      ∃ p < n, p.Prime ∧ (p^2 * (n-p).totient - 1).Prime :=
  checkedInterval 1353 150 roster009 (by decide) arithmetic009

private def roster010 : List ℕ := [11, 2, 29, 3, 5, 2, 7, 2, 3, 2, 3, 41, 31, 2, 3, 2, 3, 2, 2, 5, 13, 3, 7, 3, 2, 2, 11, 11, 2, 53, 7, 5, 29, 7, 3, 5, 29, 3, 3, 3, 2, 11, 97, 3, 3, 7, 3, 5, 73, 2, 3, 5, 3, 3, 7, 3, 2, 2, 17, 5, 11, 3, 2, 37, 19, 5, 2, 2, 3, 7, 23, 5, 2, 11, 2, 5, 2, 7, 2, 5, 5, 2, 3, 11, 13, 2, 19, 2, 3, 2, 2, 2, 3, 5, 11, 3, 19, 19, 5, 23, 47, 2, 2, 31, 2, 2, 17, 2, 3, 2, 2, 2, 11, 2, 11, 19, 2, 3, 7, 3, 7, 13, 5, 2, 2, 3, 19, 2, 5, 2, 7, 3, 7, 2, 3, 7, 5, 3, 5, 13, 5, 29, 23, 5, 13, 7, 37, 3, 2, 41]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
private theorem arithmetic010 : checkBlock 1503 roster010 = true := by decide +kernel

set_option maxRecDepth 100000 in
private theorem interval010 :
    ∀ n, 1503 ≤ n → n < 1653 → n ≤ 10000 →
      ∃ p < n, p.Prime ∧ (p^2 * (n-p).totient - 1).Prime :=
  checkedInterval 1503 150 roster010 (by decide) arithmetic010

private def roster011 : List ℕ := [2, 7, 3, 5, 2, 2, 3, 5, 3, 3, 3, 2, 3, 3, 3, 2, 3, 2, 3, 11, 2, 2, 2, 5, 2, 2, 3, 5, 3, 7, 11, 3, 3, 2, 3, 2, 3, 2, 3, 5, 11, 2, 3, 3, 2, 5, 3, 3, 2, 19, 11, 2, 3, 2, 2, 2, 5, 2, 31, 31, 37, 2, 5, 3, 2, 5, 11, 5, 17, 2, 3, 5, 79, 3, 17, 3, 3, 7, 7, 17, 13, 29, 11, 31, 5, 2, 19, 2, 3, 19, 2, 2, 3, 5, 11, 3, 2, 2, 2, 2, 3, 5, 11, 3, 3, 7, 3, 3, 7, 13, 7, 17, 2, 11, 31, 2, 3, 3, 2, 11, 2, 5, 2, 5, 11, 5, 2, 2, 3, 31, 5, 5, 2, 11, 5, 3, 3, 3, 2, 3, 2, 3, 3, 2, 3, 2, 2, 2, 2, 13]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
private theorem arithmetic011 : checkBlock 1653 roster011 = true := by decide +kernel

set_option maxRecDepth 100000 in
private theorem interval011 :
    ∀ n, 1653 ≤ n → n < 1803 → n ≤ 10000 →
      ∃ p < n, p.Prime ∧ (p^2 * (n-p).totient - 1).Prime :=
  checkedInterval 1653 150 roster011 (by decide) arithmetic011

private def roster012 : List ℕ := [11, 7, 2, 3, 2, 19, 13, 2, 2, 2, 13, 2, 2, 2, 7, 3, 2, 2, 3, 3, 23, 23, 7, 41, 13, 3, 29, 5, 2, 29, 23, 5, 7, 2, 3, 7, 7, 2, 7, 13, 2, 2, 2, 3, 5, 2, 3, 43, 53, 2, 11, 3, 2, 2, 3, 2, 2, 17, 11, 7, 31, 2, 2, 3, 5, 7, 13, 2, 3, 5, 13, 3, 2, 13, 3, 2, 3, 3, 7, 3, 23, 3, 31, 101, 37, 7, 3, 5, 23, 31, 17, 2, 2, 11, 2, 37, 31, 5, 2, 2, 5, 3, 13, 23, 3, 29, 11, 11, 11, 7, 11, 23, 11, 2, 3, 2, 2, 59, 5, 11, 5, 2, 2, 3, 2, 2, 5, 19, 17, 59, 3, 2, 2, 2, 3, 5, 2, 29, 11, 7, 2, 5, 13, 2, 17, 3, 2, 31, 3, 13]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
private theorem arithmetic012 : checkBlock 1803 roster012 = true := by decide +kernel

set_option maxRecDepth 100000 in
private theorem interval012 :
    ∀ n, 1803 ≤ n → n < 1953 → n ≤ 10000 →
      ∃ p < n, p.Prime ∧ (p^2 * (n-p).totient - 1).Prime :=
  checkedInterval 1803 150 roster012 (by decide) arithmetic012

private def roster013 : List ℕ := [23, 19, 23, 3, 3, 2, 19, 7, 3, 2, 2, 2, 37, 2, 2, 109, 2, 5, 19, 5, 13, 2, 23, 2, 3, 11, 5, 29, 5, 19, 5, 3, 2, 5, 5, 5, 3, 2, 3, 2, 3, 29, 3, 61, 3, 31, 3, 2, 13, 3, 19, 2, 7, 11, 7, 41, 7, 3, 2, 2, 2, 3, 2, 3, 3, 3, 5, 3, 7, 11, 2, 2, 3, 5, 3, 3, 11, 3, 2, 2, 2, 17, 13, 2, 3, 3, 7, 5, 3, 3, 2, 2, 5, 3, 7, 2, 3, 13, 19, 7, 7, 2, 11, 31, 3, 3, 2, 2, 7, 53, 2, 7, 5, 2, 3, 2, 11, 13, 5, 2, 3, 7, 2, 19, 5, 3, 2, 7, 3, 3, 3, 2, 11, 2, 5, 11, 5, 2, 3, 2, 2, 3, 43, 11, 3, 2, 19, 3, 3, 31]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
private theorem arithmetic013 : checkBlock 1953 roster013 = true := by decide +kernel

set_option maxRecDepth 100000 in
private theorem interval013 :
    ∀ n, 1953 ≤ n → n < 2103 → n ≤ 10000 →
      ∃ p < n, p.Prime ∧ (p^2 * (n-p).totient - 1).Prime :=
  checkedInterval 1953 150 roster013 (by decide) arithmetic013

private def roster014 : List ℕ := [11, 3, 59, 17, 2, 2, 7, 5, 37, 2, 3, 11, 2, 11, 59, 83, 11, 3, 31, 17, 2, 3, 3, 11, 3, 37, 23, 3, 23, 2, 3, 7, 5, 23, 41, 3, 2, 2, 2, 2, 5, 3, 11, 7, 17, 5, 5, 3, 11, 2, 2, 31, 23, 7, 11, 2, 2, 3, 7, 3, 13, 17, 19, 17, 2, 3, 13, 19, 3, 2, 47, 2, 7, 3, 7, 3, 7, 83, 3, 5, 2, 5, 5, 5, 41, 7, 59, 3, 2, 11, 2, 5, 3, 83, 23, 2, 2, 3, 3, 7, 5, 2, 2, 41, 7, 5, 23, 3, 2, 3, 2, 5, 3, 2, 5, 7, 2, 11, 2, 5, 19, 3, 3, 61, 2, 31, 19, 2, 3, 7, 2, 2, 2, 2, 11, 5, 7, 3, 2, 11, 2, 5, 17, 3, 5, 3, 2, 3, 3, 2]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
private theorem arithmetic014 : checkBlock 2103 roster014 = true := by decide +kernel

set_option maxRecDepth 100000 in
private theorem interval014 :
    ∀ n, 2103 ≤ n → n < 2253 → n ≤ 10000 →
      ∃ p < n, p.Prime ∧ (p^2 * (n-p).totient - 1).Prime :=
  checkedInterval 2103 150 roster014 (by decide) arithmetic014

private def roster015 : List ℕ := [2, 3, 19, 3, 5, 11, 5, 13, 3, 2, 2, 2, 3, 61, 2, 2, 37, 2, 19, 3, 2, 23, 3, 2, 3, 3, 2, 5, 19, 5, 5, 7, 2, 3, 3, 2, 3, 5, 5, 5, 17, 11, 13, 3, 3, 17, 11, 3, 2, 11, 3, 3, 2, 3, 3, 5, 2, 11, 23, 3, 2, 3, 2, 83, 101, 3, 2, 5, 3, 2, 13, 2, 3, 13, 2, 3, 2, 13, 3, 3, 13, 2, 13, 41, 3, 13, 11, 3, 3, 5, 47, 2, 3, 31, 13, 7, 7, 29, 2, 11, 47, 2, 3, 31, 3, 17, 3, 2, 3, 3, 2, 37, 2, 11, 2, 13, 2, 5, 5, 29, 2, 5, 47, 11, 5, 2, 29, 3, 3, 3, 3, 2, 3, 23, 11, 67, 5, 2, 2, 3, 2, 3, 11, 2, 5, 2, 17, 11, 3, 11]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
private theorem arithmetic015 : checkBlock 2253 roster015 = true := by decide +kernel

set_option maxRecDepth 100000 in
private theorem interval015 :
    ∀ n, 2253 ≤ n → n < 2403 → n ≤ 10000 →
      ∃ p < n, p.Prime ∧ (p^2 * (n-p).totient - 1).Prime :=
  checkedInterval 2253 150 roster015 (by decide) arithmetic015

private def roster016 : List ℕ := [2, 2, 3, 2, 2, 3, 41, 3, 13, 3, 7, 2, 3, 3, 3, 2, 3, 2, 11, 3, 3, 2, 7, 13, 5, 7, 11, 3, 7, 2, 7, 5, 7, 7, 7, 2, 2, 7, 23, 5, 59, 2, 13, 7, 31, 61, 7, 3, 3, 2, 2, 17, 11, 3, 31, 73, 5, 11, 7, 13, 13, 2, 3, 3, 19, 3, 47, 3, 3, 19, 2, 7, 2, 2, 2, 2, 7, 3, 3, 3, 2, 3, 23, 2, 2, 5, 3, 5, 3, 3, 3, 13, 13, 2, 5, 5, 3, 11, 17, 7, 3, 3, 2, 5, 11, 2, 11, 2, 5, 5, 3, 7, 7, 2, 3, 5, 2, 3, 3, 17, 2, 3, 13, 2, 13, 2, 3, 5, 2, 29, 3, 2, 3, 17, 3, 11, 2, 11, 2, 5, 2, 2, 3, 3, 3, 2, 3, 3, 11, 5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
private theorem arithmetic016 : checkBlock 2403 roster016 = true := by decide +kernel

set_option maxRecDepth 100000 in
private theorem interval016 :
    ∀ n, 2403 ≤ n → n < 2553 → n ≤ 10000 →
      ∃ p < n, p.Prime ∧ (p^2 * (n-p).totient - 1).Prime :=
  checkedInterval 2403 150 roster016 (by decide) arithmetic016

private def roster017 : List ℕ := [7, 17, 3, 43, 2, 2, 2, 3, 13, 43, 41, 2, 31, 2, 3, 83, 7, 2, 2, 3, 11, 73, 2, 2, 5, 11, 2, 3, 5, 2, 3, 11, 11, 3, 23, 5, 41, 2, 5, 5, 5, 7, 5, 3, 2, 2, 17, 17, 11, 89, 5, 101, 2, 2, 23, 3, 3, 23, 7, 2, 3, 67, 11, 5, 43, 7, 2, 83, 2, 2, 13, 2, 2, 2, 2, 2, 2, 3, 41, 3, 3, 3, 31, 3, 3, 7, 11, 3, 7, 3, 7, 2, 2, 2, 5, 2, 3, 2, 5, 2, 5, 3, 3, 2, 3, 3, 3, 13, 2, 7, 11, 5, 3, 3, 19, 2, 2, 11, 3, 5, 41, 3, 5, 5, 3, 3, 5, 3, 13, 23, 11, 3, 5, 2, 3, 5, 17, 31, 3, 11, 7, 17, 23, 2, 2, 43, 2, 2, 5, 2]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
private theorem arithmetic017 : checkBlock 2553 roster017 = true := by decide +kernel

set_option maxRecDepth 100000 in
private theorem interval017 :
    ∀ n, 2553 ≤ n → n < 2703 → n ≤ 10000 →
      ∃ p < n, p.Prime ∧ (p^2 * (n-p).totient - 1).Prime :=
  checkedInterval 2553 150 roster017 (by decide) arithmetic017

private def roster018 : List ℕ := [11, 3, 17, 11, 7, 11, 11, 2, 2, 17, 3, 2, 2, 3, 3, 3, 41, 5, 47, 19, 2, 53, 2, 13, 47, 5, 13, 2, 3, 3, 59, 29, 29, 17, 31, 7, 2, 43, 3, 3, 3, 3, 2, 2, 11, 3, 2, 5, 19, 29, 3, 5, 7, 3, 5, 3, 5, 2, 2, 17, 5, 2, 5, 2, 2, 17, 5, 2, 2, 5, 11, 2, 11, 11, 41, 3, 7, 5, 11, 3, 5, 2, 2, 2, 5, 2, 3, 2, 3, 2, 2, 11, 2, 2, 7, 3, 7, 2, 11, 5, 5, 2, 3, 7, 2, 2, 7, 3, 5, 5, 2, 5, 11, 2, 3, 2, 2, 7, 3, 11, 19, 19, 3, 19, 3, 11, 3, 2, 2, 107, 3, 13, 19, 7, 29, 13, 3, 2, 3, 13, 3, 2, 41, 3, 3, 7, 2, 3, 3, 2]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
private theorem arithmetic018 : checkBlock 2703 roster018 = true := by decide +kernel

set_option maxRecDepth 100000 in
private theorem interval018 :
    ∀ n, 2703 ≤ n → n < 2853 → n ≤ 10000 →
      ∃ p < n, p.Prime ∧ (p^2 * (n-p).totient - 1).Prime :=
  checkedInterval 2703 150 roster018 (by decide) arithmetic018

private def roster019 : List ℕ := [2, 2, 2, 5, 5, 41, 2, 2, 11, 5, 37, 5, 2, 3, 2, 3, 7, 11, 2, 17, 2, 5, 19, 2, 19, 2, 3, 73, 3, 11, 2, 7, 3, 83, 13, 5, 19, 2, 5, 11, 2, 5, 31, 2, 2, 7, 3, 2, 3, 31, 2, 3, 3, 5, 3, 2, 2, 2, 5, 3, 3, 23, 2, 2, 11, 3, 3, 37, 3, 17, 2, 5, 3, 73, 17, 3, 3, 5, 17, 11, 7, 43, 11, 3, 3, 17, 2, 7, 5, 2, 3, 2, 3, 197, 3, 2, 2, 2, 5, 2, 2, 3, 2, 2, 2, 2, 17, 2, 5, 7, 11, 13, 11, 5, 19, 2, 3, 3, 5, 2, 7, 3, 2, 23, 7, 5, 11, 3, 2, 5, 2, 2, 3, 5, 11, 5, 2, 3, 2, 3, 23, 2, 2, 3, 3, 2, 3, 13, 5, 3]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
private theorem arithmetic019 : checkBlock 2853 roster019 = true := by decide +kernel

set_option maxRecDepth 100000 in
private theorem interval019 :
    ∀ n, 2853 ≤ n → n < 3003 → n ≤ 10000 →
      ∃ p < n, p.Prime ∧ (p^2 * (n-p).totient - 1).Prime :=
  checkedInterval 2853 150 roster019 (by decide) arithmetic019

private def roster020 : List ℕ := [7, 29, 13, 3, 3, 3, 2, 3, 11, 3, 37, 5, 3, 11, 3, 13, 13, 17, 2, 2, 2, 19, 29, 3, 11, 31, 3, 2, 31, 11, 5, 2, 11, 3, 3, 17, 2, 2, 11, 59, 47, 5, 3, 2, 3, 41, 3, 5, 17, 2, 3, 3, 7, 3, 2, 2, 3, 2, 7, 3, 2, 3, 7, 7, 2, 3, 2, 13, 3, 5, 2, 11, 7, 13, 3, 2, 2, 3, 3, 3, 2, 2, 107, 3, 5, 19, 3, 2, 11, 3, 7, 23, 5, 3, 2, 3, 19, 31, 3, 2, 2, 5, 23, 2, 11, 37, 2, 3, 29, 5, 3, 5, 2, 2, 2, 7, 3, 7, 5, 5, 2, 7, 3, 5, 13, 2, 7, 3, 2, 19, 17, 53, 2, 2, 7, 3, 7, 5, 5, 31, 5, 13, 13, 2, 7, 2, 5, 2, 2, 2]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
private theorem arithmetic020 : checkBlock 3003 roster020 = true := by decide +kernel

set_option maxRecDepth 100000 in
private theorem interval020 :
    ∀ n, 3003 ≤ n → n < 3153 → n ≤ 10000 →
      ∃ p < n, p.Prime ∧ (p^2 * (n-p).totient - 1).Prime :=
  checkedInterval 3003 150 roster020 (by decide) arithmetic020

private def roster021 : List ℕ := [7, 2, 29, 2, 2, 3, 3, 2, 11, 5, 37, 29, 2, 17, 2, 11, 5, 3, 2, 11, 11, 11, 3, 3, 2, 3, 2, 19, 3, 7, 3, 2, 23, 3, 5, 3, 2, 2, 3, 11, 3, 23, 2, 3, 2, 17, 2, 5, 7, 2, 3, 5, 17, 3, 13, 2, 2, 13, 23, 2, 13, 17, 2, 3, 2, 29, 19, 37, 5, 3, 23, 2, 5, 11, 2, 17, 5, 5, 2, 17, 41, 103, 2, 2, 3, 5, 3, 7, 2, 5, 2, 5, 5, 7, 5, 3, 3, 17, 7, 2, 3, 17, 2, 7, 3, 3, 3, 3, 3, 19, 13, 31, 3, 13, 47, 7, 2, 2, 13, 3, 5, 3, 2, 5, 2, 3, 7, 13, 5, 2, 3, 3, 2, 11, 2, 3, 7, 11, 2, 19, 13, 3, 2, 5, 3, 3, 2, 2, 7, 11]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
private theorem arithmetic021 : checkBlock 3153 roster021 = true := by decide +kernel

set_option maxRecDepth 100000 in
private theorem interval021 :
    ∀ n, 3153 ≤ n → n < 3303 → n ≤ 10000 →
      ∃ p < n, p.Prime ∧ (p^2 * (n-p).totient - 1).Prime :=
  checkedInterval 3153 150 roster021 (by decide) arithmetic021

private def roster022 : List ℕ := [7, 2, 2, 3, 2, 11, 19, 2, 3, 2, 2, 3, 5, 11, 2, 5, 5, 3, 3, 17, 3, 13, 3, 23, 13, 11, 2, 2, 5, 5, 11, 13, 5, 17, 5, 5, 23, 3, 2, 61, 11, 2, 2, 13, 2, 2, 5, 3, 3, 2, 29, 11, 2, 5, 7, 2, 3, 5, 7, 5, 3, 7, 3, 11, 13, 11, 19, 2, 11, 7, 5, 5, 2, 3, 3, 2, 2, 3, 2, 31, 5, 3, 2, 5, 7, 31, 3, 2, 5, 2, 5, 3, 7, 3, 3, 23, 2, 2, 41, 2, 3, 13, 3, 31, 19, 17, 41, 11, 3, 2, 3, 3, 13, 3, 3, 3, 2, 19, 5, 41, 11, 13, 5, 53, 3, 11, 3, 3, 5, 2, 17, 29, 5, 5, 37, 2, 3, 3, 2, 13, 5, 11, 2, 7, 17, 5, 3, 3, 5, 13]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
private theorem arithmetic022 : checkBlock 3303 roster022 = true := by decide +kernel

set_option maxRecDepth 100000 in
private theorem interval022 :
    ∀ n, 3303 ≤ n → n < 3453 → n ≤ 10000 →
      ∃ p < n, p.Prime ∧ (p^2 * (n-p).totient - 1).Prime :=
  checkedInterval 3303 150 roster022 (by decide) arithmetic022

private def roster023 : List ℕ := [3, 13, 2, 79, 29, 7, 83, 17, 41, 2, 19, 3, 19, 2, 3, 3, 13, 3, 3, 43, 2, 31, 3, 13, 5, 5, 23, 23, 13, 2, 2, 2, 23, 3, 5, 3, 7, 2, 3, 11, 3, 5, 13, 2, 7, 3, 5, 2, 19, 2, 2, 29, 13, 5, 13, 19, 3, 11, 3, 13, 7, 7, 3, 3, 3, 3, 7, 3, 2, 2, 3, 3, 2, 2, 23, 2, 7, 7, 5, 3, 3, 3, 7, 5, 3, 2, 11, 2, 7, 13, 2, 2, 2, 5, 5, 2, 7, 13, 2, 11, 97, 11, 2, 2, 2, 2, 71, 3, 5, 11, 3, 3, 13, 3, 2, 2, 7, 2, 5, 17, 3, 53, 23, 3, 3, 3, 29, 2, 3, 17, 5, 2, 2, 2, 11, 11, 7, 5, 5, 29, 5, 5, 3, 2, 13, 2, 37, 2, 5, 3]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
private theorem arithmetic023 : checkBlock 3453 roster023 = true := by decide +kernel

set_option maxRecDepth 100000 in
private theorem interval023 :
    ∀ n, 3453 ≤ n → n < 3603 → n ≤ 10000 →
      ∃ p < n, p.Prime ∧ (p^2 * (n-p).totient - 1).Prime :=
  checkedInterval 3453 150 roster023 (by decide) arithmetic023

private def roster024 : List ℕ := [101, 17, 37, 3, 2, 2, 2, 11, 11, 2, 17, 5, 2, 3, 23, 13, 3, 2, 3, 7, 3, 17, 5, 2, 3, 2, 43, 2, 2, 19, 2, 13, 29, 2, 3, 2, 2, 13, 3, 13, 17, 13, 13, 5, 47, 29, 2, 13, 17, 5, 3, 7, 3, 13, 29, 17, 2, 2, 5, 7, 2, 7, 7, 19, 13, 11, 5, 17, 11, 5, 19, 3, 5, 13, 2, 17, 19, 3, 29, 29, 2, 2, 13, 3, 2, 2, 3, 7, 2, 3, 2, 2, 2, 11, 2, 41, 2, 7, 2, 3, 3, 11, 2, 31, 2, 2, 3, 7, 2, 13, 2, 3, 3, 2, 7, 3, 3, 7, 5, 3, 2, 3, 23, 2, 2, 2, 3, 3, 3, 37, 2, 3, 3, 3, 7, 13, 5, 5, 2, 2, 3, 17, 3, 3, 41, 2, 41, 2, 23, 11]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
private theorem arithmetic024 : checkBlock 3603 roster024 = true := by decide +kernel

set_option maxRecDepth 100000 in
private theorem interval024 :
    ∀ n, 3603 ≤ n → n < 3753 → n ≤ 10000 →
      ∃ p < n, p.Prime ∧ (p^2 * (n-p).totient - 1).Prime :=
  checkedInterval 3603 150 roster024 (by decide) arithmetic024

private def roster025 : List ℕ := [3, 61, 97, 5, 3, 5, 11, 47, 2, 41, 7, 71, 3, 37, 11, 11, 7, 3, 7, 3, 7, 2, 5, 3, 37, 7, 3, 3, 5, 43, 73, 29, 5, 2, 13, 2, 2, 47, 2, 2, 2, 7, 5, 3, 2, 2, 3, 2, 7, 7, 3, 19, 3, 3, 17, 13, 11, 2, 47, 5, 17, 13, 31, 3, 5, 3, 37, 3, 11, 2, 3, 5, 2, 7, 11, 5, 2, 7, 2, 3, 3, 5, 3, 2, 17, 29, 2, 3, 19, 3, 7, 7, 3, 11, 59, 2, 2, 2, 3, 2, 3, 2, 3, 3, 2, 19, 7, 5, 23, 2, 5, 11, 13, 3, 31, 2, 2, 2, 3, 5, 2, 2, 31, 2, 7, 5, 7, 3, 11, 2, 5, 2, 13, 2, 2, 3, 3, 13, 2, 67, 3, 3, 2, 2, 2, 3, 13, 3, 23, 13]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
private theorem arithmetic025 : checkBlock 3753 roster025 = true := by decide +kernel

set_option maxRecDepth 100000 in
private theorem interval025 :
    ∀ n, 3753 ≤ n → n < 3903 → n ≤ 10000 →
      ∃ p < n, p.Prime ∧ (p^2 * (n-p).totient - 1).Prime :=
  checkedInterval 3753 150 roster025 (by decide) arithmetic025

private def roster026 : List ℕ := [19, 5, 2, 3, 13, 47, 3, 3, 7, 5, 3, 5, 19, 37, 31, 2, 13, 11, 2, 23, 7, 2, 5, 37, 2, 113, 13, 5, 11, 2, 11, 7, 5, 2, 29, 2, 3, 3, 97, 2, 2, 3, 2, 5, 3, 53, 3, 11, 17, 11, 13, 2, 3, 5, 31, 17, 3, 23, 2, 5, 37, 13, 2, 2, 2, 2, 5, 5, 5, 3, 2, 2, 7, 17, 5, 2, 2, 17, 5, 13, 2, 7, 19, 3, 3, 5, 2, 47, 13, 47, 7, 13, 2, 19, 23, 47, 2, 13, 2, 3, 41, 3, 2, 3, 2, 5, 5, 13, 13, 3, 5, 23, 3, 3, 2, 3, 2, 2, 5, 3, 5, 2, 3, 17, 2, 2, 2, 2, 23, 5, 3, 7, 2, 11, 3, 47, 2, 3, 101, 5, 5, 2, 2, 3, 5, 7, 2, 2, 17, 13]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
private theorem arithmetic026 : checkBlock 3903 roster026 = true := by decide +kernel

set_option maxRecDepth 100000 in
private theorem interval026 :
    ∀ n, 3903 ≤ n → n < 4053 → n ≤ 10000 →
      ∃ p < n, p.Prime ∧ (p^2 * (n-p).totient - 1).Prime :=
  checkedInterval 3903 150 roster026 (by decide) arithmetic026

private def roster027 : List ℕ := [3, 7, 7, 13, 2, 41, 2, 2, 3, 3, 7, 2, 5, 5, 3, 7, 13, 11, 5, 13, 3, 23, 3, 5, 2, 13, 2, 11, 3, 5, 2, 2, 43, 5, 13, 7, 3, 2, 2, 5, 11, 2, 3, 7, 2, 2, 2, 19, 5, 13, 29, 7, 2, 3, 73, 41, 7, 2, 53, 3, 3, 2, 19, 2, 2, 2, 11, 17, 5, 11, 13, 2, 2, 17, 3, 13, 19, 5, 19, 17, 3, 3, 23, 13, 5, 13, 11, 19, 7, 53, 37, 3, 5, 2, 3, 2, 41, 5, 5, 7, 2, 2, 2, 2, 2, 7, 5, 11, 2, 2, 7, 3, 3, 11, 13, 5, 2, 127, 3, 3, 2, 2, 53, 5, 3, 3, 2, 17, 5, 3, 2, 2, 3, 5, 11, 7, 2, 31, 3, 5, 2, 3, 3, 37, 3, 7, 29, 3, 7, 5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
private theorem arithmetic027 : checkBlock 4053 roster027 = true := by decide +kernel

set_option maxRecDepth 100000 in
private theorem interval027 :
    ∀ n, 4053 ≤ n → n < 4203 → n ≤ 10000 →
      ∃ p < n, p.Prime ∧ (p^2 * (n-p).totient - 1).Prime :=
  checkedInterval 4053 150 roster027 (by decide) arithmetic027

private def roster028 : List ℕ := [37, 3, 3, 3, 3, 3, 29, 5, 2, 2, 67, 3, 5, 11, 11, 53, 19, 11, 2, 2, 7, 3, 2, 2, 2, 2, 23, 3, 11, 7, 29, 3, 29, 127, 2, 5, 3, 3, 11, 17, 19, 2, 3, 3, 3, 47, 2, 101, 2, 5, 7, 3, 7, 13, 2, 2, 2, 3, 7, 3, 3, 7, 37, 43, 41, 3, 7, 3, 5, 23, 3, 11, 3, 2, 31, 2, 83, 2, 29, 3, 3, 3, 3, 29, 17, 7, 2, 2, 5, 5, 29, 7, 3, 41, 3, 5, 2, 13, 11, 2, 61, 2, 5, 11, 23, 5, 2, 11, 11, 5, 2, 2, 17, 2, 3, 37, 2, 17, 2, 5, 7, 5, 2, 3, 2, 19, 5, 3, 31, 2, 3, 2, 2, 5, 37, 3, 113, 3, 2, 3, 3, 11, 5, 3, 2, 5, 3, 3, 29, 5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
private theorem arithmetic028 : checkBlock 4203 roster028 = true := by decide +kernel

set_option maxRecDepth 100000 in
private theorem interval028 :
    ∀ n, 4203 ≤ n → n < 4353 → n ≤ 10000 →
      ∃ p < n, p.Prime ∧ (p^2 * (n-p).totient - 1).Prime :=
  checkedInterval 4203 150 roster028 (by decide) arithmetic028

private def roster029 : List ℕ := [3, 2, 7, 3, 2, 2, 5, 7, 5, 2, 2, 2, 7, 2, 5, 5, 5, 7, 19, 5, 11, 19, 19, 31, 3, 19, 43, 2, 13, 3, 2, 2, 11, 5, 3, 7, 11, 47, 3, 13, 3, 3, 3, 2, 2, 2, 11, 3, 7, 13, 5, 29, 3, 73, 11, 2, 5, 7, 3, 3, 7, 3, 47, 3, 3, 3, 3, 2, 3, 2, 5, 2, 17, 2, 5, 3, 2, 13, 3, 5, 2, 2, 11, 2, 41, 2, 5, 2, 5, 19, 11, 7, 2, 71, 23, 5, 2, 2, 17, 2, 13, 5, 7, 11, 3, 5, 7, 29, 13, 2, 2, 2, 13, 7, 3, 2, 2, 3, 5, 7, 5, 5, 2, 3, 3, 89, 11, 2, 5, 2, 5, 2, 7, 13, 2, 71, 2, 2, 3, 23, 3, 3, 17, 2, 3, 13, 5, 11, 2, 2]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
private theorem arithmetic029 : checkBlock 4353 roster029 = true := by decide +kernel

set_option maxRecDepth 100000 in
private theorem interval029 :
    ∀ n, 4353 ≤ n → n < 4503 → n ≤ 10000 →
      ∃ p < n, p.Prime ∧ (p^2 * (n-p).totient - 1).Prime :=
  checkedInterval 4353 150 roster029 (by decide) arithmetic029

private def roster030 : List ℕ := [3, 2, 3, 11, 3, 5, 3, 37, 3, 3, 2, 5, 2, 47, 11, 3, 23, 7, 3, 19, 3, 2, 3, 3, 13, 7, 5, 3, 23, 2, 3, 23, 7, 3, 3, 11, 2, 5, 3, 3, 11, 2, 13, 3, 5, 3, 41, 2, 2, 13, 2, 3, 2, 2, 13, 2, 2, 3, 7, 19, 41, 3, 17, 17, 5, 2, 3, 13, 101, 13, 2, 2, 5, 47, 5, 3, 5, 5, 37, 11, 7, 3, 5, 2, 2, 7, 3, 5, 29, 7, 11, 13, 2, 3, 3, 7, 3, 2, 13, 2, 2, 19, 3, 2, 2, 2, 3, 2, 5, 3, 13, 11, 2, 2, 13, 11, 19, 7, 3, 37, 31, 2, 3, 5, 3, 2, 7, 2, 11, 5, 3, 2, 5, 2, 2, 3, 5, 53, 13, 19, 3, 13, 3, 2, 13, 13, 5, 19, 23, 2]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
private theorem arithmetic030 : checkBlock 4503 roster030 = true := by decide +kernel

set_option maxRecDepth 100000 in
private theorem interval030 :
    ∀ n, 4503 ≤ n → n < 4653 → n ≤ 10000 →
      ∃ p < n, p.Prime ∧ (p^2 * (n-p).totient - 1).Prime :=
  checkedInterval 4503 150 roster030 (by decide) arithmetic030

private def roster031 : List ℕ := [3, 3, 7, 2, 5, 2, 17, 3, 3, 23, 3, 11, 5, 3, 3, 5, 2, 113, 2, 53, 43, 5, 71, 41, 2, 7, 5, 5, 29, 3, 7, 3, 3, 11, 3, 29, 2, 2, 2, 23, 11, 3, 3, 7, 11, 211, 17, 2, 2, 3, 2, 11, 3, 17, 47, 19, 2, 23, 3, 13, 2, 13, 11, 5, 7, 7, 13, 3, 2, 13, 3, 2, 5, 2, 19, 2, 2, 2, 2, 2, 2, 2, 5, 2, 11, 13, 13, 3, 2, 13, 5, 2, 2, 3, 7, 5, 17, 3, 3, 7, 13, 17, 2, 43, 2, 3, 5, 3, 2, 2, 2, 7, 3, 7, 37, 5, 2, 3, 41, 3, 13, 7, 17, 37, 2, 17, 23, 2, 2, 13, 5, 2, 3, 2, 5, 5, 7, 7, 11, 13, 3, 5, 11, 17, 13, 13, 2, 3, 19, 2]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
private theorem arithmetic031 : checkBlock 4653 roster031 = true := by decide +kernel

set_option maxRecDepth 100000 in
private theorem interval031 :
    ∀ n, 4653 ≤ n → n < 4803 → n ≤ 10000 →
      ∃ p < n, p.Prime ∧ (p^2 * (n-p).totient - 1).Prime :=
  checkedInterval 4653 150 roster031 (by decide) arithmetic031

private def roster032 : List ℕ := [3, 2, 2, 11, 2, 3, 5, 7, 3, 2, 2, 5, 11, 5, 3, 5, 3, 5, 2, 17, 5, 11, 29, 11, 2, 43, 3, 41, 2, 3, 2, 11, 3, 5, 5, 17, 3, 11, 3, 2, 11, 3, 13, 11, 7, 17, 2, 19, 19, 19, 2, 3, 71, 3, 3, 3, 19, 3, 19, 43, 5, 7, 2, 53, 83, 67, 2, 5, 2, 7, 7, 47, 31, 2, 5, 2, 5, 5, 2, 13, 2, 37, 7, 5, 3, 7, 2, 2, 17, 3, 17, 3, 7, 5, 3, 2, 11, 13, 3, 2, 2, 2, 5, 2, 3, 3, 3, 3, 11, 3, 29, 2, 3, 5, 13, 13, 2, 13, 41, 2, 2, 31, 2, 2, 2, 3, 2, 3, 2, 11, 3, 5, 2, 7, 2, 17, 7, 7, 7, 2, 2, 2, 37, 11, 2, 2, 3, 2, 3, 2]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
private theorem arithmetic032 : checkBlock 4803 roster032 = true := by decide +kernel

set_option maxRecDepth 100000 in
private theorem interval032 :
    ∀ n, 4803 ≤ n → n < 4953 → n ≤ 10000 →
      ∃ p < n, p.Prime ∧ (p^2 * (n-p).totient - 1).Prime :=
  checkedInterval 4803 150 roster032 (by decide) arithmetic032

private def roster033 : List ℕ := [3, 2, 3, 23, 3, 23, 3, 5, 3, 13, 2, 2, 3, 3, 2, 19, 31, 11, 5, 2, 97, 5, 5, 5, 37, 7, 5, 5, 3, 5, 3, 5, 7, 2, 13, 23, 11, 11, 5, 17, 47, 2, 11, 3, 7, 3, 11, 3, 2, 5, 2, 11, 3, 5, 2, 2, 5, 5, 5, 5, 7, 2, 5, 23, 3, 5, 3, 79, 2, 3, 53, 3, 5, 3, 2, 17, 7, 3, 5, 13, 7, 7, 2, 2, 3, 5, 2, 13, 101, 3, 5, 2, 3, 5, 2, 23, 7, 2, 2, 3, 13, 2, 5, 19, 5, 13, 23, 2, 2, 2, 2, 3, 3, 2, 7, 73, 2, 3, 2, 5, 13, 2, 2, 2, 5, 11, 5, 2, 5, 13, 3, 2, 37, 11, 3, 47, 3, 11, 17, 7, 2, 89, 3, 3, 3, 5, 3, 7, 19, 2]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
private theorem arithmetic033 : checkBlock 4953 roster033 = true := by decide +kernel

set_option maxRecDepth 100000 in
private theorem interval033 :
    ∀ n, 4953 ≤ n → n < 5103 → n ≤ 10000 →
      ∃ p < n, p.Prime ∧ (p^2 * (n-p).totient - 1).Prime :=
  checkedInterval 4953 150 roster033 (by decide) arithmetic033

private def roster034 : List ℕ := [2, 7, 41, 31, 2, 47, 41, 3, 2, 2, 3, 2, 13, 2, 3, 2, 2, 5, 7, 2, 7, 3, 5, 3, 3, 3, 3, 7, 3, 47, 11, 5, 41, 3, 3, 5, 3, 2, 2, 2, 11, 3, 5, 2, 13, 2, 37, 7, 3, 11, 2, 2, 11, 2, 3, 2, 2, 17, 3, 11, 7, 3, 2, 5, 23, 5, 2, 7, 5, 31, 41, 7, 23, 17, 2, 47, 2, 3, 7, 2, 2, 5, 83, 2, 2, 7, 3, 3, 3, 2, 41, 19, 3, 19, 2, 2, 3, 7, 13, 29, 2, 5, 11, 2, 2, 2, 3, 7, 3, 31, 3, 5, 11, 5, 2, 7, 3, 5, 2, 5, 11, 5, 5, 3, 5, 23, 2, 31, 2, 5, 11, 2, 3, 2, 29, 37, 11, 2, 2, 19, 2, 43, 2, 5, 17, 2, 2, 37, 3, 2]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
private theorem arithmetic034 : checkBlock 5103 roster034 = true := by decide +kernel

set_option maxRecDepth 100000 in
private theorem interval034 :
    ∀ n, 5103 ≤ n → n < 5253 → n ≤ 10000 →
      ∃ p < n, p.Prime ∧ (p^2 * (n-p).totient - 1).Prime :=
  checkedInterval 5103 150 roster034 (by decide) arithmetic034

private def roster035 : List ℕ := [3, 7, 3, 2, 3, 2, 3, 3, 3, 29, 11, 3, 3, 2, 13, 3, 2, 7, 3, 3, 17, 7, 3, 37, 3, 3, 17, 3, 3, 2, 3, 7, 17, 2, 5, 2, 61, 2, 17, 89, 7, 2, 5, 5, 3, 2, 11, 11, 2, 3, 2, 41, 3, 2, 5, 7, 3, 2, 23, 13, 3, 13, 2, 61, 5, 3, 2, 2, 13, 2, 3, 3, 7, 2, 47, 113, 3, 2, 2, 3, 2, 2, 3, 2, 2, 7, 2, 13, 17, 5, 2, 3, 3, 31, 5, 3, 2, 23, 5, 5, 3, 2, 5, 11, 3, 2, 3, 47, 29, 2, 5, 23, 2, 2, 2, 97, 2, 3, 2, 5, 5, 5, 37, 7, 29, 2, 11, 5, 2, 47, 17, 7, 7, 7, 19, 13, 13, 3, 3, 2, 31, 11, 5, 2, 31, 2, 3, 3, 3, 59]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
private theorem arithmetic035 : checkBlock 5253 roster035 = true := by decide +kernel

set_option maxRecDepth 100000 in
private theorem interval035 :
    ∀ n, 5253 ≤ n → n < 5403 → n ≤ 10000 →
      ∃ p < n, p.Prime ∧ (p^2 * (n-p).totient - 1).Prime :=
  checkedInterval 5253 150 roster035 (by decide) arithmetic035

private def roster036 : List ℕ := [3, 73, 3, 31, 17, 149, 13, 31, 17, 17, 37, 3, 2, 37, 17, 3, 47, 2, 31, 3, 5, 5, 19, 5, 3, 2, 3, 17, 37, 13, 3, 3, 2, 3, 43, 5, 13, 7, 13, 2, 17, 2, 2, 101, 2, 2, 2, 11, 5, 3, 11, 2, 7, 11, 5, 3, 2, 13, 3, 11, 13, 7, 2, 5, 2, 23, 7, 3, 29, 5, 11, 2, 3, 2, 2, 3, 29, 5, 2, 31, 3, 5, 3, 19, 13, 2, 3, 3, 2, 3, 2, 241, 2, 2, 23, 5, 11, 3, 5, 41, 5, 3, 5, 7, 17, 17, 3, 2, 3, 3, 3, 3, 29, 3, 23, 3, 17, 2, 7, 13, 2, 11, 17, 5, 2, 17, 11, 13, 17, 2, 7, 5, 11, 3, 2, 3, 3, 2, 7, 2, 2, 19, 3, 53, 3, 3, 2, 3, 3, 11]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
private theorem arithmetic036 : checkBlock 5403 roster036 = true := by decide +kernel

set_option maxRecDepth 100000 in
private theorem interval036 :
    ∀ n, 5403 ≤ n → n < 5553 → n ≤ 10000 →
      ∃ p < n, p.Prime ∧ (p^2 * (n-p).totient - 1).Prime :=
  checkedInterval 5403 150 roster036 (by decide) arithmetic036

private def roster037 : List ℕ := [3, 2, 2, 5, 29, 3, 3, 71, 3, 2, 2, 5, 2, 7, 7, 2, 2, 3, 2, 3, 2, 5, 3, 3, 3, 17, 2, 13, 23, 5, 3, 2, 2, 3, 31, 2, 2, 2, 3, 5, 3, 7, 3, 13, 2, 3, 2, 3, 5, 5, 5, 3, 2, 3, 2, 7, 2, 5, 2, 2, 2, 2, 23, 5, 3, 2, 3, 5, 47, 7, 5, 2, 7, 5, 3, 5, 17, 11, 19, 11, 3, 3, 2, 2, 2, 13, 3, 5, 41, 3, 7, 7, 2, 13, 2, 7, 5, 5, 3, 7, 7, 2, 7, 3, 3, 23, 3, 2, 5, 7, 11, 23, 2, 5, 2, 7, 5, 5, 3, 5, 23, 13, 19, 13, 3, 2, 43, 37, 5, 3, 41, 3, 2, 3, 11, 5, 3, 2, 2, 5, 2, 7, 11, 2, 3, 7, 3, 3, 2, 23]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
private theorem arithmetic037 : checkBlock 5553 roster037 = true := by decide +kernel

set_option maxRecDepth 100000 in
private theorem interval037 :
    ∀ n, 5553 ≤ n → n < 5703 → n ≤ 10000 →
      ∃ p < n, p.Prime ∧ (p^2 * (n-p).totient - 1).Prime :=
  checkedInterval 5553 150 roster037 (by decide) arithmetic037

private def roster038 : List ℕ := [3, 2, 2, 2, 2, 2, 2, 3, 2, 11, 37, 2, 5, 2, 3, 2, 3, 11, 2, 3, 5, 37, 2, 2, 7, 2, 2, 43, 2, 2, 3, 5, 11, 7, 19, 13, 2, 2, 5, 13, 5, 2, 7, 11, 5, 23, 19, 3, 3, 19, 11, 3, 2, 7, 47, 2, 17, 59, 5, 2, 2, 2, 41, 2, 3, 5, 13, 2, 2, 23, 7, 2, 3, 3, 43, 3, 3, 3, 5, 11, 3, 2, 7, 7, 5, 13, 7, 3, 7, 2, 2, 2, 2, 3, 5, 11, 11, 5, 37, 23, 13, 2, 3, 3, 3, 5, 37, 2, 7, 3, 2, 11, 5, 2, 3, 7, 107, 17, 3, 2, 2, 3, 41, 3, 11, 2, 53, 3, 2, 11, 3, 5, 2, 11, 37, 5, 2, 3, 29, 3, 5, 2, 19, 7, 37, 53, 2, 13, 5, 3]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
private theorem arithmetic038 : checkBlock 5703 roster038 = true := by decide +kernel

set_option maxRecDepth 100000 in
private theorem interval038 :
    ∀ n, 5703 ≤ n → n < 5853 → n ≤ 10000 →
      ∃ p < n, p.Prime ∧ (p^2 * (n-p).totient - 1).Prime :=
  checkedInterval 5703 150 roster038 (by decide) arithmetic038

private def roster039 : List ℕ := [2, 19, 5, 3, 2, 5, 17, 7, 2, 2, 3, 13, 13, 7, 5, 3, 3, 7, 43, 7, 7, 71, 31, 2, 61, 3, 2, 7, 7, 3, 7, 3, 3, 13, 3, 11, 113, 17, 3, 11, 19, 3, 7, 2, 2, 2, 31, 5, 7, 3, 3, 2, 3, 3, 11, 2, 7, 2, 3, 2, 17, 2, 2, 53, 7, 17, 2, 3, 13, 5, 13, 7, 2, 2, 2, 19, 5, 2, 3, 3, 2, 3, 2, 3, 3, 5, 2, 3, 3, 3, 3, 13, 3, 23, 3, 2, 37, 2, 5, 11, 2, 5, 71, 5, 2, 2, 3, 2, 149, 5, 2, 2, 31, 2, 5, 13, 5, 2, 3, 3, 17, 5, 7, 2, 3, 3, 5, 2, 3, 2, 7, 3, 2, 3, 3, 2, 3, 7, 5, 17, 13, 79, 2, 13, 5, 5, 53, 3, 2, 11]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
private theorem arithmetic039 : checkBlock 5853 roster039 = true := by decide +kernel

set_option maxRecDepth 100000 in
private theorem interval039 :
    ∀ n, 5853 ≤ n → n < 6003 → n ≤ 10000 →
      ∃ p < n, p.Prime ∧ (p^2 * (n-p).totient - 1).Prime :=
  checkedInterval 5853 150 roster039 (by decide) arithmetic039

private def roster040 : List ℕ := [11, 5, 2, 7, 29, 5, 2, 53, 5, 7, 3, 7, 5, 2, 2, 13, 2, 3, 3, 7, 3, 3, 2, 11, 19, 11, 5, 11, 29, 3, 2, 71, 7, 5, 13, 7, 5, 2, 23, 37, 3, 2, 5, 3, 2, 3, 3, 2, 3, 11, 2, 61, 3, 5, 3, 7, 2, 37, 47, 5, 59, 7, 3, 53, 2, 59, 3, 2, 3, 47, 2, 2, 11, 2, 2, 2, 2, 11, 7, 7, 5, 3, 2, 2, 13, 13, 2, 23, 17, 5, 2, 29, 2, 5, 5, 3, 3, 3, 2, 5, 3, 7, 3, 3, 2, 3, 3, 3, 3, 2, 13, 97, 17, 5, 7, 3, 17, 3, 3, 2, 5, 2, 3, 2, 3, 3, 7, 5, 7, 2, 3, 2, 2, 2, 11, 13, 5, 11, 2, 2, 3, 2, 23, 2, 11, 3, 5, 29, 5, 5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
private theorem arithmetic040 : checkBlock 6003 roster040 = true := by decide +kernel

set_option maxRecDepth 100000 in
private theorem interval040 :
    ∀ n, 6003 ≤ n → n < 6153 → n ≤ 10000 →
      ∃ p < n, p.Prime ∧ (p^2 * (n-p).totient - 1).Prime :=
  checkedInterval 6003 150 roster040 (by decide) arithmetic040

private def roster041 : List ℕ := [13, 31, 3, 2, 3, 3, 5, 3, 3, 7, 5, 2, 19, 3, 7, 7, 3, 2, 23, 11, 5, 11, 11, 3, 19, 17, 2, 3, 3, 3, 19, 5, 23, 5, 3, 11, 3, 97, 23, 2, 3, 5, 3, 29, 73, 7, 61, 3, 41, 11, 3, 2, 5, 3, 53, 17, 3, 3, 3, 3, 13, 3, 2, 2, 3, 2, 3, 13, 7, 5, 5, 11, 61, 7, 13, 2, 2, 13, 19, 2, 5, 2, 3, 5, 5, 19, 2, 11, 5, 2, 13, 2, 19, 41, 5, 3, 7, 5, 5, 11, 7, 3, 3, 3, 3, 7, 3, 2, 19, 7, 7, 3, 47, 31, 3, 2, 2, 2, 5, 5, 3, 7, 2, 5, 37, 17, 7, 7, 2, 5, 131, 7, 17, 3, 17, 13, 11, 29, 3, 11, 2, 2, 37, 5, 13, 7, 17, 2, 43, 3]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
private theorem arithmetic041 : checkBlock 6153 roster041 = true := by decide +kernel

set_option maxRecDepth 100000 in
private theorem interval041 :
    ∀ n, 6153 ≤ n → n < 6303 → n ≤ 10000 →
      ∃ p < n, p.Prime ∧ (p^2 * (n-p).totient - 1).Prime :=
  checkedInterval 6153 150 roster041 (by decide) arithmetic041

private def roster042 : List ℕ := [3, 7, 2, 41, 11, 5, 3, 2, 13, 2, 3, 5, 17, 3, 3, 11, 3, 3, 53, 3, 7, 3, 11, 3, 2, 2, 2, 23, 7, 2, 2, 13, 2, 5, 3, 5, 2, 2, 11, 2, 3, 7, 2, 2, 3, 7, 2, 3, 5, 2, 2, 2, 31, 2, 7, 2, 2, 13, 19, 3, 2, 13, 3, 41, 13, 3, 2, 2, 2, 7, 3, 3, 7, 2, 2, 13, 2, 3, 13, 7, 17, 3, 19, 2, 3, 2, 3, 3, 17, 2, 7, 3, 5, 2, 17, 7, 2, 7, 3, 3, 2, 53, 17, 2, 2, 3, 3, 2, 2, 3, 3, 3, 3, 2, 5, 2, 11, 13, 2, 3, 2, 23, 29, 2, 2, 2, 2, 7, 23, 2, 31, 2, 2, 13, 2, 3, 11, 5, 3, 2, 2, 7, 3, 2, 13, 7, 13, 2, 3, 2]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
private theorem arithmetic042 : checkBlock 6303 roster042 = true := by decide +kernel

set_option maxRecDepth 100000 in
private theorem interval042 :
    ∀ n, 6303 ≤ n → n < 6453 → n ≤ 10000 →
      ∃ p < n, p.Prime ∧ (p^2 * (n-p).totient - 1).Prime :=
  checkedInterval 6303 150 roster042 (by decide) arithmetic042

private def roster043 : List ℕ := [2, 3, 5, 19, 2, 3, 23, 2, 11, 37, 23, 5, 11, 2, 2, 2, 5, 2, 5, 3, 2, 23, 11, 5, 53, 19, 2, 2, 2, 2, 2, 2, 7, 2, 37, 5, 31, 2, 5, 5, 3, 11, 7, 71, 13, 23, 2, 5, 2, 7, 2, 3, 2, 3, 53, 2, 11, 2, 5, 5, 3, 2, 3, 17, 3, 11, 13, 5, 13, 5, 3, 3, 37, 3, 17, 13, 2, 2, 2, 13, 2, 3, 2, 2, 19, 5, 5, 13, 3, 2, 3, 11, 3, 13, 2, 2, 2, 3, 2, 2, 3, 2, 3, 3, 2, 2, 2, 7, 5, 3, 3, 19, 3, 7, 11, 2, 11, 13, 23, 2, 3, 2, 11, 5, 2, 13, 3, 2, 2, 2, 17, 3, 3, 2, 5, 2, 11, 89, 11, 3, 2, 7, 17, 2, 13, 5, 3, 47, 13, 37]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
private theorem arithmetic043 : checkBlock 6453 roster043 = true := by decide +kernel

set_option maxRecDepth 100000 in
private theorem interval043 :
    ∀ n, 6453 ≤ n → n < 6603 → n ≤ 10000 →
      ∃ p < n, p.Prime ∧ (p^2 * (n-p).totient - 1).Prime :=
  checkedInterval 6453 150 roster043 (by decide) arithmetic043

private def roster044 : List ℕ := [11, 11, 11, 3, 5, 2, 2, 3, 17, 2, 7, 17, 3, 3, 3, 7, 11, 23, 11, 2, 17, 2, 3, 2, 17, 17, 7, 7, 5, 2, 5, 11, 7, 7, 3, 2, 7, 3, 67, 11, 13, 7, 5, 97, 2, 29, 11, 2, 2, 7, 17, 5, 7, 2, 13, 103, 3, 3, 13, 2, 3, 13, 41, 31, 37, 29, 7, 2, 2, 11, 5, 2, 2, 5, 3, 5, 2, 2, 2, 3, 11, 5, 2, 17, 43, 2, 2, 2, 3, 2, 2, 2, 3, 5, 2, 7, 2, 5, 23, 2, 131, 31, 13, 3, 2, 2, 2, 5, 3, 7, 3, 7, 5, 3, 17, 2, 2, 3, 7, 2, 2, 11, 11, 5, 37, 3, 13, 5, 3, 47, 5, 3, 2, 13, 3, 7, 7, 3, 53, 19, 2, 17, 31, 3, 7, 2, 3, 2, 2, 19]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
private theorem arithmetic044 : checkBlock 6603 roster044 = true := by decide +kernel

set_option maxRecDepth 100000 in
private theorem interval044 :
    ∀ n, 6603 ≤ n → n < 6753 → n ≤ 10000 →
      ∃ p < n, p.Prime ∧ (p^2 * (n-p).totient - 1).Prime :=
  checkedInterval 6603 150 roster044 (by decide) arithmetic044

private def roster045 : List ℕ := [5, 3, 113, 2, 3, 7, 3, 2, 7, 3, 11, 23, 3, 2, 2, 2, 2, 2, 7, 3, 7, 5, 7, 5, 2, 2, 11, 3, 3, 3, 3, 53, 3, 61, 11, 5, 3, 2, 23, 19, 17, 5, 7, 2, 3, 23, 2, 3, 13, 53, 2, 3, 37, 23, 13, 7, 2, 2, 13, 3, 11, 2, 2, 3, 5, 7, 7, 13, 13, 73, 3, 53, 3, 13, 2, 3, 3, 5, 11, 61, 3, 2, 3, 2, 5, 71, 2, 19, 17, 2, 3, 3, 11, 3, 3, 3, 5, 2, 149, 3, 2, 3, 7, 5, 2, 3, 23, 3, 3, 3, 2, 13, 19, 3, 5, 3, 2, 2, 7, 11, 2, 31, 2, 37, 3, 5, 11, 2, 5, 5, 2, 5, 2, 2, 7, 2, 2, 5, 5, 3, 2, 11, 2, 5, 3, 2, 47, 17, 5, 2]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
private theorem arithmetic045 : checkBlock 6753 roster045 = true := by decide +kernel

set_option maxRecDepth 100000 in
private theorem interval045 :
    ∀ n, 6753 ≤ n → n < 6903 → n ≤ 10000 →
      ∃ p < n, p.Prime ∧ (p^2 * (n-p).totient - 1).Prime :=
  checkedInterval 6753 150 roster045 (by decide) arithmetic045

private def roster046 : List ℕ := [2, 13, 2, 17, 2, 2, 7, 2, 29, 5, 5, 3, 7, 29, 29, 3, 3, 11, 2, 3, 3, 5, 3, 7, 2, 5, 13, 3, 31, 5, 3, 7, 5, 3, 3, 5, 3, 7, 13, 2, 47, 2, 37, 2, 2, 19, 5, 5, 2, 23, 11, 2, 2, 5, 5, 5, 7, 3, 3, 7, 3, 2, 23, 3, 3, 3, 3, 2, 2, 5, 3, 7, 7, 13, 3, 13, 7, 41, 5, 3, 5, 3, 41, 29, 19, 7, 3, 2, 2, 5, 3, 2, 2, 5, 2, 89, 2, 97, 3, 7, 3, 2, 5, 13, 5, 277, 11, 5, 11, 31, 13, 5, 11, 5, 11, 29, 19, 3, 7, 2, 2, 3, 2, 5, 83, 19, 3, 5, 29, 3, 3, 2, 2, 41, 2, 5, 3, 2, 2, 7, 3, 3, 3, 3, 13, 2, 2, 3, 13, 3]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
private theorem arithmetic046 : checkBlock 6903 roster046 = true := by decide +kernel

set_option maxRecDepth 100000 in
private theorem interval046 :
    ∀ n, 6903 ≤ n → n < 7053 → n ≤ 10000 →
      ∃ p < n, p.Prime ∧ (p^2 * (n-p).totient - 1).Prime :=
  checkedInterval 6903 150 roster046 (by decide) arithmetic046

private def roster047 : List ℕ := [7, 19, 13, 3, 29, 5, 3, 13, 3, 41, 2, 5, 3, 17, 3, 7, 17, 3, 7, 3, 3, 3, 2, 7, 3, 5, 2, 19, 7, 5, 2, 2, 3, 2, 5, 2, 2, 2, 17, 11, 11, 3, 7, 5, 11, 23, 37, 2, 17, 3, 11, 3, 29, 5, 13, 2, 3, 2, 5, 2, 5, 3, 2, 17, 2, 7, 11, 7, 2, 173, 3, 5, 3, 7, 7, 17, 3, 19, 19, 2, 7, 3, 11, 5, 73, 2, 13, 11, 5, 2, 2, 3, 61, 3, 11, 3, 3, 3, 5, 11, 3, 5, 5, 3, 23, 2, 2, 17, 2, 23, 13, 23, 11, 7, 3, 2, 3, 29, 2, 31, 17, 2, 5, 7, 11, 2, 2, 37, 11, 7, 5, 41, 7, 3, 11, 13, 3, 47, 11, 3, 3, 19, 11, 7, 31, 3, 2, 43, 3, 71]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
private theorem arithmetic047 : checkBlock 7053 roster047 = true := by decide +kernel

set_option maxRecDepth 100000 in
private theorem interval047 :
    ∀ n, 7053 ≤ n → n < 7203 → n ≤ 10000 →
      ∃ p < n, p.Prime ∧ (p^2 * (n-p).totient - 1).Prime :=
  checkedInterval 7053 150 roster047 (by decide) arithmetic047

private def roster048 : List ℕ := [11, 7, 31, 5, 5, 107, 3, 3, 5, 2, 3, 5, 3, 2, 5, 2, 5, 3, 2, 7, 2, 47, 5, 3, 3, 2, 3, 53, 13, 5, 2, 11, 7, 5, 5, 11, 3, 3, 2, 2, 2, 13, 5, 2, 2, 73, 5, 3, 3, 3, 5, 3, 13, 3, 47, 13, 11, 2, 2, 2, 11, 2, 23, 7, 5, 11, 127, 3, 5, 7, 2, 3, 3, 2, 2, 2, 11, 11, 11, 7, 2, 11, 13, 3, 2, 23, 2, 5, 19, 41, 41, 13, 2, 2, 2, 13, 5, 5, 7, 2, 3, 7, 5, 3, 2, 23, 19, 23, 2, 17, 19, 2, 2, 2, 5, 7, 3, 5, 7, 17, 17, 2, 11, 2, 3, 17, 5, 2, 2, 19, 5, 2, 2, 7, 2, 2, 5, 3, 5, 17, 5, 3, 3, 3, 2, 3, 2, 5, 3, 2]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
private theorem arithmetic048 : checkBlock 7203 roster048 = true := by decide +kernel

set_option maxRecDepth 100000 in
private theorem interval048 :
    ∀ n, 7203 ≤ n → n < 7353 → n ≤ 10000 →
      ∃ p < n, p.Prime ∧ (p^2 * (n-p).totient - 1).Prime :=
  checkedInterval 7203 150 roster048 (by decide) arithmetic048

private def roster049 : List ℕ := [2, 11, 2, 3, 3, 2, 3, 73, 11, 11, 2, 2, 3, 3, 2, 3, 2, 2, 3, 2, 2, 5, 11, 11, 5, 5, 3, 2, 2, 11, 2, 2, 13, 5, 7, 2, 19, 2, 29, 2, 7, 13, 2, 2, 11, 2, 3, 2, 3, 2, 2, 11, 2, 11, 31, 2, 2, 2, 2, 2, 3, 7, 19, 17, 5, 2, 2, 2, 29, 7, 5, 2, 3, 3, 17, 13, 2, 2, 2, 29, 3, 11, 11, 7, 19, 2, 41, 3, 3, 5, 7, 2, 3, 2, 3, 17, 23, 11, 7, 2, 17, 3, 3, 7, 3, 19, 7, 3, 11, 2, 3, 2, 2, 5, 5, 7, 2, 7, 2, 3, 7, 5, 5, 5, 5, 2, 37, 2, 3, 3, 3, 5, 41, 7, 11, 61, 3, 7, 7, 3, 7, 11, 2, 17, 37, 3, 2, 23, 11, 3]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
private theorem arithmetic049 : checkBlock 7353 roster049 = true := by decide +kernel

set_option maxRecDepth 100000 in
private theorem interval049 :
    ∀ n, 7353 ≤ n → n < 7503 → n ≤ 10000 →
      ∃ p < n, p.Prime ∧ (p^2 * (n-p).totient - 1).Prime :=
  checkedInterval 7353 150 roster049 (by decide) arithmetic049

private def roster050 : List ℕ := [2, 3, 5, 2, 5, 3, 31, 7, 3, 7, 13, 59, 53, 3, 13, 43, 11, 2, 43, 11, 7, 3, 11, 5, 19, 7, 19, 11, 29, 3, 47, 3, 5, 43, 3, 11, 23, 19, 2, 31, 13, 7, 3, 3, 2, 43, 3, 17, 47, 3, 29, 11, 23, 7, 3, 7, 47, 3, 5, 2, 3, 7, 41, 5, 43, 7, 19, 3, 17, 5, 2, 2, 3, 2, 17, 3, 7, 2, 3, 11, 47, 2, 7, 7, 2, 3, 3, 2, 11, 2, 11, 23, 7, 151, 5, 2, 3, 7, 13, 2, 3, 3, 5, 2, 29, 17, 3, 2, 3, 19, 5, 2, 13, 11, 5, 5, 3, 17, 31, 23, 3, 5, 17, 53, 41, 5, 3, 37, 5, 7, 3, 23, 13, 11, 3, 2, 13, 5, 3, 17, 5, 23, 7, 3, 2, 2, 13, 3, 5, 5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
private theorem arithmetic050 : checkBlock 7503 roster050 = true := by decide +kernel

set_option maxRecDepth 100000 in
private theorem interval050 :
    ∀ n, 7503 ≤ n → n < 7653 → n ≤ 10000 →
      ∃ p < n, p.Prime ∧ (p^2 * (n-p).totient - 1).Prime :=
  checkedInterval 7503 150 roster050 (by decide) arithmetic050

private def roster051 : List ℕ := [7, 3, 2, 2, 7, 3, 2, 2, 3, 3, 5, 5, 37, 3, 5, 7, 3, 2, 2, 3, 17, 5, 7, 2, 3, 3, 23, 17, 3, 2, 11, 3, 5, 5, 163, 23, 5, 2, 3, 3, 3, 31, 3, 2, 2, 29, 5, 7, 5, 71, 3, 17, 3, 3, 47, 7, 3, 17, 3, 2, 13, 2, 2, 47, 2, 2, 7, 7, 109, 3, 3, 7, 11, 2, 2, 7, 3, 2, 7, 17, 3, 19, 2, 2, 13, 5, 5, 41, 7, 23, 3, 2, 3, 3, 2, 41, 11, 2, 5, 5, 2, 5, 7, 3, 3, 3, 11, 11, 5, 3, 3, 3, 2, 5, 13, 3, 19, 7, 3, 2, 3, 2, 2, 3, 2, 3, 3, 2, 47, 11, 37, 3, 3, 13, 17, 2, 2, 7, 2, 2, 2, 2, 5, 5, 3, 2, 19, 3, 2, 3]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
private theorem arithmetic051 : checkBlock 7653 roster051 = true := by decide +kernel

set_option maxRecDepth 100000 in
private theorem interval051 :
    ∀ n, 7653 ≤ n → n < 7803 → n ≤ 10000 →
      ∃ p < n, p.Prime ∧ (p^2 * (n-p).totient - 1).Prime :=
  checkedInterval 7653 150 roster051 (by decide) arithmetic051

private def roster052 : List ℕ := [5, 19, 2, 23, 3, 2, 3, 2, 2, 5, 7, 3, 7, 11, 3, 5, 5, 17, 2, 11, 2, 73, 13, 7, 3, 13, 11, 23, 31, 3, 3, 3, 31, 37, 11, 5, 53, 2, 13, 3, 37, 5, 2, 3, 2, 5, 11, 5, 3, 2, 11, 3, 5, 3, 7, 2, 3, 73, 7, 101, 2, 5, 2, 7, 11, 7, 3, 3, 5, 89, 2, 7, 3, 109, 3, 5, 11, 13, 2, 3, 5, 2, 3, 3, 3, 2, 11, 3, 13, 3, 5, 3, 2, 3, 2, 2, 11, 3, 53, 2, 7, 17, 5, 11, 2, 5, 5, 3, 3, 7, 2, 2, 13, 3, 5, 2, 2, 2, 5, 3, 2, 3, 19, 3, 7, 2, 41, 3, 29, 2, 3, 2, 2, 3, 11, 2, 5, 17, 3, 2, 7, 2, 2, 2, 7, 23, 17, 2, 3, 5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
private theorem arithmetic052 : checkBlock 7803 roster052 = true := by decide +kernel

set_option maxRecDepth 100000 in
private theorem interval052 :
    ∀ n, 7803 ≤ n → n < 7953 → n ≤ 10000 →
      ∃ p < n, p.Prime ∧ (p^2 * (n-p).totient - 1).Prime :=
  checkedInterval 7803 150 roster052 (by decide) arithmetic052

private def roster053 : List ℕ := [2, 3, 11, 2, 47, 17, 19, 7, 2, 2, 11, 2, 2, 11, 2, 5, 3, 3, 5, 5, 2, 3, 2, 2, 47, 31, 11, 3, 29, 2, 3, 3, 43, 3, 13, 2, 101, 7, 19, 5, 31, 3, 3, 2, 2, 5, 3, 2, 3, 2, 2, 3, 3, 3, 7, 2, 3, 2, 3, 2, 5, 3, 61, 31, 37, 5, 2, 67, 3, 2, 2, 13, 5, 11, 5, 41, 3, 3, 2, 2, 2, 5, 2, 2, 3, 17, 17, 3, 3, 2, 2, 7, 53, 71, 11, 5, 2, 2, 11, 2, 13, 11, 3, 2, 5, 3, 5, 3, 7, 2, 2, 5, 5, 11, 11, 2, 2, 2, 19, 5, 2, 2, 7, 2, 2, 3, 5, 5, 13, 2, 5, 3, 5, 3, 7, 2, 3, 23, 11, 19, 7, 23, 7, 2, 3, 37, 13, 3, 2, 17]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
private theorem arithmetic053 : checkBlock 7953 roster053 = true := by decide +kernel

set_option maxRecDepth 100000 in
private theorem interval053 :
    ∀ n, 7953 ≤ n → n < 8103 → n ≤ 10000 →
      ∃ p < n, p.Prime ∧ (p^2 * (n-p).totient - 1).Prime :=
  checkedInterval 7953 150 roster053 (by decide) arithmetic053

private def roster054 : List ℕ := [11, 7, 47, 7, 2, 47, 73, 5, 3, 2, 13, 5, 2, 2, 7, 2, 5, 3, 3, 23, 2, 53, 3, 11, 5, 67, 2, 2, 13, 7, 5, 2, 7, 3, 19, 17, 31, 7, 13, 2, 3, 5, 5, 5, 5, 73, 5, 5, 37, 2, 31, 107, 13, 2, 2, 3, 3, 5, 7, 2, 13, 2, 5, 5, 5, 3, 7, 2, 29, 3, 5, 2, 3, 13, 47, 107, 2, 2, 5, 137, 2, 7, 3, 5, 3, 5, 5, 3, 3, 2, 3, 3, 2, 2, 13, 3, 3, 3, 2, 2, 19, 11, 5, 13, 2, 2, 2, 5, 2, 7, 7, 17, 13, 11, 79, 5, 13, 3, 3, 3, 3, 7, 7, 13, 2, 5, 3, 5, 5, 2, 11, 19, 17, 19, 83, 2, 3, 5, 2, 29, 11, 19, 3, 3, 3, 2, 5, 3, 11, 5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
private theorem arithmetic054 : checkBlock 8103 roster054 = true := by decide +kernel

set_option maxRecDepth 100000 in
private theorem interval054 :
    ∀ n, 8103 ≤ n → n < 8253 → n ≤ 10000 →
      ∃ p < n, p.Prime ∧ (p^2 * (n-p).totient - 1).Prime :=
  checkedInterval 8103 150 roster054 (by decide) arithmetic054

private def roster055 : List ℕ := [7, 5, 2, 5, 5, 23, 13, 11, 17, 41, 7, 3, 3, 3, 2, 43, 2, 3, 2, 3, 2, 5, 3, 5, 2, 3, 3, 5, 5, 2, 11, 3, 3, 2, 29, 7, 13, 3, 2, 13, 5, 3, 5, 7, 7, 2, 23, 11, 13, 73, 7, 2, 11, 11, 3, 2, 7, 11, 2, 2, 5, 2, 19, 11, 2, 47, 43, 2, 11, 3, 3, 7, 2, 5, 29, 13, 13, 2, 2, 5, 23, 7, 11, 2, 7, 5, 53, 3, 2, 2, 17, 2, 2, 2, 2, 5, 5, 5, 3, 29, 2, 11, 7, 2, 2, 2, 5, 59, 3, 2, 2, 2, 5, 5, 3, 3, 2, 2, 37, 19, 5, 2, 7, 2, 2, 3, 2, 5, 2, 3, 13, 2, 3, 11, 2, 7, 7, 5, 19, 7, 2, 67, 2, 7, 2, 5, 5, 41, 17, 7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
private theorem arithmetic055 : checkBlock 8253 roster055 = true := by decide +kernel

set_option maxRecDepth 100000 in
private theorem interval055 :
    ∀ n, 8253 ≤ n → n < 8403 → n ≤ 10000 →
      ∃ p < n, p.Prime ∧ (p^2 * (n-p).totient - 1).Prime :=
  checkedInterval 8253 150 roster055 (by decide) arithmetic055

private def roster056 : List ℕ := [5, 23, 3, 2, 5, 5, 3, 53, 3, 5, 3, 3, 5, 5, 2, 23, 13, 2, 11, 5, 103, 13, 3, 3, 2, 7, 11, 41, 3, 29, 23, 2, 7, 3, 2, 3, 3, 2, 2, 3, 5, 3, 2, 2, 5, 2, 5, 13, 2, 2, 23, 3, 2, 3, 2, 5, 2, 3, 7, 2, 19, 5, 3, 5, 7, 5, 2, 2, 5, 2, 5, 7, 2, 7, 3, 2, 7, 11, 2, 83, 2, 13, 13, 3, 3, 11, 3, 19, 83, 13, 17, 2, 11, 2, 7, 7, 5, 2, 41, 2, 19, 11, 3, 41, 2, 17, 2, 37, 11, 2, 37, 3, 13, 2, 3, 13, 2, 3, 3, 7, 13, 3, 13, 5, 13, 7, 7, 2, 7, 5, 3, 5, 5, 5, 3, 2, 23, 223, 73, 2, 3, 5, 5, 103, 3, 3, 3, 101, 3, 5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
private theorem arithmetic056 : checkBlock 8403 roster056 = true := by decide +kernel

set_option maxRecDepth 100000 in
private theorem interval056 :
    ∀ n, 8403 ≤ n → n < 8553 → n ≤ 10000 →
      ∃ p < n, p.Prime ∧ (p^2 * (n-p).totient - 1).Prime :=
  checkedInterval 8403 150 roster056 (by decide) arithmetic056

private def roster057 : List ℕ := [7, 3, 3, 83, 11, 2, 5, 3, 2, 2, 2, 7, 3, 5, 7, 3, 2, 7, 7, 7, 13, 3, 19, 2, 3, 3, 5, 3, 7, 5, 2, 5, 23, 2, 7, 7, 2, 2, 2, 17, 5, 5, 7, 2, 13, 3, 37, 13, 11, 7, 2, 11, 19, 2, 3, 5, 2, 17, 5, 3, 89, 7, 113, 2, 2, 3, 5, 5, 7, 2, 17, 2, 2, 5, 2, 13, 29, 11, 2, 71, 2, 19, 2, 2, 11, 2, 5, 2, 5, 7, 5, 5, 19, 29, 13, 2, 2, 3, 17, 2, 2, 2, 3, 41, 3, 23, 37, 11, 2, 5, 2, 7, 3, 5, 3, 2, 5, 2, 3, 17, 2, 23, 13, 17, 3, 2, 2, 2, 2, 2, 3, 7, 2, 73, 23, 17, 2, 2, 3, 2, 2, 3, 5, 11, 3, 7, 5, 3, 7, 11]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
private theorem arithmetic057 : checkBlock 8553 roster057 = true := by decide +kernel

set_option maxRecDepth 100000 in
private theorem interval057 :
    ∀ n, 8553 ≤ n → n < 8703 → n ≤ 10000 →
      ∃ p < n, p.Prime ∧ (p^2 * (n-p).totient - 1).Prime :=
  checkedInterval 8553 150 roster057 (by decide) arithmetic057

private def roster058 : List ℕ := [2, 7, 13, 3, 17, 3, 3, 2, 3, 2, 2, 2, 2, 11, 7, 3, 41, 3, 2, 11, 11, 2, 5, 7, 5, 3, 11, 13, 3, 5, 2, 2, 11, 5, 5, 5, 5, 3, 2, 2, 19, 17, 19, 2, 7, 109, 5, 3, 7, 13, 2, 2, 11, 5, 2, 7, 7, 3, 2, 5, 5, 2, 41, 7, 2, 5, 7, 59, 13, 3, 5, 11, 7, 7, 19, 5, 2, 5, 2, 5, 31, 3, 3, 2, 3, 17, 3, 2, 13, 2, 3, 17, 31, 11, 3, 17, 29, 3, 2, 2, 11, 5, 5, 5, 3, 173, 5, 7, 5, 7, 7, 11, 47, 3, 2, 2, 13, 3, 3, 41, 2, 3, 3, 13, 3, 47, 2, 3, 2, 7, 3, 5, 3, 7, 3, 11, 7, 5, 3, 31, 3, 11, 3, 2, 2, 23, 2, 7, 17, 3]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
private theorem arithmetic058 : checkBlock 8703 roster058 = true := by decide +kernel

set_option maxRecDepth 100000 in
private theorem interval058 :
    ∀ n, 8703 ≤ n → n < 8853 → n ≤ 10000 →
      ∃ p < n, p.Prime ∧ (p^2 * (n-p).totient - 1).Prime :=
  checkedInterval 8703 150 roster058 (by decide) arithmetic058

private def roster059 : List ℕ := [3, 3, 11, 2, 11, 2, 3, 13, 5, 2, 5, 2, 2, 3, 7, 5, 7, 2, 59, 19, 59, 5, 3, 5, 13, 31, 3, 3, 7, 5, 31, 5, 97, 3, 23, 2, 2, 3, 3, 5, 67, 3, 3, 2, 3, 19, 5, 5, 11, 3, 5, 31, 13, 5, 2, 17, 2, 5, 5, 5, 29, 2, 3, 19, 11, 3, 3, 31, 3, 2, 13, 2, 5, 11, 2, 5, 23, 2, 3, 7, 5, 31, 5, 2, 3, 47, 29, 29, 5, 3, 2, 19, 2, 2, 2, 2, 3, 5, 7, 3, 5, 2, 2, 3, 13, 2, 3, 5, 13, 5, 3, 3, 43, 2, 2, 13, 13, 2, 17, 2, 2, 19, 7, 2, 41, 3, 3, 89, 2, 3, 13, 5, 2, 7, 5, 13, 3, 7, 7, 5, 2, 7, 17, 5, 19, 7, 11, 2, 11, 5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
private theorem arithmetic059 : checkBlock 8853 roster059 = true := by decide +kernel

set_option maxRecDepth 100000 in
private theorem interval059 :
    ∀ n, 8853 ≤ n → n < 9003 → n ≤ 10000 →
      ∃ p < n, p.Prime ∧ (p^2 * (n-p).totient - 1).Prime :=
  checkedInterval 8853 150 roster059 (by decide) arithmetic059

private def roster060 : List ℕ := [2, 7, 3, 11, 3, 17, 53, 5, 5, 5, 11, 5, 13, 31, 13, 2, 2, 3, 3, 2, 2, 2, 2, 5, 7, 2, 2, 3, 5, 5, 3, 2, 61, 11, 5, 37, 7, 7, 23, 3, 47, 3, 5, 11, 17, 3, 2, 5, 2, 5, 2, 3, 7, 29, 3, 2, 47, 3, 3, 19, 3, 3, 5, 2, 13, 17, 2, 2, 3, 5, 2, 29, 2, 2, 2, 2, 3, 3, 3, 29, 47, 13, 7, 3, 5, 37, 2, 3, 13, 5, 3, 5, 5, 31, 11, 23, 23, 2, 11, 2, 3, 2, 3, 43, 2, 2, 19, 2, 5, 3, 7, 3, 2, 2, 3, 2, 11, 3, 2, 5, 2, 11, 3, 7, 3, 41, 7, 2, 2, 3, 2, 7, 2, 13, 2, 5, 3, 3, 13, 2, 2, 2, 5, 5, 13, 3, 11, 2, 23, 13]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
private theorem arithmetic060 : checkBlock 9003 roster060 = true := by decide +kernel

set_option maxRecDepth 100000 in
private theorem interval060 :
    ∀ n, 9003 ≤ n → n < 9153 → n ≤ 10000 →
      ∃ p < n, p.Prime ∧ (p^2 * (n-p).totient - 1).Prime :=
  checkedInterval 9003 150 roster060 (by decide) arithmetic060

private def roster061 : List ℕ := [2, 2, 5, 7, 29, 13, 3, 5, 11, 2, 3, 11, 2, 2, 19, 13, 5, 3, 7, 2, 71, 7, 5, 17, 5, 13, 17, 3, 5, 3, 11, 3, 11, 2, 5, 2, 3, 2, 7, 3, 5, 7, 31, 3, 2, 17, 23, 5, 2, 3, 2, 2, 19, 29, 37, 3, 2, 19, 3, 2, 2, 7, 11, 11, 2, 3, 3, 3, 2, 3, 3, 47, 11, 11, 53, 2, 3, 23, 3, 7, 2, 3, 11, 3, 23, 5, 2, 23, 5, 47, 7, 7, 3, 3, 3, 7, 5, 7, 7, 41, 2, 3, 3, 5, 11, 3, 5, 13, 31, 2, 37, 11, 2, 5, 2, 3, 29, 19, 17, 2, 3, 3, 13, 5, 5, 5, 3, 11, 19, 3, 11, 37, 5, 3, 3, 5, 2, 17, 11, 19, 2, 2, 23, 5, 13, 7, 2, 17, 7, 3]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
private theorem arithmetic061 : checkBlock 9153 roster061 = true := by decide +kernel

set_option maxRecDepth 100000 in
private theorem interval061 :
    ∀ n, 9153 ≤ n → n < 9303 → n ≤ 10000 →
      ∃ p < n, p.Prime ∧ (p^2 * (n-p).totient - 1).Prime :=
  checkedInterval 9153 150 roster061 (by decide) arithmetic061

private def roster062 : List ℕ := [3, 3, 3, 23, 2, 3, 7, 3, 2, 61, 13, 5, 3, 3, 3, 3, 11, 5, 5, 5, 7, 3, 47, 5, 2, 3, 3, 43, 2, 3, 31, 19, 2, 2, 13, 5, 11, 2, 13, 37, 5, 3, 5, 7, 13, 5, 7, 2, 3, 2, 5, 7, 5, 3, 7, 5, 2, 3, 3, 11, 7, 5, 3, 2, 43, 3, 41, 2, 19, 5, 61, 5, 13, 2, 3, 11, 53, 2, 11, 2, 5, 3, 3, 3, 3, 5, 41, 3, 2, 11, 13, 3, 17, 5, 2, 3, 7, 2, 2, 3, 3, 2, 2, 7, 3, 41, 5, 3, 11, 13, 2, 7, 7, 2, 5, 17, 17, 11, 17, 3, 11, 2, 23, 83, 2, 11, 5, 19, 2, 3, 19, 2, 11, 7, 3, 2, 7, 2, 5, 13, 7, 3, 59, 11, 23, 3, 11, 3, 2, 5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
private theorem arithmetic062 : checkBlock 9303 roster062 = true := by decide +kernel

set_option maxRecDepth 100000 in
private theorem interval062 :
    ∀ n, 9303 ≤ n → n < 9453 → n ≤ 10000 →
      ∃ p < n, p.Prime ∧ (p^2 * (n-p).totient - 1).Prime :=
  checkedInterval 9303 150 roster062 (by decide) arithmetic062

private def roster063 : List ℕ := [2, 5, 11, 2, 3, 43, 47, 2, 23, 5, 13, 2, 2, 17, 13, 5, 11, 3, 11, 13, 61, 11, 11, 3, 3, 7, 2, 2, 5, 5, 5, 7, 3, 2, 2, 2, 3, 5, 5, 43, 5, 11, 5, 79, 3, 13, 7, 11, 73, 3, 13, 41, 47, 2, 3, 2, 2, 61, 3, 2, 2, 7, 2, 5, 3, 2, 3, 2, 3, 3, 3, 2, 7, 43, 3, 11, 7, 2, 5, 5, 2, 5, 7, 2, 3, 7, 17, 23, 3, 67, 2, 31, 2, 83, 13, 7, 2, 61, 2, 2, 19, 2, 5, 13, 2, 17, 7, 2, 2, 7, 13, 3, 13, 3, 5, 13, 3, 3, 2, 11, 7, 17, 17, 17, 2, 5, 3, 3, 23, 3, 5, 7, 43, 13, 17, 5, 13, 29, 19, 11, 23, 3, 13, 2, 3, 2, 5, 5, 11, 19]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
private theorem arithmetic063 : checkBlock 9453 roster063 = true := by decide +kernel

set_option maxRecDepth 100000 in
private theorem interval063 :
    ∀ n, 9453 ≤ n → n < 9603 → n ≤ 10000 →
      ∃ p < n, p.Prime ∧ (p^2 * (n-p).totient - 1).Prime :=
  checkedInterval 9453 150 roster063 (by decide) arithmetic063

private def roster064 : List ℕ := [3, 3, 2, 3, 37, 2, 2, 7, 5, 2, 3, 2, 2, 13, 2, 37, 5, 19, 3, 3, 5, 2, 5, 2, 5, 7, 5, 2, 5, 7, 5, 2, 5, 3, 5, 2, 3, 2, 5, 2, 2, 61, 2, 5, 2, 5, 47, 2, 41, 2, 11, 2, 3, 7, 7, 37, 17, 2, 3, 2, 2, 2, 2, 13, 2, 11, 2, 7, 3, 7, 11, 2, 3, 43, 5, 29, 3, 3, 2, 11, 2, 17, 3, 5, 11, 5, 41, 7, 113, 29, 17, 7, 19, 2, 13, 2, 2, 13, 5, 2, 5, 2, 3, 2, 7, 3, 2, 7, 5, 11, 3, 2, 2, 3, 2, 2, 19, 13, 7, 13, 3, 7, 13, 2, 2, 2, 71, 17, 7, 3, 7, 2, 5, 2, 7, 3, 7, 2, 29, 2, 19, 11, 7, 11, 47, 11, 2, 11, 7, 17]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
private theorem arithmetic064 : checkBlock 9603 roster064 = true := by decide +kernel

set_option maxRecDepth 100000 in
private theorem interval064 :
    ∀ n, 9603 ≤ n → n < 9753 → n ≤ 10000 →
      ∃ p < n, p.Prime ∧ (p^2 * (n-p).totient - 1).Prime :=
  checkedInterval 9603 150 roster064 (by decide) arithmetic064

private def roster065 : List ℕ := [3, 3, 2, 41, 17, 2, 71, 2, 11, 2, 2, 2, 2, 11, 5, 7, 7, 2, 3, 3, 5, 2, 13, 2, 5, 5, 7, 7, 3, 7, 2, 3, 3, 7, 3, 13, 7, 59, 3, 29, 5, 7, 3, 7, 11, 2, 23, 3, 19, 5, 59, 2, 7, 17, 5, 3, 2, 2, 11, 17, 2, 3, 11, 19, 3, 13, 5, 5, 3, 2, 3, 13, 2, 2, 5, 13, 5, 7, 3, 11, 2, 13, 3, 2, 2, 17, 5, 3, 13, 31, 3, 2, 11, 5, 13, 2, 2, 3, 3, 2, 3, 5, 7, 2, 3, 2, 11, 2, 11, 3, 2, 23, 2, 3, 13, 2, 23, 2, 2, 2, 7, 13, 3, 3, 7, 2, 37, 11, 2, 5, 13, 2, 5, 3, 7, 7, 7, 17, 2, 2, 13, 3, 2, 13, 3, 7, 11, 11, 3, 3]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
private theorem arithmetic065 : checkBlock 9753 roster065 = true := by decide +kernel

set_option maxRecDepth 100000 in
private theorem interval065 :
    ∀ n, 9753 ≤ n → n < 9903 → n ≤ 10000 →
      ∃ p < n, p.Prime ∧ (p^2 * (n-p).totient - 1).Prime :=
  checkedInterval 9753 150 roster065 (by decide) arithmetic065

private def roster066 : List ℕ := [3, 11, 2, 3, 37, 5, 2, 3, 11, 5, 13, 11, 5, 13, 11, 107, 2, 3, 5, 2, 7, 2, 17, 17, 7, 7, 3, 29, 59, 2, 2, 7, 3, 11, 19, 2, 7, 5, 3, 17, 5, 3, 7, 31, 5, 5, 7, 7, 2, 53, 2, 19, 5, 11, 17, 2, 5, 3, 29, 17, 2, 7, 2, 19, 17, 3, 2, 11, 11, 71, 2, 5, 2, 5, 5, 13, 7, 5, 7, 29, 2, 7, 19, 3, 3, 5, 3, 7, 5, 3, 3, 7, 3, 47, 3, 23, 5, 2]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
private theorem arithmetic066 : checkBlock 9903 roster066 = true := by decide +kernel

set_option maxRecDepth 100000 in
private theorem interval066 :
    ∀ n, 9903 ≤ n → n < 10001 → n ≤ 10000 →
      ∃ p < n, p.Prime ∧ (p^2 * (n-p).totient - 1).Prime :=
  checkedInterval 9903 98 roster066 (by decide) arithmetic066

private theorem allCases : ∀ n, 3 ≤ n → n < 10001 → n ≤ 10000 →
    ∃ p < n, p.Prime ∧ (p^2 * (n-p).totient - 1).Prime :=
  (joinIntervals (joinIntervals (joinIntervals (joinIntervals (joinIntervals (joinIntervals interval000 interval001) (joinIntervals interval002 interval003)) (joinIntervals (joinIntervals interval004 interval005) (joinIntervals interval006 interval007))) (joinIntervals (joinIntervals (joinIntervals interval008 interval009) (joinIntervals interval010 interval011)) (joinIntervals (joinIntervals interval012 interval013) (joinIntervals interval014 interval015)))) (joinIntervals (joinIntervals (joinIntervals (joinIntervals interval016 interval017) (joinIntervals interval018 interval019)) (joinIntervals (joinIntervals interval020 interval021) (joinIntervals interval022 interval023))) (joinIntervals (joinIntervals (joinIntervals interval024 interval025) (joinIntervals interval026 interval027)) (joinIntervals (joinIntervals interval028 interval029) (joinIntervals interval030 (joinIntervals interval031 interval032)))))) (joinIntervals (joinIntervals (joinIntervals (joinIntervals (joinIntervals interval033 interval034) (joinIntervals interval035 interval036)) (joinIntervals (joinIntervals interval037 interval038) (joinIntervals interval039 interval040))) (joinIntervals (joinIntervals (joinIntervals interval041 interval042) (joinIntervals interval043 interval044)) (joinIntervals (joinIntervals interval045 interval046) (joinIntervals interval047 (joinIntervals interval048 interval049))))) (joinIntervals (joinIntervals (joinIntervals (joinIntervals interval050 interval051) (joinIntervals interval052 interval053)) (joinIntervals (joinIntervals interval054 interval055) (joinIntervals interval056 interval057))) (joinIntervals (joinIntervals (joinIntervals interval058 interval059) (joinIntervals interval060 interval061)) (joinIntervals (joinIntervals interval062 interval063) (joinIntervals interval064 (joinIntervals interval065 interval066)))))))

end OMA.PrimeTotientWitness

theorem OMA.solution : OMA.R_OeisA233566_conjecture_2_R1.H1 := by
  intro n lo hi
  exact OMA.PrimeTotientWitness.allCases n (by omega) (by omega) hi