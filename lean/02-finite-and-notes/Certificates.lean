import Foundations
import Residues

namespace Goldbach

set_option maxRecDepth 16000

/-- A stronger, finite target: both primes pass the mod-72 filter, and are in
    the middle third. The ordering counts an unordered pair only once. -/
def BalancedFiltered (n : Nat) : Prop :=
  ∃ p q : Nat, Prime p ∧ Prime q ∧ p + q = n ∧ p ≤ q ∧ n ≤ 3*p ∧
    GoldbachFilter.Allowed p ∧ GoldbachFilter.Allowed q

theorem BalancedFiltered.hasPair {n : Nat} (h : BalancedFiltered n) : HasPair n := by
  obtain ⟨p, q, hp, hq, hsum, _⟩ := h
  exact ⟨p, q, hp, hq, hsum⟩

namespace Certificate

private def bound (n : Nat) : Nat :=
  if n < 4 then 1
  else if n < 9 then 2
  else if n < 25 then 4
  else if n < 289 then 16
  else if n < 66049 then 256
  else 1024

-- Fixed factorials speed up reduction. The literals are checked by the next theorem.
private def productFor (n : Nat) : Nat :=
  if n < 4 then 0x1
  else if n < 9 then 0x2
  else if n < 25 then 0x18
  else if n < 289 then 0x130777758000
  else if n < 66049 then 0xff578f57c15bb743beaa77d27637e02b598dffa9aebd15889187fe6eb3bdca516c3fa1a52eabef31f33b4b8c2e5b5524f1aa4f3329393912f40dbbe23d7f39723e0be05b6696b11f8eea0abe365a11d9f2735ac7e5b4e015ab19b35b84893685b37a9a0a62a566d6571d7e00d4241687f5c804f37cde9bf311c0781f51cc007c5a01a94f6cfcecea640b8e9ab7bd43e73e5df5d0e1eeb4d9b6cc44be67b7cad80808b17869561b579ffe0bbdeca5c83139e458000000000000000000000000000000000000000000000000000000000000000
  else 0x2022f598887b1b677793eea7338140b96edd924fcab3a183421f3dcfe257e91fdb9fbda6fdc765c78087e0afb0469ee9dc04e88b57dbc8a8850c431640a70a5553f274cf95cf31ef50ff773bb46b4f14badbef976885d017edb30ca9d17100464466d8e2c424c4eb35a8ad96698ab9da18c5941a808585b16d700ea60fe4742b55d151d2fa72fb5314bf93374f6ba357b7e7b81928b2fcef3b564380dc3bd2d0d3580a28d5aead0d707cdd521cb09f953e45849e4ea04445db770f4473bfd62494ba215e1370df02adb30f0aec0dc9adccc96284cf6d8ffed1dd2833033d53dbb87f602c4c286f1c03b25795d45d8fd8d989a47ec52b856055b878c7329f655f487052c38bcd4a790b30277c68153bcb18a167e393143051e069b23b51d05cb8b0040c7086c76707d0d69400443d00223aaa1c24dc6aa22eeb60f1402efea0babf3f916fe20dfeca617d4a72b2818db64445eb896f589524c9803c6b97c05803e5333357ef9281627249eba91582c91ef846f3f0a84b92a079c62b33dd2419af649fbcc579686ae8fb54746b82b83fc3402833941f035b655216b02bb7a0b42ba292f70af8fd3c6922a2c065dd523c7723b37f1bba4f2411f9d917091b4c99c676242826777b15c868fa3e528596e5ce1ebe1634565a393a60c8d7daaa16b1bd7679f6f5e923569eefc0fbcea6da292fef18f19bc4b6306fc70161c9f19b75c55710ddd3a2d4edfa892b7184e2a601bf85b047b9b256a8338739e257ee896dadbfa43e08360591f78cd6a3d40e8c04beebd2e22f357d2fcf22ec25cb48ed2cee17f7a638ce99a83b6db18a25e6418e162c55479577a5b781703c46174b9b929095e732845329dde20b46d0ec7e74e90aff69906f485a24d40bae6190296d0218ce544d19db6fcdc55a624493b698ecbb01751e1a1ad46d2cf590df06e631bb6048680bd616f3e4d80b5c562d5660cf611154ad88ef87290d24ba9e89eebc2fd3cce8560a034f23134f9813c48debd014e2ccda5d947ecf35e2f40464199f5fa75900d1a2c47c50d1982caea69002fb8057c97f6eec6e1040202741885d11ad136965f70bbaa24ee85dd09dace0b2bc1008b3180a501be1e791f016fbf750ce18f1a4352b2caf0f01fa1d7020ea70f9bb3cdfce1b26b73172809e1dfa5ef33f4c89a3f6e4219d024f29cf91ecf25ae7620cdd6453351bf2e64e97212b56d7bdeb9c7fa700468ab881cda84380998f47e46a537948431b47f258fd092c739d207eeb3b91fe231adab484d6161b750c2cd6f77f650f76a8deac564d2da13a26650ee9aa992797601b1629d7ac4e540699eeb66183724dede658673e0a3b3b5c06a3c741c1c4aa746d7458000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000

private theorem productFor_eq (n : Nat) : productFor n = factorial (bound n) := by
  unfold productFor bound
  repeat' first | split | rfl

private def primeB (n : Nat) : Bool :=
  decide (2 ≤ n ∧ n < (bound n + 1) * (bound n + 1) ∧ Nat.gcd n (productFor n) = 1)

private theorem primeB_sound {n : Nat} (h : primeB n = true) : Prime n := by
  have hs := of_decide_eq_true h
  obtain ⟨hn, hsize, hg⟩ := hs
  rw [productFor_eq] at hg
  exact prime_of_gcd_certificate hn hsize hg

private def allowedB (n : Nat) : Bool :=
  Nat.testBit 0x828008800a08028a0 (n % 72)

private theorem allowedB_sound {n : Nat} (h : allowedB n = true) : GoldbachFilter.Allowed n := by
  have table : ∀ r : Fin 72, Nat.testBit 0x828008800a08028a0 r.val = true → GoldbachFilter.Allowed r.val := by decide
  exact (GoldbachFilter.allowed_mod72 n).mp (table ⟨n % 72, Nat.mod_lt _ (by decide)⟩ h)

def Target (strict : Bool) (n : Nat) : Prop :=
  if strict then BalancedFiltered n else HasPair n

private def pairB (strict : Bool) (n p : Nat) : Bool :=
  let q := n-p
  primeB p && primeB q && decide (p ≤ n) &&
    (if strict then decide (p ≤ q ∧ n ≤ 3*p) && allowedB p && allowedB q else true)

private theorem pairB_sound {strict n p} (h : pairB strict n p = true) : Target strict n := by
  cases strict with
  | false =>
    simp [pairB, Bool.and_eq_true] at h
    exact ⟨p, n-p, primeB_sound h.1.1, primeB_sound h.1.2, by omega⟩
  | true =>
    simp only [pairB, Bool.and_eq_true, decide_eq_true_eq, ite_true] at h
    obtain ⟨⟨⟨hp, hq⟩, hpn⟩, ⟨⟨⟨hle, hbal⟩, ha⟩, hb⟩⟩ := h
    exact ⟨p, n-p, primeB_sound hp, primeB_sound hq, by omega, hle, hbal,
      allowedB_sound ha, allowedB_sound hb⟩

def Block (strict : Bool) (start count : Nat) : Prop :=
  ∀ i : Nat, i < count → Target strict (start + 2*i)

theorem append {s a k l} (x : Block s a k) (y : Block s (a+2*k) l) :
    Block s a (k+l) := by
  intro i hi
  by_cases h : i < k
  · exact x i h
  · have eqn : a+2*i = a+2*k+2*(i-k) := by omega
    rw [eqn]
    exact y (i-k) (by omega)

/-- A certificate digit stores p itself, or the distance from ceil(n/3) in strict mode. -/
def checkDigits (strict : Bool) : Nat → Nat → Nat → Bool
  | 0, _, _ => true
  | k+1, start, data =>
    let base := if strict then (start+2)/3 else 0
    pairB strict start (base + data % 65536) &&
      checkDigits strict k (start+2) (data/65536)

theorem checkDigits_sound {strict k a data} (h : checkDigits strict k a data = true) :
    Block strict a k := by
  induction k generalizing a data with
  | zero => intro i hi; omega
  | succ k ih =>
    simp only [checkDigits, Bool.and_eq_true] at h
    intro i hi
    cases i with
    | zero => simpa using (pairB_sound h.1)
    | succ i =>
      have hh := (ih h.2) i (by omega)
      have e : a+2*(i+1) = a+2+2*i := by omega
      simpa only [e] using hh

end Certificate
end Goldbach
