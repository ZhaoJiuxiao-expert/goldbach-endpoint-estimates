import Foundations
import Residues

namespace GoldbachFilter

open Goldbach (Prime)

/-- A prime is itself a prime power, with exponent one. -/
def PrimePower (m : Nat) : Prop :=
  ∃ p k : Nat, Prime p ∧ 1 ≤ k ∧ m = p ^ k

/-- A dyadic upper bound for the fifth root; only this many bases are scanned. -/
def baseLimit (n : Nat) : Nat := 2 ^ (n.log2 / 5 + 1)

private theorem lt_baseLimit {p n : Nat} (hn : n ≠ 0) (h : p ^ 5 ≤ n) :
    p < baseLimit n := by
  apply Nat.lt_of_not_ge
  intro hle
  have hpow := Nat.le_trans (Nat.pow_le_pow_of_le_left hle 5) h
  unfold baseLimit at hpow
  rw [← Nat.pow_mul] at hpow
  have hlog := (Nat.le_log2 hn).2 hpow
  omega

def possibleBases (n : Nat) : List Nat :=
  (List.range (baseLimit n)).filter (fun p => decide (2 ≤ p ∧ p ^ 5 ≤ n))

def possibleExponents (n : Nat) : List Nat :=
  (List.range (n.log2 + 1)).filter (fun k => decide (5 ≤ k ∧ ¬ 2 ∣ k ∧ ¬ 3 ∣ k))

/-- A computable cover. Composite bases and repeated values only enlarge the bound. -/
def properPowerCover (n : Nat) : List Nat :=
  ((possibleBases n).bind (fun p => (possibleExponents n).map (fun k => p ^ k))).filter
    (fun m => decide (m ≤ n ∧ Allowed m))

/-- Every allowed prime power below the cutoff that fails primality belongs to the cover. -/
theorem mem_properPowerCover {m n : Nat} (hm : m ≤ n) (ha : Allowed m)
    (hpp : PrimePower m) (hcomposite : ¬ Prime m) : m ∈ properPowerCover n := by
  obtain ⟨p, k, hp, hk, rfl⟩ := hpp
  have hbase := hp.1
  have hne1 : k ≠ 1 := by
    intro heq
    subst k
    exact hcomposite (by simpa using hp)
  have h5 := allowed_power_exponent_ge_five ha rfl (by omega : 2 ≤ k)
  have hdiv := exponent_not_divisible ha
  have hbase5 := Nat.le_trans (Nat.pow_le_pow_of_le_right (by omega : 0 < p) h5) hm
  have hpow := Nat.le_trans (Nat.pow_le_pow_of_le_left hbase k) hm
  have hn : n ≠ 0 := by have := Nat.pow_pos (by decide : 0 < 2) (n := k); omega
  have hlog := (Nat.le_log2 hn).2 hpow
  have hb : p ∈ possibleBases n :=
    List.mem_filter.mpr ⟨List.mem_range.mpr (lt_baseLimit hn hbase5), by simpa using And.intro hbase hbase5⟩
  have he : k ∈ possibleExponents n :=
    List.mem_filter.mpr ⟨List.mem_range.mpr (by omega), by simpa using And.intro h5 hdiv⟩
  apply List.mem_filter.mpr
  exact ⟨List.mem_bind.mpr ⟨p, hb, List.mem_map.mpr ⟨k, he, rfl⟩⟩, by simpa using And.intro hm ha⟩

private theorem length_power_rectangle (bases exps : List Nat) :
    (bases.bind (fun p => exps.map (fun k => p ^ k))).length = bases.length * exps.length := by
  induction bases with
  | nil => simp
  | cons b bs ih => simp [ih, Nat.succ_mul, Nat.add_comm]

/-- Closed upper bound, independent of the contents of the cover. -/
theorem length_properPowerCover_le (n : Nat) :
    (properPowerCover n).length ≤ baseLimit n * (n.log2 + 1) := by
  have hb : (possibleBases n).length ≤ baseLimit n := by
    unfold possibleBases
    simpa only [List.length_range] using
      List.length_filter_le (fun p => decide (2 ≤ p ∧ p ^ 5 ≤ n)) (List.range (baseLimit n))
  have he : (possibleExponents n).length ≤ n.log2 + 1 := by
    unfold possibleExponents
    simpa only [List.length_range] using
      List.length_filter_le (fun k => decide (5 ≤ k ∧ ¬ 2 ∣ k ∧ ¬ 3 ∣ k)) (List.range (n.log2 + 1))
  unfold properPowerCover
  have h := List.length_filter_le (fun m => decide (m ≤ n ∧ Allowed m))
    ((possibleBases n).bind (fun p => (possibleExponents n).map (fun k => p ^ k)))
  rw [length_power_rectangle] at h
  exact Nat.le_trans h (Nat.mul_le_mul hb he)

private theorem length_le_of_nodup_subset {xs ys : List Nat} (hd : xs.Nodup)
    (hs : ∀ a ∈ xs, a ∈ ys) : xs.length ≤ ys.length := by
  induction xs generalizing ys with
  | nil => simp
  | cons x xs ih =>
    obtain ⟨hx, hxs⟩ := List.nodup_cons.mp hd
    have hxys := hs x (by simp)
    have hrest : ∀ a ∈ xs, a ∈ ys.erase x := by
      intro a ha
      have hne : a ≠ x := fun heq => hx (heq ▸ ha)
      exact (List.mem_erase_of_ne hne).mpr (hs a (by simp [ha]))
    have hlen := ih hxs hrest
    rw [List.length_erase_of_mem hxys] at hlen
    have hpos := List.length_pos_of_mem hxys
    simp only [List.length_cons]
    omega

/-- Distinct first summands identify the pairs. Every bad pair has its first
summand either in the cover or in its reflection about n/2. The winning
summand is returned in the input list, preserving any further restrictions. -/
theorem prime_pair_of_many_prime_power_pairs {n : Nat} {xs : List Nat}
    (hd : xs.Nodup)
    (hvalid : ∀ x ∈ xs, x ≤ n ∧ Allowed x ∧ Allowed (n - x) ∧ PrimePower x ∧ PrimePower (n - x))
    (hmany : 2 * (properPowerCover n).length < xs.length) :
    ∃ x ∈ xs, Prime x ∧ Prime (n - x) ∧ Allowed x ∧ Allowed (n - x) ∧ x + (n - x) = n := by
  apply Classical.byContradiction
  intro hnone
  let bad := properPowerCover n
  have hs : ∀ x ∈ xs, x ∈ (bad ++ bad.map (fun y => n - y)) := by
    intro x hx
    obtain ⟨hle, ha, hb, hpp, hqq⟩ := hvalid x hx
    apply List.mem_append.mpr
    by_cases hp : Prime x
    · have hq : ¬ Prime (n - x) := fun h => hnone ⟨x, hx, hp, h, ha, hb, by omega⟩
      exact Or.inr (List.mem_map.mpr ⟨n - x, mem_properPowerCover (by omega) hb hqq hq, by omega⟩)
    · exact Or.inl (mem_properPowerCover hle ha hpp hp)
  have hlen := length_le_of_nodup_subset hd hs
  simp only [List.length_append, List.length_map, bad] at hlen
  omega

/-- Explicit sufficient pair count for a balanced filtered Goldbach representation. -/
theorem balanced_prime_pair_of_many {n : Nat} {xs : List Nat}
    (hd : xs.Nodup)
    (hvalid : ∀ x ∈ xs, x ≤ n ∧ Allowed x ∧ Allowed (n - x) ∧ PrimePower x ∧ PrimePower (n - x))
    (hbalance : ∀ x ∈ xs, x ≤ n - x ∧ n - x ≤ 2 * x)
    (hmany : 2 * (baseLimit n * (n.log2 + 1)) < xs.length) :
    ∃ p q : Nat, Prime p ∧ Prime q ∧ Allowed p ∧ Allowed q ∧
      p + q = n ∧ p ≤ q ∧ q ≤ 2 * p := by
  have hupper := Nat.mul_le_mul_left 2 (length_properPowerCover_le n)
  obtain ⟨p, hmem, hp, hq, ha, hb, hadd⟩ :=
    prime_pair_of_many_prime_power_pairs hd hvalid (Nat.lt_of_le_of_lt hupper hmany)
  exact ⟨p, n - p, hp, hq, ha, hb, hadd, hbalance p hmem⟩

end GoldbachFilter
