import ModThree
import FilterCriterion

namespace Goldbach.BalancedSurplus

open Goldbach.ModThree
open GoldbachFilter (PrimePower)

/-- A dyadic upper bound for bases with p cubed at most n. -/
def cubeBaseLimit (n : Nat) : Nat := 2 ^ (n.log2 / 3 + 1)

/-- A finite cover of odd proper powers. Extra composite bases and repeated
    values are harmless for an upper bound. Cubes need just one exponent
    for each base; all remaining odd powers start at exponent five. -/
def oddPowerCover (n : Nat) : List Nat :=
  (List.range (cubeBaseLimit n)).map (fun p => p ^ 3) ++
    (List.range (GoldbachFilter.baseLimit n)).bind fun p =>
      ((List.range n.log2).filter (fun i => decide (i + 5 ≤ n.log2 ∧ ¬ 2 ∣ i + 5))).map
        (fun i => p ^ (i + 5))

theorem mem_oddPowerCover {n p k : Nat} (hp : 2 ≤ p) (hk : 3 ≤ k)
    (hodd : ¬ 2 ∣ k) (hsize : p ^ k ≤ n) : p ^ k ∈ oddPowerCover n := by
  have hpow := Nat.le_trans (Nat.pow_le_pow_of_le_left hp k) hsize
  have hn : n ≠ 0 := by have := Nat.pow_pos (by decide : 0 < 2) (n := k); omega
  have hlog := (Nat.le_log2 hn).2 hpow
  have hb3 := Nat.le_trans (Nat.pow_le_pow_of_le_right (by omega : 0 < p) hk) hsize
  have hb : p < cubeBaseLimit n := by
    apply Nat.lt_of_not_ge
    intro hle
    have hpow' := Nat.le_trans (Nat.pow_le_pow_of_le_left hle 3) hb3
    unfold cubeBaseLimit at hpow'
    rw [← Nat.pow_mul] at hpow'
    have := (Nat.le_log2 hn).2 hpow'
    omega
  apply List.mem_append.mpr
  by_cases h3 : k = 3
  · exact Or.inl (List.mem_map.mpr ⟨p, List.mem_range.mpr hb, by simp [h3]⟩)
  · have hk5 : 5 ≤ k := by omega
    have hb5 : p < GoldbachFilter.baseLimit n := by
      apply Nat.lt_of_not_ge
      intro hle
      have hpower := Nat.le_trans (Nat.pow_le_pow_of_le_left hle 5)
        (Nat.le_trans (Nat.pow_le_pow_of_le_right (by omega : 0 < p) hk5) hsize)
      unfold GoldbachFilter.baseLimit at hpower
      rw [← Nat.pow_mul] at hpower
      have := (Nat.le_log2 hn).2 hpower
      omega
    have heq : k - 5 + 5 = k := by omega
    apply Or.inr
    exact List.mem_bind.mpr ⟨p, List.mem_range.mpr hb5, List.mem_map.mpr ⟨k - 5,
      List.mem_filter.mpr ⟨List.mem_range.mpr (by omega), by simpa [heq] using And.intro hlog hodd⟩,
      by simp [heq]⟩⟩

private theorem rectangle_length (bases ks : List Nat) (f : Nat → Nat → Nat) :
    (bases.bind fun p => ks.map (f p)).length = bases.length * ks.length := by
  induction bases with
  | nil => simp
  | cons p ps ih => simp [ih, Nat.succ_mul, Nat.add_comm]

/-- The log factor only costs on the fifth-root term. -/
theorem length_oddPowerCover_le_split (n : Nat) :
    (oddPowerCover n).length ≤ cubeBaseLimit n + GoldbachFilter.baseLimit n * n.log2 := by
  unfold oddPowerCover
  simp only [List.length_append, List.length_map, rectangle_length, List.length_range]
  apply Nat.add_le_add_left
  apply Nat.mul_le_mul_left
  simpa using List.length_filter_le (fun i => decide (i + 5 ≤ n.log2 ∧ ¬ 2 ∣ i + 5)) (List.range n.log2)

theorem length_oddPowerCover_le (n : Nat) :
    (oddPowerCover n).length ≤ cubeBaseLimit n * (n.log2 + 1) := by
  have hbase : GoldbachFilter.baseLimit n ≤ cubeBaseLimit n := by
    unfold GoldbachFilter.baseLimit cubeBaseLimit
    exact Nat.pow_le_pow_of_le_right (by decide) (by omega)
  have hmul := Nat.mul_le_mul_right n.log2 hbase
  have hsplit := length_oddPowerCover_le_split n
  rw [Nat.mul_succ]
  omega

private theorem common_even_marker {n : Nat} (hn : n % 6 = 4) :
    ∃ c, ∀ u v, BalancedEvenExponentSum n u v → min u v = c := by
  by_cases h : ∃ u v, BalancedEvenExponentSum n u v
  · obtain ⟨a, b, hab⟩ := h
    refine ⟨min a b, ?_⟩
    intro u v huv
    rcases unique_unordered_even_exponent_pair hn huv hab with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
    · simp [h₁, h₂]
    · simp [h₁, h₂, Nat.min_comm]
  · exact ⟨0, fun u v huv => False.elim (h ⟨u, v, huv⟩)⟩

private theorem bad_sorted_mem {n u v c : Nat} (hsum : u + v = n)
    (hlo : n ≤ 3 * u) (hhi : 3 * u ≤ 2 * n)
    (hu : PrimePower u) (hv : PrimePower v) (hbad : ¬ Prime u)
    (hmarker : ∀ a b, BalancedEvenExponentSum n a b → min a b = c) :
    min u v ∈ c :: (oddPowerCover n).map (fun t => min t (n - t)) := by
  obtain ⟨p, k, hp, hk, hup⟩ := hu
  by_cases hev : 2 ∣ k
  · obtain ⟨i, hi⟩ := hev
    obtain ⟨q, j, hq, _, hvq⟩ := hv
    exact List.mem_cons.mpr (Or.inl (hmarker u v
      ⟨hsum, hlo, hhi, p, q, i, j, hp, hq, by simpa [hi] using hup, hvq⟩))
  · have hne : k ≠ 1 := by
      intro h
      exact hbad (by simpa [hup, h] using hp)
    have hk3 : 3 ≤ k := by omega
    have hmem : u ∈ oddPowerCover n := by
      rw [hup]
      exact mem_oddPowerCover hp.1 hk3 hev (by omega)
    exact List.mem_cons.mpr (Or.inr (List.mem_map.mpr
      ⟨u, hmem, by rw [show n - u = v by omega]⟩))

private theorem nodup_subset_length {xs ys : List Nat} (hd : xs.Nodup)
    (hs : ∀ a ∈ xs, a ∈ ys) : xs.length ≤ ys.length := by
  induction xs generalizing ys with
  | nil => simp
  | cons x xs ih =>
    obtain ⟨hx, hxs⟩ := List.nodup_cons.mp hd
    have hxy := hs x (by simp)
    have hrest : ∀ a ∈ xs, a ∈ ys.erase x := by
      intro a ha
      have hne : a ≠ x := fun heq => hx (heq ▸ ha)
      exact (List.mem_erase_of_ne hne).mpr (hs a (by simp [ha]))
    have hlen := ih hxs hrest
    rw [List.length_erase_of_mem hxy] at hlen
    have := List.length_pos_of_mem hxy
    simp only [List.length_cons]
    omega

/-- Sorted balanced pairs require only one cover entry for each exceptional
    value t: its pair is indexed by min t (n-t), on either side of the sum. -/
theorem prime_pair_of_sorted_middle_surplus {n : Nat} {xs : List Nat}
    (hn : n % 6 = 4) (hd : xs.Nodup)
    (hvalid : ∀ x ∈ xs, x ≤ n ∧ x ≤ n - x ∧ n ≤ 3 * x ∧
      PrimePower x ∧ PrimePower (n - x))
    (hmany : 1 + (oddPowerCover n).length < xs.length) :
    ∃ x ∈ xs, Prime x ∧ Prime (n - x) ∧ x + (n - x) = n := by
  apply Classical.byContradiction
  intro hnone
  obtain ⟨c, hc⟩ := common_even_marker hn
  have hs : ∀ x ∈ xs, x ∈ c :: (oddPowerCover n).map (fun t => min t (n - t)) := by
    intro x hx
    obtain ⟨hxn, hord, hlo, hpx, hpy⟩ := hvalid x hx
    by_cases hp : Prime x
    · have hbad : ¬ Prime (n - x) := fun h => hnone ⟨x, hx, hp, h, by omega⟩
      simpa [Nat.min_eq_right hord] using
        bad_sorted_mem (u := n - x) (v := x) (by omega) (by omega) (by omega) hpy hpx hbad hc
    · simpa [Nat.min_eq_left hord] using
        bad_sorted_mem (u := x) (v := n - x) (by omega) hlo (by omega) hpx hpy hp hc
  have hl := nodup_subset_length hd hs
  simp only [List.length_cons, List.length_map] at hl
  omega

/-- Closed cubic-root-scale sufficient count for the residue class 4 mod 6. -/
theorem hasPair_of_cube_root_surplus {n : Nat} {xs : List Nat}
    (hn : n % 6 = 4) (hd : xs.Nodup)
    (hvalid : ∀ x ∈ xs, x ≤ n ∧ x ≤ n - x ∧ n ≤ 3 * x ∧
      PrimePower x ∧ PrimePower (n - x))
    (hmany : 1 + cubeBaseLimit n * (n.log2 + 1) < xs.length) : HasPair n := by
  have hlen := length_oddPowerCover_le n
  obtain ⟨x, _, hp, hq, hsum⟩ := prime_pair_of_sorted_middle_surplus hn hd hvalid (by omega)
  exact ⟨x, n - x, hp, hq, hsum⟩

/-- Refined explicit threshold, of order n^(1/3) + n^(1/5) log n. -/
theorem hasPair_of_split_root_surplus {n : Nat} {xs : List Nat}
    (hn : n % 6 = 4) (hd : xs.Nodup)
    (hvalid : ∀ x ∈ xs, x ≤ n ∧ x ≤ n - x ∧ n ≤ 3 * x ∧
      PrimePower x ∧ PrimePower (n - x))
    (hmany : 1 + cubeBaseLimit n + GoldbachFilter.baseLimit n * n.log2 < xs.length) :
    HasPair n := by
  have hlen := length_oddPowerCover_le_split n
  obtain ⟨x, _, hp, hq, hsum⟩ := prime_pair_of_sorted_middle_surplus hn hd hvalid (by omega)
  exact ⟨x, n - x, hp, hq, hsum⟩

end Goldbach.BalancedSurplus
