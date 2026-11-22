import FiniteRange
import FilterCriterion
import Lift
import RoughParity
import Incidence
import Cutoff
import ModThree
import BalancedSurplus
import SpectralGapEnergy
import MobiusCutoff
import CenteredFour
import EndpointMajorant
import CutoffVariation

namespace Goldbach

/-- A finite list of distinct eligible first summands whose complements are
    also eligible prime powers. The threshold bounds all possible false positives. -/
def EnoughFilteredPowerPairs (n : Nat) : Prop :=
  ∃ xs : List Nat, xs.Nodup ∧
    (∀ x ∈ xs, x ≤ n ∧ GoldbachFilter.Allowed x ∧ GoldbachFilter.Allowed (n-x) ∧
      GoldbachFilter.PrimePower x ∧ GoldbachFilter.PrimePower (n-x)) ∧
    2 * (GoldbachFilter.properPowerCover n).length < xs.length

theorem hasPair_of_filtered_surplus {n : Nat} (h : EnoughFilteredPowerPairs n) :
    HasPair n := by
  obtain ⟨xs, hd, hv, hc⟩ := h
  obtain ⟨x, _, px, py, _, _, hsum⟩ :=
    GoldbachFilter.prime_pair_of_many_prime_power_pairs hd hv hc
  exact ⟨x, n-x, px, py, hsum⟩

/-- Conditional only. The hypothesis quantifies over *each* even integer beyond the
    verified range. An interval average or a finite test does not supply it. -/
theorem strongGoldbach_of_filtered_tail
    (tail : ∀ n : Nat, 1000000 < n → n % 2 = 0 → EnoughFilteredPowerPairs n) :
    StrongGoldbach := by
  intro n hn he
  by_cases h : n ≤ 1000000
  · exact Finite.goldbach_to_million n hn h he
  · exact hasPair_of_filtered_surplus (tail n (by omega) he)

end Goldbach

#print axioms Goldbach.Finite.goldbach_to_million
#print axioms Goldbach.Finite.balanced_6256_to_million
#print axioms Goldbach.Finite.not_balanced_filtered_6254
#print axioms Goldbach.Finite.hasPair_6254
#print axioms GoldbachFilter.balanced_allowed_progression
#print axioms GoldbachFilter.allowed_power_exponent_ge_five
#print axioms GoldbachFilter.length_properPowerCover_le
#print axioms GoldbachFilter.prime_pair_of_many_prime_power_pairs
#print axioms Goldbach.prime_or_semiprime_of_rough
#print axioms Goldbach.semiprime_at_exception
#print axioms Goldbach.unique_small_prime_of_rough_composite
#print axioms Goldbach.incidence_example_110
#print axioms Goldbach.ModThree.other_base_eq_three
#print axioms Goldbach.ModThree.even_exponent_forces_three
#print axioms Goldbach.ModThree.unique_three_power_in_middle_third
#print axioms Goldbach.ModThree.unique_unordered_even_exponent_pair
#print axioms Goldbach.BalancedSurplus.length_oddPowerCover_le_split
#print axioms Goldbach.BalancedSurplus.prime_pair_of_sorted_middle_surplus
#print axioms Goldbach.BalancedSurplus.hasPair_of_split_root_surplus
#print axioms Goldbach.strongGoldbach_of_filtered_tail
#print axioms Goldbach.SpectralGapEnergy.descent_energy_identity
#print axioms Goldbach.SpectralGapEnergy.centered_descent_attains_bound
#print axioms Goldbach.SpectralGapEnergy.hasPair_of_central_energy_gap
#print axioms Goldbach.SpectralGapEnergy.empty_window_centered_energy
#print axioms Goldbach.SpectralGapEnergy.balanced_pair_of_central_local_gap
#print axioms Goldbach.SpectralGapEnergy.strongGoldbach_of_checked_range_and_local_tail
#print axioms Goldbach.MobiusCutoff.full_divisor_switch
#print axioms Goldbach.MobiusCutoff.wide_endpoint_example

namespace Goldbach.OneSidedSieve

/-- A cubic upper bound for the scaled absolute deviation plus the first moment. -/
theorem cubic_deviation {u s r : Nat} (hs : 2 * s ≤ r * u) :
    6 * ((s - u) + (u - s)) + 6 * s ≤ 6 * u + u * (r * (r - 1) * (r - 2)) := by
  by_cases hsu : s ≤ u
  · omega
  · have hr : 3 ≤ r := by
      apply Nat.le_of_not_lt
      intro hsmall
      have hru := Nat.mul_le_mul_right u (show r ≤ 2 by omega)
      omega
    have hprod : 6 ≤ r * (r - 1) :=
      Nat.mul_le_mul hr (show 2 ≤ r - 1 by omega)
    have htriple := Nat.mul_le_mul_right (r - 2) hprod
    have hc : 6 * r ≤ 12 + r * (r - 1) * (r - 2) := by omega
    have hscale := Nat.mul_le_mul_right u hc
    rw [Nat.add_mul, Nat.mul_assoc 6 r u,
      Nat.mul_comm (r * (r - 1) * (r - 2)) u] at hscale
    omega

/-- Summing the bound on each entry produces the hypothesis of cubic_deviation. -/
theorem twice_sum_le_length_mul (xs : List Nat) (u : Nat)
    (h : ∀ a ∈ xs, 2 * a ≤ u) : 2 * Nat.sum xs ≤ xs.length * u := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
    have ha := h a (by simp)
    have ht := ih (fun b hb => h b (by simp [hb]))
    simp only [Nat.sum_cons, List.length_cons, Nat.succ_mul]
    omega

theorem cubic_deviation_of_list (xs : List Nat) (u : Nat)
    (h : ∀ a ∈ xs, 2 * a ≤ u) :
    6 * ((Nat.sum xs - u) + (u - Nat.sum xs)) + 6 * Nat.sum xs ≤
      6 * u + u * (xs.length * (xs.length - 1) * (xs.length - 2)) :=
  cubic_deviation (twice_sum_le_length_mul xs u h)

end Goldbach.OneSidedSieve

#print axioms Goldbach.OneSidedSieve.cubic_deviation
#print axioms Goldbach.OneSidedSieve.twice_sum_le_length_mul
#print axioms Goldbach.OneSidedSieve.cubic_deviation_of_list
#print axioms Goldbach.CenteredFour.centered_four
#print axioms Goldbach.EndpointMajorant.endpoint_majorant
#print axioms Goldbach.EndpointMajorant.endpoint_surplus
#print axioms Goldbach.CutoffVariation.difference_le_variation
#print axioms Goldbach.CutoffVariation.cell_variations_le_global
#print axioms Goldbach.CutoffVariation.entire_cell_above
#print axioms Goldbach.CutoffVariation.entire_cell_above_of_global

