import CubicMangoldt

open scoped BigOperators
namespace FixedEven.Cubic
noncomputable section

/-- For every target, at the lower cubic cutoff, the deviation of the
two actual von Mangoldt endpoints from the genuine log-weighted prime-pair
sum is square-root pollution plus an explicit two-logarithm bound. -/
theorem uniform_mangoldt_rate {N : ℕ} (hN : 4096 ≤ N) :
    ∃ z : ℕ, 8 ≤ z ∧ 8*z^3 ≤ N ∧ N < 27*z^3 ∧
      ∀ (q : ℕ) [Fact q.Prime], (N-2)*(N-2) < q →
      ∀ (c : ℝ), 0 < c → ∀ linear : DirichletCharacter ℂ q → ℝ,
        let e := mangoldtObservable N z c linear - ∑ p ∈ genuine (screen N z) N, Real.log p
        0 ≤ e ∧ e ≤ (135*Real.log 4)^3 * N / (Real.log N)^2 +
          (Nat.sqrt (N-2) : ℝ) * Real.log 4 := by
  obtain ⟨z,hz,hl,hu⟩ := choose_scale hN
  refine ⟨z,hz,hl,hu,?_⟩
  intro q hq' hq c hc linear
  dsimp only
  have he := mangoldt_error_count hN hz hq c hc linear
  have hd := (cubic_error_rate hN hz hl hu).2
  have hlog : 0 < Real.log (N:ℝ) := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  refine ⟨he.1, he.2.trans (add_le_add_right ?_ _)⟩
  apply (le_div_iff₀ (sq_pos_of_pos hlog)).2
  calc
    _ = (((detected (screen N z) N (N/z)).card : ℝ) - (genuine (screen N z) N).card) *
      (Real.log (N:ℝ))^3 := by ring
    _ ≤ _ := hd

#print axioms uniform_mangoldt_rate
end
end FixedEven.Cubic
