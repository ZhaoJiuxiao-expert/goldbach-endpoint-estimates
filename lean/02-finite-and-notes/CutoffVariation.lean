import Std

namespace Goldbach.CutoffVariation

/-- A nonempty ordered list of samples. Both endpoints are samples. -/
structure Cell (α : Type u) where
  first : α
  rest : List α

def Cell.samples (c : Cell α) : List α := c.first :: c.rest

/-- Sum of the magnitudes of all successive jumps, including the first one. -/
def variationFrom (f : α → Int) (x : α) : List α → Int
  | [] => 0
  | y :: ys => max (f y - f x) (f x - f y) + variationFrom f y ys

def Cell.variation (c : Cell α) (f : α → Int) : Int :=
  variationFrom f c.first c.rest

/-- Either ordering of two samples is permitted, as are jumps of either sign. -/
theorem difference_le_variation (f : α → Int) (c : Cell α) {x y : α}
    (hx : x ∈ c.samples) (hy : y ∈ c.samples) :
    f x - f y ≤ c.variation f := by
  obtain ⟨first, rest⟩ := c
  change x ∈ first :: rest at hx
  change y ∈ first :: rest at hy
  change f x - f y ≤ variationFrom f first rest
  induction rest generalizing first x y with
  | nil =>
    simp only [List.mem_singleton] at hx hy
    simp [hx, hy, variationFrom]
  | cons next rest ih =>
    simp only [List.mem_cons] at hx hy
    change f x - f y ≤ max (f next - f first) (f first - f next) + _
    have hn : next ∈ next :: rest := List.Mem.head _
    rcases hx with hx | hx <;> rcases hy with hy | hy
    · subst x; subst y
      have h := ih next hn hn
      omega
    · subst x
      have h := ih next hn (List.mem_cons.mpr hy)
      omega
    · subst y
      have h := ih next (List.mem_cons.mpr hx) hn
      omega
    · have h := ih next (List.mem_cons.mpr hx) (List.mem_cons.mpr hy)
      omega

/-- Sum an integer observation over a finite list, keeping repetitions. -/
def sumOver : List α → (α → Int) → Int
  | [], _ => 0
  | x :: xs, f => f x + sumOver xs f

/-- Join the cells in their given order, keeping even repeated endpoints. -/
def allSamples : List (Cell α) → List α
  | [] => []
  | c :: cs => c.samples ++ allSamples cs

def pathVariation (f : α → Int) : List α → Int
  | [] => 0
  | x :: xs => variationFrom f x xs

private theorem append_variation (f : α → Int) (x : α) (xs ys : List α) :
    variationFrom f x xs + pathVariation f ys ≤ variationFrom f x (xs ++ ys) := by
  induction xs generalizing x with
  | nil =>
    cases ys with
    | nil => simp [variationFrom, pathVariation]
    | cons y ys =>
      simp only [List.nil_append, variationFrom, pathVariation, Int.zero_add]
      omega
  | cons y xs ih =>
    have h := ih y
    change variationFrom f y xs + pathVariation f ys ≤
      variationFrom f y (xs.append ys) at h
    simp only [List.cons_append, variationFrom]
    omega

/-- Only the jumps connecting successive cells are omitted on the left. -/
theorem cell_variations_le_global (cs : List (Cell α)) (f : α → Int) :
    sumOver cs (fun c => c.variation f) ≤ pathVariation f (allSamples cs) := by
  induction cs with
  | nil => simp [sumOver, allSamples, pathVariation]
  | cons c cs ih =>
    have h := append_variation f c.first c.rest (allSamples cs)
    change variationFrom f c.first c.rest + _ ≤
      variationFrom f c.first (c.rest ++ allSamples cs)
    omega

private theorem weighted_upper (xs : List α) (w f : α → Int) (cap : Int)
    (hw : ∀ x ∈ xs, 0 ≤ w x) (hf : ∀ x ∈ xs, f x ≤ cap) :
    sumOver xs (fun x => w x * f x) ≤ sumOver xs w * cap := by
  induction xs with
  | nil => simp [sumOver]
  | cons x xs ih =>
    have hx := Int.mul_le_mul_of_nonneg_left (hf x (by simp)) (hw x (by simp))
    have ht := ih (fun y hy => hw y (List.mem_cons_of_mem _ hy))
      (fun y hy => hf y (List.mem_cons_of_mem _ hy))
    simp only [sumOver, Int.add_mul]
    exact Int.add_le_add hx ht

private theorem sum_cell_bounds (cs : List (Cell α)) (v total : Cell α → Int)
    (mass cap : Int) (h : ∀ c ∈ cs, total c ≤ mass * (cap + v c)) :
    sumOver cs total ≤ (cs.length : Int) * (mass * cap) + mass * sumOver cs v := by
  induction cs with
  | nil => simp [sumOver]
  | cons c cs ih =>
    have hc := h c (by simp)
    have ht := ih (fun d hd => h d (List.mem_cons_of_mem _ hd))
    simp only [sumOver, List.length_cons, Int.ofNat_succ,
      Int.add_mul, Int.mul_add, Int.one_mul]
    rw [Int.mul_add] at hc
    omega

/-- If the weighted total exceeds the threshold times the total mass plus one
    cell's mass times the sum of the within-cell variations, some entire cell
    is strictly above the threshold. Weights are arbitrary nonnegative
    integers with equal total per cell; a zero-weight sample is still tested. -/
theorem entire_cell_above (cs : List (Cell α)) (f w : α → Int) (mass cap : Int)
    (hw : ∀ c ∈ cs, ∀ x ∈ c.samples, 0 ≤ w x)
    (hm : ∀ c ∈ cs, sumOver c.samples w = mass)
    (excess : (cs.length : Int) * (mass * cap) +
        mass * sumOver cs (fun c => c.variation f) <
      sumOver cs (fun c => sumOver c.samples (fun x => w x * f x))) :
    ∃ c ∈ cs, ∀ x ∈ c.samples, cap < f x := by
  by_cases high : ∃ c ∈ cs, ∀ x ∈ c.samples, cap < f x
  · exact high
  · exfalso
    apply (Int.not_le_of_gt excess)
    apply sum_cell_bounds
    intro c hc
    have low : ∃ y ∈ c.samples, f y ≤ cap := by
      apply Classical.byContradiction
      intro h
      apply high
      refine ⟨c, hc, ?_⟩
      intro x hx
      by_cases hle : f x ≤ cap
      · exact False.elim (h ⟨x, hx, hle⟩)
      · omega
    obtain ⟨y, hy, hlow⟩ := low
    rw [← hm c hc]
    apply weighted_upper _ _ _ _ (hw c hc)
    intro x hx
    have hdiff := difference_le_variation f c hx hy
    omega

/-- The same certificate using the total variation along the whole grid. -/
theorem entire_cell_above_of_global (cs : List (Cell α)) (f w : α → Int)
    (mass cap : Int) (hmass : 0 ≤ mass)
    (hw : ∀ c ∈ cs, ∀ x ∈ c.samples, 0 ≤ w x)
    (hm : ∀ c ∈ cs, sumOver c.samples w = mass)
    (excess : (cs.length : Int) * (mass * cap) +
        mass * pathVariation f (allSamples cs) <
      sumOver cs (fun c => sumOver c.samples (fun x => w x * f x))) :
    ∃ c ∈ cs, ∀ x ∈ c.samples, cap < f x := by
  apply entire_cell_above cs f w mass cap hw hm
  have h := Int.mul_le_mul_of_nonneg_left (cell_variations_le_global cs f) hmass
  omega

#print axioms Goldbach.CutoffVariation.difference_le_variation
#print axioms Goldbach.CutoffVariation.cell_variations_le_global
#print axioms Goldbach.CutoffVariation.entire_cell_above
#print axioms Goldbach.CutoffVariation.entire_cell_above_of_global

end Goldbach.CutoffVariation
