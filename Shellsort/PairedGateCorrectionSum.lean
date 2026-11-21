import Shellsort.LocalGatePivotCounts
import Shellsort.TwoLargeGapPhysicalShapes

namespace Shellsort.PairedGateCorrectionSum
open LocalGatePivotCounts TwoLargeGapPhysicalShapes LocalRelativeOrderMean Finset

noncomputable def score (a d : ℕ) : ℝ :=
  (∑ i ∈ range (a+d),
    (selfMean (decide (i<a)) (decide (d ≤ i)) false -
      selfMean (decide (i<a)) (decide (d ≤ i)) true)) +
  ∑ i ∈ range a,
    (edgeMean (decide (d ≤ i)) (decide (i+d<a)) false -
      edgeMean (decide (d ≤ i)) (decide (i+d<a)) true)

/-- This sum uses the actual two-slot and four-slot probabilities for the
normalized source templates, prior to identifying all physical inversions. -/
theorem summed_gate_probabilities (a d : ℕ) :
    420*score a d =
      ((if a ≤ d then -42*(a:ℤ)-70*(a+d:ℕ)
        else if a ≤ 2*d then -54*(a:ℤ)-64*(a+d:ℕ)
        else -36*(a:ℤ)-76*(a+d:ℕ) : ℤ):ℝ) := by
  rw [← LargeGapCorrectionMultiplicities.three_regions, score,
    LargeGapCorrectionMultiplicities.total,mul_add,Finset.mul_sum,Finset.mul_sum]
  simp only [(eight_corrections _ _).1,(eight_corrections _ _).2,Int.cast_add,Int.cast_sum]

theorem physical_and_summed_grids {n h g : ℕ} (hg : 0 < g) (gh : g < h) (half : n ≤ 2*g)
    (i j : Fin n) (ip : i.val+g<n) (jp : j.val+g<n) (order : i<j) :
    (((∃ z, z ∈ sources (depthTwo h g i) ∧ z ∈ sources (depthTwo h g j)) ↔
      j.val+g=i.val+h) ∧
    (let r : Fin n := ⟨i.val+g,ip⟩
     depthTwo h g i = .low (leftInput h i) (rightInput h r) ∧
      depthTwo h g r = .high (leftInput h i) (rightInput h r)) ∧
    (j.val+g=i.val+h →
      let r : Fin n := ⟨j.val+g,jp⟩
      leftInput h i = .low (.leaf i) (.leaf r) ∧ rightInput h r = .high (.leaf i) (.leaf r))) ∧
    420*score (n-h) (h-g) = (LargeGapCorrectionMultiplicities.total (n-h) (h-g):ℝ) := by
  refine ⟨⟨(TwoLargeGapSourceOverlap.physical_overlap hg gh half i j ip jp order).2.2,
    column_shape gh half i ip,?_⟩,?_⟩
  · intro shared
    have p := neighboring_shapes i j ip jp shared
    exact ⟨p.1,p.2.1⟩
  · rw [LargeGapCorrectionMultiplicities.three_regions]
    exact summed_gate_probabilities _ _

#print axioms physical_and_summed_grids
end Shellsort.PairedGateCorrectionSum
