import Shellsort.PhysicalNeighborCorrection

namespace Shellsort.PhysicalColumnCorrection
open LocalRelativeOrderMean LocalGatePivotCounts TwoLargeGapPhysicalShapes
open PhysicalNeighborCorrection
noncomputable section

private theorem lowHigh {n} (l r : GateTree n) :
    localInversion (.low l r) (.high l r) = 0 := by
  rw [← pair_probability]
  have point (p : RankPlacement n) :
      (if evaluate p.symm (.high l r) < evaluate p.symm (.low l r)
        then (1:ℝ) else 0) = 0 := by
    change (if max _ _ < min _ _ then (1:ℝ) else 0) = 0
    exact if_neg (not_lt_of_ge (le_trans (min_le_left _ _) (le_max_left _ _)))
  simp_rw [point]; exact uniformAverage_const _ _

theorem physical_column {n h g : ℕ} (gh : g < h) (half : n ≤ 2*g)
    (i : Fin n) (ip : i.val+g<n) :
    let x := decide (i.val+h<n)
    let y := decide (h ≤ i.val+g)
    420*(localInversion (depthTwo h g i) (depthTwo h g ⟨i.val+g,ip⟩) - selfMean x y true) =
      (LargeGapCorrectionMultiplicities.samePair x y : ℝ) := by
  let x := decide (i.val+h<n)
  let y := decide (h ≤ i.val+g)
  have zero : selfMean x y false = 0 := by
    change uniformAverage (fun p : RankPlacement 8 =>
      if evaluate p.symm (.high (small x 0 1) (large y 2 3)) <
        evaluate p.symm (.low (small x 0 1) (large y 2 3)) then (1:ℝ) else 0) = 0
    rw [pair_probability,lowHigh]
  obtain ⟨l,r⟩ := column_shape gh half i ip
  dsimp only at l r ⊢
  rw [l,r,lowHigh,← zero]
  exact (eight_corrections x y).1

/-- Both families of possibly overlapping full-column pairs are now priced
using their actual physical gate probabilities. -/
theorem all_overlapping_columns {n h g : ℕ} (gh : g < h) (half : n ≤ 2*g)
    (i j : Fin n) (ip : i.val+g<n) (jp : j.val+g<n) (shared : j.val+g=i.val+h) :
    let x := decide (i.val+h<n)
    let y := decide (h ≤ i.val+g)
    let z := decide (j.val+h<n)
    420*(localInversion (depthTwo h g i) (depthTwo h g ⟨i.val+g,ip⟩) - selfMean x y true) =
      (LargeGapCorrectionMultiplicities.samePair x y : ℝ) ∧
    420*(actualEdge (h:=h) i j ip jp - edgeMean y z true) =
      (LargeGapCorrectionMultiplicities.neighbor y z : ℝ) := by
  exact ⟨physical_column gh half i ip,actual_neighbor_correction gh half i j ip jp shared⟩

#print axioms all_overlapping_columns
end
end Shellsort.PhysicalColumnCorrection
