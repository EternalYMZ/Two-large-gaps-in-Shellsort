import Shellsort.SevenRegionOrder
import Shellsort.OrderedRegionSum

namespace Shellsort.ThreePassClosedMean
open Finset SevenSegmentBaseline PhysicalSevenSegments SevenRegionOrder
open ThreePassSeparatedLedger LocalRelativeOrderMean
noncomputable section

def baseline (n : ℕ) (a b : ℕ) : ℝ :=
  if b-a<a then
    (n:ℝ)^2/4-2*(a:ℝ)*n/15-4*(b:ℝ)*n/15+(46*(a:ℝ)^2-34*(a:ℝ)*b+30*(b:ℝ)^2)/105-n/4
  else
    (n:ℝ)^2/4-(b:ℝ)*n/3+2*(a:ℝ)^2/5-2*(a:ℝ)*b/5+(b:ℝ)^2/3-n/4

theorem physical_baseline {n h g : ℕ} (hg : 0<g) (gh : g<h) (hn : h<n) (half : n ≤ 2*g) :
    (∑ ij ∈ gapPositionPairs n 1, separatePair n h g ij) = baseline n (n-h) (n-g) := by
  let o := decide (h-g<n-h)
  have rel : n-g-(n-h) = h-g := by omega
  have price : (∑ ij ∈ gapPositionPairs n 1, separatePair n h g ij) =
      ∑ ij ∈ gapPositionPairs n 1, prob o (region n h g ij.1.val) (region n h g ij.2.val) := by
    apply sum_congr rfl; intro ij _
    rw [prob_table]; exact pair_table hg gh hn half ij.1 ij.2
  rw [price,OrderedRegionSum.regroup (fun i : Fin n => region n h g i.val) (span n h g) (prob o)
    (region_monotone gh hn half) (one_sum gh hn half),lengths gh hn half]
  have quadratic := baseline_quadratics n (n-h:ℕ) (n-g:ℕ)
  unfold baseline
  rw [rel]
  by_cases branch : h-g<n-h
  · simpa only [branch,decide_true,ite_true,o,mass] using quadratic.2
  · simpa only [branch,decide_false,ite_false,o,mass] using quadratic.1

/-- Actual expected number of unguarded linear-insertion key comparisons,
for all pairs of decreasing large gaps. All inversion terms are closed. -/
theorem executed_closed {n h g : ℕ} (hg : 0<g) (gh : g<h) (hn : h<n) (half : n ≤ 2*g) :
    let a := n-h
    let b := n-g
    let d := h-g
    let w : HarvestBlockIteration.PositiveWord := [⟨h,by omega⟩,⟨g,hg⟩,⟨1,by decide⟩]
    uniformAverage (fun p : RankPlacement n => ((HarvestOperationalAudit.runWord
      (HarvestOperationalAudit.slots p) w).2:ℝ)) =
      (a:ℝ)+b+n-LargeGapCornerRecords.harmonic n-LargeGapRecordChanges.grouped a d +
      baseline n a b +
      ((if a ≤ d then -42*(a:ℤ)-70*(b:ℤ) else if a ≤ 2*d then -54*(a:ℤ)-64*(b:ℤ)
        else -36*(a:ℤ)-76*(b:ℤ) : ℤ):ℝ)/420 := by
  dsimp only
  rw [ThreePassPhysicalCorrection.executed_with_correction hg gh hn half,
      physical_baseline hg gh hn half,show n-h+(h-g)=n-g by omega]

#print axioms executed_closed
end
end Shellsort.ThreePassClosedMean
