import Shellsort.PhysicalOverlapClassification

namespace Shellsort.ThreePassSeparatedLedger
open LocalRelativeOrderMean DisjointGateBaseline PhysicalOverlapClassification Finset
open HarvestOperationalAudit
noncomputable section

def separatePair (n h g : ℕ) (ij : Fin n × Fin n) :=
  separate (depthTwo h g ij.1) (depthTwo h g ij.2)

def adjustment (n h g : ℕ) (ij : Fin n × Fin n) :=
  localInversion (depthTwo h g ij.1) (depthTwo h g ij.2) - separatePair n h g ij

def overlapping (n h g : ℕ) : Finset (Fin n × Fin n) := by
  classical
  exact (gapPositionPairs n 1).filter fun ij => exceptional (h:=h) (g:=g) ij.1 ij.2

/-- Exact, full-array comparison ledger. The correction is summed over each
ordered physical pair once, and can be restricted to the explicit exceptional set. -/
theorem executed_separated_ledger {n h g : ℕ} (hg : 0<g) (gh : g<h)
    (hn : h<n) (half : n ≤ 2*g) :
    let w : HarvestBlockIteration.PositiveWord := [⟨h,by omega⟩,⟨g,hg⟩,⟨1,by decide⟩]
    uniformAverage (fun p : RankPlacement n => ((runWord (slots p) w).2:ℝ)) =
      ((n-h:ℕ):ℝ)+(n-g:ℕ)+n-LargeGapCornerRecords.harmonic n-
      LargeGapRecordChanges.grouped (n-h) (h-g) +
      ∑ ij ∈ gapPositionPairs n 1, separatePair n h g ij +
      ∑ ij ∈ overlapping n h g, adjustment n h g ij := by
  classical
  dsimp only
  apply (mean_from_local_enumeration hg gh hn half).trans
  have total : (∑ ij ∈ gapPositionPairs n 1, localInversion (depthTwo h g ij.1)
      (depthTwo h g ij.2)) = (∑ ij ∈ gapPositionPairs n 1, separatePair n h g ij) +
      ∑ ij ∈ overlapping n h g, adjustment n h g ij := by
    rw [overlapping,sum_filter,← sum_add_distrib]
    apply sum_congr rfl; intro ij hij
    have ord := (mem_filter.mp hij).2.1
    by_cases f : exceptional (h:=h) (g:=g) ij.1 ij.2
    · simp [f,adjustment]
    · simp only [f,ite_false,add_zero,separatePair]
      exact all_ordinary_pairs_uncharged hg gh half _ _ (ne_of_lt ord) f
  rw [total]; ring

#print axioms executed_separated_ledger
end
end Shellsort.ThreePassSeparatedLedger
