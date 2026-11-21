import Shellsort.PhysicalExceptionBijection

namespace Shellsort.ThreePassPhysicalCorrection
open LocalRelativeOrderMean ThreePassSeparatedLedger PhysicalSeparatedTemplates
open PhysicalSeparatedEdges PhysicalExceptionBijection Finset LargeGapCorrectionMultiplicities
noncomputable section

private theorem single {n h g : ℕ} (hg : 0<g) (gh : g<h) (hn : h<n) (half : n ≤ 2*g)
    (i : Fin (n-g)) :
    420*adjustment n h g (pair hg gh hn half (.inl i)) =
      (samePair (decide (i.val<n-h)) (decide (h-g ≤ i.val)):ℝ) := by
  let u : Fin n := ⟨i.val,by have := i.isLt; omega⟩
  have fit : u.val+g<n := by dsimp [u]; have := i.isLt; omega
  have e := charged_self hg gh half u fit
  have s : (u.val+h<n) ↔ i.val<n-h := by dsimp [u]; omega
  have t : (h ≤ u.val+g) ↔ h-g ≤ i.val := by dsimp [u]; omega
  simp only [s,t] at e
  dsimp only [pair,pairNat,adjustment,separatePair]
  exact e

private theorem four {n h g : ℕ} (hg : 0<g) (gh : g<h) (hn : h<n) (half : n ≤ 2*g)
    (i : Fin (n-h)) :
    420*(∑ k : Fin 4, adjustment n h g (pair hg gh hn half (.inr (i,k)))) =
      (neighbor (decide (h-g ≤ i.val)) (decide (i.val+(h-g)<n-h)):ℝ) := by
  let u : Fin n := ⟨i.val,by have := i.isLt; omega⟩
  let v : Fin n := ⟨i.val+(h-g),by have := i.isLt; omega⟩
  have up : u.val+g<n := by dsimp [u]; have := i.isLt; omega
  have vp : v.val+g<n := by dsimp [v]; have := i.isLt; omega
  have shared : v.val+g = u.val+h := by dsimp [u,v]; omega
  have e := charged_edge gh half u v up vp shared
  have x : (h ≤ u.val+g) ↔ h-g ≤ i.val := by dsimp [u]; omega
  have y : (v.val+h<n) ↔ i.val+(h-g)<n-h := by dsimp [v]; omega
  simp only [x,y] at e
  apply Eq.trans _ e
  rw [Fin.sum_univ_four]
  dsimp only [PhysicalNeighborCorrection.actualEdge,edgeBaseline]
  dsimp only [pair,pairNat,adjustment,separatePair,u,v]
  have k0 : (0 : Fin 4).val = 0 := rfl
  have k1 : (1 : Fin 4).val = 1 := rfl
  have k2 : (2 : Fin 4).val = 2 := rfl
  have k3 : (3 : Fin 4).val = 3 := rfl
  norm_num [k0,k1,k2,k3]
  ring

theorem scaled_adjustment {n h g : ℕ} (hg : 0<g) (gh : g<h) (hn : h<n) (half : n ≤ 2*g) :
    420*(∑ ij ∈ overlapping n h g, adjustment n h g ij) =
      (total (n-h) (h-g):ℝ) := by
  rw [sum_columns hg gh hn half,mul_add,Finset.mul_sum,Finset.mul_sum]
  simp only [single hg gh hn half,four hg gh hn half]
  change (∑ i : Fin (n-g), ((samePair (decide (i.val<n-h)) (decide (h-g ≤ i.val)) : ℤ):ℝ)) +
    ∑ i : Fin (n-h), ((neighbor (decide (h-g ≤ i.val)) (decide (i.val+(h-g)<n-h)) : ℤ):ℝ) = _
  rw [Fin.sum_univ_eq_sum_range (fun i => ((samePair (decide (i<n-h)) (decide (h-g ≤ i)):ℤ):ℝ)),
    Fin.sum_univ_eq_sum_range (fun i => ((neighbor (decide (h-g ≤ i)) (decide (i+(h-g)<n-h)):ℤ):ℝ))]
  simp only [total,Int.cast_add,Int.cast_sum,show n-h+(h-g)=n-g by omega]

/-- Full actual comparison cost for all legal n,h,g. The overlap correction
is explicit and piecewise linear; the two-tree independent baseline is retained. -/
theorem executed_with_correction {n h g : ℕ} (hg : 0<g) (gh : g<h)
    (hn : h<n) (half : n ≤ 2*g) :
    let a := n-h
    let d := h-g
    let w : HarvestBlockIteration.PositiveWord := [⟨h,by omega⟩,⟨g,hg⟩,⟨1,by decide⟩]
    uniformAverage (fun p : RankPlacement n => ((HarvestOperationalAudit.runWord
      (HarvestOperationalAudit.slots p) w).2:ℝ)) =
      (a:ℝ)+(n-g:ℕ)+n-LargeGapCornerRecords.harmonic n-LargeGapRecordChanges.grouped a d +
      ∑ ij ∈ gapPositionPairs n 1, separatePair n h g ij +
      ((if a ≤ d then -42*(a:ℤ)-70*(a+d:ℕ) else if a ≤ 2*d then -54*(a:ℤ)-64*(a+d:ℕ)
        else -36*(a:ℤ)-76*(a+d:ℕ) : ℤ):ℝ)/420 := by
  dsimp only
  apply (executed_separated_ledger hg gh hn half).trans
  have corr := scaled_adjustment hg gh hn half
  rw [three_regions] at corr
  linarith

#print axioms executed_with_correction
end
end Shellsort.ThreePassPhysicalCorrection
