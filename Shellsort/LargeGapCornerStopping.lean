import Shellsort.LargeGapCornerRecords
import Shellsort.LargeGapStoppingCost

namespace Shellsort.LargeGapCornerStopping
open Finset LargeGapCornerRecords LargeGapRecordWeights LargeGapRecordMean HarvestOperationalAudit
noncomputable section

private def pool (d t g j : ℕ) := min j g + min j (d+t) + min j d

private def term (d t g j : ℕ) : ℝ :=
  ((pool d t g (j+1) - pool d t g j : ℕ) : ℝ)/(pool d t g (j+1) : ℝ)

private theorem pool_eq (n h g d t j : ℕ) (gap : d=h-g) (old : d+t=n-h) (enough : d+t ≤ g) :
    cappedWeight n j [g,h] = pool d t g j := by
  simp [cappedWeight,weight,pool, ←gap, ←old]
  omega

theorem sum_terms (d t s : ℕ) :
    let g := d+t+s
    let n := g+(2*d+t)
    ∑ j ∈ range n, term d t g j = harmonic n + reduced d t := by
  let g := d+t+s
  let n := g+(2*d+t)
  let f := term d t g
  change ∑ j ∈ range n, f j = harmonic n + reduced d t
  have first : ∑ j ∈ range d, f j = harmonic d := by
    apply sum_congr rfl
    intro j hj
    have hj' := mem_range.mp hj
    have h1 : pool d t g (j+1) = 3*(j+1) := by dsimp [pool,g]; omega
    have h0 : pool d t g j = 3*j := by dsimp [pool,g]; omega
    dsimp [f,term]; rw [h1,h0,show 3*(j+1)-3*j=3 by omega]
    push_cast; field_simp
  have second : (∑ j ∈ range t, f (d+j)) = ∑ j ∈ range t, 2/(3*(d:ℝ)+2*(j:ℝ)+2) := by
    apply sum_congr rfl
    intro j hj
    have hj' := mem_range.mp hj
    have h1 : pool d t g (d+j+1) = 3*d+2*j+2 := by dsimp [pool,g]; omega
    have h0 : pool d t g (d+j) = 3*d+2*j := by dsimp [pool,g]; omega
    dsimp [f,term]; rw [h1,h0,show 3*d+2*j+2-(3*d+2*j)=2 by omega]
    push_cast; rfl
  have third : (∑ j ∈ range s, f (d+t+j)) =
      ∑ j ∈ range s, 1/(((3*d+2*t+j:ℕ):ℝ)+1) := by
    apply sum_congr rfl
    intro j hj
    have hj' := mem_range.mp hj
    have h1 : pool d t g (d+t+j+1) = 3*d+2*t+j+1 := by dsimp [pool,g]; omega
    have h0 : pool d t g (d+t+j) = 3*d+2*t+j := by dsimp [pool,g]; omega
    dsimp [f,term]; rw [h1,h0,show 3*d+2*t+j+1-(3*d+2*t+j)=1 by omega]
    push_cast; rfl
  have fourth : (∑ j ∈ range (2*d+t), f (g+j)) = 0 := by
    apply sum_eq_zero
    intro j _
    have h : pool d t g (g+j+1) = pool d t g (g+j) := by dsimp [g,pool]; omega
    dsimp [f,term]; rw [h]; simp
  have hH : harmonic n = harmonic (3*d+2*t) +
      ∑ j ∈ range s, 1/(((3*d+2*t+j:ℕ):ℝ)+1) := by
    have hn : n = (3*d+2*t)+s := by dsimp [n,g]; omega
    simp only [hn,harmonic,sum_range_add]
  calc
    _ = (((∑ j ∈ range d, f j)+(∑ j ∈ range t, f (d+j))) +
        (∑ j ∈ range s, f (d+t+j)))+(∑ j ∈ range (2*d+t), f (g+j)) := by
          change (∑ j ∈ range (g+(2*d+t)), f j) = _
          rw [sum_range_add f g]
          congr 1
          change (∑ j ∈ range ((d+t)+s), f j) = _
          rw [sum_range_add f (d+t), sum_range_add f d]
    _ = _ := by rw [first,second,third,fourth,hH]; unfold reduced; ring

/-- The ordinary program's mean stopping comparisons is n-H_n minus the
record adjustment used in the one-dimensional corner optimization. -/
theorem executed_mean {n : ℕ} (w : HarvestBlockIteration.PositiveWord)
    (asc : (w.map Subtype.val).reverse.Pairwise (· < ·))
    (large : ∀ h ∈ w, h.val < n ∧ n ≤ 2*h.val)
    (g h d t : ℕ) (gaps : (w.map Subtype.val).reverse = [g,h])
    (hg : h ≤ n) (gh : g ≤ h) (gap : d=h-g) (old : d+t=n-h) (size : d+t ≤ g) :
    uniformAverage (fun p : RankPlacement n =>
      (((runPass (runWord (slots p) w).1 ⟨1,by decide⟩).2 : ℕ) : ℝ) -
        (gapInsertionCost (sortWord p (w.map Subtype.val)) 1 (by decide) : ℝ)) =
      (n:ℝ)-harmonic n-reduced d t := by
  rw [LargeGapStoppingCost.final_stopping_mean w asc large]
  rw [gaps]
  simp_rw [pool_eq n h g d t _ gap old size]
  change (n:ℝ) - (∑ j : Fin n, term d t g j.val) = _
  rw [Fin.sum_univ_eq_sum_range]
  have H := sum_terms d t (g-(d+t))
  dsimp only at H
  rw [show d+t+(g-(d+t))=g by omega, show g+(2*d+t)=n by omega] at H
  rw [H]; ring

#print axioms executed_mean
end
end Shellsort.LargeGapCornerStopping
