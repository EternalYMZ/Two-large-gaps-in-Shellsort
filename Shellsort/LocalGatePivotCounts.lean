import Shellsort.LocalRelativeOrderMean
import Shellsort.LargeGapCorrectionMultiplicities
import Shellsort.TaggedLaw

namespace Shellsort.LocalGatePivotCounts
open Finset LocalRelativeOrderMean

def test {n} (s : Finset (Fin n)) : GateTree n → Bool
  | .leaf i => decide (i ∈ s)
  | .low a b => test s a || test s b
  | .high a b => test s a && test s b

private theorem test_threshold {n} (p : RankPlacement n) (v : ℕ) (a : GateTree n) :
    test (thresholdSet p v) a = true ↔ (evaluate p.symm a).val < v := by
  induction a with
  | leaf i => simp [test,thresholdSet,evaluate]
  | low a b h j => simp [test,evaluate,h,j,Fin.val_min,min_lt_iff]
  | high a b h j => simp [test,evaluate,h,j,Fin.val_max,max_lt_iff]

def hit {n} (l r : GateTree n) (s : Finset (Fin n)) (i : Fin n) : Bool :=
  test s r && (!test s l) && test (insert i s) l

def numerator {n} (l r : GateTree n) : ℕ :=
  ∑ i : Fin n, ∑ B : TaggedSubset i,
    if hit l r B.val i then B.val.card.factorial * (n-1-B.val.card).factorial else 0

private theorem hit_iff {n} (p : RankPlacement n) (l r : GateTree n) (i : Fin n) :
    hit l r (tagLowerState p i).val i = true ↔
      evaluate p.symm r < evaluate p.symm l ∧ evaluate p.symm l = p.symm i := by
  have up := thresholdSet_succ_tag p (p.symm i)
  rw [Equiv.apply_symm_apply] at up
  simp only [hit,tagLowerState,← up,Bool.and_eq_true,Bool.not_eq_true',
    ← Bool.not_eq_true,test_threshold]
  constructor
  · rintro ⟨⟨hr,hl⟩,hw⟩
    have eq : (evaluate p.symm l).val = (p.symm i).val := by omega
    exact ⟨by change (evaluate p.symm r).val < (evaluate p.symm l).val; omega,Fin.ext eq⟩
  · rintro ⟨lt,eq⟩; rw [eq] at lt ⊢
    exact ⟨⟨lt,lt_irrefl _⟩,Nat.lt_succ_self _⟩

/-- Accumulate exactly one contribution, at the rank of the left-hand output. -/
theorem numerator_exact {n} (l r : GateTree n) :
    uniformAverage (fun p : RankPlacement n =>
      if evaluate p.symm r < evaluate p.symm l then (1:ℝ) else 0) =
      (numerator l r : ℝ) / (n.factorial : ℝ) := by
  classical
  let f (i : Fin n) (B : TaggedSubset i) : ℝ := if hit l r B.val i then 1 else 0
  have point (p : RankPlacement n) :
      (if evaluate p.symm r < evaluate p.symm l then (1:ℝ) else 0) =
        ∑ i : Fin n, f i (tagLowerState p i) := by
    simp only [f, hit_iff]
    by_cases lt : evaluate p.symm r < evaluate p.symm l
    · simp [lt,eq_comm,Equiv.symm_apply_eq]
    · simp [lt]
  simp_rw [point]
  have e : uniformAverage (fun p : RankPlacement n => ∑ i, f i (tagLowerState p i)) =
      ∑ i, uniformAverage (fun p : RankPlacement n => f i (tagLowerState p i)) := by
    unfold uniformAverage; rw [sum_comm,sum_div]
  rw [e,numerator,Nat.cast_sum,sum_div]
  apply sum_congr rfl; intro i _
  rw [uniform_tagged_state_mean,Nat.cast_sum,sum_div]
  apply sum_congr rfl; intro B _
  by_cases h : hit l r B.val i <;> simp [f,h]

abbrev T := GateTree 8
def v (i : Fin 8) : T := .leaf i
def column (x y : T) : T × T := (.low x y,.high x y)
def small (on : Bool) (i j : Fin 8) : T := if on then .low (v i) (v j) else v i
def large (on : Bool) (i j : Fin 8) : T := if on then .high (v i) (v j) else v i

def selfNum (x y independent : Bool) : ℕ :=
  let c := column (small x 0 1) (large y 2 3)
  let c' := if independent then column (small x 4 5) (large y 6 7) else c
  numerator c.1 c'.2

def edgeNum (x y independent : Bool) : ℕ :=
  let c := column (.low (v 0) (v 1)) (large x 2 3)
  let z := if independent then GateTree.high (v 6) (v 7) else .high (v 0) (v 1)
  let e := column (small y 4 5) z
  numerator c.1 e.1 + numerator c.1 e.2 + numerator e.1 c.2 + numerator c.2 e.2

private noncomputable def prob (l r : T) : ℝ := uniformAverage (fun p : RankPlacement 8 =>
  if evaluate p.symm r < evaluate p.symm l then (1:ℝ) else 0)

noncomputable def selfMean (x y disjoint : Bool) : ℝ :=
  let c := column (small x 0 1) (large y 2 3)
  let c' := if disjoint then column (small x 4 5) (large y 6 7) else c
  prob c.1 c'.2

noncomputable def edgeMean (x y disjoint : Bool) : ℝ :=
  let c := column (.low (v 0) (v 1)) (large x 2 3)
  let z := if disjoint then GateTree.high (v 6) (v 7) else .high (v 0) (v 1)
  let e := column (small y 4 5) z
  prob c.1 e.1 + prob c.1 e.2 + prob e.1 c.2 + prob c.2 e.2

set_option maxRecDepth 1048576
set_option maxHeartbeats 16000000

private theorem same_counts (x y : Bool) :
    (selfNum x y false : ℤ) - (selfNum x y true : ℤ) =
      96 * LargeGapCorrectionMultiplicities.samePair x y := by
  cases x <;> cases y <;> decide

private theorem edge_counts (x y : Bool) :
    (edgeNum x y false : ℤ) - (edgeNum x y true : ℤ) =
      96 * LargeGapCorrectionMultiplicities.neighbor x y := by
  cases x <;> cases y <;> decide

private theorem prob_count (l r : T) : prob l r = (numerator l r : ℝ)/40320 := by
  exact (numerator_exact l r).trans (by rw [show Nat.factorial 8 = 40320 by decide]; norm_cast)

private theorem sum_four (a b c d : ℕ) :
    (a:ℝ)/40320+(b:ℝ)/40320+(c:ℝ)/40320+(d:ℝ)/40320 = ((a+b+c+d:ℕ):ℝ)/40320 := by
  push_cast; ring

private theorem scale (a b : ℕ) (v : ℤ) (h : (a:ℤ)-b = 96*v) :
    420*((a:ℝ)/40320-(b:ℝ)/40320) = (v:ℝ) := by
  have e : (a:ℝ)-(b:ℝ)=96*(v:ℝ) := by exact_mod_cast h
  linarith

theorem eight_corrections (x y : Bool) :
    420*(selfMean x y false-selfMean x y true) = (LargeGapCorrectionMultiplicities.samePair x y : ℝ) ∧
    420*(edgeMean x y false-edgeMean x y true) = (LargeGapCorrectionMultiplicities.neighbor x y : ℝ) := by
  have se (b : Bool) : selfMean x y b = (selfNum x y b : ℝ)/40320 := by
    exact prob_count _ _
  have ee (b : Bool) : edgeMean x y b = (edgeNum x y b : ℝ)/40320 := by
    unfold edgeMean edgeNum
    simp only [prob_count]
    exact sum_four _ _ _ _
  simp only [se,ee]
  exact ⟨scale _ _ _ (same_counts x y),scale _ _ _ (edge_counts x y)⟩

#print axioms eight_corrections

end Shellsort.LocalGatePivotCounts
