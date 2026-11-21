import Mathlib.Tactic

namespace Shellsort.LargeGapCorrectionMultiplicities
open Finset

/-- Scaled by 420. The two flags describe an input from a first-pass pair. -/
def samePair (left right : Bool) : ℤ :=
  if left && right then -42 else if left || right then -63 else -70

/-- Scaled sum for all four cross-output pairs from neighboring comparators. -/
def neighbor (left right : Bool) : ℤ :=
  if left && right then -70 else if left || right then -66 else -56

private def mark (l u i : ℕ) : ℤ := if l ≤ i ∧ i < u then 1 else 0

private theorem mark_sum (N l u : ℕ) (hu : u ≤ N) :
    ∑ i ∈ range N, mark l u i = (u-l:ℕ) := by
  have e : (range N).filter (fun i => l ≤ i ∧ i < u) = Ico l u := by
    ext i; simp; omega
  simp only [mark,← sum_filter,e,sum_const,Nat.card_Ico,nsmul_eq_mul,mul_one]

private theorem same_mark (a d i : ℕ) (hi : i < a+d) :
    samePair (decide (i < a)) (decide (d ≤ i)) =
      -70+7*mark 0 a i+7*mark d (a+d) i+14*mark d a i := by
  by_cases x : i < a <;> by_cases y : d ≤ i <;> simp [samePair,mark,x,y,hi]

private theorem neighbor_mark (a d i : ℕ) (hi : i < a) :
    neighbor (decide (d ≤ i)) (decide (i+d < a)) =
      -56-10*mark d a i-10*mark 0 (a-d) i+6*mark d (a-d) i := by
  have iff : i < a-d ↔ i+d < a := by omega
  by_cases x : d ≤ i <;> by_cases y : i+d < a <;> simp [neighbor,mark,x,y,hi,iff]

def total (a d : ℕ) : ℤ :=
  (∑ i ∈ range (a+d), samePair (decide (i < a)) (decide (d ≤ i))) +
  ∑ i ∈ range a, neighbor (decide (d ≤ i)) (decide (i+d < a))

/-- Sum the two flag tables exactly for every integer width, with b = a+d.
The omitted universal diagonal correction is -n/4 before scaling. -/
theorem three_regions (a d : ℕ) :
    total a d = if a ≤ d then -42*(a:ℤ)-70*(a+d:ℕ)
      else if a ≤ 2*d then -54*(a:ℤ)-64*(a+d:ℕ)
      else -36*(a:ℤ)-76*(a+d:ℕ) := by
  unfold total
  rw [sum_congr rfl (fun i hi => same_mark a d i (mem_range.mp hi)),
    sum_congr rfl (fun i hi => neighbor_mark a d i (mem_range.mp hi))]
  simp only [sum_add_distrib,sum_sub_distrib,← mul_sum,sum_const,card_range,
    nsmul_eq_mul,mark_sum (a+d) 0 a (by omega),mark_sum (a+d) d (a+d) le_rfl,
    mark_sum (a+d) d a (by omega),mark_sum a d a le_rfl,
    mark_sum a 0 (a-d) (by omega),mark_sum a d (a-d) (by omega)]
  split <;> omega

#print axioms three_regions
end Shellsort.LargeGapCorrectionMultiplicities
