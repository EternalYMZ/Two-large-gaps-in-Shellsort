import Shellsort.LocalGatePivotCounts
import Shellsort.TwoLargeGapQuadratics

namespace Shellsort.SevenSegmentBaseline
open LocalGatePivotCounts LocalRelativeOrderMean Finset

/-- The successive physical regions: three low outputs, one untouched
key, then three high outputs. The middle column changes type at 2a=b. -/
def tree (overlap second : Bool) : Fin 7 → GateTree 8 :=
  let u : Fin 8 := if second then 4 else 0
  let v : Fin 8 := if second then 5 else 1
  let w : Fin 8 := if second then 6 else 2
  let z : Fin 8 := if second then 7 else 3
  let A := column (small true u v) (large false w z)
  let B := column (small overlap u v) (large overlap w z)
  let C := column (small false u v) (large true w z)
  ![A.1,B.1,C.1,.leaf u,A.2,B.2,C.2]

def table (overlap : Bool) : Fin 7 → Fin 7 → ℕ :=
  if overlap then
    ![![210,180,126,105,63,30,21],
       ![240,210,152,126,82,42,30],
       ![294,268,210,175,133,82,63],
       ![315,294,245,210,175,126,105],
       ![357,338,287,245,210,152,126],
       ![390,378,338,294,268,210,180],
       ![399,390,357,315,294,240,210]]
  else
    ![![210,168,126,105,63,42,21],
       ![252,210,168,140,98,70,42],
       ![294,252,210,175,133,98,63],
       ![315,280,245,210,175,140,105],
       ![357,322,287,245,210,168,126],
       ![378,350,322,280,252,210,168],
       ![399,378,357,315,294,252,210]]

set_option maxRecDepth 1048576
set_option maxHeartbeats 0

private theorem check_table (o : Bool) (i j : Fin 7) :
    numerator (tree o false i) (tree o true j) = 96 * table o i j := by
  cases o <;> fin_cases i <;> fin_cases j <;> decide

noncomputable def prob (o : Bool) (i j : Fin 7) : ℝ :=
  uniformAverage (fun p : RankPlacement 8 => if evaluate p.symm (tree o true j) <
    evaluate p.symm (tree o false i) then (1:ℝ) else 0)

theorem prob_table (o : Bool) (i j : Fin 7) :
    prob o i j = (table o i j:ℝ)/420 := by
  unfold prob
  rw [numerator_exact,check_table,show Nat.factorial 8 = 40320 by decide]
  push_cast
  ring

/-- Widths of the low, middle, and high regions in units of physical slots. -/
def widths (x y z : ℝ) : Fin 7 → ℝ := ![x,y,x,z,x,y,x]

/-- Ordered pairs between successive segments plus the true finite count
within one segment. Each pair uses independent copies of its inputs. -/
noncomputable def mass (o : Bool) (x y z : ℝ) : ℝ :=
  let w := widths x y z
  ∑ i : Fin 7, ∑ j : Fin 7,
    if i < j then w i * w j * prob o i j
    else if i = j then w i * (w i - 1) / 2 * prob o i j else 0

private theorem expand (f : Fin 7 → ℝ) :
    ∑ i, f i = f 0 + f 1 + f 2 + f 3 + f 4 + f 5 + f 6 := by
  rw [Fin.sum_univ_succ]; simp [Fin.sum_univ_succ,add_assoc]

/-- Closed quadratics for the two possible layouts. No asymptotic limits
or independent-sample approximation occurs in this finite template sum. -/
theorem baseline_quadratics (n a b : ℝ) :
    mass false a (b-2*a) (n-2*b) =
      n^2/4-b*n/3+2*a^2/5-2*a*b/5+b^2/3 - n/4 ∧
    mass true (b-a) (2*a-b) (n-2*b) =
      n^2/4-2*a*n/15-4*b*n/15+(46*a^2-34*a*b+30*b^2)/105 - n/4 := by
  constructor <;> unfold mass <;> simp only [expand,prob_table] <;>
    norm_num [widths,table,Fin.lt_def] <;> ring

#print axioms baseline_quadratics
end Shellsort.SevenSegmentBaseline
