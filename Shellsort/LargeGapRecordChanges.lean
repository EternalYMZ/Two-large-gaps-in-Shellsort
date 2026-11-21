import Shellsort.LargeGapCornerRecords

namespace Shellsort.LargeGapRecordChanges
open LargeGapCornerRecords Finset
noncomputable section

/-- The two widths exchanged by an increment of the left count. -/
def grouped (x y : ℕ) : ℝ :=
  if x ≤ y then reduced x (y-x) else reduced y (x-y)

theorem grouped_comm (x y : ℕ) : grouped x y = grouped y x := by
  rcases lt_trichotomy x y with h|h|h
  · simp [grouped, h.le, not_le.mpr h]
  · subst x; rfl
  · simp [grouped, h.le, not_le.mpr h]

private theorem longer (d t : ℕ) :
    -(1/2:ℝ) ≤ reduced d (t+1)-reduced d t ∧ reduced d (t+1)-reduced d t < 0 := by
  have H (r:ℕ) : harmonic (r+1) = harmonic r + 1/((r:ℝ)+1) := by
    simp [harmonic, sum_range_succ]
  have e : reduced d (t+1)-reduced d t =
      1/(3*(d:ℝ)+2*(t:ℝ)+2)-1/(3*(d:ℝ)+2*(t:ℝ)+1) := by
    unfold reduced
    rw [show 3*d+2*(t+1) = (3*d+2*t+1)+1 by omega, H, H, sum_range_succ]
    push_cast; ring
  rw [e]
  have aux (x:ℝ) (hx:0≤x) :
      -(1/2:ℝ) ≤ 1/(x+2)-1/(x+1) ∧ 1/(x+2)-1/(x+1) < 0 := by
    constructor <;> field_simp <;> nlinarith [sq_nonneg x]
  exact aux _ (by positivity)

private theorem forward_transfer (x y : ℕ) (h : y < x) :
    0 < grouped (x+1) y-grouped x (y+1) ∧
    grouped (x+1) y-grouped x (y+1) ≤ (1/3:ℝ) := by
  let t := x-(y+1)
  have hr := record_increment y t
  rw [grouped_comm (x+1), grouped_comm x]
  simp only [grouped, if_pos (show y≤x+1 by omega),if_pos (show y+1≤x by omega),
    show x+1-y=t+2 by dsimp [t]; omega]
  change _ ∧ reduced y (t+2)-reduced (y+1) t ≤ _
  refine ⟨hr.1,hr.2.trans ?_⟩
  have hp : (0:ℝ)<3*((y:ℝ)+1)-1 := by linarith [Nat.cast_nonneg (α:=ℝ) y]
  apply (div_le_div_iff₀ (by positivity) (by norm_num)).2
  nlinarith [sq_nonneg (y:ℝ)]

theorem transfer (x y : ℕ) :
    |grouped (x+1) y-grouped x (y+1)| ≤ 1/3 := by
  rcases lt_trichotomy y x with h|h|h
  · have t := forward_transfer x y h
    rw [abs_of_pos t.1]
    exact t.2
  · subst x; rw [grouped_comm (y+1),sub_self,abs_zero]; norm_num
  · have t := forward_transfer y x h
    rw [grouped_comm (x+1),grouped_comm x,abs_sub_comm,abs_of_pos t.1]
    exact t.2

theorem extend (x y : ℕ) :
    -(5/6:ℝ) ≤ grouped x (y+1)-grouped x y ∧
    grouped x (y+1)-grouped x y < 0 := by
  by_cases h : x ≤ y
  · simp only [grouped, if_pos h,if_pos (show x≤y+1 by omega),show y+1-x=(y-x)+1 by omega]
    have t := longer x (y-x)
    constructor <;> linarith [t.1,t.2]
  · have t := longer y (x-y)
    have tr := forward_transfer x y (by omega)
    have e : grouped (x+1) y-grouped x y = reduced y ((x-y)+1)-reduced y (x-y) := by
      simp only [grouped, if_neg h, if_neg (show ¬ x+1≤y by omega),show x+1-y=(x-y)+1 by omega]
    constructor <;> linarith [tr.1,tr.2,t.1,t.2]

/-- For the two-gap score, the mean record count minus H_n has both stability
properties; adding a second paired slot strictly decreases the record mean. -/
theorem neighboring (a b : ℕ) (h : a < b) :
    |grouped (a+1) (b-(a+1))-grouped a (b-a)| ≤ 1/3 ∧
    -(5/6:ℝ) ≤ grouped a (b+1-a)-grouped a (b-a) ∧
    grouped a (b+1-a)-grouped a (b-a) < 0 := by
  constructor
  · convert transfer a (b-(a+1)) using 2 <;> congr 2 <;> omega
  · rw [show b+1-a=(b-a)+1 by omega]; exact extend a (b-a)

#print axioms neighboring
end
end Shellsort.LargeGapRecordChanges
