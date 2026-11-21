import Mathlib.Tactic

/-! In counts (d,a)=(b-a,a), with a≥d, the record mean minus H_n consists
of d groups of size three and a-d groups of size two. The rest are singletons. -/
namespace Shellsort.LargeGapCornerRecords
open Finset
noncomputable section

def harmonic (r : ℕ) : ℝ := ∑ i ∈ range r, 1 / ((i : ℝ)+1)

def reduced (d t : ℕ) : ℝ :=
  harmonic d + (∑ i ∈ range t, 2/(3*(d:ℝ)+2*(i:ℝ)+2)) - harmonic (3*d+2*t)

private theorem harmonic_succ (r : ℕ) :
    harmonic (r+1) = harmonic r + 1/((r:ℝ)+1) := by
  simp [harmonic, sum_range_succ]

private def middle (x : ℝ) (t : ℕ) : ℝ :=
  ∑ i ∈ range t, (2/(x+2*(i:ℝ)+1)-2/(x+2*(i:ℝ)+2))

private theorem between (x : ℝ) (hx : 0 < x) :
    1/(x+1)-1/(x+3) ≤ 2/(x+1)-2/(x+2) ∧
    2/(x+1)-2/(x+2) ≤ 1/x-1/(x+2) := by
  constructor <;> field_simp <;> nlinarith

private theorem middle_bounds (x : ℝ) (hx : 0 < x) (t : ℕ) :
    1/(x+1)-1/(x+2*(t:ℝ)+1) ≤ middle x t ∧
    middle x t ≤ 1/x-1/(x+2*(t:ℝ)) := by
  induction t with
  | zero => simp [middle]
  | succ t ih =>
    have hb := between (x+2*(t:ℝ)) (by positivity)
    have hs : middle x (t+1) = middle x t +
        (2/(x+2*(t:ℝ)+1)-2/(x+2*(t:ℝ)+2)) := by simp only [middle, sum_range_succ]
    rw [hs, Nat.cast_add_one]
    rw [show x+2*((t:ℝ)+1)+1 = x+2*(t:ℝ)+3 by ring,
        show x+2*((t:ℝ)+1) = x+2*(t:ℝ)+2 by ring]
    constructor <;> linarith [ih.1, ih.2, hb.1, hb.2]

private theorem difference (d t : ℕ) :
    reduced d (t+2) - reduced (d+1) t =
      2/(3*(d:ℝ)+2)-1/((d:ℝ)+1)+middle (3*((d:ℝ)+1)) t+
      1/(3*((d:ℝ)+1)+2*(t:ℝ)+1) := by
  unfold reduced middle
  rw [show 3*d+2*(t+2) = (3*(d+1)+2*t)+1 by omega, harmonic_succ, harmonic_succ d]
  rw [sum_range_succ', sum_range_succ]
  rw [sum_sub_distrib]
  push_cast
  have ea : (∑ i ∈ range t, 2/(3*(d:ℝ)+2*((i:ℝ)+1)+2)) =
      (∑ i ∈ range t, 2/(3*((d:ℝ)+1)+2*(i:ℝ)+1)) := by
    apply sum_congr rfl; intro i hi; congr 1; ring
  rw [ea]
  ring

/-- One unit moves from the shorter side to the longer side. Even when the
two sides were equal before that move, the resulting record difference is positive. -/
theorem record_increment (d t : ℕ) :
    0 < reduced d (t+2) - reduced (d+1) t ∧
    reduced d (t+2) - reduced (d+1) t ≤ 2/(3*((d:ℝ)+1)*(3*((d:ℝ)+1)-1)) := by
  rw [difference]
  let x : ℝ := (d:ℝ)+1
  have hx : 1 ≤ x := by dsimp [x]; exact_mod_cast (show 1 ≤ d+1 by omega)
  have hlow := (middle_bounds (3*x) (by positivity) t).1
  have hhigh := (middle_bounds (3*x) (by positivity) t).2
  have hfirst : 3*(d:ℝ)+2 = 3*x-1 := by dsimp [x]; ring
  rw [hfirst]
  change 0 < 2/(3*x-1)-1/x+middle (3*x) t+1/(3*x+2*(t:ℝ)+1) ∧ _
  have hp : 0 < 2/(3*x-1)-1/x+1/(3*x+1) := by
    have h : 0 < 3*x-1 := by linarith
    field_simp <;> nlinarith
  have he : 2/(3*x-1)-1/x+1/(3*x) = 2/(3*x*(3*x-1)) := by
    have h : 0 < 3*x-1 := by linarith
    field_simp <;> ring
  have ht : 1/(3*x+2*(t:ℝ)+1) ≤ 1/(3*x+2*(t:ℝ)) :=
    one_div_le_one_div_of_le (by positivity) (by linarith)
  constructor
  · linarith
  · change 2/(3*x-1)-1/x+middle (3*x) t+1/(3*x+2*(t:ℝ)+1) ≤ _
    change _ ≤ 2/(3*x*(3*x-1))
    linarith

#print axioms record_increment
end
end Shellsort.LargeGapCornerRecords
