import Shellsort.TwoGapOverlapWinner

namespace Shellsort.TwoGapHalfWinner
open LargeGapCornerRecords LargeGapRecordChanges LargeGapCornerWinner ThreePassClosedMean
open ExecutionCornerWinner TwoGapOverlapWinner
noncomputable section

private def records (a b : ℕ) : ℝ := grouped a (b-a)
private def left (n a b : ℝ) : ℝ :=
  a+b+n+n^2/4-b*n/3+2*a^2/5-2*a*b/5+b^2/3-n/4-a/10-b/6
private def middle (n a b : ℝ) : ℝ :=
  a+b+n+n^2/4-2*a*n/15-4*b*n/15+
   (46*a^2-34*a*b+30*b^2)/105-n/4-9*a/70-16*b/105

private theorem leftexact {n a b : ℕ} (ap:0<a) (ab:a<b) (half:2*b≤n) (dis:2*a≤b) :
  actual n a b (by omega) (by omega) = left n a b-harmonic n-records a b := by
  unfold actual
  rw [executed_closed (show 0<n-b by omega) (show n-b<n-a by omega) (show n-a<n by omega)
    (show n≤2*(n-b) by omega), show n-(n-a)=a by omega, show n-(n-b)=b by omega,
    show n-a-(n-b)=b-a by omega]
  simp only [baseline,if_neg (show ¬b-a<a by omega), if_pos (show a≤b-a by omega)]
  unfold left records
  push_cast
  ring

private theorem midexact {n a b : ℕ} (ab:a<b) (half:2*b≤n) (overlap:b<2*a) (mid:3*a≤2*b) :
  actual n a b (by omega) (by omega) = middle n a b-harmonic n-records a b := by
  unfold actual
  rw [executed_closed (show 0<n-b by omega) (show n-b<n-a by omega) (show n-a<n by omega)
    (show n≤2*(n-b) by omega), show n-(n-a)=a by omega, show n-(n-b)=b by omega,
    show n-a-(n-b)=b-a by omega]
  simp only [baseline, if_pos (show b-a<a by omega), if_neg (show ¬a≤b-a by omega),
    if_pos (show a≤2*(b-a) by omega)]
  unfold middle records
  push_cast
  ring

private theorem records_lipschitz (a j b : ℕ) (h:a+j≤b) :
   |records (a+j) b - records a b| ≤ (j:ℝ)/3 := by
  induction j with
  | zero => simp
  | succ j ih =>
    have first := ih (by omega)
    have second := (neighboring (a+j) b (by omega)).1
    change |records (a+j+1) b-records (a+j) b| ≤ 1/3 at second
    have sum := abs_sub_le (records (a+j+1) b) (records (a+j) b) (records a b)
    rw [← Nat.add_assoc]
    push_cast
    linarith

private theorem near_boundary {n a b q:ℕ} (ap:0<a) (ab:a<b) (half:2*b≤n)
    (aq:a≤q) (eq:q=b/2) :
    actual n q b (by omega) (by omega) - 1 < actual n a b (by omega) (by omega) := by
  let j := q-a
  have aj : a+j=q := by dsimp [j]; omega
  have aj' : (a:ℝ)+j=q := by exact_mod_cast aj
  have qb : 2*(q:ℝ)≤b := by exact_mod_cast (show 2*q≤b by omega)
  have nonneg : 0≤(j:ℝ) := Nat.cast_nonneg _
  have recBound := records_lipschitz a j b (by omega)
  rw [aj] at recBound
  have lower := (abs_le.mp recBound).1
  rw [leftexact (by omega) (by omega) half (by omega),
    leftexact ap ab half (by omega)]
  have det : left n a b-left n q b =
    2/5*(j:ℝ)^2+2/5*((b:ℝ)-2*q)*j-9/10*j := by
    rw [←aj']; unfold left; ring
  have prod := mul_nonneg (sub_nonneg.mpr qb) nonneg
  nlinarith [sq_nonneg (24*(j:ℝ)-37)]

private theorem across_boundary {n b q:ℕ} (hn:237≤n) (hb:b=n/2) (hq:q=b/2) :
    actual n (q+2) b (by omega) (by omega) <
      actual n q b (by omega) (by omega) - 1 := by
  rw [midexact (by omega) (by omega) (by omega) (by omega),
      leftexact (by omega) (by omega) (by omega) (by omega)]
  have recBound := records_lipschitz q 2 b (by omega)
  have lower := (abs_le.mp recBound).1
  norm_num at lower
  have hnq : 59 ≤ (q:ℝ) := by exact_mod_cast (show 59≤q by omega)
  have bn : 2*(b:ℝ)≤n := by exact_mod_cast (show 2*b≤n by omega)
  have det : middle n (q+2) b - left n q b < -(5/3:ℝ) := by
    rcases (show b=2*q ∨ b=2*q+1 by omega) with he|he
    · have hh : (b:ℝ)=2*q := by exact_mod_cast he
      rw [hh] at bn ⊢
      unfold left middle
      nlinarith
    · have hh : (b:ℝ)=2*q+1 := by exact_mod_cast he
      rw [hh] at bn ⊢
      unfold left middle
      nlinarith
  push_cast
  linarith

/-- At the largest legal b, the rounded table strictly beats every other
positive a below b, including both nonoverlap and overlap. -/
theorem actual_half_winner (n:ℕ) (hn:237≤n) :
    let b := n/2
    let w := winner n b
    ∃ hw:w<n, ∃ hb:b<n, 0<w ∧ w<b ∧
      ∀ a (ha:a<n), 0<a → a<b → a≠w → actual n w b hw hb < actual n a b ha hb := by
  dsimp only
  let b := n/2
  let q := b/2
  let w := winner n b
  obtain ⟨hw,hb,wb,ov⟩ := actual_overlap_winner_from_237 n hn
  have eqb : b=n/2 := rfl
  have eqq : q=b/2 := rfl
  have wp : 0<w := by dsimp [w,b,winner]; omega
  refine ⟨hw,hb,wp,wb,?_⟩
  intro a ha ap ab ne
  by_cases yes : b≤2*a
  · exact ov a ha yes ab ne
  · have down := near_boundary (q:=q) ap ab (show 2*b≤n by omega) (by omega) eqq
    have cross := across_boundary hn eqb eqq
    have first : actual n w b hw hb ≤ actual n (q+2) b (by omega) hb := by
      by_cases eq : q+2=w
      · subst w
        simp only [eq,le_refl]
      · exact (ov (q+2) (by omega) (by omega) (by omega) eq).le
    exact first.trans_lt (cross.trans down)

#print axioms actual_half_winner
end
end Shellsort.TwoGapHalfWinner
