import Shellsort.TwoGapHalfWinner

namespace Shellsort.TwoGapInterior
open LargeGapCornerRecords LargeGapRecordChanges LargeGapCornerWinner ThreePassClosedMean
open ExecutionCornerWinner TwoGapOverlapWinner TwoGapHalfWinner
noncomputable section

private def R (a b : ℕ) : ℝ := grouped a (b-a)
private def left (n a b : ℝ) : ℝ :=
  a+b+n+n^2/4-b*n/3+2*a^2/5-2*a*b/5+b^2/3-n/4-a/10-b/6
private def right (n a b : ℝ) : ℝ :=
  a+b+n+n^2/4-2*a*n/15-4*b*n/15+
  (46*a^2-34*a*b+30*b^2)/105-n/4-3*a/35-19*b/105

private theorem left_eq {n a b : ℕ} (ap:0<a) (ab:a<b) (half:2*b≤n) (dis:2*a≤b) :
    actual n a b (by omega) (by omega) = left n a b-harmonic n-R a b := by
  unfold actual
  rw [executed_closed (show 0<n-b by omega) (show n-b<n-a by omega) (show n-a<n by omega)
    (show n≤2*(n-b) by omega), show n-(n-a)=a by omega, show n-(n-b)=b by omega,
    show n-a-(n-b)=b-a by omega]
  simp only [baseline,ite_eq_right (show ¬b-a<a by omega), ite_eq_left (show a≤b-a by omega)]
  unfold left R
  push_cast
  ring

private theorem right_eq {n a b : ℕ} (ab:a<b) (half:2*b≤n) (ov:b≤2*a) :
    actual n a b (by omega) (by omega) =
      right n a b-harmonic n-R a b+(↑(2*b-3*a):ℝ)/70 := by
  unfold actual
  rw [executed_closed (show 0<n-b by omega) (show n-b<n-a by omega) (show n-a<n by omega)
    (show n≤2*(n-b) by omega), show n-(n-a)=a by omega, show n-(n-b)=b by omega,
    show n-a-(n-b)=b-a by omega]
  unfold right R baseline
  by_cases eq : b=2*a
  · subst b
    simp only [ite_eq_right (show ¬2*a-a<a by omega), ite_eq_left (show a≤2*a-a by omega),
      show 2*(2*a)-3*a=a by omega]
    push_cast
    ring
  · simp only [ite_eq_left (show b-a<a by omega),ite_eq_right (show ¬a≤b-a by omega)]
    by_cases mid : a≤2*(b-a)
    · simp only [ite_eq_left mid, Nat.cast_sub (show 3*a≤2*b by omega)]
      push_cast
      ring
    · simp only [ite_eq_right mid,show 2*b-3*a=0 by omega,Nat.cast_zero]
      push_cast
      ring

/-- If the next vertical step remains in the overlap range, its reduction
in the quadratic cost dominates both finite corrections. -/
theorem overlap_descent {n a b : ℕ} (hn:237≤n) (ab:a<b) (cap:b<n/2) (ov:b+1≤2*a) :
    actual n a (b+1) (by omega) (by omega) < actual n a b (by omega) (by omega) := by
  have recordBound := (neighboring a b ab).2.1
  change -(5/6:ℝ) ≤ R a (b+1)-R a b at recordBound
  have bound : 2*(b+1)-3*a ≤ (2*b-3*a)+2 := by omega
  have penalty : (↑(2*(b+1)-3*a):ℝ) ≤ (↑(2*b-3*a):ℝ)+2 := by exact_mod_cast bound
  have n' : (237:ℝ)≤n := by exact_mod_cast hn
  have c' : 2*(b:ℝ)+2≤n := by exact_mod_cast (show 2*b+2≤n by omega)
  have o' : (b:ℝ)+1≤2*a := by exact_mod_cast ov
  rw [right_eq (by omega) (by omega) ov, right_eq ab (by omega) (by omega)]
  have diff : right n a ((b:ℝ)+1)-right n a b =
      (-28*(n:ℝ)-34*a+60*b+116)/105 := by unfold right; ring
  push_cast
  linarith

/-- On the other side, a vertical step improves unless a is tiny and b is large. -/
theorem separated_vertical {n a b : ℕ} (hn:237≤n) (ap:0<a) (ab:a<b) (cap:b<n/2)
    (dis:2*a≤b) (safe:4≤a ∨ b<12) :
    actual n a (b+1) (by omega) (by omega) < actual n a b (by omega) (by omega) := by
  have recordBound := (neighboring a b ab).2.1
  change -(5/6:ℝ) ≤ R a (b+1)-R a b at recordBound
  have n' : (237:ℝ)≤n := by exact_mod_cast hn
  have c' : 2*(b:ℝ)+2≤n := by exact_mod_cast (show 2*b+2≤n by omega)
  have pos : 0<(a:ℝ) := by exact_mod_cast ap
  rw [left_eq ap (by omega) (by omega) (by omega), left_eq ap ab (by omega) dis]
  have diff : left n a ((b:ℝ)+1)-left n a b =
      (2*(b:ℝ)+1-n)/3-2*a/5+5/6 := by unfold left; ring
  push_cast
  rcases safe with ha | hb
  · have a' : (4:ℝ)≤a := by exact_mod_cast ha
    linarith
  · have b' : (b:ℝ)<12 := by exact_mod_cast hb
    linarith

theorem separated_horizontal {n a b : ℕ} (ap:0<a) (small:a<4) (large:12≤b) (cap:2*b≤n) :
    actual n (a+1) b (by omega) (by omega) < actual n a b (by omega) (by omega) := by
  have recordBound := (abs_le.mp (neighboring a b (by omega)).1).1
  change -(1/3:ℝ) ≤ R (a+1) b-R a b at recordBound
  have a' : (a:ℝ)<4 := by exact_mod_cast small
  have b' : (12:ℝ)≤b := by exact_mod_cast large
  rw [left_eq (by omega) (by omega) cap (by omega),left_eq ap (by omega) cap (by omega)]
  have diff : left n ((a:ℝ)+1) b-left n a b =
      4*(a:ℝ)/5-2*b/5+13/10 := by unfold left; ring
  push_cast
  have a3 : (a:ℝ)≤3 := by exact_mod_cast (show a≤3 by omega)
  linarith

/-- Every off-boundary point admits a strictly cheaper legal neighbor.
The first branch increases the second pair count, the other the first. -/
theorem improving_neighbor {n a b : ℕ} (hn:237≤n) (ap:0<a) (ab:a<b) (cap:b<n/2) :
    actual n a (b+1) (by omega) (by omega) < actual n a b (by omega) (by omega)
    ∨ (a+1<b ∧ actual n (a+1) b (by omega) (by omega) < actual n a b (by omega) (by omega)) := by
  by_cases ov : b+1≤2*a
  · exact Or.inl (overlap_descent hn ab cap ov)
  by_cases safe : 4≤a ∨ b<12
  · exact Or.inl (separated_vertical hn ap ab cap (by omega) safe)
  exact Or.inr ⟨by omega,separated_horizontal ap (by omega) (by omega) (by omega)⟩

/-- A strictly improving walk from any interior point eventually reaches b=floor(n/2). -/
private theorem walk {n : ℕ} (hn : 237≤n) (a b:ℕ) (ap:0<a) (ab:a<b) (cap:b<n/2) :
    ∃ x, ∃ hx : x<n, 0<x ∧ x<n/2 ∧
      actual n x (n/2) hx (by omega) < actual n a b (by omega) (by omega) := by
  rcases improving_neighbor hn ap ab cap with v | ⟨next,h⟩
  · by_cases reached : b+1=n/2
    · exact ⟨a,by omega,ap,by omega,by simpa [← reached] using v⟩
    obtain ⟨x,hx,xp,xb,better⟩ := walk hn a (b+1) ap (by omega) (by omega)
    exact ⟨x,hx,xp,xb,better.trans v⟩
  · obtain ⟨x,hx,xp,xb,better⟩ := walk hn (a+1) b (by omega) next cap
    exact ⟨x,hx,xp,xb,better.trans h⟩
termination_by 2*n-(a+b)
decreasing_by all_goals omega

/-- Unique optimum over the complete two-large-gap class.
The actual positive gaps are n-a and n-b. -/
theorem actual_large_gap_winner (n:ℕ) (hn:237≤n) :
    let B := n/2
    let w := winner n B
    ∃ hw:w<n, ∃ hB:B<n, 0<w ∧ w<B ∧
      ∀ a b (ha:a<n) (hb:b<n), 0<a → a<b → 2*b≤n → (a≠w ∨ b≠B) →
        actual n w B hw hB < actual n a b ha hb := by
  dsimp only
  obtain ⟨hw,hB,wp,wB,atBound⟩ := actual_half_winner n hn
  refine ⟨hw,hB,wp,wB,?_⟩
  intro a b ha hb ap ab cap neq
  by_cases same : b=n/2
  · subst b
    exact atBound a ha ap ab (by simpa using neq)
  obtain ⟨x,hx,xp,xb,improved⟩ := walk hn a b ap ab (by omega)
  by_cases equal : x=winner n (n/2)
  · subst x; exact improved
  exact ((atBound x hx xp xb equal).trans improved)

private theorem increasing (d t : ℕ) : 0 < reduced d (t+2) - reduced (d+1) t := (record_increment d t).1

private theorem compare_offsets {x y s t c u v : ℝ}
    (hx : 105*x=s+c+u) (hy : 105*y=t+c+v) (diff : s+u<t+v) : x<y := by linarith

attribute [local irreducible] actual reduced harmonic score

set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
/-- At n=236 the proposed a is 78 and the legal neighbor 79 is strictly
cheaper, showing that the uniform onset 237 cannot be lowered. -/
theorem counterexample_236 :
    winner 236 (236/2) = 78 ∧
    actual 236 79 118 (by decide) (by decide) < actual 236 78 118 (by decide) (by decide) := by
  refine ⟨by norm_num [winner],?_⟩
  have leftSide := extended_comparison_score (n:=236) (a:=78) (b:=118) (by decide) (by decide) (by decide)
  have rightSide := extended_comparison_score (n:=236) (a:=79) (b:=118) (by decide) (by decide) (by decide)
  have inc : 0 < reduced 39 40 - reduced 40 38 := increasing 39 38
  refine compare_offsets rightSide leftSide ?_

  unfold score
  norm_num [numerator]
  
  linarith only [inc]

#print axioms counterexample_236
#print axioms actual_large_gap_winner
end
end Shellsort.TwoGapInterior
