import Shellsort.ExecutionCornerWinner

namespace Shellsort.TwoGapOverlapWinner
open LargeGapCornerRecords LargeGapRecordChanges LargeGapCornerWinner ThreePassClosedMean ExecutionCornerWinner
noncomputable section
set_option maxHeartbeats 1600000

private theorem step (n a b : ℕ) (hn : 237 ≤ n) (hb : b = n/2)
    (ha : b ≤ 2*a) (hab : a+1 < b) :
    (a < winner n b → score n b (a+1) < score n b a) ∧
    (winner n b ≤ a → score n b a < score n b (a+1)) := by
  let d := b-a-1
  let t := a-(b-a)
  have hd : b-a = d+1 := by dsimp [d]; omega
  have hd' : b-(a+1) = d := by dsimp [d]; omega
  have ht' : a+1-(b-(a+1)) = t+2 := by dsimp [t]; omega
  have recs := record_increment d t
  let gap : ℤ := 92*(a:ℤ)-14*(n:ℤ)-34*(b:ℤ)+142
  have hq : numerator n b (a+1) - numerator n b a = gap := by
    unfold numerator gap
    push_cast
    ring
  have hstep : score n b (a+1) - score n b a =
      (gap:ℝ)-105*(reduced d (t+2)-reduced (d+1) t) := by
    unfold score
    rw [ht', hd']
    change (_:ℝ) - 105*_ - (_ - 105*reduced (b-a) t) = _
    rw [hd, ← hq, Int.cast_sub]; ring
  constructor
  · intro h
    have hg : gap ≤ 0 := by dsimp [gap]; unfold winner at h; omega
    have hg' : (gap:ℝ) ≤ 0 := by exact_mod_cast hg
    linarith [recs.1]
  · intro h
    by_cases hlarge : 5 ≤ d
    · have hg : 1 ≤ gap := by dsimp [gap]; unfold winner at h; omega
      have hg' : (1:ℝ) ≤ gap := by exact_mod_cast hg
      have hd5 : (5:ℝ) ≤ d := by exact_mod_cast hlarge
      have hsmall : 2/(3*((d:ℝ)+1)*(3*((d:ℝ)+1)-1)) < 1/105 := by
        have hn0 : 0 < 3*((d:ℝ)+1)-1 := by linarith
        apply (div_lt_div_iff₀ (by positivity) (by norm_num)).2
        nlinarith [mul_self_le_mul_self (by norm_num : (0:ℝ) ≤ 5) hd5]
      linarith [recs.2]
    · have hg : 106 ≤ gap := by dsimp [gap]; dsimp [d] at hlarge; omega
      have hg' : (106:ℝ) ≤ gap := by exact_mod_cast hg
      have small : 2/(3*((d:ℝ)+1)*(3*((d:ℝ)+1)-1)) ≤ 1 := by
        have hn0 : 0 < 3*((d:ℝ)+1)-1 := by linarith [Nat.cast_nonneg (α := ℝ) d]
        apply (div_le_iff₀ (by positivity)).2
        nlinarith [sq_nonneg (d:ℝ)]
      linarith [recs.2]

theorem score_overlap_winner (n : ℕ) (hn : 237 ≤ n) :
    let b := n/2
    let w := winner n b
    b ≤ 2*w ∧ w < b ∧
      ∀ a, b ≤ 2*a → a < b → a ≠ w → score n b w < score n b a := by
  dsimp only
  let b := n/2
  let w := winner n b
  have hb : b = n/2 := rfl
  have hw : b ≤ 2*w ∧ w < b := by dsimp [w,winner,b]; omega
  refine ⟨hw.1, hw.2, ?_⟩
  intro a ha hab hne
  change score n b w < score n b a
  by_cases hlt : a < w
  · obtain ⟨k,hk⟩ := Nat.exists_eq_add_of_le (Nat.succ_le_of_lt hlt)
    have descend : ∀ (j:ℕ), a+1+j ≤ w → score n b (a+1+j) < score n b a := by
      intro j
      induction j with
      | zero =>
        intro h
        exact (step n a b hn hb ha (by omega)).1 (by omega)
      | succ j ih =>
        intro h
        have last := (step n (a+1+j) b hn hb (by omega) (by omega)).1 (by omega : a+1+j < w)
        exact last.trans (ih (by omega))
    have e : a+1+k = w := by omega
    simpa only [e] using descend k (by omega)
  · have hu : w < a := by change a ≠ w at hne; omega
    obtain ⟨k,hk⟩ := Nat.exists_eq_add_of_le (Nat.succ_le_of_lt hu)
    have ascend : ∀ (j:ℕ), w+1+j < b → score n b w < score n b (w+1+j) := by
      intro j
      induction j with
      | zero =>
        intro h
        exact (step n w b hn hb hw.1 (by omega)).2 (by rfl)
      | succ j ih =>
        intro h
        exact (ih (by omega)).trans
          ((step n (w+1+j) b hn hb (by omega) (by omega)).2 (by change w ≤ _; omega))
    have e : w+1+k = a := by omega
    simpa only [e] using ascend k (by omega)


/-- Scale for the real (extended corner) score. It depends only on n and b. -/
private def offset (n b : ℕ) : ℝ :=
  105*(n:ℝ)^2/4-28*(b:ℝ)*n+30*(b:ℝ)^2+315*(n:ℝ)/4+86*b-105*harmonic n

/-- The second affine correction contributes a nonnegative penalty for 3a < 2b. -/
theorem extended_comparison_score {n a b : ℕ} (hab : a<b) (half : 2*b≤n)
    (overlap : b≤2*a) :
    105 * actual n a b (by omega) (by omega) =
    score n b a + offset n b + 3/2*(↑(2*b-3*a):ℝ) := by
  unfold actual
  rw [executed_closed (show 0<n-b by omega) (show n-b<n-a by omega) (show n-a<n by omega)
    (show n≤2*(n-b) by omega)]
  rw [show n-(n-a)=a by omega,show n-(n-b)=b by omega,show n-a-(n-b)=b-a by omega]
  unfold baseline score numerator offset
  by_cases eq : a=b-a
  · have hb : b = 2*a := by omega
    rw [← eq, hb]
    simp only [lt_self_iff_false,ite_false,le_refl,ite_true,grouped,Nat.sub_self]
    have hh : 2*(2*a)-3*a=a := by omega
    rw [hh]
    push_cast
    ring
  · have reg : b-a<a := by omega
    simp only [reg,ite_true,grouped,not_le.mpr reg,ite_false]
    by_cases edge : a ≤ 2*(b-a)
    · simp only [edge,ite_true]
      have ok : 3*a ≤ 2*b := by omega
      rw [Nat.cast_sub ok]
      push_cast
      ring
    · simp only [edge,ite_false,show 2*b-3*a=0 by omega,Nat.cast_zero]
      push_cast
      ring

theorem rounded_corner (n : ℕ) (hn : 329 ≤ n) :
    2*(n/2) ≤ 3*winner n (n/2) := by
  unfold winner
  by_cases h : 430 ≤ n
  · omega
  · interval_cases n <;> decide

/-- This ranges over every fixed-b overlap competitor, including the middle
affine region. The rounded point need only belong to the corner. -/
theorem actual_overlap_winner_of_corner (n : ℕ) (hn : 237 ≤ n)
    (hc : 2*(n/2) ≤ 3*winner n (n/2)) :
    let b := n/2
    let w := winner n b
    ∃ hw : w<n, ∃ hb : b<n, w<b ∧
      ∀ a (ha : a<n), b≤2*a → a<b → a≠w → actual n w b hw hb < actual n a b ha hb := by
  dsimp only
  obtain ⟨ow,wb,rest⟩ := score_overlap_winner n hn
  have half : 2*(n/2)≤n := by omega
  have ws := extended_comparison_score wb half ow
  rw [Nat.sub_eq_zero_of_le hc, Nat.cast_zero, mul_zero, add_zero] at ws
  refine ⟨by omega,by omega,wb,?_⟩
  intro a ha oa ab neq
  have hs := extended_comparison_score ab half oa
  have hpen : (0:ℝ) ≤ (↑(2*(n/2)-3*a):ℝ) := Nat.cast_nonneg _
  linarith [rest a oa ab neq]

theorem actual_overlap_winner (n : ℕ) (hn : 329 ≤ n) :
    let b := n/2
    let w := winner n b
    ∃ hw : w<n, ∃ hb : b<n, w<b ∧
      ∀ a (ha : a<n), b≤2*a → a<b → a≠w → actual n w b hw hb < actual n a b ha hb :=
  actual_overlap_winner_of_corner n (by omega) (rounded_corner n hn)

#print axioms actual_overlap_winner

/-- At the exceptional rounded points the penalty is exactly 3/2. -/
private theorem rounded_cases (n : ℕ) (hn : 237 ≤ n) :
    let b := n/2
    let w := winner n b
    2*b ≤ 3*w ∨
      (2*b = 3*w+1 ∧ 2+(14*n+34*b) ≤ 92*w+142 ∧ 9 ≤ b-w-1) := by
  dsimp only
  by_cases h : 329 ≤ n
  · exact Or.inl (rounded_corner n h)
  · unfold winner
    interval_cases n <;> decide

private theorem strong_step {n w b : ℕ} (ovr : b≤2*w)
    (hg : 2+(14*n+34*b) ≤ 92*w+142) (far : 9 ≤ b-w-1) :
    score n b w + 3/2 < score n b (w+1) := by
  let d := b-w-1
  let t := w-(b-w)
  have h1 : b-w = d+1 := by dsimp [d]; omega
  have h2 : b-(w+1) = d := by dsimp [d]; omega
  have h3 : w+1-(b-(w+1))=t+2 := by dsimp [t]; omega
  have q : numerator n b (w+1) - numerator n b w =
      92*(w:ℤ)-14*(n:ℤ)-34*(b:ℤ)+142 := by
    unfold numerator
    push_cast
    ring
  have hgI : (2:ℤ) ≤ 92*(w:ℤ)-14*(n:ℤ)-34*(b:ℤ)+142 := by omega
  have hgR : (2:ℝ) ≤ ((numerator n b (w+1) : ℤ):ℝ) - (numerator n b w : ℝ) := by
    exact_mod_cast (q.trans_ge hgI)
  have inc := (record_increment d t).2
  have d9 : (9:ℝ) ≤ d := by exact_mod_cast far
  have tiny : 2 / (3*((d:ℝ)+1)*(3*((d:ℝ)+1)-1)) < 1/210 := by
    have den : 0 < 3*((d:ℝ)+1)-1 := by linarith
    apply (div_lt_div_iff₀ (by positivity) (by norm_num)).2
    nlinarith [mul_self_le_mul_self (by norm_num : (0:ℝ)≤9) d9]
  unfold score
  rw [h3,h2]
  change _ - 105*reduced (b-w) t + _ < _ - 105*reduced d (t+2)
  rw [h1]
  linarith

theorem actual_overlap_winner_from_237 (n : ℕ) (hn : 237 ≤ n) :
    let b := n/2
    let w := winner n b
    ∃ hw : w<n, ∃ hb : b<n, w<b ∧
      ∀ a (ha : a<n), b≤2*a → a<b → a≠w → actual n w b hw hb < actual n a b ha hb := by
  rcases rounded_cases n hn with hc | ⟨bd, hg,far⟩
  · exact actual_overlap_winner_of_corner n hn hc
  dsimp only
  let b := n/2
  let w := winner n b
  change 2*b=3*w+1 at bd
  change 2+(14*n+34*b) ≤ 92*w+142 at hg
  change 9 ≤ b-w-1 at far
  obtain ⟨ow,wb,rest⟩ := score_overlap_winner n hn
  change b≤2*w at ow
  change w<b at wb
  have eqb : b=n/2 := rfl
  have half : 2*b≤n := by omega
  have ws := extended_comparison_score wb half ow
  rw [show 2*b-3*w=1 by omega,Nat.cast_one,mul_one] at ws
  refine ⟨by change w<n; omega, by change b<n; omega, wb, ?_⟩
  intro a ha oa ab neq
  change b≤2*a at oa
  change a<b at ab
  change a≠w at neq
  have hs := extended_comparison_score ab half oa
  by_cases low : a<w
  · have smaller := rest a oa ab neq
    change score n b w < score n b a at smaller
    have hp : (1:ℝ) ≤ (↑(2*b-3*a):ℝ) := by
      exact_mod_cast (show 1≤2*b-3*a by omega)
    change actual n w b _ _ < actual n a b _ _
    linarith
  · have edge := strong_step ow hg far
    have above : w+1 ≤ a := by omega
    obtain ⟨k,hk⟩ := Nat.exists_eq_add_of_le above
    have inc : ∀ (j:ℕ), w+1+j < b → score n b (w+1) ≤ score n b (w+1+j) := by
      intro j
      induction j with
      | zero => simp
      | succ j ih =>
        intro hj
        have next := (step n (w+1+j) b hn eqb (by omega) (by omega)).2
          (by change w≤w+1+j; omega)
        exact (ih (by omega)).trans (le_of_lt next)
    have e : w+1+k=a := by omega
    have bounded : score n b (w+1) ≤ score n b a := e ▸ inc k (by omega)
    have hpn : (0:ℝ) ≤ ↑(2*b-3*a) := Nat.cast_nonneg _
    change actual n w b _ _ < actual n a b _ _
    linarith

#print axioms actual_overlap_winner_from_237

end
end Shellsort.TwoGapOverlapWinner
