import Shellsort.IndependentGateRenaming

namespace Shellsort.PhysicalSeparatedTemplates
open LocalRelativeOrderMean PhysicalGateRenaming DisjointGateBaseline IndependentGateRenaming
open LocalGatePivotCounts TwoLargeGapPhysicalShapes PhysicalNeighborCorrection Finset
noncomputable section
set_option maxHeartbeats 1500000

private theorem pull {m n} (f g : Fin m → Fin n) (l r : GateTree m)
    (il : Set.InjOn f (sources l)) (ir : Set.InjOn g (sources r))
    (dis : Disjoint (sources l) (sources r)) :
    separate (rename f l) (rename g r) = uniformAverage (fun p : RankPlacement m =>
      if evaluate p.symm r < evaluate p.symm l then (1:ℝ) else 0) :=
  (separate_renaming f g l r il ir).trans ((disjoint_zero l r dis).symm.trans (pair_probability l r).symm)

private def aCol (x y : Bool) := column (small x 0 1) (large y 2 3)
private def bCol (x y : Bool) := column (small x 4 5) (large y 6 7)

private def activeSelf (x y second : Bool) : Finset (Fin 8) := univ.filter fun z =>
    if second then 4 ≤ z.val ∧ (z.val ≠ 5 ∨ x=true) ∧ (z.val ≠ 7 ∨ y=true)
    else z.val < 4 ∧ (z.val ≠ 1 ∨ x=true) ∧ (z.val ≠ 3 ∨ y=true)

private theorem self_small (x y : Bool) :
    sources (aCol x y).1 ⊆ activeSelf x y false ∧
    sources (bCol x y).2 ⊆ activeSelf x y true ∧
    Disjoint (sources (aCol x y).1) (sources (bCol x y).2) := by
  cases x <;> cases y <;> decide

private def selfLabels {n h g : ℕ} (i : Fin n) (ip : i.val+g<n) : Fin 8 → Fin n :=
  let j : Fin n := ⟨i.val+g,ip⟩
  let lo := slotOr i (i.val+h)
  let hi := if h ≤ j.val then slotOr i (j.val-h) else j
  ![i,lo,hi,j,i,lo,hi,j]

private theorem self_inj {n h g : ℕ} (hg : 0<g) (gh : g<h) (half : n ≤ 2*g)
    (i : Fin n) (ip : i.val+g<n) (side : Bool) :
    Set.InjOn (selfLabels (h:=h) i ip) (activeSelf (decide (i.val+h<n)) (decide (h ≤ i.val+g)) side) := by
  have small : i.val+g-h<n := by omega
  intro a ha b hb eq
  have v := congrArg Fin.val eq
  cases side <;> by_cases x : i.val+h<n <;> by_cases y : h ≤ i.val+g <;>
    fin_cases a <;> fin_cases b <;>
    norm_num [activeSelf,x,y] at ha <;> norm_num [activeSelf,x,y] at hb <;>
    norm_num [selfLabels,slotOr,x,y,small] at v <;> first | rfl | omega

theorem self_baseline {n h g : ℕ} (hg : 0<g) (gh : g<h) (half : n ≤ 2*g)
    (i : Fin n) (ip : i.val+g<n) :
    let x := decide (i.val+h<n)
    let y := decide (h ≤ i.val+g)
    separate (depthTwo h g i) (depthTwo h g ⟨i.val+g,ip⟩) = selfMean x y true := by
  let x := decide (i.val+h<n)
  let y := decide (h ≤ i.val+g)
  let f := selfLabels (h:=h) i ip
  have small : i.val+g-h<n := by omega
  obtain ⟨lw,hw⟩ := column_shape gh half i ip
  have shapes : depthTwo h g i = rename f (aCol x y).1 ∧
      depthTwo h g ⟨i.val+g,ip⟩ = rename f (bCol x y).2 := by
    rw [lw,hw]
    by_cases xa : i.val+h<n <;> by_cases ya : h ≤ i.val+g <;>
      simp [x,y,xa,ya,aCol,bCol,column,small,LocalGatePivotCounts.small,
        large,v,rename,f,selfLabels,slotOr,leftInput,rightInput]
  dsimp only
  rw [shapes.1,shapes.2]
  obtain ⟨sl,sr,dis⟩ := self_small x y
  exact pull f f _ _ ((self_inj hg gh half i ip false).mono sl)
    ((self_inj hg gh half i ip true).mono sr) dis

/-- The actual within-column gate correction relative to the separated-source
score appearing in the full physical ledger. -/
theorem charged_self {n h g : ℕ} (hg : 0<g) (gh : g<h) (half : n ≤ 2*g)
    (i : Fin n) (ip : i.val+g<n) :
    let j : Fin n := ⟨i.val+g,ip⟩
    420*(localInversion (depthTwo h g i) (depthTwo h g j) -
      separate (depthTwo h g i) (depthTwo h g j)) =
      (LargeGapCorrectionMultiplicities.samePair (decide (i.val+h<n)) (decide (h ≤ i.val+g)):ℝ) := by
  dsimp only
  rw [self_baseline hg gh half i ip]
  exact PhysicalColumnCorrection.physical_column gh half i ip

#print axioms charged_self
end
end Shellsort.PhysicalSeparatedTemplates
