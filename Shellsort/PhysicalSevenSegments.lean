import Shellsort.SevenSegmentBaseline
import Shellsort.ThreePassPhysicalCorrection

namespace Shellsort.PhysicalSevenSegments
open SevenSegmentBaseline LocalGatePivotCounts LocalRelativeOrderMean PhysicalGateRenaming
open TwoLargeGapPhysicalShapes IndependentGateRenaming DisjointGateBaseline PhysicalNeighborCorrection
open ThreePassSeparatedLedger Finset
noncomputable section
set_option maxHeartbeats 2000000

def tag (x y high : Bool) : Fin 7 :=
  if x == y then (if high then 5 else 1)
  else if x then (if high then 4 else 0) else (if high then 6 else 2)

def region (n h g i : ℕ) : Fin 7 :=
  if i<n-g then tag (decide (i<n-h)) (decide (h-g ≤ i)) false
  else if i<g then 3
  else tag (decide (i-g<n-h)) (decide (h-g ≤ i-g)) true

private def gate (x y side high : Bool) : T :=
  let c := if side then column (small x 4 5) (large y 6 7)
    else column (small x 0 1) (large y 2 3)
  if high then c.2 else c.1

private theorem canonical (o x y side high : Bool) (compat : x=y → x=o) :
    tree o side (tag x y high) = gate x y side high := by
  cases o <;> cases x <;> cases y <;> cases side <;> cases high <;> first | rfl | simp at compat

private def labels {n h g : ℕ} (i : Fin n) (ip : i.val+g<n) : Fin 8 → Fin n :=
  let j : Fin n := ⟨i.val+g,ip⟩
  let lo := slotOr i (i.val+h)
  let hi := if h ≤ j.val then slotOr i (j.val-h) else j
  ![i,lo,hi,j,i,lo,hi,j]

private def active (x y side : Bool) : Finset (Fin 8) := univ.filter fun z =>
  if side then 4 ≤ z.val ∧ (z.val ≠ 5 ∨ x=true) ∧ (z.val ≠ 7 ∨ y=true)
  else z.val < 4 ∧ (z.val ≠ 1 ∨ x=true) ∧ (z.val ≠ 3 ∨ y=true)

private theorem gate_support (x y side high : Bool) :
    sources (gate x y side high) ⊆ active x y side := by
  cases x <;> cases y <;> cases side <;> cases high <;> decide

private theorem labels_inj {n h g : ℕ} (hg : 0<g) (gh : g<h) (half : n ≤ 2*g)
    (i : Fin n) (ip : i.val+g<n) (side : Bool) :
    Set.InjOn (labels (h:=h) i ip) (active (decide (i.val+h<n)) (decide (h ≤ i.val+g)) side) := by
  have sm : i.val+g-h<n := by omega
  intro a ha b hb eq
  have v := congrArg Fin.val eq
  cases side <;> by_cases x : i.val+h<n <;> by_cases y : h ≤ i.val+g <;>
    fin_cases a <;> fin_cases b <;>
    norm_num [active,x,y] at ha <;> norm_num [active,x,y] at hb <;>
    norm_num [labels,slotOr,x,y,sm] at v <;> first | rfl | omega

private theorem column {n h g : ℕ} (hg : 0<g) (gh : g<h) (hn : h<n) (half : n ≤ 2*g)
    (i : Fin n) (ip : i.val+g<n) (side high : Bool) :
    let j : Fin n := ⟨i.val+g,ip⟩
    let t := tree (decide (h-g<n-h)) side (tag (decide (i.val<n-h)) (decide (h-g ≤ i.val)) high)
    depthTwo h g (if high then j else i) = rename (labels (h:=h) i ip) t ∧
      Set.InjOn (labels (h:=h) i ip) (sources t) := by
  dsimp only
  have x : (i.val<n-h) ↔ i.val+h<n := by omega
  have y : (h-g ≤ i.val) ↔ h ≤ i.val+g := by omega
  simp only [x,y]
  have compat : decide (i.val+h<n) = decide (h ≤ i.val+g) →
      decide (i.val+h<n) = decide (h-g<n-h) := by
    by_cases l : i.val+h<n <;> by_cases r : h ≤ i.val+g <;> by_cases o : h-g<n-h <;>
      simp [l,r,o] <;> omega
  rw [canonical _ _ _ _ _ compat]
  refine ⟨?_,(labels_inj hg gh half i ip side).mono (gate_support _ _ _ _)⟩
  have sm : i.val+g-h<n := by omega
  obtain ⟨lo,hi⟩ := column_shape gh half i ip
  cases high <;> cases side <;> by_cases a : i.val+h<n <;> by_cases b : h ≤ i.val+g <;>
    simp [lo,hi,gate,LocalGatePivotCounts.column,large,small,v,rename,labels,slotOr,
      leftInput,rightInput,a,b,sm]

private theorem represents {n h g : ℕ} (hg : 0<g) (gh : g<h) (hn : h<n) (half : n ≤ 2*g)
    (i : Fin n) (side : Bool) :
    let t := tree (decide (h-g<n-h)) side (region n h g i.val)
    ∃ f : Fin 8 → Fin n, depthTwo h g i = rename f t ∧ Set.InjOn f (sources t) := by
  dsimp only
  by_cases low : i.val<n-g
  · have ip : i.val+g<n := by omega
    rw [region,if_pos low]
    exact ⟨labels i ip,column hg gh hn half i ip side false⟩
  by_cases mid : i.val<g
  · rw [region,if_neg low,if_pos mid]
    refine ⟨fun _ => i,?_,?_⟩
    · have a : ¬i.val+g<n := by omega
      have b : ¬i.val+h<n := by omega
      have c : ¬g ≤ i.val := by omega
      have d : ¬h ≤ i.val := by omega
      cases side <;> simp [depthTwo,passTree,a,b,c,d,tree,rename]
    · cases side <;> simp [tree,sources,Set.InjOn]
  · let j : Fin n := ⟨i.val-g,by have := i.isLt; omega⟩
    have fit : j.val+g<n := by dsimp [j]; have := i.isLt; omega
    have eq : (⟨j.val+g,fit⟩ : Fin n) = i := Fin.ext (by dsimp [j]; omega)
    rw [region,if_neg low,if_neg mid]
    refine ⟨labels (h:=h) j fit,?_⟩
    simpa only [Bool.true_eq,ite_true,eq] using column hg gh hn half j fit side true

private theorem apart (o : Bool) (i j : Fin 7) :
    Disjoint (sources (tree o false i)) (sources (tree o true j)) := by
  cases o <;> fin_cases i <;> fin_cases j <;> decide

/-- Every physical pair, including those sharing a source, has the indicated
exact separated baseline. No independence of the two true outputs is assumed. -/
theorem pair_table {n h g : ℕ} (hg : 0<g) (gh : g<h) (hn : h<n) (half : n ≤ 2*g)
    (i j : Fin n) : separatePair n h g (i,j) =
      (table (decide (h-g<n-h)) (region n h g i.val) (region n h g j.val):ℝ)/420 := by
  obtain ⟨f,a,b⟩ := represents hg gh hn half i false
  obtain ⟨t,c,d⟩ := represents hg gh hn half j true
  unfold separatePair
  dsimp only
  rw [a,c,separate_renaming f t _ _ b d,← disjoint_zero _ _ (apart _ _ _),← pair_probability]
  exact prob_table _ _ _

#print axioms pair_table
end
end Shellsort.PhysicalSevenSegments
