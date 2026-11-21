import Shellsort.PhysicalSeparatedTemplates
import Shellsort.ThreePassSeparatedLedger

namespace Shellsort.PhysicalSeparatedEdges
open LocalRelativeOrderMean PhysicalGateRenaming DisjointGateBaseline IndependentGateRenaming
open LocalGatePivotCounts TwoLargeGapPhysicalShapes PhysicalNeighborCorrection Finset
noncomputable section
set_option maxHeartbeats 1500000

private def freshColumn (y : Bool) := column (small y 4 5) (.high (v 6) (v 7))
private def srcA (x : Bool) : Finset (Fin 8) :=
  univ.filter fun z => z.val < 3 ∨ (z.val=3 ∧ x=true)
private def srcB (y : Bool) : Finset (Fin 8) :=
  univ.filter fun z => 4 ≤ z.val ∧ (z.val≠5 ∨ y=true)

private theorem source_info (x y : Bool) :
    sources (mainColumn x).1 ⊆ srcA x ∧ sources (mainColumn x).2 ⊆ srcA x ∧
    sources (freshColumn y).1 ⊆ srcB y ∧ sources (freshColumn y).2 ⊆ srcB y ∧
    Disjoint (srcA x) (srcB y) := by
  cases x <;> cases y <;> decide

private def labeling {n h g : ℕ} (i j : Fin n) (ip : i.val+g<n) (jp : j.val+g<n) : Fin 8 → Fin n :=
  let r : Fin n := ⟨i.val+g,ip⟩
  let s : Fin n := ⟨j.val+g,jp⟩
  ![i,s,if h ≤ r.val then slotOr i (r.val-h) else r,r,j,slotOr j (j.val+h),i,s]

private theorem injects {n h g : ℕ} (gh : g<h) (half : n ≤ 2*g)
    (i j : Fin n) (ip : i.val+g<n) (jp : j.val+g<n) (sh : j.val+g=i.val+h) :
    Set.InjOn (labeling (h:=h) i j ip jp) (srcA (decide (h ≤ i.val+g))) ∧
    Set.InjOn (labeling (h:=h) i j ip jp) (srcB (decide (j.val+h<n))) := by
  have tiny : i.val+g-h<n := by omega
  constructor <;> intro a ha b hb eq <;> have v := congrArg Fin.val eq <;>
    by_cases x : h ≤ i.val+g <;> by_cases y : j.val+h<n <;>
    fin_cases a <;> fin_cases b <;>
    norm_num [srcA,srcB,x,y] at ha <;> norm_num [srcA,srcB,x,y] at hb <;>
    norm_num [labeling,slotOr,x,y,tiny] at v <;> first | rfl | omega

def edgeBaseline {n h g : ℕ} (i j : Fin n) (ip : i.val+g<n) (jp : j.val+g<n) : ℝ :=
  let a := depthTwo h g i
  let b := depthTwo h g ⟨i.val+g,ip⟩
  let c := depthTwo h g j
  let d := depthTwo h g ⟨j.val+g,jp⟩
  separate a c + separate a d + separate c b + separate b d

theorem edge_baseline {n h g : ℕ} (gh : g<h) (half : n ≤ 2*g)
    (i j : Fin n) (ip : i.val+g<n) (jp : j.val+g<n) (sh : j.val+g=i.val+h) :
    let x := decide (h ≤ i.val+g)
    let y := decide (j.val+h<n)
    edgeBaseline (h:=h) i j ip jp = edgeMean x y true := by
  let x := decide (h ≤ i.val+g)
  let y := decide (j.val+h<n)
  let f := labeling (h:=h) i j ip jp
  let A := mainColumn x
  let B := freshColumn y
  have small : i.val+g-h<n := by omega
  have shapes : depthTwo h g i = rename f A.1 ∧ depthTwo h g ⟨i.val+g,ip⟩ = rename f A.2 ∧
      depthTwo h g j = rename f B.1 ∧ depthTwo h g ⟨j.val+g,jp⟩ = rename f B.2 := by
    obtain ⟨a,b⟩ := column_shape gh half i ip
    obtain ⟨c,d⟩ := column_shape gh half j jp
    obtain ⟨l,r,_⟩ := neighboring_shapes i j ip jp sh
    rw [a,b,c,d,l,r]
    by_cases xa : h ≤ i.val+g <;> by_cases ya : j.val+h<n <;>
      simp [A,B,x,y,xa,ya,mainColumn,freshColumn,column,LocalGatePivotCounts.small,
        large,v,f,labeling,rename,leftInput,rightInput,slotOr,small]
  obtain ⟨a,b,c,d⟩ := shapes
  obtain ⟨l,m,r,s,dis⟩ := source_info x y
  obtain ⟨il,ir⟩ := injects gh half i j ip jp sh
  have lift (u w : T) (iu : Set.InjOn f (sources u)) (iw : Set.InjOn f (sources w))
      (dw : Disjoint (sources u) (sources w)) : separate (rename f u) (rename f w) =
        uniformAverage (fun p : RankPlacement 8 => if evaluate p.symm w < evaluate p.symm u
          then (1:ℝ) else 0) :=
    (separate_renaming f f u w iu iw).trans ((disjoint_zero u w dw).symm.trans (pair_probability u w).symm)
  dsimp only [edgeBaseline]; rw [a,b,c,d]
  rw [lift A.1 B.1 (il.mono l) (ir.mono r) (dis.mono l r),
      lift A.1 B.2 (il.mono l) (ir.mono s) (dis.mono l s),
      lift B.1 A.2 (ir.mono r) (il.mono m) (dis.symm.mono r m),
      lift A.2 B.2 (il.mono m) (ir.mono s) (dis.mono m s)]
  rfl

theorem charged_edge {n h g : ℕ} (gh : g<h) (half : n ≤ 2*g)
    (i j : Fin n) (ip : i.val+g<n) (jp : j.val+g<n) (shared : j.val+g=i.val+h) :
    420*(actualEdge (h:=h) i j ip jp - edgeBaseline (h:=h) i j ip jp) =
      (LargeGapCorrectionMultiplicities.neighbor (decide (h ≤ i.val+g)) (decide (j.val+h<n)):ℝ) := by
  rw [edge_baseline gh half i j ip jp shared]
  exact actual_neighbor_correction gh half i j ip jp shared

#print axioms charged_edge
end
end Shellsort.PhysicalSeparatedEdges
