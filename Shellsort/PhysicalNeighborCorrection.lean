import Shellsort.PhysicalGateRenaming
import Shellsort.TwoLargeGapPhysicalShapes
import Mathlib.Data.Fin.VecNotation

namespace Shellsort.PhysicalNeighborCorrection
open LocalRelativeOrderMean LocalGatePivotCounts PhysicalGateRenaming TwoLargeGapPhysicalShapes
open Finset
noncomputable section
set_option maxHeartbeats 1500000

def mainColumn (x : Bool) : T × T := column (.low (v 0) (v 1)) (large x 2 3)
def nextColumn (y : Bool) : T × T := column (small y 4 5) (.high (v 0) (v 1))
def active (x y : Bool) : Finset (Fin 8) := univ.filter fun z =>
  z.val ≤ 5 ∧ (z.val ≠ 3 ∨ x=true) ∧ (z.val ≠ 5 ∨ y=true)

private theorem templates_supported (x y : Bool) :
    (sources (mainColumn x).1 ⊆ active x y) ∧
    (sources (mainColumn x).2 ⊆ active x y) ∧
    (sources (nextColumn y).1 ⊆ active x y) ∧
    (sources (nextColumn y).2 ⊆ active x y) := by
  cases x <;> cases y <;> decide

def slotOr {n} (fallback : Fin n) (t : ℕ) : Fin n :=
  if ht : t<n then ⟨t,ht⟩ else fallback

/-- Entries 3 and 5 are additional sources only when their respective flags
are set. Entries 6 and 7 are unused in the true, shared-source pattern. -/
def labels {n h g : ℕ} (i j : Fin n) (ip : i.val+g<n) (jp : j.val+g<n) :
    Fin 8 → Fin n :=
  ![i,⟨j.val+g,jp⟩,if h ≤ i.val+g then slotOr i (i.val+g-h) else ⟨i.val+g,ip⟩,
    ⟨i.val+g,ip⟩,j,slotOr j (j.val+h),i,i]

private theorem labels_injective {n h g : ℕ} (gh : g<h) (half : n ≤ 2*g)
    (i j : Fin n) (ip : i.val+g<n) (jp : j.val+g<n) (shared : j.val+g=i.val+h) :
    Set.InjOn (labels (h := h) i j ip jp)
      (↑(active (decide (h ≤ i.val+g)) (decide (j.val+h<n))) : Set (Fin 8)) := by
  have low : i.val+g-h<n := by omega
  intro a ha b hb eq
  have eqv := congrArg Fin.val eq
  by_cases x : h ≤ i.val+g <;> by_cases y : j.val+h<n <;>
    fin_cases a <;> fin_cases b <;>
    norm_num [active,x,y] at ha <;> norm_num [active,x,y] at hb <;>
    norm_num [labels,slotOr,x,y,low] at eqv <;> first | rfl | omega

private theorem gates_match {n h g : ℕ} (gh : g<h) (half : n ≤ 2*g)
    (i j : Fin n) (ip : i.val+g<n) (jp : j.val+g<n) (shared : j.val+g=i.val+h) :
    let x := decide (h ≤ i.val+g)
    let y := decide (j.val+h<n)
    let f := labels (h:=h) i j ip jp
    depthTwo h g i = rename f (mainColumn x).1 ∧
    depthTwo h g ⟨i.val+g,ip⟩ = rename f (mainColumn x).2 ∧
    depthTwo h g j = rename f (nextColumn y).1 ∧
    depthTwo h g ⟨j.val+g,jp⟩ = rename f (nextColumn y).2 := by
  obtain ⟨a,b⟩ := column_shape gh half i ip
  obtain ⟨c,d⟩ := column_shape gh half j jp
  obtain ⟨s,t,_⟩ := neighboring_shapes i j ip jp shared
  have low : i.val+g-h<n := by omega
  dsimp only at a b c d s t ⊢
  rw [a,b,c,d,s,t]
  by_cases x : h ≤ i.val+g <;> by_cases y : j.val+h<n <;>
    simp [mainColumn,nextColumn,column,small,large,v,labels,slotOr,rename,rightInput,leftInput,x,y,low]

def actualEdge {n h g : ℕ} (i j : Fin n) (ip : i.val+g<n) (jp : j.val+g<n) : ℝ :=
  let a := depthTwo h g i
  let b := depthTwo h g ⟨i.val+g,ip⟩
  let c := depthTwo h g j
  let d := depthTwo h g ⟨j.val+g,jp⟩
  localInversion a c + localInversion a d + localInversion c b + localInversion b d

theorem actual_neighbor_correction {n h g : ℕ} (gh : g<h) (half : n ≤ 2*g)
    (i j : Fin n) (ip : i.val+g<n) (jp : j.val+g<n) (shared : j.val+g=i.val+h) :
    let x := decide (h ≤ i.val+g)
    let y := decide (j.val+h<n)
    420*(actualEdge (h:=h) i j ip jp - edgeMean x y true) =
      (LargeGapCorrectionMultiplicities.neighbor x y : ℝ) := by
  let x := decide (h ≤ i.val+g)
  let y := decide (j.val+h<n)
  let f := labels (h:=h) i j ip jp
  obtain ⟨a,b,c,d⟩ := gates_match gh half i j ip jp shared
  obtain ⟨s,t,u,v'⟩ := templates_supported x y
  have inj := labels_injective gh half i j ip jp shared
  have lift (l r : T) (lsub : sources l ⊆ active x y) (rsub : sources r ⊆ active x y) :
      localInversion (rename f l) (rename f r) =
      uniformAverage (fun p : RankPlacement 8 => if evaluate p.symm r < evaluate p.symm l
        then (1:ℝ) else 0) := by
    rw [pair_probability]
    exact rename_inversion f l r (inj.mono (Finset.union_subset lsub rsub))
  have value : actualEdge (h:=h) i j ip jp = edgeMean x y false := by
    unfold actualEdge
    rw [a,b,c,d]
    change localInversion (rename f _) (rename f _) + localInversion (rename f _) (rename f _) +
      localInversion (rename f _) (rename f _) + localInversion (rename f _) (rename f _) = _
    rw [lift _ _ s u,lift _ _ s v',lift _ _ u t,lift _ _ t v']
    rfl
  dsimp only
  rw [value]
  exact (eight_corrections x y).2

#print axioms actual_neighbor_correction
end
end Shellsort.PhysicalNeighborCorrection
