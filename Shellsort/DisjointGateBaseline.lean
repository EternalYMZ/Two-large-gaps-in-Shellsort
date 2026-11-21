import Shellsort.PhysicalColumnCorrection

namespace Shellsort.DisjointGateBaseline
open LocalRelativeOrderMean LocalGatePivotCounts PhysicalGateRenaming
open TwoLargeGapPhysicalShapes Finset
noncomputable section

/-- Separate the two gate trees onto disjoint physical source labels. -/
def separate {n : ℕ} (l r : GateTree n) : ℝ :=
  localInversion (rename (Fin.castAdd n) l) (rename (Fin.natAdd n) r)

private theorem rename_comp {a b c} (f : Fin a → Fin b) (g : Fin b → Fin c) (t : GateTree a) :
    rename g (rename f t) = rename (g ∘ f) t := by
  induction t <;> simp_all [rename,Function.comp_apply]

private theorem rename_id {a} (t : GateTree a) : rename id t = t := by
  induction t <;> simp_all [rename]

/-- Disjoint original-slot supports contribute exactly zero dependence
correction, irrespective of n or the shapes of the two monotone trees. -/
theorem disjoint_zero {n} (l r : GateTree n) (apart : Disjoint (sources l) (sources r)) :
    localInversion l r = separate l r := by
  let f : Fin (n+n) → Fin n := Fin.addCases id id
  let a := rename (Fin.castAdd n) l
  let b := rename (Fin.natAdd n) r
  have inj : Set.InjOn f (↑(sources a ∪ sources b) : Set (Fin (n+n))) := by
    intro i hi j hj eq
    simp only [a,b,sources_rename,coe_union,coe_image,Set.mem_union,Set.mem_image] at hi hj
    rcases hi with ⟨x,hx,rfl⟩|⟨x,hx,rfl⟩ <;>
      rcases hj with ⟨y,hy,rfl⟩|⟨y,hy,rfl⟩ <;>
      simp only [f,Fin.addCases_left,Fin.addCases_right,id_eq] at eq <;> subst y
    · rfl
    · exact (disjoint_left.mp apart hx hy).elim
    · exact (disjoint_left.mp apart hy hx).elim
    · rfl
  have lift := rename_inversion f a b inj
  have left : f ∘ Fin.castAdd n = id := by funext; simp only [Function.comp_apply,f,Fin.addCases_left,Fin.addCases_right,id_eq]
  have right : f ∘ Fin.natAdd n = id := by funext; simp only [Function.comp_apply,f,Fin.addCases_left,Fin.addCases_right,id_eq]
  simpa only [a,b,separate,rename_comp,left,right,rename_id] using lift

private theorem middle_single {n h g : ℕ} (gh : g<h) (i : Fin n)
    (lo : n ≤ i.val+g) (hi : i.val<g) : depthTwo h g i = .leaf i := by
  have stop : ¬ (i.val+h<n) := by omega
  simp [depthTwo,passTree,stop,Nat.not_lt.mpr lo,not_le.mpr hi,
    show ¬(h ≤ i.val) by omega]

/-- Middle singleton slots have no shared source with any other output. -/
theorem isolated_source {n h g : ℕ} (hg : 0 < g) (gh : g<h) (half : n ≤ 2*g)
    (i z : Fin n) (lo : n ≤ i.val+g) (hi : i.val<g) (different : i≠z) :
    Disjoint (sources (depthTwo h g i)) (sources (depthTwo h g z)) := by
  rw [middle_single gh i lo hi]
  change Disjoint {i} (sources (depthTwo h g z))
  rw [disjoint_singleton_left]
  have Gi : ¬(g ≤ i.val) := by omega
  have Hi : ¬(h ≤ i.val) := by omega
  intro mem
  unfold depthTwo passTree at mem
  repeat' split at mem
  all_goals
    simp only [sources,mem_union,mem_singleton,Fin.ext_iff] at mem
    have iz : i.val ≠ z.val := fun e => different (Fin.ext e)
    have il := i.isLt
    have zl := z.isLt
    try dsimp only at *
    omega

theorem isolated_zero {n h g : ℕ} (hg : 0 < g) (gh : g<h) (half : n ≤ 2*g)
    (i z : Fin n) (lo : n ≤ i.val+g) (hi : i.val<g) (different : i≠z) :
    localInversion (depthTwo h g i) (depthTwo h g z) =
      separate (depthTwo h g i) (depthTwo h g z) :=
  disjoint_zero _ _ (isolated_source hg gh half i z lo hi different)

#print axioms isolated_zero
end
end Shellsort.DisjointGateBaseline
