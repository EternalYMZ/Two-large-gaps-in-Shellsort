import Shellsort.DisjointGateBaseline

namespace Shellsort.IndependentGateRenaming
open LocalRelativeOrderMean PhysicalGateRenaming DisjointGateBaseline Finset
noncomputable section

private theorem comp {a b c} (f : Fin a → Fin b) (g : Fin b → Fin c) (t : GateTree a) :
    rename g (rename f t) = rename (g ∘ f) t := by
  induction t <;> simp_all [rename,Function.comp_apply]

/-- The independent-copy score permits different partial injective labelings on
the two trees, even when a physical source occurs in both trees. -/
theorem separate_renaming {m n} (f g : Fin m → Fin n) (l r : GateTree m)
    (il : Set.InjOn f (sources l)) (ir : Set.InjOn g (sources r)) :
    separate (rename f l) (rename g r) = separate l r := by
  let F : Fin (m+m) → Fin (n+n) := Fin.addCases (fun x => Fin.castAdd n (f x))
    (fun y => Fin.natAdd n (g y))
  let a := rename (Fin.castAdd m) l
  let b := rename (Fin.natAdd m) r
  have inj : Set.InjOn F (sources a ∪ sources b : Finset (Fin (m+m))) := by
    intro i hi j hj eq
    simp only [a,b,sources_rename,coe_union,coe_image,Set.mem_union,Set.mem_image] at hi hj
    rcases hi with ⟨x,hx,rfl⟩|⟨x,hx,rfl⟩ <;> rcases hj with ⟨y,hy,rfl⟩|⟨y,hy,rfl⟩
    · simp only [F,Fin.addCases_left] at eq
      exact congrArg (Fin.castAdd m) (il hx hy (by exact Fin.ext (congrArg (fun z : Fin (n+n) => z.val) eq)))
    · have v := congrArg Fin.val eq
      simp only [F,Fin.addCases_left,Fin.addCases_right,Fin.val_castAdd,Fin.val_natAdd] at v
      have := (f x).isLt; omega
    · have v := congrArg Fin.val eq
      simp only [F,Fin.addCases_left,Fin.addCases_right,Fin.val_castAdd,Fin.val_natAdd] at v
      have := (f y).isLt; omega
    · have v := congrArg Fin.val eq
      simp only [F,Fin.addCases_right,Fin.val_natAdd] at v
      exact congrArg (Fin.natAdd m) (ir hx hy (Fin.ext (by omega)))
  have h := rename_inversion F a b inj
  have fl : F ∘ Fin.castAdd m = Fin.castAdd n ∘ f := by
    funext; simp only [Function.comp_apply,F,Fin.addCases_left]
  have fr : F ∘ Fin.natAdd m = Fin.natAdd n ∘ g := by
    funext; simp only [Function.comp_apply,F,Fin.addCases_right]
  simpa only [separate,a,b,comp,fl,fr] using h

#print axioms separate_renaming
end
end Shellsort.IndependentGateRenaming
