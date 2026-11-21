import Shellsort.LargeGapRecordMean

namespace Shellsort.LargeGapRecordWeights
open Finset LargeGapPrefixRecords LargeGapRecordMean HarvestOperationalAudit

/-- Initial prefix plus the total width of the newly exposed parts of right bands. -/
def weight (n l : ℕ) : List ℕ → ℕ
  | [] => l
  | g :: gs => weight n l gs + min l (gs.headD n - g)

def cappedWeight (n l : ℕ) (gs : List ℕ) := weight n (min l (gs.headD n)) gs

private def geom (n l : ℕ) : List ℕ → Finset ℕ
  | [] => range l
  | g :: gs => geom n l gs ∪ Ico g (min (gs.headD n) (g+l))

private theorem mem_geom (n l i : ℕ) (gs : List ℕ) :
    i ∈ geom n l gs ↔ seen n l i gs := by
  induction gs with
  | nil => simp [geom,seen]
  | cons g gs ih => simp [geom,seen,ih,fresh,lt_min_iff,and_assoc]

private theorem geom_facts (n l : ℕ) (gs : List ℕ) (asc : gs.Pairwise (· < ·))
    (legal : ∀ h ∈ gs, h < n) (hl : l ≤ gs.headD n) :
    (geom n l gs).card = weight n l gs ∧
    ∀ i ∈ geom n l gs, i < n ∧ (i < l ∨ gs.headD n ≤ i) := by
  induction gs with
  | nil =>
    simp only [List.headD_nil] at hl
    simp [geom,weight]
    omega
  | cons g gs ih =>
    have facts := List.pairwise_cons.mp asc
    have gH : g < gs.headD n := by
      cases gs with
      | nil => exact legal g (by simp)
      | cons h tail => exact facts.1 h (by simp)
    have Hn : gs.headD n ≤ n := by
      cases gs with
      | nil => exact le_rfl
      | cons h tail => exact (legal h (by simp)).le
    change l ≤ g at hl
    obtain ⟨card,loc⟩ := ih facts.2 (fun h hh => legal h (by simp [hh])) (by omega)
    have dis : Disjoint (geom n l gs) (Ico g (min (gs.headD n) (g+l))) := by
      rw [Finset.disjoint_left]
      intro i hi hj
      have old := (loc i hi).2
      have fr := Finset.mem_Ico.mp hj
      omega
    constructor
    · rw [geom,Finset.card_union_of_disjoint dis,card,Nat.card_Ico,weight]
      omega
    · intro i hi
      rcases Finset.mem_union.mp hi with old | new
      · have hb := loc i old
        exact ⟨hb.1,hb.2.imp_right (le_trans gH.le)⟩
      · have hb := Finset.mem_Ico.mp new
        exact ⟨by omega,Or.inr hb.1⟩

private theorem card_raw (n l : ℕ) (gs : List ℕ) (asc : gs.Pairwise (· < ·))
    (legal : ∀ h ∈ gs, h < n) : (rawSet n gs l).card = cappedWeight n l gs := by
  classical
  let k := min l (gs.headD n)
  obtain ⟨hc,loc⟩ := geom_facts n k gs asc legal (min_le_right ..)
  have same : (rawSet n gs l).image Fin.val = geom n k gs := by
    ext i
    constructor
    · intro hi
      obtain ⟨j,hj,rfl⟩ := mem_image.mp hi
      exact (mem_geom ..).mpr (by simpa [rawSet,k] using hj)
    · intro hi
      exact mem_image.mpr ⟨⟨i,(loc i hi).1⟩,
        by simpa [rawSet,k] using (mem_geom ..).mp hi,rfl⟩
  rw [← Finset.card_image_of_injective _ Fin.val_injective,same,hc]
  rfl

private theorem mono_seen {n i l k : ℕ} (lk : l ≤ k) (gs : List ℕ) :
    seen n l i gs → seen n k i gs := by
  induction gs with
  | nil => exact fun h => lt_of_lt_of_le h lk
  | cons h gs ih =>
    rintro (old | ⟨b,c,d⟩)
    · exact Or.inl (ih old)
    · exact Or.inr ⟨b,c,by omega⟩

theorem executed_weighted_record {n : ℕ} (w : HarvestBlockIteration.PositiveWord)
    (asc : (w.map Subtype.val).reverse.Pairwise (· < ·))
    (large : ∀ h ∈ w, h.val < n ∧ n ≤ 2*h.val) (j : Fin n) :
    let gs := (w.map Subtype.val).reverse
    uniformAverage (fun p : RankPlacement n =>
      indicator (record (runWord (slots p) w).1 j)) =
      ((cappedWeight n (j.val+1) gs - cappedWeight n j.val gs : ℕ) : ℝ) /
        (cappedWeight n (j.val+1) gs : ℝ) := by
  classical
  let gs := (w.map Subtype.val).reverse
  have legal (h : ℕ) (hh : h ∈ gs) : h < n := by
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp (List.mem_reverse.mp hh)
    exact (large a ha).1
  have sub : rawSet n gs j.val ⊆ rawSet n gs (j.val+1) := by
    intro i hi
    simpa only [rawSet,Finset.mem_filter,Finset.mem_univ,true_and] using
      (mono_seen (n := n) (i := i.val) (min_le_min_right (gs.headD n) (Nat.le_succ j.val)) gs
        (by simpa [rawSet] using hi))
  have prob := executed_record_probability w asc large j
  change _ = ((rawSet n gs (j.val+1) \ rawSet n gs j.val).card : ℝ) /
    ((rawSet n gs (j.val+1)).card : ℝ) at prob
  rw [Finset.card_sdiff_of_subset sub,card_raw n _ gs asc legal,card_raw n _ gs asc legal] at prob
  exact prob

#print axioms executed_weighted_record
end Shellsort.LargeGapRecordWeights
