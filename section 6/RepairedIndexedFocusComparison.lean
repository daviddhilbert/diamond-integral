import «section 6».SelectedIndexedFocusRepair

/-! Compare the repaired permitted component with the old component
formula at the updated parameter. Both its complete focus values and
its actual active locus are transported, including inactive points. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n r s k : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]
variable {B : DefSet (rawMixedSpace (M := M) 1 r) S}
variable {η : Map B (DefSet.univ (rawVFSpace (M := M) 1) S)}
variable {A : MixedSetParameterTemplate (M := M) S 1 n s}
variable {P : Fin k → MixedSetParameterTemplate (M := M) S 1 n s}
variable {W : DefSet (rawMixedSpace (M := M) (n+1) (r+s)) S}
variable {Q : Fin k → DefSet (rawMixedSpace (M := M) (n+1) (r+s)) S}
variable {F : TailContinuousFullFocusGraphData (G := G) W}
namespace IndexedFocusRepairCertificate

theorem indexed_focus_value (R : IndexedFocusRepairCertificate (G := G) η A P W Q F)
    (T : ContinuousRVGraphTemplate (M := M) S 1 s n 1)
    (hBase : ∀ p ∈ (focusActive W F.activeTags).carrier,unaryFamilyBasePoint p ∈ B.carrier)
    (hGood : ∀ p ∈ (focusActive W F.activeTags).carrier,∀ b : B,unaryFamilyBasePoint p=b.val →
      unaryFamilyParameter η b ∈ T.good)
    (hMap : F.map=unaryIndexedFamilyMap η T (focusActive W F.activeTags) hBase hGood)
    (p : focusActive W F.activeTags) (b : B) (hb : unaryFamilyBasePoint p.val=b.val) :
    ∃ ha : unaryFamilyParameter (R.freezing.unaryParameter R.baseProduct η) b ∈ T.good,
      R.component.extendedFocus p.val=
        T.value _ ha (p.val.2 ∘ Fin.natAdd r) (Fin.tail p.val.1) 0 := by
  obtain ⟨ha,hValue⟩ := R.freezing.frozen_indexed_map_value R.baseProduct η T hBase hGood p b hb
  refine ⟨ha,(R.focus p).trans ?_⟩
  rw [hMap]
  exact congrFun hValue 0

theorem indexed_active_iff (R : IndexedFocusRepairCertificate (G := G) η A P W Q F)
    (T : RVSetParameterTemplate (M := M) S 1 s)
    (hSource : W.carrier ⊆ (unaryIndexedMixedFamily η A).carrier)
    (hPullback : ∀ b : B,IsRVPullback (A.fibre (unaryFamilyParameter η b)).carrier)
    (hRows : ∀ b c : B,b.val.2=c.val.2 →
      ((leadingRVImageTemplate (focusActiveParameterTemplate A T)).fibre (unaryFamilyParameter η b)).carrier=
        ((leadingRVImageTemplate (focusActiveParameterTemplate A T)).fibre (unaryFamilyParameter η c)).carrier)
    (hLocus : ∀ p ∈ W.carrier,∀ b : B,unaryFamilyBasePoint p=b.val →
      (p.2 ∈ F.activeTags.carrier ↔ p.2 ∘ Fin.natAdd r ∈ (T.fibre (unaryFamilyParameter η b)).carrier))
    (p : Mixed M (n+1) (r+s)) (hp : p ∈ W.carrier) (b : B) (hb : unaryFamilyBasePoint p=b.val) :
    p.2 ∈ R.component.activeTags.carrier ↔ p.2 ∘ Fin.natAdd r ∈
      (T.fibre (unaryFamilyParameter (R.freezing.unaryParameter R.baseProduct η) b)).carrier := by
  let c := R.freezing.unaryBaseFreeze R.baseProduct b
  have hClip (z : B) : IsRVPullback
      ((focusActiveParameterTemplate A T).fibre (unaryFamilyParameter η z)).carrier := by
    rw [focusActiveParameterTemplate_fibre]
    exact focusActive_rvPullback _ _ (hPullback z)
  have hEq := template_fibres_eq_of_leading_rows (focusActiveParameterTemplate A T) _ _
    (hClip b) (hClip c) (hRows b c rfl)
  have hAt := Set.ext_iff.mp hEq (Fin.tail p.1,p.2 ∘ Fin.natAdd r)
  rw [focusActiveParameterTemplate_fibre,focusActiveParameterTemplate_fibre] at hAt
  have hOld := (mem_unaryIndexedMixedFamily_at η A p b hb).mp (hSource hp)
  have hNew := (mem_unaryIndexedMixedFamily_at (R.freezing.unaryParameter R.baseProduct η) A p b hb).mp
    (R.source hp)
  have hLocal : p.2 ∘ Fin.natAdd r ∈ (T.fibre (unaryFamilyParameter η b)).carrier ↔
      p.2 ∘ Fin.natAdd r ∈ (T.fibre (unaryFamilyParameter (R.freezing.unaryParameter R.baseProduct η) b)).carrier :=
    (and_iff_right hOld).symm.trans (hAt.trans (and_iff_right hNew))
  rw [R.activeTags,hLocus p hp b hb]
  exact hLocal

end IndexedFocusRepairCertificate
end DiamondIntegral.Section6
