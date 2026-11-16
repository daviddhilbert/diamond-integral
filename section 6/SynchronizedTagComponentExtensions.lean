import «section 6».CentripetalLocusExtension
import «section 6».SynchronizedCentripetalChains
import «section 6».CentripetalProgramRealizations

/-! A component on a whole old-label branch extends to the ambient
set with actual aperture-compatible components on every protected
piece. Outside that branch the VF coordinates are unchanged. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n r k : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

theorem exists_synchronized_tag_component_extension
    {A C : DefSet (rawMixedSpace (M := M) n r) S}
    (D : CentripetalData (G := G) C) (U : DefSet (rawRVSpace (M := M) r) S)
    (hC : C.carrier=(focusActive A U).carrier)
    (hA : ProperInvariant S A.carrier) (hAD : VFDoublyBounded A.carrier)
    (hTag : ∀ x ∈ A.carrier,∀ y ∈ A.carrier,x.2=y.2 → tupleRV M x.1=tupleRV M y.1)
    (P Q : Fin k → DefSet (rawMixedSpace (M := M) n r) S)
    (hPA : ∀ i,(P i).carrier ⊆ A.carrier) (hP : ∀ i,ProperInvariant S (P i).carrier)
    (hQ : ∀ i,(Q i).carrier=(focusActive (P i) U).carrier)
    (E : ∀ i,CentripetalData (G := G) (Q i)) (hData : ∀ i,ApertureRestrictionData D (E i)) :
    ∃ F : CentripetalData (G := G) A,∃ H : ∀ i,CentripetalData (G := G) (P i),
      F.coordinate=D.coordinate ∧ F.coefficient=D.coefficient ∧
      (∀ i,ApertureRestrictionData F (H i)) ∧
      (∀ x ∈ C.carrier,F.point x=D.point x) ∧
      (∀ x ∈ A.carrier,x.2 ∉ U.carrier → (F.point x).1=x.1) ∧
      SynchronizedCentripetalChain (G := G) (Fin k) A F.map.image F.bijection P := by
  let F := D.extendOnTags U hC hA hAD hTag
  let H (i) := (E i).extendOnTags U (hQ i) (hP i) (hAD.mono (hPA i))
    (fun x hx y hy he => hTag x (hPA i hx) y (hPA i hy) he)
  have hRestr (i) : ApertureRestrictionData F (H i) := by
    refine ⟨hPA i,(hData i).coordinate,(hData i).coefficient,?_⟩
    intro x hx
    by_cases hu : x.2 ∈ U.carrier
    · have hxC : x ∈ C.carrier := by rw [hC]; exact ⟨hPA i hx,hu⟩
      have hxQ : x ∈ (Q i).carrier := by rw [hQ i]; exact ⟨hx,hu⟩
      exact ((E i).extendOnTags_extendedFocus U (hQ i) (hP i) (hAD.mono (hPA i))
        (fun x hx y hy he => hTag x (hPA i hx) y (hPA i hy) he) x hxQ).trans
          (((hData i).focus x hxQ).trans (D.extendOnTags_extendedFocus U hC hA hAD hTag x hxC).symm)
    · have hF : x.2 ∉ F.activeTags.carrier := fun h => hu h.2
      have hH : x.2 ∉ (H i).activeTags.carrier := fun h => hu h.2
      rw [(H i).extendedFocus_inactive hH,F.extendedFocus_inactive hF]
  refine ⟨F,H,rfl,rfl,hRestr,D.extendOnTags_point U hC hA hAD hTag,?_,
    .centripetal A F P hPA H hRestr⟩
  intro x hx hu
  exact F.point_inactive (fun h => hu h.2)

end DiamondIntegral.Section6
