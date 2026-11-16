import «section 6».FrozenInitialJointGeometry
import «section 6».RVRefinementPieces

/-! The actual protected images after unary preparation are exactly
the selected full joint pieces in the ambient label refinement. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n r k l : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]
variable {A : DefSet (rawMixedSpace (M := M) 1 r) S}
variable {C : Fin k → DefSet (rawMixedSpace (M := M) 1 r) S} {hCA : ∀ i,(C i).carrier ⊆ A.carrier}
variable {X : UnaryPreparationContext A (0 : Fin (n+1))}
variable {P : Fin l → DefSet (rawMixedSpace (M := M) (n+1) X.arity) S}
namespace FrozenCoordinateProgramData

theorem joint_piece_subset (h00 : M ⊨ Axioms.ACVF00)
    (F : FrozenCoordinateProgramData (G := G) A C hCA X P)
    (hPX : ∀ i,(P i).carrier ⊆ X.source.carrier) (i : Fin l) :
    (unaryIndexedMixedFamily (F.oldParameterMap h00) (headFibreTemplate (P i))).carrier ⊆
      (F.initialJointAmbient h00).carrier := by
  intro p hp
  obtain ⟨b,hb,hP⟩ := (mem_unaryIndexedMixedFamily _ _ p).mp hp
  apply (mem_unaryIndexedMixedFamily _ _ p).mpr
  exact ⟨b,hb,headFibreTemplate_subset (hPX i) ((F.oldParameterMap h00 b).val 0) hP⟩

theorem actual_refinement_piece_eq (h00 : M ⊨ Axioms.ACVF00)
    (F : FrozenCoordinateProgramData (G := G) A C hCA X P)
    (U : UnaryContextLift (G := G) X F.unary.map P)
    (hPX : ∀ i,(P i).carrier ⊆ X.source.carrier) (i : Fin l) :
    (F.actualAmbientRefinement h00 U).selectedPiece
        (unaryIndexedMixedFamily (F.oldParameterMap h00) (headFibreTemplate (P i)))=
      (U.map.restrict (hPX i)).image := by
  let Z := F.actualAmbientRefinement h00 U
  let Q := unaryIndexedMixedFamily (F.oldParameterMap h00) (headFibreTemplate (P i))
  apply defSet_eq_of_carrier_eq
  ext q
  constructor
  · intro hq
    obtain ⟨hqTarget,hqJoint⟩ := (Z.mem_selectedPiece Q q).mp hq
    let qTarget : U.target.source := ⟨q,hqTarget⟩
    have hPi : (U.map.inverse (U.chain.toChain.toSpecial.bijective h00) qTarget).val ∈ (P i).carrier :=
      (F.transportedJoint_mem_iff h00 U (P i) (F.sources_preserved.2 i) qTarget).mp hqJoint
    refine ⟨⟨(U.map.inverse (U.chain.toChain.toSpecial.bijective h00) qTarget).val,hPi⟩,?_⟩
    change (U.map (U.map.inverse (U.chain.toChain.toSpecial.bijective h00) qTarget)).val=q
    rw [Map.apply_inverse]
  · rintro ⟨p,rfl⟩
    let pSource : X.source := ⟨p.val,hPX i p.property⟩
    apply (Z.mem_selectedPiece Q _).mpr
    refine ⟨(U.map pSource).property,?_⟩
    apply (F.transportedJoint_mem_iff h00 U (P i) (F.sources_preserved.2 i) (U.map pSource)).mpr
    rw [Map.inverse_apply]
    exact p.property

end FrozenCoordinateProgramData
end DiamondIntegral.Section6
