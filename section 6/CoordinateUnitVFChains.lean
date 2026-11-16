import «section 6».RelativeTailVFChainStep
import «section 6».CoordinateUnitVolumes

/-! The actual triangular chain replacing one tail coordinate by a unit
RV pad. The finite head is unchanged, and only strictly smaller RV-rank
chains are used in exceptional fibres. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section7 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M G : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable [LinearOrderedCommGroupWithZero G] [Valued (VF M) G] {k m : ℕ}

theorem exists_coordinate_unit_vf_chain_vfGenerated
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (S : LRV.Substructure M) (B : VFGeneratedFieldBase S) (hsmall : Cardinal.mk (S : Set M) < κ)
    (hΓ : NontrivialDefinableGamma (⟨(S : Set M),∅⟩ : ParameterBase M))
    (hLower : ∀ {P Q : MeasuredRVObject (M := M) (S : Set M) ((k+1)+m)} (g : MeasuredRVIso P Q),
      rvDim P.object.domain < k+1 →
        ∃ T : MeasuredVFUnaryLiftChain (S : Set M) ((k+1)+m) P Q,T.iso.iso.hom.map=g.iso.hom.map ∧
          ((P.doublyBounded ∧ Q.doublyBounded) → T.doublyBounded))
    (U : MeasuredRVObject (M := M) (S : Set M) ((k+1)+m))
    (hU : (rvHeadVolume U.object (productLeft (k+1) m)).FiniteFibres) (j : Fin m) :
    ∃ T : MeasuredVFUnaryLiftChain (S : Set M) ((k+1)+m) U
        (measuredRVCoordinateUnit hc U (productLeft (k+1) m) hU (productRight (k+1) m j)
          (fun l => productLeft_ne_right l j)),
      (∀ u,T.iso.iso.hom.map u=u) ∧ (U.doublyBounded → T.doublyBounded) := by
  let i := productRight (k+1) m j
  let hi := fun l => @productLeft_ne_right (k+1) m l j
  let V := measuredRVCoordinateUnit hc U (productLeft (k+1) m) hU i hi
  let e := measuredRVCoordinateUnitIso hc U (productLeft (k+1) m) hU i hi
  have hHead : rvHeadVolume V.object (productLeft (k+1) m)=rvHeadVolume U.object (productLeft (k+1) m) := by
    apply Map.ext
    intro u
    apply Subtype.ext
    funext l
    change V.object.value u (productLeft (k+1) m l)=U.object.value u (productLeft (k+1) m l)
    rw [measuredRVCoordinateUnit_value,Function.update_of_ne (hi l)]
  have hV : (rvHeadVolume V.object (productLeft (k+1) m)).FiniteFibres := hHead.symm ▸ hU
  have hRelative : RVUnaryRelativeAt e.iso.hom.map i := by
    intro u l hl
    change V.object.value u l=U.object.value u l
    rw [measuredRVCoordinateUnit_value,Function.update_of_ne hl]
  obtain ⟨T,hT,hTB⟩ := exists_relative_tail_vf_chain_of_smaller_ranks_vfGenerated h00 hc hκ hs hv
    S B hsmall hΓ hLower e hU hV j hRelative
  exact ⟨T,fun u => by rw [hT]; rfl,fun hB => hTB ⟨hB,measuredRVCoordinateUnit_doublyBounded hc U _ hU i hi hB⟩⟩

end DiamondIntegral.Section6
