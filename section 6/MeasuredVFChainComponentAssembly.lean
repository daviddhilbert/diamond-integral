import «section 6».MeasuredVFUnaryChainBounds

/-! Assemble actual VF component chains along an actual RV unary
factorization. Intermediate double bounds pass through composition. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n : ℕ}

theorem exists_measured_vf_chain_of_component_chains
    (hLift : ∀ {A B : MeasuredRVObject (M := M) S n} (i : Fin n) (e : MeasuredRVIso A B),
      RVUnaryRelativeAt e.iso.hom.map i →
        ∃ L : MeasuredVFUnaryLiftChain S n A B,L.iso.iso.hom.map=e.iso.hom.map ∧
          ((A.doublyBounded ∧ B.doublyBounded) → L.doublyBounded))
    {U V : MeasuredRVObject (M := M) S n} (T : MeasuredRVUnaryChain S n U V) :
    ∃ L : MeasuredVFUnaryLiftChain S n U V,L.iso.iso.hom.map=T.iso.iso.hom.map ∧
      (T.doublyBounded → L.doublyBounded) := by
  induction T with
  | identity U => exact ⟨.identity U,rfl,fun h => h⟩
  | @step U V W i e he T ih =>
    obtain ⟨L,hL,hLB⟩ := hLift i e he
    obtain ⟨H,hH,hHB⟩ := ih
    refine ⟨L.comp H,?_,fun hT => L.comp_doublyBounded H
      (hLB ⟨hT.1,T.source_doublyBounded hT.2⟩) (hHB hT.2)⟩
    apply Map.ext
    intro u
    rw [MeasuredVFUnaryLiftChain.comp_map,hL,hH]
    rfl

end DiamondIntegral.Section6
