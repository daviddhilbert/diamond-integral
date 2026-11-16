import «section 6».FiniteMeasuredVFChainLifting
import «section 6».MeasuredVFUnaryChainBounds
import «section 6».RVIsomorphismFactorizations

/-! The finite-label base of VF chain lifting retains the actual double
bounds at every intermediate object, for use in RV-rank induction. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

theorem exists_finite_measured_vf_chain_with_bounds
    (hc : CanonicalStructure.IsCanonical (M := M)) (h00 : M ⊨ Axioms.ACVF00)
    {κ : Cardinal} (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (W : Set M) (hW : ∀ a ∈ W,iVF a) (hWS : W ⊆ S) (hSW : S ⊆ algebraicClosureSet W)
    (hnt : ∃ x : vfAlgebraicClosureField W,x ≠ 0 ∧ Valued.v x.val ≠ 1)
    (hsmall : Cardinal.mk S < κ) :
    ∀ {U V : MeasuredRVObject (M := M) S n} (T : MeasuredRVUnaryChain S n U V),
      U.object.domain.carrier.Finite →
        ∃ H : MeasuredVFUnaryLiftChain S n U V,H.iso.iso.hom.map=T.iso.iso.hom.map ∧
          (T.doublyBounded → H.doublyBounded) := by
  intro U V T
  induction T with
  | identity U => exact fun _ => ⟨.identity U,rfl,fun h => h⟩
  | @step U V X i e hUnary T ih =>
    intro hFin
    obtain ⟨f,hf,hfu,hlab,_,hm⟩ := exists_finite_relative_measured_rv_lift hc h00 hs hv W hW hWS hSW hnt hsmall
      e hFin i hUnary
    let F : EverywhereMeasuredRVLift e := ⟨f,hf,hlab,hm⟩
    obtain ⟨H,hH,hHB⟩ := ih (rvIso_finite_target_domain e.iso hFin)
    refine ⟨.step i F hfu H,?_,fun hT => ⟨hT.1,hHB hT.2⟩⟩
    apply Map.ext
    intro u
    change H.iso.iso.hom.map (e.iso.hom.map u)=T.iso.iso.hom.map (e.iso.hom.map u)
    rw [hH]

theorem exists_finite_measured_vf_chain_with_bounds_vfGenerated
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (S : LRV.Substructure M) (B : VFGeneratedFieldBase S) (hsmall : Cardinal.mk (S : Set M) < κ)
    (hnt : ∃ x : B.field,x ≠ 0 ∧ Valued.v x.val ≠ 1) (hn : 0 < n)
    {U V : MeasuredRVObject (M := M) (S : Set M) n} (e : MeasuredRVIso U V)
    (hFin : U.object.domain.carrier.Finite) :
    ∃ H : MeasuredVFUnaryLiftChain (S : Set M) n U V,H.iso.iso.hom.map=e.iso.hom.map ∧
      ((U.doublyBounded ∧ V.doublyBounded) → H.doublyBounded) := by
  obtain ⟨hW,hWS,hSW,hnt'⟩ := vfGenerated_base_support S B hnt
  obtain ⟨T,hT,hTB⟩ := lemma_6_29_measured hc h00 hκ.le hs hsmall hn e
  obtain ⟨H,hH,hHB⟩ := exists_finite_measured_vf_chain_with_bounds hc h00 hs hv
    (vfFieldNames B.field) hW hWS hSW hnt' hsmall T hFin
  exact ⟨H,hH.trans hT,fun h => hHB (hTB h)⟩

end DiamondIntegral.Section6
