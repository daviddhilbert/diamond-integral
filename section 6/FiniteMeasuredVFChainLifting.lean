import «section 6».MeasuredVFUnaryLiftChains

/-! Lift every component of a finite-label measured RV chain to an
actual relatively unary VF map. Total derivatives and the measure identity
hold everywhere, and double bounds give proper homeomorphisms for every
component and the full composition. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
open Classical FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

theorem exists_finite_measured_vf_unary_chain
    (hc : CanonicalStructure.IsCanonical (M := M)) (h00 : M ⊨ Axioms.ACVF00)
    (linear : GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (W : Set M) (hW : ∀ a ∈ W, iVF a) (hWS : W ⊆ S) (hSW : S ⊆ algebraicClosureSet W)
    (hnt : ∃ x : vfAlgebraicClosureField W, x ≠ 0 ∧ Valued.v x.val ≠ 1)
    (hsmall : Cardinal.mk S < κ) (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M)) :
    ∀ {U V : MeasuredRVObject (M := M) S n} (T : MeasuredRVUnaryChain S n U V),
    U.object.domain.carrier.Finite →
    ∃ H : MeasuredVFUnaryLiftChain S n U V,
      H.iso.iso.hom.map = T.iso.iso.hom.map ∧ (T.doublyBounded → H.properComponents) := by
  intro U V T
  induction T with
  | identity U =>
    intro hFin
    refine ⟨.identity U,rfl,fun hUB => ?_⟩
    let F := EverywhereMeasuredRVLift.identity U
    exact properHomeomorphism_of_measuredRVIsoLift h00 hc linear hκ hs hv hsmall hΓ (.identity U) hUB hUB
      F.map F.bijective F.labels (fun p => ⟨(F.measure p).choose,(F.measure p).choose_spec.1⟩)
  | @step U V X i e hUnary T ih =>
    intro hFin
    obtain ⟨f,hf,hfu,hlab,hcont,hm⟩ := exists_finite_relative_measured_rv_lift hc h00 hs hv W hW hWS hSW hnt hsmall
      e hFin i hUnary
    let F : EverywhereMeasuredRVLift e := ⟨f,hf,hlab,hm⟩
    obtain ⟨H,hH,hHP⟩ := ih (rvIso_finite_target_domain e.iso hFin)
    refine ⟨.step i F hfu H,?_,fun hTB => ?_⟩
    · apply Map.ext
      intro u
      change H.iso.iso.hom.map (e.iso.hom.map u) = T.iso.iso.hom.map (e.iso.hom.map u)
      rw [hH]
    · exact ⟨properHomeomorphism_of_measuredRVIsoLift h00 hc linear hκ hs hv hsmall hΓ e hTB.1
        (T.source_doublyBounded hTB.2) f hf hlab (fun p => ⟨(hm p).choose,(hm p).choose_spec.1⟩),hHP hTB.2⟩

theorem lemma_6_33_finite_labels_vfGenerated
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    (linear : GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (S : LRV.Substructure M) (B : VFGeneratedFieldBase S) (hsmall : Cardinal.mk (S : Set M) < κ)
    (hΓ : NontrivialDefinableGamma (⟨(S : Set M),∅⟩ : ParameterBase M))
    (hnt : ∃ x : B.field, x ≠ 0 ∧ Valued.v x.val ≠ 1) (hn : 0 < n)
    {U V : MeasuredRVObject (M := M) (S : Set M) n} (e : MeasuredRVIso U V)
    (hFin : U.object.domain.carrier.Finite) :
    ∃ H : MeasuredVFUnaryLiftChain (S : Set M) n U V, H.iso.iso.hom.map = e.iso.hom.map := by
  obtain ⟨hW,hWS,hSW,hnt'⟩ := vfGenerated_base_support S B hnt
  obtain ⟨T,hT⟩ := lemma_6_29_measured_finite_labels hc hn e hFin
  obtain ⟨H,hH,_⟩ := exists_finite_measured_vf_unary_chain hc h00 linear hκ hs hv
    (vfFieldNames B.field) hW hWS hSW hnt' hsmall hΓ T hFin
  exact ⟨H,hH.trans hT⟩

theorem lemma_6_33_finite_labels_doublyBounded_vfGenerated
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    (linear : GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (S : LRV.Substructure M) (B : VFGeneratedFieldBase S) (hsmall : Cardinal.mk (S : Set M) < κ)
    (hΓ : NontrivialDefinableGamma (⟨(S : Set M),∅⟩ : ParameterBase M))
    (hnt : ∃ x : B.field, x ≠ 0 ∧ Valued.v x.val ≠ 1) (hn : 0 < n)
    {U V : MeasuredRVObject (M := M) (S : Set M) n} (e : MeasuredRVIso U V)
    (hFin : U.object.domain.carrier.Finite) (hU : U.doublyBounded) (hV : V.doublyBounded) :
    ∃ H : MeasuredVFUnaryLiftChain (S : Set M) n U V,
      H.iso.iso.hom.map = e.iso.hom.map ∧ H.properComponents ∧ ProperCovariantHomeomorphism H.lift.map := by
  obtain ⟨hW,hWS,hSW,hnt'⟩ := vfGenerated_base_support S B hnt
  obtain ⟨T,hT,hTB⟩ := lemma_6_29_measured_finite_labels_doublyBounded hc hn e hFin hU hV
  obtain ⟨H,hH,hHP⟩ := exists_finite_measured_vf_unary_chain hc h00 linear hκ hs hv
    (vfFieldNames B.field) hW hWS hSW hnt' hsmall hΓ T hFin
  exact ⟨H,hH.trans hT,hHP hTB,properHomeomorphism_of_measuredRVIsoLift h00 hc linear hκ hs hv hsmall hΓ
    H.iso hU hV H.lift.map H.lift.bijective H.lift.labels
    (fun p => ⟨(H.lift.measure p).choose,(H.lift.measure p).choose_spec.1⟩)⟩

end DiamondIntegral.Section6
