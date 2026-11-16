import «section 6».UnaryApertureInclusion
import «section 6».UnaryRelativeRVFamilyMeasuredMatching

/-! Complete Section 6 matching in the precise bounded variable class.
The original proper objects, actual forms and original VF-generated base
are retained. The result includes both genuine finite variable chains,
the literal conjugate, full RV bijection and every-label volume identity.
It does not assert the original scalar-aperture statement or a Section 7
kernel theorem. No downstream definition is changed here. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 16000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {r s : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

theorem lemma_6_38_bounded_variable_apertures
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    (linear : GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (S : LRV.Substructure M) (B₀ : VFGeneratedFieldBase S)
    (hsmall : Cardinal.mk (S : Set M) < κ)
    (hΓ : NontrivialDefinableGamma (⟨(S : Set M),∅⟩ : ParameterBase M))
    (hnt : ∃ x : B₀.field,x≠0 ∧ Valued.v x.val≠1)
    (A : DefSet (rawMixedSpace (M := M) 1 r) (S : Set M))
    (B : DefSet (rawMixedSpace (M := M) 1 s) (S : Set M))
    (f : Map A B) (hf : ProperCovariantHomeomorphism f)
    (hA : ProperInvariant (S : Set M) A.carrier) (hB : ProperInvariant (S : Set M) B.carrier)
    (ω : Map A (DefSet.univ (rawGammaPresentation (M := M)) (S : Set M)))
    (σ : Map B (DefSet.univ (rawGammaPresentation (M := M)) (S : Set M)))
    (hωLevels : ∀ u γ,IsOpen {a : Fin 1 → VF M | (a,u) ∈ A.carrier ∧ gammaFormExtension ω (a,u)=γ})
    (hσLevels : ∀ u γ,IsOpen {a : Fin 1 → VF M | (a,u) ∈ B.carrier ∧ gammaFormExtension σ (a,u)=γ})
    (hGeneric : ∀ a : A,AlgebraicIndependent (vfParameterField (S : Set M)) a.val.1 →
      ∃ J : VF M,HasMixedVFJacobianAt f a J ∧ vfValue J=(gammaMapValue ω a/gammaMapValue σ (f a)).val) :
    ∃ H : UnaryRelativeMeasuredMatching (G := G) A B f h00 ω σ,
      RelativeApertureChain (G := G) A H.geometry.source H.geometry.sourceMap ∧
      RelativeApertureChain (G := G) B H.geometry.target H.geometry.targetMap := by
  obtain ⟨H⟩ := unary_relative_measured_rv_family_matching_exists h00 hc linear hκ hs hv S B₀ hsmall hΓ hnt
    A B f hf hA hB ω σ hωLevels hσLevels hGeneric
  exact ⟨H,H.geometry.sourceChain.toRelativeChain hc h00 linear hκ.le hs hsmall hΓ,
    H.geometry.targetChain.toRelativeChain hc h00 linear hκ.le hs hsmall hΓ⟩

end DiamondIntegral.Section6
