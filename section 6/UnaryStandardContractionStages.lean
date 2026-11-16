import «section 6».OrderedStandardContractionPrograms

/-! The completed unary standard-contraction theorem supplies an actual
stage of the higher-dimensional ordered program, with its full derivative,
proper homeomorphism and retained-label certificates. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section8 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {r : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]
variable {A : DefSet (rawMixedSpace (M := M) 1 r) S}

def UnaryStandardContraction.toStage
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    (linear : GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (hsmall : Cardinal.mk S < κ) (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M))
    (T : UnaryStandardContraction (G := G) A) : StandardContractionStage (G := G) A := by
  let h := T.retainsOriginalRV.choose
  have hRetained := T.retainsOriginalRV.choose_spec
  have hData := T.lift_jacobian_ae h00 hc linear hκ hs hv hsmall hΓ
  let E := hData.2.choose
  have hEA := hData.2.choose_spec.1
  have hDim := hData.2.choose_spec.2.1
  have hUnit := hData.2.choose_spec.2.2
  refine {
    arity := 1+T.labels
    target := T.target
    lift := T.lift
    home := hData.1
    proper := T.proper
    doublyBounded := T.doublyBounded
    relative := fun _ i => i.elim0
    oldLabels := rvTailIndex h
    oldLabels_injective := ?_
    retained := hRetained
    leading := Fin.castAdd T.labels (0 : Fin 1)
    bundle := rvPullback_last_coordinate_bundle T.target T.prepared _ T.leading
    exceptional := E
    exceptional_subset := hEA
    exceptional_dim := hDim
    unitDerivative := hUnit }
  intro i j he
  apply Fin.ext
  have he' := congrArg Fin.val he
  change (1+T.labels)-r+i.val=(1+T.labels)-r+j.val at he'
  omega

theorem ordered_standard_program_unary
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    (linear : GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (V : Set M) (hsmall : Cardinal.mk S < κ)
    (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M))
    (hV : ∀ x ∈ V,iVF x) (hVS : V ⊆ S) (hSV : S ⊆ algebraicClosureSet V)
    (hnt : ∃ x : vfAlgebraicClosureField V,x ≠ 0 ∧ Valued.v x.val ≠ 1)
    (A : DefSet (rawMixedSpace (M := M) 1 r) S) (hA : ProperInvariant S A.carrier) :
    ∃ q,∃ U : DefSet (rawMixedSpace (M := M) 0 q) S,
      Nonempty (OrderedStandardContractionProgram (G := G) S A U) := by
  obtain ⟨T⟩ := lemma_6_27_unary h00 hc linear hκ hs hv V hsmall hΓ hV hVS hSV hnt A hA
  let R := T.toStage h00 hc linear hκ hs hv hsmall hΓ
  exact ⟨R.arity,R.contracted,⟨.step R (.zero R.contracted)⟩⟩

end DiamondIntegral.Section6
