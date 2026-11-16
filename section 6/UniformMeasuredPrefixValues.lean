import «section 6».UniformMeasuredProgramPrefixes
import «section 6».CodeGraphValueUniqueness

/-! The remaining family agrees with inverse transport through every
actual realization of the prefix. Its canonical choice of a realization
does not impose an additional compatibility assumption on global fusion. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section8 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6.UniformMeasuredProgramFamily
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n r s t v k : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]
variable {B : DefSet (rawMixedSpace (M := M) 1 r) S}

theorem afterPrefix_value
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    (linear : GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (hsmall : Cardinal.mk S < κ) (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M))
    {η : Map B (DefSet.univ (rawVFSpace (M := M) 1) S)}
    {F : CentripetalProgramTemplate (M := M) S 1 n s t}
    {H : CentripetalProgramTemplate (M := M) S 1 n t v}
    {A : MixedSetParameterTemplate (M := M) S 1 n s}
    {P : Fin k → MixedSetParameterTemplate (M := M) S 1 n s}
    {W : GammaFormParameterTemplate (M := M) S 1 n s}
    (U : UniformMeasuredProgramFamily (G := G) η (F.comp H) A P W) (b : B)
    {Z : DefSet (rawMixedSpace (M := M) n t) (S ∪ Set.range (unaryFamilyParameter η b))}
    (f : Map (A.fibre (unaryFamilyParameter η b)) Z) (hf : Function.Bijective f)
    (hF : {z | Sum.elim (unaryFamilyParameter η b) z ∈ (F.transition A).graph}=
      (rawMixedSpace n s).relation (rawMixedSpace n t) f.graph)
    (x : A.fibre (unaryFamilyParameter η b)) (y : (F.target A).fibre (unaryFamilyParameter η b))
    (hPoint : y.val=(f x).val) :
    ((U.afterPrefix h00 hc linear hκ hs hv hsmall hΓ).forms b y).val=(U.forms b x).val := by
  let V := U.afterPrefix h00 hc linear hκ hs hv hsmall hΓ
  let ζ := (U.forms b).comp (f.inverse hf)
  have hGraph := gammaTransitionImage_at (unaryFamilyParameter η b) (F.transition A).graph W.graph
    f hf (U.forms b) hF (U.graphs b)
  have hSame := map_values_eq_of_code_graph_eq (V.forms b) ζ ((V.graphs b).symm.trans hGraph) y (f x) hPoint
  change (V.forms b y).val=(U.forms b (f.inverse hf (f x))).val at hSame
  rw [Map.inverse_apply] at hSame
  exact hSame

end DiamondIntegral.Section6.UniformMeasuredProgramFamily
