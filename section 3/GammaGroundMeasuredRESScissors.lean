import «section 3».GammaGroundRESScissors
import «section 3».GammaGroundMeasuredRVIsomorphismClasses

/-! Measured RES retains all Gamma forms, including in degree zero,
and the same finite source-value support as unmeasured RES. -/
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {ground : GammaParameters.Base (M := M)} {k : ℕ}

def GammaGroundMeasuredRESObject.empty (hc : CanonicalStructure.IsCanonical (M := M))
    (ground : GammaParameters.Base (M := M)) (k : ℕ) : GammaGroundMeasuredRESObject hc ground k :=
  ⟨GammaGroundMeasuredRVObject.empty hc ground k, (GammaGroundRESObject.empty hc ground k).property⟩

def GammaGroundMeasuredRESObject.restrict (U : GammaGroundMeasuredRESObject hc ground k)
    (X : GammaGroundDefSet hc ground (rawRVSpace (M := M) U.obj.underlying.arity))
    (hX : X.carrier ⊆ U.obj.underlying.domain.carrier) : GammaGroundMeasuredRESObject hc ground k :=
  ⟨U.obj.restrict X hX, gammaGroundResProperty_restrict U.obj.underlying U.property X hX⟩

def GammaGroundMeasuredRESObject.coprod (U V : GammaGroundMeasuredRESObject hc ground k) :
    GammaGroundMeasuredRESObject hc ground k :=
  ⟨U.obj.coprod V.obj, GammaGroundRVObject.coprod_res U.property V.property⟩

def gammaGroundMeasuredRESPresentation (hc : CanonicalStructure.IsCanonical (M := M))
    (ground : GammaParameters.Base (M := M)) (k : ℕ) : ScissorPresentation (GammaGroundMeasuredRESObject hc ground k) where
  iso A B := Nonempty (A ≅ B)
  empty := GammaGroundMeasuredRESObject.empty hc ground k
  scissor A B D E := gammaGroundMeasuredRVScissor A.obj B.obj D.obj E.obj

abbrev GammaGroundMeasuredRESKPlus (hc : CanonicalStructure.IsCanonical (M := M))
    (ground : GammaParameters.Base (M := M)) (k : ℕ) := KPlus (gammaGroundMeasuredRESPresentation hc ground k)

def gammaGroundMeasuredRESClass (U : GammaGroundMeasuredRESObject hc ground k) : GammaGroundMeasuredRESKPlus hc ground k :=
  positiveClass (gammaGroundMeasuredRESPresentation hc ground k) U

def gammaGroundMeasuredRESToRVKPlus : GammaGroundMeasuredRESKPlus hc ground k →+ GammaGroundMeasuredRVKPlus hc ground k :=
  PositiveAdditiveGrothendieck.lift (gammaGroundMeasuredRESPresentation hc ground k) {
    toFun U := gammaGroundMeasuredRVClass U.obj
    iso := fun h => by
      obtain ⟨e⟩ := h
      exact gammaGroundMeasuredRVClass_iso (gammaGroundMeasuredResProperty.ι.mapIso e)
    empty := gammaGroundMeasuredRVClass_empty
    scissor := fun h => positiveClass_scissor (gammaGroundMeasuredRVPresentation hc ground k) h }

@[simp] theorem gammaGroundMeasuredRESToRVKPlus_class (U : GammaGroundMeasuredRESObject hc ground k) :
    gammaGroundMeasuredRESToRVKPlus (gammaGroundMeasuredRESClass U) = gammaGroundMeasuredRVClass U.obj :=
  PositiveAdditiveGrothendieck.lift_of _ _ U

theorem gammaGroundMeasuredRESClass_iso {U V : GammaGroundMeasuredRESObject hc ground k} (e : U ≅ V) :
    gammaGroundMeasuredRESClass U = gammaGroundMeasuredRESClass V := positiveClass_iso (gammaGroundMeasuredRESPresentation hc ground k) ⟨e⟩

@[simp] theorem gammaGroundMeasuredRESClass_empty : gammaGroundMeasuredRESClass (GammaGroundMeasuredRESObject.empty hc ground k) = 0 :=
  positiveClass_empty (gammaGroundMeasuredRESPresentation hc ground k)

end DiamondIntegral.Section3
