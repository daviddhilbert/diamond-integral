import «section 3».GammaGroundRESClosure
import «section 3».GammaGroundRVIsomorphismClasses

/-! Actual finite-value-support RES scissors and their forgetful map
at the original complete Gamma ground. -/
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {ground : GammaParameters.Base (M := M)} {k l : ℕ}

theorem gammaGroundResProperty_restrict (U : GammaGroundRVObject hc ground k) (hU : gammaGroundResProperty U)
    (X : GammaGroundDefSet hc ground (rawRVSpace (M := M) U.arity)) (hX : X.carrier ⊆ U.domain.carrier) :
    gammaGroundResProperty (U.restrict X hX) := by
  apply hU.subset
  rintro γ ⟨t, ht, rfl⟩
  exact ⟨t, hX ht, rfl⟩

def GammaGroundRESObject.empty (hc : CanonicalStructure.IsCanonical (M := M))
    (ground : GammaParameters.Base (M := M)) (k : ℕ) : GammaGroundRESObject hc ground k :=
  ⟨GammaGroundRVObject.empty hc ground k, Set.finite_empty.image _⟩

def GammaGroundRESObject.restrict (U : GammaGroundRESObject hc ground k)
    (X : GammaGroundDefSet hc ground (rawRVSpace (M := M) U.obj.arity)) (hX : X.carrier ⊆ U.obj.domain.carrier) :
    GammaGroundRESObject hc ground k := ⟨U.obj.restrict X hX, gammaGroundResProperty_restrict U.obj U.property X hX⟩

def GammaGroundRESObject.product (U : GammaGroundRESObject hc ground k) (V : GammaGroundRESObject hc ground l) :
    GammaGroundRESObject hc ground (k + l) := ⟨U.obj.product V.obj, GammaGroundRVObject.product_res U.property V.property⟩

def GammaGroundRESObject.coprod (U V : GammaGroundRESObject hc ground k) : GammaGroundRESObject hc ground k :=
  ⟨U.obj.coprod V.obj, GammaGroundRVObject.coprod_res U.property V.property⟩

def gammaGroundRESPresentation (hc : CanonicalStructure.IsCanonical (M := M))
    (ground : GammaParameters.Base (M := M)) (k : ℕ) : ScissorPresentation (GammaGroundRESObject hc ground k) where
  iso A B := Nonempty (A ≅ B)
  empty := GammaGroundRESObject.empty hc ground k
  scissor A B D E := gammaGroundRVScissor A.obj B.obj D.obj E.obj

abbrev GammaGroundRESKPlus (hc : CanonicalStructure.IsCanonical (M := M))
    (ground : GammaParameters.Base (M := M)) (k : ℕ) := KPlus (gammaGroundRESPresentation hc ground k)

def gammaGroundRESClass (U : GammaGroundRESObject hc ground k) : GammaGroundRESKPlus hc ground k :=
  positiveClass (gammaGroundRESPresentation hc ground k) U

def gammaGroundRESToRVKPlus : GammaGroundRESKPlus hc ground k →+ GammaGroundRVKPlus hc ground k :=
  PositiveAdditiveGrothendieck.lift (gammaGroundRESPresentation hc ground k) {
    toFun U := gammaGroundRVClass U.obj
    iso := fun h => by
      obtain ⟨e⟩ := h
      exact gammaGroundRVClass_iso (gammaGroundResProperty.ι.mapIso e)
    empty := gammaGroundRVClass_empty
    scissor := fun h => positiveClass_scissor (gammaGroundRVPresentation hc ground k) h }

@[simp] theorem gammaGroundRESToRVKPlus_class (U : GammaGroundRESObject hc ground k) :
    gammaGroundRESToRVKPlus (gammaGroundRESClass U) = gammaGroundRVClass U.obj := PositiveAdditiveGrothendieck.lift_of _ _ U

theorem gammaGroundRESClass_iso {U V : GammaGroundRESObject hc ground k} (e : U ≅ V) :
    gammaGroundRESClass U = gammaGroundRESClass V := positiveClass_iso (gammaGroundRESPresentation hc ground k) ⟨e⟩

@[simp] theorem gammaGroundRESClass_empty : gammaGroundRESClass (GammaGroundRESObject.empty hc ground k) = 0 :=
  positiveClass_empty (gammaGroundRESPresentation hc ground k)

end DiamondIntegral.Section3
