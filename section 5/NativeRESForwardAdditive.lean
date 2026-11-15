import «section 5».RESForwardBijections
import «section 5».NativeRESClasses

/-! The actual native positive RES presentation maps additively to the
raw diagonal constructible ring. All scissor and isomorphism relations
are discharged from actual domains over the empty-Gamma original base. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace DiamondIntegral.Section5.PuiseuxOriginal
open Classical FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry
open DiamondIntegral.Section3
local instance nativeRESForwardAdditiveStructure : LRV.Structure Carrier := canonicalInterpret
attribute [local instance] FirstOrder.Ring.compatibleRingOfRing
variable [Carrier ⊨ Axioms.ACVF]

abbrev originalPuiseuxGround : GammaParameters.Base (M := Carrier) :=
  EmptyGammaGround.base {c | baseCarrier c}

def nativeForwardValue {k : ℕ}
    (U : GammaGroundRESObject canonicalInterpret_isCanonical originalPuiseuxGround k) : DiagonalConstructible.Ring :=
  forwardRESValue (originalDomain canonicalInterpret_isCanonical U)
    (originalDomain_finite_values canonicalInterpret_isCanonical U)

theorem nativeForwardValue_bijection {k l : ℕ}
    (U : GammaGroundRESObject canonicalInterpret_isCanonical originalPuiseuxGround k)
    (V : GammaGroundRESObject canonicalInterpret_isCanonical originalPuiseuxGround l)
    (f : GammaGroundBijection U.obj.domain V.obj.domain) : nativeForwardValue U = nativeForwardValue V :=
  forwardRESValue_bijection _ _ _ _ (EmptyGammaGround.bijectionToReal canonicalInterpret_isCanonical f)

theorem nativeForwardValue_empty (k : ℕ) :
    nativeForwardValue (GammaGroundRESObject.empty canonicalInterpret_isCanonical originalPuiseuxGround k) = 0 :=
  forwardRESValue_empty _ _ rfl

theorem nativeForwardValue_cut {k : ℕ}
    (U : GammaGroundRESObject canonicalInterpret_isCanonical originalPuiseuxGround k)
    (X : GammaGroundDefSet canonicalInterpret_isCanonical originalPuiseuxGround (rawRVSpace (M := Carrier) U.obj.arity))
    (hX : X.carrier ⊆ U.obj.domain.carrier) :
    nativeForwardValue (U.restrict X hX) +
      nativeForwardValue (U.restrict (U.obj.domain.sdiff X) (fun _ h => h.1)) = nativeForwardValue U :=
  (forwardRESValue_scissor (originalDomain canonicalInterpret_isCanonical U)
    (originalDomain canonicalInterpret_isCanonical (U.restrict X hX))
    (originalDomain canonicalInterpret_isCanonical (U.restrict (U.obj.domain.sdiff X) (fun _ h => h.1)))
    _ _ _ hX rfl).symm

theorem nativeForwardValue_scissor {k : ℕ}
    (A B D E : GammaGroundRESObject canonicalInterpret_isCanonical originalPuiseuxGround k)
    (h : gammaGroundRVScissor A.obj B.obj D.obj E.obj) :
    nativeForwardValue A + nativeForwardValue B = nativeForwardValue D + nativeForwardValue E := by
  obtain ⟨W, X, hX, hA, hB, hD, hE⟩ := h
  subst W
  have ha : A = D.restrict X hX := by apply ObjectProperty.FullSubcategory.ext; exact hA
  have hb : B = D.restrict (D.obj.domain.sdiff X) (fun _ h => h.1) := by
    apply ObjectProperty.FullSubcategory.ext
    exact hB
  have he : E = GammaGroundRESObject.empty canonicalInterpret_isCanonical originalPuiseuxGround k := by
    apply ObjectProperty.FullSubcategory.ext
    exact hE
  rw [ha, hb, he, nativeForwardValue_empty, add_zero]
  exact nativeForwardValue_cut D X hX

def nativeForwardComponent (k : ℕ) :
    GammaGroundRESKPlus canonicalInterpret_isCanonical originalPuiseuxGround k →+ DiagonalConstructible.Ring :=
  PositiveAdditiveGrothendieck.lift (gammaGroundRESPresentation canonicalInterpret_isCanonical originalPuiseuxGround k) {
    toFun := nativeForwardValue
    iso := fun h => by obtain ⟨e⟩ := h; exact nativeForwardValue_bijection _ _ e.hom.hom
    empty := nativeForwardValue_empty k
    scissor := fun h => nativeForwardValue_scissor _ _ _ _ h }

theorem nativeForwardComponent_class {k : ℕ}
    (U : GammaGroundRESObject canonicalInterpret_isCanonical originalPuiseuxGround k) :
    nativeForwardComponent k (gammaGroundRESClass U) = nativeForwardValue U :=
  PositiveAdditiveGrothendieck.lift_of _ _ U

def nativeForwardPositive :
    GammaGroundRESDirectSum canonicalInterpret_isCanonical originalPuiseuxGround →+ DiagonalConstructible.Ring :=
  DirectSum.toAddMonoid (fun k => nativeForwardComponent k)

theorem nativeForwardPositive_class {k : ℕ}
    (U : GammaGroundRESObject canonicalInterpret_isCanonical originalPuiseuxGround k) :
    nativeForwardPositive (gammaGroundRESDirectSumClass U) = nativeForwardValue U := by
  rw [gammaGroundRESDirectSumClass, nativeForwardPositive, DirectSum.toAddMonoid_of,
    nativeForwardComponent_class]

end DiamondIntegral.Section5.PuiseuxOriginal
