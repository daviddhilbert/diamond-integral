import «section 6».UnaryActiveLabelFiniteness
import «section 6».ZeroCenteredPullbacks
import «section 6».CentripetalProgramRealizations

/-! The pullback and finite-RV-fibre properties used in the unary trace
argument hold after every actual finite special covariant chain. They
are consequences of the permitted constructors, not additional trace
assumptions on intermediate objects. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2

namespace DiamondIntegral.Section6.SpecialCovariantChain

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {r s : ℕ} {S : Set M}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]
variable {A : DefSet (rawMixedSpace (M := M) 1 r) S}
variable {B : DefSet (rawMixedSpace (M := M) 1 s) S} {f : Map A B}

theorem unary_target_rvPullback (h : SpecialCovariantChain (G := G) A B f)
    (hA : IsRVPullback A.carrier) : IsRVPullback B.carrier := by
  induction h with
  | identity => exact hA
  | regularize A hA hVF => exact regularization_rvPullback A hA
  | centripetal A D => exact D.unary_image_rvPullback hA
  | zeroCentered A D => exact D.image_rvPullback hA
  | comp hf hg ihf ihg => exact ihg (ihf hA)

theorem unary_target_finite_rv_fibers (h : SpecialCovariantChain (G := G) A B f)
    (hc : CanonicalStructure.IsCanonical (M := M)) (h00 : M ⊨ Axioms.ACVF00)
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (hsmall : Cardinal.mk S < κ)
    (hFin : ∀ x : Fin 1 → VF M, {u : Fin r → RVInfinity M | (x,u) ∈ A.carrier}.Finite) :
    ∀ y : Fin 1 → VF M, {v : Fin s → RVInfinity M | (y,v) ∈ B.carrier}.Finite :=
  finite_rv_fibers_of_bijective hc h00 hκ hs hsmall f (h.bijective h00) hFin

end DiamondIntegral.Section6.SpecialCovariantChain
