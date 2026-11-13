import «section 3».GammaGroundVFCategories
import «section 3».Grothendieck

set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] [TopologicalSpace (Section2.VF M)]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {ground : GammaParameters.Base (M := M)} {k : ℕ}

def GammaGroundVFObject.empty (hc : CanonicalStructure.IsCanonical (M := M))
    (ground : GammaParameters.Base (M := M)) (k : ℕ) : GammaGroundVFObject hc ground k where
  vfArity := 0
  rvArity := 0
  domain := GammaGroundDefSet.empty hc ground (rawMixedSpace 0 0)
  dimension := by
    change Section2.vfDimension (∅ : Set (Section2.Mixed M 0 0)) ≤ (k : WithBot ℕ)
    rw [Section2.vfDimension_empty]
    exact bot_le
  finite _ := Set.finite_empty

def gammaGroundVFScissor (A B D E : GammaGroundVFObject hc ground k) : Prop :=
  ∃ U : GammaGroundVFObject hc ground k,
    ∃ X : GammaGroundDefSet hc ground (rawMixedSpace (M := M) U.vfArity U.rvArity),
    ∃ hX : X.carrier ⊆ U.domain.carrier,
      A = U.restrict X hX ∧ B = U.restrict (U.domain.sdiff X) (fun _ h => h.1) ∧
      D = U ∧ E = GammaGroundVFObject.empty hc ground k

def gammaGroundVFPresentation (hc : CanonicalStructure.IsCanonical (M := M))
    (ground : GammaParameters.Base (M := M)) (k : ℕ) : ScissorPresentation (GammaGroundVFObject hc ground k) where
  iso A B := Nonempty (A ≅ B)
  empty := GammaGroundVFObject.empty hc ground k
  scissor := gammaGroundVFScissor

abbrev GammaGroundVFKPlus (hc : CanonicalStructure.IsCanonical (M := M))
    (ground : GammaParameters.Base (M := M)) (k : ℕ) := KPlus (gammaGroundVFPresentation hc ground k)

def gammaGroundVFClass (U : GammaGroundVFObject hc ground k) : GammaGroundVFKPlus hc ground k :=
  positiveClass (gammaGroundVFPresentation hc ground k) U

@[simp] theorem gammaGroundVFClass_empty : gammaGroundVFClass (GammaGroundVFObject.empty hc ground k) = 0 :=
  positiveClass_empty (gammaGroundVFPresentation hc ground k)

theorem gammaGroundVFClass_iso {U V : GammaGroundVFObject hc ground k} (e : U ≅ V) :
    gammaGroundVFClass U = gammaGroundVFClass V := positiveClass_iso (gammaGroundVFPresentation hc ground k) ⟨e⟩

theorem gammaGroundVFClass_scissor (U : GammaGroundVFObject hc ground k)
    (X : GammaGroundDefSet hc ground (rawMixedSpace (M := M) U.vfArity U.rvArity))
    (hX : X.carrier ⊆ U.domain.carrier) :
    gammaGroundVFClass (U.restrict X hX) +
      gammaGroundVFClass (U.restrict (U.domain.sdiff X) (fun _ h => h.1)) = gammaGroundVFClass U := by
  have h := positiveClass_scissor (gammaGroundVFPresentation hc ground k) ⟨U, X, hX, rfl, rfl, rfl, rfl⟩
  change gammaGroundVFClass _ + gammaGroundVFClass _ = gammaGroundVFClass _ + gammaGroundVFClass _ at h
  simpa only [gammaGroundVFClass_empty, add_zero] using h

end DiamondIntegral.Section3
