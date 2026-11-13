import «section 3».GammaGroundRVCategories
import «section 3».Grothendieck
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

def GammaGroundRVObject.empty (hc : CanonicalStructure.IsCanonical (M := M)) (ground : GammaParameters.Base (M := M)) (k : ℕ) : GammaGroundRVObject hc ground k where
  arity := 0
  domain := GammaGroundDefSet.empty hc ground (rawRVSpace 0)
  volume := GammaGroundMap.ofReal (Map.empty (rawRVSpace 0) (rawRVSpace k) ground.real)
  finite t := Set.finite_empty.subset (fun a _ => False.elim a.property)
  nonzero a := False.elim a.property

def GammaGroundRVObject.restrict (U : GammaGroundRVObject hc ground k)
    (X : GammaGroundDefSet hc ground (rawRVSpace (M := M) U.arity))
    (hX : X.carrier ⊆ U.domain.carrier) : GammaGroundRVObject hc ground k where
  arity := U.arity
  domain := X
  volume := U.volume.restrict hX
  finite := U.finite.comp (GammaGroundMap.finiteFibres_of_injective (by
    intro a b he
    exact Subtype.ext (congrArg (fun y : U.domain => y.val) he)))
  nonzero a := U.nonzero (GammaGroundMap.inclusion hX a)

def gammaGroundRVScissor (A B D E : GammaGroundRVObject hc ground k) : Prop :=
  ∃ U : GammaGroundRVObject hc ground k,
    ∃ X : GammaGroundDefSet hc ground (rawRVSpace (M := M) U.arity),
    ∃ hX : X.carrier ⊆ U.domain.carrier,
      A = U.restrict X hX ∧ B = U.restrict (U.domain.sdiff X) (fun _ h => h.1) ∧
      D = U ∧ E = GammaGroundRVObject.empty hc ground k

def gammaGroundRVPresentation (hc : CanonicalStructure.IsCanonical (M := M)) (ground : GammaParameters.Base (M := M)) (k : ℕ) :
    ScissorPresentation (GammaGroundRVObject hc ground k) where
  iso A B := Nonempty (A ≅ B)
  empty := GammaGroundRVObject.empty hc ground k
  scissor := gammaGroundRVScissor

abbrev GammaGroundRVKPlus (hc : CanonicalStructure.IsCanonical (M := M)) (ground : GammaParameters.Base (M := M)) (k : ℕ) := KPlus (gammaGroundRVPresentation hc ground k)

def gammaGroundRVClass (U : GammaGroundRVObject hc ground k) : GammaGroundRVKPlus hc ground k := positiveClass (gammaGroundRVPresentation hc ground k) U

@[simp] theorem gammaGroundRVClass_empty : gammaGroundRVClass (GammaGroundRVObject.empty hc ground k) = 0 :=
  positiveClass_empty (gammaGroundRVPresentation hc ground k)

theorem gammaGroundRVClass_iso {U V : GammaGroundRVObject hc ground k} (e : U ≅ V) : gammaGroundRVClass U = gammaGroundRVClass V :=
  positiveClass_iso (gammaGroundRVPresentation hc ground k) ⟨e⟩

theorem gammaGroundRVClass_scissor (U : GammaGroundRVObject hc ground k)
    (X : GammaGroundDefSet hc ground (rawRVSpace (M := M) U.arity))
    (hX : X.carrier ⊆ U.domain.carrier) :
    gammaGroundRVClass (U.restrict X hX) + gammaGroundRVClass (U.restrict (U.domain.sdiff X) (fun _ h => h.1)) = gammaGroundRVClass U := by
  have h := positiveClass_scissor (gammaGroundRVPresentation hc ground k) ⟨U, X, hX, rfl, rfl, rfl, rfl⟩
  change gammaGroundRVClass _ + gammaGroundRVClass _ = gammaGroundRVClass _ + gammaGroundRVClass _ at h
  simpa only [gammaGroundRVClass_empty, add_zero] using h


end DiamondIntegral.Section3
