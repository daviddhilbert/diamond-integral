import «section 3».GammaGroundDerivativeFormula
import «section 3».GammaGroundRawDescent
import «section 3».GammaGroundMapImages

/-! The full fixed-label Jacobian relation is definable over the
original Gamma ground, with the determinant left as a VF coordinate. -/
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {ground : GammaParameters.Base (M := M)}
variable {n r s : ℕ}
variable {A : GammaGroundDefSet hc ground (rawMixedSpace (M := M) n r)}
variable {B : GammaGroundDefSet hc ground (rawMixedSpace (M := M) n s)}

def gammaGroundFullJacobianRelation (f : GammaGroundMap A B) :
    Set ((rawMixedSpace (M := M) n r).prod (rawVFSpace 1)).Carrier :=
  {z | ∃ p : A, p.val = z.1 ∧ ∃ L : (Fin n → VFType (M := M)) →ₗ[VFType (M := M)] (Fin n → VFType (M := M)),
    HasMixedVFDerivativeAt f p L ∧ (LinearMap.toMatrix' L).det = z.2 0}

theorem gammaGroundFullJacobianRelation_definable (hn : 0 < n) (f : GammaGroundMap A B) :
    GammaGroundDefinable hc ground ((rawMixedSpace (M := M) n r).prod (rawVFSpace 1))
      (gammaGroundFullJacobianRelation f) := by
  apply GammaGroundDefinable.of_real_codes
  apply (GammaGroundDerivativeLogic.mixedJacobianCodes_definable hn f).congr
  intro z
  constructor
  · rintro ⟨p, hp, L, hL, hJ⟩
    have hx : z ∘ Sum.inl ∈ (rawMixedSpace (M := M) n r).domain := hp ▸ mixedValues_mem_domain p.val
    have hj : z ∘ Sum.inr ∈ (rawVFSpace (M := M) 1).domain := by
      refine ⟨fun _ => (LinearMap.toMatrix' L).det, ?_⟩
      funext i
      fin_cases i
      exact hJ
    have hp' : p.val = (rawMixedSpace (M := M) n r).decode ⟨z ∘ Sum.inl, hx⟩ :=
      mixedValues_injective (hp.trans (mixedValues_decode (n := n) (r := r) ⟨z ∘ Sum.inl, hx⟩).symm)
    have hJ' : (LinearMap.toMatrix' L).det = (rawVFSpace (M := M) 1).decode ⟨z ∘ Sum.inr, hj⟩ 0 := by
      apply Subtype.ext
      exact hJ.trans (congrFun (vfValues_decode ⟨z ∘ Sum.inr, hj⟩) 0).symm
    exact ⟨⟨hx, hj⟩, p, hp', L, hL, hJ'⟩
  · rintro ⟨⟨hx, hj⟩, p, hp, L, hL, hdet⟩
    refine ⟨p, (congrArg mixedValues hp).trans (mixedValues_decode _), L, hL, ?_⟩
    exact (congrArg Subtype.val hdet).trans (congrFun (vfValues_decode ⟨z ∘ Sum.inr, hj⟩) 0)

def gammaGroundFullJacobianGraph (hn : 0 < n) (f : GammaGroundMap A B) :
    GammaGroundDefSet hc ground ((rawMixedSpace (M := M) n r).prod (rawVFSpace 1)) :=
  ⟨gammaGroundFullJacobianRelation f, gammaGroundFullJacobianRelation_definable hn f⟩

def gammaGroundJacobianSource (hn : 0 < n) (f : GammaGroundMap A B) :
    GammaGroundMap (gammaGroundFullJacobianGraph hn f) A :=
  GammaGroundMap.ofGlobal _ A (universalProductFst _ _ ground.real) (by
    intro z
    obtain ⟨p, hp, hL⟩ := z.property
    change z.val.1 ∈ A.carrier
    exact hp ▸ p.property)

def gammaGroundJacobianScalar (hn : 0 < n) (f : GammaGroundMap A B) :
    GammaGroundMap (gammaGroundFullJacobianGraph hn f) (GammaGroundDefSet.univ hc ground (rawVFSpace 1)) :=
  GammaGroundMap.ofGlobal _ _ (universalProductSnd _ _ ground.real) (fun _ => Set.mem_univ _)

def gammaGroundDifferentiabilityLocus (hn : 0 < n) (f : GammaGroundMap A B) :
    GammaGroundDefSet hc ground (rawMixedSpace (M := M) n r) := (gammaGroundJacobianSource hn f).image

theorem mem_gammaGroundDifferentiabilityLocus (hn : 0 < n) (f : GammaGroundMap A B)
    (x : (rawMixedSpace (M := M) n r).Carrier) :
    x ∈ (gammaGroundDifferentiabilityLocus hn f).carrier ↔
      ∃ p : A, p.val = x ∧ ∃ L : (Fin n → VFType (M := M)) →ₗ[VFType (M := M)] (Fin n → VFType (M := M)),
        HasMixedVFDerivativeAt f p L := by
  constructor
  · rintro ⟨z, hz⟩
    obtain ⟨p, hp, L, hL, hdet⟩ := z.property
    exact ⟨p, hp.trans hz, L, hL⟩
  · rintro ⟨p, hp, L, hL⟩
    exact ⟨⟨(p.val, fun _ => (LinearMap.toMatrix' L).det), p, rfl, L, hL, rfl⟩, hp⟩

end DiamondIntegral.Section3
