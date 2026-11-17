import «section 3».GammaDensityPreparation
import «section 3».GammaSurjectiveMapDescent

/-! Every mixed Gamma form factors through an actual finite tuple of RV
data over the original base. The map is obtained from a preparation's
full key; it does not select a representative of a Gamma value. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section3.GammaParameters
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] [CharZero (Section2.VF M)]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {n r : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (Section2.VF M) G]

theorem gammaDensity_RV_factorization
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (h00 : M ⊨ Axioms.ACVF00) (hr : Cardinal.mk B.real < κ)
    (hv : ∀ x y : Section2.VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (A : GammaGroundDefSet hc B (rawMixedSpace (M := M) n r))
    (ω : GammaGroundVolumeForm hc B A) :
    ∃ l : ℕ, ∃ R : GammaGroundDefSet hc B (rawRVSpace (M := M) l),
      ∃ K : GammaGroundMap A R, Function.Surjective K ∧
      ∃ η : GammaGroundVolumeForm hc B R, ∀ p, η (K p) = ω p := by
  obtain ⟨l,Y,e,_,_,hSame⟩ := gammaDensity_preparation hκ hs h00 hr hv A ω
  let K := (Section5.nativeMixedFullKeyMap Y).comp e.map
  have hSurj : Function.Surjective K.toImage := by
    rintro ⟨_,p,rfl⟩
    exact ⟨p,rfl⟩
  have hFibres : ∀ p q, K.toImage p = K.toImage q → ω p = ω q := by
    intro p q hpq
    apply Subtype.ext
    have he := congrArg (fun z : K.image => z.val) hpq
    exact hSame p q (Subtype.ext he)
  let η := gammaGroundSurjectiveDescent K.toImage hSurj ω hFibres
  exact ⟨n+(l+r),K.image,K.toImage,hSurj,η,
    gammaGroundSurjectiveDescent_apply K.toImage hSurj ω hFibres⟩

end DiamondIntegral.Section3
