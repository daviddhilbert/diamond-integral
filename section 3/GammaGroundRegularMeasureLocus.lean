import «section 3».GammaGroundJacobianGraph
import «section 3».GammaGroundTopForms
import «section 3».GammaGroundEqualizers

/-! A same-ground definable locus where a full fixed-label derivative
satisfies the actual Gamma volume equation. -/
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

def gammaGroundMeasureJacobianLeft (hn : 0 < n) (f : GammaGroundMap A B)
    (ω : GammaGroundVolumeForm hc ground A) : GammaGroundTopForm hc ground (gammaGroundFullJacobianGraph hn f) :=
  ω.toTop.comp (gammaGroundJacobianSource hn f)

def gammaGroundMeasureJacobianRight (hn : 0 < n) (f : GammaGroundMap A B)
    (σ : GammaGroundVolumeForm hc ground B) : GammaGroundTopForm hc ground (gammaGroundFullJacobianGraph hn f) :=
  GammaGroundTopForm.mul (σ.toTop.comp (f.comp (gammaGroundJacobianSource hn f)))
    (gammaGroundJacobianScalar hn f).valuation

def gammaGroundRegularMeasureLocus (hn : 0 < n) (f : GammaGroundMap A B)
    (ω : GammaGroundVolumeForm hc ground A) (σ : GammaGroundVolumeForm hc ground B) :
    GammaGroundDefSet hc ground (rawMixedSpace (M := M) n r) :=
  ((gammaGroundJacobianSource hn f).restrict
    ((gammaGroundMeasureJacobianLeft hn f ω).equalizer_subset (gammaGroundMeasureJacobianRight hn f σ))).image

theorem mem_gammaGroundRegularMeasureLocus (hn : 0 < n) (f : GammaGroundMap A B)
    (ω : GammaGroundVolumeForm hc ground A) (σ : GammaGroundVolumeForm hc ground B)
    (x : (rawMixedSpace (M := M) n r).Carrier) :
    x ∈ (gammaGroundRegularMeasureLocus hn f ω σ).carrier ↔
      ∃ p : A, p.val = x ∧ ∃ L : (Fin n → VFType (M := M)) →ₗ[VFType (M := M)] (Fin n → VFType (M := M)),
        HasMixedVFDerivativeAt f p L ∧ (gammaGroundFormValue ω p).val =
          (gammaGroundFormValue σ (f p)).val * Values.vfValueHom (LinearMap.toMatrix' L).det := by
  constructor
  · rintro ⟨e, he⟩
    obtain ⟨z, hz, hEq⟩ := e.property
    let p := gammaGroundJacobianSource hn f z
    obtain ⟨p0, hp0, L, hL, hdet⟩ := z.property
    have hp : p = p0 := Subtype.ext hp0.symm
    have hpx : p.val = x := (congrArg Prod.fst hz).trans he
    refine ⟨p, hpx, L, hp.symm ▸ hL, ?_⟩
    change (gammaGroundFormValue ω p).val =
      (gammaGroundFormValue σ (f p)).val * Values.vfValueHom (z.val.2 0) at hEq
    rwa [hdet] 
  · rintro ⟨p, hp, L, hL, hw⟩
    let z : gammaGroundFullJacobianGraph hn f :=
      ⟨(p.val, fun _ => (LinearMap.toMatrix' L).det), p, rfl, L, hL, rfl⟩
    have hEq : (gammaGroundMeasureJacobianLeft hn f ω z).val =
        (gammaGroundMeasureJacobianRight hn f σ z).val := hw
    exact ⟨⟨z.val, z, rfl, hEq⟩, hp⟩

theorem gammaGroundRegularMeasureLocus_subset (hn : 0 < n) (f : GammaGroundMap A B)
    (ω : GammaGroundVolumeForm hc ground A) (σ : GammaGroundVolumeForm hc ground B) :
    (gammaGroundRegularMeasureLocus hn f ω σ).carrier ⊆ A.carrier := by
  intro x hx
  obtain ⟨p, hp, _⟩ := (mem_gammaGroundRegularMeasureLocus hn f ω σ x).mp hx
  exact hp ▸ p.property

end DiamondIntegral.Section3
