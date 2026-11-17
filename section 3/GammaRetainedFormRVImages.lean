import «section 3».GammaHeadRetainedForms
import «section 3».GammaGroundMapImages

/-! A form depending on selected old RV labels is a form on the actual
image of all retained RV labels. This closes the head-comparison induction
under the addition of each new head label, without an RV representative
for the Gamma value. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
open IntegrationInACVF.Section5 IntegrationInACVF.Section6
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {S : Set M} {n a r : ℕ}

def gammaPointRVImage (A : DefSet (M := M) S n a) (hA : GammaSetDefinable B (carrier A)) :=
  (Section5.nativeMixedRVProjection (Section5.nativeGammaPointDomain (hc := hc) (carrier A) hA)).image

theorem gammaPointRVImage_mem (A : DefSet (M := M) S n a) (hA : GammaSetDefinable B (carrier A)) (p : A) :
    p.val.2 ∈ (gammaPointRVImage (hc := hc) A hA).carrier :=
  Set.mem_range_self (⟨p.val,p.property⟩ : Section5.nativeGammaPointDomain (hc := hc) (carrier A) hA)

def gammaPointRVImageOldLabels (A : DefSet (M := M) S n a) (hA : GammaSetDefinable B (carrier A))
    (Q : GammaGroundDefSet hc B (rawRVSpace (M := M) r)) (ν : Fin r → Fin a)
    (hLabels : ∀ p : A, p.val.2 ∘ ν ∈ Q.carrier) : GammaGroundMap (gammaPointRVImage A hA) Q :=
  (gammaGroundRVSelectCoordinates ν (gammaPointRVImage A hA)).corestrict (fun q => by
    obtain ⟨p,hp⟩ := q.property
    have he : p.val.2 = q.val := hp
    change q.val ∘ ν ∈ Q.carrier
    rw [← he]
    exact hLabels ⟨p.val,p.property⟩)

def gammaPointRVImageForm (A : DefSet (M := M) S n a) (hA : GammaSetDefinable B (carrier A))
    (Q : GammaGroundDefSet hc B (rawRVSpace (M := M) r)) (ν : Fin r → Fin a)
    (hLabels : ∀ p : A, p.val.2 ∘ ν ∈ Q.carrier) (ω : GammaGroundVolumeForm hc B Q) :=
  ω.comp (gammaPointRVImageOldLabels A hA Q ν hLabels)

theorem gammaPointRVImageForm_pointForm (A : DefSet (M := M) S n a) (hA : GammaSetDefinable B (carrier A))
    (Q : GammaGroundDefSet hc B (rawRVSpace (M := M) r)) (ν : Fin r → Fin a)
    (hLabels : ∀ p : A, p.val.2 ∘ ν ∈ Q.carrier) (ω : GammaGroundVolumeForm hc B Q) :
    gammaPointRetainedForm A hA (gammaPointRVImage A hA) id (fun p => gammaPointRVImage_mem A hA p)
      (gammaPointRVImageForm A hA Q ν hLabels ω) = gammaPointRetainedForm A hA Q ν hLabels ω := by
  apply GammaGroundMap.ext
  intro p
  rfl

end DiamondIntegral.Section3
