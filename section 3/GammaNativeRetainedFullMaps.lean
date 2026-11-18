import «section 3».GammaNativeAlmostEverywhereJacobians
import «section 3».GammaHeadMeasuredFibres
import «section 3».GammaHeadRetainedForms
import IntegrationSection6.GammaPermutedFibrePresentations

/-! Native Jacobian-one maps transport arbitrary total retained Gamma
forms. The checked intrinsic exceptional-set descent supplies the
original-ground generic Jacobian required by full measured comparison. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4500000
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5 SpecialTransformations.Section9
open IntegrationInACVF.Section5 IntegrationInACVF.Section6 IntegrationInACVF.Section7
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] [CharZero (Section2.VF M)]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (Section2.VF M) G]

def gammaTotalRVCoordinateForm {a b : ℕ} (ρ : Fin a → Fin b)
    (ω : GammaGroundVolumeForm hc B (GammaGroundDefSet.univ hc B (rawRVSpace (M := M) a))) :
    GammaGroundVolumeForm hc B (GammaGroundDefSet.univ hc B (rawRVSpace (M := M) b)) :=
  ω.comp ((gammaGroundRVSelectCoordinates ρ (GammaGroundDefSet.univ hc B (rawRVSpace b))).corestrict
    (fun _ => Set.mem_univ _))

def gammaNativeRetainedFullMap
    (C : BaseContext M) (hBC : B.real ⊆ (C.base : Set M))
    (hv : ∀ x y : Section2.VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    {n a b : ℕ} (hn : 0 < n)
    {A : SpecialTransformations.Section5.DefSet (M := M) (C.base : Set M) n a}
    {D : SpecialTransformations.Section5.DefSet (M := M) (C.base : Set M) n b}
    (hA : GammaSetDefinable B (carrier A)) (hD : GammaSetDefinable B (carrier D))
    (hfinA : ∀ x : Fin n → VF (M := M), {r | (x,r) ∈ carrier A}.Finite)
    (hfinD : ∀ x : Fin n → VF (M := M), {r | (x,r) ∈ carrier D}.Finite)
    (ω : GammaGroundVolumeForm hc B (GammaGroundDefSet.univ hc B (rawRVSpace (M := M) a)))
    (η : GammaGroundVolumeForm hc B (GammaGroundDefSet.univ hc B (rawRVSpace (M := M) b)))
    (f : SpecialTransformations.Section5.Map A D) (hf : Function.Bijective f)
    (hF : GammaGraphDefinable B (pointMapGraph f))
    (hJ : VFAlmostEverywhere (rawSpecialSet hc A)
      (fun p => HasMixedVFJacobianAt (rawSpecialMap hc f) p 1))
    (hForm : ∀ p : A, η ⟨(f p).val.2,Set.mem_univ _⟩ = ω ⟨p.val.2,Set.mem_univ _⟩) :
    GammaFullMeasuredBijection
      (gammaPointMeasuredData A hA hfinA (gammaPointRetainedForm A hA
        (GammaGroundDefSet.univ hc B (rawRVSpace a)) id (fun _ => Set.mem_univ _) ω))
      (gammaPointMeasuredData D hD hfinD (gammaPointRetainedForm D hD
        (GammaGroundDefSet.univ hc B (rawRVSpace b)) id (fun _ => Set.mem_univ _) η)) := by
  let F := Section5.nativeGammaPointBijection (hc := hc) hA hD
    (⟨Equiv.ofBijective f hf,hF⟩ : GammaIso B (carrier A) (carrier D))
  apply gammaFullMeasuredOfJacobianOne F
  · exact gammaNative_jacobian_one_of_almostEverywhere C hBC hv hn hA hD f hf hF hJ
  · intro p
    apply congrArg (fun q : GammaGroundDefSet.univ hc B (volumeGammaSpace hc) =>
      (cast (gammaCarrier hc) q.val).val)
    change ω ⟨p.val.2,Set.mem_univ _⟩ = η ⟨(F.map p).val.2,Set.mem_univ _⟩
    have h := hForm ⟨p.val,p.property⟩
    rw [Section5.nativeGammaPointBijection_apply]
    exact h.symm

theorem gammaNativeRetainedFullMap_apply
    (C : BaseContext M) (hBC : B.real ⊆ (C.base : Set M))
    (hv : ∀ x y : Section2.VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    {n a b : ℕ} (hn : 0 < n)
    {A : SpecialTransformations.Section5.DefSet (M := M) (C.base : Set M) n a}
    {D : SpecialTransformations.Section5.DefSet (M := M) (C.base : Set M) n b}
    (hA : GammaSetDefinable B (carrier A)) (hD : GammaSetDefinable B (carrier D))
    (hfinA : ∀ x : Fin n → VF (M := M), {r | (x,r) ∈ carrier A}.Finite)
    (hfinD : ∀ x : Fin n → VF (M := M), {r | (x,r) ∈ carrier D}.Finite)
    (ω : GammaGroundVolumeForm hc B (GammaGroundDefSet.univ hc B (rawRVSpace (M := M) a)))
    (η : GammaGroundVolumeForm hc B (GammaGroundDefSet.univ hc B (rawRVSpace (M := M) b)))
    (f : SpecialTransformations.Section5.Map A D) (hf : Function.Bijective f)
    (hF : GammaGraphDefinable B (pointMapGraph f))
    (hJ : VFAlmostEverywhere (rawSpecialSet hc A)
      (fun p => HasMixedVFJacobianAt (rawSpecialMap hc f) p 1))
    (hForm : ∀ p : A, η ⟨(f p).val.2,Set.mem_univ _⟩ = ω ⟨p.val.2,Set.mem_univ _⟩)
    (p : Section5.nativeGammaPointDomain (hc := hc) (carrier A) hA) :
    ((gammaNativeRetainedFullMap C hBC hv hn hA hD hfinA hfinD ω η f hf hF hJ hForm).map.map p).val =
      (f ⟨p.val,p.property⟩).val := Section5.nativeGammaPointBijection_apply hA hD _ p

end DiamondIntegral.Section3
