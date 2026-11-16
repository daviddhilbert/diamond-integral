import «section 6».ExtendedMeasuredLiftBijections
import «section 6».MixedTupleDifferentiability

/-! Full total derivatives of the actual extended map. On the selected
whole label fibre its chart is the given local chart; on every other
fibre the chart is the identity. Relative unary coordinates are retained. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section7 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n : ℕ}

def extendedLiftPoint (hc : CanonicalStructure.IsCanonical (M := M))
    (U A : MeasuredRVObject (M := M) S n)
    (D : DefSet (rawRVSpace (M := M) U.object.arity) S) (hD : D.carrier ⊆ U.object.domain.carrier)
    (χ : Map D A.object.domain) (hχ : Function.Injective χ)
    (p : rvLift (measuredRVVolumeExtension hc U A D χ hχ).object) (hp : p.val.2 ∈ D.carrier) : rvLift A.object :=
  extendedLiftPiecePullback hc U A D hD χ hχ
    ⟨p.val,(rvLift_restrict_mem_iff (measuredRVVolumeExtension hc U A D χ hχ).object D hD p.val).mpr
      ⟨p.property,hp⟩⟩

theorem extendedLiftPoint_value (hc : CanonicalStructure.IsCanonical (M := M))
    (U A : MeasuredRVObject (M := M) S n)
    (D : DefSet (rawRVSpace (M := M) U.object.arity) S) (hD : D.carrier ⊆ U.object.domain.carrier)
    (χ : Map D A.object.domain) (hχ : Function.Injective χ)
    (p : rvLift (measuredRVVolumeExtension hc U A D χ hχ).object) (hp : p.val.2 ∈ D.carrier) :
    (extendedLiftPoint hc U A D hD χ hχ p hp).val = (p.val.1,(χ ⟨p.val.2,hp⟩).val) := rfl

theorem extendedMeasuredLiftMap_derivative_on_piece (hc : CanonicalStructure.IsCanonical (M := M))
    (U : MeasuredRVObject (M := M) S n) {A B : MeasuredRVObject (M := M) S n}
    {e : MeasuredRVIso A B} (F : EverywhereMeasuredRVLift e)
    (D : DefSet (rawRVSpace (M := M) U.object.arity) S) (hD : D.carrier ⊆ U.object.domain.carrier)
    (χ : Map D A.object.domain) (hχ : Function.Injective χ)
    (p : rvLift (measuredRVVolumeExtension hc U A D χ hχ).object) (hp : p.val.2 ∈ D.carrier)
    {L : (Fin n → VF M) →ₗ[VF M] (Fin n → VF M)}
    (hL : HasMixedVFDerivativeAt F.map (extendedLiftPoint hc U A D hD χ hχ p hp) L) :
    HasMixedVFDerivativeAt (extendedMeasuredLiftMap hc U F D hD χ hχ) p L := by
  let W := measuredRVVolumeExtension hc U A D χ hχ
  let a₀ := extendedLiftPoint hc U A D hD χ hχ p hp
  obtain ⟨f,⟨ρ,hρ⟩,hDer⟩ := hL
  refine ⟨f,⟨ρ,fun x hx => ?_⟩,hDer⟩
  obtain ⟨hxA,hF⟩ := hρ x hx
  let aX : rvLift A.object := ⟨(x,a₀.val.2),hxA⟩
  have hTag : liftLabelMap A.object aX = χ ⟨p.val.2,hp⟩ := Subtype.ext rfl
  have hAVol := liftLabelMap_volume A.object aX
  rw [hTag] at hAVol
  have hWVol : W.object.value (liftLabelMap W.object p) = tupleRV x :=
    (measuredRVVolumeExtension_of_mem hc U A D χ hχ (liftLabelMap W.object p) hp).trans hAVol
  let pX : rvLift W.object := ⟨(x,p.val.2),liftLabelMap W.object p,rfl,hWVol⟩
  let p₀ : rvLift (W.object.restrict D hD) :=
    ⟨pX.val,(rvLift_restrict_mem_iff W.object D hD pX.val).mpr ⟨pX.property,hp⟩⟩
  have hφ : extendedLiftPiecePullback hc U A D hD χ hχ p₀ = aX := Subtype.ext rfl
  refine ⟨pX.property,?_⟩
  change (extendedMeasuredLiftMap hc U F D hD χ hχ pX).val = _
  rw [extendedMeasuredLiftMap_value,extendedLiftVFMap_of_piece hc U F D hD χ hχ pX p₀ rfl,hφ]
  apply Prod.ext
  · change (F.map aX).val.1 = f x
    exact congrArg (fun z : (rawMixedSpace (M := M) n B.object.arity).Carrier => z.1) hF
  · rfl

theorem extendedMeasuredLiftMap_derivative_off_piece (hc : CanonicalStructure.IsCanonical (M := M))
    (U : MeasuredRVObject (M := M) S n) {A B : MeasuredRVObject (M := M) S n}
    {e : MeasuredRVIso A B} (F : EverywhereMeasuredRVLift e)
    (D : DefSet (rawRVSpace (M := M) U.object.arity) S) (hD : D.carrier ⊆ U.object.domain.carrier)
    (χ : Map D A.object.domain) (hχ : Function.Injective χ)
    (p : rvLift (measuredRVVolumeExtension hc U A D χ hχ).object) (hp : p.val.2 ∉ D.carrier) :
    HasMixedVFDerivativeAt (extendedMeasuredLiftMap hc U F D hD χ hχ) p LinearMap.id := by
  let W := measuredRVVolumeExtension hc U A D χ hχ
  obtain ⟨ρ,hρ⟩ := exists_fixed_label_ball_in_rvLift W p
  refine ⟨fun x => x+0,⟨ρ,fun x hx => ?_⟩,hasVFDerivativeAt_affine LinearMap.id 0 p.val.1⟩
  let q : rvLift W.object := ⟨(x,p.val.2),hρ x hx⟩
  refine ⟨q.property,?_⟩
  change (extendedMeasuredLiftMap hc U F D hD χ hχ q).val = _
  rw [extendedMeasuredLiftMap_value,extendedLiftVFMap_of_not_mem hc U F D hD χ hχ q hp]
  apply Prod.ext
  · change x = x+0
    rw [add_zero]
  · rfl

theorem extendedMeasuredLiftMap_differentiable (hc : CanonicalStructure.IsCanonical (M := M))
    (U : MeasuredRVObject (M := M) S n) {A B : MeasuredRVObject (M := M) S n}
    {e : MeasuredRVIso A B} (F : EverywhereMeasuredRVLift e)
    (D : DefSet (rawRVSpace (M := M) U.object.arity) S) (hD : D.carrier ⊆ U.object.domain.carrier)
    (χ : Map D A.object.domain) (hχ : Function.Injective χ)
    (p : rvLift (measuredRVVolumeExtension hc U A D χ hχ).object) :
    ∃ L,HasMixedVFDerivativeAt (extendedMeasuredLiftMap hc U F D hD χ hχ) p L := by
  by_cases hp : p.val.2 ∈ D.carrier
  · obtain ⟨L,hL,_⟩ := F.measure (extendedLiftPoint hc U A D hD χ hχ p hp)
    exact ⟨L,extendedMeasuredLiftMap_derivative_on_piece hc U F D hD χ hχ p hp hL⟩
  · exact ⟨LinearMap.id,extendedMeasuredLiftMap_derivative_off_piece hc U F D hD χ hχ p hp⟩

theorem extendedMeasuredLiftMap_unary (hc : CanonicalStructure.IsCanonical (M := M))
    (U : MeasuredRVObject (M := M) S n) {A B : MeasuredRVObject (M := M) S n}
    {e : MeasuredRVIso A B} (F : EverywhereMeasuredRVLift e)
    (D : DefSet (rawRVSpace (M := M) U.object.arity) S) (hD : D.carrier ⊆ U.object.domain.carrier)
    (χ : Map D A.object.domain) (hχ : Function.Injective χ) (i : Fin n) (hF : VFUnaryRelativeAt F.map i) :
    VFUnaryRelativeAt (extendedMeasuredLiftMap hc U F D hD χ hχ) i := by
  intro p j hj
  change (extendedLiftVFMap hc U F D hD χ hχ p).val j = p.val.1 j
  by_cases hp : p.val.2 ∈ D.carrier
  · let q : rvLift ((measuredRVVolumeExtension hc U A D χ hχ).object.restrict D hD) :=
      ⟨p.val,(rvLift_restrict_mem_iff (measuredRVVolumeExtension hc U A D χ hχ).object D hD p.val).mpr
        ⟨p.property,hp⟩⟩
    rw [extendedLiftVFMap_of_piece hc U F D hD χ hχ p q rfl]
    exact hF (extendedLiftPiecePullback hc U A D hD χ hχ q) j hj
  · rw [extendedLiftVFMap_of_not_mem hc U F D hD χ hχ p hp]

end DiamondIntegral.Section6
