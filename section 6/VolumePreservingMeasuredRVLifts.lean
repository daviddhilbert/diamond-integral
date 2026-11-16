import «section 6».RVJacobianLifting
import «section 6».MeasuredRVReindexingTransfer

/-! A volume-preserving label isomorphism lifts by keeping the entire
VF tuple fixed. Its full derivative is the identity and the measured
Gamma identity holds everywhere, including degree zero. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section7 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n : ℕ}

def volumePreservingRVLift {U V : MeasuredRVObject (M := M) S n} (e : MeasuredRVIso U V)
    (hVol : ∀ u,V.object.value (e.iso.hom.map u) = U.object.value u) :
    Map (rvLift U.object) (rvLift V.object) :=
  ((Map.fst (rawVFSpace (M := M) n) (rawRVSpace U.object.arity) S (rvLift U.object)).pair
    (e.iso.hom.map.comp (liftLabelMap U.object))).corestrict (fun p =>
      ⟨e.iso.hom.map (liftLabelMap U.object p),rfl,(hVol _).trans (liftLabelMap_volume U.object p)⟩)

theorem volumePreservingRVLift_value {U V : MeasuredRVObject (M := M) S n} (e : MeasuredRVIso U V)
    (hVol : ∀ u,V.object.value (e.iso.hom.map u) = U.object.value u) (p : rvLift U.object) :
    (volumePreservingRVLift e hVol p).val = (p.val.1,(e.iso.hom.map (liftLabelMap U.object p)).val) := rfl

theorem volumePreservingRVLift_label {U V : MeasuredRVObject (M := M) S n} (e : MeasuredRVIso U V)
    (hVol : ∀ u,V.object.value (e.iso.hom.map u) = U.object.value u) (p : rvLift U.object) :
    liftLabelMap V.object (volumePreservingRVLift e hVol p) = e.iso.hom.map (liftLabelMap U.object p) :=
  Subtype.ext rfl

theorem volumePreservingRVLift_bijective {U V : MeasuredRVObject (M := M) S n} (e : MeasuredRVIso U V)
    (hVol : ∀ u,V.object.value (e.iso.hom.map u) = U.object.value u) :
    Function.Bijective (volumePreservingRVLift e hVol) := by
  constructor
  · intro p q h
    apply Subtype.ext
    apply Prod.ext
    · exact congrArg (fun z : rvLift V.object => z.val.1) h
    · have he : e.iso.hom.map (liftLabelMap U.object p) = e.iso.hom.map (liftLabelMap U.object q) :=
        Subtype.ext (congrArg (fun z : rvLift V.object => z.val.2) h)
      exact congrArg Subtype.val ((rvIso_map_bijective e.iso).1 he)
  · intro q
    let u := e.iso.inv.map (liftLabelMap V.object q)
    have hTag : e.iso.hom.map u = liftLabelMap V.object q := rvIso_apply_inv e.iso _
    have hU : U.object.value u = tupleRV q.val.1 := by
      rw [← hVol u,hTag]
      exact liftLabelMap_volume V.object q
    let p : rvLift U.object := ⟨(q.val.1,u.val),u,rfl,hU⟩
    have hp : liftLabelMap U.object p = u := Subtype.ext rfl
    refine ⟨p,Subtype.ext ?_⟩
    rw [volumePreservingRVLift_value,hp,hTag]
    rfl

theorem volumePreservingRVLift_derivative {U V : MeasuredRVObject (M := M) S n} (e : MeasuredRVIso U V)
    (hVol : ∀ u,V.object.value (e.iso.hom.map u) = U.object.value u) (p : rvLift U.object) :
    HasMixedVFDerivativeAt (volumePreservingRVLift e hVol) p LinearMap.id := by
  obtain ⟨ρ,hρ⟩ := exists_fixed_label_ball_in_rvLift U p
  refine ⟨fun x => x+0,⟨ρ,fun x hx => ?_⟩,hasVFDerivativeAt_affine LinearMap.id 0 p.val.1⟩
  refine ⟨hρ x hx,?_⟩
  rw [volumePreservingRVLift_value,volumePreservingRVLift_value]
  apply Prod.ext
  · change x = x+0
    rw [add_zero]
  · apply congrArg (fun u : U.object.domain => (e.iso.hom.map u).val)
    apply Subtype.ext
    rfl

def volumePreservingMeasuredRVLift {U V : MeasuredRVObject (M := M) S n} (e : MeasuredRVIso U V)
    (hVol : ∀ u,V.object.value (e.iso.hom.map u) = U.object.value u) : EverywhereMeasuredRVLift e where
  map := volumePreservingRVLift e hVol
  bijective := volumePreservingRVLift_bijective e hVol
  labels p := ⟨liftLabelMap U.object p,rfl,rfl⟩
  measure p := by
    refine ⟨LinearMap.id,volumePreservingRVLift_derivative e hVol p,?_⟩
    rw [LinearMap.toMatrix'_id,Matrix.det_one,volumePreservingRVLift_label,e.gamma_jacobian]
    simp only [rvGammaJacobian,hVol,div_self']
    change Values.vfValueHom 1 = Values.gammaValHom 1
    rw [map_one,map_one]

theorem volumePreservingMeasuredRVLift_unary {U V : MeasuredRVObject (M := M) S n}
    (e : MeasuredRVIso U V) (hVol : ∀ u,V.object.value (e.iso.hom.map u) = U.object.value u)
    (i : Fin n) : VFUnaryRelativeAt (volumePreservingMeasuredRVLift e hVol).map i := by
  intro p j hj
  rfl

end DiamondIntegral.Section6
