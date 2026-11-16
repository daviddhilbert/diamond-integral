import «section 6».ExtendedLiftDerivatives

/-! The extended local VF bijection has the exact everywhere measured
identity for the constructed global forms. On the selected label piece
its density is the local density; elsewhere its density is one. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section7 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n : ℕ}

theorem rvGammaJacobian_congr_values {a b c d : Fin n → RVInfinity M}
    {ha : ∀ i,(a i).val ≠ iRVZero} {hb : ∀ i,(b i).val ≠ iRVZero}
    {hc : ∀ i,(c i).val ≠ iRVZero} {hd : ∀ i,(d i).val ≠ iRVZero}
    (hA : a=c) (hB : b=d) : rvGammaJacobian a b ha hb = rvGammaJacobian c d hc hd := by
  cases hA
  cases hB
  rfl

theorem measuredRVVolumeExtension_density_on_piece (hc : CanonicalStructure.IsCanonical (M := M))
    (U : MeasuredRVObject (M := M) S n) {A B : MeasuredRVObject (M := M) S n} (e : MeasuredRVIso A B)
    (D : DefSet (rawRVSpace (M := M) U.object.arity) S) (χ : Map D A.object.domain)
    (hχ : Function.Injective χ) (u : U.object.domain) (hu : u.val ∈ D.carrier) :
    gammaMapValue (measuredRVVolumeExtension hc U A D χ hχ).form u /
      gammaMapValue (measuredRVVolumeExtension hc U B D (e.iso.hom.map.comp χ)
        ((rvIso_map_bijective e.iso).1.comp hχ)).form u =
      gammaMapValue A.form (χ ⟨u.val,hu⟩) / gammaMapValue B.form (e.iso.hom.map (χ ⟨u.val,hu⟩)) := by
  let d := measuredRVVolumeExtensionIso hc U e D χ hχ
  rw [show gammaMapValue (measuredRVVolumeExtension hc U A D χ hχ).form u /
      gammaMapValue (measuredRVVolumeExtension hc U B D (e.iso.hom.map.comp χ)
        ((rvIso_map_bijective e.iso).1.comp hχ)).form u =
      rvGammaJacobian ((measuredRVVolumeExtension hc U A D χ hχ).object.value u)
        ((measuredRVVolumeExtension hc U B D (e.iso.hom.map.comp χ)
          ((rvIso_map_bijective e.iso).1.comp hχ)).object.value u) _ _ from d.gamma_jacobian u,
    e.gamma_jacobian]
  exact rvGammaJacobian_congr_values
    (measuredRVVolumeExtension_of_mem hc U A D χ hχ u hu)
    (measuredRVVolumeExtension_of_mem hc U B D (e.iso.hom.map.comp χ)
      ((rvIso_map_bijective e.iso).1.comp hχ) u hu)

theorem measuredRVVolumeExtension_density_off_piece (hc : CanonicalStructure.IsCanonical (M := M))
    (U : MeasuredRVObject (M := M) S n) {A B : MeasuredRVObject (M := M) S n} (e : MeasuredRVIso A B)
    (D : DefSet (rawRVSpace (M := M) U.object.arity) S) (χ : Map D A.object.domain)
    (hχ : Function.Injective χ) (u : U.object.domain) (hu : u.val ∉ D.carrier) :
    gammaMapValue (measuredRVVolumeExtension hc U A D χ hχ).form u /
      gammaMapValue (measuredRVVolumeExtension hc U B D (e.iso.hom.map.comp χ)
        ((rvIso_map_bijective e.iso).1.comp hχ)).form u = 1 := by
  let d := measuredRVVolumeExtensionIso hc U e D χ hχ
  have h := d.gamma_jacobian u
  change gammaMapValue (measuredRVVolumeExtension hc U A D χ hχ).form u /
      gammaMapValue (measuredRVVolumeExtension hc U B D (e.iso.hom.map.comp χ)
        ((rvIso_map_bijective e.iso).1.comp hχ)).form u =
      rvGammaJacobian ((measuredRVVolumeExtension hc U A D χ hχ).object.value u)
        ((measuredRVVolumeExtension hc U B D (e.iso.hom.map.comp χ)
          ((rvIso_map_bijective e.iso).1.comp hχ)).object.value u) _ _ at h
  rw [h]
  have heq : rvGammaJacobian ((measuredRVVolumeExtension hc U A D χ hχ).object.value u)
      ((measuredRVVolumeExtension hc U B D (e.iso.hom.map.comp χ)
        ((rvIso_map_bijective e.iso).1.comp hχ)).object.value u)
      ((measuredRVVolumeExtension hc U A D χ hχ).nonzero u)
      ((measuredRVVolumeExtension hc U B D (e.iso.hom.map.comp χ)
        ((rvIso_map_bijective e.iso).1.comp hχ)).nonzero u) =
      rvGammaJacobian (U.object.value u) (U.object.value u) (U.nonzero u) (U.nonzero u) :=
    rvGammaJacobian_congr_values
      (measuredRVVolumeExtension_of_not_mem hc U A D χ hχ u hu)
      (measuredRVVolumeExtension_of_not_mem hc U B D (e.iso.hom.map.comp χ)
        ((rvIso_map_bijective e.iso).1.comp hχ) u hu)
  rw [heq]
  simp only [rvGammaJacobian,div_self']

def extendedEverywhereMeasuredRVLift (hc : CanonicalStructure.IsCanonical (M := M))
    (U : MeasuredRVObject (M := M) S n) {A B : MeasuredRVObject (M := M) S n}
    {e : MeasuredRVIso A B} (F : EverywhereMeasuredRVLift e)
    (D : DefSet (rawRVSpace (M := M) U.object.arity) S) (hD : D.carrier ⊆ U.object.domain.carrier)
    (χ : Map D A.object.domain) (hχ : Function.Injective χ) :
    EverywhereMeasuredRVLift (measuredRVVolumeExtensionIso hc U e D χ hχ) where
  map := extendedMeasuredLiftMap hc U F D hD χ hχ
  bijective := extendedMeasuredLiftMap_bijective hc U F D hD χ hχ
  labels p := ⟨liftLabelMap (measuredRVVolumeExtension hc U A D χ hχ).object p,rfl,rfl⟩
  measure p := by
    let u := liftLabelMap (measuredRVVolumeExtension hc U A D χ hχ).object p
    by_cases hp : p.val.2 ∈ D.carrier
    · let a := extendedLiftPoint hc U A D hD χ hχ p hp
      obtain ⟨L,hL,hJ⟩ := F.measure a
      refine ⟨L,extendedMeasuredLiftMap_derivative_on_piece hc U F D hD χ hχ p hp hL,?_⟩
      have hTarget := liftLabelMap_target_of_graph e.iso.hom.map F.map F.labels a
      have hSource : liftLabelMap A.object a = χ ⟨p.val.2,hp⟩ := Subtype.ext rfl
      rw [hTarget,hSource] at hJ
      change vfValue (LinearMap.toMatrix' L).det =
        (gammaMapValue (measuredRVVolumeExtension hc U A D χ hχ).form u /
          gammaMapValue (measuredRVVolumeExtension hc U B D (e.iso.hom.map.comp χ)
            ((rvIso_map_bijective e.iso).1.comp hχ)).form u).val
      rw [measuredRVVolumeExtension_density_on_piece hc U e D χ hχ u hp]
      exact hJ
    · refine ⟨LinearMap.id,extendedMeasuredLiftMap_derivative_off_piece hc U F D hD χ hχ p hp,?_⟩
      rw [LinearMap.toMatrix'_id,Matrix.det_one]
      change Values.vfValueHom 1 =
        (gammaMapValue (measuredRVVolumeExtension hc U A D χ hχ).form u /
          gammaMapValue (measuredRVVolumeExtension hc U B D (e.iso.hom.map.comp χ)
            ((rvIso_map_bijective e.iso).1.comp hχ)).form u).val
      rw [measuredRVVolumeExtension_density_off_piece hc U e D χ hχ u hp]
      change Values.vfValueHom 1 = Values.gammaValHom 1
      rw [map_one,map_one]

theorem extendedEverywhereMeasuredRVLift_unary (hc : CanonicalStructure.IsCanonical (M := M))
    (U : MeasuredRVObject (M := M) S n) {A B : MeasuredRVObject (M := M) S n}
    {e : MeasuredRVIso A B} (F : EverywhereMeasuredRVLift e)
    (D : DefSet (rawRVSpace (M := M) U.object.arity) S) (hD : D.carrier ⊆ U.object.domain.carrier)
    (χ : Map D A.object.domain) (hχ : Function.Injective χ) (i : Fin n) (hF : VFUnaryRelativeAt F.map i) :
    VFUnaryRelativeAt (extendedEverywhereMeasuredRVLift hc U F D hD χ hχ).map i :=
  extendedMeasuredLiftMap_unary hc U F D hD χ hχ i hF

end DiamondIntegral.Section6
