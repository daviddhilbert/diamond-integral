import «section 3».GammaHeadFibreGroundMaps
import «section 3».GammaMeasuredRealBaseExtension
import Integration7.RelativeMixedFibreJacobians
import Integration7.GenericCoordinateFibreDimension

/-! Genuine Gamma densities restrict to the actual unary head fibre.
A generic frozen tail supplies exactly the independence needed to restrict
an everywhere defined measured bijection. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5 SpecialTransformations.Section9
open IntegrationInACVF.Section5 IntegrationInACVF.Section6 IntegrationInACVF.Section7
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)}
variable {S : Set M} {n a b : ℕ}

def gammaPointMeasuredData (A : DefSet (M := M) S n a)
    (hA : GammaSetDefinable B (carrier A))
    (hfin : ∀ x, {r | (x,r) ∈ carrier A}.Finite)
    (ω : GammaGroundVolumeForm hc B (Section5.nativeGammaPointDomain (carrier A) hA)) :
    GammaGroundMeasuredVFData hc B n := ⟨a,Section5.nativeGammaPointDomain (carrier A) hA,hfin,ω⟩

def gammaHeadMeasuredFibre (A : DefSet (M := M) S (n+1) a)
    (hA : GammaSetDefinable B (carrier A))
    (hfin : ∀ x, {r | (x,r) ∈ carrier A}.Finite)
    (ω : GammaGroundVolumeForm hc B (Section5.nativeGammaPointDomain (carrier A) hA))
    (x : Fin n → VF (M := M)) :
    GammaGroundMeasuredVFData hc ⟨B.real ∪ Set.range (vfValues x),B.gamma⟩ 1 where
  arity := a
  domain := gammaHeadFibreDomain A hA x
  finite z := hfin (Function.update (headFrozenTuple x) 0 (z 0))
  form := (ω.monoReal Set.subset_union_left).comp (gammaHeadFibreInclusion A hA x)

theorem gammaHeadMeasuredFibre_weight (A : DefSet (M := M) S (n+1) a)
    (hA : GammaSetDefinable B (carrier A))
    (hfin : ∀ x, {r | (x,r) ∈ carrier A}.Finite)
    (ω : GammaGroundVolumeForm hc B (Section5.nativeGammaPointDomain (carrier A) hA))
    (x : Fin n → VF (M := M)) (p : (gammaHeadMeasuredFibre A hA hfin ω x).domain) :
    gammaGroundMeasuredVFWeight (gammaHeadMeasuredFibre A hA hfin ω x) p =
      gammaGroundMeasuredVFWeight (gammaPointMeasuredData A hA hfin ω)
        (gammaHeadFibreInclusion A hA x p) := rfl

def gammaHeadFibreBijection {A : DefSet (M := M) S (n+1) a} {D : DefSet (M := M) S (n+1) b}
    (hA : GammaSetDefinable B (carrier A)) (hD : GammaSetDefinable B (carrier D))
    (f : Map A D) (hf : Function.Bijective f) (hΓ : GammaGraphDefinable B (pointMapGraph f))
    (hi : UnaryRelative f 0) (x : Fin n → VF (M := M)) :
    GammaGroundBijection (gammaHeadFibreDomain (hc := hc) A hA x) (gammaHeadFibreDomain D hD x) :=
  Section5.nativeGammaPointBijection (gamma_head_fibre A hA x) (gamma_head_fibre D hD x)
    (gammaRelativeHeadFibreIso f hf hΓ hi x)

theorem gammaHeadFibreBijection_value {A : DefSet (M := M) S (n+1) a} {D : DefSet (M := M) S (n+1) b}
    (hA : GammaSetDefinable B (carrier A)) (hD : GammaSetDefinable B (carrier D))
    (f : Map A D) (hf : Function.Bijective f) (hΓ : GammaGraphDefinable B (pointMapGraph f))
    (hi : UnaryRelative f 0) (x : Fin n → VF (M := M)) (p : gammaHeadFibreDomain (hc := hc) A hA x) :
    ((gammaHeadFibreBijection hA hD f hf hΓ hi x).map p).val =
      (coordinateFibreMap f 0 hi (headFrozenTuple x) ⟨p.val,p.property⟩).val :=
  Section5.nativeGammaPointBijection_apply _ _ _ p

variable [CharZero (Section2.VF M)]
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (Section2.VF M) G]

def gammaFullMeasuredHeadFibre
    {A : DefSet (M := M) S (n+1) a} {D : DefSet (M := M) S (n+1) b}
    (hA : GammaSetDefinable B (carrier A)) (hD : GammaSetDefinable B (carrier D))
    (hfinA : ∀ x, {r | (x,r) ∈ carrier A}.Finite) (hfinD : ∀ x, {r | (x,r) ∈ carrier D}.Finite)
    (ω : GammaGroundVolumeForm hc B (Section5.nativeGammaPointDomain (carrier A) hA))
    (η : GammaGroundVolumeForm hc B (Section5.nativeGammaPointDomain (carrier D) hD))
    (F : GammaFullMeasuredBijection (gammaPointMeasuredData A hA hfinA ω) (gammaPointMeasuredData D hD hfinD η))
    (f : Map A D) (hf : Function.Bijective f) (hΓ : GammaGraphDefinable B (pointMapGraph f))
    (hF : ∀ p, (F.map.map p).val = (f ⟨p.val,p.property⟩).val)
    (hi : UnaryRelative f 0) (x : Fin n → VF (M := M))
    (hx : AlgebraicIndependent (vfParameterField B.real) x) :
    GammaFullMeasuredBijection (gammaHeadMeasuredFibre A hA hfinA ω x) (gammaHeadMeasuredFibre D hD hfinD η x) where
  map := gammaHeadFibreBijection hA hD f hf hΓ hi x
  measure := by
    intro p hp
    have hp' : AlgebraicIndependent (tupleField (vfParameterField B.real) x) p.val.1 :=
      Eq.mp (congrArg (fun E : Subfield (VFType (M := M)) => AlgebraicIndependent E p.val.1)
        (vfParameterField_union_tuple B.real x)) hp
    let q := gammaHeadFibreInclusion A hA x p
    have hq : AlgebraicIndependent (vfParameterField B.real) q.val.1 :=
      independent_cons_over_tuple_field (vfParameterField B.real) x p.val.1 hx hp'
    obtain ⟨J,hJ,hw⟩ := F.measure q hq
    have hJf : HasMixedVFJacobianAt (rawSpecialMap hc f) ⟨q.val,q.property⟩ J := by
      obtain ⟨H,⟨ρ,hρ⟩,hH⟩ := hJ
      refine ⟨H,⟨ρ,fun z hz => ?_⟩,hH⟩
      obtain ⟨hzA,hzF⟩ := hρ z hz
      refine ⟨hzA,?_⟩
      rw [hF,hF] at hzF
      exact hzF
    have hqInsert : (⟨coordinateInsert 0 (headFrozenTuple x) p.val,p.property⟩ : rawSpecialSet hc A) = ⟨q.val,q.property⟩ :=
      Subtype.ext (coordinateInsert_head x p.val)
    have hJf' : HasMixedVFJacobianAt (rawSpecialMap hc f)
        ⟨coordinateInsert 0 (headFrozenTuple x) p.val,p.property⟩ J := by
      rw [hqInsert]
      exact hJf
    have hJF := relative_mixed_vf_jacobian_on_coordinate_fibre hc f 0 hi (headFrozenTuple x)
      ⟨p.val,p.property⟩ J hJf'
    have hJactual : HasMixedVFJacobianAt (gammaHeadFibreBijection hA hD f hf hΓ hi x).map p J := by
      obtain ⟨H,⟨ρ,hρ⟩,hH⟩ := hJF
      refine ⟨H,⟨ρ,fun z hz => ?_⟩,hH⟩
      obtain ⟨hzA,hzF⟩ := hρ z hz
      refine ⟨hzA,?_⟩
      rw [gammaHeadFibreBijection_value,gammaHeadFibreBijection_value]
      exact hzF
    refine ⟨J,hJactual,?_⟩
    rw [gammaHeadMeasuredFibre_weight,gammaHeadMeasuredFibre_weight]
    have hTarget : gammaHeadFibreInclusion D hD x ((gammaHeadFibreBijection hA hD f hf hΓ hi x).map p) = F.map.map q := by
      apply Subtype.ext
      rw [gammaHeadFibreInclusion_value,gammaHeadFibreBijection_value,hF]
      change (Fin.cons ((f ⟨coordinateInsert 0 (headFrozenTuple x) p.val,p.property⟩).val.1 0) x,
        (f ⟨coordinateInsert 0 (headFrozenTuple x) p.val,p.property⟩).val.2) = (f ⟨q.val,q.property⟩).val
      have hqeq : (⟨coordinateInsert 0 (headFrozenTuple x) p.val,p.property⟩ : A) = ⟨q.val,q.property⟩ :=
        Subtype.ext (coordinateInsert_head x p.val)
      rw [hqeq]
      refine Prod.ext ?_ rfl
      funext j
      cases j using Fin.cases with
      | zero => rfl
      | succ j =>
        exact ((hi ⟨q.val,q.property⟩ j.succ (Fin.succ_ne_zero j)).trans (by rfl)).symm
    rw [hTarget]
    exact hw

end DiamondIntegral.Section3
