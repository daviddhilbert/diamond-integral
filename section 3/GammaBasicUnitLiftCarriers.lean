import «section 3».GammaNativeUnitElementaryLift
import «section 3».GammaMeasuredNormalizedPoint
import «section 5».Completed18LocalLift
import IntegrationSection6.GammaBasicAdmissibility
import IntegrationSection6.ElementaryCoordinates

/-! Literal carrier comparisons for the unit-density basic relation. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section3.GammaParameters SpecialTransformations.Section5 SpecialTransformations.Section7
open IntegrationInACVF.Section6
namespace DiamondIntegral.Section3
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)}
local notation "N" => (@CanonicalStructure.normalize M sM)
local notation "hN" => (@CanonicalStructure.normalized_model M sM hM)

theorem gammaBasicPoint_lift_carrier :
    (gammaNativeUnitLift (hc := hc) (FiniteRV.gammaOneAt (B := B) (S := Set.univ) (Set.subset_univ _)).toGamma).domain.carrier =
      (gammaGroundMeasuredObjectLift (gammaMeasuredPointZeroArity hc B)).domain.carrier := by
  let P := FiniteRV.gammaOneAt (B := B) (S := Set.univ) (Set.subset_univ _)
  let p₀ : (gammaMeasuredPointZeroArity hc B).underlying.domain := ⟨Fin.elim0,Set.mem_univ _⟩
  let u₀ : rvObjectDomain P.object.obj := ⟨Fin.elim0,Set.mem_univ _⟩
  have hv (u : rvObjectDomain P.object.obj) :
      (rvObjectVolume P.object.obj u).val = ((gammaMeasuredPointZeroArity hc B).underlying.volume p₀).val := by
    funext i
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    apply Subtype.ext
    exact (@RVOperations.one_val M N hN).trans normalized_rv_one
  ext q
  constructor
  · rintro ⟨u,hu,hq⟩
    refine ⟨p₀,funext (fun i => i.elim0),?_⟩
    exact (hv u).symm.trans (hq.trans (Section5.completed18_tupleRV q.1))
  · rintro ⟨u,hu,hq⟩
    refine ⟨u₀,funext (fun i => i.elim0),?_⟩
    have he : u = p₀ := Subtype.ext (funext (fun i => i.elim0))
    exact (hv u₀).trans ((congrArg (fun z => ((gammaMeasuredPointZeroArity hc B).underlying.volume z).val) he.symm).trans
      (hq.trans (Section5.completed18_tupleRV q.1).symm))

theorem gammaBasicElementary_lift_carrier_ordinary (S : Set M) :
    (SpecialTransformations.Section4.rvLift (elementary (FiniteRV.oneVolumeRVObject (M := M) S).obj 0)).carrier =
      (SpecialTransformations.Section4.rvLift (FiniteRV.positiveVolumeRVObject (M := M) S).obj).carrier := by
  let P := FiniteRV.oneVolumeRVObject (M := M) S
  let Q := positiveRV (M := M) S
  have hdom (t : Fin 1 → CanonicalRV.RVSort M) :
      t ∈ (@elementary M sM hM S 1 P.obj 0).domain.carrier ↔ t ∈ Q.carrier := by
    constructor
    · intro ht
      let u : (@elementary M sM hM S 1 P.obj 0).domain := ⟨t,ht⟩
      let a := @elementaryParameter M sM hM S 1 P.obj 0 u
      have he : a.val = t := by
        funext i
        have hi : i=0 := Fin.fin_one_eq_zero i
        subst i
        exact congrFun (@elementaryParameter_labels M sM hM S 1 P.obj 0 u) 0
      exact he ▸ a.property
    · intro ht
      let u : P.obj.domain := ⟨Fin.elim0,Set.mem_univ _⟩
      let a := @rvPackPair M sM S 0 1 P.obj.domain Q u ⟨t,ht⟩
      have he : a.val = t := by
        funext i
        have hi : i=0 := Fin.fin_one_eq_zero i
        subst i
        change Fin.append u.val t (Fin.natAdd 0 (0 : Fin 1)) = t 0
        exact Fin.append_right u.val t (0 : Fin 1)
      exact he ▸ a.property
  have hval (u : (@elementary M sM hM S 1 P.obj 0).domain) :
      ((@elementary M sM hM S 1 P.obj 0).volume u).val = u.val := by
    change (elementary P.obj 0).value u = u.val
    rw [elementary_value]
    funext i
    have hi : i=0 := Fin.fin_one_eq_zero i
    subst i
    rw [blowupValue_same]
    change (elementaryParameter P.obj 0 u).val 0 * 1 = (show Fin 1 → CanonicalRV.RVSort M from u.val) 0
    rw [mul_one]
    exact congrFun (elementaryParameter_labels P.obj 0 u) 0
  ext q
  change (∃ u : (@elementary M sM hM S 1 P.obj 0).domain,
    u.val=q.2 ∧ ((@elementary M sM hM S 1 P.obj 0).volume u).val=
      @SpecialTransformations.Section4.tupleRV M sM hM 1 q.1) ↔
    (∃ u : Q, u.val=q.2 ∧ u.val=@SpecialTransformations.Section4.tupleRV M sM hM 1 q.1)
  constructor
  · rintro ⟨u,hu,hv⟩
    exact ⟨⟨u.val,(hdom u.val).mp u.property⟩,hu,(hval u).symm.trans hv⟩
  · rintro ⟨u,hu,hv⟩
    let a : (@elementary M sM hM S 1 P.obj 0).domain := ⟨u.val,(hdom u.val).mpr u.property⟩
    exact ⟨a,hu,(hval a).trans hv⟩

theorem gammaBasicElementary_positive_lift_carrier
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (h00 : M ⊨ Axioms.ACVF00) (hr : Cardinal.mk B.real < κ) :
    (gammaNativeUnitLift (hc := hc) (FiniteRV.gammaElementaryAt hκ hs h00 hr
      (FiniteRV.gammaOneAt (B := B) (S := Set.univ) (Set.subset_univ _)) 0
      (FiniteRV.gammaOneAt_admissible (Set.subset_univ _))).toGamma).domain.carrier =
    (gammaNativeUnitLift (hc := hc) (FiniteRV.gammaPositiveAt (B := B) (S := Set.univ) (Set.subset_univ _)).toGamma).domain.carrier := by
  exact @gammaBasicElementary_lift_carrier_ordinary M N hN Set.univ

end DiamondIntegral.Section3
