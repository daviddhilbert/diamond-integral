import «section 3».GammaFrozenPrefixSliceMaps
import Integration7.ActiveVFCoordinateSlices

/-! A defined full mixed Jacobian of a prefix-fixed map is exactly
the unary Jacobian of its actual native slice map. The full chart and
fixed output RV labels are retained. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2800000
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5 SpecialTransformations.Section9
open IntegrationInACVF.Section7
open IntegrationInACVF.Section6 IntegrationInACVF.Section6.FiniteRV
namespace DiamondIntegral.Section3
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {p : ℕ}
variable (U V : GammaObjectAt B Set.univ (p+1))
variable (ω : GammaGroundVolumeForm hc B (Section5.nativeRVGroundDomain U))
variable (η : GammaGroundVolumeForm hc B (Section5.nativeRVGroundDomain V)) (N L : ℕ)
variable (x : Fin p → VF (M := M))
variable (hF : (gammaNativeMeasuredVFSliceSchema U ω N).valid (vfValues x))
variable (hG : (gammaNativeMeasuredVFSliceSchema V η L).valid (vfValues x))
variable (P : GammaFiniteGraphPresentation ⟨B.real ∪ Set.range (vfValues x),B.gamma⟩ (rvObjectArity U.object.obj) 1
  ((gammaNativeMeasuredVFSliceSchema U ω N).object.rowDomain (vfValues x))
  ((gammaNativeMeasuredVFSliceSchema U ω N).object.rowVolume (vfValues x)))
variable (Q : GammaFiniteGraphPresentation ⟨B.real ∪ Set.range (vfValues x),B.gamma⟩ (rvObjectArity V.object.obj) 1
  ((gammaNativeMeasuredVFSliceSchema V η L).object.rowDomain (vfValues x))
  ((gammaNativeMeasuredVFSliceSchema V η L).object.rowVolume (vfValues x)))
variable (f : GammaGroundBijection (gammaNativeUnitLift (hc := hc) U.toGamma).domain (gammaNativeUnitLift V.toGamma).domain)
variable (hFix : ∀ q, (f.map q).val.1 ∘ Fin.castAdd 1 = q.val.1 ∘ Fin.castAdd 1)


theorem gammaNativeUnarySliceMap_jacobian
    (q : (gammaNativeUnitLift (hc := hc) (gammaUniversalObject P.toGamma).toGamma).domain)
    (J : Section2.VF M)
    (hJ : HasMixedVFJacobianAt f.map (gammaNativeSliceRowOriginalPoint U ω N x hF P q) J) :
    HasMixedVFJacobianAt (gammaNativeUnarySliceMap U V ω η N L x hF hG P Q f hFix) q J := by
  let u := gammaNativeSliceRowOriginalPoint U ω N x hF P q
  let i : Fin (p+1) := Fin.natAdd p (0 : Fin 1)
  obtain ⟨H,⟨ρ,hH⟩,hHJ⟩ := hJ
  have hFixed : ∀ z ∈ vfBall u.val.1 ρ, ∀ j, j ≠ i → H z j = z j := by
    intro z hz j
    obtain ⟨hzA,hHz⟩ := hH z hz
    let a : (gammaNativeUnitLift (hc := hc) U.toGamma).domain := ⟨(z,u.val.2),hzA⟩
    have hVF := congrArg (fun b : Section2.Mixed M (p+1) (rvObjectArity V.object.obj) => b.1) hHz
    refine Fin.addCases ?_ ?_ j
    · intro t _
      exact (congrFun hVF (Fin.castAdd 1 t)).symm.trans (congrFun (hFix a) t)
    · intro t ht
      have he : t = 0 := Subsingleton.elim _ _
      subst t
      exact False.elim (ht rfl)
  let G := activeVFCoordinateSlice H u.val.1 i
  have hCentre : (fun _ : Fin 1 => u.val.1 i) = q.val.1 := by
    funext j
    have hj : j = 0 := Subsingleton.elim _ _
    subst j
    change Fin.append x q.val.1 (Fin.natAdd p (0 : Fin 1)) = q.val.1 0
    exact Fin.append_right _ _ _
  have hGJ : HasVFJacobianAt G q.val.1 J := by
    have h := relative_vf_coordinate_slice_jacobian hHJ i ρ hFixed
    rw [hCentre] at h
    exact h
  refine ⟨G,⟨ρ,?_⟩,hGJ⟩
  intro z hz
  let w := Function.update u.val.1 i (z 0)
  have hu0 : u.val.1 i = q.val.1 0 := congrFun hCentre 0
  have hw : w ∈ vfBall u.val.1 ρ := by
    intro j
    by_cases hj : j = i
    · subst j
      change ρ.val < Values.vfValueHom ((Function.update u.val.1 i (z 0)) i-u.val.1 i)
      rw [Function.update_self,hu0]
      exact hz 0
    · change ρ.val < Values.vfValueHom ((Function.update u.val.1 i (z 0)) j-u.val.1 j)
      rw [Function.update_of_ne hj,sub_self]
      exact gamma_lt_value_zero _
  have hRestoreVF : w = Fin.append x z := by
    funext j
    refine Fin.addCases ?_ ?_ j
    · intro t
      have ht : Fin.castAdd 1 t ≠ i := by
        intro he
        have hv := congrArg Fin.val he
        change t.val = p at hv
        omega
      change Function.update (Fin.append x q.val.1) i (z 0) (Fin.castAdd 1 t) = Fin.append x z (Fin.castAdd 1 t)
      rw [Function.update_of_ne ht,Fin.append_left,Fin.append_left]
    · intro t
      have ht : t = 0 := Subsingleton.elim _ _
      subst t
      change Function.update (Fin.append x q.val.1) (Fin.natAdd p (0 : Fin 1)) (z 0) (Fin.natAdd p (0 : Fin 1)) =
        Fin.append x z (Fin.natAdd p (0 : Fin 1))
      rw [Function.update_self,Fin.append_right]
  obtain ⟨hwA,hHw⟩ := hH w hw
  have hRestore : (w,u.val.2) = (Fin.append x z,q.val.2) := Prod.ext hRestoreVF rfl
  have hqz : (z,q.val.2) ∈ (gammaNativeUnitLift (hc := hc) (gammaUniversalObject P.toGamma).toGamma).domain.carrier :=
    (gammaNativeSliceRow_lift U ω N x hF P (z,q.val.2)).mpr (hRestore ▸ hwA)
  have hArg : gammaNativeSliceRowOriginalPoint U ω N x hF P ⟨(z,q.val.2),hqz⟩ =
      (⟨(w,u.val.2),hwA⟩ : (gammaNativeUnitLift (hc := hc) U.toGamma).domain) := Subtype.ext hRestore.symm
  have hFullOut := (congrArg (fun a => (f.map a).val) hArg).trans hHw
  have hSlice := (gammaNativeUnarySliceMap_value U V ω η N L x hF hG P Q f hFix ⟨(z,q.val.2),hqz⟩).trans
    (congrArg (fun b : Section2.Mixed M (p+1) (rvObjectArity V.object.obj) => (b.1 ∘ Fin.natAdd p,b.2)) hFullOut)
  have hGF : H w ∘ Fin.natAdd p = G z := by
    funext j
    have hj : j = 0 := Subsingleton.elim _ _
    subst j
    rfl
  have hRV : (f.map u).val.2 = (gammaNativeUnarySliceMap U V ω η N L x hF hG P Q f hFix q).val.2 :=
    (congrArg (fun b : Section2.Mixed M 1 (rvObjectArity V.object.obj) => b.2)
      (gammaNativeUnarySliceMap_value U V ω η N L x hF hG P Q f hFix q)).symm
  exact ⟨hqz,hSlice.trans (Prod.ext hGF hRV)⟩

end DiamondIntegral.Section3
