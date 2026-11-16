import «section 6».UnaryFirstZeroCapture

/-! At a captured centre the new VF coordinate is exactly its prescribed
offset. On the live noncore it is the ordinary next value. These give
the radius bound needed to transport every entire core chart. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 7000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S R : Set M}

theorem UnaryRelativeApertureData.point_nonzero {q : ℕ}
    {W : DefSet (rawMixedSpace (M := M) 1 q) S} (E : UnaryRelativeApertureData W) (a : W) :
    (E.point a.val).1 0≠0 := by
  by_cases hActive : a.val.2 ∈ E.focusData.activeTags.carrier
  · intro hz
    have h := (E.point_active_bounds ⟨a.val,a.property,hActive⟩).2
    rw [hz,value_zero] at h
    exact (finiteValue (E.endpoint a.val.2) (E.endpoint_nonzero ⟨a.val,a.property,hActive⟩)).property
      (le_antisymm (Values.le_infinity _) h)
  · rw [E.point_inactive hActive]
    exact E.focusData.sourceDoublyBounded.nonzero a.property 0

theorem ordinary_chain_value_lt_pointRadius_bound {r s : ℕ}
    {A : SpecialTransformations.Section5.DefSet (M := M) R 1 r}
    {B : SpecialTransformations.Section5.DefSet (M := M) R 1 s}
    (T : SpecialTransformations.Section5.Chain R 1 A B) (p : A) (γ : Gamma M)
    (hBound : ordinaryChainPointRadius T p<γ) (hNZ : p.val.1 0≠(0 : VF M)) :
    vfValue (p.val.1 0)<γ.val := by
  have hHead : ordinaryNonzeroFieldValue p.val.1<γ := by
    cases T with
    | nil A => exact (le_max_right _ _).trans_lt hBound
    | cons step tail => exact (le_max_right _ _).trans_lt ((le_max_left _ _).trans_lt hBound)
  have hFinite : finiteValue (p.val.1 0) hNZ<γ := by
    simpa only [ordinaryNonzeroFieldValue,dif_pos hNZ] using hHead
  exact hFinite

namespace UnaryFirstZeroState
variable {r₀ r s : ℕ} {A₀ : DefSet (rawMixedSpace (M := M) 1 r₀) S}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {K : UnaryCorePlan A₀}
variable {A : SpecialTransformations.Section5.DefSet (M := M) R 1 r}
variable {B : SpecialTransformations.Section5.DefSet (M := M) R 1 s} {j : Fin r}
variable (D : SpecialTransformations.Section5.Focus A 0 j)
variable (tail : SpecialTransformations.Section5.Chain R 1 D.etaImage B)
variable (hT : SpecialTransformations.Section5.GammaChainDefinable (ordinaryNamedGammaBase S)
  (.cons (.centripetal D) tail))
variable (Z : UnaryFirstZeroState (G := G) hc K (.cons (.centripetal D) tail) hT)
variable (h00 : M ⊨ Axioms.ACVF00)

theorem firstZero_centre_selected (p : K.centres)
    (hCore : (Z.firstZeroAperture D tail hT h00).core (Z.map (K.centre p)).val=true) :
    ∃ z : focusActive Z.frame.current (Z.frame.wholeFocusData D hT.1.2).activeTags,
      z.val=(Z.map (K.centre p)).val ∧ Z.firstZeroCentreMap D tail hT h00 z=p := by
  have hActive : (Z.map (K.centre p)).val.2 ∈ (Z.frame.wholeFocusData D hT.1.2).activeTags.carrier := by
    by_contra hn
    rw [Z.firstZero_core_false_of_inactive D tail hT h00 (K.centre p) hn] at hCore
    contradiction
  let z : focusActive Z.frame.current (Z.frame.wholeFocusData D hT.1.2).activeTags :=
    ⟨(Z.map (K.centre p)).val,(Z.map (K.centre p)).property,hActive⟩
  refine ⟨z,rfl,?_⟩
  have hpDisc := (Z.firstZero_capture_exact D tail hT h00 z (K.centre p)).mp ⟨rfl,hCore⟩
  exact (K.centre_unique_in_disc p _ hpDisc).symm

theorem firstZero_output_captured_centre (p : K.centres)
    (hCore : (Z.firstZeroAperture D tail hT h00).core (Z.map (K.centre p)).val=true) :
    ((Z.firstZeroAperture D tail hT h00).point (Z.map (K.centre p)).val).1 0=(K.offset p).val 0 := by
  obtain ⟨z,hz,hc⟩ := Z.firstZero_centre_selected D tail hT h00 p hCore
  have hField := Z.firstZeroCentreMap_field D tail hT h00 z
  rw [hc] at hField
  have hTags := congrArg (fun a : Mixed M 1 Z.arity => a.2) hz
  have hFocus : (Z.firstZeroAperture D tail hT h00).extendedFocus (Z.map (K.centre p)).val=
      (Z.map (K.centre p)).val.1 0 := by
    rw [← hz,(Z.firstZeroAperture D tail hT h00).extendedFocus_active z]
    exact hField.symm.trans (congrArg (fun a : Mixed M 1 Z.arity => a.1 0) hz).symm
  have hEndpoint : (Z.firstZeroAperture D tail hT h00).extendedEndpoint (Z.map (K.centre p)).val=
      (K.offset p).val 0 := by
    rw [← hz,(Z.firstZeroAperture D tail hT h00).extendedEndpoint_active z,
      Z.firstZeroAperture_endpoint_at D tail hT h00 z,hc]
  simp only [UnaryRelativeApertureData.point,UnaryRelativeApertureData.coordinate,
    Function.update_self,hCore,ite_true,hFocus,hEndpoint,sub_self,zero_add]

theorem firstZero_noncore_live_field (a : A₀)
    (hLive : (Z.map a).val.2 ∈ Z.frame.liveLabels.carrier)
    (hCore : (Z.firstZeroAperture D tail hT h00).core (Z.map a).val=false) :
    ((Z.firstZeroAperture D tail hT h00).point (Z.map a).val).1=
      (D.toFocusGeometry.eta (Z.ordinaryMap a).val).1 := by
  have h := Z.frame.relative_field_matches_ordinary D hT.1.2 (Z.firstZeroAperture D tail hT h00)
    rfl (fun _ => rfl) ⟨(Z.map a).val,(Z.map a).property,hLive⟩ hCore
  rw [Z.live_agrees a hLive] at h
  exact h

theorem firstZero_core_centre_bound (p : K.centres) :
    vfValue (((Z.firstZeroAperture D tail hT h00).point (Z.map (K.centre p)).val).1 0)≤(K.radius p).val := by
  by_cases hLive : (Z.map (K.centre p)).val.2 ∈ Z.frame.liveLabels.carrier
  · cases hCore : (Z.firstZeroAperture D tail hT h00).core (Z.map (K.centre p)).val with
    | true =>
        rw [Z.firstZero_output_captured_centre D tail hT h00 p hCore]
        exact le_rfl
    | false =>
        have hField := Z.firstZero_noncore_live_field D tail hT h00 (K.centre p) hLive hCore
        have hNZ : (D.toFocusGeometry.eta (Z.ordinaryMap (K.centre p)).val).1 0≠(0 : VF M) := by
          rw [← hField]
          exact (Z.firstZeroAperture D tail hT h00).point_nonzero (Z.map (K.centre p))
        rw [hField]
        exact (ordinary_chain_value_lt_pointRadius_bound tail
          ((SpecialTransformations.Section5.Primitive.centripetal D).toMap (Z.ordinaryMap (K.centre p)))
          (K.radius p) ((le_max_right _ _).trans_lt (Z.future_bound p)) hNZ).le
  · rw [Z.frame.relative_inactive_on_frozen D hT.1.2 (Z.firstZeroAperture D tail hT h00) rfl hLive,
      Z.frozen_value p hLive]

theorem firstZero_after_core_chart (p : K.centres) :
    UnaryCoreChart ((Z.firstZeroAperture D tail hT h00).stepMap.comp Z.map) (K.centre p) (K.radius p) :=
  (Z.core_chart p).afterRelativeStep (Z.firstZeroAperture D tail hT h00)
    (Z.firstZero_core_constant D tail hT h00 p) (Z.firstZero_core_centre_bound D tail hT h00 p)

end UnaryFirstZeroState
end DiamondIntegral.Section6
