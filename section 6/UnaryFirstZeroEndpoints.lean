import «section 6».UnaryFirstZeroCentreMaps
import «section 6».UnaryRelativeApertureExistence

/-! The endpoint at an actual first zero is the prescribed offset of
the original centre obtained by pulling back the current focus. Both
the endpoint map and its label presentation are constructed over S. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6.UnaryFirstZeroState
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S R : Set M} {r₀ r s : ℕ}
variable {A₀ : DefSet (rawMixedSpace (M := M) 1 r₀) S}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {K : UnaryCorePlan A₀}
variable {A : SpecialTransformations.Section5.DefSet (M := M) R 1 r}
variable {B : SpecialTransformations.Section5.DefSet (M := M) R 1 s} {j : Fin r}
variable (D : SpecialTransformations.Section5.Focus A 0 j)
variable (tail : SpecialTransformations.Section5.Chain R 1 D.etaImage B)
variable (hT : SpecialTransformations.Section5.GammaChainDefinable (ordinaryNamedGammaBase S)
  (.cons (.centripetal D) tail))
variable (Z : UnaryFirstZeroState (G := G) hc K (.cons (.centripetal D) tail) hT)

def firstZeroEndpointMap (h00 : M ⊨ Axioms.ACVF00) :
    Map (focusActive Z.frame.current (Z.frame.wholeFocusData D hT.1.2).activeTags)
      (DefSet.univ (rawVFSpace 1) S) :=
  K.offset.comp (Z.firstZeroCentreMap D tail hT h00)

theorem firstZeroEndpointMap_same_labels (h00 : M ⊨ Axioms.ACVF00)
    (p q : focusActive Z.frame.current (Z.frame.wholeFocusData D hT.1.2).activeTags)
    (hTags : p.val.2=q.val.2) :
    (Z.firstZeroEndpointMap D tail hT h00 p).val 0=
      (Z.firstZeroEndpointMap D tail hT h00 q).val 0 := by
  change (K.offset (Z.firstZeroCentreMap D tail hT h00 p)).val 0=_
  rw [Z.firstZeroCentreMap_same_labels D tail hT h00 p q hTags]
  rfl

theorem firstZeroCentreMap_ordinary_field (h00 : M ⊨ Axioms.ACVF00)
    (p : focusActive Z.frame.current (Z.frame.wholeFocusData D hT.1.2).activeTags) :
    (Z.ordinaryMap (K.centre (Z.firstZeroCentreMap D tail hT h00 p))).val.1 0=
      (Z.frame.wholeFocusData D hT.1.2).focus p.val.2 := by
  let c := Z.firstZeroCentreMap D tail hT h00 p
  have hPoint := Z.firstZeroCentreMap_point D tail hT h00 p
  have hLive : (Z.map (K.centre c)).val.2 ∈ Z.frame.liveLabels.carrier := by
    rw [hPoint]
    have hTags := congrArg (fun a : Mixed M 1 Z.arity => a.2)
      ((Z.frame.wholeFocusData D hT.1.2).focusPointMap_value Z.pullback p)
    exact hTags.symm ▸ Z.frame.activeTags_live D hT.1.2 p.property.2
  have hOld := Z.live_agrees (K.centre c) hLive
  have hVF := congrArg (fun a : originalBaseOrdinarySet hc A _ => a.val.1 0) hOld
  have hFrame := congrArg (fun a : Mixed M 1 r => a.1 0)
    (Z.frame.point ⟨(Z.map (K.centre c)).val,(Z.map (K.centre c)).property,hLive⟩)
  have hFocus := congrArg (fun a : Mixed M 1 Z.arity => a.1 0)
    ((Z.frame.wholeFocusData D hT.1.2).focusPointMap_value Z.pullback p)
  exact hVF.symm.trans (hFrame.trans ((congrArg (fun a : Z.frame.current => a.val.1 0) hPoint).trans hFocus))

theorem firstZeroEndpointMap_strict (h00 : M ⊨ Axioms.ACVF00)
    (p : focusActive Z.frame.current (Z.frame.wholeFocusData D hT.1.2).activeTags) :
    vfValue ((Z.frame.wholeFocusData D hT.1.2).focus p.val.2)<
      vfValue ((Z.firstZeroEndpointMap D tail hT h00 p).val 0) := by
  let c := Z.firstZeroCentreMap D tail hT h00 p
  have hField := Z.firstZeroCentreMap_ordinary_field D tail hT h00 p
  have hNZ : (Z.ordinaryMap (K.centre c)).val.1 0≠(0 : VF M) := by
    rw [hField,← (Z.frame.wholeFocusData D hT.1.2).focusMap_eq p]
    exact (Z.frame.wholeFocusData D hT.1.2).focusImage_nonzero
      (((Z.frame.wholeFocusData D hT.1.2).focusMap p).val 0) (Set.mem_range_self p)
  have hHead : ordinaryNonzeroFieldValue (Z.ordinaryMap (K.centre c)).val.1<K.radius c :=
    (le_max_right 1 _).trans_lt ((le_max_left _ _).trans_lt (Z.future_bound c))
  have hFinite : finiteValue ((Z.ordinaryMap (K.centre c)).val.1 0) hNZ<K.radius c := by
    simpa only [ordinaryNonzeroFieldValue,dif_pos hNZ] using hHead
  have hValue : vfValue ((Z.ordinaryMap (K.centre c)).val.1 0)<(K.radius c).val := hFinite
  rw [hField] at hValue
  exact hValue

def firstZeroAperture (h00 : M ⊨ Axioms.ACVF00) : UnaryRelativeApertureData Z.frame.current :=
  (Z.frame.wholeFocusData D hT.1.2).withRelativeEndpoint Z.pullback
    (scalarRVValue (Z.firstZeroEndpointMap D tail hT h00))
    (Z.firstZeroEndpointMap D tail hT h00)
    (fun p => (scalarRVValue_at _ (Z.firstZeroEndpointMap_same_labels D tail hT h00) p).symm)
    (by
      intro p
      rw [scalarRVValue_at _ (Z.firstZeroEndpointMap_same_labels D tail hT h00) p]
      exact K.offset_nonzero (Z.firstZeroCentreMap D tail hT h00 p))
    (by
      intro p
      rw [scalarRVValue_at _ (Z.firstZeroEndpointMap_same_labels D tail hT h00) p]
      exact (Z.firstZeroEndpointMap_strict D tail hT h00 p).le)

end DiamondIntegral.Section6.UnaryFirstZeroState
