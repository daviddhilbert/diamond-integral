import «section 3».GammaNativeVFSliceLiftDomains

/-! The complete Gamma density of a native volume slice is exactly the
original density at its retained RV labels, on every point of the full
VF lift. No representatives are selected as parameters. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
open IntegrationInACVF.Section6 IntegrationInACVF.Section6.FiniteRV
namespace DiamondIntegral.Section3
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {p k : ℕ}

theorem gammaNativeVFSliceSchema_point_volume (U : GammaObjectAt B Set.univ (p+k))
    (q : (gammaNativeUnitLift (hc := hc) U.toGamma).domain) :
    (gammaNativeVFSliceSchema U).rowVolume (vfValues (q.val.1 ∘ Fin.castAdd k)) q.val.2
      (@Section2.tupleRV M sM hM k (q.val.1 ∘ Fin.natAdd p)) := by
  apply (gammaNativeVFSliceSchema_lift U _ _ _).mp
  have he : (Fin.append (q.val.1 ∘ Fin.castAdd k) (q.val.1 ∘ Fin.natAdd p),q.val.2) = q.val :=
    Prod.ext Fin.append_castAdd_natAdd rfl
  exact he.symm ▸ q.property

theorem gammaNativeMeasuredVFSliceSchema_point_density
    (U : GammaObjectAt B Set.univ (p+k))
    (ω : GammaGroundVolumeForm hc B (Section5.nativeRVGroundDomain U)) (N : ℕ)
    (q : (gammaNativeUnitLift (hc := hc) U.toGamma).domain)
    (c : (volumeGammaSpace hc).domain)
    (hcValue : (volumeGammaSpace hc).decode c = ((gammaNativeMeasuredLift U ω).form q).val) :
    (gammaNativeMeasuredVFSliceSchema U ω N).rowDensity (vfValues (q.val.1 ∘ Fin.castAdd k)) q.val.2 c := by
  have hV := gammaNativeVFSliceSchema_point_volume U q
  have hD := (gammaNativeVFSliceSchema_finiteRows U (q.val.1 ∘ Fin.castAdd k)).2.1 _ _ hV
  apply (gammaMeasuredLabelSchema_density ((gammaNativeVFSliceSchema U).withBound N) ω
    (vfValues (q.val.1 ∘ Fin.castAdd k)) (fun j => (q.val.1 (Fin.castAdd k j)).property) q.val.2 c).mpr
  exact ⟨hD,gammaNativeLiftLabel U q,rfl,hcValue.symm⟩

end DiamondIntegral.Section3
