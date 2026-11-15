import «section 5».NativeTotalRVLabelMaps
import «section 5».NativeRVFiniteLiftLabels

/-! The actual lift of the total label map has its literal full domain:
the selected base labels lift, every old RV parameter is retained, and
the fibre label graph lifts exactly once. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section
namespace DiamondIntegral.Section5
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section3.GammaParameters
open IntegrationInACVF.Section6
open DiamondIntegral.Section3 DiamondIntegral.Section4 Section3RVCodeBridge
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {p a k d : ℕ}

theorem nativeTotalRVLabelMap_raw_value
    (X : GammaGroundDefSet hc B (rawRVSpace (M := M) p))
    (F : GammaFiniteRVSchema B p a k (fun _ => .rv)) (j : Fin d → Fin p)
    (hv : ∀ z ∈ rawDomain X,nativeFiniteRVSchemaValid F z)
    (u : originalRVTotalFamily X (finiteRVSchemaDomain F)) :
    rvValues (((nativeTotalRVLabelMap X F j hv) u).val) = nativeTotalLabelRawValue F j (rvValues u.val) := rfl

theorem rvValues_tupleRV_append (x : Fin d → Section2.VF M) (y : Fin k → Section2.VF M) :
    rvValues (Section2.tupleRV M (Fin.append x y)) =
      Fin.append (rvValues (Section2.tupleRV M x)) (rvValues (Section2.tupleRV M y)) := by
  funext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;>
    simp only [rvValues,Section2.tupleRV,Fin.append_left,Fin.append_right]

theorem nativeTotalRVLabelLift_mem
    (X : GammaGroundDefSet hc B (rawRVSpace (M := M) p))
    (F : GammaFiniteRVSchema B p a k (fun _ => .rv)) (j : Fin d → Fin p)
    (hv : ∀ z ∈ rawDomain X,nativeFiniteRVSchemaValid F z)
    (x : Fin d → Section2.VF M) (y : Fin k → Section2.VF M)
    (w : Fin (p+a) → CanonicalRV.RVSort M) :
    (Fin.append x y,w) ∈ (nativeRVLabelLift (originalRVTotalFamily X (finiteRVSchemaDomain F))
      (nativeTotalRVLabelMap X F j hv)).carrier ↔
      w ∈ (originalRVTotalFamily X (finiteRVSchemaDomain F)).carrier ∧
        rvValues w ∘ Fin.castAdd a ∘ j = rvValues (Section2.tupleRV M x) ∧
          Fin.append (rvValues w) (rvValues (Section2.tupleRV M y)) ∈ F.volume := by
  constructor
  · rintro ⟨u,hu,hy⟩
    have hu' : u.val = w := hu
    have hw : w ∈ (originalRVTotalFamily X (finiteRVSchemaDomain F)).carrier := hu' ▸ u.property
    have hraw := congrArg rvValues hy
    rw [nativeTotalRVLabelMap_raw_value,hu,rvValues_tupleRV_append] at hraw
    have hleft : rvValues w ∘ Fin.castAdd a ∘ j = rvValues (Section2.tupleRV M x) :=
      funext (fun i => by
        have hi := congrFun hraw (Fin.castAdd k i)
        simpa only [nativeTotalLabelRawValue,Fin.append_left] using hi)
    have hright : finiteRVSchemaRawValue F (rvValues w ∘ Fin.castAdd a) (rvValues w ∘ Fin.natAdd p) =
        rvValues (Section2.tupleRV M y) := funext (fun i => by
      have hi := congrFun hraw (Fin.natAdd d i)
      simpa only [nativeTotalLabelRawValue,Fin.append_right] using hi)
    have hw' := (originalRVTotalFamily_mem X (finiteRVSchemaDomain F) w).mp hw
    have hz : rvValues w ∘ Fin.castAdd a ∈ rawDomain X := ⟨w ∘ Fin.castAdd a,hw'.1,rfl⟩
    have hx : Fin.append (rvValues w ∘ Fin.castAdd a) (rvValues w ∘ Fin.natAdd p) ∈ F.domain :=
      Fin.append_castAdd_natAdd.symm ▸ hw'.2
    have hvolume := (finiteRVSchemaRawValue_graph F _ (hv _ hz).1 _ hx _).mpr hright
    have hpack : Fin.append (rvValues w ∘ Fin.castAdd a) (rvValues w ∘ Fin.natAdd p) = rvValues w :=
      Fin.append_castAdd_natAdd
    rw [hpack] at hvolume
    exact ⟨hw,hleft,hvolume⟩
  · rintro ⟨hw,hleft,hvolume⟩
    let u : originalRVTotalFamily X (finiteRVSchemaDomain F) := ⟨w,hw⟩
    refine ⟨u,rfl,?_⟩
    apply rvValues_injective
    rw [nativeTotalRVLabelMap_raw_value,rvValues_tupleRV_append]
    have hw' := (originalRVTotalFamily_mem X (finiteRVSchemaDomain F) w).mp hw
    have hz : rvValues w ∘ Fin.castAdd a ∈ rawDomain X := ⟨w ∘ Fin.castAdd a,hw'.1,rfl⟩
    have hx : Fin.append (rvValues w ∘ Fin.castAdd a) (rvValues w ∘ Fin.natAdd p) ∈ F.domain :=
      Fin.append_castAdd_natAdd.symm ▸ hw'.2
    have hgraph := finiteRVSchemaRawValue_graph F _ (hv _ hz).1 _ hx (rvValues (Section2.tupleRV M y))
    have hpack : Fin.append (rvValues w ∘ Fin.castAdd a) (rvValues w ∘ Fin.natAdd p) = rvValues w :=
      Fin.append_castAdd_natAdd
    rw [hpack] at hgraph
    exact congrArg₂ Fin.append hleft (hgraph.mp hvolume)

end DiamondIntegral.Section5
