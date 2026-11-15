import «section 5».NativeWeakRVLabelGraphs
import «section 5».NativeFiniteRVSchemaPromotion
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
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)}
variable {p k : ℕ} {sp : Fin p → SortTag}

theorem native_weak_finite_rv_schema_at_parameter
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
    (z : Fin p → M) (hz : ∀ i, sortEval (sp i) (z i))
    (U : NativeWeakRVObject hc ⟨B.real ∪ Set.range z,B.gamma⟩ k) :
    ∃ F : GammaFiniteRVSchema B p U.arity k sp, F.valid z ∧
      {x | Fin.append z x ∈ F.domain} = rawDomain U.domain ∧
      ∀ x : Fin U.arity → M, ∀ y : Fin k → M,
        Fin.append (Fin.append z x) y ∈ F.volume ↔ Fin.append x y ∈ nativeWeakRVLabelGraph U := by
  obtain ⟨N,hN⟩ := nativeWeakRVLabelGraph_uniform_bound (B := ⟨B.real ∪ Set.range z,B.gamma⟩)
    hκ hs (small_union_range_carrier hκ B.real hr z) hγ U
  obtain ⟨D,hD,_⟩ := original_rv_domain_at_parameter hc B sp z hz U.domain
  obtain ⟨V,hV,hVrow⟩ := gamma_sorted_tuple_relation_promotion B sp
    (fun _ : Fin U.arity => .rv) (fun _ : Fin k => .rv) z hz (nativeWeakRVLabelGraph U) (nativeWeakRVLabelGraph_definable U)
  let F : GammaFiniteRVSchema B p U.arity k sp := ⟨D.val,V,D.property,hV,N⟩
  have hd (x : Fin U.arity → M) : Fin.append z x ∈ F.domain ↔ x ∈ rawDomain U.domain :=
    Set.ext_iff.mp hD x
  have hv (x : Fin U.arity → M) (y : Fin k → M) :
      Fin.append (Fin.append z x) y ∈ F.volume ↔ Fin.append x y ∈ nativeWeakRVLabelGraph U := hVrow x y
  have hvalid : F.valid z := by
    refine ⟨hz,?_,?_,?_⟩
    · intro x hx
      obtain ⟨v,hv',hvx⟩ := (hd x).mp hx
      let u : U.domain := ⟨v,hv'⟩
      refine ⟨rvValues (U.volume u).val,(hv x _).mpr
        ((nativeWeakRVLabelGraph_append_iff U x _).mpr ⟨u,hvx,rfl⟩),?_⟩
      intro y hy
      obtain ⟨w,hw,hwy⟩ := (nativeWeakRVLabelGraph_append_iff U x y).mp ((hv x y).mp hy)
      have he : w = u := Subtype.ext (rvValues_injective (hw.trans hvx.symm))
      subst w
      exact hwy.symm
    · intro x y hxy
      obtain ⟨u,hux,_⟩ := (nativeWeakRVLabelGraph_append_iff U x y).mp ((hv x y).mp hxy)
      exact (hd x).mpr ⟨u.val,u.property,hux⟩
    · intro y hy
      have he : {x | Fin.append (Fin.append z x) y ∈ F.volume} =
          {x | Fin.append x y ∈ nativeWeakRVLabelGraph U} := Set.ext (fun x => hv x y)
      change _ ∧ _
      rw [he]
      exact hN y hy
  exact ⟨F,hvalid,hD,hv⟩

end DiamondIntegral.Section5
