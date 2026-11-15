import «section 5».VFFieldSmallPresentation
import «section 5».VFFieldGamma
import Section3.GammaFullDescent
import «section 3».GammaGroundContext

/-! Naming finitely many VF coordinates over a VF-generated ground is
equivalent to naming precisely the generated field and its RV images. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
noncomputable section
namespace DiamondIntegral.Section5
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters
open CanonicalRV ValuedModelMap DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable (hc : CanonicalStructure.IsCanonical (M := M)) (G : GammaGroundContext M)
variable {n : ℕ} (b : Fin n → M) (hb : ∀ i,iVF (b i))

def vfAdjoinedField : Subfield (VFType (M := M)) := vfParameterField (G.base.real ∪ Set.range b)

theorem groundField_le_vfAdjoinedField : G.fieldBase.field ≤ vfAdjoinedField G b := by
  intro x hx
  exact Subfield.subset_closure (Or.inl ((G.fieldBase.mem_iff x).mp hx))

theorem groundReal_subset_vfAdjoinedFieldNames :
    G.base.real ⊆ (vfFieldSubstructure hc (vfAdjoinedField G b) : Set M) := by
  intro x hx
  rcases TypedModelMap.sort_cover (M := M) x with hv | hr
  · apply (vfFieldCarrier_vf (vfAdjoinedField G b) ⟨x,hv⟩).mpr
    exact groundField_le_vfAdjoinedField G b ((G.fieldBase.mem_iff ⟨x,hv⟩).mpr hx)
  · obtain ⟨a,ha⟩ := G.fieldBase.rv_lift x hx hr
    apply (vfFieldCarrier_rv (vfAdjoinedField G b) ⟨x,hr⟩).mpr
    refine ⟨a.val,groundField_le_vfAdjoinedField G b a.property,?_⟩
    exact Subtype.ext ha

include hb in
theorem rawVFParameters_subset_vfAdjoinedFieldNames :
    G.base.real ∪ Set.range b ⊆ (vfFieldSubstructure hc (vfAdjoinedField G b) : Set M) := by
  rintro x (hx | ⟨i,rfl⟩)
  · exact groundReal_subset_vfAdjoinedFieldNames hc G b hx
  · apply (vfFieldCarrier_vf (vfAdjoinedField G b) ⟨b i,hb i⟩).mpr
    exact Subfield.subset_closure (Or.inr ⟨i,rfl⟩)

theorem vfAdjoinedField_small : Cardinal.mk (vfAdjoinedField G b) < G.κ :=
  vfParameterField_small _ G.uncountable
    (small_union_range_carrier G.uncountable.le G.base.real G.small_real b)

theorem vfAdjoinedField_nontrivial
    (hnt : ∃ x : G.fieldBase.fieldˣ,vfFieldGammaMap G.fieldBase.field x ≠ 1) :
    ∃ x : (vfAdjoinedField G b)ˣ,vfFieldGammaMap (vfAdjoinedField G b) x ≠ 1 := by
  obtain ⟨x,hx⟩ := hnt
  let f : G.fieldBase.field →+* vfAdjoinedField G b :=
    Subfield.inclusion (groundField_le_vfAdjoinedField G b)
  refine ⟨Units.map f.toMonoidHom x,?_⟩
  exact hx

end DiamondIntegral.Section5
