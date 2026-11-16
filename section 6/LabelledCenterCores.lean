import «section 6».LabelledScalarOffsets

/-! Core domains from actual label-separated center families and actual
offset maps, with a literal incidence description through those centers. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section8 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {r : ℕ}
variable {A : DefSet (rawMixedSpace (M := M) 1 r) S}
variable (E : DefSet (rawMixedSpace (M := M) 1 r) S)
variable (hUnique : ∀ p q : E,p.val.2=q.val.2 → p=q)
variable (e : Map E (DefSet.univ (rawVFSpace (M := M) 1) S))
variable (hEA : E.carrier ⊆ A.carrier) (hA : ProperInvariant S A.carrier) (hD : VFDoublyBounded A.carrier)
variable (hTag : ∀ p ∈ A.carrier,∀ q ∈ A.carrier,p.2=q.2 → tupleRV M p.1=tupleRV M q.1)

def labelledCenterCore : DefSet (rawMixedSpace (M := M) 1 r) S :=
  (unaryLabelCenterFocusData E hUnique hEA hA hD hTag).offsetCoreDomain (unaryAmbientScalarMap E hUnique e)

theorem mem_labelledCenterCore (x : Mixed M 1 r) :
    x ∈ (labelledCenterCore E hUnique e hEA hA hD hTag).carrier ↔
      x ∈ A.carrier ∧ ∃ p : E,p.val.2=x.2 ∧ vfValue ((e p).val 0) < vfValue (x.1 0-p.val.1 0) := by
  rw [show x ∈ (labelledCenterCore E hUnique e hEA hA hD hTag).carrier ↔
      x ∈ ((unaryLabelCenterFocusData E hUnique hEA hA hD hTag).offsetCoreDomain
        (unaryAmbientScalarMap E hUnique e)).carrier from Iff.rfl,
    UnaryFocusData.mem_offsetCoreDomain _ _ (unaryLabelScalar E hUnique e)
      (unaryAmbientScalarMap_value E hUnique e)]
  change (x ∈ A.carrier ∧ x.2 ∈ (pureRVTagDomain E).carrier ∧
      vfValue (unaryLabelScalar E hUnique e x.2) < vfValue (x.1 0-unaryLabelCenter E hUnique x.2)) ↔ _
  constructor
  · rintro ⟨hx,hu,hClose⟩
    obtain ⟨p,hp⟩ := pureRVTagQuotient_surjective E ⟨x.2,hu⟩
    have hpu : p.val.2=x.2 := congrArg Subtype.val hp
    refine ⟨hx,p,hpu,?_⟩
    simpa only [← hpu,unaryLabelScalar_at,unaryLabelCenter_at] using hClose
  · rintro ⟨hx,p,hpu,hClose⟩
    have hu : x.2 ∈ (pureRVTagDomain E).carrier := hpu ▸ (pureRVTagQuotient E p).property
    refine ⟨hx,hu,?_⟩
    simpa only [← hpu,unaryLabelScalar_at,unaryLabelCenter_at] using hClose

theorem labelledCenterCore_subset : (labelledCenterCore E hUnique e hEA hA hD hTag).carrier ⊆ A.carrier :=
  (unaryLabelCenterFocusData E hUnique hEA hA hD hTag).offsetCoreDomain_subset (unaryAmbientScalarMap E hUnique e)

variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

theorem labelledCenterCore_proper
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (he : ∀ p : E,(e p).val 0 ≠ 0) :
    ProperInvariant S (labelledCenterCore E hUnique e hEA hA hD hTag).carrier :=
  (unaryLabelCenterFocusData E hUnique hEA hA hD hTag).offsetCoreDomain_proper
    (unaryAmbientScalarMap E hUnique e) (unaryLabelScalar E hUnique e) (unaryAmbientScalarMap_value E hUnique e)
    h00 hc hκ hs hv (unaryLabelScalar_nonzero E hUnique e he)

end DiamondIntegral.Section6
