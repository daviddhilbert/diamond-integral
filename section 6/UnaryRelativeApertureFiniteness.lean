import «section 6».UnaryRelativePullbackPreservation
import «section 6».FiniteRVFiberTransport

/-! Actual unary focus labels are finite on a prepared source with
finite RV fibres, before an endpoint is chosen. Variable-endpoint
bijections preserve that finite-fibre hypothesis. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {r : ℕ} {S : Set M}
variable {A : DefSet (rawMixedSpace (M := M) 1 r) S}

namespace UnaryFocusData

def actualActiveLabels (D : UnaryFocusData A) : Set (Fin r → RVInfinity M) :=
  {u | ∃ x,(x,u) ∈ A.carrier ∧ u ∈ D.activeTags.carrier}

theorem focus_mem_of_rvPullback (D : UnaryFocusData A)
    (hA : IsRVPullback A.carrier) {p : Mixed M 1 r} (hp : p ∈ A.carrier)
    (hu : p.2 ∈ D.activeTags.carrier) : ((fun _ => D.focus p.2),p.2) ∈ A.carrier := by
  apply rvPullback_mem_of_sameRV (q := ((fun _ => D.focus p.2),p.2)) hA hp _ rfl
  funext i
  fin_cases i
  exact (D.focusRV p hp hu).symm

theorem actualActiveLabels_finite (D : UnaryFocusData A)
    (hc : CanonicalStructure.IsCanonical (M := M)) {κ : Cardinal} (hs : Saturated M κ)
    (hsmall : Cardinal.mk S < κ) (hA : IsRVPullback A.carrier)
    (hFin : ∀ x : Fin 1 → VF M,{u : Fin r → RVInfinity M | (x,u) ∈ A.carrier}.Finite) :
    D.actualActiveLabels.Finite := by
  have hFocus := D.focusImage_finite hc hs hsmall
  apply (hFocus.biUnion (fun a _ => hFin (fun _ => a))).subset
  rintro u ⟨x,hx,hu⟩
  have ha : D.focus u ∈ scalarFocusImage D.focusMap :=
    ⟨⟨(x,u),hx,hu⟩,D.focusMap_eq _⟩
  simp only [Set.mem_iUnion]
  exact ⟨D.focus u,ha,D.focus_mem_of_rvPullback hA hx hu⟩

end UnaryFocusData

namespace UnaryRelativeApertureData

theorem image_finite_rv_fibres (D : UnaryRelativeApertureData A)
    (hc : CanonicalStructure.IsCanonical (M := M)) (h00 : M ⊨ Axioms.ACVF00)
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ) (hsmall : Cardinal.mk S < κ)
    (hFin : ∀ x : Fin 1 → VF M,{u : Fin r → RVInfinity M | (x,u) ∈ A.carrier}.Finite) :
    ∀ x : Fin 1 → VF M,{u : Fin (1+r) → RVInfinity M | (x,u) ∈ D.map.image.carrier}.Finite :=
  finite_rv_fibers_of_bijective hc h00 hκ hs hsmall D.bijection (D.bijective h00) hFin

end UnaryRelativeApertureData
end DiamondIntegral.Section6
