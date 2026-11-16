import «section 6».FiniteFocusImages
import «section 6».UnaryPullbackPreservation
import «section 6».FiniteRVFiberTransport

/-! On a unary RV-pullback with finite RV fibres, an actual centripetal
component can act on only finitely many old label tuples. The finite
focus image is not assumed: it is deduced from its original-base graph.
The focus point itself belongs to the full source RV disc. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2

namespace DiamondIntegral.Section6

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {r : ℕ} {S : Set M}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]
variable {A : DefSet (rawMixedSpace (M := M) 1 r) S}

namespace CentripetalData

def unaryActiveLabels (D : CentripetalData (G := G) A) : Set (Fin r → RVInfinity M) :=
  {u | ∃ x, (x,u) ∈ A.carrier ∧ u ∈ D.activeTags.carrier}

theorem unary_update_zero (D : CentripetalData (G := G) A) (x : Fin 1 → VF M) :
    Function.update x D.coordinate 0 = fun _ => 0 := by
  funext i
  have hi : i = D.coordinate := Subsingleton.elim _ _
  subst i
  exact Function.update_self _ _ _

theorem unary_focusImage_finite (D : CentripetalData (G := G) A)
    (hc : CanonicalStructure.IsCanonical (M := M)) {κ : Cardinal} (hs : Saturated M κ)
    (hsmall : Cardinal.mk S < κ) : (scalarFocusImage D.focusMap).Finite := by
  apply scalarFocusImage_finite hc hs hsmall D.focusMap
  intro p q hu
  rw [D.focusMap_eq,D.focusMap_eq,D.unary_update_zero,D.unary_update_zero,hu]

theorem unary_focus_mem (D : CentripetalData (G := G) A)
    (hA : IsRVPullback A.carrier) {p : Mixed M 1 r} (hp : p ∈ A.carrier)
    (hu : p.2 ∈ D.activeTags.carrier) :
    ((fun _ => D.extendedFocus p),p.2) ∈ A.carrier := by
  apply rvPullback_mem_of_sameRV (q := ((fun _ => D.extendedFocus p),p.2)) hA hp _ rfl
  funext i
  have hi : i = D.coordinate := Subsingleton.elim _ _
  subst i
  change rv M (p.1 D.coordinate) = rv M (D.extendedFocus p)
  rw [D.extendedFocus_active hp hu]
  exact (D.focusRV p hp hu).symm

theorem unaryActiveLabels_finite (D : CentripetalData (G := G) A)
    (hc : CanonicalStructure.IsCanonical (M := M)) {κ : Cardinal} (hs : Saturated M κ)
    (hsmall : Cardinal.mk S < κ) (hA : IsRVPullback A.carrier)
    (hFin : ∀ x : Fin 1 → VF M, {u : Fin r → RVInfinity M | (x,u) ∈ A.carrier}.Finite) :
    D.unaryActiveLabels.Finite := by
  have hFocus := D.unary_focusImage_finite hc hs hsmall
  apply (hFocus.biUnion (fun a _ => hFin (fun _ => a))).subset
  rintro u ⟨x,hx,hu⟩
  have ha : D.extendedFocus (x,u) ∈ scalarFocusImage D.focusMap := by
    refine ⟨⟨(x,u),hx,hu⟩,?_⟩
    exact (D.focusMap_eq _).trans (D.extendedFocus_active hx hu).symm
  simp only [Set.mem_iUnion]
  exact ⟨D.extendedFocus (x,u),ha,D.unary_focus_mem hA hx hu⟩

theorem unary_image_finite_rv_fibers (D : CentripetalData (G := G) A)
    (hc : CanonicalStructure.IsCanonical (M := M)) (h00 : M ⊨ Axioms.ACVF00)
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (hsmall : Cardinal.mk S < κ)
    (hFin : ∀ x : Fin 1 → VF M, {u : Fin r → RVInfinity M | (x,u) ∈ A.carrier}.Finite) :
    ∀ x : Fin 1 → VF M,
      {u : Fin (1+r) → RVInfinity M | (x,u) ∈ D.map.image.carrier}.Finite :=
  finite_rv_fibers_of_bijective hc h00 hκ hs hsmall D.bijection (D.bijective h00) hFin

end CentripetalData
end DiamondIntegral.Section6
