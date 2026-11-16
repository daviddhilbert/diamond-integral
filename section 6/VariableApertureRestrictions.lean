import «section 6».VariableApertureBundles
import «section 6».ProtectedTaggedApertureRadii

/-! The same variable old aperture and the same whole-label annulus
apply to every compatible protected component. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n r : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]
variable {A P : DefSet (rawMixedSpace (M := M) n r) S}
variable {D : CentripetalData (G := G) A} {E : CentripetalData (G := G) P}

theorem VariableApertureReleaseData.restrict
    {U : DefSet (rawRVSpace (M := M) (n+(1+r))) S}
    {ρ : (Fin r → RVInfinity M) → Gamma M} (H : VariableApertureReleaseData D U ρ)
    (h : ApertureRestrictionData D E)
    (hStable : ∀ a ∈ P.carrier, a.2 ∈ D.activeTags.carrier → ∀ x : VF M,
      (ρ a.2).val < vfValue (a.1 D.coordinate-x) →
        (Function.update a.1 D.coordinate x,a.2) ∈ P.carrier) :
    VariableApertureReleaseData E U ρ where
  labels a ha := by
    rw [h.point a ha,H.labels a (h.subset ha)]
    rw [h.coordinate,h.focus a ha,h.core a ha]
    exact and_congr (h.active_iff ha).symm Iff.rfl
  stable a ha hu x hx := by
    rw [h.coordinate] at hx ⊢
    exact hStable a ha ((h.active_iff ha).mp hu) x hx

theorem ApertureRestrictionData.variable_released_image_subset
    (h : ApertureRestrictionData D E)
    (U : DefSet (rawRVSpace (M := M) (n+(1+r))) S) :
    (E.variableReleasedImage U).carrier ⊆ (D.variableReleasedImage U).carrier := by
  intro q hq
  obtain ⟨a,ha,hU,he⟩ := (E.mem_variableReleasedImage U q).mp hq
  apply (D.mem_variableReleasedImage U q).mpr
  rw [h.point a ha] at hU he
  exact ⟨a,h.subset ha,hU,he⟩

end DiamondIntegral.Section6
