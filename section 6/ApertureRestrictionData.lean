import «section 6».ReleasedProjectionGeometry

/-! Restriction data preserving the actual coordinate, coefficient
and focus on a protected piece. These explicit conditions persist
under a common coefficient refinement and identify both branch tests. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2

namespace DiamondIntegral.Section6

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n r : ℕ} {S : Set M}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]
variable {A P : DefSet (rawMixedSpace (M := M) n r) S}

structure ApertureRestrictionData (D : CentripetalData (G := G) A)
    (E : CentripetalData (G := G) P) : Prop where
  subset : P.carrier ⊆ A.carrier
  coordinate : E.coordinate = D.coordinate
  coefficient : E.coefficient = D.coefficient
  focus : ∀ p ∈ P.carrier, E.extendedFocus p = D.extendedFocus p

namespace ApertureRestrictionData

variable {D : CentripetalData (G := G) A} {E : CentripetalData (G := G) P}

theorem core (h : ApertureRestrictionData D E) (p : Mixed M n r) (hp : p ∈ P.carrier) :
    E.core p = D.core p := by
  simp only [CentripetalData.core,h.coordinate,h.coefficient,h.focus p hp]

theorem point (h : ApertureRestrictionData D E) (p : Mixed M n r) (hp : p ∈ P.carrier) :
    E.point p = D.point p := by
  simp only [CentripetalData.point,h.coordinate,h.coefficient,h.focus p hp,h.core p hp]

def refine (h : ApertureRestrictionData D E) (c : VF M)
    (hc0 : c ≠ 0) (hcdef : S.Definable₁ LRV {c.val})
    (hval : vfValue D.coefficient ≤ vfValue c) :
    ApertureRestrictionData (D.refineCoefficient c hc0 hcdef hval)
      (E.refineCoefficient c hc0 hcdef (by rw [h.coefficient]; exact hval)) :=
  ⟨h.subset,h.coordinate,rfl,h.focus⟩

theorem protectedUnaryStep
    {B : DefSet (rawMixedSpace (M := M) 1 r) S} (F : UnaryFocusData B) (δ : Gamma M)
    (hδ : S.Definable LRV {z : Fin 1 → M | z 0 ∈ Values.gammaPullback {δ}})
    (hInv : ∀ u, AlphaInvariant (fun _ => δ) (vfFibre B.carrier u))
    (c : VF M) (hc0 : c ≠ 0) (hcpos : (1 : GammaInfinity M) ≤ vfValue c)
    (hcdef : S.Definable₁ LRV {c.val})
    (hcdom : ∀ a ∈ scalarFocusImage F.focusMap, δ.val < vfValue (c*a))
    (C : DefSet (rawMixedSpace (M := M) 1 r) S)
    (hCB : C.carrier ⊆ B.carrier) (hC : ProperInvariant S C.carrier)
    (hInvC : ∀ u, AlphaInvariant (fun _ => δ) (vfFibre C.carrier u)) :
    ApertureRestrictionData (F.withCoefficient (G := G) δ hδ hInv c hc0 hcpos hcdef hcdom)
      (F.protectedStep δ hδ c hc0 hcpos hcdef hcdom C hCB hC hInvC) := by
  refine ⟨hCB,rfl,rfl,fun p hp => ?_⟩
  let D := F.withCoefficient (G := G) δ hδ hInv c hc0 hcpos hcdef hcdom
  let E := F.protectedStep (G := G) δ hδ c hc0 hcpos hcdef hcdom C hCB hC hInvC
  change E.extendedFocus p = D.extendedFocus p
  by_cases hu : p.2 ∈ F.activeTags.carrier
  · rw [E.extendedFocus_active hp hu,D.extendedFocus_active (hCB hp) hu]
    rfl
  · rw [E.extendedFocus_inactive hu,D.extendedFocus_inactive hu]

end ApertureRestrictionData
end DiamondIntegral.Section6
