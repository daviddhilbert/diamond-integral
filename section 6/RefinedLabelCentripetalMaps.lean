import «section 6».CentripetalLabelRefinement

/-! Full-map compatibility after selecting retained RV labels. The
new branch flag is retained first, followed by the selected old labels;
the VF map agrees exactly with the original component. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2

namespace DiamondIntegral.Section6

def prefixLabelSelection {r s : ℕ} (π : Fin r → Fin s) : Fin (1+r) → Fin (1+s) :=
  Fin.addCases (Fin.castAdd s) (fun i => Fin.natAdd 1 (π i))

theorem append_prefixLabelSelection {X : Type*} {r s : ℕ} (π : Fin r → Fin s)
    (a : Fin 1 → X) (b : Fin s → X) :
    Fin.append a b ∘ prefixLabelSelection π = Fin.append a (b ∘ π) := by
  funext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · simp only [Function.comp_apply,prefixLabelSelection,Fin.addCases_left,Fin.append_left]
  · simp only [Function.comp_apply,prefixLabelSelection,Fin.addCases_right,Fin.append_right]

namespace CentripetalData

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n r s : ℕ} {S : Set M}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]
variable {A : DefSet (rawMixedSpace (M := M) n r) S}
variable {C : DefSet (rawMixedSpace (M := M) n s) S}
variable (D : CentripetalData (G := G) A) (π : Fin r → Fin s)
variable (hC : ProperInvariant S C.carrier) (hDouble : VFDoublyBounded C.carrier)
variable (hTagged : ∀ p ∈ C.carrier, ∀ q ∈ C.carrier, p.2 = q.2 → tupleRV M p.1 = tupleRV M q.1)
variable (hFibres : ∀ u : Fin s → RVInfinity M,
  vfFibre C.carrier u = ∅ ∨ vfFibre C.carrier u = vfFibre A.carrier (u ∘ π))

theorem refineLabels_extendedFocus (p : Mixed M n s) (hp : p ∈ C.carrier) :
    (D.refineLabels π hC hDouble hTagged hFibres).extendedFocus p = D.extendedFocus (p.1,p.2 ∘ π) := by
  have hOld := labelRefinement_source_subset π hFibres p hp
  by_cases hu : p.2 ∘ π ∈ D.activeTags.carrier
  · rw [(D.refineLabels π hC hDouble hTagged hFibres).extendedFocus_active hp hu,
      D.extendedFocus_active hOld hu]
    rfl
  · rw [(D.refineLabels π hC hDouble hTagged hFibres).extendedFocus_inactive hu,
      D.extendedFocus_inactive hu]

theorem refineLabels_core (p : Mixed M n s) (hp : p ∈ C.carrier) :
    (D.refineLabels π hC hDouble hTagged hFibres).core p = D.core (p.1,p.2 ∘ π) := by
  change decide (vfValue (D.coefficient * (D.refineLabels π hC hDouble hTagged hFibres).extendedFocus p) <
    vfValue (p.1 D.coordinate - (D.refineLabels π hC hDouble hTagged hFibres).extendedFocus p)) = _
  rw [D.refineLabels_extendedFocus π hC hDouble hTagged hFibres p hp]
  rfl

theorem refineLabels_point_commutes (p : Mixed M n s) (hp : p ∈ C.carrier) :
    let E := D.refineLabels π hC hDouble hTagged hFibres
    ((E.point p).1,(E.point p).2 ∘ prefixLabelSelection π) = D.point (p.1,p.2 ∘ π) := by
  let E := D.refineLabels π hC hDouble hTagged hFibres
  have hFocus := D.refineLabels_extendedFocus π hC hDouble hTagged hFibres p hp
  have hCore := D.refineLabels_core π hC hDouble hTagged hFibres p hp
  apply Prod.ext
  · change Function.update p.1 D.coordinate
      (p.1 D.coordinate - E.extendedFocus p + if E.core p then D.coefficient * E.extendedFocus p else 0) = _
    rw [hFocus,hCore]
    rfl
  · change Fin.append (fun _ : Fin 1 => branchTag (M := M) (E.core p)) p.2 ∘ prefixLabelSelection π =
      Fin.append (fun _ : Fin 1 => branchTag (M := M) (D.core (p.1,p.2 ∘ π))) (p.2 ∘ π)
    rw [hCore,append_prefixLabelSelection]

theorem refineLabels_full_image
    (hCover : ∀ a ∈ A.carrier, ∃ p ∈ C.carrier, (p.1,p.2 ∘ π) = a) :
    (fun q : Mixed M n (1+s) => (q.1,q.2 ∘ prefixLabelSelection π)) ''
      (D.refineLabels π hC hDouble hTagged hFibres).point '' C.carrier = D.point '' A.carrier := by
  apply Set.Subset.antisymm
  · rintro q ⟨z,⟨p,hp,rfl⟩,rfl⟩
    exact ⟨(p.1,p.2 ∘ π),labelRefinement_source_subset π hFibres p hp,
      (D.refineLabels_point_commutes π hC hDouble hTagged hFibres p hp).symm⟩
  · rintro q ⟨a,ha,rfl⟩
    obtain ⟨p,hp,hpa⟩ := hCover a ha
    refine ⟨(D.refineLabels π hC hDouble hTagged hFibres).point p,⟨p,hp,rfl⟩,?_⟩
    exact (D.refineLabels_point_commutes π hC hDouble hTagged hFibres p hp).trans (congrArg D.point hpa)

end CentripetalData
end DiamondIntegral.Section6
