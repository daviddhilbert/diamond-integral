import IntegrationSection5.CanonicalProductSource
import IntegrationSection5.CanonicalRVSliceGeometry
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.DefinableGeometry.Space.prod
  SpecialTransformations.Section4.realSpace SpecialTransformations.Milestone0.sortEval
  SpecialTransformations.Section4.vfSpace SpecialTransformations.Section4.rvSpace
  SpecialTransformations.Section5.pointSpace
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section5
namespace IntegrationInACVF.Section5
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {S : Set M} {n m l : ℕ} {A : DefSet (M := M) S 1 m}
variable {R : DefSet (M := M) S (n+1) l}

def canonicalClassPassive (A : DefSet (M := M) S 1 m) (ρ : Fin m → Fin l)
    (Q : Point (M := M) (n+1) l → Prop) (p : Point (M := M) (n+1) (1+l)) : Prop :=
  Q (forgetCoordinateLabel p) ∧ ∃ a ∈ carrier A,
    a.2 = p.2 ∘ Fin.natAdd 1 ∘ ρ ∧ rv (vfAt a 0) = p.2 0

theorem canonicalClassPassive_independent (ρ : Fin m → Fin l)
    (Q : Point (M := M) (n+1) l → Prop)
    (hQ : ∀ p x, Q (replace 0 p x) ↔ Q p) :
    ∀ p x, canonicalClassPassive A ρ Q (replace 0 p x) ↔ canonicalClassPassive A ρ Q p := by
  intro p x
  change (Q (replace 0 (forgetCoordinateLabel p) x) ∧ _) ↔ (Q (forgetCoordinateLabel p) ∧ _)
  rw [hQ]
  rfl

theorem activeUnaryProjection_dropCanonical_comp (ρ : Fin m → Fin l)
    (p : Point (M := M) (n+1) l) :
    activeUnaryProjection 0 (Fin.natAdd 1 ∘ ρ) (coordinateCanonical 0 p) = activeUnaryProjection 0 ρ p := by
  refine Prod.ext rfl ?_
  exact congrArg (fun s => s ∘ ρ) (coordinateCanonical_oldRV 0 p)

theorem coordinateCanonical_class_product_source (ρ : Fin m → Fin l)
    (Q : Point (M := M) (n+1) l → Prop)
    (hR : carrier R = {p | activeUnaryProjection 0 ρ p ∈ carrier A ∧ Q p})
    (hClass : ∀ p ∈ carrier A, ∀ q ∈ carrier A, p.2 = q.2 → rv (vfAt p 0) = rv (vfAt q 0)) :
    carrier (coordinateCanonicalImage R 0) =
      {p | activeUnaryProjection 0 (Fin.natAdd 1 ∘ ρ) p ∈ carrier A ∧ canonicalClassPassive A ρ Q p} := by
  ext p
  constructor
  · rintro ⟨r,rfl⟩
    have hr := (Set.ext_iff.mp hR r.val).mp r.property
    change activeUnaryProjection 0 (Fin.natAdd 1 ∘ ρ) (coordinateCanonical 0 r.val) ∈ carrier A ∧ _
    rw [activeUnaryProjection_dropCanonical_comp]
    refine ⟨hr.1,?_,activeUnaryProjection 0 ρ r.val,hr.1,?_,?_⟩
    · change Q (forgetCoordinateLabel (coordinateCanonical 0 r.val))
      rw [forgetCoordinateLabel_canonical]
      exact hr.2
    · exact (congrArg (fun s => s ∘ ρ) (coordinateCanonical_oldRV 0 r.val)).symm
    · change rv (vfAt r.val 0) = Fin.append (fun _ : Fin 1 => rv (vfAt r.val 0)) r.val.2 (0 : Fin (1+l))
      exact (Fin.append_left (fun _ : Fin 1 => rv (vfAt r.val 0)) r.val.2 (0 : Fin 1)).symm
  · rintro ⟨hpA,hpQ,a,ha,hLabels,hTag⟩
    let old := forgetCoordinateLabel p
    have hOldA : activeUnaryProjection 0 ρ old ∈ carrier A := hpA
    have hold : old ∈ carrier R := (Set.ext_iff.mp hR old).mpr ⟨hOldA,hpQ⟩
    have hClassEq : rv (vfAt a 0) = rv (vfAt p 0) :=
      hClass a ha (activeUnaryProjection 0 ρ old) hOldA hLabels
    have hHead : p.2 0 = rv (vfAt p 0) := hTag.symm.trans hClassEq
    refine ⟨⟨old,hold⟩,?_⟩
    change coordinateCanonical 0 old = p
    apply Prod.ext
    · rfl
    · funext j
      cases j using Fin.addCases with
      | left j =>
        fin_cases j
        change Fin.append (fun _ : Fin 1 => rv (vfAt old 0)) old.2 (0 : Fin (1+l)) = p.2 0
        exact (Fin.append_left _ _ (0 : Fin 1)).trans hHead.symm
      | right j => simp only [coordinateCanonical,Fin.append_right]; rfl

end IntegrationInACVF.Section5
