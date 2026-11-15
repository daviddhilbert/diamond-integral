import IntegrationSection5.CanonicalHeadGeometry
import IntegrationSection5.SharedRVProductImage
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
variable {S : Set M} {m : ℕ} {R : DefSet (M := M) S 2 m}
variable {A B : DefSet (M := M) S 1 m}

def canonicalProductPassive (k : Fin m) (B : DefSet (M := M) S 1 m)
    (p : Point (M := M) 2 (1+m)) : Prop :=
  activeUnaryProjection 1 (Fin.natAdd 1) p ∈ carrier B ∧ p.2 0 = p.2 (Fin.natAdd 1 k)

theorem canonicalProductPassive_independent (k : Fin m) (B : DefSet (M := M) S 1 m)
    (p : Point (M := M) 2 (1+m)) (x : VF (M := M)) :
    canonicalProductPassive k B (replace 0 p x) ↔ canonicalProductPassive k B p := by
  have he : activeUnaryProjection 1 (Fin.natAdd 1) (replace 0 p x) =
      activeUnaryProjection 1 (Fin.natAdd 1) p := by
    apply Prod.ext
    · funext j; fin_cases j
      simp only [activeUnaryProjection,replace,vfAt,Function.update_of_ne (by decide : (1 : Fin 2) ≠ 0)]
    · rfl
  change (_ ∈ carrier B ∧ _) ↔ (_ ∈ carrier B ∧ _)
  rw [he]
  rfl

theorem coordinateCanonical_shared_product_source (k : Fin m) (hTag : Tagged (carrier A) 0 k)
    (hR : carrier R = {p | activeUnaryProjection 0 id p ∈ carrier A ∧
      activeUnaryProjection 1 id p ∈ carrier B}) :
    carrier (coordinateCanonicalImage R 0) =
      {p | activeUnaryProjection 0 (Fin.natAdd 1) p ∈ carrier A ∧ canonicalProductPassive k B p} := by
  ext p
  constructor
  · rintro ⟨r,rfl⟩
    have h := (Set.ext_iff.mp hR r.val).mp r.property
    have hProj (j : Fin 2) : activeUnaryProjection j (Fin.natAdd 1) (coordinateCanonical 0 r.val) =
        activeUnaryProjection j id r.val := by
      apply Prod.ext
      · rfl
      · funext t
        simp only [activeUnaryProjection,coordinateCanonical,Function.comp_apply,Fin.append_right,id_eq]
    change activeUnaryProjection 0 (Fin.natAdd 1) (coordinateCanonical 0 r.val) ∈ carrier A ∧
      activeUnaryProjection 1 (Fin.natAdd 1) (coordinateCanonical 0 r.val) ∈ carrier B ∧ _
    rw [hProj 0,hProj 1]
    refine ⟨h.1,h.2,?_⟩
    have ht := hTag (activeUnaryProjection 0 id r.val) h.1
    change Fin.append (fun _ : Fin 1 => rv (vfAt r.val 0)) r.val.2 (0 : Fin (1+m)) =
      Fin.append (fun _ : Fin 1 => rv (vfAt r.val 0)) r.val.2 (Fin.natAdd 1 k)
    rw [Fin.append_right]
    exact (Fin.append_left _ _ (0 : Fin 1)).trans ht.symm
  · rintro ⟨hpA,hpB,hpTag⟩
    let old := forgetCoordinateLabel p
    have hold : old ∈ carrier R := (Set.ext_iff.mp hR old).mpr ⟨hpA,hpB⟩
    have htag := hTag (activeUnaryProjection 0 (Fin.natAdd 1) p) hpA
    have hhead : p.2 0 = rv (vfAt p 0) := hpTag.trans htag
    refine ⟨⟨old,hold⟩,?_⟩
    change coordinateCanonical 0 old = p
    apply Prod.ext
    · rfl
    · funext j
      cases j using Fin.addCases with
      | left j =>
        fin_cases j
        change Fin.append (fun _ : Fin 1 => rv (vfAt old 0)) old.2 (0 : Fin (1+m)) = p.2 0
        exact (Fin.append_left _ _ (0 : Fin 1)).trans hhead.symm
      | right j => simp only [coordinateCanonical,Fin.append_right]; rfl

end IntegrationInACVF.Section5
