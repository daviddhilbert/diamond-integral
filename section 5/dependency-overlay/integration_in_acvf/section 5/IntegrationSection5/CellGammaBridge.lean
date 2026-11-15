import IntegrationSection4.Cells
import IntegrationSection4.GammaTupleGraphs
import IntegrationSection5.GammaGraphOperations

/-! The actual native VF pair cells and positioning graphs, in the pinned
mixed-point Gamma conventions used by standard contractions. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section5 SpecialTransformations.Section3
open IntegrationInACVF.Section4 IntegrationInACVF.Section4.Cells
open IntegrationInACVF.Section3ACVF
namespace IntegrationInACVF.Section5
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {G : GammaParameters.Base (M := M)}

def cellPoint (p : VF (M := M) × VF (M := M)) : Point (M := M) 2 0 :=
  (![p.1,p.2],Fin.elim0)

def pointCell (p : Point (M := M) 2 0) : VF (M := M) × VF (M := M) := (vfAt p 0,vfAt p 1)

theorem pointCell_cellPoint (p : VF (M := M) × VF (M := M)) : pointCell (cellPoint p) = p := rfl

theorem cellPoint_pointCell (p : Point (M := M) 2 0) : cellPoint (pointCell p) = p := by
  refine Prod.ext ?_ (funext fun j => j.elim0)
  funext j
  fin_cases j <;> rfl

def cellPointSet (R : Set (VF (M := M) × VF (M := M))) : Set (Point (M := M) 2 0) :=
  {p | pointCell p ∈ R}

theorem cellPointSet_gamma (R : Set (VF (M := M) × VF (M := M)))
    (hR : GammaParameters.DefinableOverBase G (fun _ : Fin 2 => .vf) (pairCodes R)) :
    GammaSetDefinable G (cellPointSet R) := by
  have h := GammaTupleGraphs.set_of_full G (n := 2) (m := 0) (pairCodes R) (GammaBaseBridge.of_gamma G hR)
  convert h using 1
  ext p
  constructor
  · intro hp
    refine ⟨pointCell p,hp,?_⟩
    funext j
    fin_cases j <;> rfl
  · rintro ⟨q,hq,he⟩
    have hEq : q = pointCell p := Prod.ext
      (Subtype.ext (congrFun he 0).symm) (Subtype.ext (congrFun he 1).symm)
    change pointCell p ∈ R
    rw [← hEq]
    exact hq

theorem cell_position_scalar_gamma (R : Set (VF (M := M) × VF (M := M)))
    (f : VF (M := M) → VF (M := M))
    (hR : GammaSetDefinable G (cellPointSet R))
    (hf : GammaParameters.DefinableOverBase G (fun _ : Fin 2 => .vf) (positionCodes (first R) f)) :
    GammaScalarGraphDefinable G (fun p x => p ∈ cellPointSet R ∧ x = f (vfAt p 0)) := by
  let C : Set (Fin 3 → M) := {z | ![z 0,z 2] ∈ positionCodes (first R) f}
  have hC : FullBaseAtomicity.OverBase (GammaBaseBridge.fullBase G) C := by
    have hh := FullBaseAtomicity.OverBase.preimage_comp (GammaBaseBridge.of_gamma G hf) (![0,2] : Fin 2 → Fin 3)
    convert hh using 1
    ext z
    have he : z ∘ (![0,2] : Fin 2 → Fin 3) = ![z 0,z 2] := by
      funext j
      fin_cases j <;> rfl
    change ![z 0,z 2] ∈ positionCodes (first R) f ↔ z ∘ ![0,2] ∈ positionCodes (first R) f
    rw [he]
  have h := GammaTupleGraphs.relation_of_full G (n := 2) (m := 0) (u := 1) (w := 0) C hC
  apply GammaGraphDefinable.congr ((gammaLogicInput G).restrict_graph hR h)
  intro p z
  constructor
  · rintro ⟨hp,a,ha,he⟩
    have haEq : a = vfAt p 0 := Subtype.ext (congrFun he 0).symm
    have hz : vfAt z 0 = f a := Subtype.ext (congrFun he 1)
    exact ⟨hp,hz.trans (congrArg f haEq)⟩
  · rintro ⟨hp,hz⟩
    refine ⟨hp,vfAt p 0,⟨pointCell p,hp,rfl⟩,?_⟩
    funext j
    fin_cases j
    · rfl
    · change (vfAt z 0).val = (f (vfAt p 0)).val
      exact congrArg Subtype.val hz

end IntegrationInACVF.Section5
