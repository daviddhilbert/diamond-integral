import «section 3».GammaGroundMapRealization

/-! Simultaneously realize finitely many heterogeneous Gamma-ground
maps over one small real set, preserving the original VF field. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : GammaParameters.Base (M := M)}

theorem gammaGroundMaps_realizeFinite {ι : Type} [Fintype ι]
    (P Q : ι → Space LRV M)
    (A : ∀ i, GammaGroundDefSet hc B (P i)) (D : ∀ i, GammaGroundDefSet hc B (Q i))
    (f : ∀ i, GammaGroundMap (A i) (D i))
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hS : Cardinal.mk B.real < κ) :
    ∃ T : Set M, B.real ⊆ T ∧ Cardinal.mk T < κ ∧ vfParameterField T = vfParameterField B.real ∧
      ∀ i, (P i).Definable T (A i).carrier ∧ (Q i).Definable T (D i).carrier ∧
        ((P i).prod (Q i)).Definable T {z | ∃ a : A i,a.val=z.1 ∧ (f i a).val=z.2} := by
  let J := ι × Fin 3
  let spaces (j : J) : Space LRV M :=
    Fin.cases (P j.1) (Fin.cases (Q j.1) (Fin.cases ((P j.1).prod (Q j.1)) (fun i => i.elim0))) j.2
  let sets (j : J) : Set (spaces j).Carrier := by
    refine Fin.cases (motive := fun z => Set (spaces (j.1,z)).Carrier) ?_ ?_ j.2
    · exact (A j.1).carrier
    · intro z
      refine Fin.cases (motive := fun z => Set (spaces (j.1,z.succ)).Carrier) ?_ ?_ z
      · exact (D j.1).carrier
      · intro z
        refine Fin.cases (motive := fun z => Set (spaces (j.1,z.succ.succ)).Carrier) ?_ ?_ z
        · exact {z | ∃ a : A j.1,a.val=z.1 ∧ (f j.1 a).val=z.2}
        · intro z
          exact z.elim0
  have hsets (j : J) : GammaGroundDefinable hc B (spaces j) (sets j) := by
    rcases j with ⟨i,j⟩
    fin_cases j
    · exact (A i).definable
    · exact (D i).definable
    · exact (f i).graph_definable
  let E := (Fintype.equivFin J).symm
  obtain ⟨T,hT,hsmall,hfield,h⟩ := GammaGroundDefinable.realizeFinite
    (fun i => spaces (E i)) (fun i => sets (E i)) (fun i => hsets (E i)) hκ hS
  refine ⟨T,hT,hsmall,hfield,fun i => ?_⟩
  have hJ (j : J) : (spaces j).Definable T (sets j) :=
    Eq.mp (congrArg (fun q => (spaces q).Definable T (sets q)) ((Fintype.equivFin J).symm_apply_apply j))
      (h ((Fintype.equivFin J) j))
  exact ⟨hJ (i,0),hJ (i,1),hJ (i,2)⟩

end DiamondIntegral.Section3
