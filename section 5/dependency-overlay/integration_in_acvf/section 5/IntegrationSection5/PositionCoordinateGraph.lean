import IntegrationSection5.CellGammaBridge

/-! Uniformly insert an actual positioning graph at any selected VF
coordinate while retaining all complementary VF coordinates and RV labels. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section5 SpecialTransformations.Section3
open IntegrationInACVF.Section4 IntegrationInACVF.Section4.Cells
open IntegrationInACVF.Section3ACVF
namespace IntegrationInACVF.Section5
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {G : GammaParameters.Base (M := M)} {n m : ℕ}

theorem position_coordinate_scalar_gamma (A : Set (Point (M := M) n m))
    (hA : GammaSetDefinable G A) (i : Fin n) (D : Set (VF (M := M)))
    (hi : ∀ p ∈ A, vfAt p i ∈ D) (f : VF (M := M) → VF (M := M))
    (hf : GammaParameters.DefinableOverBase G (fun _ : Fin 2 => .vf) (positionCodes D f)) :
    GammaScalarGraphDefinable G (fun p x => p ∈ A ∧ x = f (vfAt p i)) := by
  let σ : Fin 2 → Fin ((n+m)+(1+0)) :=
    ![Fin.castAdd (1+0) (Fin.castAdd m i),Fin.natAdd (n+m) (0 : Fin (1+0))]
  let C := {z : Fin ((n+m)+(1+0)) → M | z ∘ σ ∈ positionCodes D f}
  have hC : FullBaseAtomicity.OverBase (GammaBaseBridge.fullBase G) C :=
    FullBaseAtomicity.OverBase.preimage_comp (GammaBaseBridge.of_gamma G hf) σ
  have h := GammaTupleGraphs.relation_of_full G (n := n) (m := m) (u := 1) (w := 0) C hC
  apply GammaGraphDefinable.congr ((gammaLogicInput G).restrict_graph hA h)
  intro p z
  have hCode : Fin.append (gammaPointCode p) (gammaPointCode z) ∘ σ =
      ![(vfAt p i).val,(vfAt z 0).val] := by
    funext j
    fin_cases j <;> simp [σ,gammaPointCode,vfAt]
    exact Fin.append_left _ _ (0 : Fin 1)
  constructor
  · rintro ⟨hp,hc⟩
    change Fin.append (gammaPointCode p) (gammaPointCode z) ∘ σ ∈ positionCodes D f at hc
    rw [hCode] at hc
    obtain ⟨a,ha,he⟩ := hc
    have haEq : a = vfAt p i := Subtype.ext (congrFun he 0).symm
    have hz : vfAt z 0 = f a := Subtype.ext (congrFun he 1)
    exact ⟨hp,hz.trans (congrArg f haEq)⟩
  · rintro ⟨hp,hz⟩
    refine ⟨hp,?_⟩
    change Fin.append (gammaPointCode p) (gammaPointCode z) ∘ σ ∈ positionCodes D f
    rw [hCode]
    refine ⟨vfAt p i,hi p hp,?_⟩
    funext j
    fin_cases j
    · rfl
    · exact congrArg Subtype.val hz

end IntegrationInACVF.Section5
