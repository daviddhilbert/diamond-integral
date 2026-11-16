import «section 6».GammaFormRVTraceBounds

/-! Equality of complete Gamma RV rows identifies the actual form
values on equal old labels, when the receiving form is already constant
on those fibres. The comparison quantifies a representative and never
adjoins it to the parameter base. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section8 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {p n r : ℕ}

theorem GammaFormParameterTemplate.values_eq_of_rvTrace_eq
    (W : GammaFormParameterTemplate (M := M) S p n r) (a b : Fin p → M)
    {A : DefSet (rawMixedSpace (M := M) n r) (S ∪ Set.range a)}
    {B : DefSet (rawMixedSpace (M := M) n r) (S ∪ Set.range b)}
    (ω : Map A (DefSet.univ (rawGammaPresentation (M := M)) (S ∪ Set.range a)))
    (η : Map B (DefSet.univ (rawGammaPresentation (M := M)) (S ∪ Set.range b)))
    (hWa : {z | Sum.elim a z ∈ W.graph}=(rawMixedSpace n r).relation rawGammaPresentation ω.graph)
    (hWb : {z | Sum.elim b z ∈ W.graph}=(rawMixedSpace n r).relation rawGammaPresentation η.graph)
    (hTrace : (W.rvTrace.fibre a).carrier=(W.rvTrace.fibre b).carrier)
    (hConst : ∀ t u : B,t.val.2=u.val.2 → (η t).val=(η u).val)
    (x : A) (y : B) (hTags : x.val.2=y.val.2) : (ω x).val=(η y).val := by
  obtain ⟨c,hc,hcω⟩ := GammaParameters.EndpointLogic.codeValue_surjective (ω x).val
  let tag : RVInfinity M := ⟨c,hc.1⟩
  let v : Fin (r+1) → RVInfinity M := Fin.append x.val.2 (fun _ : Fin 1 => tag)
  have hPrefix : (fun j => v (Fin.castAdd 1 j))=x.val.2 := by
    funext j
    exact Fin.append_left _ _ j
  have hV : v ∈ (W.rvTrace.fibre a).carrier := by
    apply (W.rvTrace_entries a ω hWa v).mpr
    refine ⟨x,hPrefix.symm,?_,?_⟩
    · simpa only [v,Fin.append_right] using hc
    · simpa only [v,Fin.append_right] using hcω
  have hVb : v ∈ (W.rvTrace.fibre b).carrier := hTrace ▸ hV
  obtain ⟨t,hTV,hNZ,hCode⟩ := (W.rvTrace_entries b η hWb v).mp hVb
  have hValue : (ω x).val=(η t).val := hcω.symm.trans (by
    simpa only [v,Fin.append_right] using hCode)
  exact hValue.trans (hConst t y (hTV.trans (hPrefix.trans hTags)))

end DiamondIntegral.Section6
