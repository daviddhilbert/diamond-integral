import «section 3».GammaMeasuredIsomorphismSchemata

/-! Reverse interface to the native Gamma chart predicate. Its proof
uses the existing correspondence formula and applies to complete density
code relations without RV-function validity. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3500000
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4
open IntegrationInACVF.Section6 IntegrationInACVF.Section7
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)}
variable {p a b k : ℕ} {sp : Fin p → SortTag}

theorem gamma_volumeChartGammaRowValid_of_typed
    (F : GammaRVVolumeSchema B p a k sp) (G : GammaRVVolumeSchema B p b k sp)
    {H : Set (Fin ((p+a)+b) → M)}
    (hH : DefinableOverBase B (Fin.append (Fin.append sp (fun _ : Fin a => .rv)) (fun _ : Fin b => .rv)) H)
    (z : Fin p → M) (hz : ∀ i, sortEval (sp i) (z i))
    (hBalance : ∀ (x : Fin a → M) (y : Fin b → M)
      (u v : Fin ((k+1)+1) → CanonicalRV.RVSort M),
      Fin.append (Fin.append z x) (rvValues u) ∈ weightedVolumeGraph F →
      Fin.append (Fin.append z x) y ∈ H →
      Fin.append (Fin.append z y) (rvValues v) ∈ weightedVolumeGraph G →
      Fin.append (rvValues u) (rvValues v) ∈ rvProductGammaBalance (M := M) ((k+1)+1)) :
    volumeChartGammaRowValid F G H z := by
  refine ⟨hz,?_⟩
  intro r hr
  have hRV (i : Fin (((k+1)+1)+((k+1)+1))) : iRV (r i) := by
    simpa only [Fin.append_right,sortEval,iRV] using
      (schemaVolumeCorrespondence_definable (weightedVolumeSchema F) (weightedVolumeSchema G) hH).proper
        _ hr (Fin.natAdd p i)
  let t : Fin (((k+1)+1)+((k+1)+1)) → CanonicalRV.RVSort M := fun i => ⟨r i,hRV i⟩
  let u := t ∘ Fin.castAdd ((k+1)+1)
  let v := t ∘ Fin.natAdd ((k+1)+1)
  have he : Fin.append (rvValues u) (rvValues v) = r := Fin.append_castAdd_natAdd
  rw [← he] at hr ⊢
  obtain ⟨x,y,hx,hxy,hy⟩ := (schemaVolumeCorrespondence_append
    (weightedVolumeSchema F) (weightedVolumeSchema G) H z (rvValues u) (rvValues v)
      hz (fun i => (u i).property) (fun i => (v i).property)).mp hr
  exact hBalance x y u v hx hxy hy

end DiamondIntegral.Section3
