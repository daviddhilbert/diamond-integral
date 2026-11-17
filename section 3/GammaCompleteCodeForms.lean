import «section 3».GammaMeasuredSchemaRowForms
import «section 3».GammaRVFormCodeRows

/-! Realize a Gamma form directly from its complete code graph.
The graph may have many RV representatives for one Gamma value. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4500000
set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.Section4.rawRVSpace
  SpecialTransformations.Section4.realSpace SpecialTransformations.DefinableGeometry.Space.ofEmbedding
  SpecialTransformations.DefinableGeometry.Space.prod
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {a : ℕ}

def gammaCompleteCodeForm
    (A : GammaGroundDefSet hc B (rawRVSpace (M := M) a))
    (f : A → (volumeGammaSpace hc).Carrier)
    (D : Set (Fin (a+1) → M))
    (hD : DefinableOverBase B (fun _ => .rv) D)
    (hCode : ∀ w ∈ D, w ∘ Fin.natAdd a ∈ (volumeGammaSpace hc).domain)
    (hGraph : ∀ x : Fin a → CanonicalRV.RVSort M, ∀ c : (volumeGammaSpace hc).domain,
      Fin.append (rvValues x) c.val ∈ D ↔ ∃ u : A, u.val = x ∧ f u = (volumeGammaSpace hc).decode c) :
    GammaGroundVolumeForm hc B A := by
  refine ⟨fun u => ⟨f u,Set.mem_univ _⟩,?_⟩
  apply GammaGroundDefinable.of_real_codes
  have hRaw : GammaGroundRawDefinable hc B D :=
    (gammaGroundRawDefinable_iff_sortedBase (hc := hc) (ground := B) hD.proper).mpr hD
  let ix : Fin (a+1) → Fin a ⊕ Fin 1 := Fin.addCases Sum.inl Sum.inr
  apply (hRaw.preimage_comp ix).congr
  intro w
  constructor
  · intro hw
    have hRV (j : Fin a) : iRV (w (Sum.inl j)) := by
      simpa only [Function.comp_apply,ix,Fin.addCases_left,sortEval,iRV] using
        hD.proper _ hw (Fin.castAdd 1 j)
    have hC : w ∘ Sum.inr ∈ (volumeGammaSpace hc).domain := by
      simpa only [Function.comp_def,ix,Fin.addCases_right] using hCode _ hw
    let r : Fin a → CanonicalRV.RVSort M := fun j => ⟨w (Sum.inl j),hRV j⟩
    let c : (volumeGammaSpace hc).domain := ⟨w ∘ Sum.inr,hC⟩
    have he : w ∘ ix = Fin.append (rvValues r) c.val := by
      funext i
      refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;>
        simp only [Function.comp_apply,ix,Fin.addCases_left,Fin.addCases_right,Fin.append_left,Fin.append_right] <;> rfl
    obtain ⟨u,hu,hf⟩ := (hGraph r c).mp (he ▸ hw)
    refine ⟨⟨⟨r,rfl⟩,hC⟩,u,?_,hf⟩
    exact hu.trans (rvValues_injective (rvValues_decode ⟨w ∘ Sum.inl,⟨r,rfl⟩⟩)).symm
  · rintro ⟨⟨hRV,hC⟩,u,hu,hf⟩
    let c : (volumeGammaSpace hc).domain := ⟨w ∘ Sum.inr,hC⟩
    have hd := (hGraph u.val c).mpr ⟨u,rfl,hf⟩
    have hValues : rvValues u.val = w ∘ Sum.inl :=
      (congrArg rvValues hu).trans (rvValues_decode ⟨w ∘ Sum.inl,hRV⟩)
    have he : Fin.append (rvValues u.val) c.val = w ∘ ix := by
      funext i
      refine Fin.addCases (fun j => ?_) (fun j => ?_) i
      · simpa only [Fin.append_left,Function.comp_apply,ix,Fin.addCases_left] using congrFun hValues j
      · simp only [Fin.append_right,Function.comp_apply,ix,Fin.addCases_right]; rfl
    change w ∘ ix ∈ D
    exact he ▸ hd

@[simp] theorem gammaCompleteCodeForm_value
    (A : GammaGroundDefSet hc B (rawRVSpace (M := M) a))
    (f : A → (volumeGammaSpace hc).Carrier) (D) (hD) (hCode) (hGraph) (u : A) :
    (gammaCompleteCodeForm A f D hD hCode hGraph u).val = f u := rfl

end DiamondIntegral.Section3
