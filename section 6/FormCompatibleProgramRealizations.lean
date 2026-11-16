import «section 6».FormCompatibleProgramMaps

/-! The complete core-form program test constructs an actual permitted
form-compatible chain. Intermediate Gamma graphs are realized by the
same actual maps and their inverse transport, at every parameter. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section8 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {p n r s k : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

theorem CentripetalProgramTemplate.exists_form_compatible_realization
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (T : CentripetalProgramTemplate (M := M) S p n r s)
    (A : MixedSetParameterTemplate (M := M) S p n r)
    (P : Fin k → MixedSetParameterTemplate (M := M) S p n r)
    (W : GammaFormParameterTemplate (M := M) S p n r) (a : Fin p → M)
    (ha : a ∈ T.good A P) (hCore : a ∈ T.coreFormGood A W)
    (hA : ProperInvariant (S ∪ Set.range a) (A.fibre a).carrier)
    (hAD : VFDoublyBounded (A.fibre a).carrier)
    (hPA : ∀ i,((P i).fibre a).carrier ⊆ (A.fibre a).carrier)
    (hP : ∀ i,ProperInvariant (S ∪ Set.range a) ((P i).fibre a).carrier)
    (ω : Map (A.fibre a) (DefSet.univ (rawGammaPresentation (M := M)) (S ∪ Set.range a)))
    (hW : {z | Sum.elim a z ∈ W.graph}=(rawMixedSpace n r).relation rawGammaPresentation ω.graph) :
    ∃ F : CentripetalProgramRealization (G := G) T A P a,
      FormCompatibleSynchronizedChain (G := G) (Fin k) (A.fibre a) ((T.target A).fibre a) F.map
        (fun i => (P i).fibre a) ω := by
  induction T with
  | identity r =>
    exact CentripetalProgramRealization.ofMap_form_compatible h00 (.identity r) A P a (Map.id (A.fibre a)) ω
      (.identity _ hA _ hPA hP ω) (identityParameterTransition_at A a)
  | regularize r =>
    exact CentripetalProgramRealization.ofMap_form_compatible h00 (.regularize r) A P a (regularization (A.fibre a)) ω
      (.regularize _ hA hAD _ hPA hP (fun i => hAD.mono (hPA i)) ω) (regularizationParameterTransition_at A a)
  | @centripetal r T =>
    obtain ⟨D,hj,hU,hCoeff,hFocus,hE⟩ := T.exists_component hc hv A P a ha hA hAD hPA hP
    let E i := (hE i).choose
    have hGraph := focusComponentTransition_at T A a ha.1.1.1 ha.1.1.2 D hj hU hCoeff hFocus
    change a ∈ gammaCoreConstantParameterLocus (focusComponentTransition T A) W.graph T.coordinate _ at hCore
    rw [← hj] at hCore
    have hDForm := (gammaCoreConstantParameterLocus_at_component a _ _ D h00 ω hGraph hW).mp hCore
    exact CentripetalProgramRealization.ofMap_form_compatible h00 (.centripetal T) A P a D.bijection ω
      (.centripetal _ D _ hPA E (fun i => (hE i).choose_spec) ω hDForm) hGraph
  | @comp r s t F H ihF ihH =>
    obtain ⟨f,hf⟩ := ihF A P W ha.1 hCore.1 hA hAD hPA hP ω hW
    have hfBij := hf.toSynchronized.toChain.toSpecial.bijective h00
    have hB := hf.toSynchronized.toChain.toSpecial.target_properInvariant h00 hc hκ hs hv
    have hBD := hf.toSynchronized.toChain.toSpecial.target_vfDoublyBounded hAD
    have hPB (i) : ((F.pieceTarget A (P i)).fibre a).carrier ⊆ ((F.target A).fibre a).carrier := by
      rw [f.pieces i (hPA i)]
      rintro q ⟨x,hx⟩
      exact hx ▸ (f.map.restrict (hPA i) x).property
    have hPiB (i) : ProperInvariant (S ∪ Set.range a) ((F.pieceTarget A (P i)).fibre a).carrier := by
      rw [f.pieces i (hPA i)]
      exact ((hf.toSynchronized.atPiece i).literal_restriction h00 (hPA i)).target_properInvariant h00 hc hκ hs hv
    let η := ω.comp (f.map.inverse hfBij)
    have hTransport (x : A.fibre a) : (η (f.map x)).val=(ω x).val := by
      change (ω (f.map.inverse hfBij (f.map x))).val=(ω x).val
      rw [Map.inverse_apply]
    have hGammaGraph := gammaTransitionImage_at a (F.transition A).graph W.graph f.map hfBij ω f.graph hW
    obtain ⟨g,hg⟩ := ihH (F.target A) (fun i => F.pieceTarget A (P i)) (W.transport (F.transition A))
      ha.2 hCore.2 hB hBD hPB hPiB η hGammaGraph
    have hG := hg.changePieces (fun i => f.pieces i (hPA i))
    apply CentripetalProgramRealization.ofMap_form_compatible h00 (.comp F H) A P a (g.map.comp f.map) ω
      (.comp (fun i => (P i).fibre a) hPA hf η hTransport hG)
    exact parameterRelationComp_at (P := rawMixedSpace n r) (Q := rawMixedSpace n s)
      (R := rawMixedSpace n t) (S := S) a (F.transition A).graph (H.transition (F.target A)).graph
      f.map g.map f.graph g.graph

end DiamondIntegral.Section6
