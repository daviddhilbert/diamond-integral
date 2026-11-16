import «section 6».CentripetalProgramRealizations

/-! Whole-program admissibility realizes an actual synchronized chain,
including exact intermediate and protected images. No existence of a
prepared chain is assumed by this interpretation theorem. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {p n r s k : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

theorem CentripetalProgramTemplate.exists_realization
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (T : CentripetalProgramTemplate (M := M) S p n r s)
    (A : MixedSetParameterTemplate (M := M) S p n r)
    (P : Fin k → MixedSetParameterTemplate (M := M) S p n r) (a : Fin p → M)
    (ha : a ∈ T.good A P) (hA : ProperInvariant (S ∪ Set.range a) (A.fibre a).carrier)
    (hAD : VFDoublyBounded (A.fibre a).carrier)
    (hPA : ∀ i,((P i).fibre a).carrier ⊆ (A.fibre a).carrier)
    (hP : ∀ i,ProperInvariant (S ∪ Set.range a) ((P i).fibre a).carrier) :
    Nonempty (CentripetalProgramRealization (G := G) T A P a) := by
  induction T with
  | identity r =>
    exact CentripetalProgramRealization.ofMap h00 (.identity r) A P a (Map.id (A.fibre a))
      (.identity _ hA _ hPA hP) (identityParameterTransition_at A a)
  | regularize r =>
    exact CentripetalProgramRealization.ofMap h00 (.regularize r) A P a (regularization (A.fibre a))
      (.regularize _ hA hAD _ hPA hP (fun i => hAD.mono (hPA i))) (regularizationParameterTransition_at A a)
  | centripetal T =>
    obtain ⟨D,hj,hU,hCoeff,hFocus,hE⟩ := T.exists_component hc hv A P a ha hA hAD hPA hP
    let E i := (hE i).choose
    exact CentripetalProgramRealization.ofMap h00 (.centripetal T) A P a D.bijection
      (.centripetal _ D _ hPA E (fun i => (hE i).choose_spec))
      (focusComponentTransition_at T A a ha.1.1.1 ha.1.1.2 D hj hU hCoeff hFocus)
  | @comp r s t F H ihF ihH =>
    obtain ⟨f⟩ := ihF A P ha.1 hA hAD hPA hP
    have hB := f.chain.toChain.toSpecial.target_properInvariant h00 hc hκ hs hv
    have hBD := f.chain.toChain.toSpecial.target_vfDoublyBounded hAD
    have hPB (i) : ((F.pieceTarget A (P i)).fibre a).carrier ⊆ ((F.target A).fibre a).carrier := by
      rw [f.pieces i (hPA i)]
      rintro q ⟨x,hx⟩
      exact hx ▸ (f.map.restrict (hPA i) x).property
    have hPiB (i) : ProperInvariant (S ∪ Set.range a) ((F.pieceTarget A (P i)).fibre a).carrier := by
      rw [f.pieces i (hPA i)]
      exact ((f.chain.atPiece i).literal_restriction h00 (hPA i)).target_properInvariant h00 hc hκ hs hv
    obtain ⟨g⟩ := ihH (F.target A) (fun i => F.pieceTarget A (P i)) ha.2 hB hBD hPB hPiB
    have hG := g.chain.changePieces (fun i => f.pieces i (hPA i))
    apply CentripetalProgramRealization.ofMap h00 (.comp F H) A P a (g.map.comp f.map)
      (.comp (fun i => (P i).fibre a) hPA f.chain hG)
    exact parameterRelationComp_at (P := rawMixedSpace n r) (Q := rawMixedSpace n s)
      (R := rawMixedSpace n t) (S := S) a (F.transition A).graph (H.transition (F.target A)).graph
      f.map g.map f.graph g.graph

end DiamondIntegral.Section6
