import «section 6».CentripetalProgramAdmissibility

/-! The geometric invariant of every program prefix, including the
actual protected images. It is retained by a realized whole program. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {p n r s k : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

structure TemplateFibreGeometry (A : MixedSetParameterTemplate (M := M) S p n r)
    (P : Fin k → MixedSetParameterTemplate (M := M) S p n r) (a : Fin p → M) : Prop where
  proper : ProperInvariant (S ∪ Set.range a) (A.fibre a).carrier
  doublyBounded : VFDoublyBounded (A.fibre a).carrier
  subset : ∀ i,((P i).fibre a).carrier ⊆ (A.fibre a).carrier
  piecesProper : ∀ i,ProperInvariant (S ∪ Set.range a) ((P i).fibre a).carrier

theorem CentripetalProgramRealization.outputGeometry
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    {T : CentripetalProgramTemplate (M := M) S p n r s}
    {A : MixedSetParameterTemplate (M := M) S p n r}
    {P : Fin k → MixedSetParameterTemplate (M := M) S p n r} {a : Fin p → M}
    (F : CentripetalProgramRealization (G := G) T A P a) (h : TemplateFibreGeometry A P a) :
    TemplateFibreGeometry (T.target A) (fun i => T.pieceTarget A (P i)) a := by
  refine ⟨F.chain.toChain.toSpecial.target_properInvariant h00 hc hκ hs hv,
    F.chain.toChain.toSpecial.target_vfDoublyBounded h.doublyBounded,?_,?_⟩
  · intro i
    rw [F.pieces i (h.subset i)]
    rintro y ⟨x,hx⟩
    exact hx ▸ (F.map.restrict (h.subset i) x).property
  · intro i
    rw [F.pieces i (h.subset i)]
    exact ((F.chain.atPiece i).literal_restriction h00 (h.subset i)).target_properInvariant h00 hc hκ hs hv

end DiamondIntegral.Section6
