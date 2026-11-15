import «section 5».MonomialGammaGraphSupports
import «section 5».CylindricalFibreSyntax

/-! Original-ground Gamma supports for cylindrical endpoint families on
monomial pieces. All endpoint parameters remain quantified. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace DiamondIntegral.Section5
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section3.GammaParameters
open IntegrationInACVF.Section3 IntegrationInACVF.Section3ACVF
open DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {n : ℕ}
variable {X : GammaGroundDefSet hc B (rawRVUnitSpace (M := M) n)}

theorem CylinderFibreKind.condition_fullDefinable (shape : CylinderFibreKind)
    {ι : Type} [Finite ι] (a : Fin shape.endpoints → ι) (t : ι) :
    FullGammaSyntax.Definable (integrationGammaBase B)
      (fun z => shape.condition (z ∘ a) (z t)) := by
  cases shape with
  | graph => exact FullGammaSyntax.eq_definable _ t (a 0)
  | band => exact (FullGammaSyntax.lt_definable _ (a 0) t).and (FullGammaSyntax.lt_definable _ t (a 1))
  | upperRay => exact FullGammaSyntax.lt_definable _ (a 0) t
  | lowerRay => exact FullGammaSyntax.lt_definable _ t (a 0)
  | line => exact FullGammaSyntax.Definable.true_ _

def GroundMonomialPiece.endpointGammaSupport (P : GroundMonomialPiece X) (shape : CylinderFibreKind)
    (D : Fin shape.endpoints → GammaGroundDefSet hc B ((volumeGammaSpace hc).power (Fin (n+1)))) :
    GammaGroundDefSet hc B ((volumeGammaSpace hc).power (Fin (P.split.freeArity+1))) := by
  let q : Fin shape.endpoints → Fin (P.split.freeArity+1) →
      (Fin (P.split.freeArity+1) ⊕ Fin shape.endpoints) := fun j i =>
    Fin.lastCases (Sum.inr j) (fun k => Sum.inl k.castSucc) i
  have hgraphs := FullGammaSyntax.Definable.forall_finite (fun j : Fin shape.endpoints =>
    ((gammaGroundGammaPower_definable_iff (P.reconstructedGammaGraph (D j)).carrier).mp
      (P.reconstructedGammaGraph (D j)).definable).reindex (q j))
  have hcond := shape.condition_fullDefinable (B := B)
    (Sum.inr : Fin shape.endpoints → Fin (P.split.freeArity+1) ⊕ Fin shape.endpoints)
    (Sum.inl (Fin.last P.split.freeArity))
  have hI := ((gammaGroundGammaPower_definable_iff P.gamma.carrier).mp P.gamma.definable).reindex
    (Fin.castSucc : Fin P.split.freeArity → Fin (P.split.freeArity+1))
  let K : Set (Fin (P.split.freeArity+1) → Values.Gamma (M := M)) :=
    {z | (z ∘ Fin.castSucc) ∈ P.gamma.carrier ∧ ∃ a : Fin shape.endpoints → Values.Gamma (M := M),
      (∀ j, Fin.snoc (z ∘ Fin.castSucc) (a j) ∈ (P.reconstructedGammaGraph (D j)).carrier) ∧
        shape.condition a (z (Fin.last P.split.freeArity))}
  refine ⟨K, gammaGroundGammaPower_predicate_definable _ ?_⟩
  apply (hI.and (hgraphs.and hcond).exists_block).congr
  intro z
  change (_ ∧ ∃ a, (∀ j, Sum.elim z a ∘ q j ∈ _) ∧ _) ↔ _
  have hq (a : Fin shape.endpoints → Values.Gamma (M := M)) (j : Fin shape.endpoints) :
      Sum.elim z a ∘ q j = Fin.snoc (z ∘ Fin.castSucc) (a j) := by
    funext i
    refine Fin.lastCases ?_ (fun k => ?_) i <;> simp only [q, Function.comp_def, Fin.lastCases_last,
      Fin.lastCases_castSucc, Sum.elim_inr, Sum.elim_inl, Fin.snoc_last, Fin.snoc_castSucc]
  simp only [hq, Function.comp_def, Sum.elim_inl, Sum.elim_inr]

theorem GroundMonomialPiece.endpointGammaSupport_row (P : GroundMonomialPiece X) (shape : CylinderFibreKind)
    (D : Fin shape.endpoints → GammaGroundDefSet hc B ((volumeGammaSpace hc).power (Fin (n+1))))
    (η : Fin P.split.freeArity → Values.Gamma (M := M)) (γ : Values.Gamma (M := M)) :
    Fin.snoc η γ ∈ (P.endpointGammaSupport shape D).carrier ↔
      η ∈ P.gamma.carrier ∧ ∃ a : Fin shape.endpoints → Values.Gamma (M := M),
        (∀ j, Fin.snoc η (a j) ∈ (P.reconstructedGammaGraph (D j)).carrier) ∧ shape.condition a γ := by
  have hi : (Fin.snoc (α := fun _ : Fin (P.split.freeArity+1) => Values.Gamma (M := M)) η γ) ∘ Fin.castSucc = η := by
    funext j
    simp only [Function.comp_def, Fin.snoc_castSucc]
  change (_ ∧ _) ↔ _
  rw [hi, Fin.snoc_last]

end DiamondIntegral.Section5
