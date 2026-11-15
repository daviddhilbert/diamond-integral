import IntegrationSection5.MixedPositionDefinability
import IntegrationSection5.MixedFibreDefinability
import IntegrationSection4.DefinableParadigms

noncomputable section
set_option backward.isDefEq.respectTransparency false

set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.DefinableGeometry.Space.prod
  SpecialTransformations.Section4.realSpace SpecialTransformations.Milestone0.sortEval
  SpecialTransformations.Section4.vfSpace SpecialTransformations.Section4.rvSpace
  SpecialTransformations.Section5.pointSpace

open Set Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters SpecialTransformations.Section5
open IntegrationInACVF.Section3 IntegrationInACVF.Section3ACVF IntegrationInACVF.Section4

namespace IntegrationInACVF.Section5

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

theorem mixedPairFibre_nonempty {G : GammaParameters.Base (M := M)} {m d : ℕ}
    {A : Set (Point (M := M) 2 m)} (P : GammaRVMap G A d) (a₀ : A) : (mixedPairFibre P a₀).Nonempty := by
  refine ⟨(vfAt a₀.val 1,vfAt a₀.val 0),a₀,?_,rfl⟩
  funext i
  fin_cases i <;> rfl

theorem MixedVerticalPresentation.pullback_definable_cells {G : GammaParameters.Base (M := M)}
    {m d : ℕ} {A : Set (Point (M := M) 2 m)} (V : MixedVerticalPresentation G A)
    (Q : GammaRVMap G (GammaFamilySyntax.domain (GammaScalarFamilies.family V.domain)) d)
    (hQ : ∀ a b, Q.toFun a = Q.toFun b → SameRV a.val b.val)
    (hRows : ∀ a, Nonempty (PositionRow Q a (GammaScalarFamilies.value V.position) V.paradigm_index)) :
    ∀ a₀ : A, Cells.DefinableTwoCell (RVLabelSlices.labelBase G ((V.pullback Q).toFun a₀))
      (mixedPairFibre (V.pullback Q) a₀) := by
  intro a₀
  obtain ⟨row⟩ := hRows (V.scalarProjection a₀)
  have hP : ∀ a b, (V.pullback Q).toFun a = (V.pullback Q).toFun b → SameRV a.val b.val := by
    intro a b he
    exact V.inverse_rv a b (hQ (V.scalarProjection a) (V.scalarProjection b) he)
  have hPoly := mixedPairFibre_polydisc (V.pullback Q) hP a₀
  have hFibre := V.pullback_fibre Q a₀ row
  rw [hFibre] at hPoly
  have hCell := row.cell hPoly
  rw [← hFibre] at hCell
  refine ⟨row.position,(V.scalarProjection a₀).val.2 V.paradigm_index,?_⟩
  exact DefinableParadigms.cellData (RVLabelSlices.labelBase G ((V.pullback Q).toFun a₀))
    _ _ _ hCell (mixedPairFibre_nonempty (V.pullback Q) a₀)
    (MixedFibreDefinability.pairFibre_definable (V.pullback Q) a₀) (V.position_definable Q a₀ row)

/-- Lemma 4.8. Every original-Gamma-base definable VF² set admits an actual
finite-arity RV map over that same base. Every nonempty fibre is a two-cell,
and its positioning graph and both paradigms are definable over its output
RV tuple together with the original base. Native coordinate 1 is the first
coordinate in the displayed pair fibre; no carrier or language is replaced. -/
theorem mixed_two_cell_decomposition {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (h00 : M ⊨ Axioms.ACVF00) (G : GammaParameters.Base (M := M))
    (hsmall : Cardinal.mk G.real < κ) (hGenerated : VFGammaGeneratedBase G)
    (δ : Values.Gamma (M := M)) (hδ : δ ∈ G.gamma) (hδ1 : 1 < δ)
    {m : ℕ} (A : Set (Point (M := M) 2 m)) (hA : GammaSetDefinable G A) :
    ∃ d : ℕ, ∃ P : GammaRVMap G A d, ∀ a₀ : A,
      Cells.DefinableTwoCell (RVLabelSlices.labelBase G (P.toFun a₀)) (mixedPairFibre P a₀) := by
  obtain ⟨V⟩ := MixedVerticalPresentation.exists_presentation hs h00 G hsmall hGenerated A hA
  let Af := GammaScalarFamilies.family V.domain
  let f := GammaScalarFamilies.value V.position
  have hf := GammaScalarFamilies.graph_definable G V.domain V.position V.position_graph
  obtain ⟨d,Q,hQ,hRows⟩ := ScalarPositionDecomposition.exists_map hκ hs h00 G hsmall hGenerated
    δ hδ hδ1 Af (GammaScalarFamilies.domain_vf V.domain) f (GammaScalarFamilies.value_vf V.position)
    hf V.paradigm_index
  exact ⟨d,V.pullback Q,V.pullback_definable_cells Q hQ hRows⟩

/-- Lemma 4.8. Every original-Gamma-base definable VF² set admits an actual
finite-arity RV map over that same base. Every nonempty fibre is a two-cell,
and its positioning graph and both paradigms are definable over its output
RV tuple together with the original base. Native coordinate 1 is the first
coordinate in the displayed pair fibre; no carrier or language is replaced. -/
theorem mixed_two_cell_decomposition_with_rv {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (h00 : M ⊨ Axioms.ACVF00) (G : GammaParameters.Base (M := M))
    (hsmall : Cardinal.mk G.real < κ) (hGenerated : VFGammaGeneratedBase G)
    (δ : Values.Gamma (M := M)) (hδ : δ ∈ G.gamma) (hδ1 : 1 < δ)
    {m : ℕ} (A : Set (Point (M := M) 2 m)) (hA : GammaSetDefinable G A) :
    ∃ d : ℕ, ∃ P : GammaRVMap G A d,
      (∀ a b : A, P.toFun a = P.toFun b → SameRV a.val b.val) ∧ ∀ a₀ : A,
      Cells.DefinableTwoCell (RVLabelSlices.labelBase G (P.toFun a₀)) (mixedPairFibre P a₀) := by
  obtain ⟨V⟩ := MixedVerticalPresentation.exists_presentation hs h00 G hsmall hGenerated A hA
  let Af := GammaScalarFamilies.family V.domain
  let f := GammaScalarFamilies.value V.position
  have hf := GammaScalarFamilies.graph_definable G V.domain V.position V.position_graph
  obtain ⟨d,Q,hQ,hRows⟩ := ScalarPositionDecomposition.exists_map hκ hs h00 G hsmall hGenerated
    δ hδ hδ1 Af (GammaScalarFamilies.domain_vf V.domain) f (GammaScalarFamilies.value_vf V.position)
    hf V.paradigm_index
  exact ⟨d,V.pullback Q,(fun a b he => V.inverse_rv a b (hQ _ _ he)),
    V.pullback_definable_cells Q hQ hRows⟩

end IntegrationInACVF.Section5
