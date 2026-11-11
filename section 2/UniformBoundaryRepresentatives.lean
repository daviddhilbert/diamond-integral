import «section 2».CoordinateBoundaryFamily
import «section 2».UniformDefinableChoice

/-! Uniform representatives of the actual unary-section boundary tags.
Pointwise definability is discharged by Corollary 2.21, and the finite
formula-priority construction keeps the full choice graph over S. -/

set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3

namespace DiamondIntegral.Section2
variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

theorem uniform_coordinate_boundary_representatives (h00 : M ⊨ Axioms.ACVF00)
    {κ : Cardinal} (hs : Saturated M κ) (S : Set M) (hsmall : Cardinal.mk S < κ)
    {n : ℕ} (A : Set (Fin (n+1) → M)) (hA : DefinableOver S (fun _ => .vf) A)
    (i : Fin (n+1)) :
    ∃ f : (Fin (n+1) → M) → M,
      S.Definable LRV {z : Fin (n+1) ⊕ Fin 1 → M |
        z ∘ Sum.inl ∈ coordinateBoundaryPairs A i ∧ f (z ∘ Sum.inl) = z (.inr 0)} ∧
      ∀ p ∈ coordinateBoundaryPairs A i, iVF (f p) ∧ iRv (f p) = p (Fin.last n) := by
  let B : ParameterBase M := ⟨S,∅⟩
  have hAB : GammaParameters.DefinableOverBase B (fun _ => .vf) A :=
    (GammaParameters.base_empty_iff S _ _).mpr hA
  have hJ := (GammaParameters.base_empty_iff S _ _).mp (coordinateBoundaryPairs_definable B A hAB i)
  have hT := (GammaParameters.base_empty_iff S _ _).mp (boundaryFibreRelation_definable B n)
  have hpoint : ∀ p ∈ coordinateBoundaryPairs A i, ∃ x : M,
      (p,x) ∈ boundaryFibreRelation n ∧
      GammaParameters.DefinableClosureAtBase (tupleBase B p) .vf x := by
    intro p hp
    have htRV : iRV (p (Fin.last n)) := by
      simpa only [boundaryParameterSort,Fin.lastCases_last,sortEval,iRV] using hp.1 (Fin.last n)
    let t : RVInfinity M := ⟨p (Fin.last n),htRV⟩
    have ha : ∀ j : Fin n, iVF (Fin.init p j) := by
      intro j
      simpa only [boundaryParameterSort,Fin.lastCases_castSucc,sortEval,iVF,Fin.init] using hp.1 j.castSucc
    obtain ⟨x,hxVF,hxrv,hxA⟩ := hp.2.1
    obtain ⟨y,hyVF,hyrv,hyA⟩ := hp.2.2
    have ht : t ∈ scalarRVBoundary (rawCoordinateSection A i (Fin.init p)) :=
      ⟨⟨⟨x,hxVF⟩,hxA,Subtype.ext hxrv⟩,⟨⟨y,hyVF⟩,hyA,Subtype.ext hyrv⟩⟩
    obtain ⟨c,hc,hdef⟩ := coordinate_boundary_definable_point h00 B A hAB i (Fin.init p) ha t ht
    have he : Fin.snoc (Fin.init p) t.val = p := Fin.snoc_init_self p
    rw [he] at hdef
    exact ⟨c,⟨hp.1,hc⟩,hdef⟩
  obtain ⟨f,hf,hfT⟩ := uniform_vf_choice_of_pointwise_definable hs S hsmall
    (boundaryParameterSort n) (coordinateBoundaryPairs A i) hJ (boundaryFibreRelation n) hT hpoint
  exact ⟨f,hf,fun p hp => (hfT p hp).2⟩

end DiamondIntegral.Section2
