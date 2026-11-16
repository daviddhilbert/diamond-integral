import «section 6».BranchedShearHeadMaps

/-! One actual original-base freezing family simultaneously repairs the
indicator and the full offset, while preserving every original source
fibre. The source supplies its named uniform protection radius. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n r s : ℕ}

theorem totalFocusFibre_family_definable
    {A : DefSet (rawMixedSpace (M := M) n r) S} {B : DefSet (rawVFSpace (M := M) 1) S} (f : Map A B) :
    S.Definable LRV (rvVFGraph (totalFocusFibre f)) := by
  rw [rvVFGraph_eq_functionFamilyGraph (totalFocusFamilyCode f) (totalFocusFibre f) (totalFocusFamilyCode_at f)]
  exact rvFunctionFamilyGraph_definable _ (totalFocusFamilyCode_definable f)

variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

theorem totalFocusFibre_univ_continuous
    (f : Map (DefSet.univ (rawMixedSpace (M := M) n r) S) (DefSet.univ (rawVFSpace 1) S))
    (u : Fin r → RVInfinity M) (hf : Continuous (FMT.focusFibre f u)) : Continuous (totalFocusFibre f u) :=
  totalFocusFibre_continuous f u (by change IsClopen (Set.univ : Set (Fin n → VF M)); exact isClopen_univ) hf

theorem exists_branched_shear_common_freezing
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    (linear : GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (V : Set M) (hsmall : Cardinal.mk S < κ)
    (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M))
    (hV : ∀ a ∈ V,iVF a) (hVS : V ⊆ S) (hSV : S ⊆ algebraicClosureSet V)
    (hnt : ∃ x : vfAlgebraicClosureField V,x ≠ 0 ∧ Valued.v x.val ≠ 1)
    (A : DefSet (rawMixedSpace (M := M) (n+2) r) S) (hA : ProperInvariant S A.carrier)
    (T : BranchedShearChartTemplate (M := M) S 1 n r s) (hF : ∀ a,a ∈ T.goodFunctions) :
    ∃ D : FMT.FocusFreezingData (DefSet.univ (rawMixedSpace (M := M) (n+2) (r+s)) S),
      (∀ u,Continuous (FMT.focusFibre (D.frozenMap (T.headIndicatorMap hF)) u)) ∧
      (∀ u,Continuous (FMT.focusFibre (D.frozenMap (T.headFullOffsetMap hF)) u)) ∧
      ∀ E : D.balls,FMT.CoordinateProductDomain A.carrier (FMT.vfOpenBall E.val) (D.centers E) 0 := by
  obtain ⟨δ,hδdef,hδ0,hδ⟩ := properInvariant_uniform_named_radius h00 hc linear hκ hs hv hsmall hΓ hA
  obtain ⟨c,hc0,hcDef,hδc⟩ := exists_named_vf_above_radius Valued.v hv hc h00 V S hV hVS hSV hnt δ hδ0 hδdef
  let C := DefSet.univ (rawMixedSpace (M := M) (n+2) (r+s)) S
  let f : Bool → Map C (DefSet.univ (rawVFSpace (M := M) 1) S) :=
    fun b => if b then T.headIndicatorMap hF else T.headFullOffsetMap hF
  have hf : ∀ b u a,Continuous (focusTailMap (f b) u a) := by
    intro b u a
    cases b
    · exact T.headFullOffsetMap_tail_continuous hv hF u a
    · exact T.headIndicatorMap_tail_continuous hv hF u a
  have hC : ∀ u,AlphaInvariant (fun _ => δ) (vfFibre C.carrier u) := fun _ _ _ _ => Iff.rfl
  obtain ⟨D,hCont,hAll⟩ := FMT.exists_finite_family_focus_freezing_with_all_domains
    h00 hc hκ hs hsmall hv δ hC c hc0 hcDef hδc.le f hf
  exact ⟨D,hCont true,hCont false,hAll (n+2) r A.carrier hδ 0⟩

end DiamondIntegral.Section6
