import «section 6».PreparedCentripetalProgramTemplates
import Section3.SmallFiniteParameters

/-! Genuine compactness gives finitely many complete prepared programs
for a definable family of locally prepared pullback fibres. Their
lengths and output RV arities consequently have one finite bound. -/

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

def CentripetalProgramTemplate.length : {r s : ℕ} → CentripetalProgramTemplate (M := M) S p n r s → ℕ
  | _,_,.identity _ => 0
  | _,_,.regularize _ => 1
  | _,_,.centripetal _ => 1
  | _,_,.comp F H => F.length+H.length

theorem exists_finite_prepared_centripetal_programs
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    (linear : GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (hsmall : Cardinal.mk S < κ) (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M))
    (X : Set (Fin p → M)) (hX : S.Definable LRV X)
    (A : MixedSetParameterTemplate (M := M) S p n r)
    (P : Fin k → MixedSetParameterTemplate (M := M) S p n r)
    (hLocal : ∀ a ∈ X,∃ s,∃ B : DefSet (rawMixedSpace (M := M) n s) (S ∪ Set.range a),
      ∃ f : Map (A.fibre a) B,
      ∃ h : SynchronizedCentripetalChain (G := G) (Fin k) (A.fibre a) B f (fun i => (P i).fibre a),
        IsRVPullback (A.fibre a).carrier ∧
          ∀ i,IsRVPullback (f.restrict (h.atPiece i).source_subset).image.carrier) :
    ∃ l : ℕ,∃ T : Fin l → Σ s,CentripetalProgramTemplate (M := M) S p n r s,
      ∀ a ∈ X,∃ i,a ∈ (T i).2.preparedGood A P := by
  let C := Set.range (fun T : Σ s,CentripetalProgramTemplate (M := M) S p n r s => T.2.preparedGood A P)
  have hC : ∀ c ∈ C,S.Definable LRV c := by
    rintro c ⟨T,rfl⟩
    exact T.2.preparedGood_definable A P
  have hCover (a) (ha : a ∈ X) : ∃ c ∈ C,a ∈ c := by
    obtain ⟨s,B,f,h,hARV,hPrepared⟩ := hLocal a ha
    have hsmallA := small_union_range hκ.le S hsmall a
    have hGammaA : NontrivialDefinableGamma (⟨S ∪ Set.range a,∅⟩ : ParameterBase M) :=
      hΓ.mono Set.subset_union_left (Set.Subset.rfl)
    obtain ⟨T,hT,hGraph⟩ := exists_promoted_prepared_centripetal_program h00 hc linear hκ hs hv
      A P a hsmallA hGammaA h hARV (fun i => (h.atPiece i).source_subset) hPrepared
    exact ⟨T.preparedGood A P,⟨⟨s,T⟩,rfl⟩,hT⟩
  obtain ⟨C₀,hFin,hSub,hCov⟩ := hs.definable_finite_subcover_tuple S hsmall X hX C hC hCover
  letI : Fintype C₀ := hFin.fintype
  let e := Fintype.equivFin C₀
  let chooseT (c : C₀) := (hSub c.property).choose
  have hT (c : C₀) : (chooseT c).2.preparedGood A P=c.val := (hSub c.property).choose_spec
  refine ⟨Fintype.card C₀,fun i => chooseT (e.symm i),?_⟩
  intro a ha
  obtain ⟨c,hc,hac⟩ := hCov a ha
  refine ⟨e ⟨c,hc⟩,?_⟩
  change a ∈ (chooseT (e.symm (e ⟨c,hc⟩))).2.preparedGood A P
  rw [e.symm_apply_apply,hT]
  exact hac

theorem finite_centripetal_program_bounds
    {l : ℕ} (T : Fin l → Σ s,CentripetalProgramTemplate (M := M) S p n r s) :
    ∃ N : ℕ,∀ i,(T i).1 ≤ N ∧ (T i).2.length ≤ N := by
  refine ⟨Finset.univ.sup (fun i => max (T i).1 (T i).2.length),fun i => ?_⟩
  have h : max (T i).1 (T i).2.length ≤ Finset.univ.sup (fun j => max (T j).1 (T j).2.length) :=
    Finset.le_sup (f := fun j => max (T j).1 (T j).2.length) (Finset.mem_univ i)
  exact ⟨(le_max_left _ _).trans h,(le_max_right _ _).trans h⟩

end DiamondIntegral.Section6
