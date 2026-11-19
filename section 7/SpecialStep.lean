import «section 7».IsoOfMeasured
import «section 7».BlowupLiftClasses

/-! Lemma 7.11 (`special:to:blowup:coa`), the relative step on Section 7's classes.

For an annular datum `D` and relative aperture data `R` on the lift of its
chart, matching `D` in the sense of `BlowupLiftImage` (same coordinate, all
labels active, endpoint leading term `τ(u) f_j(u)`), the contraction `W` of the
regularized image is a Section 7 object of the class of the blowup
`U^{τ,j}`. So the contraction of a relative step is a blowup of length one of
the source. Pieces of `chartOf U` along raw definable sets are Section 6
restrictions of `U` (`pieceIso`, `cpieceIso`). -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry

namespace DiamondIntegral.Section7.SpecialStep
open DiamondIntegral.Section4 DiamondIntegral.Section4.RVMeasuredCharts
open RelativeAnnularGenerators
open DiamondIntegral.Section6 DiamondIntegral.Section6.DiamondLiftHomomorphism
open DiamondIntegral.Section7.MeasuredRVBridge DiamondIntegral.Section7.ChartOfMeasured
open DiamondIntegral.Section7.IsoOfMeasured DiamondIntegral.Section7.BoundedClasses
open DiamondIntegral.Section7.ElementaryBlowups

variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable (hc : CanonicalStructure.IsCanonical (M := M)) {S : Set M} {k : ℕ}

/-! ### Pieces of `chartOf U` -/

section Pieces
variable (U : MeasuredRVObject (M := M) S k) (I : Set (Fin U.object.arity → M))
  (hI : DefinableOverBase (⟨S, ∅⟩ : GammaParameters.Base (M := M)) (fun _ : Fin U.object.arity => .rv) I)
  (Dset : DefSet (rawRVSpace (M := M) U.object.arity) S) (hD : Dset.carrier ⊆ U.object.domain.carrier)
  (hmem : ∀ a ∈ U.object.domain.carrier, a ∈ Dset.carrier ↔ rvValues a ∈ I)

theorem mem_domain_of_rawDom {a : Fin U.object.arity → CanonicalRV.RVSort M} (ha : rvValues a ∈ rawDom U) :
    a ∈ U.object.domain.carrier := by
  obtain ⟨t, ht, he⟩ := ha
  rw [← rvValues_injective he]
  exact ht

include hmem in
/-- The piece of `chartOf U` along `I` is the restriction of `U` to `Dset`. -/
def pieceIso : MeasuredRVIso (toMeasured hc (resChart (chartOf hc U) I hI)) (U.restrict Dset hD) := by
  have hsub : (toMeasured hc (resChart (chartOf hc U) I hI)).object.domain.carrier ⊆ Dset.carrier := by
    intro a ha
    have ha' : rvValues a ∈ rawDom U ∩ I := ha
    exact (hmem a (mem_domain_of_rawDom U ha'.1)).mpr ha'.2
  let F : Map (toMeasured hc (resChart (chartOf hc U) I hI)).object.domain (U.restrict Dset hD).object.domain :=
    Map.inclusion hsub
  have hF : Function.Bijective F := by
    refine ⟨fun a b he => ?_, fun b => ?_⟩
    · exact Subtype.ext (congrArg (fun x : (U.restrict Dset hD).object.domain => x.val) he)
    · refine ⟨⟨b.val, ?_⟩, rfl⟩
      show rvValues b.val ∈ rawDom U ∩ I
      exact ⟨mem_rawDom U ⟨b.val, hD b.property⟩, (hmem b.val (hD b.property)).mp b.property⟩
  refine ⟨rvIsoOfFiniteFibres F hF (toMeasured hc _).finiteVolume (U.restrict Dset hD).finiteVolume
    (toMeasured hc _).nonzero (U.restrict Dset hD).nonzero, fun a => ?_⟩
  rw [rvIsoOfFiniteFibres_map]
  unfold MeasuredRVObject.totalWeight
  let b : U.object.domain := ⟨a.val, hD (hsub a.property)⟩
  have hv : (toMeasured hc (resChart (chartOf hc U) I hI)).object.value a = (U.restrict Dset hD).object.value (F a) := by
    apply rvValues_injective
    change rawCoord U (rvValues a.val) = rvValues (U.object.value b)
    exact rawCoord_of U b
  rw [volumeGamma_congr hv]
  congr 1
  change rawVol U (rvValues a.val) = gammaMapValue U.form b
  exact rawVol_of U b

include hmem in
/-- The complementary piece of `chartOf U` along `I` is the complementary
restriction of `U`. -/
def cpieceIso : MeasuredRVIso (toMeasured hc (cresChart (chartOf hc U) I hI)) (restrictCompl U Dset) := by
  have hsub : (toMeasured hc (cresChart (chartOf hc U) I hI)).object.domain.carrier ⊆
      (U.object.domain.sdiff Dset).carrier := by
    intro a ha
    have ha' : rvValues a ∈ rawDom U \ I := ha
    have hU := mem_domain_of_rawDom U ha'.1
    exact ⟨hU, fun hd => ha'.2 ((hmem a hU).mp hd)⟩
  let F : Map (toMeasured hc (cresChart (chartOf hc U) I hI)).object.domain (restrictCompl U Dset).object.domain :=
    Map.inclusion hsub
  have hF : Function.Bijective F := by
    refine ⟨fun a b he => ?_, fun b => ?_⟩
    · exact Subtype.ext (congrArg (fun x : (restrictCompl U Dset).object.domain => x.val) he)
    · refine ⟨⟨b.val, ?_⟩, rfl⟩
      show rvValues b.val ∈ rawDom U \ I
      exact ⟨mem_rawDom U ⟨b.val, b.property.1⟩, fun hi => b.property.2 ((hmem b.val b.property.1).mpr hi)⟩
  refine ⟨rvIsoOfFiniteFibres F hF (toMeasured hc _).finiteVolume (restrictCompl U Dset).finiteVolume
    (toMeasured hc _).nonzero (restrictCompl U Dset).nonzero, fun a => ?_⟩
  rw [rvIsoOfFiniteFibres_map]
  unfold MeasuredRVObject.totalWeight
  let b : U.object.domain := ⟨a.val, (hsub a.property).1⟩
  have hv : (toMeasured hc (cresChart (chartOf hc U) I hI)).object.value a = (restrictCompl U Dset).object.value (F a) := by
    apply rvValues_injective
    change rawCoord U (rvValues a.val) = rvValues (U.object.value b)
    exact rawCoord_of U b
  rw [volumeGamma_congr hv]
  congr 1
  change rawVol U (rvValues a.val) = gammaMapValue U.form b
  exact rawVol_of U b

end Pieces

/-! ### The contraction of a relative step is a blowup -/

section Step
open DiamondIntegral.Section7.BlowupLiftData DiamondIntegral.Section7.BlowupLiftImage
open DiamondIntegral.Section7.BlowupLiftContraction DiamondIntegral.Section7.BlowupLiftClasses
open DiamondIntegral.Section7.LiftClasses
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (DiamondIntegral.Section2.VF M) G]
variable (T : LRV.Substructure M) (D : AnnularDatum (BT T) k)
variable (R : RelativeApertureData (G := G) (liftSet hc D))
variable (hj : R.coordinate = D.coordinate)
variable (hact : ∀ p ∈ (liftSet hc D).carrier, p.2 ∈ R.activeTags.carrier)
variable (hend : ∀ p ∈ (liftSet hc D).carrier,
  (DiamondIntegral.Section2.rv M (R.extendedEndpoint p)).val = centrePair D (rvValues p.2) 1)
variable (h00 : M ⊨ Axioms.ACVF00)

/-- The contraction of the relative step, as a Section 7 object. -/
abbrev contractionObj : Obj (BT T) (1 + k) :=
  objOf hc T (W hc D R hj hact hend h00) (W_doublyBounded hc D R hj hact hend h00)

/-- The contraction of the regularized image of a relative step has the class of
the blowup `U^{τ,j}`. -/
theorem cls_contraction : cls (contractionObj hc T D R hj hact hend h00) = cls D.annularObject := by
  rw [cls_annular, add_comm (cls (BlowupRelation.shellBounded _ _ _ _ _)) (cls (BlowupRelation.endpointBounded _ _ _ _ _)),
    cls_partition (contractionObj hc T D R hj hact hend h00) (Icore D) (Icore_definable D)]
  have hmemC : ∀ a ∈ (W hc D R hj hact hend h00).object.domain.carrier,
      a ∈ (Dcore hc D).carrier ↔ rvValues a ∈ Icore D := fun a _ => Iff.rfl
  congr 1
  · apply (cls_eq_iff_measured hc).mpr
    exact ⟨(pieceIso hc (W hc D R hj hact hend h00) (Icore D) (Icore_definable D) (Dcore hc D)
      (Dcore_sub hc D R hj hact hend h00) hmemC).comp (isoE hc D R hj hact hend h00).symm⟩
  · apply (cls_eq_iff_measured hc).mpr
    exact ⟨(cpieceIso hc (W hc D R hj hact hend h00) (Icore D) (Icore_definable D) (Dcore hc D)
      hmemC).comp (isoS hc D R hj hact hend h00).symm⟩

/-- Lemma 7.11, one relative step: the contraction is a blowup of length one of
the source. -/
theorem step_contraction :
    Step (cls D.source) (cls (contractionObj hc T D R hj hact hend h00)) := by
  rw [cls_contraction]
  exact step_elem D

end Step

end DiamondIntegral.Section7.SpecialStep
