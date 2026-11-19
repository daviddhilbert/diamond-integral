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
open DiamondIntegral.Section7.ElementaryBlowups DiamondIntegral.Section7.BlowupLiftImage

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

/-! ### The aperture of relative aperture data on the lift of a chart -/

section Datum
open DiamondIntegral.Section7.BlowupLiftData DiamondIntegral.Section7.RVMaps
open DiamondIntegral.Section7.ElementaryComparison
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (DiamondIntegral.Section2.VF M) G]
variable (c : Chart (⟨S, ∅⟩ : GammaParameters.Base (M := M)) (1 + k))
variable (R : RelativeApertureData (G := G) (rvLift (toMeasured hc c).object))
variable (hall : ∀ p ∈ (rvLift (toMeasured hc c).object).carrier, p.2 ∈ R.activeTags.carrier)

theorem mem_chartLift_iff (p : DiamondIntegral.Section2.Mixed M (1 + k) c.arity) :
    p ∈ (rvLift (toMeasured hc c).object).carrier ↔
      rvValues p.2 ∈ c.domain ∧ rvValues (DiamondIntegral.Section2.tupleRV M p.1) = c.coordinate (rvValues p.2) := by
  constructor
  · rintro ⟨u, hu, hv⟩
    have hd : rvValues u.val ∈ c.domain := u.property
    rw [hu] at hd
    refine ⟨hd, ?_⟩
    have h1 : rvValues (DiamondIntegral.Section2.tupleRV M p.1) = rvValues ((toMeasured hc c).object.value u) := by
      rw [hv]
      rfl
    rw [h1, ← hu]
    rfl
  · rintro ⟨hd, hv⟩
    refine ⟨⟨p.2, hd⟩, rfl, ?_⟩
    apply rvValues_injective
    change c.coordinate (rvValues p.2) = rvValues (DiamondIntegral.Section2.tupleRV M p.1)
    exact hv.symm

/-- Every label of the domain carries points of the lift. -/
theorem exists_point {u : Fin c.arity → M} (hu : u ∈ c.domain) :
    ∃ p ∈ (rvLift (toMeasured hc c).object).carrier, rvValues p.2 = u := by
  have hs := c.domain_definable.proper u hu
  obtain ⟨x, hx⟩ := DiamondIntegral.Section2.tupleRV_surjective
    (rvTuple (c.coordinate u) (fun i => (c.coordinate_proper u hu i).1))
  refine ⟨(x, rvTuple u hs), (mem_chartLift_iff hc c _).mpr ⟨hu, ?_⟩, rvValues_rvTuple _ _⟩
  rw [hx, rvValues_rvTuple, rvValues_rvTuple]

/-- The leading term of the endpoint, as a Section 6 map on the lift. -/
def endpointRV : Map (rvLift (toMeasured hc c).object) (DefSet.univ (rawRVSpace (M := M) 1) S) := by
  let P := rawMixedSpace (M := M) (1 + k) (toMeasured hc c).object.arity
  let codes (z : Fin (1 + k) ⊕ Fin (toMeasured hc c).object.arity → M) : Fin 1 → M :=
    fun _ => iRv (scalarCodeExtension R.endpointMap z)
  have hCodes : S.DefinableMap LRV codes :=
    fun _ => rv_scalarCode_definable (scalarCodeExtension_definable R.endpointMap)
  have hCode (c' : P.domain) :
      rvValues (fun _ : Fin 1 => DiamondIntegral.Section2.rv M (R.extendedEndpoint (P.decode c'))) = codes c'.val := by
    funext i
    exact congrArg (fun z => iRv (scalarCodeExtension R.endpointMap z)) (mixedValues_decode c')
  have hDom (c' : P.domain) : codes c'.val ∈ (rawRVSpace (M := M) 1).domain := ⟨_, hCode c'⟩
  refine Map.ofCodes _ (fun p => fun _ => DiamondIntegral.Section2.rv M (R.extendedEndpoint p)) codes hCodes hDom ?_
  intro c'
  apply rvValues_injective
  exact (SpecialTransformations.Section4.rvValues_decode ⟨codes c'.val, hDom c'⟩).trans (hCode c').symm

theorem endpointRV_val (p : rvLift (toMeasured hc c).object) :
    (endpointRV hc c R p).val = fun _ => DiamondIntegral.Section2.rv M (R.extendedEndpoint p.val) := rfl

include hall in
theorem endpointRV_const (p q : rvLift (toMeasured hc c).object) (he : p.val.2 = q.val.2) :
    endpointRV hc c R p = endpointRV hc c R q := by
  apply Subtype.ext
  rw [endpointRV_val, endpointRV_val]
  funext _
  have hp : p.val ∈ (focusActive (rvLift (toMeasured hc c).object) R.activeTags).carrier :=
    ⟨p.property, hall _ p.property⟩
  have hq : q.val ∈ (focusActive (rvLift (toMeasured hc c).object) R.activeTags).carrier :=
    ⟨q.property, hall _ q.property⟩
  rw [R.extendedEndpoint_active p.property (hall _ p.property),
    R.extendedEndpoint_active q.property (hall _ q.property)]
  have h := R.endpoint_RV_constant ⟨p.val, hp⟩ ⟨q.val, hq⟩ he
  rw [R.endpointMap_eq, R.endpointMap_eq] at h
  exact h

/-- The endpoint leading term on labels. -/
def endpointLabel : Map (pureRVTagDomain (rvLift (toMeasured hc c).object)) (DefSet.univ (rawRVSpace (M := M) 1) S) :=
  definableSurjectiveDescent (pureRVTagQuotient _) (pureRVTagQuotient_surjective _) (endpointRV hc c R)
    (fun p q h => endpointRV_const hc c R hall p q ((pureRVTagQuotient_eq_iff _ p q).mp h))

/-- The raw endpoint leading term of a label. -/
def gEnd (u : Fin c.arity → M) : M := rawFun (endpointLabel hc c R hall) u 0

theorem labels_eq : rvValues '' (pureRVTagDomain (rvLift (toMeasured hc c).object)).carrier = c.domain := by
  ext w
  constructor
  · rintro ⟨t, ht, rfl⟩
    obtain ⟨p, hp⟩ := pureRVTagQuotient_surjective (rvLift (toMeasured hc c).object) ⟨t, ht⟩
    have he : p.val.2 = t := congrArg Subtype.val hp
    rw [← he]
    exact ((mem_chartLift_iff hc c p.val).mp p.property).1
  · intro hw
    obtain ⟨p, hp, he⟩ := exists_point hc c hw
    exact ⟨p.2, (pureRVTagQuotient _ ⟨p, hp⟩).property, he⟩

theorem gEnd_of {p : DiamondIntegral.Section2.Mixed M (1 + k) c.arity} (hp : p ∈ (rvLift (toMeasured hc c).object).carrier) :
    gEnd hc c R hall (rvValues p.2) = (DiamondIntegral.Section2.rv M (R.extendedEndpoint p)).val := by
  have h := rawFun_of (endpointLabel hc c R hall) (pureRVTagQuotient _ ⟨p, hp⟩)
  have h2 : endpointLabel hc c R hall (pureRVTagQuotient _ ⟨p, hp⟩) = endpointRV hc c R ⟨p, hp⟩ :=
    definableSurjectiveDescent_apply _ _ _ _ _
  rw [h2, endpointRV_val] at h
  exact congrFun h 0

theorem gEnd_scalarDef : ScalarDef (⟨S, ∅⟩ : GammaParameters.Base (M := M)) c.domain (gEnd hc c R hall) := by
  have h := rawFun_graph hc (endpointLabel hc c R hall)
  rw [labels_eq hc c] at h
  exact scalarDef_of_tupleDef h 0

include hall in
theorem focus_rv_chart {p : DiamondIntegral.Section2.Mixed M (1 + k) c.arity}
    (hp : p ∈ (rvLift (toMeasured hc c).object).carrier) :
    (DiamondIntegral.Section2.rv M (R.extendedFocus p)).val = c.coordinate (rvValues p.2) R.coordinate := by
  rw [R.extendedFocus_active hp (hall p hp), R.focusRV p hp (hall p hp)]
  exact congrFun ((mem_chartLift_iff hc c p).mp hp).2 R.coordinate

include hall in
theorem endpoint_ne_zero {p : DiamondIntegral.Section2.Mixed M (1 + k) c.arity}
    (hp : p ∈ (rvLift (toMeasured hc c).object).carrier) : R.extendedEndpoint p ≠ 0 := by
  rw [R.extendedEndpoint_active hp (hall p hp)]
  exact R.endpoint_nonzero ⟨p, hp, hall p hp⟩

theorem coord_nonzero_chart {u : Fin c.arity → M} (hu : u ∈ c.domain) (i : Fin (1 + k)) :
    NonzeroRV (c.coordinate u i) := ⟨(c.coordinate_proper u hu i).1, (c.coordinate_proper u hu i).2⟩

theorem gEnd_nonzero {u : Fin c.arity → M} (hu : u ∈ c.domain) : NonzeroRV (gEnd hc c R hall u) := by
  obtain ⟨p, hp, rfl⟩ := exists_point hc c hu
  rw [gEnd_of hc c R hall hp]
  exact DiamondIntegral.Section6.iRv_nonzero (endpoint_ne_zero hc c R hall hp)

/-- The aperture `τ(u) = rv(b₁)/f_j(u)` of the data. -/
def apertureOf : AnnularBlowup.Aperture c where
  aperture u := rvDiv (hM := hM) (gEnd hc c R hall u) (c.coordinate u R.coordinate)
  graph_definable := scalarDef_rvDiv c.domain_definable (gEnd_scalarDef hc c R hall)
    (scalarDef_of_tupleDef c.coordinate_definable R.coordinate) (fun _ hu => (gEnd_nonzero hc c R hall hu).1)
    (fun _ hu => coord_nonzero_chart c hu _)
  nonzero := fun _ hu => rvDiv_nonzero (gEnd_nonzero hc c R hall hu) (coord_nonzero_chart c hu _)
  nonnegative := fun u hu => by
    obtain ⟨p, hp, rfl⟩ := exists_point hc c hu
    rw [codeValue_rvDiv (gEnd_nonzero hc c R hall hu) (coord_nonzero_chart c hu _)]
    have hle := R.endpoint_nonnegative ⟨p, hp, hall p hp⟩
    rw [← R.extendedFocus_active hp (hall p hp), ← R.extendedEndpoint_active hp (hall p hp)] at hle
    rw [vfValue_eq_codeValue (focus_rv_chart hc c R hall hp) (coord_nonzero_chart c hu _),
      vfValue_eq_codeValue (gEnd_of hc c R hall hp).symm (gEnd_nonzero hc c R hall hu)] at hle
    exact le_mul_inv_iff_mul_le.mpr (by rw [one_mul]; exact hle)
  bound := R.apertureBound
  bounded := fun u hu => by
    obtain ⟨p, hp, rfl⟩ := exists_point hc c hu
    rw [codeValue_rvDiv (gEnd_nonzero hc c R hall hu) (coord_nonzero_chart c hu _)]
    have hb := R.endpoint_upper_bound ⟨p, hp, hall p hp⟩
    rw [R.endpointMap_eq, ← R.extendedEndpoint_active hp (hall p hp)] at hb
    have hx : (DiamondIntegral.Section2.rv M (p.1 R.coordinate)).val = c.coordinate (rvValues p.2) R.coordinate :=
      congrFun ((mem_chartLift_iff hc c p).mp hp).2 R.coordinate
    rw [vfValue_eq_codeValue (gEnd_of hc c R hall hp).symm (gEnd_nonzero hc c R hall hu),
      vfValue_eq_codeValue hx (coord_nonzero_chart c hu _),
      ← SpecialTransformations.Section3.Values.gamma_val_mul] at hb
    exact mul_inv_le_iff_le_mul.mpr hb

include hall in
theorem apertureOf_endpoint {p : DiamondIntegral.Section2.Mixed M (1 + k) c.arity}
    (hp : p ∈ (rvLift (toMeasured hc c).object).carrier) :
    (DiamondIntegral.Section2.rv M (R.extendedEndpoint p)).val =
      iRVMul ((apertureOf hc c R hall).aperture (rvValues p.2)) (c.coordinate (rvValues p.2) R.coordinate) := by
  have hu := ((mem_chartLift_iff hc c p).mp hp).1
  change _ = iRVMul (rvDiv (hM := hM) (gEnd hc c R hall (rvValues p.2)) _) _
  rw [← gEnd_of hc c R hall hp]
  exact ((mul_eq_iff_rvDiv (rvDiv_nonzero (gEnd_nonzero hc c R hall hu) (coord_nonzero_chart c hu R.coordinate)).1
    (gEnd_nonzero hc c R hall hu).1 (coord_nonzero_chart c hu R.coordinate)).mpr rfl).symm

/-! ### The finite-to-one condition (R171) -/

/-- Base change of a definable set to a larger parameter set. -/
def defSetMono {P : Space LRV M} {S' : Set M} (h : S ⊆ S') (A : DefSet P S) : DefSet P S' :=
  ⟨A.carrier, Set.Definable.mono A.definable h⟩

/-- Base change of a definable map. -/
def mapMono {P Q : Space LRV M} {S' : Set M} (h : S ⊆ S') {A : DefSet P S} {B : DefSet Q S} (f : Map A B) :
    Map (defSetMono h A) (defSetMono h B) := ⟨fun a => f a, Set.Definable.mono f.graph_definable h⟩

include hall in
/-- The finite-to-one condition of Definition 7.2 for the data: for a fixed VF
input `a` of the inactive leading terms, the focus `u ↦ λ(a, u)` has finite
image (Lemma 2.13 through Section 6's `scalarFocusImage_finite`, over
`S ∪ {a}`), and the lift has finite fibres. -/
theorem inactive_finite {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hsmall : Cardinal.mk S < κ) : AnnularBlowup.InactiveFinite c R.coordinate := by
  intro t
  by_cases hne : ∃ u₀, u₀ ∈ c.domain ∧ AnnularBlowup.inactive c R.coordinate u₀ = t
  swap
  · apply Set.Finite.subset Set.finite_empty
    rintro u ⟨hu, htu⟩
    exact hne ⟨u, hu, htu⟩
  obtain ⟨u₀, hu₀, ht⟩ := hne
  obtain ⟨p₀, hp₀, hpu₀⟩ := exists_point hc c hu₀
  let a := p₀.1
  let S' : Set M := S ∪ Set.range (fun i => (a i).val)
  have hSS : S ⊆ S' := Set.subset_union_left
  have hsmall' : Cardinal.mk S' < κ := by
    refine (Cardinal.mk_union_le _ _).trans_lt (Cardinal.add_lt_of_lt hκ.le hsmall ?_)
    exact ((Set.finite_range _).lt_aleph0).trans hκ
  let FA := focusActive (rvLift (toMeasured hc c).object) R.activeTags
  let P := rawMixedSpace (M := M) (1 + k) (toMeasured hc c).object.arity
  let Xc : Set P.Carrier := {p | p ∈ FA.carrier ∧ ∀ i, i ≠ R.coordinate → p.1 i = a i}
  have hX : P.Definable S' Xc := by
    have hcoord : ∀ i : Fin (1 + k), S'.Definable LRV
        {z : Fin (1 + k) ⊕ Fin (toMeasured hc c).object.arity → M | z (Sum.inl i) = (a i).val} := by
      intro i
      have h1 := Set.Definable.singleton_of_mem (L := LRV) (show (a i).val ∈ S' from Or.inr ⟨i, rfl⟩)
      have h2 := h1.preimage_comp (fun _ : Fin 1 => (Sum.inl i : Fin (1 + k) ⊕ Fin (toMeasured hc c).object.arity))
      convert h2 using 1
      ext z
      simp only [Set.mem_setOf_eq, Set.mem_preimage, Function.comp_apply, Set.mem_singleton_iff]
    have hall' : S'.Definable LRV (⋂ i ∈ (Finset.univ.erase R.coordinate),
        {z : Fin (1 + k) ⊕ Fin (toMeasured hc c).object.arity → M | z (Sum.inl i) = (a i).val}) :=
      Set.definable_biInter_finset hcoord _
    have hFA : S'.Definable LRV (P.preimage FA.carrier) := Set.Definable.mono FA.definable hSS
    change S'.Definable LRV (P.preimage Xc)
    convert hFA.inter hall' using 1
    ext z
    constructor
    · rintro ⟨hz, hm, hoff⟩
      refine ⟨⟨hz, hm⟩, ?_⟩
      simp only [Set.mem_iInter, Finset.mem_erase, Finset.mem_univ, and_true]
      intro i hi
      have h := congrArg Subtype.val (hoff i hi)
      have hm' := congrFun (mixedValues_decode ⟨z, hz⟩) (Sum.inl i)
      have h3 : z (Sum.inl i) = ((P.decode ⟨z, hz⟩).1 i).val := hm'.symm
      exact h3.trans h
    · rintro ⟨⟨hz, hm⟩, hoff⟩
      refine ⟨hz, hm, fun i hi => ?_⟩
      simp only [Set.mem_iInter, Finset.mem_erase, Finset.mem_univ, and_true] at hoff
      apply Subtype.ext
      have hm' := congrFun (mixedValues_decode ⟨z, hz⟩) (Sum.inl i)
      exact hm'.trans (hoff i hi)
  let X : DefSet P S' := ⟨Xc, hX⟩
  have hXsub : X.carrier ⊆ (defSetMono hSS FA).carrier := fun p hp => hp.1
  let f : Map X (defSetMono hSS (DefSet.univ (rawVFSpace (M := M) 1) S)) :=
    (mapMono hSS R.focusMap).comp (Map.inclusion hXsub)
  have hRV : ∀ p q : X, p.val.2 = q.val.2 → (f p).val 0 = (f q).val 0 := by
    intro p q he
    change (R.focusMap ⟨p.val, p.property.1⟩).val 0 = (R.focusMap ⟨q.val, q.property.1⟩).val 0
    rw [R.focusMap_eq, R.focusMap_eq]
    have hupd : Function.update p.val.1 R.coordinate 0 = Function.update q.val.1 R.coordinate 0 := by
      funext i
      by_cases hi : i = R.coordinate
      · rw [hi, Function.update_self, Function.update_self]
      · rw [Function.update_of_ne hi, Function.update_of_ne hi, p.property.2 i hi, q.property.2 i hi]
    change R.focus (Function.update p.val.1 R.coordinate 0) p.val.2 = R.focus (Function.update q.val.1 R.coordinate 0) q.val.2
    rw [hupd, he]
  have hΛ := scalarFocusImage_finite hc hs hsmall' f hRV
  apply (hΛ.biUnion (fun y _ => c.finite_fibres
    (rvValues (DiamondIntegral.Section2.tupleRV M (Function.update a R.coordinate y))))).subset
  rintro u ⟨hu, htu⟩
  have hoffu : ∀ i, i ≠ R.coordinate → c.coordinate u i = c.coordinate u₀ i := by
    intro i hi
    have h := congrFun (htu.trans ht.symm) i
    simp only [AnnularBlowup.inactive] at h
    rw [Function.update_of_ne hi, Function.update_of_ne hi] at h
    exact h
  have hp₀rv := ((mem_chartLift_iff hc c p₀).mp hp₀).2
  rw [hpu₀] at hp₀rv
  have hfj := coord_nonzero_chart c hu R.coordinate
  obtain ⟨z, hz⟩ := DiamondIntegral.Section2.rv_surjective (⟨c.coordinate u R.coordinate, hfj.1⟩ : DiamondIntegral.Section2.RVInfinity M)
  have hsu := c.domain_definable.proper u hu
  let q : DiamondIntegral.Section2.Mixed M (1 + k) c.arity := (Function.update a R.coordinate z, rvTuple u hsu)
  have hrvq : rvValues (DiamondIntegral.Section2.tupleRV M q.1) = c.coordinate u := by
    funext i
    change (DiamondIntegral.Section2.rv M (Function.update a R.coordinate z i)).val = _
    by_cases hi : i = R.coordinate
    · rw [hi, Function.update_self, hz]
    · rw [Function.update_of_ne hi, hoffu i hi]
      exact congrFun hp₀rv i
  have hq : q ∈ (rvLift (toMeasured hc c).object).carrier :=
    (mem_chartLift_iff hc c q).mpr ⟨by rw [rvValues_rvTuple]; exact hu, by rw [rvValues_rvTuple]; exact hrvq⟩
  have hqX : q ∈ X.carrier := ⟨⟨hq, hall q hq⟩, fun i hi => Function.update_of_ne hi _ _⟩
  let lamU := (f ⟨q, hqX⟩).val 0
  have hlam : lamU = R.extendedFocus q := by
    change (R.focusMap ⟨q, hq, hall q hq⟩).val 0 = _
    rw [R.focusMap_eq, R.extendedFocus_active hq (hall q hq)]
  have hlamrv : (DiamondIntegral.Section2.rv M lamU).val = c.coordinate u R.coordinate := by
    rw [hlam, focus_rv_chart hc c R hall hq, rvValues_rvTuple]
  refine Set.mem_iUnion₂.mpr ⟨lamU, ⟨⟨q, hqX⟩, rfl⟩, hu, ?_⟩
  funext i
  change _ = (DiamondIntegral.Section2.rv M (Function.update a R.coordinate lamU i)).val
  by_cases hi : i = R.coordinate
  · rw [hi, Function.update_self, hlamrv]
  · rw [Function.update_of_ne hi, hoffu i hi]
    exact (congrFun hp₀rv i).symm

end Datum

/-! ### Lemma 7.11 for one relative step on the lift of a chart -/

section StepOfData
open DiamondIntegral.Section7.BlowupLiftData DiamondIntegral.Section7.BlowupLiftClasses
open DiamondIntegral.Section7.LiftClasses
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (DiamondIntegral.Section2.VF M) G]
variable (T : LRV.Substructure M) (c : Chart (BT T) (1 + k)) (hb : RVMeasuredBounds.DomainBounded c)
variable (R : RelativeApertureData (G := G) (rvLift (toMeasured hc c).object))
variable (hall : ∀ p ∈ (rvLift (toMeasured hc c).object).carrier, p.2 ∈ R.activeTags.carrier)
variable {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ) (hsmall : Cardinal.mk (T : Set M) < κ)
variable (h00 : M ⊨ Axioms.ACVF00)

/-- The annular datum of relative aperture data: the coordinate of `R`, the
aperture `rv(b₁)/f_j`, and `R`'s named bound. -/
def datumOf : AnnularDatum (BT T) k where
  chart := c
  coordinate := R.coordinate
  finite := inactive_finite hc c R hall hκ hs hsmall
  aperture := apertureOf hc c R hall
  bounded := hb

/-- Lemma 7.11 for one relative step with all labels active: the contraction
of the regularized image is a blowup of length one of the source. -/
theorem step_of_data :
    Step (cls (⟨c, hb⟩ : Obj (BT T) (1 + k)))
      (cls (contractionObj hc T (datumOf hc T c hb R hall hκ hs hsmall) R rfl hall
        (fun _ hp => apertureOf_endpoint hc c R hall hp) h00)) :=
  step_contraction hc T (datumOf hc T c hb R hall hκ hs hsmall) R rfl hall
    (fun _ hp => apertureOf_endpoint hc c R hall hp) h00

end StepOfData

end DiamondIntegral.Section7.SpecialStep
