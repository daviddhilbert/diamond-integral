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

end Datum

end DiamondIntegral.Section7.SpecialStep
