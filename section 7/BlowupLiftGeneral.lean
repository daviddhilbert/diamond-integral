import «section 7».BlowupLiftClasses
import «section 7».ElementaryComparison
import «section 7».BlowupCongruence

/-! Lemma 7.12 (`blowup:same:RV:coa`) for every aperture datum.

A chart may carry `∞` labels, which Section 6's doubly bounded objects exclude.
The strict chart of `StrictCharts` encodes them with the tags `1` and `rv(-1)`.
Its coordinate map and volume are those of the original chart read through the
decoding, and the aperture is transported the same way. The strict datum has
the same source class and the same blowup class: Lemma 7.5's comparison
isomorphisms for `F = strictIso` have equal apertures, so the deep part of the
shell is empty and the second endpoint has unit aperture. Lemma 7.12 for the
strict datum (`BlowupLiftClasses`) then gives it for the original one.

Consequently blowups of length one, and hence `μIsp`, preserve the lift. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters

namespace DiamondIntegral.Section7.BlowupLiftGeneral
open DiamondIntegral.Section4
open RVMeasuredCharts FiniteTupleBlocks
open AnnularBlowup BlowupChart BlowupRelation RelativeAnnularGenerators
open DiamondIntegral.Section7.BoundedClasses DiamondIntegral.Section7.ElementaryBlowups
open DiamondIntegral.Section7.ElementaryComparison DiamondIntegral.Section7.RVMaps
open DiamondIntegral.Section7.StrictCharts

variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF] {B : Base (M := M)} {k : ℕ}

/-! ### Endpoints with unit aperture -/

/-- The endpoint of a blowup whose aperture has depth `0` is isomorphic to the
source. -/
def unitEndpointIso (r : Chart B (1 + k)) (j : Fin (1 + k)) (hfin : InactiveFinite r j) (σ : Aperture r)
    (h1 : ∀ u ∈ r.domain, codeValue (σ.aperture u) = 1) : Iso (endpointChart r j hfin σ) r :=
  isoOfMap _ _ (fun w => w ∘ headIndex 1 r.arity) (tupleDef_coord (graphChart r σ).domain_definable _)
    ⟨fun _ hw => hw.1,
      fun w hw w' hw' he => by
        rw [graph_canonical r σ hw, graph_canonical r σ hw']
        simp only at he
        rw [he],
      fun u hu => ⟨gpt u (σ.aperture u), (mem_graph_iff r σ u _).mpr ⟨hu, rfl⟩, gpt_head _ _⟩⟩
    (fun w hw => by
      rw [endpoint_weight r j hfin σ w hw, graph_aperture r σ hw, h1 _ hw.1, mul_one])

/-! ### The strict datum -/

section Strict
variable (h00 : M ⊨ Axioms.ACVF00) (D : AnnularDatum B k)

theorem strict_isoMap {u : Fin D.chart.arity → M} (hu : u ∈ D.chart.domain) :
    isoMap (strictIso h00 D.chart) u = encode u :=
  isoMap_on (strictIso h00 D.chart) ⟨u, hu⟩

/-- The aperture read through the decoding. -/
def strictAperture : Aperture (strictChart h00 D.chart) where
  aperture := fun z => D.aperture.aperture (decode z)
  graph_definable := scalarDef_comp (decode_tupleDef (encode_image_definable D.chart))
    D.aperture.graph_definable (fun _ hz => decode_mem h00 hz)
  nonzero := fun _ hz => D.aperture.nonzero _ (decode_mem h00 hz)
  nonnegative := fun _ hz => D.aperture.nonnegative _ (decode_mem h00 hz)
  bound := D.aperture.bound
  bounded := fun _ hz => D.aperture.bounded _ (decode_mem h00 hz)

theorem strict_finite : InactiveFinite (strictChart h00 D.chart) D.coordinate := by
  intro t
  apply ((D.finite t).image encode).subset
  rintro z ⟨⟨u, hu, rfl⟩, ht⟩
  refine ⟨u, ⟨hu, ?_⟩, rfl⟩
  have he : AnnularBlowup.inactive (strictChart h00 D.chart) D.coordinate (encode u) =
      AnnularBlowup.inactive D.chart D.coordinate u := by
    change Function.update (D.chart.coordinate (decode (encode u))) _ _ = _
    rw [decode_encode h00]
    rfl
  rw [← he]
  exact ht

/-- The strict datum: the same blowup on the `∞`-free strict chart. -/
def strictDatum : AnnularDatum B k where
  chart := strictChart h00 D.chart
  coordinate := D.coordinate
  finite := strict_finite h00 D
  aperture := strictAperture h00 D
  bounded := strictChart_bounded h00 D.chart D.bounded

theorem strict_le : ∀ u ∈ D.chart.domain, codeValue (D.aperture.aperture u) ≤
    codeValue ((strictDatum h00 D).aperture.aperture (isoMap (strictIso h00 D.chart) u)) := by
  intro u hu
  rw [strict_isoMap h00 D hu]
  change _ ≤ codeValue (D.aperture.aperture (decode (encode u)))
  rw [decode_encode h00]

theorem strict_ratio_one {w : Fin (1 + D.chart.arity) → M} (hw : w ∈ (graphChart D.chart D.aperture).domain) :
    codeValue (ratio D (strictDatum h00 D) (strictIso h00 D.chart) w) = 1 := by
  rw [codeValue_ratio D (strictDatum h00 D) (strictIso h00 D.chart) hw, strict_isoMap h00 D hw.1]
  change codeValue (D.aperture.aperture (decode (encode _))) * _ = 1
  rw [decode_encode h00, mul_inv_cancel]

theorem strict_second_shell_empty :
    (shellChart (secondDatum D (strictDatum h00 D) (strictIso h00 D.chart) (strict_le h00 D)).chart
      (secondDatum D (strictDatum h00 D) (strictIso h00 D.chart) (strict_le h00 D)).coordinate
      (secondDatum D (strictDatum h00 D) (strictIso h00 D.chart) (strict_le h00 D)).finite
      (secondDatum D (strictDatum h00 D) (strictIso h00 D.chart) (strict_le h00 D)).aperture).domain = ∅ := by
  apply Set.eq_empty_of_forall_notMem
  intro w hw
  obtain ⟨hd, _, h1, h2⟩ := shell_points _ _ hw
  have h3 : codeValue ((secondDatum D (strictDatum h00 D) (strictIso h00 D.chart) (strict_le h00 D)).aperture.aperture
      (w ∘ xIdx (secondDatum D (strictDatum h00 D) (strictIso h00 D.chart) (strict_le h00 D)).chart)) = 1 :=
    strict_ratio_one h00 D hd
  rw [h3] at h2
  exact lt_irrefl _ (h1.trans_le h2)

/-- The strict datum has the class of blowup of the original datum. -/
theorem strict_annular : cls (strictDatum h00 D).annularObject = cls D.annularObject := by
  have hle := strict_le h00 D
  rw [cls_annular (strictDatum h00 D),
    cls_partition (shellE (strictDatum h00 D)) (shallow D (strictDatum h00 D) (strictIso h00 D.chart))
      (shallow_definable D (strictDatum h00 D) (strictIso h00 D.chart)),
    ← cls_eq_of_iso (a := shellBounded D.chart D.coordinate D.finite D.aperture D.bounded)
      (shallowIso D (strictDatum h00 D) (strictIso h00 D.chart) hle),
    ← cls_eq_of_iso (a := shellBounded (secondDatum D (strictDatum h00 D) (strictIso h00 D.chart) hle).chart
        (secondDatum D (strictDatum h00 D) (strictIso h00 D.chart) hle).coordinate
        (secondDatum D (strictDatum h00 D) (strictIso h00 D.chart) hle).finite
        (secondDatum D (strictDatum h00 D) (strictIso h00 D.chart) hle).aperture
        (secondDatum D (strictDatum h00 D) (strictIso h00 D.chart) hle).bounded)
      (deepIso D (strictDatum h00 D) (strictIso h00 D.chart) hle),
    ← cls_eq_of_iso (a := endpointBounded (secondDatum D (strictDatum h00 D) (strictIso h00 D.chart) hle).chart
        (secondDatum D (strictDatum h00 D) (strictIso h00 D.chart) hle).coordinate
        (secondDatum D (strictDatum h00 D) (strictIso h00 D.chart) hle).finite
        (secondDatum D (strictDatum h00 D) (strictIso h00 D.chart) hle).aperture
        (secondDatum D (strictDatum h00 D) (strictIso h00 D.chart) hle).bounded)
      (b := endpointBounded (strictDatum h00 D).chart (strictDatum h00 D).coordinate (strictDatum h00 D).finite
        (strictDatum h00 D).aperture (strictDatum h00 D).bounded)
      (endpointIso D (strictDatum h00 D) (strictIso h00 D.chart) hle),
    cls_empty (shellBounded (secondDatum D (strictDatum h00 D) (strictIso h00 D.chart) hle).chart
        (secondDatum D (strictDatum h00 D) (strictIso h00 D.chart) hle).coordinate
        (secondDatum D (strictDatum h00 D) (strictIso h00 D.chart) hle).finite
        (secondDatum D (strictDatum h00 D) (strictIso h00 D.chart) hle).aperture
        (secondDatum D (strictDatum h00 D) (strictIso h00 D.chart) hle).bounded)
      (strict_second_shell_empty h00 D), add_zero,
    cls_eq_of_iso (a := endpointBounded (secondDatum D (strictDatum h00 D) (strictIso h00 D.chart) hle).chart
        (secondDatum D (strictDatum h00 D) (strictIso h00 D.chart) hle).coordinate
        (secondDatum D (strictDatum h00 D) (strictIso h00 D.chart) hle).finite
        (secondDatum D (strictDatum h00 D) (strictIso h00 D.chart) hle).aperture
        (secondDatum D (strictDatum h00 D) (strictIso h00 D.chart) hle).bounded)
      (b := endpointBounded D.chart D.coordinate D.finite D.aperture D.bounded)
      (unitEndpointIso (secondDatum D (strictDatum h00 D) (strictIso h00 D.chart) hle).chart
        (secondDatum D (strictDatum h00 D) (strictIso h00 D.chart) hle).coordinate
        (secondDatum D (strictDatum h00 D) (strictIso h00 D.chart) hle).finite
        (secondDatum D (strictDatum h00 D) (strictIso h00 D.chart) hle).aperture
        (fun w hw => strict_ratio_one h00 D hw)),
    cls_annular D]

theorem strict_source : cls (strictDatum h00 D).source = cls D.source :=
  (cls_eq_of_iso (a := D.source) (b := (strictDatum h00 D).source) (strictIso h00 D.chart)).symm

end Strict

/-! ### Lemma 7.12 and the lift of blowups -/

section Lift
open DiamondIntegral.Section7.LiftClasses DiamondIntegral.Section7.BlowupLiftClasses
open DiamondIntegral.Section7.BlowupCongruence IntegrationInACVF.Section6.Iteration
open DiamondIntegral.Section2
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]
variable (hc : CanonicalStructure.IsCanonical (M := M)) (h00 : M ⊨ Axioms.ACVF00)
  {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
  (T : LRV.Substructure M) (hsmall : Cardinal.mk (T : Set M) < κ)
  (hΓ : NontrivialDefinableGamma (⟨(T : Set M), ∅⟩ : ParameterBase M))
  (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
  (B₀ : VFGeneratedFieldBase T) (hnt : ∃ x : B₀.field, x ≠ 0 ∧ Valued.v x.val ≠ 1)

/-- Lemma 7.12 (`blowup:same:RV:coa`) on Section 7's classes: for every
aperture datum, `μ𝕃[U^{τ,j}] = μ𝕃[U]` in `K₊ μVF^◇[1+k]`. -/
theorem lemma_7_12 (D : AnnularDatum (BT T) k) :
    liftCls (G := G) (k := 1 + k) hc h00 hκ hs T hsmall hΓ hv B₀ hnt (cls D.annularObject) =
      liftCls (G := G) (k := 1 + k) hc h00 hκ hs T hsmall hΓ hv B₀ hnt (cls D.source) := by
  rw [← strict_annular h00 D, ← strict_source h00 D]
  exact lemma_7_12_noInfinity hc h00 hκ hs T hsmall hΓ hv B₀ hnt (strictDatum h00 D)
    (strictChart_infinityFree h00 D.chart)

/-- A blowup of length one preserves the lift. -/
theorem step_lift {x y : Cls (BT T) (1 + k)} (h : Step x y) :
    liftCls (G := G) (k := 1 + k) hc h00 hκ hs T hsmall hΓ hv B₀ hnt x =
      liftCls (G := G) (k := 1 + k) hc h00 hκ hs T hsmall hΓ hv B₀ hnt y := by
  obtain ⟨n, D, z, rfl, rfl⟩ := h
  rw [map_add, map_add, map_sum, map_sum]
  congr 1
  exact Finset.sum_congr rfl (fun i _ => (lemma_7_12 hc h00 hκ hs T hsmall hΓ hv B₀ hnt (D i)).symm)

theorem steps_lift {n : ℕ} {x y : Cls (BT T) (1 + k)} (h : BlowupSteps n x y) :
    liftCls (G := G) (k := 1 + k) hc h00 hκ hs T hsmall hΓ hv B₀ hnt x =
      liftCls (G := G) (k := 1 + k) hc h00 hκ hs T hsmall hΓ hv B₀ hnt y := by
  induction h with
  | refl _ => rfl
  | cons hab _ ih => exact (step_lift hc h00 hκ hs T hsmall hΓ hv B₀ hnt hab).trans ih

/-- `μIsp`-equivalent classes have the same lift: the lift factors through the
quotient by `μIsp` (one direction of Corollary 7.13). -/
theorem muIsp_lift {x y : Cls (BT T) (1 + k)} (h : MuIsp x y) :
    liftCls (G := G) (k := 1 + k) hc h00 hκ hs T hsmall hΓ hv B₀ hnt x =
      liftCls (G := G) (k := 1 + k) hc h00 hκ hs T hsmall hΓ hv B₀ hnt y := by
  obtain ⟨w, m, n, hx, hy⟩ := h
  exact (steps_lift hc h00 hκ hs T hsmall hΓ hv B₀ hnt hx).trans
    (steps_lift hc h00 hκ hs T hsmall hΓ hv B₀ hnt hy).symm

end Lift

end DiamondIntegral.Section7.BlowupLiftGeneral
