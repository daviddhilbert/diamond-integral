import «section 4».RelativeAnnularConverse
import «section 4».RVRadiusIdeal

/-! Notation 4.17, last sentence: constant apertures give `I = (P_Γ) ⊆ J_var`.

For an admissible radius `γ` with a definable lift `t`, the manuscript datum
`U = (1)` (the structural unit point), `j = 0`, constant aperture `t` has shell
`{s : 1 < vrv s ≤ γ}` (the annulus chart) and endpoint the point `t`; its
generator is the scalar generator `P_γ = [annulus γ] + [t] - [1]`. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry
open DiamondIntegral.Section3

namespace DiamondIntegral.Section4.RelativeAnnularScalar
open DiamondIntegral.Section4 DiamondIntegral.Section4.RVMeasuredCharts
open DiamondIntegral.Section4.FiniteTupleBlocks
open DiamondIntegral.Section4.AnnularBlowup DiamondIntegral.Section4.BlowupChart
open DiamondIntegral.Section4.BlowupRelation DiamondIntegral.Section4.RelativeAnnularGenerators
open DiamondIntegral.Section4.RelativeAnnularConverse

variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF] {B : Base (M := M)}
variable (γ : Values.Gamma (M := M)) (hγ : γ ∈ GammaRVLifts.admissibleRadii B)
  (t : RVRadiusGenerators.RadiusLift B γ)

/-- The unit point as a chart of degree `1 + 0`. -/
abbrev U0 : Chart B (1 + 0) := unitPoint

theorem point_finite : InactiveFinite (U0 (B := B)) 0 :=
  fun _ => (Set.finite_singleton ![one]).subset (fun _ h => h.1)

omit [LRV.Structure M] hM in
theorem pair_eq (w : Fin (1 + 1) → M) (a b : M) :
    (w ∘ headIndex 1 1 = ![a] ∧ ![b] = w ∘ tailIndex 1 1) ↔ w = ![a, b] := by
  constructor
  · rintro ⟨h1, h2⟩
    funext i
    fin_cases i
    · exact congrFun h1 0
    · exact (congrFun h2 0).symm
  · rintro rfl
    exact ⟨funext (fun i => by fin_cases i; rfl), funext (fun i => by fin_cases i; rfl)⟩

theorem graph_domain_eq :
    RVDefinableGraphExtension.domain (U0 (B := B)) (fun _ => raw t.point) = {![one, raw t.point]} := by
  ext w
  exact pair_eq w one (raw t.point)

/-- The constant aperture `t`. -/
def constAperture : Aperture (U0 (B := B)) where
  aperture _ := raw t.point
  graph_definable := by
    rw [graph_domain_eq γ t]
    exact RVPointChoices.pair_tuple_definable B RVRadiusGenerators.oneCode t.point
      (RVRadiusGenerators.oneCode_definable B) t.definable
  nonzero _ _ := ⟨t.point.val.property, t.point.property⟩
  nonnegative _ _ := by
    rw [codeValue_raw, t.value_eq]
    exact hγ.1
  bound := γ
  bounded _ _ := le_of_eq ((codeValue_raw t.point).trans t.value_eq)

/-- The manuscript datum of `P_γ`. -/
def scalarDatum : AnnularDatum B 0 where
  chart := U0
  coordinate := 0
  finite := point_finite
  aperture := constAperture γ hγ t
  bounded := (RVRadiusIdeal.boundedPoint B RVRadiusGenerators.oneCode
    (RVRadiusGenerators.oneCode_definable B)).domain_bounded

theorem one_eq : (one : M) = iRVOne := RVOperations.one_val

theorem raw_iRV : iRV (raw t.point) := t.point.val.property

theorem unit_weight (x : Fin 1 → M) (hx : x ∈ (U0 (B := B)).domain) : (U0 (B := B)).correctedWeight x = 1 :=
  (RVPointChoices.pointChart_weight B RVRadiusGenerators.oneCode
    (RVRadiusGenerators.oneCode_definable B) ⟨x, hx⟩).trans RVRadiusGenerators.oneCode_value

theorem annulus_weight (z : Fin 1 → M) :
    (RVRadiusIdeal.boundedAnnulus B γ hγ).toChart.correctedWeight z = codeValue (z 0) := by
  change 1 * (∏ i : Fin 1, codeValue (z i)) = _
  simp

/-- The endpoint of the scalar datum is the point `t`. -/
def scalarEndpointIso :
    Iso (endpointBounded U0 0 point_finite (constAperture γ hγ t) (scalarDatum γ hγ t).bounded).toChart
      (RVRadiusIdeal.boundedPoint B t.point t.definable).toChart := by
  refine RVCoordinateMaps.coordinateIso _ _ (fun _ => aIdx U0) ?_ ?_
  · show Set.BijOn _ (RVDefinableGraphExtension.domain (U0 (B := B)) (fun _ => raw t.point)) {![raw t.point]}
    rw [graph_domain_eq γ t, Set.bijOn_singleton]
    funext i
    fin_cases i
    rfl
  · intro w hw
    have hw' : w = ![one, raw t.point] := (graph_domain_eq γ t ▸ hw : w ∈ ({![one, raw t.point]} : Set _))
    subst hw'
    change 1 * (∏ l : Fin (1 + 0), codeValue (blownCoordinate (U0 (B := B)) 0 ![one]
      (raw t.point) l)) = (RVPointChoices.pointChart B t.point t.definable).correctedWeight ![raw t.point]
    rw [RVPointChoices.pointChart_weight B t.point t.definable ⟨![raw t.point], rfl⟩, ← codeValue_raw]
    rw [one_mul]
    change (∏ l : Fin 1, codeValue (blownCoordinate (U0 (B := B)) 0 ![one] (raw t.point) l)) = _
    rw [Fin.prod_univ_one, blownCoordinate_at]
    change codeValue (iRVMul (raw t.point) one) = _
    have h := RVOperations.mul_val t.point.val 1
    rw [mul_one, RVOperations.one_val] at h
    rw [one_eq]
    exact congrArg codeValue h.symm

/-- The shell of the scalar datum is the annulus `1 < vrv s ≤ γ`. -/
def scalarShellIso :
    Iso (shellBounded U0 0 point_finite (constAperture γ hγ t) (scalarDatum γ hγ t).bounded).toChart
      (RVRadiusIdeal.boundedAnnulus B γ hγ).toChart := by
  have hA := annular_mem_iff (graphChart (U0 (B := B)) (constAperture γ hγ t)) (aIdx U0)
    (graph_aperture_nonzero U0 (constAperture γ hγ t))
  have hgraph : (graphChart (U0 (B := B)) (constAperture γ hγ t)).domain = {![one, raw t.point]} :=
    graph_domain_eq γ t
  have hval : codeValue (raw t.point) = γ := (codeValue_raw t.point).trans t.value_eq
  have tail_eq : ∀ w : Fin (1 + (1 + 1)) → M,
      w ∘ tailIndex 1 (1 + 1) = fun _ => w (sIdx (U0 (B := B))) := by
    intro w
    funext i
    fin_cases i
    rfl
  refine RVCoordinateMaps.coordinateIso _ _ (fun _ => sIdx U0) ?_ ?_
  · refine ⟨fun w hw => ?_, fun w hw v hv he => ?_, fun z hz => ?_⟩
    · obtain ⟨h1, h2, h3, h4⟩ := (hA w).mp hw
      have hh : w ∘ headIndex 1 (1 + 1) = ![one, raw t.point] := by
        have h1' : w ∘ headIndex 1 (1 + 1) ∈ (graphChart (U0 (B := B)) (constAperture γ hγ t)).domain := h1
        rw [hgraph] at h1'
        exact h1'
      refine ⟨?_, h3, ?_⟩
      · show Proper (fun _ : Fin 1 => w (sIdx (U0 (B := B))))
        have h2' : Proper (w ∘ tailIndex 1 (1 + 1)) := h2
        rw [tail_eq] at h2'
        exact h2'
      · change codeValue (w (sIdx U0)) ≤ γ
        rw [← hval]
        have h4' : codeValue (w (tailIndex 1 (1 + 1) 0)) ≤ codeValue ((w ∘ headIndex 1 (1 + 1)) (aIdx U0)) := h4
        rw [hh] at h4'
        exact h4'
    · have mem1 : ∀ u, u ∈ (shellBounded U0 0 point_finite (constAperture γ hγ t)
          (scalarDatum γ hγ t).bounded).toChart.domain → u ∘ headIndex 1 (1 + 1) = ![one, raw t.point] := by
        intro u hu
        have h1' : u ∘ headIndex 1 (1 + 1) ∈ (graphChart (U0 (B := B)) (constAperture γ hγ t)).domain :=
          ((hA u).mp hu).1
        rw [hgraph] at h1'
        exact h1'
      have hw1 := mem1 w hw
      have hv1 := mem1 v hv
      have he' : (fun _ : Fin 1 => w (sIdx (U0 (B := B)))) = fun _ => v (sIdx (U0 (B := B))) := he
      have hs : w (sIdx (U0 (B := B))) = v (sIdx (U0 (B := B))) := congrFun he' 0
      rw [← join_reconstruct 1 (1 + 1) w, ← join_reconstruct 1 (1 + 1) v, hw1, hv1, tail_eq, tail_eq, hs]
    · obtain ⟨hz1, hz2, hz3⟩ := hz
      let w := join 1 (1 + 1) ![one, raw t.point] z
      have hwh : w ∘ headIndex 1 (1 + 1) = ![one, raw t.point] := funext (join_head 1 _ _ _)
      have hwt : w ∘ tailIndex 1 (1 + 1) = z := funext (join_tail 1 _ _ _)
      refine ⟨w, (hA w).mpr ⟨?_, ?_, ?_, ?_⟩, ?_⟩
      · show w ∘ headIndex 1 (1 + 1) ∈ (graphChart (U0 (B := B)) (constAperture γ hγ t)).domain
        rw [hwh, hgraph]
        exact rfl
      · show Proper (w ∘ tailIndex 1 (1 + 1))
        rw [hwt]
        exact hz1
      · show 1 < codeValue ((w ∘ tailIndex 1 (1 + 1)) 0)
        rw [hwt]
        exact hz2
      · show codeValue ((w ∘ tailIndex 1 (1 + 1)) 0) ≤ codeValue ((w ∘ headIndex 1 (1 + 1)) (aIdx U0))
        rw [hwt, hwh]
        exact hz3.trans_eq hval.symm
      · show (fun _ : Fin 1 => w (sIdx (U0 (B := B)))) = z
        funext i
        fin_cases i
        exact congrFun hwt _
  · intro w hw
    show (shellChart U0 0 point_finite (constAperture γ hγ t)).correctedWeight w =
      (RVRadiusIdeal.boundedAnnulus B γ hγ).toChart.correctedWeight (fun _ => w (sIdx (U0 (B := B))))
    rw [shell_weight U0 0 point_finite (constAperture γ hγ t) w hw,
      unit_weight _ (shell_points U0 (constAperture γ hγ t) hw).1, one_mul, annulus_weight]

/-- Notation 4.17: each scalar generator `P_γ` is a manuscript generator. -/
theorem pGamma_eq_generator :
    RVRadiusIdeal.pGamma B γ hγ = (scalarDatum γ hγ t).generator := by
  rw [AnnularDatum.generator_eq, RVRadiusIdeal.pGamma_eq B γ hγ t]
  unfold RVRadiusIdeal.radiusGenerator
  rw [← RVBoundedRing.objectClass_iso (scalarShellIso γ hγ t),
    ← RVBoundedRing.objectClass_iso (scalarEndpointIso γ hγ t)]
  rfl

end DiamondIntegral.Section4.RelativeAnnularScalar

namespace DiamondIntegral.Section4.RelativeAnnularScalar
open DiamondIntegral.Section4 DiamondIntegral.Section4.RelativeAnnularGenerators

variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF] {B : Base (M := M)}

/-- Notation 4.17: constant apertures give `I = (P_Γ) ⊆ J_var`. -/
theorem radiusIdeal_le_manuscriptIdeal : RVRadiusIdeal.radiusIdeal B ≤ manuscriptIdeal B := by
  apply Ideal.span_le.mpr
  rintro x ⟨γ, hγ, rfl⟩
  rw [pGamma_eq_generator γ hγ (Classical.choice (RVRadiusGenerators.radiusLift_exists B γ hγ))]
  exact Ideal.subset_span ⟨0, _, rfl⟩

end DiamondIntegral.Section4.RelativeAnnularScalar
