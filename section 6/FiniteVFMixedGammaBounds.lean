import «section 6».MixedGammaRelationRows
import «section 6».FinitePrefixUniformRadii
import «section 6».StageShearChartFamilies
import «section 6».RVCoordinateArithmeticObjects

/-! A positive Gamma relation over finitely many VF coordinates and
an arbitrary bounded RV tail has one original-base named bound whenever
each individual row is bounded. No RV parameter is added to the base. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n r : ℕ}

theorem mixedTuple_prefix_finite (E : Set (Mixed M n r)) (hVF : (Prod.fst '' E).Finite) :
    ((fun x : Fin (n+r) → M => x ∘ Fin.castAdd r) '' (mixedTuple '' E)).Finite := by
  apply (hVF.image vfValues).subset
  rintro x ⟨z,⟨p,hp,rfl⟩,rfl⟩
  refine ⟨p.1,⟨p,hp,rfl⟩,?_⟩
  funext i
  exact (Fin.append_left _ _ i).symm

theorem mixedTuple_tail_nonzero (E : Set (Mixed M n r)) (hRV : RVSupportDoublyBounded E) :
    ∀ x ∈ mixedTuple '' E,∀ i : Fin r,GammaParameters.NonzeroRV (x (Fin.natAdd n i)) := by
  rintro x ⟨p,hp,rfl⟩ i
  simp only [mixedTuple,Fin.append_right,rvValues]
  exact ⟨(p.2 i).property,hRV.nonzero_code p hp i⟩

theorem mixedTuple_tail_bounded (E : Set (Mixed M n r)) (hRV : RVSupportDoublyBounded E) :
    RVCodeDoublyBounded ((fun x : Fin (n+r) → M => x ∘ Fin.natAdd n) '' (mixedTuple '' E)) := by
  obtain ⟨β,hβ⟩ := hRV
  refine ⟨β,?_⟩
  rintro x ⟨z,⟨p,hp,rfl⟩,rfl⟩ i
  have hNZ : p.2 i≠rvZero M := by
    intro he
    have hCode := congrArg (fun x : RVInfinity M => x.val) he
    exact (RVSupportDoublyBounded.nonzero_code ⟨β,hβ⟩ p hp i) hCode
  simp only [Function.comp_apply,mixedTuple,Fin.append_right,rvValues]
  change (β⁻¹).val≤(GammaParameters.codeValue ((p.2 i).val)).val ∧
    (GammaParameters.codeValue ((p.2 i).val)).val≤β.val
  rw [nonzero_rv_codeValue_val (p.2 i) hNZ]
  exact hβ p hp i

theorem finite_vf_positive_gamma_relation_named_bound
    (hc : CanonicalStructure.IsCanonical (M := M)) (h00 : M ⊨ Axioms.ACVF00)
    (linear : GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (hsmall : Cardinal.mk S < κ) (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M))
    (E : DefSet (rawMixedSpace (M := M) n r) S)
    (hVF : (Prod.fst '' E.carrier).Finite) (hRV : RVSupportDoublyBounded E.carrier)
    (H : DefSet ((rawMixedSpace (M := M) n r).prod rawGammaPresentation) S)
    (hSource : ∀ z ∈ H.carrier,z.1 ∈ E.carrier)
    (hPositive : ∀ (p : Mixed M n r) (γ : Gamma M),(p,γ) ∈ H.carrier → 1≤γ)
    (hRows : ∀ p : E,BddAbove {γ : Gamma M | (p.val,γ) ∈ H.carrier}) :
    ∃ δ : Gamma M,S.Definable LRV {z : Fin 1 → M | z 0 ∈ Values.gammaPullback {δ}} ∧
      1≤δ ∧ ∀ (p : Mixed M n r) (γ : Gamma M),(p,γ) ∈ H.carrier → γ≤δ := by
  let D := mixedTuple '' E.carrier
  let R := mixedGammaRelationRows H
  have hD : S.Definable LRV D := (mixedTuple_image_definable_iff E.carrier).mpr E.definable
  have hR : S.Definable LRV (rawGammaFamilyGraph D R) := mixedGammaRelationRows_definable H E hSource
  have hRowBounds (x) (hx : x ∈ D) : (upperBounds (R x)).Nonempty := by
    obtain ⟨p,hp,rfl⟩ := hx
    obtain ⟨δ,hδ⟩ := hRows ⟨p,hp⟩
    exact ⟨δ,fun γ hγ => hδ ((mixedGammaRelationRows_at H p γ).mp hγ)⟩
  obtain ⟨δ,hδ,hδ1,hGood⟩ := finite_prefix_rv_upper_rays_named_threshold hc h00 linear hκ hs hsmall hΓ
    D hD (mixedTuple_prefix_finite E.carrier hVF) (mixedTuple_tail_nonzero E.carrier hRV)
    (mixedTuple_tail_bounded E.carrier hRV) (fun x => upperBounds (R x))
    (rawGammaUpperGraph_definable S D hD R hR) hRowBounds
    (fun _ _ a ha b hab γ hγ => (ha hγ).trans hab)
  obtain ⟨β,hβ⟩ := exists_gt (max δ 1)
  have hUnion : ∃ β : Gamma M,∀ x ∈ D,∀ γ ∈ R x,β⁻¹≤γ ∧ γ≤β := by
    refine ⟨β,fun x hx γ hγ => ?_⟩
    obtain ⟨p,hpx,hpH⟩ := hγ
    refine ⟨(inv_le_one'.mpr ((le_max_right _ _).trans hβ.le)).trans (hPositive _ _ hpH),?_⟩
    exact hGood x hx β ((le_max_left _ _).trans_lt hβ) ⟨p,hpx,hpH⟩
  obtain ⟨η,hη,hBound⟩ := bounded_gamma_rows_named_bound hc h00 D R hR hUnion
  refine ⟨max η 1,gamma_max_named η 1 hη (gamma_one_named hc),le_max_right _ _,fun p γ hz => ?_⟩
  have h := (hBound (mixedTuple p) ⟨p,hSource (p,γ) hz,rfl⟩ γ ⟨p,rfl,hz⟩).2
  exact h.trans (le_max_left _ _)

end DiamondIntegral.Section6
