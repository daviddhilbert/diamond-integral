import «section 6».BoundaryBadGammaRelations
import «section 6».FiniteVFMixedGammaBounds
import «section 6».PointwiseSmallPairedBoundary

/-! One original-base named boundary coefficient works on a centre
family with finite VF projection and an arbitrary bounded RV tail.
The actual bad Gamma relation, not a choice of fibre thresholds, gives
the uniform bound. No finiteness of the complete mixed family is used. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section8 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {r s : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]
variable {A : DefSet (rawMixedSpace (M := M) 1 r) S} {B : DefSet (rawMixedSpace (M := M) 1 s) S}

theorem exists_named_boundary_coefficient_finiteVF
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    (linear : GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (hsmall : Cardinal.mk S < κ) (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M))
    (V : Set M) (hV : ∀ a ∈ V,iVF a) (hVS : V ⊆ S) (hSV : S ⊆ algebraicClosureSet V)
    (hnt : ∃ x : vfAlgebraicClosureField V,x≠0 ∧ Valued.v x.val≠1)
    (f : Map A B) (E : DefSet (rawMixedSpace (M := M) 1 r) S) (hEA : E.carrier ⊆ A.carrier)
    (hRV : IsRVPullback A.carrier) (hD : VFDoublyBounded A.carrier)
    (hEVF : (Prod.fst '' E.carrier).Finite) (hERV : RVSupportDoublyBounded E.carrier)
    (D : DefSet (pairedBoundaryDataSpace M (r+s)) S)
    (hPoint : ∀ p : E,∃ η : Gamma M,∀ c : positiveBoundaryCoefficients (S := S) hc,
      η.val<vfValue (c.val 0) →
      (uniformPairedBoundaryDataMap hc f E hEA hRV hD (boundaryPairInput hc E p c)).val ∈ D.carrier) :
    ∃ (c : VF M) (hc0 : c≠0) (hcPos : (1 : GammaInfinity M)<vfValue c),
      S.Definable₁ LRV {c.val} ∧ ∀ p : E,
        (uniformPairedBoundaryDataMap hc f E hEA hRV hD
          (boundaryPairInput hc E p ⟨(fun _ => c),hc0,hcPos⟩)).val ∈ D.carrier := by
  let H := BoundaryBadGamma.relation hc f E hEA hRV hD D
  obtain ⟨δ,hδ,hδ1,hBound⟩ := finite_vf_positive_gamma_relation_named_bound hc h00 linear hκ hs hsmall hΓ
    E hEVF hERV H (BoundaryBadGamma.source hc f E hEA hRV hD D)
    (BoundaryBadGamma.positive hc f E hEA hRV hD D)
    (fun p => BoundaryBadGamma.row_bddAbove hc f E hEA hRV hD D p (hPoint p))
  apply exists_named_boundary_coefficient_for_data h00 hc hv V hV hVS hSV hnt f E hEA hRV hD D
  refine ⟨δ,hδ1,fun c hcSmall p => ?_⟩
  by_contra hBad
  let z := boundaryPairInput hc E p c
  let b : BoundaryBadGamma.domain hc f E hEA hRV hD D := ⟨z.val,z,rfl,hBad⟩
  have hMember : (p.val,finiteValue (c.val 0) c.property.1) ∈ H.carrier := by
    apply (BoundaryBadGamma.mem_relation_iff hc f E hEA hRV hD D p.val _).mpr
    refine ⟨b,rfl,?_⟩
    rw [BoundaryBadGamma.valueMap_value]
    rfl
  have h := hBound p.val (finiteValue (c.val 0) c.property.1) hMember
  have hSmall : δ<finiteValue (c.val 0) c.property.1 := hcSmall
  exact (not_lt_of_ge h) hSmall

theorem exists_named_small_paired_boundary_coefficient_finiteVF
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    (linear : GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (hsmall : Cardinal.mk S < κ) (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M))
    (V : Set M) (hV : ∀ a ∈ V,iVF a) (hVS : V ⊆ S) (hSV : S ⊆ algebraicClosureSet V)
    (hnt : ∃ x : vfAlgebraicClosureField V,x≠0 ∧ Valued.v x.val≠1)
    (f : Map A B) (hf : ProperCovariantHomeomorphism f)
    (E : DefSet (rawMixedSpace (M := M) 1 r) S) (hEA : E.carrier ⊆ A.carrier)
    (hRV : IsRVPullback A.carrier) (hD : VFDoublyBounded A.carrier)
    (hEVF : (Prod.fst '' E.carrier).Finite) (hERV : RVSupportDoublyBounded E.carrier)
    (α β : Gamma M)
    (hα : S.Definable LRV {z : Fin 1 → M | z 0 ∈ Values.gammaPullback {α}})
    (hβ : S.Definable LRV {z : Fin 1 → M | z 0 ∈ Values.gammaPullback {β}}) :
    ∃ (c : VF M) (hc0 : c≠0) (hcPos : (1 : GammaInfinity M)<vfValue c),
      S.Definable₁ LRV {c.val} ∧ ∀ p : E,
        (uniformPairedBoundaryDataMap hc f E hEA hRV hD
          (boundaryPairInput hc E p ⟨(fun _ => c),hc0,hcPos⟩)).val ∈
          (smallPairedBoundaryData f α β hα hβ).carrier :=
  exists_named_boundary_coefficient_finiteVF h00 hc linear hκ hs hv hsmall hΓ V hV hVS hSV hnt
    f E hEA hRV hD hEVF hERV (smallPairedBoundaryData f α β hα hβ)
    (point_eventual_small_paired_boundary_data hc hκ hs hsmall hv f hf hRV hD E hEA α β hα hβ)

end DiamondIntegral.Section6
