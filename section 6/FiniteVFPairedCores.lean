import «section 6».FiniteVFBoundaryCoefficients
import «section 6».UniformFinitePairedCores

/-! Whole paired offset data over an original-base centre family with
finite VF projection and arbitrarily many bounded retained RV labels.
The legacy data record has no finite-mixed-family premise. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 9000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section8 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {r s : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]
variable {A : DefSet (rawMixedSpace (M := M) 1 r) S} {B : DefSet (rawMixedSpace (M := M) 1 s) S}

theorem exists_uniform_paired_cores_finiteVF
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    (linear : GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (hsmall : Cardinal.mk S < κ) (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M))
    (V : Set M) (hV : ∀ a ∈ V,iVF a) (hVS : V ⊆ S) (hSV : S ⊆ algebraicClosureSet V)
    (hnt : ∃ x : vfAlgebraicClosureField V,x≠0 ∧ Valued.v x.val≠1)
    (f : Map A B) (h : ProperCovariantHomeomorphism f)
    (hRV : IsRVPullback A.carrier) (hD : VFDoublyBounded A.carrier)
    (E : DefSet (rawMixedSpace (M := M) 1 r) S) (hEA : E.carrier ⊆ A.carrier)
    (hEVF : (Prod.fst '' E.carrier).Finite) (hERV : RVSupportDoublyBounded E.carrier)
    (α β : Gamma M)
    (hα : S.Definable LRV {z : Fin 1 → M | z 0 ∈ Values.gammaPullback {α}})
    (hβ : S.Definable LRV {z : Fin 1 → M | z 0 ∈ Values.gammaPullback {β}}) :
    Nonempty (UniformFinitePairedCores f E hEA α β) := by
  obtain ⟨c,hc0,hcPos,hcDef,hAll⟩ := exists_named_small_paired_boundary_coefficient_finiteVF
    h00 hc linear hκ hs hv hsmall hΓ V hV hVS hSV hnt f h E hEA hRV hD hEVF hERV α β hα hβ
  let dMap := selectedBoundaryOffsetMap hc (Map.id A) E hEA hRV hD c hc0 hcDef hcPos
  let eMap := selectedBoundaryOffsetMap hc f E hEA hRV hD c hc0 hcDef hcPos
  have hd (p : E) : (dMap p).val 0 ≠ 0 ∧ α.val < vfValue ((dMap p).val 0) := (hAll p).2.1.2
  have he (p : E) : (eMap p).val 0 ≠ 0 ∧ β.val < vfValue ((eMap p).val 0) := (hAll p).2.2
  have hPair (p : E) :
      centeredGammaDisc (p.val.1 0) (finiteValue ((dMap p).val 0) (hd p).1) ⊆
          unaryGraphFibreSource f p.val.2 (f ⟨p.val,hEA p.property⟩).val.2 ∧
      unaryGraphFibreMap f p.val.2 (f ⟨p.val,hEA p.property⟩).val.2 ''
        centeredGammaDisc (p.val.1 0) (finiteValue ((dMap p).val 0) (hd p).1)=
        centeredGammaDisc ((f ⟨p.val,hEA p.property⟩).val.1 0) (finiteValue ((eMap p).val 0) (he p).1) := by
    have hCode := (hAll p).1
    change pairedBoundaryDataCodes _ ∈ parameterizedPairedDiscCodes (unaryMixedScalarGraph f) at hCode
    have hGeom := (mixedPairedDiscCodes_at f p.val.2 (f ⟨p.val,hEA p.property⟩).val.2
      (p.val.1 0) ((f ⟨p.val,hEA p.property⟩).val.1 0) ((dMap p).val 0) ((eMap p).val 0) (hd p).1 (he p).1).mp hCode
    exact hGeom.2.2
  refine ⟨{
    sourceOffset := dMap
    targetOffset := eMap
    sourceNonzero := fun p => (hd p).1
    targetNonzero := fun p => (he p).1
    sourceFloor := fun p => (hd p).2
    targetFloor := fun p => (he p).2
    sourceDisc := fun p => (hPair p).1
    targetDisc := ?_
    image := fun p => (hPair p).2 }⟩
  intro p y hy
  obtain ⟨x,hx,rfl⟩ := (hPair p).2.symm ▸ hy
  exact (unaryGraphFibreMap_bijOn f h.bijective.injective _ _).mapsTo ((hPair p).1 hx)

end DiamondIntegral.Section6
