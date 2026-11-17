import «section 3».GammaTwoVFAllOrderMeasuredValues
import «section 3».GammaPrincipalGeometricReflection
import «section 3».GammaLastGeometryBaseReduction
import «section 3».GammaGroundMonotoneBases
import «section 3».GammaRawContractionLiteralRows
import «section 3».GammaMeasuredGeometryFormulaWitnesses
import Integration7.FrozenGeneratedVolumeContexts
import Integration7.DefinableVolumeRowReduction
import IntegrationSection6.GammaClosureIsomorphisms

/-! The full two-coordinate comparison specializes to actual frozen
programs and arbitrary complete Gamma densities. All temporary generated
closure names are removed from the finite geometric proof. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5 SpecialTransformations.Section7
open IntegrationInACVF.Section5 IntegrationInACVF.Section6 IntegrationInACVF.Section6.FiniteRV IntegrationInACVF.Section7
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] [CharZero (Section2.VF M)]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {n a : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (Section2.VF M) G]

theorem gammaFrozen_two_VF_measured_witness
    (C : BaseContext M) (hBC : B.real ⊆ (C.base : Set M))
    (hv : ∀ x y : Section2.VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (hg : Cardinal.mk B.gamma < C.κ) (hNames : commonRealNames B ⊆ (C.base : Set M))
    (hGenerated : VFGammaGeneratedBase B)
    (δ : Values.Gamma (M := M)) (hδ : δ ∈ B.gamma) (hδ1 : 1 < δ)
    (x : Fin n → VF (M := M))
    (A : SpecialTransformations.Section5.DefSet (M := M)
      ((C.base : Set M) ∪ Set.range (vfValues x)) 2 a)
    (hA : GammaSetDefinable ⟨B.real ∪ Set.range (vfValues x),B.gamma⟩ (carrier A))
    (hfin : ∀ y : Fin 2 → VF (M := M), {r | (y,r) ∈ carrier A}.Finite)
    (ω : GammaGroundVolumeForm hc ⟨B.real ∪ Set.range (vfValues x),B.gamma⟩
      (GammaGroundDefSet.univ hc ⟨B.real ∪ Set.range (vfValues x),B.gamma⟩ (rawRVSpace (M := M) a)))
    {σ τ : Equiv.Perm (Fin 2)} (T : StandardContraction A σ) (W : StandardContraction A τ)
    (hT : GammaProgramDefinable ⟨B.real ∪ Set.range (vfValues x),B.gamma⟩ T.program)
    (hW : GammaProgramDefinable ⟨B.real ∪ Set.range (vfValues x),B.gamma⟩ W.program)
    (F : GammaMeasuredRVSchema hc B n T.arity 2 (fun _ => .vf))
    (E : GammaMeasuredRVSchema hc B n W.arity 2 (fun _ => .vf))
    (hF : F.valid (vfValues x)) (hE : E.valid (vfValues x))
    (hFT : ∀ r y, F.object.rowVolume (vfValues x) r y ↔
      (Fin.elim0,r) ∈ carrier T.target ∧ r ∘ T.volumeIndex = y)
    (hET : ∀ r y, E.object.rowVolume (vfValues x) r y ↔
      (Fin.elim0,r) ∈ carrier W.target ∧ r ∘ W.volumeIndex = y)
    (hFD : ∀ r c, F.rowDensity (vfValues x) r c ↔ (Fin.elim0,r) ∈ carrier T.target ∧
      (ω ⟨r ∘ suffixIndex T.program.rvArity_le,Set.mem_univ _⟩).val = (volumeGammaSpace hc).decode c)
    (hED : ∀ r c, E.rowDensity (vfValues x) r c ↔ (Fin.elim0,r) ∈ carrier W.target ∧
      (ω ⟨r ∘ suffixIndex W.program.rvArity_le,Set.mem_univ _⟩).val = (volumeGammaSpace hc).decode c) :
    ∃ H : GammaMeasuredRelationSchema F.essential E.essential, H.valid (vfValues x) := by
  let Bx : Base (M := M) := ⟨B.real ∪ Set.range (vfValues x),B.gamma⟩
  let P := vfParameterCoefficientBase B x
  let D := frozenGeneratedVolumeContext hc C B hBC hg x
  let hSD := frozen_generated_context_contains hc C hBC hg x
  have hPN := frozen_generated_context_contains_names hc C hBC hNames hg x
  have hPD : P.real ⊆ (D.base : Set M) := fun _ h => hPN (Or.inl h)
  let AD := extendBase A hSD
  have hAD : GammaSetDefinable P (carrier AD) :=
    hA.mono (subset_closureBase Bx).1 (subset_closureBase Bx).2
  let R := T.extendBase hSD
  let S := W.extendBase hSD
  have hR : GammaProgramDefinable P R.program := gamma_program_mono
    (subset_closureBase Bx).1 (subset_closureBase Bx).2 _ (T.program.extendBase_gamma hSD hT)
  have hS : GammaProgramDefinable P S.program := gamma_program_mono
    (subset_closureBase Bx).1 (subset_closureBase Bx).2 _ (W.program.extendBase_gamma hSD hW)
  let Ω : GammaGroundVolumeForm hc P (GammaGroundDefSet.univ hc P (rawRVSpace (M := M) a)) :=
    gammaGroundVolumeFormMonoBase ω (subset_closureBase Bx).1 (subset_closureBase Bx).2
  let hpGamma := vfParameterCoefficientBase_gamma_small C.uncountable
    ((Cardinal.mk_le_mk_of_subset hBC).trans_lt C.small) hg x
  have hValue := gammaTwo_VF_all_order_measured_values D hPD hv hpGamma hPN
    (vfParameterCoefficientBase_generated hGenerated x) δ
    (vfParameterCoefficientBase_gamma_contains x hδ) hδ1 AD hAD hfin Ω R S hR hS
  let RT := gammaNativeRawMeasuredContraction D hPD hAD hfin R hR Ω
  let ST := gammaNativeRawMeasuredContraction D hPD hAD hfin S hS Ω
  have hGeom := gammaLastMeasuredGeometry_of_native
    (gammaPrincipal_geometric_reflection D.uncountable.le D.saturated D.model00
      ((Cardinal.mk_le_mk_of_subset hPD).trans_lt D.small) hValue)
  have hr : Cardinal.mk B.real < C.κ := (Cardinal.mk_le_mk_of_subset hBC).trans_lt C.small
  have hrx : Cardinal.mk Bx.real < C.κ := small_union_range C.uncountable.le B.real hr (vfValues x)
  let HBase := closureBaseReduction Bx
  have hReduced := gammaLastMeasuredGeometry_reduce C.uncountable.le C.saturated C.model00
    ((Cardinal.mk_le_mk_of_subset hPD).trans_lt D.small) hrx HBase hGeom
  have hRV : R.volumeIndex = T.volumeIndex := funext (T.extendBase_volumeIndex hSD)
  have hSV : S.volumeIndex = W.volumeIndex := funext (W.extendBase_volumeIndex hSD)
  have rRT : GammaMeasuredLiteralObjectRow (vfValues x) RT F.essential := by
    apply gammaRaw_contraction_literal_row D hPD hAD hfin R hR Ω F (vfValues x)
    · intro r y
      change F.object.rowVolume (vfValues x) r y ↔
        (Fin.elim0,r) ∈ carrier T.target ∧ r ∘ R.volumeIndex = y
      rw [hRV]
      exact hFT r y
    · exact hFD
  have rST : GammaMeasuredLiteralObjectRow (vfValues x) ST E.essential := by
    apply gammaRaw_contraction_literal_row D hPD hAD hfin S hS Ω E (vfValues x)
    · intro r y
      change E.object.rowVolume (vfValues x) r y ↔
        (Fin.elim0,r) ∈ carrier W.target ∧ r ∘ S.volumeIndex = y
      rw [hSV]
      exact hET r y
    · exact hED
  have rRT' : GammaMeasuredObjectRow (vfValues x) (gammaGroundMeasuredRVReduceObject HBase RT) F.essential :=
    ⟨rRT.domain,rRT.volume,rRT.density⟩
  have rST' : GammaMeasuredObjectRow (vfValues x) (gammaGroundMeasuredRVReduceObject HBase ST) E.essential :=
    ⟨rST.domain,rST.volume,rST.density⟩
  exact gammaMeasured_geometry_formula_witness C.uncountable.le C.saturated C.model00 hr hg hReduced
    F.essential E.essential (F.essential_valid _ hF) (E.essential_valid _ hE) rRT' rST'

end DiamondIntegral.Section3
