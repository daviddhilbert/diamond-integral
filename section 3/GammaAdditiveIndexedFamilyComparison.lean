import «section 3».GammaSpecialFamilyVolumes
import «section 3».GammaAdditiveSpecialComparison

/-! The same prepared indexed-family comparison holds for every additive
elementary invariant. The proof reuses the checked special chain and
actual indexed RV coordinate map, retaining finite geometric derivations. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5 SpecialTransformations.Section7
open IntegrationInACVF.Section6 IntegrationInACVF.Section6.FiniteRV
namespace DiamondIntegral.Section3
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {V : Type*} [AddCommMonoid V]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {n l : ℕ}
local notation "N" => (@CanonicalStructure.normalize M sM)
local notation "hN" => (@CanonicalStructure.normalized_model M sM hM)

theorem gammaSpecial_indexed_family_additive_comparison
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (h00 : M ⊨ Axioms.ACVF00) (hr : Cardinal.mk B.real < κ)
    (χ : GammaGroundMeasuredRVKPlus hc B (n+1) →+ V)
    (hχ : GammaNativeElementaryInvariant hκ hs h00 hr χ)
    (U : GammaObjectAt B Set.univ (n+1))
    {H : SpecialTransformations.Section5.DefSet (M := M) Set.univ (n+1) (rvObjectArity U.object.obj)}
    (h : @PresentsLift M N hN Set.univ (n+1) U.object.obj (normalizedPointSet H))
    {X : SpecialTransformations.Section5.DefSet (M := M) Set.univ (n+1) 0}
    {Z : SpecialTransformations.Section5.DefSet (M := M) Set.univ (n+1) l}
    (T : SpecialBijection X Z)
    (hHX : ∀ q ∈ carrier H, (q.1,Fin.elim0) ∈ carrier X)
    (L : GammaSpecialFamilyLift (B := B) T H hHX)
    (F : GammaFiniteRVSchema B (n+1) (rvObjectArity U.object.obj) 0)
    (G : GammaFiniteRVSchema B ((n+1)+l) (rvObjectArity U.object.obj) 0 (fun _ => .rv))
    (hSource : carrier H = vfSchemaSource (carrier X) F)
    (hRows : ∀ q : Z, GammaSchemaRowAgreement F (rawVFParameter (T.inverseMap q).val) G (rawPreparedKey q.val))
    (BP : PreparedIndexPresentation B Z) (P : G.IndexedPresentation BP)
    (ω : GammaGroundVolumeForm hc B (Section5.nativeRVGroundDomain U))
    (hG : ∀ t ∈ preparedKeyDomain Z, G.rowDomain (rvValues t) ⊆ (Section5.nativeRVGroundDomain (hc := hc) U).carrier) :
    gammaNativeAdditiveValue χ U ω =
      gammaNativeAdditiveValue χ (gammaUniversalObject P.toGamma)
        (ω.comp (gammaIndexedOriginalLabelMap BP G P (Section5.nativeRVGroundDomain U) hG)) := by
  obtain ⟨hKF,hClass⟩ := gammaNativeAdditiveSpecial_comparison hκ hs h00 hr χ hχ U h L.special L.graph ω
  let K := gammaPullbackAt (Set.subset_univ _) L.target (GammaChainDefinable.target B L.special.chain L.graph) hKF
  let η := ω.comp (gammaPreparedRVLabelMap U h L.special L.graph hKF)
  let π := ω.comp (gammaIndexedOriginalLabelMap BP G P (Section5.nativeRVGroundDomain U) hG)
  have E := gammaSpecialFamilyMeasuredHom (hc := hc) L F G hSource hRows BP P hKF η π (fun u => by
    let v := (gammaSpecialFamilyRVBijection (hc := hc) L F G hSource hRows BP P hKF).map u
    have hlabel : gammaPreparedRVLabelMap U h L.special L.graph hKF u =
        gammaIndexedOriginalLabelMap BP G P (Section5.nativeRVGroundDomain U) hG v := by
      apply Subtype.ext
      exact (gammaFamilyKeyCode_old L.projection (gammaChainOldLabelIndex L.special.chain) u.val).symm
    exact congrArg (fun x : Section5.nativeRVGroundDomain (hc := hc) U => gammaGroundFormValue ω x) hlabel)
  exact hClass.trans (gammaNativeAdditiveValue_hom χ K (gammaUniversalObject P.toGamma) η π E)

end DiamondIntegral.Section3
