import «section 3».GammaPreparedUnaryMeasuredRows
import «section 3».GammaPartialBaseFullMeasured
import «section 3».GammaPreparedIndexedFullMeasured

/-! The prepared unary indexed object represents the actual mixed
selected family by a full Gamma-measured bijection. This is the same
preparation and indexed-lift construction used for RV densities. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section3.GammaParameters SpecialTransformations.Section5
open IntegrationInACVF.Section6 IntegrationInACVF.Section6.FiniteRV IntegrationInACVF.Section7
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] [CharZero (Section2.VF M)]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (Section2.VF M) G]
variable {S : Set M} {k l a : ℕ}

theorem gammaPreparedUnaryIndexed_full_measured
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (h00 : M ⊨ Axioms.ACVF00) (hr : Cardinal.mk B.real < κ)
    (hv : ∀ x y : Section2.VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (F : GammaMeasuredRVSchema hc B 1 a (k+1) (fun _ => .vf))
    (hF : ∀ x : Fin 1 → VF (M := M), F.valid (vfValues x))
    {X : DefSet (M := M) S 1 0} {Z : DefSet (M := M) S 1 l}
    (T : SpecialBijection X Z) (hT : GammaChainDefinable B T.chain) (hZ : IsRVPullback (carrier Z))
    (hAgreement : ∀ c : Z, (GammaVolumeParameterRecode.prepared T hT).VolumeObjectAgreement
      F.toRVTemplate (rawVFParameter (T.inverseMap c).val) (rawPreparedKey c.val))
    (H : DefSet (M := M) Set.univ (1+(k+1)) a) (hH : GammaSetDefinable B (carrier H))
    (hP : ∀ q : Section5.nativeGammaPointDomain (hc := hc) (carrier H) hH,
      ((Section5.nativeMixedCoordinateMap _ (Fin.castAdd (k+1)) (Fin.elim0 : Fin 0 → Fin a)) q).val ∈
        (Section5.nativeGammaPointDomain (hc := hc) (carrier X) (GammaChainDefinable.source B T.chain hT)).carrier)
    (hfin : ∀ x, {r | (x,r) ∈ carrier H}.Finite)
    (Ω : GammaGroundVolumeForm hc B (Section5.nativeGammaPointDomain (carrier H) hH))
    (hSource : ∀ (x : Fin 1 → Section2.VF M) (y : Fin (k+1) → Section2.VF M) (r : Fin a → RV (M := M)),
      (Fin.append x y,r) ∈ carrier H ↔ F.object.rowVolume (vfValues x) r (Section2.tupleRV M y))
    (hDensity : ∀ (p : Section5.nativeGammaPointDomain (hc := hc) (carrier H) hH) (cΓ : (volumeGammaSpace hc).domain),
      (volumeGammaSpace hc).decode cΓ = (Ω p).val → F.rowDensity (vfValues (p.val.1 ∘ Fin.castAdd (k+1))) p.val.2 cΓ)
    (BP : PreparedIndexPresentation B Z)
    (P : (F.recode (GammaParameterRecode.prepared T hT)).object.IndexedPresentation BP) :
    ∃ E : GammaFullMeasuredBijection (gammaPointMeasuredData H hH hfin Ω)
      (gammaNativeMeasuredLift (gammaUniversalObject P.toGamma)
        ((F.recode (GammaParameterRecode.prepared T hT)).indexedForm BP (gammaPreparedUnaryMeasured_valid F T hT hAgreement hF) P)),
      ∀ p, (E.map.map p).val.1 ∘ Fin.natAdd 1 = p.val.1 ∘ Fin.natAdd 1 := by
  let A := Section5.nativeGammaPointDomain (hc := hc) (carrier H) hH
  let TΓ := Section5.nativeSpecialBaseBijection (hc := hc) T hT
  let W := Section5.nativeVFPrepareBaseBijection A TΓ hP
  let Y := (Section5.nativeVFPrepareBaseMap A TΓ hP).image
  let hfinY := Section5.nativeVFPrepareBaseMap_finite hκ hs h00 hr A TΓ hP hfin
  let η := Ω.comp W.symm.map
  let R := F.recode (GammaParameterRecode.prepared T hT)
  let hR := gammaPreparedUnaryMeasured_valid F T hT hAgreement hF
  let hBase := gammaPartialBase_base_mem A TΓ hP
  let hRows := gammaPreparedUnaryMeasured_rows F T hT hAgreement A hP hSource
  let hDens := gammaPreparedUnaryMeasured_density F T hT hAgreement A hP Ω hDensity
  let g := gammaPreparedIndexedFullMeasured hκ hs hr hv Z hZ BP R hR P Y hBase hRows hfinY η hDens
  let f := gammaPartialBaseFullMeasured hκ hs h00 hr T hT H hH hP hfin Ω hv
  refine ⟨f.comp hκ hs hr hv g,?_⟩
  intro p
  have hVF := gammaPreparedIndexedFullMeasured_vf hκ hs hr hv Z hZ BP R hR P Y hBase hRows hfinY η hDens (f.map.map p)
  change (g.map.map (f.map.map p)).val.1 ∘ Fin.natAdd 1 = p.val.1 ∘ Fin.natAdd 1
  rw [hVF]
  change Fin.append _ (p.val.1 ∘ Fin.natAdd 1) ∘ Fin.natAdd 1 = p.val.1 ∘ Fin.natAdd 1
  funext j
  exact Fin.append_right _ _ j

end DiamondIntegral.Section3
