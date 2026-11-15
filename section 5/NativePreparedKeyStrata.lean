import «section 5».NativePreparedFunctionalKeys
import «section 5».NativeRVStratumBijections

/-! The actual prepared full-key bijection preserves base VF residues.
It therefore identifies every base zero stratum with the literal RV-family
total over the corresponding original-ground prepared RV subbase. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace DiamondIntegral.Section5
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section3.GammaParameters
open IntegrationInACVF.Section6
open DiamondIntegral.Section3 DiamondIntegral.Section4 Section3RVCodeBridge
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {p k l q a : ℕ}

section Graph
variable (Y : GammaGroundDefSet hc B (rawMixedSpace (M := M) (p+k) (l+(q+a))))
variable (X : GammaGroundDefSet hc B (rawRVSpace (M := M) ((p+l)+q)))
variable (F : GammaFiniteRVSchema B ((p+l)+q) a k (fun _ => .rv))
variable (hv : ∀ z ∈ rawDomain X,nativeFiniteRVSchemaValid F z)
variable (hmem : ∀ u : (nativeMixedFullKeyMap Y).image,
  u.val ∘ preparedRVTotalIndices p k l q a ∈ (originalRVTotalFamily X (finiteRVSchemaDomain F)).carrier)
variable (hgraph : ∀ u : (nativeMixedFullKeyMap Y).image,
  Fin.append (rvValues (u.val ∘ preparedRVTotalIndices p k l q a))
    (rvValues (u.val ∘ preparedRVFibreLabelIndices p k l q a)) ∈ F.volume)
variable (honto : ∀ w : originalRVTotalFamily X (finiteRVSchemaDomain F),
  ∃ u : (nativeMixedFullKeyMap Y).image,u.val ∘ preparedRVTotalIndices p k l q a = w.val)

def nativePreparedRVKeyStratumBijection (I : Finset (Fin p)) :
    GammaGroundBijection
      (nativeRVZeroPatternBase (nativeMixedFullKeyMap Y).image (Fin.castAdd (l+(q+a)) ∘ Fin.castAdd k) I)
      (originalRVTotalFamily (nativeRVZeroPatternBase X (Fin.castAdd q ∘ Fin.castAdd l) I) (finiteRVSchemaDomain F)) := by
  let e := nativePreparedRVKeyBijection Y X F hv hmem hgraph honto
  have hcoord : ∀ u : (nativeMixedFullKeyMap Y).image,
      (e.map u).val ∘ (Fin.castAdd a ∘ (Fin.castAdd q ∘ Fin.castAdd l)) =
        u.val ∘ (Fin.castAdd (l+(q+a)) ∘ Fin.castAdd k) := by
    intro u
    funext i
    change u.val (preparedRVTotalIndices p k l q a (Fin.castAdd a (Fin.castAdd q (Fin.castAdd l i)))) = _
    simp only [preparedRVTotalIndices,Function.comp_apply,Fin.append_left]
  exact (GammaGroundBijection.ofCarrierEq
    (nativeRVTotal_zeroPattern_carrier X (finiteRVSchemaDomain F) (Fin.castAdd q ∘ Fin.castAdd l) I)).comp
      (nativeRVZeroPatternBijection e _ _ hcoord I)

include hv hmem hgraph honto in
theorem nativePreparedRVKeyStratum_value
    (h00 : M ⊨ Axioms.ACVF00) (linear : Section2.GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
    (hΓ : Section2.NontrivialDefinableGamma B) (kind : EulerKind) (I : Finset (Fin p)) :
    nativeRVSetValue h00 linear hκ hs hc B hr hγ hΓ kind
        (nativeRVZeroPatternBase (nativeMixedFullKeyMap Y).image (Fin.castAdd (l+(q+a)) ∘ Fin.castAdd k) I) =
      nativeRVSetValue h00 linear hκ hs hc B hr hγ hΓ kind
        (originalRVTotalFamily (nativeRVZeroPatternBase X (Fin.castAdd q ∘ Fin.castAdd l) I) (finiteRVSchemaDomain F)) :=
  nativeRVSetValue_bijection h00 linear hκ hs hc B hr hγ hΓ kind _ _
    (nativePreparedRVKeyStratumBijection Y X F hv hmem hgraph honto I)
end Graph

end DiamondIntegral.Section5
