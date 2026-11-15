import «section 5».NativePreparedFunctionalKeys
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
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
variable (hv : ∀ z ∈ rawDomain X,F.valid z)
variable (hmem : ∀ u : (nativeMixedFullKeyMap Y).image,
  u.val ∘ preparedRVTotalIndices p k l q a ∈ (originalRVTotalFamily X (finiteRVSchemaDomain F)).carrier)
variable (hgraph : ∀ u : (nativeMixedFullKeyMap Y).image,
  Fin.append (rvValues (u.val ∘ preparedRVTotalIndices p k l q a))
    (rvValues (u.val ∘ preparedRVFibreLabelIndices p k l q a)) ∈ F.volume)

include hv hgraph in
theorem nativePreparedRVTotalMap_injective_weak : Function.Injective (nativePreparedRVTotalMap Y X F hmem) := by
  intro u v heq
  have he : u.val ∘ preparedRVTotalIndices p k l q a = v.val ∘ preparedRVTotalIndices p k l q a :=
    congrArg Subtype.val heq
  have hτ := (originalRVTotalFamily_mem X (finiteRVSchemaDomain F)
    (u.val ∘ preparedRVTotalIndices p k l q a)).mp (hmem u)
  let t : Fin (((p+l)+q)+a) → M := rvValues (u.val ∘ preparedRVTotalIndices p k l q a)
  have hX : t ∘ Fin.castAdd a ∈ rawDomain X :=
    ⟨(u.val ∘ preparedRVTotalIndices p k l q a) ∘ Fin.castAdd a,hτ.1,rfl⟩
  have hpack : Fin.append (t ∘ Fin.castAdd a) (t ∘ Fin.natAdd ((p+l)+q)) = t :=
    Fin.append_castAdd_natAdd (f := t)
  have hD : Fin.append (t ∘ Fin.castAdd a) (t ∘ Fin.natAdd ((p+l)+q)) ∈ F.domain :=
    hpack.symm ▸ hτ.2
  obtain ⟨w,hw,hu⟩ := (hv _ hX).2.1 _ hD
  have hgU : Fin.append (Fin.append (t ∘ Fin.castAdd a) (t ∘ Fin.natAdd ((p+l)+q)))
      (rvValues (u.val ∘ preparedRVFibreLabelIndices p k l q a)) ∈ F.volume :=
    hpack.symm ▸ hgraph u
  have hgV : Fin.append (Fin.append (t ∘ Fin.castAdd a) (t ∘ Fin.natAdd ((p+l)+q)))
      (rvValues (v.val ∘ preparedRVFibreLabelIndices p k l q a)) ∈ F.volume := by
    have ht : t = rvValues (v.val ∘ preparedRVTotalIndices p k l q a) := congrArg rvValues he
    have hg : Fin.append t (rvValues (v.val ∘ preparedRVFibreLabelIndices p k l q a)) ∈ F.volume :=
      ht.symm ▸ hgraph v
    exact hpack.symm ▸ hg
  have hl : u.val ∘ preparedRVFibreLabelIndices p k l q a = v.val ∘ preparedRVFibreLabelIndices p k l q a :=
    rvValues_injective ((hu _ hgU).trans (hu _ hgV).symm)
  exact Subtype.ext (preparedRVKey_ext u.val v.val he hl)

def nativePreparedRVKeyBijection_weak
    (honto : ∀ w : originalRVTotalFamily X (finiteRVSchemaDomain F),
      ∃ u : (nativeMixedFullKeyMap Y).image,u.val ∘ preparedRVTotalIndices p k l q a = w.val) :
    GammaGroundBijection (nativeMixedFullKeyMap Y).image (originalRVTotalFamily X (finiteRVSchemaDomain F)) :=
  ⟨nativePreparedRVTotalMap Y X F hmem,⟨nativePreparedRVTotalMap_injective_weak Y X F hv hmem hgraph,
    fun w => by obtain ⟨u,hu⟩ := honto w; exact ⟨u,Subtype.ext hu⟩⟩⟩

include hv hgraph hmem in
theorem nativePreparedRVKey_value_weak
    (h00 : M ⊨ Axioms.ACVF00) (linear : Section2.GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
    (hΓ : Section2.NontrivialDefinableGamma B) (kind : EulerKind)
    (honto : ∀ w : originalRVTotalFamily X (finiteRVSchemaDomain F),
      ∃ u : (nativeMixedFullKeyMap Y).image,u.val ∘ preparedRVTotalIndices p k l q a = w.val) :
    nativeRVSetValue h00 linear hκ hs hc B hr hγ hΓ kind (nativeMixedFullKeyMap Y).image =
      nativeRVSetValue h00 linear hκ hs hc B hr hγ hΓ kind (originalRVTotalFamily X (finiteRVSchemaDomain F)) :=
  nativeRVSetValue_bijection h00 linear hκ hs hc B hr hγ hΓ kind _ _
    (nativePreparedRVKeyBijection_weak Y X F hv hmem hgraph honto)
end Graph

end DiamondIntegral.Section5
