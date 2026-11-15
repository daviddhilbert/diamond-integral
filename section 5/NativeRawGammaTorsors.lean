import «section 5».NativeRawGammaFubini
import «section 4».GammaPointFamilies

/-! Full varying value torsors over arbitrary raw RV bases, including
zeros, have exactly one residue-torus factor per Gamma output coordinate. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace DiamondIntegral.Section5
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section3.GammaParameters
open DiamondIntegral.Section3 DiamondIntegral.Section4
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {p n : ℕ}

def rawGammaFunctionFamily
    {X : GammaGroundDefSet hc B (rawRVSpace (M := M) p)}
    (f : GammaGroundMap X (GammaGroundDefSet.univ hc B ((volumeGammaSpace hc).power (Fin n)))) :
    GammaGroundDefSet hc B ((rawRVSpace (M := M) p).prod ((volumeGammaSpace hc).power (Fin n))) :=
  ⟨{z | ∃ x : X, x.val = z.1 ∧ (f x).val = z.2},f.graph_definable⟩

theorem rawGammaFunctionFamily_euler
    (h00 : M ⊨ Axioms.ACVF00) {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ) (kind : EulerKind)
    {X : GammaGroundDefSet hc B (rawRVSpace (M := M) p)}
    (f : GammaGroundMap X (GammaGroundDefSet.univ hc B ((volumeGammaSpace hc).power (Fin n)))) (x : X) :
    rawRVGammaFibreEulerValue h00 hκ hs hr hγ (rawGammaFunctionFamily f) x.val kind = 1 := by
  unfold rawRVGammaFibreEulerValue
  apply GammaPointFamilies.integrateAll_singleton h00 hκ hs
    ⟨B.real ∪ Set.range (rvValues x.val),B.gamma⟩ _ _ kind n _ (f x).val 1
  intro γ
  have hm : (x.val,γ) ∈ (rawGammaFunctionFamily f).carrier ↔ γ = (f x).val := by
    constructor
    · rintro ⟨y,hy,hf⟩
      have he : y = x := Subtype.ext hy
      exact hf.symm.trans (congrArg (fun a : X => (f a).val) he)
    · intro he
      exact ⟨x,rfl,he.symm⟩
  change (if (x.val,γ) ∈ (rawGammaFunctionFamily f).carrier then (1 : ℤ) else 0) = _
  rw [hm]
  by_cases he : γ = (f x).val <;> simp only [he,ite_true,ite_false]

theorem native_raw_gamma_tuple_torsor_fubini
    (h00 : M ⊨ Axioms.ACVF00) (linear : Section2.GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
    (hΓ : Section2.NontrivialDefinableGamma B) (kind : EulerKind)
    (X : GammaGroundDefSet hc B (rawRVSpace (M := M) p))
    (f : GammaGroundMap X (GammaGroundDefSet.univ hc B ((volumeGammaSpace hc).power (Fin n)))) :
    nativeUnitRVSetValue h00 linear hκ hs hc B hr hγ hΓ kind (rawRVGammaLift h00 X (rawGammaFunctionFamily f)) =
      nativeTorusClass B ^ n * nativeRVSetValue h00 linear hκ hs hc B hr hγ hΓ kind X := by
  have he := native_raw_relative_gamma_fubini h00 linear hκ hs hr hγ hΓ kind X (rawGammaFunctionFamily f)
  have hw := nativeRawWeightedValue_partition h00 linear hκ hs hr hγ hΓ kind X
    (fun x => rawRVGammaFibreEulerValue h00 hκ hs hr hγ (rawGammaFunctionFamily f) x kind)
    (raw_rv_gamma_fibre_euler_constructible h00 hκ hs hr hγ X (rawGammaFunctionFamily f) kind).1
    (raw_rv_gamma_fibre_euler_constructible h00 hκ hs hr hγ X (rawGammaFunctionFamily f) kind).2
    (fun _ : Unit => X) (fun _ : Unit => (1 : ℤ)) (fun _ => Set.Subset.rfl)
    (fun i j h => (h (Subsingleton.elim i j)).elim) (fun _ => ⟨fun h => ⟨(),h⟩,fun ⟨_,h⟩ => h⟩)
    (fun _ x => rawGammaFunctionFamily_euler h00 hκ hs hr hγ kind f x)
  have hv : nativeRawWeightedValue h00 linear hκ hs hr hγ hΓ kind X
      (fun x => rawRVGammaFibreEulerValue h00 hκ hs hr hγ (rawGammaFunctionFamily f) x kind)
      (raw_rv_gamma_fibre_euler_constructible h00 hκ hs hr hγ X (rawGammaFunctionFamily f) kind).1
      (raw_rv_gamma_fibre_euler_constructible h00 hκ hs hr hγ X (rawGammaFunctionFamily f) kind).2 =
      nativeRVSetValue h00 linear hκ hs hc B hr hγ hΓ kind X := by
    simpa only [Finset.univ_unique,Finset.sum_singleton,Int.cast_one,one_mul] using hw
  exact he.trans (congrArg (fun w => nativeTorusClass B ^ n * w) hv)

end DiamondIntegral.Section5
