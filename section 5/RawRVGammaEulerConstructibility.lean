import «section 5».RawRVGammaFibreEuler

/-! Actual Gamma fibre Euler values have finite range and original-ground
level sets on all RV bases, including tuples with zero coordinates. -/
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

theorem rawRVGammaFibreEulerValue_forward_code
    (h00 : M ⊨ Axioms.ACVF00) {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
    (X : GammaGroundDefSet hc B (rawRVSpace (M := M) p))
    (T : GammaGroundDefSet hc B ((rawRVSpace (M := M) p).prod ((volumeGammaSpace hc).power (Fin n))))
    (x : X) (kind : EulerKind) :
    rvGammaFibreEulerValue hc h00 hκ hs hr hγ (rawRVGammaFamilyCode h00 X T)
      ((gammaGroundRVNonzeroTupleCodeBijection h00 X).map x).val kind =
      rawRVGammaFibreEulerValue h00 hκ hs hr hγ T x.val kind := by
  have h := rawRVGammaFibreEulerValue_code h00 hκ hs hr hγ X T
    ((gammaGroundRVNonzeroTupleCodeBijection h00 X).map x) kind
  have he : (gammaGroundRVNonzeroTupleCodeBijection h00 X).symm.map
      ((gammaGroundRVNonzeroTupleCodeBijection h00 X).map x) = x := GammaGroundMap.inverse_apply _ _ x
  exact h.trans (congrArg (fun a : X => rawRVGammaFibreEulerValue h00 hκ hs hr hγ T a.val kind) he)

theorem raw_rv_gamma_fibre_euler_constructible
    (h00 : M ⊨ Axioms.ACVF00) {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
    (X : GammaGroundDefSet hc B (rawRVSpace (M := M) p))
    (T : GammaGroundDefSet hc B ((rawRVSpace (M := M) p).prod ((volumeGammaSpace hc).power (Fin n))))
    (kind : EulerKind) :
    (Set.range (fun x : X => rawRVGammaFibreEulerValue h00 hκ hs hr hγ T x.val kind)).Finite ∧
      ∀ m : ℤ, GammaGroundDefinable hc B (rawRVSpace (M := M) p)
        {x | x ∈ X.carrier ∧ rawRVGammaFibreEulerValue h00 hκ hs hr hγ T x kind = m} := by
  let e := gammaGroundRVNonzeroTupleCodeBijection h00 X
  let c := fun q => rvGammaFibreEulerValue hc h00 hκ hs hr hγ (rawRVGammaFamilyCode h00 X T) q kind
  have hvalue (x : X) : c (e.map x).val = rawRVGammaFibreEulerValue h00 hκ hs hr hγ T x.val kind :=
    rawRVGammaFibreEulerValue_forward_code h00 hκ hs hr hγ X T x kind
  obtain ⟨hfinite,hlevels⟩ := rv_gamma_fibre_euler_constructible hc h00 hκ hs hr hγ
    (rawRVGammaBaseCode X) (rawRVGammaFamilyCode h00 X T) kind
  constructor
  · apply hfinite.subset
    rintro m ⟨x,rfl⟩
    exact ⟨e.map x,hvalue x⟩
  · intro m
    let L : GammaGroundDefSet hc B (rawRVUnitSpace (M := M) (p*2)) :=
      ⟨{q | q ∈ (rawRVGammaBaseCode X).carrier ∧ c q = m},hlevels m⟩
    apply (e.inverseImage L).definable.congr
    intro x
    constructor
    · rintro ⟨a,ha,hm⟩
      refine ⟨ha ▸ a.property,?_⟩
      have he := (hvalue a).symm.trans hm.2
      exact ha ▸ he
    · rintro ⟨hx,hm⟩
      exact ⟨⟨x,hx⟩,rfl,(e.map ⟨x,hx⟩).property,(hvalue ⟨x,hx⟩).trans hm⟩

end DiamondIntegral.Section5
