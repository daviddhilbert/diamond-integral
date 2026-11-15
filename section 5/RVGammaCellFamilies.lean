import «section 5».RVGammaHeadFamilies

/-! An actual relative cylindrical Gamma cell has its shape Euler factor
in the native RV evaluation, with every Gamma coordinate lifted fully. -/
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
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {p : ℕ}

inductive RVGammaCellFamily (X : GammaGroundDefSet hc B (rawRVUnitSpace (M := M) p)) :
    {n : ℕ} → GammaGroundDefSet hc B ((rawRVUnitSpace (M := M) p).prod ((volumeGammaSpace hc).power (Fin n))) →
      CylindricalShape n → Prop where
  | base (T : GammaGroundDefSet hc B ((rawRVUnitSpace (M := M) p).prod ((volumeGammaSpace hc).power (Fin 0))))
      (row : ∀ x γ, (x,γ) ∈ T.carrier ↔ x ∈ X.carrier) : RVGammaCellFamily X T .base
  | step {n : ℕ}
      {S : GammaGroundDefSet hc B ((rawRVUnitSpace (M := M) p).prod ((volumeGammaSpace hc).power (Fin n)))}
      {s : CylindricalShape n} (child : RVGammaCellFamily X S s) (shape : CylinderFibreKind)
      (T : GammaGroundDefSet hc B ((rawRVUnitSpace (M := M) p).prod ((volumeGammaSpace hc).power (Fin (n+1)))))
      (projection : ∀ x γ, (x,γ) ∈ T.carrier → (x,Fin.tail γ) ∈ S.carrier)
      (fibres : ∀ x η, (x,η) ∈ S.carrier →
        shape.Describes (fun δ : Values.Gamma (M := M) => (x,Fin.cons δ η) ∈ T.carrier)) :
      RVGammaCellFamily X T (shape.attach s)

theorem CylinderFibreKind.attach_eulerValue (shape : CylinderFibreKind) {n : ℕ} (s : CylindricalShape n)
    (kind : EulerKind) : (shape.attach s).eulerValue kind = shape.eulerFactor kind * s.eulerValue kind := by
  cases shape <;> simp only [CylinderFibreKind.attach,CylindricalShape.eulerValue,CylinderFibreKind.eulerFactor,one_mul,neg_one_mul]

theorem RVGammaCellFamily.native_value
    (h00 : M ⊨ Axioms.ACVF00) (linear : Section2.GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
    (hΓ : Section2.NontrivialDefinableGamma B) (kind : EulerKind)
    {X : GammaGroundDefSet hc B (rawRVUnitSpace (M := M) p)} {n : ℕ}
    {T : GammaGroundDefSet hc B ((rawRVUnitSpace (M := M) p).prod ((volumeGammaSpace hc).power (Fin n)))}
    {s : CylindricalShape n} (C : RVGammaCellFamily X T s) :
    nativeUnitRVSetValue h00 linear hκ hs hc B hr hγ hΓ kind (rvGammaReverseLift T) =
      (s.eulerValue kind : RESDimensionFreeReduction.Ring B) * nativeTorusClass B ^ n *
        nativeUnitRVSetValue h00 linear hκ hs hc B hr hγ hΓ kind X := by
  induction C with
  | base T hrow =>
    have he : (rvGammaReverseLift T).carrier = X.carrier := by
      ext u
      change (u ∘ Fin.castAdd 0,_) ∈ T.carrier ↔ u ∈ X.carrier
      rw [hrow]
      have hu : u ∘ Fin.castAdd 0 = u := by
        funext j
        apply congrArg u
        apply Fin.ext
        rfl
      rw [hu]
    simpa only [CylindricalShape.eulerValue,Int.cast_one,pow_zero,one_mul] using
      nativeUnitRVSetValue_bijection h00 linear hκ hs hc B hr hγ hΓ kind _ _
        (GammaGroundBijection.ofCarrierEq he)
  | @step n S s child shape T hp hf ih =>
    have hhp : ∀ u δ, (u,δ) ∈ (rvGammaHeadFamily T).carrier → u ∈ (rvGammaReverseLift S).carrier := by
      intro u δ hu
      have ht := (rvGammaHeadFamily_mem T u δ).mp hu
      have hc := hp _ _ ht
      change (u ∘ Fin.castAdd n,rvUnitTupleValues (u ∘ Fin.natAdd p ∘ Fin.rev)) ∈ S.carrier
      simpa only [Fin.tail_cons] using hc
    have hhf : ∀ u : rvGammaReverseLift S,
        shape.Describes (fun δ : Values.Gamma (M := M) => (u.val,δ) ∈ (rvGammaHeadFamily T).carrier) := by
      intro u
      obtain ⟨a,ha,hr⟩ := hf (u.val ∘ Fin.castAdd n)
        (rvUnitTupleValues (u.val ∘ Fin.natAdd p ∘ Fin.rev)) u.property
      exact ⟨a,ha,fun δ => (rvGammaHeadFamily_mem T u.val δ).trans (hr δ)⟩
    have he := native_described_cylinder_fubini h00 linear hκ hs hr hγ hΓ kind
      (rvGammaReverseLift S) shape (rvGammaHeadFamily T) hhp hhf
    have hc := nativeUnitRVSetValue_bijection h00 linear hκ hs hc B hr hγ hΓ kind _ _
      (GammaGroundBijection.ofCarrierEq (rvGammaReverseLift_head T))
    rw [hc,he,ih,CylinderFibreKind.attach_eulerValue,Int.cast_mul,pow_succ]
    ring

end DiamondIntegral.Section5
