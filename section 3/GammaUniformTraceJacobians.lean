import «section 3».GammaUniformTraceMeasuredBijections
import «section 3».GammaNativeSpecialJacobian

/-! Uniform traces have Jacobian one at original-base independent
points even when the source has infinite RV fibres. Finite RV fibres
are needed for the measured category, rather than this chart statement. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3500000
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.Section3.GammaParameters SpecialTransformations.Section5
open IntegrationInACVF.Section5 IntegrationInACVF.Section6
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] [CharZero (Section2.VF M)]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)}
variable {S : Set M} {n a b : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (Section2.VF M) G]
variable {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ) (hr : Cardinal.mk B.real < κ)
variable (hv : ∀ x y : Section2.VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)

include hκ hs hr hv in
theorem gammaGround_jacobian_one_comp
    {r s t : ℕ} {A : GammaGroundDefSet hc B (rawMixedSpace (M := M) n r)}
    {D : GammaGroundDefSet hc B (rawMixedSpace (M := M) n s)}
    {E : GammaGroundDefSet hc B (rawMixedSpace (M := M) n t)}
    (f : GammaGroundBijection A D) (g : GammaGroundBijection D E)
    (hf : ∀ p, AlgebraicIndependent (vfParameterField B.real) p.val.1 → HasMixedVFJacobianAt f.map p 1)
    (hg : ∀ p, AlgebraicIndependent (vfParameterField B.real) p.val.1 → HasMixedVFJacobianAt g.map p 1)
    (p : A) (hp : AlgebraicIndependent (vfParameterField B.real) p.val.1) :
    HasMixedVFJacobianAt (g.comp f).map p 1 := by
  have hff := GammaGroundMap.finiteFibres_of_injective f.bijective.injective
  obtain ⟨J,K,hJ,hK,hC⟩ := gammaGround_jacobian_comp_of_independent hκ hs hr hv f.map g.map hff p hp
  have heJ := hJ.unique (hf p hp)
  have heK := hK.unique (hg (f.map p) (gammaGround_independent_map f.map hff hκ hr p hp))
  rw [heJ,heK,mul_one] at hC
  exact hC

include hκ hs hr hv in
theorem gammaUniformTrace_jacobian_one
    {A : DefSet (M := M) S n a} {D : DefSet (M := M) S n b}
    (T : UniformRelativeTrace S n A D) (hT : GammaUniformTrace (G := B) T)
    (p : Section5.nativeGammaPointDomain (hc := hc) (carrier A) hT.source)
    (hp : AlgebraicIndependent (vfParameterField B.real) p.val.1) :
    HasMixedVFJacobianAt
      (Section5.nativeGammaPointBijection hT.source
        ((gammaUniformTraceIso T hT).target_definable (gammaLogicInput B)) (gammaUniformTraceIso T hT)).map p 1 := by
  let hA := hT.source
  let hD := (gammaUniformTraceIso T hT).target_definable (gammaLogicInput B)
  let P := T.inputPresentation
  have hP := T.gamma_inputPresentation hT
  let ρ : Fin a → Fin (a+T.flagCount) := Fin.castAdd T.flagCount
  let hPA : ∀ q ∈ carrier P, fullRVProjection ρ q ∈ carrier A := fun q hq => (T.inputProjection ⟨q,hq⟩).property
  let eIP : GammaIso B (carrier P) (carrier A) :=
    ⟨Equiv.ofBijective T.inputProjection T.inputProjection_bijective,gamma_fullRVProjectionInto ρ P A hPA hP⟩
  let IP := Section5.nativeGammaPointBijection (hc := hc) hP hA eIP
  obtain ⟨l,K,σ,W,hWG,hKD,hOut,hSquare⟩ := T.gamma_special_presentation hT
  let hK := GammaChainDefinable.target B W.chain hWG
  let WΓ := gammaNativeSpecialBijection (hc := hc) W hWG
  let out := fullRVProjectionInto σ K D hKD
  let eOP : GammaIso B (carrier K) (carrier D) :=
    ⟨Equiv.ofBijective out hOut,gamma_fullRVProjectionInto σ K D hKD hK⟩
  let OP := Section5.nativeGammaPointBijection (hc := hc) hK hD eOP
  let F := OP.comp (WΓ.comp IP.symm)
  have hIP : ∀ q, AlgebraicIndependent (vfParameterField B.real) q.val.1 → HasMixedVFJacobianAt IP.symm.map q 1 := by
    intro q hq
    apply gammaVFFixed_jacobian_one hκ hs hr hv IP.symm.map ?_ q hq
    intro z
    have hz := IP.map.apply_inverse IP.bijective z
    have he := Section5.nativeGammaPointBijection_apply hP hA eIP (IP.symm.map z)
    have hVF := congrArg Prod.fst he
    exact hVF.symm.trans (congrArg (fun u => u.val.1) hz)
  have hW : ∀ q, AlgebraicIndependent (vfParameterField B.real) q.val.1 → HasMixedVFJacobianAt WΓ.map q 1 :=
    gammaNativeSpecial_jacobian_one hκ hs hr hv W hWG
  have hOP : ∀ q, AlgebraicIndependent (vfParameterField B.real) q.val.1 → HasMixedVFJacobianAt OP.map q 1 := by
    intro q hq
    apply gammaVFFixed_jacobian_one hκ hs hr hv OP.map ?_ q hq
    intro z
    rw [Section5.nativeGammaPointBijection_apply]
    rfl
  have hWF := gammaGround_jacobian_one_comp hκ hs hr hv IP.symm WΓ hIP hW
  have hJF := gammaGround_jacobian_one_comp hκ hs hr hv (WΓ.comp IP.symm) OP hWF hOP
  have hValue (q : Section5.nativeGammaPointDomain (hc := hc) (carrier A) hA) :
      (F.map q).val = (T.toMap ⟨q.val,q.property⟩).val := by
    let u := IP.symm.map q
    have hInput : T.inputProjection ⟨u.val,u.property⟩ = ⟨q.val,q.property⟩ := by
      apply Subtype.ext
      have hInv := congrArg Subtype.val (IP.map.apply_inverse IP.bijective q)
      rw [Section5.nativeGammaPointBijection_apply] at hInv
      exact hInv
    have hOutput : (OP.map (WΓ.map u)).val = fullRVProjection σ (WΓ.map u).val :=
      Section5.nativeGammaPointBijection_apply hK hD eOP (WΓ.map u)
    exact hOutput.trans ((congrArg (fullRVProjection σ) (gammaNativeSpecialBijection_apply W hWG u)).trans
      ((hSquare ⟨u.val,u.property⟩).trans (congrArg (fun v => (T.toMap v).val) hInput)))
  have hMap : (Section5.nativeGammaPointBijection hA hD (gammaUniformTraceIso T hT)).map = F.map := by
    apply GammaGroundMap.ext
    intro q
    apply Subtype.ext
    exact (Section5.nativeGammaPointBijection_apply hA hD (gammaUniformTraceIso T hT) q).trans (hValue q).symm
  rw [hMap]
  exact hJF p hp

end DiamondIntegral.Section3
