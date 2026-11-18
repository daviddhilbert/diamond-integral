import «section 3».GammaHeadMeasuredFibres
import «section 3».GammaSpecialFullMeasuredBijections
import «section 3».GammaFullMeasuredFixedMaps
import «section 3».GammaGroundFiniteFibreInvariance
import IntegrationSection5.GammaTracePresentation

/-! The native trace compiler factors a Gamma trace through two VF-fixed
label maps and an actual Gamma special chain. Its unit measured map
therefore exists over the original base in every positive degree. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
open IntegrationInACVF.Section5 IntegrationInACVF.Section6
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] [CharZero (Section2.VF M)]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)}
variable {S : Set M} {n a b : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (Section2.VF M) G]

theorem gammaUniformTrace_full_unit_measured
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (h00 : M ⊨ Axioms.ACVF00) (hr : Cardinal.mk B.real < κ)
    (hv : ∀ x y : Section2.VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    {A : DefSet (M := M) S (n+1) a} {D : DefSet (M := M) S (n+1) b}
    (T : UniformRelativeTrace S (n+1) A D) (hT : GammaUniformTrace (G := B) T)
    (hfinA : ∀ x, {r | (x,r) ∈ carrier A}.Finite) :
    let hA := hT.source
    let hD := (gammaUniformTraceIso T hT).target_definable (gammaLogicInput B)
    ∃ hfinD : ∀ x, {r | (x,r) ∈ carrier D}.Finite,
    ∃ F : GammaFullMeasuredBijection
      (gammaPointMeasuredData (hc := hc) A hA hfinA (gammaGroundOneForm _))
      (gammaPointMeasuredData (hc := hc) D hD hfinD (gammaGroundOneForm _)),
      ∀ p, (F.map.map p).val = (T.toMap ⟨p.val,p.property⟩).val := by
  intro hA hD
  let P := T.inputPresentation
  have hP := T.gamma_inputPresentation hT
  let ρ : Fin a → Fin (a+T.flagCount) := Fin.castAdd T.flagCount
  let hPA : ∀ p ∈ carrier P, fullRVProjection ρ p ∈ carrier A :=
    fun p hp => (T.inputProjection ⟨p,hp⟩).property
  let eIP : GammaIso B (carrier P) (carrier A) :=
    ⟨Equiv.ofBijective T.inputProjection T.inputProjection_bijective,
      gamma_fullRVProjectionInto ρ P A hPA hP⟩
  let IP := Section5.nativeGammaPointBijection (hc := hc) hP hA eIP
  have hfinP : ∀ x, {r | (x,r) ∈ carrier P}.Finite :=
    (gammaGroundFiniteRVFibres_iff IP hκ hs h00 hr).mpr hfinA
  let fIP := gammaFullMeasuredFixedVF hκ hs hr hv
    (U := gammaPointMeasuredData P hP hfinP (gammaGroundOneForm _))
    (V := gammaPointMeasuredData A hA hfinA (gammaGroundOneForm _)) IP
    (fun p => by rw [Section5.nativeGammaPointBijection_apply]; rfl) (fun _ => rfl)
  obtain ⟨l,K,σ,W,hWG,hKD,hOut,hSquare⟩ := T.gamma_special_presentation hT
  have hK := GammaChainDefinable.target B W.chain hWG
  let NK := Section5.nativeGammaPointDomain (hc := hc) (carrier K) hK
  let WΓ := gammaNativeSpecialBijection (hc := hc) W hWG
  have hfinK : ∀ x, {r | (x,r) ∈ carrier K}.Finite :=
    (gammaGroundFiniteRVFibres_iff WΓ hκ hs h00 hr).mp hfinP
  let fW := gammaSpecialFullMeasuredBijection (hc := hc) hκ hs hr hv W hWG hfinP (gammaGroundOneForm _)
  let out := fullRVProjectionInto σ K D hKD
  let eOP : GammaIso B (carrier K) (carrier D) :=
    ⟨Equiv.ofBijective out hOut,gamma_fullRVProjectionInto σ K D hKD hK⟩
  let OP := Section5.nativeGammaPointBijection (hc := hc) hK hD eOP
  have hfinD : ∀ x, {r | (x,r) ∈ carrier D}.Finite :=
    (gammaGroundFiniteRVFibres_iff OP hκ hs h00 hr).mp hfinK
  let fOP := gammaFullMeasuredFixedVF hκ hs hr hv
    (U := gammaPointMeasuredData K hK hfinK (gammaGroundOneForm _))
    (V := gammaPointMeasuredData D hD hfinD (gammaGroundOneForm _)) OP
    (fun p => by rw [Section5.nativeGammaPointBijection_apply]; rfl) (fun _ => rfl)
  let F := ((fIP.symm hκ hs hr hv).comp hκ hs hr hv fW).comp hκ hs hr hv fOP
  refine ⟨hfinD,F,?_⟩
  intro q
  let p := IP.symm.map q
  have hInput : T.inputProjection ⟨p.val,p.property⟩ = ⟨q.val,q.property⟩ := by
    apply Subtype.ext
    have hInv := congrArg Subtype.val (IP.map.apply_inverse IP.bijective q)
    rw [Section5.nativeGammaPointBijection_apply] at hInv
    exact hInv
  change (OP.map (WΓ.map p)).val = _
  have hOP : (OP.map (WΓ.map p)).val = fullRVProjection σ (WΓ.map p).val :=
    Section5.nativeGammaPointBijection_apply hK hD eOP (WΓ.map p)
  exact hOP.trans ((congrArg (fullRVProjection σ) (gammaNativeSpecialBijection_apply W hWG p)).trans
    ((hSquare ⟨p.val,p.property⟩).trans (congrArg (fun u => (T.toMap u).val) hInput)))

end DiamondIntegral.Section3
