import «section 3».GammaRelativeGenericHeadFormulaWitnesses
import «section 3».GammaSelectedMeasuredHeads

/-! A full relatively unary measured map starts the selected induction
with no initially selected RV coordinate. After the first specified
heads, the new head labels give its required positive selected degree. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5500000
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5 SpecialTransformations.Section9
open IntegrationInACVF.Section5 IntegrationInACVF.Section6 IntegrationInACVF.Section7
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {n : ℕ}

theorem GammaSelectedRetainedData.finite_zero_select
    (U : GammaSelectedRetainedData hc B n 0) (x : Fin n → VF (M := M)) :
    {r | (x,r) ∈ carrier U.set}.Finite := by
  apply (U.finite x Fin.elim0).subset
  intro r hr
  exact ⟨hr,Subsingleton.elim _ _⟩

def GammaSelectedRetainedData.zeroSelectedMeasured (U : GammaSelectedRetainedData hc B n 0) :=
  gammaPointMeasuredData U.set U.gamma U.finite_zero_select U.pointForm

theorem GammaSelectedMeasuredHead.next_schema_zero {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ) (hr : Cardinal.mk B.real < κ)
    {U : GammaSelectedRetainedData hc B (n+1) 0} (T : GammaSelectedMeasuredHead U) (N : ℕ) :
    (T.next hκ hs hr).schema N =
      gammaMeasuredBoundedSelectedSchema T.head.contractedSet (gamma_headImage T.head.target T.targetGamma)
        (headVolumeIndex T.head (Fin.elim0 : Fin 0 → Fin U.arity))
        (gammaHeadContractedForm T.head T.targetGamma U.labels U.labels_mem U.form) N := by
  change gammaMeasuredBoundedSelectedSchema _ _ _ (T.next hκ hs hr).pointForm N = _
  rw [T.next_pointForm hκ hs hr]
  have he : U.select = Fin.elim0 := Subsingleton.elim _ _
  change gammaMeasuredBoundedSelectedSchema T.head.contractedSet _ (headVolumeIndex T.head U.select)
    (gammaHeadContractedForm T.head T.targetGamma U.labels U.labels_mem U.form) N = _
  rw [he]

variable [CharZero (Section2.VF M)]
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (Section2.VF M) G]

theorem gammaRelative_first_head_related {κ : Cardinal}
    (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    (hr : Cardinal.mk B.real < κ) (hg : Cardinal.mk B.gamma < κ)
    (hv : ∀ x y : Section2.VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (δ : Values.Gamma (M := M)) (hδ : δ ∈ B.gamma) (hδ1 : 1 < δ)
    {U V : GammaSelectedRetainedData hc B (n+1) 0}
    (F : GammaFullMeasuredBijection U.zeroSelectedMeasured V.zeroSelectedMeasured)
    (hi : ∀ p, ∀ j, j ≠ 0 → (F.map.map p).val.1 j = p.val.1 j)
    (T : GammaSelectedMeasuredHead U) (E : GammaSelectedMeasuredHead V) :
    GammaGenericSelectedRelated (n := n) (k := 0) (T.next hκ.le hs hr) (E.next hκ.le hs hr) := by
  let f := gammaGroundPointMap (A := U.set) (C := V.set) U.gamma V.gamma F.map
  have hf : Function.Bijective f := F.map.bijective
  have hΓ : GammaGraphDefinable B (pointMapGraph f) := (gammaGroundPointIso F.map).graph
  have hUnary : UnaryRelative f 0 := hi
  obtain ⟨NT,NE,hNT,hNE,hWitness⟩ := gammaRelativeGenericHead_measured_formula_witnesses
    hκ hs h00 hr hg hv δ hδ hδ1 T.head E.head U.gamma V.gamma T.targetGamma E.targetGamma
    T.mapGamma E.mapGamma T.jacobian E.jacobian U.finite_zero_select V.finite_zero_select
    U.labels V.labels U.labels_mem V.labels_mem U.form V.form F f hf hΓ (fun _ => rfl) hUnary
  refine ⟨NT,NE,?_,?_,?_⟩
  · intro x
    rw [T.next_schema_zero hκ.le hs hr NT]
    exact hNT x
  · intro x
    rw [E.next_schema_zero hκ.le hs hr NE]
    exact hNE x
  · intro x hx
    rw [T.next_schema_zero hκ.le hs hr NT,E.next_schema_zero hκ.le hs hr NE]
    exact hWitness x hx

end DiamondIntegral.Section3
