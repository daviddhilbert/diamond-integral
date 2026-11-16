import «section 6».SelectedRepairedProgramContexts
import «section 6».TemplateComponentFamilies
import «section 6».NamedCoefficientDominance

/-! Assemble one actual global permitted component from a uniform
local program family. The same parameter update applies to the entire
remaining program, and one original-base coefficient dominates all old
coefficients while retaining every protected restriction. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n r s q t k : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]
variable {B : DefSet (rawMixedSpace (M := M) 1 r) S}

structure CentripetalFusionRepair
    (η : Map B (DefSet.univ (rawVFSpace (M := M) 1) S))
    (T : CentripetalProgramTemplate (M := M) S 1 n s t)
    (K : FocusComponentParameterTemplate (M := M) S 1 n s)
    (A : MixedSetParameterTemplate (M := M) S 1 n s)
    (P : Fin k → MixedSetParameterTemplate (M := M) S 1 n s)
    (C : DefSet (rawMixedSpace (M := M) (n+1) q) S) (π : Fin r → Fin q) (σ : Fin s → Fin q) where
  parameter : Map B (DefSet.univ (rawVFSpace (M := M) 1) S)
  family : UniformProgramFamily parameter T A P
  context : SelectedProgramContext parameter A P C π σ
  protectedEq : ∀ i,rvLabelPullback C (Fin.addCases π σ) (unaryIndexedMixedFamily η (P i))=
    rvLabelPullback C (Fin.addCases π σ) (unaryIndexedMixedFamily parameter (P i))
  admissible : ∀ b : B,unaryFamilyParameter parameter b ∈ K.good A P
  fibreComponents : TemplateComponentFamily (G := G) parameter K A P admissible
  component : CentripetalData (G := G) C
  coordinate : component.coordinate=K.coordinate.succ
  active : ∀ p : C,p.val.2 ∈ component.activeTags.carrier ↔
    p.val.2 ∘ σ ∈ (fibreComponents.component (context.baseMap p)).activeTags.carrier
  focus : ∀ p : C,component.extendedFocus p.val=
    (fibreComponents.component (context.baseMap p)).extendedFocus (Fin.tail p.val.1,p.val.2 ∘ σ)
  coefficient : ∀ b : B,vfValue (fibreComponents.component b).coefficient ≤ vfValue component.coefficient
  restrictions : ∀ i,∃ E : CentripetalData (G := G)
    (rvLabelPullback C (Fin.addCases π σ) (unaryIndexedMixedFamily parameter (P i))),
      ApertureRestrictionData component E

theorem exists_centripetal_fusion_repair
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    (linear : GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (V : Set M) (hsmall : Cardinal.mk S < κ)
    (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M))
    (hV : ∀ x ∈ V,iVF x) (hVS : V ⊆ S) (hSV : S ⊆ algebraicClosureSet V)
    (hnt : ∃ x : vfAlgebraicClosureField V,x ≠ 0 ∧ Valued.v x.val ≠ 1)
    {η : Map B (DefSet.univ (rawVFSpace (M := M) 1) S)}
    {T : CentripetalProgramTemplate (M := M) S 1 n s t}
    {K : FocusComponentParameterTemplate (M := M) S 1 n s}
    {A : MixedSetParameterTemplate (M := M) S 1 n s}
    {P : Fin k → MixedSetParameterTemplate (M := M) S 1 n s}
    {C : DefSet (rawMixedSpace (M := M) (n+1) q) S} {π : Fin r → Fin q} {σ : Fin s → Fin q}
    (hB : ProperInvariant S B.carrier) (hBRP : IsRVPullback B.carrier)
    (hBTag : ∀ p ∈ B.carrier,∀ z ∈ B.carrier,p.2=z.2 → tupleRV M p.1=tupleRV M z.1)
    (U : UniformProgramFamily η T A P) (X : SelectedProgramContext η A P C π σ)
    (hGood : ∀ b : B,unaryFamilyParameter η b ∈ K.good A P)
    (hActiveMem : (⟨n+s,leadingRVImageTemplate (focusActiveParameterTemplate A K.active)⟩ : RVDataTemplate S 1)
      ∈ T.rvTrace A P)
    (hCoeffMem : (⟨1,coefficientRVDataTemplate K.coefficient⟩ : RVDataTemplate S 1) ∈ T.rvTrace A P) :
    Nonempty (CentripetalFusionRepair (G := G) η T K A P C π σ) := by
  let hTag := U.component_joint_tagged K hGood hBTag
  let Y := X.jointFrame hTag
  have hL := Y.coveredBase_properInvariant h00 hc hκ hs hv X.pullback
  let hActiveRows := U.rows _ hActiveMem
  let F := selectedIndexedFocusGraph (G := G) hv K Y X.pullback hBRP hBTag hGood U.pullback
    U.initial_rows hActiveRows hL
  obtain ⟨R⟩ := exists_selected_indexed_focus_repair h00 hc linear hκ hs hv V hsmall hΓ hV hVS hSV hnt
    Y X.pullback hB X.piecesProper F
  let η' := R.freezing.unaryParameter R.baseProduct η
  let U' := U.freeze R.freezing R.baseProduct
  let X' := X.afterFocusRepair hTag R
  have hGood' (b : B) : unaryFamilyParameter η' b ∈ K.good A P :=
    hGood (R.freezing.unaryBaseFreeze R.baseProduct b)
  let L := templateComponentFamily (G := G) hc hv η' K A P hGood' U'.geometry
  let f := unaryCoefficientMap K.coefficient η' (fun b => (hGood' b).1.1.2)
  have hBound (b : B) : vfValue ((f b).val 0) ≤ U'.radius.val :=
    (unaryCoefficientMap_bound K.coefficient η' (fun b => (hGood' b).1.1.2) U'.radius
      (U'.bound _ hCoeffMem) b).2
  obtain ⟨c,hc0,hcDef,hDom,hOldDom⟩ := R.component.exists_named_coefficient_dominating
    h00 hc hv V hV hVS hSV hnt U'.radius U'.named f hBound
  let D := R.refinedSelectedComponent Y c hc0 hcDef hDom
  have hPieces (i : Fin k) : rvLabelPullback C (Fin.addCases π σ) (unaryIndexedMixedFamily η (P i))=
      rvLabelPullback C (Fin.addCases π σ) (unaryIndexedMixedFamily η' (P i)) := R.selected_pieces Y i
  refine ⟨{
    parameter := η'
    family := U'
    context := X'
    protectedEq := hPieces
    admissible := hGood'
    fibreComponents := L
    component := D
    coordinate := ?_
    active := ?_
    focus := ?_
    coefficient := ?_
    restrictions := ?_ }⟩
  · change R.component.coordinate=K.coordinate.succ
    exact R.coordinate
  · intro p
    let z : Y.coveredBase := Y.coveredFrame.oldPoint ⟨p.val,p.property⟩
    let b := X'.baseMap p
    have hb : unaryFamilyBasePoint z.val=b.val := by
      change unaryFamilyBasePoint (selectedJointPoint π σ p.val)=(X'.baseMap p).val
      rw [selectedJointPoint_base,X'.baseMap_value]
    have h := selectedIndexedFocusGraph_repaired_active_iff hv K Y X.pullback hBRP hBTag hGood
      U.pullback U.initial_rows hActiveRows hL R z.val z.property b hb
    have hTags : z.val.2 ∘ Fin.natAdd r=p.val.2 ∘ σ := selectedJointPoint_local π σ p.val
    rw [hTags] at h
    change z.val.2 ∈ R.component.activeTags.carrier ↔ p.val.2 ∘ σ ∈ (L.component b).activeTags.carrier
    rw [L.active b]
    exact h
  · intro p
    let z : Y.coveredBase := Y.coveredFrame.oldPoint ⟨p.val,p.property⟩
    let b := X'.baseMap p
    have hb : unaryFamilyBasePoint z.val=b.val := by
      change unaryFamilyBasePoint (selectedJointPoint π σ p.val)=(X'.baseMap p).val
      rw [selectedJointPoint_base,X'.baseMap_value]
    have h := selectedIndexedFocusGraph_local_focus hv K Y X.pullback hBRP hBTag hGood
      U.pullback U.initial_rows hActiveRows hL R z.val z.property b hb (L.component b)
      (hGood' b).1.1.1 (L.active b) (L.focus b)
    have hTags : z.val.2 ∘ Fin.natAdd r=p.val.2 ∘ σ := selectedJointPoint_local π σ p.val
    rw [hTags] at h
    exact (R.refinedSelectedComponent_focus Y c hc0 hcDef hDom ⟨p.val,p.property⟩).trans h
  · intro b
    change vfValue (L.component b).coefficient ≤ vfValue c
    rw [← L.coefficient_map b]
    exact hOldDom b
  · intro i
    rw [← hPieces i]
    exact R.refinedSelectedComponent_restrictions Y h00 hc hκ hs hv c hc0 hcDef hDom i

end DiamondIntegral.Section6
