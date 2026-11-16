import «section 6».FocusComponentTransitionRelations
import «section 6».ComponentFocusExtensionValues

/-! A uniform component transition specializes to the exact complete
graph of the actual permitted map. Both branches, inactive labels and
every original source point are included. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 7000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {p n r : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

theorem focusComponentTransition_at
    (T : FocusComponentParameterTemplate (M := M) S p n r)
    (A : MixedSetParameterTemplate (M := M) S p n r) (a : Fin p → M)
    (hF : a ∈ T.focus.good) (hC : a ∈ T.coefficient.good)
    (D : CentripetalData (G := G) (A.fibre a)) (hj : D.coordinate=T.coordinate)
    (hU : D.activeTags=T.active.fibre a) (hCoeff : D.coefficient=vfScalarTemplateValue T.coefficient a hC)
    (hFocus : ∀ q : focusActive (A.fibre a) (T.active.fibre a),D.extendedFocus q.val=
      T.focus.value a hF q.val.2 q.val.1 0) :
    {z | Sum.elim a z ∈ focusComponentTransition T A}=
      (rawMixedSpace n r).relation (rawMixedSpace n (1+r)) D.map.graph := by
  let P := rawMixedSpace (M := M) n r
  let Q := rawMixedSpace (M := M) n (1+r)
  let f := rvFamilyMap (focusActive (A.fibre a) (T.active.fibre a))
    (T.focus.value a hF) (T.focus.family_graph_definable a hF)
  have hGraph := focusGraphParameterCode_at A T.active T.focus a hF
  have hAcode := (A.fibre_code a).symm
  have hValue (x : Mixed M n r) (hx : x ∈ (A.fibre a).carrier) :
      scalarCodeExtension f (mixedValues x)=(D.extendedFocus x).val :=
    componentTemplateFocusExtension T A a hF D hU hFocus x hx
  ext z
  constructor
  · rintro ⟨hSource,w,hLambda,hCoef,hStep⟩
    obtain ⟨hx,hxA⟩ := (Set.ext_iff.mp hAcode _).mp hSource
    let x := P.decode ⟨z ∘ Sum.inl,hx⟩
    have hX : mixedValues x=z ∘ Sum.inl := mixedValues_decode _
    have hLambdaCode : w ∘ Sum.inl=(fun _ : Fin 1 => w (.inl 0)) := by funext i; fin_cases i; rfl
    rw [hLambdaCode] at hLambda
    have hl := (zeroExtendedScalarGraph_at (focusGraphParameterCode A T.active T.focus) a f hGraph
      (z ∘ Sum.inl) (w (.inl 0))).mp hLambda
    rw [← hX,hValue x hxA] at hl
    have hc0 := (coefficientParameterGraph_at T.coefficient a hC (w ∘ Sum.inr)).mp hCoef
    have hc : w (.inr 0)=D.coefficient.val := hc0.trans (congrArg Subtype.val hCoeff).symm
    have hw : w=Sum.elim (fun _ : Fin 1 => (D.extendedFocus x).val)
        (fun _ : Fin 1 => D.coefficient.val) := by
      funext i
      cases i with
      | inl i => fin_cases i; exact hl.symm
      | inr i => fin_cases i; exact hc
    change scalarCentripetalCodes T.coordinate (Sum.elim (z ∘ Sum.inl) w)=z ∘ Sum.inr at hStep
    rw [hw,← hX,← hj,scalarCentripetalCodes_at D x] at hStep
    have hy : z ∘ Sum.inr ∈ Q.domain := hStep ▸ mixedValues_mem_domain (D.point x)
    have hDecode : mixedValues (Q.decode ⟨z ∘ Sum.inr,hy⟩)=z ∘ Sum.inr :=
      mixedValues_decode (⟨z ∘ Sum.inr,hy⟩ : Q.domain)
    have hTarget : D.point x=Q.decode ⟨z ∘ Sum.inr,hy⟩ := mixedValues_injective (hStep.trans hDecode.symm)
    exact ⟨hx,hy,⟨⟨x,hxA⟩,rfl,hTarget⟩⟩
  · rintro ⟨hx,hy,x,hSource,hTarget⟩
    have hX : mixedValues x.val=z ∘ Sum.inl := by rw [hSource]; exact mixedValues_decode _
    have hY : mixedValues (D.point x.val)=z ∘ Sum.inr :=
      (congrArg mixedValues hTarget).trans (mixedValues_decode _)
    refine ⟨(Set.ext_iff.mp hAcode _).mpr ⟨hx,hSource ▸ x.property⟩,
      Sum.elim (fun _ : Fin 1 => (D.extendedFocus x.val).val) (fun _ : Fin 1 => D.coefficient.val),?_,?_,?_⟩
    · apply (zeroExtendedScalarGraph_at (focusGraphParameterCode A T.active T.focus) a f hGraph
        (z ∘ Sum.inl) (D.extendedFocus x.val).val).mpr
      rw [← hX]
      exact hValue x.val x.property
    · exact (coefficientParameterGraph_at T.coefficient a hC _).mpr (congrArg Subtype.val hCoeff)
    · change scalarCentripetalCodes T.coordinate (Sum.elim (z ∘ Sum.inl)
        (Sum.elim (fun _ : Fin 1 => (D.extendedFocus x.val).val) (fun _ : Fin 1 => D.coefficient.val)))=z ∘ Sum.inr
      rw [← hX,← hj,scalarCentripetalCodes_at D x.val]
      exact hY

end DiamondIntegral.Section6
