import «section 3».GammaGenericFiniteLabelKernel
import «section 3».GammaFixedVFRowIsomorphisms
import «section 3».GammaWeightedFiniteRowWitnesses
import Integration7.SelectedLabelSchemaUniformBounds

/-! An actual VF-fixed original-Gamma bijection preserving the Gamma
form at independent points has equal measured principal classes in every
positive degree. Finite-row bounds and witnesses reuse the native schemas. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6500000
set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.DefinableGeometry.Space.prod
  SpecialTransformations.Section4.realSpace SpecialTransformations.Milestone0.sortEval
  SpecialTransformations.Section4.vfSpace SpecialTransformations.Section4.rvSpace
  SpecialTransformations.Section4.rawVFSpace SpecialTransformations.Section4.rawRVSpace
  SpecialTransformations.Section4.rawMixedSpace SpecialTransformations.DefinableGeometry.Space.ofEmbedding
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5 SpecialTransformations.Section7
open IntegrationInACVF.Section6 IntegrationInACVF.Section6.FiniteRV IntegrationInACVF.Section7
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {n : ℕ}

theorem gammaNativeFixedVFPoint_comparison {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    (hr : Cardinal.mk B.real < κ) (hg : Cardinal.mk B.gamma < κ)
    (C : BaseContext M) (hBC : B.real ⊆ (C.base : Set M))
    (U V : GammaObjectAt B Set.univ (n+1))
    (ω : GammaGroundVolumeForm hc B (Section5.nativeRVGroundDomain U))
    (π : GammaGroundVolumeForm hc B (Section5.nativeRVGroundDomain V))
    (e : GammaIso B (carrier (typedLift U.object.obj)) (carrier (typedLift V.object.obj)))
    (hp : ∀ u, (e.equiv u).val.1 = u.val.1)
    (hω : ∀ u, AlgebraicIndependent (vfParameterField B.real)
        (show Fin (n+1) → VF (M := M) from u.val.1) →
      ω (gammaPresentationLabelAt U (normalizedTypedLift_presents U.object.obj) u) =
        π (gammaPresentationLabelAt V (normalizedTypedLift_presents V.object.obj) (e.equiv u))) :
    gammaNativeSpecialClass U ω = gammaNativeSpecialClass V π := by
  let HU := typedLift U.object.obj
  let HV := typedLift V.object.obj
  have hU := gammaNativeTypedLift_definable U
  have hV := gammaNativeTypedLift_definable V
  obtain ⟨NF,hNF⟩ := selected_label_schema_uniform_bound hκ hs hr hg HU hU Fin.elim0
    (fun x t => ((gammaNativeTypedMeasuredData U ω).finite x).subset (fun _ h => h.1))
  obtain ⟨NG,hNG⟩ := selected_label_schema_uniform_bound hκ hs hr hg HV hV Fin.elim0
    (fun x t => ((gammaNativeTypedMeasuredData V π).finite x).subset (fun _ h => h.1))
  let F := (gammaSelectedLabelSchema HU hU (Fin.elim0 : Fin 0 → Fin (rvObjectArity U.object.obj))).withBound NF
  let G := (gammaSelectedLabelSchema HV hV (Fin.elim0 : Fin 0 → Fin (rvObjectArity V.object.obj))).withBound NG
  have hFD (x : Fin (n+1) → VF (M := M)) : F.rowDomain (vfValues x) = {r | (x,r) ∈ carrier HU} :=
    gammaSelectedLabelSchema_domain HU hU Fin.elim0 x
  have hGD (x : Fin (n+1) → VF (M := M)) : G.rowDomain (vfValues x) = {r | (x,r) ∈ carrier HV} :=
    gammaSelectedLabelSchema_domain HV hV Fin.elim0 x
  apply gammaGeneric_finite_label_kernel hκ hs h00 hr hg C hBC U V ω π F G hNF hNG
    (gammaSelectedLabelSchema_source HU hU Fin.elim0) (gammaSelectedLabelSchema_source HV hV Fin.elim0)
  intro x hx
  have hFA : F.rowDomain (vfValues x) ⊆ (Section5.nativeRVGroundDomain (hc := hc) U).carrier := by
    intro r hr'
    exact (gammaPresentationLabelAt (hc := hc) U (normalizedTypedLift_presents U.object.obj)
      ⟨(x,r),(hFD x).le hr'⟩).property
  have hGA : G.rowDomain (vfValues x) ⊆ (Section5.nativeRVGroundDomain (hc := hc) V).carrier := by
    intro r hr'
    exact (gammaPresentationLabelAt (hc := hc) V (normalizedTypedLift_presents V.object.obj)
      ⟨(x,r),(hGD x).le hr'⟩).property
  let ex := gammaFixedVFRowIso e hp x
  have hFU : {q : Point (M := M) 0 (rvObjectArity U.object.obj) | (x,q.2) ∈ carrier HU} =
      {q : Point (M := M) 0 (rvObjectArity U.object.obj) | q.2 ∈ F.rowDomain (vfValues x)} := by
    ext q
    exact (Set.ext_iff.mp (hFD x) q.2).symm
  have hGV : {q : Point (M := M) 0 (rvObjectArity V.object.obj) | (x,q.2) ∈ carrier HV} =
      {q : Point (M := M) 0 (rvObjectArity V.object.obj) | q.2 ∈ G.rowDomain (vfValues x)} := by
    ext q
    exact (Set.ext_iff.mp (hGD x) q.2).symm
  let E := ex.congr hFU hGV
  apply gammaWeighted_finite_row_formula_witness (Section5.nativeRVGroundDomain U)
    (Section5.nativeRVGroundDomain V) ω π F G (vfValues x) (hNF x) (hNG x) hFA hGA E
  intro u
  let q : {q : Point (M := M) 0 (rvObjectArity U.object.obj) | (x,q.2) ∈ carrier HU} :=
    ⟨u.val,hFU.ge u.property⟩
  let p : HU := ⟨(x,u.val.2),q.property⟩
  have hOut : (E.equiv u).val.2 = (e.equiv p).val.2 := by
    change ((ex.congr hFU hGV).equiv u).val.2 = _
    rw [gammaIsoCongr_value]
    exact gammaFixedVFRowIso_value e hp x q
  have hSource : gammaPresentationLabelAt U (normalizedTypedLift_presents U.object.obj) p =
      ⟨u.val.2,hFA u.property⟩ := Subtype.ext rfl
  have hTarget : gammaPresentationLabelAt V (normalizedTypedLift_presents V.object.obj) (e.equiv p) =
      ⟨(E.equiv u).val.2,hGA (E.equiv u).property⟩ := Subtype.ext hOut.symm
  exact (congrArg ω hSource.symm).trans ((hω p hx).trans (congrArg π hTarget))

end DiamondIntegral.Section3
