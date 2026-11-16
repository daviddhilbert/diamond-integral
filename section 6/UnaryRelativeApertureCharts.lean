import «section 6».UnaryRelativeApertureBounds
import «section 6».CentripetalCharts

/-! Actual clopen source branches and local translation charts for the
auxiliary unary variable-aperture map. Fixed RV labels fix both VF
centres, so each branch is a constant translation. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
open Classical FirstOrder FirstOrder.Language Filter Topology
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6.UnaryRelativeApertureData
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {r : ℕ} {S : Set M}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]
variable {A : DefSet (rawMixedSpace (M := M) 1 r) S}

def branch (D : UnaryRelativeApertureData A) (u : Fin r → RVInfinity M) (b : Bool) :
    Set (Fin 1 → VF M) := {a | (a,u) ∈ A.carrier ∧ D.core (a,u)=b}

theorem core_branch_isClopen (D : UnaryRelativeApertureData A)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (u : Fin r → RVInfinity M) : IsClopen (D.branch u true) := by
  have hA := D.focusData.sourceProper.clopen_fibres hv u
  by_cases hu : u ∈ D.focusData.activeTags.carrier
  · by_cases he : (vfFibre A.carrier u).Nonempty
    · obtain ⟨a,ha⟩ := he
      let p : focusActive A D.focusData.activeTags := ⟨(a,u),ha,hu⟩
      let δ := finiteValue (D.endpoint u) (D.endpoint_nonzero p)
      let F (x : Fin 1 → VF M) := x 0-D.focusData.focus u
      have hF : ContinuousOn F (vfFibre A.carrier u) :=
        ((continuous_apply 0).sub continuous_const).continuousOn
      have hBall := scalarBall_isClopen hv δ
      have hpre : IsClopen (vfFibre A.carrier u ∩ F ⁻¹' {x : VF M | δ.val<vfValue x}) :=
        ⟨hF.preimage_isClosed_of_isClosed hA.isClosed hBall.isClosed,
          hF.isOpen_inter_preimage hA.isOpen hBall.isOpen⟩
      convert hpre using 1
      ext x
      constructor
      · rintro ⟨hx,hcore⟩
        refine ⟨hx,?_⟩
        rw [D.core_active ⟨(x,u),hx,hu⟩] at hcore
        have hc : vfValue (D.endpoint u)<vfValue (x 0-D.focusData.focus u) := of_decide_eq_true hcore
        exact hc
      · rintro ⟨hx,hlt⟩
        refine ⟨hx,?_⟩
        rw [D.core_active ⟨(x,u),hx,hu⟩]
        have hc : vfValue (D.endpoint u)<vfValue (x 0-D.focusData.focus u) := hlt
        exact decide_eq_true hc
    · have hempty : D.branch u true=∅ := Set.eq_empty_iff_forall_notMem.mpr
        (fun _ hx => he ⟨_,hx.1⟩)
      exact hempty.symm ▸ isClopen_empty
  · have hempty : D.branch u true=∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      rintro x ⟨hx,hcore⟩
      exact Bool.noConfusion ((D.core_inactive (p := (x,u)) hu).symm.trans hcore)
    exact hempty.symm ▸ isClopen_empty

theorem branch_isClopen (D : UnaryRelativeApertureData A)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (u : Fin r → RVInfinity M) (b : Bool) : IsClopen (D.branch u b) := by
  cases b
  · have he : D.branch u false=vfFibre A.carrier u \ D.branch u true := by
      ext a
      simp only [branch,Set.mem_setOf_eq,Set.mem_diff,Section2.vfFibre]
      exact ⟨fun h => ⟨h.1,fun ht => Bool.noConfusion (h.2.symm.trans ht.2)⟩,
        fun h => ⟨h.1,Bool.eq_false_iff.mpr (fun ht => h.2 ⟨h.1,ht⟩)⟩⟩
    rw [he]
    exact (D.focusData.sourceProper.clopen_fibres hv u).diff (D.core_branch_isClopen hv u)
  · exact D.core_branch_isClopen hv u

def outputTags (D : UnaryRelativeApertureData A) (u : Fin r → RVInfinity M) (b : Bool) :=
  Fin.append (fun _ : Fin 1 => branchTag (M := M) b) u

theorem point_tags (D : UnaryRelativeApertureData A) (p : Mixed M 1 r) :
    (D.point p).2 = D.outputTags p.2 (D.core p) := rfl

theorem outputTags_injective (D : UnaryRelativeApertureData A)
    (h00 : M ⊨ Axioms.ACVF00) (u : Fin r → RVInfinity M) : Function.Injective (D.outputTags u) := by
  intro b c he
  apply branchTag_injective h00
  simpa only [outputTags,Fin.append_left] using congrFun he (Fin.castAdd r 0)

def branchFocus (D : UnaryRelativeApertureData A) (u : Fin r → RVInfinity M)
    (b : Bool) (_a : Fin 1 → VF M) : VF M :=
  if u ∈ D.focusData.activeTags.carrier then
    -D.focusData.focus u+if b then D.endpoint u else 0 else 0

theorem point_on_branch (D : UnaryRelativeApertureData A)
    (u : Fin r → RVInfinity M) (b : Bool) {a : Fin 1 → VF M} (ha : a ∈ D.branch u b) :
    D.point (a,u) = (coordinateShear D.coordinate (D.branchFocus u b) a,D.outputTags u b) := by
  classical
  apply Prod.ext
  · by_cases hu : u ∈ D.focusData.activeTags.carrier
    · rw [point,D.extendedFocus_active ⟨(a,u),ha.1,hu⟩,
        D.extendedEndpoint_active ⟨(a,u),ha.1,hu⟩]
      change Function.update a D.coordinate (a D.coordinate-D.focusData.focus u+
        if D.core (a,u) then D.endpoint u else 0)=coordinateShear D.coordinate (D.branchFocus u b) a
      rw [ha.2]
      simp only [branchFocus,hu,ite_true,coordinateShear]
      apply congrArg (Function.update a D.coordinate)
      cases b <;> simp only [Bool.false_eq_true,ite_false,ite_true,add_zero] <;> abel
    · rw [D.point_inactive (p := (a,u)) hu]
      simp only [coordinateShear,branchFocus,hu,ite_false,add_zero,Function.update_eq_self]
  · rw [D.point_tags,ha.2]

theorem branchFocus_continuous (D : UnaryRelativeApertureData A)
    (u : Fin r → RVInfinity M) (b : Bool) :
    ContinuousOn (fun a => D.branchFocus u b (Function.update a D.coordinate 0)) (vfFibre A.carrier u) :=
  continuousOn_const

theorem branchFocus_continuousAt (D : UnaryRelativeApertureData A)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (u : Fin r → RVInfinity M) (b : Bool) {a : Fin 1 → VF M} (ha : (a,u) ∈ A.carrier) :
    ContinuousAt (fun x => D.branchFocus u b (Function.update x D.coordinate 0)) a :=
  (D.branchFocus_continuous u b).continuousAt ((D.focusData.sourceProper.clopen_fibres hv u).isOpen.mem_nhds ha)

theorem shear_chart (D : UnaryRelativeApertureData A)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y) (p : A) :
    IsVFChartAt D.bijection p (coordinateShear D.coordinate (D.branchFocus p.val.2 (D.core p.val))) := by
  have hp : p.val.1 ∈ D.branch p.val.2 (D.core p.val) := ⟨p.property,rfl⟩
  obtain ⟨ρ,hρ⟩ := exists_vfBall_subset_nhds hv p.val.1
    ((D.branch_isClopen hv p.val.2 (D.core p.val)).isOpen.mem_nhds hp)
  refine ⟨ρ,fun x hx => ?_⟩
  have hxB := hρ hx
  refine ⟨hxB.1,?_⟩
  change D.point (x,p.val.2) = (_, (D.point p.val).2)
  rw [D.point_on_branch p.val.2 (D.core p.val) hxB,D.point_tags]

theorem local_shear_charts (D : UnaryRelativeApertureData A)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y) : HasLocalShearCharts D.bijection :=
  fun p => ⟨D.coordinate,D.branchFocus p.val.2 (D.core p.val),D.shear_chart hv p⟩

theorem unit_derivative_ae [CharZero (VF M)] (D : UnaryRelativeApertureData A)
    (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ) (hsmall : Cardinal.mk S < κ)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y) :
    ∃ E : DefSet (rawMixedSpace (M := M) 1 r) S, E.carrier ⊆ A.carrier ∧
      vfDim (rawRVSpace (M := M) 1) E < 1 ∧
      ∀ p : A, p.val ∉ E.carrier → HasMixedUnitDerivativeAt D.bijection p :=
  local_shear_unit_derivative_ae hc hκ hs hsmall hv
    (lt_of_le_of_lt (Nat.zero_le _) D.coordinate.isLt) D.bijection (D.local_shear_charts hv)

end DiamondIntegral.Section6.UnaryRelativeApertureData
