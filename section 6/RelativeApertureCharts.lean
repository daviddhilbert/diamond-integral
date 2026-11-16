import «section 6».RelativeApertureBranches

/-! On a fixed finite branch the concrete map is a triangular shear.
Clopen branch domains give actual VF charts with all RV labels fixed. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

open FirstOrder FirstOrder.Language Filter Topology
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2

namespace DiamondIntegral.Section6.RelativeApertureData

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n r : ℕ} {S : Set M}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]
variable {A : DefSet (rawMixedSpace (M := M) n r) S}

def outputTags (D : RelativeApertureData (G := G) A) (u : Fin r → RVInfinity M) (b : Bool) :=
  Fin.append (fun _ : Fin 1 => branchTag (M := M) b) u

theorem point_tags (D : RelativeApertureData (G := G) A) (p : Mixed M n r) :
    (D.point p).2 = D.outputTags p.2 (D.core p) := rfl

theorem outputTags_injective (D : RelativeApertureData (G := G) A)
    (h00 : M ⊨ Axioms.ACVF00) (u : Fin r → RVInfinity M) : Function.Injective (D.outputTags u) := by
  intro b c he
  apply branchTag_injective h00
  simpa only [outputTags,Fin.append_left] using congrFun he (Fin.castAdd r 0)

def branchFocus (D : RelativeApertureData (G := G) A) (u : Fin r → RVInfinity M)
    (b : Bool) (a : Fin n → VF M) : VF M := by
  classical
  exact if u ∈ D.activeTags.carrier then
    if b then D.endpoint a u-D.focus a u else -D.focus a u else 0

theorem point_on_branch (D : RelativeApertureData (G := G) A)
    (u : Fin r → RVInfinity M) (b : Bool) {a : Fin n → VF M} (ha : a ∈ D.branch u b) :
    D.point (a,u) = (coordinateShear D.coordinate (D.branchFocus u b) a,D.outputTags u b) := by
  classical
  apply Prod.ext
  · by_cases hu : u ∈ D.activeTags.carrier
    · rw [point,D.extendedFocus_active ha.1 hu,D.extendedEndpoint_active ha.1 hu,ha.2]
      simp only [branchFocus,hu,ite_true,coordinateShear]
      apply congrArg (Function.update a D.coordinate)
      cases b <;> simp only [Bool.false_eq_true,ite_false,ite_true,add_zero]
      · exact sub_eq_add_neg _ _
      · ring
    · rw [D.point_inactive (p := (a,u)) hu]
      simp only [coordinateShear,branchFocus,hu,ite_false,add_zero,Function.update_eq_self]
  · rw [D.point_tags,ha.2]

theorem branchFocus_continuous (D : RelativeApertureData (G := G) A)
    (u : Fin r → RVInfinity M) (b : Bool) :
    ContinuousOn (fun a => D.branchFocus u b (Function.update a D.coordinate 0)) (vfFibre A.carrier u) := by
  classical
  by_cases hu : u ∈ D.activeTags.carrier
  · cases b
    · simp only [branchFocus,hu,ite_true,Bool.false_eq_true,ite_false]
      convert (D.continuous u hu).neg using 1
    · simp only [branchFocus,hu,ite_true]
      convert (D.endpoint_continuous u hu).sub (D.continuous u hu) using 1
  · simp only [branchFocus,hu,ite_false]
    exact continuousOn_const

theorem branchFocus_continuousAt (D : RelativeApertureData (G := G) A)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (u : Fin r → RVInfinity M) (b : Bool) {a : Fin n → VF M} (ha : (a,u) ∈ A.carrier) :
    ContinuousAt (fun x => D.branchFocus u b (Function.update x D.coordinate 0)) a :=
  (D.branchFocus_continuous u b).continuousAt ((D.sourceProper.clopen_fibres hv u).isOpen.mem_nhds ha)

theorem shear_chart (D : RelativeApertureData (G := G) A)
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

theorem local_shear_charts (D : RelativeApertureData (G := G) A)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y) : HasLocalShearCharts D.bijection :=
  fun p => ⟨D.coordinate,D.branchFocus p.val.2 (D.core p.val),D.shear_chart hv p⟩

theorem unit_derivative_ae [CharZero (VF M)] (D : RelativeApertureData (G := G) A)
    (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ) (hsmall : Cardinal.mk S < κ)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y) :
    ∃ E : DefSet (rawMixedSpace (M := M) n r) S, E.carrier ⊆ A.carrier ∧
      vfDim (rawRVSpace (M := M) 1) E < n ∧
      ∀ p : A, p.val ∉ E.carrier → HasMixedUnitDerivativeAt D.bijection p :=
  local_shear_unit_derivative_ae hc hκ hs hsmall hv
    (lt_of_le_of_lt (Nat.zero_le _) D.coordinate.isLt) D.bijection (D.local_shear_charts hv)

end DiamondIntegral.Section6.RelativeApertureData
