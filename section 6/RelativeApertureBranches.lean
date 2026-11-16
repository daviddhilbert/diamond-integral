import «section 6».CentripetalBranches
import «section 6».RelativeApertureBounds

/-! The two finite-aperture branches are clopen on each old RV fiber.
The cutoff is constant there because regularization fixed the VF leading
terms. The proof retains the actual focus graph and uses its continuity. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

open FirstOrder FirstOrder.Language Filter Topology
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2

namespace DiamondIntegral.Section6

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

namespace RelativeApertureData

variable {n r : ℕ} {S : Set M} {A : DefSet (rawMixedSpace (M := M) n r) S}

def branch (D : RelativeApertureData (G := G) A) (u : Fin r → RVInfinity M) (b : Bool) :
    Set (Fin n → VF M) := {a | (a,u) ∈ A.carrier ∧ D.core (a,u) = b}

theorem branch_subset (D : RelativeApertureData (G := G) A) (u : Fin r → RVInfinity M) (b : Bool) :
    D.branch u b ⊆ vfFibre A.carrier u := fun _ h => h.1

theorem cutoff_value_eq (D : RelativeApertureData (G := G) A)
    {u : Fin r → RVInfinity M} (hu : u ∈ D.activeTags.carrier)
    {a x : Fin n → VF M} (ha : (a,u) ∈ A.carrier) (hx : (x,u) ∈ A.carrier) :
    vfValue (D.extendedEndpoint (a,u)) =
      vfValue (D.extendedEndpoint (x,u)) := by
  have h := D.endpoint_RV_constant ⟨(a,u),ha,hu⟩ ⟨(x,u),hx,hu⟩ rfl
  have hV := congrArg Values.vrv h
  change vfValue ((D.endpointMap ⟨(a,u),ha,hu⟩).val 0)=
    vfValue ((D.endpointMap ⟨(x,u),hx,hu⟩).val 0) at hV
  rw [D.endpointMap_eq,D.endpointMap_eq] at hV
  rwa [D.extendedEndpoint_active ha hu,D.extendedEndpoint_active hx hu]

theorem core_branch_isClopen (D : RelativeApertureData (G := G) A)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (u : Fin r → RVInfinity M) : IsClopen (D.branch u true) := by
  classical
  have hA := D.sourceProper.clopen_fibres hv u
  by_cases hu : u ∈ D.activeTags.carrier
  · by_cases he : (vfFibre A.carrier u).Nonempty
    · obtain ⟨a,ha⟩ := he
      let δ := finiteValue (D.extendedEndpoint (a,u))
        (D.endpoint_nonzero_at ha hu)
      let F (x : Fin n → VF M) := x D.coordinate - D.focus (Function.update x D.coordinate 0) u
      have hF : ContinuousOn F (vfFibre A.carrier u) :=
        (continuous_apply D.coordinate).continuousOn.sub (D.continuous u hu)
      have hBall := scalarBall_isClopen hv δ
      have hpre : IsClopen (vfFibre A.carrier u ∩ F ⁻¹' {x : VF M | δ.val < vfValue x}) :=
        ⟨hF.preimage_isClosed_of_isClosed hA.isClosed hBall.isClosed,
          hF.isOpen_inter_preimage hA.isOpen hBall.isOpen⟩
      convert hpre using 1
      ext x
      constructor
      · rintro ⟨hx,hc⟩
        refine ⟨hx,?_⟩
        have hlt : vfValue (D.extendedEndpoint (x,u)) <
            vfValue (x D.coordinate - D.extendedFocus (x,u)) := of_decide_eq_true hc
        rw [D.extendedFocus_active hx hu] at hlt
        change δ.val < vfValue (F x)
        have hcut := D.cutoff_value_eq hu ha hx
        exact hcut.trans_lt hlt
      · rintro ⟨hx,hlt⟩
        refine ⟨hx,?_⟩
        apply decide_eq_true
        change vfValue (D.extendedEndpoint (x,u)) <
          vfValue (x D.coordinate - D.extendedFocus (x,u))
        rw [← D.cutoff_value_eq hu ha hx,D.extendedFocus_active hx hu]
        exact hlt
    · have hempty : D.branch u true = ∅ := Set.eq_empty_iff_forall_notMem.mpr
        (fun _ hx => he ⟨_,hx.1⟩)
      exact hempty.symm ▸ isClopen_empty
  · have hempty : D.branch u true = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      rintro x ⟨hx,hc⟩
      have hf := D.core_inactive (p := (x,u)) hu
      exact Bool.noConfusion (hf.symm.trans hc)
    exact hempty.symm ▸ isClopen_empty

theorem branch_isClopen (D : RelativeApertureData (G := G) A)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (u : Fin r → RVInfinity M) (b : Bool) : IsClopen (D.branch u b) := by
  cases b
  · have he : D.branch u false = vfFibre A.carrier u \ D.branch u true := by
      ext a
      simp only [branch,Set.mem_setOf_eq,Set.mem_diff,Section2.vfFibre]
      exact ⟨fun h => ⟨h.1,fun ht => Bool.noConfusion (h.2.symm.trans ht.2)⟩,
        fun h => ⟨h.1,Bool.eq_false_iff.mpr (fun ht => h.2 ⟨h.1,ht⟩)⟩⟩
    rw [he]
    exact (D.sourceProper.clopen_fibres hv u).diff (D.core_branch_isClopen hv u)
  · exact D.core_branch_isClopen hv u

end RelativeApertureData
end DiamondIntegral.Section6
