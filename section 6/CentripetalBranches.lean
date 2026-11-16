import «section 6».CentripetalBounds

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

theorem scalarBall_isClopen
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y) (δ : Gamma M) :
    IsClopen {x : VF M | δ.val < vfValue x} := by
  let α : Fin 1 → Gamma M := fun _ => δ
  let D : Set (Fin 1 → VF M) := {a | Congruent α 0 a}
  have hD : AlphaInvariant α D := by
    intro a b hab
    exact ⟨fun ha => ha.trans hab,fun hb => hb.trans hab.symm⟩
  have hp := (hD.isClopen hv).preimage (continuous_pi (fun _ : Fin 1 => continuous_id))
  convert hp using 1
  ext x
  simp only [Set.mem_setOf_eq,Set.mem_preimage,D,Congruent,Pi.zero_apply,zero_sub,
    ← valueHom_eq_value,vfValue_neg,Fin.forall_fin_one,α]
  rfl

namespace CentripetalData

variable {n r : ℕ} {S : Set M} {A : DefSet (rawMixedSpace (M := M) n r) S}

def branch (D : CentripetalData (G := G) A) (u : Fin r → RVInfinity M) (b : Bool) :
    Set (Fin n → VF M) := {a | (a,u) ∈ A.carrier ∧ D.core (a,u) = b}

theorem branch_subset (D : CentripetalData (G := G) A) (u : Fin r → RVInfinity M) (b : Bool) :
    D.branch u b ⊆ vfFibre A.carrier u := fun _ h => h.1

theorem cutoff_value_eq (D : CentripetalData (G := G) A)
    {u : Fin r → RVInfinity M} (hu : u ∈ D.activeTags.carrier)
    {a x : Fin n → VF M} (ha : (a,u) ∈ A.carrier) (hx : (x,u) ∈ A.carrier) :
    vfValue (D.coefficient * D.extendedFocus (a,u)) =
      vfValue (D.coefficient * D.extendedFocus (x,u)) := by
  have he : vfValue (a D.coordinate) = vfValue (x D.coordinate) :=
    congrArg Values.vrv (congrFun (D.tagged (a,u) ha (x,u) hx rfl) D.coordinate)
  change Values.vfValueHom _ = Values.vfValueHom _
  rw [map_mul,map_mul]
  change vfValue D.coefficient * vfValue (D.extendedFocus (a,u)) =
    vfValue D.coefficient * vfValue (D.extendedFocus (x,u))
  rw [D.focus_value ha hu,D.focus_value hx hu,he]

theorem core_branch_isClopen (D : CentripetalData (G := G) A)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (u : Fin r → RVInfinity M) : IsClopen (D.branch u true) := by
  classical
  have hA := D.sourceProper.clopen_fibres hv u
  by_cases hu : u ∈ D.activeTags.carrier
  · by_cases he : (vfFibre A.carrier u).Nonempty
    · obtain ⟨a,ha⟩ := he
      let δ := finiteValue (D.coefficient * D.extendedFocus (a,u))
        (mul_ne_zero D.coefficient_nonzero (D.focus_nonzero ha hu))
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
        have hlt : vfValue (D.coefficient * D.extendedFocus (x,u)) <
            vfValue (x D.coordinate - D.extendedFocus (x,u)) := of_decide_eq_true hc
        rw [D.extendedFocus_active hx hu] at hlt
        change δ.val < vfValue (F x)
        have hcut := D.cutoff_value_eq hu ha hx
        rw [D.extendedFocus_active hx hu] at hcut
        exact hcut.trans_lt hlt
      · rintro ⟨hx,hlt⟩
        refine ⟨hx,?_⟩
        apply decide_eq_true
        change vfValue (D.coefficient * D.extendedFocus (x,u)) <
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

theorem branch_isClopen (D : CentripetalData (G := G) A)
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

end CentripetalData
end DiamondIntegral.Section6
