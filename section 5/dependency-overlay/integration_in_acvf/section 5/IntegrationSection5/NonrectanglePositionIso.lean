import IntegrationSection5.PositionedCellLabelInjection
import IntegrationSection5.NativeCellProjections
import IntegrationSection5.RVRectangleCases
import IntegrationSection5.NonrectangleCellGeometry

/-! The selected positioning functions form one actual original-Gamma bijection between the mixed projections of the nonrectangle branch, preserving its entire RV code. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section5 SpecialTransformations.Section3
open IntegrationInACVF.Section4
namespace IntegrationInACVF.Section5.PositionedCellLabelInjection
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {G : GammaParameters.Base (M := M)} {m : ℕ} {A : Set (Point (M := M) 2 m)}

def nonrectangleFirstInclusion (T : PositionedCellLabelInjection G A)
    (p : mixedUnaryProjectionSet (nonrectangleFamilyBranch T.target) 0) : mixedUnaryProjectionSet T.target 0 :=
  ⟨p.val,by obtain ⟨q,hq,hqp⟩ := p.property; exact ⟨q,hq.1,hqp⟩⟩

def nonrectanglePosition (T : PositionedCellLabelInjection G A)
    (p : mixedUnaryProjectionSet (nonrectangleFamilyBranch T.target) 0) : VF (M := M) :=
  T.restrictedPosition (T.nonrectangleFirstInclusion p)

theorem nonrectanglePosition_graph (T : PositionedCellLabelInjection G A) :
    GammaScalarGraphDefinable G (fun p y =>
      ∃ u : mixedUnaryProjectionSet (nonrectangleFamilyBranch T.target) 0,
        u.val = p ∧ T.nonrectanglePosition u = y) := by
  have hN := nonrectangleFamilyBranch_gamma T.target (T.iso.target_definable (gammaLogicInput G))
  have hD := mixedUnaryProjection_gamma _ hN 0
  apply GammaGraphDefinable.congr ((gammaLogicInput G).restrict_graph hD T.restrictedPosition_graph)
  intro p q
  constructor
  · rintro ⟨hp,u,hu,he⟩
    refine ⟨⟨p,hp⟩,rfl,?_⟩
    have hu' : T.nonrectangleFirstInclusion ⟨p,hp⟩ = u := Subtype.ext hu.symm
    change T.restrictedPosition (T.nonrectangleFirstInclusion ⟨p,hp⟩) = vfAt q 0
    rw [hu']
    exact he
  · rintro ⟨u,hu,he⟩
    exact ⟨hu ▸ u.property,T.nonrectangleFirstInclusion u,hu,he⟩

theorem nonrectangle_fibre_position (T : PositionedCellLabelInjection G A)
    (δ : Values.Gamma (M := M)) (hδ : 1 < δ) (s : Fin T.arity → RV (M := M))
    (hs : (nativeTwoFibre (nonrectangleFamilyBranch T.target) s).Nonempty) :
    ∃ f : VF (M := M) → VF (M := M), ∃ t : RV (M := M),
      Cells.DefinableCellData (RVLabelSlices.labelBase G s) (nativeTwoFibre T.target s) f t ∧
      Set.BijOn f (Cells.first (nativeTwoFibre (nonrectangleFamilyBranch T.target) s))
        (Cells.second (nativeTwoFibre (nonrectangleFamilyBranch T.target) s)) ∧
      ∀ p : mixedUnaryProjectionSet (nonrectangleFamilyBranch T.target) 0,
        p.val.2 = s → T.nonrectanglePosition p = f (vfAt p.val 0) := by
  obtain ⟨hEq,hNonrect⟩ := nonrectangleFamilyBranch_native_fibre T.target s hs
  obtain ⟨f,t,hDef,hAgree⟩ := T.cells_restrictedPosition s (hEq ▸ hs)
  have hBij := nonrectangle_position_bijective δ hδ hDef.1 hNonrect
  refine ⟨f,t,hDef,?_,?_⟩
  · rw [hEq]
    exact hBij
  · intro p hp
    have hx := (mixed_first_projection_fibre_iff (nonrectangleFamilyBranch T.target) p.val).mp p.property
    rw [hp,hEq] at hx
    apply hAgree (vfAt p.val 0) hx (T.nonrectangleFirstInclusion p)
    apply Prod.ext
    · funext j; fin_cases j; rfl
    · exact hp

theorem nonrectangle_position_gamma_iso (T : PositionedCellLabelInjection G A)
    (δ : Values.Gamma (M := M)) (hδ : 1 < δ) :
    ∃ e : GammaIso G (mixedUnaryProjectionSet (nonrectangleFamilyBranch T.target) 0)
        (mixedUnaryProjectionSet (nonrectangleFamilyBranch T.target) 1),
      (∀ p, (e.equiv p).val.2 = p.val.2) ∧
      ∀ p, vfAt (e.equiv p).val 0 = T.nonrectanglePosition p := by
  let N := nonrectangleFamilyBranch T.target
  let D := mixedUnaryProjectionSet N 0
  let E := mixedUnaryProjectionSet N 1
  let g : D → VF (M := M) := T.nonrectanglePosition
  have hMap (a : D) : replace 0 a.val (g a) ∈ E := by
    have hx := (mixed_first_projection_fibre_iff N a.val).mp a.property
    have hNe : (nativeTwoFibre N a.val.2).Nonempty := by
      obtain ⟨p,hp,_⟩ := hx
      exact ⟨p,hp⟩
    obtain ⟨f,t,hDef,hBij,hAgree⟩ := T.nonrectangle_fibre_position δ hδ a.val.2 hNe
    apply (mixed_second_projection_fibre_iff N _).mpr
    change T.nonrectanglePosition a ∈ Cells.second (nativeTwoFibre (nonrectangleFamilyBranch T.target) a.val.2)
    rw [hAgree a rfl]
    exact hBij.mapsTo hx
  let F (a : D) : E := ⟨replace 0 a.val (g a),hMap a⟩
  have hInj : Function.Injective F := by
    intro a b he
    have hl : a.val.2 = b.val.2 := congrArg (fun q : E => q.val.2) he
    have hv : g a = g b := congrArg (fun q : E => vfAt q.val 0) he
    have hx := (mixed_first_projection_fibre_iff N a.val).mp a.property
    have hy := (mixed_first_projection_fibre_iff N b.val).mp b.property
    rw [← hl] at hy
    have hNe : (nativeTwoFibre N a.val.2).Nonempty := by
      obtain ⟨p,hp,_⟩ := hx
      exact ⟨p,hp⟩
    obtain ⟨f,t,hDef,hBij,hAgree⟩ := T.nonrectangle_fibre_position δ hδ a.val.2 hNe
    have hxy : vfAt a.val 0 = vfAt b.val 0 := hBij.injOn hx hy
      ((hAgree a rfl).symm.trans (hv.trans (hAgree b hl.symm)))
    apply Subtype.ext
    apply Prod.ext
    · funext j; fin_cases j; exact hxy
    · exact hl
  have hSurj : Function.Surjective F := by
    intro b
    have hy := (mixed_second_projection_fibre_iff N b.val).mp b.property
    have hNe : (nativeTwoFibre N b.val.2).Nonempty := by
      obtain ⟨p,hp,_⟩ := hy
      exact ⟨p,hp⟩
    obtain ⟨f,t,hDef,hBij,hAgree⟩ := T.nonrectangle_fibre_position δ hδ b.val.2 hNe
    obtain ⟨x,hx,hfx⟩ := hBij.surjOn hy
    let p : Point (M := M) 1 T.arity := (fun _ => x,b.val.2)
    let a : D := ⟨p,(mixed_first_projection_fibre_iff N p).mpr hx⟩
    refine ⟨a,Subtype.ext (Prod.ext ?_ rfl)⟩
    funext j
    fin_cases j
    exact (hAgree a rfl).trans hfx
  let e : GammaIso G D E := ⟨Equiv.ofBijective F ⟨hInj,hSurj⟩,
    gamma_scalar_replacement_graph 0 g T.nonrectanglePosition_graph⟩
  exact ⟨e,fun _ => rfl,fun _ => rfl⟩

end IntegrationInACVF.Section5.PositionedCellLabelInjection
