import IntegrationSection3ACVF.OpenImages
import «section 3».IntegrationBallShapes
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
/-! Exact primitive-shape comparison for reuse of [18, Lemma 3.8]. -/
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3
open IntegrationInACVF.Section3ACVF
open IntegrationInACVF.Section3ACVF.PuncturedGeometry
open IntegrationInACVF.Section3ACVF.GammaRadiusAtomicity
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

theorem integrationIsClosedBall_iff (A : Set M) :
    PaperBalls.IsClosedBall A ↔ Section2.IsClosedDisc A := by
  constructor
  · intro hA
    obtain ⟨q,hq⟩ := BallKindPredicates.paper_closed_code hA
    exact ⟨Quotient.mk _ q,hq.symm⟩
  · rintro ⟨C,rfl⟩
    obtain ⟨q,rfl⟩ := Quotient.exists_rep C
    exact BallKindGeometry.closed_raw_isClosedBall q

theorem integrationClosed_oneComponent {A : Set M} (hA : PaperBalls.IsClosedBall A) :
    PrimitiveImages.OnePrimitiveComponent A := by
  obtain ⟨q,hq⟩ := BallKindPredicates.paper_closed_code hA
  have hb : IsBall A := hq ▸ BallCodeGeometry.closed_raw_isBall q
  let d : PuncturedBall M := {
    parent := A
    parent_ball := hb
    holes := ∅
    holes_ball := by simp
    holes_proper := by simp
    holes_disjoint := by simp }
  refine ⟨d,?_,.closedBall,rfl,hA⟩
  ext x
  simp [PuncturedBall.body,d]

theorem integrationThin_body (d : PuncturedBall M) (ht : PaperBalls.IsThinAnnulus d) :
    Section2.IsThinAnnulus d.body := by
  obtain ⟨a,b,γ,hp,hh⟩ := ht
  have hb : b.val ∈ d.parent :=
    (d.holes_proper (gammaBall b γ true) (by rw [hh]; simp)).1
      (BallEnlargementGeometry.gammaBall_centre_mem b γ true)
  have hbc : b ∈ Section2.discPoints (Section2.closedDiscCode a γ.val) := by
    change b.val ∈ BallImaginaries.underlying (Section2.closedDiscCode a γ.val)
    rw [integrationClosedDisc_gammaBall]
    rwa [hp] at hb
  obtain ⟨Γ,hΓ,v,hv⟩ := VFValued.exists_valuation_predV (M := M)
  letI := hΓ
  have hn := Section2.finitePolydiscNames_recenter v hv
    (fun _ : Fin 1 => true) (fun _ => a) (fun _ => b) (fun _ => γ) (fun _ => hbc)
  have hc : Section2.closedDiscCode b γ.val = Section2.closedDiscCode a γ.val := congrFun hn 0
  have he : d.body = gammaBall a γ false \ gammaBall b γ true := by
    ext x
    simp [PuncturedBall.body,hp,hh]
  refine ⟨b,γ,?_⟩
  rw [he,Section2.thinAnnulus,hc,integrationClosedDisc_gammaBall,integrationOpenDisc_gammaBall]

theorem integrationThin_oneComponent (a : Section2.VF M) (γ : Section2.Gamma M) :
    PrimitiveImages.OnePrimitiveComponent (Section2.thinAnnulus a γ) := by
  let d : PuncturedBall M := {
    parent := gammaBall a γ false
    parent_ball := BallEnlargementGeometry.gammaBall_isBall a γ false
    holes := {gammaBall a γ true}
    holes_ball := by
      intro h hh
      have he := Finset.mem_singleton.mp hh
      rw [he]
      exact BallEnlargementGeometry.gammaBall_isBall a γ true
    holes_proper := by
      intro h hh
      have he := Finset.mem_singleton.mp hh
      rw [he]
      exact BallEnlargementGeometry.open_inside_closed_same_radius a a γ
        (BallEnlargementGeometry.gammaBall_centre_mem a γ false)
    holes_disjoint := by simp }
  refine ⟨d,?_,.thinAnnulus,a,a,γ,rfl,rfl⟩
  ext x
  simp [Section2.thinAnnulus,integrationClosedDisc_gammaBall,integrationOpenDisc_gammaBall,
    PuncturedBall.body,d]

theorem integrationPrimitive_iff (A : Set M) :
    PrimitiveImages.OnePrimitiveComponent A ↔ Section2.IsPrimitiveDisc A := by
  constructor
  · rintro ⟨d,rfl,k,hk⟩
    cases k with
    | openBall =>
      have he := OpenImages.body_eq_parent hk.1
      rw [he]
      rcases (integrationIsOpenBall_iff d.parent).mp hk.2 with hVF | hopen
      · exact Or.inr (Or.inl ((integrationIsClosedBall_iff d.parent).mp (Or.inl hVF)))
      · exact Or.inl hopen
    | closedBall =>
      rw [OpenImages.body_eq_parent hk.1]
      exact Or.inr (Or.inl ((integrationIsClosedBall_iff d.parent).mp hk.2))
    | thinAnnulus => exact Or.inr (Or.inr (integrationThin_body d hk))
  · rintro (hOpen | hClosed | ⟨a,γ,rfl⟩)
    · exact OpenImages.open_one_component ((integrationIsOpenBall_iff A).mpr (Or.inr hOpen))
    · exact integrationClosed_oneComponent ((integrationIsClosedBall_iff A).mpr hClosed)
    · exact integrationThin_oneComponent a γ
end DiamondIntegral.Section3
