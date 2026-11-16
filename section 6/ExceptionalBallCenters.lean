import «section 6».FiniteExceptionalOpenBalls

/-! Centers for the exceptional discs use their existing finite
exceptional set as a hitting set. This needs no additional field-base
or algebraic-closure size hypothesis. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section8 SpecialTransformations.Section9
open DiamondIntegral.Section2

namespace DiamondIntegral.Section6.FMT

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

theorem exceptionalOpenBalls_centers
    (hc : CanonicalStructure.IsCanonical (M := M)) (h00 : M ⊨ Axioms.ACVF00)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (E : Set (Fin 1 → VF M)) (hEF : E.Finite) (hE : S.Definable LRV (vfValues '' E))
    (r : VF M) (hr : r ≠ 0) (hrdef : S.Definable₁ LRV {r.val}) :
    ∃ c : exceptionalOpenBalls E r hr → VF M,
      (∀ D, c D ∈ vfOpenBall D.val) ∧
      S.Definable LRV (OpenBallCodes.quotientCenterGraph
        (exceptionalOpenBalls E r hr) (fun D => (c D).val)) := by
  let A := exceptionalOpenBalls E r hr
  have hAdef : S.Definable LRV (OpenBallCodes.pullback A) := exceptionalOpenBalls_definable E hE r hr hrdef
  let F : Set (VF M) := (fun a : Fin 1 → VF M => a 0) '' E
  have hFF : F.Finite := hEF.image _
  let R := hFF.toFinset
  have hRraw : S.Definable₁ LRV (Subtype.val '' (R : Set (VF M))) := by
    change S.Definable LRV {z : Fin 1 → M | z 0 ∈ Subtype.val '' (R : Set (VF M))}
    convert hE.image_comp (fun _ : Fin 1 => (0 : Fin 1)) using 1
    ext z
    constructor
    · rintro ⟨x,hx,hxz⟩
      obtain ⟨a,ha,hax⟩ := hFF.mem_toFinset.mp hx
      refine ⟨vfValues a,⟨a,ha,rfl⟩,?_⟩
      funext i
      fin_cases i
      exact (congrArg Subtype.val hax).trans hxz
    · rintro ⟨w,⟨a,ha,rfl⟩,he⟩
      exact ⟨a 0,hFF.mem_toFinset.mpr ⟨a,ha,rfl⟩,congrFun he 0⟩
  have hRdef : DefinableAt S .vf (Subtype.val '' (R : Set (VF M))) := by
    apply (definableAt_iff_normalized_raw S .vf _).mpr
    constructor
    · change @Set.Definable M S LRV (CanonicalStructure.normalize (M := M)) (Fin 1)
        {z | z 0 ∈ Subtype.val '' (R : Set (VF M))}
      rw [normalize_eq_of_isCanonical hc]
      exact hRraw
    · rintro x ⟨a,ha,rfl⟩
      exact a.property
  have hhit (q : Fin 2 → M) (hq : q ∈ OpenBallCodes.pullback A) :
      ∃ x ∈ R, x ∈ OpenBallCodes.ball q := by
    obtain ⟨hqp,a,ha,he⟩ := hq
    have hball : OpenBallCodes.rawBall ![(a 0).val,r.val] = OpenBallCodes.rawBall q :=
      congrArg OpenBallCodes.underlying he
    refine ⟨a 0,hFF.mem_toFinset.mpr ⟨a,ha,rfl⟩,?_⟩
    change (a 0).val ∈ OpenBallCodes.rawBall q
    rw [← hball]
    exact OpenBallCodes.raw_center_mem _ (pointedOpenBallCode (a 0) r hr).property
  have hopen (q : Fin 2 → M) (hq : q ∈ OpenBallCodes.pullback A) :
      ∃ a r : VF M, r ≠ 0 ∧ OpenBallCodes.ball q = ValOneEC.openBall Valued.v a (Valued.v r) := by
    refine ⟨⟨q 0,hq.1.1 0⟩,⟨q 1,hq.1.1 1⟩,?_,?_⟩
    · exact fun he => hq.1.2 (congrArg Subtype.val he)
    · exact OpenBallCodes.ball_eq_open Valued.v hv q hq.1
  obtain ⟨g,hg,hgmem,hginv⟩ := BallFamilies.open_centers_of_finite_hitting_set Valued.v hv h00 S
    (OpenBallCodes.pullback A) (OpenBallCodes.ball (M := M)) (OpenBallCodes.relation_definable S) R hRdef hhit hopen
  exact open_center_graph_of_code_function A hAdef g hg hgmem
    (fun q u he => hginv q u (congrArg (fun D : Set M => {x : VF M | x.val ∈ D}) he))

end DiamondIntegral.Section6.FMT
