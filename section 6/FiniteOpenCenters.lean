import «section 6».FiniteHittingSets
import Section3.OpenBallCenters

/-! Original-base centers for a finite definable family of actual open
balls. Finite hitting tuples supply one definable hitting set; checked
means then give a complete code-invariant center function. No temporary
closure-smallness or abstract Gamma-generation premise is required. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section8 SpecialTransformations.Section9
open DiamondIntegral.Section2

namespace DiamondIntegral.Section6

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M}

private theorem finite_open_family_hitting_tuple
    (A : Set (OpenBallCodes.OpenBall M)) (hA : A.Finite) :
    ∃ N : ℕ, (HittingTuples (OpenBallCodes.pullback A)
      (fun q x => (q,x) ∈ BallFamilies.relation (OpenBallCodes.ball (M := M))) N).Nonempty := by
  letI : Fintype A := hA.fintype
  let point (D : A) : VF M := ⟨(OpenBallCodes.underlying_nonempty D.val).choose,
    OpenBallCodes.underlying_subset_vf D.val (OpenBallCodes.underlying_nonempty D.val).choose_spec⟩
  have hpoint (D : A) : (point D).val ∈ OpenBallCodes.underlying D.val :=
    (OpenBallCodes.underlying_nonempty D.val).choose_spec
  let e : A ≃ Fin (Fintype.card A) := Fintype.equivFin A
  let a (i : Fin (Fintype.card A)) := point (e.symm i)
  refine ⟨Fintype.card A,a,?_⟩
  intro q hq
  obtain ⟨hqp,hqA⟩ := hq
  let D : A := ⟨Quotient.mk _ (⟨q,hqp⟩ : OpenBallCodes.Code M),hqA⟩
  have he : a (e D) = point D := congrArg point (e.symm_apply_apply D)
  refine ⟨e D,a (e D),?_,rfl⟩
  rw [he]
  exact hpoint D

variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

theorem exists_original_base_open_centers
    (hc : CanonicalStructure.IsCanonical (M := M)) (h00 : M ⊨ Axioms.ACVF00)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (V S : Set M) (hV : ∀ a ∈ V, iVF a) (hVS : V ⊆ S) (hSV : S ⊆ algebraicClosureSet V)
    (hnt : ∃ x : vfAlgebraicClosureField V, x ≠ 0 ∧ Valued.v x.val ≠ 1)
    (A : Set (OpenBallCodes.OpenBall M)) (hA : A.Finite)
    (hAdef : S.Definable LRV (OpenBallCodes.pullback A)) :
    ∃ f : (Fin 2 → M) → VF M, S.DefinableFun LRV (fun q => (f q).val) ∧
      (∀ q ∈ OpenBallCodes.pullback A, (f q).val ∈ OpenBallCodes.rawBall q) ∧
      ∀ q u, OpenBallCodes.rawBall q = OpenBallCodes.rawBall u → f q = f u := by
  obtain ⟨N,hN⟩ := finite_open_family_hitting_tuple A hA
  obtain ⟨E,hEfin,hEdef,hEhit⟩ := exists_finite_definable_hitting_set hc h00 hv V S hV hVS hSV hnt
    (OpenBallCodes.pullback A) hAdef
    (fun q x => (q,x) ∈ BallFamilies.relation (OpenBallCodes.ball (M := M)))
    (OpenBallCodes.relation_definable S) N hN
  let R := hEfin.toFinset
  have hRraw : S.Definable₁ LRV (Subtype.val '' (R : Set (VF M))) := by
    simpa only [R,hEfin.coe_toFinset] using hEdef
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
    obtain ⟨x,hx,b,hb,hbx⟩ := hEhit q hq
    have hbe : b = x := Subtype.ext hbx
    exact ⟨x,hEfin.mem_toFinset.mpr hx,hbe ▸ hb⟩
  have hopen (q : Fin 2 → M) (hq : q ∈ OpenBallCodes.pullback A) :
      ∃ a r : VF M, r ≠ 0 ∧ OpenBallCodes.ball q = ValOneEC.openBall Valued.v a (Valued.v r) := by
    obtain ⟨hqp,hqA⟩ := hq
    refine ⟨⟨q 0,hqp.1 0⟩,⟨q 1,hqp.1 1⟩,?_,?_⟩
    · intro he
      exact hqp.2 (congrArg Subtype.val he)
    · exact OpenBallCodes.ball_eq_open Valued.v hv q hqp
  obtain ⟨f,hf,hfmem,hfinv⟩ := BallFamilies.open_centers_of_finite_hitting_set Valued.v hv h00 S
    (OpenBallCodes.pullback A) (OpenBallCodes.ball (M := M)) (OpenBallCodes.relation_definable S) R hRdef hhit hopen
  refine ⟨f,hf,hfmem,fun q u he => hfinv q u ?_⟩
  exact congrArg (fun D : Set M => {x : VF M | x.val ∈ D}) he

end DiamondIntegral.Section6
