import «section 5».Completed18Section5Input
import «section 5».Completed18VFComparison
import IntegrationSection6.GammaNonzeroBasicRelation
import IntegrationSection6.GlobalIntegrationSemiringEquivalence

/-! The completed [18] additive kernel gives the exact kernel of its
positive semiring lift. The two-order input is instantiated by proofs. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section3.GammaParameters SpecialTransformations.Section5 SpecialTransformations.Section7
open IntegrationInACVF.Section6 IntegrationInACVF.Section6.FiniteRV
namespace DiamondIntegral.Section5
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {κ : Cardinal}
variable (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
  (h00 : M ⊨ Axioms.ACVF00) (hr : Cardinal.mk B.real < κ) (FBase : VFFieldBase B.real)
  (hγ : Cardinal.mk B.gamma < κ) (δ : Values.Gamma (M := M)) (hδ : δ∈B.gamma) (hδ1 : 1<δ)
  (hB : VFGammaGeneratedBase B)
local instance : Fact (B.real ⊆ (Set.univ : Set M)) := ⟨Set.subset_univ _⟩
local notation "SS" => gammaVFAllCommSemiring hκ.le hs h00 hr FBase hγ δ hδ hδ1
  (completed_section5_input hκ.le hs) hB

def completed18NativeVFForgetInvariant :
    letI := SS
    PositiveGrothendieck.Invariant (gammaVFAllPositivePresentation B)
      (R := GammaVFAllAdditiveKPlus B) := by
  letI := SS
  exact {
    toFun A := PositiveAdditiveGrothendieck.of (gammaVFAllAdditivePresentation B) A
    iso h := PositiveAdditiveGrothendieck.of_iso _ h
    empty := PositiveAdditiveGrothendieck.of_empty _
    unit := rfl
    product A C := (gammaVFProductBilinear_class A C).symm
    scissor h := PositiveAdditiveGrothendieck.of_scissor _ h }

def completed18NativeVFForget :
    letI := SS
    GammaVFAllKPlus B →+* GammaVFAllAdditiveKPlus B := by
  letI := SS
  exact PositiveGrothendieck.lift (gammaVFAllPositivePresentation B)
    (completed18NativeVFForgetInvariant hκ hs h00 hr FBase hγ δ hδ hδ1 hB)

theorem completed18NativeVFForget_class (A : GammaVFAllFiniteObject B) :
    letI := SS
    completed18NativeVFForget hκ hs h00 hr FBase hγ δ hδ hδ1 hB (completed18VFClass A)=
      PositiveAdditiveGrothendieck.of (gammaVFAllAdditivePresentation B) A := by
  letI := SS
  exact PositiveGrothendieck.lift_of _ _ A

theorem completed18NativeVFForget_lift (x : GammaNonzeroGradedAt (B := B) (S := Set.univ)) :
    letI := SS
    completed18NativeVFForget hκ hs h00 hr FBase hγ δ hδ hδ1 hB
      (gammaNonzeroGlobalLiftAt hκ.le hs h00 hr hB x)=
    gammaNonzeroGlobalAdditiveLiftAt hκ.le hs h00 hr hB x := by
  letI := SS
  induction x using DirectSum.induction_on with
  | zero => simp only [map_zero]
  | of k a =>
    obtain ⟨U,hu,hU⟩ := a.property
    have ha : a=gammaNonzeroClassAt U hU := Subtype.ext hu.symm
    subst a
    change completed18NativeVFForget hκ hs h00 hr FBase hγ δ hδ hδ1 hB
      (gammaNonzeroGlobalLiftAt hκ.le hs h00 hr hB (gammaNonzeroGradedClassAt U hU))=_
    rw [gammaNonzeroGlobalLiftAt_class]
    unfold gammaAllLiftClass
    rw [completed18NativeVFForget_class]
    change _=gammaNonzeroGlobalAdditiveLiftAt hκ.le hs h00 hr hB
      (DirectSum.of (GammaNonzeroClassesAt (B := B) (S := Set.univ)) k (gammaNonzeroClassAt U hU))
    rw [gammaNonzeroGlobalAdditiveLiftAt,DirectSum.toAddMonoid_of]
    exact (gammaAllAdditiveLiftClassesAt_class hκ.le hs h00 hr hB U).symm
  | add x y hx hy =>
    let F := completed18NativeVFForget hκ hs h00 hr FBase hγ δ hδ hδ1 hB
    let L := gammaNonzeroGlobalLiftAt (S := Set.univ) hκ.le hs h00 hr hB
    let A := gammaNonzeroGlobalAdditiveLiftAt (S := Set.univ) hκ.le hs h00 hr hB
    exact (congrArg F (L.map_add x y)).trans
      ((F.map_add (L x) (L y)).trans ((congrArg₂ (· + ·) hx hy).trans (A.map_add x y).symm))

include FBase hγ δ hδ hδ1 in
theorem completed18NativePositiveLift_kernel :
    ringConGen (gammaNonzeroBasicRelation (B := B))=
      RingCon.ker (gammaNonzeroGlobalLiftAt (S := Set.univ) hκ.le hs h00 hr hB) := by
  letI := SS
  have he : gammaNonzeroIspRingCon (B := B) hκ.le hs h00 hr=
      ringConGen (gammaNonzeroBasicRelation (B := B)) :=
    (gammaNonzeroIspRingCon_eq_union hκ.le hs h00 hr FBase hγ δ hδ hδ1
      (completed_section5_input hκ.le hs) hB).trans
    (gammaNonzeroIsp_eq_basic hκ.le hs h00 hr FBase hγ δ hδ hδ1
      (completed_section5_input hκ.le hs) hB)
  apply le_antisymm
  · rw [← he]
    exact gammaNonzeroIspRingCon_le_lift_kernel hκ.le hs h00 hr hB
  · intro x y hxy
    change gammaNonzeroGlobalLiftAt hκ.le hs h00 hr hB x=
      gammaNonzeroGlobalLiftAt hκ.le hs h00 hr hB y at hxy
    have ha := congrArg (completed18NativeVFForget hκ hs h00 hr FBase hγ δ hδ hδ1 hB) hxy
    rw [completed18NativeVFForget_lift,completed18NativeVFForget_lift] at ha
    have hb : gammaNonzeroIspUnionRingCon hκ.le hs h00 hr FBase hγ δ hδ hδ1
        (completed_section5_input hκ.le hs) hB x y := by
      change gammaNonzeroIspUnionAddCon hκ.le hs h00 hr FBase hγ δ hδ hδ1
        (completed_section5_input hκ.le hs) hB x y
      rw [gammaNonzeroIspUnionAddCon_eq_lift_kernel]
      exact ha
    rw [gammaNonzeroIsp_eq_basic] at hb
    exact hb

end DiamondIntegral.Section5
