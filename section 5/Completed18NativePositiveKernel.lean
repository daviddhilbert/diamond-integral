import «section 5».Completed18VFComparison
import IntegrationSection6.GammaNonzeroBasicRelation
import Integration7.ClosedSection6GlobalIntegrationSemiringEquivalence
import Integration7.ClosedSection6GammaNonzeroBasicRelation

/-! The completed [18] additive kernel gives the exact kernel of its
positive semiring lift. The published generated-base kernel is used without modifying dependency sources. -/
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

def completed18ClosedVFObject (A : GammaVFAllFiniteObject B) :
    IntegrationInACVF.Section7.CompletedSection6.GammaVFAllFiniteObject B :=
  ⟨A.arity,A.domain,A.definable,A.finiteFibres⟩

variable (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
  (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M)) (hr : Cardinal.mk B.real < κ) (FBase : VFFieldBase B.real)
  (hγ : Cardinal.mk B.gamma < κ) (δ : Values.Gamma (M := M)) (hδ : δ∈B.gamma) (hδ1 : 1<δ)
  (hB : VFGammaGeneratedBase B)
local instance : Fact (B.real ⊆ (Set.univ : Set M)) := ⟨Set.subset_univ _⟩
local notation "SS" => IntegrationInACVF.Section7.CompletedSection6.gammaVFAllCommSemiring hκ.le hs h00 hr FBase hγ δ hδ hδ1
  hc hB

def completed18NativeVFForgetInvariant :
    letI := SS
    PositiveGrothendieck.Invariant (gammaVFAllPositivePresentation B)
      (R := IntegrationInACVF.Section7.CompletedSection6.GammaVFAllAdditiveKPlus B) := by
  letI := SS
  exact {
    toFun A := PositiveAdditiveGrothendieck.of (IntegrationInACVF.Section7.CompletedSection6.gammaVFAllAdditivePresentation B) (completed18ClosedVFObject A)
    iso h := PositiveAdditiveGrothendieck.of_iso _ h
    empty := PositiveAdditiveGrothendieck.of_empty _
    unit := rfl
    product A C := (IntegrationInACVF.Section7.CompletedSection6.gammaVFProductBilinear_class (completed18ClosedVFObject A) (completed18ClosedVFObject C)).symm
    scissor h := PositiveAdditiveGrothendieck.of_scissor _ h }

def completed18NativeVFForget :
    letI := SS
    GammaVFAllKPlus B →+* IntegrationInACVF.Section7.CompletedSection6.GammaVFAllAdditiveKPlus B := by
  letI := SS
  exact PositiveGrothendieck.lift (gammaVFAllPositivePresentation B)
    (completed18NativeVFForgetInvariant hκ hs h00 hc hr FBase hγ δ hδ hδ1 hB)

theorem completed18NativeVFForget_class (A : GammaVFAllFiniteObject B) :
    letI := SS
    completed18NativeVFForget hκ hs h00 hc hr FBase hγ δ hδ hδ1 hB (completed18VFClass A)=
      PositiveAdditiveGrothendieck.of (IntegrationInACVF.Section7.CompletedSection6.gammaVFAllAdditivePresentation B) (completed18ClosedVFObject A) := by
  letI := SS
  exact PositiveGrothendieck.lift_of _ _ A

theorem completed18NativeVFForget_lift (x : GammaNonzeroGradedAt (B := B) (S := Set.univ)) :
    letI := SS
    completed18NativeVFForget hκ hs h00 hc hr FBase hγ δ hδ hδ1 hB
      (gammaNonzeroGlobalLiftAt hκ.le hs h00 hr hB x)=
    IntegrationInACVF.Section7.CompletedSection6.gammaNonzeroGlobalAdditiveLiftAt hκ.le hs h00 hr hB x := by
  letI := SS
  induction x using DirectSum.induction_on with
  | zero => simp only [map_zero]
  | of k a =>
    obtain ⟨U,hu,hU⟩ := a.property
    have ha : a=gammaNonzeroClassAt U hU := Subtype.ext hu.symm
    subst a
    change completed18NativeVFForget hκ hs h00 hc hr FBase hγ δ hδ hδ1 hB
      (gammaNonzeroGlobalLiftAt hκ.le hs h00 hr hB (gammaNonzeroGradedClassAt U hU))=_
    rw [gammaNonzeroGlobalLiftAt_class]
    unfold gammaAllLiftClass
    rw [completed18NativeVFForget_class]
    change _=IntegrationInACVF.Section7.CompletedSection6.gammaNonzeroGlobalAdditiveLiftAt hκ.le hs h00 hr hB
      (DirectSum.of (GammaNonzeroClassesAt (B := B) (S := Set.univ)) k (gammaNonzeroClassAt U hU))
    rw [IntegrationInACVF.Section7.CompletedSection6.gammaNonzeroGlobalAdditiveLiftAt,DirectSum.toAddMonoid_of]
    exact (IntegrationInACVF.Section7.CompletedSection6.gammaAllAdditiveLiftClassesAt_class hκ.le hs h00 hr hB U).symm
  | add x y hx hy =>
    let F := completed18NativeVFForget hκ hs h00 hc hr FBase hγ δ hδ hδ1 hB
    let L := gammaNonzeroGlobalLiftAt (S := Set.univ) hκ.le hs h00 hr hB
    let A := IntegrationInACVF.Section7.CompletedSection6.gammaNonzeroGlobalAdditiveLiftAt (S := Set.univ) hκ.le hs h00 hr hB
    exact (congrArg F (L.map_add x y)).trans
      ((F.map_add (L x) (L y)).trans ((congrArg₂ (· + ·) hx hy).trans (A.map_add x y).symm))

include hc FBase hγ δ hδ hδ1 in
theorem completed18NativePositiveLift_kernel :
    ringConGen (gammaNonzeroBasicRelation (B := B))=
      RingCon.ker (gammaNonzeroGlobalLiftAt (S := Set.univ) hκ.le hs h00 hr hB) := by
  letI := SS
  have he : IntegrationInACVF.Section7.CompletedSection6.gammaNonzeroIspRingCon (B := B) hκ.le hs h00 hr=
      ringConGen (gammaNonzeroBasicRelation (B := B)) :=
    (IntegrationInACVF.Section7.CompletedSection6.gammaNonzeroIspRingCon_eq_union hκ.le hs h00 hr FBase hγ δ hδ hδ1
      hc hB).trans
    (IntegrationInACVF.Section7.CompletedSection6.gammaNonzeroIsp_eq_basic hκ.le hs h00 hr FBase hγ δ hδ hδ1
      hc hB)
  apply le_antisymm
  · rw [← he]
    exact gammaNonzeroIspRingCon_le_lift_kernel hκ.le hs h00 hr hB
  · intro x y hxy
    change gammaNonzeroGlobalLiftAt hκ.le hs h00 hr hB x=
      gammaNonzeroGlobalLiftAt hκ.le hs h00 hr hB y at hxy
    have ha := congrArg (completed18NativeVFForget hκ hs h00 hc hr FBase hγ δ hδ hδ1 hB) hxy
    rw [completed18NativeVFForget_lift,completed18NativeVFForget_lift] at ha
    have hb : IntegrationInACVF.Section7.CompletedSection6.gammaNonzeroIspUnionRingCon hκ.le hs h00 hr FBase hγ δ hδ hδ1
        hc hB x y := by
      change IntegrationInACVF.Section7.CompletedSection6.gammaNonzeroIspUnionAddCon hκ.le hs h00 hr FBase hγ δ hδ hδ1
        hc hB x y
      rw [IntegrationInACVF.Section7.CompletedSection6.gammaNonzeroIspUnionAddCon_eq_lift_kernel]
      exact ha
    rw [IntegrationInACVF.Section7.CompletedSection6.gammaNonzeroIsp_eq_basic] at hb
    exact hb

end DiamondIntegral.Section5
