import «section 5».RelativeRVFamilyPresentation
import «section 5».OriginalRVRowProducts
import «section 3».GammaGroundEmptyBijections

/-! Actual bijections over every displayed RV parameter define the
relative positive presentation. Canonical products share that parameter. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace DiamondIntegral.Section5
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section3.GammaParameters
open IntegrationInACVF.Section6
open DiamondIntegral.Section3 DiamondIntegral.Section4
open SpecialTransformations.Section4.PositiveAdditiveGrothendieck
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {p : ℕ}

def RelativeRVFamily.blockProduct (F G : RelativeRVFamily B p) : RelativeRVFamily B p :=
  ⟨F.1+G.1,originalDomainProduct F.2 G.2⟩

def relativePointwiseIso
    (X : GammaGroundDefSet hc B (rawRVSpace (M := M) p)) (F G : RelativeRVFamily B p) : Prop :=
  ∀ x : X, Nonempty (GammaGroundBijection
    (originalRVRowDomain hc F.2 (rvValues x.val)) (originalRVRowDomain hc G.2 (rvValues x.val)))

def relativePointPresentation
    (X : GammaGroundDefSet hc B (rawRVSpace (M := M) p)) : Presentation (RelativeRVFamily B p) where
  iso := relativePointwiseIso X
  empty := RelativeRVFamily.empty B p
  scissor F G H I := F = H.sum I ∧ G = RelativeRVFamily.empty B p

theorem relativePointClass_sum
    (X : GammaGroundDefSet hc B (rawRVSpace (M := M) p)) (F G : RelativeRVFamily B p) :
    of (relativePointPresentation X) (F.sum G) =
      of (relativePointPresentation X) F + of (relativePointPresentation X) G := by
  have h := of_scissor (relativePointPresentation X)
    (a := F.sum G) (b := RelativeRVFamily.empty B p) (c := F) (d := G) ⟨rfl,rfl⟩
  have he : of (relativePointPresentation X) (RelativeRVFamily.empty B p) = 0 :=
    of_empty (relativePointPresentation X)
  simpa only [he,add_zero] using h

def originalRVRowProductPairBijection (F G : RelativeRVFamily B p) (z : Fin p → M) :
    GammaGroundBijection (originalRVRowDomain hc (F.blockProduct G).2 z)
      ((originalRVRowDomain hc F.2 z).prod (originalRVRowDomain hc G.2 z)) :=
  (gammaGroundRVPackBijection _ _).symm.comp (originalRVRowProductBijection F.2 G.2 z)

theorem relativePointwiseIso_product
    {X : GammaGroundDefSet hc B (rawRVSpace (M := M) p)} {F G H I : RelativeRVFamily B p}
    (f : relativePointwiseIso X F G) (g : relativePointwiseIso X H I) :
    relativePointwiseIso X (F.blockProduct H) (G.blockProduct I) := by
  intro x
  obtain ⟨a⟩ := f x
  obtain ⟨b⟩ := g x
  exact ⟨(originalRVRowProductPairBijection G I _).symm.comp
    ((a.prodMap b).comp (originalRVRowProductPairBijection F H _))⟩

theorem relativePointwiseIso_refl
    (X : GammaGroundDefSet hc B (rawRVSpace (M := M) p)) (F : RelativeRVFamily B p) :
    relativePointwiseIso X F F := fun _ => ⟨GammaGroundBijection.id _⟩

theorem relativePointwiseIso_product_comm
    (X : GammaGroundDefSet hc B (rawRVSpace (M := M) p)) (F G : RelativeRVFamily B p) :
    relativePointwiseIso X (F.blockProduct G) (G.blockProduct F) := by
  intro x
  exact ⟨(originalRVRowProductPairBijection G F _).symm.comp
    ((GammaGroundBijection.prodSwap _ _).comp (originalRVRowProductPairBijection F G _))⟩

theorem relativePointwiseIso_product_assoc
    (X : GammaGroundDefSet hc B (rawRVSpace (M := M) p)) (F G H : RelativeRVFamily B p) :
    relativePointwiseIso X ((F.blockProduct G).blockProduct H) (F.blockProduct (G.blockProduct H)) := by
  intro x
  let z := rvValues x.val
  let A := originalRVRowDomain hc F.2 z
  let C := originalRVRowDomain hc G.2 z
  let D := originalRVRowDomain hc H.2 z
  let f := originalRVRowProductPairBijection (hc := hc) F G z
  let g := originalRVRowProductPairBijection (hc := hc) G H z
  exact ⟨(originalRVRowProductPairBijection F (G.blockProduct H) z).symm.comp
    (((GammaGroundBijection.id A).prodMap g.symm).comp
      ((GammaGroundBijection.prodAssoc A C D).comp
        ((f.prodMap (GammaGroundBijection.id D)).comp
          (originalRVRowProductPairBijection (F.blockProduct G) H z))))⟩

theorem relativePointwiseIso_product_empty
    (X : GammaGroundDefSet hc B (rawRVSpace (M := M) p)) (F : RelativeRVFamily B p) :
    relativePointwiseIso X (F.blockProduct (RelativeRVFamily.empty B p)) (RelativeRVFamily.empty B p) := by
  intro x
  apply Nonempty.intro
  apply GammaGroundBijection.ofEmpty
  · ext u
    change (Fin.append (rvValues x.val) (rvValues u) ∈
      (originalDomainProduct F.2 (RelativeRVFamily.empty B p).2).val) ↔ False
    rw [originalDomainProduct_row]
    constructor
    · exact fun h => h.2
    · exact False.elim
  · rfl

theorem relativePointwiseIso_product_one
    (X : GammaGroundDefSet hc B (rawRVSpace (M := M) p)) (F : RelativeRVFamily B p) :
    relativePointwiseIso X ((RelativeRVFamily.one B p).blockProduct F) F := by
  intro x
  let A := originalRVRowDomain hc (RelativeRVFamily.one B p).2 (rvValues x.val)
  let C := originalRVRowDomain hc F.2 (rvValues x.val)
  have ha : (Fin.elim0 : Fin 0 → CanonicalRV.RVSort M) ∈ A.carrier := by
    change Fin.append (rvValues x.val) (rvValues Fin.elim0) ∈
      sortedUniverse (Fin.append (fun _ : Fin p => .rv) (fun _ : Fin 0 => .rv))
    intro i
    refine Fin.addCases (fun j => ?_) (fun j => j.elim0) i
    simpa only [Fin.append_left,sortEval,iRV,rvValues] using (x.val j).property
  let e : GammaGroundBijection (A.prod C) C := {
    map := GammaGroundMap.prodSnd A C
    bijective := ⟨by
      intro u v he
      apply Subtype.ext
      apply Prod.ext
      · change (u.val.1 : Fin 0 → CanonicalRV.RVSort M) = v.val.1
        funext i
        exact i.elim0
      · exact congrArg Subtype.val he,
      fun c => ⟨⟨(Fin.elim0,c.val),ha,c.property⟩,rfl⟩⟩ }
  exact ⟨e.comp (originalRVRowProductPairBijection (RelativeRVFamily.one B p) F (rvValues x.val))⟩

end DiamondIntegral.Section5
