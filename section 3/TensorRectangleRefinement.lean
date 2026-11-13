import «section 3».TensorProductCuts
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section3.GammaParameters
open scoped TensorProduct
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {r n : ℕ}

/-- Product subpieces of a fixed labelled RES coefficient. -/
structure GammaGroundTensorRectangle (X : GammaGroundRESObject hc B r) (n : ℕ) where
  residueDomain : GammaGroundDefSet hc B (rawRVSpace X.obj.arity)
  residue_subset : residueDomain.carrier ⊆ X.obj.domain.carrier
  gammaDomain : GammaGroundGammaPiece hc B n

namespace GammaGroundTensorRectangle
variable {X : GammaGroundRESObject hc B r}

def residueObject (R : GammaGroundTensorRectangle X n) := X.restrict R.residueDomain R.residue_subset

def value (R : GammaGroundTensorRectangle X n) : GammaGroundUnmeasuredPositiveTensor hc B :=
  gammaGroundRESDirectSumClass R.residueObject ⊗ₜ[GammaGroundFiniteGammaPositiveSemiring hc B]
    gammaGroundGammaSemiringClass (GammaGroundGammaObject.single R.gammaDomain)

def source (R : GammaGroundTensorRectangle X n) :=
  R.residueDomain.prod (gammaGroundRVUnitGammaPreimage R.gammaDomain)

def inside (R : GammaGroundTensorRectangle X n)
    (A : GammaGroundDefSet hc B (rawRVSpace X.obj.arity)) (H : GammaGroundGammaPiece hc B n) :
    GammaGroundTensorRectangle X n :=
  ⟨R.residueDomain.inter A,fun _ h => R.residue_subset h.1,R.gammaDomain.inter H⟩

def outsideGamma (R : GammaGroundTensorRectangle X n)
    (A : GammaGroundDefSet hc B (rawRVSpace X.obj.arity)) (H : GammaGroundGammaPiece hc B n) :
    GammaGroundTensorRectangle X n :=
  ⟨R.residueDomain.inter A,fun _ h => R.residue_subset h.1,R.gammaDomain.sdiff (R.gammaDomain.inter H)⟩

def outsideResidue (R : GammaGroundTensorRectangle X n)
    (A : GammaGroundDefSet hc B (rawRVSpace X.obj.arity)) : GammaGroundTensorRectangle X n :=
  ⟨R.residueDomain.sdiff (R.residueDomain.inter A),fun _ h => R.residue_subset h.1,R.gammaDomain⟩

def split (R : GammaGroundTensorRectangle X n)
    (A : GammaGroundDefSet hc B (rawRVSpace X.obj.arity)) (H : GammaGroundGammaPiece hc B n) :
    List (GammaGroundTensorRectangle X n) := [R.inside A H,R.outsideGamma A H,R.outsideResidue A]

theorem value_split (R : GammaGroundTensorRectangle X n)
    (A : GammaGroundDefSet hc B (rawRVSpace X.obj.arity)) (H : GammaGroundGammaPiece hc B n) :
    R.value = ((R.split A H).map value).sum := by
  have hp := gammaGroundUnmeasuredTensor_product_cut R.residueObject
    (R.residueDomain.inter A) (fun _ h => h.1) R.gammaDomain (R.gammaDomain.inter H) (fun _ h => h.1)
  have ha : gammaGroundRESDirectSumClass
      (R.residueObject.restrict (R.residueDomain.inter A) (fun _ h => h.1)) =
      gammaGroundRESDirectSumClass (R.inside A H).residueObject :=
    gammaGroundRESDirectSumClass_bijection _ _ (GammaGroundBijection.id _)
  have hd : gammaGroundRESDirectSumClass
      (R.residueObject.restrict (R.residueObject.obj.domain.sdiff (R.residueDomain.inter A)) (fun _ h => h.1)) =
      gammaGroundRESDirectSumClass (R.outsideResidue A).residueObject :=
    gammaGroundRESDirectSumClass_bijection _ _ (GammaGroundBijection.id _)
  rw [ha,hd] at hp
  simpa only [value,split,inside,outsideGamma,outsideResidue,residueObject,
    List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,add_assoc] using hp

theorem split_source_subset (R : GammaGroundTensorRectangle X n)
    (A : GammaGroundDefSet hc B (rawRVSpace X.obj.arity)) (H : GammaGroundGammaPiece hc B n)
    {D : GammaGroundTensorRectangle X n} (hD : D ∈ R.split A H) : D.source.carrier ⊆ R.source.carrier := by
  simp only [split,List.mem_cons,List.not_mem_nil,or_false] at hD
  rcases hD with rfl | rfl | rfl
  · exact fun _ h => ⟨h.1.1,h.2.1⟩
  · exact fun _ h => ⟨h.1.1,h.2.1⟩
  · exact fun _ h => ⟨h.1.1,h.2⟩

theorem split_source_cover (R : GammaGroundTensorRectangle X n)
    (A : GammaGroundDefSet hc B (rawRVSpace X.obj.arity)) (H : GammaGroundGammaPiece hc B n)
    (z : ((rawRVSpace (M := M) X.obj.arity).prod (rawRVUnitSpace n)).Carrier) :
    z ∈ R.source.carrier ↔ ∃ D ∈ R.split A H, z ∈ D.source.carrier := by
  constructor
  · rintro ⟨ha,hu⟩
    by_cases hA : z.1 ∈ A.carrier
    · by_cases hH : rvUnitTupleValues z.2 ∈ H.carrier
      · exact ⟨R.inside A H,by simp only [split,List.mem_cons,true_or],⟨ha,hA⟩,hu,hH⟩
      · exact ⟨R.outsideGamma A H,by simp only [split,List.mem_cons,true_or,or_true],
          ⟨ha,hA⟩,hu,fun h => hH h.2⟩
    · exact ⟨R.outsideResidue A,by simp only [split,List.mem_cons,true_or,or_true],
        ⟨ha,fun h => hA h.2⟩,hu⟩
  · rintro ⟨D,hD,hz⟩
    exact R.split_source_subset A H hD hz

theorem split_pairwise_disjoint (R : GammaGroundTensorRectangle X n)
    (A : GammaGroundDefSet hc B (rawRVSpace X.obj.arity)) (H : GammaGroundGammaPiece hc B n) :
    (R.split A H).Pairwise (fun D E => Disjoint D.source.carrier E.source.carrier) := by
  simp only [split,List.pairwise_cons,List.Pairwise.nil,List.mem_cons,List.not_mem_nil,or_false]
  refine ⟨?_,?_,?_,trivial⟩
  · intro E hE
    rcases hE with rfl | rfl
    · exact Set.disjoint_left.mpr (fun z h1 h2 => h2.2.2 h1.2)
    · exact Set.disjoint_left.mpr (fun z h1 h2 => h2.1.2 h1.1)
  · intro E hE
    cases hE
    exact Set.disjoint_left.mpr (fun z h1 h2 => h2.1.2 h1.1)
  · intro E hE
    exact False.elim hE

/-- Apply finitely many rectangular cuts. All leaves are retained as
positive terms, including empty ones. -/
def refine (l : List ((GammaGroundDefSet hc B (rawRVSpace X.obj.arity)) × GammaGroundGammaPiece hc B n))
    (R : GammaGroundTensorRectangle X n) : List (GammaGroundTensorRectangle X n) :=
  match l with
  | [] => [R]
  | (A,H)::l => (R.split A H).flatMap (refine l)

theorem refine_source_subset
    (l : List ((GammaGroundDefSet hc B (rawRVSpace X.obj.arity)) × GammaGroundGammaPiece hc B n))
    (R : GammaGroundTensorRectangle X n) {D : GammaGroundTensorRectangle X n}
    (hD : D ∈ R.refine l) : D.source.carrier ⊆ R.source.carrier := by
  induction l generalizing R with
  | nil =>
    have he : D = R := by simpa only [refine,List.mem_singleton] using hD
    subst D
    exact Set.Subset.rfl
  | cons P l ih =>
    obtain ⟨E,hE,hDE⟩ := List.mem_flatMap.mp hD
    exact (ih E hDE).trans (R.split_source_subset P.1 P.2 hE)

theorem refine_source_cover
    (l : List ((GammaGroundDefSet hc B (rawRVSpace X.obj.arity)) × GammaGroundGammaPiece hc B n))
    (R : GammaGroundTensorRectangle X n)
    (z : ((rawRVSpace (M := M) X.obj.arity).prod (rawRVUnitSpace n)).Carrier) :
    z ∈ R.source.carrier ↔ ∃ D ∈ R.refine l, z ∈ D.source.carrier := by
  induction l generalizing R with
  | nil => simp only [refine,List.mem_singleton,exists_eq_left]
  | cons P l ih =>
    constructor
    · intro hz
      obtain ⟨E,hE,hzE⟩ := (R.split_source_cover P.1 P.2 z).mp hz
      obtain ⟨D,hD,hzD⟩ := (ih E).mp hzE
      exact ⟨D,List.mem_flatMap.mpr ⟨E,hE,hD⟩,hzD⟩
    · rintro ⟨D,hD,hzD⟩
      exact R.refine_source_subset (P::l) hD hzD

theorem value_refine
    (l : List ((GammaGroundDefSet hc B (rawRVSpace X.obj.arity)) × GammaGroundGammaPiece hc B n))
    (R : GammaGroundTensorRectangle X n) : R.value = ((R.refine l).map value).sum := by
  induction l generalizing R with
  | nil => exact (add_zero R.value).symm
  | cons P l ih =>
    have hf (q : List (GammaGroundTensorRectangle X n)) :
        ((q.flatMap (refine l)).map value).sum = (q.map value).sum := by
      induction q with
      | nil => rfl
      | cons E q hq =>
        simp only [List.flatMap_cons,List.map_append,List.sum_append,List.map_cons,List.sum_cons]
        rw [← ih E,hq]
    exact (R.value_split P.1 P.2).trans (hf (R.split P.1 P.2)).symm

private theorem pairwise_flatMap_subpieces
    (q : List (GammaGroundTensorRectangle X n))
    (F : GammaGroundTensorRectangle X n → List (GammaGroundTensorRectangle X n))
    (hq : q.Pairwise (fun D E => Disjoint D.source.carrier E.source.carrier))
    (hF : ∀ R ∈ q, (F R).Pairwise (fun D E => Disjoint D.source.carrier E.source.carrier))
    (hsub : ∀ R ∈ q, ∀ D ∈ F R, D.source.carrier ⊆ R.source.carrier) :
    (q.flatMap F).Pairwise (fun D E => Disjoint D.source.carrier E.source.carrier) := by
  induction q with
  | nil => exact List.Pairwise.nil
  | cons R q ih =>
    obtain ⟨hRq,hq⟩ := List.pairwise_cons.mp hq
    rw [List.flatMap_cons,List.pairwise_append]
    refine ⟨hF R (List.mem_cons_self ..),ih hq ?_ ?_,?_⟩
    · exact fun E hE => hF E (List.mem_cons_of_mem R hE)
    · exact fun E hE D hD => hsub E (List.mem_cons_of_mem R hE) D hD
    · intro D hD E hE
      obtain ⟨R',hR',hE⟩ := List.mem_flatMap.mp hE
      exact (hRq R' hR').mono (hsub R (List.mem_cons_self ..) D hD)
        (hsub R' (List.mem_cons_of_mem R hR') E hE)

theorem refine_pairwise_disjoint
    (l : List ((GammaGroundDefSet hc B (rawRVSpace X.obj.arity)) × GammaGroundGammaPiece hc B n))
    (R : GammaGroundTensorRectangle X n) :
    (R.refine l).Pairwise (fun D E => Disjoint D.source.carrier E.source.carrier) := by
  induction l generalizing R with
  | nil => exact List.pairwise_singleton _ R
  | cons P l ih =>
    exact pairwise_flatMap_subpieces (R.split P.1 P.2) (refine l) (R.split_pairwise_disjoint P.1 P.2)
      (fun E _ => ih E) (fun E _ D hD => E.refine_source_subset l hD)

theorem split_decides_patch (R : GammaGroundTensorRectangle X n)
    (A : GammaGroundDefSet hc B (rawRVSpace X.obj.arity)) (H : GammaGroundGammaPiece hc B n)
    {D : GammaGroundTensorRectangle X n} (hD : D ∈ R.split A H) :
    D.source.carrier ⊆ (A.prod (gammaGroundRVUnitGammaPreimage H)).carrier ∨
      Disjoint D.source.carrier (A.prod (gammaGroundRVUnitGammaPreimage H)).carrier := by
  simp only [split,List.mem_cons,List.not_mem_nil,or_false] at hD
  rcases hD with rfl | rfl | rfl
  · exact Or.inl (fun _ h => ⟨h.1.2,h.2.2⟩)
  · exact Or.inr (Set.disjoint_left.mpr (fun z hD hP => hD.2.2 ⟨hD.2.1,hP.2⟩))
  · exact Or.inr (Set.disjoint_left.mpr (fun z hD hP => hD.1.2 ⟨hD.1.1,hP.1⟩))

/-- Each final product leaf is either wholly within or disjoint from
each prescribed patch. Combined with value_refine, this is a finite
positive common refinement of the original product. -/
theorem refine_decides_patches
    (l : List ((GammaGroundDefSet hc B (rawRVSpace X.obj.arity)) × GammaGroundGammaPiece hc B n))
    (R : GammaGroundTensorRectangle X n) {D : GammaGroundTensorRectangle X n}
    (hD : D ∈ R.refine l) :
    ∀ P ∈ l, D.source.carrier ⊆ (P.1.prod (gammaGroundRVUnitGammaPreimage P.2)).carrier ∨
      Disjoint D.source.carrier (P.1.prod (gammaGroundRVUnitGammaPreimage P.2)).carrier := by
  induction l generalizing R with
  | nil => intro P hP; exact False.elim (List.not_mem_nil hP)
  | cons P l ih =>
    obtain ⟨E,hE,hDE⟩ := List.mem_flatMap.mp hD
    have hsub := E.refine_source_subset l hDE
    intro Q hQ
    rcases List.mem_cons.mp hQ with hQP | hQ
    · subst Q
      rcases R.split_decides_patch P.1 P.2 hE with hin | hout
      · exact Or.inl (hsub.trans hin)
      · exact Or.inr (hout.mono_left hsub)
    · exact ih E hDE Q hQ
end GammaGroundTensorRectangle
end DiamondIntegral.Section3
