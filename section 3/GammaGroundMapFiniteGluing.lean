import «section 3».GammaGroundFiniteCoverPartition
import «section 3».GammaGroundMapRestrictions
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : GammaParameters.Base (M := M)}
variable {Q R : Space LRV M}

/-- A finite definable partition glues actual map graphs over the same
ground. Its pointwise formula retains all source and target data. -/
theorem gammaGroundMap_of_finite_partition {ι : Type} [Finite ι]
    (A : GammaGroundDefSet hc B Q) (D : GammaGroundDefSet hc B R)
    (P : ι → GammaGroundDefSet hc B Q) (hP : ∀ i, (P i).carrier ⊆ A.carrier)
    (hcover : ∀ a : A, ∃! i, a.val ∈ (P i).carrier)
    (f : ∀ i, GammaGroundMap (P i) D) :
    ∃ F : GammaGroundMap A D, ∀ i (a : A) (ha : a.val ∈ (P i).carrier),
      F a = f i ⟨a.val,ha⟩ := by
  choose index hindex using fun a : A => ExistsUnique.exists (hcover a)
  let F : A → D := fun a => f (index a) ⟨a.val,hindex a⟩
  have hvalue (i : ι) (a : A) (ha : a.val ∈ (P i).carrier) :
      F a = f i ⟨a.val,ha⟩ := by
    have he : index a = i := (hcover a).unique (hindex a) ha
    subst i
    rfl
  have hgraph := GammaGroundDefinable.iUnion (fun i => (f i).graph_definable)
  have hFG : GammaGroundDefinable hc B (Q.prod R)
      {z | ∃ a : A, a.val = z.1 ∧ (F a).val = z.2} := by
    apply hgraph.congr
    intro z
    constructor
    · intro hz
      obtain ⟨i,u,hu,hf⟩ := Set.mem_iUnion.mp hz
      let a : A := ⟨u.val,hP i u.property⟩
      refine ⟨a,hu,?_⟩
      exact (congrArg Subtype.val (hvalue i a u.property)).trans hf
    · rintro ⟨a,ha,hf⟩
      exact Set.mem_iUnion.mpr ⟨index a,⟨a.val,hindex a⟩,ha,hf⟩
  exact ⟨⟨F,hFG⟩,hvalue⟩

end DiamondIntegral.Section3
