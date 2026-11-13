import «section 3».RVUnitPresentationBridge
import «section 3».RVAngularQuotient
import «section 3».GammaGroundRVNonzeroTargets
import «section 3».GammaGroundRESScissors
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : GammaParameters.Base (M := M)} {n k : ℕ}

def gammaGroundRVUnitToRVMap (R : GammaGroundDefSet hc B (rawRVUnitSpace (M := M) n)) :
    GammaGroundMap R (GammaGroundDefSet.univ hc B (rawRVSpace n)) :=
  GammaGroundMap.ofGlobal _ _ (rvUnitToRVMap (DefSet.univ (rawRVUnitSpace n) B.real))
    (fun _ => Set.mem_univ _)

theorem gammaGroundRVUnitToRVMap_injective (R : GammaGroundDefSet hc B (rawRVUnitSpace (M := M) n)) :
    Function.Injective (gammaGroundRVUnitToRVMap R) := by
  intro x y he
  apply Subtype.ext
  funext i
  apply Units.ext
  exact congrArg (fun z : GammaGroundDefSet.univ hc B (rawRVSpace n) => z.val i) he

def gammaGroundRVUnitPresentationBijection (R : GammaGroundDefSet hc B (rawRVUnitSpace (M := M) n)) :
    GammaGroundBijection R (gammaGroundRVUnitToRVMap R).image :=
  ⟨(gammaGroundRVUnitToRVMap R).toImage,
    (gammaGroundRVUnitToRVMap R).toImage_bijective (gammaGroundRVUnitToRVMap_injective R)⟩

/-- Finite residue value support and a pointwise rank bound construct an
actual RES[k] object with a nonzero finite-to-one label over the same base. -/
theorem gammaGroundRVUnit_RES_of_rank_bound
    (hex : RVExchangeInput (M := M)) {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (hsmall : Cardinal.mk B.real < κ)
    (R : GammaGroundDefSet hc B (rawRVUnitSpace (M := M) n))
    (hR : (rvUnitTupleValues '' R.carrier).Finite)
    (hrank : ∀ r : R, rvTupleRank hc hex B.real (fun i => (r.val i : CanonicalRV.RVSort M)) ≤ k) :
    ∃ U : GammaGroundRESObject hc B k, Nonempty (GammaGroundBijection R U.obj.domain) := by
  let e := gammaGroundRVUnitPresentationBijection R
  let I := (gammaGroundRVUnitToRVMap R).image
  have hI : ∀ a : I, rvTupleRank hc hex B.real a.val ≤ k := by
    intro a
    obtain ⟨r,rfl⟩ := e.bijective.2 a
    exact hrank r
  obtain ⟨g,hg⟩ := gammaGroundRVFiniteMap_of_point_rank hex hκ hs hsmall I k hI
  obtain ⟨f,hf,hNZ⟩ := (gammaGroundRVHasFiniteMap_iff_nonzero I).mp ⟨g,hg⟩
  let U : GammaGroundRVObject hc B k := ⟨n,I,f,hf,hNZ⟩
  have hres : gammaGroundResProperty U := by
    apply (hR.image (fun γ => fun i => (γ i).val)).subset
    rintro v ⟨t,⟨r,he⟩,rfl⟩
    refine ⟨rvUnitTupleValues r.val,⟨r.val,r.property,rfl⟩,?_⟩
    rw [← he]
    rfl
  exact ⟨⟨U,hres⟩,⟨e⟩⟩
end DiamondIntegral.Section3
