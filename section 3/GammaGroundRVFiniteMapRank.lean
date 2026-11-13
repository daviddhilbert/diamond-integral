import Section4.GammaRVIndependence
import Section3.GammaProjection
import «section 3».GammaGroundRealFibres
import «section 3».GammaGroundMapImages
import «section 3».GammaGroundRawDescent
import «section 3».GammaGroundSyntaxBridge
import Section4.RelationFibres
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {ground : GammaParameters.Base (M := M)}
variable {P Q : Space LRV M}
variable {n m : ℕ}

def gammaGroundRVCoordinateSet (A : GammaGroundDefSet hc ground (rawRVSpace (M := M) n))
    (i : Fin n) : Set M := {x | ∃ a : A, (a.val i).val = x}

theorem gammaGroundRVCoordinateSet_definable (A : GammaGroundDefSet hc ground (rawRVSpace (M := M) n))
    (i : Fin n) : GammaParameters.DefinableAtBase ground .rv (gammaGroundRVCoordinateSet A i) := by
  have h := A.definable.toRVBase.image_real (fun _ : Fin 1 => i)
  change GammaParameters.DefinableOverBase ground (fun _ : Fin 1 => .rv) {z | z 0 ∈ gammaGroundRVCoordinateSet A i}
  have he : ((fun x : Fin n → M => x ∘ (fun _ : Fin 1 => i)) '' (rvValues '' A.carrier)) =
      {z : Fin 1 → M | z 0 ∈ gammaGroundRVCoordinateSet A i} := by
    ext z
    constructor
    · rintro ⟨t, ⟨a, ha, rfl⟩, he⟩
      exact ⟨⟨a, ha⟩, congrFun he 0⟩
    · rintro ⟨a, he⟩
      refine ⟨rvValues a.val, ⟨a.val, a.property, rfl⟩, ?_⟩
      funext j
      fin_cases j
      exact he
  rw [he] at h
  exact h

theorem gammaGroundRVCoordinateSet_finite (A : GammaGroundDefSet hc ground (rawRVSpace (M := M) n))
    (hA : A.carrier.Finite) (i : Fin n) : (gammaGroundRVCoordinateSet A i).Finite := by
  apply (hA.image (fun t => (t i).val)).subset
  rintro x ⟨a, he⟩
  exact ⟨a.val, a.property, he⟩

theorem gammaGroundFiniteMapRVCoordinateAlgebraic
    {A : GammaGroundDefSet hc ground (rawRVSpace (M := M) n)}
    {B : GammaGroundDefSet hc ground (rawRVSpace (M := M) m)}
    (f : GammaGroundMap A B) (hf : f.FiniteFibres) (a : A) (i : Fin n) :
    GammaParameters.AlgebraicAtBase
      ⟨ground.real ∪ Set.range (rvValues (f a).val), ground.gamma⟩ .rv (a.val i).val := by
  let c : (rawRVSpace (M := M) m).domain := ⟨rvValues (f a).val, ⟨(f a).val, rfl⟩⟩
  let F := f.fibre (f a) c (decode_rvValues (f a).val)
  exact ⟨gammaGroundRVCoordinateSet F i, gammaGroundRVCoordinateSet_definable F i,
    gammaGroundRVCoordinateSet_finite F (f.fibre_finite hf (f a) c (decode_rvValues (f a).val)) i,
    ⟨⟨a.val, ⟨a, rfl, rfl⟩⟩, rfl⟩⟩

theorem gammaGroundRVTupleRank_le_of_finite_map
    (hex : RVExchangeInput (M := M)) {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hγ : GammaRVAlgebraicityInput (M := M) κ) (hS : Cardinal.mk ground.real < κ)
    {A : GammaGroundDefSet hc ground (rawRVSpace (M := M) n)}
    {B : GammaGroundDefSet hc ground (rawRVSpace (M := M) m)}
    (f : GammaGroundMap A B) (hf : f.FiniteFibres) (a : A) :
    rvTupleRank hc hex ground.real a.val ≤ rvTupleRank hc hex ground.real (f a).val := by
  apply rvTupleRank_le_of_algebraic hc hex ground.real (f a).val a.val
  intro i
  exact (hγ _ (small_union_range hκ ground.real hS (rvValues (f a).val)) _).mp
    (gammaGroundFiniteMapRVCoordinateAlgebraic f hf a i)

end DiamondIntegral.Section3
