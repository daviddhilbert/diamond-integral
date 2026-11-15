import «section 5».RVGammaFamilySchemata
import «section 5».NativeGammaTupleTorsors

/-! A mixed RV/Gamma family lifts to literal nonzero RV tuples, keeping
all representatives of every value coordinate. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace DiamondIntegral.Section5
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section3.GammaParameters
open DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {p n : ℕ}

def unitMixedGammaMap (hc : CanonicalStructure.IsCanonical (M := M)) (S : Set M) (p n : ℕ) :
    Map (DefSet.univ (rawRVUnitSpace (M := M) (p+n)) S)
      (DefSet.univ ((rawRVUnitSpace p).prod ((volumeGammaSpace hc).power (Fin n))) S) := by
  let F (z : Fin (p+n) → M) : Fin p ⊕ (Fin n × Fin 1) → M :=
    Sum.elim (fun i => z (Fin.castAdd n i)) (fun ij => z (Fin.natAdd p ij.1))
  have hpz (c : (rawRVUnitSpace (M := M) (p+n)).domain) : ∀ i, NonzeroRV (c.val i) :=
    (Set.ext_iff.mp rvUnitValues_range c.val).mp c.property
  have hdom (c : (rawRVUnitSpace (M := M) (p+n)).domain) :
      F c.val ∈ ((rawRVUnitSpace p).prod ((volumeGammaSpace hc).power (Fin n))).domain := by
    refine ⟨?_,fun j => hpz c (Fin.natAdd p j)⟩
    exact (Set.ext_iff.mp rvUnitValues_range _).mpr (fun i => hpz c (Fin.castAdd n i))
  refine Map.ofCodes _ (fun u => (u ∘ Fin.castAdd n, rvUnitTupleValues (u ∘ Fin.natAdd p))) F
    (fun i => by cases i <;> exact Set.DefinableFun.proj LRV) hdom ?_
  intro c
  apply Prod.ext
  · apply rvUnitValues_injective
    funext i
    have hleft := congrFun (rvUnitValues_decode
      (⟨fun j => c.val (Fin.castAdd n j), (hdom c).1⟩ : (rawRVUnitSpace p).domain)) i
    have hright := congrFun (rvUnitValues_decode c) (Fin.castAdd n i)
    exact hleft.trans hright.symm
  · funext j
    apply Subtype.ext
    change Values.vrv ⟨c.val (Fin.natAdd p j),(hpz c (Fin.natAdd p j)).1⟩ =
      Values.vrv ((((rawRVUnitSpace (p+n)).decode c) (Fin.natAdd p j) : (CanonicalRV.RVSort M)ˣ) : CanonicalRV.RVSort M)
    exact congrArg Values.vrv (Subtype.ext (congrFun (rvUnitValues_decode c) (Fin.natAdd p j)).symm)

def rvGammaFamilyLift
    (T : GammaGroundDefSet hc B ((rawRVUnitSpace (M := M) p).prod ((volumeGammaSpace hc).power (Fin n)))) :
    GammaGroundDefSet hc B (rawRVUnitSpace (M := M) (p+n)) :=
  ⟨{u | (u ∘ Fin.castAdd n, rvUnitTupleValues (u ∘ Fin.natAdd p)) ∈ T.carrier},
    T.definable.preimage (unitMixedGammaMap hc B.real p n)⟩

theorem rvGammaFamilyLift_mem
    (T : GammaGroundDefSet hc B ((rawRVUnitSpace (M := M) p).prod ((volumeGammaSpace hc).power (Fin n))))
    (u : Fin (p+n) → (CanonicalRV.RVSort M)ˣ) :
    u ∈ (rvGammaFamilyLift T).carrier ↔
      (u ∘ Fin.castAdd n, rvUnitTupleValues (u ∘ Fin.natAdd p)) ∈ T.carrier := Iff.rfl

end DiamondIntegral.Section5
