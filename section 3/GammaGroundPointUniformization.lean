import «section 3».RealTupleParameterAbstraction
import «section 3».GammaGroundFunctionalRelations
import «section 3».GammaGroundRVUnitDomains
import «section 3».ResidueGammaClosureInvariant
import Section3.GammaClosureLaws
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section3.GammaParameters
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)}
variable {Q : Space LRV M} {n m : ℕ}

/-- A point definable after naming a finite real tuple lies on an actual
original-ground definable partial function of that tuple. -/
theorem gammaGroundPoint_realTuple_function {β : Type} [Finite β]
    (r : β → M) (q : Q.Carrier)
    (hq : GammaGroundDefinable hc ⟨B.real ∪ Set.range r,B.gamma⟩ Q {q}) :
    ∃ (A : GammaGroundDefSet hc B (rawTupleSpace LRV M β)) (hr : r ∈ A.carrier)
      (f : GammaGroundMap A (GammaGroundDefSet.univ hc B Q)), (f ⟨r,hr⟩).val = q := by
  obtain ⟨R,hR,hRx⟩ := gammaGroundDefinable_realTuple_abstraction Q r hq
  let D : GammaGroundDefSet hc B ((rawTupleSpace LRV M β).prod Q) := ⟨R,hR⟩
  let A : GammaGroundDefSet hc B (rawTupleSpace LRV M β) :=
    ⟨{p | ∃! v, (p,v) ∈ R},gammaGroundDefinable_unique_fibre hR⟩
  have hr : r ∈ A.carrier := by
    refine ⟨q,(hRx q).mpr rfl,?_⟩
    intro v hv
    exact (hRx v).mp hv
  refine ⟨A,hr,gammaGroundUniqueFibreFunction D,?_⟩
  exact (hRx _).mp (gammaGroundUniqueFibreFunction_spec D ⟨r,hr⟩)

/-- The actual code tuple of an RV-unit tuple is a parameter-free definable map. -/
def rvUnitRealTupleMap (S : Set M) (n : ℕ) :
    Map (DefSet.univ (rawRVUnitSpace (M := M) n) S)
      (DefSet.univ (rawTupleSpace LRV M (Fin n)) S) :=
  Map.ofCodes _ rvUnitValues id (fun _ => Set.DefinableFun.proj LRV)
    (fun _ => Set.mem_univ _) (fun c => (rvUnitValues_decode c).symm)

/-- A coefficient definable over B and a retained RES tuple can be
uniformized as a function of that tuple over exactly B. -/
theorem gammaGroundPoint_rvUnitTuple_function
    (r : Fin n → (CanonicalRV.RVSort M)ˣ) (q : Q.Carrier)
    (hq : GammaGroundDefinable hc (adjoinRVUnitTuple B r) Q {q}) :
    ∃ (A : GammaGroundDefSet hc B (rawRVUnitSpace n)) (hr : r ∈ A.carrier)
      (f : GammaGroundMap A (GammaGroundDefSet.univ hc B Q)), (f ⟨r,hr⟩).val = q := by
  obtain ⟨D,hr,f,hf⟩ := gammaGroundPoint_realTuple_function (rvUnitValues r) q hq
  let A : GammaGroundDefSet hc B (rawRVUnitSpace n) :=
    ⟨{x | rvUnitValues x ∈ D.carrier},D.definable.preimage (rvUnitRealTupleMap B.real n)⟩
  let g : GammaGroundMap A D :=
    GammaGroundMap.ofGlobal A D (rvUnitRealTupleMap B.real n) (fun a => a.property)
  exact ⟨A,hr,f.comp g,hf⟩

/-- Coordinatewise RV definable closure gives the definable singleton of
the native tuple, without adjoining any representative of a Gamma value. -/
theorem gammaGroundRVUnitTuple_point_definable
    (c : Fin m → (CanonicalRV.RVSort M)ˣ)
    (hcdef : ∀ j, DefinableClosureAtBase B .rv (rvUnitValues c j)) :
    GammaGroundDefinable hc B (rawRVUnitSpace m) {c} := by
  apply (gammaGroundRVUnit_definable_iff {c}).mpr
  simpa only [Set.image_singleton] using
    tuple_singleton_definable_base B (fun _ : Fin m => .rv) (rvUnitValues c) hcdef

/-- The generic monomial theorem's coordinatewise coefficients over B(r)
therefore give a genuine original-base coefficient function near r. -/
theorem gammaGroundRVUnitCoefficient_function
    (r : Fin n → (CanonicalRV.RVSort M)ˣ) (c : Fin m → (CanonicalRV.RVSort M)ˣ)
    (hcdef : ∀ j, DefinableClosureAtBase (adjoinRVUnitTuple B r) .rv (rvUnitValues c j)) :
    ∃ (A : GammaGroundDefSet hc B (rawRVUnitSpace n)) (hr : r ∈ A.carrier)
      (f : GammaGroundMap A (GammaGroundDefSet.univ hc B (rawRVUnitSpace m))),
      (f ⟨r,hr⟩).val = c :=
  gammaGroundPoint_rvUnitTuple_function (Q := rawRVUnitSpace m) r c
    (gammaGroundRVUnitTuple_point_definable c hcdef)
end DiamondIntegral.Section3
