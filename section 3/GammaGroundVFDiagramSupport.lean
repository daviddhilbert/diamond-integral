import «section 3».GammaGroundFiniteNameSupport
import «section 3».GammaGroundNamedFunctors
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open Classical FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] [TopologicalSpace (Section2.VF M)]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : GammaParameters.Base (M := M)} {k : ℕ}
variable {ι E : Type}

structure GammaGroundVFDiagramSupport (U : ι → GammaGroundVFObject hc B k)
    (a b : E → ι) (f : ∀ e, GammaGroundBijection (U (a e)).domain (U (b e)).domain) where
  size : ℕ
  values : Fin size → Values.Gamma (M := M)
  values_mem : ∀ j, values j ∈ B.gamma
  domain : ∀ i, ImaginaryDefinable ((volumeGammaSpace hc).power (Fin size)) values
    (rawMixedSpace (U i).vfArity (U i).rvArity) B.real (U i).domain.carrier
  arrow : ∀ e, ImaginaryDefinable ((volumeGammaSpace hc).power (Fin size)) values
    ((rawMixedSpace (U (a e)).vfArity (U (a e)).rvArity).prod
      (rawMixedSpace (U (b e)).vfArity (U (b e)).rvArity)) B.real
      {z | ∃ x : (U (a e)).domain, x.val = z.1 ∧ ((f e).map x).val = z.2}

/-- A finite VF diagram has one old-Gamma-name presentation, retaining
its literal intrinsic VF dimension bounds and finite RV fibres. -/
theorem gammaGroundVFDiagram_finite_support [Fintype ι] [Fintype E]
    (U : ι → GammaGroundVFObject hc B k) (a b : E → ι)
    (f : ∀ e, GammaGroundBijection (U (a e)).domain (U (b e)).domain) :
    Nonempty (GammaGroundVFDiagramSupport U a b f) := by
  let Q : ι ⊕ E → Space LRV M := Sum.elim
    (fun i => rawMixedSpace (U i).vfArity (U i).rvArity)
    (fun e => (rawMixedSpace (U (a e)).vfArity (U (a e)).rvArity).prod
      (rawMixedSpace (U (b e)).vfArity (U (b e)).rvArity))
  let A : ∀ j, Set (Q j).Carrier := by
    intro j
    rcases j with i | e
    · exact (U i).domain.carrier
    · exact {z | ∃ x : (U (a e)).domain, x.val = z.1 ∧ ((f e).map x).val = z.2}
  have hA : ∀ j, GammaGroundDefinable hc B (Q j) (A j) := by
    intro j
    rcases j with i | e
    · exact (U i).domain.definable
    · exact (f e).map.graph_definable
  obtain ⟨n,γ,hγ,h⟩ := gammaGroundDefinable_fintype_common_names Q A hA
  exact ⟨⟨n,γ,hγ,fun i => h (.inl i),fun e => h (.inr e)⟩⟩

namespace GammaGroundVFDiagramSupport
variable {U : ι → GammaGroundVFObject hc B k} {a b : E → ι}
variable {f : ∀ e, GammaGroundBijection (U (a e)).domain (U (b e)).domain}

def namedObject (S : GammaGroundVFDiagramSupport U a b f) (i : ι) :
    NamedVFObject ((volumeGammaSpace hc).power (Fin S.size)) S.values B.real k :=
  ⟨(U i).vfArity,(U i).rvArity,⟨(U i).domain.carrier,S.domain i⟩,(U i).dimension,(U i).finite⟩

def namedArrow (S : GammaGroundVFDiagramSupport U a b f) (e : E) :
    NamedBijection (S.namedObject (a e)).domain (S.namedObject (b e)).domain :=
  ⟨⟨(f e).map.toFun,S.arrow e⟩,(f e).bijective⟩

@[simp] theorem object_reconstructed (S : GammaGroundVFDiagramSupport U a b f) (i : ι) :
    GammaGroundVFObject.ofNamed (S.namedObject i)
      (GammaGroundDefinable.gammaTuple_singleton S.values S.values_mem) = U i := rfl

@[simp] theorem arrow_reconstructed (S : GammaGroundVFDiagramSupport U a b f) (e : E) :
    GammaGroundBijection.ofNamed (S.namedArrow e)
      (GammaGroundDefinable.gammaTuple_singleton S.values S.values_mem) = f e := by
  apply GammaGroundBijection.ext
  apply GammaGroundMap.ext
  intro x
  rfl
end GammaGroundVFDiagramSupport
end DiamondIntegral.Section3
