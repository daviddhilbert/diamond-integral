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
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : GammaParameters.Base (M := M)} {k : ℕ}
variable {ι E : Type}

/-- A finite diagram's domains, labels, full forms and actual arrow
code graphs all use one tuple of the original Gamma names. -/
structure GammaGroundMeasuredRVDiagramSupport
    (U : ι → GammaGroundMeasuredRVObject hc B k) (a b : E → ι)
    (f : ∀ e, GammaGroundMeasuredRVHom (U (a e)) (U (b e))) where
  size : ℕ
  values : Fin size → Values.Gamma (M := M)
  values_mem : ∀ j, values j ∈ B.gamma
  domain : ∀ i, ImaginaryDefinable ((volumeGammaSpace hc).power (Fin size)) values
    (rawRVSpace (U i).underlying.arity) B.real (U i).underlying.domain.carrier
  label : ∀ i, ImaginaryDefinable ((volumeGammaSpace hc).power (Fin size)) values
    ((rawRVSpace (U i).underlying.arity).prod (rawRVSpace k)) B.real
      {z | ∃ x : (U i).underlying.domain, x.val = z.1 ∧ ((U i).underlying.volume x).val = z.2}
  form : ∀ i, ImaginaryDefinable ((volumeGammaSpace hc).power (Fin size)) values
    ((rawRVSpace (U i).underlying.arity).prod (volumeGammaSpace hc)) B.real
      {z | ∃ x : (U i).underlying.domain, x.val = z.1 ∧ ((U i).form x).val = z.2}
  arrow : ∀ e, ImaginaryDefinable ((volumeGammaSpace hc).power (Fin size)) values
    ((rawRVSpace (U (a e)).underlying.arity).prod (rawRVSpace (U (b e)).underlying.arity)) B.real
      {z | ∃ x : (U (a e)).underlying.domain, x.val = z.1 ∧ ((f e).bijection.map x).val = z.2}

/-- Every finite measured RV diagram, including its full weights and
morphisms, descends to one finite-name stage of the same ground. -/
theorem gammaGroundMeasuredRVDiagram_finite_support [Fintype ι] [Fintype E]
    (U : ι → GammaGroundMeasuredRVObject hc B k) (a b : E → ι)
    (f : ∀ e, GammaGroundMeasuredRVHom (U (a e)) (U (b e))) :
    Nonempty (GammaGroundMeasuredRVDiagramSupport U a b f) := by
  let I := ((ι ⊕ ι) ⊕ ι) ⊕ E
  let Q : I → Space LRV M := Sum.elim
    (Sum.elim (Sum.elim (fun i => rawRVSpace (U i).underlying.arity)
      (fun i => (rawRVSpace (U i).underlying.arity).prod (rawRVSpace k)))
      (fun i => (rawRVSpace (U i).underlying.arity).prod (volumeGammaSpace hc)))
    (fun e => (rawRVSpace (U (a e)).underlying.arity).prod (rawRVSpace (U (b e)).underlying.arity))
  let A : ∀ j : I, Set (Q j).Carrier := by
    intro j
    rcases j with ((i | i) | i) | e
    · exact (U i).underlying.domain.carrier
    · exact {z | ∃ x : (U i).underlying.domain, x.val = z.1 ∧ ((U i).underlying.volume x).val = z.2}
    · exact {z | ∃ x : (U i).underlying.domain, x.val = z.1 ∧ ((U i).form x).val = z.2}
    · exact {z | ∃ x : (U (a e)).underlying.domain, x.val = z.1 ∧ ((f e).bijection.map x).val = z.2}
  have hA : ∀ j : I, GammaGroundDefinable hc B (Q j) (A j) := by
    intro j
    rcases j with ((i | i) | i) | e
    · exact (U i).underlying.domain.definable
    · exact (U i).underlying.volume.graph_definable
    · exact (U i).form.graph_definable
    · exact (f e).bijection.map.graph_definable
  obtain ⟨n,γ,hγ,h⟩ := gammaGroundDefinable_fintype_common_names Q A hA
  exact ⟨⟨n,γ,hγ,fun i => h (.inl (.inl (.inl i))),fun i => h (.inl (.inl (.inr i))),
    fun i => h (.inl (.inr i)),fun e => h (.inr e)⟩⟩

namespace GammaGroundMeasuredRVDiagramSupport
variable {U : ι → GammaGroundMeasuredRVObject hc B k} {a b : E → ι}
variable {f : ∀ e, GammaGroundMeasuredRVHom (U (a e)) (U (b e))}

def namedDomain (S : GammaGroundMeasuredRVDiagramSupport U a b f) (i : ι) :
    NamedDefSet ((volumeGammaSpace hc).power (Fin S.size)) S.values
      (rawRVSpace (U i).underlying.arity) B.real := ⟨(U i).underlying.domain.carrier,S.domain i⟩

def namedLabel (S : GammaGroundMeasuredRVDiagramSupport U a b f) (i : ι) :
    NamedMap (S.namedDomain i)
      (NamedDefSet.univ ((volumeGammaSpace hc).power (Fin S.size)) S.values (rawRVSpace k) B.real) :=
  ⟨(U i).underlying.volume.toFun,S.label i⟩

def namedUnderlying (S : GammaGroundMeasuredRVDiagramSupport U a b f) (i : ι) :
    NamedRVObject ((volumeGammaSpace hc).power (Fin S.size)) S.values B.real k :=
  ⟨(U i).underlying.arity,S.namedDomain i,S.namedLabel i,(U i).underlying.finite,(U i).underlying.nonzero⟩

def namedObject (S : GammaGroundMeasuredRVDiagramSupport U a b f) (i : ι) :
    NamedMeasuredRVObject ((volumeGammaSpace hc).power (Fin S.size)) S.values hc B.real k :=
  ⟨S.namedUnderlying i,⟨(U i).form.toFun,S.form i⟩⟩

def namedArrow (S : GammaGroundMeasuredRVDiagramSupport U a b f) (e : E) :
    NamedMeasuredRVHom (S.namedObject (a e)) (S.namedObject (b e)) :=
  ⟨⟨⟨(f e).bijection.map.toFun,S.arrow e⟩,(f e).bijection.bijective⟩,(f e).preserves⟩

/-- Reconstruction is literal, with the original RV labels and volume
forms, rather than only an equality of resulting scissors classes. -/
@[simp] theorem object_reconstructed (S : GammaGroundMeasuredRVDiagramSupport U a b f) (i : ι) :
    GammaGroundMeasuredRVObject.ofNamed (S.namedObject i)
      (GammaGroundDefinable.gammaTuple_singleton S.values S.values_mem) = U i := rfl

@[simp] theorem arrow_reconstructed (S : GammaGroundMeasuredRVDiagramSupport U a b f) (e : E) :
    GammaGroundMeasuredRVHom.ofNamed (S.namedArrow e)
      (GammaGroundDefinable.gammaTuple_singleton S.values S.values_mem) = f e := by
  apply GammaGroundMeasuredRVHom.ext
  apply GammaGroundBijection.ext
  apply GammaGroundMap.ext
  intro x
  rfl
end GammaGroundMeasuredRVDiagramSupport
end DiamondIntegral.Section3
