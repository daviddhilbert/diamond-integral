import «section 3».GammaGroundMapUnions
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {ground : GammaParameters.Base (M := M)}
variable {P Q : Space LRV M}
def GammaGroundMap.emptyTo (B : GammaGroundDefSet hc ground Q) :
    GammaGroundMap (GammaGroundDefSet.empty hc ground P) B where
  toFun a := False.elim a.property
  graph_definable := by
    apply (GammaGroundDefSet.empty hc ground (P.prod Q)).definable.congr
    intro z
    constructor
    · exact False.elim
    · rintro ⟨a, _, _⟩
      exact False.elim a.property

/-- A definable piece equipped with an actual finite-to-one map to a common
target. This is gluing data, rather than an assumption about dimension. -/
structure GammaGroundFiniteMapPiece (P : Space LRV M) {Q : Space LRV M} (B : GammaGroundDefSet hc ground Q) where
  source : GammaGroundDefSet hc ground P
  map : GammaGroundMap source B
  finite : map.FiniteFibres

namespace GammaGroundFiniteMapPiece

variable {B : GammaGroundDefSet hc ground Q}

def empty : GammaGroundFiniteMapPiece P B :=
  ⟨GammaGroundDefSet.empty hc ground P, GammaGroundMap.emptyTo B, fun b => Set.finite_empty.subset (fun a => False.elim a.property)⟩

def union (p q : GammaGroundFiniteMapPiece P B) : GammaGroundFiniteMapPiece P B :=
  ⟨p.source.union q.source, p.map.union q.map, p.finite.union q.finite⟩

def glue : List (GammaGroundFiniteMapPiece P B) → GammaGroundFiniteMapPiece P B
  | [] => empty
  | p :: ps => p.union (glue ps)

@[simp] theorem mem_glue_source (ps : List (GammaGroundFiniteMapPiece P B)) (x : P.Carrier) :
    x ∈ (glue ps).source.carrier ↔ ∃ p ∈ ps, x ∈ p.source.carrier := by
  induction ps with
  | nil => simp [glue, empty, GammaGroundDefSet.empty, GammaGroundDefSet.ofReal, DefSet.empty]
  | cons p ps ih => simp [glue, union, GammaGroundDefSet.union, ih]

end GammaGroundFiniteMapPiece

/-- Finite gluing of finite-to-one maps to a common target. Images of
different branches may overlap; finiteness of fibres is preserved. -/
theorem gammaGroundFiniteCoverFiniteMap {ι : Type} [Fintype ι] (A : GammaGroundDefSet hc ground P) (B : GammaGroundDefSet hc ground Q)
    (D : ι → GammaGroundDefSet hc ground P) (f : ∀ i, GammaGroundMap (D i) B) (hf : ∀ i, (f i).FiniteFibres)
    (hcover : ∀ a : A, ∃ i, a.val ∈ (D i).carrier) :
    ∃ g : GammaGroundMap A B, g.FiniteFibres := by
  let pieces : List (GammaGroundFiniteMapPiece P B) :=
    (Finset.univ : Finset ι).toList.map (fun i => ⟨D i, f i, hf i⟩)
  let p := GammaGroundFiniteMapPiece.glue pieces
  have hsub : A.carrier ⊆ p.source.carrier := by
    intro a ha
    obtain ⟨i, hi⟩ := hcover ⟨a, ha⟩
    apply (GammaGroundFiniteMapPiece.mem_glue_source pieces a).mpr
    refine ⟨⟨D i, f i, hf i⟩, ?_, hi⟩
    exact List.mem_map.mpr ⟨i, by simp, rfl⟩
  let inc : GammaGroundMap A p.source := GammaGroundMap.inclusion hsub
  have hinc : Function.Injective inc := by
    intro a b he
    exact Subtype.ext (congrArg (fun x : p.source => x.val) he)
  exact ⟨p.map.comp inc, p.finite.comp (GammaGroundMap.finiteFibres_of_injective hinc)⟩


end DiamondIntegral.Section3
