import «section 3».GoodGammaRVRelations
import Section3.GammaRealMap
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section3.GammaParameters
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {n : ℕ} {sn : Fin n → SortTag}

theorem goodGammaRow_definable (G : GoodBaseGammaRelation B n sn) (a : Fin n → M) :
    GammaDefinableOverBase ⟨B.real ∪ Set.range a,B.gamma⟩ (gammaRow G.carrier a) := by
  let C : Base (M := M) := ⟨B.real ∪ Set.range a,B.gamma⟩
  let T : Set M := C.real
  let F (z : Fin 1 → M) : Fin (n+1) → M := Fin.snoc a (z 0)
  have hF : @Set.DefinableMap M LRV (CanonicalStructure.normalize (M := M)) (Fin 1) (Fin (n+1)) T F := by
    letI := CanonicalStructure.normalize (M := M)
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp only [F,Fin.snoc_last]
      exact Set.DefinableFun.proj LRV
    · simp only [F,Fin.snoc_castSucc]
      exact LRV.definableFun_const (Fin 1) (show a j ∈ T from Or.inr (Set.mem_range_self j))
  have hd := (G.definable.mono (C := C) Set.subset_union_left Set.Subset.rfl).preimage_real_map
    (fun _ : Fin 1 => .rv) F hF
  change DefinableOverBase C (fun _ : Fin 1 => .rv) {z | z 0 ∈ Values.gammaPullback (gammaRow G.carrier a)}
  have heF (z : Fin 1 → M) : (Fin.init (F z),F z (Fin.last n)) = (a,z 0) := by
    simp only [F,Fin.init_snoc,Fin.snoc_last]
  convert hd using 1
  ext z
  change (z 0 ∈ Values.gammaPullback (gammaRow G.carrier a)) ↔
    ((Fin.init (F z),F z (Fin.last n)) ∈ G.carrier ∧
      z ∈ sortedUniverse (fun _ : Fin 1 => .rv))
  rw [heF z,GammaSyntax.mem_gammaPullback_iff]
  constructor
  · rintro ⟨hn,hr⟩
    refine ⟨(goodGammaRow_mem_code_iff G a (z 0) hn).mp hr,?_⟩
    intro i
    have hi : i = (0 : Fin 1) := Subsingleton.elim _ _
    subst i
    exact hn.1
  · rintro ⟨hg,_⟩
    have hn := G.proper a (z 0) hg
    exact ⟨hn,(goodGammaRow_mem_code_iff G a (z 0) hn).mpr hg⟩

theorem goodGammaRow_member_algebraic (G : GoodBaseGammaRelation B n sn)
    (a : Fin n → M) (δ : Values.Gamma (M := M)) (hδ : δ ∈ gammaRow G.carrier a) :
    GammaAlgebraicAtBase ⟨B.real ∪ Set.range a,B.gamma⟩ δ :=
  ⟨gammaRow G.carrier a,goodGammaRow_definable G a,G.finite a,hδ⟩
end DiamondIntegral.Section3
