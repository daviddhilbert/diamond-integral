import «section 3».GammaGroundRVBinaryClassifiers
import «section 3».GammaGroundPointIsomorphisms

/-! Original-ground RV predicates are native zero-VF predicates. The
absolute finite RV tags therefore give literal native label cuts. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.Section4.rawRVSpace
  SpecialTransformations.Section4.realSpace SpecialTransformations.DefinableGeometry.Space.ofEmbedding
  SpecialTransformations.DefinableGeometry.Space.prod
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
open IntegrationInACVF.Section6
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {d : ℕ}

theorem gammaGroundRV_point_predicate (A : GammaGroundDefSet hc B (rawRVSpace (M := M) d)) :
    GammaSetDefinable B {p : Point (M := M) 0 d | p.2 ∈ A.carrier} := by
  let P : GammaGroundDefSet hc B (rawMixedSpace (M := M) 0 d) :=
    ⟨{p | p.2 ∈ A.carrier},A.definable.preimage (universalProductSnd (SpecialTransformations.Section4.rawVFSpace (M := M) 0) (SpecialTransformations.Section4.rawRVSpace (M := M) d) B.real)⟩
  exact (gammaGroundPointIso (GammaGroundBijection.id P)).target_definable (gammaLogicInput B)

theorem gammaGroundRV_binary_tag_singleton (i : Fin 2) :
    GammaGroundDefinable hc B (rawRVSpace (M := M) 2) ({rvFamilyTag i} : Set (Fin 2 → CanonicalRV.RVSort M)) := by
  let Z := GammaGroundDefSet.univ hc B (rawRVSpace (M := M) 0)
  let f := gammaGroundRVBinaryConstant Z i
  apply f.image.definable.congr
  intro r
  constructor
  · rintro ⟨p,hp⟩
    exact hp ▸ gammaGroundRVBinaryConstant_value Z i p
  · intro hr
    exact ⟨⟨Fin.elim0,Set.mem_univ _⟩,(gammaGroundRVBinaryConstant_value Z i _).trans hr.symm⟩

include hc in
theorem gammaRV_binary_tag_point (i : Fin 2) :
    GammaSetDefinable B {p : Point (M := M) 0 2 | p.2 = rvFamilyTag i} :=
  gammaGroundRV_point_predicate (⟨{rvFamilyTag i},gammaGroundRV_binary_tag_singleton i⟩ :
    GammaGroundDefSet hc B (rawRVSpace (M := M) 2))

include hc in
theorem gammaRV_binary_tag_point_complement (i : Fin 2) :
    GammaSetDefinable B (Set.univ \ {p : Point (M := M) 0 2 | p.2 = rvFamilyTag i}) := by
  let A : GammaGroundDefSet hc B (rawRVSpace (M := M) 2) :=
    ⟨{rvFamilyTag i},gammaGroundRV_binary_tag_singleton i⟩
  have h := gammaGroundRV_point_predicate A.compl
  convert h using 1
  ext p
  change (p ∈ Set.univ ∧ p.2 ≠ rvFamilyTag i) ↔ p.2 ≠ rvFamilyTag i
  exact ⟨fun h => h.2,fun h => ⟨Set.mem_univ _,h⟩⟩

end DiamondIntegral.Section3
