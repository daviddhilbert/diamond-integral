import IntegrationSection5.GammaBranchBoundaryPrefix
import IntegrationSection5.RVBranchProductHeadSaturation
import IntegrationSection5.CanonicalProductSource
import IntegrationSection5.CanonicalRVSliceGeometry
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.DefinableGeometry.Space.prod
  SpecialTransformations.Section4.realSpace SpecialTransformations.Milestone0.sortEval
  SpecialTransformations.Section4.vfSpace SpecialTransformations.Section4.rvSpace
  SpecialTransformations.Section5.pointSpace
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section5
namespace IntegrationInACVF.Section5
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {G : SpecialTransformations.Section3.GammaParameters.Base (M := M)}
variable {S : Set M} {m b : ℕ}
variable {A : DefSet (M := M) S 1 m} {B : DefSet (M := M) S 1 b}
variable {H R : DefSet (M := M) S 2 m} {Z : DefSet (M := M) S 1 m}

structure RVProductBranchCompletion (u : SpecialBijection A B) (H : DefSet (M := M) S 2 m)
    (E : Set (Fin m → RV (M := M))) where
  prefixTarget : DefSet (M := M) S 2 (1+m)
  preMap : Map H prefixTarget
  start : Option Bool
  prefix_special : SpecialRelativeBoundary preMap 0 (some true) start
  prefix_gamma : GammaGraphDefinable G (pointMapGraph preMap)
  prefixTarget_gamma : GammaSetDefinable G (carrier prefixTarget)
  prefix_formula : ∀ p : H, (preMap p).val = coordinateCanonical 0 p.val
  arity : ℕ
  target : DefSet (M := M) S 2 arity
  step : Map prefixTarget target
  projection : Fin b → Fin arity
  arity_le : 1+m ≤ arity
  embedding : ∀ p ∈ carrier prefixTarget, p.2 ∘ Fin.natAdd 1 ∈ E →
    activeUnaryProjection 0 (Fin.natAdd 1) p ∈ carrier A
  step_special : SpecialRelativeBoundary step 0 start (u.chain.lastKind start)
  step_gamma : GammaGraphDefinable G (pointMapGraph step)
  target_gamma : GammaSetDefinable G (carrier target)
  saturated : HeadSaturated (carrier target)
  suffix_compatibility : ∀ j, projection (suffixIndex (special_chain_rvArity_le u.chain) j) =
    suffixIndex arity_le (Fin.natAdd 1 j)
  coordinate_coverage : ∀ j : Fin arity, (∃ k, projection k = j) ∨ ∃ k, suffixIndex arity_le k = j
  square : ∀ p : prefixTarget, ∀ hp : p.val.2 ∘ Fin.natAdd 1 ∈ E,
    activeUnaryProjection 0 projection (step p).val =
      (u.toMap ⟨activeUnaryProjection 0 (Fin.natAdd 1) p.val,embedding p.val p.property hp⟩).val
  inactive_vf : ∀ p : prefixTarget, p.val.2 ∘ Fin.natAdd 1 ∉ E →
    vfAt (step p).val 0 = vfAt p.val 0
  inactive_sameRV : ∀ p q : prefixTarget, p.val.2 ∘ Fin.natAdd 1 ∉ E →
    q.val.2 ∘ Fin.natAdd 1 ∉ E → SameRV p.val q.val → SameRV (step p).val (step q).val

namespace RVProductBranchCompletion
variable {u : SpecialBijection A B} {E : Set (Fin m → RV (M := M))}
def preparation (C : RVProductBranchCompletion (G := G) u H E) : HeadPreparation H where
  arity := C.arity
  target := C.target
  map := Map.comp C.step C.preMap
  special := specialRelativeBoundary_forget (specialRelativeBoundary_comp C.preMap C.step 0
    C.prefix_special C.step_special)
  saturated := C.saturated

theorem preparation_special (C : RVProductBranchCompletion (G := G) u H E) :
    SpecialRelativeBoundary C.preparation.map 0 (some true) (u.chain.lastKind C.start) :=
  specialRelativeBoundary_comp C.preMap C.step 0 C.prefix_special C.step_special

theorem preparation_gamma (C : RVProductBranchCompletion (G := G) u H E) :
    GammaGraphDefinable G (pointMapGraph C.preparation.map) :=
  gamma_composition_graph C.preMap C.step C.prefix_gamma C.step_gamma

theorem preparation_inactive_vf (C : RVProductBranchCompletion (G := G) u H E)
    (p : H) (hp : p.val.2 ∉ E) : vfAt (C.preparation.map p).val 0 = vfAt p.val 0 := by
  have hflag : (C.preMap p).val.2 ∘ Fin.natAdd 1 ∉ E := by
    rw [C.prefix_formula,coordinateCanonical_oldRV]
    exact hp
  exact (C.inactive_vf (C.preMap p) hflag).trans
    (congrArg (fun q : Point (M := M) 2 (1+m) => vfAt q 0) (C.prefix_formula p))

theorem preparation_inactive_sameRV (C : RVProductBranchCompletion (G := G) u H E)
    (p q : H) (hp : p.val.2 ∉ E) (hq : q.val.2 ∉ E) (he : SameRV p.val q.val) :
    SameRV (C.preparation.map p).val (C.preparation.map q).val := by
  apply C.inactive_sameRV (C.preMap p) (C.preMap q)
  · rw [C.prefix_formula,coordinateCanonical_oldRV]; exact hp
  · rw [C.prefix_formula,coordinateCanonical_oldRV]; exact hq
  · rw [C.prefix_formula,C.prefix_formula]
    exact coordinateCanonical_sameRV 0 he
end RVProductBranchCompletion

theorem rv_product_branch_completion (u : SpecialBijection A B) (hu : GammaChainDefinable G u.chain)
    (hB : IsRVPullback (carrier B)) (hH : GammaSetDefinable G (carrier H))
    (E : Set (Fin m → RV (M := M)))
    (hR : carrier R = {p | p ∈ carrier H ∧ p.2 ∈ E})
    (hProduct : carrier R = {p | activeUnaryProjection 0 id p ∈ carrier A ∧
      activeUnaryProjection 1 id p ∈ carrier Z})
    (hAflag : ∀ p ∈ carrier A, p.2 ∈ E)
    (k : Fin m) (hTag : Tagged (carrier A) 0 k)
    (hInactive : HeadSaturated {p | p ∈ carrier H ∧ p.2 ∉ E}) :
    Nonempty (RVProductBranchCompletion (G := G) u H E) := by
  obtain ⟨C,pre,start,hPre,hAlt,hC,hPreG,hForm,hTagC⟩ :=
    gamma_branch_boundary_prefix u.chain u.alternating hH 0 (some true) (fun h => (by cases h))
  have hCeq : carrier C = carrier (coordinateCanonicalImage H 0) :=
    canonical_form_target 0 pre (specialRelative_bijective (specialRelativeBoundary_forget hPre)) hForm
  have hCimage : carrier C = coordinateCanonical 0 '' carrier H := by
    rw [hCeq]
    ext p
    constructor
    · rintro ⟨q,hq⟩; exact ⟨q.val,q.property,hq⟩
    · rintro ⟨q,hq,hqp⟩; exact ⟨⟨q,hq⟩,hqp⟩
  have hEmb : ∀ p ∈ carrier C, p.2 ∘ Fin.natAdd 1 ∈ E →
      activeUnaryProjection 0 (Fin.natAdd 1) p ∈ carrier A := by
    intro p hp he
    obtain ⟨q,hq,rfl⟩ := (Set.ext_iff.mp hCimage p).mp hp
    rw [coordinateCanonical_oldRV] at he
    have hqR : q ∈ carrier R := (Set.ext_iff.mp hR q).mpr ⟨hq,he⟩
    rw [activeUnaryProjection_dropCanonical]
    exact ((Set.ext_iff.mp hProduct q).mp hqR).1
  let D := coordinateCanonicalImage R 0
  have hD : carrier D = {p | p ∈ carrier C ∧ p.2 ∘ Fin.natAdd 1 ∈ E} := by
    rw [hCeq]
    exact coordinateCanonical_rvSlice 0 E hR
  have hDProduct : carrier D = {p | activeUnaryProjection 0 (Fin.natAdd 1) p ∈ carrier A ∧
      canonicalProductPassive k Z p} := coordinateCanonical_shared_product_source k hTag hProduct
  have hOff : HeadSaturated {p | p ∈ carrier C ∧ p.2 ∘ Fin.natAdd 1 ∉ E} := by
    rw [hCimage]
    exact headSaturated_coordinateCanonical_slice (carrier H) Eᶜ hInactive
  obtain ⟨r,K,σ,hle,f,hf,hK,hfG,hCompat,hCover,hComm,hOffVF,hOffRV,_⟩ :=
    gamma_unary_chain_rvPredicateLift u.chain hu E hAflag C hC 0 (Fin.natAdd 1)
      hEmb start hTagC hAlt
  have hSat : HeadSaturated (carrier K) := headSaturated_rvBranch_product_lift u hB f hf hle
    (Fin.natAdd 1) σ E hD (canonicalProductPassive k Z) (canonicalProductPassive_independent k Z)
    hDProduct hEmb hComm hCompat hCover hOff hOffVF hOffRV
  exact ⟨⟨C,pre,start,hPre,hPreG,hC,hForm,r,K,f,σ,hle,hEmb,hf,hfG,hK,hSat,
    hCompat,hCover,hComm,hOffVF,hOffRV⟩⟩

end IntegrationInACVF.Section5
