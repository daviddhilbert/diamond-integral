import IntegrationSection5.GammaBranchBoundaryPrefix
import IntegrationSection5.GammaSpecialRestriction
import IntegrationSection5.CanonicalRVSliceGeometry
import IntegrationSection5.SharedRVUnaryHeadPreparation
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
variable {R H : DefSet (M := M) S 1 m} {B : DefSet (M := M) S 1 b}

theorem activeUnaryProjection_one_id (p : Point (M := M) 1 m) : activeUnaryProjection 0 id p = p := by
  refine Prod.ext ?_ rfl
  funext i
  fin_cases i
  rfl

structure CanonicalUnaryBranchExtension
    (u : SpecialBijection (coordinateCanonicalImage R 0) B) (H : DefSet (M := M) S 1 m)
    (E : Set (Fin m → RV (M := M))) (previous : Option Bool) where
  prefixTarget : DefSet (M := M) S 1 (1+m)
  preMap : Map H prefixTarget
  start : Option Bool
  prefix_special : SpecialRelativeBoundary preMap 0 previous start
  prefix_graph : GammaGraphDefinable G (pointMapGraph preMap)
  prefix_gamma : GammaSetDefinable G (carrier prefixTarget)
  prefix_formula : ∀ p : H, (preMap p).val = coordinateCanonical 0 p.val
  arity : ℕ
  target : DefSet (M := M) S 1 arity
  step : Map prefixTarget target
  projection : Fin b → Fin arity
  arity_le : 1+m ≤ arity
  projection_surjective : Function.Surjective projection
  embedding : ∀ p ∈ carrier prefixTarget, p.2 ∘ Fin.natAdd 1 ∈ E →
    activeUnaryProjection 0 id p ∈ carrier (coordinateCanonicalImage R 0)
  step_special : SpecialRelativeBoundary step 0 start (u.chain.lastKind start)
  step_graph : GammaGraphDefinable G (pointMapGraph step)
  target_gamma : GammaSetDefinable G (carrier target)
  active_image : DefSet (M := M) S 1 arity
  active_image_eq : carrier active_image = {q | ∃ p : prefixTarget,
    p.val.2 ∘ Fin.natAdd 1 ∈ E ∧ (step p).val = q}
  active_saturated : HeadSaturated (carrier active_image)
  active_gamma : GammaSetDefinable G (carrier active_image)
  active_projection_mem : ∀ p ∈ carrier active_image, activeUnaryProjection 0 projection p ∈ carrier B
  active_projection_surjective : ∀ b : B, ∃ p : active_image, activeUnaryProjection 0 projection p.val = b.val
  square : ∀ p : prefixTarget, ∀ hp : p.val.2 ∘ Fin.natAdd 1 ∈ E,
    activeUnaryProjection 0 projection (step p).val =
      (u.toMap ⟨activeUnaryProjection 0 id p.val,embedding p.val p.property hp⟩).val
  inactive_vf : ∀ p : prefixTarget, p.val.2 ∘ Fin.natAdd 1 ∉ E → vfAt (step p).val 0 = vfAt p.val 0
  inactive_sameRV : ∀ p q : prefixTarget, p.val.2 ∘ Fin.natAdd 1 ∉ E →
    q.val.2 ∘ Fin.natAdd 1 ∉ E → SameRV p.val q.val → SameRV (step p).val (step q).val
  ending_tag : u.chain.lastKind start ≠ some true → ∃ kH, Tagged (carrier target) 0 kH

namespace CanonicalUnaryBranchExtension
variable {u : SpecialBijection (coordinateCanonicalImage R 0) B}
variable {E : Set (Fin m → RV (M := M))} {previous : Option Bool}
def map (C : CanonicalUnaryBranchExtension (G := G) u H E previous) : Map H C.target := Map.comp C.step C.preMap

theorem special (C : CanonicalUnaryBranchExtension (G := G) u H E previous) :
    SpecialRelativeBoundary C.map 0 previous (u.chain.lastKind C.start) :=
  specialRelativeBoundary_comp C.preMap C.step 0 C.prefix_special C.step_special

theorem graph (C : CanonicalUnaryBranchExtension (G := G) u H E previous) :
    GammaGraphDefinable G (pointMapGraph C.map) :=
  gamma_composition_graph C.preMap C.step C.prefix_graph C.step_graph

theorem inactive (C : CanonicalUnaryBranchExtension (G := G) u H E previous)
    (p : H) (hp : p.val.2 ∉ E) : vfAt (C.map p).val 0 = vfAt p.val 0 := by
  have hflag : (C.preMap p).val.2 ∘ Fin.natAdd 1 ∉ E := by
    rw [C.prefix_formula,coordinateCanonical_oldRV]; exact hp
  exact (C.inactive_vf (C.preMap p) hflag).trans
    (congrArg (fun q : Point (M := M) 1 (1+m) => vfAt q 0) (C.prefix_formula p))

theorem inactive_rv (C : CanonicalUnaryBranchExtension (G := G) u H E previous)
    (p q : H) (hp : p.val.2 ∉ E) (hq : q.val.2 ∉ E) (he : SameRV p.val q.val) :
    SameRV (C.map p).val (C.map q).val := by
  apply C.inactive_sameRV (C.preMap p) (C.preMap q)
  · rw [C.prefix_formula,coordinateCanonical_oldRV]; exact hp
  · rw [C.prefix_formula,coordinateCanonical_oldRV]; exact hq
  · rw [C.prefix_formula,C.prefix_formula]
    exact coordinateCanonical_sameRV 0 he
end CanonicalUnaryBranchExtension

theorem canonical_unary_branch_extension
    (u : SpecialBijection (coordinateCanonicalImage R 0) B) (hu : GammaChainDefinable G u.chain)
    (hB : IsRVPullback (carrier B)) (hH : GammaSetDefinable G (carrier H))
    (hRΓ : GammaSetDefinable G (carrier R)) (E : Set (Fin m → RV (M := M)))
    (hR : carrier R = {p | p ∈ carrier H ∧ p.2 ∈ E}) (previous : Option Bool)
    (hTag : previous = some false → ∃ kH, Tagged (carrier H) 0 kH) :
    Nonempty (CanonicalUnaryBranchExtension (G := G) u H E previous) := by
  obtain ⟨C,pre,start,hPre,hAlt,hC,hPreG,hForm,hTagC⟩ :=
    gamma_branch_boundary_prefix u.chain u.alternating hH 0 previous hTag
  have hCeq := canonical_form_target 0 pre
    (specialRelative_bijective (specialRelativeBoundary_forget hPre)) hForm
  let D := coordinateCanonicalImage R 0
  let ER : Set (Fin (1+m) → RV (M := M)) := {s | s ∘ Fin.natAdd 1 ∈ E}
  have hD : carrier D = {p | p ∈ carrier C ∧ p.2 ∈ ER} := by
    rw [hCeq]
    exact coordinateCanonical_rvSlice 0 E hR
  have hDG := gamma_coordinateCanonicalImage R hRΓ 0
  have hEmb : ∀ p ∈ carrier C, p.2 ∈ ER → activeUnaryProjection 0 id p ∈ carrier D := by
    intro p hp he
    rw [activeUnaryProjection_one_id]
    exact (Set.ext_iff.mp hD p).mpr ⟨hp,he⟩
  have hFlag : ∀ p ∈ carrier D, p.2 ∈ ER := fun p hp => ((Set.ext_iff.mp hD p).mp hp).2
  obtain ⟨r,K,σ,hle,f,hf,hK,hfG,hCompat,hCover,hComm,hOff,hOffRV,hEnd⟩ :=
    gamma_unary_chain_rvPredicateLift u.chain hu ER hFlag C hC 0 id hEmb start hTagC hAlt
  have hDC : carrier D ⊆ carrier C := fun p hp => ((Set.ext_iff.mp hD p).mp hp).1
  let g := restrictPointMap f D hDC
  let I := restrictPointImage f D hDC
  have hg := specialRelativeBoundary_restrict f D hDC hf
  have hProduct : carrier D = {p | activeUnaryProjection 0 id p ∈ carrier D ∧ True} := by
    ext p
    change p ∈ carrier D ↔ activeUnaryProjection 0 id p ∈ carrier D ∧ True
    rw [activeUnaryProjection_one_id]
    exact ⟨fun h => ⟨h,trivial⟩,And.left⟩
  have hCommD (p : D) : activeUnaryProjection 0 σ (g p).val =
      (u.toMap ⟨activeUnaryProjection 0 id p.val,((Set.ext_iff.mp hProduct p.val).mp p.property).1⟩).val := by
    exact hComm ⟨p.val,hDC p.property⟩ ((Set.ext_iff.mp hD p.val).mp p.property).2
  have hImage := coordinate_lift_product_image_sharedRV u g 0 (specialRelativeBoundary_forget hg)
    hle id σ (fun _ => True) (fun _ _ => Iff.rfl) hProduct hCommD hCompat hCover
  have hSat : HeadSaturated (carrier I) := unary_product_head_saturated hB σ hle (fun _ => True) (fun _ _ => Iff.rfl) hImage
  have hIG := gamma_restrictPointImage f D hDC hDG hfG
  have hIEq : carrier I = {q | ∃ p : C, p.val.2 ∘ Fin.natAdd 1 ∈ E ∧ (f p).val = q} := by
    ext q
    constructor
    · rintro ⟨p,hpq⟩
      exact ⟨⟨p.val,hDC p.property⟩,((Set.ext_iff.mp hD p.val).mp p.property).2,hpq⟩
    · rintro ⟨p,hp,hpq⟩
      exact ⟨⟨p.val,(Set.ext_iff.mp hD p.val).mpr ⟨p.property,hp⟩⟩,hpq⟩
  have hσ : Function.Surjective σ := by
    intro j
    rcases hCover j with h | ⟨k,hk⟩
    · exact h
    · exact ⟨suffixIndex (special_chain_rvArity_le u.chain) k,(hCompat k).trans hk⟩
  have hMem : ∀ p ∈ carrier I, activeUnaryProjection 0 σ p ∈ carrier B :=
    fun p hp => ((Set.ext_iff.mp hImage p).mp hp).1
  have hSurj : ∀ b : B, ∃ p : I, activeUnaryProjection 0 σ p.val = b.val := by
    intro b
    let a : D := u.inverseMap b
    have ha : (⟨activeUnaryProjection 0 id a.val,
        ((Set.ext_iff.mp hProduct a.val).mp a.property).1⟩ : D) = a :=
      Subtype.ext (activeUnaryProjection_one_id a.val)
    refine ⟨g a,?_⟩
    rw [hCommD a,ha]
    exact congrArg Subtype.val (u.apply_inverse b)
  exact ⟨⟨C,pre,start,hPre,hPreG,hC,hForm,r,K,f,σ,hle,hσ,hEmb,hf,hfG,hK,I,hIEq,hSat,hIG,
    hMem,hSurj,hComm,hOff,hOffRV,hEnd⟩⟩

end IntegrationInACVF.Section5
