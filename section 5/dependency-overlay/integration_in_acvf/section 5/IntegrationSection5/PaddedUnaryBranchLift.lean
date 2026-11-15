import IntegrationSection5.RVProjectionPadding
import IntegrationSection5.GammaSpecialRestriction
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
variable {S : Set M} {a b l : ℕ}
variable {A : DefSet (M := M) S 1 a} {B : DefSet (M := M) S 1 b}
variable {H D : DefSet (M := M) S 1 l}

structure PaddedUnaryBranchLift (u : SpecialBijection A B) (H : DefSet (M := M) S 1 l)
    (ρ : Fin a → Fin l) (E : Set (Fin a → RV (M := M))) (previous : Option Bool) where
  arity : ℕ
  target : DefSet (M := M) S 1 arity
  map : Map H target
  projection : Fin b → Fin arity
  arity_le : l ≤ arity
  special : SpecialRelativeBoundary map 0 previous (u.chain.lastKind previous)
  graph : GammaGraphDefinable G (pointMapGraph map)
  target_gamma : GammaSetDefinable G (carrier target)
  suffix_compatibility : ∀ j, projection (suffixIndex (special_chain_rvArity_le u.chain) j) =
    suffixIndex arity_le (ρ j)
  active_image : DefSet (M := M) S 1 arity
  active_image_eq : carrier active_image = {q | ∃ p : H, p.val.2 ∘ ρ ∈ E ∧ (map p).val = q}
  active_padding : RVProjectionPadding (G := G) active_image B projection
  active_saturated : HeadSaturated (carrier active_image)
  active_gamma : GammaSetDefinable G (carrier active_image)
  inactive_vf : ∀ p : H, p.val.2 ∘ ρ ∉ E → vfAt (map p).val 0 = vfAt p.val 0
  inactive_sameRV : ∀ p q : H, p.val.2 ∘ ρ ∉ E → q.val.2 ∘ ρ ∉ E →
    SameRV p.val q.val → SameRV (map p).val (map q).val
  ending_tag : u.chain.lastKind previous ≠ some true → ∃ kH, Tagged (carrier target) 0 kH

theorem padded_unary_branch_lift (u : SpecialBijection A B) (hu : GammaChainDefinable G u.chain)
    (hB : IsRVPullback (carrier B)) (hH : GammaSetDefinable G (carrier H))
    (ρ : Fin a → Fin l) (E : Set (Fin a → RV (M := M)))
    (hD : carrier D = {p | p ∈ carrier H ∧ p.2 ∘ ρ ∈ E})
    (P : RVProjectionPadding (G := G) D A ρ)
    (hClass : ∀ p ∈ carrier A, ∀ q ∈ carrier A, p.2 = q.2 → rv (vfAt p 0) = rv (vfAt q 0))
    (previous : Option Bool) (hTag : previous ≠ some true → ∃ kH, Tagged (carrier H) 0 kH)
    (hAlt : u.chain.Alternating previous) : Nonempty (PaddedUnaryBranchLift (G := G) u H ρ E previous) := by
  have hDH : carrier D ⊆ carrier H := fun p hp => ((Set.ext_iff.mp hD p).mp hp).1
  have hEmb : ∀ p ∈ carrier H, p.2 ∘ ρ ∈ E → activeUnaryProjection 0 ρ p ∈ carrier A := by
    intro p hp he
    have hm := (P.iso.equiv ⟨p,(Set.ext_iff.mp hD p).mpr ⟨hp,he⟩⟩).property
    rwa [P.values] at hm
  have hFlag : ∀ p ∈ carrier A, p.2 ∈ E := by
    intro p hp
    obtain ⟨d,hd⟩ := P.iso.equiv.surjective ⟨p,hp⟩
    have he : d.val.2 ∘ ρ = p.2 := congrArg (fun z : Point (M := M) 1 a => z.2)
      ((P.values d).symm.trans (congrArg Subtype.val hd))
    exact he ▸ ((Set.ext_iff.mp hD d.val).mp d.property).2
  obtain ⟨r,K,σ,hle,f,hf,hK,hfG,hCompat,hCover,hComm,hOff,hOffRV,hEnd⟩ :=
    gamma_unary_chain_rvPredicateLift u.chain hu E hFlag H hH 0 ρ hEmb previous hTag hAlt
  let g := restrictPointMap f D hDH
  let I := restrictPointImage f D hDH
  have hg := specialRelativeBoundary_restrict f D hDH hf
  have hgBij := specialRelative_bijective (specialRelativeBoundary_forget hg)
  have hCommD (d : D) : activeUnaryProjection 0 σ (g d).val = (u.toMap (P.iso.equiv d)).val := by
    have h := hComm ⟨d.val,hDH d.property⟩ ((Set.ext_iff.mp hD d.val).mp d.property).2
    have he : (⟨activeUnaryProjection 0 ρ d.val,hEmb d.val (hDH d.property)
        ((Set.ext_iff.mp hD d.val).mp d.property).2⟩ : A) = P.iso.equiv d := Subtype.ext (P.values d).symm
    exact h.trans (congrArg (fun z : A => (u.toMap z).val) he)
  have hProduct := P.product_source hClass
  have hQ : ∀ (p : Point (M := M) 1 l) (x : VF (M := M)), (replace 0 p x).2 ∈ paddingRVLabels D ↔ p.2 ∈ paddingRVLabels D := fun _ _ => Iff.rfl
  have hCommProd (d : D) : activeUnaryProjection 0 σ (g d).val =
      (u.toMap ⟨activeUnaryProjection 0 ρ d.val,((Set.ext_iff.mp hProduct d.val).mp d.property).1⟩).val := by
    have he : (⟨activeUnaryProjection 0 ρ d.val,((Set.ext_iff.mp hProduct d.val).mp d.property).1⟩ : A) =
        P.iso.equiv d := Subtype.ext (P.values d).symm
    rw [he]
    exact hCommD d
  have hImage := coordinate_lift_product_image_sharedRV u g 0 (specialRelativeBoundary_forget hg)
    hle ρ σ (fun p => p.2 ∈ paddingRVLabels D) hQ hProduct hCommProd hCompat hCover
  have hSat : HeadSaturated (carrier I) := unary_product_head_saturated hB σ hle
    (fun p => p.2 ∈ paddingRVLabels D) hQ hImage
  have hDG := (P.iso.symm (gammaLogicInput G)).target_definable (gammaLogicInput G)
  have hIG := gamma_restrictPointImage f D hDH hDG hfG
  have hMem : ∀ p ∈ carrier I, activeUnaryProjection 0 σ p ∈ carrier B :=
    fun p hp => ((Set.ext_iff.mp hImage p).mp hp).1
  let F : I → B := fun p => ⟨activeUnaryProjection 0 σ p.val,hMem p.val p.property⟩
  have hFComm (d : D) : F (g d) = u.toMap (P.iso.equiv d) := Subtype.ext (hCommD d)
  have hFBij : Function.Bijective F := by
    constructor
    · intro p q he
      obtain ⟨d,rfl⟩ := hgBij.2 p
      obtain ⟨e,rfl⟩ := hgBij.2 q
      rw [hFComm,hFComm] at he
      exact congrArg g (P.iso.equiv.injective (u.bijective.1 he))
    · intro b
      let d := P.iso.equiv.symm (u.inverseMap b)
      refine ⟨g d,?_⟩
      rw [hFComm,P.iso.equiv.apply_symm_apply,u.apply_inverse]
  have hFΓ : GammaGraphDefinable G (fun p q => ∃ a : I, a.val = p ∧ (F a).val = q) := by
    let X := PresentedSet.univ (pointSpace (M := M) 1 r) G.real
    apply GammaGraphDefinable.congr ((gammaLogicInput G).restrict_graph hIG
      ((gammaLogicInput G).real_map_graph (activeUnaryProjectionMap 0 σ X)))
    intro p q
    constructor
    · rintro ⟨hp,a,ha,hq⟩
      exact ⟨⟨p,hp⟩,rfl,(congrArg (activeUnaryProjection 0 σ) ha).symm.trans hq⟩
    · rintro ⟨p,hp,hq⟩
      exact ⟨hp ▸ p.property,⟨p.val,Set.mem_univ _⟩,hp,hq⟩
  let J : GammaIso G (carrier I) (carrier B) := ⟨Equiv.ofBijective F hFBij,hFΓ⟩
  have hJRV (p q : I) : SameRV (J.equiv p).val (J.equiv q).val ↔ SameRV p.val q.val := by
    constructor
    · intro he
      obtain ⟨d,rfl⟩ := hgBij.2 p
      obtain ⟨e,rfl⟩ := hgBij.2 q
      have hProj : SameRV (activeUnaryProjection 0 σ (g d).val) (activeUnaryProjection 0 σ (g e).val) := he
      change SameRV (F (g d)).val (F (g e)).val at he
      rw [hFComm,hFComm] at he
      have hInv := u.inverse_contractible (u.toMap (P.iso.equiv d)) (u.toMap (P.iso.equiv e)) he
      rw [u.inverse_apply,u.inverse_apply] at hInv
      have hDSame := (P.sameRV d e).mp hInv
      obtain ⟨hv,hl⟩ := (sameRV_iff _ _).mp hProj
      apply (sameRV_iff _ _).mpr
      refine ⟨fun i => by fin_cases i; exact hv 0,?_⟩
      funext j
      rcases hCover j with ⟨k,rfl⟩ | ⟨k,rfl⟩
      · exact congrFun hl k
      · exact (specialRelative_oldLabels (specialRelativeBoundary_forget hf) ⟨d.val,hDH d.property⟩ k).trans
          ((congrFun ((sameRV_iff _ _).mp hDSame).2 k).trans
            (specialRelative_oldLabels (specialRelativeBoundary_forget hf) ⟨e.val,hDH e.property⟩ k).symm)
    · exact activeUnaryProjection_sameRV 0 σ
  have hIEq : carrier I = {q | ∃ p : H, p.val.2 ∘ ρ ∈ E ∧ (f p).val = q} := by
    ext q
    exact ⟨fun ⟨d,hd⟩ => ⟨⟨d.val,hDH d.property⟩,((Set.ext_iff.mp hD d.val).mp d.property).2,hd⟩,
      fun ⟨p,hp,hpq⟩ => ⟨⟨p.val,(Set.ext_iff.mp hD p.val).mpr ⟨p.property,hp⟩⟩,hpq⟩⟩
  exact ⟨⟨r,K,f,σ,hle,hf,hfG,hK,hCompat,I,hIEq,⟨J,fun _ => rfl,hJRV⟩,hSat,hIG,hOff,hOffRV,hEnd⟩⟩

end IntegrationInACVF.Section5
