import IntegrationSection5.SharedRVUnaryHeadPreparation
import IntegrationSection5.RelativeSpecialRestriction
import IntegrationSection5.InactiveHeadSaturation
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
variable {S : Set M} {n a b l r : ℕ}
variable {A : DefSet (M := M) S 1 a} {B : DefSet (M := M) S 1 b}
variable {H D : DefSet (M := M) S (n+1) l} {K : DefSet (M := M) S (n+1) r}

theorem headSaturated_rvBranch_product_lift (u : SpecialBijection A B)
    (hB : IsRVPullback (carrier B)) (f : Map H K) {previous ending : Option Bool}
    (hf : SpecialRelativeBoundary f 0 previous ending) (hle : l ≤ r)
    (ρ : Fin a → Fin l) (σ : Fin b → Fin r) (E : Set (Fin a → RV (M := M)))
    (hD : carrier D = {p | p ∈ carrier H ∧ p.2 ∘ ρ ∈ E})
    (Q : Point (M := M) (n+1) l → Prop) (hQ : ∀ p x, Q (replace 0 p x) ↔ Q p)
    (hProduct : carrier D = {p | activeUnaryProjection 0 ρ p ∈ carrier A ∧ Q p})
    (hHA : ∀ p ∈ carrier H, p.2 ∘ ρ ∈ E → activeUnaryProjection 0 ρ p ∈ carrier A)
    (hComm : ∀ p : H, ∀ hp : p.val.2 ∘ ρ ∈ E,
      activeUnaryProjection 0 σ (f p).val =
        (u.toMap ⟨activeUnaryProjection 0 ρ p.val,hHA p.val p.property hp⟩).val)
    (hCompat : ∀ j, σ (suffixIndex (special_chain_rvArity_le u.chain) j) = suffixIndex hle (ρ j))
    (hCover : ∀ j : Fin r, (∃ k, σ k = j) ∨ ∃ k, suffixIndex hle k = j)
    (hInactive : HeadSaturated {p | p ∈ carrier H ∧ p.2 ∘ ρ ∉ E})
    (hOffVF : ∀ p : H, p.val.2 ∘ ρ ∉ E → vfAt (f p).val 0 = vfAt p.val 0)
    (hOffRV : ∀ p q : H, p.val.2 ∘ ρ ∉ E → q.val.2 ∘ ρ ∉ E →
      SameRV p.val q.val → SameRV (f p).val (f q).val) : HeadSaturated (carrier K) := by
  have hDH : carrier D ⊆ carrier H := fun p hp => ((Set.ext_iff.mp hD p).mp hp).1
  let g := restrictPointMap f D hDH
  have hg := specialRelativeBoundary_restrict f D hDH hf
  have hCommD (p : D) : activeUnaryProjection 0 σ (g p).val =
      (u.toMap ⟨activeUnaryProjection 0 ρ p.val,((Set.ext_iff.mp hProduct p.val).mp p.property).1⟩).val := by
    exact hComm ⟨p.val,hDH p.property⟩ ((Set.ext_iff.mp hD p.val).mp p.property).2
  have hImage := coordinate_lift_product_image_sharedRV u g 0 (specialRelativeBoundary_forget hg)
    hle ρ σ Q hQ hProduct hCommD hCompat hCover
  have hSatActive := unary_product_head_saturated hB σ hle Q hQ hImage
  have hSatOff := headSaturated_unary_fixed_image f
    (specialRelative_unaryRelative (specialRelativeBoundary_forget hf))
    {p | p ∈ carrier H ∧ p.2 ∘ ρ ∉ E} (fun _ hp => hp.1) hInactive
    (fun p hp => hOffVF p hp.2) (fun p q hp hq he => hOffRV p q hp.2 hq.2 he)
  rintro p hp x hx
  obtain ⟨a,ha⟩ := (specialRelative_bijective (specialRelativeBoundary_forget hf)).2 ⟨p,hp⟩
  have hav : (f a).val = p := congrArg (fun q : K => q.val) ha
  by_cases he : a.val.2 ∘ ρ ∈ E
  · let aD : D := ⟨a.val,(Set.ext_iff.mp hD a.val).mpr ⟨a.property,he⟩⟩
    have hpActive : p ∈ carrier (restrictPointImage f D hDH) := ⟨aD,hav⟩
    obtain ⟨b,hb⟩ := hSatActive p hpActive x hx
    exact hb ▸ (f ⟨b.val,hDH b.property⟩).property
  · have hpOff : p ∈ {q | ∃ a : H, a.val ∈ {p | p ∈ carrier H ∧ p.2 ∘ ρ ∉ E} ∧ (f a).val = q} :=
      ⟨a,⟨a.property,he⟩,hav⟩
    obtain ⟨b,_,hb⟩ := hSatOff p hpOff x hx
    exact hb ▸ (f b).property

end IntegrationInACVF.Section5
