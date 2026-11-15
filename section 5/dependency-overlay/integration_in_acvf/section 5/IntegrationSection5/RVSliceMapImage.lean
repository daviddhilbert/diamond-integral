import IntegrationSection5.FixedVFProjectionPadding
import IntegrationSection5.GammaSpecialRestriction
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section5
namespace IntegrationInACVF.Section5
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {G : SpecialTransformations.Section3.GammaParameters.Base (M := M)}
variable {S : Set M} {n m l a : ℕ}
variable {X D : DefSet (M := M) S n m} {Y : DefSet (M := M) S n l}

theorem rvSlice_map_image (f : Map X Y) (hf : Function.Surjective f)
    (ρ : Fin a → Fin m) (σ : Fin m → Fin l)
    (hLabels : ∀ p : X, (f p).val.2 ∘ σ = p.val.2)
    (E : Set (Fin a → RV (M := M)))
    (hD : carrier D = {p | p ∈ carrier X ∧ p.2 ∘ ρ ∈ E}) :
    carrier (restrictPointImage f D (fun _ hp => ((Set.ext_iff.mp hD _).mp hp).1)) =
      {q | q ∈ carrier Y ∧ q.2 ∘ (σ ∘ ρ) ∈ E} := by
  ext q
  constructor
  · rintro ⟨p,hpq⟩
    let x : X := ⟨p.val,((Set.ext_iff.mp hD p.val).mp p.property).1⟩
    have he : (f x).val = q := hpq
    refine ⟨he ▸ (f x).property,?_⟩
    have h := ((Set.ext_iff.mp hD p.val).mp p.property).2
    have hl := congrArg (fun s => s ∘ ρ) (hLabels x)
    change (f x).val.2 ∘ (σ ∘ ρ) = p.val.2 ∘ ρ at hl
    rwa [← he,hl]
  · rintro ⟨hq,he⟩
    obtain ⟨p,hp⟩ := hf ⟨q,hq⟩
    have hval : (f p).val = q := congrArg Subtype.val hp
    have hl := congrArg (fun s => s ∘ ρ) (hLabels p)
    have hFlag : p.val.2 ∘ ρ ∈ E := by
      change (f p).val.2 ∘ (σ ∘ ρ) = p.val.2 ∘ ρ at hl
      rw [← hl,hval]
      exact he
    exact ⟨⟨p.val,(Set.ext_iff.mp hD p.val).mpr ⟨p.property,hFlag⟩⟩,hval⟩

variable {X D : DefSet (M := M) S 1 m} {Y : DefSet (M := M) S 1 l}

def inactiveProjectionPadding (f : Map X Y) (hf : Function.Bijective f)
    (hDX : carrier D ⊆ carrier X) (hDΓ : GammaSetDefinable G (carrier D))
    (hfG : GammaGraphDefinable G (pointMapGraph f))
    (hVF : ∀ p : D, vfAt (f ⟨p.val,hDX p.property⟩).val 0 = vfAt p.val 0)
    (σ : Fin m → Fin l) (hLabels : ∀ p : X, (f p).val.2 ∘ σ = p.val.2)
    (hRV : ∀ p q : D, SameRV p.val q.val →
      SameRV (f ⟨p.val,hDX p.property⟩).val (f ⟨q.val,hDX q.property⟩).val) :
    RVProjectionPadding (G := G) (restrictPointImage f D hDX) D σ := by
  let g := restrictPointMap f D hDX
  have hg : Function.Bijective g := by
    refine ⟨?_,restrictPointMap_surjective f D hDX⟩
    intro p q he
    have hEq : f ⟨p.val,hDX p.property⟩ = f ⟨q.val,hDX q.property⟩ :=
      Subtype.ext (congrArg (fun z : restrictPointImage f D hDX => z.val) he)
    exact Subtype.ext (congrArg (fun z : X => z.val) (hf.1 hEq))
  refine fixedVFProjectionPadding g hg (gamma_restrictPointMap f D hDX hDΓ hfG) ?_ σ ?_ hRV
  · intro p i
    fin_cases i
    exact hVF p
  · intro p
    exact hLabels ⟨p.val,hDX p.property⟩

end IntegrationInACVF.Section5
