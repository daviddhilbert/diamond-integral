import IntegrationSection5.GammaSpecialRestriction
import IntegrationSection5.RelativeLabelPreservation
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
variable {S : Set M} {n m l : ℕ}
variable {A X : DefSet (M := M) S n m} {Y : DefSet (M := M) S n l}

theorem restrictPointImage_rvSlice (f : Map X Y) (hf : Function.Surjective f)
    (ρ : Fin m → Fin l) (hLabels : ∀ a : X, (f a).val.2 ∘ ρ = a.val.2)
    (E : Set (Fin m → RV (M := M)))
    (hA : carrier A = {p | p ∈ carrier X ∧ p.2 ∈ E}) (hAX : carrier A ⊆ carrier X) :
    carrier (restrictPointImage f A hAX) = {q | q ∈ carrier Y ∧ q.2 ∘ ρ ∈ E} := by
  ext q
  constructor
  · rintro ⟨a,rfl⟩
    let x : X := ⟨a.val,hAX a.property⟩
    change (f x).val ∈ carrier Y ∧ (f x).val.2 ∘ ρ ∈ E
    rw [hLabels]
    exact ⟨(f x).property,((Set.ext_iff.mp hA a.val).mp a.property).2⟩
  · rintro ⟨hq,hE⟩
    obtain ⟨x,hx⟩ := hf ⟨q,hq⟩
    have hxv : (f x).val = q := congrArg (fun z : Y => z.val) hx
    have hxE : x.val.2 ∈ E := by rw [← hLabels x,hxv]; exact hE
    let a : A := ⟨x.val,(Set.ext_iff.mp hA x.val).mpr ⟨x.property,hxE⟩⟩
    exact ⟨a,hxv⟩

theorem headKey_oldRV {n : ℕ} (p : Point (M := M) (n+1) m) :
    (headKey p).2 ∘ Fin.natAdd 1 = p.2 := by
  funext j
  simp only [headKey,Function.comp_apply,Fin.append_right]

theorem headImage_rvSlice {n : ℕ} {A X : DefSet (M := M) S (n+1) m}
    {a : ℕ} (ρ : Fin a → Fin m) (E : Set (Fin a → RV (M := M)))
    (hA : carrier A = {p | p ∈ carrier X ∧ p.2 ∘ ρ ∈ E}) :
    carrier (headImage A) =
      {q | q ∈ carrier (headImage X) ∧ q.2 ∘ (Fin.natAdd 1 ∘ ρ) ∈ E} := by
  rw [headImage_carrier,headImage_carrier]
  ext q
  constructor
  · rintro ⟨p,hp,rfl⟩
    have h := (Set.ext_iff.mp hA p).mp hp
    refine ⟨⟨p,h.1,rfl⟩,?_⟩
    have he : (headKey p).2 ∘ (Fin.natAdd 1 ∘ ρ) = p.2 ∘ ρ := by
      exact congrArg (fun s => s ∘ ρ) (headKey_oldRV p)
    rw [he]
    exact h.2
  · rintro ⟨⟨p,hp,rfl⟩,hE⟩
    have he : (headKey p).2 ∘ (Fin.natAdd 1 ∘ ρ) = p.2 ∘ ρ := by
      exact congrArg (fun s => s ∘ ρ) (headKey_oldRV p)
    rw [he] at hE
    exact ⟨p,(Set.ext_iff.mp hA p).mpr ⟨hp,hE⟩,rfl⟩

end IntegrationInACVF.Section5
