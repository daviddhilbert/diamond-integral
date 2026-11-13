import «section 3».IntegrationMixedFibres
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open IntegrationInACVF.Section3 IntegrationInACVF.Section3ACVF
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

theorem integrationMixed_reconstruct {r : ℕ} (x : Section2.Mixed M 1 r) :
    ((fun _ : Fin 1 => x.1 0),x.2) = x := by
  apply Prod.ext
  · funext i
    have hi : i = (0 : Fin 1) := Subsingleton.elim _ _
    rw [hi]
  · rfl

theorem IntegrationMixedPaperFibres.mono {r s : ℕ} {A C : Set (Section2.Mixed M 1 r)}
    {f : Section2.Mixed M 1 r → Section2.Mixed M 1 s}
    (h : IntegrationMixedPaperFibres A f) (hCA : C ⊆ A) : IntegrationMixedPaperFibres C f :=
  fun t u D hD => h t u D (fun x hx => ⟨hCA (hD x hx).1,(hD x hx).2⟩)

/-- The iff on every fixed-label fibre transports to the actual inverse.
No definability assumption on a chosen inverse is used. -/
theorem IntegrationMixedPaperFibres.inverse {r s : ℕ}
    {A : Set (Section2.Mixed M 1 r)} {B : Set (Section2.Mixed M 1 s)}
    {f : Section2.Mixed M 1 r → Section2.Mixed M 1 s}
    {g : Section2.Mixed M 1 s → Section2.Mixed M 1 r}
    (h : IntegrationMixedPaperFibres A f) (hg : Set.MapsTo g B A) (hinv : Set.InvOn g f A B) :
    IntegrationMixedPaperFibres B g := by
  intro t u D hD
  let E : Set (Section2.VF M) := (fun y => (g ((fun _ => y),t)).1 0) '' D
  have hG (y : Section2.VF M) (hy : y ∈ D) :
      ((fun _ => (g ((fun _ => y),t)).1 0),u) = g ((fun _ => y),t) := by
    rw [← (hD y hy).2]
    exact integrationMixed_reconstruct _
  have hE : ∀ x ∈ E, ((fun _ => x),u) ∈ A ∧ (f ((fun _ => x),u)).2 = t := by
    rintro x ⟨y,hy,rfl⟩
    rw [hG y hy]
    exact ⟨hg (hD y hy).1,congrArg Prod.snd (hinv.2 (hD y hy).1)⟩
  have hImage : (fun x => (f ((fun _ => x),u)).1 0) '' E = D := by
    ext y
    constructor
    · rintro ⟨_,⟨z,hz,rfl⟩,rfl⟩
      dsimp only
      rw [hG z hz,hinv.2 (hD z hz).1]
      exact hz
    · intro hy
      refine ⟨(g ((fun _ => y),t)).1 0,⟨y,hy,rfl⟩,?_⟩
      dsimp only
      rw [hG y hy,hinv.2 (hD y hy).1]
  have he := h u t E hE
  rw [hImage] at he
  exact he.symm
end DiamondIntegral.Section3
