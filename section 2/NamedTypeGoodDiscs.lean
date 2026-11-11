import «section 2».NamedTaggedImages
import «section 2».PrefixedPolydiscAtomicity
import «section 2».NamedDiscExtensions
import «section 2».RawTaggedPolydiscs

/-! The type-local good-disc assertion over the retained DC ground tuple
follows from the proved 2.25 and 2.29, with their cited unary inputs. -/

set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
namespace DiamondIntegral.Section2
variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

theorem rawGoodTaggedPolydiscCodes_of_branches {n : ℕ}
    (d : Fin (n+n) → M) (P : Set (Fin n → M)) (he : rawOpenPolydisc d = P)
    (F : Set ((Fin n → M) × M)) (T : Set (RVInfinity M))
    (g : RVInfinity M → (Fin n → M) → M)
    (hshape : ∀ t ∈ T, (∃ c : VF M, ∀ x ∈ P, g t x = c.val) ∨ IsOpenDisc (g t '' P))
    (hbranch : ∀ t ∈ T, ∀ x ∈ P, ∀ y, ((x,y) ∈ F ∧ iRv y = t.val) ↔ g t x = y)
    (hcover : ∀ x ∈ P, ∀ y, (x,y) ∈ F ↔ ∃ t ∈ T, g t x = y) :
    d ∈ rawGoodTaggedPolydiscCodes F := by
  constructor
  · intro t ht x hx
    obtain ⟨y,u,hu,huy,hyt⟩ := ht
    obtain ⟨s,hs,hsy⟩ := (hcover u (he ▸ hu) y).mp huy
    have hst := ((hbranch s hs u (he ▸ hu) y).mpr hsy).2
    have hf := (hbranch s hs x (he ▸ hx) (g s x)).mpr rfl
    exact ⟨g s x,hf.1,hf.2.trans (hst.symm.trans hyt)⟩
  · intro t
    apply rawDiscShapeCodes_of_shape
    intro hne
    obtain ⟨y,u,hu,huy,hyt⟩ := hne
    obtain ⟨s,hs,hsy⟩ := (hcover u (he ▸ hu) y).mp huy
    have hst := ((hbranch s hs u (he ▸ hu) y).mpr hsy).2
    have hI : rawTaggedPolydiscImage F (Sum.elim d t) = g s '' P := by
      ext v
      constructor
      · rintro ⟨x,hx,hxv,hvt⟩
        exact ⟨x,he ▸ hx,(hbranch s hs x (he ▸ hx) v).mp ⟨hxv,hvt.trans (hyt.symm.trans hst)⟩⟩
      · rintro ⟨x,hx,rfl⟩
        have hf := (hbranch s hs x hx (g s x)).mpr rfl
        exact ⟨x,he.symm ▸ hx,hf.1,hf.2.trans (hst.symm.trans hyt)⟩
    rw [hI]
    rcases hshape s hs with ⟨c,hc⟩ | hopen
    · left
      rintro v ⟨x,hx,rfl⟩ w ⟨z,hz,rfl⟩
      exact (hc x hx).trans (hc z hz).symm
    · exact Or.inr hopen

theorem type_good_tagged_polydisc_code_disc_names
    (hc : CanonicalStructure.IsCanonical (M := M)) (h00 : M ⊨ Axioms.ACVF00)
    (B : ParameterBase M) (hΓ : NontrivialDefinableGamma B)
    (unary : ∀ E : ParameterBase M, UnaryDiscAtomicityInput E)
    (gamma : ∀ E : ParameterBase M, AtomicDiscGammaBaseChangeInput E)
    (rvbase : ∀ E : ParameterBase M, UnaryOpenDiscRVBaseChangeInput E)
    (image : ∀ E : ParameterBase M, OpenDiscNamesImageInput E)
    {k n : ℕ} (ground : Fin k → Bool) (b : Fin k → VF M) (τ : Fin k → Gamma M)
    (d : Fin (n+n) → M) (hd : rawOpenPolydiscProper d)
    (A : Set (Fin n → M)) (hA : GeneratesTypeOverFiniteDiscNames B ground b τ (fun _ => .vf) A)
    (hsub : rawOpenPolydisc d ⊆ A) (F : Set ((Fin n → M) × M))
    (hF : DefinableOverFiniteDiscNames B ground b τ (fun _ : Fin (n+1) => .vf)
      {z | (Fin.init z,z (Fin.last n)) ∈ F})
    (hfinite : ∀ x ∈ rawOpenPolydisc d, {y | (x,y) ∈ F}.Finite)
    (hrv : ∀ x ∈ rawOpenPolydisc d, Set.InjOn iRv {y | (x,y) ∈ F}) :
    d ∈ rawGoodTaggedPolydiscCodes F := by
  obtain ⟨a,δ,he⟩ := rawOpenPolydisc_presentation d hd
  let D (i : Fin n) := BallImaginaries.underlying (openDiscCode (a i) (δ i))
  have hopen (i) : IsOpenDisc (D i) := ⟨a i,δ i,rfl⟩
  have hDP : {x | ∀ i, x i ∈ D i} = namedPolydisc (fun _ => false) a δ := rfl
  have hAtomic := lemma_2_25_with_disc_ground hc h00 B hΓ unary gamma ground b τ
    (fun _ => false) a δ A hA (he ▸ hsub)
  rw [← hDP] at hAtomic
  have hFAll := hF.append_names_left (fun _ : Fin n => false) a δ
  obtain ⟨T,_,_,g,hg,hcov⟩ := lemma_2_29_disc_names hc h00 B hΓ rvbase image
    (Fin.append ground (fun _ => false)) (Fin.append b a) (Fin.append τ δ) D hopen hAtomic F hFAll
    (by rw [hDP,← he]; exact hfinite) (by rw [hDP,← he]; exact hrv)
  apply rawGoodTaggedPolydiscCodes_of_branches d _ (he.trans hDP.symm) F T g
  · intro t ht
    exact ((hg t ht).2.1).imp_right And.right
  · exact fun t ht => (hg t ht).2.2
  · exact hcov

end DiamondIntegral.Section2
