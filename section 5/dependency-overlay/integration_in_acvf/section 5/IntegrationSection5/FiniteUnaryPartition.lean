import IntegrationSection5.FiniteMixedRVFibres
import IntegrationSection5.UnaryPartition
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section5 SpecialTransformations.Section3
namespace IntegrationInACVF.Section5
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {G : GammaParameters.Base (M := M)} {n m l : ℕ}

theorem finite_mixed_rv_fibres_mono {A D : Set (Point (M := M) n m)}
    (hA : FiniteMixedRVFibres A) (hDA : D ⊆ A) : FiniteMixedRVFibres D :=
  fun x => (hA x).subset (fun _ ht => hDA ht)

def FiniteGammaUnaryChain {a b : ℕ} {A : Set (Point (M := M) n a)} {B : Set (Point (M := M) n b)} :
    GammaUnaryChain G n A B → Prop
  | .nil A _ => FiniteMixedRVFibres A
  | .cons _ _ _ tail => FiniteMixedRVFibres A ∧ FiniteGammaUnaryChain tail

theorem finite_gamma_unary_chain {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (hsmall : Cardinal.mk G.real < κ)
    {A : Set (Point (M := M) n m)} {B : Set (Point (M := M) n l)}
    (T : GammaUnaryChain G n A B) (hA : FiniteMixedRVFibres A) : FiniteGammaUnaryChain T := by
  induction T with
  | nil A hΓ => exact hA
  | cons i e hu tail ih => exact ⟨hA,ih (GammaIso.finite_mixed_rv_fibres hκ hs hsmall e hA)⟩

theorem lemma_5_6_finite {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00) (hsmall : Cardinal.mk G.real < κ)
    (δ : Values.Gamma (M := M)) (hδ : 1 < δ) {p m w : ℕ}
    {A : Set (Point (M := M) (p+1) m)} {B : Set (Point (M := M) (p+1) w)}
    (f : A → B) (hbij : Function.Bijective f)
    (hf : GammaGraphDefinable G (fun x y => ∃ a : A, a.val = x ∧ (f a).val = y))
    (hFinite : FiniteMixedRVFibres A) :
    ∃ Q : GammaUnaryPartition (⟨Equiv.ofBijective f hbij,hf⟩ : GammaIso G A B),
      Nonempty (RealizedUnaryPartition G.real (⟨Equiv.ofBijective f hbij,hf⟩ : GammaIso G A B) Q) ∧
      ∀ D (hD : D ∈ Q.pieces), ∃ C : Set (Point (M := M) (p+1) w),
        ∃ T : GammaUnaryChain G (p+1) D C, FiniteGammaUnaryChain T ∧
          ∀ a : D, (T.toIso.equiv a).val = (f ⟨a.val,Q.subset D hD a.property⟩).val := by
  obtain ⟨Q,hReal⟩ := lemma_5_6 hκ hs h00 hsmall δ hδ f hbij hf
  refine ⟨Q,hReal,?_⟩
  intro D hD
  obtain ⟨C,T,hSquare⟩ := Q.factors D hD
  exact ⟨C,T,finite_gamma_unary_chain hκ hs hsmall T
    (finite_mixed_rv_fibres_mono hFinite (Q.subset D hD)),hSquare⟩

end IntegrationInACVF.Section5
