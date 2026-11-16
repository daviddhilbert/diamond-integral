import «section 6».ProperMeasuredRVLifts

/-! Constant maps into the actual Gamma presentation retain every
representative of their named value. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M}

def constantPresentedMap {P Q : SpecialTransformations.DefinableGeometry.Space LRV M}
    (A : DefSet P S) (q : Q.Carrier) (hq : Q.Definable S {q}) : Map A (DefSet.univ Q S) := by
  refine ⟨fun _ => ⟨q,Set.mem_univ _⟩,?_⟩
  have h := (A.definable.preimage_comp (Sum.inl : P.Index → P.Index ⊕ Q.Index)).inter
    (hq.preimage_comp (Sum.inr : Q.Index → P.Index ⊕ Q.Index))
  change S.Definable LRV (P.relation Q (fun x y => ∃ a : A, a.val = x ∧ q = y))
  convert h using 1
  ext z
  constructor
  · rintro ⟨hx,hy,a,ha,hq⟩
    exact ⟨⟨hx,ha ▸ a.property⟩,hy,hq.symm⟩
  · rintro ⟨⟨hx,ha⟩,hy,hq⟩
    exact ⟨hx,hy,⟨P.decode ⟨z ∘ Sum.inl,hx⟩,ha⟩,rfl,hq.symm⟩

theorem gamma_named_singleton (γ : Gamma M)
    (hγ : S.Definable LRV {z : Fin 1 → M | z 0 ∈ Values.gammaPullback {γ}}) :
    (rawGammaPresentation (M := M)).Definable S {γ} := by
  change S.Definable LRV ((rawGammaPresentation (M := M)).preimage {γ})
  convert hγ using 1 <;> try rfl
  apply Set.ext
  intro (z : Fin 1 → M)
  constructor
  · rintro ⟨hz,he⟩
    exact (GammaParameters.gammaPullback_mem_codeValue_iff _ _ hz).mpr he
  · intro hz
    let ht : GammaParameters.NonzeroRV (z 0) := ⟨hz.1,hz.2.1⟩
    exact ⟨ht,(GammaParameters.gammaPullback_mem_codeValue_iff _ _ ht).mp hz⟩

def gammaOneMap {P : SpecialTransformations.DefinableGeometry.Space LRV M}
    (hc : CanonicalStructure.IsCanonical (M := M)) (A : DefSet P S) :
    Map A (DefSet.univ (rawGammaPresentation (M := M)) S) :=
  constantPresentedMap A (1 : Gamma M) (gamma_named_singleton 1 (gamma_one_named hc))

theorem gammaOneMap_value {P : SpecialTransformations.DefinableGeometry.Space LRV M}
    (hc : CanonicalStructure.IsCanonical (M := M)) (A : DefSet P S) (a : A) :
    gammaMapValue (gammaOneMap hc A) a = 1 := rfl

end DiamondIntegral.Section6
