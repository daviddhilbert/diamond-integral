import «section 5».OriginalRVTotalFamilies
import «section 3».GammaGroundRVUnitDomains

/-! Full original Gamma-domain rows give actual mixed families on raw RV
bases, including zero parameters. The complete code preimage is proved. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section
namespace DiamondIntegral.Section5
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section3.GammaParameters
open IntegrationInACVF.Section3 IntegrationInACVF.Section3ACVF IntegrationInACVF.Section6
open DiamondIntegral.Section3 DiamondIntegral.Section4 Section3RVCodeBridge
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {p n : ℕ}

theorem originalRawGammaFamily_definable
    (X : GammaGroundDefSet hc B (rawRVSpace (M := M) p))
    (D : GammaDomainFormula B p n (fun _ => .rv))
    (hD : ∀ x : X, originalGammaSourceValid hc D (rvValues x.val)) :
    GammaGroundDefinable hc B ((rawRVSpace (M := M) p).prod ((volumeGammaSpace hc).power (Fin n)))
      {q | q.1 ∈ X.carrier ∧ q.2 ∈ originalGammaSourceRow hc D (rvValues q.1)} := by
  let Q := (rawRVSpace (M := M) p).prod ((volumeGammaSpace hc).power (Fin n))
  have hQ : ∀ c ∈ Q.domain, ∀ i, iRV (c i) := by
    intro c hdom i
    cases i with
    | inl j =>
      obtain ⟨x,hx⟩ := hdom.1
      exact (congrArg (fun v => iRV (v j)) hx).mp (x j).property
    | inr j => exact gammaPower_code_proper (M := M) hc (c ∘ Sum.inr) hdom.2 j
  apply (gammaGroundDefinable_iff_full_rv_codes Q hQ _).mpr
  let ψ : Fin (p+n) → Fin p ⊕ (Fin n × Fin 1) :=
    Fin.append Sum.inl (fun j => Sum.inr (j,0))
  have hraw : FullRawDefinable (integrationGammaBase B)
      (fun c : Fin p ⊕ (Fin n × Fin 1) → M => c ∘ Sum.inl ∈ rawDomain X ∧ c ∘ ψ ∈ D.val) :=
    FullRawDefinable.and
      (FullRawDefinable.reindex (integrationGammaDefinable (rawDomain_definable X))
        (Sum.inl : Fin p → Fin p ⊕ (Fin n × Fin 1)))
      (FullRawDefinable.reindex (integrationGammaDefinable (allRVGammaDomain_definable D)) ψ)
  apply FullBaseAtomicity.OverBase.congr hraw
  intro c
  let v : Fin n → M := fun j => c (Sum.inr (j,0))
  have hψ : c ∘ ψ = Fin.append (c ∘ Sum.inl) v := by
    funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;>
      simp only [ψ,Function.comp_def,Fin.append_left,Fin.append_right,v]
  have hg (hd : c ∘ Sum.inr ∈ ((volumeGammaSpace hc).power (Fin n)).domain) :
      ((volumeGammaSpace hc).power (Fin n)).decode ⟨c ∘ Sum.inr,hd⟩ = codeValue ∘ v := by
    funext j
    exact (codeValue_raw ⟨⟨c (Sum.inr (j,0)),(hd j).1⟩,(hd j).2⟩).symm
  change ((c ∘ Sum.inl) ∈ rawDomain X ∧ c ∘ ψ ∈ D.val) ↔
    ∃ hd : c ∈ Q.domain, (Q.decode ⟨c,hd⟩).1 ∈ X.carrier ∧
      (Q.decode ⟨c,hd⟩).2 ∈ originalGammaSourceRow hc D (rvValues (Q.decode ⟨c,hd⟩).1)
  rw [hψ]
  constructor
  · rintro ⟨⟨x,hx,hxc⟩,hd⟩
    have hdx : Fin.append (rvValues x) v ∈ D.val := hxc.symm ▸ hd
    have hr := (originalGammaSourceRow_represents hc D (rvValues x) (hD ⟨x,hx⟩) v).mp
      ((gammaDomainSyntax_realize hc B D (rvValues x) v).mpr hdx)
    have hγdom : c ∘ Sum.inr ∈ ((volumeGammaSpace hc).power (Fin n)).domain := by
      intro j
      exact hr.1 j
    let hdom : c ∈ Q.domain := ⟨⟨x,hxc⟩,hγdom⟩
    have he : (rawRVSpace p).decode ⟨c ∘ Sum.inl,hdom.1⟩ = x :=
      rvValues_injective ((rvValues_decode _).trans hxc.symm)
    refine ⟨hdom,?_,?_⟩
    · change (rawRVSpace p).decode ⟨c ∘ Sum.inl,hdom.1⟩ ∈ X.carrier
      exact he.symm ▸ hx
    · change ((volumeGammaSpace hc).power (Fin n)).decode ⟨c ∘ Sum.inr,hγdom⟩ ∈
        originalGammaSourceRow hc D (rvValues ((rawRVSpace p).decode ⟨c ∘ Sum.inl,hdom.1⟩))
      rw [he,hg hγdom]
      exact hr.2
  · rintro ⟨hd,hx,hγ⟩
    let x : X := ⟨(rawRVSpace p).decode ⟨c ∘ Sum.inl,hd.1⟩,hx⟩
    have he : rvValues x.val = c ∘ Sum.inl := rvValues_decode _
    refine ⟨⟨x.val,x.property,he⟩,?_⟩
    have hval : codeValue ∘ v ∈ originalGammaSourceRow hc D (rvValues x.val) := by
      exact hg hd.2 ▸ hγ
    have hproper : Proper v := fun j => hd.2 j
    have hv := (originalGammaSourceRow_represents hc D (rvValues x.val) (hD x) v).mpr ⟨hproper,hval⟩
    have hm := (gammaDomainSyntax_realize hc B D (rvValues x.val) v).mp hv
    exact he ▸ hm

def originalRawGammaFamily
    (X : GammaGroundDefSet hc B (rawRVSpace (M := M) p))
    (D : GammaDomainFormula B p n (fun _ => .rv))
    (hD : ∀ x : X, originalGammaSourceValid hc D (rvValues x.val)) :
    GammaGroundDefSet hc B ((rawRVSpace (M := M) p).prod ((volumeGammaSpace hc).power (Fin n))) :=
  ⟨{q | q.1 ∈ X.carrier ∧ q.2 ∈ originalGammaSourceRow hc D (rvValues q.1)},
    originalRawGammaFamily_definable X D hD⟩

end DiamondIntegral.Section5
