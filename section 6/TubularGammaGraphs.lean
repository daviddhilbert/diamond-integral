import «section 6».TubularGeometry

/-! The full Gamma graph of the tubular extension is obtained by
existentially quantifying only the old VF point. All old RV labels and all
codes of the output Gamma value remain in the complete graph. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open DiamondIntegral.Section2

namespace DiamondIntegral.Section6

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n r : ℕ} {S : Set M}

def tubeGammaIndex (n r : ℕ) : Fin (n+r) ⊕ Fin 1 → (Fin (n+r) ⊕ Fin 1) ⊕ Fin n :=
  Sum.elim (Fin.addCases Sum.inr (fun j => .inl (.inl (Fin.natAdd n j)))) (fun _ => .inl (.inr 0))

def tubeComparisonIndex (n r : ℕ) : Fin n ⊕ Fin n → (Fin (n+r) ⊕ Fin 1) ⊕ Fin n :=
  Sum.elim Sum.inr (fun i => .inl (.inl (Fin.castAdd r i)))

def tubularGammaRelation (δ : Gamma M) (A : Set (Mixed M n r)) (f : Mixed M n r → Gamma M) :
    Set (Fin (n+r) ⊕ Fin 1 → M) := {z | GammaParameters.NonzeroRV (z (.inr 0)) ∧
      ∃ p ∈ A, ∃ x : Fin n → VF M, Congruent (fun _ => δ) p.1 x ∧
        mixedTuple (x,p.2) = z ∘ Sum.inl ∧ GammaParameters.codeValue (z (.inr 0)) = f p}

theorem tubularGammaRelation_definable (δ : Gamma M)
    (hδ : S.Definable LRV {z : Fin 1 → M | z 0 ∈ Values.gammaPullback {δ}})
    (A : Set (Mixed M n r)) (f : Mixed M n r → Gamma M)
    (hf : S.Definable LRV (mixedGammaGraph A f)) : S.Definable LRV (tubularGammaRelation δ A f) := by
  have h := ((hf.preimage_comp (tubeGammaIndex n r)).inter
    ((named_scalar_congruence_definable (m := n) δ hδ).preimage_comp (tubeComparisonIndex n r))).exists_of_finite
  convert h using 1
  ext z
  constructor
  · rintro ⟨ht,p,hp,x,hclose,hcode,hout⟩
    refine ⟨vfValues p.1,⟨ht,p,hp,?_,hout⟩,⟨p.1,x,hclose,?_⟩⟩
    · funext i
      refine Fin.addCases (fun i => ?_) (fun i => ?_) i
      · simp only [mixedTuple,Fin.append_left,Function.comp_apply,tubeGammaIndex,Sum.elim_inl,
          Fin.addCases_left,Sum.elim_inr]
      · have he := congrFun hcode (Fin.natAdd n i)
        simpa only [mixedTuple,Fin.append_right,Function.comp_apply,tubeGammaIndex,Sum.elim_inl,
          Fin.addCases_right] using he
    · funext i
      cases i with
      | inl i => rfl
      | inr i =>
        have he := congrFun hcode (Fin.castAdd r i)
        simpa only [mixedTuple,Fin.append_left,Function.comp_apply,tubeComparisonIndex,Sum.elim_inr,
          Sum.elim_inl] using he
  · rintro ⟨w,⟨ht,p,hp,hsource,hout⟩,⟨a,x,hclose,hcompare⟩⟩
    have hpa : p.1 = a := by
      funext i
      apply Subtype.ext
      have h₁ := congrFun hsource (Fin.castAdd r i)
      have h₂ := congrFun hcompare (.inl i)
      simp only [mixedTuple,Fin.append_left,Function.comp_apply,tubeGammaIndex,Sum.elim_inl,
        Fin.addCases_left,Sum.elim_inr] at h₁
      simp only [Function.comp_apply,tubeComparisonIndex,Sum.elim_inl,Sum.elim_inr] at h₂
      exact h₁.trans h₂.symm
    refine ⟨ht,p,hp,x,hpa.symm ▸ hclose,?_,hout⟩
    funext i
    refine Fin.addCases (fun i => ?_) (fun i => ?_) i
    · have he := congrFun hcompare (.inr i)
      simpa only [mixedTuple,Fin.append_left,Function.comp_apply,tubeComparisonIndex,Sum.elim_inr,
        Sum.elim_inl] using he
    · have he := congrFun hsource (Fin.natAdd n i)
      simpa only [mixedTuple,Fin.append_right,Function.comp_apply,tubeGammaIndex,Sum.elim_inl,
        Fin.addCases_right] using he

theorem tubularExtension_graph (δ : Gamma M) (A : Set (Mixed M n r)) (f : Mixed M n r → Gamma M)
    (hconst : ∀ u, ∀ a ∈ vfFibre A u, ∀ b ∈ vfFibre A u,
      Congruent (fun _ => δ) a b → f (a,u) = f (b,u)) :
    mixedGammaGraph (tubularHull δ A) (tubularExtension δ A f) = tubularGammaRelation δ A f := by
  ext z
  constructor
  · rintro ⟨ht,p,⟨a,ha,hclose⟩,he,hout⟩
    exact ⟨ht,(a,p.2),ha,p.1,hclose,he,hout.trans (tubularExtension_value δ A f hconst ha hclose)⟩
  · rintro ⟨ht,p,hp,x,hclose,he,hout⟩
    exact ⟨ht,(x,p.2),⟨p.1,hp,hclose⟩,he,
      hout.trans (tubularExtension_value δ A f hconst (p := (x,p.2)) hp hclose).symm⟩

theorem mixedGammaGraph_domain_codes (A : Set (Mixed M n r)) (f : Mixed M n r → Gamma M) :
    (fun z => z ∘ (Sum.inl : Fin (n+r) → Fin (n+r) ⊕ Fin 1)) '' mixedGammaGraph A f = mixedTuple '' A := by
  ext z
  constructor
  · rintro ⟨w,⟨_,p,hp,he,_⟩,hz⟩
    exact ⟨p,hp,he.trans hz⟩
  · rintro ⟨p,hp,rfl⟩
    obtain ⟨t,ht,htf⟩ := GammaParameters.EndpointLogic.codeValue_surjective (f p)
    exact ⟨Sum.elim (mixedTuple p) (fun _ => t),⟨ht,p,hp,rfl,htf⟩,rfl⟩

theorem mixedTuple_image_definable_iff (A : Set (Mixed M n r)) :
    S.Definable LRV (mixedTuple '' A) ↔ (rawMixedSpace (M := M) n r).Definable S A := by
  constructor
  · intro h
    apply (mixed_definable_iff_values_image S A).mpr
    let π : Fin (n+r) → Fin n ⊕ Fin r := Fin.addCases Sum.inl Sum.inr
    convert h.preimage_comp π using 1
    ext z
    constructor
    · rintro ⟨p,hp,rfl⟩
      refine ⟨p,hp,?_⟩
      funext i
      refine Fin.addCases (fun i => ?_) (fun i => ?_) i
      · simp only [Function.comp_apply,π,Fin.addCases_left,mixedTuple,Fin.append_left]
        rfl
      · simp only [Function.comp_apply,π,Fin.addCases_right,mixedTuple,Fin.append_right]
        rfl
    · rintro ⟨p,hp,he⟩
      refine ⟨p,hp,?_⟩
      funext i
      cases i with
      | inl i =>
        simpa only [Function.comp_apply,π,Fin.addCases_left,mixedTuple,Fin.append_left,mixedValues,Sum.elim_inl]
          using congrFun he (Fin.castAdd r i)
      | inr i =>
        simpa only [Function.comp_apply,π,Fin.addCases_right,mixedTuple,Fin.append_right,mixedValues,Sum.elim_inr]
          using congrFun he (Fin.natAdd n i)
  · exact mixed_tuple_image_definable S A

end DiamondIntegral.Section6
