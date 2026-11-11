import «section 2».FiniteDiscInvariantHull

/-! Invariance of the presentation hull under both Gamma representatives
and actual DC names. The promoted real tuple remains a variable. -/

set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4

namespace DiamondIntegral.Section2
variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF] {k n p m : ℕ}

theorem gamma_raw_relation_invariant
    (H : Set (Fin p ⊕ (Fin (k+n) ⊕ Fin (n+m)) → M))
    (hH : ∀ v b (t u : Fin (k+n) → GammaParameters.Code (M := M)),
      GammaParameters.values t = GammaParameters.values u →
      (Sum.elim v (Sum.elim (GammaParameters.rawTuple t) b) ∈ H ↔
        Sum.elim v (Sum.elim (GammaParameters.rawTuple u) b) ∈ H))
    (v : Fin p → M) (b : Fin (n+m) → M) (c d : Fin (k+n) → M)
    (hc : GammaParameters.Proper c) (hd : GammaParameters.Proper d)
    (he : (fun i => GammaParameters.codeValue (c i)) = fun i => GammaParameters.codeValue (d i)) :
    Sum.elim v (Sum.elim c b) ∈ H ↔ Sum.elim v (Sum.elim d b) ∈ H := by
  have hval : GammaParameters.values (GammaParameters.ofRaw c hc) =
      GammaParameters.values (GammaParameters.ofRaw d hd) := by
    rw [raw_gamma_values_ofRaw,raw_gamma_values_ofRaw,he]
  have h := hH v b _ _ hval
  simpa only [GammaParameters.rawTuple_ofRaw] using h

theorem discInvariantHull_congr
    (closed : Fin n → Bool) (H : Set (Fin p ⊕ (Fin (k+n) ⊕ Fin (n+m)) → M))
    (hH : ∀ v b (t u : Fin (k+n) → GammaParameters.Code (M := M)),
      GammaParameters.values t = GammaParameters.values u →
      (Sum.elim v (Sum.elim (GammaParameters.rawTuple t) b) ∈ H ↔
        Sum.elim v (Sum.elim (GammaParameters.rawTuple u) b) ∈ H))
    (c d : Fin (k+n) → M) (hc : GammaParameters.Proper c) (hd : GammaParameters.Proper d)
    (z w : Fin (n+(p+m)) → M)
    (hdisc : finiteDiscRawEq closed (discHullCurrent c z) (discHullCurrent d w))
    (htail : z ∘ Fin.natAdd n = w ∘ Fin.natAdd n)
    (hprefix : ∀ i, GammaParameters.codeValue (c (Fin.castAdd n i)) =
      GammaParameters.codeValue (d (Fin.castAdd n i))) :
    discInvariantHull closed H c z ↔ discInvariantHull closed H d w := by
  have hstep (c d : Fin (k+n) → M) (hc : GammaParameters.Proper c) (hd : GammaParameters.Proper d)
      (z w : Fin (n+(p+m)) → M)
      (hdisc : finiteDiscRawEq closed (discHullCurrent c z) (discHullCurrent d w))
      (htail : z ∘ Fin.natAdd n = w ∘ Fin.natAdd n)
      (hprefix : ∀ i, GammaParameters.codeValue (c (Fin.castAdd n i)) =
        GammaParameters.codeValue (d (Fin.castAdd n i))) :
      discInvariantHull closed H c z → discInvariantHull closed H d w := by
    rintro ⟨q,hq,hHq⟩
    have he : finiteDiscRawNames closed (discHullCurrent c z) =
        finiteDiscRawNames closed (discHullCurrent d w) :=
      (finiteDiscRawEq_iff closed _ _ hdisc.1 hdisc.2.1).mp hdisc
    refine ⟨q,(finiteDiscRawEq_congr_left closed _ _ q hdisc.1 hdisc.2.1 he).mp hq,?_⟩
    let c' := Fin.append (c ∘ Fin.castAdd n) (q ∘ Fin.natAdd n)
    let d' := Fin.append (d ∘ Fin.castAdd n) (q ∘ Fin.natAdd n)
    have hc' : GammaParameters.Proper c' := by
      intro j
      refine Fin.addCases (fun i => ?_) (fun i => ?_) j
      · simpa only [c',Fin.append_left,Function.comp_apply] using hc (Fin.castAdd n i)
      · simp only [c',Fin.append_right,Function.comp_apply]
        exact ⟨(hq.2.1.2 i).1,(hq.2.1.2 i).2⟩
    have hd' : GammaParameters.Proper d' := by
      intro j
      refine Fin.addCases (fun i => ?_) (fun i => ?_) j
      · simpa only [d',Fin.append_left,Function.comp_apply] using hd (Fin.castAdd n i)
      · simp only [d',Fin.append_right,Function.comp_apply]
        exact ⟨(hq.2.1.2 i).1,(hq.2.1.2 i).2⟩
    have hvalues : (fun j => GammaParameters.codeValue (c' j)) = fun j => GammaParameters.codeValue (d' j) := by
      funext j
      refine Fin.addCases (fun i => ?_) (fun i => ?_) j
      · simpa only [c',d',Fin.append_left,Function.comp_apply] using hprefix i
      · simp only [c',d',Fin.append_right,Function.comp_apply]
    have h := gamma_raw_relation_invariant H hH (z ∘ Fin.natAdd n ∘ Fin.castAdd m)
      (Fin.append (q ∘ Fin.castAdd n) (z ∘ Fin.natAdd n ∘ Fin.natAdd p)) c' d' hc' hd' hvalues
    unfold discHullArguments at hHq ⊢
    change Sum.elim ((w ∘ Fin.natAdd n) ∘ Fin.castAdd m)
      (Sum.elim d' (Fin.append (q ∘ Fin.castAdd n) ((w ∘ Fin.natAdd n) ∘ Fin.natAdd p))) ∈ H
    rw [← htail]
    exact h.mp hHq
  constructor
  · exact hstep c d hc hd z w hdisc htail hprefix
  · apply hstep d c hd hc w z
    · exact ⟨hdisc.2.1,hdisc.1,fun i x => (hdisc.2.2 i x).symm⟩
    · exact htail.symm
    · exact fun i => (hprefix i).symm

end DiamondIntegral.Section2
