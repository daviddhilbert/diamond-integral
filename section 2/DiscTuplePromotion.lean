import «section 2».FiniteDiscPromotedRelations
import «section 2».BlockTypeFibres

/-! Promoting named real parameters while retaining actual disc names.
The invariant hull is necessary away from the original named tuple. -/

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4

namespace DiamondIntegral.Section2
variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF] {n p m : ℕ}

theorem gamma_representatives_append_left {k : ℕ} (σ : Fin k → Gamma M) (δ : Fin n → Gamma M) (i : Fin k) :
    GammaParameters.codeValue (GammaParameters.rawTuple (GammaParameters.representatives (Fin.append σ δ))
      (Fin.castAdd n i)) = σ i := by
  change GammaParameters.codeValue (GammaParameters.raw (GammaParameters.representatives (Fin.append σ δ) (Fin.castAdd n i))) = _
  rw [GammaParameters.codeValue_raw]
  simpa only [Fin.append_left,GammaParameters.values] using congrFun (GammaParameters.representatives_values (Fin.append σ δ)) (Fin.castAdd n i)

theorem gamma_representatives_append_right {k : ℕ} (σ : Fin k → Gamma M) (δ : Fin n → Gamma M) (i : Fin n) :
    GammaParameters.codeValue (GammaParameters.rawTuple (GammaParameters.representatives (Fin.append σ δ))
      (Fin.natAdd k i)) = δ i := by
  change GammaParameters.codeValue (GammaParameters.raw (GammaParameters.representatives (Fin.append σ δ) (Fin.natAdd k i))) = _
  rw [GammaParameters.codeValue_raw]
  simpa only [Fin.append_right,GammaParameters.values] using congrFun (GammaParameters.representatives_values (Fin.append σ δ)) (Fin.natAdd k i)

theorem sorted_append_vf (a : Fin n → VF M) (sn : Fin m → SortTag) (x : Fin m → M) :
    Fin.append (vfValues a) x ∈ GammaParameters.sortedUniverse (Fin.append (fun _ : Fin n => .vf) sn) ↔
      x ∈ GammaParameters.sortedUniverse sn := by
  constructor
  · intro h j
    simpa only [Fin.append_right] using h (Fin.natAdd n j)
  · intro h j
    refine Fin.addCases (fun i => ?_) (fun i => ?_) j
    · simpa only [Fin.append_left,vfValues,sortEval,iVF] using (a i).property
    · simpa only [Fin.append_right] using h i

def FiniteDiscTupleRelation.promoted
    (hc : CanonicalStructure.IsCanonical (M := M)) (B : ParameterBase M)
    (closed : Fin n → Bool) (sp : Fin p → SortTag) (sn : Fin m → SortTag)
    (u : Fin p → M) (R : FiniteDiscTupleRelation (tupleBase B u) closed sn)
    (H : Set (Fin p ⊕ (Fin (R.supportArity+n) ⊕ Fin (n+m)) → M)) (hHd : B.real.Definable LRV H)
    (hHi : ∀ v b (t v' : Fin (R.supportArity+n) → GammaParameters.Code (M := M)),
      GammaParameters.values t = GammaParameters.values v' →
      (Sum.elim v (Sum.elim (GammaParameters.rawTuple t) b) ∈ H ↔
        Sum.elim v (Sum.elim (GammaParameters.rawTuple v') b) ∈ H)) :
    FiniteDiscTupleRelation B closed (Fin.append sp sn) where
  supportArity := R.supportArity
  support := R.support
  support_mem := R.support_mem
  relation := discPromotedGammaRelation hc B.real closed sp sn H hHd hHi
  invariant := by
    intro a a' δ δ' he x
    let c := GammaParameters.rawTuple (GammaParameters.representatives (Fin.append R.support δ))
    let d := GammaParameters.rawTuple (GammaParameters.representatives (Fin.append R.support δ'))
    have hcP : GammaParameters.Proper c := GammaParameters.rawTuple_proper _
    have hdP : GammaParameters.Proper d := GammaParameters.rawTuple_proper _
    have hca : finiteDiscRawProper (discHullCurrent c (Fin.append (vfValues a) x)) := by
      rw [discHullCurrent_append]
      exact finiteDiscRawProper_append a _ (fun i => hcP (Fin.natAdd R.supportArity i))
    have hda : finiteDiscRawProper (discHullCurrent d (Fin.append (vfValues a') x)) := by
      rw [discHullCurrent_append]
      exact finiteDiscRawProper_append a' _ (fun i => hdP (Fin.natAdd R.supportArity i))
    have hdisc : finiteDiscRawEq closed (discHullCurrent c (Fin.append (vfValues a) x))
        (discHullCurrent d (Fin.append (vfValues a') x)) := by
      apply (finiteDiscRawEq_iff closed _ _ hca hda).mpr
      rw [discHullCurrent_names closed c hcP a x δ (gamma_representatives_append_right R.support δ),
        discHullCurrent_names closed d hdP a' x δ' (gamma_representatives_append_right R.support δ'),he]
    have htail : Fin.append (vfValues a) x ∘ Fin.natAdd n = Fin.append (vfValues a') x ∘ Fin.natAdd n := by
      funext i
      simp only [Function.comp_apply,Fin.append_right]
    have hprefix (i : Fin R.supportArity) : GammaParameters.codeValue (c (Fin.castAdd n i)) =
        GammaParameters.codeValue (d (Fin.castAdd n i)) :=
      (gamma_representatives_append_left R.support δ i).trans (gamma_representatives_append_left R.support δ' i).symm
    change (GammaParameters.Proper c ∧ _ ∧ _) ↔ (GammaParameters.Proper d ∧ _ ∧ _)
    rw [and_iff_right hcP,and_iff_right hdP,sorted_append_vf,sorted_append_vf]
    exact and_congr Iff.rfl (discInvariantHull_congr closed H hHi c d hcP hdP _ _ hdisc htail hprefix)

theorem discInvariantHull_named_iff (B : ParameterBase M) (closed : Fin n → Bool) (sn : Fin m → SortTag)
    (u : Fin p → M) (R : FiniteDiscTupleRelation (tupleBase B u) closed sn)
    (H : Set (Fin p ⊕ (Fin (R.supportArity+n) ⊕ Fin (n+m)) → M))
    (hHa : ∀ c b, GammaParameters.Proper c →
      (Sum.elim u (Sum.elim c b) ∈ H ↔ (c,b) ∈ R.relation.carrier))
    (a : Fin n → VF M) (δ : Fin n → Gamma M) (x : Fin m → M) :
    discInvariantHull closed H
      (GammaParameters.rawTuple (GammaParameters.representatives (Fin.append R.support δ)))
      (Fin.append (vfValues a) (Fin.append u x)) ↔ x ∈ R.fibre a δ := by
  let c := GammaParameters.rawTuple (GammaParameters.representatives (Fin.append R.support δ))
  let z := Fin.append (vfValues a) (Fin.append u x)
  have hcP : GammaParameters.Proper c := GammaParameters.rawTuple_proper _
  have hcurrent : finiteDiscRawProper (discHullCurrent c z) := by
    rw [discHullCurrent_append]
    exact finiteDiscRawProper_append a _ (fun i => hcP (Fin.natAdd R.supportArity i))
  have hnames : finiteDiscRawNames closed (discHullCurrent c z) = finitePolydiscNames closed a δ :=
    discHullCurrent_names closed c hcP a _ δ (gamma_representatives_append_right R.support δ)
  have hrow (q : Fin (n+n) → M) (hq : finiteDiscRawEq closed (discHullCurrent c z) q) :
      discHullArguments c z q ∈ H ↔ x ∈ R.fibre a δ := by
    let d := Fin.append (c ∘ Fin.castAdd n) (q ∘ Fin.natAdd n)
    have hd : GammaParameters.Proper d := by
      intro j
      refine Fin.addCases (fun i => ?_) (fun i => ?_) j
      · simpa only [d,Fin.append_left,Function.comp_apply] using hcP (Fin.castAdd n i)
      · simp only [d,Fin.append_right,Function.comp_apply]
        exact ⟨(hq.2.1.2 i).1,(hq.2.1.2 i).2⟩
    have hσ (i : Fin R.supportArity) : GammaParameters.codeValue (d (Fin.castAdd n i)) = R.support i := by
      simpa only [d,Fin.append_left,Function.comp_apply] using gamma_representatives_append_left R.support δ i
    have hqr : q ∘ Fin.natAdd n = d ∘ Fin.natAdd R.supportArity := by
      funext i
      simp only [d,Fin.append_right,Function.comp_apply]
    have heNames : finitePolydiscNames closed (finiteDiscRawCentres q)
        (fun i => GammaParameters.codeValue (q (Fin.natAdd n i))) = finitePolydiscNames closed a δ :=
      ((finiteDiscRawEq_iff closed _ _ hcurrent hq.2.1).mp hq).symm.trans hnames
    change discHullArguments c (Fin.append (vfValues a) (Fin.append u x)) q ∈ H ↔ _
    rw [discHullArguments_append,hHa _ _ hd,R.raw_row_iff d hd hσ q hq.2.1 hqr x,
      R.fibre_eq_of_names _ a _ δ heNames]
  constructor
  · rintro ⟨q,hq,hHq⟩
    exact (hrow q hq).mp hHq
  · intro hx
    have he : finiteDiscRawEq closed (discHullCurrent c z) (discHullCurrent c z) :=
      ⟨hcurrent,hcurrent,fun _ _ => Iff.rfl⟩
    exact ⟨discHullCurrent c z,he,(hrow _ he).mpr hx⟩

theorem promote_tuple_definable_disc_names (hc : CanonicalStructure.IsCanonical (M := M))
    (B : ParameterBase M) (closed : Fin n → Bool) (a : Fin n → VF M) (δ : Fin n → Gamma M)
    (sp : Fin p → SortTag) (u : Fin p → M) (hu : ∀ i, sortEval (sp i) (u i))
    (sn : Fin m → SortTag) (C : Set (Fin m → M))
    (hC : DefinableOverFiniteDiscNames (tupleBase B u) closed a δ sn C) :
    ∃ P : Set (Fin (p+m) → M), DefinableOverFiniteDiscNames B closed a δ (Fin.append sp sn) P ∧
      ∀ x : Fin m → M, Fin.append u x ∈ P ↔ x ∈ C := by
  have hCproper := hC.proper
  obtain ⟨R,hRC⟩ := hC
  obtain ⟨H,hHd,hHi,hHa⟩ := GammaParameters.promote_gamma_relation B.real u R.relation
  let H' := {z : Fin p ⊕ (Fin (R.supportArity+n) ⊕ Fin (n+m)) → M |
    (z ∘ Sum.inl,z ∘ Sum.inr ∘ Sum.inl,z ∘ Sum.inr ∘ Sum.inr) ∈ H}
  have hHd' : B.real.Definable LRV H' := by
    rw [SpecialTransformations.Section8.normalize_eq_of_isCanonical hc] at hHd
    exact hHd
  let Q := R.promoted hc B closed sp sn u H' hHd' hHi
  refine ⟨Q.fibre a δ,⟨Q,rfl⟩,fun x => ?_⟩
  change (GammaParameters.Proper (GammaParameters.rawTuple (GammaParameters.representatives (Fin.append R.support δ))) ∧
    Fin.append (vfValues a) (Fin.append u x) ∈ GammaParameters.sortedUniverse
      (Fin.append (fun _ : Fin n => .vf) (Fin.append sp sn)) ∧
    discInvariantHull closed H' (GammaParameters.rawTuple (GammaParameters.representatives (Fin.append R.support δ)))
      (Fin.append (vfValues a) (Fin.append u x))) ↔ x ∈ C
  rw [and_iff_right (GammaParameters.rawTuple_proper _),sorted_append_vf,
    discInvariantHull_named_iff B closed sn u R H' hHa a δ x,hRC]
  constructor
  · exact And.right
  · intro hx
    refine ⟨?_,hx⟩
    intro j
    refine Fin.addCases (fun i => ?_) (fun i => ?_) j
    · simpa only [Fin.append_left] using hu i
    · simpa only [Fin.append_right] using hCproper hx i

end DiamondIntegral.Section2
