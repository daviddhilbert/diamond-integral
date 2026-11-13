import «section 3».GammaFiniteVFCodeGraphs
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section3.RawClosure.Tuple
open SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section3.Barycentre
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {B : GammaParameters.Base (M := M)} {n : ℕ}

/-- Finite VF tuples have an injective RV code over the original real
and Gamma ground. No representatives of the Gamma names are added. -/
theorem gammaFiniteVFCoding (hc : CanonicalStructure.IsCanonical (M := M))
    (h00 : M ⊨ Axioms.ACVF00)
    (A : Set (Fin n → VFType (M := M))) (hfin : A.Finite)
    (hA : GammaParameters.DefinableOverBase B (fun _ => .vf) (FiniteCoding.values '' A)) :
    ∃ m : ℕ, ∃ f : A → Fin m → M, Function.Injective f ∧
      (∀ a j, iRV (f a j)) ∧
      GammaParameters.DefinableOverBase B FiniteCoding.graphSort (FiniteCoding.graph A f) := by
  obtain ⟨q,γ,hγ,R,hR⟩ := hA
  let t := GammaParameters.representatives γ
  have ht : GammaParameters.values t = γ := GammaParameters.representatives_values γ
  let d := A.ncard
  have hrow (i : Fin n) :
      {x | (GammaParameters.rawTuple t,x) ∈ gammaVFCoordinateRow R i} =
        (fun a : Fin n → VFType (M := M) => (a i).val) '' A := by
    ext x
    constructor
    · rintro ⟨b,hb,hi⟩
      have hb' : b ∈ R.fibre γ := (R.mem_fibre_iff t γ ht b).mpr hb
      rw [hR] at hb'
      obtain ⟨a,ha,rfl⟩ := hb'
      exact ⟨a,ha,hi⟩
    · rintro ⟨a,ha,rfl⟩
      refine ⟨FiniteCoding.values a,?_,rfl⟩
      apply (R.mem_fibre_iff t γ ht _).mp
      rw [hR]
      exact ⟨a,ha,rfl⟩
  have hbound (i : Fin n) : GammaParameters.rawTuple t ∉ HasMore (gammaVFCoordinateRow R i) d := by
    change ¬ ∃ u : Fin (d+1) → M, Function.Injective u ∧
      ∀ j, (GammaParameters.rawTuple t,u j) ∈ gammaVFCoordinateRow R i
    apply (RawClosure.no_inj_iff_finite_ncard_le
      (s := {x | (GammaParameters.rawTuple t,x) ∈ gammaVFCoordinateRow R i}) (k := d)).mpr
    rw [hrow]
    exact ⟨hfin.image _,Set.ncard_image_le hfin⟩
  have hmem (i : Fin n) (a : A) : a.val i ∈
      boundedVFFibre (gammaVFCoordinateRow R i) (gammaVFCoordinateRow_vf R i) d (GammaParameters.rawTuple t) := by
    apply (boundedVFFibre_mem _ _ _ _ _).mpr
    refine ⟨?_,hbound i⟩
    change (a.val i).val ∈ {x | (GammaParameters.rawTuple t,x) ∈ gammaVFCoordinateRow R i}
    rw [hrow]
    exact ⟨a.val,a.property,rfl⟩
  let f (a : A) := gammaFiniteVFCode R d (GammaParameters.rawTuple t) (FiniteCoding.values a.val)
  have hsort (a : A) (k : Fin (n*d)) : iRV (f a k) := by
    change iRV (rawCode d
      (boundedVFFibre (gammaVFCoordinateRow R (finProdFinEquiv.symm k).1)
        (gammaVFCoordinateRow_vf R (finProdFinEquiv.symm k).1) d) (GammaParameters.rawTuple t)
      (a.val (finProdFinEquiv.symm k).1).val (finProdFinEquiv.symm k).2)
    rw [rawCode_eq_code]
    exact code_sorted _ _ _ _
  have hinj : Function.Injective f := by
    intro a b hab
    apply Subtype.ext
    funext i
    apply boundedVFFibre_code_injective h00 (gammaVFCoordinateRow R i)
      (gammaVFCoordinateRow_vf R i) d (GammaParameters.rawTuple t) (hmem i a) (hmem i b)
    funext j
    have h := congrFun hab (finProdFinEquiv (i,j))
    change gammaFiniteVFCode R d (GammaParameters.rawTuple t) (FiniteCoding.values a.val) (finProdFinEquiv (i,j)) =
      gammaFiniteVFCode R d (GammaParameters.rawTuple t) (FiniteCoding.values b.val) (finProdFinEquiv (i,j)) at h
    unfold gammaFiniteVFCode at h
    simp only [Equiv.symm_apply_apply] at h
    exact h
  refine ⟨n*d,f,hinj,hsort,q,γ,hγ,gammaFiniteVFCodeRelation hc h00 R d,?_⟩
  ext z
  change ((GammaParameters.rawTuple t,z ∘ finSumFinEquiv ∘ Sum.inl) ∈ R.carrier ∧
    gammaFiniteVFCode R d (GammaParameters.rawTuple t) (z ∘ finSumFinEquiv ∘ Sum.inl) =
      z ∘ finSumFinEquiv ∘ Sum.inr) ↔ z ∈ FiniteCoding.graph A f
  constructor
  · rintro ⟨hz,hc⟩
    have hz' := (R.mem_fibre_iff t γ ht _).mpr hz
    rw [hR] at hz'
    obtain ⟨a,ha,he⟩ := hz'
    exact ⟨⟨a,ha⟩,he,by simpa only [f,he] using hc⟩
  · rintro ⟨a,ha,hb⟩
    refine ⟨?_,?_⟩
    · apply (R.mem_fibre_iff t γ ht _).mp
      rw [hR]
      exact ⟨a.val,a.property,ha⟩
    · simpa only [f,ha] using hb
end DiamondIntegral.Section3
