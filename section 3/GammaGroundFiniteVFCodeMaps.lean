import «section 3».GammaFiniteVFCoding
import «section 3».GammaGroundRawDescent
import «section 3».GammaGroundMapImages
import Section4.CanonicalNormalization
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : GammaParameters.Base (M := M)} {n m : ℕ}

omit [M ⊨ Axioms.ACVF] in
theorem rawVFSpace_preimage_eq_values_image (A : Set (rawVFSpace (M := M) n).Carrier) :
    (rawVFSpace n).preimage A = vfValues '' A := by
  ext z
  constructor
  · rintro ⟨hz,ha⟩
    exact ⟨(rawVFSpace n).decode ⟨z,hz⟩,ha,vfValues_decode _⟩
  · rintro ⟨a,ha,hz⟩
    have hdom : z ∈ (rawVFSpace (M := M) n).domain := ⟨a,hz⟩
    refine ⟨hdom,?_⟩
    have he : (rawVFSpace n).decode ⟨z,hdom⟩ = a :=
      vfValues_injective ((vfValues_decode _).trans hz.symm)
    exact he ▸ ha

/-- A complete sorted finite-coding graph gives an actual definable map
between the geometric VF and RV presentations over the same Gamma ground. -/
def gammaGroundMapOfFiniteCodeGraph
    (A : GammaGroundDefSet hc B (rawVFSpace (M := M) n))
    (f : A → Fin m → M) (hsort : ∀ a j, iRV (f a j))
    (hgraph : GammaParameters.DefinableOverBase B FiniteCoding.graphSort (FiniteCoding.graph A.carrier f)) :
    GammaGroundMap A (GammaGroundDefSet.univ hc B (rawRVSpace (M := M) m)) where
  toFun a := ⟨fun j => ⟨f a j,hsort a j⟩,Set.mem_univ _⟩
  graph_definable := by
    have hr := (gammaGroundRawDefinable_iff_sortedBase
      (hc := hc) (ground := B) (FiniteCoding.graph_sorted A.carrier f hsort)).mpr hgraph
    have hd := hr.preimage_comp (finSumFinEquiv.symm : Fin (n+m) → Fin n ⊕ Fin m)
    apply GammaGroundDefinable.of_real_codes
    apply hd.congr
    intro z
    change (∃ a : A, FiniteCoding.values a.val =
      (z ∘ finSumFinEquiv.symm) ∘ finSumFinEquiv ∘ Sum.inl ∧
      f a = (z ∘ finSumFinEquiv.symm) ∘ finSumFinEquiv ∘ Sum.inr) ↔ _
    simp only [Function.comp_def,Equiv.symm_apply_apply]
    constructor
    · rintro ⟨a,ha,hf⟩
      have hrv : z ∘ Sum.inr ∈ (rawRVSpace (M := M) m).domain :=
        ⟨fun j => ⟨f a j,hsort a j⟩,hf⟩
      have hvf : z ∘ Sum.inl ∈ (rawVFSpace (M := M) n).domain := ⟨a.val,ha⟩
      refine ⟨⟨hvf,hrv⟩,a,?_,?_⟩
      · exact vfValues_injective (ha.trans (vfValues_decode ⟨z ∘ Sum.inl,hvf⟩).symm)
      · exact rvValues_injective (hf.trans (rvValues_decode ⟨z ∘ Sum.inr,hrv⟩).symm)
    · rintro ⟨⟨hvf,hrv⟩,a,ha,hf⟩
      refine ⟨a,?_,?_⟩
      · exact (congrArg vfValues ha).trans (vfValues_decode ⟨z ∘ Sum.inl,hvf⟩)
      · exact (congrArg rvValues hf).trans (rvValues_decode ⟨z ∘ Sum.inr,hrv⟩)

/-- Every finite Gamma-ground VF set has a genuinely definable injection
into a finite RV tuple, with its complete graph over the original ground. -/
theorem gammaGroundFiniteVFCodeMap (h00 : M ⊨ Axioms.ACVF00)
    (A : GammaGroundDefSet hc B (rawVFSpace (M := M) n)) (hfin : A.carrier.Finite) :
    ∃ m : ℕ, ∃ f : GammaGroundMap A (GammaGroundDefSet.univ hc B (rawRVSpace (M := M) m)),
      Function.Injective f := by
  have ha := A.definable.on_real_codes
  rw [rawVFSpace_preimage_eq_values_image] at ha
  have hproper : ∀ b ∈ vfValues '' A.carrier, ∀ i : Fin n, sortEval .vf (b i) := by
    rintro b ⟨a,ha,rfl⟩ i
    exact (a i).property
  obtain ⟨m,f,hf,hs,hg⟩ := gammaFiniteVFCoding hc h00 A.carrier hfin
    ((gammaGroundRawDefinable_iff_sortedBase hproper).mp ha)
  refine ⟨m,gammaGroundMapOfFiniteCodeGraph A f hs hg,?_⟩
  intro a b he
  apply hf
  exact congrArg (fun z : GammaGroundDefSet.univ hc B (rawRVSpace (M := M) m) => rvValues z.val) he
end DiamondIntegral.Section3
