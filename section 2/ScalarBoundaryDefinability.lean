import «section 2».ScalarBoundary
import «section 2».RVImage
import «section 2».RVDimension

/-! Definability of the actual unary RV-boundary over the original
real/Gamma base, using the full rv graph. The zero tag is preserved by the
image construction and is then excluded by the boundary theorem. -/

set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3

namespace DiamondIntegral.Section2
variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

private theorem scalar_rv_image_definable (B : ParameterBase M) (A : Set M)
    (hA : GammaParameters.DefinableAtBase B .vf A) :
    GammaParameters.DefinableAtBase B .rv
      (Subtype.val '' (rv M '' {x : VF M | x.val ∈ A})) := by
  let F : Set ((Fin 0 → M) × M) := {p | p.2 ∈ A}
  have hF : GammaParameters.DefinableOverBase B (fun _ : Fin 1 => .vf)
      {z | (Fin.init z, z (Fin.last 0)) ∈ F} := by
    change GammaParameters.DefinableOverBase B (fun _ : Fin 1 => .vf) {z | z 0 ∈ A}
    exact hA
  have hR := vfRVImage_definable B F hF
  have hsort : Fin.lastCases SortTag.rv (fun _ : Fin 0 => .vf) =
      (fun _ : Fin 1 => .rv) := by
    funext j
    fin_cases j
    rfl
  rw [hsort] at hR
  change GammaParameters.DefinableOverBase B (fun _ : Fin 1 => .rv)
    {z | z 0 ∈ Subtype.val '' (rv M '' {x : VF M | x.val ∈ A})}
  convert hR using 1
  ext z
  constructor
  · rintro ⟨t, ⟨x, hx, hxt⟩, htz⟩
    exact ⟨x.val, hx, (congrArg Subtype.val hxt).trans htz⟩
  · rintro ⟨y, hyA, hyt⟩
    let x : VF M := ⟨y, hA.proper y hyA⟩
    exact ⟨rv M x, ⟨x, hyA, rfl⟩, hyt⟩

/-- The unary boundary is definable over exactly the given ground base. -/
theorem scalarRVBoundary_definable (B : ParameterBase M) (A : Set M)
    (hA : GammaParameters.DefinableAtBase B .vf A) :
    GammaParameters.DefinableAtBase B .rv (Subtype.val '' scalarRVBoundary A) := by
  let N : Set M := {x | iVF x ∧ x ∉ A}
  have hN : GammaParameters.DefinableAtBase B .vf N := by
    have hc := GammaParameters.DefinableOverBase.compl hA
    change GammaParameters.DefinableOverBase B (fun _ : Fin 1 => .vf) {z | z 0 ∈ N}
    convert hc using 1
    ext z
    change (iVF (z 0) ∧ z 0 ∉ A) ↔
      (z ∈ GammaParameters.sortedUniverse (fun _ : Fin 1 => .vf) ∧ z 0 ∉ A)
    constructor
    · rintro ⟨hz, hn⟩
      refine ⟨?_, hn⟩
      intro j
      fin_cases j
      exact hz
    · rintro ⟨hz, hn⟩
      exact ⟨hz 0, hn⟩
  have heN : {x : VF M | x.val ∈ N} = {x : VF M | x.val ∉ A} := by
    ext x
    exact and_iff_right x.property
  have hI := scalar_rv_image_definable B A hA
  have hJ := scalar_rv_image_definable B N hN
  rw [heN] at hJ
  change GammaParameters.DefinableOverBase B (fun _ : Fin 1 => .rv)
    {z | z 0 ∈ Subtype.val '' scalarRVBoundary A}
  convert hI.inter hJ using 1
  ext z
  constructor
  · rintro ⟨t, ⟨htA, htN⟩, htz⟩
    exact ⟨⟨t, htA, htz⟩, t, htN, htz⟩
  · rintro ⟨⟨t, htA, htz⟩, u, huN, huz⟩
    have he : t = u := Subtype.ext (htz.trans huz.symm)
    exact ⟨t, ⟨htA, he.symm ▸ huN⟩, htz⟩

/-- Unary tuples put the scalar boundary into the existing RV-dimension
interface; its elements remain actual RV-infinity values. -/
def scalarBoundaryTuples (A : Set M) : Set (Fin 1 → RVInfinity M) :=
  {t | t 0 ∈ scalarRVBoundary A}

theorem scalarBoundaryTuples_finite (B : ParameterBase M) (A : Set M)
    (hA : GammaParameters.DefinableAtBase B .vf A) : (scalarBoundaryTuples A).Finite := by
  apply (lemma_2_35_unary_finite B A hA).preimage
  intro x _ y _ hxy
  funext j
  fin_cases j
  exact hxy

/-- The tuple boundary graph is defined over the same genuine Gamma base. -/
theorem scalarBoundaryTuples_definable (B : ParameterBase M) (A : Set M)
    (hA : GammaParameters.DefinableAtBase B .vf A) :
    GammaParameters.DefinableOverBase B (fun _ : Fin 1 => .rv)
      (rvInputValues '' scalarBoundaryTuples A) := by
  have h := scalarRVBoundary_definable B A hA
  change GammaParameters.DefinableOverBase B (fun _ : Fin 1 => .rv)
    {z | z 0 ∈ Subtype.val '' scalarRVBoundary A} at h
  convert h using 1
  ext z
  constructor
  · rintro ⟨t, ht, htz⟩
    exact ⟨t 0, ht, congrFun htz 0⟩
  · rintro ⟨t, ht, htz⟩
    refine ⟨fun _ => t, ht, ?_⟩
    funext j
    fin_cases j
    exact htz

end DiamondIntegral.Section2
