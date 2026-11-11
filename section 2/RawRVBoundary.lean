import «section 2».RawRVPolydiscs
import «section 2».RawMapImages

/-! Actual RV images, boundaries and interiors of raw pure-VF sets,
with their full definitions over the original real parameter set. -/

set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3

namespace DiamondIntegral.Section2
variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF] {n : ℕ}

def rawVFComplement (A : Set (Fin n → M)) : Set (Fin n → M) :=
  {x | (∀ j, iVF (x j)) ∧ x ∉ A}

def rawRVImage (A : Set (Fin n → M)) : Set (Fin n → RVInfinity M) :=
  {t | ∃ x ∈ rawRVPolydisc t, x ∈ A}

def rawRVBoundary (A : Set (Fin n → M)) : Set (Fin n → RVInfinity M) :=
  {t | (∃ x ∈ rawRVPolydisc t, x ∈ A) ∧ ∃ y ∈ rawRVPolydisc t, y ∉ A}

def rawRVInterior (A : Set (Fin n → M)) : Set (Fin n → RVInfinity M) :=
  rawRVImage A \ rawRVBoundary A

theorem rawRVBoundary_eq_inter (A : Set (Fin n → M)) :
    rawRVBoundary A = rawRVImage A ∩ rawRVImage (rawVFComplement A) := by
  ext t
  constructor
  · rintro ⟨hin,y,hy,hyA⟩
    exact ⟨hin,y,hy,fun j => (hy j).1,hyA⟩
  · rintro ⟨hin,y,hy,_,hyA⟩
    exact ⟨hin,y,hy,hyA⟩

theorem rawRVInterior_iff (A : Set (Fin n → M)) (t : Fin n → RVInfinity M) :
    t ∈ rawRVInterior A ↔ rawRVPolydisc t ⊆ A := by
  classical
  constructor
  · rintro ⟨hin,hnot⟩ x hx
    by_contra h
    exact hnot ⟨hin,x,hx,h⟩
  · intro h
    obtain ⟨x,hx⟩ := rawRVPolydisc_nonempty t
    exact ⟨⟨x,hx,h hx⟩,fun ⟨_,y,hy,hyA⟩ => hyA (h hy)⟩

theorem rawRVInterior_of_mem_not_boundary (A : Set (Fin n → M)) (t : Fin n → RVInfinity M)
    (a : Fin n → M) (ha : a ∈ A) (hat : a ∈ rawRVPolydisc t)
    (hnot : t ∉ rawRVBoundary A) : t ∈ rawRVInterior A := ⟨⟨a,hat,ha⟩,hnot⟩

theorem rawVFComplement_definable (S : Set M) (A : Set (Fin n → M))
    (hA : DefinableOver S (fun _ => .vf) A) : DefinableOver S (fun _ => .vf) (rawVFComplement A) := by
  exact (GammaParameters.base_empty_iff S _ _).mp
    (((GammaParameters.base_empty_iff S _ _).mpr hA).compl)

theorem rawRVImage_values_eq (A : Set (Fin n → M))
    (hA : ∀ x ∈ A, ∀ j, iVF (x j)) : rvInputValues '' rawRVImage A = rawRVValues '' A := by
  ext z
  constructor
  · rintro ⟨t,⟨x,hxt,hx⟩,rfl⟩
    exact ⟨x,hx,funext (fun j => (hxt j).2)⟩
  · rintro ⟨x,hx,rfl⟩
    let t : Fin n → RVInfinity M := fun j => rv M ⟨x j,hA x hx j⟩
    exact ⟨t,⟨x,fun j => ⟨hA x hx j,rfl⟩,hx⟩,rfl⟩

theorem rawRVImage_definable (hc : CanonicalStructure.IsCanonical (M := M))
    (S : Set M) (A : Set (Fin n → M)) (hA : DefinableOver S (fun _ => .vf) A) :
    DefinableOver S (fun _ => .rv) (rvInputValues '' rawRVImage A) := by
  have hsort : ∀ x ∈ A, ∀ j, iVF (x j) := by
    obtain ⟨p,φ,hφ,rfl⟩ := hA
    exact fun x hx => hx.1
  apply raw_definableOver_sorted hc
  · rw [rawRVImage_values_eq A hsort]
    exact raw_definable_map_image S A hA.raw_definable rawRVValues (rawRVValues_definable S)
  · rintro z ⟨t,ht,rfl⟩ j
    exact (t j).property

theorem rawRVBoundary_definable (hc : CanonicalStructure.IsCanonical (M := M))
    (S : Set M) (A : Set (Fin n → M)) (hA : DefinableOver S (fun _ => .vf) A) :
    DefinableOver S (fun _ => .rv) (rvInputValues '' rawRVBoundary A) := by
  rw [rawRVBoundary_eq_inter,Set.image_inter rvInputValues_injective]
  have hI := (GammaParameters.base_empty_iff S _ _).mpr (rawRVImage_definable hc S A hA)
  have hJ := (GammaParameters.base_empty_iff S _ _).mpr
    (rawRVImage_definable hc S _ (rawVFComplement_definable S A hA))
  exact (GammaParameters.base_empty_iff S _ _).mp (hI.inter hJ)

theorem rawRVInterior_definable (hc : CanonicalStructure.IsCanonical (M := M))
    (S : Set M) (A : Set (Fin n → M)) (hA : DefinableOver S (fun _ => .vf) A) :
    DefinableOver S (fun _ => .rv) (rvInputValues '' rawRVInterior A) := by
  have hI := rawRVImage_definable hc S A hA
  have hB := rawRVBoundary_definable hc S A hA
  apply raw_definableOver_sorted hc
  · rw [rawRVInterior,Set.image_sdiff rvInputValues_injective]
    exact hI.raw_definable.inter hB.raw_definable.compl
  · rintro z ⟨t,ht,rfl⟩ j
    exact (t j).property

end DiamondIntegral.Section2
