import «section 2».BoundaryRepresentativePartition
import «section 2».BoundaryRVGraphs
import «section 2».RectangleImages

/-! Coverage in the author's proof of 2.35: the first coordinate exit
places a boundary tuple either in a lower-dimensional boundary cylinder
or in a retained-tag representative graph. -/

set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3

namespace DiamondIntegral.Section2
variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF] {n : ℕ}

theorem rawRVBoundary_coordinate_exit (A : Set (Fin (n+1) → M))
    (t : Fin (n+1) → RVInfinity M) (ht : t ∈ rawRVBoundary A) :
    ∃ (i : Fin (n+1)) (a : Fin n → M), a ∈ rawCoordinateProjection A i ∧
      a ∈ rawRVPolydisc (Fin.removeNth i t) ∧ t i ∈ boundaryTagSet A i a := by
  classical
  obtain ⟨⟨c,hct,hcA⟩,d,hdt,hdA⟩ := ht
  let D (j : Fin (n+1)) : Set M := rvRawFibre (t j)
  obtain ⟨b,hbt,hbA,i,x,hxt,hxA⟩ := rectangle_coordinate_exit D A c d hct hdt hcA hdA
  let a := Fin.removeNth i b
  have ha : ∀ j, iVF (a j) := fun j => (hbt (i.succAbove j)).1
  have htag : t i ∈ scalarRVBoundary (rawCoordinateSection A i a) := by
    constructor
    · refine ⟨⟨b i,(hbt i).1⟩,?_,Subtype.ext (hbt i).2⟩
      change Fin.insertNth i (b i) (Fin.removeNth i b) ∈ A
      rwa [Fin.insertNth_self_removeNth]
    · refine ⟨⟨x,hxt.1⟩,?_,Subtype.ext hxt.2⟩
      change Fin.insertNth i x (Fin.removeNth i b) ∉ A
      rwa [Fin.insertNth_removeNth]
  exact ⟨i,a,⟨b,hbA,rfl⟩,(fun j => hbt (i.succAbove j)),
    (coordinateBoundaryPairs_at_iff A i a (t i)).mpr ⟨ha,htag⟩⟩

def boundaryCoverPiece (i : Fin (n+1)) (V : Set (Fin n → M))
    (F : (Fin n → M) → Set M) : Set (Fin (n+1) → RVInfinity M) :=
  rvCoordinateCylinder i (rawRVBoundary V) ∪ boundaryRVGraph i V F

theorem rawRVBoundary_subset_cover (A : Set (Fin (n+1) → M))
    (F : Fin (n+1) → (Fin n → M) → Set M)
    (Q : Fin (n+1) → Set (Set (Fin n → M)))
    (hproper : ∀ i, ∀ a ∈ rawCoordinateProjection A i, ∀ y ∈ F i a, iVF y)
    (hrepresent : ∀ i, ∀ a ∈ rawCoordinateProjection A i,
      Subtype.val '' boundaryTagSet A i a ⊆ iRv '' F i a)
    (hcover : ∀ i, ∀ a ∈ rawCoordinateProjection A i, ∃ V ∈ Q i, a ∈ V) :
    rawRVBoundary A ⊆ ⋃₀ (⋃ i, (fun V => boundaryCoverPiece i V (F i)) '' Q i) := by
  classical
  intro t ht
  obtain ⟨i,a,haD,hat,htag⟩ := rawRVBoundary_coordinate_exit A t ht
  obtain ⟨V,hV,haV⟩ := hcover i a haD
  refine Set.mem_sUnion.mpr ⟨boundaryCoverPiece i V (F i),
    Set.mem_iUnion.mpr ⟨i,Set.mem_image_of_mem _ hV⟩,?_⟩
  by_cases hb : Fin.removeNth i t ∈ rawRVBoundary V
  · exact Or.inl hb
  · have hint := rawRVInterior_of_mem_not_boundary V _ a haV hat hb
    obtain ⟨y,hy,hyt⟩ := hrepresent i a haD (Set.mem_image_of_mem Subtype.val htag)
    exact Or.inr ((boundaryRVGraph_mem_iff i V (F i) t).mpr
      ⟨hint,a,hat,haV,y,hy,hproper i a haD y hy,hyt⟩)

end DiamondIntegral.Section2
