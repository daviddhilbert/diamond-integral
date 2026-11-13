import Mathlib.Data.Set.Finite.Basic
set_option autoImplicit false
noncomputable section
namespace DiamondIntegral.Section3
variable {X Y : Type}

/-- Values at which a subset splits a fibre of a quotient map. -/
def mixedFibreValues (v : X → Y) (A : Set X) : Set Y := v '' A ∩ v '' Aᶜ

/-- Values whose entire fibre lies in A, with a nonempty-fibre guard. -/
def fullFibreValues (v : X → Y) (A : Set X) : Set Y := v '' A \ v '' Aᶜ

theorem mixedFibreValues_finite_of_exceptions (v : X → Y) (A T : Set X) (hT : T.Finite)
    (hpattern : ∀ x y, v x = v y → x ∉ T → y ∉ T → (x ∈ A ↔ y ∈ A)) :
    (mixedFibreValues v A).Finite := by
  apply (hT.image v).subset
  rintro z ⟨⟨x,hx,hxz⟩,⟨y,hy,hyz⟩⟩
  by_cases hxT : x ∈ T
  · exact ⟨x,hxT,hxz⟩
  by_cases hyT : y ∈ T
  · exact ⟨y,hyT,hyz⟩
  exact (hy ((hpattern x y (hxz.trans hyz.symm) hxT hyT).mp hx)).elim

theorem mem_fullFibreValues_iff (v : X → Y) (A : Set X) (y : Y) :
    y ∈ fullFibreValues v A ↔ (∃ x, v x = y) ∧ ∀ x, v x = y → x ∈ A := by
  constructor
  · rintro ⟨⟨x,hx,he⟩,hn⟩
    exact ⟨⟨x,he⟩,fun t ht => by by_contra hta; exact hn ⟨t,hta,ht⟩⟩
  · rintro ⟨⟨x,hx⟩,h⟩
    exact ⟨⟨x,h x hx,hx⟩,fun ⟨t,ht,he⟩ => ht (h t he)⟩

theorem fullFibreValues_subset (v : X → Y) (A : Set X) : v ⁻¹' fullFibreValues v A ⊆ A := by
  intro x hx
  exact ((mem_fullFibreValues_iff v A (v x)).mp hx).2 x rfl

theorem mixed_full_fibre_partition (v : X → Y) (A : Set X) :
    (A ∩ v ⁻¹' mixedFibreValues v A) ∪ v ⁻¹' fullFibreValues v A = A := by
  ext x
  constructor
  · exact fun h => h.elim (fun h => h.1) (fun h => fullFibreValues_subset v A h)
  · intro hx
    by_cases hn : v x ∈ v '' Aᶜ
    · exact Or.inl ⟨hx,⟨⟨x,hx,rfl⟩,hn⟩⟩
    · exact Or.inr ⟨⟨x,hx,rfl⟩,hn⟩

theorem mixed_full_fibre_disjoint (v : X → Y) (A : Set X) :
    Disjoint (A ∩ v ⁻¹' mixedFibreValues v A) (v ⁻¹' fullFibreValues v A) := by
  apply Set.disjoint_left.mpr
  intro x hx hy
  exact hy.2 hx.2.2

/-- Any prescribed finite collection of value fibres can be moved to the
residue part. In particular this isolates the zero RV fibre. -/
theorem mixed_full_fibre_partition_avoiding (v : X → Y) (A : Set X) (E : Set Y) :
    (A ∩ v ⁻¹' (mixedFibreValues v A ∪ E)) ∪
      v ⁻¹' (fullFibreValues v A \ E) = A := by
  ext x
  constructor
  · intro h
    exact h.elim (fun h => h.1) (fun h => fullFibreValues_subset v A h.1)
  · intro hx
    by_cases he : v x ∈ E
    · exact Or.inl ⟨hx,Or.inr he⟩
    have hm := Set.ext_iff.mp (mixed_full_fibre_partition v A) x
    rcases hm.mpr hx with h | h
    · exact Or.inl ⟨hx,Or.inl h.2⟩
    · exact Or.inr ⟨h,he⟩

theorem mixed_full_fibre_disjoint_avoiding (v : X → Y) (A : Set X) (E : Set Y) :
    Disjoint (A ∩ v ⁻¹' (mixedFibreValues v A ∪ E))
      (v ⁻¹' (fullFibreValues v A \ E)) := by
  apply Set.disjoint_left.mpr
  intro x hx hy
  rcases hx.2 with hm | he
  · exact hy.1.2 hm.2
  · exact hy.2 he
end DiamondIntegral.Section3
