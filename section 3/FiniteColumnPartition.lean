import «section 3».ValueFibrePartition
set_option autoImplicit false
noncomputable section
namespace DiamondIntegral.Section3
variable {X Y : Type}

def relationColumn (R : Y → X → Prop) (x : X) : Set Y := {y | R y x}

theorem finite_columns_of_constant_off_finite (R : Y → X → Prop) (D T : Set X)
    (hT : T.Finite) (h : ∀ x ∈ D, ∀ u ∈ D, x ∉ T → u ∉ T → relationColumn R x = relationColumn R u) :
    (relationColumn R '' D).Finite := by
  classical
  by_cases he : (D \ T).Nonempty
  · obtain ⟨u,hu,huT⟩ := he
    apply ((hT.image (relationColumn R)).union (Set.finite_singleton (relationColumn R u))).subset
    rintro _ ⟨x,hx,rfl⟩
    by_cases hxT : x ∈ T
    · exact Or.inl ⟨x,hxT,rfl⟩
    · exact Or.inr (h x hx u hu hxT huT)
  · apply (hT.image (relationColumn R)).subset
    rintro _ ⟨x,hx,rfl⟩
    have hxT : x ∈ T := by
      by_contra hn
      exact he ⟨x,hx,hn⟩
    exact ⟨x,hxT,rfl⟩

/-- Intrinsic column classes give a finite disjoint partition. This set
lemma does not assert that classes defined using representatives are
definable over a smaller parameter base. -/
theorem finite_column_partition (R : Y → X → Prop) (D : Set X)
    (hfin : (relationColumn R '' D).Finite) :
    ∃ P : Finset (Set X),
      (∀ W ∈ P, W.Nonempty ∧ W ⊆ D ∧ ∀ x ∈ W, ∀ u ∈ W, relationColumn R x = relationColumn R u) ∧
      (P : Set (Set X)).Pairwise Disjoint ∧ D = {x | ∃ W ∈ P, x ∈ W} := by
  classical
  let cell (c : Set Y) : Set X := {x | x ∈ D ∧ relationColumn R x = c}
  let P : Finset (Set X) := hfin.toFinset.image cell
  refine ⟨P,?_,?_,?_⟩
  · intro W hW
    obtain ⟨c,hc,rfl⟩ := Finset.mem_image.mp hW
    obtain ⟨x,hx,hxc⟩ := hfin.mem_toFinset.mp hc
    exact ⟨⟨x,hx,hxc⟩,fun _ h => h.1,fun _ hx _ hu => hx.2.trans hu.2.symm⟩
  · intro W hW V hV hne
    obtain ⟨c,hc,rfl⟩ := Finset.mem_image.mp hW
    obtain ⟨d,hd,rfl⟩ := Finset.mem_image.mp hV
    apply Set.disjoint_left.mpr
    intro x hx hu
    have hcd : c = d := hx.2.symm.trans hu.2
    exact hne (congrArg cell hcd)
  · ext x
    constructor
    · intro hx
      exact ⟨cell (relationColumn R x),Finset.mem_image.mpr ⟨_,hfin.mem_toFinset.mpr ⟨x,hx,rfl⟩,rfl⟩,hx,rfl⟩
    · rintro ⟨W,hW,hx⟩
      obtain ⟨c,hc,rfl⟩ := Finset.mem_image.mp hW
      exact hx.1
end DiamondIntegral.Section3
