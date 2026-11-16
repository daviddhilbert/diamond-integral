import «section 6».ContinuousParameterLoci

/-! First-order admissibility of total single-valued VF graph rows.
These complete parameter loci are used before applying compactness to
parameter-dependent focus definitions. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section8
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {ι : Type} [Finite ι] {n m : ℕ}

def totalVFGraphParameterLocus (R : Set (ι ⊕ (Fin n ⊕ Fin m) → M)) : Set (ι → M) :=
  {t | ∀ x ∈ vfRawUniverse n,∃ y ∈ vfRawUniverse m,Sum.elim t (Sum.elim x y) ∈ R}

theorem totalVFGraphParameterLocus_definable
    (R : Set (ι ⊕ (Fin n ⊕ Fin m) → M)) (hR : S.Definable LRV R) :
    S.Definable LRV (totalVFGraphParameterLocus R) := by
  let e : ι ⊕ (Fin n ⊕ Fin m) → (ι ⊕ Fin n) ⊕ Fin m :=
    Sum.elim (Sum.inl ∘ Sum.inl) (Sum.elim (Sum.inl ∘ Sum.inr) Sum.inr)
  have hExists := ((hR.preimage_comp e).inter
    ((vfRawUniverse_definable S m).preimage_comp (Sum.inr : Fin m → (ι ⊕ Fin n) ⊕ Fin m))).exists_of_finite
  have hBad := ((vfRawUniverse_definable S n).preimage_comp (Sum.inr : Fin n → ι ⊕ Fin n)).inter hExists.compl
  convert (hBad.exists_of_finite).compl using 1
  ext t
  have he (x : Fin n → M) (y : Fin m → M) :
      Sum.elim (Sum.elim t x) y ∘ e=Sum.elim t (Sum.elim x y) := by funext j; rcases j with j | (j | j) <;> rfl
  change (∀ x,x ∈ vfRawUniverse n → ∃ y,y ∈ vfRawUniverse m ∧ Sum.elim t (Sum.elim x y) ∈ R) ↔
    ¬ ∃ x : Fin n → M,x ∈ vfRawUniverse n ∧
      ¬ ∃ y : Fin m → M,Sum.elim (Sum.elim t x) y ∘ e ∈ R ∧ y ∈ vfRawUniverse m
  simp only [he]
  constructor
  · intro h hn
    obtain ⟨x,hx,hNo⟩ := hn
    obtain ⟨y,hy,hr⟩ := h x hx
    exact hNo ⟨y,hr,hy⟩
  · intro h x hx
    by_contra hn
    apply h
    refine ⟨x,hx,?_⟩
    rintro ⟨y,hr,hy⟩
    exact hn ⟨y,hy,hr⟩

def singleVFGraphParameterLocus (R : Set (ι ⊕ (Fin n ⊕ Fin m) → M)) : Set (ι → M) :=
  {t | ∀ x y z,Sum.elim t (Sum.elim x y) ∈ R → Sum.elim t (Sum.elim x z) ∈ R → y=z}

theorem singleVFGraphParameterLocus_definable
    (R : Set (ι ⊕ (Fin n ⊕ Fin m) → M)) (hR : S.Definable LRV R) :
    S.Definable LRV (singleVFGraphParameterLocus R) := by
  let left : ι ⊕ (Fin n ⊕ Fin m) → (ι ⊕ Fin n) ⊕ (Fin m ⊕ Fin m) :=
    Sum.elim (Sum.inl ∘ Sum.inl) (Sum.elim (Sum.inl ∘ Sum.inr) (Sum.inr ∘ Sum.inl))
  let right : ι ⊕ (Fin n ⊕ Fin m) → (ι ⊕ Fin n) ⊕ (Fin m ⊕ Fin m) :=
    Sum.elim (Sum.inl ∘ Sum.inl) (Sum.elim (Sum.inl ∘ Sum.inr) (Sum.inr ∘ Sum.inr))
  have hEq : S.Definable LRV {w : (ι ⊕ Fin n) ⊕ (Fin m ⊕ Fin m) → M |
      (fun i => w (.inr (.inl i)))=(fun i => w (.inr (.inr i)))} := by
    have hEach (i : Fin m) : S.Definable LRV {w : (ι ⊕ Fin n) ⊕ (Fin m ⊕ Fin m) → M |
        w (.inr (.inl i))=w (.inr (.inr i))} :=
      (Set.DefinableFun.proj LRV).ofPred_eq (Set.DefinableFun.proj LRV)
    convert Set.definable_iInter_of_finite hEach using 1
    ext w
    simp only [Set.mem_iInter,Set.mem_setOf_eq,funext_iff]
  have hBad := ((hR.preimage_comp left).inter (hR.preimage_comp right)).inter hEq.compl
  convert (hBad.exists_of_finite.exists_of_finite).compl using 1
  ext t
  have hLeft (x : Fin n → M) (yz : Fin m ⊕ Fin m → M) :
      Sum.elim (Sum.elim t x) yz ∘ left=Sum.elim t (Sum.elim x (yz ∘ Sum.inl)) := by
    funext j; rcases j with j | (j | j) <;> rfl
  have hRight (x : Fin n → M) (yz : Fin m ⊕ Fin m → M) :
      Sum.elim (Sum.elim t x) yz ∘ right=Sum.elim t (Sum.elim x (yz ∘ Sum.inr)) := by
    funext j; rcases j with j | (j | j) <;> rfl
  change (∀ x y z,Sum.elim t (Sum.elim x y) ∈ R → Sum.elim t (Sum.elim x z) ∈ R → y=z) ↔
    ¬ ∃ x : Fin n → M,∃ yz : Fin m ⊕ Fin m → M,
      (Sum.elim (Sum.elim t x) yz ∘ left ∈ R ∧ Sum.elim (Sum.elim t x) yz ∘ right ∈ R) ∧
        (fun i => yz (.inl i)) ≠ (fun i => yz (.inr i))
  have hNeg : (∀ x y z,Sum.elim t (Sum.elim x y) ∈ R → Sum.elim t (Sum.elim x z) ∈ R → y=z) ↔
    ¬ ∃ x y z,Sum.elim t (Sum.elim x y) ∈ R ∧ Sum.elim t (Sum.elim x z) ∈ R ∧ y ≠ z := by
      simp only [not_exists,not_and,not_not]
  rw [hNeg]
  apply not_congr
  constructor
  · rintro ⟨x,y,z,hy,hz,hne⟩
    exact ⟨x,Sum.elim y z,by simpa only [hLeft,hRight,Sum.elim_comp_inl,Sum.elim_comp_inr] using ⟨⟨hy,hz⟩,hne⟩⟩
  · rintro ⟨x,yz,⟨hy,hz⟩,hne⟩
    exact ⟨x,yz ∘ Sum.inl,yz ∘ Sum.inr,by rw [← hLeft]; exact hy,by rw [← hRight]; exact hz,hne⟩

end DiamondIntegral.Section6
