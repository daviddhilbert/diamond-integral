import «section 6».ApertureCoefficients
import Section3.FiniteImage

/-! An actual scalar focus map depending only on the existing RV tags
has finite original-base definable image. The full graph is projected
before applying the checked RV-to-VF finite-image theorem. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2

namespace DiamondIntegral.Section6

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n r : ℕ} {S : Set M}
variable {A : DefSet (rawMixedSpace (M := M) n r) S}
variable {B : DefSet (rawVFSpace (M := M) 1) S}

def scalarFocusImage (f : Map A B) : Set (VF M) := Set.range (fun p : A => (f p).val 0)

def rvScalarFocusGraph (f : Map A B) : Set (Fin r ⊕ Fin 1 → M) :=
  {z | ∃ p : A, Sum.elim (rvValues p.val.2) (vfValues (f p).val) = z}

theorem scalarMapGraph_iff (f : Map A B) (z : (Fin n ⊕ Fin r) ⊕ Fin 1 → M) :
    z ∈ (rawMixedSpace n r).relation (rawVFSpace 1) f.graph ↔
      ∃ p : A, Sum.elim (mixedValues p.val) (vfValues (f p).val) = z := by
  constructor
  · rintro ⟨hx,hy,p,hp,hfp⟩
    have hxcode : mixedValues p.val = z ∘ Sum.inl := by rw [hp]; exact mixedValues_decode _
    have hycode : vfValues (f p).val = z ∘ Sum.inr := by rw [hfp]; exact vfValues_decode _
    exact ⟨p,by funext i; cases i with
      | inl i => exact congrFun hxcode i
      | inr i => exact congrFun hycode i⟩
  · rintro ⟨p,rfl⟩
    have hd := (rawMixedSpace n r).relation_decode (rawVFSpace 1) f.graph
      ⟨mixedValues p.val,mixedValues_mem_domain _⟩ ⟨vfValues (f p).val,Set.mem_range_self _⟩
    rw [decode_mixedValues,decode_vfValues] at hd
    exact hd.mpr ⟨p,rfl,rfl⟩

theorem rvScalarFocusGraph_definable (f : Map A B) : S.Definable LRV (rvScalarFocusGraph f) := by
  let π : Fin r ⊕ Fin 1 → (Fin n ⊕ Fin r) ⊕ Fin 1 := Sum.elim (Sum.inl ∘ Sum.inr) Sum.inr
  have h := f.graph_definable.image_comp π
  convert h using 1
  ext z
  constructor
  · rintro ⟨p,rfl⟩
    exact ⟨Sum.elim (mixedValues p.val) (vfValues (f p).val),
      (scalarMapGraph_iff f _).mpr ⟨p,rfl⟩,by funext i; cases i <;> rfl⟩
  · rintro ⟨w,hw,he⟩
    obtain ⟨p,hp⟩ := (scalarMapGraph_iff f w).mp hw
    exact ⟨p,by rw [← he,← hp]; funext i; cases i <;> rfl⟩

theorem scalarFocusImage_definable (f : Map A B) :
    S.Definable₁ LRV (Subtype.val '' scalarFocusImage f) := by
  have h := (rvScalarFocusGraph_definable f).image_comp (Sum.inr : Fin 1 → Fin r ⊕ Fin 1)
  change S.Definable LRV {z : Fin 1 → M | z 0 ∈ Subtype.val '' scalarFocusImage f}
  convert h using 1
  ext z
  constructor
  · rintro ⟨_,⟨p,rfl⟩,he⟩
    refine ⟨Sum.elim (rvValues p.val.2) (vfValues (f p).val),⟨p,rfl⟩,?_⟩
    funext i
    fin_cases i
    exact he
  · rintro ⟨w,⟨p,rfl⟩,he⟩
    exact ⟨(f p).val 0,⟨p,rfl⟩,congrFun he 0⟩

theorem scalarFocusImage_finite
    (hc : CanonicalStructure.IsCanonical (M := M)) {κ : Cardinal} (hs : Saturated M κ)
    (hsmall : Cardinal.mk S < κ) (f : Map A B)
    (hRV : ∀ p q : A, p.val.2 = q.val.2 → (f p).val 0 = (f q).val 0) :
    (scalarFocusImage f).Finite := by
  have hsort (t : Fin r → M) (y : Fin 1 → M) (hy : Sum.elim t y ∈ rvScalarFocusGraph f) :
      (∀ i, iRV (t i)) ∧ ∀ i, iVF (y i) := by
    obtain ⟨p,hp⟩ := hy
    constructor
    · intro i
      have he : (p.val.2 i).val = t i := congrFun hp (.inl i)
      rw [← he]
      exact (p.val.2 i).property
    · intro i
      have he : ((f p).val i).val = y i := congrFun hp (.inr i)
      rw [← he]
      exact ((f p).val i).property
  have hf (t : Fin r → M) : {y | Sum.elim t y ∈ rvScalarFocusGraph f}.Finite := by
    apply Set.Subsingleton.finite
    intro y hy z hz
    obtain ⟨p,hp⟩ := hy
    obtain ⟨q,hq⟩ := hz
    have heRV : p.val.2 = q.val.2 := funext fun i =>
      Subtype.ext ((congrFun hp (.inl i)).trans (congrFun hq (.inl i)).symm)
    funext i
    fin_cases i
    exact (congrFun hp (.inr 0)).symm.trans
      ((congrArg Subtype.val (hRV p q heRV)).trans (congrFun hq (.inr 0)))
  have hfin := finite_rv_to_vf_tuple_relation_image hc hs S hsmall _ (rvScalarFocusGraph_definable f) hsort hf
  have hi : Function.Injective (fun x : VF M => fun _ : Fin 1 => x.val) := by
    intro x y he
    exact Subtype.ext (congrFun he 0)
  apply (hfin.preimage hi.injOn).subset
  rintro _ ⟨p,rfl⟩
  exact ⟨rvValues p.val.2,p,by funext i; cases i with
    | inl i => rfl
    | inr i => fin_cases i; rfl⟩

end DiamondIntegral.Section6
