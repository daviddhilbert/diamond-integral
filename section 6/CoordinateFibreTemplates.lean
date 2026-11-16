import «section 6».MixedSetParameterTemplates
import «section 6».CentripetalProgramRealizations

/-! The actual coordinate fibres of a mixed set form one complete
original-base family. Proper invariance, double bounds and pullback
geometry specialize with exactly the chosen VF parameter adjoined. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n r : ℕ}

def headFibreCodeIndex : (Fin (n+1) ⊕ Fin r) → Fin 1 ⊕ (Fin n ⊕ Fin r) :=
  Sum.elim (Fin.cases (.inl 0) (fun i => .inr (.inl i))) (fun i => .inr (.inr i))

def headFibreTemplate (A : DefSet (rawMixedSpace (M := M) (n+1) r) S) :
    MixedSetParameterTemplate (M := M) S 1 n r :=
  ⟨{z | z ∘ headFibreCodeIndex ∈ (rawMixedSpace (n+1) r).preimage A.carrier},
    A.definable.preimage_comp headFibreCodeIndex⟩

theorem headFibreCode_at (a : VF M) (x : Mixed M n r) :
    Sum.elim (fun _ : Fin 1 => a.val) (mixedValues x) ∘ headFibreCodeIndex=
      mixedValues (Fin.cons a x.1,x.2) := by
  funext i
  cases i with
  | inl i =>
    refine Fin.cases ?_ (fun j => ?_) i
    · rfl
    · rfl
  | inr i => rfl

theorem mem_headFibreTemplate_iff (A : DefSet (rawMixedSpace (M := M) (n+1) r) S)
    (a : VF M) (x : Mixed M n r) :
    x ∈ ((headFibreTemplate A).fibre (fun _ => a.val)).carrier ↔ (Fin.cons a x.1,x.2) ∈ A.carrier := by
  change (Sum.elim (fun _ : Fin 1 => a.val) (mixedValues x) ∘ headFibreCodeIndex ∈
    (rawMixedSpace (n+1) r).preimage A.carrier) ↔ _
  rw [headFibreCode_at]
  have h := (rawMixedSpace (M := M) (n+1) r).preimage_decode A.carrier
    ⟨mixedValues (Fin.cons a x.1,x.2),mixedValues_mem_domain _⟩
  simpa only [decode_mixedValues] using h

theorem headFibreTemplate_subset
    {A P : DefSet (rawMixedSpace (M := M) (n+1) r) S}
    (hPA : P.carrier ⊆ A.carrier) (a : VF M) :
    ((headFibreTemplate P).fibre (fun _ => a.val)).carrier ⊆
      ((headFibreTemplate A).fibre (fun _ => a.val)).carrier := by
  intro x hx
  exact (mem_headFibreTemplate_iff A a x).mpr (hPA ((mem_headFibreTemplate_iff P a x).mp hx))

theorem headFibreTemplate_properInvariant
    (A : DefSet (rawMixedSpace (M := M) (n+1) r) S) (hA : ProperInvariant S A.carrier) (a : VF M) :
    ProperInvariant (S ∪ Set.range (fun _ : Fin 1 => a.val))
      ((headFibreTemplate A).fibre (fun _ => a.val)).carrier := by
  let C := (headFibreTemplate A).fibre (fun _ => a.val)
  have hMem (x : Mixed M n r) := mem_headFibreTemplate_iff A a x
  refine ⟨C.definable,?_,?_,?_⟩
  · obtain ⟨γ,hγ⟩ := hA.vfBounded
    exact ⟨γ,fun x hx i => hγ (Fin.cons a x.1,x.2) ((hMem x).mp hx) i.succ⟩
  · obtain ⟨γ,hγ⟩ := hA.rvBounded
    exact ⟨γ,fun x hx i => hγ (Fin.cons a x.1,x.2) ((hMem x).mp hx) i⟩
  · intro u
    obtain ⟨α,hNamed,hInv⟩ := hA.radii u
    refine ⟨fun i => α i.succ,(fun i => (hNamed i.succ).mono ?_),?_⟩
    · rintro x (hx | hx)
      · exact Or.inl (Or.inl hx)
      · exact Or.inr hx
    · intro x y hxy
      have hFull : Congruent α (Fin.cons a x) (Fin.cons a y) := by
        intro i
        refine Fin.cases ?_ (fun j => hxy j) i
        change (α 0).val < vfValue (a-a)
        rw [sub_self]
        exact gamma_lt_value_zero (α 0)
      exact ((hMem (x,u)).trans (hInv (Fin.cons a x) (Fin.cons a y) hFull)).trans (hMem (y,u)).symm

theorem headFibreTemplate_doublyBounded
    (A : DefSet (rawMixedSpace (M := M) (n+1) r) S) (hA : VFDoublyBounded A.carrier) (a : VF M) :
    VFDoublyBounded ((headFibreTemplate A).fibre (fun _ => a.val)).carrier := by
  obtain ⟨γ,hγ⟩ := hA
  exact ⟨γ,fun x hx i => hγ (Fin.cons a x.1,x.2) ((mem_headFibreTemplate_iff A a x).mp hx) i.succ⟩

theorem headFibreTemplate_rvPullback
    (A : DefSet (rawMixedSpace (M := M) (n+1) r) S) (hA : IsRVPullback A.carrier) (a : VF M) :
    IsRVPullback ((headFibreTemplate A).fibre (fun _ => a.val)).carrier := by
  apply Set.Subset.antisymm _ (subset_rvHull _)
  intro y hy
  obtain ⟨x,hx,hVF,hRV⟩ := (mem_rvHull_iff _ y).mp hy
  apply (mem_headFibreTemplate_iff A a y).mpr
  apply rvPullback_mem_of_sameRV hA ((mem_headFibreTemplate_iff A a x).mp hx) _ hRV
  funext i
  refine Fin.cases rfl (fun j => congrFun hVF j) i

theorem headFibreTemplate_tagged
    (A : DefSet (rawMixedSpace (M := M) (n+1) r) S)
    (hA : ∀ x ∈ A.carrier,∀ y ∈ A.carrier,x.2=y.2 → tupleRV M x.1=tupleRV M y.1) (a : VF M) :
    ∀ x ∈ ((headFibreTemplate A).fibre (fun _ => a.val)).carrier,
      ∀ y ∈ ((headFibreTemplate A).fibre (fun _ => a.val)).carrier,
        x.2=y.2 → tupleRV M x.1=tupleRV M y.1 := by
  intro x hx y hy hxy
  have h := hA (Fin.cons a x.1,x.2) ((mem_headFibreTemplate_iff A a x).mp hx)
    (Fin.cons a y.1,y.2) ((mem_headFibreTemplate_iff A a y).mp hy) hxy
  exact funext (fun i => congrFun h i.succ)

end DiamondIntegral.Section6
