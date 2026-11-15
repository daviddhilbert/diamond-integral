import «section 5».ElementaryRVConstants

/-! Elementary original-language embeddings induce actual field maps on
VF and commute with rv. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace DiamondIntegral.Section5
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer SpecialTransformations.Section3
variable {M N : Type} [LRV.Structure M] [LRV.Structure N]
variable [M ⊨ Axioms.ACVF] [N ⊨ Axioms.ACVF]
variable (e : M ↪ₑ[LRV] N)

def elementaryVFMap (a : VFType (M := M)) : VFType (M := N) :=
  ⟨e a.val,by
    have h := e.map_rel Rel.memVF ![a.val]
    have ht : e ∘ (![a.val] : Fin 1 → M) = ![e a.val] := by funext i; fin_cases i; rfl
    rw [ht] at h
    exact h.mpr a.property⟩

def elementaryVFFieldHom : VFType (M := M) →+* VFType (M := N) where
  toFun := elementaryVFMap e
  map_zero' := by
    apply Subtype.ext
    have ht : e ∘ (Fin.elim0 : Fin 0 → M) = (Fin.elim0 : Fin 0 → N) := Subsingleton.elim _ _
    change e (Structure.funMap (L := LRV) Fn.vfZero Fin.elim0) = Structure.funMap (L := LRV) Fn.vfZero Fin.elim0
    simpa only [ht] using e.map_fun Fn.vfZero Fin.elim0
  map_one' := by
    apply Subtype.ext
    have ht : e ∘ (Fin.elim0 : Fin 0 → M) = (Fin.elim0 : Fin 0 → N) := Subsingleton.elim _ _
    change e (Structure.funMap (L := LRV) Fn.vfOne Fin.elim0) = Structure.funMap (L := LRV) Fn.vfOne Fin.elim0
    simpa only [ht] using e.map_fun Fn.vfOne Fin.elim0
  map_add' a b := by
    apply Subtype.ext
    have ht : e ∘ (![a.val,b.val] : Fin 2 → M) = ![e a.val,e b.val] := by funext i; fin_cases i <;> rfl
    change e (Structure.funMap (L := LRV) Fn.vfAdd ![a.val,b.val]) = Structure.funMap (L := LRV) Fn.vfAdd ![e a.val,e b.val]
    simpa only [ht] using e.map_fun Fn.vfAdd ![a.val,b.val]
  map_mul' a b := by
    apply Subtype.ext
    have ht : e ∘ (![a.val,b.val] : Fin 2 → M) = ![e a.val,e b.val] := by funext i; fin_cases i <;> rfl
    change e (Structure.funMap (L := LRV) Fn.vfMul ![a.val,b.val]) = Structure.funMap (L := LRV) Fn.vfMul ![e a.val,e b.val]
    simpa only [ht] using e.map_fun Fn.vfMul ![a.val,b.val]

theorem elementaryVFFieldHom_rv (a : VFType (M := M)) :
    elementaryRVMap e (CanonicalRV.encodedRv a) = CanonicalRV.encodedRv (elementaryVFFieldHom e a) := by
  apply Subtype.ext
  have ht : e ∘ (![a.val] : Fin 1 → M) = ![e a.val] := by funext i; fin_cases i; rfl
  change e (Structure.funMap (L := LRV) Fn.rvMap ![a.val]) = Structure.funMap (L := LRV) Fn.rvMap ![e a.val]
  simpa only [ht] using e.map_fun Fn.rvMap ![a.val]

end DiamondIntegral.Section5
