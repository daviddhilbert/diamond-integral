import «section 5».NativeMixedKeyMaps

/-! Prepared mixed families retain separate base, old RV and fibre
coordinate blocks. Their full RV data are constant on actual RV fibres. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace DiamondIntegral.Section5
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section5
open DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {p k l q a : ℕ}

def preparedFamilyBase (w : Point (M := M) (p+k) (l+(q+a))) : Point (M := M) p l :=
  (w.1 ∘ Fin.castAdd k,w.2 ∘ Fin.castAdd (q+a))

def preparedFamilyOldRV (w : Point (M := M) (p+k) (l+(q+a))) : Fin q → RV (M := M) :=
  w.2 ∘ Fin.natAdd l ∘ Fin.castAdd a

def preparedFamilyFibreRV (w : Point (M := M) (p+k) (l+(q+a))) : Fin a → RV (M := M) :=
  w.2 ∘ Fin.natAdd l ∘ Fin.natAdd q

def preparedFamilyFibreVF (w : Point (M := M) (p+k) (l+(q+a))) : Fin k → VF (M := M) :=
  w.1 ∘ Fin.natAdd p

theorem preparedFamily_reconstruct (w : Point (M := M) (p+k) (l+(q+a))) :
    (Fin.append (preparedFamilyBase w).1 (preparedFamilyFibreVF w),
      Fin.append (preparedFamilyBase w).2 (Fin.append (preparedFamilyOldRV w) (preparedFamilyFibreRV w))) = w := by
  apply Prod.ext Fin.append_castAdd_natAdd
  have ht : Fin.append (preparedFamilyOldRV w) (preparedFamilyFibreRV w) = w.2 ∘ Fin.natAdd l := by
    change Fin.append ((w.2 ∘ Fin.natAdd l) ∘ Fin.castAdd a) ((w.2 ∘ Fin.natAdd l) ∘ Fin.natAdd q) = _
    exact Fin.append_castAdd_natAdd (f := w.2 ∘ Fin.natAdd l)
  exact (congrArg (Fin.append (preparedFamilyBase w).2) ht).trans Fin.append_castAdd_natAdd

theorem preparedFamilyBase_sameRV {w w' : Point (M := M) (p+k) (l+(q+a))} (h : SameRV w w') :
    SameRV (preparedFamilyBase w) (preparedFamilyBase w') := by
  obtain ⟨hv,hr⟩ := (sameRV_iff w w').mp h
  apply (sameRV_iff _ _).mpr
  exact ⟨fun i => hv (Fin.castAdd k i),congrArg (fun t => t ∘ Fin.castAdd (q+a)) hr⟩

def PreparedFamilyRVData (M : Type) [LRV.Structure M] (p k l q a : ℕ) :=
  (Fin (p+l) → RV (M := M)) × (Fin q → RV (M := M)) × (Fin a → RV (M := M)) × (Fin k → RV (M := M))

def preparedFamilyRVData (w : Point (M := M) (p+k) (l+(q+a))) : PreparedFamilyRVData M p k l q a :=
  ((flatKey (preparedFamilyBase w)).2,preparedFamilyOldRV w,preparedFamilyFibreRV w,
    Section2.tupleRV M (preparedFamilyFibreVF w))

theorem preparedFamilyRVData_sameRV {w w' : Point (M := M) (p+k) (l+(q+a))} (h : SameRV w w') :
    preparedFamilyRVData w = preparedFamilyRVData w' := by
  obtain ⟨hv,hr⟩ := (sameRV_iff w w').mp h
  have hb := congrArg Prod.snd ((flatKey_eq_iff _ _).mpr (preparedFamilyBase_sameRV h))
  have ho : preparedFamilyOldRV w = preparedFamilyOldRV w' :=
    congrArg (fun t => t ∘ Fin.natAdd l ∘ Fin.castAdd a) hr
  have hu : preparedFamilyFibreRV w = preparedFamilyFibreRV w' :=
    congrArg (fun t => t ∘ Fin.natAdd l ∘ Fin.natAdd q) hr
  have hy : Section2.tupleRV M (preparedFamilyFibreVF w) = Section2.tupleRV M (preparedFamilyFibreVF w') :=
    funext (fun i => hv (Fin.natAdd p i))
  exact Prod.ext hb (Prod.ext ho (Prod.ext hu hy))

theorem preparedFamilyRVData_pullback (C : Set (Point (M := M) p l)) (hC : IsRVPullback C)
    (P : PreparedFamilyRVData M p k l q a → Prop) :
    IsRVPullback {w : Point (M := M) (p+k) (l+(q+a)) | preparedFamilyBase w ∈ C ∧ P (preparedFamilyRVData w)} := by
  apply (isRVPullback_iff _).mpr
  intro w hw w' hsame
  refine ⟨(mem_iff_sameRV hC (preparedFamilyBase_sameRV hsame)).mp hw.1,?_⟩
  exact (preparedFamilyRVData_sameRV hsame) ▸ hw.2

end DiamondIntegral.Section5
