import «section 5».VFPolynomialLoci

/-! Finite polynomial equation loci give actual native VF objects with
no RV coordinates. Their tuple interpretation is proved by evaluating
the same polynomial terms in the actual VF field. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
noncomputable section
namespace DiamondIntegral.Section5
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section3.GammaParameters SpecialTransformations.Section5
open DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {n : ℕ}

theorem vfPolynomialRawCode_eval (p : MvPolynomial (Fin n) (VFType (M := M)))
    (x : Fin n → VFType (M := M)) :
    vfPolynomialRawCode p (fun i => (x i).val) = (MvPolynomial.eval x p).val :=
  mvPolynomialCode_eq p _ x (fun _ => rfl)

def vfPolynomialRawLocus (s : Finset (MvPolynomial (Fin n) (VFType (M := M)))) : Set (Fin n → M) :=
  {z | z ∈ sortedUniverse (fun _ : Fin n => .vf) ∧ ∀ p ∈ s,vfPolynomialRawCode p z = iVFZero}

theorem vfPolynomialRawLocus_definable (hc : CanonicalStructure.IsCanonical (M := M))
    (s : Finset (MvPolynomial (Fin n) (VFType (M := M))))
    (hcoeff : ∀ p ∈ s,∀ d,(p.coeff d).val ∈ B.real) :
    DefinableOverBase B (fun _ : Fin n => .vf) (vfPolynomialRawLocus s) := by
  have h := DefinableOverBase.finite_iInter s
    (fun p => {z | z ∈ sortedUniverse (fun _ : Fin n => .vf) ∧ vfPolynomialRawCode p z = iVFZero})
    (fun p hp => vfPolynomial_zero_definable hc p (hcoeff p hp))
  convert h using 1
  ext z
  simp only [vfPolynomialRawLocus,Set.mem_setOf_eq]
  constructor
  · rintro ⟨hz,hp⟩
    exact ⟨hz,fun p hps => ⟨hz,hp p hps⟩⟩
  · rintro ⟨hz,hp⟩
    exact ⟨hz,fun p hps => (hp p hps).2⟩

def nativeVFPolynomialDomain (hc : CanonicalStructure.IsCanonical (M := M))
    (s : Finset (MvPolynomial (Fin n) (VFType (M := M))))
    (hcoeff : ∀ p ∈ s,∀ d,(p.coeff d).val ∈ B.real) :
    GammaGroundDefSet hc B (rawMixedSpace (M := M) n 0) :=
  nativeMixedOfRaw (n := n) (r := 0) (vfPolynomialRawLocus s) (by
    have hsn : Fin.append (fun _ : Fin n => SortTag.vf) (fun _ : Fin 0 => SortTag.rv) = (fun _ : Fin (n+0) => SortTag.vf) := by
      funext i
      exact Fin.addCases (fun j => Fin.append_left _ _ j) (fun j => j.elim0) i
    rw [hsn]
    exact vfPolynomialRawLocus_definable hc s hcoeff)

theorem nativeVFPolynomialDomain_mem (hc : CanonicalStructure.IsCanonical (M := M))
    (s : Finset (MvPolynomial (Fin n) (VFType (M := M))))
    (hcoeff : ∀ p ∈ s,∀ d,(p.coeff d).val ∈ B.real)
    (q : Section2.Mixed M n 0) :
    q ∈ (nativeVFPolynomialDomain hc s hcoeff).carrier ↔ ∀ p ∈ s,MvPolynomial.eval q.1 p = 0 := by
  have he : nativeMixedCode q = fun i => (q.1 i).val := by
    funext i
    have hi : Fin.castAdd 0 i = i := Fin.ext rfl
    have hh : nativeMixedCode q (Fin.castAdd 0 i) = (q.1 i).val := by
      simp only [nativeMixedCode,Fin.append_left,vfValues]
    exact (congrArg (nativeMixedCode q) hi).symm.trans hh
  change (nativeMixedCode q ∈ sortedUniverse (fun _ : Fin n => .vf) ∧
    ∀ p ∈ s,vfPolynomialRawCode p (nativeMixedCode q) = iVFZero) ↔ _
  rw [he]
  constructor
  · rintro ⟨_,h⟩ p hp
    apply Subtype.ext
    exact (vfPolynomialRawCode_eval p q.1).symm.trans (h p hp)
  · intro h
    refine ⟨?_,?_⟩
    · intro i
      simpa only [sortEval,iVF] using (q.1 i).property
    · intro p hp
      exact (vfPolynomialRawCode_eval p q.1).trans (congrArg Subtype.val (h p hp))

def nativeVFPolynomialObject (hc : CanonicalStructure.IsCanonical (M := M))
    (s : Finset (MvPolynomial (Fin n) (VFType (M := M))))
    (hcoeff : ∀ p ∈ s,∀ d,(p.coeff d).val ∈ B.real) : GammaGroundFiniteVFObject hc B :=
  ⟨n,0,nativeVFPolynomialDomain hc s hcoeff,fun _ => Set.toFinite _⟩

end DiamondIntegral.Section5
