import «section 4».CoactionGradedMaps

/-! Transport ring maps, their compositions, exact kernels and grading
compatibility along proved presentation equivalences. -/

set_option autoImplicit false
noncomputable section
namespace DiamondIntegral.Section4.RingPresentationTransport
variable {A A' B B' C C' : Type*} [CommRing A] [CommRing A'] [CommRing B] [CommRing B'] [CommRing C] [CommRing C']

def transport (a : A' ≃+* A) (b : B' ≃+* B) (f : A →+* B) : A' →+* B' :=
  b.symm.toRingHom.comp (f.comp a.toRingHom)

theorem transport_apply (a : A' ≃+* A) (b : B' ≃+* B) (f : A →+* B) (x : A') :
    transport a b f x = b.symm (f (a x)) := rfl

theorem comparison (a : A' ≃+* A) (b : B' ≃+* B) (f : A →+* B) :
    b.toRingHom.comp (transport a b f) = f.comp a.toRingHom := by
  ext x
  exact b.apply_symm_apply (f (a x))

theorem transport_comp (a : A' ≃+* A) (b : B' ≃+* B) (c : C' ≃+* C) (f : A →+* B) (g : B →+* C) :
    (transport b c g).comp (transport a b f) = transport a c (g.comp f) := by
  ext x
  change c.symm (g (b (b.symm (f (a x))))) = c.symm (g (f (a x)))
  rw [b.apply_symm_apply]

theorem transport_id (a : A' ≃+* A) : transport a a (RingHom.id A) = RingHom.id A' := by
  ext x
  exact a.symm_apply_apply x

theorem kernel (a : A' ≃+* A) (b : B' ≃+* B) (f : A →+* B) :
    RingHom.ker (transport a b f) = (RingHom.ker f).comap a.toRingHom := by
  ext x
  change b.symm (f (a x)) = 0 ↔ f (a x) = 0
  constructor
  · intro h
    exact b.symm.injective (h.trans (map_zero b.symm).symm)
  · intro h
    rw [h, map_zero]

theorem map_mem {aPiece : ℕ → AddSubgroup A'} {bPiece : ℕ → AddSubgroup B'}
    {oldAPiece : ℕ → AddSubgroup A} {oldBPiece : ℕ → AddSubgroup B}
    (a : A' ≃+* A) (b : B' ≃+* B) (f : A →+* B)
    (ha : ∀ n x, x ∈ aPiece n → a x ∈ oldAPiece n)
    (hb : ∀ n x, x ∈ oldBPiece n → b.symm x ∈ bPiece n)
    (hf : ∀ n x, x ∈ oldAPiece n → f x ∈ oldBPiece n)
    {n : ℕ} {x : A'} (hx : x ∈ aPiece n) : transport a b f x ∈ bPiece n :=
  hb n _ (hf n _ (ha n _ hx))


theorem transport_value (a : A' ≃+* A) (b : B' ≃+* B) (f : A →+* B) (x : A') (y : B')
    (h : f (a x) = b y) : transport a b f x = y := by
  change b.symm (f (a x)) = y
  rw [h, b.symm_apply_apply]

theorem inverse_eq (a : A' ≃+* A) (g : A →+* A') (h : a.toRingHom.comp g = RingHom.id A) :
    a.symm.toRingHom = g := by
  ext x
  apply a.injective
  exact (a.apply_symm_apply x).trans (RingHom.congr_fun h x).symm

end DiamondIntegral.Section4.RingPresentationTransport
