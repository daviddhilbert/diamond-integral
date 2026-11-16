import «section 6».SynchronizedFocusSteps

/-! Finite syntactic shapes and actual realizations of common chains.
The entire permitted component data are retained in a Type-valued
witness. RV arities are determined by the finite shape, rather than
being separate unbounded choices at each intermediate stage. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
universe u

inductive SynchronizedChainShape where
  | identity
  | regularize
  | centripetal
  | comp : SynchronizedChainShape → SynchronizedChainShape → SynchronizedChainShape

def SynchronizedChainShape.size : SynchronizedChainShape → ℕ
  | .identity => 0
  | .regularize => 1
  | .centripetal => 1
  | .comp a b => a.size+b.size

def SynchronizedChainShape.targetArity (n r : ℕ) : SynchronizedChainShape → ℕ
  | .identity => r
  | .regularize => n+r
  | .centripetal => 1+r
  | .comp a b => b.targetArity n (a.targetArity n r)

theorem SynchronizedChainShape.targetArity_le (shape : SynchronizedChainShape) (n r : ℕ) :
    shape.targetArity n r ≤ r+(n+1)*shape.size := by
  induction shape generalizing r with
  | identity => simpa only [targetArity,size,Nat.mul_zero,Nat.add_zero] using (Nat.le_refl r)
  | regularize => simp only [targetArity,size,Nat.mul_one]; omega
  | centripetal => simp only [targetArity,size,Nat.mul_one]; omega
  | comp a b iha ihb =>
    have h := (ihb (a.targetArity n r)).trans (Nat.add_le_add_right (iha r) ((n+1)*b.size))
    simpa only [targetArity,size,Nat.mul_add,Nat.add_assoc] using h

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n : ℕ} {I : Type u}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

inductive SynchronizedChainRealization : SynchronizedChainShape → {r s : ℕ} →
    (A : DefSet (rawMixedSpace (M := M) n r) S) →
    (B : DefSet (rawMixedSpace (M := M) n s) S) → Map A B →
    (I → DefSet (rawMixedSpace (M := M) n r) S) → Type u where
  | identity (A : DefSet (rawMixedSpace (M := M) n r) S) (hA : ProperInvariant S A.carrier)
      (P : I → DefSet (rawMixedSpace (M := M) n r) S) (hPA : ∀ i,(P i).carrier ⊆ A.carrier)
      (hP : ∀ i,ProperInvariant S (P i).carrier) :
      SynchronizedChainRealization .identity A A (Map.id A) P
  | regularize (A : DefSet (rawMixedSpace (M := M) n r) S)
      (hA : ProperInvariant S A.carrier) (hVF : VFDoublyBounded A.carrier)
      (P : I → DefSet (rawMixedSpace (M := M) n r) S) (hPA : ∀ i,(P i).carrier ⊆ A.carrier)
      (hP : ∀ i,ProperInvariant S (P i).carrier) (hPVF : ∀ i,VFDoublyBounded (P i).carrier) :
      SynchronizedChainRealization .regularize A (regularizeMap A).image (regularization A) P
  | centripetal (A : DefSet (rawMixedSpace (M := M) n r) S) (D : CentripetalData (G := G) A)
      (P : I → DefSet (rawMixedSpace (M := M) n r) S) (hPA : ∀ i,(P i).carrier ⊆ A.carrier)
      (E : ∀ i,CentripetalData (G := G) (P i)) (hData : ∀ i,ApertureRestrictionData D (E i)) :
      SynchronizedChainRealization .centripetal A D.map.image D.bijection P
  | comp {r s t : ℕ} {A : DefSet (rawMixedSpace (M := M) n r) S}
      {B : DefSet (rawMixedSpace (M := M) n s) S} {C : DefSet (rawMixedSpace (M := M) n t) S}
      {f : Map A B} {g : Map B C} {a b : SynchronizedChainShape}
      (P : I → DefSet (rawMixedSpace (M := M) n r) S) (hPA : ∀ i,(P i).carrier ⊆ A.carrier)
      (F : SynchronizedChainRealization a A B f P)
      (H : SynchronizedChainRealization b B C g (fun i => (f.restrict (hPA i)).image)) :
      SynchronizedChainRealization (.comp a b) A C (g.comp f) P

theorem SynchronizedChainRealization.toChain {shape : SynchronizedChainShape} {r s : ℕ}
    {A : DefSet (rawMixedSpace (M := M) n r) S} {B : DefSet (rawMixedSpace (M := M) n s) S}
    {f : Map A B} {P : I → DefSet (rawMixedSpace (M := M) n r) S}
    (F : SynchronizedChainRealization (G := G) shape A B f P) :
    SynchronizedCentripetalChain (G := G) I A B f P := by
  induction F with
  | identity A hA P hPA hP => exact .identity A hA P hPA hP
  | regularize A hA hVF P hPA hP hPVF => exact .regularize A hA hVF P hPA hP hPVF
  | centripetal A D P hPA E hData => exact .centripetal A D P hPA E hData
  | comp P hPA F H ihF ihH => exact .comp P hPA ihF ihH

theorem SynchronizedCentripetalChain.exists_realization {r s : ℕ}
    {A : DefSet (rawMixedSpace (M := M) n r) S} {B : DefSet (rawMixedSpace (M := M) n s) S}
    {f : Map A B} {P : I → DefSet (rawMixedSpace (M := M) n r) S}
    (h : SynchronizedCentripetalChain (G := G) I A B f P) :
    ∃ shape : SynchronizedChainShape,Nonempty (SynchronizedChainRealization (G := G) shape A B f P) := by
  induction h with
  | identity A hA P hPA hP => exact ⟨.identity,⟨.identity A hA P hPA hP⟩⟩
  | regularize A hA hVF P hPA hP hPVF => exact ⟨.regularize,⟨.regularize A hA hVF P hPA hP hPVF⟩⟩
  | centripetal A D P hPA E hData => exact ⟨.centripetal,⟨.centripetal A D P hPA E hData⟩⟩
  | comp P hPA hf hg ihf ihg =>
    obtain ⟨a,⟨F⟩⟩ := ihf
    obtain ⟨b,⟨H⟩⟩ := ihg
    exact ⟨.comp a b,⟨.comp P hPA F H⟩⟩

theorem SynchronizedChainRealization.target_arity {shape : SynchronizedChainShape} {r s : ℕ}
    {A : DefSet (rawMixedSpace (M := M) n r) S} {B : DefSet (rawMixedSpace (M := M) n s) S}
    {f : Map A B} {P : I → DefSet (rawMixedSpace (M := M) n r) S}
    (F : SynchronizedChainRealization (G := G) shape A B f P) : s=shape.targetArity n r := by
  induction F with
  | identity A hA P hPA hP => rfl
  | regularize A hA hVF P hPA hP hPVF => rfl
  | centripetal A D P hPA E hData => rfl
  | comp P hPA F H ihF ihH =>
    change _=SynchronizedChainShape.targetArity _ (SynchronizedChainShape.targetArity _ _ _) _
    rw [ihH,ihF]

end DiamondIntegral.Section6
