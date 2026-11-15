import «section 5».ElementaryTupleProjections

/-! Definable maps between actual raw tuple domains restrict along an
elementary embedding. Both source and target keep precisely the fixed
named parameters. Outputs at smaller-model inputs lie in that model. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section
namespace DiamondIntegral.Section5
open Classical FirstOrder FirstOrder.Language
variable {L : Language} {M N P : Type} [L.Structure M] [L.Structure N]
variable {c : P → M} {n m : ℕ}

structure RawDefinableGraphMap (c : P → M)
    (A : L.DefinableSet (Set.range c) (Fin n)) (B : L.DefinableSet (Set.range c) (Fin m)) where
  toFun : A.val → B.val
  graph_definable : (Set.range c).Definable L
    {w | ∃ a : A.val,w = Fin.append a.val (toFun a).val}

def RawDefinableGraphMap.graph
    {A : L.DefinableSet (Set.range c) (Fin n)} {B : L.DefinableSet (Set.range c) (Fin m)}
    (f : RawDefinableGraphMap c A B) : L.DefinableSet (Set.range c) (Fin (n+m)) :=
  ⟨_,f.graph_definable⟩

theorem RawDefinableGraphMap.graph_append_iff
    {A : L.DefinableSet (Set.range c) (Fin n)} {B : L.DefinableSet (Set.range c) (Fin m)}
    (f : RawDefinableGraphMap c A B) (x : Fin n → M) (y : Fin m → M) :
    Fin.append x y ∈ f.graph.val ↔ ∃ a : A.val,a.val = x ∧ (f.toFun a).val = y := by
  constructor
  · rintro ⟨a,he⟩
    refine ⟨a,?_,?_⟩
    · simpa only [Function.comp_def,Fin.append_left] using (congrArg (fun w : Fin (n+m) → M => w ∘ Fin.castAdd m) he).symm
    · simpa only [Function.comp_def,Fin.append_right] using (congrArg (fun w : Fin (n+m) → M => w ∘ Fin.natAdd n) he).symm
  · rintro ⟨a,rfl,rfl⟩
    exact ⟨a,rfl⟩

theorem raw_tuple_comp_append {Q R : Type} (g : Q → R) (x : Fin n → Q) (y : Fin m → Q) :
    g ∘ Fin.append x y = Fin.append (g ∘ x) (g ∘ y) := by
  funext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;> simp [Function.comp_def]

variable (e : M ↪ₑ[L] N) (c : P → M)
variable {A : L.DefinableSet (Set.range (e ∘ c)) (Fin n)}
variable {B : L.DefinableSet (Set.range (e ∘ c)) (Fin m)}

theorem RawDefinableGraphMap.output_in_elementary_image
    (f : RawDefinableGraphMap (e ∘ c) A B)
    (x : (elementaryActualDefinableEquiv e c A).val) :
    ∃ y : Fin m → M,e ∘ y = (f.toFun ⟨e ∘ x.val,x.property⟩).val := by
  let a : A.val := ⟨e ∘ x.val,x.property⟩
  have hex : ∃ y : Fin m → N,Fin.append (e ∘ x.val) y ∈ f.graph.val :=
    ⟨(f.toFun a).val,⟨a,rfl⟩⟩
  obtain ⟨y,hy⟩ := (elementary_actual_projection e c f.graph x.val).mp hex
  have hN : Fin.append (e ∘ x.val) (e ∘ y) ∈ f.graph.val := by
    change e ∘ Fin.append x.val y ∈ f.graph.val at hy
    simpa only [raw_tuple_comp_append] using hy
  obtain ⟨b,hb,hout⟩ := (f.graph_append_iff _ _).mp hN
  have hba : b = a := Subtype.ext hb
  exact ⟨y,(hba ▸ hout).symm⟩

def RawDefinableGraphMap.restrict
    (f : RawDefinableGraphMap (e ∘ c) A B) :
    (elementaryActualDefinableEquiv e c A).val → (elementaryActualDefinableEquiv e c B).val :=
  fun x => ⟨Classical.choose (f.output_in_elementary_image e c x),by
    change e ∘ Classical.choose (f.output_in_elementary_image e c x) ∈ B.val
    rw [Classical.choose_spec (f.output_in_elementary_image e c x)]
    exact (f.toFun ⟨e ∘ x.val,x.property⟩).property⟩

theorem RawDefinableGraphMap.restrict_commutes
    (f : RawDefinableGraphMap (e ∘ c) A B)
    (x : (elementaryActualDefinableEquiv e c A).val) :
    e ∘ (f.restrict e c x).val = (f.toFun ⟨e ∘ x.val,x.property⟩).val :=
  Classical.choose_spec (f.output_in_elementary_image e c x)

theorem RawDefinableGraphMap.restrict_graph
    (f : RawDefinableGraphMap (e ∘ c) A B) :
    {w | ∃ a : (elementaryActualDefinableEquiv e c A).val,
      w = Fin.append a.val (f.restrict e c a).val} =
        (elementaryActualDefinableEquiv e c f.graph).val := by
  ext w
  constructor
  · rintro ⟨a,rfl⟩
    change e ∘ Fin.append a.val (f.restrict e c a).val ∈ f.graph.val
    rw [raw_tuple_comp_append,f.restrict_commutes]
    exact ⟨⟨e ∘ a.val,a.property⟩,rfl⟩
  · intro hw
    have hN : e ∘ w ∈ f.graph.val := hw
    obtain ⟨a,ha⟩ := hN
    let x := w ∘ Fin.castAdd m
    let y := w ∘ Fin.natAdd n
    have hx : e ∘ x = a.val := by
      simpa only [x,Function.comp_def,Fin.append_left] using congrArg (fun t : Fin (n+m) → N => t ∘ Fin.castAdd m) ha
    have hy : e ∘ y = (f.toFun a).val := by
      simpa only [y,Function.comp_def,Fin.append_right] using congrArg (fun t : Fin (n+m) → N => t ∘ Fin.natAdd n) ha
    let b : (elementaryActualDefinableEquiv e c A).val := ⟨x,by change e ∘ x ∈ A.val;rw [hx];exact a.property⟩
    have hb : (⟨e ∘ b.val,b.property⟩ : A.val) = a := Subtype.ext hx
    have hby : (f.restrict e c b).val = y := by
      funext i
      apply e.injective
      exact congrFun ((f.restrict_commutes e c b).trans ((congrArg (fun a : A.val => (f.toFun a).val) hb).trans hy.symm)) i
    refine ⟨b,?_⟩
    rw [hby]
    exact (Fin.append_castAdd_natAdd (f := w)).symm

def RawDefinableGraphMap.restriction
    (f : RawDefinableGraphMap (e ∘ c) A B) :
    RawDefinableGraphMap c (elementaryActualDefinableEquiv e c A) (elementaryActualDefinableEquiv e c B) where
  toFun := f.restrict e c
  graph_definable := (f.restrict_graph e c).symm ▸ (elementaryActualDefinableEquiv e c f.graph).property

end DiamondIntegral.Section5
