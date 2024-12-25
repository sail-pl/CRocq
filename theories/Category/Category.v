From Coq.Logic Require Import FunctionalExtensionality.

Set Universe Polymorphism.

Declare Scope category_scope.
Open Scope category_scope.

(** ** Category *)

(** A _category_ [C] consists of:
    -   a type of objects [obj], denoted by [C]
    -   a type of morphisms [hom a b], denoted [C a b], for each pair of objects [a] and [b]
    -   an identity morphism [idty a : C a a] for every object [a]
    -   a composition operator [∘], which assigns to each pair of arrows 
        [g : C b c] and [f : C a b] a composite morphism [g ∘ f : C a c] 
    The composition operator is associative and has identity morphisms
    as neutral elements.
*)

Reserved Infix "∘" (at level 42, left associativity).

Class Category : Type := {
    obj : Type;
    hom : obj -> obj -> Type;
    idty (a : obj) : hom a a;
    compose {a b c : obj} :  hom b c -> hom a b ->  hom a c
        where " g ∘ f " := (compose g f);
    compose_left_idty (a b : obj) : 
        forall (f : hom a b), f ∘ (idty a) = f;
    compose_right_idty (a b :obj) : 
        forall (f : hom a b), (idty b) ∘ f = f;
    compose_assoc (a b c d : obj) : 
        forall (f : hom a b) (g : hom b c) (h : hom c d),
            h ∘ (g ∘ f) = (h ∘ g) ∘ f }.

Coercion obj : Category >-> Sortclass.
Coercion hom : Category >-> Funclass.

Infix "∘" := compose (at level 42, left associativity) : category_scope.

(** ** Initial and final objects *)
(** An _initial object_ of a category [C] is a an object [a] with 
    a unique morphism to all objects of the category. *)

Class initial (C : Category) (a : C) : Prop := (* type class ? *)
    initial_spec : forall b : C, exists h : C a b, forall h' : C a b, h = h'.

(** An _initial object_ of a category [C] is a an object [a] with 
    a unique morphism from all objects of the category. *)

Class terminal (C : Category) (a : C) : Prop := 
    final_spec : forall b : C, exists h : C b a, forall h' : C b a, h = h'. 

(** ** Products and coproducts *)

(** A _product_ of two objects [a] and [b] of a category [C] is an 
    object [p : C] together with two morphisms [π₁ : C p a] and [π₂ : C p b]
    such that for all object [c] with morphisms [f : C c a] and [g : C c b]
    we have a unique [⟨ f, g ⟩ : C c p] such that 
        - [f = π₁ ∘ ⟨ f, g ⟩]
        - [g = π₂ ∘ ⟨ f, g ⟩]
    *)

Reserved Notation "⟨ F , G ⟩" (at level 0, no associativity).

Class product (C : Category) (a b : C) (p : C) := {
    π₁ : C p a;
    π₂ : C p b;
    pair_f (c : C) : C c a -> C c b -> C c p
        where "⟨ F , G ⟩" := (pair_f _ F G);
    pair_f_spec1 : forall (c : C) (f : C c a) (g : C c b),
            f = π₁ ∘ ⟨ f, g ⟩ /\ g = π₂ ∘ ⟨ f, g ⟩;
    pair_f_spec2 (c : C) : forall (f : C c a) (g : C c b) (h : C c p),
            f = π₁ ∘ h /\ g = π₂ ∘ h -> h = ⟨ f,  g ⟩ }.
    
Arguments pair_f {C a b p _}. 

Notation "⟨ F , G ⟩" := (pair_f _ F G) (at level 0, no associativity).

(** A _coproduct_ of two objects [a] and [b] of a category [C] is an 
    object [q : C] together with two morphisms [ι₁ : C a p] and [ι₂ : C b p]
    such that for all object [c] with morphisms [f : C a c] and [g : C b c]
    there exists a unique [h : C p c] such that 
    - [f = copair_f c f g ∘ ι₁]
    - [g = (pair_f c f g) ∘ ι₂].
    *)

Reserved Notation "[ F , G ]" (at level 0, no associativity).

Class coproduct (C : Category) (a b : C) (p : C) := {
    ι₁ : C a p;
    ι₂ : C b p;
    copair_f (c : C) : C a c -> C b c -> C p c
        where "[ F , G ]" := (copair_f _ F G);
    copair_f_spec1 : forall (c : C) (f : C a c) (g : C b c),
            f = [ f, g ] ∘ ι₁ /\ g = [ f, g ] ∘ ι₂;
    copair_f_spec2 : forall (c : C) (f : C a c) (g : C b c) (h : C p c),
            f = h ∘ ι₁ /\ g = h ∘ ι₂ -> [ f, g ] = h }.

Arguments copair_f {C a b p _}. 

Notation "[ F , G ]" := (copair_f _ F G) (at level 0, no associativity).
    
(** ** Cartesian category *)
(** A cartesian category is a category with a 
    product [a × b] for 
    all all pair of objects [a] and [b] *)

Reserved Infix "×" (at level 41, right associativity).

Class Cartesian `{C : Category}: Type := {
    product_obj : obj -> obj -> obj
        where "x × y" := (product_obj x y);
    product_obj_spec :: forall o o', product C o o' (o × o') }.

Infix "×" := product_obj 
    (at level 41, right associativity) : category_scope.

Generalizable Variables  C.

Definition product_hom `{H : @Cartesian C} {a b c d : C} : 
    C a b -> C c d -> C (a × c) (b × d) :=
        fun (f : C a b) (g : C c d) => ⟨ (f ∘ π₁), (g ∘ π₂) ⟩.

Infix "⨉" := product_hom 
    (at level 42, left associativity) : category_scope.

(** ** Cartesian Closed Category *)
(** A cartesian closed category is a category with an 
    exponential [exp a b] for all all pair of objects 
    [a] and [b] and a morphism 
        [eval : C ((exp o1 o2) × o1) o2] 
    such that *)

Class CartesianClosed `{@Cartesian C} : Type := {
    exp : obj -> obj -> obj;
    eval : forall (o1 o2 : C), C ((exp o1 o2) × o1) o2;
    eval_spec : 
        forall (o1 o2 q : C) (g : C (q × o1) o2),
            exists! (curry_g : C q (exp o1 o2)),
                g = eval o1 o2 ∘ (curry_g ⨉ (idty _ ))
}.