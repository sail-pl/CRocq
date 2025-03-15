From Coq.Logic Require Import FunctionalExtensionality.

Set Universe Polymorphism.

Declare Scope category_scope.

Open Scope category_scope.

(*****************************************************************************)
(** ** Category object *)
(*****************************************************************************)
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
    id (a : obj) : hom a a;
    compose {a b c : obj} :  hom b c -> hom a b ->  hom a c
        where " g ∘ f " := (compose g f);
    cat_left_idty (a b : obj) : 
        forall (f : hom a b), f ∘ (id a) = f;
    cat_right_idty (a b :obj) : 
        forall (f : hom a b), (id b) ∘ f = f;
    cat_assoc (a b c d : obj) : 
        forall (f : hom a b) (g : hom b c) (h : hom c d),
            h ∘ (g ∘ f) = (h ∘ g) ∘ f }.

Coercion obj : Category >-> Sortclass.
Coercion hom : Category >-> Funclass.

Infix "∘" := compose (at level 42, left associativity) : category_scope.

(*****************************************************************************)
(** ** Initial object *)
(*****************************************************************************)
(** An _initial object_ of a category [C] is a an object [a] with 
    a unique morphism to all objects of the category. *)

Class Initial (C : Category) : Type := {
    init_obj : C;
    init_morph (a : C) : C init_obj a;
    init_spec (a : C) (h' : C init_obj a) : 
            h' = init_morph a
}.

Coercion init_obj : Initial >-> obj.

(*****************************************************************************)
(** ** Terminal object *)
(*****************************************************************************)
(** A _terminal object_ of a category [C] is a an object [a] with 
    a unique morphism from all objects of the category. *)

Class Terminal (C : Category) : Type := 
{
    term_obj : C;
    term_morph (a : C) : C a term_obj;
    term_spec (a : C) (h' : C a term_obj) :
        h' = term_morph a
}.

Coercion term_obj : Terminal >-> obj.

(*****************************************************************************)
(** ** Product object *)
(*****************************************************************************)
(** Given two objects [a] and [b] of a category [C], 
    an object [c] is a _product_ of [a] and [b] if there exists two morphisms
    [π₁ : C c a] and [π₂ : C c b] such that for all object [x] with morphisms 
    [f : C x a] and [g : C x b] we have a unique [⟨ f, g ⟩ : C c x] such that 
        - [f = π₁ ∘ ⟨ f, g ⟩]
        - [g = π₂ ∘ ⟨ f, g ⟩]
    *)

Reserved Notation "⟨ F , G ⟩" (at level 0, no associativity).

Class Product  {C : Category} (a b : C) : Type := {
    prod_obj : C;
    π₁ : C prod_obj a;
    π₂ : C prod_obj b;
    prod_morph (x : C) : C x a -> C x b -> C x prod_obj
        where "⟨ F , G ⟩" := (prod_morph _ F G);
    prod_spec1 : forall (c : C) (f : C c a) (g : C c b),
            f = π₁ ∘ ⟨ f, g ⟩ /\ g = π₂ ∘ ⟨ f, g ⟩;
    prod_spec2 (c : C) : 
        forall (f : C c a) (g : C c b) (h : C c prod_obj),
            f = π₁ ∘ h /\ g = π₂ ∘ h -> h = ⟨ f,  g ⟩ }.
    
Arguments prod_morph {C a b _}. 

Coercion prod_obj : Product >-> obj.

Notation "⟨ F , G ⟩" := (prod_morph _ F G) (at level 0, no associativity).

(*****************************************************************************)
(** ** Coproduct object *)
(*****************************************************************************)
(** Given two objects [a] and [b] of a category [C], 
    an object [c] is a _coproduct_ of [a] and [b] if there exists two morphisms
    [ι₁ : C a c] and [ι₂ : C b c] such that for all object [x] with morphisms 
    [f : C a x] and [g : C b x] we have a unique [⟨ f, g ⟩ : C x c] such that 
        - [f = [f, g] ∘ ι₁]
        - [g = [f, g] ∘ ι₂].
    *)

Reserved Notation "[ F , G ]" (at level 0, no associativity).

Class Coproduct `{C : Category} (a b : obj) : Type := {
    coprod_obj : C;
    ι₁ : C a coprod_obj;
    ι₂ : C b coprod_obj;
    coprod_morph (c : C) : C a c -> C b c -> C coprod_obj c
        where "[ F , G ]" := (coprod_morph _ F G);
    coprod_spec1 : forall (c : C) (f : C a c) (g : C b c),
            f = [ f, g ] ∘ ι₁ /\ g = [ f, g ] ∘ ι₂;
    coprod_spec2 : forall (c : C) (f : C a c) (g : C b c) 
        (h : C coprod_obj c),
            f = h ∘ ι₁ /\ g = h ∘ ι₂ -> [ f, g ] = h }.

Arguments coprod_morph {C a b _}. 

Notation "[ F , G ]" := (coprod_morph _ F G) (at level 0, no associativity).
    
(*****************************************************************************)
(** ** Cartesian Category *)
(*****************************************************************************)
(** A cartesian category is a category with a 
    product [a ⊗ b] for all all pair of objects [a] and [b] *)

Class Cartesian (C : Category) : Type := {
    product : forall (a b : C), Product a b 
}.

Infix "⊗" := product 
    (at level 41, right associativity) : category_scope.

Definition product_hom {C : Category} {H : @Cartesian C} : 
    forall {a b c d : C}, C a b -> C c d -> C (a ⊗ c) (b ⊗ d) :=
        fun {a b c d : C} (f : C a b) (g : C c d) => ⟨ (f ∘ π₁), (g ∘ π₂) ⟩.

Infix "⨂" := product_hom 
    (at level 42, left associativity) : category_scope.

(*******************************************************************)
(** ** Exponential *)
(*******************************************************************)
(** Given two objects [a] and [b] of a category [C], an object [c] 
    is an exponential of [a] and [b] if there exists 
    a morphism [eval : C (c ⊗ a) b] such that ... 
    *)

Class Exponential {C : Category} {H : Cartesian C} (a b : C) : Type :=
{
    exp_obj : C;
    exp_morph : C (exp_obj ⊗ a) b;
    exp_spec : 
        forall (c : C) (g : C (c ⊗ a) b),
            exists! (curry_g : C c exp_obj),
                g = exp_morph ∘ (curry_g ⨂ (id _ ))
}.

Coercion exp_obj : Exponential >-> obj.
(*******************************************************************)
(** ** Cartesian Closed Category *)
(*******************************************************************)
(** A cartesian closed category is a category with a terminal object
    and an exponential [exp a b] for all all pair of objects 
    [a] and [b] *)

Class CartesianClosed (C:Category) : Type := {
    CartesianClosed_Cartesian :: Cartesian C;
    term : Terminal C;
    exp : forall a b, Exponential a b
}.

(*******************************************************************)
(** ** BiCartesian Closed Category *)
(*******************************************************************)
(** A bicartesian closed category is a cartesian closed category
    with a initial object and a coproduct [a ⊕ b] for all objects [a]
    and [b] *)

Class BiCartesianClosed (C : Category) : Type := {
    BiCartesianClosed_CartesianClosed :: CartesianClosed C;
    init : Initial C;
    coproduct : forall a b, Coproduct a b
}.

Infix "⊕" := coproduct 
    (at level 41, right associativity) : category_scope.

Class Epic {C : Category} (a b : C): Type := 
{
    epic_morph : C a b;
    epic_spec : forall (c : C) (f1 f2 : C b c),
        f1 ∘ epic_morph = f2 ∘ epic_morph -> f1 = f2
}.

Class Monic {C : Category} (a b : C): Type := 
{
    monic_morph : C a b;
    monic_spec : forall (c : C) (f1 f2 : C c a),
        monic_morph ∘ f1 = monic_morph ∘ f2 -> f1 = f2
}.

Coercion monic_morph : Monic >-> hom.

Class CRelation {C : Category} {H : @Cartesian C} (a b c : C) : Type := 
{
    crelation_morph : Monic c (a ⊗ b)
}.
