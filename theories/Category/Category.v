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

(*****************************************************************************)
(** ** Initial object *)
(*****************************************************************************)
(** An _initial object_ of a category [C] is a an object [a] with 
    a unique morphism to all objects of the category. *)

Class initial {C : Category} : Type := {
    initial_obj : C;
    initial_morph (a : C) : C initial_obj a;
    initial_morph_spec (a : C) (h' : C initial_obj a) : 
            h' = initial_morph a
}.

Coercion initial_obj : initial >-> obj.

(*****************************************************************************)
(** ** Terminal object *)
(*****************************************************************************)
(** A _terminal object_ of a category [C] is a an object [a] with 
    a unique morphism from all objects of the category. *)

Class terminal {C : Category} : Type := 
{
    terminal_obj : C;
    terminal_morph (a : C) : C a terminal_obj;
    terminal_morph_spec (a : C) (h' : C a terminal_obj) :
        h' = terminal_morph a
}.

Coercion terminal_obj : terminal >-> obj.

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

Class product  {C : Category} (a b : C) : Type := {
    product_obj : C;
    π₁ : C product_obj a;
    π₂ : C product_obj b;
    product_morph (x : C) : C x a -> C x b -> C x product_obj
        where "⟨ F , G ⟩" := (product_morph _ F G);
    product_morph_spec1 : forall (c : C) (f : C c a) (g : C c b),
            f = π₁ ∘ ⟨ f, g ⟩ /\ g = π₂ ∘ ⟨ f, g ⟩;
    product_morph_spec2 (c : C) : 
        forall (f : C c a) (g : C c b) (h : C c product_obj),
            f = π₁ ∘ h /\ g = π₂ ∘ h -> h = ⟨ f,  g ⟩ }.
    
Arguments product_morph {C a b _}. 

Coercion product_obj : product >-> obj.

Notation "⟨ F , G ⟩" := (product_morph _ F G) (at level 0, no associativity).

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

Class coproduct `{C : Category} (a b : obj) : Type := {
    co_product_obj : C;
    ι₁ : C a co_product_obj;
    ι₂ : C b co_product_obj;
    coproduct_morph (c : C) : C a c -> C b c -> C co_product_obj c
        where "[ F , G ]" := (coproduct_morph _ F G);
    coproduct_morph_spec1 : forall (c : C) (f : C a c) (g : C b c),
            f = [ f, g ] ∘ ι₁ /\ g = [ f, g ] ∘ ι₂;
    coprodict_morph_spec2 : forall (c : C) (f : C a c) (g : C b c) 
        (h : C co_product_obj c),
            f = h ∘ ι₁ /\ g = h ∘ ι₂ -> [ f, g ] = h }.

Arguments coproduct_morph {C a b _}. 

Notation "[ F , G ]" := (coproduct_morph _ F G) (at level 0, no associativity).
    
(*****************************************************************************)
(** ** Cartesian Category *)
(*****************************************************************************)
(** A cartesian category is a category with a 
    product [a ⊗ b] for all all pair of objects [a] and [b] *)

Class Cartesian (C : Category) : Type := {
    prod : forall (a b : C), product a b 
}.

Infix "⊗" := prod 
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
    exponential_obj : C;
    exponential_morph : C (exponential_obj ⊗ a) b;
    exponential_morph_spec : 
        forall (c : C) (g : C (c ⊗ a) b),
            exists! (curry_g : C c exponential_obj),
                g = exponential_morph ∘ (curry_g ⨂ (idty _ ))
}.

(*******************************************************************)
(** ** Cartesian Closed Category *)
(*******************************************************************)
(** A cartesian closed category is a category with a terminal object
    and an exponential [exp a b] for all all pair of objects 
    [a] and [b] *)

Class CartesianClosed (C:Category) : Type := {
    CartesianClosed_Cartesian :: Cartesian C;
    term : terminal ;
    exp : forall a b, Exponential a b
}.

(* Class CartesianClosed (C:Category) {H :@Cartesian C} : Type := {
    term : terminal ;
    exp : forall a b, Exponential a b
}. *)

(*******************************************************************)
(** ** BiCartesian Closed Category *)
(*******************************************************************)
(** A bicartesian closed category is a cartesian closed category
    with a initial object and a coproduct [a ⊕ b] for all objects [a]
    and [b] *)

Class BiCartesianClosed (C : Category) : Type := {
    BiCartesianClosed_CartesianClosed :: CartesianClosed C;
    init : initial;
    coprod : forall a b, coproduct a b
}.

Infix "⊕" := coprod 
    (at level 41, right associativity) : category_scope.


Class epic {C : Category} (a b : C): Type := 
{
    epic_morph : C a b;
    epic_spec : forall (c : C) (f1 f2 : C b c),
        f1 ∘ epic_morph = f2 ∘ epic_morph -> f1 = f2
}.

Class monic {C : Category} (a b : C): Type := 
{
    monic_morph : C a b;
    monic_spec : forall (c : C) (f1 f2 : C c a),
        monic_morph ∘ f1 = monic_morph ∘ f2 -> f1 = f2
}.

Class crelation {C : Category} {H : @Cartesian C} (a b : C) : Type := 
{
    crelation_obj : C;
    crelation_morph : monic crelation_obj (a ⊗ b)
}.

(* Relation *)
(* monic relation_obj -> X, Y*)
