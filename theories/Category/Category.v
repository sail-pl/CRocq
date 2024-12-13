From Coq.Logic Require Import FunctionalExtensionality.

Set Universe Polymorphism.

Declare Scope category_scope.


(** ** Category *)

Reserved Infix "∘" (at level 42, left associativity).

Class Category : Type := {
    obj : Type;
    hom : obj -> obj -> Type;
    idty {A : obj} : hom A A;
    compose {A B C : obj} :  hom B C -> hom A B ->  hom A C
        where " g ∘ f " := (compose g f);
    compose_left_idty (A B :obj) : forall (f : hom A B), f ∘ idty = f;
    compose_right_idty (A B :obj) : forall (f : hom A B), idty ∘ f = f;
    compose_assoc (A B C D : obj) : 
        forall (f : hom A B) (g : hom B C) (h : hom C D),
            h ∘ (g ∘ f) = (h ∘ g) ∘ f }.

Coercion obj : Category >-> Sortclass.
Coercion hom : Category >-> Funclass.

Infix "∘" := compose (at level 42, left associativity) : category_scope.

Open Scope category_scope.

(** ** Initial and final objects *)

Class initial {C : Category} (a : C) : Prop := (* type class ? *)
    initial_spec : forall b : C, exists h : C a b, forall h' : C a b, h = h'.

Class final {C : Category} (a : C) : Prop := 
    final_spec : forall b : C, exists h : C b a, forall h' : C b a, h = h'. 

(** ** Products and coproduct *)

Class product {C : Category} (a b : C) (p : C) := {
    π₁ : C p a;
    π₂ : C p b;
    pair_f : forall (c : C) (f : C c a) (g : C c b), C c p;
    pair_f_spec1 : 
        forall (c : C) (f : C c a) (g : C c b),
            f = π₁ ∘ (pair_f c f g) /\ g = π₂ ∘ (pair_f c f g);
    pair_f_spec2 : 
        forall (c : C) (f : C c a) (g : C c b) (h : C c p),
            f = π₁ ∘ h /\ g = π₂ ∘ h -> pair_f c f g = h }.

Arguments pair_f {C a b p _ _}. 

Class coproduct {C : Category} (a b : C) (p : C) := {
    ι₁ : C a p;
    ι₂ : C b p;
    copair_f : forall (c : C) (f : C a c) (g : C b c), C p c;
    copair_f_spec1 : 
        forall (c : C) (f : C a c) (g : C b c),
            f = (copair_f c f g) ∘ ι₁ /\ g = (copair_f c f g) ∘ ι₂;
    copair_f_spec2 : 
        forall (c : C) (f : C a c) (g : C b c) (h : C p c),
            f = h ∘ ι₁ /\ g = h ∘ ι₂ -> copair_f c f g = h }.

Arguments copair_f {C a b p _ _}. 

(** ** Cartesian category *)

Reserved Infix "×" (at level 41, right associativity).

Class CartesianCategory `{C : Category}: Type := {
    product_obj : obj -> obj -> obj
        where "x × y" := (product_obj x y);
    product_obj_spec :: forall o o',
        product o o' (o × o') }.

Infix "×" := product_obj 
    (at level 41, right associativity) : category_scope.

Generalizable Variables  C.

Definition product_hom `{H : @CartesianCategory C} {a b c d : C} : 
    C a b -> C c d -> C (a × c) (b × d) :=
        fun (f : C a b) (g : C c d) =>
            pair_f (f ∘ π₁) (g ∘ π₂).

(** ** Cartesian Closed Category *)

Class CartesianClosedCategory `{@CartesianCategory C} : Type := {
    exp : obj -> obj -> obj;
    eval : forall (o1 o2 : C), C ((exp o1 o2) × o1) o2;
    eval_spec : forall o1 o2 (q : C) (g : C (q × o1) o2),
            exists! (curry_g : C q (exp o1 o2)),
                g = eval o1 o2 ∘ (product_hom curry_g idty)
}.
