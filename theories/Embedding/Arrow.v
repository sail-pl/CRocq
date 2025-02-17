Require Import Categories.Category.Category.
Require Import Categories.Embedding.CategoryType.

Reserved Infix ">>>" (at level 42, left associativity).

Definition assoc {a b c : Typ} : (a * b) * c -> a * (b * c) := 
                fun '((x,y),z) => (x,(y,z)).

Definition unassoc {a b c : Typ} : a * (b * c) -> (a * b) * c := 
                fun '(x,(y,z)) => ((x,y),z).

Class Arrow := 
{
    Ar : Typ -> Typ -> Typ;
    arr {a b : Typ} : forall (f : a -> b), Ar a b;
    arrcomp {a b c : Typ} : Ar a b -> Ar b c -> Ar a c
        where " f >>> g " := (arrcomp f g);
    first_ { a b c : Typ} : Ar a b -> Ar (a * c) (b * c);
    arrow_prop1 : 
        forall {a b : Typ} (f : Ar a b), 
            arr (fun (x : a) => x) >>> f = f;
    arrow_prop2 : 
        forall {a b : Typ} (f : Ar a b), 
            f >>> arr (fun (x : b) => x) = f;
    arrow_prop3 : 
        forall {a b c d : Typ} (f : Ar a b) (g : Ar b c) (h : Ar c d),
            (f >>> g) >>> h = f >>> (g >>> h);
    arrow_prop4 : 
        forall {a b c : Typ} (f : a -> b) (g : b -> c),
            arr f >>> arr g = arr (g ∘ f); 
    arrow_prop5 :
        forall {a b c : Typ} (f : Ar a b),
            @first_ _ _ c f >>> arr fst = arr fst >>> f;
    arrow_prop6 :
        forall {a b : Typ} (f : Ar a b) (g : a -> b),
            first_ f >>> arr (fun '(x,y) => (x, g y)) = 
            arr (fun '(x,y) => (x, g y)) >>> first_ f;
    arrow_prop7 :
        forall {a b c : Typ} f,
            first_ (first_ f) >>> arr (@assoc b a c)
                = arr (@assoc b a c)>>> first_ f;
    arrow_prop8 : forall {a b c : Typ} (f : a -> b),
        @first_ _ _ c (arr f) = arr (fun '(x,y) => (f x, y));
    arrow_prop9 : forall {a b c : Typ} (f : Ar a b) (g : Ar b c),
        @first_ _ _ c (f >>> g) = first_ f >>> first_ g;
}.

Infix ">>>" := arrcomp (at level 42, left associativity)
    : category_scope.

Open Scope category_scope.

Class ArrowLoop := 
{
    ArrowLoop_Arrow :: Arrow;
    loop {a b c : Typ} : c -> Ar (a * c) (b * c) -> Ar a b;
    arrowloop_prop1 : 
        forall {a b c d : Typ} 
            (h : Ar a b) (f : Ar (b * c) (d * c)) (x : c),
                loop x (first_ h >>> f) = h >>> loop x f;
    arrowloop_prop2 : 
        forall {a b c d : Typ} 
            (h : Ar b d) (f : Ar (a * c) (b * c)) (x : c),
                loop x (f >>> first_ h) = loop x f >>> h;
    arrowloop_prop3 : 
        forall {a b c d : Typ} 
            (f : Ar ((a * c) * d) ((b * c) * d)) (x : c) (y : d),
                loop x (loop y f) = loop (x,y) (arr unassoc >>> f >>> arr assoc);
}.
