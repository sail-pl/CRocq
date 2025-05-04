Require Import CRocq.Category.Category.
Require Import CRocq.Embedding.CategoryType.

Reserved Infix ">>>" (at level 42, left associativity).

Definition swap {A B : Type} (u : A * B) := 
    let (x,y) := u in (y,x).

Definition assoc {A B C : Typ} : (A * B) * C -> A * (B * C) := 
                fun '((x,y),z) => (x,(y,z)).

Definition unassoc {A B C : Typ} : A * (B * C) -> (A * B) * C := 
                fun '(x,(y,z)) => ((x,y),z).

Class Arrow := 
{
    Ar : Typ -> Typ -> Typ;
    arr {a b : Typ} : forall (f : a -> b), Ar a b;
    arrcomp {a b c : Typ} : Ar a b -> Ar b c -> Ar a c
        where " f >>> g " := (arrcomp f g);
    first { a b c : Typ} : Ar a b -> Ar (a * c) (b * c);
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
            @first _ _ c f >>> arr fst = arr fst >>> f;
    arrow_prop6 :
        forall {a b : Typ} (f : Ar a b) (g : a -> b),
            first f >>> arr (fun '(x,y) => (x, g y)) = 
            arr (fun '(x,y) => (x, g y)) >>> first f;
    arrow_prop7 :
        forall {a b c : Typ} f,
            first (first f) >>> arr (@assoc b a c)
                = arr (@assoc b a c)>>> first f;
    arrow_prop8 : forall {a b c : Typ} (f : a -> b),
        @first _ _ c (arr f) = arr (fun '(x,y) => (f x, y));
    arrow_prop9 : forall {a b c : Typ} (f : Ar a b) (g : Ar b c),
        @first _ _ c (f >>> g) = first f >>> first g;
}.

Infix ">>>" := arrcomp (at level 42, left associativity)
    : category_scope.

Open Scope category_scope.

Class ArrowLoop2 := 
{
    ArrowLoop_Arrow2 :: Arrow;
    loop2 {a b c : Typ} : Ar (a * c) (b * c) -> Ar a b;
    arrowloop2_prop1 : 
        forall {a b c d : Typ} 
            (h : Ar a b) (f : Ar (b * c) (d * c)) (x : c),
                loop2 (first h >>> f) = h >>> loop2 f;
    arrowloop2_prop2 : 
        forall {a b c d : Typ} 
            (h : Ar b d) (f : Ar (a * c) (b * c)) (x : c),
                loop2 (f >>> first h) = loop2 f >>> h;
    arrowloop2_prop3 : 
        forall {a b c d : Typ} 
            (f : Ar ((a * c) * d) ((b * c) * d)) (x : c) (y : d),
                loop2 (loop2 f) = loop2 (arr unassoc >>> f >>> arr assoc);
}.

Class ArrowLoop := 
{
    ArrowLoop_Arrow :: Arrow;
    loop {a b c : Typ} : c -> Ar (a * c) (b * c) -> Ar a b;
    arrowloop_prop1 : 
        forall {a b c d : Typ} 
            (h : Ar a b) (f : Ar (b * c) (d * c)) (x : c),
                loop x (first h >>> f) = h >>> loop x f;
    arrowloop_prop2 : 
        forall {a b c d : Typ} 
            (h : Ar b d) (f : Ar (a * c) (b * c)) (x : c),
                loop x (f >>> first h) = loop x f >>> h;
    arrowloop_prop3 : 
        forall {a b c d : Typ} 
            (f : Ar ((a * c) * d) ((b * c) * d)) (x : c) (y : d),
                loop x (loop y f) = loop (x,y) (arr unassoc >>> f >>> arr assoc);
}.

(* first { a b c : Typ} : Ar a b -> Ar (a * c) (b * c); *)


Definition second {A : Arrow} {A B C : Type} (a : Ar A B) : 
    Ar (C * A) (C * B) := 
        arr swap >>> first a >>> arr swap.