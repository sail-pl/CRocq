Require Import CRocq.Category.Category.
Require Import CRocq.Category.Functor.
Require Import CRocq.Category.Transformation.
Require Import CRocq.Category.Cone.


(* Limit *)

Class Limit {J C : Category} (D : Functor J C) : Type:= {
    limit_apex : C;
    limit_cone : Cone D limit_apex;
    
    factorization : forall (x : C) (X : Cone D x),
        {f : C x limit_apex |
            forall j (R : C limit_apex ((ConstantFunctor J C limit_apex) j)) 
            (Q : C x ((ConstantFunctor J C x) j)), (X j) ∘ Q = (limit_cone j) ∘ R ∘ f}; 

    factorize_unique : forall (x : C) (X : Cone D x) (f g : C x limit_apex),
        (forall j (R : C limit_apex ((ConstantFunctor J C limit_apex) j)), 
            (limit_cone j) ∘ R ∘ f = (limit_cone j) ∘ R ∘ g ) -> f = g;
}.

(* Need a definition for R and Q or something else to reduce (ConstantFunctor J C limit_apex) j *)
